/*
 * Copyright (c) 2025
 *
 * SPDX-License-Identifier: MIT
 */

#include "IC3IA.h"

#include "Common.h"
#include "TermUtils.h"
#include "TransformationUtils.h"

#include <algorithm>
#include <cassert>
#include <chrono>
#include <iostream>
#include <sstream>

namespace golem {

//=============================================================================
// Constructor
//=============================================================================

IC3IA::IC3IA(Logic & logic, Options const & options) : logic_(logic) {
    verbosity_ = std::stoi(options.getOrDefault(Options::VERBOSE, "0"));
    computeWitness = options.getOrDefault(Options::COMPUTE_WITNESS, "") == "true";
    useUnsatCoreGeneralization_ =
    options.getOrDefault(Options::IC3IA_USE_UNSAT_CORE_GENERALIZATION, "true") == "true";
    minimizeRefinementPredicates_ =
        options.getOrDefault(Options::IC3IA_MINIMIZE_REFINEMENT_PREDICATES, "true") == "true";
    useBinaryRefinementInterpolants_ =
        options.getOrDefault(Options::IC3IA_USE_BINARY_REFINEMENT_INTERPOLANTS, "false") == "true";
    addInitialReset_ =
        options.getOrDefault(Options::IC3IA_ADD_INITIAL_RESET, "true") == "true";
}

//=============================================================================
// IC3 core — reset and main loop
//=============================================================================

void IC3IA::resetIC3State() {
    depth_ = 0;
    clauses_.clear();
    cexTrace_.clear();
}

TransitionSystemVerificationResult IC3IA::runIC3() {
    if (verbosity_ > 0) { std::cout << "[IC3] Starting\n"; }

    // Base check: Init ∧ bad SAT → immediately unsafe.
    {
        SMTSolver solver(logic_, SMTSolver::WitnessProduction::NONE);
        solver.assertProp(init_);
        solver.assertProp(bad_);
        if (solver.check() == SMTSolver::Answer::SAT) {
            if (verbosity_ > 0) { std::cout << "[IC3] Initial states satisfy bad\n"; }
            return {VerificationAnswer::UNSAFE, 0u};
        }
    }

    pushFrame(); // depth_ = 1

    while (true) {
        if (verbosity_ > 0) { std::cout << "[IC3] Depth = " << depth_ << "\n"; }

        Cube badCube;
        while (hasBadSuccessor(badCube)) {
            if (!blockObligations(Obligation{badCube, depth_, nullptr})) {
                if (verbosity_ > 0) { std::cout << "[IC3] Counterexample found\n"; }
                return {VerificationAnswer::UNSAFE, depth_};
            }
            badCube.clear();
        }

        pushFrame();

        if (propagateClauses()) {
            for (unsigned i = 1; i < depth_; ++i) {
                bool hasAtI = false;
                for (auto const & c : clauses_) {
                    if (c.level == i) { hasAtI = true; break; }
                }
                if (!hasAtI) {
                    if (verbosity_ > 0) {
                        std::cout << "[IC3] Fixpoint at level " << i << "\n";
                    }
                    return {VerificationAnswer::SAFE, buildInvariant(i)};
                }
            }
            return {VerificationAnswer::SAFE, logic_.getTerm_true()};
        }
    }
}

//=============================================================================
// IC3 core — frame management
//=============================================================================

PTRef IC3IA::getF(unsigned k) const {
    if (k == 0) { return init_; }
    vec<PTRef> parts;
    for (auto const & c : clauses_) {
        if (c.level >= k) { parts.push(c.fla); }
    }
    if (parts.size() == 0) { return logic_.getTerm_true(); }
    return logic_.mkAnd(parts);
}

void IC3IA::addClause(PTRef clauseFla, unsigned level) {
    for (auto & c : clauses_) {
        if (c.fla == clauseFla) {
            if (c.level < level) { c.level = level; }
            return;
        }
    }
    clauses_.push_back({clauseFla, level});
}

//=============================================================================
// IC3 core — formula helpers
//=============================================================================

PTRef IC3IA::cubeToFla(Cube const & cube) const {
    if (cube.empty()) { return logic_.getTerm_true(); }
    vec<PTRef> lits;
    for (PTRef lit : cube) { lits.push(lit); }
    return logic_.mkAnd(lits);
}

PTRef IC3IA::prime(PTRef fla) const {
    return shiftFormulaThroughTime(fla, 1);
}

//=============================================================================
// IC3 core — model extraction
//=============================================================================

IC3IA::Cube IC3IA::modelToCube(std::shared_ptr<Model> const & model,
                                std::vector<PTRef> const & vars) const {
    Cube cube;
    cube.reserve(vars.size());
    for (PTRef var : vars) {
        PTRef val = model->evaluate(var);
        cube.push_back(val == logic_.getTerm_true() ? var : logic_.mkNot(var));
    }
    return cube;
}

//=============================================================================
// IC3 core — queries
//=============================================================================

bool IC3IA::initIntersects(Cube const & cube) const {
    SMTSolver solver(logic_, SMTSolver::WitnessProduction::NONE);
    solver.assertProp(init_);
    solver.assertProp(cubeToFla(cube));
    return solver.check() == SMTSolver::Answer::SAT;
}

bool IC3IA::hasBadSuccessor(Cube & outCube) const {
    SMTSolver solver(logic_, SMTSolver::WitnessProduction::ONLY_MODEL);
    solver.assertProp(getF(depth_));
    solver.assertProp(trans_);
    solver.assertProp(prime(bad_));
    if (solver.check() != SMTSolver::Answer::SAT) { return false; }
    outCube = modelToCube(solver.getModel(), stateVars_);
    return true;
}

bool IC3IA::hasPredecessorUnder(PTRef frameFormula, Cube const & cube,
                                 Cube & outCTI) const {
    SMTSolver solver(logic_, SMTSolver::WitnessProduction::ONLY_MODEL);
    solver.assertProp(frameFormula);
    solver.assertProp(trans_);
    solver.assertProp(prime(cubeToFla(cube)));
    if (solver.check() != SMTSolver::Answer::SAT) { return false; }
    outCTI = modelToCube(solver.getModel(), stateVars_);
    return true;
}

bool IC3IA::hasPredecessor(Cube const & cube, unsigned level, Cube & outCTI) const {
    assert(level > 0);
    return hasPredecessorUnder(getF(level - 1), cube, outCTI);
}

//=============================================================================
// IC3 core — generalization
//=============================================================================

IC3IA::Cube IC3IA::generalize(Cube cube, unsigned level) const {
    if (useUnsatCoreGeneralization_) { return generalizeWithUnsatCore(std::move(cube), level); }

    assert(level > 0);
    PTRef frameFormula = getF(level - 1);
    Cube dummy;
    for (std::size_t i = 0; i < cube.size(); ) {
        if (cube.size() == 1) { break; }
        Cube attempt;
        attempt.reserve(cube.size() - 1);
        for (std::size_t j = 0; j < cube.size(); ++j) {
            if (j != i) { attempt.push_back(cube[j]); }
        }
        if (!initIntersects(attempt) &&
            !hasPredecessorUnder(frameFormula, attempt, dummy)) {
            cube = std::move(attempt);
        } else {
            ++i;
        }
    }
    return cube;
}

IC3IA::Cube IC3IA::generalizeWithUnsatCore(Cube cube, unsigned level) const {
    assert(level > 0);
    if (cube.size() <= 1) { return cube; }

    PTRef frameFormula = getF(level - 1);

    auto extractCoreLiterals = [&](std::vector<PTRef> const & literals,
                                   vec<PTRef> const & background) -> std::vector<PTRef> {
        SMTSolver solver(logic_, SMTSolver::WitnessProduction::ONLY_UNSAT_CORE);
        for (PTRef part : background) { solver.assertProp(part); }
        for (PTRef lit : literals) { solver.assertProp(lit); }

        if (solver.check() != SMTSolver::Answer::UNSAT) { return {}; }

        auto core = solver.getCoreSolver().getUnsatCore();
        std::vector<PTRef> coreTerms;
        coreTerms.reserve(core->getTerms().size());
        for (PTRef t : core->getTerms()) { coreTerms.push_back(t); }
        return coreTerms;
    };

    vec<PTRef> initBackground;
    initBackground.push(init_);
    auto initCore = extractCoreLiterals(cube, initBackground);

    std::vector<PTRef> primedCube;
    primedCube.reserve(cube.size());
    for (PTRef lit : cube) { primedCube.push_back(prime(lit)); }

    vec<PTRef> predBackground;
    predBackground.push(frameFormula);
    predBackground.push(trans_);
    auto predCore = extractCoreLiterals(primedCube, predBackground);

    Cube reduced;
    reduced.reserve(cube.size());
    for (std::size_t i = 0; i < cube.size(); ++i) {
        if (std::find(initCore.begin(), initCore.end(), cube[i]) != initCore.end() ||
            std::find(predCore.begin(), predCore.end(), primedCube[i]) != predCore.end()) {
            reduced.push_back(cube[i]);
        }
    }

    Cube dummy;
    if (!initIntersects(reduced) && !hasPredecessorUnder(frameFormula, reduced, dummy)) {
        return reduced;
    }
    return cube;
}

//=============================================================================
// IC3 core — blocking loop
//=============================================================================

bool IC3IA::blockObligations(Obligation seed) {
    using PQ = std::priority_queue<Obligation,
                                   std::vector<Obligation>,
                                   std::greater<Obligation>>;
    PQ pq;
    pq.push(std::move(seed));

    while (!pq.empty()) {
        Obligation obl = pq.top();
        pq.pop();

        {
            SMTSolver solver(logic_, SMTSolver::WitnessProduction::NONE);
            solver.assertProp(getF(obl.level));
            solver.assertProp(cubeToFla(obl.cube));
            if (solver.check() == SMTSolver::Answer::UNSAT) { continue; }
        }

        if (obl.level == 0) {
            if (initIntersects(obl.cube)) {
                cexTrace_.clear();
                Obligation const * cur = &obl;
                while (cur) {
                    cexTrace_.push_back(cur->cube);
                    cur = cur->successor.get();
                }
                return false;
            }
            addClause(logic_.mkNot(cubeToFla(obl.cube)), 1u);
            continue;
        }

        Cube cti;
        if (hasPredecessor(obl.cube, obl.level, cti)) {
            auto oblPtr = std::make_shared<Obligation>(obl);
            pq.push(Obligation{std::move(cti), obl.level - 1, std::move(oblPtr)});
            pq.push(std::move(obl));
        } else if (initIntersects(obl.cube)) {
            // No predecessor, but the cube is in init — push to level 0
            // so the level-0 handler recognizes it as a real counterexample.
            pq.push(Obligation{obl.cube, 0, obl.successor});
        } else {
            Cube gen = generalize(obl.cube, obl.level);
            PTRef clause = logic_.mkNot(cubeToFla(gen));
            addClause(clause, obl.level);
            if (verbosity_ > 1) {
                std::cout << "[IC3] Blocked at level " << obl.level
                          << ", clause literals = " << gen.size() << "\n";
            }
        }
    }
    return true;
}

//=============================================================================
// IC3 core — clause propagation
//=============================================================================

bool IC3IA::propagateClauses() {
    for (unsigned i = 1; i < depth_; ++i) {
        for (auto & c : clauses_) {
            if (c.level != i) { continue; }
            PTRef negClausePrimed = prime(logic_.mkNot(c.fla));
            SMTSolver solver(logic_, SMTSolver::WitnessProduction::NONE);
            solver.assertProp(getF(i));
            solver.assertProp(trans_);
            solver.assertProp(negClausePrimed);
            if (solver.check() == SMTSolver::Answer::UNSAT) {
                c.level = i + 1;
            }
        }
        bool hasAtI = false;
        for (auto const & c : clauses_) {
            if (c.level == i) { hasAtI = true; break; }
        }
        if (!hasAtI) { return true; }
    }
    return false;
}

//=============================================================================
// IC3 core — invariant construction
//=============================================================================

PTRef IC3IA::buildInvariant(unsigned fixpointLevel) const {
    return getF(fixpointLevel);
}

//=============================================================================
// IC3IA top-level solve
//=============================================================================

TransitionSystemVerificationResult IC3IA::solve(TransitionSystem const & system) {
    concreteInit_         = system.getInit();
    concreteTrans_        = system.getTransition();
    concreteBad_          = system.getQuery();
    concreteStateVars_    = system.getStateVars();
    concreteNextStateVars_= system.getNextStateVars();

    if (addInitialReset_) {
        applyInitialReset();
    }

    predicates_.clear();
    predLabels_.clear();
    predLabelsNext_.clear();

    initializePredicates();

    if (verbosity_ > 0) {
        std::cout << "[IC3IA] Initial predicates: " << predicates_.size() << "\n";
    }

    static constexpr unsigned maxRefinements = 1000;
    for (unsigned iter = 0; iter < maxRefinements; ++iter) {
        setupAbstractSystem();

        auto result = runIC3();

        if (result.answer == VerificationAnswer::SAFE) {
            PTRef abstractInv = std::get<PTRef>(result.witness);
            PTRef concreteInv = concreteInvariant(abstractInv);
            if (addInitialReset_) {
                // Substitute reset → false to eliminate the internal reset variable.
                // In all reachable states of the original system, reset is always false.
                TimeMachine tm{logic_};
                PTRef resetVar = tm.getVarVersionZero("ic3ia_reset", logic_.getSort_bool());
                TermUtils::substitutions_map subst;
                subst[resetVar] = logic_.getTerm_false();
                concreteInv = TermUtils(logic_).varSubstitute(concreteInv, subst);
            }
            return {VerificationAnswer::SAFE, concreteInv};
        }

        if (result.answer == VerificationAnswer::UNSAFE) {
            std::size_t realDepth = 0;
            if (checkAndRefine(realDepth)) {
                // The reset transformation adds one extra step at the front; subtract it.
                if (addInitialReset_ && realDepth > 0) { --realDepth; }
                return {VerificationAnswer::UNSAFE, realDepth};
            }
            if (verbosity_ > 0) {
                std::cout << "[IC3IA] Spurious CEX at depth "
                          << std::get<std::size_t>(result.witness)
                          << "; predicates now: " << predicates_.size() << "\n";
            }
            continue;
        }

        return result;
    }

    return {VerificationAnswer::UNKNOWN, 0u};
}

//=============================================================================
// IC3IA — predicate management
//=============================================================================

void IC3IA::collectVars(PTRef fla, std::vector<PTRef> & vars) const {
    if (logic_.isVar(fla)) {
        if (std::find(vars.begin(), vars.end(), fla) == vars.end()) {
            vars.push_back(fla);
        }
        return;
    }

    Pterm const & t = logic_.getPterm(fla);
    for (int i = 0; i < t.size(); ++i) {
        collectVars(t[i], vars);
    }
}

PTRef IC3IA::shiftFormulaThroughTime(PTRef fla, int steps) const {
    if (steps == 0) { return fla; }

    TimeMachine tm{logic_};
    std::vector<PTRef> stack;
    collectVars(fla, stack);

    TermUtils::substitutions_map substitutions;
    for (PTRef var : stack) {
        if (tm.isVersioned(var)) {
            substitutions[var] = tm.sendVarThroughTime(var, steps);
        }
    }

    if (substitutions.empty()) { return fla; }
    return TermUtils(logic_).varSubstitute(fla, substitutions);
}

void IC3IA::collectAtoms(PTRef fla, std::vector<PTRef> & atoms) const {
    if (logic_.isTrue(fla) || logic_.isFalse(fla)) { return; }

    Pterm const & t = logic_.getPterm(fla);

    if (logic_.isAnd(fla) || logic_.isOr(fla)) {
        for (int i = 0; i < t.size(); ++i) { collectAtoms(t[i], atoms); }
        return;
    }
    if (logic_.isNot(fla)) {
        collectAtoms(t[0], atoms);
        return;
    }
    if (std::find(atoms.begin(), atoms.end(), fla) == atoms.end()) {
        atoms.push_back(fla);
    }
}

std::vector<PTRef> IC3IA::minimizeRefinementPredicateSet(std::vector<PTRef> candidates,
                                                         std::vector<PTRef> const & unshiftedInterpolants,
                                                         std::size_t depth) const {
    if (candidates.size() <= 1 || unshiftedInterpolants.empty()) { return candidates; }

    SMTSolver solver(logic_, SMTSolver::WitnessProduction::ONLY_UNSAT_CORE);
    solver.assertProp(concreteInit_);
    for (std::size_t i = 0; i < depth; ++i) {
        solver.assertProp(atTime(concreteTrans_, static_cast<unsigned>(i)));
    }
    solver.assertProp(atTime(concreteBad_, static_cast<unsigned>(depth)));

    TermUtils::substitutions_map subst;
    std::vector<PTRef> activationLiterals;
    std::vector<PTRef> abstractionLabels;
    std::vector<PTRef> guardedDefinitions;
    activationLiterals.reserve(candidates.size());
    abstractionLabels.reserve(candidates.size());
    guardedDefinitions.reserve(candidates.size());

    for (std::size_t i = 0; i < candidates.size(); ++i) {
        std::string suffix = std::to_string(i);
        PTRef act = logic_.mkBoolVar((".ic3ia_refpred_act_" + suffix).c_str());
        PTRef lbl = logic_.mkBoolVar((".ic3ia_refpred_lbl_" + suffix).c_str());
        activationLiterals.push_back(act);
        abstractionLabels.push_back(lbl);
        subst[candidates[i]] = lbl;
        subst[logic_.mkNot(candidates[i])] = logic_.mkNot(lbl);
    }

    TermUtils termUtils(logic_);
    for (std::size_t i = 0; i < unshiftedInterpolants.size(); ++i) {
        PTRef abstractedInterpolant = termUtils.varSubstitute(unshiftedInterpolants[i], subst);
        solver.assertProp(atTime(abstractedInterpolant, static_cast<unsigned>(i + 1)));
    }

    for (std::size_t i = 0; i < candidates.size(); ++i) {
        vec<PTRef> eqs;
        for (std::size_t step = 0; step < unshiftedInterpolants.size(); ++step) {
            eqs.push(logic_.mkEq(atTime(abstractionLabels[i], static_cast<unsigned>(step + 1)),
                                 atTime(candidates[i], static_cast<unsigned>(step + 1))));
        }
        PTRef definition = eqs.size() == 1 ? eqs[0] : logic_.mkAnd(eqs);
        PTRef guarded = logic_.mkOr(logic_.mkNot(activationLiterals[i]), definition);
        guardedDefinitions.push_back(guarded);
        solver.assertProp(guarded);
        solver.assertProp(activationLiterals[i]);
    }

    if (solver.check() != SMTSolver::Answer::UNSAT) { return candidates; }

    auto core = solver.getCoreSolver().getUnsatCore();
    std::vector<PTRef> kept;
    kept.reserve(candidates.size());
    for (std::size_t i = 0; i < candidates.size(); ++i) {
        bool inCore = false;
        for (PTRef t : core->getTerms()) {
            if (t == activationLiterals[i] || t == guardedDefinitions[i]) {
                inCore = true;
                break;
            }
        }
        if (inCore) { kept.push_back(candidates[i]); }
    }

    return kept.empty() ? candidates : kept;
}

bool IC3IA::addPredicate(PTRef pred) {
    if (std::find(predicates_.begin(), predicates_.end(), pred) != predicates_.end()) {
        return false;
    }

    predicates_.push_back(pred);

    TimeMachine tm{logic_};
    std::ostringstream ss;
    ss << "ic3ia_pred_" << (predicates_.size() - 1);
    std::string baseName = ss.str();

    PTRef lCurr = tm.getVarVersionZero(baseName, logic_.getSort_bool());
    PTRef lNext = tm.sendVarThroughTime(lCurr, 1);

    predLabels_.push_back(lCurr);
    predLabelsNext_.push_back(lNext);
    return true;
}

void IC3IA::applyInitialReset() {
    TimeMachine tm{logic_};
    PTRef reset = tm.getVarVersionZero("ic3ia_reset", logic_.getSort_bool());
    PTRef resetNext = tm.sendVarThroughTime(reset, 1);

    PTRef oldInit = concreteInit_;
    PTRef oldTrans = concreteTrans_;
    PTRef oldBad = concreteBad_;

    concreteInit_ = reset;
    vec<PTRef> transParts;
    transParts.push(logic_.mkNot(resetNext));
    transParts.push(logic_.mkOr(logic_.mkNot(reset), atTime(oldInit, 1)));
    transParts.push(logic_.mkOr(reset, oldTrans));
    concreteTrans_ = logic_.mkAnd(transParts);
    concreteBad_ = logic_.mkAnd(logic_.mkNot(reset), oldBad);
    concreteStateVars_.push_back(reset);
    concreteNextStateVars_.push_back(resetNext);

    if (verbosity_ > 0) {
        std::cout << "[IC3IA] Added initial reset state\n";
    }
}

void IC3IA::initializePredicates() {
    std::vector<PTRef> atoms;
    collectAtoms(concreteInit_, atoms);
    collectAtoms(concreteBad_,  atoms);

    for (PTRef a : atoms) {
        addPredicate(a);
    }
}

//=============================================================================
// IC3IA — abstract system construction
//=============================================================================

PTRef IC3IA::abstractFormula(PTRef fla) const {
    if (logic_.isTrue(fla) || logic_.isFalse(fla)) { return fla; }

    for (std::size_t i = 0; i < predicates_.size(); ++i) {
        if (fla == predicates_[i])               { return predLabels_[i]; }
        if (fla == logic_.mkNot(predicates_[i])) { return logic_.mkNot(predLabels_[i]); }
    }

    Pterm const & t = logic_.getPterm(fla);

    if (logic_.isAnd(fla)) {
        vec<PTRef> args;
        for (int i = 0; i < t.size(); ++i) { args.push(abstractFormula(t[i])); }
        return logic_.mkAnd(args);
    }
    if (logic_.isOr(fla)) {
        vec<PTRef> args;
        for (int i = 0; i < t.size(); ++i) { args.push(abstractFormula(t[i])); }
        return logic_.mkOr(args);
    }
    if (logic_.isNot(fla)) {
        return logic_.mkNot(abstractFormula(t[0]));
    }

    return fla;
}

void IC3IA::setupAbstractSystem() {
    assert(!predicates_.empty());

    vec<PTRef> labelDefParts;
    for (std::size_t i = 0; i < predicates_.size(); ++i) {
        labelDefParts.push(logic_.mkEq(predLabels_[i], predicates_[i]));
    }
    PTRef labelDefs = logic_.mkAnd(labelDefParts);

    init_ = logic_.mkAnd(concreteInit_, labelDefs);
    bad_  = logic_.mkAnd(concreteBad_,  labelDefs);

    vec<PTRef> transParts;
    transParts.push(concreteTrans_);
    transParts.push(labelDefs);
    for (std::size_t i = 0; i < predicates_.size(); ++i) {
        PTRef pNext = shiftFormulaThroughTime(predicates_[i], 1);
        transParts.push(logic_.mkEq(predLabelsNext_[i], pNext));
    }
    trans_ = logic_.mkAnd(transParts);

    stateVars_     = predLabels_;
    nextStateVars_ = predLabelsNext_;

    resetIC3State();
}

PTRef IC3IA::concreteInvariant(PTRef abstractInv) const {
    TermUtils::substitutions_map subst;
    for (std::size_t i = 0; i < predicates_.size(); ++i) {
        subst[predLabels_[i]]               = predicates_[i];
        subst[logic_.mkNot(predLabels_[i])] = logic_.mkNot(predicates_[i]);
    }
    return TermUtils(logic_).varSubstitute(abstractInv, subst);
}

//=============================================================================
// IC3IA — concrete CEGAR check
//=============================================================================

PTRef IC3IA::atTime(PTRef fla, unsigned steps) const {
    return shiftFormulaThroughTime(fla, static_cast<int>(steps));
}

bool IC3IA::checkAndRefine(std::size_t & outDepth) {
    std::size_t const k = cexTrace_.empty() ? depth_ : cexTrace_.size();
    auto const refineStart = std::chrono::steady_clock::now();

    if (verbosity_ > 1) {
        std::cout << "[IC3IA] Checking concrete trace of length " << k << "\n";
    }

    SMTSolver solver(logic_, SMTSolver::WitnessProduction::MODEL_AND_INTERPOLANTS);
    solver.getConfig().setSimplifyInterpolant(4);

    auto guidedStateFormulaAt = [&](std::size_t index) {
        if (cexTrace_.empty() || index >= cexTrace_.size()) { return logic_.getTerm_true(); }
        return atTime(concreteInvariant(cubeToFla(cexTrace_[index])), static_cast<unsigned>(index));
    };

    vec<PTRef> initParts;
    initParts.push(concreteInit_);
    PTRef guideAtZero = guidedStateFormulaAt(0);
    if (guideAtZero != logic_.getTerm_true()) { initParts.push(guideAtZero); }
    solver.assertProp(initParts.size() == 1 ? initParts[0] : logic_.mkAnd(initParts));

    for (std::size_t i = 0; i < k; ++i) {
        vec<PTRef> transParts;
        transParts.push(atTime(concreteTrans_, static_cast<unsigned>(i)));
        PTRef guidedState = guidedStateFormulaAt(i + 1);
        if (guidedState != logic_.getTerm_true()) { transParts.push(guidedState); }
        solver.assertProp(transParts.size() == 1 ? transParts[0] : logic_.mkAnd(transParts));
    }

    solver.assertProp(atTime(concreteBad_, static_cast<unsigned>(k)));

    auto const solveStart = std::chrono::steady_clock::now();
    auto res = solver.check();
    auto const solveEnd = std::chrono::steady_clock::now();
    if (res == SMTSolver::Answer::SAT) {
        outDepth = k;
        if (verbosity_ > 1) {
            auto solveMs = std::chrono::duration_cast<std::chrono::milliseconds>(solveEnd - solveStart).count();
            std::cout << "[IC3IA] Concrete check SAT in " << solveMs << " ms\n";
        }
        return true;
    }
    if (res != SMTSolver::Answer::UNSAT) {
        outDepth = k;
        if (verbosity_ > 1) {
            auto solveMs = std::chrono::duration_cast<std::chrono::milliseconds>(solveEnd - solveStart).count();
            std::cout << "[IC3IA] Concrete check returned UNKNOWN in " << solveMs << " ms\n";
        }
        return true;
    }

    auto itpCtx = solver.getInterpolationContext();
    vec<PTRef> interpolantsVec;
    std::vector<ipartitions_t> pathMasks;
    pathMasks.reserve(k);
    for (std::size_t i = 0; i < k; ++i) {
        ipartitions_t mask = 0;
        for (std::size_t j = 0; j <= i + 1; ++j) {
            opensmt::setbit(mask, static_cast<unsigned>(j));
        }
        pathMasks.push_back(mask);
    }
    auto const interpolationStart = std::chrono::steady_clock::now();
    if (not pathMasks.empty()) {
        if (useBinaryRefinementInterpolants_) {
            for (ipartitions_t mask : pathMasks) {
                std::vector<PTRef> single;
                itpCtx->getSingleInterpolant(single, mask);
                if (!single.empty()) { interpolantsVec.push(single.front()); }
            }
        } else {
            itpCtx->getPathInterpolants(interpolantsVec, pathMasks);
        }
    }
    auto const interpolationEnd = std::chrono::steady_clock::now();

    std::vector<PTRef> interpolants;
    interpolants.reserve(interpolantsVec.size());
    for (PTRef itp : interpolantsVec) { interpolants.push_back(itp); }

    std::vector<PTRef> unshiftedInterpolants;
    unshiftedInterpolants.reserve(interpolants.size());
    std::vector<PTRef> candidatePredicates;
    for (std::size_t i = 0; i < interpolants.size(); ++i) {
        PTRef unshifted = shiftFormulaThroughTime(interpolants[i], -static_cast<int>(i + 1));
        unshiftedInterpolants.push_back(unshifted);
        std::vector<PTRef> atoms;
        collectAtoms(unshifted, atoms);
        for (PTRef a : atoms) {
            if (std::find(candidatePredicates.begin(), candidatePredicates.end(), a) == candidatePredicates.end()) {
                candidatePredicates.push_back(a);
            }
        }
    }

    if (minimizeRefinementPredicates_) {
        auto minimized = minimizeRefinementPredicateSet(candidatePredicates, unshiftedInterpolants, k);
        if (verbosity_ > 0 && minimized.size() < candidatePredicates.size()) {
            std::cout << "[IC3IA] Minimized refinement predicates from "
                      << candidatePredicates.size() << " to " << minimized.size() << "\n";
        }
        candidatePredicates = std::move(minimized);
    }

    unsigned newPreds = 0;
    for (PTRef pred : candidatePredicates) {
        if (addPredicate(pred)) { ++newPreds; }
    }

    if (verbosity_ > 0) {
        std::cout << "[IC3IA] Added " << newPreds << " new predicates\n";
    }

    if (newPreds == 0) {
        for (PTRef itp : unshiftedInterpolants) { addPredicate(itp); }
    }

    if (verbosity_ > 1) {
        auto solveMs = std::chrono::duration_cast<std::chrono::milliseconds>(solveEnd - solveStart).count();
        auto interpolationMs =
            std::chrono::duration_cast<std::chrono::milliseconds>(interpolationEnd - interpolationStart).count();
        auto totalMs = std::chrono::duration_cast<std::chrono::milliseconds>(
            std::chrono::steady_clock::now() - refineStart).count();
        std::cout << "[IC3IA] Refinement timings (ms): solve=" << solveMs
                  << ", interpolation=" << interpolationMs
                  << ", total=" << totalMs << "\n";
    }

    return false;
}

} // namespace golem
