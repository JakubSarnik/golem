/*
 * Copyright (c) 2025
 *
 * SPDX-License-Identifier: MIT
 */

#ifndef GOLEM_IC3IA_H
#define GOLEM_IC3IA_H

#include "Options.h"
#include "TermUtils.h"
#include "TransitionSystem.h"
#include "TransitionSystemEngine.h"
#include "utils/SmtSolver.h"

#include <memory>
#include <queue>
#include <chrono>
#include <unordered_map>
#include <vector>

namespace golem {

/*
 * IC3 with Implicit Predicate Abstraction (IC3IA).
 *
 * CEGAR loop:
 *   1. Extract initial predicates from init and bad (their atomic sub-formulas).
 *   2. Build abstract Boolean TransitionSystem:
 *        stateVars  = { l_i (Bool) ↔ p_i(x##0) }
 *        trans      = concreteT ∧ (l_i ↔ p_i(x##0)) ∧ (l_i' ↔ p_i(x##1))
 *        init / bad = concrete init/bad with atoms replaced by labels
 *   3. Run IC3 on the abstract system (via runIC3()).
 *   4a. SAFE → translate invariant (substitute labels back to predicates) → done.
 *   4b. UNSAFE(depth k) → concrete BMC check:
 *        - Build Init ∧ T@0 ∧ ... ∧ T@{k-1} ∧ bad@k (using cexTrace_ cubes as guides).
 *        - SAT  → real counterexample.
 *        - UNSAT → extract k sequence interpolants as new predicates; restart IC3.
 */
class IC3IA : public TransitionSystemEngine {
public:
    IC3IA(Logic & logic, Options const & options);

    using TransitionSystemEngine::solve;
    TransitionSystemVerificationResult solve(TransitionSystem const & system) override;

private:
    // --- IC3 core types ---

    // A cube is a conjunction of literals over the current state variables.
    using Cube = std::vector<PTRef>;

    // Proof obligation: prove `cube` is not reachable at `level` steps from Init.
    struct Obligation {
        Cube   cube;
        unsigned level;
        // unsigned traceLen;
        std::shared_ptr<Obligation const> successor;

        bool operator>(Obligation const & o) const { return level > o.level; }
    };

    // A blocking clause: ¬cube (a disjunction), valid for F[1..level].
    struct BlockingClause {
        PTRef    fla;
        unsigned level;
    };

    // --- IC3 core state ---

    Logic &   logic_;
    int       verbosity_{0};
    bool      useUnsatCoreGeneralization_{true};
    bool      minimizeRefinementPredicates_{true};
    bool      useBinaryRefinementInterpolants_{false};
    bool      addInitialReset_{true};

    // Set before calling runIC3(); setupAbstractSystem() fills these with abstract formulas.
    PTRef                init_{PTRef_Undef};
    PTRef                trans_{PTRef_Undef};
    PTRef                bad_{PTRef_Undef};
    std::vector<PTRef>   stateVars_;
    std::vector<PTRef>   nextStateVars_;

    unsigned             depth_{0};
    std::vector<BlockingClause> clauses_;

    // Populated when blockObligations returns false (real CEX found).
    std::vector<Cube>    cexTrace_;

    // --- IC3 core methods ---

    void resetIC3State();
    TransitionSystemVerificationResult runIC3(bool resuming = false);

    void  pushFrame()          { ++depth_; }
    PTRef getF(unsigned k) const;
    void  addClause(PTRef clauseFla, unsigned level);

    PTRef cubeToFla(Cube const & cube) const;
    PTRef prime(PTRef fla) const;

    Cube  modelToCube(std::shared_ptr<Model> const & model,
                      std::vector<PTRef> const & vars) const;

    bool  initIntersects(Cube const & cube) const;
    bool  hasBadSuccessor(Cube & outCube) const;
    bool  hasPredecessorUnder(PTRef frameFormula, Cube const & cube,
                               Cube & outCTI) const;
    bool  hasPredecessor(Cube const & cube, unsigned level, Cube & outCTI) const;

    Cube  generalize(Cube cube, unsigned level) const;
    Cube  generalizeWithUnsatCore(Cube cube, unsigned level) const;
    bool  blockObligations(Obligation seed);
    bool  propagateClauses();
    PTRef buildInvariant(unsigned fixpointLevel) const;

    // --- Concrete system (set at the start of solve()) ---

    PTRef               concreteInit_{PTRef_Undef};
    PTRef               concreteTrans_{PTRef_Undef};
    PTRef               concreteBad_{PTRef_Undef};
    std::vector<PTRef>  concreteStateVars_;
    std::vector<PTRef>  concreteNextStateVars_;

    // --- Predicate abstraction state ---

    std::vector<PTRef>  predicates_;      // p_i(x##0) — concrete atoms
    std::vector<PTRef>  predLabels_;      // l_i##0    — Boolean current-state label
    std::vector<PTRef>  predLabelsNext_;  // l_i##1    — Boolean next-state label

    // --- Predicate management ---

    void collectVars(PTRef fla, std::vector<PTRef> & vars) const;
    PTRef shiftFormulaThroughTime(PTRef fla, int steps) const;
    void collectAtoms(PTRef fla, std::vector<PTRef> & atoms) const;
    std::vector<PTRef> minimizeRefinementPredicateSet(std::vector<PTRef> candidates,
                                                      std::vector<PTRef> const & unshiftedInterpolants,
                                                      std::size_t depth) const;
    bool addPredicate(PTRef pred);
    void applyInitialReset();
    void initializePredicates();

    // --- Abstract system construction ---

    // Number of predicates whose label-definition equalities have already been
    // conjoined into init_/trans_/bad_. Maintained monotonically across CEGAR
    // iterations so that extendAbstractSystem() only asserts new predicates.
    std::size_t numAssertedPreds_{0};

    PTRef abstractFormula(PTRef fla) const;
    void  initializeAbstractSystem();
    void  extendAbstractSystem();
    PTRef concreteInvariant(PTRef abstractInv) const;

    // --- Persistent solvers for IC3 queries ---
    //
    // Both solvers are seeded once with the abstract system's constant context
    // (init_ / trans_) in initializeAbstractSystem(). New label-definition
    // conjuncts produced by extendAbstractSystem() are asserted incrementally,
    // outside any push scope, so they persist across queries. Each query uses
    // push()/pop() to scope its query-specific assertions.
    std::unique_ptr<SMTSolver> initSolver_;
    std::unique_ptr<SMTSolver> transSolver_;

    // --- Concrete CEGAR check ---

    bool checkAndRefine(std::size_t & outDepth);
    PTRef atTime(PTRef fla, unsigned steps) const;
};

} // namespace golem

#endif // GOLEM_IC3IA_H
