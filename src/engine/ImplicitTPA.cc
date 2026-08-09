/*
 * Copyright (c) 2026, Martin Blicha <martin.blicha@gmail.com>
 *
 * SPDX-License-Identifier: MIT
 */

#include "ImplicitTPA.h"

#include "Common.h"
#include "Spacer.h"

#include <TransformationUtils.h>
#include <utils/StdUtils.h>

#include "graph/ChcGraphBuilder.h"
#include "transformers/SingleLoopTransformation.h"

namespace golem {

namespace {

std::string transitionHoleName = "implicit_tpa_tr";
std::string stateHoleName = "implicit_tpa_inv";

}

VerificationResult ImplicitTPA::solve(ChcDirectedGraph const & graph) {
    if (isTrivial(graph)) {
        return solveTrivial(graph);
    }

    if (logic.hasArrays()) {
        return VerificationResult{VerificationAnswer::UNKNOWN};
    }

    if (isTransitionSystem(graph)) {
        auto ts = toTransitionSystem(graph);

        assert(ts);
        const auto newGraph = reencodeTransitionSystem(*ts);

        assert(newGraph);
        auto res = runSpacer(*newGraph);

        res.getValidityWitness().print(std::cout, *newGraph);

        if (options.hasOption(Options::COMPUTE_WITNESS)) {
            return translateTransitionSystemResult(translateWitness(res), graph, *ts);
        } else {
            return res;
        }
    }

    if (isTransitionSystemDAG(graph) && !options.hasOption(Options::FORCE_TS)) {
        return VerificationResult{VerificationAnswer::UNKNOWN}; // TODO
    }

    // Otherwise, convert the graph to a transition system and try to solve it
    // using the transition system encoding.

    SingleLoopTransformation transformation;

    auto [ts, backtranslator] = transformation.transform(graph);

    assert(ts);
    const auto newGraph = reencodeTransitionSystem(*ts);

    assert(newGraph);
    auto res = runSpacer(*newGraph);

    return computeWitness ? backtranslator->translate(translateWitness(res)) : VerificationResult{res.getAnswer()};
}

std::unique_ptr<ChcDirectedHyperGraph> ImplicitTPA::reencodeTransitionSystem(const TransitionSystem & ts) {
    ChcSystem newSystem;

    const SymRef transitionHole = [&] {
        std::vector<SRef> args;

        for (PTRef const var : ts.getStateVars()) {
            args.push_back(logic.getSortRef(var));
        }

        for (PTRef const var : ts.getStateVars()) {
            args.push_back(logic.getSortRef(var));
        }

        return logic.declareFun(transitionHoleName, logic.getSort_bool(), args);
    }();

    newSystem.addUninterpretedPredicate(transitionHole);

    auto const stateVars = ts.getStateVars();
    auto const nextStateVars = ts.getNextStateVars();
    auto const nextNextStateVars = [&]() {
        auto res = stateVars;
        for (PTRef & var : res) {
            var = TimeMachine(logic).sendVarThroughTime(var,2);
        }
        return res;
    }();

    // transition invariant includes identity
    newSystem.addClause(
        ChcHead{UninterpretedPredicate{logic.mkUninterpFun(transitionHole, stateVars + stateVars)}},
        ChcBody{.interpretedPart = {logic.getTerm_true()}, .uninterpretedPart = {}}
    );

    // transition invariant includes Tr
    newSystem.addClause(
        ChcHead{UninterpretedPredicate{logic.mkUninterpFun(transitionHole, stateVars + nextStateVars)}},
        ChcBody{.interpretedPart = {ts.getTransition()}, .uninterpretedPart = {}}
    );

    // transition invariant is transitive
    newSystem.addClause(
        ChcHead{UninterpretedPredicate{logic.mkUninterpFun(transitionHole, stateVars + nextNextStateVars)}},
        ChcBody{.interpretedPart = {logic.getTerm_true()}, .uninterpretedPart = {
            UninterpretedPredicate{logic.mkUninterpFun(transitionHole, stateVars + nextStateVars)},
            UninterpretedPredicate{logic.mkUninterpFun(transitionHole, nextStateVars + nextNextStateVars)},
        }}
    );

    // transition invariant is safe
    newSystem.addClause(
        ChcHead{UninterpretedPredicate{logic.getTerm_false()}},
        ChcBody{
            .interpretedPart = {logic.mkAnd(ts.getInit(), TimeMachine(logic).sendFlaThroughTime(ts.getQuery(), 1))},
            .uninterpretedPart = {UninterpretedPredicate{logic.mkUninterpFun(transitionHole, stateVars + nextStateVars)}}}
    );

    // Compute a state invariant as well
    const SymRef stateHole = [&] {
        std::vector<SRef> args;

        for (PTRef const var : ts.getStateVars()) {
            args.push_back(logic.getSortRef(var));
        }

        return logic.declareFun(stateHoleName, logic.getSort_bool(), args);
    }();

    newSystem.addUninterpretedPredicate(stateHole);

    // Inv(X') <- Init(X) /\ TrInv(X, X')
    newSystem.addClause(
        ChcHead{UninterpretedPredicate(logic.mkUninterpFun(stateHole, nextStateVars))},
        ChcBody{
            .interpretedPart = {ts.getInit()},
            .uninterpretedPart = {UninterpretedPredicate(logic.mkUninterpFun(transitionHole, stateVars + nextStateVars))}
        }
    ); // TODO: This is not enough, Spacer interprets Inv as True (well, duh!)

    auto normalizedSystem = Normalizer(logic).normalize(newSystem);

    return ChcGraphBuilder(logic).buildGraph(normalizedSystem);
}

VerificationResult ImplicitTPA::runSpacer(const ChcDirectedHyperGraph & graph) {
    auto engine = Spacer(logic, options);
    return engine.solve(graph);
}

TransitionSystemVerificationResult ImplicitTPA::translateWitness(const VerificationResult & res) {
    switch (res.getAnswer()) {
        case VerificationAnswer::UNSAFE:
            return translateUnsafeWitness(res.getInvalidityWitness());
        case VerificationAnswer::SAFE:
            return translateSafeWitness(res.getValidityWitness());
        default:
            return {.answer = VerificationAnswer::UNKNOWN, .witness = 0u};
    }
}

TransitionSystemVerificationResult ImplicitTPA::translateUnsafeWitness(const InvalidityWitness & res) {
    std::size_t transitionsSeen = 0;

    // TODO: Can we assume that the derivation has no useless steps that would
    //       increase the counter?

    for (const auto & step : res.getDerivation()) {
        if (step.clauseId == EId{1}) {
            ++transitionsSeen;
        }
    }

    return {.answer = VerificationAnswer::UNSAFE, .witness = transitionsSeen};
}

TransitionSystemVerificationResult ImplicitTPA::translateSafeWitness(const ValidityWitness & res) {
    auto stateHoleInterpretation = std::optional<PTRef>{};

    // TODO: Does this work? (Assuming we get the invariant right...)

    res.run([&](const std::pair<const SymRef, PTRef> & entry) {
        if (const auto & [symbol, interpretation] = entry;
            std::string{logic.getSymName(symbol)} == stateHoleName) {
            stateHoleInterpretation = interpretation;
        }
    });

    assert(stateHoleInterpretation);

    return {.answer = VerificationAnswer::SAFE, .witness = *stateHoleInterpretation};
}

}
