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

VerificationResult ImplicitTPA::solve(ChcDirectedGraph const & graph) {
    if (isTrivial(graph)) {
        return solveTrivial(graph);
    }

    if (logic.hasArrays()) {
        return VerificationResult{VerificationAnswer::UNKNOWN};
    }

    if (isTransitionSystem(graph)) {
        auto ts = toTransitionSystem(graph);
        return reencodeAndSolve(std::move(ts));
    }

    if (isTransitionSystemDAG(graph) && !options.hasOption(Options::FORCE_TS)) {
        return reencodeAndSolve(graph);
    }

    // Otherwise, convert the graph to a transition system and try to solve it
    // using the transition system encoding.

    SingleLoopTransformation transformation;

    auto [ts, backtranslator] = transformation.transform(graph);
    assert(ts);

    auto res = reencodeAndSolve(std::move(ts));

    return computeWitness ? backtranslator->translate(translateWitness(res)) : VerificationResult{res.getAnswer()};
}

VerificationResult ImplicitTPA::reencodeAndSolve(std::unique_ptr<TransitionSystem> ts) {
    ChcSystem newSystem;
    std::vector<SRef> args;
    for (PTRef const var : ts->getStateVars()) {
        args.push_back(logic.getSortRef(var));
    }
    for (PTRef const var : ts->getStateVars()) {
        args.push_back(logic.getSortRef(var));
    }
    SymRef const transitionHole = logic.declareFun("implicit_tpa_tr", logic.getSort_bool(), args);
    newSystem.addUninterpretedPredicate(transitionHole);
    auto const stateVars = ts->getStateVars();
    auto const nextStateVars = ts->getNextStateVars();
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
        ChcBody{.interpretedPart = {ts->getTransition()}, .uninterpretedPart = {}}
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
            .interpretedPart = {logic.mkAnd(ts->getInit(), TimeMachine(logic).sendFlaThroughTime(ts->getQuery(), 1))},
            .uninterpretedPart = {UninterpretedPredicate{logic.mkUninterpFun(transitionHole, stateVars + nextStateVars)}}}
    );
    auto normalizedSystem = Normalizer(logic).normalize(newSystem);
    auto newGraph = ChcGraphBuilder(logic).buildGraph(normalizedSystem);
    Options options;
    auto engine = Spacer(logic, options);
    auto res = engine.solve(*newGraph);
    return res;

    // TODO: Compute the witness!
}

VerificationResult ImplicitTPA::reencodeAndSolve(ChcDirectedGraph const & graph) {
    ChcSystem newSystem;
    return VerificationResult{VerificationAnswer::UNKNOWN};
}

TransitionSystemVerificationResult ImplicitTPA::translateWitness(const VerificationResult & res) {
    // TODO: How to do this? TransitionSystemVerificationResult wants a state
    //       invariant or an unrolling level.
}

}
