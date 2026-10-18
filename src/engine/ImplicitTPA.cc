/*
 * Copyright (c) 2026, Martin Blicha <martin.blicha@gmail.com>
 *
 * SPDX-License-Identifier: MIT
 */

#include "ImplicitTPA.h"

#include "Common.h"
#include "Spacer.h"

#include <TransformationUtils.h>
#include <TermUtils.h>
#include <utils/StdUtils.h>

#include "graph/ChcGraphBuilder.h"
#include "transformers/SingleLoopTransformation.h"

#include <set>
#include <iterator>
#include <algorithm>
#include <ranges>

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

        if (options.hasOption(Options::COMPUTE_WITNESS)) {
            return translateTransitionSystemResult(translateWitness(res), graph, *ts);
        } else {
            return res;
        }
    }

    if (isTransitionSystemDAG(graph) && !options.hasOption(Options::FORCE_TS)) {
        auto newGraph = reencodeDAG(graph);

        assert(newGraph);
        auto res = runSpacer(*newGraph);

        // TODO: Witness reconstruction here is much more complicated. We need
        //       to translate a derivation of false in the new non-linear
        //       system to a derivation of false in the original linear system,
        //       and a interpretation of the new predicates into an
        //       interpretation of the original predicates.
        return res;
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

std::unique_ptr<ChcDirectedHyperGraph> ImplicitTPA::reencodeTransitionSystem(TransitionSystem const & ts) {
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
    );

    // P(X) <- Inv(X)
    // TODO: This is not enough for inductiveness, but it should establish a
    //       safe invariant.
    newSystem.addClause(
        ChcHead{UninterpretedPredicate{logic.getTerm_false()}},
        ChcBody{
            .interpretedPart = {ts.getQuery()},
            .uninterpretedPart = {UninterpretedPredicate(logic.mkUninterpFun(stateHole, stateVars))}
        }
    );

    auto normalizedSystem = Normalizer(logic).normalize(newSystem);

    return ChcGraphBuilder(logic).buildGraph(normalizedSystem);
}

std::unique_ptr<ChcDirectedHyperGraph> ImplicitTPA::reencodeDAG(ChcDirectedGraph const & graph){
    // We assume that the passed graph represents a transition system DAG
    // (except for self-loops).
    //
    // The graph has the following nodes:
    //   - There is a single entry node ⊤.
    //   - There is a single exit node ⊥.
    //   - We denote by S₁, ..., Sₙ the inner nodes of the system, i.e. all
    //     the nodes except ⊤ and ⊥. We know (from isTransitionSystemDAG) that
    //     there is at least one such node.
    //
    // Each node Sₖ represents a transition system with its own transition
    // function.
    //
    // There are edges of the following kinds:
    //   - Each inner node Sₖ has a self-loop labelled by Transₖ(X, X').
    //   - Each edge ⊤ → Sₖ is labelled by Initₖ(X'), the initial formula of
    //     the system Sₖ.
    //   - Each edge Sₖ → ⊥ is labelled by Errorₖ(X), the error formula of
    //     the system Sₖ.
    //   - Each edge Sₖ → Sₗ is Labelled by Switchₖₗ(X, X'). This formula
    //     is a combined "error" (target) formula for Sₖ and an initial formula
    //     for Sₗ. Whenever the system Sₖ reaches a state X satisfying
    //     Switchₖₗ(X, X') for some X', the system Sₗ is initiated in the state
    //     X = unprime(X').
    //
    // Our goal is to produce a new, non-linear CHC system that encodes this
    // composition of systems in a way that the new system is satisfiable
    // whenever the original graph can reach ⊥ from ⊤.

    const auto sendVarsThroughTime = [&](std::vector<PTRef> const & vars, int steps) {
        const auto tm = TimeMachine{logic};

        auto res = std::vector<PTRef>{};

        for (const auto var : vars) {
            res.emplace_back(tm.sendVarThroughTime(var, steps));
        }

        return res;
    };

    const auto stateVars = detectStateVariables(graph);
    const auto nextStateVars = sendVarsThroughTime(stateVars, 1);
    const auto nextNextStateVars = sendVarsThroughTime(stateVars, 2);

    const auto entry = graph.getEntry();
    const auto exit = graph.getExit();

    const auto makeStateInvariantSymbols = [&] {
        // *(X)
        auto argSorts = std::vector<SRef>{};

        for (const auto var : stateVars) {
            argSorts.push_back(logic.getSortRef(var));
        }

        return makeInvariantSymbols(graph, argSorts, stateHoleName);
    };

    const auto makeTransitionInvariantSymbols = [&] {
        // *(X, X')
        auto argSorts = std::vector<SRef>{};

        for (const auto var : stateVars) {
            argSorts.push_back(logic.getSortRef(var));
        }

        for (const auto var : stateVars) {
            argSorts.push_back(logic.getSortRef(var));
        }

        return makeInvariantSymbols(graph, argSorts, transitionHoleName);
    };

    // Maps a node Sₖ in the graph to its uninterpreted predicate Invₖ(X).
    const auto stateInvariantMap = makeStateInvariantSymbols();
    // Maps a node Sₖ in the graph to its uninterpreted predicate Transₖ(X, X').
    const auto transitionInvariantMap = makeTransitionInvariantSymbols();

    //const auto adjList = AdjacencyListsGraphRepresentation::from(graph);
    auto newSystem = ChcSystem{};

    for (const auto sym : stateInvariantMap | std::views::values) {
        newSystem.addUninterpretedPredicate(sym);
    }

    for (const auto sym : transitionInvariantMap | std::views::values) {
        newSystem.addUninterpretedPredicate(sym);
    }

    // TODO

    const auto normalizedSystem = Normalizer(logic).normalize(newSystem);

    return ChcGraphBuilder(logic).buildGraph(normalizedSystem);
}

std::vector<PTRef> ImplicitTPA::detectStateVariables(ChcDirectedGraph const & graph) {
    auto stateVars = std::set<PTRef>{};
    const auto tm = TimeMachine{logic};

    graph.forEachEdge([&](DirectedEdge const & edge) {
        auto edgeVars = getVariablesFromEdge(logic, graph, edge.id);
        std::ranges::copy(edgeVars.stateVars, std::inserter(stateVars, stateVars.end()));

        for (const auto var : edgeVars.nextStateVars) {
            stateVars.insert(tm.getVarVersionZero(tm.getUnversioned(var)));
        }
    });

    // TODO: Do we need the variables ordered somehow?
    return { stateVars.begin(), stateVars.end() };
}
std::unordered_map<SymRef, SymRef, SymRefHash> ImplicitTPA::makeInvariantSymbols(ChcDirectedGraph const & graph,
    std::vector<SRef> const & argSorts, std::string const & baseName) {
    auto map = std::unordered_map<SymRef, SymRef, SymRefHash>{};

    int i = 0;

    for (const auto v : graph.getVertices()) {
        if (v == graph.getEntry() || v == graph.getExit()) {
            continue;
        }

        map.emplace(v, logic.declareFun(baseName + "_" + std::to_string(i++),
            logic.getSort_bool(), argSorts));
    }

    return map;
}

VerificationResult ImplicitTPA::runSpacer(ChcDirectedHyperGraph const & graph) {
    auto engine = Spacer(logic, options);
    return engine.solve(graph);
}

TransitionSystemVerificationResult ImplicitTPA::translateWitness(VerificationResult const & res) {
    switch (res.getAnswer()) {
        case VerificationAnswer::UNSAFE:
            return translateUnsafeWitness(res.getInvalidityWitness());
        case VerificationAnswer::SAFE:
            return translateSafeWitness(res.getValidityWitness());
        default:
            return {.answer = VerificationAnswer::UNKNOWN, .witness = 0u};
    }
}

TransitionSystemVerificationResult ImplicitTPA::translateUnsafeWitness(InvalidityWitness const & res) {
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

TransitionSystemVerificationResult ImplicitTPA::translateSafeWitness(ValidityWitness const & res) {
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
