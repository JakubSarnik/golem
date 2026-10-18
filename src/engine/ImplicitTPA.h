/*
 * Copyright (c) 2026, Martin Blicha <martin.blicha@gmail.com>
 *
 * SPDX-License-Identifier: MIT
 */
#ifndef GOLEM_IMPLICITTPA_H
#define GOLEM_IMPLICITTPA_H

#include "Options.h"
#include "TransitionSystemEngine.h"
#include <unordered_map>

namespace golem {
class ImplicitTPA : public TransitionSystemEngine {
public:
    explicit ImplicitTPA(Logic & logic, Options const & options) : logic(logic), options(options) {
        computeWitness = this->options.getOrDefault(Options::COMPUTE_WITNESS, "") == "true";
    }

    using TransitionSystemEngine::solve;
    VerificationResult solve(ChcDirectedGraph const & graph) override;
private:
    std::unique_ptr<ChcDirectedHyperGraph> reencodeTransitionSystem(TransitionSystem const & ts);
    std::unique_ptr<ChcDirectedHyperGraph> reencodeDAG(ChcDirectedGraph const & graph);

    std::vector<PTRef> detectStateVariables(ChcDirectedGraph const & graph);
    std::unordered_map<SymRef, SymRef, SymRefHash> makeInvariantSymbols(ChcDirectedGraph const & graph,
        std::vector<SRef> const & argSorts, std::string const & baseName);

    VerificationResult runSpacer(ChcDirectedHyperGraph const & graph);

    TransitionSystemVerificationResult translateWitness(VerificationResult const & res);
    TransitionSystemVerificationResult translateUnsafeWitness(InvalidityWitness const & res);
    TransitionSystemVerificationResult translateSafeWitness(ValidityWitness const & res);

    Logic & logic;
    Options options;
};
} // namespace golem




#endif //GOLEM_IMPLICITTPA_H
