/*
 * Copyright (c) 2026, Martin Blicha <martin.blicha@gmail.com>
 *
 * SPDX-License-Identifier: MIT
 */
#ifndef GOLEM_IMPLICITTPA_H
#define GOLEM_IMPLICITTPA_H

#include "Options.h"
#include "TransitionSystemEngine.h"

namespace golem {
class ImplicitTPA : public TransitionSystemEngine {
public:
    explicit ImplicitTPA(Logic & logic, Options const & options) : logic(logic), options(options) {}

    using TransitionSystemEngine::solve;
    VerificationResult solve(ChcDirectedGraph const & graph) override;
private:
    VerificationResult reencodeAndSolve(std::unique_ptr<TransitionSystem> ts);
    VerificationResult reencodeAndSolve(ChcDirectedGraph const & graph);

    Logic & logic;
    Options options;
};
} // namespace golem




#endif //GOLEM_IMPLICITTPA_H
