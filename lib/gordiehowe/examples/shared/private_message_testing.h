// Copyright 2026 Chad Sharp and Paul Grubbs
// SPDX-License-Identifier: Apache-2.0

// GordieHowe tests: proofs of possession over private messages of several
// lengths in one relation (lib/message.h).

#ifndef PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_EXAMPLES_SHARED_PRIVATE_MESSAGE_TESTING_H_
#define PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_EXAMPLES_SHARED_PRIVATE_MESSAGE_TESTING_H_

#include <stdexcept>

#include "random/secure_random_engine.h"

namespace proofs::gordiehowe::examples::message::testing {

// Whether the verifier of the compiled system C (of system type SYS)
// accepts a proof of the statement ST and the witness W. HONEST keeps the
// prover's satisfaction check; without it a cheating prover completes its
// proof. A prover that throws counts as a rejection.
template <class Sys, class C>
bool accepts(const C &c, const typename Sys::Assignment &st,
             const typename Sys::Assignment &w, bool honest = true) {
  auto prep = c.prepare(st);
  typename Sys::ProveOptions opt;
  opt.require_satisfied = honest;
  SecureRandomEngine rng;
  try {
    return prep.verify(prep.prove(w, rng, opt));
  } catch (const std::runtime_error &) {
    return false;
  }
}

}  // namespace proofs::gordiehowe::examples::message::testing

#endif  // PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_EXAMPLES_SHARED_PRIVATE_MESSAGE_TESTING_H_
