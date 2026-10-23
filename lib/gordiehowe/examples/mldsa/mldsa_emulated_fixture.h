// Copyright 2026 Chad Sharp and Paul Grubbs
// SPDX-License-Identifier: Apache-2.0

// ML-DSA emulated tests (mldsa_emulated_test*.cc, one binary): the
// compiled fixture and helpers they share. Each test file has its own
// copy (anonymous namespace).

#ifndef PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_EXAMPLES_MLDSA_MLDSA_EMULATED_FIXTURE_H_
#define PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_EXAMPLES_MLDSA_MLDSA_EMULATED_FIXTURE_H_

#include "gordiehowe/examples/mldsa/mldsa_emulated.h"

#include <array>
#include <chrono>
#include <cstdio>
#include <cstdlib>
#include <functional>
#include <map>
#include <optional>
#include <string>
#include <vector>

#include "params/param_sets.h"
#include "params/param_sets_testing.h"
#include "gordiehowe/examples/mldsa/mldsa_emulated_testing.h"
#include "gordiehowe/examples/instances.h"
#include "gordiehowe/examples/mldsa/mldsa_openssl_testing.h"
#include "gordiehowe/examples/shared/private_message_testing.h"
#include "random/secure_random_engine.h"
#include "gtest/gtest.h"

namespace proofs::gordiehowe::examples::mldsa::emulated {
namespace {


using examples::mldsa::support::bytes_of;
using examples::mldsa::support::domain_size;
using examples::mldsa::support::Existing;
using examples::mldsa::support::ints_of;
using examples::mldsa::support::node_id;
using support::export_plan;
using support::signature_residual;
using support::w_limbs;
using support::z_limbs;

// The system on one example, compiled once; PACKING is the packing
// ablation (setup.h).
template <class P>
struct Fixture {
  using T = MLDSAEmulatedSystem<P>;
  using Sys = typename T::Sys;
  using Value = typename Sys::Value;
  Env<P> env;
  const ml_dsa::MlDsa44SignatureExample &ex;
  Existing old{ex};
  T t;
  std::shared_ptr<const typename T::Compiled> c;
  explicit Fixture(const ml_dsa::MlDsa44SignatureExample &e =
                       ml_dsa::GetMlDsa44BenchmarkExample(),
                   PackingAblation packing = PackingAblation::kNone)
      : ex(e), t(env, e.msg.size(), e.ctx.size(), packing) {
    c = t.compile();
  }
  typename T::Assignment statement() const {
    return t.statement(ex.pkey, ex.ctx);
  }
  typename T::Assignment witness() const {
    return t.witness(ex.msg, old.signature());
  }
  size_t id(const std::string &name) const { return node_id(t.cs, name); }
  // An honest proof, with every generated value recorded.
  bool prove_verify(std::map<size_t, Value> *cap = nullptr) const {
    auto prep = c->prepare(statement());
    typename Sys::ProveOptions opt;
    if (cap) opt.tamper = [cap](size_t i, Value &v) { (*cap)[i] = v; };
    SecureRandomEngine rng;
    return prep.verify(prep.prove(witness(), rng, opt));
  }
  // Whether a cheating prover's proof fails: TAMPER changes generated
  // values, W the assignment.
  bool rejects(std::function<void(size_t, Value &)> tamper,
               std::optional<typename T::Assignment> w = std::nullopt) const {
    auto prep = c->prepare(statement());
    typename Sys::ProveOptions opt;
    opt.tamper = std::move(tamper);
    opt.require_satisfied = false;
    SecureRandomEngine rng;
    try {
      return !prep.verify(prep.prove(w ? *w : witness(), rng, opt));
    } catch (const std::runtime_error &) {
      return true;
    } catch (const std::exception &e) {
      ADD_FAILURE() << "the cheating prover failed: " << e.what();
      return false;
    }
  }
};

}  // namespace
}  // namespace proofs::gordiehowe::examples::mldsa::emulated

#endif  // PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_EXAMPLES_MLDSA_MLDSA_EMULATED_FIXTURE_H_
