// Copyright 2026 Chad Sharp and Paul Grubbs
// SPDX-License-Identifier: Apache-2.0

// GordieHowe over F_p256: the domain profile, list-radius tableaux and the
// timing helpers of the F_p256 tests and benches (gordiehowe_p256_test,
// p256_scalar_mult_test).
//
// profile() is Longfellow v7's Ligero over F_p256 (kLigeroRatev7 and
// kLigeroNreqv7: rate 7 and 132 opened columns at unique decoding), the field
// prime (DomainProfile::prime = kField, the designated subfield is the
// field); list_profile() is the field's default (domain_profile.h), at
// which the compiler chooses the list-radius parameters, and
// compile_at_list_radius builds and compiles a system at it.

#ifndef PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_EXAMPLES_P256_P256_TESTING_H_
#define PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_EXAMPLES_P256_P256_TESTING_H_

#include <algorithm>
#include <array>
#include <chrono>
#include <cstddef>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <memory>
#include <random>
#include <string>
#include <utility>
#include <vector>

#include "bench/timing.h"
#include "circuits/mdoc/mdoc_zk.h"
#include "algebra/reed_solomon_p256.h"
#include "params/param_sets.h"
#include "ec/p256.h"
#include "gordiehowe/examples/shared/domain_profile.h"
#include "gordiehowe/instances.h"
#include "gordiehowe/system.h"
#include "gtest/gtest.h"
#include "random/secure_random_engine.h"

namespace proofs::gordiehowe::examples::mdoc::p256_testing {

using P = param_sets::ROMParams;
using F = P::EcdsaField;
using Elt = F::Elt;
using Vec = std::vector<Elt>;
using RS = P256ReedSolomon;
using RSF = RS::Factory;
using Sys = ConstraintSystem<P::ProtocolHash, F>;
using Assignment = Sys::Assignment;
using ProveOptions = Sys::ProveOptions;
using Compiled = BasicCompiledSystem<instances::SetP256>;
using Profile = DomainProfile<F, RSF, P::ProtocolHash>;
static_assert(std::is_same_v<RSF, instances::RsP256>);

inline const F &fp() { return p256_base; }
inline const RS &rs() {
  static const RS *r = new RS;
  return *r;
}

// Original Ligero at Longfellow v7's rate and opened columns.
inline Profile profile() {
  Profile p;
  p.f = &fp();
  p.rsf = &rs().factory();
  p.rates = param_sets::placement_rates<F>();
  p.field_name = "F_p256";
  p.rate = kLigeroRatev7;
  p.nreq = kLigeroNreqv7;
  p.has_subfield = true;
  p.prime = Space::kField;
  return p;
}
// List-radius Ligero at the compiler's choice (domain_profile.h).
inline Profile list_profile() { return domain_profile<P>(fp(), rs().factory()); }

// BUILD(profile) returns a holder with the system as its member s; it is
// built at list_profile() and compiled with OPTIONS.
template <class Build>
auto compile_at_list_radius(Build build, const CompileOptions &options = {}) {
  auto h = build(list_profile());
  auto c = compile(h->cs, CompileProfile{}, options);
  return std::make_pair(std::move(h), std::move(c));
}

inline Vec random_vec(size_t n, std::mt19937_64 &g) {
  Vec v(n);
  for (auto &x : v) {
    std::array<uint64_t, 4> a = {g(), g(), g(), g() >> 1};
    x = fp().of_scalar_field(a);
  }
  return v;
}

// ------------------------------------------------------------- timing --
// GH_P256_REPS proofs per point (default 5); medians in milliseconds.

using bench::Clock;
using bench::ms_since;
using bench::median;
inline size_t reps() {
  const char *e = std::getenv("GH_P256_REPS");
  return e != nullptr ? std::strtoull(e, nullptr, 10) : 5;
}

struct Measured {
  double witness = 0, commit = 0, prove = 0, verify = 0;
  size_t bytes = 0;
};
// Medians over reps() proofs of WITNESS against STATEMENT; every proof must
// verify.
inline Measured measure(const Compiled &c, const Assignment &statement,
                        const Assignment &witness) {
  auto prep = c.prepare(statement);
  SecureRandomEngine rng;
  std::vector<double> wt, cm, pr, vf;
  Measured m;
  for (size_t i = 0; i < reps(); ++i) {
    ProveTimes times;
    ProveOptions opt;
    opt.times = &times;
    const auto proof = prep.prove(witness, rng, opt);
    const auto t0 = Clock::now();
    const bool ok = prep.verify(proof);
    vf.push_back(ms_since(t0));
    EXPECT_TRUE(ok);
    wt.push_back(times.witness);
    cm.push_back(times.commit);
    pr.push_back(times.prove);
    m.bytes = proof.size();
  }
  m.witness = median(wt);
  m.commit = median(cm);
  m.prove = median(pr);
  m.verify = median(vf);
  return m;
}

// The tableau and circuit of a compiled system's one domain.
inline std::string tableau(const Compiled &c) {
  const DomainPlan p = c.compiled_domain(0).plan();
  char buf[256];
  std::snprintf(buf, sizeof(buf),
                "nw=%zu nq=%zu N=%zu k=%zu t=%zu nrow=%zu block_enc=%zu "
                "layers=%zu quad_terms=%zu",
                p.nw, p.nq, p.N, p.k, p.t, p.nrow, p.block_enc, p.layers,
                p.quad_terms);
  return buf;
}

// One line: TAG WHAT size=SIZE, the medians, the proof bytes, the tableau.
inline void report(const char *tag, const std::string &what, size_t size,
                   const Compiled &c, const Measured &m) {
  std::printf("%s %s size=%zu witness=%.3f commit=%.3f prove=%.3f "
              "verify=%.3f bytes=%zu %s\n",
              tag, what.c_str(), size, m.witness, m.commit, m.prove, m.verify,
              m.bytes, tableau(c).c_str());
  std::fflush(stdout);
}

}  // namespace proofs::gordiehowe::examples::mdoc::p256_testing

#endif  // PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_EXAMPLES_P256_P256_TESTING_H_
