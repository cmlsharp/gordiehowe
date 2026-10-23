// Copyright 2026 Chad Sharp and Paul Grubbs
// SPDX-License-Identifier: Apache-2.0

// GordieHowe: the low-degree test's repetitions end to end. One domain over
// each profile field the systems use (the ML-DSA hash domain, the ML-DSA native
// and the Falcon native A domains), at each forced repetition count rho in
// {1, 2, 3} (CompileOptions::ldt_reps):
//   - the compiled tableau has rho mask rows and the report says so;
//   - single- and multi-threaded proofs verify in both modes;
//   - two proofs from one seed are equal byte for byte;
//   - a byte changed anywhere in the domain's section is rejected.
// One repetition over F_q^9 at the classical target has no tableau: the
// commit budget floor((|K| - 1)/2^113.5), about 2^8.8, is below every line
// certificate's count, and the micro domain's own rounds besides Ligero's
// meet 2^-113.5, so no fallback applies. Its compile fails (INFEASIBLE).

#include <cstddef>
#include <cstdint>
#include <exception>
#include <random>
#include <string>
#include <type_traits>
#include <vector>

#include "params/param_sets.h"
#include "gordiehowe/compiler/ligero_choice.h"
#include "gordiehowe/examples/falcon/falcon_native.h"
#include "gordiehowe/examples/instances.h"
#include "gordiehowe/examples/mldsa/mldsa_native.h"
#include "gordiehowe/threads_testing.h"
#include "gtest/gtest.h"

namespace proofs::gordiehowe {
namespace {

using namespace ::proofs::gordiehowe::examples;  // NOLINT

// One domain D over F: an anchor (a a = 0 in the circuit), N Subfield cells
// x and NF Field cells y, and an affine row over x.
template <class Sys, class F, class Prof>
struct Micro {
  Sys cs{"gh-ldt-reps-micro"};
  Ref<F, Subfield<>, Committed> a, x;
  Ref<F> y;
  size_t n, nf;
  Micro(const Prof &p, size_t count, size_t nfield) : n(count), nf(nfield) {
    auto &D = cs.domain(p, "D");
    a = D.priv(Subfield{}, "a", 1);
    assert_zero(a * a, "anchor").pin(Placement::kCircuit);
    x = D.priv(Subfield{}, "x", n);
    y = D.priv(Field{}, "y", nf);
    assert_zero(x.reindex({0}) + x.reindex({1}) - x.reindex({2}), "affine");
  }
  typename Sys::Assignment witness(const F &f) const {
    std::vector<typename F::Elt> av(1, f.zero()), xv(n), yv(nf);
    for (size_t i = 0; i < n; ++i) xv[i] = (i % 3) ? f.one() : f.zero();
    // x_0 + x_1 - x_2 = 0
    xv[0] = f.one();
    xv[1] = f.zero();
    xv[2] = f.one();
    for (size_t i = 0; i < nf; ++i) yv[i] = f.of_scalar(i % 1000 + 1);
    typename Sys::Assignment w;
    w.set(a, av).set(x, xv).set(y, yv);
    return w;
  }
};

// A seeded stream: proofs from one seed are equal byte for byte.
class Seeded : public RandomEngine {
 public:
  explicit Seeded(uint64_t seed) : g_(seed) {}
  void bytes(uint8_t *buf, size_t n) override {
    for (size_t i = 0; i < n; ++i) buf[i] = uint8_t(g_());
  }

 private:
  std::mt19937_64 g_;
};

template <class Sys, class F, class Prof>
void check_reps(const std::string &name, const F &f, const Prof &p,
                size_t infeasible = 0) {
  for (size_t reps : {size_t(1), size_t(2), size_t(3)}) {
    SCOPED_TRACE(name + " reps=" + std::to_string(reps));
    CompileOptions forced;
    forced.ldt_reps = reps;
    Micro<Sys, F, Prof> t(p, 600, 40);
    if (reps == infeasible) {
      EXPECT_THROW(compile(t.cs, CompileProfile{}, forced), std::exception);
      continue;
    }
    const auto c = compile(t.cs, CompileProfile{}, forced);
    const std::string report = c->report();
    if (reps > 1)
      EXPECT_NE(report.find("ldt_reps=" + std::to_string(reps)),
                std::string::npos)
          << report;
    else
      EXPECT_EQ(report.find("ldt_reps="), std::string::npos) << report;
    EXPECT_EQ(c->compiled_domain(0).plan().ldt_reps, reps);
    auto prep = c->prepare(typename Sys::Assignment{});
    const auto wit = t.witness(f);
    typename std::decay_t<decltype(prep)>::ProveOptions single;
    single.multithreaded = false;
    std::vector<size_t> sections;
    single.domain_bytes = &sections;
    Seeded r1(7), r2(7);
    const auto proof = prep.prove(wit, r1, single);
    EXPECT_EQ(prep.prove(wit, r2, single), proof);
    EXPECT_TRUE(prep.verify(proof));
    threads_testing::expect_threads_cross_verify(prep, wit);
    // A byte changed anywhere in the domain's section (its last bytes are
    // the Ligero proof: the responses, the openings) is rejected.
    ASSERT_EQ(sections.size(), 1u);
    const size_t end = proof.size(), begin = end - sections[0];
    for (size_t i = 0; i < 48; ++i) {
      std::vector<uint8_t> bad = proof;
      const size_t at = begin + (sections[0] - 1) * i / 47;
      bad[at] ^= 0x01;
      EXPECT_FALSE(prep.verify(bad)) << "byte " << at;
    }
  }
}

template <class P>
void check_profile() {
  const std::string pid = P::kId;
  {
    const mldsa::Env<P> env;
    auto p = domain_profile<P>(env.hf, env.rsh);
    check_reps<typename mldsa::Env<P>::Sys>(pid + ".hash", env.hf, p);
  }
  {
    const mldsa::Env<P> env;
    auto p = domain_profile<P>(env.af, env.rsa);
    check_reps<typename mldsa::Env<P>::Sys>(pid + ".ml-dsa", env.af, p);
  }
  {
    const falcon::native::Env<P> env;
    auto p = domain_profile<P>(env.af, env.rsa);
    check_reps<typename falcon::native::Env<P>::Sys>(
        pid + ".falcon", env.af, p, kPostQuantumProfile<P> ? 0 : 1);
  }
}

TEST(LdtReps, ROMParams) { check_profile<param_sets::ROMParams>(); }
TEST(LdtReps, QROMParams) { check_profile<param_sets::QROMParams>(); }

}  // namespace
}  // namespace proofs::gordiehowe
