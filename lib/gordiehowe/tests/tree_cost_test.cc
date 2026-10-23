// Copyright 2026 Chad Sharp and Paul Grubbs
// SPDX-License-Identifier: Apache-2.0

// GordieHowe: the per-stage cost of the packing tree's chains, a
// test-only microbench of the stage rates.
//
//   TreeCost.ForcedChain   the override (CompileOptions::forced_chains)
//                          gives the forced tree, and its proof verifies
//   TreeCost.FittedRatesPickMeasuredChains
//                          the fitted chain rates (placement_rates<F>()'s
//                          stage) at the shipped systems' region sizes
//   DISABLED_Rates         one domain over F with N Subfield cells (S0
//                          coordinates) and NF Field cells (more L), at each
//                          forced chain of the root edge S0 < K: GH_TC_REPS
//                          proofs per point (default 9) after GH_TC_WARMUPS
//                          (default 2), the chains interleaved per round.
//                          Each proof prints TC_BEGIN, the PQ_PHASE lines of
//                          its sessions (with PQ_PROFILE=1), then TC_END with
//                          its commit, prove, verify and bytes. GH_TC_FIELDS
//                          (default all) selects hash,ml-dsa,falcon,
//                          emulated; GH_TC_REQUESTS names the rate run's
//                          request scan, whose chains each field measures
//                          (from a compile under GH_RATE_REQUESTS);
//                          GH_TC_NS and GH_TC_NFS list the points' N and
//                          NF;
//                          GH_TC_ONE measures the point (N2, 0) alone;
//                          GH_TC_AFFINE adds an affine row, so each stage
//                          combines two rows (with weights), as the
//                          systems' stages do.

#include <chrono>
#include <cstdio>
#include <cstdlib>
#include <memory>
#include <random>
#include <string>
#include <type_traits>
#include <utility>
#include <vector>

#include "params/param_sets.h"
#include "gordiehowe/compiler/test_switches.h"
#include "gordiehowe/examples/falcon/falcon_emulated.h"
#include "gordiehowe/examples/falcon/falcon_native.h"
#include "gordiehowe/examples/instances.h"
#include "gordiehowe/examples/mldsa/mldsa_native.h"
#include "gordiehowe/threads_testing.h"
#include "gtest/gtest.h"
#include "params/param_sets_testing.h"
#include "random/secure_random_engine.h"

namespace proofs::gordiehowe {
namespace {

using namespace ::proofs::gordiehowe::examples;  // NOLINT

// The C++ name of F, as the rate run names a field.
template <class F>
const char *field_type() {
  if constexpr (std::is_same_v<F, Fp24_6>) {
    return "Fp24_6";
  } else if constexpr (std::is_same_v<F, MlDsaField11>) {
    return "MlDsaField11";
  } else if constexpr (std::is_same_v<F, Fp14_9>) {
    return "Fp14_9";
  } else if constexpr (std::is_same_v<F, FalconField20>) {
    return "FalconField20";
  } else if constexpr (std::is_same_v<F, Fp64G2>) {
    return "Fp64G2";
  } else if constexpr (std::is_same_v<F, Fp64G4>) {
    return "Fp64G4";
  } else if constexpr (std::is_same_v<F, GF2_128<>>) {
    return "GF2_128";
  } else if constexpr (std::is_same_v<F, GF2_256<>>) {
    return "GF2_256";
  } else {
    return "unknown";
  }
}


// One domain D over F: an anchor (a a = 0 in the circuit), N Subfield cells
// x and NF Field cells y, unchecked.
template <class Sys, class F, class Prof>
struct Micro {
  Sys cs{"gh-tree-cost-micro"};
  Ref<F, Subfield<>, Committed> a, x;
  Ref<F> y;
  size_t n, nf;
  // AFFINE adds x_0 + x_1 - x_2 = 0, a row of the domain's own (affine
  // rows) that the stages route.
  Micro(const Prof &p, size_t count, size_t nfield, bool affine = false)
      : n(count), nf(nfield) {
    auto &D = cs.domain(p, "D");
    a = D.priv(Subfield{}, "a", 1);
    assert_zero(a * a, "anchor").pin(Placement::kCircuit);
    x = D.priv(Subfield{}, "x", n);
    if (nf > 0) y = D.priv(Field{}, "y", nf);
    if (affine)
      assert_zero(x.reindex({0}) + x.reindex({1}) - x.reindex({2}), "affine");
  }
  typename Sys::Assignment witness(const F &f) const {
    std::vector<typename F::Elt> av(1, f.zero()), xv(n), yv(nf);
    for (size_t i = 0; i < n; ++i) xv[i] = (i % 3) ? f.one() : f.zero();
    for (size_t i = 0; i < nf; ++i) yv[i] = f.of_scalar(i % 1000 + 1);
    typename Sys::Assignment w;
    w.set(a, av).set(x, xv);
    if (nf > 0) w.set(y, yv);
    return w;
  }
};

std::string chain_name(const std::vector<size_t> &c) {
  std::string s;
  for (size_t d : c) s += (s.empty() ? "" : "<") + std::to_string(d);
  return s;
}

size_t env_size(const char *name, size_t dflt) {
  const char *e = std::getenv(name);
  return e != nullptr ? std::strtoull(e, nullptr, 10) : dflt;
}

// The packing-tree lines of a domain report.
std::string tree_lines(const std::string &report) {
  std::string out;
  size_t at = report.find("packing tree");
  if (at == std::string::npos) return out;
  at = report.rfind('\n', at) + 1;
  while (at < report.size()) {
    size_t end = report.find('\n', at);
    if (end == std::string::npos) end = report.size();
    const std::string line = report.substr(at, end - at);
    if (!out.empty() && line.rfind("    ", 0) != 0) break;
    out += line + "\n";
    at = end + 1;
  }
  return out;
}

bool selected(const char *what) {
  const char *e = std::getenv("GH_TC_FIELDS");
  return e == nullptr || std::string(e).find(what) != std::string::npos;
}

// The points of one field: every chain of CHAINS (edges S0 < K) at each
// (N, NF), the chains interleaved per round.
template <class Sys, class F, class Prof>
void points(const char *field, const F &f, const Prof &p,
            const std::vector<std::vector<size_t>> &chains,
            const std::vector<size_t> &ns, const std::vector<size_t> &nfs) {
  const size_t reps = env_size("GH_TC_REPS", 9);
  const size_t warm = env_size("GH_TC_WARMUPS", 2);
  for (size_t n : ns)
    for (size_t nf : nfs) {
      struct One {
        std::vector<size_t> chain;
        std::unique_ptr<Micro<Sys, F, Prof>> t;
        decltype(compile(std::declval<Sys &>())) c;
      };
      std::vector<One> sys;
      for (const auto &ch : chains) {
        CompileOptions force;
        force.forced_chains = {{{ch.front(), ch.back()}, ch}};
        One o;
        o.chain = ch;
        o.t = std::make_unique<Micro<Sys, F, Prof>>(
            p, n, nf, std::getenv("GH_TC_AFFINE") != nullptr);
        o.c = compile(o.t->cs, CompileProfile{}, force);
        std::printf("TC_TREE field=%s type=%s chain=%s n=%zu nf=%zu\n%s\n",
                    field, field_type<F>(), chain_name(ch).c_str(), n, nf,
                    tree_lines(o.c->compiled_domain(0).report()).c_str());
        sys.push_back(std::move(o));
      }
      const auto wit = sys[0].t->witness(f);
      SecureRandomEngine rng;
      for (size_t r = 0; r < warm + reps; ++r)
        for (auto &o : sys) {
          auto prep = o.c->prepare(typename Sys::Assignment{});
          std::printf("TC_BEGIN field=%s chain=%s n=%zu nf=%zu rep=%zu "
                      "warm=%d\n",
                      field, chain_name(o.chain).c_str(), n, nf, r,
                      int(r < warm));
          std::fflush(stdout);
          ProveTimes times;
          typename Sys::ProveOptions opt;
          opt.times = &times;
          const auto proof = prep.prove(wit, rng, opt);
          VerifyTimes vt;
          const bool ok = prep.verify(proof, &vt);
          EXPECT_TRUE(ok);
          std::printf("TC_END field=%s type=%s chain=%s n=%zu nf=%zu rep=%zu "
                      "warm=%d ok=%d commit=%.4f prove=%.4f verify=%.4f "
                      "bytes=%zu\n",
                      field, field_type<F>(), chain_name(o.chain).c_str(), n,
                      nf, r,
                      int(r < warm), int(ok), times.domain_commit[0],
                      times.domain_prove[0], vt.domain[0], proof.size());
          std::fflush(stdout);
        }
    }
}

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

// Every chain of FIELD under every stage-optimization switch
// (compiler/test_switches.h's stage_opts_off) gives the proof of the
// unoptimized code for one seed, and each verifies.
template <class Sys, class F, class Prof>
void same_proofs(const char *field, const F &f, const Prof &p,
                 const std::vector<std::vector<size_t>> &chains) {
  using compiler::StageOpt;
  for (const auto &ch : chains) {
    CompileOptions force;
    force.forced_chains = {{{ch.front(), ch.back()}, ch}};
    Micro<Sys, F, Prof> t(p, 300, 40, true);
    const auto c = compile(t.cs, CompileProfile{}, force);
    auto prep = c->prepare(typename Sys::Assignment{});
    const auto wit = t.witness(f);
    std::vector<uint8_t> ref;
    for (uint32_t off : {~uint32_t(0), uint32_t(0),
                         uint32_t(StageOpt::kCheck), uint32_t(StageOpt::kPack),
                         uint32_t(StageOpt::kTwist), uint32_t(StageOpt::kUnit),
                         uint32_t(StageOpt::kParts)}) {
      compiler::test_switches().stage_opts_off = off;
      Seeded rng(7);
      const auto proof = prep.prove(wit, rng);
      EXPECT_TRUE(prep.verify(proof)) << field << " " << chain_name(ch);
      if (ref.empty())
        ref = proof;
      else
        EXPECT_EQ(proof, ref) << field << " " << chain_name(ch) << " off=" << off;
    }
    compiler::test_switches().stage_opts_off = 0;
    // Single- and multi-threaded proofs verify in both modes.
    threads_testing::expect_threads_cross_verify(prep, wit);
  }
}

template <class P>
void same_proofs_profile() {
  const std::string pid = P::kId;
  {
    const mldsa::Env<P> env;
    auto p = domain_profile<P>(env.hf, env.rsh);
    const size_t k = env.hf.kBits;
    same_proofs<typename mldsa::Env<P>::Sys>(
        (pid + ".hash").c_str(), env.hf, p,
        {{16, k}, {16, 32, k}, {16, 64, k}});
  }
  if (pid == "narrow") {
    const mldsa::Env<P> env;
    auto p = domain_profile<P>(env.af, env.rsa);
    same_proofs<typename mldsa::Env<P>::Sys>((pid + ".ml-dsa").c_str(), env.af,
                                             p, {{1, 6}, {1, 2, 6}, {1, 3, 6}});
  }
  {
    const falcon::native::Env<P> env;
    auto p = domain_profile<P>(env.af, env.rsa);
    std::vector<std::vector<size_t>> ch;
    if (pid == "narrow")
      ch = {{1, 9}, {1, 3, 9}};
    else
      ch = {{1, 4, 20}, {1, 2, 4, 20}, {1, 20}};
    same_proofs<typename falcon::native::Env<P>::Sys>((pid + ".falcon").c_str(),
                                                      env.af, p, ch);
  }
}

TEST(TreeCost, OptimizationsKeepProofs) {
  same_proofs_profile<param_sets::ROMParams>();
  same_proofs_profile<param_sets::QROMParams>();
}

TEST(TreeCost, ForcedChain) {
  using P = param_sets::ROMParams;
  const mldsa::Env<P> env;
  auto p = domain_profile<P>(env.hf, env.rsh);
  using Sys = typename mldsa::Env<P>::Sys;
  for (const std::vector<size_t> &ch :
       {std::vector<size_t>{16, 128}, std::vector<size_t>{16, 32, 128},
        std::vector<size_t>{16, 64, 128}}) {
    CompileOptions force;
    force.forced_chains = {{{16, 128}, ch}};
    Micro<Sys, typename mldsa::Env<P>::HF, decltype(p)> t(p, 100, 3);
    const auto c = compile(t.cs, CompileProfile{}, force);
    const std::string rep = c->compiled_domain(0).report();
    for (size_t i = 1; i + 1 < ch.size(); ++i)
      EXPECT_NE(rep.find("GF(2^" + std::to_string(ch[i]) + ") (intermediate)"),
                std::string::npos)
          << chain_name(ch) << "\n" << rep;
    EXPECT_EQ(rep.find("(intermediate)") == std::string::npos, ch.size() == 2)
        << rep;
    auto prep = c->prepare(typename Sys::Assignment{});
    SecureRandomEngine rng;
    const auto proof = prep.prove(t.witness(env.hf), rng);
    EXPECT_TRUE(prep.verify(proof)) << chain_name(ch);
  }
}

// The cheapest measured chain of F's root edge under the fitted rates
// (placement_rates<F>()'s stage), prover plus verifier, at a domain's N
// and M.
template <class F>
std::vector<size_t> cheapest(double n, double m) {
  const auto r = param_sets::placement_rates<F>().stage;
  std::vector<size_t> best;
  double lo = 0;
  for (const auto &c : r.chains) {
    const double us = c.prover(n, m) + c.verifier(n, m);
    if (best.empty() || us < lo) {
      best = c.chain;
      lo = us;
    }
  }
  return best;
}

// The fitted rates of the optimized stages choose the chains the
// end-to-end runs measured best at the shipped systems' N and M:
// GF(2^16) < GF(2^128), F_q < F_q^9, F_q < GF(p^4) < F_q^20, and
// GF(2^16) < GF(2^64) < GF(2^256), which the D_max rule never builds (its
// chain is GF(2^16) < GF(2^256)).
TEST(TreeCost, FittedRatesPickMeasuredChains) {
  using V = std::vector<size_t>;
  // ML-DSA emulated, Falcon emulated and native, the ECDSA mDL (H at the
  // ROM parameters).
  EXPECT_EQ(cheapest<GF2_128<>>(25480, 11979), (V{16, 128}));
  EXPECT_EQ(cheapest<GF2_128<>>(25480, 21095), (V{16, 128}));
  EXPECT_EQ(cheapest<GF2_128<>>(63240, 29019), (V{16, 128}));
  // ML-DSA emulated, Falcon emulated and native (H at the QROM parameters).
  EXPECT_EQ(cheapest<GF2_256<>>(25414, 12171), (V{16, 64, 256}));
  EXPECT_EQ(cheapest<GF2_256<>>(25414, 21287), (V{16, 64, 256}));
  // Falcon native's A at the ROM and QROM parameters.
  EXPECT_EQ(cheapest<Fp14_9>(25672, 750), (V{1, 9}));
  EXPECT_EQ(cheapest<FalconField20>(28168, 894), (V{1, 4, 20}));
}

// The comma-separated sizes of NAME, or DFLT.
std::vector<size_t> env_list(const char *name, std::vector<size_t> dflt) {
  const char *e = std::getenv(name);
  if (e == nullptr) return dflt;
  std::vector<size_t> v;
  for (const char *p = e; *p != '\0';) {
    char *end = nullptr;
    v.push_back(std::strtoull(p, &end, 10));
    if (end == p) break;
    p = *end == ',' ? end + 1 : end;
  }
  return v;
}

// The chains of the root edge S0 < K the rate run's request scan
// (GH_TC_REQUESTS: lines "<field> stage c0<c1<...", from a compile under
// GH_RATE_REQUESTS) lists for field TYPE; without the file, DFLT.
std::vector<std::vector<size_t>> requested(
    const char *type, size_t s0, size_t k,
    std::vector<std::vector<size_t>> dflt) {
  const char *path = std::getenv("GH_TC_REQUESTS");
  if (path == nullptr) return dflt;
  std::vector<std::vector<size_t>> out;
  if (std::FILE *in = std::fopen(path, "r")) {
    char line[256], f[64], what[64], chain[128];
    while (std::fgets(line, sizeof(line), in) != nullptr) {
      if (std::sscanf(line, "%63s %63s %127s", f, what, chain) != 3) continue;
      if (std::string(f) != type || std::string(what) != "stage") continue;
      std::vector<size_t> c;
      for (const char *p = chain; *p != '\0';) {
        char *end = nullptr;
        c.push_back(std::strtoull(p, &end, 10));
        if (end == p) break;
        p = *end == '<' ? end + 1 : end;
      }
      if (c.size() < 2 || c.front() != s0 || c.back() != k) {
        std::printf("TC_UNSUPPORTED field=%s chain=%s\n", type, chain);
        continue;
      }
      bool seen = false;
      for (const auto &o : out) seen = seen || o == c;
      if (!seen) out.push_back(c);
    }
    std::fclose(in);
  }
  return out;
}

TEST(TreeCost, DISABLED_Rates) {
  // GH_TC_ONE: the single point (N2, 0). GH_TC_NS and GH_TC_NFS: the
  // instance counts and the Field cells (default N1, N2 and 0, NF).
  const bool one = std::getenv("GH_TC_ONE") != nullptr;
  std::vector<size_t> ns = env_list(
      "GH_TC_NS", {env_size("GH_TC_N1", 16384), env_size("GH_TC_N2", 65536)});
  std::vector<size_t> nfs =
      env_list("GH_TC_NFS", {0, env_size("GH_TC_NF", 65536)});
  if (one) {
    ns = {ns.back()};
    nfs = {0};
  }
  param_sets::with_profile([&](auto prof) {
    using P = decltype(prof);
    const std::string pid = P::kId;
    if (selected("hash")) {
      const mldsa::Env<P> env;
      using F = typename mldsa::Env<P>::HF;
      auto p = domain_profile<P>(env.hf, env.rsh);
      const size_t k = env.hf.kBits;
      const auto ch = requested(field_type<F>(), 16, k,
                                {{16, k}, {16, 32, k}, {16, 64, k}});
      if (!ch.empty())
        points<typename mldsa::Env<P>::Sys>((pid + ".hash").c_str(), env.hf,
                                            p, ch, ns, nfs);
    }
    if (selected("ml-dsa")) {
      const mldsa::Env<P> env;
      using F = typename mldsa::Env<P>::AF;
      auto p = domain_profile<P>(env.af, env.rsa);
      const size_t k = field_degree<F>();
      const auto ch = requested(field_type<F>(), 1, k,
                                pid == "narrow"
                                    ? std::vector<std::vector<size_t>>{
                                          {1, 6}, {1, 2, 6}, {1, 3, 6}}
                                    : std::vector<std::vector<size_t>>{});
      if (!ch.empty())
        points<typename mldsa::Env<P>::Sys>((pid + ".ml-dsa").c_str(), env.af,
                                            p, ch, ns, nfs);
    }
    if (selected("falcon")) {
      const falcon::native::Env<P> env;
      using F = typename falcon::native::Env<P>::AF;
      auto p = domain_profile<P>(env.af, env.rsa);
      const size_t k = field_degree<F>();
      std::vector<std::vector<size_t>> dflt;
      if (pid == "narrow")
        dflt = {{1, 9}, {1, 3, 9}};
      else
        dflt = {{1, 4, 20}, {1, 2, 4, 20}, {1, 20}};
      const auto ch = requested(field_type<F>(), 1, k, dflt);
      if (!ch.empty())
        points<typename falcon::native::Env<P>::Sys>(
            (pid + ".falcon").c_str(), env.af, p, ch, ns, nfs);
    }
    if (selected("emulated")) {
      const falcon::emulated::Env<P> env;
      using F = typename falcon::emulated::Env<P>::AF;
      auto p = domain_profile<P>(env.af, env.rsa.factory());
      const size_t k = field_degree<F>();
      const auto ch = requested(field_type<F>(), 1, k, {});
      if (!ch.empty())
        points<typename falcon::emulated::Env<P>::Sys>(
            (pid + ".emulated").c_str(), env.af, p, ch, ns, nfs);
    }
  });
}

}  // namespace
}  // namespace proofs::gordiehowe
