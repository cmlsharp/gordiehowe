// Copyright 2026 Chad Sharp and Paul Grubbs
// SPDX-License-Identifier: Apache-2.0

// GordieHowe: an untimed smoke check of the per-chunk MAC ablation
// (CompileProfile::unsound_per_chunk_mac, compiler/mac.h) on the systems
// the bench compares it in, at the ROM parameters: the ECDSA mDL (the
// list-radius build, 1 attribute), the ML-DSA-44 proof of possession over
// Goldilocks^2 (emulated), and the post-quantum mDL at 1 attribute in both
// arms of A (F_q and Goldilocks^2). Each system compiles with and without
// the ablation, and one honest proof of each verifies. The tests print the
// MAC's report line, the proof bytes of both and each domain's plan
// (GH_PER_CHUNK lines). Not a benchmark: the tests are DISABLED_, run them
// with --gtest_also_run_disabled_tests.

#include <sys/resource.h>

#include <chrono>
#include <cstddef>
#include <cstdio>
#include <memory>
#include <sstream>
#include <string>
#include <vector>

#include "circuits/tests/pq/ml_dsa/ml_dsa_44_examples.h"
#include "gordiehowe/examples/mdoc/mdoc_testing.h"
#include "gordiehowe/examples/mldsa/mldsa_emulated.h"
#include "gordiehowe/examples/mldsa/mldsa_emulated_testing.h"
#include "gordiehowe/examples/mldsa/mldsa_native_testing.h"
#include "gordiehowe/examples/pq_mdoc/pq_mdoc_testing.h"
#include "gordiehowe/examples/shared/setup.h"
#include "gtest/gtest.h"
#include "params/param_sets.h"
#include "random/secure_random_engine.h"

namespace proofs::gordiehowe::examples {
namespace {

using param_sets::ROMParams;

// The report's MAC lines.
std::string mac_lines(const std::string &report) {
  std::istringstream in(report);
  std::string line, out;
  while (std::getline(in, line))
    if (line.find("MAC mac") != std::string::npos) out += line + "\n";
  return out;
}

// Prints C's MAC lines and each domain's plan under the label WHAT.
template <class C>
void print_plan(const std::string &what, const C &c) {
  std::printf("GH_PER_CHUNK %s mac:\n%s", what.c_str(),
              mac_lines(c.report()).c_str());
  for (size_t d = 0; d < c.num_domains(); ++d) {
    const DomainPlan p = c.compiled_domain(d).plan();
    std::printf("GH_PER_CHUNK %s domain=%s nw=%zu nq=%zu nrow=%zu "
                "layers=%zu wires=%zu ninputs=%zu\n",
                what.c_str(), c.domain(d).name.c_str(), p.nw, p.nq, p.nrow,
                p.layers, p.wires, p.ninputs);
  }
}

// Milliseconds since T0.
double ms_since(std::chrono::steady_clock::time_point t0) {
  return std::chrono::duration<double, std::milli>(
             std::chrono::steady_clock::now() - t0)
      .count();
}

// One honest proof of the statement ST and witness W under C: its bytes,
// and whether it verifies. Prints the prove and verify wall times (one
// untimed execution, prepare outside both) and the process's peak RSS so
// far, under the label WHAT.
template <class C, class A>
size_t prove_once(const std::string &what, const C &c, const A &st,
                  const A &w, bool &ok) {
  auto prep = c.prepare(st);
  SecureRandomEngine rng;
  auto t0 = std::chrono::steady_clock::now();
  const auto proof = prep.prove(w, rng);
  const double prove_ms = ms_since(t0);
  t0 = std::chrono::steady_clock::now();
  ok = prep.verify(proof);
  const double verify_ms = ms_since(t0);
  rusage ru{};
  getrusage(RUSAGE_SELF, &ru);
  std::printf("GH_PER_CHUNK %s prove_ms=%.0f verify_ms=%.0f "
              "peak_rss_mb=%ld\n",
              what.c_str(), prove_ms, verify_ms, ru.ru_maxrss / 1024);
  return proof.size();
}

void report(const std::string &what, size_t full, size_t per_chunk) {
  std::printf("GH_PER_CHUNK %s proof_bytes full=%zu per_chunk=%zu\n",
              what.c_str(), full, per_chunk);
}

BuildOptions per_chunk() {
  BuildOptions o;
  o.unsound_per_chunk_mac = true;
  return o;
}

TEST(PerChunkMac, DISABLED_EcdsaMdl) {
  namespace m = mdoc::full;
  const m::Instance x = m::instance_of(m::bench_case(3, 1));
  size_t bytes[2];
  for (bool abl : {false, true}) {
    m::MdocSystem sys(m::list_h_profile(), m::list_a_profile(), 1,
                      mdoc::kBlocks, true, abl ? per_chunk() : BuildOptions{});
    const auto &c = sys.compiled();
    print_plan(abl ? "ecdsa-mdl per-chunk" : "ecdsa-mdl full", c);
    bool ok = false;
    bytes[abl] = prove_once(abl ? "ecdsa-mdl per-chunk" : "ecdsa-mdl full",
                            c, sys.statement(x.statement),
                            sys.witness(x.data), ok);
    EXPECT_TRUE(ok) << (abl ? "per-chunk" : "full");
  }
  report("ecdsa-mdl", bytes[0], bytes[1]);
}

TEST(PerChunkMac, DISABLED_MlDsaEmulated) {
  namespace e = mldsa::emulated;
  e::Env<ROMParams> env;
  const auto &ex = ml_dsa::GetMlDsa44BenchmarkExample();
  const mldsa::support::Existing old{ex};
  const auto sig = old.signature();
  size_t bytes[2];
  for (bool abl : {false, true}) {
    e::MLDSAEmulatedSystem<ROMParams> sys(env, ex.msg.size(), ex.ctx.size(),
                                          mldsa::PackingAblation::kNone,
                                          abl ? per_chunk() : BuildOptions{});
    const auto c = sys.compile();
    print_plan(abl ? "mldsa-emulated per-chunk" : "mldsa-emulated full", *c);
    bool ok = false;
    bytes[abl] = prove_once(
        abl ? "mldsa-emulated per-chunk" : "mldsa-emulated full", *c,
        sys.statement(ex.pkey, ex.ctx),
                            sys.witness(ex.msg, sig), ok);
    EXPECT_TRUE(ok) << (abl ? "per-chunk" : "full");
  }
  report("mldsa-emulated", bytes[0], bytes[1]);
}

// The post-quantum mDL of ARM at 1 attribute, as PqMdocSystem builds it,
// with the ablation in its compile profile when PER_CHUNK.
template <class Arm>
void expect_pq_mdoc(const std::string &what) {
  namespace q = pq_mdoc;
  using S = q::PqMdocSystem<ROMParams, Arm>;
  using Profiles = typename S::Profiles;
  using Sys = typename S::Sys;
  const typename Profiles::E env;
  const q::Instance x = q::bench_instance(1);
  const size_t tbs = x.statement.device_tbs.size();
  size_t bytes[2];
  // The ablation first, so that the peak RSS it prints is its own.
  for (bool abl : {true, false}) {
    const q::PqMdocConfig cfg;
    CompileProfile p = S::compile_profile(cfg);
    p.unsound_per_chunk_mac = abl;
    CompileOptions options;
    options.placement_force = q::bit_checks_force(cfg.bit_checks);
    auto rel = q::pq_mdoc<Arm, Sys>(
        p, S::name(cfg), S::h_profile(env, cfg),
        Profiles::a_profile(env, cfg.a_unpacked_s0), 1, tbs,
        cfg.device_signature, options);
    auto &typed = rel.template typed<Sys>();
    const auto c = typed.compiled_ptr();
    print_plan(what + (abl ? " per-chunk" : " full"), *c);
    bool ok = false;
    bytes[abl] =
        prove_once(what + (abl ? " per-chunk" : " full"), *c,
                   typed.statement(q::pq_mdoc_statement(x.statement)),
                   typed.witness(q::pq_mdoc_witness(x.data)), ok);
    EXPECT_TRUE(ok) << what << (abl ? " per-chunk" : " full");
  }
  report(what, bytes[0], bytes[1]);
}

TEST(PerChunkMac, DISABLED_PqMdocFq) {
  expect_pq_mdoc<pq_mdoc::FqArm>("pq-mdoc-fq");
}
TEST(PerChunkMac, DISABLED_PqMdocGoldilocks) {
  expect_pq_mdoc<pq_mdoc::GoldilocksArm>("pq-mdoc-goldilocks");
}

}  // namespace
}  // namespace proofs::gordiehowe::examples
