// Copyright 2026 Chad Sharp and Paul Grubbs
// SPDX-License-Identifier: Apache-2.0

// GordieHowe: the verifier's phase records (util/prover_profile.h, the
// profile switch of util/diagnostics.h) on the ML-DSA-44 native proof of
// possession.
//
//   SumToTotal   in each domain's verification (PQ_PHASE gh.verify.post),
//                the outermost phases (the *.v.* keys) and other= add up to
//                total= within the lines' rounding; every Ligero phase of
//                ligero_verifier.h is recorded; the Ligero phases are at most
//                the domain's total
//
// The test turns the phase timers on before its first proof, so the binary
// holds no other test.

#include <cmath>
#include <map>
#include <sstream>
#include <string>
#include <vector>

#include "gordiehowe/examples/mldsa/mldsa_native_fixture.h"
#include "util/diagnostics.h"

namespace proofs::gordiehowe::examples::mldsa {
namespace {

// One PQ_PHASE line: its kind, field, total and keys (other= among them).
struct PhaseLine {
  std::string kind, field;
  double total = 0;
  std::map<std::string, double> keys;
};

std::vector<PhaseLine> phase_lines(const std::string &out) {
  std::vector<PhaseLine> v;
  std::istringstream in(out);
  std::string line;
  while (std::getline(in, line)) {
    std::istringstream ws(line);
    std::string tag;
    ws >> tag;
    if (tag != "PQ_PHASE") continue;
    PhaseLine p;
    ws >> p.kind >> p.field;
    std::string kv;
    while (ws >> kv) {
      const size_t eq = kv.find('=');
      if (eq == std::string::npos) continue;
      const std::string k = kv.substr(0, eq);
      const double x = std::stod(kv.substr(eq + 1));
      if (k == "total")
        p.total = x;
      else if (k != "inputs" && k != "depth")
        p.keys[k] = x;
    }
    v.push_back(p);
  }
  return v;
}

// The Ligero phases of ligero_verifier.h, without the bin./odd.v.ligero.
// prefix.
const char *const kLigeroPhases[] = {
    "transcript",   "merkle",      "subfield",     "ldt.columns",
    "ldt.response", "masks",       "rows",         "dot.encode",
    "dot.columns",  "dot.response", "quad.columns", "quad.response"};

template <class P>
class VerifyPhases : public ::testing::Test {};
TYPED_TEST_SUITE(VerifyPhases, param_sets::Profiles, param_sets::ProfileName);

TYPED_TEST(VerifyPhases, SumToTotal) {
  diagnostics::Options on = diagnostics::options();
  on.profile = true;
  diagnostics::set(on);
  ASSERT_TRUE(profiling::enabled());
  Fixture<TypeParam> f(ml_dsa::GetMlDsa44BenchmarkExample());
  auto prep = f.c->prepare(f.statement());
  SecureRandomEngine rng;
  const auto proof = prep.prove(f.witness(), rng);
  testing::internal::CaptureStdout();
  const bool ok = prep.verify(proof, nullptr, /*multithreaded=*/false);
  const std::vector<PhaseLine> lines =
      phase_lines(testing::internal::GetCapturedStdout());
  EXPECT_TRUE(ok);
  size_t domains = 0;
  for (const PhaseLine &p : lines) {
    if (p.kind != "gh.verify.post") continue;
    ++domains;
    const std::string pre =
        p.keys.count("bin.v.ligero.merkle") ? "bin.v." : "odd.v.";
    double outer = 0, ligero = 0;
    for (const auto &[k, x] : p.keys) {
      EXPECT_GE(x, 0) << k;
      if (k.find(".v.") != std::string::npos) outer += x;
      if (k.rfind(pre + "ligero.", 0) == 0) ligero += x;
    }
    ASSERT_TRUE(p.keys.count("other")) << p.field;
    // Each key and other= is printed to 1e-9 ms.
    const double rounding = 1e-9 * double(p.keys.size() + 1);
    EXPECT_NEAR(outer + p.keys.at("other"), p.total, rounding) << p.field;
    EXPECT_GE(p.keys.at("other"), -rounding) << p.field;
    EXPECT_LE(ligero, p.total + rounding) << p.field;
    for (const char *ph : kLigeroPhases)
      EXPECT_TRUE(p.keys.count(pre + "ligero." + ph)) << p.field << " " << ph;
  }
  // A and H.
  EXPECT_EQ(domains, 2u);
}

}  // namespace
}  // namespace proofs::gordiehowe::examples::mldsa
