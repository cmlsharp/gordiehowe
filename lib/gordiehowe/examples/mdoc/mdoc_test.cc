// Copyright 2026 Chad Sharp and Paul Grubbs
// SPDX-License-Identifier: Apache-2.0

// GordieHowe: plain mdoc in one proof (mdoc.h). Domain H = GF(2^128)
// hashes, domain A = F_p256 verifies the signatures, and the MAC equality
// of e, dpkx and dpky joins them.
//
// Honest proofs verify on Longfellow's doc 3 with 1, 2 and 4 attributes,
// and on a re-signed doc 3 whose keys the test holds. A witness whose
// domain A values differ from domain H's in exactly one of e, dpkx and
// dpky (each domain valid on its own) is rejected.
//
// The device-signature ablation (DEVICE_SIGNATURE false: no device ECDSA
// verification and no dpkx, dpky crossing) proves doc 3, rejects a tampered
// issuer signature and accepts a tampered device signature.
//
// The bench's MAC and mask-test ablations (ablation_testing.h; Mdoc.
// MacAblation, Mdoc.MaskTestAblation) prove doc 3 and reject a changed
// proof and a tampered issuer signature.
//
// The build the gh-mdoc bench case times (MdocBenched: list radius, doc 3,
// 1 attribute, 40 blocks) rejects a wrong attribute value, a date outside
// the validity, a changed, absent or misdirected device signature, a
// flipped proof bit and a truncated or extended proof.
//
// At Vega's 1920-byte MSO bound (kVegaBlocks, 31 SHA-256 blocks) in place
// of v7's 40, the list-radius build proves doc 3 and rejects a tampered
// proof.
//
// mdoc_bench (mdoc_bench.cc) holds the benches, the Vega-bound report and
// the plan export.

#include <algorithm>
#include <chrono>
#include <cstddef>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <fstream>
#include <memory>
#include <random>
#include <string>
#include <vector>

#include "gordiehowe/examples/shared/ablation_testing.h"
#include "gordiehowe/examples/mdoc/mdoc_fixture.h"
#include "gordiehowe/compiler/plan_export.h"
#include "gordiehowe/compiler/plan_program.h"
#include "gtest/gtest.h"
#include "random/secure_random_engine.h"

namespace proofs::gordiehowe::examples::mdoc::full {
namespace {

// At v7's Ligero, once per attribute count.
Built &compiled(size_t n) {
  static std::vector<std::unique_ptr<Built>> cache(5);
  if (!cache.at(n))
    cache[n] = std::make_unique<Built>(build(h_profile(), a_profile(), n));
  return *cache[n];
}

// Whether the proof of X verifies (the prover does not require X to
// satisfy the system). A generator that cannot run on X (no witness value
// exists) counts as a rejection, reported in WHY.
bool accepts(const Built &b, const Instance &x, std::string *why = nullptr) {
  auto prep = b.c->prepare(b.sys->statement(x.statement));
  Sys::ProveOptions opt;
  opt.require_satisfied = false;
  SecureRandomEngine rng;
  try {
    return prep.verify(prep.prove(b.sys->witness(x.data), rng, opt));
  } catch (const std::exception &e) {
    if (why != nullptr) *why = e.what();
    return false;
  }
}

void expect_honest(size_t n) {
  const Instance x = instance_of(bench_case(3, n));
  Built &b = compiled(n);
  auto prep = b.c->prepare(b.sys->statement(x.statement));
  SecureRandomEngine rng;
  const auto proof = prep.prove(b.sys->witness(x.data), rng);
  EXPECT_TRUE(prep.verify(proof)) << n << " attributes";
}

TEST(Mdoc, HonestOneAttribute) { expect_honest(1); }
TEST(Mdoc, HonestTwoAttributes) { expect_honest(2); }
TEST(Mdoc, HonestFourAttributes) { expect_honest(4); }

// Domain H's digest is the issuer's ECDSA message: Longfellow's
// signature witness reads the same e.
TEST(Mdoc, VectorDigestIsTheSignedOne) {
  const Instance x = instance_of(bench_case(3, 1));
  const MdocTests &t = mdoc_tests[3];
  ParsedMdoc pm;
  ASSERT_EQ(pm.parse_device_response(t.mdoc_size, t.mdoc), MDOC_PROVER_SUCCESS);
  const Fp256Nat e = nat_from_hash<Fp256Nat>(pm.tagged_mso_bytes_.data(),
                                             pm.tagged_mso_bytes_.size());
  EXPECT_EQ(digest_limbs(x.data.e), limbs_of(e));
}

// Each domain valid on its own, the two differing in one crossing value.
TEST(Mdoc, CrossingMismatchRejected) {
  Built &b = compiled(1);
  const Instance base = instance_of(bench_case(3, 1));
  std::mt19937_64 g(1135);

  // Re-signed, both domains agreeing: accepted.
  {
    std::string why;
    EXPECT_TRUE(accepts(b, resigned(base, agreeing(g), g), &why))
        << "re-signed honest: " << why;
  }
  // e: the issuer signs e with one bit flipped, and domain A
  // reads that e; H's digest is the MSO's.
  {
    Resign r = agreeing(g);
    r.other_digest = true;
    std::string why;
    EXPECT_FALSE(accepts(b, resigned(base, r, g), &why)) << "e";
    std::printf("mismatch e: %s\n", why.empty() ? "verifier rejects" : why.c_str());
  }
  // dpky: the MSO holds Q = (x, y), the device signs with -Q = (x, -y).
  {
    Resign r = agreeing(g);
    r.device_d = negate_scalar(r.device_d);
    r.device_q = gmult(r.device_d);
    ASSERT_EQ(be(r.device_q.x), r.mso_x);
    ASSERT_NE(be(r.device_q.y), r.mso_y);
    std::string why;
    EXPECT_FALSE(accepts(b, resigned(base, r, g), &why)) << "dpky";
    std::printf("mismatch dpky: %s\n",
                why.empty() ? "verifier rejects" : why.c_str());
  }
  // dpkx: the MSO holds (x', y), the device signs with Q = (x, y), where
  // (x', y) is the curve's other point of ordinate y.
  {
    Resign r;
    AElt x2;
    do {
      r = agreeing(g);
    } while (!other_x(r.device_q.x, x2));
    r.mso_x = be(x2);
    ASSERT_NE(r.mso_x, be(r.device_q.x));
    std::string why;
    EXPECT_FALSE(accepts(b, resigned(base, r, g), &why)) << "dpkx";
    std::printf("mismatch dpkx: %s\n",
                why.empty() ? "verifier rejects" : why.c_str());
  }
}

// The bench's MAC and mask-test ablations (ablation_testing.h) of the
// list-radius build at 1 attribute, built as its report_bench worker
// builds them: doc 3's honest proof verifies; a proof with a byte changed
// (start, middle, end) and the issuer's signature with a byte of s changed
// are rejected. The MAC ablation's report names the dropped equalities;
// the mask-test ablation's domains have untested masks, the full system's
// repetitions and at least its opened columns.
void expect_ablation(const std::string &which) {
  const Instance x = instance_of(bench_case(3, 1));
  const Built full = build_list_radius(1);
  auto t0 = Clock::now();
  const auto bp = ablation::build(
      [](const examples::BuildOptions &o) {
        return std::make_unique<Built>(
            build_list_radius(1, examples::mdoc::kBlocks, true, o));
      },
      [](const Built &v) -> const Compiled & { return *v.c; }, t0, which);
  const Built &b = *bp;
  if (which == "nomac") {
    EXPECT_NE(b.c->report().find("MAC ablation: dropped"), std::string::npos);
  } else {
    for (size_t d = 0; d < b.c->num_domains(); ++d) {
      const DomainPlan p = b.c->compiled_domain(d).plan();
      const DomainPlan q = full.c->compiled_domain(d).plan();
      EXPECT_FALSE(p.split) << b.c->domain(d).name;
      EXPECT_EQ(p.ldt_reps, q.ldt_reps) << b.c->domain(d).name;
      EXPECT_GE(p.t, q.t) << b.c->domain(d).name;
      std::printf("GH_ABLATION untested mdoc domain=%s t=%zu (full %zu, "
                  "split=%d) reps=%zu A=%zu nrow=%zu (full %zu) rounds -log2: "
                  "commit %.3f test %.3f column %.3f\n",
                  b.c->domain(d).name.c_str(), p.t, q.t, int(q.split),
                  p.ldt_reps, p.agreement, p.nrow, q.nrow, p.commit_bits,
                  p.test_bits, p.column_bits);
    }
  }
  std::string why;
  EXPECT_TRUE(accepts(b, x, &why)) << which << ": honest " << why;
  {
    auto prep = b.c->prepare(b.sys->statement(x.statement));
    SecureRandomEngine rng;
    const auto proof = prep.prove(b.sys->witness(x.data), rng);
    for (size_t at : {size_t(0), proof.size() / 2, proof.size() - 1}) {
      std::vector<uint8_t> bad = proof;
      bad[at] ^= 1;
      bool ok = false;
      try {
        ok = prep.verify(bad);
      } catch (const std::exception &) {
        ok = false;
      }
      EXPECT_FALSE(ok) << which << ": byte " << at << " changed";
    }
  }
  Instance w = x;
  w.data.issuer_sig[40] ^= 1;
  EXPECT_FALSE(accepts(b, w)) << which << ": tampered issuer signature";
}
TEST(Mdoc, MacAblation) { expect_ablation("nomac"); }
TEST(Mdoc, MaskTestAblation) { expect_ablation("untested"); }

// The device-signature ablation (mdoc.h's mdoc_relation, DEVICE_SIGNATURE
// false) of the list-radius build at 1 attribute: the system declares no
// node of the device's scope and no dpkx or dpky crossing; doc 3's honest
// proof verifies; the issuer's signature with one byte of s changed is
// rejected; a device signature with one byte changed verifies, since the
// ablation reads no device signature.
TEST(Mdoc, NoDeviceHonestAndTampered) {
  const Instance x = instance_of(bench_case(3, 1));
  const Built b = build_list_radius(1, examples::mdoc::kBlocks, false);
  for (const auto &node : b.sys->cs.graph().nodes) {
    EXPECT_NE(node.name.rfind("device.", 0), 0u) << node.name;
    EXPECT_EQ(node.name.find("cross.dpk"), std::string::npos) << node.name;
  }
  for (size_t d = 0; d < b.c->num_domains(); ++d)
    std::printf("MDOC_NODEVICE domain=%s %s\n", b.c->domain(d).name.c_str(),
                plan_line(*b.c, d).c_str());
  std::string why;
  EXPECT_TRUE(accepts(b, x, &why)) << "honest: " << why;
  {
    Instance w = x;
    w.data.issuer_sig[40] ^= 1;
    why.clear();
    EXPECT_FALSE(accepts(b, w, &why)) << "tampered issuer signature";
    std::printf("MDOC_REJECT nodevice tampered issuer signature: %s\n",
                why.empty() ? "verifier rejects" : why.c_str());
  }
  {
    Instance w = x;
    w.data.device_sig[40] ^= 1;
    EXPECT_TRUE(accepts(b, w)) << "a tampered device signature";
  }
}

// ------------------------------------------- the benched build rejects --
//
// The system the gh-mdoc bench case times (DISABLED_Bench's worker: the
// list-radius build, doc 3, 1 attribute, v7's 40 blocks, the device
// signature checked), built once. Each change of the statement or the
// witness is rejected by the verifier: the prover (not requiring
// satisfaction) makes a proof, and no generator or prover check stops it
// first. A flipped proof bit is rejected by the verifier without an
// exception; a truncated or extended proof may be rejected by its parser.

const Built &benched() {
  static const Built *b = new Built(build_list_radius(1));
  return *b;
}

void expect_benched_rejected(const Instance &x, const char *what) {
  std::string why;
  EXPECT_FALSE(accepts(benched(), x, &why)) << what;
  EXPECT_EQ(why, "") << what << ": rejected before the verifier";
  std::printf("MDOC_REJECT benched %s: %s\n", what,
              why.empty() ? "verifier rejects" : why.c_str());
}

// Whether the verifier of the benched build accepts PROOF of doc 3's
// statement. With PARSED, a verifier that throws on it fails the test (a
// flipped bit must reach the checks); without, it rejects the proof.
bool benched_verifies(const std::vector<uint8_t> &proof, bool parsed = true) {
  const Instance x = instance_of(bench_case(3, 1));
  auto prep = benched().c->prepare(benched().sys->statement(x.statement));
  try {
    return prep.verify(proof);
  } catch (const std::exception &e) {
    if (parsed) ADD_FAILURE() << "the verifier threw: " << e.what();
    return false;
  }
}

// An honest proof of doc 3 by the benched build.
std::vector<uint8_t> benched_proof() {
  const Instance x = instance_of(bench_case(3, 1));
  auto prep = benched().c->prepare(benched().sys->statement(x.statement));
  SecureRandomEngine rng;
  return prep.prove(benched().sys->witness(x.data), rng);
}

TEST(MdocBenched, HonestAccepted) {
  EXPECT_TRUE(benched_verifies(benched_proof()));
}

// The statement requests age_over_18 = false (CBOR 0xF4); doc 3 holds true.
TEST(MdocBenched, WrongAttribute) {
  Instance x = instance_of(bench_case(3, 1));
  ASSERT_EQ(x.statement.attributes[0].value[0], 0xF5);
  x.statement.attributes[0].value[0] = 0xF4;
  expect_benched_rejected(x, "wrong attribute value");
}

// now after doc 3's validUntil, and before its validFrom.
TEST(MdocBenched, WrongDate) {
  for (const char *now : {"2099-01-01T00:00:00Z", "2000-01-01T00:00:00Z"}) {
    Instance x = instance_of(bench_case(3, 1));
    ASSERT_EQ(x.statement.now.size(), 20u);
    x.statement.now.assign(now, now + 20);
    expect_benched_rejected(x, now);
  }
}

// The device signature with a byte of r and a byte of s changed, all zero
// (absent), and a valid signature on another e2 (the statement's e2 with
// one bit flipped, signed by a re-signed case's device key).
TEST(MdocBenched, WrongOrAbsentDeviceSignature) {
  const Instance base = instance_of(bench_case(3, 1));
  for (size_t at : {size_t(10), size_t(40)}) {
    Instance x = base;
    x.data.device_sig[at] ^= 1;
    expect_benched_rejected(x, at < 32 ? "device signature, r changed"
                                       : "device signature, s changed");
  }
  {
    Instance x = base;
    std::fill(x.data.device_sig.begin(), x.data.device_sig.end(), 0);
    expect_benched_rejected(x, "device signature absent (zero r and s)");
  }
  {
    std::mt19937_64 g(20261016);
    const Resign r = agreeing(g);
    Instance x = resigned(base, r, g);
    std::string why;
    ASSERT_TRUE(accepts(benched(), x, &why)) << "re-signed honest: " << why;
    Limbs other = x.statement.e2;
    other[0] ^= 1;
    x.data.device_sig = sign(r.device_d, other, random_scalar(g));
    expect_benched_rejected(x, "device signature on another e2");
  }
}

// An honest proof with one bit flipped at its start, middle and end.
TEST(MdocBenched, FlippedProofByte) {
  const auto proof = benched_proof();
  ASSERT_TRUE(benched_verifies(proof));
  for (size_t at : {size_t(0), size_t(1), proof.size() / 2, proof.size() - 1}) {
    std::vector<uint8_t> bad = proof;
    bad[at] ^= 1;
    EXPECT_FALSE(benched_verifies(bad)) << "byte " << at << " flipped";
  }
}

// An honest proof cut short (by one byte, to half, to nothing) or extended
// by one byte.
TEST(MdocBenched, TruncatedProof) {
  const auto proof = benched_proof();
  ASSERT_TRUE(benched_verifies(proof));
  for (size_t n : {proof.size() - 1, proof.size() / 2, size_t(0)}) {
    const std::vector<uint8_t> bad(proof.begin(), proof.begin() + n);
    EXPECT_FALSE(benched_verifies(bad, false))
        << "truncated to " << n << " bytes";
  }
  std::vector<uint8_t> longer = proof;
  longer.push_back(0);
  EXPECT_FALSE(benched_verifies(longer, false)) << "one byte appended";
}

// The tagged MSO's length of doc DOC (Longfellow's parser).
size_t tagged_mso_length(size_t doc) {
  const MdocTests &t = mdoc_tests[doc];
  ParsedMdoc pm;
  check(pm.parse_device_response(t.mdoc_size, t.mdoc) == MDOC_PROVER_SUCCESS,
        "mdoc test vector: parse");
  return pm.t_mso_.len;
}

// At Vega's bound: doc 3's MSO fits 31 blocks, its honest proof verifies,
// and a proof with one byte flipped does not.
TEST(Mdoc, VegaBoundHonestAndTampered) {
  const size_t len = tagged_mso_length(3);
  std::printf("doc 3: tagged MSO %zu bytes, message %zu bytes\n", len,
              18 + 2 + len);
  ASSERT_LE(18 + 2 + len + 9, 64 * kVegaBlocks);
  const Instance x = instance_of(bench_case(3, 1), kVegaBlocks);
  ASSERT_EQ(x.data.hash.buffer.size(), 64 * kVegaBlocks);
  const Built b = build_list_radius(1, kVegaBlocks);
  auto prep = b.c->prepare(b.sys->statement(x.statement));
  SecureRandomEngine rng;
  const auto proof = prep.prove(b.sys->witness(x.data), rng);
  EXPECT_TRUE(prep.verify(proof));
  for (size_t at : {size_t(0), proof.size() / 2, proof.size() - 1}) {
    std::vector<uint8_t> bad = proof;
    bad[at] ^= 1;
    bool ok = false;
    try {
      ok = prep.verify(bad);
    } catch (const std::exception &) {
      ok = false;
    }
    EXPECT_FALSE(ok) << "byte " << at << " flipped";
  }
  // The witness of v7's 40 blocks is not one of 31.
  const Instance x40 = instance_of(bench_case(3, 1));
  EXPECT_ANY_THROW(b.sys->witness(x40.data));
}

// The realized program of the list-radius build at 1 attribute
// (plan_program.h): its structural invariants hold, and the MAC's H part
// is a realization part of the cross-field equality.
TEST(Mdoc, ProgramExport) {
  const Built b = build_list_radius(1);
  const auto p = compiler::build_program(
      *b.c, compiler::ExportMeta{"mdoc", P::kId, "test", "test", 0});
  for (const auto &e : compiler::program_errors(p)) ADD_FAILURE() << e;
  // Every index map, decoded from the runs the text writes, equals its
  // explicit entries; the maps with no run longer than one entry.
  for (const auto &e : compiler::index_map_errors(p)) ADD_FAILURE() << e;
  for (const auto &e : compiler::module_errors(p)) ADD_FAILURE() << e;
  for (size_t k : compiler::maps_without_runs(p))
    std::printf("GH_MAP_WITHOUT_RUNS idx%zu length %zu\n", k,
                p.index_maps[k].size());
  bool h = false;
  for (const auto &q : p.predicates)
    if (q.name == "mac.H") {
      h = true;
      EXPECT_EQ(q.role, "realization");
      EXPECT_EQ(p.predicates.at(q.owner).name, "mac.equal");
    }
  EXPECT_TRUE(h);
}

}  // namespace
}  // namespace proofs::gordiehowe::examples::mdoc::full
