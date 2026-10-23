// Copyright 2026 Chad Sharp and Paul Grubbs
// SPDX-License-Identifier: Apache-2.0

// GordieHowe: the SHA-256 comparison's tests (sha256_compare_test.h): each
// column proves honestly and rejects a wrong digest and changed proofs, the
// bench's tableaus sit at the profile's rate, and the bit phase gives the
// same proofs.

#include "gordiehowe/bench/hash_comparisons/sha256_compare_test.h"

namespace proofs::gordiehowe::examples::sha256_compare {
namespace {

// ---------------------------------------------------------------- tests --

template <class P>
void expect_sound(size_t blocks, Column c, bool unpacked = false,
                  bool no_skip = false) {
  using T = ShaSystem<P>;
  Env<P> env;
  LigeroChoice lc;
  lc.unpacked_s0 = unpacked;
  lc.no_skip = no_skip;
  T t(env, blocks, c, lc);
  const auto comp = t.compile();
  // H at its field's default profile: the applications' rate, list radius
  // at the profile's target.
  EXPECT_EQ(comp->compiled_domain(0).plan().rate,
            domain_profile<P>(env.hf, env.rsh).rate);
  expect_ligero_target<P>(*comp);
  if (no_skip) {
    // Every batch runs at width 1: no skip values, one round per variable.
    const DomainPlan dp = comp->compiled_domain(0).plan();
    EXPECT_FALSE(dp.batches.empty());
    for (const auto &b : dp.batches) EXPECT_EQ(b.width, 1u) << b.name;
    EXPECT_NE(comp->report().find("no univariate skip, width 1"),
              std::string::npos);
  }
  if (unpacked) {
    // The GF(2^16) words are subfield cells of the prefix rows, so the
    // prefix test covers them, and no root stage runs.
    const std::string r = comp->report();
    EXPECT_NE(r.find("committed unpacked, one per cell"), std::string::npos)
        << r;
    EXPECT_EQ(r.find("edge to GF(2^" + std::to_string(P::HashField::kBits) +
                     ")"),
              std::string::npos)
        << r;
  }
  auto prep = comp->prepare(t.statement());
  SecureRandomEngine rng;
  const auto proof = prep.prove(t.witness(), rng);
  EXPECT_TRUE(prep.verify(proof)) << "honest proof";
  EXPECT_FALSE(comp->prepare(t.statement(/*wrong=*/true)).verify(proof))
      << "digest";
  typename T::Sys::ProveOptions opt;
  opt.require_satisfied = false;
  const auto &f = env.hf;
  opt.tamper = [&](size_t id, typename T::Sys::Value &v) {
    if (id != t.tamper_node) return;
    auto &e = std::get<std::vector<typename T::Elt>>(v).at(t.tamper_at);
    e = t.tamper_word ? f.addf(e, f.beta(0))
                      : (e == f.one() ? f.zero() : f.one());
  };
  EXPECT_FALSE(prep.verify(prep.prove(t.witness(), rng, opt))) << "witness";
  if (c != Column::kBatched) return;
  // A batch message changed before it is absorbed (the later rounds are
  // not recomputed from it): the first round's coefficients (the skip
  // values under the skip) and the last message, a terminal value.
  // SIZE_MAX: the last message.
  for (size_t at : {size_t(0), size_t(1), SIZE_MAX}) {
    typename T::Sys::ProveOptions bad;
    bad.batch_tamper = [&f, at](size_t d, size_t b,
                                typename T::Sys::Value &m) {
      if (d != 0 || b != 0) return;
      auto &v = std::get<std::vector<typename T::Elt>>(m);
      auto &x = v.at(at == SIZE_MAX ? v.size() - 1 : at);
      x = f.addf(x, f.one());
    };
    EXPECT_FALSE(prep.verify(prep.prove(t.witness(), rng, bad)))
        << "batch message " << at;
  }
}

template <class P>
class GordieHoweSha256Compare : public ::testing::Test {};
TYPED_TEST_SUITE(GordieHoweSha256Compare, param_sets::Profiles,
                 param_sets::ProfileName);

TYPED_TEST(GordieHoweSha256Compare, GkrTwoBlocks) {
  expect_sound<TypeParam>(2, Column::kGkr);
}
// DomainProfile::unpacked_s0: the words committed one per subfield cell.
TYPED_TEST(GordieHoweSha256Compare, BatchedTwoBlocksUnpacked) {
  expect_sound<TypeParam>(2, Column::kBatched, /*unpacked=*/true);
}
TYPED_TEST(GordieHoweSha256Compare, GkrTwoBlocksUnpacked) {
  expect_sound<TypeParam>(2, Column::kGkr, /*unpacked=*/true);
}
TYPED_TEST(GordieHoweSha256Compare, BatchedTwoBlocks) {
  expect_sound<TypeParam>(2, Column::kBatched);
}
// DomainProfile::no_skip: the batches without the univariate skip.
TYPED_TEST(GordieHoweSha256Compare, BatchedTwoBlocksNoSkip) {
  expect_sound<TypeParam>(2, Column::kBatched, /*unpacked=*/false,
                          /*no_skip=*/true);
}
// The bit adjoint by its steps, by its folded products and by the cheaper
// per template give the same proof, single- and multi-threaded
// (threads_testing.h): SHA-256's rotations and carry views inside 32-bit
// halves of 64-bit lanes, on packed and on unpacked words.
TYPED_TEST(GordieHoweSha256Compare, AdjointPaths) {
  using T = ShaSystem<TypeParam>;
  Env<TypeParam> env;
  for (const bool unpacked : {false, true}) {
    LigeroChoice lc;
    lc.unpacked_s0 = unpacked;
    T t(env, 2, Column::kBatched, lc);
    const auto c = t.compile();
    auto prep = c->prepare(t.statement());
    gordiehowe::threads_testing::expect_adjoint_paths_same_proof(prep,
                                                                 t.witness());
  }
}
// The branch run on the calling thread: the SHA-256 batch when the hash is
// batched (its digest check is affine rows, so its GKR branch is empty),
// GKR when the hash is in the circuit.
TYPED_TEST(GordieHoweSha256Compare, HeaviestBranch) {
  using T = ShaSystem<TypeParam>;
  Env<TypeParam> env;
  const LigeroChoice lc;
  T batched(env, 2, Column::kBatched, lc);
  const auto cb = batched.compile();
  const auto &db = cb->compiled_domain(0);
  EXPECT_LT(db.heaviest_branch(), db.branches() - 1);
  T circuit(env, 2, Column::kGkr, lc);
  const auto cg = circuit.compile();
  const auto &dg = cg->compiled_domain(0);
  EXPECT_EQ(dg.heaviest_branch(), dg.branches() - 1);
}

TYPED_TEST(GordieHoweSha256Compare, LongfellowTwoBlocks) {
  const LongfellowSha<TypeParam> lf(2);
  EXPECT_GE(lf.bits(), baseline_target<TypeParam>());
  SecureRandomEngine rng;
  EXPECT_TRUE(lf.run(rng).ok) << "honest proof";
  EXPECT_FALSE(lf.run(rng, /*wrong_digest=*/true).ok) << "digest";
}

// The rate of every bench case of the GordieHowe columns (report_bench's
// sha256-gkr and sha256-batched at 8 blocks, sha256-batched-noskip,
// sha256-batched-17 and sha256-{gkr,batched}-{64,2048}B) is the rate of the
// default profile of H's field (domain_profile.h), every application's H
// rate: each case has a kListRadius entry, a tableau at that rate, as has
// every entry of the profile; and the 64-byte cases compile to it, at list
// radius at the profile's target, on their entry's block_enc.
TYPED_TEST(GordieHoweSha256Compare, TableauRate) {
  using P = TypeParam;
  using lib::sha256::sha256_internal::blocks_of;
  Env<P> env;
  const size_t rate = domain_profile<P>(env.hf, env.rsh).rate;
  EXPECT_EQ(h_profile<P>(env, LigeroChoice{}).rate, rate);
  for (const auto *table : {&kListRadius, &kListRadiusUnpacked})
    for (const ListRadiusEntry &e : *table)
      if (std::strcmp(e.profile, P::kId) == 0)
        EXPECT_TRUE(compiler::tableau_of(e.block_enc, rate).has_value())
            << name(e.column) << " " << e.blocks;
  struct Case {
    Column col;
    size_t blocks;
  };
  const Case cases[] = {
      {Column::kGkr, 8},           {Column::kBatched, 8},
      {Column::kBatched, 17},      {Column::kGkr, blocks_of(64)},
      {Column::kBatched, blocks_of(64)}, {Column::kGkr, blocks_of(2048)},
      {Column::kBatched, blocks_of(2048)}};
  for (const Case &c : cases)
    EXPECT_NE(list_radius(P::kId, c.col, c.blocks), nullptr)
        << name(c.col) << " " << c.blocks;
  for (Column col : {Column::kGkr, Column::kBatched}) {
    const Prepared<P> x(env, blocks_of(64), col, /*unpacked=*/false,
                        /*ud_rule=*/false, /*no_skip=*/false, 64);
    EXPECT_FALSE(x.searched) << name(col);
    const DomainPlan dp = x.c->compiled_domain(0).plan();
    EXPECT_EQ(dp.rate, rate) << name(col);
    EXPECT_EQ(dp.block_enc, x.ligero.block_enc) << name(col);
    expect_ligero_target<P>(*x.c);
  }
}

// The system the sha256-batched bench case times (the serve command's worker
// at its defaults: the batched column, 8 blocks, a 503-byte message, the
// list-radius tableau of kListRadius), in each profile. The honest proof
// verifies; it is rejected against a wrong digest, and a proof of the
// wrong digest's statement (the prover not requiring satisfaction) is
// rejected; the honest proof with one bit flipped (start, middle, end) is
// rejected. Each of these reaches the verifier's checks (no exception);
// the honest proof cut short (by one byte, to half, to nothing) is
// rejected, by its parser or the checks.
TYPED_TEST(GordieHoweSha256Compare, BenchedEightBlocksRejected) {
  using P = TypeParam;
  using T = ShaSystem<P>;
  Env<P> env;
  Prepared<P> x(env, 8, Column::kBatched);
  ASSERT_EQ(x.t->message_bytes(), 503u);
  ASSERT_TRUE(x.ligero.list_radius) << "the bench's list-radius tableau";
  x.prepare();
  auto verifies = [](const typename T::Sys::Prepared &prep,
                     const std::vector<uint8_t> &proof, bool parsed = true) {
    try {
      return prep.verify(proof);
    } catch (const std::exception &e) {
      if (parsed) ADD_FAILURE() << "the verifier threw: " << e.what();
      return false;
    }
  };
  SecureRandomEngine rng;
  const auto proof = x.prep->prove(x.t->witness(), rng);
  ASSERT_TRUE(verifies(*x.prep, proof)) << "honest proof";
  const auto wrong = x.c->prepare(x.t->statement(/*wrong=*/true));
  EXPECT_FALSE(verifies(wrong, proof)) << "honest proof, wrong digest";
  {
    typename T::Sys::ProveOptions opt;
    opt.require_satisfied = false;
    bool ok = false;
    try {
      ok = wrong.verify(wrong.prove(x.t->witness(), rng, opt));
    } catch (const std::exception &e) {
      ADD_FAILURE() << "rejected before the verifier: " << e.what();
    }
    EXPECT_FALSE(ok) << "a proof of the wrong digest";
  }
  for (size_t at : {size_t(0), proof.size() / 2, proof.size() - 1}) {
    std::vector<uint8_t> bad = proof;
    bad[at] ^= 1;
    EXPECT_FALSE(verifies(*x.prep, bad)) << "byte " << at << " flipped";
  }
  for (size_t n : {proof.size() - 1, proof.size() / 2, size_t(0)}) {
    const std::vector<uint8_t> bad(proof.begin(), proof.begin() + n);
    EXPECT_FALSE(verifies(*x.prep, bad, false))
        << "truncated to " << n << " bytes";
  }
}

// The block counts of the padding rule: L bytes, the 0x80 byte and the
// 8-byte length fill ceil((L + 9) / 64) blocks; the Binius64 comparison's
// 1 KiB, 8 KiB and 32 KiB messages take 17, 129 and 513.
TEST(Sha256Compare, MessageBlocks) {
  using lib::sha256::sha256_internal::blocks_of;
  EXPECT_EQ(blocks_of(55), 1u);
  EXPECT_EQ(blocks_of(56), 2u);
  EXPECT_EQ(blocks_of(503), 8u);
  EXPECT_EQ(blocks_of(1024), 17u);
  EXPECT_EQ(blocks_of(8192), 129u);
  EXPECT_EQ(blocks_of(32768), 513u);
}

// The sha256-batched-1KiB bench case's system (the serve command at
// --bytes 1024: the batched column, 17 blocks, the list-radius
// tableau of kListRadius), in each profile: the honest proof verifies and
// is rejected against a wrong digest.
TYPED_TEST(GordieHoweSha256Compare, BatchedOneKiB) {
  using P = TypeParam;
  Env<P> env;
  Prepared<P> x(env, 17, Column::kBatched, false, false, false, 1024);
  ASSERT_EQ(x.t->message_bytes(), 1024u);
  ASSERT_TRUE(x.ligero.list_radius) << "the bench's list-radius tableau";
  x.prepare();
  SecureRandomEngine rng;
  const auto proof = x.prep->prove(x.t->witness(), rng);
  EXPECT_TRUE(x.prep->verify(proof)) << "honest proof";
  EXPECT_FALSE(x.c->prepare(x.t->statement(/*wrong=*/true)).verify(proof))
      << "honest proof, wrong digest";
}

// The bit phase (DomainProfile::bit_phase, compiler/bit_phase.h) on the batched
// column, at 2 blocks packed and unpacked: the soundness checks above, the
// bit phase's own rejections (bit_phase_testing.h), and the same proof by
// the adjoint's steps, folded products and chosen way, single- and
// multi-threaded. Each bit-phase batch sends 8 field elements more than
// without the bit phase (LigeroChoice::bit_phase false).
TYPED_TEST(GordieHoweSha256Compare, BatchedTwoBlocksBitPhase) {
  using P = TypeParam;
  using T = ShaSystem<P>;
  Env<P> env;
  for (const bool unpacked : {false, true}) {
    LigeroChoice lc;
    lc.unpacked_s0 = unpacked;
    std::vector<size_t> plain;
    {
      LigeroChoice off = lc;
      off.bit_phase = false;
      T t(env, 2, Column::kBatched, off);
      plain = t.compile()->compiled_domain(0).batch_message_bytes();
    }
    expect_sound<P>(2, Column::kBatched, unpacked);
    T t(env, 2, Column::kBatched, lc);
    const auto c = t.compile();
    auto prep = c->prepare(t.statement());
    bit_phase_testing::expect_bit_phase<typename T::Sys, typename T::Elt>(
        *c, prep, t.witness(), env.hf);
    gordiehowe::threads_testing::expect_adjoint_paths_same_proof(prep,
                                                                 t.witness());
    bit_phase_testing::expect_bridge_same_proof(prep, t.witness());
    const auto with = c->compiled_domain(0).batch_message_bytes();
    ASSERT_EQ(with.size(), plain.size());
    const auto pb = bit_phase_testing::phase_batches(*c);
    for (size_t b = 0; b < with.size(); ++b) {
      bool phase = false;
      for (const auto &[d, x] : pb) phase = phase || (d == 0 && x == b);
      EXPECT_EQ(with[b], plain[b] + (phase ? compiler::BitPhaseShape::kMessages *
                                                 P::HashField::kBytes
                                           : 0))
          << (unpacked ? "unpacked" : "packed") << ", batch " << b;
    }
  }
}
// The sha256-batched-1KiB bench system with the bit phase: the honest
// proof verifies and is rejected against a wrong digest.
TYPED_TEST(GordieHoweSha256Compare, BatchedOneKiBBitPhase) {
  using P = TypeParam;
  Env<P> env;
  Prepared<P> x(env, 17, Column::kBatched, false, false, false, 1024);
  x.prepare();
  EXPECT_FALSE(bit_phase_testing::phase_batches(*x.c).empty());
  SecureRandomEngine rng;
  const auto proof = x.prep->prove(x.t->witness(), rng);
  EXPECT_TRUE(x.prep->verify(proof)) << "honest proof";
  EXPECT_FALSE(x.c->prepare(x.t->statement(/*wrong=*/true)).verify(proof))
      << "honest proof, wrong digest";
}

}  // namespace
}  // namespace proofs::gordiehowe::examples::sha256_compare
