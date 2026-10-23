// Copyright 2026 Chad Sharp and Paul Grubbs
// SPDX-License-Identifier: Apache-2.0

// GordieHowe: the Keccak comparison's tests (keccak_compare_test.h): each
// preset and mode proves honestly and rejects a wrong output, a changed
// committed value and changed batch messages.

#include "gordiehowe/bench/hash_comparisons/keccak_compare_test.h"

namespace proofs::gordiehowe::examples::keccak_compare {
namespace {

// ---------------------------------------------------------------- tests --

template <class P>
void expect_sound(Preset preset, Mode mode, bool no_skip = false,
                  size_t sha3_bytes = 0) {
  using T = KeccakSystem<P>;
  Env<P> env;
  T t(env, preset, mode, no_skip, sha3_bytes);
  const auto c = t.compile();
  std::printf("KECCAK_COMPARE preset=%s mode=%s profile=%s perms=%zu\n",
              name(preset), name(mode), P::kId, t.permutations());
  // H at its field's default profile: the applications' rate, list radius
  // at the profile's target.
  EXPECT_EQ(c->compiled_domain(0).plan().rate,
            domain_profile<P>(env.hf, env.rsh).rate);
  expect_ligero_target<P>(*c);
  if (no_skip) {
    // Every batch runs at width 1: no skip values, one round per variable.
    const DomainPlan dp = c->compiled_domain(0).plan();
    EXPECT_FALSE(dp.batches.empty());
    for (const auto &b : dp.batches) EXPECT_EQ(b.width, 1u) << b.name;
    EXPECT_NE(c->report().find("no univariate skip, width 1"),
              std::string::npos);
  }
  auto prep = c->prepare(t.statement());
  SecureRandomEngine rng;
  const auto proof = prep.prove(t.witness(), rng);
  EXPECT_TRUE(prep.verify(proof)) << "honest proof";
  // A wrong public output word.
  EXPECT_FALSE(c->prepare(t.statement(/*wrong=*/true)).verify(proof))
      << "output";
  // The perms preset runs exactly N permutations, the sha3 preset one per
  // padded block.
  if (preset == Preset::kPerms) EXPECT_EQ(t.permutations(), kDefaultPerms);
  if (preset == Preset::kSha3)
    EXPECT_EQ(t.permutations(), sha3_blocks(t.sha3_bytes()));
  // sha3: a flipped message bit (the first byte's and the last byte's)
  // gives a digest other than the public one.
  if (preset == Preset::kSha3) {
    typename T::Sys::ProveOptions flipped;
    flipped.require_satisfied = false;
    const size_t last = 8 * t.sha3_bytes();
    for (size_t bit : {size_t(1), last})
      EXPECT_FALSE(prep.verify(prep.prove(t.witness(bit), rng, flipped)))
          << "message bit " << bit - 1;
  }
  // A committed Keccak value changed: a checkpoint bit (gkr) or a round
  // word only the batch reads (batched).
  typename T::Sys::ProveOptions opt;
  opt.require_satisfied = false;
  const auto &f = env.hf;
  opt.tamper = [&](size_t id, typename T::Sys::Value &v) {
    if (id != t.tamper_node) return;
    auto &x = std::get<std::vector<typename T::Elt>>(v);
    auto &e = x.at(t.tamper_at);
    e = t.tamper_word ? f.addf(e, f.beta(0))
                      : (e == f.one() ? f.zero() : f.one());
  };
  EXPECT_FALSE(prep.verify(prep.prove(t.witness(), rng, opt))) << "witness";
  if (mode != Mode::kBatched) return;
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
class GordieHoweKeccakCompare : public ::testing::Test {};
TYPED_TEST_SUITE(GordieHoweKeccakCompare, param_sets::Profiles,
                 param_sets::ProfileName);

TYPED_TEST(GordieHoweKeccakCompare, FalconGkr) {
  expect_sound<TypeParam>(Preset::kFalcon, Mode::kGkr);
}
TYPED_TEST(GordieHoweKeccakCompare, FalconBatched) {
  expect_sound<TypeParam>(Preset::kFalcon, Mode::kBatched);
}
TYPED_TEST(GordieHoweKeccakCompare, MlDsaGkr) {
  expect_sound<TypeParam>(Preset::kMlDsa, Mode::kGkr);
}
TYPED_TEST(GordieHoweKeccakCompare, MlDsaBatched) {
  expect_sound<TypeParam>(Preset::kMlDsa, Mode::kBatched);
}
// The sha3 preset's reference digest is SHA3-256: FIPS 202's "abc" vector.
TEST(KeccakCompare, Sha3ReferenceKnownAnswer) {
  const std::vector<uint8_t> d = sha3_256_reference({'a', 'b', 'c'});
  static const uint8_t kAbc[32] = {
      0x3a, 0x98, 0x5d, 0xa7, 0x4f, 0xe2, 0x25, 0xb2, 0x04, 0x5c, 0x17,
      0x2d, 0x6b, 0xd3, 0x90, 0xbd, 0x85, 0x5f, 0x08, 0x6e, 0x3e, 0x9d,
      0x52, 0x5b, 0x46, 0xbf, 0xe2, 0x45, 0x11, 0x43, 0x15, 0x32};
  EXPECT_EQ(d, std::vector<uint8_t>(kAbc, kAbc + 32));
}
// SHA3-256 of a private message of N = 8 blocks (1087 bytes).
TYPED_TEST(GordieHoweKeccakCompare, Sha3Batched) {
  expect_sound<TypeParam>(Preset::kSha3, Mode::kBatched);
}
// SHA3-256 of a private 1,024-byte message (8 blocks, one partly padding).
TYPED_TEST(GordieHoweKeccakCompare, Sha3Batched1KiB) {
  expect_sound<TypeParam>(Preset::kSha3, Mode::kBatched, false, 1024);
}
// The block counts of the padding rule: L bytes and at least one padding
// byte fill floor(L / 136) + 1 blocks.
TEST(KeccakCompare, Sha3Blocks) {
  EXPECT_EQ(sha3_blocks(0), 1u);
  EXPECT_EQ(sha3_blocks(135), 1u);
  EXPECT_EQ(sha3_blocks(136), 2u);
  EXPECT_EQ(sha3_blocks(1087), 8u);
  EXPECT_EQ(sha3_blocks(1088), 9u);
  EXPECT_EQ(sha3_blocks(1024), 8u);
  EXPECT_EQ(sha3_blocks(8192), 61u);
  EXPECT_EQ(sha3_blocks(32768), 241u);
}
// The bit adjoint by its steps, by its folded products and by the cheaper
// per template give the same proof, single- and multi-threaded
// (threads_testing.h): Keccak-f's rotations and column parities, in the
// perms and sha3 presets.
TYPED_TEST(GordieHoweKeccakCompare, AdjointPaths) {
  using T = KeccakSystem<TypeParam>;
  Env<TypeParam> env;
  for (const Preset preset : {Preset::kPerms, Preset::kSha3}) {
    T t(env, preset, Mode::kBatched, /*no_skip=*/false, /*sha3_bytes=*/0);
    const auto c = t.compile();
    auto prep = c->prepare(t.statement());
    gordiehowe::threads_testing::expect_adjoint_paths_same_proof(prep,
                                                                 t.witness());
  }
}
TYPED_TEST(GordieHoweKeccakCompare, PermsBatched) {
  expect_sound<TypeParam>(Preset::kPerms, Mode::kBatched);
}
// DomainProfile::no_skip: the batches without the univariate skip.
TYPED_TEST(GordieHoweKeccakCompare, PermsBatchedNoSkip) {
  expect_sound<TypeParam>(Preset::kPerms, Mode::kBatched, /*no_skip=*/true);
}
// The bit phase (DomainProfile::bit_phase, compiler/bit_phase.h) on the sha3
// and perms presets: the soundness checks above, the bit phase's own
// rejections (bit_phase_testing.h), and the same proof by the adjoint's
// steps, folded products and chosen way (Keccak's templates run on their
// steps), single- and multi-threaded.
TYPED_TEST(GordieHoweKeccakCompare, Sha3BatchedBitPhase) {
  using P = TypeParam;
  using T = KeccakSystem<P>;
  expect_sound<P>(Preset::kSha3, Mode::kBatched);
  for (const Preset preset : {Preset::kSha3, Preset::kPerms}) {
    Env<P> env;
    T t(env, preset, Mode::kBatched, /*no_skip=*/false, /*sha3_bytes=*/0);
    const auto c = t.compile();
    auto prep = c->prepare(t.statement());
    bit_phase_testing::expect_bit_phase<typename T::Sys, typename T::Elt>(
        *c, prep, t.witness(), env.hf);
    gordiehowe::threads_testing::expect_adjoint_paths_same_proof(prep,
                                                                 t.witness());
    bit_phase_testing::expect_bridge_same_proof(prep, t.witness());
  }
}

}  // namespace
}  // namespace proofs::gordiehowe::examples::keccak_compare
