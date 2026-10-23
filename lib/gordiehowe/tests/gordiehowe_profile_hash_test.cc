// Copyright 2026 Chad Sharp and Paul Grubbs
// SPDX-License-Identifier: Apache-2.0
//
// GordieHowe: the protocol hash belongs to the field profile
// (lib/params/param_sets.h): SHA-256 at the ROM parameters and SHA-384 at
// the QROM parameters, for the Fiat-Shamir transcript, the Merkle
// commitments and the system digest. The tests check the sizes a proof
// carries in each profile (the system digest, the proof's seed and the
// Merkle leaf nonce), and that a proof under one hash is rejected by the
// same system's verifier under the other.

#include <algorithm>
#include <cstddef>
#include <cstdint>
#include <random>
#include <stdexcept>
#include <memory>
#include <string>
#include <type_traits>
#include <vector>

#include "params/param_sets.h"
#include "params/param_sets_testing.h"
#include "gf2k/gf2_128.h"
#include "gf2k/lch14_reed_solomon.h"
#include "gordiehowe/gordiehowe.h"
#include "gordiehowe/instances.h"
#include "merkle/merkle_commitment.h"
#include "random/secure_random_engine.h"
#include "random/transcript.h"
#include "util/crypto.h"
#include "gtest/gtest.h"

namespace proofs::gordiehowe {
namespace {

// The binary domain over HF at the protocol hash H.
template <class HF_, class H>
struct BinaryEnv {
  using HF = HF_;
  using RS = LCH14ReedSolomonFactory<HF>;
  using Sys = ConstraintSystem<H, HF>;
  HF f;
  RS rs{f};
  DomainProfile<HF, RS, H> profile() const {
    DomainProfile<HF, RS, H> p;
    p.f = &f;
    p.rsf = &rs;
    p.field_name = "GF(2^" + std::to_string(HF::kBits) + ")";
    p.rate = 4;
    p.nreq = 64;
    p.has_subfield = true;
    p.prime = Space::kPrime;
    p.rates = param_sets::placement_rates<HF>();
    return p;
  }
};

// One relation over ENV's domain: a committed bit matrix x and the
// committed expressions x + rot(x) and x & rot(x).
template <class Env>
struct Small {
  using Sys = typename Env::Sys;
  using HF = typename Env::HF;
  const Env &env;
  Sys cs{"gh-profile-hash"};
  Ref<HF, Bit, Committed> x;
  std::unique_ptr<typename Sys::Compiled> c;
  explicit Small(const Env &e) : env(e) {
    auto &H = cs.domain(env.profile(), "H");
    x = H.priv(Bit{}, "x", Shape{16, 16});
    H.priv("lin", x + x.rotate(1, 1));
    H.priv("quad", x & x.rotate(3, 1));
    c = compile(cs);
  }
  typename Sys::Assignment witness() const {
    std::mt19937_64 g(20261010);
    std::vector<typename HF::Elt> xv(256);
    for (auto &e : xv) e = ct::bit_elt(env.f, g() & 1);
    typename Sys::Assignment w;
    w.set(x, xv);
    return w;
  }
};

// The prover's randomness, with the bytes of its first draw (the proof's
// seed, drawn before anything else) kept.
class Recording : public RandomEngine {
 public:
  void bytes(uint8_t *buf, size_t n) override {
    rng_.bytes(buf, n);
    if (first_.empty()) first_.assign(buf, buf + n);
  }
  const std::vector<uint8_t> &first() const { return first_; }

 private:
  SecureRandomEngine rng_;
  std::vector<uint8_t> first_;
};

template <class P>
class GordieHoweProfileHash : public ::testing::Test {};
TYPED_TEST_SUITE(GordieHoweProfileHash, param_sets::Profiles,
                 param_sets::ProfileName);

// A proof of profile P is over P's hash: the system digest is one digest,
// the serialized proof opens with its seed of one digest's length, and the
// Merkle leaves carry nonces of two.
TYPED_TEST(GordieHoweProfileHash, DigestAndSaltSizes) {
  using P = TypeParam;
  using PH = typename P::ProtocolHash;
  const bool rom = !P::kPostQuantum;
  const size_t k = rom ? 32 : 48;
  EXPECT_STREQ(PH::kName, rom ? "SHA-256" : "SHA-384");
  EXPECT_EQ(PH::kDigestSize, k);
  EXPECT_EQ(BasicProofSeed<PH>::kLength, k);
  EXPECT_EQ(BasicMerkleNonce<PH>::kLength, 2 * k);

  using Env = BinaryEnv<typename P::HashField, PH>;
  static_assert(std::is_same_v<typename Env::Sys::Set::Hash, PH>);
  const Env env;
  const Small<Env> s(env);
  EXPECT_EQ(s.c->digest().size(), k);
  const auto prep = s.c->prepare({});
  Recording rng;
  const std::vector<uint8_t> proof = prep.prove(s.witness(), rng);
  ASSERT_EQ(rng.first().size(), k);
  ASSERT_GE(proof.size(), k);
  EXPECT_TRUE(std::equal(proof.begin(), proof.begin() + k,
                         rng.first().begin()));
  EXPECT_TRUE(prep.verify(proof));
}

// The same relation over GF(2^128) at SHA-256 (the hash of the ROM parameters)
// and at SHA-384 (the hash of the QROM parameters): each verifier accepts its
// own proofs and rejects the other's.
TEST(GordieHoweProfileHash, OtherHashRejected) {
  using HF = GF2_128<>;
  using E256 = BinaryEnv<HF, SHA256>;
  using E384 = BinaryEnv<HF, SHA384>;
  static_assert(std::is_same_v<param_sets::ROMParams::ProtocolHash, SHA256>);
  static_assert(std::is_same_v<param_sets::QROMParams::ProtocolHash, SHA384>);
  const E256 e256;
  const E384 e384;
  const Small<E256> a(e256);
  const Small<E384> b(e384);
  const auto pa = a.c->prepare({});
  const auto pb = b.c->prepare({});
  SecureRandomEngine rng;
  const auto proof_a = pa.prove(a.witness(), rng);
  const auto proof_b = pb.prove(b.witness(), rng);
  EXPECT_TRUE(pa.verify(proof_a));
  EXPECT_TRUE(pb.verify(proof_b));
  auto rejects = [](const auto &prep, const std::vector<uint8_t> &proof) {
    try {
      return !prep.verify(proof);
    } catch (const std::runtime_error &) {
      return true;
    }
  };
  EXPECT_TRUE(rejects(pb, proof_a));
  EXPECT_TRUE(rejects(pa, proof_b));
}

}  // namespace
}  // namespace proofs::gordiehowe
