// Copyright 2026 Chad Sharp and Paul Grubbs
// SPDX-License-Identifier: Apache-2.0

// GordieHowe plain mdoc (mdoc.h): the test and bench system, its
// statement and witness from Longfellow's mdoc test vectors, and re-signed
// variants of them under keys the test holds.
//
// The witness of a case is domain H's (mdoc_hash_testing.h, through
// Longfellow's witness parser) and the signatures as Longfellow's
// MdocSignatureWitness reads them (the issuer's on the MSO's digest, the
// device's on e2 = SHA-256(DeviceAuthenticationBytes)). A re-signed case
// writes a chosen device key into the MSO's deviceKeyInfo window, signs the
// new digest with an issuer key of its own and e2 with the device key, so
// that domain A's values may differ from domain H's in exactly one of e,
// dpkx and dpky.

#ifndef PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_EXAMPLES_MDOC_MDOC_TESTING_H_
#define PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_EXAMPLES_MDOC_MDOC_TESTING_H_

#include <algorithm>
#include <cstddef>
#include <cstdint>
#include <memory>
#include <random>
#include <string>
#include <vector>

#include "circuits/mdoc/mdoc_witness.h"
#include "gordiehowe/examples/mdoc/mdoc.h"
#include "gordiehowe/examples/mdoc/mdoc_builders.h"
#include "gordiehowe/examples/shared/setup.h"
#include "gordiehowe/examples/mdoc/mdoc_hash_testing.h"
#include "gordiehowe/examples/p256/p256_testing.h"
#include "gordiehowe/examples/shared/system_testing.h"
#include "gordiehowe/instances.h"
#include "util/crypto.h"

namespace proofs::gordiehowe::examples::mdoc::full {

using P = param_sets::ROMParams;
using HF = P::HashField;
using AF = P::EcdsaField;
using PH = P::ProtocolHash;
using Sys = ConstraintSystem<PH, HF, AF>;
using Assignment = Sys::Assignment;
using Compiled = BasicCompiledSystem<instances::SetMdoc>;
using HProfile = examples::mdoc::testing::Profile;
using AProfile = examples::mdoc::p256_testing::Profile;
using examples::mdoc::testing::bench_case;
using examples::mdoc::testing::Case;
using Limbs = examples::mdoc::p256_ecdsa::Limbs;
using AElt = examples::mdoc::p256_ecdsa::Elt;
static_assert(
    std::is_same_v<PH, examples::mdoc::p256_testing::P::ProtocolHash>);

inline const HF &hf() { return examples::mdoc::testing::hf(); }
inline const AF &af() { return examples::mdoc::p256_testing::fp(); }

// The compile profile: the MAC basis of GF(2^128); the system gh-mdoc, or
// gh-mdoc-nodevice under the device-signature ablation (mdoc.h).
inline CompileProfile compile_profile(bool device_signature = true) {
  return mac_profile<P>(device_signature ? "gh-mdoc" : "gh-mdoc-nodevice");
}
// H and A at Longfellow v7's Ligero (rate 7, 132 opened columns at unique
// decoding), or at the compiler's list-radius choice (domain_profile.h).
inline HProfile h_profile() { return examples::mdoc::testing::profile(); }
inline AProfile a_profile() { return examples::mdoc::p256_testing::profile(); }
inline HProfile list_h_profile() {
  return domain_profile<P>(hf(), examples::mdoc::testing::rs());
}
inline AProfile list_a_profile() {
  return examples::mdoc::p256_testing::list_profile();
}

// The relation for N_ATTR attributes and an MSO buffer of BLOCKS SHA-256
// blocks (mdoc.h), with the assignments of host values for the tests and
// benchmarks that drive the prover directly. DEVICE_SIGNATURE false is the
// device-signature ablation (mdoc.h's mdoc_relation, a test-only
// ablation); BUILD the bench's ablations (setup.h's BuildOptions).
struct MdocSystem
    : examples::RelationSystem<Sys, examples::mdoc::MdocStatement<Value>,
                               examples::mdoc::MdocWitness<Value>> {
  MdocSystem(const HProfile &hp, const AProfile &ap, size_t n_attr,
             size_t blocks = examples::mdoc::kBlocks,
             bool device_signature = true,
             const examples::BuildOptions &build = {})
      : RelationSystem(examples::mdoc::mdoc<Sys>(
            build.profile(compile_profile(device_signature)), hp, ap, n_attr,
            blocks, device_signature, build.compile)) {}
  Assignment statement(const examples::mdoc::MdocStatementData &x) const {
    return RelationSystem::statement(examples::mdoc::mdoc_statement(x));
  }
  Assignment witness(const examples::mdoc::MdocData &d) const {
    return RelationSystem::witness(examples::mdoc::mdoc_witness(d));
  }
};

// ------------------------------------------------------------- cases --

// One instance: the statement's values and the prover's.
struct Instance {
  examples::mdoc::MdocStatementData statement;
  examples::mdoc::MdocData data;
};

inline Limbs limbs_of(const Fp256Nat &x) {
  return {x.limb_[0], x.limb_[1], x.limb_[2], x.limb_[3]};
}
inline std::vector<uint8_t> be(const Limbs &k) {
  return examples::mdoc::p256_ecdsa::host::be_bytes(k);
}
inline std::vector<uint8_t> be(const AElt &x) {
  return be(examples::mdoc::p256_ecdsa::host::canonical(x));
}

// Case C of Longfellow's vectors: domain H's witness and statement
// (its buffer of BLOCKS SHA-256 blocks), the issuer key, both signatures
// and e2 as Longfellow's witness reads them
// (MdocSignatureWitness::compute_witness).
inline Instance instance_of(const Case &c,
                            size_t blocks = examples::mdoc::kBlocks) {
  const examples::mdoc::testing::Witness hw =
      examples::mdoc::testing::witness_of(c, blocks);
  const MdocTests &t = mdoc_tests[c.doc];
  ParsedMdoc pm;
  check(pm.parse_device_response(t.mdoc_size, t.mdoc) == MDOC_PROVER_SUCCESS,
        "mdoc test vector: parse");
  check(pm.sig_.len == 64 && pm.dksig_.len == 64, "mdoc test vector: r || s");
  Instance x;
  auto &st = x.statement;
  st.now.assign(t.now, t.now + 20);
  for (const auto &a : c.attrs)
    st.attributes.push_back(examples::mdoc::testing::statement_of(a));
  st.issuer_x = p256_base.of_string(t.pkx);
  st.issuer_y = p256_base.of_string(t.pky);
  st.e2 = limbs_of(compute_transcript_hash<Fp256Nat>(
      t.transcript, t.transcript_size, &pm.doc_type_));
  auto &d = x.data;
  d.hash = hw.data;
  d.e = hw.e;
  d.issuer_sig.assign(&t.mdoc[pm.sig_.pos], &t.mdoc[pm.sig_.pos] + 64);
  d.dpk = hw.dpkx;
  d.dpk.insert(d.dpk.end(), hw.dpky.begin(), hw.dpky.end());
  d.device_sig.assign(&t.mdoc[pm.dksig_.pos], &t.mdoc[pm.dksig_.pos] + 64);
  return x;
}

// ------------------------------------------------------- re-signed cases --
// Test data, not constant-time.

inline Limbs random_scalar(std::mt19937_64 &g) {
  for (;;) {
    Limbs k = {g(), g(), g(), g()};
    const Fp256Nat kn(k);
    if (kn < n256_order && kn != Fp256Nat(0)) return k;
  }
}
inline P256::ECPoint gmult(const Limbs &k) {
  P256::ECPoint p = p256.scalar_multf(p256.generator(), Fp256Nat(k));
  p256.normalize(p);
  return p;
}
// r || s of the ECDSA signature on E under the key D with nonce K:
// r = x(k G) mod n, s = (e + r d) / k mod n.
inline std::vector<uint8_t> sign(const Limbs &d, const Limbs &e,
                                 const Limbs &k) {
  const auto &fn = p256_scalar;
  const P256::ECPoint kg = gmult(k);
  const auto r = fn.to_montgomery(p256_base.from_montgomery(kg.x));
  const auto num = fn.addf(fn.to_montgomery(Fp256Nat(e)),
                           fn.mulf(r, fn.to_montgomery(Fp256Nat(d))));
  const auto s = fn.mulf(num, fn.invertf(fn.to_montgomery(Fp256Nat(k))));
  std::vector<uint8_t> out = be(limbs_of(fn.from_montgomery(r)));
  const auto sb = be(limbs_of(fn.from_montgomery(s)));
  out.insert(out.end(), sb.begin(), sb.end());
  return out;
}
inline Limbs negate_scalar(const Limbs &d) {
  return limbs_of(p256_scalar.from_montgomery(
      p256_scalar.negf(p256_scalar.to_montgomery(Fp256Nat(d)))));
}
inline Limbs digest_limbs(const std::vector<uint8_t> &e) {
  return examples::mdoc::p256_ecdsa::host::be_limbs(e.data());
}

// What a re-signed case changes.
struct Resign {
  // The key the MSO holds (H's dpkx, dpky), 32 big-endian bytes each.
  std::vector<uint8_t> mso_x, mso_y;
  // The device key and its secret (domain A's dpk, and the key
  // that signs e2).
  Limbs device_d{};
  P256::ECPoint device_q;
  // Whether the issuer signs a digest other than the MSO's (one bit of e
  // flipped): domain A's e then differs from H's.
  bool other_digest = false;
};
// X with the MSO's device key replaced by R.mso_x, R.mso_y, the digest
// recomputed, the issuer key and signature replaced by ones of a random
// issuer key, and the device key and signature by R's.
inline Instance resigned(Instance x, const Resign &r, std::mt19937_64 &g) {
  auto &buf = x.data.hash.buffer;
  auto put = [&buf](const std::vector<uint8_t> &old,
                    const std::vector<uint8_t> &now) {
    const auto at = std::search(buf.begin(), buf.end(), old.begin(), old.end());
    check(at != buf.end(), "resigned: the key bytes are not in the MSO");
    std::copy(now.begin(), now.end(), at);
  };
  const std::vector<uint8_t> ox(x.data.dpk.begin(), x.data.dpk.begin() + 32),
      oy(x.data.dpk.begin() + 32, x.data.dpk.end());
  put(ox, r.mso_x);
  put(oy, r.mso_y);
  SHA256 h;
  h.Update(buf.data(), x.data.hash.length);
  std::vector<uint8_t> e(kSHA256DigestSize);
  h.DigestData(e.data());
  if (r.other_digest) e[31] ^= 1;
  const Limbs di = random_scalar(g);
  const P256::ECPoint qi = gmult(di);
  x.statement.issuer_x = qi.x;
  x.statement.issuer_y = qi.y;
  x.data.e = e;
  x.data.issuer_sig = sign(di, digest_limbs(e), random_scalar(g));
  x.data.dpk = be(r.device_q.x);
  const auto y = be(r.device_q.y);
  x.data.dpk.insert(x.data.dpk.end(), y.begin(), y.end());
  x.data.device_sig = sign(r.device_d, x.statement.e2, random_scalar(g));
  return x;
}
// The re-signed case whose MSO holds the device key (d G): both domains
// agree.
inline Resign agreeing(std::mt19937_64 &g) {
  Resign r;
  r.device_d = random_scalar(g);
  r.device_q = gmult(r.device_d);
  r.mso_x = be(r.device_q.x);
  r.mso_y = be(r.device_q.y);
  return r;
}

// The x' != x with (x', y) on the curve beside (x, y), when one exists:
// the other roots of X^3 - 3 X + b - y^2 = (X - x)(X^2 + x X + x^2 - 3),
// X = (-x +- sqrt(12 - 3 x^2)) / 2.
inline bool other_x(const AElt &x, AElt &out) {
  const auto &f = p256_base;
  const AElt disc =
      f.subf(f.of_scalar(12), f.mulf(f.of_scalar(3), f.mulf(x, x)));
  // p = 3 mod 4: sqrt(a) = a^((p + 1) / 4) when a is a square.
  const Limbs ex = {0, 0x40000000, 0x4000000000000000, 0x3fffffffc0000000};
  AElt s = f.one(), b = disc;
  for (size_t i = 0; i < 256; ++i) {
    if ((ex[i / 64] >> (i % 64)) & 1) s = f.mulf(s, b);
    b = f.mulf(b, b);
  }
  if (f.mulf(s, s) != disc) return false;
  out = f.mulf(f.subf(s, x), f.invertf(f.of_scalar(2)));
  return out != x;
}

}  // namespace proofs::gordiehowe::examples::mdoc::full

#endif  // PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_EXAMPLES_MDOC_MDOC_TESTING_H_
