// Copyright 2026 Chad Sharp and Paul Grubbs
// SPDX-License-Identifier: Apache-2.0

// GordieHowe: mdoc's domain H (mdoc_hash.h) alone: the test and bench
// system, and its statement and witness from Longfellow's mdoc test
// vectors (lib/circuits/mdoc/mdoc_examples.h, mdoc_test_attributes.h)
// through Longfellow's own witness parser (MdocHashWitness,
// mdoc_witness.h).
//
// The system is domain H's relation at the ROM parameters, plus a stand-in
// for domain A: public expected values of the crossing
// values e, dpkx and dpky, equated with them in a circuit constraint, so a
// proof is bound to the issuer-signed digest and device key.

#ifndef PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_EXAMPLES_MDOC_MDOC_HASH_TESTING_H_
#define PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_EXAMPLES_MDOC_MDOC_HASH_TESTING_H_

#include <algorithm>
#include <array>
#include <cstddef>
#include <cstdint>
#include <memory>
#include <string>
#include <utility>
#include <vector>

#include "circuits/mdoc/mdoc_examples.h"
#include "circuits/mdoc/mdoc_test_attributes.h"
#include "circuits/mdoc/mdoc_witness.h"
#include "circuits/mdoc/mdoc_zk.h"
#include "gordiehowe/examples/shared/packed_bits.h"
#include "params/param_sets.h"
#include "ec/p256.h"
#include "gf2k/lch14_reed_solomon.h"
#include "gordiehowe/examples/mdoc/mdoc_hash.h"
#include "gordiehowe/examples/mdoc/mdoc_hash_builders.h"
#include "gordiehowe/instances.h"
#include "gordiehowe/relation.h"
#include "gordiehowe/system.h"
#include "util/crypto.h"

namespace proofs::gordiehowe::examples::mdoc::testing {

using P = param_sets::ROMParams;
using HF = P::HashField;
using PH = P::ProtocolHash;
using Elt = HF::Elt;
using RS = LCH14ReedSolomonFactory<HF>;
using Sys = ConstraintSystem<PH, HF>;
using Assignment = Sys::Assignment;
using Profile = DomainProfile<HF, RS, PH>;

inline const HF &hf() {
  static const HF *f = new HF;
  return *f;
}
inline const RS &rs() {
  static const RS *r = new RS(hf());
  return *r;
}

// H at Longfellow v7's Ligero: rate 7 and 132 opened columns at unique
// decoding (kLigeroRatev7, kLigeroNreqv7), block_enc from the packed-layout
// search: the v7 configuration, at Longfellow's parameters, of mdoc_test's
// tests and of the mdoc bench's compare (--config v7). The bench worker
// (gh-mdoc) builds H at its field's default profile (mdoc_testing.h's
// list_h_profile).
inline Profile profile() {
  Profile p;
  p.f = &hf();
  p.rsf = &rs();
  p.rates = param_sets::placement_rates<HF>();
  p.field_name = "GF(2^128)";
  p.rate = kLigeroRatev7;
  p.nreq = kLigeroNreqv7;
  p.has_subfield = true;
  p.prime = Space::kPrime;
  const size_t rate = p.rate, opened = p.opened();
  p.block_enc = [rate, opened](const Circuit<HF> &c, size_t, size_t) {
    return h_block_enc<PH>("GH-MDOC-H", c, rate, opened);
  };
  return p;
}

// One case: a test vector and its requested attributes.
struct Case {
  size_t doc = 0;
  std::vector<RequestedAttribute> attrs;
};
// The bench's cases: doc 0 with age_over_18, doc 3 with the first N of
// age_over_18, familyname_mustermann, birthdate_1971_09_01, height_175.
inline Case bench_case(size_t doc, size_t n) {
  const RequestedAttribute all[4] = {test::age_over_18,
                                     test::familyname_mustermann,
                                     test::birthdate_1971_09_01,
                                     test::height_175};
  return Case{doc, std::vector<RequestedAttribute>(all, all + n)};
}

// v7's fill_attribute layout of a requested attribute.
inline examples::mdoc::MdocAttributeStatement statement_of(
    const RequestedAttribute &a) {
  examples::mdoc::MdocAttributeStatement x;
  std::vector<uint8_t> id;
  append_text_len(id, a.id_len);
  id.insert(id.end(), a.id, a.id + a.id_len);
  for (size_t j = 0; j < id.size() && j < 32; ++j) x.id[j] = id[j];
  for (size_t j = 0; j < a.cbor_value_len && j < 64; ++j)
    x.value[j] = a.cbor_value[j];
  x.id_len = uint8_t(1 + 17 + 1 + a.id_len);
  x.value_len = uint8_t(a.cbor_value_len + 12 + 1);
  return x;
}

// What a case's witness holds: the prover inputs, and the crossing values
// as bytes (the digest, and the device key's coordinates big-endian).
struct Witness {
  examples::mdoc::MdocHashData data;
  std::vector<uint8_t> e, dpkx, dpky;
};
// Longfellow's witness parser on case C (mdoc_witness.h), the buffer cut
// to its first BLOCKS SHA-256 blocks (v7's kBlocks = 40 by default). The
// message and its padding must end within them: L + 9 <= 64 BLOCKS.
inline Witness witness_of(const Case &c,
                          size_t blocks = examples::mdoc::kBlocks) {
  const MdocTests &t = mdoc_tests[c.doc];
  auto hw = std::make_unique<MdocHashWitness<P256, HF>>(c.attrs.size(), p256,
                                                         hf());
  const auto rc = hw->compute_witness(t.mdoc, t.mdoc_size, t.transcript,
                                      t.transcript_size, c.attrs.data(),
                                      c.attrs.size(), 7);
  check(rc == MDOC_PROVER_SUCCESS, "mdoc test vector: witness");
  check(blocks >= 1 && blocks <= examples::mdoc::kBlocks,
        "witness_of: the block count");
  Witness w;
  auto &d = w.data;
  d.length = kCose1PrefixLen + 2 + hw->pm_.t_mso_.len;
  check(d.length + 9 <= 64 * blocks,
        "witness_of: the MSO does not fit the buffer");
  d.buffer.assign(hw->signed_bytes_, hw->signed_bytes_ + 64 * blocks);
  // Longfellow's buffer holds zeros after the padded message.
  for (size_t i = 64 * blocks; i < examples::mdoc::kBufBytes; ++i)
    check(hw->signed_bytes_[i] == 0, "witness_of: a byte past the buffer");
  d.offsets = {hw->pm_.valid_from_.k, hw->pm_.valid_until_.k,
               hw->pm_.dev_key_info_.k, hw->pm_.value_digests_.k};
  for (size_t a = 0; a < c.attrs.size(); ++a) {
    d.offsets.push_back(hw->attr_mso_[a].v);
    examples::mdoc::MdocHashData::Item it;
    for (size_t i = 0; i < examples::mdoc::kItemBytes; ++i)
      it.bytes[i] = hw->attr_bytes_[a][i];
    uint64_t bits = 0;
    for (size_t i = 0; i < 8; ++i) bits = (bits << 8) | it.bytes[120 + i];
    it.length = size_t(bits / 8);
    const auto &sh = hw->attr_sh_[a];
    it.i1 = sh.i1;
    it.i2 = sh.i2;
    it.i3 = sh.i3;
    for (size_t j = 0; j < 4; ++j) it.l[j] = sh.l[j];
    it.perm = sh.perm;
    d.items.push_back(it);
  }
  SHA256 h;
  h.Update(d.buffer.data(), d.length);
  w.e.resize(kSHA256DigestSize);
  h.DigestData(w.e.data());
  const size_t pmso = hw->pm_.t_mso_.pos + 5;
  const uint8_t *x = &t.mdoc[pmso + hw->pm_.dev_key_pkx_.pos];
  const uint8_t *y = &t.mdoc[pmso + hw->pm_.dev_key_pky_.pos];
  w.dpkx.assign(x, x + 32);
  w.dpky.assign(y, y + 32);
  return w;
}

// The test system's statement: domain H's members and the stand-in's
// expected crossing values, the digest and the device key's coordinates
// (32 bytes each, as H reads them).
template <template <class> class F>
struct HashStatement {
  F<std::array<uint8_t, examples::mdoc::kDateBytes>> now;
  examples::mdoc::MdocAttributes<F> attr;
  F<std::array<uint8_t, 32>> want_e;
  F<std::array<uint8_t, 32>> want_dpkx;
  F<std::array<uint8_t, 32>> want_dpky;
};
// The test system's witness: domain H's members.
template <template <class> class F>
struct HashWitness {
  F<std::array<uint8_t, examples::mdoc::kMsoBytes>> mso;
  F<uint16_t> mso_length;
  F<std::vector<uint16_t>> offsets;
  F<std::vector<std::array<uint8_t, examples::mdoc::kItemBytes>>> items;
  F<std::vector<uint8_t>> item_lengths;
  F<std::vector<std::array<bool, examples::mdoc::kSaltedBits>>> salted;
};

// Domain H's relation in domain H of profile P, and the stand-in for
// domain A: the crossing values equal the statement's expected ones.
inline void hash_relation(Sys &cs, const HashStatement<In> &st,
                          const HashWitness<In> &w,
                          const Profile &p) {
  auto &H = cs.domain(p, "H");
  const auto in = examples::mdoc::mdoc_hash_inputs(H, st);
  const auto hashed = examples::mdoc::mdoc_hash_domain(cs, H, in, w);
  const auto want_e = st.want_e.bits(H).flat();
  const auto want_dpkx = st.want_dpkx.bits(H).flat();
  const auto want_dpky = st.want_dpky.bits(H).flat();
  const Expr<HF, Bit> got = hashed.e;
  const Expr<HF, Bit> want = want_e;
  assert_equal(got.concat(hashed.dpkx).concat(hashed.dpky),
               want.concat(want_dpkx).concat(want_dpky), "crossing");
}

// The relation for N_ATTR attributes, with the assignments of host values
// for the tests and benchmarks that drive the prover directly.
struct MdocHashSystem {
  Relation<HashStatement<Value>, HashWitness<Value>> rel;
  Sys &cs;

  MdocHashSystem(const Profile &p, size_t n_attr)
      : rel(compile<HashStatement, HashWitness>(
            CompileProfile{},
            [&p](Sys &cs, HashStatement<In> st, HashWitness<In> w) {
              hash_relation(cs, st, w, p);
            },
            "gh-mdoc-hash", shape_statement(n_attr), shape_witness(n_attr))),
        cs(rel.typed<Sys>().system()) {}

  static HashStatement<Value> shape_statement(size_t n_attr) {
    HashStatement<Value> st{};
    examples::mdoc::shape_hash_statement(st, n_attr);
    return st;
  }
  static HashWitness<Value> shape_witness(size_t n_attr) {
    HashWitness<Value> w{};
    examples::mdoc::shape_hash_witness(w, n_attr);
    return w;
  }
  const Sys::Compiled &compiled() const { return rel.typed<Sys>().compiled(); }
  Assignment statement(const Case &c, const Witness &w,
                       const uint8_t *now = nullptr) const {
    const uint8_t *nw = now != nullptr ? now : mdoc_tests[c.doc].now;
    std::vector<examples::mdoc::MdocAttributeStatement> attrs;
    for (const auto &a : c.attrs) attrs.push_back(statement_of(a));
    HashStatement<Value> st{};
    examples::mdoc::set_hash_statement(
        st, std::vector<uint8_t>(nw, nw + examples::mdoc::kDateBytes), attrs);
    check(w.e.size() == 32 && w.dpkx.size() == 32 && w.dpky.size() == 32,
          "MdocHashSystem: the crossing values");
    std::copy(w.e.begin(), w.e.end(), st.want_e.begin());
    std::copy(w.dpkx.begin(), w.dpkx.end(), st.want_dpkx.begin());
    std::copy(w.dpky.begin(), w.dpky.end(), st.want_dpky.begin());
    return rel.typed<Sys>().statement(st);
  }
  Assignment witness(const examples::mdoc::MdocHashData &d) const {
    HashWitness<Value> w{};
    examples::mdoc::set_hash_witness(w, d);
    return rel.typed<Sys>().witness(w);
  }
};

}  // namespace proofs::gordiehowe::examples::mdoc::testing

#endif  // PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_EXAMPLES_MDOC_MDOC_HASH_TESTING_H_
