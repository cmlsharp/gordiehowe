// Copyright 2026 Chad Sharp and Paul Grubbs
// SPDX-License-Identifier: Apache-2.0

// GordieHowe: the ECDSA mDL, Longfellow's ZkSpec v7 relation, as one proof
// over two domains. The prover shows that it holds an MSO the issuer
// signed, valid at the public time now, that contains the requested
// attributes and the device key, and a device signature under that key.
// Domain H = GF(2^128) hashes the MSO and checks its
// windows, dates and requested attributes (mdoc_hash.h). Domain A = F_p256
// verifies the issuer's ECDSA signature on the MSO's digest e and the
// device's signature on e2 under the device key (dpkx, dpky)
// (mdoc_signatures.h). A MAC equality joins the domains on e, dpkx and
// dpky. H holds an integer's bits in byte order and A least significant
// first, so the equality reads H through lib::arith::big_endian_bit_order.
//
// mdoc<Sys>(...) compiles the relation for a fixed number of attributes
// and MSO blocks; mdoc_builders.h builds its statement and witness.

#ifndef PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_EXAMPLES_MDOC_MDOC_H_
#define PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_EXAMPLES_MDOC_MDOC_H_

#include <array>
#include <cstddef>
#include <cstdint>
#include <type_traits>
#include <vector>

#include "gordiehowe/examples/mdoc/mdoc_hash.h"
#include "gordiehowe/examples/mdoc/mdoc_signatures.h"
#include "gordiehowe/lib/arith.h"
#include "gordiehowe/relation.h"
#include "gordiehowe/system.h"

namespace proofs::gordiehowe::examples::mdoc {

// The statement: v7's public inputs. Per requested attribute a, attr.id[a]
// is "<text header><identifier>" and attr.value[a] the CBOR value, each
// padded with zeros, attr.id_len[a] = 1 + 17 + 1 + |identifier| and
// attr.value_len[a] = |value| + 13 (v7's fill_attribute). The issuer key
// is (pkX, pkY) on the curve, and e2 the 128-bit halves (lo, hi) of
// SHA-256(DeviceAuthenticationBytes) read as a big-endian integer.
template <template <class> class F>
struct MdocStatement {
  // 20 ASCII bytes
  F<std::array<uint8_t, kDateBytes>> now;
  MdocAttributes<F> attr;
  F<std::array<examples::mdoc::p256_ecdsa::Elt, 2>> issuer_pk;
  F<std::array<examples::mdoc::p256_ecdsa::Elt, 2>> e2;
};
// The witness: the MSO (the buffer after kCose1Prefix, mso_bytes(blocks)
// bytes) and its message length L (prefix included), v7's window offsets,
// the items, their lengths and SaltedHash fields (i1 i2 i3 l0..l3 in 12
// bits each, then perm, least significant bit first), the MSO's digest e,
// the issuer's signature r || s, the device key dpkx || dpky (big-endian)
// and the device's signature.
template <template <class> class F>
struct MdocWitness {
  // mso_bytes(blocks)
  F<std::vector<uint8_t>> mso;
  F<uint16_t> mso_length;
  // kFixedWindows + n
  F<std::vector<uint16_t>> offsets;
  F<std::vector<std::array<uint8_t, kItemBytes>>> items;
  F<std::vector<uint8_t>> item_lengths;
  F<std::vector<std::array<bool, kSaltedBits>>> salted;
  F<std::array<uint8_t, 32>> e;
  F<std::array<uint8_t, 64>> issuer_sig;
  F<std::array<uint8_t, 64>> dpk;
  F<std::array<uint8_t, 64>> device_sig;
};

// The values the relation declares that its caller reads.
template <class D, class F>
struct Mdoc {
  MdocHashDomain<D, F> hash;
  examples::mdoc::signatures::MdocSignatureDomain signatures;
};

// v7 mdoc in system CS over the statement ST and the witness W: the hashes
// in domain H of profile H_PROFILE, the signatures in domain A of profile
// A_PROFILE, and e, dpkx and dpky equal across them.
// DEVICE_SIGNATURE false is a test-only ablation (the device-signature
// ablation): the device's ECDSA verification (ecdsa_verify_private_key,
// with its statement value e2) and the crossing of dpkx and dpky are not
// declared, so e2, the witness's dpk and device_sig are never read; domain
// H's relation, the deviceKeyInfo window among it, and the issuer's
// verification stay.
template <class Sys, class HP, class AP>
auto mdoc_relation(Sys &cs, const MdocStatement<In> &st,
                   const MdocWitness<In> &w,
                   const HP &h_profile, const AP &a_profile,
                   bool device_signature = true) {
  namespace ms = examples::mdoc::signatures;
  auto &H = cs.domain(h_profile, "H");
  auto &A = cs.domain(a_profile, "A");
  const auto hash_in = mdoc_hash_inputs(H, st);
  const auto sig_in = ms::mdoc_signature_inputs(A, st, device_signature);
  auto hash = mdoc_hash_domain(cs, H, hash_in, w);
  auto sig = ms::mdoc_signature_domain(cs, A, sig_in, w, device_signature);
  const std::vector<size_t> order = lib::arith::big_endian_bit_order(32);
  assert_equal(hash.e[order].named("cross.e"), sig.e);
  if (device_signature) {
    assert_equal(hash.dpkx[order].named("cross.dpkx"), sig.dpkx);
    assert_equal(hash.dpky[order].named("cross.dpky"), sig.dpky);
  }
  using D = std::decay_t<decltype(H)>;
  using F = std::decay_t<decltype(H.field())>;
  return Mdoc<D, F>{hash, sig};
}

// A statement and a witness of N_ATTR attributes and an MSO buffer of
// BLOCKS SHA-256 blocks as shape values (their vectors' lengths) for
// compile().
inline MdocStatement<Value> mdoc_statement_shape(size_t n_attr) {
  MdocStatement<Value> st{};
  shape_hash_statement(st, n_attr);
  return st;
}
inline MdocWitness<Value> mdoc_witness_shape(size_t n_attr,
                                             size_t blocks = kBlocks) {
  MdocWitness<Value> w{};
  w.mso.resize(mso_bytes(blocks));
  shape_hash_witness(w, n_attr);
  return w;
}

// The relation for N_ATTR attributes and an MSO buffer of BLOCKS SHA-256
// blocks in system type SYS, compiled under PROFILE with OPTIONS;
// DEVICE_SIGNATURE false is the device-signature ablation (mdoc_relation),
// the system gh-mdoc-nodevice.
template <class Sys, class HP, class AP>
Relation<MdocStatement<Value>, MdocWitness<Value>> mdoc(
    const CompileProfile &profile, const HP &h_profile, const AP &a_profile,
    size_t n_attr, size_t blocks = kBlocks, bool device_signature = true,
    const CompileOptions &options = {}) {
  return compile<MdocStatement, MdocWitness>(
      profile,
      [&](Sys &cs, MdocStatement<In> st, MdocWitness<In> w) {
        mdoc_relation(cs, st, w, h_profile, a_profile, device_signature);
      },
      device_signature ? "gh-mdoc" : "gh-mdoc-nodevice",
      mdoc_statement_shape(n_attr), mdoc_witness_shape(n_attr, blocks),
      options);
}

}  // namespace proofs::gordiehowe::examples::mdoc

#endif  // PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_EXAMPLES_MDOC_MDOC_H_
