// Copyright 2026 Chad Sharp and Paul Grubbs
// SPDX-License-Identifier: Apache-2.0

// GordieHowe: the ML-DSA-44 private ring, the parts both arms share.
//
// The statement is R public keys, a message and a context. The prover
// shows that it holds a signature on the message under one member's key
// without revealing which. This header holds the ring's inputs and:
//   ring_rows      the members' rows, public computations of the
//                  statement: tr_j, the key part in the arm's form, and
//                  mu_j as 24 limbs of 22 bits
//   select_member  the committed record (key part, mu, index) and its
//                  selection from the table of rows (lib/table.h)
//   ring_crossing  domain H's challenge equals domain A's
// mldsa_ring_native.h and mldsa_ring_carrier.h check the signature in
// domain A, and domain H recomputes the challenge from the committed mu.
// A ring whose size is not a power of two is padded by duplicating real
// members, because a zero row would select the zero key.

#ifndef PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_EXAMPLES_RINGS_MLDSA_RING_H_
#define PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_EXAMPLES_RINGS_MLDSA_RING_H_

#include <array>
#include <cstddef>
#include <cstdint>
#include <memory>
#include <type_traits>
#include <utility>
#include <vector>

#include "gordiehowe/ct.h"
#include "gordiehowe/examples/mldsa/mldsa_gadgets.h"
#include "gordiehowe/examples/mldsa/mldsa_params.h"
#include "gordiehowe/examples/rings/mldsa_ring_host.h"
#include "gordiehowe/examples/rings/mldsa_ring_params.h"
#include "gordiehowe/lib/table.h"
#include "gordiehowe/relation.h"
#include "gordiehowe/system.h"
#include "gordiehowe/examples/rings/ml_dsa_ring_shake.h"

namespace proofs::gordiehowe::examples::mldsa {

// ---------------------------------------------------------------- inputs --

// The ring statement: the members' keys (pkEncode, kPkBytes each), the
// message and the context; the ring size and the lengths are fixed per
// relation by the shape value. Every kPkBytes-byte string is a pkEncode
// (rho, then 10-bit t1 coefficients), so a key needs no codec.
template <template <class> class F>
struct MLDSARingStatement {
  F<std::vector<std::array<uint8_t, kPkBytes>>> pk;
  F<std::vector<uint8_t>> msg;
  F<std::vector<uint8_t>> ctx;
};
// The selected member, a record member of the ring witness: its key part
// in the arm's spectral form (canonical integers), its mu, and its index
// in the ring (below the padded size).
template <template <class> class F>
struct MLDSARingMember {
  F<std::array<std::array<std::array<uint64_t, kN>, kL>, kK>> a_hat;
  F<std::array<std::array<uint64_t, kN>, kK>> t1;
  F<std::array<uint8_t, kMuBytes>> mu;
  F<uint32_t> index;
};
// The ring witness: the selected member and the decoded signature (z as
// centered integers, the hint bits, c~).
template <template <class> class F>
struct MLDSARingWitness {
  MLDSARingMember<F> member;
  F<std::array<std::array<int32_t, kN>, kL>> z;
  F<std::array<std::array<bool, kN>, kK>> h;
  F<std::array<uint8_t, kCTildeBytes>> c_tilde;
};

// The shape values of a ring of R members, MSG_BYTES-byte messages and
// CTX_BYTES-byte contexts.
inline MLDSARingStatement<Value> ring_statement_shape(size_t R,
                                                      size_t msg_bytes,
                                                      size_t ctx_bytes) {
  MLDSARingStatement<Value> st{};
  st.pk.resize(R);
  st.msg.resize(msg_bytes);
  st.ctx.resize(ctx_bytes);
  return st;
}

// --------------------------------------------------------------- records --

// The elements of HF that hold tr's 64 bytes.
template <class HF>
constexpr size_t tr_elements = (kTrBytes + HF::kBytes - 1) / HF::kBytes;

// The members' rows in two column blocks: the key part (the arm's decode,
// cached per statement) and the mu limbs (per message), both of A's field.
template <class HF, class AF>
struct RingRows {
  // [R][elements of 64 bytes]
  Ref<HF, Field, Public> tr;
  // [R][5120]
  Ref<AF, Subfield<>, Public> keys;
  // [R][24]
  Ref<AF, Subfield<>, Public> mu;
};

// The rows of the ring statement ST, in scope S. DECODE_ID and DECODE name
// and compute a member's key part from its pkEncode (5120 canonical
// integers below q); the decode runs once per ring (cache).
template <class DH, class DA, class Decode,
          class HF = std::decay_t<decltype(std::declval<DH &>().field())>,
          class AF = std::decay_t<decltype(std::declval<DA &>().field())>>
RingRows<HF, AF> ring_rows(const Scope &s, DH &H, DA &A,
                           const MLDSARingStatement<In> &st,
                           const Computes &decode_id, Decode decode) {
  using HElt = typename HF::Elt;
  using AElt = typename AF::Elt;
  const auto &pk = st.pk;
  const auto &msg = st.msg;
  const auto &ctx = st.ctx;
  const size_t R = pk.dims().at(0);
  const size_t msg_bytes = msg.dims().at(0);
  const size_t ctx_bytes = ctx.dims().at(0);
  if (ctx_bytes > 255) fail("ring_rows: a context of over 255 bytes");
  if (R < 2) fail("ring_rows: a ring of fewer than two members");
  const HF *ph = &H.field();
  const AF *pa = &A.field();
  auto sh256 = std::make_shared<const ::proofs::Shake256>();
  RingRows<HF, AF> rows;
  // tr_j, its bytes in the elements' serialization.
  rows.tr =
      s[H].pub(Field{}, "tr", Shape{R, tr_elements<HF>}, depends_on(pk),
               computes("shake256", {kTrBytes, R}),
               [ph, R, sh256](const std::vector<uint8_t> &keys) {
                 std::vector<HElt> out;
                 for (size_t j = 0; j < R; ++j) {
                   std::array<uint8_t, tr_elements<HF> * HF::kBytes> t{};
                   (*sh256)(keys.data() + j * kPkBytes, kPkBytes, t.data(),
                            kTrBytes);
                   for (size_t e = 0; e < tr_elements<HF>; ++e)
                     out.push_back(
                         *ph->of_bytes_field(t.data() + e * HF::kBytes));
                 }
                 return out;
               })
          .cache();
  rows.keys =
      s[A].pub(Subfield{}, "keys", Shape{R, kKeyCells}, depends_on(pk),
               decode_id,
               [pa, R, decode](const std::vector<uint8_t> &keys) {
                 std::vector<AElt> out;
                 out.reserve(R * kKeyCells);
                 for (size_t j = 0; j < R; ++j) {
                   const std::vector<uint8_t> key(
                       keys.begin() + long(j * kPkBytes),
                       keys.begin() + long((j + 1) * kPkBytes));
                   for (uint64_t x : decode(key))
                     out.push_back(pa->of_scalar(x));
                 }
                 return out;
               })
          .cache();
  // mu_j from tr_j, the message and the context, as 22-bit limbs.
  auto limbs = [ph, pa, R, sh256](const Tensor<HElt> &tr,
                                  const std::vector<uint8_t> &m,
                                  const std::vector<uint8_t> &c) {
    std::vector<AElt> out;
    out.reserve(R * kMuLimbs);
    for (size_t j = 0; j < R; ++j) {
      std::array<uint8_t, tr_elements<HF> * HF::kBytes> t{};
      for (size_t e = 0; e < tr_elements<HF>; ++e)
        ph->to_bytes_field(t.data() + e * HF::kBytes,
                           tr[j * tr_elements<HF> + e]);
      const auto mu = ring_host::mu_of(*sh256, t.data(), m, c);
      for (uint64_t x : ring_host::mu_limbs(mu.data()))
        out.push_back(pa->of_scalar(x));
    }
    return out;
  };
  const Computes mu_id =
      computes("mldsa_mu_limbs", {kMuLimbBits, R, msg_bytes, ctx_bytes});
  // The plan export: mu as limbs of the rows' second block (a statement
  // value of A's field, no domain).
  s.note("mu-limbs", "mu",
         NoteValues{{"muBits", __int128(kMuBits)},
                    {"limbs", __int128(kMuLimbs)},
                    {"limbBits", __int128(kMuLimbBits)},
                    {"rows", __int128(R)},
                    {"msgBytes", __int128(msg_bytes)},
                    {"ctxBytes", __int128(ctx_bytes)}});
  if (ctx_bytes > 0) {
    rows.mu = s[A].pub(Subfield{}, "mu", Shape{R, kMuLimbs},
                       depends_on(rows.tr, msg, ctx), mu_id, limbs);
  } else {
    rows.mu = s[A].pub(
        Subfield{}, "mu", Shape{R, kMuLimbs}, depends_on(rows.tr, msg), mu_id,
        [limbs](const Tensor<HElt> &tr, const std::vector<uint8_t> &m) {
          return limbs(tr, m, {});
        });
  }
  return rows;
}

// --------------------------------------------------------------- members --

// The selected member's committed record and its index: A_hat and t1 in
// the arm's spectral form, and mu's 512 bits.
template <class AF>
struct Member {
  // [K][L][N]
  Ref<AF, Subfield<>, Committed> a_hat;
  // [K][N]
  Ref<AF, Subfield<>, Committed> t1;
  // [512], bit i of byte k at 8k + i
  Ref<AF, Bit, Committed> mu;
  // [log2 R'], least significant first
  Ref<AF, Bit, Committed> index;
};

// MU's 24 limbs of 22 bits (the last zero-extended), behind a layer
// boundary: materialize shares each coordinate (ntt_gadget::share) before
// the digest reads them.
template <class AF, class P>
auto mu_record_limbs(const Ref<AF, Bit, P> &mu) {
  return materialize(mu.zero_extend(kMuLimbs * kMuLimbBits)
                         .reshape(Shape{kMuLimbs, kMuLimbBits})
                         .named(mu.name() + ".limb_bits")
                         .from_digits(2));
}

// The selected member, in scope S of domain A: the record (A_hat, t1, mu)
// committed from the witness W, and the record's selection from the table
// of ROWS under MAP (the arm's row map: the key part's 20 leaves of N, then
// the 24 mu limbs) by the index bits select.index, committed from the
// witness member's index.
template <class D, class HF, class AF>
Member<AF> select_member(const Scope &s, D &A,
                         const MLDSARingWitness<In> &w,
                         const RingRows<HF, AF> &rows,
                         lib::table::RowMap<AF> map) {
  Member<AF> m;
  m.a_hat = A.priv(Subfield{}, w.member.a_hat);
  m.t1 = A.priv(Subfield{}, w.member.t1);
  m.mu = A.priv(w.member.mu).flat();
  const auto table = lib::table::public_table(s, A, "table", std::move(map),
                                              rows.keys, rows.mu);
  const AF *pf = &A.field();
  const size_t bits = table.index_bits;
  // The index's bits, least significant first, from its u32le bytes.
  m.index = s[A].priv(
      Bit{}, "select.index", bits, depends_on(w.member.index),
      [pf, bits](const std::vector<uint8_t> &b) {
        size_t index = 0;
        for (size_t k = 0; k < b.size(); ++k) index |= size_t(b[k]) << (8 * k);
        std::vector<typename AF::Elt> out;
        for (size_t t = 0; t < bits; ++t)
          out.push_back(ct::bit_elt(*pf, (index >> t) & 1));
        return out;
      });
  const std::vector<Expr<AF>> record = {m.a_hat, m.t1, mu_record_limbs(m.mu)};
  lib::table::select_row(s, table, "select", m.index, record);
  return m;
}

// The arm's row map: KEY (the map of one key polynomial) for each of the
// 20 polynomials, then the identity on the 24 mu limbs.
template <class AF>
lib::table::RowMap<AF> member_map(const lib::table::RowMap<AF> &key) {
  return lib::table::RowMap<AF>::blocks(
      {{key, kKeyPolys}, {lib::table::RowMap<AF>::identity(kMuLimbs), 1}});
}

// ---------------------------------------------------------------- crossing --

// Domain H's challenge equals domain A's. Domain H's copies of mu and w1
// state their own equalities (H.copy_of), and the MAC lowering merges the
// three into one MAC per domain pair, in the order mu, w1, the (support,
// sign) pairs.
template <class HS, class AF>
void ring_crossing(const Scope &s, const HS &hash,
                   const Ref<AF, Bit, Committed> &c) {
  assert_equal(hash.c_H.flat(), c.flat());
}

}  // namespace proofs::gordiehowe::examples::mldsa

#endif  // PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_EXAMPLES_RINGS_MLDSA_RING_H_
