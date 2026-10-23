// Copyright 2026 Chad Sharp and Paul Grubbs
// SPDX-License-Identifier: Apache-2.0

// GordieHowe: domain A of the ECDSA mDL, F_p256: Longfellow's v7 signature
// circuit without its MACs. ecdsa_verify_public_key checks the issuer's
// signature on the private digest e under the public issuer key, and
// ecdsa_verify_private_key the device's signature on the public digest e2
// under the private device key. Both prove X = [s^-1] (e G + r Q) with
// x(X) = r as integers, from p256_ecdsa.h's fixed- and variable-base
// chains, with a complete addition wherever a valid signature can make an
// addition exceptional. mdoc_signature_domain runs both and returns e, dpkx
// and dpky as bits, least significant first, for the crossing into domain
// H. Unlike v7, e may exceed n, and dpkx and dpky must lie below p.

#ifndef PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_EXAMPLES_MDOC_MDOC_SIGNATURES_H_
#define PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_EXAMPLES_MDOC_MDOC_SIGNATURES_H_

#include <cstddef>
#include <cstdint>
#include <string>
#include <type_traits>
#include <vector>

#include "ec/p256.h"
#include "gordiehowe/ct.h"
#include "gordiehowe/examples/p256/p256_ecdsa.h"
#include "gordiehowe/relation.h"
#include "gordiehowe/system.h"

namespace proofs::gordiehowe::examples::mdoc::signatures {

namespace host = p256_ecdsa::host;
using p256_ecdsa::Bits;
using p256_ecdsa::CellPoint;
using p256_ecdsa::Cells;
using p256_ecdsa::Digits;
using p256_ecdsa::E;
using p256_ecdsa::Elt;
using p256_ecdsa::FbTable;
using p256_ecdsa::FixedBase;
using p256_ecdsa::Limbs;
using p256_ecdsa::ModN;
using p256_ecdsa::Pub;
using p256_ecdsa::PPt;
using p256_ecdsa::VarBase;
using p256_ecdsa::add_complete;
using p256_ecdsa::affine_of;
using p256_ecdsa::bind_mod_n;
using p256_ecdsa::check_r;
using p256_ecdsa::digit_values;
using p256_ecdsa::fixed_base;
using p256_ecdsa::fp;
using p256_ecdsa::generator_table;
using p256_ecdsa::kSteps;
using p256_ecdsa::kTable;
using p256_ecdsa::kWindows;
using p256_ecdsa::point_from_bits;
using p256_ecdsa::projective;
using p256_ecdsa::var_base;

inline Limbs of_halves(const Elt &lo, const Elt &hi) {
  const Limbs l = host::canonical(lo);
  const Limbs h = host::canonical(hi);
  return {l[0], l[1], h[0], h[1]};
}

// The bits [256] of the 32 big-endian bytes at OFFSET of BYTES (bytes
// that only generators read: a host input, or a Witness member), least
// significant first.
template <class D, class B>
Bits integer_bits(const Scope &s, D &A, const std::string &nm,
                  const B &bytes, size_t offset) {
  return s[A].priv(Bit{}, nm, Shape{256}, depends_on(bytes),
                     [offset](const std::vector<uint8_t> &b) {
                       const Limbs k = host::be_limbs(&b.at(offset));
                       std::vector<Elt> out(256);
                       for (size_t i = 0; i < 256; ++i)
                         out[i] = ct::bit_elt(fp(), host::bit(k, i));
                       return out;
                     });
}
// The integer of the bits V [256] (0 or 1, least significant first).
inline Limbs bits_limbs(const Tensor<Elt> &v) {
  Limbs k{};
  for (size_t i = 0; i < 256; ++i)
    k[i / 64] |= (host::canonical(v[i])[0] & 1) << (i % 64);
  return k;
}
// The scalar sinv = s^-1 mod n of a signature r || s, and r.
inline Limbs sig_r(const std::vector<uint8_t> &sig) {
  return host::be_limbs(&sig.at(0));
}
inline Limbs sig_sinv(const std::vector<uint8_t> &sig) {
  return host::scalar_limbs(
      host::scalar_inverse(host::scalar(host::be_limbs(&sig.at(32)))));
}
inline std::vector<Elt> digit_elts(const Digits &d) {
  std::vector<Elt> out(kWindows);
  for (size_t j = 0; j < kWindows; ++j) out[j] = fp().of_scalar(d[j]);
  return out;
}
// The signed odd digits [64] of sinv' (sinv or sinv - n, whichever is odd).
template <class D, class S>
Cells sinv_digits(const Scope &s, D &A, const S &sig) {
  return s[A].priv(Subfield{}, "sinv", Shape{kWindows}, depends_on(sig),
                     [](const std::vector<uint8_t> &b) {
                       return digit_elts(host::signed_digits(sig_sinv(b)));
                     });
}

// ---------------------------------------------------------- the issuer --

// Q_I's table points [kTable] in the public value TV.
inline std::vector<host::Point> table_points(const Tensor<Elt> &tv) {
  std::vector<host::Point> pts(kTable);
  for (size_t i = 0; i < kTable; ++i)
    pts[i] = {host::of(tv[2 * i]), host::of(tv[2 * i + 1])};
  return pts;
}
// K_I, projective, in the public value TV.
inline host::ProjPoint table_offset(const Tensor<Elt> &tv) {
  return {host::of(tv[2 * kTable]), host::of(tv[2 * kTable + 1]),
          host::of(tv[2 * kTable + 2])};
}
// P3 = ((A_e,63 + K_I) + T_e,63) + A_r for the G chain's last point
// A_e,63 and entry T_e,63 (complete additions, in the circuit's order).
inline host::ProjPoint issuer_p3(const host::Point &ae63,
                                 const host::Point &te63,
                                 const host::ProjPoint &ar,
                                 const host::ProjPoint &ki) {
  const host::ProjPoint ae = host::add_complete(
      host::add_complete(host::projective(ae63), ki), host::projective(te63));
  return host::add_complete(ae, ar);
}

// r_int's hex digits as the honest prover computes them, in scope S of A:
// X = [sinv'] ([e + 2M] G + [r + 2M] Q_I + K_I) on the host, from Q_I's
// table T, the digest E (its bits in A, or its 32 big-endian bytes) and the
// signature SIG (r and r_int agree mod n).
template <class D, class E, class S>
Cells issuer_r(const Scope &s, D &A, const Pub &t, const E &e, const S &sig) {
  auto digits = [](const Tensor<Elt> &tv, const Limbs &el,
                   const std::vector<uint8_t> &sb) {
    const std::vector<host::Point> pts = table_points(tv);
    const Digits de = host::nibbles(el);
    const Digits dr = host::nibbles(sig_r(sb));
    const host::FbChain ce = host::fb_chain(host::g_table().t, de);
    const host::ProjPoint ar = host::fb_chain(pts, dr).result;
    const host::Point p3 = host::affine(issuer_p3(
        ce.acc[kSteps - 2],
        host::fb_entry(&host::g_table().t[16 * kSteps], de[kSteps]), ar,
        table_offset(tv)));
    const host::VbChain x =
        host::vb_chain(p3, host::signed_digits(sig_sinv(sb)));
    return digit_elts(host::nibbles(host::canonical(x.result().x)));
  };
  if constexpr (std::is_same_v<E, Bits>) {
    return s[A].priv(Subfield{}, "r", Shape{kWindows}, depends_on(t, e, sig),
                     [digits](const Tensor<Elt> &tv, const Tensor<Elt> &ev,
                              const std::vector<uint8_t> &sb) {
                       return digits(tv, bits_limbs(ev), sb);
                     });
  } else {
    return s[A].priv(Subfield{}, "r", Shape{kWindows}, depends_on(t, e, sig),
                     [digits](const Tensor<Elt> &tv,
                              const std::vector<uint8_t> &eb,
                              const std::vector<uint8_t> &sb) {
                       return digits(tv, host::be_limbs(eb.data()), sb);
                     });
  }
}

struct IssuerVerification {
  // the crossing: e's bits [256]
  Bits e;
  // Q_I's fixed-base table [1024][2], then K_I [3] (projective)
  Pub table;
  // r_int's digits [64], sinv's signed odd digits [64]
  Cells r, w;
  FixedBase eg, rq;
  CellPoint p3;
  VarBase x;
  Cells iota_r;
};
// The issuer's ECDSA verification with the public key Q_I (statement
// (pkX, pkY)), the private digest E (its bits [256] in A, least
// significant first, the crossing a caller binds to the hash domain's
// digest) and the signature SIG (r || s), read by generators only:
//   eG         [e + 2M] G, fixed base over e's bits (digits as bit views)
//   r          r_int's hex digits, r_int = x(X) (the honest prover computes
//              X on the host)
//   rQ         [r_int + 2M] Q_I, fixed base over the public table
//   p3         P3 = A_e + A_r + K_I = [e] G + [r] Q_I, complete
//              additions, P3 affine (x, y)
//   sinv, x    X = [sinv'] P3, variable base
//   check_r    x(X) = r_int, r_int below p and not 0 or n
// E_SRC is what r's generator reads of the digest: E itself, or the
// digest's 32 big-endian bytes.
template <class D, class E, class S>
IssuerVerification issuer_verification(const Scope &s, D &A, const Pub &q_i,
                                       const Bits &e, const E &e_src,
                                       const S &sig) {
  IssuerVerification out;
  out.e = e;
  out.table = s[A].pub(Field{}, "q_table", Shape{2 * kTable + 3}, depends_on(q_i),
      computes("p256_fixed_base_table"), [](const Tensor<Elt> &q) {
        const host::FbTable t = host::fb_table(q[0], q[1]);
        std::vector<Elt> v;
        for (const host::Point &p : t.t) host::append(v, {p.x, p.y});
        // K_I = K_G + K_Q, projective (O when Q_I = -G).
        const host::Point &kg = host::g_table().k;
        const P256::ECPoint k = p256.addEf(
            P256::ECPoint(host::to(kg.x), host::to(kg.y), fp().one()),
            P256::ECPoint(host::to(t.k.x), host::to(t.k.y), fp().one()));
        for (const Elt &c : host::public_point(k)) v.push_back(c);
        return v;
      });
  out.r = issuer_r(s, A, out.table, e_src, sig);
  out.w = sinv_digits(s, A, sig);
  out.eg = fixed_base(s.scope("eG"), A, generator_table(), out.e);
  out.rq = fixed_base(s.scope("rQ"), A, FbTable{nullptr, out.table}, out.r);
  const auto ki = [&](size_t c) {
    return p256_ecdsa::E(out.table.reindex({2 * kTable + c}));
  };
  // K_I joins the G chain before its shallow entry T_e,63, so that the
  // deep entry T_r,63 (Q_I's table times the digit basis) is one complete
  // addition from P3.
  const PPt ae = add_complete(
      add_complete(projective(out.eg.last), PPt{ki(0), ki(1), ki(2)}),
      projective(out.eg.entry));
  const PPt p3 = add_complete(ae, out.rq.result);
  out.p3 = affine_of(
      s.scope("p3"), A, p3,
      depends_on(out.eg.acc, out.rq.acc, out.e, out.r, out.table),
      [](const Tensor<Elt> &ea, const Tensor<Elt> &ra, const Tensor<Elt> &ev,
         const Tensor<Elt> &rv, const Tensor<Elt> &tv) {
        // Each chain's committed A_63.
        auto last = [](const Tensor<Elt> &acc) {
          return host::Point{host::of(acc[2 * (kSteps - 2)]),
                             host::of(acc[2 * (kSteps - 2) + 1])};
        };
        const std::vector<host::Point> pts = table_points(tv);
        const host::Point te = host::fb_entry(
            &host::g_table().t[16 * kSteps], digit_values<Bit>(ev)[kSteps]);
        const host::Point tr = host::fb_entry(
            &pts[16 * kSteps], digit_values<Subfield<>>(rv)[kSteps]);
        const host::ProjPoint ar = host::add_complete(
            host::projective(last(ra)), host::projective(tr));
        const host::Point p =
            host::affine(issuer_p3(last(ea), te, ar, table_offset(tv)));
        return std::vector<Elt>{host::to(p.x), host::to(p.y)};
      });
  out.x = var_base(s.scope("x"), A, out.p3, out.w);
  // r's digits are in range by rQ's multiplexer.
  out.iota_r = check_r(s.scope("check_r"), A, out.x.result(), out.r, false);
  return out;
}
template <class D, class S>
IssuerVerification ecdsa_verify_public_key(const Scope &s, D &A,
                                           const Pub &q_i, const Bits &e,
                                           const S &sig) {
  return issuer_verification(s, A, q_i, e, e, sig);
}
// The same with the digest E as 32 big-endian bytes (a Witness member, or
// a host input), read by generators only: its bits are committed in A as
// "e".
template <class D, class B, class S>
IssuerVerification ecdsa_verify_public_key(const Scope &s, D &A,
                                           const Pub &q_i, const B &e,
                                           const S &sig) {
  return issuer_verification(s, A, q_i, integer_bits(s, A, "e", e, 0), e,
                             sig);
}

// ---------------------------------------------------------- the device --

struct DeviceVerification {
  // the crossing: the key's bits [256] each
  Bits dpkx, dpky;
  CellPoint key;
  // [e2] G, projective
  Pub e2g;
  // r' (signed odd), sinv' (signed odd), r_int digits
  Cells t, w, r;
  VarBase rq, x;
  CellPoint p3;
  ModN bind;
  Cells iota_r;
};
// The device's ECDSA verification with the private key DPK (dpkx ||
// dpky), the public digest E2 (statement, its halves) and the signature
// SIG (r || s), DPK and SIG read by generators only:
//   dpkx, dpky   Bit [256] each, the crossing
//   key          Q_D from the bits: below p, on the curve
//   r_signed     the signed odd digits of r' (r or r - n, whichever is odd)
//   rQ           [r'] Q_D, variable base
//   e2_point     [e2] G, a public computation, projective (O when
//                e2 = 0 mod n)
//   p3           P3 = [r'] Q_D + [e2] G, complete addition, P3 affine
//   sinv, x      X = [sinv'] P3, variable base
//   r            r_int's hex digits, read from x(X)
//   bind         r' = r_int - beta n
//   check_r      x(X) = r_int, below p, not 0 or n; r's digit ranges
template <class D, class B, class S>
DeviceVerification ecdsa_verify_private_key(const Scope &s, D &A,
                                            const B &dpk, const Pub &e2,
                                            const S &sig) {
  DeviceVerification out;
  out.dpkx = integer_bits(s, A, "dpkx", dpk, 0);
  out.dpky = integer_bits(s, A, "dpky", dpk, 32);
  out.key = point_from_bits(s.scope("key"), A, out.dpkx, out.dpky);
  out.t = s[A].priv(Subfield{}, "r_signed", Shape{kWindows},
                      depends_on(sig), [](const std::vector<uint8_t> &b) {
                        return digit_elts(host::signed_digits(sig_r(b)));
                      });
  out.rq = var_base(s.scope("rQ"), A, out.key, out.t);
  out.e2g = s[A].pub(Field{}, "e2_point", Shape{3}, depends_on(e2), computes("p256_g_mult"),
      [](const Tensor<Elt> &h) {
        return host::public_point(host::g_mult(of_halves(h[0], h[1])));
      });
  const CellPoint q2 = out.rq.result();
  const PPt p3 =
      add_complete(projective(q2.pt()),
                   PPt{E(out.e2g[0]), E(out.e2g[1]), E(out.e2g[2])});
  const size_t qx = q2.x, qy = q2.y;
  out.p3 = affine_of(
      s.scope("p3"), A, p3, depends_on(q2.ref, out.e2g),
      [qx, qy](const Tensor<Elt> &qv, const Tensor<Elt> &ev) {
        const host::Point p = host::affine(host::add_complete(
            host::projective({host::of(qv[qx]), host::of(qv[qy])}),
            {host::of(ev[0]), host::of(ev[1]), host::of(ev[2])}));
        return std::vector<Elt>{host::to(p.x), host::to(p.y)};
      });
  out.w = sinv_digits(s, A, sig);
  out.x = var_base(s.scope("x"), A, out.p3, out.w);
  const CellPoint X = out.x.result();
  const size_t xi = X.x;
  out.r = s[A].priv(Subfield{}, "r", Shape{kWindows}, depends_on(X.ref),
                      [xi](const Tensor<Elt> &v) {
                        return digit_elts(host::nibbles(host::canonical(v[xi])));
                      });
  out.bind = bind_mod_n(s.scope("bind"), A, out.t, out.r);
  out.iota_r = check_r(s.scope("check_r"), A, X, out.r, true);
  return out;
}

// -------------------------------------------------------------- domain A --

// Domain A's statement values: the issuer key (pkX, pkY), on the
// curve by its codec, and e2's 128-bit halves (lo, hi), each below 2^128
// by its codec.
struct MdocSignatureInputs {
  Pub issuer_pk;
  Pub e2;
};
// Domain A's statement values, read from the members issuer_pk and e2 of
// the statement ST. Without DEVICE (the device-signature ablation, mdoc.h)
// e2, which only the device's verification reads, is not read.
template <class St, class D>
MdocSignatureInputs mdoc_signature_inputs(D &A, const St &st,
                                          bool device = true) {
  const auto pk = st.issuer_pk;
  pk.check(A, computes("p256_affine_point"), [](const std::vector<Elt> &v) {
    return p256.is_on_curve(v[0], v[1]);
  });
  const auto e2 = st.e2;
  if (device)
    e2.check(A, computes("u128_halves"), [](const std::vector<Elt> &v) {
      for (const Elt &x : v) {
        const Limbs k = host::canonical(x);
        if ((k[2] | k[3]) != 0) return false;
      }
      return true;
    });
  MdocSignatureInputs in;
  in.issuer_pk = pk.values(A);
  if (device) in.e2 = e2.values(A);
  return in;
}

// The crossing values (Bit [256] each, A's cells) and the two
// verifications.
struct MdocSignatureDomain {
  Bits e, dpkx, dpky;
  IssuerVerification issuer;
  DeviceVerification device;
};
// Both verifications in domain A of CS, for the statement values IN and
// the witness W's members e, issuer_sig, dpk and device_sig. Without DEVICE
// (the device-signature ablation, mdoc.h) the issuer's alone: the device's
// verification is not declared, and device, dpkx and dpky stay empty.
template <class W, class Sys, class D>
MdocSignatureDomain mdoc_signature_domain(Sys &cs, D &A,
                                      const MdocSignatureInputs &in,
                                      const W &w, bool device = true) {
  MdocSignatureDomain out;
  out.issuer = ecdsa_verify_public_key(cs.scope("issuer"), A, in.issuer_pk,
                                       w.e, w.issuer_sig);
  out.e = out.issuer.e;
  if (!device) return out;
  out.device = ecdsa_verify_private_key(cs.scope("device"), A, w.dpk,
                                        in.e2, w.device_sig);
  out.dpkx = out.device.dpkx;
  out.dpky = out.device.dpky;
  return out;
}

}  // namespace proofs::gordiehowe::examples::mdoc::signatures

#endif  // PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_EXAMPLES_MDOC_MDOC_SIGNATURES_H_
