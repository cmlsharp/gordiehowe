// Copyright 2026 Chad Sharp and Paul Grubbs
// SPDX-License-Identifier: Apache-2.0

// GordieHowe: a proof of possession of an RSA-2048 PKCS#1 v1.5 signature
// with SHA-256 (RFC 8017, section 9.2). The statement is the modulus N of
// the key, whose public exponent is fixed at e = 65537; the witness is a message m of private length and its signature
// s. The relation proves s^65537 = EM (mod N), where EM is the PKCS#1
// encoding of SHA-256(m).
//
// Domain H, a binary field, hashes m. Domain A, Goldilocks^k or Fp128,
// proves the exponentiation as 17 modular multiplications x y = q N + r on
// limbs of committed digits (mul_mod). Each holds as integer equations
// with committed carries, which the compiler checks cannot wrap around the
// field's characteristic. The digest's bits cross from H to A under a MAC.
// Layout and witness code: rsa_pkcs1_params.h, rsa_pkcs1_witness.h.

#ifndef PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_EXAMPLES_RSA_RSA_PKCS1_H_
#define PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_EXAMPLES_RSA_RSA_PKCS1_H_

#include <algorithm>
#include <array>
#include <cstddef>
#include <cstdint>
#include <map>
#include <string>
#include <tuple>
#include <utility>
#include <vector>

#include "gordiehowe/core.h"
#include "gordiehowe/examples/rsa/rsa_pkcs1_params.h"
#include "gordiehowe/examples/rsa/rsa_pkcs1_witness.h"
#include "gordiehowe/examples/shared/setup.h"
#include "gordiehowe/expr.h"
#include "gordiehowe/lib/arith.h"
#include "gordiehowe/lib/message.h"
#include "gordiehowe/lib/sha256.h"
#include "gordiehowe/linear.h"
#include "gordiehowe/ops/operators.h"
#include "gordiehowe/predicates.h"
#include "gordiehowe/relation.h"
#include "gordiehowe/system.h"

namespace proofs::gordiehowe::examples::rsa {

// --------------------------------------------------------------- inputs --

// The statement: the modulus N (big-endian; the public exponent is fixed
// at kE). The witness: the message's SHA-256 buffer
// (lib::message::sha256_layout of the relation's maximum MAX, fixed per
// relation by the shape value), the message length L <= MAX and the
// signature s (big-endian).
template <template <class> class F>
struct RsaStatement {
  F<std::array<uint8_t, kModulusBytes>> n;
};
template <template <class> class F>
struct RsaWitness {
  F<std::vector<uint8_t>> m;
  F<uint16_t> m_length;
  F<std::array<uint8_t, kModulusBytes>> s;
};

inline RsaWitness<Value> rsa_witness_shape(size_t max) {
  RsaWitness<Value> w{};
  w.m.resize(lib::message::sha256_layout(max).part);
  return w;
}

// --------------------------------------------------------------- profile --

// The choices a relation is compiled with: the digit width t, the
// multiplication variant (kAuto: the compiler's choice; a bench variant
// pins it), the maximum message length and the carry group k (0: the
// largest the compiler accepts, carry_group). M is the digits per limb
// (the limb width is w = m t). SHA-256 is batched (sha256_varlen has no
// GKR form).
struct RsaConfig {
  size_t t = 10;
  ConvRealization mul = ConvRealization::kAuto;
  size_t max_bytes = 64;
  size_t k = 0;
  size_t m = 1;
};

// The compile profile: the MAC basis of P's hash field, and a range
// policy whose max_digits admits the carries' bound W in t-bit digits
// (more than the default 4 for wide limbs: W = 2^50 at w = 40).
template <class P>
CompileProfile compile_profile(const RsaConfig &cfg) {
  CompileProfile c = mac_profile<P>("rsa-pkcs1");
  const size_t w = cfg.m * cfg.t;
  const Bound shift = Bound((kModulusBits + w - 1) / w) << w;
  unsigned digits = 1;
  while ((Bound(1) << (cfg.t * digits)) < 2 * shift + 1) ++digits;
  c.range.max_digits = std::max(c.range.max_digits, digits);
  return c;
}

// --------------------------------------------------------------- gadgets --

// The key: N's L limbs of w bits (a public computation of the
// statement, N's kModulusBytes big-endian bytes), with the verifier's
// statement check that N has exactly 2048 bits (its top bit set),
// recorded against the limbs as rsa_modulus_2048 [2048, w, L]: the limbs
// n_i lie below 2^w and 2^2047 <= sum_i n_i 2^(w i) < 2^2048.
template <class D, class SN>
auto rsa_key(const Scope &s, D &A, const In<SN> &n, const RsaShape &sh) {
  const size_t w = sh.w, L = sh.L;
  n.check_value(s.scoped("n"),
                computes("rsa_modulus_2048", {kModulusBits, w, L}),
                [](const std::vector<uint8_t> &b) {
                  return b.size() == kModulusBytes && (b[0] & 0x80) != 0;
                });
  return s[A].pub(Subfield{}, "n", Shape{L}, depends_on(n),
                  computes("rsa_digits", {w, L}),
                  [w, L](const std::vector<uint8_t> &b) {
                    const auto x = host::from_be_bytes(b.data(), b.size(),
                                                       kModulusBits / 64);
                    return host::bounds(host::digits(x, w, L));
                  });
}

// EM's L limbs: the constant bytes 0x00 01 FF..FF 00 || DigestInfo and
// the digest bits DIGEST (Bit [256], bit 8 j + i of digest byte j, the
// least significant byte last), as an affine expression: limb d is
// const_d + sum 2^(pos - w d) bits over the digest bits at integer bit
// positions pos in [w d, w (d + 1)).
template <class D, class F, class P>
Expr<F> pkcs1_encoding(const Scope &s, D &A, const Ref<F, Bit, P> &digest,
                       const RsaShape &sh) {
  const F &f = A.field();
  const size_t w = sh.w, L = sh.L;
  uint8_t zero[32] = {};
  const auto em = host::encoded(zero);
  const auto x = host::from_be_bytes(em.data(), em.size(), kModulusBits / 64);
  const auto cd = host::digits(x, w, L);
  std::vector<std::vector<std::pair<size_t, uint64_t>>> rows(L);
  for (size_t j = 0; j < 32; ++j)
    for (size_t i = 0; i < 8; ++i) {
      const size_t pos = 8 * (31 - j) + i;
      rows[pos / w].push_back({8 * j + i, uint64_t(1) << (pos % w)});
    }
  std::vector<typename F::Elt> c(L);
  for (size_t d = 0; d < L; ++d) c[d] = f.of_scalar(cd[d]);
  const auto constant = s[A].constant("em.constant", c);
  return Expr<F>(ops::sparse_matrix(f, "em_digits", 256, rows)(digest)) +
         constant;
}

// The limbs of the digit table DIGITS ([R][n m] digits of t bits): [R][n],
// limb i of a row sum_{j<m} 2^(t j) d_{i m + j} (from_digits, an affine
// view with its row bound); the digits themselves when m = 1.
template <class F>
Expr<F> limbs_of(const Ref<F, Subfield<>, Committed> &digits, size_t R,
                 size_t n, const RsaShape &sh) {
  if (sh.m == 1) return Expr<F>(digits);
  return Expr<F>(lin_limbs(digits, {R, n, sh.m}, sh.beta()));
}

// The carry groups of X, rows of coefficients ([B, cols], cols at most
// K): [B, G], group g the integer in base 2^w of coefficients g k to
// g k + k - 1, X zero-extended to G k coefficients (from_digits).
template <class D, class F>
Expr<F> carry_groups(const D &A, const Expr<F> &x, const RsaShape &sh) {
  const size_t B = x.dims().at(0), cols = x.dims().at(1);
  const size_t pad = sh.G * sh.k - cols;
  Expr<F> padded = x;
  if (pad > 0)
    padded = x.concat(
        A.constant(std::vector<uint64_t>(B * pad, 0), Shape{B, pad}), 1);
  return padded.reshape(Shape{B, sh.G, sh.k}).from_digits(sh.limb());
}

// x_b y_b = q_b N + r_b over the integers for each row b, with
// x_b = XL[XROWS[b]], y_b = XL[YROWS[b]] (XL the limbs of the digit table
// X), R the rows r_b ([B][L], an expression over limbs in [0, 2^w)) and
// N the public limbs ([L]). Commits q's digits and the carries with their
// range requests; conv(x, y) takes the realization VARIANT (kAuto: the
// compiler's choice), and the carry equations are assert_int_equal, whose
// no-wrap condition the compiler checks.
template <class D, class F>
void mul_mod(const Scope &s, D &A, const Ref<F, Subfield<>, Committed> &X,
             const Expr<F> &XL, const std::vector<size_t> &xrows,
             const std::vector<size_t> &yrows, const Expr<F> &R,
             const Ref<F, Subfield<>, Public> &n, const RsaShape &sh,
             ConvRealization variant) {
  using Elt = typename F::Elt;
  using Ints = std::vector<NatInt>;
  const F &f = A.field();
  const size_t G = sh.G, B = xrows.size();
  const RsaShape shape = sh;
  if (B != kRows) fail("mul_mod: the generators prove the exponentiation's rows");
  const auto Q = s[A].priv(Subfield{}, "q", Shape{B, sh.q_digits()},
                           depends_on(X, n),
                           [shape](const Ints &x, const Ints &nd) {
                             return host::bounds(host::quotients(
                                 shape, host::words(x), host::words(nd)));
                           });
  assert_range(Q, sh.beta(), s.name("q"));
  // The carries c_g, signed: c + shift lies in [0, 2 shift + 1), and the
  // planner may establish any bound up to W.
  const auto carry = s[A].priv(
      Subfield{}, "carry", Shape{B, G - 1}, depends_on(X, Q, n),
      [shape](const Ints &x, const Ints &q, const Ints &nd) {
        return host::carries(shape, host::words(x), host::words(q),
                             host::words(nd));
      });
  const auto carry_shift = s[A].constant(
      "carry.shift", std::vector<Elt>(B * (G - 1), elt_of_nat(f, sh.shift)));
  assert_centered_range(carry, carry_shift, sh.shift, MaxBound{sh.W},
                        s.name("carry"));
  // The products and q N, over limbs.
  const Expr<F> x = XL.reindex(xrows, 0);
  const Expr<F> y = XL.reindex(yrows, 0);
  const auto xy = conv(x, y).pin(variant);
  const auto qn =
      conv(limbs_of(Q, B, sh.Lq, sh), n, ops::EntryBound{Bound(sh.limb())});
  // E_g of D = conv(x, y) - conv(q, N) - r, each part grouped.
  const Expr<F> e = carry_groups(A, Expr<F>(xy), sh) -
                    carry_groups(A, Expr<F>(qn), sh) - carry_groups(A, R, sh);
  // carries_wrap reads the compile error of this name, rsa.mul.carries.
  lib::arith::assert_carry_chain(f, e, carry, G, elt_of_nat(f, sh.base()),
                                 s.name("carries"));
}

// s^65537 = EM (mod N): X = (x_0 = s, x_1, ..., x_16) committed as
// [17][L m] digits below 2^t, read as [17][L] limbs, the rows
// x_b^2 = x_{b+1} (b < 16) and x_16 x_0 = EM of mul_mod.
template <class D, class F, class SM>
void rsa_exponentiation(const Scope &s, D &A, const In<SM> &sig,
                        const Ref<F, Subfield<>, Public> &n,
                        const Expr<F> &em, const RsaShape &sh,
                        ConvRealization variant) {
  const RsaShape shape = sh;
  const auto X = s[A].priv(Subfield{}, "x", Shape{kRows, sh.digits()},
                           depends_on(sig, n),
                           [shape](const std::vector<uint8_t> &sv,
                                   const std::vector<NatInt> &nd) {
                             return host::bounds(
                                 host::chain(shape, sv, host::words(nd)));
                           });
  assert_range(X, sh.beta(), s.name("x"));
  std::vector<size_t> xrows(kRows), yrows(kRows);
  for (size_t b = 0; b < kRows; ++b) {
    xrows[b] = host::xrow(b);
    yrows[b] = host::yrow(b);
  }
  const Expr<F> XL = limbs_of(X, kRows, sh.L, sh);
  const Expr<F> R =
      XL.slice(1, kRows, 0).concat(em.reshape(Shape{1, sh.L}), 0);
  mul_mod(s.scope("mul"), A, X, XL, xrows, yrows, R, n, sh, variant);
}

// ---------------------------------------------------------------- system --

// The relation over ST and W under CFG (CFG.k the carry group, nonzero):
// H first (SHA-256 of the message at its private length), then A.
template <class P>
void rsa_relation(typename Env<P>::Sys &cs, const Env<P> &env,
                  RsaStatement<In> st, RsaWitness<In> w,
                  const RsaConfig &cfg) {
  auto &H = cs.domain(domain_profile<P>(env.hf, env.rsh), "H");
  auto &A = cs.domain(domain_profile<P>(env.af, env.rsa.factory()), "A");
  const RsaShape sh =
      RsaShape::derive(field_characteristic(env.af), cfg.t, cfg.k, cfg.m);
  const lib::message::Layout layout =
      lib::message::sha256_layout(cfg.max_bytes);
  const auto msg = lib::message::committed_message(H, w.m, layout, w.m_length,
                                                   "msg.in_message");
  const auto hs = cs.scope("hash");
  const auto sha = lib::sha256::sha256_batch(
      hs[H], "sha256.chi", lib::sha256::Sha256Mode::kBatched);
  const auto digest = lib::message::sha256_message(sha, "sha256", layout,
                                                   msg.bits, msg.flags);
  const auto n = rsa_key(cs.scope("key"), A, st.n, sh);
  const auto digest_A = digest.to(cs.scope("crossing")[A], "digest");
  const auto em = pkcs1_encoding(cs.scope("encoding"), A, digest_A, sh);
  rsa_exponentiation(cs.scope("rsa"), A, w.s, n, em, sh, cfg.mul);
}

// The relation under CFG with its carry group CFG.k (nonzero).
template <class P>
Relation<RsaStatement<Value>, RsaWitness<Value>> rsa_pkcs1_at(
    const Env<P> &env, const RsaConfig &cfg) {
  return compile<RsaStatement, RsaWitness>(
      compile_profile<P>(cfg),
      [&env, cfg](typename Env<P>::Sys &cs, RsaStatement<In> st,
                  RsaWitness<In> w) { rsa_relation<P>(cs, env, st, w, cfg); },
      "rsa-pkcs1-sha256-possession", RsaStatement<Value>{},
      rsa_witness_shape(cfg.max_bytes));
}

// Whether E is the carry equations' no-wrap failure (compiler/mod.h, the
// integer equality): the equation can wrap around p, or an operand's
// interval passes the check's cap 2^126 (the binding limit when p is near
// 2^128, as in Fp128).
inline bool carries_wrap(const CompileError &e) {
  const std::string w = e.what();
  return w.find("assert_int_equal 'rsa.mul.carries'") != std::string::npos &&
         (w.find("can wrap around p") != std::string::npos ||
          w.find("has no integer interval") != std::string::npos);
}

// The carry group of CFG: CFG.k when set, otherwise the largest k
// (from (bits(p) - 2) / w down) whose carry equations the compiler accepts.
// The compiler's no-wrap check decides; the search compiles the relation
// of CFG's limb layout over messages of at most 64 bytes (k depends only
// on the field, t and m), once per characteristic, t and m.
template <class P>
size_t carry_group(const Env<P> &env, const RsaConfig &cfg) {
  if (cfg.k != 0) return cfg.k;
  static std::map<std::tuple<Bound, size_t, size_t>, size_t> cache;
  const Bound p = field_characteristic(env.af);
  const auto key = std::make_tuple(p, cfg.t, cfg.m);
  auto it = cache.find(key);
  if (it != cache.end()) return it->second;
  for (size_t k = RsaShape::max_group(p, cfg.m * cfg.t); k >= 1; --k) {
    RsaConfig c = cfg;
    c.k = k;
    c.max_bytes = 64;
    try {
      rsa_pkcs1_at<P>(env, c);
    } catch (const CompileError &e) {
      if (carries_wrap(e)) continue;
      throw;
    }
    cache[key] = k;
    return k;
  }
  fail("carry_group: no carry group fits p at t = " + std::to_string(cfg.t) +
       ", m = " + std::to_string(cfg.m));
}

// CFG with its carry group resolved (carry_group).
template <class P>
RsaConfig resolved(const Env<P> &env, RsaConfig cfg) {
  cfg.k = carry_group<P>(env, cfg);
  return cfg;
}

template <class P>
Relation<RsaStatement<Value>, RsaWitness<Value>> rsa_pkcs1(
    const Env<P> &env, const RsaConfig &cfg) {
  return rsa_pkcs1_at<P>(env, resolved<P>(env, cfg));
}

}  // namespace proofs::gordiehowe::examples::rsa

#endif  // PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_EXAMPLES_RSA_RSA_PKCS1_H_
