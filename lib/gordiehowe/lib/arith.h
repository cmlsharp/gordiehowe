// Copyright 2026 Chad Sharp and Paul Grubbs
// SPDX-License-Identifier: Apache-2.0

// GordieHowe: word arithmetic as library functions over the core.
//
//   assert_sum_mod(r, {x_1, ..., x_k}, N)   the words sum to r mod 2^N
//   word_value(x)                           a word in the group where
//                                           addition is cheap
//   ch(x, y, z), maj(x, y, z), xor3(x, y, z)  SHA-256's bit functions
//   eq_mask(x, mask, v)                     the bits of x under a mask
//                                           equal v's
//   add(x_1, ..., x_k[, nm])                the committed sum mod 2^w
//   assert_sum(s, {x_1, ..., x_k}[, p])     s = x_1 + ... + x_k mod 2^w
//                                           through committed partial
//                                           sums p
//   assert_add_majority(s, x, y)            s = x + y mod 2^w, one product
//                                           per bit (each step of both)
//   assert_carry_chain(f, e, c, G, B, nm)   E_g + c_{g-1} = B c_g, the
//                                           carries of grouped limbs
//   add_words(a, b)                         a + b mod 2^w, Sklansky's carries
//   add_bit(t, b)                           t + b mod 2^w for a late bit b
//   prefix_and(c)                           the prefix ANDs of Bit columns
//   below_constant(x, c)                    the word x below a constant
//   constant_word(D, x, w)                  a constant word of w bits
//   big_endian_bit_order(bytes[, bits])     the bits of a big-endian
//                                           integer in a byte string
//
// assert_sum_mod mirrors Longfellow's BitAdder (circuits/logic/
// bit_adder.h). A word of N bits (a Bit expression [..., N], least
// significant first) maps to a field element in which addition is cheap:
//   odd characteristic  v(x) = sum_i 2^i x_i, the integer, added by field
//                       addition;
//   characteristic 2    v(x) = alpha^x = prod_i x_i.mux(alpha^(2^i), 1),
//                       alpha of multiplicative order above (k + 1) 2^N,
//                       added by field multiplication.
// The words x_1..x_k sum to the committed r modulo 2^N exactly when the
// sum s = v(x_1) + ... + v(x_k) (the product in characteristic 2) is
// v(r) + i 2^N (v(r) alpha^(i 2^N)) for one i < k, so no carry is
// computed:
//   odd                 prod_{i < k} (s - v(r) - i 2^N) = 0,
//   characteristic 2    prod_{i < k} (s - alpha^(i 2^N) v(r)) = 0,
// one predicate of degree k in s (BitAdder::assert_eqmod). Exactness:
// in odd characteristic the integers sum_j x_j and r + i 2^N lie below k
// 2^N <= p, where field equality is integer equality; in characteristic 2
// the exponents sum_j x_j - r - i 2^N lie in (-(k + 1) 2^N, (k + 1) 2^N),
// where alpha^e = 1 forces e = 0. word_value and the form of
// assert_sum_mod taking an encoded sum share a partial sum between two
// assertions (SHA-256's T1).
//
// ch, maj and xor3 use the exclusive-OR trick of logic.h's lCh and lMaj:
// (x & y) and (~x & z) never both hold, so Ch is their sum, which is
// x.mux(y, z) (Logic::mux on bits, lCh's two products); Maj is x when
// x = y and z otherwise, (x ^ y).mux(z, x): two products and an XOR (free
// in characteristic 2), as lMaj.

#ifndef PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_LIB_ARITH_H_
#define PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_LIB_ARITH_H_

#include <cstddef>
#include <cstdint>
#include <initializer_list>
#include <string>
#include <vector>

#include "gordiehowe/core.h"
#include "gordiehowe/ct.h"
#include "gordiehowe/domain.h"
#include "gordiehowe/expr.h"
#include "gordiehowe/predicates.h"
#include "gordiehowe/system_core.h"

namespace proofs::gordiehowe::lib::arith {

namespace arith_internal {

// x^E for a 128-bit exponent E, by square-and-multiply on the public E.
template <class F>
typename F::Elt power(const F &f, typename F::Elt x, unsigned __int128 e) {
  typename F::Elt r = f.one();
  while (e != 0) {
    if ((e & 1) != 0) r = f.mulf(r, x);
    x = f.mulf(x, x);
    e >>= 1;
  }
  return r;
}

// The multiplicative order of X, an element of the subgroup of order
// 2^128 - 1 (of GF(2^128), or the subfield GF(2^128) of GF(2^256)): 2^128
// - 1 with each prime factor removed while X still has the smaller order.
// 2^128 - 1 = (2^64 - 1)(2^64 + 1) = 3 5 17 257 641 65537 6700417 274177
// 67280421310721.
template <class F>
unsigned __int128 order_128(const F &f, const typename F::Elt &x) {
  const uint64_t primes[] = {3,      5,      17,      257,           641,
                             65537,  274177, 6700417, 67280421310721ull};
  unsigned __int128 n = ~(unsigned __int128)0;
  for (uint64_t q : primes)
    while (n % q == 0 && power(f, x, n / q) == f.one()) n /= q;
  return n;
}

}  // namespace arith_internal

// alpha for characteristic 2 (above): the polynomial generator x of
// GF(2^128), or x^(2^128 + 1), which lies in the subfield GF(2^128) of
// GF(2^256); its order is checked to exceed BOUND.
template <class F>
typename F::Elt sum_generator(const F &f, unsigned __int128 bound) {
  static_assert(F::kCharacteristicTwo,
                "sum_generator: the multiplicative encoding is for "
                "characteristic 2");
  static_assert(F::kBits == 128 || F::kBits == 256,
                "sum_generator: GF(2^128) or GF(2^256)");
  typename F::Elt a = f.of_scalar_field(0b10);
  if constexpr (F::kBits == 256) {
    // x^(2^128 + 1): 128 squarings, then times x.
    typename F::Elt y = a;
    for (size_t i = 0; i < 128; ++i) y = f.mulf(y, y);
    a = f.mulf(y, a);
  }
  if (arith_internal::order_128(f, a) <= bound)
    fail("assert_sum_mod: the generator's order is too small");
  return a;
}

// The value of the words X (Bit [..., N]) in the group where their
// addition is cheap (above): [...].
template <class F>
Expr<F> word_value(const Domain<F> &D, const Expr<F, Bit> &x,
                   size_t k_max = 8) {
  const size_t N = x.dims().back();
  if constexpr (F::kCharacteristicTwo) {
    const F &f = D.field();
    const auto alpha =
        sum_generator(f, (unsigned __int128)(k_max + 1) << N);
    std::vector<typename F::Elt> p(N);
    p[0] = alpha;
    for (size_t i = 1; i < N; ++i) p[i] = f.mulf(p[i - 1], p[i - 1]);
    return Expr<F>(x.mux(D.constant(p), f.one())).prod(x.dims().size() - 1);
  } else {
    return Expr<F>(x.from_bits().value);
  }
}

// The encoded sum S (the product, in characteristic 2, or the sum of K
// words' values) is R + i 2^N for one i < K: the words sum to R (Bit
// [..., N]) modulo 2^N. NM names the predicate.
template <class F>
Predicate assert_sum_mod(const Domain<F> &D, const Expr<F, Bit> &r,
                         const Expr<F> &s, size_t k, const Name &nm = {}) {
  const auto dims = r.dims();
  const size_t N = dims.back();
  const size_t m = r.size() / N;
  const F &f = D.field();
  if (k == 0 || s.size() != m)
    fail("assert_sum_mod: a sum of " + std::to_string(k) + " words of " +
         std::to_string(s.size()) + " coordinates for " + std::to_string(m) +
         " results");
  const Expr<F> v = word_value(D, r, k);
  std::vector<typename F::Elt> c(k);
  if constexpr (F::kCharacteristicTwo) {
    // alpha^(i 2^N): N squarings of alpha, then its powers.
    typename F::Elt a = sum_generator(f, (unsigned __int128)(k + 1) << N);
    for (size_t i = 0; i < N; ++i) a = f.mulf(a, a);
    c[0] = f.one();
    for (size_t i = 1; i < k; ++i) c[i] = f.mulf(c[i - 1], a);
    const Expr<F> t = s.reshape({m, 1}) - v.reshape({m, 1}) * D.constant(c);
    return assert_zero(t.prod(t.dims().size() - 1), nm);
  } else {
    if (Bound(k) << N >= field_characteristic(f))
      fail("assert_sum_mod: " + std::to_string(k) + " words of " +
           std::to_string(N) + " bits wrap modulo the characteristic");
    for (size_t i = 0; i < k; ++i) c[i] = f.of_scalar(uint64_t(i) << N);
    const Expr<F> t = (s - v).reshape({m, 1}) - D.constant(c);
    return assert_zero(t.prod(t.dims().size() - 1), nm);
  }
}
// The words X_1..X_K (Bit [..., N] each) sum to R modulo 2^N.
template <class F>
Predicate assert_sum_mod(const Domain<F> &D, const Expr<F, Bit> &r,
                         const std::vector<Expr<F, Bit>> &x,
                         const Name &nm = {}) {
  if (x.empty()) fail("assert_sum_mod: no word");
  const size_t k = x.size();
  Expr<F> s = word_value(D, x[0], k);
  for (size_t i = 1; i < k; ++i) {
    if constexpr (F::kCharacteristicTwo) {
      s = s * word_value(D, x[i], k);
    } else {
      s = s + word_value(D, x[i], k);
    }
  }
  return assert_sum_mod(D, r, s, k, nm);
}

// The sum of encoded values A and B (word_value): their product in
// characteristic 2, their sum otherwise.
template <class F>
Expr<F> add_values(const Expr<F> &a, const Expr<F> &b) {
  if constexpr (F::kCharacteristicTwo) {
    return a * b;
  } else {
    return a + b;
  }
}

// C = A + B mod 2^w for Bit words [w] (least significant first), in
// constant depth: Logic::assert_sum. With g_i = a_i b_i and p_i = a_i ^
// b_i, the carries into bits 1.. are cy_{i-1} = c_i ^ p_i, and the checks
// are c_0 = p_0, cy_0 = g_0 and cy_i = g_i + cy_{i-1} p_i (the two terms
// exclusive, since g_i excludes p_i) for i < w - 1; the carry out of bit
// w - 1 is free. NM names the predicate.
template <class F>
Predicate assert_add(const Expr<F, Bit> &c, const Expr<F, Bit> &a,
                     const Expr<F, Bit> &b, const Name &nm = {}) {
  const size_t w = c.size();
  if (a.size() != w || b.size() != w || w < 2)
    fail("assert_add: words of one width of at least 2 bits");
  const Expr<F, Bit> g = a & b, p = a ^ b;
  const Expr<F, Bit> cy = c.slice(1, w) ^ p.slice(1, w);
  Expr<F, Bit> lhs = c.slice(0, 1).concat(cy.slice(0, 1));
  Expr<F, Bit> rhs = p.slice(0, 1).concat(g.slice(0, 1));
  if (w > 2) {
    lhs = lhs.concat(cy.slice(1, w - 1));
    rhs = rhs.concat(g.slice(1, w - 1) ^
                     (cy.slice(0, w - 2) & p.slice(1, w - 1)));
  }
  return assert_equal(lhs, rhs, nm);
}

// S = X + Y mod 2^w on Bit words [..., w] (least significant first) in
// Keccak's chi shape, one product per bit, with cin = S ^ X ^ Y the carry
// into each bit and M the mask of bits 0..w-2:
//   ((S ^ Y) & M) & ((S ^ X) & M) ^ (cin & M) ^ rotr(cin, 1) = 0.
// Bit i < w - 1 says cin_{i+1} = maj(x_i, y_i, cin_i), since maj(x_i, y_i,
// c) = ((s_i ^ y_i) & (s_i ^ x_i)) ^ c for s_i = x_i ^ y_i ^ c; bit w - 1
// says cin_0 = 0. The carries are a view of S, X and Y, so the committed
// sum determines them. In characteristic 2 the predicate has degree 2; in
// odd characteristic the gates take their integer forms (a higher degree).
// NM names the predicate.
template <class F>
Predicate assert_add_majority(const Expr<F, Bit> &s, const Expr<F, Bit> &x,
                              const Expr<F, Bit> &y, const Name &nm = {}) {
  const auto dims = s.dims();
  const size_t w = dims.back();
  const size_t last = dims.size() - 1;
  if (x.dims() != dims || y.dims() != dims || w < 2)
    fail("assert_add_majority: words of one shape, at least 2 bits wide");
  std::vector<uint64_t> bits(w, 1);
  bits[w - 1] = 0;
  // The mask, one constant for its three uses.
  Graph *g = graph_of(s.node);
  if (g == nullptr) fail("assert_add_majority: the sum reads no value");
  Domain<F> *d = g->system->template domain_of<F>();
  if (d == nullptr)
    fail("assert_add_majority: the system has no domain of the field");
  const Expr<F, Bit> m = d->constant(Bit{}, bits);
  const Expr<F, Bit> cin = s ^ x ^ y;
  return assert_zero((((s ^ y) & m) & ((s ^ x) & m)) ^ (cin & m) ^
                         cin.rotate(-1, last),
                     nm);
}

// S = X_1 + ... + X_k mod 2^w (k >= 2) for Bit words of one shape, through
// committed partial sums: P[0] = X_1 + X_2, P[j] = P[j - 1] + X_{j+2}, and
// S = P[k - 3] + X_k, each step by assert_add_majority (named NM.p2 ..
// NM.p<k-1> and NM). P has shape [k - 2, ...] (no partial sum for k = 2).
template <class F>
void assert_sum(const Expr<F, Bit> &s, const std::vector<Expr<F, Bit>> &x,
                const Expr<F, Bit> &p, const Name &nm = {}) {
  const size_t k = x.size();
  if (k < 2) fail("assert_sum: at least two words");
  if (k > 2 && p.dims().at(0) != k - 2)
    fail("assert_sum: " + std::to_string(k - 2) + " partial sums");
  auto step = [&](size_t j) {
    if (nm.name.empty()) return nm;
    return Name(nm.prefix, nm.name + ".p" + std::to_string(j));
  };
  Expr<F, Bit> acc = x[0];
  for (size_t j = 1; j < k; ++j) {
    const Expr<F, Bit> out = j + 1 == k ? s : Expr<F, Bit>(p[j - 1]);
    assert_add_majority(out, acc, x[j], j + 1 == k ? nm : step(j + 1));
    acc = out;
  }
}
template <class F>
void assert_sum(const Expr<F, Bit> &s, const std::vector<Expr<F, Bit>> &x,
                const Name &nm = {}) {
  if (x.size() != 2)
    fail("assert_sum: the partial sums of " + std::to_string(x.size()) +
         " words");
  assert_add_majority(s, x[0], x[1], nm);
}

namespace arith_internal {

// The honest prover's sum of two Bit word tensors of width W (the last
// axis): a ripple of carries on the host, branch-free in the bits.
template <class F>
auto sum_words(const F *f, size_t w) {
  using Elt = typename F::Elt;
  return [f, w](const std::vector<Elt> &x, const std::vector<Elt> &y) {
    std::vector<Elt> s(x.size());
    for (size_t at = 0; at < x.size(); at += w) {
      uint64_t c = 0;
      for (size_t i = 0; i < w; ++i) {
        const uint64_t a = ct::bit_of(*f, x[at + i]);
        const uint64_t b = ct::bit_of(*f, y[at + i]);
        s[at + i] = ct::bit_elt(*f, a ^ b ^ c);
        c = (a & b) | (c & (a ^ b));
      }
    }
    return s;
  };
}

// The operands of add as Bit expressions of one field, and the trailing
// Name when there is one.
template <class F>
void add_operands(std::vector<Expr<F, Bit>> &, Name &) {}
template <class F, class A, class... R>
void add_operands(std::vector<Expr<F, Bit>> &x, Name &nm, const A &a,
                  const R &...r) {
  if constexpr (kIsPoly<A>) {
    x.push_back(Expr<F, Bit>(a));
    add_operands<F>(x, nm, r...);
  } else {
    static_assert(sizeof...(R) == 0, "add: the name comes after the words");
    nm = Name(a);
  }
}

// S = A + B mod 2^w, committed as NM in the domain of their field in the
// system of graph G, with assert_add_majority(S, A, B). A and B may both
// be public (the first sum of SHA-256's block 0 adds two constants).
template <class F>
Ref<F, Bit, Committed> add2(Graph *g, const Expr<F, Bit> &a,
                            const Expr<F, Bit> &b, const Name &nm) {
  Domain<F> *d = g->system->template domain_of<F>();
  if (d == nullptr)
    fail("add '" + nm.name + "': the system has no domain of the field");
  const auto dims = a.dims();
  const Scope sc = internal::Predicates::at(*g->system, nm.prefix);
  const std::string label =
      nm.name.empty() ? "add" + std::to_string(g->nodes.size()) : nm.name;
  const auto s = sc[*d].priv(Bit{}, label, Shape(dims), depends_on(a, b),
                             sum_words(&d->field(), dims.back()));
  assert_add_majority(Expr<F, Bit>(s), a, b, Name(nm.prefix, label));
  return s;
}

}  // namespace arith_internal

// add(x_1, ..., x_k[, nm]): x_1 + ... + x_k mod 2^w for Bit words [..., w]
// (least significant first, k >= 2), committed. The partial sums s_2 =
// x_1 + x_2 and s_j = s_{j-1} + x_j are committed values NM.p2 ..
// NM.p<k-1>, and the last is NM; each is computed by the honest prover
// from its two operands (a small host closure) and stated by
// assert_add_majority. The domain is the one of the words' field.
template <class X, class... Y>
Ref<PolyField<X>, Bit, Committed> add(const X &x, const Y &...y) {
  using F = PolyField<X>;
  std::vector<Expr<F, Bit>> v;
  Name nm;
  arith_internal::add_operands<F>(v, nm, x, y...);
  if (v.size() < 2) fail("add: at least two words");
  auto part = [&](size_t j) {
    if (j + 1 == v.size()) return nm;
    if (nm.name.empty()) return Name(nm.prefix, "");
    return Name(nm.prefix, nm.name + ".p" + std::to_string(j + 1));
  };
  // The system: that of the first word that reads one of its values.
  Graph *g = nullptr;
  for (const auto &w : v)
    if (g == nullptr) g = internal::operand_graph(w);
  if (g == nullptr || g->system == nullptr)
    fail("add '" + nm.name + "': the words read no value of a system");
  Ref<F, Bit, Committed> s = arith_internal::add2(g, v[0], v[1], part(1));
  for (size_t j = 2; j < v.size(); ++j)
    s = arith_internal::add2(g, Expr<F, Bit>(s), v[j], part(j));
  return s;
}

// A + B mod 2^w for Bit words [..., w] (least significant first, one sum
// per word, the carry out of the top bit dropped): Logic::vadd, the
// generate-propagate adder with Sklansky's parallel-prefix carries, depth
// about log2 w.
template <class F>
Expr<F, Bit> add_words(const Expr<F, Bit> &a, const Expr<F, Bit> &b) {
  const auto dims = a.dims();
  if (b.dims() != dims || dims.empty() || dims.back() == 0)
    fail("add_words: words of one shape");
  const size_t w = dims.back(), ax = dims.size() - 1;
  std::vector<Expr<F, Bit>> g(w), p(w);
  for (size_t i = 0; i < w; ++i) {
    g[i] = a.slice(i, i + 1, ax) & b.slice(i, i + 1, ax);
    p[i] = a.slice(i, i + 1, ax) ^ b.slice(i, i + 1, ax);
  }
  // Prefixes over [block start, i]: (G, P) o (G', P') = (G | P G', P P'),
  // G and P G' exclusive. The propagate products are written with * (a
  // product of Bits is a Bit), so that P G' stays one product of two
  // operands: the emitter flattens a chain of one operation into a
  // balanced tree, which would otherwise pull G' down the tree of P's
  // factors.
  std::vector<Expr<F, Bit>> G = g, P = p;
  for (size_t d = 1; d < w; d <<= 1)
    for (size_t i = 0; i < w; ++i)
      if ((i & d) != 0) {
        const size_t j = i - (i & (d - 1)) - 1;
        G[i] = G[i] ^ (P[i] & G[j]);
        P[i] = P[i] * P[j];
      }
  Expr<F, Bit> s = p[0];
  for (size_t i = 1; i < w; ++i) s = s.concat(p[i] ^ G[i - 1], ax);
  return s;
}

// SHA-256's Ch(x, y, z) = (x & y) ^ (~x & z): the exclusive terms summed,
// x.mux(y, z).
template <class F>
Expr<F, Bit> ch(const Expr<F, Bit> &x, const Expr<F, Bit> &y,
                const Expr<F, Bit> &z) {
  return x.mux(y, z);
}
// SHA-256's Maj(x, y, z) = (x & y) ^ (x & z) ^ (y & z): x when x = y, z
// otherwise, (x ^ y).mux(z, x).
template <class F>
Expr<F, Bit> maj(const Expr<F, Bit> &x, const Expr<F, Bit> &y,
                 const Expr<F, Bit> &z) {
  return (x ^ y).mux(z, x);
}
// x ^ y ^ z.
template <class F>
Expr<F, Bit> xor3(const Expr<F, Bit> &x, const Expr<F, Bit> &y,
                  const Expr<F, Bit> &z) {
  return x ^ y ^ z;
}

// The bits of the word X (Bit [w]) at MASK's set positions equal VAL's
// there: Logic::veqmask, one comparison of the masked bits with the
// packed constant (Logic::eq).
template <class F>
Expr<F, Bit> eq_mask(const Expr<F, Bit> &x, uint64_t mask, uint64_t val) {
  std::vector<size_t> masked;
  uint64_t packed = 0;
  for (size_t t = 0; t < x.size(); ++t)
    if ((mask >> t) & 1) {
      packed |= ((val >> t) & 1) << masked.size();
      masked.push_back(t);
    }
  return x.reindex(masked).from_bits() == packed;
}

// The prefix ANDs c_0 & ... & c_b of the columns C (Bit [m] each), by
// Sklansky's parallel prefix: depth ceil(log2 |C|).
template <class F>
std::vector<Expr<F, Bit>> prefix_and(std::vector<Expr<F, Bit>> c) {
  for (size_t d = 1; d < c.size(); d <<= 1)
    for (size_t i = 0; i < c.size(); ++i)
      if ((i & d) != 0) c[i] = c[i] & c[i - (i & (d - 1)) - 1];
  return c;
}

// T + B mod 2^w for Bit words T [..., w] (least significant first) and
// bits B [...] (one bit per word, the carry out of the top bit dropped),
// for a B that arrives late, deeper in the circuit than T: the prefix ANDs
// of T's bits (prefix_and) do not read B, and B multiplies each prefix
// last, so the result lies one product above B. Bit i is
// t_i ^ (b & t_0 & ... & t_{i-1}). B times a prefix is a product (*), so
// that the emitter does not merge B into the prefix's AND tree.
template <class F>
Expr<F, Bit> add_bit(const Expr<F, Bit> &t, const Expr<F, Bit> &b) {
  const auto dims = t.dims();
  if (dims.empty() || dims.back() == 0) fail("add_bit: an empty word");
  const size_t w = dims.back(), ax = dims.size() - 1;
  std::vector<size_t> lead(dims.begin(), dims.end() - 1);
  if (b.size() != t.size() / w) fail("add_bit: one bit per word");
  std::vector<size_t> col = lead;
  col.push_back(1);
  const Expr<F, Bit> bl =
      lead.empty() || b.dims() == lead ? b : b.reshape(Shape(lead));
  std::vector<Expr<F, Bit>> cols;
  for (size_t i = 0; i + 1 < w; ++i) cols.push_back(t.at(ax, i));
  const auto prefix = prefix_and<F>(cols);
  Expr<F, Bit> flips = bl.reshape(Shape(col));
  for (size_t i = 0; i + 1 < w; ++i)
    flips = flips.concat((bl * prefix[i]).reshape(Shape(col)), ax);
  return t ^ flips;
}

// Whether the word X (Bit [n], least significant first) lies below the
// constant C (little-endian 64-bit limbs, n bits), by C's runs of equal
// bits from the top: below a run of ones when X's bits there are not all
// set or the rest lies below; below a run of zeros when X's bits there
// are all clear and the rest lies below. A run of one 1 bit reads X's bit
// itself; the lowest run of ones ends the comparison.
template <class F, class P>
Expr<F, Bit> below_constant(const Ref<F, Bit, P> &x,
                            const std::vector<uint64_t> &c) {
  using B = Expr<F, Bit>;
  const size_t n = x.n;
  if (n == 0 || 64 * c.size() < n) fail("below_constant: the widths differ");
  auto bit = [&c](size_t i) { return (c[i / 64] >> (i % 64)) & 1; };
  // The runs from the top, each with X's test there: all set for ones,
  // all clear for zeros.
  struct Run {
    bool ones;
    B test;
  };
  std::vector<Run> runs;
  for (size_t hi = n; hi > 0;) {
    const uint64_t v = bit(hi - 1);
    size_t lo = hi - 1;
    while (lo > 0 && bit(lo - 1) == v) --lo;
    if (v == 0)
      runs.push_back({false, (!B(x.slice(lo, hi))).all(0)});
    else if (hi - lo == 1)
      runs.push_back({true, B(x[lo])});
    else
      runs.push_back({true, x.slice(lo, hi).all(0)});
    hi = lo;
  }
  // From the bottom: zeros below the lowest one hold nothing below them.
  bool any = false;
  B rest;
  for (size_t r = runs.size(); r-- > 0;) {
    if (runs[r].ones) {
      rest = any ? B(!runs[r].test | rest) : B(!runs[r].test);
      any = true;
    } else if (any) {
      rest = runs[r].test & rest;
    }
  }
  if (!any) fail("below_constant: no word lies below 0");
  return rest;
}

// The carry chain of the group sums E ([..., G]) with the committed
// carries CARRY ([..., G - 1]): E_g + c_{g-1} = BASE c_g over the
// integers for every g < G, with c_{-1} = c_{G-1} = 0, as one
// assert_int_equal named NM (whose no-wrap condition the compiler
// checks). The carries enter through Gather views, c_{g-1} before c_g.
template <class F, class T, class P>
Predicate assert_carry_chain(const F &f, const Expr<F> &e,
                             const Ref<F, T, P> &carry, size_t groups,
                             const typename F::Elt &base, const Name &nm) {
  const size_t G = groups;
  if (G < 1) fail("assert_carry_chain: no group");
  std::vector<size_t> prev(G, kGatherNone), cur(G, kGatherNone);
  for (size_t g = 1; g < G; ++g) prev[g] = g - 1;
  for (size_t g = 0; g + 1 < G; ++g) cur[g] = g;
  const Lin<F> c_prev = Gather(f, prev, G - 1)(carry);
  const Lin<F> c_cur = Gather(f, cur, G - 1)(carry);
  return assert_int_equal(e + c_prev, base * c_cur, nm);
}

// The constant word X of W bits (Bit [w], least significant first) in
// domain D.
template <class F>
Expr<F, Bit> constant_word(const Domain<F> &D, uint64_t x, size_t w) {
  std::vector<uint64_t> v;
  for (size_t t = 0; t < w; ++t) v.push_back((x >> t) & 1);
  return D.constant(Bit{}, v, Shape(w));
}

// The coordinates, in a string of BYTES bytes (bit 8 m + t is bit t of
// byte m), of bits 0 .. BITS - 1 of the big-endian integer the string
// holds (BITS = 8 BYTES when 0): bit k at 8 (BYTES - 1 - k / 8) + k % 8.
inline std::vector<size_t> big_endian_bit_order(size_t bytes,
                                                size_t bits = 0) {
  if (bits == 0) bits = 8 * bytes;
  if (bits > 8 * bytes) fail("big_endian_bit_order: more bits than bytes");
  std::vector<size_t> idx(bits);
  for (size_t k = 0; k < bits; ++k) idx[k] = 8 * (bytes - 1 - k / 8) + k % 8;
  return idx;
}

}  // namespace proofs::gordiehowe::lib::arith

#endif  // PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_LIB_ARITH_H_
