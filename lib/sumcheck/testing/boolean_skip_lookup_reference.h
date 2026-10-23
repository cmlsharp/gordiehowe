// Copyright 2026 Chad Sharp and Paul Grubbs
// SPDX-License-Identifier: Apache-2.0

// UNSAFE lookup reference, retained ONLY for differential tests/benchmarks.
// Experimental non-ZK Boolean zerocheck reduction; NOT a standalone proof.
// Terminal claims require authenticated openings of the original bit tables.
#ifndef PRIVACY_PROOFS_ZK_LIB_SUMCHECK_BOOLEAN_SKIP_LOOKUP_REFERENCE_H_
#define PRIVACY_PROOFS_ZK_LIB_SUMCHECK_BOOLEAN_SKIP_LOOKUP_REFERENCE_H_
#include "arrays/eqs.h"
#include "gf2k/gf2_256.h"
#include "random/transcript.h"
#include "util/panic.h"
#include <array>
#include <chrono>
#include <cstdint>
#include <utility>
#include <vector>
namespace proofs {
class BooleanSkipLookupReference {
public:
  using Field =
      GF2_256<>; // 16-bit commitment subfield, separate 8-bit skip subfield.
  using Elt = Field::Elt;
  struct Word {
    uint64_t a, b, c;
  };
  struct Proof {
    std::vector<Elt> skip; // Values outside the w-point zero domain.
    // Coefficients q1, q2 of each round's quadratic q_i(X) = q0 + q1 X +
    // q2 X^2; the verifier derives q0 from claim = prefix (q0 + rho_i (q1 +
    // q2)), prefix = eq(rho_{<i}, s_{<i}).
    std::vector<std::array<Elt, 2>> rounds;
    std::array<Elt, 3> terminal;
  };
  struct Stats {
    double weights = 0, skip = 0, bind = 0, sumcheck = 0;
    size_t rows = 0;
  };
  const Field &f;
  explicit BooleanSkipLookupReference(const Field &field, unsigned width)
      : f(field), w(width) {
    check(w >= 1 && w <= 64 && (w & (w - 1)) == 0, "skip width");
    GF2_256<3> small_field;
    std::array<GF2_256<3>::Elt, 256> small_embed;
    for (unsigned i = 0; i < 256; ++i) {
      small_embed[i] = small_field.of_scalar(i);
      embed[i] = f.of_scalar_field(small_embed[i].unpack().u64());
    }
    for (unsigned i = 0; i < 256; ++i)
      for (unsigned j = 0; j < 256; ++j) {
        uint8_t b;
        small_field.to_bytes_subfield(
            &b, small_field.mulf(small_embed[i], small_embed[j]));
        mul[i][j] = b;
      }
    for (unsigned i = 1; i < 256; ++i)
      for (unsigned j = 1; j < 256; ++j)
        if (mul[i][j] == 1)
          inv[i] = j;
    // Tabulate the linear bit->small-field interpolation map for byte chunks.
    small.resize((w - 1) * chunks() * 256);
    for (unsigned x = w; x < 2 * w - 1; ++x) {
      auto l = small_basis(0, w, x);
      for (unsigned b = 0; b < chunks(); ++b)
        for (unsigned value = 1; value < 256; ++value) {
          unsigned bit = __builtin_ctz(value), prev = value & (value - 1);
          small[((x - w) * chunks() + b) * 256 + value] =
              small[((x - w) * chunks() + b) * 256 + prev] ^
              (8 * b + bit < w ? l[8 * b + bit] : 0);
        }
    }
  }
  unsigned width() const { return w; }
  // Prover and verifier initialize an identically domain-separated transcript
  // after binding a real commitment. Tests use a mock public instance seed.
  template <class Hash>
  Proof prove(const std::vector<Word> &input, BasicTranscript<Hash> &ts,
              Stats &stats, const std::vector<Elt> *pads = nullptr) const {
    size_t pad_cursor = 0;
    auto mask = [&](Elt &v) {
      if (pads)
        f.add(v, pads->at(pad_cursor++));
    };
    auto start = now();
    auto words = split(input);
    size_t n = 1, logn = 0;
    while (n < words.size()) {
      n *= 2;
      ++logn;
    }
    words.resize(n, Word{});
    stats.rows = n;
    std::vector<Elt> batch(logn);
    for (auto &x : batch)
      x = challenge(ts);
    Eqs<Field> weights(logn, n, batch.data(), f);
    std::vector<Elt> e = std::move(static_cast<Dense<Field> &>(weights).v_);
    stats.weights = elapsed(start);
    Proof proof;
    start = now();
    for (unsigned x = w; x < 2 * w - 1; ++x) {
      std::array<Elt, 256> buckets{};
      for (size_t i = 0; i < n; ++i) {
        uint8_t a = small_eval(words[i].a, x - w),
                b = small_eval(words[i].b, x - w),
                c = small_eval(words[i].c, x - w);
        f.add(buckets[mul[a][b] ^ c], e[i]);
      }
      Field::Accum acc{};
      for (unsigned b = 1; b < 256; ++b)
        f.mac(acc, buckets[b], embed[b]);
      proof.skip.push_back(f.reduce(acc));
    }
    for (auto &v : proof.skip)
      mask(v);
    ts.write(proof.skip.data(), 1, proof.skip.size(), f);
    Elt r = challenge(ts);
    stats.skip = elapsed(start);
    start = now();
    // Round i sends the quadratic q_i with
    //   p_i(X) = eq(rho_{<i}, s_{<i}) eq(rho_i, X) q_i(X),
    // q_i(X) = sum_x eq(rho_{>i}, x) (A B + C)(s_{<i}, X, x). Adding the two
    // halves of e over its low variable drops eq(rho_i, .), since
    // eq(rho, 0) + eq(rho, 1) = 1: e holds eq(rho_{>i}, .) in round i.
    if (n > 1) {
      for (size_t i = 0; i < n / 2; ++i)
        e[i] = f.addf(e[2 * i], e[2 * i + 1]);
      e.resize(n / 2);
    }
    std::vector<Elt> a, b, c;
    if (w == 1 && n > 1) {
      // Give the ordinary Boolean control a cheap first round: all its
      // operand coefficients are bits, so multiply weights by selection/XOR.
      std::array<Elt, 2> p{};
      for (size_t i = 0; i < n / 2; ++i) {
        const auto &u = words[2 * i];
        const auto &v = words[2 * i + 1];
        uint64_t da = u.a ^ v.a, db = u.b ^ v.b, dc = u.c ^ v.c;
        uint64_t v1 = (da & u.b) ^ (u.a & db) ^ dc, v2 = da & db;
        if (v1)
          f.add(p[0], e[i]);
        if (v2)
          f.add(p[1], e[i]);
      }
      for (auto &v : p)
        mask(v);
      proof.rounds.push_back(p);
      ts.write(p.data(), 1, p.size(), f);
      Elt t = challenge(ts);
      Elt lookup[4] = {f.zero(), f.addf(f.one(), t), t, f.one()};
      a.resize(n / 2);
      b.resize(n / 2);
      c.resize(n / 2);
      for (size_t i = 0; i < n / 2; ++i) {
        a[i] = lookup[words[2 * i].a + 2 * words[2 * i + 1].a];
        b[i] = lookup[words[2 * i].b + 2 * words[2 * i + 1].b];
        c[i] = lookup[words[2 * i].c + 2 * words[2 * i + 1].c];
      }
      for (size_t i = 0; i < n / 4; ++i)
        e[i] = f.addf(e[2 * i], e[2 * i + 1]);
      n /= 2;
    } else {
      auto tables = large_tables(basis(0, w, r));
      a.resize(n);
      b.resize(n);
      c.resize(n);
      for (size_t i = 0; i < n; ++i) {
        a[i] = large_eval(words[i].a, tables);
        b[i] = large_eval(words[i].b, tables);
        c[i] = large_eval(words[i].c, tables);
      }
    }
    stats.bind = elapsed(start);
    start = now();
    while (n > 1) {
      std::array<Field::Accum, 2> accum{};
      for (size_t i = 0; i < n / 2; ++i) {
        Elt a0 = a[2 * i], da = f.addf(a0, a[2 * i + 1]);
        Elt b0 = b[2 * i], db = f.addf(b0, b[2 * i + 1]);
        Elt dc = f.addf(c[2 * i], c[2 * i + 1]);
        Elt v1 = f.addf(f.addf(f.mulf(da, b0), f.mulf(a0, db)), dc);
        Elt v2 = f.mulf(da, db);
        f.mac(accum[0], e[i], v1);
        f.mac(accum[1], e[i], v2);
      }
      std::array<Elt, 2> p;
      for (unsigned j = 0; j < 2; ++j)
        p[j] = f.reduce(accum[j]);
      for (auto &v : p)
        mask(v);
      proof.rounds.push_back(p);
      ts.write(p.data(), 1, p.size(), f);
      Elt t = challenge(ts);
      for (auto *v : {&a, &b, &c})
        for (size_t i = 0; i < n / 2; ++i)
          (*v)[i] = f.addf((*v)[2 * i],
                           f.mulf(t, f.addf((*v)[2 * i], (*v)[2 * i + 1])));
      for (size_t i = 0; i < n / 4; ++i)
        e[i] = f.addf(e[2 * i], e[2 * i + 1]);
      n /= 2;
    }
    proof.terminal = {a[0], b[0], c[0]};
    for (auto &v : proof.terminal)
      mask(v);
    stats.sumcheck = elapsed(start);
    return proof;
  }
  // The supplied opening callback is a REQUIRED trust boundary, not a PCS.
  // It must authenticate all three claims against a prior bit-valued witness.
  template <class Opening, class Hash>
  bool verify(const Proof &proof, size_t word_count, BasicTranscript<Hash> &ts,
              Opening &&opening) const {
    size_t n = 1, logn = 0;
    while (n < word_count * (64 / w)) {
      n *= 2;
      ++logn;
    }
    if (proof.skip.size() != w - 1 || proof.rounds.size() != logn)
      return false;
    std::vector<Elt> batch(logn);
    for (auto &x : batch)
      x = challenge(ts);
    ts.write(proof.skip.data(), 1, proof.skip.size(), f);
    Elt r = challenge(ts), claim = f.zero();
    auto l = basis(0, 2 * w - 1, r);
    for (unsigned i = 0; i < w - 1; ++i)
      f.add(claim, f.mulf(proof.skip[i], l[w + i]));
    std::vector<Elt> challenges;
    Elt prefix = f.one();
    for (size_t i = 0; i < logn; ++i) {
      const auto &q = proof.rounds[i];
      ts.write(q.data(), 1, q.size(), f);
      Elt t = challenge(ts);
      challenges.push_back(t);
      // With q0 = claim / prefix + rho (q1 + q2), the next claim
      // prefix eq_i(t) q(t) is eq_i(t) claim + prefix eq_i(t)
      // ((rho + t) q1 + (rho + t^2) q2).
      Elt eq_i = f.addf(f.one(), f.addf(batch[i], t));
      f.mul(prefix, eq_i);
      Elt rest = f.addf(f.mulf(f.addf(batch[i], t), q[0]),
                        f.mulf(f.addf(batch[i], f.mulf(t, t)), q[1]));
      claim = f.addf(f.mulf(eq_i, claim), f.mulf(prefix, rest));
    }
    // prefix is now eq(rho, s), the weight of the terminal row.
    if (claim !=
        f.mulf(prefix, f.addf(f.mulf(proof.terminal[0], proof.terminal[1]),
                              proof.terminal[2])))
      return false;
    return opening(r, challenges, proof.terminal);
  }
  // Slow reference opening oracle, used ONLY by algebra tests. It reveals the
  // entire witness to the checker and must never be treated as a proof backend.
  bool reference_open(const std::vector<Word> &input, const Elt &r,
                      const std::vector<Elt> &challenges,
                      const std::array<Elt, 3> &claimed) const {
    auto words = split(input);
    auto l = basis(0, w, r);
    Eqs<Field> eq(challenges.size(), size_t(1) << challenges.size(),
                  challenges.data(), f);
    std::array<Elt, 3> got{};
    for (size_t i = 0; i < words.size(); ++i) {
      uint64_t values[3] = {words[i].a, words[i].b, words[i].c};
      for (unsigned j = 0; j < 3; ++j) {
        Elt v = f.zero();
        for (unsigned z = 0; z < w; ++z)
          if ((values[j] >> z) & 1)
            f.add(v, l[z]);
        f.add(got[j], f.mulf(v, eq.at(i)));
      }
    }
    return got == claimed;
  }
  std::vector<Elt> bit_basis(const Elt &r) const { return basis(0, w, r); }
  std::vector<Elt> skip_basis(const Elt &r) const {
    return basis(0, 2 * w - 1, r);
  }

private:
  template <class Hash>
  Elt challenge(BasicTranscript<Hash> &ts) const {
    return f.sample([&](size_t n, uint8_t *b) { ts.bytes(b, n); });
  }
  unsigned w;
  std::array<Elt, 256> embed;
  uint8_t mul[256][256]{}, inv[256]{};
  std::vector<uint8_t> small;
  unsigned chunks() const { return (w + 7) / 8; }
  static std::chrono::steady_clock::time_point now() {
    return std::chrono::steady_clock::now();
  }
  template <class T> static double elapsed(T t) {
    return std::chrono::duration<double, std::milli>(now() - t).count();
  }
  std::vector<Word> split(const std::vector<Word> &in) const {
    std::vector<Word> out;
    out.reserve(in.size() * (64 / w));
    uint64_t mask = w == 64 ? ~uint64_t(0) : (uint64_t(1) << w) - 1;
    for (const auto &x : in)
      for (unsigned z = 0; z < 64; z += w)
        out.push_back(
            {(x.a >> z) & mask, (x.b >> z) & mask, (x.c >> z) & mask});
    return out;
  }
  std::vector<uint8_t> small_basis(unsigned first, unsigned n,
                                   unsigned x) const {
    std::vector<uint8_t> l(n, 1);
    for (unsigned i = 0; i < n; ++i)
      for (unsigned j = 0; j < n; ++j)
        if (i != j)
          l[i] =
              mul[l[i]][mul[x ^ (first + j)][inv[(first + i) ^ (first + j)]]];
    return l;
  }
  std::vector<Elt> basis(unsigned first, unsigned n, const Elt &r) const {
    std::vector<Elt> l(n, f.zero());
    for (unsigned i = 0; i < n; ++i)
      if (r == embed[first + i]) {
        l[i] = f.one();
        return l;
      }
    Elt product = f.one();
    for (unsigned i = 0; i < n; ++i)
      f.mul(product, f.addf(r, embed[first + i]));
    for (unsigned i = 0; i < n; ++i) {
      uint8_t den = 1;
      for (unsigned j = 0; j < n; ++j)
        if (i != j)
          den = mul[den][(first + i) ^ (first + j)];
      l[i] = f.mulf(product, f.mulf(embed[inv[den]],
                                    f.invertf(f.addf(r, embed[first + i]))));
    }
    return l;
  }
  uint8_t small_eval(uint64_t word, unsigned point) const {
    uint8_t v = 0;
    for (unsigned b = 0; b < chunks(); ++b)
      v ^= small[(point * chunks() + b) * 256 + ((word >> (8 * b)) & 255)];
    return v;
  }
  std::vector<Elt> large_tables(const std::vector<Elt> &l) const {
    std::vector<Elt> t(chunks() * 256);
    for (unsigned b = 0; b < chunks(); ++b)
      for (unsigned v = 1; v < 256; ++v) {
        unsigned bit = __builtin_ctz(v);
        t[b * 256 + v] = t[b * 256 + (v & (v - 1))];
        if (8 * b + bit < w)
          f.add(t[b * 256 + v], l[8 * b + bit]);
      }
    return t;
  }
  Elt large_eval(uint64_t word, const std::vector<Elt> &t) const {
    Elt v = f.zero();
    for (unsigned b = 0; b < chunks(); ++b)
      f.add(v, t[b * 256 + ((word >> (8 * b)) & 255)]);
    return v;
  }
};
} // namespace proofs
#endif
