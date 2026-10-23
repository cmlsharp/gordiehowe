// Copyright 2026 Chad Sharp and Paul Grubbs
// SPDX-License-Identifier: Apache-2.0
// Masked pre-parity MAC accumulators authenticated by Ligero linear
// constraints.
#ifndef PRIVACY_PROOFS_ZK_LIB_CIRCUITS_MAC_LINEAR_MAC_H_
#define PRIVACY_PROOFS_ZK_LIB_CIRCUITS_MAC_LINEAR_MAC_H_
#include <algorithm>
#include <chrono>
#include <cstddef>
#include <cstdint>
#include <cstring>
#include <map>
#include <memory>
#include <vector>

#include "algebra/fp14_8.h"
#include "algebra/fp_goldilocks.h"
#include "algebra/fp_goldilocks4.h"
#include "algebra/fp14_n.h"
#include "algebra/fp24_6.h"
#include "algebra/fp_native_wide.h"
#include "algebra/fp_p128.h"
#include "arrays/dense.h"
#include "circuits/compiler/compiler.h"
#include "circuits/logic/compiler_backend.h"
#include "random/transcript.h"
#include "zk/zk_common.h"
#include "circuits/ntt/host_ntt.h"

namespace proofs {
// Record the declared input layout using only the compiler's public allocation
// API. Derived wires are deliberately not accepted as committed input entries.
template <class F>
class InputLayoutBackend : public CompilerBackend<F> {
 public:
  explicit InputLayoutBackend(QuadCircuit<F>* q)
      : CompilerBackend<F>(q), q_(q) {}
  size_t input_wire() const {
    const size_t index = q_->ninput();
    const size_t wire = CompilerBackend<F>::input_wire();
    inputs_.emplace(wire, index);
    return wire;
  }
  size_t input_index(size_t wire) const {
    auto it = inputs_.find(wire);
    check(it != inputs_.end(), "linear MAC operand must be a declared input");
    return it->second;
  }
  size_t next_input_index() const { return q_->ninput(); }
  bool packs_bits() const { return q_->packs_bits(); }

 private:
  QuadCircuit<F>* q_;
  mutable std::map<size_t, size_t> inputs_;
};
namespace linear_mac {
inline auto root(const Fp24_6& f) { return f.of_scalar(5801164); }
inline auto root(const Fp14_8& f) { return f.of_scalar(8340); }
// 8340 has order 256 in F_12289 itself, so the same scalar serves every
// extension of it -- the root never leaves the base field.
template <size_t D, uint32_t B>
auto root(const Fp14_N<D, B>& f) { return f.of_scalar(8340); }
template <bool O>
auto root(const Fp128<O>& f) {
  return f.of_string("256628283718674907881677235433084396228");
}
// Order-256 root of the Goldilocks extension: the 2^32-th root of F_p to the
// 2^24.
inline auto root(const Fp64G2& f) {
  const Fp64G& b = f.base_field();
  return f.of_scalar(b.powf(goldilocks_root_2_32(), uint64_t{1} << 24));
}
}  // namespace linear_mac
namespace linear_mac256 {
// Order-512 roots.
inline auto root(const Fp64G4 &f) {
  return f.of_scalar(
      f.base_field().powf(goldilocks_root_2_32(), uint64_t{1} << 23));
}
template <class B, size_t D, uint32_t Beta, uint32_t Linear, bool Delayed,
          NativeConvolution Kernel, bool Tower>
auto root(const NativeWide<B, D, Beta, Linear, Delayed, Kernel, Tower>& f) {
  uint64_t r=1,a=B::m_==12289?1331:1938117;
  for(unsigned n=(B::m_==12289?4096:8192)/512;n;n>>=1,a=a*a%B::m_)if(n&1)r=r*a%B::m_;
  return f.of_scalar(r);
}
}  // namespace linear_mac256
namespace linear_mac {
// The W-bit MAC multiplies in GF(2)[x] modulo x^W + SUM_{d in taps} x^d, by
// an integer convolution of length 2W over F.
template <size_t W> struct Shape;
template <> struct Shape<128> {
  static constexpr int kTaps[4] = {0, 1, 2, 7};
  static constexpr char kDomain[] = "MAC-linear-fold256-v1";
};
template <> struct Shape<256> {
  static constexpr int kTaps[4] = {0, 2, 5, 10};
  static constexpr char kDomain[] = "MAC-linear-fold512-gf256-v1";
};
// A root of order 2W.
template <size_t W, class F> auto mac_root(const F& f) {
  if constexpr (W == 128)
    return linear_mac::root(f);
  else
    return linear_mac256::root(f);
}
template <class F>
auto power(const F& f, typename F::Elt x, size_t n) {
  auto y = f.one();
  for (; n; n >>= 1, x = f.mulf(x, x))
    if (n & 1) y = f.mulf(y, x);
  return y;
}
// Natural-order convenience interface. Batched production callers reuse a
// plan and keep bit-reversed frequencies between forward/inverse transforms.
template <size_t W, class F>
void basic_fft(const F& f, std::vector<typename F::Elt>& a, bool inv) {
  check(a.size() == 2 * W, "linear MAC FFT size");
  const host_ntt::Plan<F> plan(f, 2 * W, mac_root<W>(f));
  auto permute = [&]() {
    for (size_t i = 1, j = 0; i < 2 * W; ++i) {
      size_t bit = W;
      for (; j & bit; bit >>= 1) j ^= bit;
      j ^= bit;
      if (i < j) std::swap(a[i], a[j]);
    }
  };
  if (inv) permute();
  plan.transform(a, inv);
  if (!inv) permute();
}
// Reduce a product of degree < 2W - 1 modulo the MAC polynomial.
template <size_t W, class F>
void fold(const F& f, std::vector<typename F::Elt>& a) {
  for (int k = 2 * W - 2; k >= int(W); --k)
    for (int d : Shape<W>::kTaps) a[k - W + d] = f.addf(a[k - W + d], a[k]);
  a.resize(W);
}
template <size_t W, class F>
auto transpose_fold(const F& f, const typename F::Elt* lambda) {
  std::vector<typename F::Elt> a(2 * W, f.zero());
  std::copy(lambda, lambda + W, a.begin());
  for (size_t k = W; k < 2 * W - 1; ++k)
    for (int d : Shape<W>::kTaps) a[k] = f.addf(a[k], a[k - W + d]);
  return a;
}
template <class F, size_t W> class BasicArgument {
public:
  using E = typename F::Elt;
  using ExtraConstraints = typename ZkCommon<F>::ExtraConstraints;
  using Map = std::map<size_t, E>;
  struct Group {
    size_t first, last;
    std::vector<Map> x, r, blind;
  };
  const F &f;
  const InputLayoutBackend<F> *layout;
  size_t rows, pub_base = 0, npub = 0, pad_base = 0;
  std::vector<size_t> pubw, padw;
  std::vector<Group> groups;
  std::vector<E> reveals;
  double prepare_ms = 0;
  BasicArgument(const F &field, const InputLayoutBackend<F> &inputs,
                size_t count)
      : f(field), layout(&inputs), rows(count), reveals(count, field.zero()) {
    check(count > 0 && count % W == 0, "MAC rows must comprise full groups");
  }
  template <class LC> void publics(const LC &lc) {
    pub_base = layout->next_input_index();
    for (size_t i = 0; i < rows; ++i)
      pubw.push_back(lc.eltw_input());
    npub = layout->next_input_index();
  }
  template <class LC> void pads(const LC &lc) {
    pad_base = layout->next_input_index();
    for (size_t i = 0; i < rows; ++i)
      padw.push_back(lc.eltw_input());
  }
  Map capture(size_t w, bool public_input) {
    Map m{{layout->input_index(w), f.one()}};
    for (auto [i, a] : m)
      if (i && a != f.zero())
        check(public_input ? i < pub_base : i >= npub && i < pad_base,
              "linear MAC input ownership mismatch");
    return m;
  }
  template <class RNG> void sample(Dense<F> &wit, RNG &rng) const {
    for (size_t i = 0; i < rows; ++i)
      wit.v_[pad_base + i] = rng.subfield_elt(f);
  }
  E eval(const Map &m, const Dense<F> &wit) const {
    auto y = f.zero();
    for (auto [i, a] : m)
      y = f.addf(y, f.mulf(a, i ? wit.v_[i] : f.one()));
    return y;
  }
  template <class Bits> void prepare(Dense<F> &wit, const std::vector<Bits> &r) {
    auto start = std::chrono::steady_clock::now();
    const host_ntt::Plan<F> plan(f, 2 * W, mac_root<W>(f));
    for (size_t g = 0; g < groups.size(); ++g) {
      const auto &z = groups[g];
      std::vector<E> sum(2 * W, f.zero());
      for (size_t c = z.first; c < z.last; ++c) {
        std::vector<E> x(2 * W, f.zero()), y(2 * W, f.zero());
        for (size_t k = 0; k < W; ++k) {
          x[k] = eval(z.x[(c - z.first) * W + k], wit);
          y[k] = f.of_scalar(uint64_t(r[c][k] != 0));
        }
        plan.transform(x, false);
        plan.transform(y, false);
        for (size_t k = 0; k < 2 * W; ++k)
          sum[k] = f.addf(sum[k], f.mulf(x[k], y[k]));
      }
      plan.transform(sum, true);
      fold<W>(f, sum);
      for (size_t k = 0; k < W; ++k) {
        auto a = sum[k];
        if (!z.blind.empty())
          a = f.addf(a, eval(z.blind[k], wit));
        reveals[g * W + k] = f.addf(a, wit.v_[pad_base + g * W + k]);
      }
    }
    fill_public(wit);
    prepare_ms = std::chrono::duration<double, std::milli>(
                     std::chrono::steady_clock::now() - start)
                     .count();
  }
  void fill_public(Dense<F> &wit) const {
    for (size_t i = 0; i < rows; ++i)
      wit.v_[pub_base + i] = reveals[i];
  }
  template <class Hash>
  void absorb(BasicTranscript<Hash>& t) const {
    for (auto a : reveals)
      t.write(a, f);
  }
  size_t bytes() const { return rows * F::kSubFieldBytes; }
  // The rows' description, fixed before the protocol starts: the layout and
  // the complete affine maps, then the additional rows' tag. The ladder r and
  // the reveals are public inputs derived in the protocol (a challenge and an
  // absorbed prover message), so the tag leaves them out and can be absorbed
  // with the statement before any commitment.
  std::vector<uint8_t> tag(const std::vector<uint8_t> *additional = nullptr) const {
    std::vector<uint8_t> t;
    const char *domain = Shape<W>::kDomain;
    t.assign(domain, domain + std::strlen(domain) + 1);
    auto putn = [&](size_t n) {
      for (size_t i = 0; i < 8; ++i)
        t.push_back(uint8_t(n >> (8 * i)));
    };
    auto pute = [&](E e) {
      uint8_t b[F::kBytes];
      f.to_bytes_field(b, e);
      t.insert(t.end(), b, b + sizeof(b));
    };
    putn(npub);
    putn(pad_base);
    putn(rows);
    for (const auto &g : groups) {
      putn(g.first);
      putn(g.last);
      // Bind complete affine maps, not just their dimensions.
      for (const auto *maps : {&g.x, &g.r, &g.blind}) {
        putn(maps->size());
        for (const auto &m : *maps) {
          putn(m.size());
          for (auto [i, a] : m) {
            putn(i);
            pute(a);
          }
        }
      }
    }
    if (additional) {
      putn(additional->size());
      t.insert(t.end(), additional->begin(), additional->end());
    }
    return t;
  }
  // Both sides call this using public inputs only. No witness is captured.
  auto extra(const Dense<F> &pub,
             const ExtraConstraints *additional = nullptr) const {
    using EC = typename ZkCommon<F>::ExtraConstraints;
    EC ec;
    ec.tag = tag(additional ? &additional->tag : nullptr);
    auto plan = std::make_shared<host_ntt::Plan<F>>(f, 2 * W, mac_root<W>(f));
    std::vector<std::vector<std::vector<E>>> spectra;
    std::vector<E> rhs(rows);
    for (size_t gi = 0; gi < groups.size(); ++gi) {
      const auto &g = groups[gi];
      std::vector<std::vector<E>> gs;
      std::vector<E> constant(2 * W, f.zero());
      bool has_constant = false;
      for (size_t c = 0; c < g.last - g.first; ++c) {
        std::vector<E> rev(2 * W, f.zero()), xc(2 * W, f.zero());
        for (size_t k = 0; k < W; ++k) {
          E rk = eval(g.r[c * W + k], pub);
          rev[(2 * W - k) % (2 * W)] = rk;
          auto it = g.x[c * W + k].find(0);
          if (it != g.x[c * W + k].end()) {
            xc[k] = it->second;
            has_constant |= xc[k] != f.zero();
          }
        }
        // The constant part is normally zero; retain it for affine bit
        // encodings.
        if (has_constant) {
          std::vector<E> forward(2 * W, f.zero());
          for (size_t k = 0; k < W; ++k)
            forward[k] = rev[(2 * W - k) % (2 * W)];
          plan->transform(forward, false);
          plan->transform(xc, false);
          for (size_t k = 0; k < 2 * W; ++k)
            constant[k] = f.addf(constant[k], f.mulf(xc[k], forward[k]));
        }
        plan->transform(rev, false);
        gs.push_back(std::move(rev));
      }
      if (has_constant) {
        plan->transform(constant, true);
        fold<W>(f, constant);
      }
      for (size_t k = 0; k < W; ++k) {
        auto a = constant[k];
        if (!g.blind.empty()) {
          auto it = g.blind[k].find(0);
          if (it != g.blind[k].end())
            a = f.addf(a, it->second);
        }
        rhs[gi * W + k] = f.subf(pub.v_[pub_base + gi * W + k], a);
      }
      spectra.push_back(std::move(gs));
    }
    ec.gen = [rhs](auto &a, auto &b, size_t &ci) {
      b.insert(b.end(), rhs.begin(), rhs.end());
      ci += rhs.size();
    };
    ec.accumulate = [this, plan, spectra = std::move(spectra)](
                        E *A, const E *al, size_t base) {
      auto addmap = [&](const Map &m, E scale) {
        for (auto [i, a] : m)
          if (i)
            A[i - npub] = f.addf(A[i - npub], f.mulf(a, scale));
      };
      for (size_t gi = 0; gi < groups.size(); ++gi) {
        const auto &g = groups[gi];
        const E *l = al + base + gi * W;
        auto lifted = transpose_fold<W>(f, l);
        plan->transform(lifted, false);
        for (size_t c = 0; c < g.last - g.first; ++c) {
          auto weights = lifted;
          for (size_t k = 0; k < 2 * W; ++k)
            weights[k] = f.mulf(weights[k], spectra[gi][c][k]);
          plan->transform(weights, true);
          for (size_t k = 0; k < W; ++k)
            addmap(g.x[c * W + k], weights[k]);
        }
        for (size_t k = 0; k < W; ++k) {
          size_t p = pad_base - npub + gi * W + k;
          A[p] = f.addf(A[p], l[k]);
          if (!g.blind.empty())
            addmap(g.blind[k], l[k]);
        }
      }
    };
    if (additional) {
      check(bool(additional->accumulate),
            "additional MAC constraints require fast accumulation");
      auto first_gen = ec.gen, second_gen = additional->gen;
      auto first_acc = ec.accumulate, second_acc = additional->accumulate;
      const size_t offset = rows;
      ec.gen = [first_gen, second_gen](auto &a, auto &b, size_t &ci) {
        first_gen(a, b, ci);
        second_gen(a, b, ci);
      };
      ec.accumulate = [first_acc, second_acc, offset](E *a, const E *al,
                                                      size_t base) {
        first_acc(a, al, base);
        second_acc(a, al, base + offset);
      };
    }
    return ec;
  }
};
template <class C, class P, class Z, class Wit, class T>
bool prove(C &c, P &p, Z &z, Wit &w, T &t,
           const typename C::ExtraConstraints *other = nullptr) {
  auto ec = c.extra(w, other);
  return p.prove(z, w, t, &ec);
}
template <class C, class V, class Z, class Wit, class T>
bool verify(C &c, V &v, Z &z, Wit &w, T &t,
            const typename C::ExtraConstraints *other = nullptr) {
  c.fill_public(w);
  auto ec = c.extra(w, other);
  return v.verify(z, w, t, &ec);
}
template <class F> using Argument = BasicArgument<F, 128>;
template <class F>
void fft(const F& f, std::vector<typename F::Elt>& a, bool inv) {
  basic_fft<128>(f, a, inv);
}
}  // namespace linear_mac
namespace linear_mac256 {
template <class F> using Argument = linear_mac::BasicArgument<F, 256>;
using linear_mac::power;
using linear_mac::prove;
using linear_mac::verify;
template <class F>
void fft(const F& f, std::vector<typename F::Elt>& a, bool inv) {
  linear_mac::basic_fft<256>(f, a, inv);
}
template <class F> void fold(const F& f, std::vector<typename F::Elt>& a) {
  linear_mac::fold<256>(f, a);
}
template <class F>
auto transpose_fold(const F& f, const typename F::Elt* lambda) {
  return linear_mac::transpose_fold<256>(f, lambda);
}
}  // namespace linear_mac256
}  // namespace proofs
#endif
