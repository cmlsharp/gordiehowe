// Copyright 2026 Chad Sharp and Paul Grubbs
// SPDX-License-Identifier: Apache-2.0

// Experimental relative-field packing. Apache-2.0.
#ifndef PRIVACY_PROOFS_ZK_LIB_ZK_ZK_EXTENSION_PACKED_H_
#define PRIVACY_PROOFS_ZK_LIB_ZK_ZK_EXTENSION_PACKED_H_
#include "algebra/fp14_n.h"
#include "algebra/fp24_6.h"
#include "algebra/fp_goldilocks.h"
#include "algebra/fp_goldilocks4.h"
#include "algebra/fp_native_wide.h"
#include "gf2k/gf2_128.h"
#include "gf2k/gf2_256.h"
#include "ligero/ligero_param.h"
#include "random/transcript.h"
#include <array>
#include <string>
#include <type_traits>
#include <vector>

namespace proofs {
template <class F> struct ExtensionTraits {
  static constexpr bool supported = false;
  static constexpr size_t degree = 1;
  static constexpr uint64_t q = 2;
};
template <> struct ExtensionTraits<GF2_128<>> {
  static constexpr bool supported = true;
  static constexpr size_t degree = 8;
  static constexpr uint64_t q = 65536;
};
template <> struct ExtensionTraits<Fp24_6> {
  static constexpr bool supported = true;
  static constexpr size_t degree = 6;
  static constexpr uint64_t q = 8380417;
};
template <> struct ExtensionTraits<Fp14_9> {
  static constexpr bool supported = true;
  static constexpr size_t degree = 9;
  static constexpr uint64_t q = 12289;
};
template <> struct ExtensionTraits<Fp64G2> {
  static constexpr bool supported = true;
  static constexpr size_t degree = 2;
  static constexpr uint64_t q = 0xffffffff00000001ULL;
};

template <> struct ExtensionTraits<GF2_256<>> {
  static constexpr bool supported = true;
  static constexpr size_t degree = 16;
  static constexpr uint64_t q = 65536;
};
template <> struct ExtensionTraits<Fp64G4> {
  static constexpr bool supported = true;
  static constexpr size_t degree = 4;
  static constexpr uint64_t q = Fp64G::kP;
};
template <class F> struct NativeWideTraits {
  static constexpr bool value = false, monomial = false, tower = false;
};
template <class B, size_t D, uint32_t Beta, uint32_t Linear, bool Delayed,
          NativeConvolution Kernel, bool Tower>
struct NativeWideTraits<NativeWide<B, D, Beta, Linear, Delayed, Kernel, Tower>> {
  static constexpr bool value = true, monomial = !Tower && Linear == 0, tower = Tower;
};
template <class B, size_t D, uint32_t Beta, uint32_t Linear, bool Delayed,
          NativeConvolution Kernel, bool Tower>
struct ExtensionTraits<NativeWide<B, D, Beta, Linear, Delayed, Kernel, Tower>> {
  static constexpr bool supported = true;
  static constexpr size_t degree = D;
  static constexpr uint64_t q = B::m_;
};

template <class F> struct ExtensionBasis {
  using E = typename F::Elt;
  static constexpr size_t D = ExtensionTraits<F>::degree;
  static constexpr bool Native =
      std::is_same_v<F, Fp24_6> || std::is_same_v<F, Fp14_9> ||
      std::is_same_v<F, Fp64G4> || NativeWideTraits<F>::monomial;
  std::array<E, D> beta, dual;
  std::array<std::array<E, D>, D> beta_phi;
  // Native Frobenius and multiplication by a trace-dual basis element are
  // scaled coordinate permutations. Store embedded base scalars for the scales.
  std::array<std::array<size_t, D>, D> dest{}, dual_dest{};
  std::array<std::array<E, D>, D> scale, dual_scale;
  // Tower dual multiplication maps one four-coordinate block into another.
  // Coefficients are public; applying a map never indexes by witness values.
  std::vector<std::array<std::array<uint32_t, 4>, 4>> tower_dual_maps;
  // GF(2)-linear nibble tables for the eight relative Frobenius maps.
  std::vector<E> binary_phi;

  static E power(E x, uint64_t e, const F &f) {
    E y = f.one();
    for (; e; e >>= 1) {
      if (e & 1)
        f.mul(y, x);
      x = f.mulf(x, x);
    }
    return y;
  }
  static E slow_phi(E x, size_t k, const F &f) {
    if constexpr (NativeWideTraits<F>::value)
      return f.frobenius(x, k);
    for (size_t j = 0; j < k % D; ++j)
      x = power(x, ExtensionTraits<F>::q, f);
    return x;
  }
  static E trace(E x, const F &f) {
    E y = f.zero();
    for (size_t j = 0; j < D; ++j) {
      f.add(y, x);
      x = slow_phi(x, 1, f);
    }
    return y;
  }
  explicit ExtensionBasis(const F &f) {
    E generator = f.one();
    if constexpr ((std::is_same_v<F, GF2_128<>> ||
                   std::is_same_v<F, GF2_256<>>))
      generator = f.of_scalar_field(2);
    if constexpr (Native || NativeWideTraits<F>::value) {
      generator = f.zero();
      generator.e[1] = f.base_field().one();
    }
    if constexpr (std::is_same_v<F, Fp64G2>) {
      generator = f.zero();
      generator.im = f.base_field().one();
    }
    beta[0] = f.one();
    for (size_t i = 1; i < D; ++i) {
      if constexpr (NativeWideTraits<F>::value) {
        beta[i] = f.zero();
        beta[i].e[i] = f.base_field().one();
      } else
        beta[i] = f.mulf(beta[i - 1], generator);
    }
    for (size_t k = 0; k < D; ++k)
      for (size_t i = 0; i < D; ++i)
        beta_phi[k][i] = slow_phi(beta[i], k, f);
    std::array<std::array<E, 2 * D>, D> m;
    for (size_t i = 0; i < D; ++i)
      for (size_t j = 0; j < D; ++j) {
        m[i][j] = trace(f.mulf(beta[i], beta[j]), f);
        m[i][j + D] = i == j ? f.one() : f.zero();
      }
    for (size_t c = 0; c < D; ++c) {
      size_t pivot = c;
      while (pivot < D && m[pivot][c] == f.zero())
        ++pivot;
      check(pivot < D, "relative trace form nonsingular");
      std::swap(m[pivot], m[c]);
      E inv = f.invertf(m[c][c]);
      for (auto &x : m[c])
        f.mul(x, inv);
      for (size_t i = 0; i < D; ++i)
        if (i != c) {
          E a = m[i][c];
          for (size_t j = 0; j < 2 * D; ++j)
            f.sub(m[i][j], f.mulf(a, m[c][j]));
        }
    }
    for (size_t i = 0; i < D; ++i) {
      dual[i] = f.zero();
      for (size_t j = 0; j < D; ++j)
        f.add(dual[i], f.mulf(m[i][j + D], beta[j]));
    }
    if constexpr (Native) {
      for (size_t k = 0; k < D; ++k)
        for (size_t i = 0; i < D; ++i) {
          auto decode = [&](const E &x, size_t &dst, E &s) {
            size_t count = 0;
            for (size_t j = 0; j < D; ++j)
              if (x.e[j] != f.base_field().zero()) {
                dst = j;
                s = f.of_scalar(x.e[j]);
                ++count;
              }
            check(count == 1, "native basis map must be monomial");
          };
          decode(beta_phi[k][i], dest[k][i], scale[k][i]);
          decode(f.mulf(dual[k], beta[i]), dual_dest[k][i], dual_scale[k][i]);
        }
    }
    if constexpr (NativeWideTraits<F>::tower) {
      tower_dual_maps.resize(D * 5);
      for (size_t h = 0; h < D; ++h)
        for (size_t j = 0; j < 5; ++j) {
          size_t dst = 5;
          for (size_t i = 0; i < 4; ++i) {
            E p = f.mulf(dual[h], beta[4 * j + i]);
            for (size_t k = 0; k < D; ++k)
              if (p.e[k] != f.base_field().zero()) {
                if (dst == 5) dst = k / 4;
                check(dst == k / 4, "tower dual map must have one output block");
              }
            check(dst < 5, "tower dual product nonzero");
            for (size_t k = 0; k < 4; ++k)
              tower_dual_maps[h * 5 + j][k][i] = p.e[4 * dst + k].n;
          }
          dual_dest[h][j] = dst;
        }
    }
    if constexpr ((std::is_same_v<F, GF2_128<>> ||
                   std::is_same_v<F, GF2_256<>>)) {
      binary_phi.resize(D * (F::kBits / 4) * 16, f.zero());
      for (size_t k = 1; k < D; ++k)
        for (size_t nib = 0; nib < F::kBits / 4; ++nib) {
          std::array<E, 4> bits;
          for (size_t b = 0; b < 4; ++b) {
            std::array<uint64_t, F::kBits / 64> raw{};
            raw[nib / 16] = uint64_t{1} << (4 * (nib % 16) + b);
            bits[b] = slow_phi(f.of_scalar_field(raw), k, f);
          }
          for (size_t v = 1; v < 16; ++v)
            for (size_t b = 0; b < 4; ++b)
              if ((v >> b) & 1)
                f.add(binary_phi[(k * (F::kBits / 4) + nib) * 16 + v], bits[b]);
        }
    }
  }
  // Cached arrays have no references to F; all supported field types have
  // fixed moduli/bases. Initialization is paid once per executable.
  static const ExtensionBasis &get(const F &f) {
    static const ExtensionBasis b(f);
    return b;
  }
  // Table indices may depend on x: only public coefficients or transcript
  // messages already revealed to the verifier may be passed here.
  E phi_public(const E &x, size_t k, const F &f) const {
    k %= D;
    if (k == 0)
      return x;
    if constexpr ((std::is_same_v<F, GF2_128<>> ||
                   std::is_same_v<F, GF2_256<>>)) {
      uint8_t raw[F::kBytes];
      f.to_bytes_field(raw, x);
      E out = f.zero();
      for (size_t nib = 0; nib < F::kBits / 4; ++nib)
        f.add(out, binary_phi[(k * (F::kBits / 4) + nib) * 16 +
                              ((raw[nib / 2] >> (4 * (nib % 2))) & 15)]);
      return out;
    } else if constexpr (Native) {
      E out = f.zero();
      for (size_t i = 0; i < D; ++i)
        out.e[dest[k][i]] = f.base_field().mulf(scale[k][i].e[0], x.e[i]);
      return out;
    } else if constexpr (std::is_same_v<F, Fp64G2>) {
      E out = x;
      f.base_field().neg(out.im);
      return out;
    } else
      return slow_phi(x, k, f);
  }
  E mul_dual(size_t i, const E &x, const F &f) const {
    if constexpr (NativeWideTraits<F>::tower) {
      E out = f.zero();
      for (size_t j = 0; j < 5; ++j)
        for (size_t k = 0; k < 4; ++k) {
          uint64_t sum = 0;
          for (size_t h = 0; h < 4; ++h)
            sum += uint64_t(tower_dual_maps[i * 5 + j][k][h]) * x.e[4 * j + h].n;
          out.e[4 * dual_dest[i][j] + k] = f.base_field().reduce(sum);
        }
      return out;
    } else if constexpr (Native) {
      E out = f.zero();
      for (size_t j = 0; j < D; ++j)
        out.e[dual_dest[i][j]] =
            f.base_field().mulf(dual_scale[i][j].e[0], x.e[j]);
      return out;
    } else
      return f.mulf(dual[i], x);
  }
  void pack_coordinate(E &x, size_t i, const E &y, const F &f) const {
    if constexpr (Native || NativeWideTraits<F>::value)
      x.e[i] = y.e[0];
    else if constexpr (std::is_same_v<F, Fp64G2>) {
      if (i == 0)
        x.re = y.re;
      else
        x.im = y.re;
    } else
      f.add(x, f.mulf(beta[i], y));
  }
};

template <class F> struct ExtensionLayout {
  using E = typename F::Elt;
  static constexpr size_t D = ExtensionTraits<F>::degree;
  size_t original_n, subfield_n, words, prefix, size;
  ExtensionLayout(size_t n, size_t sub, size_t w)
      : original_n(n), subfield_n(sub), words(ceildiv(sub, D)),
        prefix(w ? ceildiv(D * D, w) * w : D * D),
        size(prefix + words + n - sub) {
    check(sub <= n, "extension subfield boundary");
  }
  size_t map(size_t old) const {
    check(old >= subfield_n && old < original_n,
          "quadratic uses packed subfield input");
    return prefix + words + old - subfield_n;
  }
  void remap(std::vector<LigeroQuadraticConstraint> &q) const {
    for (auto &x : q) {
      x.x = map(x.x);
      x.y = map(x.y);
      x.z = map(x.z);
    }
  }
  std::vector<E> pack(const std::vector<E> &original, RandomEngine &rng,
                      const F &f) const {
    check(original.size() == original_n, "original packing witness length");
    const auto &b = ExtensionBasis<F>::get(f);
    std::vector<E> out(size, f.zero());
    for (size_t i = 0; i < D * D; ++i)
      out[i] = rng.subfield_elt(f);
    for (size_t i = 0; i < subfield_n; ++i) {
      check(f.in_subfield(original[i]), "packed input must lie in subfield");
      b.pack_coordinate(out[prefix + i / D], i % D, original[i], f);
    }
    for (size_t i = subfield_n; i < original_n; ++i)
      out[map(i)] = original[i];
    return out;
  }
  template <class Hash> void bind(BasicTranscript<Hash> &ts) const {
    static const char tag[] = "experimental/relative-input-packing/v1";
    ts.write(reinterpret_cast<const uint8_t *>(tag), sizeof(tag));
    uint8_t dims[32];
    u64_to_le(dims, D);
    u64_to_le(dims + 8, original_n);
    u64_to_le(dims + 16, subfield_n);
    u64_to_le(dims + 24, prefix);
    ts.write(dims, sizeof(dims));
  }
};

// Batch all existing GKR and application linear rows AFTER their claims have
// been transcript-bound, BEFORE the new masked trace measurements. This adds
// one random linear-combination soundness event, bounded by 1/|K|. Quadratic
// rows remain separate and are remapped normally by Ligero.
template <class F> struct ExtensionForms {
  using E = typename F::Elt;
  using Llc = LigeroLinearConstraint<F>;
  static constexpr size_t D = ExtensionTraits<F>::degree;
  std::vector<E> coeff;
  E target;
  std::array<std::vector<E>, D> a;
  template <class Extra, class Hash>
  ExtensionForms(const ExtensionLayout<F> &l, size_t nl,
                 const std::vector<Llc> &ll, const std::vector<E> &rhs,
                 BasicTranscript<Hash> &ts, const Extra *extra, size_t ci_extra,
                 const F &f)
      : coeff(l.original_n, f.zero()), target(f.zero()) {
    static const char tag[] = "relative-pack/linear-batch/v1";
    ts.write(reinterpret_cast<const uint8_t *>(tag), sizeof(tag));
    std::vector<E> alpha(nl);
    for (auto &x : alpha)
      x = ts.elt(f);
    for (size_t i = 0; i < nl; ++i)
      f.add(target, f.mulf(alpha[i], rhs[i]));
    for (const auto &term : ll)
      f.add(coeff.at(term.w), f.mulf(alpha.at(term.c), term.k));
    if (extra && extra->accumulate)
      extra->accumulate(coeff.data(), alpha.data(), ci_extra);
    const auto &b = ExtensionBasis<F>::get(f);
    for (size_t k = 0; k < D; ++k) {
      a[k].resize(l.words, f.zero());
      if constexpr (F::kCharacteristicTwo) {
        // Pull the inverse Frobenius outside the coordinate sum:
        // sum_i dual_i phi^-k(c_i) = phi^-k(sum_i phi^k(dual_i) c_i).
        // This applies one expensive binary linear map per packed word,
        // instead of one per coordinate. The authenticated forms are identical.
        std::array<E, D> twisted_dual;
        for (size_t i = 0; i < D; ++i)
          twisted_dual[i] = b.phi_public(b.dual[i], k, f);
        for (size_t y = 0; y < l.words; ++y) {
          typename F::Accum sum{};
          for (size_t i = 0; i < D && y * D + i < l.subfield_n; ++i)
            f.mac(sum, twisted_dual[i], coeff[y * D + i]);
          a[k][y] = b.phi_public(f.reduce(sum), D - k, f);
        }
      } else {
        for (size_t i = 0; i < l.subfield_n; ++i)
          f.add(a[k][i / D],
                b.mul_dual(i % D, b.phi_public(coeff[i], D - k, f), f));
      }
    }
  }
  void reveal(std::vector<E> &m, const ExtensionLayout<F> &l, const E *w,
              const F &f) const {
    const auto &b = ExtensionBasis<F>::get(f);
    m.assign(D, f.zero());
    for (size_t k = 0; k < D; ++k) {
      for (size_t y = 0; y < l.words; ++y)
        f.add(m[k], f.mulf(a[k][y], w[l.prefix + y]));
      for (size_t i = 0; i < D; ++i)
        f.add(m[k], f.mulf(b.beta[i], w[k * D + i]));
    }
  }
  std::vector<E> rhs(const std::vector<E> &m, const F &f) const {
    check(m.size() == D, "relative measurement count");
    const auto &b = ExtensionBasis<F>::get(f);
    auto out = m;
    E last = target;
    for (size_t k = 0; k < D; ++k)
      f.sub(last, b.phi_public(m[k], k, f));
    out.push_back(last);
    return out;
  }
  void accumulate(E *out, const E *alpha, const ExtensionLayout<F> &l,
                  const F &f) const {
    const auto &b = ExtensionBasis<F>::get(f);
    for (size_t k = 0; k < D; ++k) {
      for (size_t y = 0; y < l.words; ++y)
        f.add(out[l.prefix + y], f.mulf(alpha[k], a[k][y]));
      for (size_t i = 0; i < D; ++i) {
        f.add(out[k * D + i], f.mulf(alpha[k], b.beta[i]));
        f.sub(out[k * D + i], f.mulf(alpha[D], b.beta_phi[k][i]));
      }
    }
    for (size_t i = l.subfield_n; i < l.original_n; ++i)
      f.add(out[l.map(i)], f.mulf(alpha[D], coeff[i]));
  }
};
} // namespace proofs
#endif
