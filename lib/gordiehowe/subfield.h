// Copyright 2026 Chad Sharp and Paul Grubbs
// SPDX-License-Identifier: Apache-2.0

// GordieHowe: the subfields of a domain's field.
//
// A domain over K may declare values in several subfields S of K
// (Subfield<GF<d>>, core.h), each named by its degree d over the prime
// field. domain_subfield<F> is the designated subfield, F's own: GF(2^16)
// (Field::kSubFieldBits) in characteristic 2 and the prime field otherwise,
// with ExtensionTraits<F> for relative packing. It is the subfield Ligero
// commits subfield rows in, so every membership test of a packing stage runs
// in it (packing.h). SubfieldInfo<F> is any subfield, by degree: a basis over
// the prime field, membership (x^(p^d) = x), its codec and sampler. The
// packing tree (packing.h) reads both.

#ifndef PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_SUBFIELD_H_
#define PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_SUBFIELD_H_

#include <array>
#include <cstddef>
#include <cstdint>
#include <map>
#include <memory>
#include <mutex>
#include <optional>
#include <string>
#include <vector>

#include "gordiehowe/ct.h"
#include "random/random.h"
#include "util/panic.h"
#include "zk/zk_extension_packed.h"

namespace proofs::gordiehowe {

// [K : prime field].
template <class F>
constexpr size_t field_degree() {
  if constexpr (F::kCharacteristicTwo) {
    return F::kBits;
  } else {
    return ExtensionTraits<F>::supported ? ExtensionTraits<F>::degree : 1;
  }
}
// The designated subfield's degree over the prime field.
template <class F>
constexpr size_t designated_degree() {
  if constexpr (F::kCharacteristicTwo) {
    return F::kSubFieldBits;
  } else {
    return 1;
  }
}
// A declared degree as a domain stores it: the designated degree is 0.
template <class F>
uint16_t normalize_degree(size_t d) {
  return d == designated_degree<F>() ? 0 : static_cast<uint16_t>(d);
}
// The degree a stored one names.
template <class F>
size_t subfield_degree(size_t stored) {
  return stored == 0 ? designated_degree<F>() : stored;
}

// x^(p^e), the e-th power of the absolute Frobenius: in characteristic 2
// through ExtensionBasis's tables for the multiples of 16 and squarings for
// the rest, otherwise through the relative Frobenius x^q (q = p).
template <class F>
typename F::Elt frobenius_power(const F &f, typename F::Elt x, size_t e) {
  e %= field_degree<F>();
  if constexpr (F::kCharacteristicTwo) {
    if constexpr (ExtensionTraits<F>::supported) {
      static_assert(ExtensionTraits<F>::q == 65536, "GF(2^16) relative field");
      if (e >= 16) x = ExtensionBasis<F>::get(f).phi_public(x, e / 16, f);
      e %= 16;
    }
    for (size_t i = 0; i < e; ++i) x = f.mulf(x, x);
    return x;
  } else if constexpr (!ExtensionTraits<F>::supported) {
    // An odd field without relative packing is prime (field_degree 1): the
    // Frobenius is the identity.
    return x;
  } else {
    return ExtensionBasis<F>::get(f).phi_public(x, e, f);
  }
}

// frobenius_power for witness values: in characteristic 2, E squarings,
// where frobenius_power's multiples of 16 read ExtensionBasis's nibble
// tables at addresses that depend on X (ct.h). The odd paths index by the
// power alone.
template <class F>
typename F::Elt frobenius_power_ct(const F &f, typename F::Elt x, size_t e) {
  e %= field_degree<F>();
  if constexpr (F::kCharacteristicTwo) {
    for (size_t i = 0; i < e; ++i) x = f.mulf(x, x);
    return x;
  } else {
    return frobenius_power(f, x, e);
  }
}

// The designated subfield, statically.
template <class F>
struct domain_subfield {
  using Elt = typename F::Elt;
  // Bits and serialized bytes of a subfield element.
  static constexpr size_t kBits = F::kSubFieldBits;
  static constexpr size_t kBytes = F::kSubFieldBytes;
  // Degree over the prime field.
  static constexpr size_t kDegree = designated_degree<F>();
  // Subfield coordinates of a field element.
  static constexpr size_t kCoordinates = F::kBytes / F::kSubFieldBytes;
  // Relative packing (ExtensionTraits) and its degree [K : S].
  static constexpr bool kRelativePacking = ExtensionTraits<F>::supported;
  static constexpr size_t kRelativeDegree = ExtensionTraits<F>::degree;
  // Bits are words of sixteen: characteristic 2 with a GF(2^16) subfield
  // (bit views, bit-packed batches, the selection's samples).
  static constexpr bool kBitWords = F::kCharacteristicTwo && kBits == 16;
  // Bits pack sixteen to a committed word.
  static constexpr bool kBitPacking = kRelativePacking && kBitWords;

  static bool contains(const F &f, const Elt &x) { return f.in_subfield(x); }
  static Elt sample(const F &f, RandomEngine &rng) {
    return rng.subfield_elt(f);
  }
  static void to_bytes(const F &f, uint8_t *out, const Elt &x) {
    f.to_bytes_subfield(out, x);
  }
  static std::optional<Elt> of_bytes(const F &f, const uint8_t *in) {
    return f.of_bytes_subfield(in);
  }
};

template <class F>
bool subfield_contains(const F &f, const typename F::Elt &x) {
  return domain_subfield<F>::contains(f, x);
}
template <class F>
typename F::Elt subfield_sample(const F &f, RandomEngine &rng) {
  return domain_subfield<F>::sample(f, rng);
}
template <class F>
void subfield_to_bytes(const F &f, uint8_t *out, const typename F::Elt &x) {
  domain_subfield<F>::to_bytes(f, out, x);
}
template <class F>
std::optional<typename F::Elt> subfield_of_bytes(const F &f,
                                                  const uint8_t *in) {
  return domain_subfield<F>::of_bytes(f, in);
}

// The subfield of degree D (over the prime field) of F, at run time.
// D = designated_degree<F>() is domain_subfield<F> with the basis F.beta
// in characteristic 2 (of_scalar's) and {1} in odd characteristic. Another
// D needs relative packing (ExtensionTraits, for the Frobenius) and D | [K :
// prime]; in characteristic 2, D <= 64. Its basis is chosen from the images
// of K's coordinate basis under the trace K -> S, and fixed: a description
// that names the subfield names this basis.
template <class F>
class SubfieldInfo {
 public:
  using Elt = typename F::Elt;
  size_t degree = 0;    // over the prime field
  size_t bytes = 0;     // codec width
  bool designated = false;
  std::vector<Elt> basis;  // over the prime field, degree elements

  // D = 0 names the designated subfield.
  static const SubfieldInfo &get(const F &f, size_t d) {
    static std::mutex mu;
    static std::map<size_t, std::unique_ptr<SubfieldInfo>> cache;
    if (d == 0) d = designated_degree<F>();
    std::lock_guard<std::mutex> lock(mu);
    auto &p = cache[d];
    if (!p) p.reset(new SubfieldInfo(f, d));
    return *p;
  }
  // Why F has no subfield of degree D, or "".
  static std::string unsupported(size_t d) {
    if (d == 0 || d == designated_degree<F>()) return "";
    if (!ExtensionTraits<F>::supported)
      return "the field has no relative packing, so only its designated "
             "subfield is available";
    if (field_degree<F>() % d != 0)
      return "degree " + std::to_string(d) + " does not divide the field's " +
             std::to_string(field_degree<F>());
    if (F::kCharacteristicTwo && d > 64)
      return "binary subfields above degree 64 are not supported";
    return "";
  }

  bool contains(const F &f, const Elt &x) const {
    if (designated) return f.in_subfield(x);
    return frobenius_power(f, x, degree) == x;
  }
  // Membership as a bit, without a branch on X (the prover's check on
  // witness values): in characteristic 2, X re-encoded from its decoded
  // coordinates is X exactly when X lies in the subfield.
  uint64_t contains_bit(const F &f, const Elt &x) const {
    if constexpr (F::kCharacteristicTwo) {
      return ct::equal(word(f, bits(f, x)), x);
    } else {
      if (designated) return uint64_t(f.in_subfield(x));
      return ct::equal(frobenius_power(f, x, degree), x);
    }
  }
  // Prime-field coordinates over the basis, as elements of K.
  std::vector<Elt> coordinates(const F &f, const Elt &x) const {
    std::vector<Elt> c(degree, f.zero());
    if constexpr (F::kCharacteristicTwo) {
      const uint64_t u = bits(f, x);
      for (size_t i = 0; i < degree; ++i) c[i] = ct::bit_elt(f, u >> i);
    } else {
      if (designated) {
        c[0] = x;
      } else {
        const auto &b = ExtensionBasis<F>::get(f);
        std::vector<Elt> v(pivot_.size());
        for (size_t i = 0; i < pivot_.size(); ++i)
          v[i] = ExtensionBasis<F>::trace(f.mulf(b.dual[pivot_[i]], x), f);
        for (size_t j = 0; j < degree; ++j)
          for (size_t i = 0; i < degree; ++i)
            f.add(c[j], f.mulf(v[i], inv_[i * degree + j]));
      }
    }
    return c;
  }
  // Characteristic 2: the coordinate bits of a subfield element (bit i is
  // the coefficient of basis[i]), and the element of bits U.
  uint64_t bits(const F &f, const Elt &x) const {
    static_assert(F::kCharacteristicTwo, "bits of a binary subfield");
    std::array<uint8_t, F::kBytes> b;
    f.to_bytes_field(b.data(), x);
    uint64_t g = 0;
    for (size_t i = 0; i < degree; ++i)
      g |= uint64_t((b[pivot_[i] / 8] >> (pivot_[i] % 8)) & 1) << i;
    uint64_t u = 0;
    for (size_t i = 0; i < degree; ++i) u ^= rows_[i] & ct::mask(g >> i);
    return u;
  }
  Elt word(const F &f, uint64_t u) const {
    Elt x = f.zero();
    for (size_t i = 0; i < degree; ++i)
      f.add(x, ct::select(ct::mask(u >> i), basis[i], f.zero()));
    return x;
  }
  Elt sample(const F &f, RandomEngine &rng) const {
    if (designated) return rng.subfield_elt(f);
    if constexpr (F::kCharacteristicTwo) {
      uint8_t b[8] = {0};
      rng.bytes(b, (degree + 7) / 8);
      uint64_t u = 0;
      for (size_t i = 0; i < 8; ++i) u |= uint64_t(b[i]) << (8 * i);
      if (degree < 64) u &= (uint64_t(1) << degree) - 1;
      return word(f, u);
    } else {
      Elt x = f.zero();
      for (size_t i = 0; i < degree; ++i)
        f.add(x, f.mulf(rng.subfield_elt(f), basis[i]));
      return x;
    }
  }
  void to_bytes(const F &f, uint8_t *out, const Elt &x) const {
    if (designated) return f.to_bytes_subfield(out, x);
    if constexpr (F::kCharacteristicTwo) {
      const uint64_t u = bits(f, x);
      for (size_t i = 0; i < bytes; ++i) out[i] = uint8_t(u >> (8 * i));
    } else {
      const auto c = coordinates(f, x);
      for (size_t i = 0; i < degree; ++i)
        f.to_bytes_subfield(out + i * F::kSubFieldBytes, c[i]);
    }
  }
  std::optional<Elt> of_bytes(const F &f, const uint8_t *in) const {
    if (designated) return f.of_bytes_subfield(in);
    if constexpr (F::kCharacteristicTwo) {
      uint64_t u = 0;
      for (size_t i = 0; i < bytes; ++i) u |= uint64_t(in[i]) << (8 * i);
      return word(f, u);
    } else {
      Elt x = f.zero();
      for (size_t i = 0; i < degree; ++i) {
        auto c = f.of_bytes_subfield(in + i * F::kSubFieldBytes);
        if (!c) return std::nullopt;
        f.add(x, f.mulf(*c, basis[i]));
      }
      return x;
    }
  }

 private:
  SubfieldInfo(const F &f, size_t d) : degree(d) {
    const std::string why = unsupported(d);
    if (!why.empty()) fail_("subfield of degree " + std::to_string(d) + ": " + why);
    designated = d == designated_degree<F>();
    if constexpr (F::kCharacteristicTwo) {
      bytes = (d + 7) / 8;
      if (designated) {
        for (size_t i = 0; i < d; ++i) basis.push_back(f.beta(i));
      } else {
        // Trace images of the unit coordinate vectors, kept when independent
        // over GF(2).
        std::vector<std::array<uint8_t, F::kBytes>> red;
        for (size_t j = 0; j < F::kBits && basis.size() < d; ++j) {
          std::array<uint8_t, F::kBytes> raw{};
          raw[j / 8] = uint8_t(1u << (j % 8));
          const Elt y = *f.of_bytes_field(raw.data());
          Elt t = f.zero();
          for (size_t i = 0; i < F::kBits / d; ++i)
            f.add(t, frobenius_power(f, y, d * i));
          std::array<uint8_t, F::kBytes> v;
          f.to_bytes_field(v.data(), t);
          if (reduce(red, v)) basis.push_back(t);
        }
        check(basis.size() == d, "subfield basis");
      }
      decoder(f);
    } else {
      bytes = d * F::kSubFieldBytes;
      if (designated) {
        basis.push_back(f.one());
      } else {
        const auto &b = ExtensionBasis<F>::get(f);
        constexpr size_t D = ExtensionTraits<F>::degree;
        // Rows: E-coordinates of the chosen basis elements, reduced.
        std::vector<std::vector<Elt>> red;
        std::vector<std::vector<Elt>> coords;
        for (size_t j = 0; j < D && basis.size() < d; ++j) {
          Elt t = f.zero();
          for (size_t i = 0; i < D / d; ++i)
            f.add(t, frobenius_power(f, b.beta[j], d * i));
          std::vector<Elt> v(D);
          for (size_t i = 0; i < D; ++i)
            v[i] = ExtensionBasis<F>::trace(f.mulf(b.dual[i], t), f);
          std::vector<Elt> w = v;
          bool independent = true;
          for (const auto &r : red) {
            size_t p = 0;
            while (r[p] == f.zero()) ++p;
            const Elt c = f.mulf(w[p], f.invertf(r[p]));
            for (size_t i = 0; i < D; ++i) f.sub(w[i], f.mulf(c, r[i]));
          }
          independent = false;
          for (const auto &x : w)
            if (x != f.zero()) independent = true;
          if (!independent) continue;
          red.push_back(w);
          coords.push_back(v);
          basis.push_back(t);
        }
        check(basis.size() == d, "subfield basis");
        // Pivot coordinates: a column set where the coordinate matrix is
        // invertible, and its inverse.
        for (size_t i = 0; i < d; ++i) {
          size_t p = 0;
          while (red[i][p] == f.zero()) ++p;
          pivot_.push_back(p);
        }
        // M[j][i] = coords[j][pivot_i]; c = v M^-1 with v the pivot
        // coordinates of x = sum_j c_j basis_j: v_i = sum_j c_j M[j][i].
        std::vector<Elt> m(d * 2 * d, f.zero());
        for (size_t i = 0; i < d; ++i) {
          for (size_t j = 0; j < d; ++j) m[i * 2 * d + j] = coords[j][pivot_[i]];
          m[i * 2 * d + d + i] = f.one();
        }
        // Rows i of [A | I] with A[i][j] = M[j][i]; invert A.
        for (size_t c = 0; c < d; ++c) {
          size_t r = c;
          while (r < d && m[r * 2 * d + c] == f.zero()) ++r;
          check(r < d, "subfield coordinate matrix");
          for (size_t k = 0; k < 2 * d; ++k)
            std::swap(m[r * 2 * d + k], m[c * 2 * d + k]);
          const Elt inv = f.invertf(m[c * 2 * d + c]);
          for (size_t k = 0; k < 2 * d; ++k) f.mul(m[c * 2 * d + k], inv);
          for (size_t r2 = 0; r2 < d; ++r2)
            if (r2 != c) {
              const Elt a = m[r2 * 2 * d + c];
              for (size_t k = 0; k < 2 * d; ++k)
                f.sub(m[r2 * 2 * d + k], f.mulf(a, m[c * 2 * d + k]));
            }
        }
        // A^-1 = (M^T)^-1; c_j = sum_i (A^-1)[j][i] v_i, stored as
        // inv_[i * d + j].
        inv_.assign(d * d, f.zero());
        for (size_t j = 0; j < d; ++j)
          for (size_t i = 0; i < d; ++i) inv_[i * d + j] = m[j * 2 * d + d + i];
      }
    }
  }
  static void fail_(const std::string &m) { check(false, m.c_str()); }
  // Gaussian reduction of V against RED; appends and returns true when V is
  // independent.
  static bool reduce(std::vector<std::array<uint8_t, F::kBytes>> &red,
                     std::array<uint8_t, F::kBytes> v) {
    for (const auto &r : red) {
      size_t p = 0;
      while (!((r[p / 8] >> (p % 8)) & 1)) ++p;
      if ((v[p / 8] >> (p % 8)) & 1)
        for (size_t i = 0; i < v.size(); ++i) v[i] ^= r[i];
    }
    for (uint8_t x : v)
      if (x) {
        red.push_back(v);
        return true;
      }
    return false;
  }
  // Characteristic 2: pivot bits of the basis and the inverse of its pivot
  // matrix, so that bits(x) reads `degree` bits of x.
  void decoder(const F &f) {
    const size_t d = degree;
    std::vector<std::array<uint8_t, F::kBytes>> rows(d), red;
    for (size_t k = 0; k < d; ++k) f.to_bytes_field(rows[k].data(), basis[k]);
    red = rows;
    pivot_.assign(d, 0);
    for (size_t k = 0; k < d; ++k) {
      size_t b = 0;
      while (b < 8 * F::kBytes && !((red[k][b / 8] >> (b % 8)) & 1)) ++b;
      check(b < 8 * F::kBytes, "subfield basis is dependent");
      pivot_[k] = b;
      for (size_t j = k + 1; j < d; ++j)
        if ((red[j][b / 8] >> (b % 8)) & 1)
          for (size_t i = 0; i < red[j].size(); ++i) red[j][i] ^= red[k][i];
    }
    // A[k] = pivot bits of basis k; g = u A, so u = g A^-1.
    std::vector<uint64_t> a(d), inv(d);
    for (size_t k = 0; k < d; ++k) {
      for (size_t i = 0; i < d; ++i)
        if ((rows[k][pivot_[i] / 8] >> (pivot_[i] % 8)) & 1)
          a[k] |= uint64_t(1) << i;
      inv[k] = uint64_t(1) << k;
    }
    for (size_t c = 0; c < d; ++c) {
      size_t r = c;
      while (r < d && !((a[r] >> c) & 1)) ++r;
      check(r < d, "pivot bits of the subfield basis are singular");
      std::swap(a[r], a[c]);
      std::swap(inv[r], inv[c]);
      for (size_t j = 0; j < d; ++j)
        if (j != c && ((a[j] >> c) & 1)) {
          a[j] ^= a[c];
          inv[j] ^= inv[c];
        }
    }
    rows_ = inv;  // u = XOR over set bits i of g of row i of A^-1
  }

  std::vector<size_t> pivot_;
  std::vector<uint64_t> rows_;
  std::vector<Elt> inv_;
};

}  // namespace proofs::gordiehowe

#endif  // PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_SUBFIELD_H_
