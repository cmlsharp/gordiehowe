// Copyright 2026 Chad Sharp and Paul Grubbs
// SPDX-License-Identifier: Apache-2.0

#ifndef PRIVACY_PROOFS_ZK_LIB_ZK_ZK_PACKED_H_
#define PRIVACY_PROOFS_ZK_LIB_ZK_ZK_PACKED_H_

#include <cstddef>
#include <cstdint>
#include <utility>
#include <vector>

#include "arrays/eqs.h"
#include "ligero/ligero_param.h"
#include "sumcheck/circuit.h"
#include "util/panic.h"

namespace proofs {

/*
Packed bits.

A circuit over a characteristic-two field F may declare ranges of private
input wires as packed bits (Circuit::packed_bits).  Each aligned group of
K = Field::kSubFieldBits wires 16Y+i, 0 <= i < K, is committed as the single
subfield element

    p_Y = SUM_i bit_{Y,i} * beta_i

where beta_i is the subfield basis behind of_scalar().  GKR still sees one
wire per bit; only the commitment changes.

Bit i of a subfield element p is Tr(beta*_i * p), where beta*_i is the trace
dual basis and Tr(x) = SUM_{k<K} x^(2^k) is the trace from the subfield E to
GF(2).  The identity needs p in E, which the Ligero verifier enforces on the
packed rows (LigeroVerifier::verify, SUBFIELD_WROWS).  Because Tr(x) lies in
{0,1} for x in E, packed bits are bits by construction, and the circuit does
not assert them.

GKR ends with the claim  SUM_x (eq(g0,x) + alpha*eq(g1,x)) * w_x  on the
input wires.  Split each packed index as x = K*Y + i, which splits the point
as g = (g_lo, g_hi) because Eqs maps index bit j to g[j].  Substituting the
trace for each bit, the packed part of the claim becomes

    SUM_k SUM_Y c_{k,Y} * p_Y^(2^k)
    c_{k,Y} = d_k(g0_lo) eq(g0_hi,Y) + alpha d_k(g1_lo) eq(g1_hi,Y)
    d_k(g_lo) = SUM_i eq(g_lo,i) * (beta*_i)^(2^k).

Frobenius is additive and invertible, so SUM_Y c_{k,Y} p_Y^(2^k) equals
z_k^(2^k) with z_k = SUM_Y a_{k,Y} p_Y and a_{k,Y} = c_{k,Y}^(2^-k).  Each
z_k is an F-linear form in the committed p.  Frobenius fixes the Boolean
hypercube, so eq(g_hi,Y)^(2^-k) = eq(g_hi^(2^-k), Y), and the verifier builds
the forms from eq tables over Frobenius-twisted points.

The prover reveals M_k = z_k + sigma_k for committed uniform pads sigma_k.
With pi_k = sigma_k^(2^k), Ligero checks
    SUM_Y a_{k,Y} p_Y + sigma_k = M_k                      (K linear)
    packed part of the claim = SUM_k (M_k^(2^k) + pi_k)    (in the input row)
    s_{k,j} = s_{k,j-1}^2, s_{k,0} = sigma_k, pi_k = s_{k,k} (quadratic).
The identity is exact; soundness adds nothing beyond Ligero's tests and the
subfield enforcement.

Committed layout, for circuit inputs [npub, ninputs):

    [packed p_Y | zeros | unpacked subfield inputs | full-field inputs |
     GKR pads | sigma_0..sigma_{K-1} | chain s_{k,j}, 1 <= j <= k < K]

The zeros pad the packed block so that every row holding a packed element is
a whole subfield row of the tableau; only whole subfield rows are enforced.
*/

// Frobenius x^(2^k), by k squarings.  K and 2^k are small, and the inverse
// x^(2^-k) = x^(2^(kBits-k)) is used only on O(log n) point coordinates.
template <class Field>
typename Field::Elt frobenius(typename Field::Elt x, size_t k, const Field& F) {
  for (size_t j = 0; j < k; ++j) {
    x = F.mulf(x, x);
  }
  return x;
}

template <class Field>
typename Field::Elt inverse_frobenius(const typename Field::Elt& x, size_t k,
                                      const Field& F) {
  return frobenius(x, (Field::kBits - (k % Field::kBits)) % Field::kBits, F);
}

// out[k] = x^(2^-k) for 0 <= k < n, from one chain of kBits squarings:
// x^(2^-(n-1)) = x^(2^(kBits-n+1)), then each lower k squares the next.
template <class Field>
void inverse_frobenius_powers(const typename Field::Elt& x, size_t n,
                              typename Field::Elt* out, const Field& F) {
  if (n == 0) return;
  out[0] = x;
  if (n == 1) return;
  typename Field::Elt y = inverse_frobenius(x, n - 1, F);
  for (size_t k = n - 1; k >= 1; --k) {
    out[k] = y;
    y = F.mulf(y, y);
  }
}

// The trace dual basis of the subfield basis beta_i, and its Frobenius powers
// dual_pow(k, i) = (beta*_i)^(2^k).
template <class Field>
class PackedBasis {
  using Elt = typename Field::Elt;

 public:
  static constexpr size_t kPack = Field::kSubFieldBits;

  explicit PackedBasis(const Field& F) : f_(F) {
    static_assert(Field::kCharacteristicTwo);
    static_assert(kPack <= 64);

    // T[i][j] = Tr(beta_i beta_j), in {0,1}.
    uint64_t T[kPack];
    for (size_t i = 0; i < kPack; ++i) {
      T[i] = 0;
      for (size_t j = 0; j < kPack; ++j) {
        Elt t = trace(F.mulf(F.beta(i), F.beta(j)));
        if (t == F.one()) {
          T[i] |= uint64_t(1) << j;
        } else {
          check(t == F.zero(), "trace of a subfield element outside GF(2)");
        }
      }
    }

    // Invert T over GF(2) by Gauss-Jordan on [T | I].
    uint64_t inv[kPack];
    for (size_t i = 0; i < kPack; ++i) {
      inv[i] = uint64_t(1) << i;
    }
    for (size_t c = 0; c < kPack; ++c) {
      size_t piv = c;
      while (piv < kPack && !((T[piv] >> c) & 1)) ++piv;
      check(piv < kPack, "trace form is degenerate");
      std::swap(T[c], T[piv]);
      std::swap(inv[c], inv[piv]);
      for (size_t r = 0; r < kPack; ++r) {
        if (r != c && ((T[r] >> c) & 1)) {
          T[r] ^= T[c];
          inv[r] ^= inv[c];
        }
      }
    }

    // T is symmetric, so beta*_i = SUM_j (T^-1)_{ij} beta_j satisfies
    // Tr(beta*_i beta_j) = delta_ij.
    dual_pow_.resize(kPack * kPack);
    for (size_t i = 0; i < kPack; ++i) {
      Elt d = F.zero();
      for (size_t j = 0; j < kPack; ++j) {
        if ((inv[i] >> j) & 1) {
          F.add(d, F.beta(j));
        }
      }
      for (size_t k = 0; k < kPack; ++k) {
        dual_pow_[k * kPack + i] = d;
        d = F.mulf(d, d);
      }
    }
  }

  Elt trace(const Elt& x) const {
    Elt t = F().zero();
    Elt y = x;
    for (size_t k = 0; k < kPack; ++k) {
      F().add(t, y);
      y = F().mulf(y, y);
    }
    return t;
  }

  const Elt& dual(size_t i) const { return dual_pow_[i]; }
  const Elt& dual_pow(size_t k, size_t i) const {
    return dual_pow_[k * kPack + i];
  }

  // Bit i of the subfield element p, as a field element 0 or 1.
  Elt bit(const Elt& p, size_t i) const { return trace(F().mulf(dual(i), p)); }

 private:
  const Field& F() const { return f_; }
  const Field& f_;
  std::vector<Elt> dual_pow_;  // [k][i]
};

// Where every circuit input lands in the committed witness.
template <class Field>
struct PackedLayout {
  static constexpr size_t kPack = Field::kSubFieldBits;
  static constexpr size_t kNone = ~size_t(0);
  static constexpr size_t kChain = kPack * (kPack - 1) / 2;

  size_t npub = 0;
  size_t ninputs = 0;
  std::vector<std::pair<size_t, size_t>> runs;  // [a, b) circuit inputs

  size_t npacked = 0;        // packed elements p_Y
  size_t nzero = 0;          // zeros after the packed block
  size_t boundary = 0;       // committed subfield boundary
  size_t n_witness = 0;      // committed inputs, before the GKR pads
  size_t subfield_wrows = 0; // tableau rows enforced to be subfield

  // committed index of circuit input i, or kNone if i is public or packed
  std::vector<size_t> map;
  // committed index of the packed group Y = i / kPack, or kNone
  std::vector<size_t> group;
  std::vector<size_t> alias_target; // absolute subfield input or kNone

  // committed indices of the pads, given the GKR pad size
  size_t sigma(size_t gkr_pad, size_t k) const {
    return n_witness + gkr_pad + k;
  }
  // s_{k,j} for 1 <= j <= k < kPack
  size_t chain(size_t gkr_pad, size_t k, size_t j) const {
    return n_witness + gkr_pad + kPack + k * (k - 1) / 2 + (j - 1);
  }
  size_t pi(size_t gkr_pad, size_t k) const {
    return k == 0 ? sigma(gkr_pad, 0) : chain(gkr_pad, k, k);
  }
  size_t committed_size(size_t gkr_pad) const {
    return n_witness + gkr_pad + kPack + kChain;
  }

  // W is the number of witnesses per tableau row, or 0 to lay out without
  // the row alignment (used only to size the parameter search).
  PackedLayout(const Circuit<Field>& c, size_t w) {
    npub = c.npub_in;
    ninputs = c.ninputs;
    runs = c.packed_bits;
    check(!runs.empty(), "PackedLayout without packed bits");
    check(c.subfield_boundary >= npub && c.subfield_boundary <= ninputs,
          "packed bits need a subfield boundary");

    map.assign(ninputs, kNone);
    group.assign(ceildiv(ninputs, kPack), kNone);

    alias_target.assign(group.size(),kNone);
    for(auto a:c.packed_input_aliases) {
      check(a.first%kPack==0 && a.first>=npub && a.first+kPack<=c.subfield_boundary,"unaligned alias");
      check(a.second>=npub && a.second<c.subfield_boundary && !packed(a.second),"alias target must be unpacked subfield input");
      check(packed(a.first) && packed(a.first+kPack-1),"alias source must be a packed group");
      check(alias_target.at(a.first/kPack)==kNone,"duplicate alias source");
      alias_target[a.first/kPack]=a.second;
    }
    size_t prev = npub;
    for (const auto& r : runs) {
      check(r.first % kPack == 0 && r.second % kPack == 0,
            "packed run not aligned");
      check(r.first >= prev && r.first < r.second,
            "packed runs must be ordered and disjoint");
      check(r.second <= c.subfield_boundary,
            "packed run outside the subfield inputs");
      for (size_t Y = r.first / kPack; Y < r.second / kPack; ++Y) {
        if(alias_target[Y]==kNone)group[Y] = npacked++;
      }
      prev = r.second;
    }

    if (w > 0) {
      size_t need = ceildiv(npacked, w) * w;
      size_t nsub = 0;
      for (size_t i = npub; i < c.subfield_boundary; ++i) {
        if (!packed(i)) ++nsub;
      }
      if(!c.packed_input_aliases.empty())need=ceildiv(npacked+nsub,w)*w;
      if (npacked + nsub < need) {
        nzero = need - (npacked + nsub);
      }
    }

    size_t ci = npacked + nzero;
    for (size_t i = npub; i < c.subfield_boundary; ++i) {
      if (!packed(i)) map[i] = ci++;
    }
    boundary = ci;
    for (size_t i = c.subfield_boundary; i < ninputs; ++i) {
      map[i] = ci++;
    }
    for(size_t y=0;y<group.size();++y)if(alias_target[y]!=kNone) {
      group[y]=map.at(alias_target[y]);
      check(group[y]!=kNone && group[y]<boundary,"invalid mapped alias");
    }
    n_witness = ci;
    subfield_wrows = (w > 0) ? boundary / w : 0;
    check(w == 0 || subfield_wrows * w >= npacked,
          "packed rows are not whole subfield rows");
  }

  bool packed(size_t i) const {
    for (const auto& r : runs) {
      if (i >= r.first && i < r.second) return true;
    }
    return false;
  }

 private:
  static size_t ceildiv(size_t a, size_t b) { return (a + b - 1) / b; }
};

// The K linear forms a_k over the packed groups, for one GKR input claim.
template <class Field>
class PackedForms {
  using Elt = typename Field::Elt;

 public:
  static constexpr size_t kPack = Field::kSubFieldBits;
  static constexpr size_t kLogPack = Field::kSubFieldLogBits;

  // a(k)[Y] = a_{k,Y} for 0 <= Y < ngroups.
  PackedForms(const PackedBasis<Field>& basis, size_t logv, size_t ngroups,
              const Elt* g0, const Elt* g1, const Elt& alpha, const Field& F)
      : ngroups_(ngroups), a_(kPack) {
    check(logv >= kLogPack, "input layer too small to pack");
    const size_t loghi = logv - kLogPack;

    Eqs<Field> e0lo(kLogPack, kPack, g0, F);
    Eqs<Field> e1lo(kLogPack, kPack, g1, F);

    std::vector<Elt> h0(loghi), h1(loghi);
    // tw[(2j + b) * kPack + k] = g_b[kLogPack + j]^(2^-k)
    std::vector<Elt> tw(2 * loghi * kPack);
    for (size_t j = 0; j < loghi; ++j) {
      inverse_frobenius_powers(g0[kLogPack + j], kPack, &tw[(2 * j) * kPack], F);
      inverse_frobenius_powers(g1[kLogPack + j], kPack,
                               &tw[(2 * j + 1) * kPack], F);
    }
    for (size_t k = 0; k < kPack; ++k) {
      // d_k for each claim, alpha folded into the second
      Elt d0 = F.zero(), d1 = F.zero();
      for (size_t i = 0; i < kPack; ++i) {
        F.add(d0, F.mulf(e0lo.at(i), basis.dual_pow(k, i)));
        F.add(d1, F.mulf(e1lo.at(i), basis.dual_pow(k, i)));
      }
      F.mul(d1, alpha);
      const Elt D0 = inverse_frobenius(d0, k, F);
      const Elt D1 = inverse_frobenius(d1, k, F);

      for (size_t j = 0; j < loghi; ++j) {
        h0[j] = tw[(2 * j) * kPack + k];
        h1[j] = tw[(2 * j + 1) * kPack + k];
      }
      Eqs<Field> e0(loghi, ngroups, h0.data(), F);
      Eqs<Field> e1(loghi, ngroups, h1.data(), F);

      a_[k].resize(ngroups);
      for (size_t Y = 0; Y < ngroups; ++Y) {
        a_[k][Y] = F.addf(F.mulf(e0.at(Y), D0), F.mulf(e1.at(Y), D1));
      }
    }
  }

  const std::vector<Elt>& a(size_t k) const { return a_[k]; }

  // z_k = SUM_Y a_{k,Y} p_Y, with p_Y read through the layout's group map.
  Elt z(size_t k, const PackedLayout<Field>& layout, const Elt* committed,
        const Field& F) const {
    Elt s = F.zero();
    for (size_t Y = 0; Y < ngroups_ && Y < layout.group.size(); ++Y) {
      if (layout.group[Y] != PackedLayout<Field>::kNone) {
        F.add(s, F.mulf(a_[k][Y], committed[layout.group[Y]]));
      }
    }
    return s;
  }

 private:
  size_t ngroups_;
  std::vector<std::vector<Elt>> a_;
};

}  // namespace proofs

#endif  // PRIVACY_PROOFS_ZK_LIB_ZK_ZK_PACKED_H_
