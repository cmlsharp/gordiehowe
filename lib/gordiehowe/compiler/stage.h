// Copyright 2026 Chad Sharp and Paul Grubbs
// SPDX-License-Identifier: Apache-2.0

// GordieHowe: one packing stage B ⊂ T of a domain's field K
// (the formalization's
// PackedClaim and RelativePacking).
//
// A T-value p holds d = [T:B] coordinates over B in a fixed basis beta_j of
// T/B: p = sum_j beta_j x_j and x_j = Tr_{T/B}(beta*_j p), where beta*_j is
// the trace-dual basis and Tr_{T/B}(y) = sum_{k<d} phi^k(y) for the
// Frobenius phi(y) = y^|B| of K. A claim sum_{g,j} c_{g,j} x_{g,j} with
// coefficients in K on the B-coordinates of T-values p_g is
//
//     sum_k phi^k(z_k),   z_k = sum_g a_{k,g} p_g,
//     a_{k,g} = phi^-k( sum_j phi^k(beta*_j) c_{g,j} ),
//
// since phi is a field automorphism; phi^k(y) is the k-th Frobenius twist of
// y (Hashcaster). This reduction of a claim on B-coordinates to d forms on
// the T-values is ring switching (Diamond-Posen, ePrint 2024/504, section
// 1.2) in its Frobenius-twist form. The prover reveals M_k = z_k + sigma_k
// for masks sigma_k uniform in K, and the claim becomes
//
//     sum_g a_{k,g} p_g + sigma_k = M_k                     (d rows)
//     rest + sum_k phi^k(sigma_k) = rhs - sum_k phi^k(M_k)  (the claim)
//
// in characteristic 2, and with -phi^k(sigma_k) otherwise. The mode says how
// the masks' twists phi^k(sigma_k) are functions of committed values (both
// names are descriptive coinages):
//   squaring-chain masks
//           B = GF(2^b) in characteristic 2, phi = x^(2^b) the b-th
//           power of the squaring: sigma_k and its squaring chain
//           s_{k,j} = sigma_k^(2^j), 1 <= j <= b k, are committed in K,
//           with b d(d-1)/2 quadratic constraints, and
//           phi^k(sigma_k) = s_{k,bk}. For B = GF(2) (b = 1) this is
//           zk_packed.h's stage. The planner uses it for GF(2) and for
//           every base the prefix-row test does not cover (tree.h);
//   subfield masks
//           sigma_k = sum_i gamma_i s_{k,i} with gamma_i the basis of K over
//           the domain's designated subfield S0 (ExtensionBasis) and s_{k,i}
//           in S0, committed in the prefix rows; when S0 ⊆ B, phi fixes
//           S0, so phi^k(sigma_k) = sum_i phi^k(gamma_i) s_{k,i} is linear
//           (zk_extension_packed.h). The prefix-row test in S0 covers every
//           subfield-masks stage.
// For T = K and B = S0 this is zk_extension_packed.h's stage (ExtensionBasis
// and its D^2 masks), and for B = GF(2), T = GF(2^16) zk_packed.h's bit
// stage; the bases and masks are theirs, so the proofs are too.

#ifndef PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_COMPILER_STAGE_H_
#define PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_COMPILER_STAGE_H_

#include <algorithm>
#include <cstddef>
#include <array>
#include <cstdint>
#include <string>
#include <type_traits>
#include <utility>
#include <vector>

#include "arrays/eqs.h"
#include "gordiehowe/compiler/bit_planes.h"
#include "gordiehowe/compiler/test_switches.h"
#include "gordiehowe/subfield.h"
#include "util/panic.h"
#include "util/parallel.h"
#include "zk/zk_extension_packed.h"

namespace proofs::gordiehowe::compiler {

enum class StageMode : uint8_t { kSquaringChain = 0, kSubfieldMasks = 1 };

// Whether F multiplies an element by a prime-field scalar, its Elt's
// first coordinate (the native extension fields).
template <class F, class = void>
struct has_scalar_mul : std::false_type {};
template <class F>
struct has_scalar_mul<
    F, std::void_t<decltype(std::declval<const F &>().mulf(
           std::declval<typename F::Elt>(),
           std::declval<typename F::Elt>().e[0]))>> : std::true_type {};

template <class F>
class PackingStage {
 public:
  using Elt = typename F::Elt;
  size_t b = 0, t = 0, d = 0;  // degrees of B and T over the prime field
  StageMode mode = StageMode::kSubfieldMasks;
  bool root = false;           // T = K
  bool legacy_root = false;    // T = K, B = S0: ExtensionBasis's stage
  std::vector<Elt> beta, dual;       // T over B
  std::vector<Elt> twisted_dual;     // [k * d + j] = phi^k(beta*_j)
  size_t m = 0;                      // subfield masks: [K : S0]
  std::vector<Elt> gamma;            // subfield masks: K over S0
  std::vector<Elt> gamma_phi;        // subfield masks: [k * m + i] = phi^k(gamma_i)

  PackingStage() = default;
  PackingStage(const F &f, size_t base, size_t top)
      : b(base), t(top), d(top / base) {
    check(top % base == 0 && d >= 2, "packing stage degrees");
    root = top == field_degree<F>();
    mode = (F::kCharacteristicTwo &&
            (base == 1 || base % designated_degree<F>() != 0))
               ? StageMode::kSquaringChain
               : StageMode::kSubfieldMasks;
    if (mode == StageMode::kSquaringChain && base == 1) {
      bit_basis(f);
    } else if (mode == StageMode::kSquaringChain) {
      power_basis(f);
    } else {
      check(base % designated_degree<F>() == 0,
            "a subfield-masks stage's base contains the designated subfield");
      const auto &eb = ExtensionBasis<F>::get(f);
      m = ExtensionTraits<F>::degree;
      gamma.assign(eb.beta.begin(), eb.beta.end());
      legacy_root = root && base == designated_degree<F>();
      if (legacy_root) {
        beta.assign(eb.beta.begin(), eb.beta.end());
        dual.assign(eb.dual.begin(), eb.dual.end());
      } else {
        power_basis(f);
      }
      gamma_phi.resize(d * m);
      for (size_t k = 0; k < d; ++k)
        for (size_t i = 0; i < m; ++i)
          gamma_phi[k * m + i] =
              legacy_root ? eb.beta_phi[k][i] : phi(f, gamma[i], k);
    }
    twisted_dual.resize(d * d);
    for (size_t k = 0; k < d; ++k)
      for (size_t j = 0; j < d; ++j) twisted_dual[k * d + j] = phi(f, dual[j], k);
    twist_tables(f);
  }

  bool squaring_chain() const { return mode == StageMode::kSquaringChain; }
  // The Frobenius twists phi^k and phi^-k on K.
  Elt phi(const F &f, const Elt &x, size_t k) const {
    return frobenius_power(f, x, b * k);
  }
  Elt phi_inv(const F &f, const Elt &x, size_t k) const {
    const size_t n = field_degree<F>();
    return frobenius_power(f, x, (n - (b * k) % n) % n);
  }
  // phi^-k of a public X: from the stage's byte tables when it has them
  // (GF(2^128) and GF(2^256), the twist optimization; a root stage's are
  // its linear maps'), else phi_inv; the same value, since phi^-k is
  // GF(2)-linear.
  Elt phi_inv_public(const F &f, const Elt &x, size_t k) const {
    if constexpr (kTwistTables) {
      if (k % d != 0 && !inv_map_.empty() &&
          test_switches().stage_opt_on(StageOpt::kTwist)) {
        Elt out;
        inv_map_[k % d - 1].apply(&x, &out, 1);
        return out;
      }
      if (k % d != 0 && !inv_tab_.empty() &&
          test_switches().stage_opt_on(StageOpt::kTwist)) {
        uint8_t raw[F::kBytes];
        f.to_bytes_field(raw, x);
        const Elt *t = &inv_tab_[(k % d - 1) * F::kBytes * 256];
        Elt out = f.zero();
        for (size_t i = 0; i < F::kBytes; ++i, t += 256) f.add(out, t[raw[i]]);
        return out;
      }
    }
    return phi_inv(f, x, k);
  }

  // Committed mask cells: squaring-chain masks, in K (sigma_k, then
  // s_{k,j}); subfield masks, in the prefix (d * m coordinates in S0).
  size_t mask_cells() const {
    return squaring_chain() ? d + chain_cells() : d * m;
  }
  size_t chain_cells() const {
    return squaring_chain() ? b * d * (d - 1) / 2 : 0;
  }
  // The squarings of sigma_k's chain: phi^k = x^(2^(b k)).
  size_t squarings(size_t k) const { return b * k; }
  // Offsets of sigma_k, s_{k,j} (1 <= j <= squarings(k)) and its twist
  // phi^k(sigma_k) (squaring-chain masks) among the mask cells.
  size_t sigma(size_t k) const { return k; }
  size_t chain_cell(size_t k, size_t j) const {
    return d + b * k * (k - 1) / 2 + (j - 1);
  }
  size_t twist(size_t k) const {
    return k == 0 ? sigma(0) : chain_cell(k, squarings(k));
  }

  // The forms a_k (k < d) over N groups from coefficients C on their
  // B-coordinates (c[g * d + j]; a short last group is zero-padded): adds
  // into a[k * ng + g].
  void add_forms(const F &f, const Elt *c, size_t ncoord, size_t ng,
                 std::vector<Elt> &a) const {
    a.resize(d * ng, f.zero());
    if (!F::kCharacteristicTwo && legacy_root) {
      // zk_extension_packed.h's odd path: dual multiplication through the
      // native basis maps.
      const auto &eb = ExtensionBasis<F>::get(f);
      for (size_t k = 0; k < d; ++k)
        for (size_t i = 0; i < ncoord; ++i) {
          if (c[i] == f.zero()) continue;
          f.add(a[k * ng + i / d],
                eb.mul_dual(i % d, eb.phi_public(c[i], d - k, f), f));
        }
      return;
    }
    // A root stage's twists by its linear maps, a chunk of groups at a time
    // per k: the sums first, then phi^-k on all of them (inv_map_).
    if (!inv_map_.empty() && test_switches().stage_opt_on(StageOpt::kTwist)) {
      parallel::for_chunks(
          ng, parallel::grain_for(ng, parallel::kChunks),
          [&](size_t g0, size_t g1) {
            std::vector<Elt> x(g1 - g0);
            for (size_t k = 0; k < d; ++k) {
              for (size_t g = g0; g < g1; ++g) {
                typename F::Accum sum{};
                for (size_t j = 0; j < d && g * d + j < ncoord; ++j)
                  f.mac(sum, twisted_dual[k * d + j], c[g * d + j]);
                x[g - g0] = f.reduce(sum);
              }
              if (k != 0) inv_map_[k - 1].apply(x.data(), x.data(), g1 - g0);
              for (size_t g = g0; g < g1; ++g) f.add(a[k * ng + g], x[g - g0]);
            }
          });
      return;
    }
    // Each (k, g) adds into its own a[k * ng + g]: under a runner
    // (util/parallel.h) the groups run in chunks.
    parallel::for_chunks(
        ng, parallel::grain_for(ng, parallel::kChunks),
        [&](size_t g0, size_t g1) {
          for (size_t k = 0; k < d; ++k)
            for (size_t g = g0; g < g1; ++g) {
              typename F::Accum sum{};
              bool any = false;
              for (size_t j = 0; j < d && g * d + j < ncoord; ++j) {
                if (c[g * d + j] == f.zero()) continue;
                f.mac(sum, twisted_dual[k * d + j], c[g * d + j]);
                any = true;
              }
              if (!any) continue;
              f.add(a[k * ng + g], phi_inv_public(f, f.reduce(sum), k));
            }
        });
  }

  // Whether add_coefficients serves the stage: in characteristic 2 the
  // forms are the twisted-dual sums above, and phi^-k is GF(2)-linear.
  static constexpr bool kCoefficients = F::kCharacteristicTwo;

  // Adds into v[g] (g < ng) the coefficient sum_k w_k a_k[g] of the forms
  // add_forms builds from C, without building them. Since
  // phi^-k(phi^k(beta*_j)) = beta*_j,
  //
  //     a_k[g] = sum_j beta*_j phi^-k(c_{g,j}),
  //     sum_k w_k a_k[g] = sum_j beta*_j R(c_{g,j}),  R = sum_k w_k phi^-k,
  //
  // and R is one GF(2)-linear map (LinearMap): one map and one product per
  // coordinate in place of d products and d twists per group. W and C are
  // public, so the map's byte tables are no leak.
  void add_coefficients(const F &f, const Elt *w, const Elt *c, size_t ncoord,
                        size_t ng, Elt *v) const {
    static_assert(kCoefficients, "coefficients without forms: characteristic 2");
    const LinearMap<F> r(f, [&](const Elt &x) {
      Elt y = f.mulf(w[0], x);
      for (size_t k = 1; k < d; ++k)
        f.add(y, f.mulf(w[k], phi_inv_public(f, x, k)));
      return y;
    });
    parallel::for_chunks(
        ng, parallel::grain_for(ng, parallel::kChunks),
        [&](size_t g0, size_t g1) {
          // The chunk's coordinates through R; a short last group's missing
          // coordinates stay zero.
          const size_t c0 = std::min(g0 * d, ncoord);
          const size_t c1 = std::min(g1 * d, ncoord);
          std::vector<Elt> x((g1 - g0) * d, f.zero());
          r.apply(c + c0, x.data(), c1 - c0);
          for (size_t g = g0; g < g1; ++g) {
            typename F::Accum sum{};
            for (size_t j = 0; j < d; ++j)
              f.mac(sum, dual[j], x[(g - g0) * d + j]);
            f.add(v[g], f.reduce(sum));
          }
        });
  }

  // The forms of a GKR input claim on bits packed d to a group (the bit
  // stage, zk_packed.h's PackedForms over d-bit groups): the claim is
  // sum_x (eq(g0, x) + alpha eq(g1, x)) w_x over the circuit inputs, input
  // d Y + j bit j of group Y. Adds SCALE times the claim into a[k * ng + Y]
  // for Y < ng.
  //
  // A block of groups holding a composed view's bits (Block) takes the
  // view's basis change: its D canonical bits l lie in groups Y0 + l / d,
  // and group Y0 + i's form k is phi^-k(sum_l E(d Y0 + l) tau_{k,i,l})
  // (ComposedBits), with E the claim's coefficient on input d Y0 + l. Since
  // E(d Y + j) splits as eq(lo, j) eq(hi, Y), that form is
  //   sum_{i'} e0(Y0 + i') D0_{k,i,i'} + e1(Y0 + i') D1_{k,i,i'},
  //   D0_{k,i,i'} = phi^-k(scale sum_j eq(g0 lo, j) tau_{k,i,d i' + j}),
  // and D1 likewise with alpha: the eq structure is kept.
  struct Block {
    size_t group;            // first group (absolute)
    size_t r;                // groups per word
    const Elt *tau;          // [(k * r + i) * (r d) + l]
  };
  void add_eq_forms(const F &f, size_t logv, size_t ng, const Elt *g0,
                    const Elt *g1, const Elt &alpha, const Elt &scale,
                    std::vector<Elt> &a,
                    const std::vector<Block> &blocks = {}) const {
    check(squaring_chain() && b == 1, "eq forms of the bit stage");
    size_t logd = 0;
    while ((size_t(1) << logd) < d) ++logd;
    check((size_t(1) << logd) == d && logv >= logd, "eq forms: group size");
    a.resize(d * ng, f.zero());
    const size_t loghi = logv - logd;
    Eqs<F> e0lo(logd, d, g0, f);
    Eqs<F> e1lo(logd, d, g1, f);
    std::vector<Elt> h0(loghi), h1(loghi);
    std::vector<bool> in_block;
    if (!blocks.empty()) {
      in_block.assign(ng, false);
      for (const auto &b : blocks)
        for (size_t i = 0; i < b.r; ++i) in_block.at(b.group + i) = true;
    }
    for (size_t k = 0; k < d; ++k) {
      Elt d0 = f.zero(), d1 = f.zero();
      for (size_t i = 0; i < d; ++i) {
        f.add(d0, f.mulf(e0lo.at(i), twisted_dual[k * d + i]));
        f.add(d1, f.mulf(e1lo.at(i), twisted_dual[k * d + i]));
      }
      f.mul(d1, alpha);
      f.mul(d0, scale);
      f.mul(d1, scale);
      const Elt D0 = phi_inv(f, d0, k), D1 = phi_inv(f, d1, k);
      for (size_t j = 0; j < loghi; ++j) {
        h0[j] = phi_inv(f, g0[logd + j], k);
        h1[j] = phi_inv(f, g1[logd + j], k);
      }
      Eqs<F> e0(loghi, ng, h0.data(), f);
      Eqs<F> e1(loghi, ng, h1.data(), f);
      for (size_t Y = 0; Y < ng; ++Y) {
        if (!in_block.empty() && in_block[Y]) continue;
        f.add(a[k * ng + Y], f.addf(f.mulf(e0.at(Y), D0), f.mulf(e1.at(Y), D1)));
      }
      // The blocks' mixing matrices, per distinct basis.
      const Elt *tau_seen = nullptr;
      std::vector<Elt> M0, M1;
      for (const auto &b : blocks) {
        const size_t D = b.r * d;
        if (b.tau != tau_seen) {
          tau_seen = b.tau;
          M0.assign(b.r * b.r, f.zero());
          M1.assign(b.r * b.r, f.zero());
          for (size_t i = 0; i < b.r; ++i)
            for (size_t ip = 0; ip < b.r; ++ip) {
              const Elt *t = b.tau + (k * b.r + i) * D + d * ip;
              Elt c0 = f.zero(), c1 = f.zero();
              for (size_t j = 0; j < d; ++j) {
                f.add(c0, f.mulf(e0lo.at(j), t[j]));
                f.add(c1, f.mulf(e1lo.at(j), t[j]));
              }
              f.mul(c1, alpha);
              f.mul(c0, scale);
              f.mul(c1, scale);
              M0[i * b.r + ip] = phi_inv(f, c0, k);
              M1[i * b.r + ip] = phi_inv(f, c1, k);
            }
        }
        for (size_t i = 0; i < b.r; ++i) {
          Elt s = f.zero();
          for (size_t ip = 0; ip < b.r; ++ip) {
            f.add(s, f.mulf(e0.at(b.group + ip), M0[i * b.r + ip]));
            f.add(s, f.mulf(e1.at(b.group + ip), M1[i * b.r + ip]));
          }
          f.add(a[k * ng + b.group + i], s);
        }
      }
    }
  }

  // The T-value of d B-coordinates (the prover's packing).
  Elt pack(const F &f, const Elt *x, size_t n) const {
    Elt p = f.zero();
    for (size_t j = 0; j < d && j < n; ++j) f.add(p, f.mulf(beta[j], x[j]));
    return p;
  }
  // pack() on coordinates the prover has checked to lie in B: in odd
  // characteristic over the prime subfield (b = 1), whose elements are
  // their first coordinate, by scalar multiplications; the same value.
  Elt pack_checked(const F &f, const Elt *x, size_t n) const {
    if constexpr (!F::kCharacteristicTwo && has_scalar_mul<F>::value) {
      if (b == 1) {
        Elt p = f.zero();
        for (size_t j = 0; j < d && j < n; ++j)
          f.add(p, f.mulf(beta[j], x[j].e[0]));
        return p;
      }
    }
    return pack(f, x, n);
  }
  // The d B-coordinates of a T-value P (the prover's unpacking):
  // x_j = Tr_{T/B}(beta*_j p) = sum_k phi^k(beta*_j) phi^k(p).
  void coordinates(const F &f, const Elt &p, Elt *x) const {
    std::vector<Elt> pk(d);
    pk[0] = p;
    // P is a witness value: frobenius_power_ct.
    for (size_t k = 1; k < d; ++k) pk[k] = frobenius_power_ct(f, p, b * k);
    for (size_t j = 0; j < d; ++j) {
      Elt s = f.zero();
      for (size_t k = 0; k < d; ++k)
        f.add(s, f.mulf(twisted_dual[k * d + j], pk[k]));
      x[j] = s;
    }
  }

  // The stage's transcript label (tree_zk.h, gordiehowe.stage:<label>). The
  // proof binds these bytes, so the mode tags keep their original spelling:
  // "chain" for squaring-chain masks, "linear" for subfield masks.
  std::string transcript_label() const {
    return "GF(p^" + std::to_string(b) + ") < GF(p^" + std::to_string(t) +
           ") " + (squaring_chain() ? "chain" : "linear");
  }

 private:
  static constexpr bool kTwistTables =
      std::is_same_v<F, GF2_128<>> || std::is_same_v<F, GF2_256<>>;
  // [((k - 1) * kBytes + i) * 256 + v]: phi^-k of the element whose byte i
  // is v and whose other bytes are zero, for 0 < k < d.
  std::vector<Elt> inv_tab_;
  // A root stage's phi^-k, 0 < k < d, as linear maps (add_forms).
  std::vector<LinearMap<F>> inv_map_;
  void twist_tables(const F &f) {
    if constexpr (kTwistTables) {
      // A root stage keeps its twists as linear maps only: their byte
      // tables are these tables.
      if (root) {
        for (size_t k = 1; k < d; ++k)
          inv_map_.emplace_back(f, [&](const Elt &x) { return phi_inv(f, x, k); });
        return;
      }
      constexpr size_t kWords = F::kBytes / 8;
      inv_tab_.assign((d - 1) * F::kBytes * 256, f.zero());
      for (size_t k = 1; k < d; ++k)
        for (size_t i = 0; i < F::kBytes; ++i) {
          Elt *t = &inv_tab_[((k - 1) * F::kBytes + i) * 256];
          Elt img[8];
          for (size_t bit = 0; bit < 8; ++bit) {
            std::array<uint64_t, kWords> raw{};
            raw[i / 8] = uint64_t(1) << (8 * (i % 8) + bit);
            img[bit] = phi_inv(f, f.of_scalar_field(raw), k);
          }
          for (size_t v = 1; v < 256; ++v) {
            size_t low = 0;
            while (((v >> low) & 1) == 0) ++low;
            t[v] = f.addf(t[v & (v - 1)], img[low]);
          }
        }
    }
  }
  // GF(2) in T: T's prime basis and its dual for Tr_{T/GF(2)} (PackedBasis).
  void bit_basis(const F &f) {
    const auto &s = SubfieldInfo<F>::get(f, t);
    check(d <= 64, "bit stage of degree above 64");
    beta = s.basis;
    std::vector<uint64_t> T(d, 0), inv(d, 0);
    for (size_t i = 0; i < d; ++i)
      for (size_t j = 0; j < d; ++j) {
        const Elt tr = trace2(f, f.mulf(beta[i], beta[j]));
        if (tr == f.one()) {
          T[i] |= uint64_t(1) << j;
        } else {
          check(tr == f.zero(), "trace of a subfield element outside GF(2)");
        }
      }
    for (size_t i = 0; i < d; ++i) inv[i] = uint64_t(1) << i;
    for (size_t c = 0; c < d; ++c) {
      size_t p = c;
      while (p < d && !((T[p] >> c) & 1)) ++p;
      check(p < d, "trace form is degenerate");
      std::swap(T[c], T[p]);
      std::swap(inv[c], inv[p]);
      for (size_t r = 0; r < d; ++r)
        if (r != c && ((T[r] >> c) & 1)) {
          T[r] ^= T[c];
          inv[r] ^= inv[c];
        }
    }
    dual.assign(d, f.zero());
    for (size_t i = 0; i < d; ++i)
      for (size_t j = 0; j < d; ++j)
        if ((inv[i] >> j) & 1) f.add(dual[i], beta[j]);
  }
  Elt trace2(const F &f, Elt x) const {
    Elt s = f.zero();
    for (size_t k = 0; k < t; ++k) {
      f.add(s, x);
      x = f.mulf(x, x);
    }
    return s;
  }
  // A power basis 1, g, ..., g^(d-1) of T over B, g of degree d over B, and
  // its dual for Tr_{T/B} (subfield-masks stages, and squaring-chain-masks
  // stages over B > GF(2)).
  void power_basis(const F &f) {
    // Candidates: T's prime basis, or K's basis over S0 for T = K.
    std::vector<Elt> cand;
    if (root) {
      const auto &eb = ExtensionBasis<F>::get(f);
      cand.assign(eb.beta.begin(), eb.beta.end());
    } else {
      cand = SubfieldInfo<F>::get(f, t).basis;
    }
    Elt g = f.zero();
    bool found = false;
    for (size_t i = 0; i < cand.size() && !found; ++i)
      for (size_t j = i; j < cand.size() && !found; ++j) {
        g = i == j ? cand[i] : f.addf(cand[i], cand[j]);
        found = true;
        for (size_t k = 1; k < d && found; ++k)
          if (phi(f, g, k) == g) found = false;
      }
    check(found, "no generator of the stage's top field");
    beta.assign(d, f.one());
    for (size_t i = 1; i < d; ++i) beta[i] = f.mulf(beta[i - 1], g);
    // Tr_{T/B}(beta_i beta_j), inverted by Gauss-Jordan in K.
    std::vector<std::vector<Elt>> M(d, std::vector<Elt>(2 * d, f.zero()));
    for (size_t i = 0; i < d; ++i) {
      for (size_t j = 0; j < d; ++j) {
        const Elt x = f.mulf(beta[i], beta[j]);
        Elt tr = f.zero();
        for (size_t k = 0; k < d; ++k) f.add(tr, phi(f, x, k));
        M[i][j] = tr;
      }
      M[i][d + i] = f.one();
    }
    for (size_t c = 0; c < d; ++c) {
      size_t p = c;
      while (p < d && M[p][c] == f.zero()) ++p;
      check(p < d, "relative trace form nonsingular");
      std::swap(M[p], M[c]);
      const Elt inv = f.invertf(M[c][c]);
      for (auto &x : M[c]) f.mul(x, inv);
      for (size_t r = 0; r < d; ++r)
        if (r != c) {
          const Elt a = M[r][c];
          for (size_t j = 0; j < 2 * d; ++j) f.sub(M[r][j], f.mulf(a, M[c][j]));
        }
    }
    dual.assign(d, f.zero());
    for (size_t i = 0; i < d; ++i)
      for (size_t j = 0; j < d; ++j) f.add(dual[i], f.mulf(M[i][d + j], beta[j]));
  }
};

// The bits of GF(2^D) words viewed through the packing tree's path
// GF(2) < N_1 < N_2 < ... < GF(2^D): the bit stage GF(2) < N_1 and the
// stages above it, in either mode (the reduction above, applied stage by
// stage; only their bases enter).
//
// A word w is decoded top-down: its coordinates over each N_m in the basis
// delta^(m) of N_(m+1)/N_m, down to r = D / [N_1 : GF(2)] values y_i of N_1,
// each of which the bit stage decodes into d bits b_{i,j}. So
//   w = sum_{i,j} t_{i,j} b_{i,j},  t_{i,j} = beta_j delta^(1)_{i_1}
//       delta^(2)_{i_2} ...,  i = i_1 + d_1 (i_2 + d_2 (...)),
// with d_m = [N_(m+1) : N_m]: the tower basis, tower bit i d + j.
//
// The view's bit l is the word's canonical bit c_l (the coefficient of
// SubfieldInfo<F>(D)'s basis element l), the order the circuit reads, and
// c_l = sum_m P_{l,m} b_m with P_{l,m} the canonical coordinate l of the
// tower element m: a fixed GF(2)-linear map, which the system description
// records. A claim sum_l v_l c_l is sum_m (P^T v)_m b_m, so the bit
// stage's form k of group i is
//   phi^-k(sum_j phi^k(beta*_j) (P^T v)_{i d + j})
//     = phi^-k(sum_l v_l tau_{k,i,l}),
//   tau_{k,i,l} = phi^k(rho_{i,l}),  rho_{i,l} = sum_j P_{l, i d + j} beta*_j,
// since phi is additive and P has entries 0 and 1. The basis change sits
// in the forms' coefficients and adds no witness.
template <class F>
struct ComposedBits {
  using Elt = typename F::Elt;
  size_t D = 0, d = 0, r = 0;  // word degree, bit-stage degree, groups per word
  std::vector<uint64_t> P;     // P[l], bit m: canonical coordinate l of t_m
  std::vector<Elt> tau;        // [(k * r + i) * D + l]

  ComposedBits() = default;
  // BITS: GF(2) < N_1. UPPER: N_1 < N_2, ..., up to GF(2^D), in either
  // mode.
  ComposedBits(const F &f, const PackingStage<F> &bits,
               const std::vector<const PackingStage<F> *> &upper) {
    check(bits.squaring_chain() && bits.b == 1,
          "composed bits: the bit stage first");
    d = bits.d;
    D = d;
    size_t below = bits.t;
    for (const auto *s : upper) {
      check(s->b == below, "composed bits: a path of stages");
      below = s->t;
      D *= s->d;
    }
    check(D == below && D <= 64, "composed bits: words of at most 64 bits");
    r = D / d;
    P.assign(D, 0);
    if constexpr (F::kCharacteristicTwo) {
      const auto &canon = SubfieldInfo<F>::get(f, D);
      for (size_t i = 0; i < r; ++i) {
        Elt delta = f.one();
        size_t rest = i;
        for (const auto *s : upper) {
          delta = f.mulf(delta, s->beta[rest % s->d]);
          rest /= s->d;
        }
        for (size_t j = 0; j < d; ++j) {
          const uint64_t u = canon.bits(f, f.mulf(delta, bits.beta[j]));
          for (size_t l = 0; l < D; ++l)
            if ((u >> l) & 1) P[l] |= uint64_t(1) << (i * d + j);
        }
      }
    }
    tau.assign(d * r * D, f.zero());
    for (size_t i = 0; i < r; ++i)
      for (size_t l = 0; l < D; ++l) {
        Elt rho = f.zero();
        for (size_t j = 0; j < d; ++j)
          if ((P[l] >> (i * d + j)) & 1) f.add(rho, bits.dual[j]);
        for (size_t k = 0; k < d; ++k)
          tau[(k * r + i) * D + l] = bits.phi(f, rho, k);
      }
  }

  // The bit stage's forms of a claim with coefficients V on the D
  // canonical bits of a word whose groups are G0 .. G0 + r - 1 of NG: adds
  // into a[k * ng + g0 + i].
  void add_forms(const F &f, const PackingStage<F> &bits, const Elt *v,
                 size_t ng, size_t g0, std::vector<Elt> &a) const {
    a.resize(d * ng, f.zero());
    for (size_t k = 0; k < d; ++k)
      for (size_t i = 0; i < r; ++i) {
        typename F::Accum sum{};
        const Elt *t = &tau[(k * r + i) * D];
        for (size_t l = 0; l < D; ++l) f.mac(sum, t[l], v[l]);
        f.add(a[k * ng + g0 + i], bits.phi_inv(f, f.reduce(sum), k));
      }
  }
};

}  // namespace proofs::gordiehowe::compiler

#endif  // PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_COMPILER_STAGE_H_
