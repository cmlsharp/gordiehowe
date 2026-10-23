// Copyright 2026 Chad Sharp and Paul Grubbs
// SPDX-License-Identifier: Apache-2.0

// Reed-Solomon encoding over a multiplicative subgroup of a prime field
// (algebra/subgroup_reed_solomon.h), the encoders of the fields whose roots
// of unity of order 2^32 lie in the field:
//   BasicFpReedSolomon  the emulated arms' Goldilocks extensions F_{p^2} and
//                       F_{p^4}, rows encoded over the subgroup of F_p
//                       componentwise, with subfield rows encoding one
//                       component
//   P128ReedSolomon     the prime field Fp128 (p = 2^128 - 2^108 + 1,
//                       algebra/fp_p128.h), on its own root of order 2^32
//                       (fp_p128.h derives it: w^(2^76) for w of order 2^108)
// The subgroup encoder needs Ligero's block to be a power of two, so
// block_enc comes from pow2_block_enc's search. The P-256 base field's
// encoder is a convolution instead (algebra/reed_solomon_p256.h).

#ifndef PRIVACY_PROOFS_ZK_LIB_ALGEBRA_REED_SOLOMON_FP_H_
#define PRIVACY_PROOFS_ZK_LIB_ALGEBRA_REED_SOLOMON_FP_H_

#include <cstddef>
#include <cstdint>

#include "algebra/fp_goldilocks.h"
#include "algebra/fp_goldilocks4.h"
#include "algebra/fp_p128.h"
#include "algebra/subgroup_reed_solomon.h"
#include "ligero/ligero_param.h"

namespace proofs {

// The smallest predicted proof over block_enc values whose Ligero block is a
// power of two: block = (block_enc + 1) / (2 + rate). Hash is the protocol
// hash policy, which sizes the Merkle part of the prediction. The first
// argument, the caller's label for the search, is unused.
template <class Fld, class Hash>
size_t pow2_block_enc(const char* /*name*/, size_t nw, size_t nq,
                      size_t rate, size_t req) {
  size_t best_e = 0, best = SIZE_MAX;
  for (size_t j = 4; j <= 20; ++j) {
    size_t lo = (2 + rate) * (size_t{1} << j) - 1;
    for (size_t e = lo; e < lo + (2 + rate); ++e) {
      LigeroParam<Fld, Hash> p(nw, nq, rate, req);
      size_t sz = p.layout(e);
      if (p.block != (size_t{1} << j)) continue;
      if (sz < best) {
        best = sz;
        best_e = e;
      }
    }
  }
  return best_e;
}

// The emulated field's encoder: the subgroup encoder on the 2^32 roots of F_p,
// applied componentwise to Goldilocks extension rows.
template <class Ext> struct GoldilocksReedSolomonFactory;
template <> struct GoldilocksReedSolomonFactory<Fp64G2> {
  template <class Base> using type = Fp64G2ReedSolomonFactory<Base>;
};
template <> struct GoldilocksReedSolomonFactory<Fp64G4> {
  template <class Base> using type = Fp64G4ReedSolomonFactory<Base>;
};
template <class Ext> class BasicFpReedSolomon {
  using BF = Fp64G;
  using BaseFactory = SubgroupReedSolomonFactory<BF>;

 public:
  using Factory =
      typename GoldilocksReedSolomonFactory<Ext>::template type<BaseFactory>;
  explicit BasicFpReedSolomon(const Ext& F)
      : base_(goldilocks_root_2_32(), 32, F.base_field()), rsf_(base_) {}
  BasicFpReedSolomon(const BasicFpReedSolomon&) = delete;
  BasicFpReedSolomon& operator=(const BasicFpReedSolomon&) = delete;
  const Factory& factory() const { return rsf_; }

  // block_enc for a commitment of nw values and nq quadratic constraints.
  template <class Hash>
  size_t block_enc(const char* name, size_t nw, size_t nq, size_t rate,
                   size_t req) const {
    return pow2_block_enc<Ext, Hash>(name, nw, nq, rate, req);
  }

 private:
  BaseFactory base_;
  Factory rsf_;
};
using FpReedSolomon = BasicFpReedSolomon<Fp64G2>;
using PqFp4ReedSolomon = BasicFpReedSolomon<Fp64G4>;

// Fp128's encoder: the subgroup encoder on the field's own roots.
class P128ReedSolomon {
 public:
  using Field = Fp128<>;
  using Factory = SubgroupReedSolomonFactory<Field>;

  explicit P128ReedSolomon(const Field& F)
      : rsf_(F.of_string(kRoot32), 32, F) {}
  P128ReedSolomon(const P128ReedSolomon&) = delete;
  P128ReedSolomon& operator=(const P128ReedSolomon&) = delete;
  const Factory& factory() const { return rsf_; }

 private:
  // The root of unity of order 2^32 (fp_p128.h).
  static constexpr char kRoot32[] = "164956748514267535023998284330560247862";
  Factory rsf_;
};

}  // namespace proofs

#endif  // PRIVACY_PROOFS_ZK_LIB_ALGEBRA_REED_SOLOMON_FP_H_
