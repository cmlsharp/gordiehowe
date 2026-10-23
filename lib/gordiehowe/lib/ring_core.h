// Copyright 2026 Chad Sharp and Paul Grubbs
// SPDX-License-Identifier: Apache-2.0
//
// Host-side kernels of the public-table digests (table.h).  Everything here
// runs out of circuit, after the challenges are drawn, and both parties run
// it, so it is charged to prove AND to verify.
//
//   batch_invert   -- Montgomery's trick: one inversion for the whole vector.
//   ExtCoefTable   -- the lazy base-field ring digest used by the native arms.

#ifndef PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_LIB_RING_CORE_H_
#define PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_LIB_RING_CORE_H_

#include <stddef.h>
#include <stdint.h>

#include <array>
#include <vector>

#include "util/panic.h"

namespace proofs {

// out[i] = 1/x[i], with one field inversion and 3(n-1) multiplications.
// Every x[i] must be nonzero; callers draw them from post-commitment
// challenges, where a zero has probability n/|F|.
template <class Field>
void batch_invert(const Field& F, const typename Field::Elt* x, size_t n,
                  typename Field::Elt* out) {
  using Elt = typename Field::Elt;
  if (n == 0) return;
  std::vector<Elt> pre(n);  // pre[i] = x[0]*...*x[i-1]
  Elt run = F.one();
  for (size_t i = 0; i < n; ++i) {
    pre[i] = run;
    check(x[i] != F.zero(), "batch_invert: zero operand");
    run = F.mulf(run, x[i]);
  }
  Elt inv = F.invertf(run);  // the one inversion
  for (size_t i = n; i-- > 0;) {
    out[i] = F.mulf(inv, pre[i]);
    inv = F.mulf(inv, x[i]);
  }
}

template <class Field>
std::vector<typename Field::Elt> batch_invert(
    const Field& F, const std::vector<typename Field::Elt>& x) {
  std::vector<typename Field::Elt> out(x.size());
  batch_invert(F, x.data(), x.size(), out.data());
  return out;
}

// The ring digest d_j = sum_k entry_j[k] * gamma^k, for an extension field
// whose base is a small prime.  Writing gamma^k in the polynomial basis turns
// the digest into kDegree independent base-field dot products, so no extension
// multiply and no per-product Montgomery reduction appear in the inner loop.
//
// The table holds base residues, each below the base modulus, so uint32_t
// suffices for every field here (Falcon q = 12289, ML-DSA q = 8380417).  That
// halves the bytes the O(|R| * len) pass streams, and the pass is
// memory-bound.  Entries must also be plain residues below the base modulus:
// products then stay under 2^46 and `cap` of them accumulate in a uint64.
template <class Field>
class ExtCoefTable {
 public:
  static constexpr size_t kDeg = Field::kDegree;

  // Tabulate the first `len` powers of gamma.  `cap` is the largest entry
  // length that will be digested, which fixes the no-overflow bound.
  ExtCoefTable(const Field& F, const typename Field::Elt& gamma, size_t len,
               uint64_t modulus, size_t cap)
      : f_(F), q_(modulus), coef_(len * kDeg) {
    const auto& base = F.base_field();
    typename Field::Elt pw = F.one();
    uint64_t hi = 0;
    for (size_t k = 0; k < len; ++k) {
      for (size_t t = 0; t < kDeg; ++t) {
        const uint64_t c = base.from_montgomery(pw.e[t]).u64()[0];
        if (c > hi) hi = c;
        coef_[k * kDeg + t] = (uint32_t)c;
      }
      pw = F.mulf(pw, gamma);
    }
    check(hi < q_ && q_ <= (uint64_t{1} << 32), "table entry exceeds uint32");
    // (q-1)^2 * cap must fit a uint64 for the lazy accumulation to be exact.
    const uint64_t m = q_ - 1;
    check(cap == 0 || m == 0 || (m <= (~uint64_t{0}) / m / cap),
          "lazy digest would overflow");
  }

  // Acc accumulates the digest of one record over successive add() calls, each
  // consuming the next run of powers of gamma.  The arms digest a whole record
  // with a single add() followed by finish().
  struct Acc {
    std::array<uint64_t, kDeg> sum{};
    size_t pos = 0;  // index of the next power of gamma to consume
  };

  // entry[i] < modulus for i < len; the runs added to one Acc must together
  // stay within the cap this table was built with.
  //
  // Templated on the entry width because entries are bounded by the modulus:
  // 23 bits for ML-DSA and 14 for Falcon, against 64 bits of storage.  The
  // loop is load bound at these lengths, so narrowing the stream is most of
  // what the digest costs.
  template <typename T>
  void add(Acc& a, const T* entry, size_t len) const {
    check(a.pos + len <= coef_.size() / kDeg, "digest run exceeds the table");
    const uint32_t* c = coef_.data() + a.pos * kDeg;
    uint64_t s[kDeg];
    for (size_t t = 0; t < kDeg; ++t) s[t] = a.sum[t];
    for (size_t i = 0; i < len; ++i, c += kDeg) {
      const uint64_t v = entry[i];
      for (size_t t = 0; t < kDeg; ++t) s[t] += v * c[t];
    }
    for (size_t t = 0; t < kDeg; ++t) a.sum[t] = s[t];
    a.pos += len;
  }

  typename Field::Elt finish(const Acc& a) const {
    std::array<uint64_t, kDeg> red = a.sum;
    for (size_t t = 0; t < kDeg; ++t) red[t] %= q_;
    return f_.of_scalar_field(red);
  }

  template <typename T>
  typename Field::Elt digest(const T* entry, size_t len) const {
    Acc a;
    add(a, entry, len);
    return finish(a);
  }

  template <typename T>
  typename Field::Elt digest(const std::vector<T>& entry) const {
    return digest(entry.data(), entry.size());
  }

 private:
  const Field& f_;
  uint64_t q_;
  std::vector<uint32_t> coef_;  // row-major [k][t]
};

}  // namespace proofs

#endif  // PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_LIB_RING_CORE_H_
