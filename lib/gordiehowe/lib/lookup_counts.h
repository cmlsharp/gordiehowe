// Copyright 2026 Chad Sharp and Paul Grubbs
// SPDX-License-Identifier: Apache-2.0

// GordieHowe: the honest counts of a log-derivative lookup, shared by the
// public tables (table.h) and assert_in (compiler/assert_in.h).
//
//   first_match_counts(n, R, eq)   multiplicities, by an oblivious scan

#ifndef PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_LIB_LOOKUP_COUNTS_H_
#define PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_LIB_LOOKUP_COUNTS_H_

#include <cstddef>
#include <cstdint>
#include <vector>

namespace proofs::gordiehowe::lib::table::table_internal {

// COUNT[j] = the number of keys t < N whose first matching row is j, where
// EQ(t, j) is 1 when key t matches row j and 0 otherwise. Oblivious: every
// key is compared with every row (ct.h).
template <class Eq>
std::vector<uint64_t> first_match_counts(size_t n, size_t R, const Eq &eq) {
  std::vector<uint64_t> cnt(R, 0);
  for (size_t t = 0; t < n; ++t) {
    uint64_t open = 1;
    for (size_t j = 0; j < R; ++j) {
      const uint64_t hit = eq(t, j) & open;
      cnt[j] += hit;
      open &= hit ^ 1;
    }
  }
  return cnt;
}

}  // namespace proofs::gordiehowe::lib::table::table_internal

#endif  // PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_LIB_LOOKUP_COUNTS_H_
