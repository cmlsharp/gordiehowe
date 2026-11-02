// Copyright 2026 Chad Sharp and Paul Grubbs
// SPDX-License-Identifier: Apache-2.0

// The ML-DSA bench executables' parameter-set flag: --param-set
// ml-dsa-44 (the default), ml-dsa-65 or ml-dsa-87 (mldsa_params.h).

#ifndef PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_EXAMPLES_MLDSA_MLDSA_BENCH_FLAGS_H_
#define PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_EXAMPLES_MLDSA_MLDSA_BENCH_FLAGS_H_

#include <string>

#include "bench/cli.h"
#include "gordiehowe/examples/mldsa/mldsa_params.h"

namespace proofs::gordiehowe::examples::mldsa {

inline void add_param_set_flag(bench::Flags &f) {
  f.flag("param-set", MLDSA44::kName,
         "the parameter set: ml-dsa-44, ml-dsa-65 or ml-dsa-87");
}
// FN(S{}) for the set S that --param-set names.
template <class Fn>
void with_param_set_flag(const bench::Flags &f, Fn &&fn) {
  if (!with_param_set(f.str("param-set"), fn))
    throw bench::UsageError("unknown parameter set " + f.str("param-set"));
}

}  // namespace proofs::gordiehowe::examples::mldsa

#endif  // PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_EXAMPLES_MLDSA_MLDSA_BENCH_FLAGS_H_
