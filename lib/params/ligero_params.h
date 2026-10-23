// Copyright 2026 Chad Sharp and Paul Grubbs
// SPDX-License-Identifier: Apache-2.0
//
// Starting parameters for the PQ circuits at the QROM parameters. Every
// reported layout must
// still pass the per-construction soundness screen; these are not a
// certificate.
#ifndef PRIVACY_PROOFS_ZK_LIB_PARAMS_LIGERO_PARAMS_H_
#define PRIVACY_PROOFS_ZK_LIB_PARAMS_LIGERO_PARAMS_H_

#include <stddef.h>

namespace proofs {

inline constexpr size_t kRate = 6;
inline constexpr size_t kNreq = 304;

} // namespace proofs

#endif // PRIVACY_PROOFS_ZK_LIB_PARAMS_LIGERO_PARAMS_H_
