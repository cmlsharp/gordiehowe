// Copyright 2026 Chad Sharp and Paul Grubbs
// SPDX-License-Identifier: Apache-2.0

// GordieHowe: the entry header. It includes the core language and the built-in
// linear operators.
//
// Namespaces, which the directories mirror:
//   proofs::gordiehowe (gh)   the core: ConstraintSystem, Domain<F>, the value
//                             forms, expressions, the predicates, Scope,
//                             assert_in's tables, compile(), the prover and
//                             verifier
//   gh::ops (ops/)            linear operators: NegacyclicConv, PolyMatVec,
//                             PolyBroadcast, the staged NTTs, the spectral
//                             circuits, MACConv
//   gh::lib::* (lib/)         library functions: keccak, sha256,
//                             permutation (multisets), windows, select,
//                             table, arith (norms, crossings)
//   gh::compiler (compiler/)  lowerings and their realizations (MAC, mod,
//                             range, LogUp), pads through Lowering, phase
//                             inference, placement, batches, the packing
//                             tree, the domain compiler, the plan export
//   gh::internal              implementation details
//   gh::examples::* (examples/)  mldsa, falcon, mdoc, pq_mdoc
// A library header is included on its own (gordiehowe/lib/keccak.h).

#ifndef PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_GORDIEHOWE_H_
#define PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_GORDIEHOWE_H_

#include "gordiehowe/core.h"           // IWYU pragma: export
#include "gordiehowe/domain.h"         // IWYU pragma: export
#include "gordiehowe/expr.h"           // IWYU pragma: export
#include "gordiehowe/linear.h"         // IWYU pragma: export
#include "gordiehowe/membership.h"     // IWYU pragma: export
#include "gordiehowe/ops/ntt.h"        // IWYU pragma: export
#include "gordiehowe/ops/operators.h"  // IWYU pragma: export
#include "gordiehowe/ops/spectral.h"   // IWYU pragma: export
#include "gordiehowe/predicates.h"     // IWYU pragma: export
#include "gordiehowe/relation.h"       // IWYU pragma: export
#include "gordiehowe/system.h"         // IWYU pragma: export
#include "gordiehowe/system_core.h"    // IWYU pragma: export

// The core namespace's short name, as the examples write it.
namespace gh = ::proofs::gordiehowe;

#endif  // PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_GORDIEHOWE_H_
