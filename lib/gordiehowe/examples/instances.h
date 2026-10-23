// Copyright 2026 Chad Sharp and Paul Grubbs
// SPDX-License-Identifier: Apache-2.0

// Explicit instantiations of the example systems' builders for both PQ
// profiles (gordiehowe/instances.h explains the mechanism). The
// definitions are in gordiehowe/examples/instantiations/<system>_rom.cc and
// <system>_qrom.cc, one static library gordiehowe_example_<system> per
// system, which its tests and bench executables link (EXAMPLES in
// examples/CMakeLists.txt).

#ifndef PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_EXAMPLES_INSTANCES_H_
#define PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_EXAMPLES_INSTANCES_H_

#include <cstddef>

#include "params/param_sets.h"
#include "gordiehowe/examples/composite/composite.h"
#include "gordiehowe/examples/falcon/falcon_emulated.h"
#include "gordiehowe/examples/falcon/falcon_native.h"
#include "gordiehowe/examples/mldsa/mldsa_emulated.h"
#include "gordiehowe/examples/rings/falcon_ring.h"
#include "gordiehowe/examples/mldsa/mldsa_native.h"
#include "gordiehowe/examples/rings/mldsa_ring_carrier.h"
#include "gordiehowe/examples/rings/mldsa_ring_native.h"
#include "gordiehowe/instances.h"

// The Falcon emulated relation of profile P.
#define GORDIEHOWE_FALCON_EMULATED_INSTANCE(EXT, P)                       \
  EXT template void falcon_emulated_relation<P>(                         \
      Env<P>::Sys &, const Env<P> &, FalconStatement<In>,                \
      FalconWitness<In>, size_t);
// The Falcon native relation of profile P.
#define GORDIEHOWE_FALCON_NATIVE_INSTANCE(EXT, P)                         \
  EXT template void falcon_native_relation<P>(                           \
      Env<P>::Sys &, const Env<P> &, FalconStatement<In>,                \
      FalconWitness<In>, size_t);
// The Falcon ring relations of profile P, carrier and native arms.
#define GORDIEHOWE_FALCON_RING_INSTANCE(EXT, P)                           \
  EXT template void ring_carrier_relation<P>(                            \
      CarrierEnv<P>::Sys &, const CarrierEnv<P> &, RingStatement<In>,    \
      RingWitness<In>);                                                  \
  EXT template void ring_native_relation<P>(                             \
      NativeEnv<P>::Sys &, const NativeEnv<P> &, RingStatement<In>,      \
      RingWitness<In>);
// The ML-DSA native relation of profile P.
#define GORDIEHOWE_MLDSA_NATIVE_INSTANCE(EXT, P)                          \
  EXT template void mldsa_native_relation<P>(                            \
      Env<P>::Sys &, const Env<P> &, MLDSAStatement<In>,                 \
      MLDSAWitness<In>, size_t, PackingAblation);

// The ML-DSA emulated relation of profile P.
#define GORDIEHOWE_MLDSA_EMULATED_INSTANCE(EXT, P)                        \
  EXT template void mldsa_emulated_relation<P>(                          \
      Env<P>::Sys &, const Env<P> &, MLDSAStatement<In>,                 \
      MLDSAWitness<In>, size_t, PackingAblation);

// The ML-DSA private ring relations of profile P, native and carrier.
#define GORDIEHOWE_MLDSA_RING_NATIVE_INSTANCE(EXT, P)                     \
  EXT template void mldsa_ring_native_relation<P>(                       \
      Env<P>::Sys &, const Env<P> &, MLDSARingStatement<In>,             \
      MLDSARingWitness<In>);
#define GORDIEHOWE_MLDSA_RING_CARRIER_INSTANCE(EXT, P)                    \
  EXT template void mldsa_ring_carrier_relation<P>(                      \
      CarrierEnv<P>::Sys &, const CarrierEnv<P> &,                       \
      MLDSARingStatement<In>, MLDSARingWitness<In>);

// The composite signature's relation and the proofs of possession of each
// of its signatures alone, of profile P.
#define GORDIEHOWE_COMPOSITE_INSTANCE(EXT, P)                             \
  EXT template void composite_relation<P>(                               \
      Env<P>::Sys &, const Env<P> &, CompositeStatement<In>,             \
      CompositeWitness<In>, size_t);                                     \
  EXT template void ecdsa_pop_relation<P>(                               \
      Env<P>::EcdsaSys &, const Env<P> &, EcdsaStatement<In>,            \
      EcdsaWitness<In>, size_t);                                         \
  EXT template void mldsa_pop_relation<P>(                               \
      Env<P>::MldsaSys &, const Env<P> &, mldsa::MLDSAStatement<In>,     \
      mldsa::MLDSAWitness<In>, size_t);

namespace proofs::gordiehowe::examples::composite {
GORDIEHOWE_COMPOSITE_INSTANCE(extern, param_sets::ROMParams)
GORDIEHOWE_COMPOSITE_INSTANCE(extern, param_sets::QROMParams)
}  // namespace proofs::gordiehowe::examples::composite

namespace proofs::gordiehowe::examples::falcon::emulated {
GORDIEHOWE_FALCON_EMULATED_INSTANCE(extern, param_sets::ROMParams)
GORDIEHOWE_FALCON_EMULATED_INSTANCE(extern, param_sets::QROMParams)
}  // namespace proofs::gordiehowe::examples::falcon::emulated

namespace proofs::gordiehowe::examples::falcon::native {
GORDIEHOWE_FALCON_NATIVE_INSTANCE(extern, param_sets::ROMParams)
GORDIEHOWE_FALCON_NATIVE_INSTANCE(extern, param_sets::QROMParams)
}  // namespace proofs::gordiehowe::examples::falcon::native

namespace proofs::gordiehowe::examples::falcon::ring {
GORDIEHOWE_FALCON_RING_INSTANCE(extern, param_sets::ROMParams)
GORDIEHOWE_FALCON_RING_INSTANCE(extern, param_sets::QROMParams)
}  // namespace proofs::gordiehowe::examples::falcon::ring

namespace proofs::gordiehowe::examples::mldsa {
GORDIEHOWE_MLDSA_NATIVE_INSTANCE(extern, param_sets::ROMParams)
GORDIEHOWE_MLDSA_NATIVE_INSTANCE(extern, param_sets::QROMParams)
GORDIEHOWE_MLDSA_RING_NATIVE_INSTANCE(extern, param_sets::ROMParams)
GORDIEHOWE_MLDSA_RING_NATIVE_INSTANCE(extern, param_sets::QROMParams)
GORDIEHOWE_MLDSA_RING_CARRIER_INSTANCE(extern, param_sets::ROMParams)
GORDIEHOWE_MLDSA_RING_CARRIER_INSTANCE(extern, param_sets::QROMParams)
}  // namespace proofs::gordiehowe::examples::mldsa

namespace proofs::gordiehowe::examples::mldsa::emulated {
GORDIEHOWE_MLDSA_EMULATED_INSTANCE(extern, param_sets::ROMParams)
GORDIEHOWE_MLDSA_EMULATED_INSTANCE(extern, param_sets::QROMParams)
}  // namespace proofs::gordiehowe::examples::mldsa::emulated

#endif  // PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_EXAMPLES_INSTANCES_H_
