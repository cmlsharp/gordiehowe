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

// The Falcon emulated relation of profile P and parameter set S.
#define GORDIEHOWE_FALCON_EMULATED_INSTANCE(EXT, P, S)                    \
  EXT template void falcon_emulated_relation<P, S>(                      \
      Env<P>::Sys &, const Env<P> &, FalconStatement<S, In>,             \
      FalconWitness<S, In>, size_t);
// The Falcon native relation of profile P and parameter set S.
#define GORDIEHOWE_FALCON_NATIVE_INSTANCE(EXT, P, S)                      \
  EXT template void falcon_native_relation<P, S>(                        \
      Env<P>::Sys &, const Env<P> &, FalconStatement<S, In>,             \
      FalconWitness<S, In>, size_t);
// The Falcon ring relations of profile P and parameter set S, the carrier
// arm and the native arm.
#define GORDIEHOWE_FALCON_RING_CARRIER_INSTANCE(EXT, P, S)                \
  EXT template void ring_carrier_relation<P, S>(                         \
      CarrierEnv<P>::Sys &, const CarrierEnv<P> &, RingStatement<S, In>, \
      RingWitness<S, In>);
#define GORDIEHOWE_FALCON_RING_NATIVE_INSTANCE(EXT, P, S)                 \
  EXT template void ring_native_relation<P, S>(                          \
      NativeEnv<P>::Sys &, const NativeEnv<P> &, RingStatement<S, In>,   \
      RingWitness<S, In>);
// The ML-DSA native relation of profile P at the parameter set S.
#define GORDIEHOWE_MLDSA_NATIVE_INSTANCE(EXT, P, S)                       \
  EXT template void mldsa_native_relation<P, S>(                         \
      Env<P>::Sys &, const Env<P> &, MLDSAInputs<S>::Statement<In>,      \
      MLDSAInputs<S>::Witness<In>, size_t, PackingAblation);

// The ML-DSA emulated relation of profile P at the parameter set S.
#define GORDIEHOWE_MLDSA_EMULATED_INSTANCE(EXT, P, S)                     \
  EXT template void mldsa_emulated_relation<P, S>(                       \
      Env<P>::Sys &, const Env<P> &, MLDSAInputs<S>::Statement<In>,      \
      MLDSAInputs<S>::Witness<In>, size_t, PackingAblation);

// The ML-DSA private ring relations of profile P at the parameter set S,
// native and carrier.
#define GORDIEHOWE_MLDSA_RING_NATIVE_INSTANCE(EXT, P, S)                  \
  EXT template void mldsa_ring_native_relation<P, S>(                    \
      Env<P>::Sys &, const Env<P> &, MLDSARingInputs<S>::Statement<In>,  \
      MLDSARingInputs<S>::Witness<In>);
#define GORDIEHOWE_MLDSA_RING_CARRIER_INSTANCE(EXT, P, S)                 \
  EXT template void mldsa_ring_carrier_relation<P, S>(                   \
      CarrierEnv<P>::Sys &, const CarrierEnv<P> &,                       \
      MLDSARingInputs<S>::Statement<In>, MLDSARingInputs<S>::Witness<In>);
// Each ML-DSA system's relations for both profiles at the parameter set S.
#define GORDIEHOWE_MLDSA_SET_INSTANCES(EXT, M, S)                         \
  M(EXT, param_sets::ROMParams, S)                                       \
  M(EXT, param_sets::QROMParams, S)

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
      Env<P>::MldsaSys &, const Env<P> &,                                \
      mldsa::MLDSAInputs<MLDSA>::Statement<In>,                          \
      mldsa::MLDSAInputs<MLDSA>::Witness<In>, size_t);

namespace proofs::gordiehowe::examples::composite {
GORDIEHOWE_COMPOSITE_INSTANCE(extern, param_sets::ROMParams)
GORDIEHOWE_COMPOSITE_INSTANCE(extern, param_sets::QROMParams)
}  // namespace proofs::gordiehowe::examples::composite

// The Falcon systems of both parameter sets.
#define GORDIEHOWE_FALCON_EXTERN(SYSTEM)                                  \
  SYSTEM(extern, param_sets::ROMParams, Falcon512)                       \
  SYSTEM(extern, param_sets::QROMParams, Falcon512)                      \
  SYSTEM(extern, param_sets::ROMParams, Falcon1024)                      \
  SYSTEM(extern, param_sets::QROMParams, Falcon1024)

namespace proofs::gordiehowe::examples::falcon::emulated {
GORDIEHOWE_FALCON_EXTERN(GORDIEHOWE_FALCON_EMULATED_INSTANCE)
}  // namespace proofs::gordiehowe::examples::falcon::emulated

namespace proofs::gordiehowe::examples::falcon::native {
GORDIEHOWE_FALCON_EXTERN(GORDIEHOWE_FALCON_NATIVE_INSTANCE)
}  // namespace proofs::gordiehowe::examples::falcon::native

namespace proofs::gordiehowe::examples::falcon::ring {
GORDIEHOWE_FALCON_EXTERN(GORDIEHOWE_FALCON_RING_CARRIER_INSTANCE)
GORDIEHOWE_FALCON_EXTERN(GORDIEHOWE_FALCON_RING_NATIVE_INSTANCE)
}  // namespace proofs::gordiehowe::examples::falcon::ring

namespace proofs::gordiehowe::examples::mldsa {
#define GORDIEHOWE_MLDSA_EXTERN(S)                                         \
  GORDIEHOWE_MLDSA_SET_INSTANCES(extern, GORDIEHOWE_MLDSA_NATIVE_INSTANCE, \
                                 S)                                        \
  GORDIEHOWE_MLDSA_SET_INSTANCES(extern,                                   \
                                 GORDIEHOWE_MLDSA_RING_NATIVE_INSTANCE, S) \
  GORDIEHOWE_MLDSA_SET_INSTANCES(extern,                                   \
                                 GORDIEHOWE_MLDSA_RING_CARRIER_INSTANCE, S)
GORDIEHOWE_MLDSA_EXTERN(MLDSA44)
GORDIEHOWE_MLDSA_EXTERN(MLDSA65)
GORDIEHOWE_MLDSA_EXTERN(MLDSA87)
#undef GORDIEHOWE_MLDSA_EXTERN
}  // namespace proofs::gordiehowe::examples::mldsa

namespace proofs::gordiehowe::examples::mldsa::emulated {
GORDIEHOWE_MLDSA_SET_INSTANCES(extern, GORDIEHOWE_MLDSA_EMULATED_INSTANCE,
                               MLDSA44)
GORDIEHOWE_MLDSA_SET_INSTANCES(extern, GORDIEHOWE_MLDSA_EMULATED_INSTANCE,
                               MLDSA65)
GORDIEHOWE_MLDSA_SET_INSTANCES(extern, GORDIEHOWE_MLDSA_EMULATED_INSTANCE,
                               MLDSA87)
}  // namespace proofs::gordiehowe::examples::mldsa::emulated

#endif  // PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_EXAMPLES_INSTANCES_H_
