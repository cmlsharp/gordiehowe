// Copyright 2026 Chad Sharp and Paul Grubbs
// SPDX-License-Identifier: Apache-2.0

// Explicit instantiations of GordieHowe's compile, lowering and domain
// paths for the field sets the tests and examples use.
//
// A translation unit that includes this header refers to the listed
// instantiations instead of instantiating them: the lowering passes, the
// domain compiler (CompiledDomain), the domain provers and verifiers,
// tree_zk, Ligero and sumcheck are compiled once, in
// gordiehowe/instantiations/<set>__<field>.cc (one file per domain, compiled
// in parallel; one library gordiehowe_instances_<set> per field set),
// instead of once per test file. Each entry point named here is a function
// template defined out of class without `inline`: an explicit instantiation
// declaration suppresses its body, and everything only it reaches, in the
// including translation unit. (A member defined in its class is inline and
// would still be instantiated for inlining.)
//
// A field set or domain missing from the list is instantiated implicitly
// where it is used; only build time differs. A target that includes this
// header links the libraries of the field sets it uses
// (gordiehowe_add_test's SETS); a missing one is a link error.

#ifndef PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_INSTANCES_H_
#define PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_INSTANCES_H_

#include <memory>

#include "algebra/convolution.h"
#include "algebra/fp14_n.h"
#include "algebra/fp2.h"
#include "algebra/fp24_6.h"
#include "algebra/fp_goldilocks.h"
#include "algebra/fp_goldilocks4.h"
#include "algebra/fp_native_wide.h"
#include "algebra/fp_p128.h"
#include "algebra/reed_solomon.h"
#include "algebra/reed_solomon_extension_n.h"
#include "algebra/subgroup_reed_solomon.h"
#include "ec/p256.h"
#include "gf2k/gf2_128.h"
#include "gf2k/gf2_256.h"
#include "gf2k/lch14_reed_solomon.h"
#include "gordiehowe/system.h"
#include "util/crypto.h"

namespace proofs::gordiehowe::instances {

// Reed-Solomon factories of the domains.
using RsGold2 = Fp64G2ReedSolomonFactory<SubgroupReedSolomonFactory<Fp64G>>;
using RsGold4 = Fp64G4ReedSolomonFactory<SubgroupReedSolomonFactory<Fp64G>>;
using RsGf128 = LCH14ReedSolomonFactory<GF2_128<>>;
using RsGf128_3 = LCH14ReedSolomonFactory<GF2_128<3>>;
using RsGf256 = LCH14ReedSolomonFactory<GF2_256<>>;
using RsFp14_9 = ReedSolomonExtensionNFactory<Fp14_9>;
using RsFalcon20 = ReedSolomonExtensionNFactory<FalconField20>;
using RsFp24_6 = ReedSolomonExtensionNFactory<Fp24_6>;
using RsMlDsa11 = ReedSolomonExtensionNFactory<MlDsaField11>;
// F_p256: Longfellow's encoder, a convolution by FFT over F_p256^2.
using RsP256 = ReedSolomonFactory<
    Fp256Base, FFTExtConvolutionFactory<Fp256Base, Fp2<Fp256Base>>>;
// Fp128: the subgroup encoder on its own roots of unity.
using RsFp128 = SubgroupReedSolomonFactory<Fp128<>>;

// The field sets.
using SetFp14_9 = FieldSet<SHA256, Fp14_9>;
using SetMod = FieldSet<SHA384, Fp64G4, GF2_256<>, GF2_128<>, Fp14_9>;
using SetROMEmu = FieldSet<SHA256, GF2_128<>, Fp64G2>;
using SetQROMEmu = FieldSet<SHA384, GF2_256<>, Fp64G4>;
using SetROMMlDsa = FieldSet<SHA256, GF2_128<>, Fp24_6>;
using SetQROMMlDsa = FieldSet<SHA384, GF2_256<>, MlDsaField11>;
using SetROMFalconNative = FieldSet<SHA256, GF2_128<>, Fp14_9>;
using SetQROMFalconNative = FieldSet<SHA384, GF2_256<>, FalconField20>;
using SetGold4Gf128Sha256 = FieldSet<SHA256, Fp64G4, GF2_128<>>;
using SetGold4Gf128 = FieldSet<SHA384, Fp64G4, GF2_128<>>;
using SetGold4Gf256 = FieldSet<SHA384, Fp64G4, GF2_256<>>;
using SetGold4 = FieldSet<SHA384, Fp64G4>;
using SetGold2Sha256 = FieldSet<SHA256, Fp64G2>;
using SetGf128_3 = FieldSet<SHA384, GF2_128<3>>;
using SetGf128Sha256 = FieldSet<SHA256, GF2_128<>>;
using SetGf128 = FieldSet<SHA384, GF2_128<>>;
using SetGf256 = FieldSet<SHA384, GF2_256<>>;
using SetFalcon20 = FieldSet<SHA384, FalconField20>;
using SetP256 = FieldSet<SHA256, Fp256Base>;
// Plain mdoc: the hash side in GF(2^128), the signature side in F_p256.
using SetMdoc = FieldSet<SHA256, GF2_128<>, Fp256Base>;
// The ROM parameters with A in the prime field Fp128 (RSA).
using SetROMFp128 = FieldSet<SHA256, GF2_128<>, Fp128<>>;
// The composite signature (examples/composite/composite.h): H, F_p256 for
// ECDSA and the ML-DSA native field, per parameter set; ECDSA's proof of
// possession at the QROM parameters (at the ROM parameters it is
// SetMdoc's).
using SetROMComposite = FieldSet<SHA256, GF2_128<>, Fp256Base, Fp24_6>;
using SetQROMComposite = FieldSet<SHA384, GF2_256<>, Fp256Base, MlDsaField11>;
using SetQROMEcdsa = FieldSet<SHA384, GF2_256<>, Fp256Base>;

}  // namespace proofs::gordiehowe::instances

// compile() of the system over field set S, its four overloads.
#define GORDIEHOWE_SYSTEM_INSTANCE(EXT, S)                      \
  EXT template std::unique_ptr<BasicCompiledSystem<S>> compile( \
      const S::System &);                                       \
  EXT template std::unique_ptr<BasicCompiledSystem<S>> compile( \
      const S::System &, const CompileCache &);                 \
  EXT template std::unique_ptr<BasicCompiledSystem<S>> compile( \
      S::System &, const CompileProfile &);                     \
  EXT template std::unique_ptr<BasicCompiledSystem<S>> compile( \
      S::System &, const CompileProfile &, const CompileCache &);

// The domain of field F with factory RSF in field set S: its compiler,
// which alone reaches CompiledDomain, the domain prover and verifier,
// tree_zk, Ligero and sumcheck.
#define GORDIEHOWE_DOMAIN_INSTANCE(EXT, F, RSF, S)    \
  EXT template std::unique_ptr<CompiledDomainBase<S>> \
  DomainImpl<F, RSF, S>::compile(const CompilePlan &,  \
                                 const DomainSource *) const;

// The lowerings of the domain of field F in field set S: ranges and
// assert_mod.
#define GORDIEHOWE_LOWERING_INSTANCE(EXT, F, S)             \
  EXT template void compiler::lower_ranges<F, S>(           \
      Domain<F> &, compiler::ConstraintSystemBuilder<S> &); \
  EXT template void compiler::lower_mod<F, S>(              \
      Domain<F> &, compiler::ConstraintSystemBuilder<S> &,  \
      compiler::ModSpec<F, S>);

// Every instance: SYS(S) for the field set S, DOM(F, RSF, S) for each
// domain its systems declare. A domain's compiler and lowerings are defined
// in instantiations/<set>__<field>.cc, the system's compile() in the file of
// the set's first domain.
#define GORDIEHOWE_INSTANCES(SYS, DOM)                                     \
  SYS(SetFp14_9)                                                           \
  DOM(Fp14_9, RsFp14_9, SetFp14_9)                                         \
  SYS(SetMod)                                                              \
  DOM(Fp64G4, RsGold4, SetMod)                                             \
  DOM(GF2_256<>, RsGf256, SetMod)                                          \
  DOM(GF2_128<>, RsGf128, SetMod)                                          \
  DOM(Fp14_9, RsFp14_9, SetMod)                                            \
  SYS(SetROMEmu)                                                        \
  DOM(GF2_128<>, RsGf128, SetROMEmu)                                    \
  DOM(Fp64G2, RsGold2, SetROMEmu)                                       \
  SYS(SetQROMEmu)                                                          \
  DOM(GF2_256<>, RsGf256, SetQROMEmu)                                      \
  DOM(Fp64G4, RsGold4, SetQROMEmu)                                         \
  SYS(SetROMMlDsa)                                                      \
  DOM(GF2_128<>, RsGf128, SetROMMlDsa)                                  \
  DOM(Fp24_6, RsFp24_6, SetROMMlDsa)                                    \
  SYS(SetQROMMlDsa)                                                        \
  DOM(GF2_256<>, RsGf256, SetQROMMlDsa)                                    \
  DOM(MlDsaField11, RsMlDsa11, SetQROMMlDsa)                               \
  SYS(SetROMFalconNative)                                               \
  DOM(GF2_128<>, RsGf128, SetROMFalconNative)                           \
  DOM(Fp14_9, RsFp14_9, SetROMFalconNative)                             \
  SYS(SetQROMFalconNative)                                                 \
  DOM(GF2_256<>, RsGf256, SetQROMFalconNative)                             \
  DOM(FalconField20, RsFalcon20, SetQROMFalconNative)                      \
  SYS(SetGold4Gf128Sha256)                                                 \
  DOM(Fp64G4, RsGold4, SetGold4Gf128Sha256)                                \
  SYS(SetGold4Gf128)                                                       \
  DOM(Fp64G4, RsGold4, SetGold4Gf128)                                      \
  SYS(SetGold4Gf256)                                                       \
  DOM(Fp64G4, RsGold4, SetGold4Gf256)                                      \
  DOM(GF2_256<>, RsGf256, SetGold4Gf256)                                   \
  SYS(SetGold4)                                                            \
  DOM(Fp64G4, RsGold4, SetGold4)                                           \
  SYS(SetGold2Sha256)                                                      \
  DOM(Fp64G2, RsGold2, SetGold2Sha256)                                     \
  SYS(SetGf128_3)                                                          \
  DOM(GF2_128<3>, RsGf128_3, SetGf128_3)                                   \
  SYS(SetGf128Sha256)                                                      \
  DOM(GF2_128<>, RsGf128, SetGf128Sha256)                                  \
  SYS(SetGf128)                                                            \
  DOM(GF2_128<>, RsGf128, SetGf128)                                        \
  SYS(SetGf256)                                                            \
  DOM(GF2_256<>, RsGf256, SetGf256)                                        \
  SYS(SetFalcon20)                                                         \
  DOM(FalconField20, RsFalcon20, SetFalcon20)                              \
  SYS(SetP256)                                                             \
  DOM(Fp256Base, RsP256, SetP256)                                          \
  SYS(SetMdoc)                                                             \
  DOM(GF2_128<>, RsGf128, SetMdoc)                                         \
  DOM(Fp256Base, RsP256, SetMdoc)                                         \
  SYS(SetROMFp128)                                                      \
  DOM(GF2_128<>, RsGf128, SetROMFp128)                                  \
  DOM(Fp128<>, RsFp128, SetROMFp128)                                    \
  SYS(SetROMComposite)                                                  \
  DOM(GF2_128<>, RsGf128, SetROMComposite)                              \
  DOM(Fp256Base, RsP256, SetROMComposite)                               \
  DOM(Fp24_6, RsFp24_6, SetROMComposite)                                \
  SYS(SetQROMComposite)                                                    \
  DOM(GF2_256<>, RsGf256, SetQROMComposite)                                \
  DOM(Fp256Base, RsP256, SetQROMComposite)                                 \
  DOM(MlDsaField11, RsMlDsa11, SetQROMComposite)                           \
  SYS(SetQROMEcdsa)                                                        \
  DOM(GF2_256<>, RsGf256, SetQROMEcdsa)                                    \
  DOM(Fp256Base, RsP256, SetQROMEcdsa)

// The declarations, for every including translation unit.
#define GORDIEHOWE_EXTERN_SYSTEM(S) \
  GORDIEHOWE_SYSTEM_INSTANCE(extern, instances::S)
#define GORDIEHOWE_EXTERN_DOMAIN(F, RSF, S)                            \
  GORDIEHOWE_DOMAIN_INSTANCE(extern, F, instances::RSF, instances::S) \
  GORDIEHOWE_LOWERING_INSTANCE(extern, F, instances::S)
namespace proofs::gordiehowe {
GORDIEHOWE_INSTANCES(GORDIEHOWE_EXTERN_SYSTEM, GORDIEHOWE_EXTERN_DOMAIN)
}  // namespace proofs::gordiehowe

#endif  // PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_INSTANCES_H_
