// Copyright 2026 Chad Sharp and Paul Grubbs
// SPDX-License-Identifier: Apache-2.0

// GordieHowe held-out programs: the setup they share.
//
// The held-out programs test whether the Lean validity checking of the
// realized programs generalizes beyond the applications it was built
// around. Each is a relation a new user of the language could write, in
// the public language and the standard library only, at the ROM parameters
// (ROMParams). This header holds the fields and Reed-Solomon factories, the
// domains' default profiles (examples/shared/domain_profile.h), the compile
// profile, the plan export of a compiled program and a prover that may
// cheat (a tampered value, or the honest prover's check off).
//
// The field sets are those instances.h instantiates:
//   SetGf128Sha256      GF(2^128)
//   SetGold2Sha256      Goldilocks^2
//   SetROMEmu           GF(2^128) and Goldilocks^2
//   SetFp14_9           F_q^9, q = 12289

#ifndef PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_HELDOUT_HELDOUT_ENV_H_
#define PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_HELDOUT_HELDOUT_ENV_H_

#include <cstddef>
#include <cstdint>
#include <functional>
#include <stdexcept>
#include <string>
#include <type_traits>
#include <utility>
#include <vector>

#include "algebra/fp14.h"
#include "algebra/fp14_n.h"
#include "algebra/fp_goldilocks.h"
#include "algebra/reed_solomon_extension_n.h"
#include "algebra/reed_solomon_fp.h"
#include "gf2k/gf2_128.h"
#include "gf2k/lch14_reed_solomon.h"
#include "gordiehowe/compiler/plan_export.h"
#include "gordiehowe/examples/shared/domain_profile.h"
#include "gordiehowe/examples/shared/program_testing.h"
#include "gordiehowe/examples/shared/setup.h"
#include "gordiehowe/gordiehowe.h"
#include "gordiehowe/instances.h"
#include "gordiehowe/relation.h"
#include "params/param_sets.h"
#include "random/secure_random_engine.h"
#include "util/optimization_options.h"

namespace proofs::gordiehowe::heldout {

using P = param_sets::ROMParams;
using Hash = P::ProtocolHash;
// GF(2^128) with its GF(2^16) subfield.
using HF = GF2_128<>;
// Goldilocks^2, its prime subfield F_p, p = 2^64 - 2^32 + 1.
using GF = Fp64G2;
// F_q^9, q = 12289 (Falcon's field), its prime subfield F_q.
using QF = Fp14_9;

using RSH = LCH14ReedSolomonFactory<HF>;
using RSG = BasicFpReedSolomon<GF>;
using RSQ = ReedSolomonExtensionNFactory<QF>;

// The systems of the field sets the programs use.
using BinarySys = ConstraintSystem<Hash, HF>;
using GoldSys = ConstraintSystem<Hash, GF>;
using MixedSys = ConstraintSystem<Hash, HF, GF>;
using SmallSys = ConstraintSystem<Hash, QF>;

constexpr uint64_t kGoldilocksP = 0xFFFFFFFF00000001ull;
constexpr uint64_t kSmallQ = 12289;

// The fields and their encoders, shared by every program; they outlive
// every system.
struct Fields {
  HF hf;
  RSH rsh{hf};
  GF gf;
  RSG rsg{gf};
  Fp14 qbase{kSmallQ};
  QF qf{qbase, QF::beta_};
  RSQ rsq{qbase, OptimizationOptions::optimized()};
};
inline const Fields &fields() {
  static const Fields *f = new Fields;
  return *f;
}

// The domains' default profiles at the ROM parameters.
inline auto binary_profile() {
  return examples::domain_profile<P>(fields().hf, fields().rsh);
}
inline auto gold_profile() {
  return examples::domain_profile<P>(fields().gf, fields().rsg.factory());
}
inline auto small_profile() {
  return examples::domain_profile<P>(fields().qf, fields().rsq);
}

// The compile profile of program NAME: version 1, the MAC basis of
// GF(2^128).
inline CompileProfile compile_profile(const std::string &name) {
  return examples::mac_profile<P>("heldout-" + name);
}

// The plan export of the compiled program C as the Lean configuration
// GordieHowe.Generated.Heldout.<LEAN>.ROMParams, written under DIR with its
// realized program and proof modules (examples::write_plan). Returns the
// plan module's path.
template <class C>
std::string export_program(const C &c, const std::string &dir,
                           const std::string &config, const std::string &lean,
                           const std::string &commit,
                           const std::string &run_id = "heldout") {
  compiler::ExportMeta meta{"heldout-" + config, P::kId, commit, run_id, 0};
  meta.lean_name = "Heldout." + lean + "." + compiler::lean_param_set(P::kId);
  return examples::write_plan(c, dir, meta);
}

// The realized program of C (compiler::build_program), for the export
// tests' structural checks.
template <class C>
compiler::ProgramData program_of(const C &c, const std::string &config) {
  compiler::ExportMeta meta{"heldout-" + config, P::kId, "test", "test", 0};
  meta.lean_name = "Heldout.Test." + compiler::lean_param_set(P::kId);
  return compiler::build_program(c, meta);
}

// A tamper of a compiled system C's prover (ProveOptions::tamper).
template <class C>
using TamperOf = decltype(std::declval<typename C::ProveOptions>().tamper);

// Proves WITNESS against STATEMENT on the compiled system C and verifies.
// A cheating prover (TAMPER changes a generator's output, or CHEATING: a
// witness that does not satisfy the relation) proves with the honest
// prover's check off; a proof the prover refuses is a rejection.
template <class C, class A>
bool proves(const C &c, const A &statement, const A &witness,
            TamperOf<C> tamper = nullptr, bool cheating = false) {
  auto prep = c.prepare(statement);
  typename C::ProveOptions opt;
  opt.require_satisfied = !cheating && !tamper;
  opt.tamper = std::move(tamper);
  SecureRandomEngine rng;
  try {
    return prep.verify(prep.prove(witness, rng, opt));
  } catch (const std::runtime_error &) {
    return false;
  }
}

// A tamper that adds 1 to coordinate K of node ID (a value of field F).
template <class S, class F>
std::function<void(size_t, typename S::Value &)> bump(const F &f, size_t id,
                                                      size_t k) {
  return [&f, id, k](size_t at, typename S::Value &v) {
    if (at != id) return;
    auto &x = S::template get<F>(v);
    f.add(x.at(k), f.one());
  };
}

// The node of the compiled system C named NAME; an error when there is
// none.
template <class C>
size_t node_named(const C &c, const std::string &name) {
  for (size_t id = 0; id < c.nodes().size(); ++id)
    if (c.nodes()[id].name == name) return id;
  throw std::runtime_error("no node named " + name);
}

}  // namespace proofs::gordiehowe::heldout

#endif  // PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_HELDOUT_HELDOUT_ENV_H_
