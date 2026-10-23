// Copyright 2026 Chad Sharp and Paul Grubbs
// SPDX-License-Identifier: Apache-2.0

// GordieHowe tests (gordiehowe_lowering_test*.cc, one binary): the
// fields, profiles and helpers they share. Each test file has its own copy
// (anonymous namespace).

#ifndef PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_TESTS_GORDIEHOWE_LOWERING_TEST_H_
#define PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_TESTS_GORDIEHOWE_LOWERING_TEST_H_

#include <algorithm>
#include <cstddef>
#include <cstdint>
#include <cstdio>
#include <memory>
#include <set>
#include <string>
#include <vector>

#include "algebra/fp_goldilocks4.h"
#include "algebra/reed_solomon_fp.h"
#include "gf2k/gf2_256.h"
#include "gf2k/lch14_reed_solomon.h"
#include "gordiehowe/compile_error_testing.h"
#include "gordiehowe/instances.h"
#include "gordiehowe/lib/cutoff_select.h"
#include "gordiehowe/system.h"
#include "gtest/gtest.h"
#include "random/secure_random_engine.h"

namespace proofs::gordiehowe {
namespace {


using AF = Fp64G4;
using AElt = AF::Elt;
using AV = std::vector<AElt>;
using RSA = BasicFpReedSolomon<AF>;
using HF = GF2_256<>;
using HElt = HF::Elt;
using HV = std::vector<HElt>;
using RSH = LCH14ReedSolomonFactory<HF>;

// Every system of these tests lists the two fields.
using Sys = ConstraintSystem<SHA384, AF, HF>;
using SysValue = Sys::Value;
using Assignment = Sys::Assignment;
using ProveOptions = Sys::ProveOptions;
using CompiledSystem = Sys::Compiled;

constexpr Bound kP = (Bound(1) << 64) - (Bound(1) << 32) + 1;

struct Env {
  AF af;
  RSA rsa{af};
  HF hf;
  RSH rsh{hf};
  DomainProfile<AF, RSA::Factory, SHA384> a_profile() const {
    DomainProfile<AF, RSA::Factory, SHA384> p;
    p.f = &af;
    p.rsf = &rsa.factory();
    p.field_name = "Goldilocks^4";
    p.rate = 4;
    p.nreq = 64;
    const RSA *r = &rsa;
    p.block_enc = [r](const Circuit<AF> &, size_t nw, size_t nq) {
      return r->block_enc<SHA384>("gordiehowe", nw, nq, 4, 64);
    };
    p.has_subfield = true;
    p.prime = Space::kSubfield;
    return p;
  }
  DomainProfile<HF, RSH, SHA384> h_profile() const {
    DomainProfile<HF, RSH, SHA384> p;
    p.f = &hf;
    p.rsf = &rsh;
    p.field_name = "GF(2^256)";
    p.rate = 4;
    p.nreq = 64;
    p.has_subfield = true;
    p.prime = Space::kPrime;
    return p;
  }
};
const Env &env() {
  static const Env *e = new Env;
  return *e;
}
const AF &af() { return env().af; }
const HF &hf() { return env().hf; }

// 4096 private values of A below 2048: with them, a table of 2048 rows
// serves A's other range checks (the planner weighs its rows against 4096
// needles), as a test of one realization at a time needs. Their witness is
// zeros (zero_fill).
inline Ref<AF> fill_2048(Domain<AF> &A) {
  auto f = A.priv(Subfield{}, "fill", 4096);
  assert_range(f, 2048, "fill");
  return f;
}
inline void zero_fill(Assignment &w, Ref<AF> fill) {
  w.set(fill, AV(4096, af().zero()));
}

// The compiler tier, for tests of bound views and of the GKR circuit
// itself (its token circuits, the wires a view reads).
struct L : compiler::Lowering {
  using compiler::Lowering::bind_view;
  using compiler::Lowering::gkr;
};


size_t id_of(const Sys &cs, const std::string &name) {
  const auto &N = cs.graph().nodes;
  for (size_t i = 0; i < N.size(); ++i)
    if (N[i].name == name) return i;
  ADD_FAILURE() << "no node " << name;
  return SIZE_MAX;
}

AV avec(std::initializer_list<uint64_t> v) {
  AV out;
  for (uint64_t x : v) out.push_back(af().of_scalar(x));
  return out;
}

// The cheating prover under TAMPER completes its proof, and the verifier
// rejects it.
template <class Tamper>
bool verifier_rejects(const CompiledSystem &c, const Assignment &st,
                      const Assignment &w, Tamper tamper) {
  auto prep = c.prepare(st);
  ProveOptions opt;
  opt.tamper = tamper;
  opt.require_satisfied = false;
  SecureRandomEngine rng;
  std::vector<uint8_t> proof;
  try {
    proof = prep.prove(w, rng, opt);
  } catch (const std::runtime_error &e) {
    ADD_FAILURE() << "the cheating prover stopped: " << e.what();
    return false;
  }
  return !prep.verify(proof);
}
bool honest(const CompiledSystem &c, const Assignment &st, const Assignment &w) {
  auto prep = c.prepare(st);
  SecureRandomEngine rng;
  return prep.verify(prep.prove(w, rng));
}
// Whether the honest prover's satisfaction check refuses under TAMPER.
template <class Tamper>
bool prover_refuses(const CompiledSystem &c, const Assignment &st,
                    const Assignment &w, Tamper tamper) {
  auto prep = c.prepare(st);
  ProveOptions opt;
  opt.tamper = tamper;
  SecureRandomEngine rng;
  try {
    prep.prove(w, rng, opt);
  } catch (const std::runtime_error &) {
    return true;
  }
  return false;
}
// A tamper that sets coordinate I of node ID to V.
auto set_at(size_t id, size_t i, AElt v) {
  return [id, i, v](size_t at, SysValue &x) {
    if (at == id) std::get<AV>(x).at(i) = v;
  };
}


}  // namespace
}  // namespace proofs::gordiehowe

#endif  // PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_TESTS_GORDIEHOWE_LOWERING_TEST_H_
