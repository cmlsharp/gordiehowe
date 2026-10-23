// Copyright 2026 Chad Sharp and Paul Grubbs
// SPDX-License-Identifier: Apache-2.0

// GordieHowe: the placement rule (placement.h) on
// small domains of the profiles' fields, and the microbench of its rates.
//
//   Rule.PackedOdd        F_q^6 (relatively packed, odd): Boolean checks
//                         and a degree-2 predicate go to the circuit or a
//                         field batch by the rates, in a shallow and a deep
//                         circuit; the check is in the input layer either
//                         way (3 terms per bit)
//   Rule.UnpackedOdd      F_p256 (no relative packing): triples or the
//                         circuit by the rates; a batch is inadmissible
//   Rule.PackedBinary     GF(2^128): Bit cells need no check; a degree-2
//                         predicate on GF(2^16) cells goes to a batch or
//                         the circuit, one on Field cells to triples or the
//                         circuit
//   Rule.ManyTriplesProve the quadratic test's challenges get their own
//                         stream grant
//   Rule.Pins             pins override the rates; inadmissible pins are
//                         CompileErrors
//   Rule.UnitRates        a profile without measured rates costs every
//                         unit 1
//   Rule.ProfileRates     the flagship profiles' fields have rates
//   Rule.Batched*         a predicate placed in a field batch is proved and
//                         a wrong witness is rejected
//
//   DISABLED_Rates        the microbench of the rates, per profile field:
//                         PLACEMENT_POINT lines, which a fit outside this
//                         repository turns into
//                         lib/params/placement_rates_measured.h.
//                         GH_PLACEMENT_REPS proofs per point (default 7)
//                         after GH_PLACEMENT_WARMUP (default 1);
//                         GH_PLACEMENT_SIZES the instance counts (default
//                         256,4096,16384), GH_PLACEMENT_TRIPLE_SIZES the
//                         triples' (default 256,1024);
//                         GH_PLACEMENT_WIDTHS_BIT, _SUB and
//                         _FIELD the batches' skip widths (default 16, 4,
//                         4); GH_PLACEMENT_PARTS and GH_PLACEMENT_PART_N
//                         the merged predicate counts of the part series
//                         and their instances (default 1,4,16,64,256 at
//                         16384); GH_PLACEMENT_REQUESTS the rate run's
//                         request scan, whose degrees each evaluator
//                         measures (else GH_PLACEMENT_DEGREES, default
//                         2,3); GH_PLACEMENT_HIGH_DEGREE and _HIGH_N the
//                         degree from which batch series stop at N
//                         instances (16, 8192); GH_PLACEMENT_FIELDS
//                         (default all) selects
//                         ml-dsa,falcon,emulated,hash,p256,fp128 (P256 and
//                         Fp128: the ROM parameters only; Fp128 at the RSA
//                         system's A under ROMParamsFp128); GH_PLACEMENT_PART one part of a
//                         field's series ("base" or
//                         "<evaluator>:<degree>"). Every check's point is
//                         timed in pairs with its bare cells (Point)
//   DISABLED_PrintRates   the compiled rate table of every profile field

#include <algorithm>
#include <array>
#include <chrono>
#include <cstdio>
#include <cstdlib>
#include <memory>
#include <random>
#include <string>
#include <type_traits>
#include <vector>

#include "bench/timing.h"
#include "params/param_sets.h"
#include "gordiehowe/compiler/op_counts.h"
#include "gordiehowe/examples/falcon/falcon_emulated.h"
#include "gordiehowe/examples/falcon/falcon_native.h"
#include "gordiehowe/examples/instances.h"
#include "gordiehowe/examples/mldsa/mldsa_native.h"
#include "gordiehowe/examples/p256/p256_testing.h"
#include "gordiehowe/examples/shared/setup.h"
#include "gtest/gtest.h"
#include "params/param_sets_testing.h"
#include "random/secure_random_engine.h"

namespace proofs::gordiehowe {
namespace {

// The examples' profiles and list-radius choices.
using namespace ::proofs::gordiehowe::examples;  // NOLINT

using ROMParams = param_sets::ROMParams;

// The packing chains the profile fields' domains weigh, all at one cost,
// so each tree keeps its default chain: the tests' rates and the
// microbench's, whose trees are the default ones.
compiler::StageRates equal_chains() {
  compiler::StageRates s;
  for (const std::vector<size_t> &c : std::vector<std::vector<size_t>>{
           {1, 4}, {1, 2, 4}, {1, 6}, {1, 2, 6}, {1, 3, 6}, {1, 9},
           {1, 3, 9}, {1, 4, 20}, {1, 20}, {1, 2, 20}, {1, 5, 20},
           {1, 10, 20}, {16, 128}, {16, 32, 128}, {16, 64, 128},
           {16, 256}, {16, 32, 256}, {16, 64, 256}})
    s.chains.push_back({c, 1, 1, 1, 1, 1, 1});
  return s;
}

// Rates that make one target cheap: CIRCUIT, BATCH or TRIPLE costs 1 per
// unit, the others 1000; every packing chain costs the same.
compiler::PlacementRates synthetic(Placement cheap) {
  compiler::PlacementRates r;
  r.source = "synthetic";
  r.stage = equal_chains();
  const double lo = 1, hi = 1000;
  r.gkr_term = cheap == Placement::kCircuit ? lo : hi;
  r.commit_full = cheap == Placement::kQuadratic ? lo : hi;
  r.triple = cheap == Placement::kQuadratic ? lo : hi * 10;
  const double b = cheap == Placement::kBatch ? lo : hi * 10;
  using E = compiler::BatchEval;
  for (E e : {E::kSubfield, E::kField, E::kBitSliced})
    r.batch.push_back({e, b, b, b, b, b, b, b, b, b, b, b, b});
  return r;
}

template <class C>
bool has(const C &c, const std::string &s) {
  return c->report().find(s) != std::string::npos;
}

// ------------------------------------------------------- packed, odd --
// ML-DSA's A field at the ROM parameters, F_q^6 (DomainProfile::prime = kSubfield).
using MEnv = examples::mldsa::Env<ROMParams>;
using MSys = MEnv::Sys;
using AF = MEnv::AF;
using AV = std::vector<AF::Elt>;

// B: Bit cells [n]; x, y: Subfield cells [n] with the predicate
// (x - y)(x + y - 5) = 0 ("quad"). DEEP adds a pinned circuit predicate of
// depth 4 on d (d0 d1 d2 ... d15 = d0 for d all ones).
struct PackedOdd {
  MSys cs{"gh-placement-packed-odd"};
  Ref<AF, Bit, Committed> b;
  Ref<AF, Subfield<>, Committed> x, y, d;
  Predicate quad;
  PackedOdd(const MEnv &env, const compiler::PlacementRates &rates, size_t n,
            bool deep, Placement bit_pin = Placement::kAuto) {
    auto p = examples::domain_profile<ROMParams>(env.af, env.rsa);
    p.rates = rates;
    auto &A = cs.domain(p, "A");
    A.pin_bit_checks(bit_pin);
    b = A.priv(Bit{}, "b", n);
    x = A.priv(Subfield{}, "x", n);
    y = A.priv(Subfield{}, "y", n);
    quad = assert_zero((x - y) * (x + y - 5), "quad");
    d = A.priv(Subfield{}, "d", 16);
    if (deep) {
      auto e = d.reindex({0}) * d.reindex({1});
      for (size_t i = 2; i < 16; ++i) e = e * d.reindex({i});
      assert_zero(e - d.reindex({0}), "deep").pin(Placement::kCircuit);
    } else {
      assert_zero(d.reindex({0}) * d.reindex({0}) - d.reindex({0}), "shallow")
          .pin(Placement::kCircuit);
    }
  }
  MSys::Assignment witness(const AF &f, size_t n, bool wrong_quad = false,
                           bool wrong_bit = false) const {
    AV bv(n), xv(n), yv(n);
    for (size_t i = 0; i < n; ++i) {
      bv[i] = (i % 3) ? f.one() : f.zero();
      xv[i] = f.of_scalar(i % 7);
      // x = y, or x + y = 5 for odd i.
      yv[i] = (i % 2) ? f.subf(f.of_scalar(5), xv[i]) : xv[i];
    }
    if (wrong_quad) yv[4] = f.addf(yv[4], f.one());
    if (wrong_bit) bv[2] = f.of_scalar(2);
    MSys::Assignment w;
    w.set(b, bv).set(x, xv).set(y, yv).set(d, AV(16, f.one()));
    return w;
  }
};

template <class C, class W>
bool proves(const C &c, const W &w, bool cheating) {
  auto prep = c->prepare(typename std::decay_t<decltype(*c)>::Assignment{});
  typename std::decay_t<decltype(*c)>::ProveOptions opt;
  opt.require_satisfied = !cheating;
  SecureRandomEngine rng;
  try {
    return prep.verify(prep.prove(w, rng, opt));
  } catch (const std::runtime_error &e) {
    if (!cheating) std::printf("PROVES_ERROR %s\n", e.what());
    return false;
  }
}

TEST(Rule, PackedOdd) {
  const MEnv env;
  const size_t n = 64;
  for (bool deep : {false, true}) {
    SCOPED_TRACE(deep ? "deep" : "shallow");
    for (Placement cheap : {Placement::kCircuit, Placement::kBatch}) {
      SCOPED_TRACE(placement_name(cheap));
      PackedOdd t(env, synthetic(cheap), n, deep);
      const auto c = compile(t.cs);
      const std::string want =
          cheap == Placement::kBatch ? "field batch" : "circuit";
      // The circuit is the default; another target is the cheapest.
      const std::string why =
          cheap == Placement::kCircuit ? " (default; " : " (cheapest; ";
      EXPECT_TRUE(has(c, "Boolean checks n=64: " + want + why))
          << c->report();
      EXPECT_TRUE(has(c, "assert_zero 'quad' n=64: " + want + why))
          << c->report();
      // The checks' terms do not depend on the depth: 3 per bit.
      EXPECT_TRUE(has(c, "circuit 0.") || has(c, "circuit "));
      EXPECT_TRUE(has(c, "(192 terms,")) << c->report();
      // Triples are inadmissible on packed cells.
      EXPECT_TRUE(has(c, "quadratic triples: relatively packed subfield "
                         "cells"))
          << c->report();
      if (cheap == Placement::kBatch) {
        EXPECT_TRUE(has(c, "batch A.boolean")) << c->report();
        EXPECT_TRUE(has(c, "batch quad")) << c->report();
        EXPECT_TRUE(has(c, " cell_bit_checks=0 ")) << c->report();
      } else {
        EXPECT_TRUE(has(c, " cell_bit_checks=64 ")) << c->report();
      }
      EXPECT_TRUE(proves(c, t.witness(env.af, n), false));
      EXPECT_FALSE(proves(c, t.witness(env.af, n, true, false), true));
      EXPECT_FALSE(proves(c, t.witness(env.af, n, false, true), true));
    }
  }
}

// ------------------------------------------------------ unpacked, odd --
// F_p256: no relative packing. b: Bit cells; u, v, w: Field cells with the
// triple-form predicate u v - w ("tri").
struct UnpackedOdd {
  using Sys = examples::mdoc::p256_testing::Sys;
  using F = examples::mdoc::p256_testing::F;
  Sys cs{"gh-placement-unpacked-odd"};
  Ref<F, Bit, Committed> b;
  Ref<F, Field, Committed> u, v, w;
  UnpackedOdd(const compiler::PlacementRates &rates, size_t n,
              Placement bit_pin = Placement::kAuto,
              Placement tri_pin = Placement::kAuto) {
    auto p = examples::mdoc::p256_testing::profile();
    p.rates = rates;
    auto &A = cs.domain(p, "A");
    A.pin_bit_checks(bit_pin);
    b = A.priv(Bit{}, "b", n);
    u = A.priv(Field{}, "u", n);
    v = A.priv(Field{}, "v", n);
    w = A.priv(Field{}, "w", n);
    assert_zero(u * v - w, "tri").pin(tri_pin);
    assert_zero(u.reindex({0}) * v.reindex({0}) - w.reindex({0}), "anchor")
        .pin(Placement::kCircuit);
  }
  Sys::Assignment witness(size_t n, bool wrong_bit = false) const {
    const F &f = examples::mdoc::p256_testing::fp();
    examples::mdoc::p256_testing::Vec bv(n), uv(n), vv(n), wv(n);
    for (size_t i = 0; i < n; ++i) {
      bv[i] = (i % 2) ? f.one() : f.zero();
      uv[i] = f.of_scalar(i + 2);
      vv[i] = f.of_scalar(3 * i + 1);
      wv[i] = f.mulf(uv[i], vv[i]);
    }
    if (wrong_bit) bv[1] = f.of_scalar(3);
    Sys::Assignment a;
    a.set(b, bv).set(u, uv).set(v, vv).set(w, wv);
    return a;
  }
};

TEST(Rule, UnpackedOdd) {
  const size_t n = 32;
  for (Placement cheap : {Placement::kCircuit, Placement::kQuadratic}) {
    SCOPED_TRACE(placement_name(cheap));
    UnpackedOdd t(synthetic(cheap), n);
    const auto c = compile(t.cs);
    const std::string want = placement_name(cheap);
    const std::string why =
        cheap == Placement::kCircuit ? " (default; " : " (cheapest; ";
    EXPECT_TRUE(has(c, "Boolean checks n=32: " + want + why))
        << c->report();
    EXPECT_TRUE(has(c, "assert_zero 'tri' n=32: " + want + why))
        << c->report();
    // The Boolean checks admit no batch without relative packing.
    EXPECT_TRUE(has(c, "field batch: no relative packing")) << c->report();
    EXPECT_TRUE(proves(c, t.witness(n), false));
    EXPECT_FALSE(proves(c, t.witness(n, true), true));
  }
  // The predicate on Field cells admits a batch (the full-field
  // evaluator); the Boolean checks still do not.
  UnpackedOdd t(synthetic(Placement::kBatch), n);
  const auto c = compile(t.cs);
  EXPECT_TRUE(has(c, "assert_zero 'tri' n=32: field batch (")) << c->report();
  EXPECT_FALSE(has(c, "Boolean checks n=32: field batch (")) << c->report();
  EXPECT_TRUE(proves(c, t.witness(n), false));
  EXPECT_FALSE(proves(c, t.witness(n, true), true));
}

// A batch the measured rates have no rate for takes no part in the
// automatic choice, and a pin to it still compiles and proves: on F_q^6
// with its batch rates removed (the rule is general), and on F_p256 at the
// shipped rates, which hold no F_p256 batch rate.
TEST(Rule, NoRates) {
  const MEnv env;
  {
    compiler::PlacementRates r = synthetic(Placement::kBatch);
    r.batch.clear();
    PackedOdd t(env, r, 16, false);
    const auto c = compile(t.cs);
    EXPECT_TRUE(has(c, "assert_zero 'quad' n=16: circuit (default; "))
        << c->report();
    EXPECT_TRUE(has(c, "batch: no rates")) << c->report();
    EXPECT_TRUE(proves(c, t.witness(env.af, 16), false));
    PackedOdd t2(env, r, 16, false);
    t2.quad.pin(Placement::kBatch);
    const auto c2 = compile(t2.cs);
    EXPECT_TRUE(has(c2, "assert_zero 'quad' n=16: field batch (pinned"))
        << c2->report();
    EXPECT_TRUE(proves(c2, t2.witness(env.af, 16), false));
    EXPECT_FALSE(proves(c2, t2.witness(env.af, 16, true, false), true));
  }
  {
    const compiler::PlacementRates r =
        param_sets::placement_rates<ROMParams::EcdsaField>();
    EXPECT_TRUE(r.batch.empty());
    UnpackedOdd t(r, 32);
    const auto c = compile(t.cs);
    EXPECT_FALSE(has(c, "assert_zero 'tri' n=32: field batch ("))
        << c->report();
    EXPECT_TRUE(has(c, "batch: no rates")) << c->report();
    EXPECT_TRUE(proves(c, t.witness(32), false));
    UnpackedOdd t2(r, 32, Placement::kAuto, Placement::kBatch);
    const auto c2 = compile(t2.cs);
    EXPECT_TRUE(has(c2, "assert_zero 'tri' n=32: field batch (pinned"))
        << c2->report();
    EXPECT_TRUE(proves(c2, t2.witness(32), false));
    EXPECT_FALSE(proves(c2, t2.witness(32, true), true));
  }
}

// ------------------------------------------------------ packed, binary --
// GF(2^128) (ML-DSA's H at the ROM parameters): x, y, z GF(2^16) cells with x y - z
// ("sub"); u, v, w Field cells with u v - w ("full"); Bit cells b, which
// relative packing makes Boolean.
struct PackedBinary {
  using HF = MEnv::HF;
  using HV = std::vector<HF::Elt>;
  MSys cs{"gh-placement-packed-binary"};
  Ref<HF, Bit, Committed> b;
  Ref<HF, Subfield<>, Committed> x, y, z;
  Ref<HF, Field, Committed> u, v, w;
  PackedBinary(const MEnv &env, const compiler::PlacementRates &rates,
               size_t n) {
    auto p = examples::domain_profile<ROMParams>(env.hf, env.rsh);
    p.rates = rates;
    auto &H = cs.domain(p, "H");
    b = H.priv(Bit{}, "b", n);
    x = H.priv(Subfield{}, "x", n);
    y = H.priv(Subfield{}, "y", n);
    z = H.priv(Subfield{}, "z", n);
    u = H.priv(Field{}, "u", n);
    v = H.priv(Field{}, "v", n);
    w = H.priv(Field{}, "w", n);
    assert_zero(x * y - z, "sub");
    assert_zero(u * v - w, "full");
    assert_zero(u.reindex({0}) * v.reindex({1}) - w.reindex({2}), "anchor")
        .pin(Placement::kCircuit);
  }
  MSys::Assignment witness(const HF &f, size_t n, bool wrong = false) const {
    HV bv(n), xv(n), yv(n), zv(n), uv(n, f.one()), vv(n, f.one()),
        wv(n, f.one());
    for (size_t i = 0; i < n; ++i) {
      bv[i] = (i % 2) ? f.one() : f.zero();
      xv[i] = (i % 3) ? f.one() : f.zero();
      yv[i] = (i % 5) ? f.one() : f.zero();
      zv[i] = f.mulf(xv[i], yv[i]);
    }
    if (wrong) zv[4] = f.addf(zv[4], f.one());
    MSys::Assignment a;
    a.set(b, bv).set(x, xv).set(y, yv).set(z, zv);
    a.set(u, uv).set(v, vv).set(w, wv);
    return a;
  }
};

// Batches of many instances, every evaluator of a binary field: honest
// proofs verify, a wrong cell is rejected.
// Ligero's quadratic test draws 3 nq + ceil(nq / w) challenges from the
// point of its linear test, which grants them stream (gen_alphaq,
// gen_uquad): 4096 triples on F_p256 (and as many Boolean checks) draw
// about 800 KB, beyond the fixed budget of about 200 KB, and prove.
TEST(Rule, ManyTriplesProve) {
  const size_t n = 4096;
  UnpackedOdd t(synthetic(Placement::kCircuit), n, Placement::kQuadratic,
                Placement::kQuadratic);
  const auto c = compile(t.cs);
  EXPECT_TRUE(has(c, "assert_zero 'tri' n=4096: quadratic triples (pinned)"))
      << c->report();
  EXPECT_TRUE(proves(c, t.witness(n), false));
  EXPECT_FALSE(proves(c, t.witness(n, true), true));
}

TEST(Rule, LargeBatches) {
  const MEnv env;
  for (size_t n : {size_t(256), size_t(320), size_t(384), size_t(512),
                   size_t(640), size_t(768), size_t(1024), size_t(4096)}) {
    SCOPED_TRACE(n);
    PackedBinary t(env, synthetic(Placement::kBatch), n);
    const auto c = compile(t.cs);
    EXPECT_TRUE(has(c, "assert_zero 'sub' n=" + std::to_string(n) +
                           ": field batch"))
        << c->report();
    EXPECT_TRUE(proves(c, t.witness(env.hf, n), false)) << c->report();
    EXPECT_FALSE(proves(c, t.witness(env.hf, n, true), true));
  }
}

TEST(Rule, PackedBinary) {
  const MEnv env;
  const size_t n = 32;
  for (Placement cheap :
       {Placement::kCircuit, Placement::kBatch, Placement::kQuadratic}) {
    SCOPED_TRACE(placement_name(cheap));
    PackedBinary t(env, synthetic(cheap), n);
    const auto c = compile(t.cs);
    EXPECT_FALSE(has(c, "Boolean checks n=")) << c->report();
    const std::string sub = cheap == Placement::kBatch ? "field batch"
                                                       : "circuit";
    // Field cells admit a batch too (the full-field evaluator).
    const std::string full = cheap == Placement::kQuadratic ? "quadratic triples"
                             : cheap == Placement::kBatch   ? "field batch"
                                                            : "circuit";
    EXPECT_TRUE(has(c, "assert_zero 'sub' n=32: " + sub)) << c->report();
    EXPECT_TRUE(has(c, "assert_zero 'full' n=32: " + full)) << c->report();
    EXPECT_TRUE(proves(c, t.witness(env.hf, n), false));
    EXPECT_FALSE(proves(c, t.witness(env.hf, n, true), true));
  }
}

// ---------------------------------------------------------------- pins --
TEST(Rule, Pins) {
  const MEnv env;
  {
    // Boolean checks pinned to the circuit although the batch is cheaper.
    PackedOdd t(env, synthetic(Placement::kBatch), 16, false,
                Placement::kCircuit);
    t.quad.pin(Placement::kCircuit);
    const auto c = compile(t.cs);
    EXPECT_TRUE(has(c, "Boolean checks n=16: circuit (pinned")) << c->report();
    EXPECT_TRUE(has(c, "assert_zero 'quad' n=16: circuit (pinned)"))
        << c->report();
    EXPECT_TRUE(proves(c, t.witness(env.af, 16), false));
  }
  {
    // And to a batch although the circuit is cheaper.
    PackedOdd t(env, synthetic(Placement::kCircuit), 16, false,
                Placement::kBatch);
    t.quad.pin(Placement::kBatch);
    const auto c = compile(t.cs);
    EXPECT_TRUE(has(c, "Boolean checks n=16: field batch (pinned"))
        << c->report();
    EXPECT_TRUE(has(c, "assert_zero 'quad' n=16: field batch (pinned"))
        << c->report();
    EXPECT_TRUE(proves(c, t.witness(env.af, 16), false));
    EXPECT_FALSE(proves(c, t.witness(env.af, 16, true, false), true));
  }
  {
    // Triples on packed cells: refused.
    PackedOdd t(env, synthetic(Placement::kCircuit), 16, false,
                Placement::kQuadratic);
    EXPECT_THROW((void)compile(t.cs), CompileError);
  }
  {
    // Boolean checks pinned to a batch without relative packing: refused.
    // A predicate on Field cells pinned to one: a full-field batch.
    UnpackedOdd t(synthetic(Placement::kCircuit), 8, Placement::kBatch);
    EXPECT_THROW((void)compile(t.cs), CompileError);
    UnpackedOdd t2(synthetic(Placement::kCircuit), 8, Placement::kAuto,
                   Placement::kBatch);
    const auto c2 = compile(t2.cs);
    EXPECT_TRUE(has(c2, "assert_zero 'tri' n=8: field batch (pinned"))
        << c2->report();
    EXPECT_TRUE(proves(c2, t2.witness(8), false));
  }
  {
    // Triples pinned on F_p256 although the circuit is cheaper.
    UnpackedOdd t(synthetic(Placement::kCircuit), 8, Placement::kQuadratic,
                  Placement::kQuadratic);
    const auto c = compile(t.cs);
    EXPECT_TRUE(has(c, "Boolean checks n=8: quadratic triples (pinned"))
        << c->report();
    EXPECT_TRUE(has(c, "assert_zero 'tri' n=8: quadratic triples (pinned)"))
        << c->report();
    EXPECT_TRUE(proves(c, t.witness(8), false));
  }
}

// A profile without measured rates costs every unit 1
// (PlacementRates::unit): 16 packed Boolean checks cost 48 quad terms in
// the circuit against a batch of 1 + 16, so the batch; on F_p256 they cost
// 16 triples against 48 terms, so triples; 'tri' costs 16 triples against
// 32 terms or a batch of 1 + 16 * 3.
// The skip's operation counts (op_counts.h): the parts solved from small
// sizes give the kernel's counts at any size exactly, field operands and
// both bit-sliced kernels.
template <class F, class Hash>
void expect_exact_skip_counts(const F &f, compiler::SkipKind kind,
                              unsigned width, std::vector<size_t> units) {
  using CF = compiler::CountingField<F>;
  const CF cf(f);
  compiler::FieldRelation<CF> rel;
  rel.name = "x y - z";
  rel.operands = 3;
  rel.monomials = {{f.one(), {0, 1}}, {f.mone(), {2}}};
  if (kind != compiler::SkipKind::kField)
    rel.monomials = {{f.one(), {0, 1}}, {f.one(), {2}}};
  for (size_t u : units) {
    const auto x = compiler::skip_ops<F, Hash>(cf, rel, kind, u, width);
    const auto y = compiler::op_counts_internal::skip_at<F, Hash>(
        cf, rel, kind, u, width);
    EXPECT_EQ(x.mul, y.mul) << u;
    EXPECT_EQ(x.add, y.add) << u;
    EXPECT_EQ(x.mac, y.mac) << u;
    EXPECT_EQ(x.reduce, y.reduce) << u;
    EXPECT_EQ(x.inv, y.inv) << u;
  }
}

TEST(OpCounts, DISABLED_PrintSkipCounts) {
  using P = ROMParams;
  const examples::mldsa::Env<P> env;
  using Hash = typename P::ProtocolHash;
  using F = std::decay_t<decltype(env.af)>;
  using CF = compiler::CountingField<F>;
  const CF cf(env.af);
  compiler::FieldRelation<CF> rel;
  rel.operands = 3;
  rel.monomials = {{env.af.one(), {0, 1}}, {env.af.mone(), {2}}};
  for (size_t u : {31, 32, 33, 63, 64, 65, 127, 128, 129, 255, 256, 257, 511,
                   512}) {
    const auto y = compiler::op_counts_internal::skip_at<F, Hash>(
        cf, rel, compiler::SkipKind::kField, u, 4);
    std::printf("u=%zu mul=%llu add=%llu mac=%llu reduce=%llu inv=%llu\n", u,
                (unsigned long long)y.mul, (unsigned long long)y.add,
                (unsigned long long)y.mac, (unsigned long long)y.reduce,
                (unsigned long long)y.inv);
  }
}

TEST(OpCounts, SkipCountsExtrapolateExactly) {
  using P = ROMParams;
  const examples::mldsa::Env<P> env;
  using Hash = typename P::ProtocolHash;
  expect_exact_skip_counts<std::decay_t<decltype(env.af)>, Hash>(
      env.af, compiler::SkipKind::kField, 4, {1000, 4097, 9001});
  expect_exact_skip_counts<std::decay_t<decltype(env.hf)>, Hash>(
      env.hf, compiler::SkipKind::kBitChi, 16, {37, 300});
  expect_exact_skip_counts<std::decay_t<decltype(env.hf)>, Hash>(
      env.hf, compiler::SkipKind::kBitRuntime, 16, {37, 300});
}

TEST(Rule, UnitRates) {
  const MEnv env;
  {
    PackedOdd t(env, compiler::PlacementRates{}, 16, false);
    const auto c = compile(t.cs);
    EXPECT_TRUE(has(c, "Boolean checks n=16: field batch (cheapest; "))
        << c->report();
    EXPECT_TRUE(has(c, "assert_zero 'quad' n=16: field batch (cheapest; "))
        << c->report();
    EXPECT_TRUE(proves(c, t.witness(env.af, 16), false));
  }
  {
    UnpackedOdd t(compiler::PlacementRates{}, 16);
    const auto c = compile(t.cs);
    EXPECT_TRUE(has(c, "Boolean checks n=16: quadratic triples (cheapest; "))
        << c->report();
    EXPECT_TRUE(has(c, "assert_zero 'tri' n=16: quadratic triples (cheapest; "))
        << c->report();
    EXPECT_TRUE(proves(c, t.witness(16), false));
  }
}

// Every field of the flagship profiles has measured rates.
TEST(Rule, ProfileRates) {
  using param_sets::placement_rates;
  using W = param_sets::QROMParams;
  for (const compiler::PlacementRates &r :
       {placement_rates<ROMParams::HashField>(),
        placement_rates<ROMParams::EmulatedField>(),
        placement_rates<ROMParams::FalconNativeField>(),
        placement_rates<ROMParams::MLDSANativeField>(),
        placement_rates<ROMParams::EcdsaField>(),
        placement_rates<W::HashField>(), placement_rates<W::EmulatedField>(),
        placement_rates<W::FalconNativeField>(),
        placement_rates<W::MLDSANativeField>()}) {
    EXPECT_TRUE(r.measured());
    EXPECT_GT(r.commit_full, 0);
    EXPECT_GT(r.gkr_term, 0);
    // The triples' terms (per triple, per row, per compression, fixed) are
    // fitted together, and one of them alone may be negative.
    EXPECT_NE(std::string(r.source), "");
  }
  // The relatively packed fields have a batch rate. F_p256 has none, because
  // no fit of its field batch meets the 10 % rule, so its groups never land
  // in a batch unless pinned (Rule.NoRates).
  for (const compiler::PlacementRates &r :
       {placement_rates<ROMParams::HashField>(),
        placement_rates<ROMParams::MLDSANativeField>(),
        placement_rates<W::FalconNativeField>()})
    EXPECT_FALSE(r.batch.empty());
  EXPECT_TRUE(placement_rates<ROMParams::EcdsaField>().batch.empty());
}

// ------------------------------------------------------------ microbench --

using bench::Clock;
using bench::ms_since;
using bench::median;
size_t env_size(const char *name, size_t dflt) {
  const char *r = std::getenv(name);
  return r != nullptr ? std::strtoull(r, nullptr, 10) : dflt;
}
size_t reps() { return env_size("GH_PLACEMENT_REPS", 7); }
size_t warmups() { return env_size("GH_PLACEMENT_WARMUP", 1); }
// The comma-separated unsigned integers of NAME, or DFLT.
std::vector<size_t> env_list(const char *name, std::vector<size_t> dflt) {
  const char *e = std::getenv(name);
  if (e == nullptr) return dflt;
  std::vector<size_t> v;
  for (const char *s = e; *s != '\0';) {
    char *end = nullptr;
    v.push_back(std::strtoull(s, &end, 10));
    s = *end == ',' ? end + 1 : end;
    if (end == s && *s != '\0') break;
  }
  return v;
}
// The instance counts of every series (GH_PLACEMENT_SIZES).
std::vector<size_t> sizes() {
  return env_list("GH_PLACEMENT_SIZES", {256, 4096, 16384});
}
// The instance counts of the triple series (GH_PLACEMENT_TRIPLE_SIZES): at
// 4096 triples the Fiat-Shamir stream budget is exceeded.
std::vector<size_t> triple_sizes() {
  return env_list("GH_PLACEMENT_TRIPLE_SIZES", {256, 1024});
}
// The skip widths a batch series runs at, per evaluator
// (GH_PLACEMENT_WIDTHS_BIT, _SUB, _FIELD; default 16, 4, 4).
std::vector<size_t> widths(compiler::BatchEval e) {
  using E = compiler::BatchEval;
  if (e == E::kBitSliced) return env_list("GH_PLACEMENT_WIDTHS_BIT", {16});
  if (e == E::kSubfield) return env_list("GH_PLACEMENT_WIDTHS_SUB", {4});
  return env_list("GH_PLACEMENT_WIDTHS_FIELD", {4});
}

// The merged predicate counts of the part series (GH_PLACEMENT_PARTS) and
// their instance count (GH_PLACEMENT_PART_N).
std::vector<size_t> part_counts() {
  return env_list("GH_PLACEMENT_PARTS", {1, 4, 16, 64, 256});
}
size_t part_n() { return env_size("GH_PLACEMENT_PART_N", 16384); }

// The degrees the batch series of evaluator EVAL measure in field TYPE: with
// GH_PLACEMENT_REQUESTS naming the rate run's request scan (lines
// "<field> <evaluator> <degree>", from a compile under GH_RATE_REQUESTS),
// the degrees some shipped system requests there, none when it requests
// none; otherwise GH_PLACEMENT_DEGREES (default 2, 3).
std::vector<size_t> degrees(const char *type, const char *eval) {
  const char *path = std::getenv("GH_PLACEMENT_REQUESTS");
  if (path == nullptr) return env_list("GH_PLACEMENT_DEGREES", {2, 3});
  std::vector<size_t> out;
  if (std::FILE *in = std::fopen(path, "r")) {
    char line[256], f[64], e[64];
    unsigned d = 0;
    while (std::fgets(line, sizeof(line), in) != nullptr)
      if (std::sscanf(line, "%63s %63s %u", f, e, &d) == 3 &&
          std::string(f) == type && std::string(e) == eval &&
          std::find(out.begin(), out.end(), d) == out.end())
        out.push_back(d);
    std::fclose(in);
  }
  std::sort(out.begin(), out.end());
  return out;
}
// The most merged predicates of a part series of degree D
// (GH_PLACEMENT_HIGH_PARTS, default 16, from GH_PLACEMENT_PARTS_DEGREE,
// default 4, on): from degree 3 every merged predicate adds operands, and
// at degree 16 a proof of 16 merged predicates takes about 25 s.
size_t max_parts(size_t d) {
  return d >= env_size("GH_PLACEMENT_PARTS_DEGREE", 4)
             ? env_size("GH_PLACEMENT_HIGH_PARTS", 16)
             : SIZE_MAX;
}
// The largest instance count of a batch series of degree D
// (GH_PLACEMENT_HIGH_DEGREE and GH_PLACEMENT_HIGH_N, default 16 and 8192):
// at degree 16 and above a batch of 16384 instances overruns a
// Fiat-Shamir challenge point's stream budget.
size_t max_count(size_t d) {
  return d >= env_size("GH_PLACEMENT_HIGH_DEGREE", 16)
             ? env_size("GH_PLACEMENT_HIGH_N", 8192)
             : SIZE_MAX;
}

// A check's form over the five cells x0..x4 of a microbench system: the
// first product of PRODS less the other products and the cells SUB (Bits:
// ANDs, XORed together). Each product reads its cells as separate
// operands, and SUB joins one affine operand, so the forms span 1 to 5
// operands at each degree D: x0^D - x0, x0^(D-1) x1, x0^(D-1) x1 - x2,
// x0^(D-1) x1 - x2^(D-1) x3, and x0^(D-1) x1 - x2^(D-1) x3 - x4.
struct Form {
  std::string name;
  std::vector<std::vector<int>> prods;
  std::vector<int> sub;
  unsigned degree() const { return unsigned(prods[0].size()); }
};
constexpr size_t kCells = 5;
// The form of degree D with K operands.
Form make_form(size_t d, size_t k) {
  Form f;
  f.name = "d" + std::to_string(d) + "k" + std::to_string(k);
  auto prod = [d](int a, int b) {
    std::vector<int> p(d - 1, a);
    p.push_back(b);
    return p;
  };
  if (k == 1) {
    f.prods = {std::vector<int>(d, 0)};
    f.sub = {0};
    return f;
  }
  f.prods = {prod(0, 1)};
  if (k == 3 || k == 5) f.sub = {k == 3 ? 2 : 4};
  if (k >= 4) f.prods.push_back(prod(2, 3));
  return f;
}
// The part series' form of degree D: three operands.
constexpr size_t kPartArity = 3;

// One microbench system in a single domain D over F: an anchor (a a = 0 in
// the circuit) and n cells x0..x4 of one type; with FORM, the check over
// them pinned to a target, one predicate or PARTS predicates over
// consecutive slices; without, the bare cells.
enum class Cell { kBit, kSub, kField };
const char *cell_name(Cell c) {
  return c == Cell::kBit ? "bit" : c == Cell::kSub ? "sub" : "field";
}

template <class Sys, class F, class Prof>
struct Micro {
  Sys cs{"gh-placement-micro"};
  Ref<F, Subfield<>, Committed> a;
  std::vector<Ref<F>> x;
  const Form *fm;
  size_t n, copies;
  // COPIES (field cells only): that many copies of the cells and the
  // check, copy r's check scaled by r + 1 so the copies do not merge: a
  // point of COPIES batches of the form.
  Micro(const Prof &p, Cell c, const Form *form, Placement pin, size_t parts,
        size_t count, size_t ncopies = 1)
      : fm(form), n(count), copies(ncopies) {
    check(copies == 1 || c != Cell::kBit, "micro: copies of Bit cells");
    auto &D = cs.domain(p, "D");
    a = D.priv(Subfield{}, "a", 1);
    assert_zero(a * a, "anchor").pin(Placement::kCircuit);
    std::vector<Expr<F, Bit>> eb;
    std::vector<Expr<F>> ef;
    for (size_t k = 0; k < kCells * copies; ++k) {
      const std::string nm =
          "x" + std::to_string(k % kCells) +
          (k < kCells ? std::string() : "." + std::to_string(k / kCells));
      if (c == Cell::kBit) {
        const auto r = D.priv(Bit{}, nm, n);
        eb.push_back(Expr<F, Bit>(r));
        x.push_back(r);
      } else if (c == Cell::kSub) {
        const auto r = D.priv(Subfield{}, nm, n);
        ef.push_back(Expr<F>(r));
        x.push_back(r);
      } else {
        const auto r = D.priv(Field{}, nm, n);
        ef.push_back(Expr<F>(r));
        x.push_back(r);
      }
    }
    if (form == nullptr) return;
    for (size_t cp = 0; cp < copies; ++cp)
    for (size_t k = 0; k < parts; ++k) {
      const size_t b = k * n / parts, e = (k + 1) * n / parts;
      const std::string nm = "check" + std::to_string(k) +
                             (cp == 0 ? std::string()
                                      : "." + std::to_string(cp));
      if (c == Cell::kBit) {
        // Each cell's view once per part (batch_form makes equal views
        // one operand either way).
        std::vector<Expr<F, Bit>> v;
        for (const auto &x : eb) v.push_back(parts > 1 ? x.slice(b, e) : x);
        auto op = [&](int i) { return v[size_t(i)]; };
        auto product = [&](const std::vector<int> &p) {
          Expr<F, Bit> e = op(p[0]);
          for (size_t i = 1; i < p.size(); ++i) e = e & op(p[i]);
          return e;
        };
        Expr<F, Bit> q = product(form->prods[0]);
        for (size_t j = 1; j < form->prods.size(); ++j)
          q = q ^ product(form->prods[j]);
        for (int s : form->sub) q = q ^ op(s);
        assert_zero(q, nm).pin(pin);
      } else {
        // One predicate reads the cells whole (a triple's form).
        // Each cell's view once per part (as for Bits).
        std::vector<Expr<F>> v;
        for (size_t i = 0; i < kCells; ++i) {
          const auto &x = ef[cp * kCells + i];
          v.push_back(parts > 1 ? Expr<F>(x.slice(b, e)) : x);
        }
        auto op = [&](int i) { return v[size_t(i)]; };
        auto product = [&](const std::vector<int> &p) {
          Expr<F> e = op(p[0]);
          for (size_t i = 1; i < p.size(); ++i) e = e * op(p[i]);
          return e;
        };
        Expr<F> q = product(form->prods[0]);
        for (size_t j = 1; j < form->prods.size(); ++j)
          q = q - product(form->prods[j]);
        for (int s : form->sub) q = q - op(s);
        if (cp > 0) q = q * p.f->of_scalar(cp + 1);
        assert_zero(q, nm).pin(pin);
      }
    }
  }
  // Random bits, set so that the form holds: every product but the first
  // is 0 (its last cell 0 where it would be 1), and the SUB cell is the
  // first product, or, without SUB, the first product is 0 too.
  typename Sys::Assignment witness(const F &f) const {
    std::vector<std::vector<bool>> v(kCells, std::vector<bool>(n));
    std::mt19937_64 g(n);
    for (auto &c : v)
      for (size_t i = 0; i < n; ++i) c[i] = (g() & 1) != 0;
    if (fm != nullptr) {
      auto all = [&](const std::vector<int> &p, size_t i) {
        bool r = true;
        for (int k : p) r = r && v[size_t(k)][i];
        return r;
      };
      for (size_t i = 0; i < n; ++i) {
        for (size_t j = 1; j < fm->prods.size(); ++j)
          if (all(fm->prods[j], i)) v[size_t(fm->prods[j].back())][i] = false;
        const bool first = all(fm->prods[0], i);
        if (fm->sub.empty()) {
          if (first) v[size_t(fm->prods[0].back())][i] = false;
        } else if (fm->sub[0] != fm->prods[0][0]) {
          v[size_t(fm->sub[0])][i] = first;
        }
      }
    }
    typename Sys::Assignment wa;
    wa.set(a, std::vector<typename F::Elt>(1, f.zero()));
    for (size_t k = 0; k < kCells * copies; ++k) {
      std::vector<typename F::Elt> e(n);
      for (size_t i = 0; i < n; ++i)
        e[i] = v[k % kCells][i] ? f.one() : f.zero();
      wa.set(x[k], e);
    }
    return wa;
  }
};

// Medians of REPS proofs of the domain after WARMUPS: commit, prove, verify
// (ms), and the quartiles of their sum; its quad terms, committed size,
// rows, proof bytes, its batch's skip width and the check's operands (the
// count the placement rule's batch cost reads).
//
// A point with a reference (the bare cells it is measured against) also
// has the paired excess: each proof of the check is followed or preceded
// (alternately) by one of the reference, and EXCESS, EX_Q1 and EX_Q3 are
// the median and quartiles of the pairs' differences of commit + prove +
// verify, EXCESS_PV the median of their differences of prove + verify. A
// drift between the two series cancels in each pair.
struct Point {
  double commit = 0, prove = 0, verify = 0, q1 = 0, q3 = 0;
  double excess = 0, ex_q1 = 0, ex_q3 = 0, excess_pv = 0;
  bool paired = false;
  size_t terms = 0, nw = 0, nrow = 0, bytes = 0, width = 0, batches = 0;
  size_t arity = 0, block_enc = 0;
  double total() const { return commit + prove + verify; }
};

double quantile(std::vector<double> v, double q) {
  std::sort(v.begin(), v.end());
  const double at = q * double(v.size() - 1);
  const size_t lo = size_t(at);
  const size_t hi = std::min(lo + 1, v.size() - 1);
  return v[lo] + (at - double(lo)) * (v[hi] - v[lo]);
}

// The C++ name of F, for the fields the profiles give rates
// (param_sets::placement_rates); the rate fit keys its fits by it.
template <class F>
const char *field_type() {
  if constexpr (std::is_same_v<F, Fp24_6>) {
    return "Fp24_6";
  } else if constexpr (std::is_same_v<F, MlDsaField11>) {
    return "MlDsaField11";
  } else if constexpr (std::is_same_v<F, Fp14_9>) {
    return "Fp14_9";
  } else if constexpr (std::is_same_v<F, FalconField20>) {
    return "FalconField20";
  } else if constexpr (std::is_same_v<F, Fp64G2>) {
    return "Fp64G2";
  } else if constexpr (std::is_same_v<F, Fp64G4>) {
    return "Fp64G4";
  } else if constexpr (std::is_same_v<F, GF2_128<>>) {
    return "GF2_128";
  } else if constexpr (std::is_same_v<F, GF2_256<>>) {
    return "GF2_256";
  } else if constexpr (std::is_same_v<F, Fp256Base>) {
    return "Fp256Base";
  } else if constexpr (std::is_same_v<F, Fp128<>>) {
    return "Fp128";
  } else {
    return "unknown";
  }
}

// A target as one token of a PLACEMENT_POINT line.
const char *target_token(Placement p) {
  switch (p) {
    case Placement::kQuadratic:
      return "triples";
    case Placement::kCircuit:
      return "circuit";
    case Placement::kBatch:
      return "batch";
    default:
      return "auto";
  }
}

// The compression size of a system's protocol hash.
template <class H, class... Fs>
constexpr size_t hash_block_size(const BasicConstraintSystem<H, Fs...> *) {
  return H::kBlockSize;
}

// The point of one microbench system (Micro) at N instances: REPS proofs
// after WARMUPS. With REF_P, the bare REF_CELL cells at N under REF_P are
// its reference, timed in pairs with it (Point).
template <class Sys, class F, class Prof>
Point run(const char *field, const F &f, const Prof &p, Cell cell,
          const Form *form, Placement pin, size_t parts, size_t n,
          const Prof *ref_p = nullptr, Cell ref_cell = Cell::kField) {
  // GH_PLACEMENT_COPIES: a batch point's copies of its check (Micro).
  const size_t copies =
      pin == Placement::kBatch && cell != Cell::kBit
          ? env_size("GH_PLACEMENT_COPIES", 1)
          : 1;
  Micro<Sys, F, Prof> t(p, cell, form, pin, parts, n, copies);
  const auto c = compile(t.cs);
  auto prep = c->prepare(typename Sys::Assignment{});
  const auto wit = t.witness(f);
  std::unique_ptr<Micro<Sys, F, Prof>> rt;
  if (ref_p != nullptr)
    rt = std::make_unique<Micro<Sys, F, Prof>>(*ref_p, ref_cell, nullptr,
                                               Placement::kAuto, 1, n, copies);
  const auto rc = rt ? compile(rt->cs) : nullptr;
  auto rprep = rc ? std::make_unique<decltype(rc->prepare(
                        typename Sys::Assignment{}))>(
                        rc->prepare(typename Sys::Assignment{}))
                  : nullptr;
  const auto rwit = rt ? rt->witness(f) : typename Sys::Assignment{};
  SecureRandomEngine rng;
  std::vector<double> cm, pr, vf, tot, ex, expv;
  size_t bytes = 0;
  // One proof of PR on W: commit, prove, verify (ms) of domain 0.
  auto one = [&](auto &pr_, const auto &w, size_t *by) {
    ProveTimes times;
    typename Sys::ProveOptions opt;
    opt.times = &times;
    const auto proof = pr_.prove(w, rng, opt);
    if (by != nullptr) *by = proof.size();
    VerifyTimes vt;
    EXPECT_TRUE(pr_.verify(proof, &vt));
    return std::array<double, 3>{times.domain_commit[0],
                                 times.domain_prove[0], vt.domain[0]};
  };
  for (size_t r = 0; r < warmups() + reps(); ++r) {
    std::array<double, 3> ref{};
    // The reference before the check on odd proofs, after it on even ones.
    if (rprep && r % 2 == 1) ref = one(*rprep, rwit, nullptr);
    const auto x = one(prep, wit, &bytes);
    if (rprep && r % 2 == 0) ref = one(*rprep, rwit, nullptr);
    if (r < warmups()) continue;
    cm.push_back(x[0]);
    pr.push_back(x[1]);
    vf.push_back(x[2]);
    tot.push_back(x[0] + x[1] + x[2]);
    if (rprep) {
      ex.push_back(tot.back() - (ref[0] + ref[1] + ref[2]));
      expv.push_back(x[1] + x[2] - (ref[1] + ref[2]));
    }
  }
  Point pt;
  // GH_PLACEMENT_REPS=0 with no warm-up: the point's plan and counts
  // alone, no proof.
  if (!cm.empty()) {
    pt.commit = median(cm);
    pt.prove = median(pr);
    pt.verify = median(vf);
    pt.q1 = quantile(tot, 0.25);
    pt.q3 = quantile(tot, 0.75);
  }
  if (rprep && !ex.empty()) {
    pt.paired = true;
    pt.excess = median(ex);
    pt.ex_q1 = quantile(ex, 0.25);
    pt.ex_q3 = quantile(ex, 0.75);
    pt.excess_pv = median(expv);
  }
  const DomainPlan pl = c->compiled_domain(0).plan();
  pt.terms = pl.quad_terms;
  pt.nw = pl.nw;
  pt.nrow = pl.nrow;
  pt.block_enc = pl.block_enc;
  pt.bytes = bytes;
  pt.batches = pl.batches.size();
  for (const auto &b : pl.batches) pt.width = std::max(pt.width, b.width);
  // The operands the placement rule's batch cost reads for the check.
  for (const auto &x : pl.placements)
    if (x.name == "check0") pt.arity = x.operands;
  std::printf("PLACEMENT_POINT field=%s type=%s cell=%s form=%s target=%s "
              "degree=%u parts=%zu operands=%zu width=%zu n=%zu commit=%.4f "
              "prove=%.4f verify=%.4f total=%.4f total_q1=%.4f "
              "total_q3=%.4f reps=%zu quad_terms=%zu nw=%zu nrow=%zu "
              "block_enc=%zu bytes=%zu batches=%zu",
              field, field_type<F>(), cell_name(cell),
              form ? form->name.c_str() : "none",
              form ? target_token(pin) : "none", form ? form->degree() : 0,
              form ? parts : 0, pt.arity, pt.width, n, pt.commit, pt.prove,
              pt.verify, pt.total(), pt.q1, pt.q3, cm.size(), pt.terms,
              pt.nw, pt.nrow, pt.block_enc, pt.bytes, pt.batches);
  // The check's batches (not the Boolean checks') and their work as the
  // placement rule counts it (op_counts.h), summed.
  {
    compiler::OpCounts w;
    size_t nb = 0;
    for (const auto &bt : pl.batches) {
      if (bt.name == "D.boolean") continue;
      ++nb;
      w.mul += bt.work.mul;
      w.add += bt.work.add;
      w.mac += bt.work.mac;
      w.reduce += bt.work.reduce;
      w.inv += bt.work.inv;
      w.lane_lookup += bt.work.lane_lookup;
      w.lane_mul += bt.work.lane_mul;
      w.lane_term += bt.work.lane_term;
      w.lin += bt.work.lin;
      w.map_mul += bt.work.map_mul;
      w.map_add += bt.work.map_add;
      w.map_mac += bt.work.map_mac;
      w.region += bt.work.region;
    }
    if (nb > 0)
      std::printf(" nbatch=%zu mul=%llu add=%llu mac=%llu reduce=%llu "
                  "inv=%llu lane_lookup=%llu lane_mul=%llu lane_term=%llu "
                  "lin=%llu map_mul=%llu map_add=%llu map_mac=%llu "
                  "region=%llu",
                  nb, (unsigned long long)w.mul, (unsigned long long)w.add,
                  (unsigned long long)w.mac, (unsigned long long)w.reduce,
                  (unsigned long long)w.inv,
                  (unsigned long long)w.lane_lookup,
                  (unsigned long long)w.lane_mul,
                  (unsigned long long)w.lane_term,
                  (unsigned long long)w.lin, (unsigned long long)w.map_mul,
                  (unsigned long long)w.map_add,
                  (unsigned long long)w.map_mac,
                  (unsigned long long)w.region);
  }
  if (pt.paired)
    std::printf(" ref_nrow=%zu elt_bytes=%zu hash_block=%zu",
                rc->compiled_domain(0).plan().nrow, size_t(F::kBytes),
                hash_block_size(static_cast<const Sys *>(nullptr)));
  if (pt.paired)
    std::printf(" ref=%s excess=%.4f excess_q1=%.4f excess_q3=%.4f "
                "excess_pv=%.4f",
                cell_name(ref_cell), pt.excess, pt.ex_q1, pt.ex_q3,
                pt.excess_pv);
  std::printf("\n");
  std::fflush(stdout);
  return pt;
}

// P with its Ligero tableau fixed to the one P chooses for the bare Field
// cells at the largest instance count (block_enc, opened columns,
// masking), so that every point of a field shares one block and the costs
// grow with the rows alone, without the steps of the block_enc search.
template <class Sys, class F, class Prof>
Prof fixed_tableau(const Prof &p, size_t n) {
  Micro<Sys, F, Prof> t(p, Cell::kField, nullptr, Placement::kAuto, 1, n);
  const auto c = compile(t.cs);
  const DomainPlan pl = c->compiled_domain(0).plan();
  Prof q = p;
  q.target.reset();
  q.rate = pl.rate;
  q.list_radius = pl.list_radius;
  q.t = pl.t;
  if (!pl.list_radius) q.nreq = pl.t;
  q.masking = pl.split ? LigeroMasking::kSplit : LigeroMasking::kUntested;
  const size_t e = pl.block_enc;
  q.block_enc = [e](const auto &, size_t, size_t) { return e; };
  std::printf("PLACEMENT_TABLEAU field_n=%zu rate=%zu block_enc=%zu t=%zu "
              "list_radius=%d split=%d\n",
              n, pl.rate, e, pl.t, int(pl.list_radius), int(pl.split));
  return q;
}

// The points of one field, all at one tableau (fixed_tableau): the bare
// cells of each type (the commit rates), x x - x in the circuit (the GKR
// term rate), x y - z as triples, and each evaluator that applies to F
// (bit-sliced in characteristic 2, the subfield's when the designated
// subfield is proper, the field's always) at each of its widths(): at each
// degree it is requested at (degrees(); none, no series), the forms of
// arity 1 to kCells pinned to a batch at every instance count up to
// max_count(), and the part series (the form of arity kPartArity as
// part_counts() merged predicates over part_n() instances). Measurement
// only: a fit outside this repository fits the rates from the
// PLACEMENT_POINT lines.
template <class Sys, class F, class Prof>
void rates(const char *field, const F &f, Prof p0) {
  using E = compiler::BatchEval;
  // GH_PLACEMENT_PART: "base" measures the bare cells, the circuit and the
  // triples alone; "<evaluator>:<degree>" one evaluator's batch series at
  // one degree alone (one measurement job each); unset, everything.
  // The microbench's trees are the default ones, whatever the profile's
  // stage rates; a profile measured before its batch rates weighs its
  // batches at unit op rates, the same in each check and its reference.
  p0.rates.stage = equal_chains();
  if (p0.rates.batch.empty())
    for (auto e : {compiler::BatchEval::kBitSliced,
                   compiler::BatchEval::kSubfield, compiler::BatchEval::kField})
      p0.rates.batch.push_back({e, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1});
  const char *part_env = std::getenv("GH_PLACEMENT_PART");
  const std::string part = part_env == nullptr ? "" : part_env;
  const bool base = part.empty() || part == "base";
  const std::vector<size_t> ns = sizes();
  // The tableau of the bare Field cells at GH_PLACEMENT_TABLEAU_N
  // (default the largest instance count).
  const Prof p = fixed_tableau<Sys, F, Prof>(
      p0, env_size("GH_PLACEMENT_TABLEAU_N",
                   *std::max_element(ns.begin(), ns.end())));
  auto sweep = [&](Cell c, const Form *fm, Placement pin, size_t parts,
                   const Prof &q, const std::vector<size_t> &counts) {
    for (size_t n : counts)
      run<Sys, F, Prof>(field, f, q, c, fm, pin, parts, n);
  };
  // The bare Field cells at the triples' counts too.
  std::vector<size_t> nf = ns;
  for (size_t n : triple_sizes())
    if (std::find(nf.begin(), nf.end(), n) == nf.end()) nf.push_back(n);
  std::sort(nf.begin(), nf.end());
  const auto none = Placement::kAuto;
  // A check's series, each point paired with its reference: the bare
  // REF cells at the same count under P.
  auto paired = [&](Cell c, const Form *fm, Placement pin, size_t parts,
                    const Prof &q, const std::vector<size_t> &counts,
                    Cell ref) {
    for (size_t n : counts)
      run<Sys, F, Prof>(field, f, q, c, fm, pin, parts, n, &p, ref);
  };
  // The circuit series' form: x0 x1 - x2 x3 - x4, the most terms per
  // instance of the degree-2 forms, so its excess stands above the noise
  // of a binary field's cheap terms.
  const Form square = make_form(2, 5), chi = make_form(2, 3);
  if (base) {
    sweep(Cell::kField, nullptr, none, 1, p, nf);
    sweep(Cell::kSub, nullptr, none, 1, p, ns);
    paired(Cell::kSub, &square, Placement::kCircuit, 1, p, ns, Cell::kSub);
    paired(Cell::kField, &chi, Placement::kQuadratic, 1, p, triple_sizes(),
           Cell::kField);
    // The triples again at the tableaus of GH_PLACEMENT_TRIPLE_TABLEAUS
    // (bare Field cell counts; default none), each paired with its bare
    // cells at that tableau: their rows' cost against block_enc.
    for (size_t tn : env_list("GH_PLACEMENT_TRIPLE_TABLEAUS", {})) {
      const Prof q = fixed_tableau<Sys, F, Prof>(p0, tn);
      for (size_t n : triple_sizes())
        run<Sys, F, Prof>(field, f, q, Cell::kField, &chi,
                          Placement::kQuadratic, 1, n, &q, Cell::kField);
    }
  }
  // A table with every evaluator at every measured degree, EVAL's at width
  // W, so a pinned batch is admissible and runs at W whatever the profile's
  // own table holds. Its costs are never read: every check is pinned.
  auto eval_token = [](E e) {
    return e == E::kBitSliced ? "bit-sliced"
           : e == E::kSubfield ? "subfield"
                               : "field";
  };
  auto at_width = [&](E eval, unsigned w) {
    Prof q = p;
    q.rates = compiler::PlacementRates{};
    q.rates.gkr_term = 1;
    q.rates.stage = equal_chains();
    (void)eval;
    (void)w;
    for (E e : {E::kBitSliced, E::kSubfield, E::kField})
      q.rates.batch.push_back({e, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1});
    return q;
  };
  std::vector<Cell> cells = {Cell::kField};
  if (designated_degree<F>() < field_degree<F>())
    cells.insert(cells.begin(), Cell::kSub);
  if constexpr (F::kCharacteristicTwo) {
    cells.insert(cells.begin(), Cell::kBit);
    if (base) sweep(Cell::kBit, nullptr, none, 1, p, ns);
  }
  for (Cell cell : cells) {
    const E eval = cell == Cell::kBit   ? E::kBitSliced
                   : cell == Cell::kSub ? E::kSubfield
                                        : E::kField;
    const std::vector<size_t> ds = degrees(field_type<F>(), eval_token(eval));
    if (ds.empty()) continue;
    for (size_t w : widths(eval)) {
      const Prof q = at_width(eval, unsigned(w));
      for (size_t d : ds) {
        if (!part.empty() &&
            part != std::string(eval_token(eval)) + ":" + std::to_string(d))
          continue;
        std::vector<size_t> nd;
        for (size_t n : ns)
          if (n <= max_count(d)) nd.push_back(n);
        for (size_t k = 1; k <= kCells; ++k) {
          const Form fm = make_form(d, k);
          paired(cell, &fm, Placement::kBatch, 1, q, nd, cell);
        }
        const Form pf = make_form(d, kPartArity);
        const size_t pn = std::min(part_n(), max_count(d));
        for (size_t parts : part_counts())
          if (parts > 1 && parts <= max_parts(d))
            paired(cell, &pf, Placement::kBatch, parts, q, {pn}, cell);
      }
    }
  }
}


bool selected(const char *what) {
  const char *e = std::getenv("GH_PLACEMENT_FIELDS");
  return e == nullptr || std::string(e).find(what) != std::string::npos;
}

TEST(Placement, DISABLED_Rates) {
  param_sets::with_profile([&](auto prof) {
    using P = decltype(prof);
    const std::string pid = P::kId;
    if (selected("ml-dsa")) {
      const examples::mldsa::Env<P> env;
      auto p = examples::domain_profile<P>(env.af, env.rsa);
      rates<typename examples::mldsa::Env<P>::Sys>((pid + ".ml-dsa").c_str(),
                                                   env.af, p);
    }
    if (selected("hash")) {
      const examples::mldsa::Env<P> env;
      auto p = examples::domain_profile<P>(env.hf, env.rsh);
      rates<typename examples::mldsa::Env<P>::Sys>((pid + ".hash").c_str(),
                                                   env.hf, p);
    }
    if (selected("falcon")) {
      const examples::falcon::native::Env<P> env;
      auto p = examples::domain_profile<P>(env.af, env.rsa);
      rates<typename examples::falcon::native::Env<P>::Sys>(
          (pid + ".falcon").c_str(), env.af, p);
    }
    if (selected("emulated")) {
      const examples::falcon::emulated::Env<P> env;
      auto p = examples::domain_profile<P>(env.af, env.rsa.factory());
      rates<typename examples::falcon::emulated::Env<P>::Sys>(
          (pid + ".emulated").c_str(), env.af, p);
    }
    if (selected("p256") && pid == "narrow") {
      rates<examples::mdoc::p256_testing::Sys>(
          "narrow.p256", examples::mdoc::p256_testing::fp(),
          examples::mdoc::p256_testing::profile());
    }
    // Fp128 at the RSA system's A profile (param_sets::ROMParamsFp128).
    if (selected("fp128") && pid == "narrow") {
      using Q = param_sets::ROMParamsFp128;
      const examples::rsa::Env<Q> env;
      auto p = examples::domain_profile<Q>(env.af, env.rsa.factory());
      rates<typename examples::rsa::Env<Q>::Sys>("narrow.fp128", env.af, p);
    }
  });
}

// One field's rate table as compiled (param_sets::placement_rates).
template <class F>
void print_table() {
  const compiler::PlacementRates r = param_sets::placement_rates<F>();
  std::printf("PLACEMENT_TABLE type=%s commit_full=%.6g commit_sub=%.6g "
              "gkr_term=%.6g triple=%.6g source=%s\n",
              field_type<F>(), r.commit_full, r.commit_sub, r.gkr_term,
              r.triple, r.source);
  for (const auto &b : r.batch) {
    const char *e = b.eval == compiler::BatchEval::kBitSliced ? "bit-sliced"
                    : b.eval == compiler::BatchEval::kSubfield
                        ? "subfield"
                        : "field";
    std::printf("PLACEMENT_TABLE_BATCH type=%s eval=%s fixed=%.6g mul=%.6g "
                "add=%.6g mac=%.6g lane_lookup=%.6g lane_mul=%.6g "
                "lane_term=%.6g lin=%.6g map_mul=%.6g map_add=%.6g "
                "map_mac=%.6g\n",
                field_type<F>(), e, b.fixed, b.mul, b.add, b.mac,
                b.lane_lookup, b.lane_mul, b.lane_term, b.lin, b.map_mul,
                b.map_add, b.map_mac);
  }
}

// Every profile field's compiled rate table, for comparing the table a
// build holds with a run's fits.
TEST(Placement, DISABLED_PrintRates) {
  print_table<Fp24_6>();
  print_table<MlDsaField11>();
  print_table<Fp14_9>();
  print_table<FalconField20>();
  print_table<Fp64G2>();
  print_table<Fp64G4>();
  print_table<GF2_128<>>();
  print_table<GF2_256<>>();
  print_table<Fp256Base>();
  print_table<Fp128<>>();
}

}  // namespace
}  // namespace proofs::gordiehowe
