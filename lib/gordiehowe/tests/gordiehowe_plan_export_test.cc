// Copyright 2026 Chad Sharp and Paul Grubbs
// SPDX-License-Identifier: Apache-2.0

// GordieHowe: the plan export (plan_export.h). A toy H/A pair (an ordered
// selection in H, its samples in A tied by the MAC equality, and a range
// request in A) exports to a fixed Lean module: any change to the
// exporter's output, or to what the compiled system records, shows here.
// GH_PRINT_GOLDEN=1 prints the output.

#include <algorithm>
#include <cmath>
#include <cstdio>
#include <cstdlib>
#include <filesystem>
#include <fstream>
#include <map>
#include <memory>
#include <random>
#include <set>
#include <sstream>
#include <stdexcept>
#include <string>
#include <tuple>
#include <vector>

#include <unistd.h>

#include "algebra/fp_goldilocks4.h"
#include "algebra/reed_solomon_fp.h"
#include "gf2k/gf2_128.h"
#include "gf2k/gf2_256.h"
#include "gf2k/lch14_reed_solomon.h"
#include "gordiehowe/compiler/assignment_reads.h"
#include "gordiehowe/compiler/plan_export.h"
#include "gordiehowe/compiler/plan_program.h"
#include "gordiehowe/compiler/plan_proofs.h"
#include "gordiehowe/instances.h"
#include "gordiehowe/examples/mldsa/mldsa_shape_inputs.h"
#include "gordiehowe/examples/mldsa/mldsa_source_roles.h"
#include "gordiehowe/examples/shared/domain_profile.h"
#include "gordiehowe/examples/shared/program_testing.h"
#include "gordiehowe/lib/cutoff_select.h"
#include "gordiehowe/system.h"
#include "random/secure_random_engine.h"
#include "gtest/gtest.h"

namespace proofs::gordiehowe {
namespace {

// Exact list order matters: the producer is checked against Lean list equality,
// not set equality. Nested shared entries also distinguish the prefix closure
// from the duplicate-retaining bounded closure used by bound values.
TEST(AssignmentReads, OrderedRowsAndRepeatedSharedReferences) {
  ir::Program p;
  auto node = [&](ir::Expr::Op op, uint64_t x = 0,
                  ir::Id a = ir::kNone, ir::Id b = ir::kNone) {
    ir::Expr e;
    e.op = op;
    e.x = x;
    e.a = a;
    e.b = b;
    p.nodes.push_back(e);
    return static_cast<ir::Id>(p.nodes.size() - 1);
  };
  const auto zero = node(ir::Expr::kLeaf, 0);
  const auto two = node(ir::Expr::kLeaf, 2);
  const auto leaves = node(ir::Expr::kAdd, 0, two, zero);
  const auto ref0 = node(ir::Expr::kRef, 0);
  const auto twice = node(ir::Expr::kAdd, 0, ref0, ref0);
  const auto ref1 = node(ir::Expr::kRef, 1);
  p.exprs = {leaves, twice};
  p.values.resize(11);
  p.values[3].kind = ir::Value::kPubExpr;
  p.values[3].expr = ref1;
  p.values[4].kind = ir::Value::kPubExpr;
  p.values[4].expr = ref0;
  p.values[5].kind = ir::Value::kBound;
  p.values[5].expr = ref1;
  p.values[6].kind = ir::Value::kOpaque;
  p.values[6].args = {5, 4, 5};
  p.values[7].kind = ir::Value::kBits;
  p.values[7].ref = 5;
  p.values[8].kind = ir::Value::kBits;
  p.values[8].ref = 9;
  p.values[10].kind = ir::Value::kOpaque;
  p.values[10].args = {10, 0};
  const compiler::AssignmentReads::Rows expected{
      {0}, {1}, {2}, {0, 2}, {2, 0}, {2, 0, 2, 0},
      {0, 2}, {2, 0, 2, 0}, {}, {9}, {0}};
  EXPECT_EQ(compiler::assignment_reads(p), expected);

  // An absent shared entry defaults to leaf 0 in the bounded closure, but
  // defaults to [] in the prefix table used by a public expression.
  const auto missing = node(ir::Expr::kRef, 99);
  p.values[3].expr = missing;
  p.values[5].expr = missing;
  auto rows = compiler::assignment_reads(p);
  EXPECT_TRUE(rows[3].empty());
  EXPECT_EQ(rows[5], (compiler::AssignmentReads::Row{0}));

  // Cyclic shared references terminate at the declared number of entries;
  // they are not rejected by an extra DAG precondition.
  p.exprs = {node(ir::Expr::kAdd, 0, two, ref0)};
  p.values[5].expr = ref0;
  rows = compiler::assignment_reads(p);
  EXPECT_EQ(rows[5], (compiler::AssignmentReads::Row{2}));
}

TEST(AssignmentReads, CoefficientsAndNamedOperators) {
  ir::Program p;
  p.values.resize(4);
  p.coefs = {{false, "", 2, 0}, {false, "", 1, 0}};
  p.linears.push_back({{{0, 0}, {1, 1}}, {{0, 0}}});
  ir::NamedOp mac;
  mac.kind = ir::NamedOp::kMacConv;
  mac.value = 3;
  ir::NamedOp batched;
  batched.kind = ir::NamedOp::kBatched;
  batched.inner = 0;
  p.ops = {mac, batched};
  ir::Expr leaf;
  leaf.x = 0;
  ir::Expr linear;
  linear.op = ir::Expr::kLinear;
  linear.a = 0;
  ir::Expr apply;
  apply.op = ir::Expr::kApply;
  apply.x = 1;
  apply.a = 1;
  p.nodes = {leaf, linear, apply};
  ir::Value bound;
  bound.kind = ir::Value::kBound;
  bound.expr = 2;
  p.values.push_back(bound);
  EXPECT_EQ(compiler::assignment_reads(p).back(),
            (compiler::AssignmentReads::Row{3, 2, 1, 2, 0}));
  p.ops[0].kind = ir::NamedOp::kSum;
  EXPECT_EQ(compiler::assignment_reads(p).back(),
            (compiler::AssignmentReads::Row{2, 1, 2, 0}));
}

TEST(AssignmentReads, RejectUnrepresentableArena) {
  ir::Program p;
  ir::Expr e;
  e.op = ir::Expr::kReindex;
  e.a = 0;
  p.nodes.push_back(e);
  p.exprs.push_back(0);
  EXPECT_THROW(compiler::assignment_reads(p), std::runtime_error);
  p.nodes[0].a = 99;
  EXPECT_THROW(compiler::assignment_reads(p), std::runtime_error);
}

// The cutoff selection (lib/cutoff_select.h).
using namespace ::proofs::gordiehowe::lib::select;  // NOLINT

using AF = Fp64G4;
using AV = std::vector<AF::Elt>;
using RSA = BasicFpReedSolomon<AF>;
using HF = GF2_256<>;
using HV = std::vector<HF::Elt>;
using RSH = LCH14ReedSolomonFactory<HF>;
using Sys = ConstraintSystem<SHA384, AF, HF>;

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

// H selects 512 samples below 60000 from 520 (a MAC of 32 chunks, whose
// quotient digits have radix 128); A holds them as bits, tied by
// assert_same_bits, and a value v below 3000 (MaxBound 2^22).
struct Toy {
  std::unique_ptr<Sys> cs;
  std::unique_ptr<Sys::Compiled> c;
};
Toy toy_system() {
  static const Env *e = new Env;
  auto sys = std::make_unique<Sys>("gh-plan-export-toy");
  Sys &cs = *sys;
  auto &H = cs.domain(e->h_profile(), "H");
  auto &A = cs.domain(e->a_profile(), "A");
  auto stream = H.priv(Bit{}, "stream", 16 * 520);
  auto sel =
      select_first_n(cs, H, stream, Cutoff{60000}, lib::select::Count{512});
  const AF *pa = &e->af;
  const HF *ph = &e->hf;
  auto c_A = A.priv(Bit{}, "samples", 16 * 512, depends_on(sel.raw),
                      [pa, ph](const HV &b) {
                        AV out;
                        for (const auto &x : b)
                          out.push_back(x == ph->one() ? pa->one()
                                                       : pa->zero());
                        return out;
                      });
  assert_same_bits(sel.raw, c_A);
  auto v = A.priv(Subfield{}, "v", 4);
  assert_range(v, 3000, MaxBound{Bound(1) << 22}, "v");
  auto c = compile(cs);
  return Toy{std::move(sys), std::move(c)};
}
std::string toy_export() {
  return compiler::export_lean_plan(
      *toy_system().c,
      compiler::ExportMeta{"toy", "wide", "c0ffee", "run-0", 0});
}

const char kGolden[] = R"lean(-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Language.Export

@[expose] public section

/-!
# GordieHowe plan data: toy-wide

Generated by `lib/gordiehowe/compiler/plan_export.h` from the compiled system; do not edit.

- configuration: `toy-wide`, system `gordiehowe:gh-plan-export-toy`, compile profile `default v1`
- C++ commit: `c0ffee`
- bench run: `run-0`
- system digest: `13d49f6e0069436c536ed257917bfd21dc8eae5bfb590f484201117f2981c25fc0b5845847fe9cbce6f03f03fbbfb4a7`
- circuit ids: H `a871f316d9cdd0ef3875603ccfd140a9e5def9342085ff223ba96aa7ccba66c8337058921eee77589fa69aaf8dec1852`, A `ad8ce39e5d89e9899eabc4bff649536da93b0371d5102fc55921157d061ea6965c88ba1c462cd536a62298ef593c2611`

Coordinate ranges are circuit inputs (input 0 is the constant one); phases are the C++'s.
-/

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace GordieHowe.Generated.Toy.QROMParams.Plan

/-- The compiled plan of `toy-wide`. Sealed: importers see the name, not the body; only the modules that check the plan import it with `import all`. -/
@[no_expose, irreducible] def plan : GordieHowe.RealizedProgram.Export.Plan :=
  { schemaVersion := 3,
    config := "toy-wide",
    cppCommit := "c0ffee",
    runId := "run-0",
    digest := "13d49f6e0069436c536ed257917bfd21dc8eae5bfb590f484201117f2981c25fc0b5845847fe9cbce6f03f03fbbfb4a7",
    msgLen := 0,
    ctxLen := 0,
    hash := "SHA-384",
    opaqueSet := "targetBits",
    phases := 2,
    domains := [{ name := "H",
                  field := { name := "GF(2^256)",
                             characteristic := 2,
                             degree := 256,
                             modulus := [256, 10, 5, 2, 0] },
                  subfields := [{ name := "bit", characteristic := 2, degree := 1 },
                                { name := "GF(2^16)",
                                  characteristic := 2,
                                  degree := 16,
                                  modulus := [16, 14, 13, 12, 9, 8, 5, 3, 0] }],
                  maskingSubfield := "GF(2^16)",
                  prime := "prime",
                  ligero := { rate := 4,
                              blockEnc := 1024,
                              N := 685,
                              k := 170,
                              t := 64,
                              r := 64,
                              nrow := 20,
                              masking := .uniqueDecoding },
                  packing := [{ child := "bit",
                                parent := "GF(2^16)",
                                mode := .squaringChain,
                                degree := 16,
                                measurements := 16,
                                masks := 16,
                                chainCells := 120,
                                childDegree := 1,
                                parentDegree := 16,
                                declared := true,
                                routedRows := 2 },
                              { child := "GF(2^16)",
                                parent := "GF(2^256)",
                                mode := .subfieldMasks,
                                degree := 16,
                                measurements := 16,
                                masks := 256,
                                childDegree := 16,
                                parentDegree := 256,
                                declared := true,
                                routedRows := 0 }],
                  coords := [{ name := "select.delta",
                               offset := 1,
                               length := 1,
                               cellType := "Field",
                               storage := "public",
                               phase := 1 },
                             { name := "select.raw.words",
                               offset := 2,
                               length := 512,
                               cellType := "Subfield",
                               storage := "committed" },
                             { name := "select.count",
                               offset := 514,
                               length := 520,
                               cellType := "Subfield",
                               storage := "committed" },
                             { name := "select.raw",
                               offset := 1040,
                               length := 8192,
                               cellType := "Bit",
                               storage := "view" },
                             { name := "stream",
                               offset := 9232,
                               length := 8320,
                               cellType := "Bit",
                               storage := "committed" },
                             { name := "select.full",
                               offset := 17552,
                               length := 8,
                               cellType := "Bit",
                               storage := "committed" },
                             { name := "pad8",
                               offset := 17568,
                               length := 1,
                               cellType := "Field",
                               storage := "pad" }],
                  inputs := 17569,
                  publicInputs := 2,
                  circuits := [{ name := "H", layers := 15, wires := 35841, quadTerms := 47781 }],
                  circuitId := "a871f316d9cdd0ef3875603ccfd140a9e5def9342085ff223ba96aa7ccba66c8337058921eee77589fa69aaf8dec1852",
                  affineRows := [("select.start", 1), ("mac.H", 1)],
                  quadTriples := 0,
                  batches := [],
                  streamPoints := [{ name := "stage:1", rows := 18, streamBytes := 209200 },
                                   { name := "root", rows := 34, streamBytes := 211248 },
                                   { name := "ligero.alphal", rows := 17, streamBytes := 209072 }],
                  characteristicFloor := 2,
                  placements := [{ name := "select.start", target := .affine, instances := 1 },
                                 { name := "select.step", target := .circuit, instances := 519 },
                                 { name := "select.done", target := .circuit, instances := 8 },
                                 { name := "select.route", target := .circuit, instances := 1 },
                                 { name := "mac.H", target := .affine, instances := 1 }] },
                { name := "A",
                  field := { name := "Goldilocks^4",
                             characteristic := 18446744069414584321,
                             degree := 4,
                             modulus := [4, 0],
                             modulusCoeffs := [1, 18446744069414584314] },
                  subfields := [{ name := "GF(p^1)",
                                  characteristic := 18446744069414584321,
                                  degree := 1 }],
                  maskingSubfield := "GF(p^1)",
                  prime := "subfield",
                  ligero := { rate := 4,
                              blockEnc := 1535,
                              N := 1024,
                              k := 256,
                              t := 64,
                              r := 64,
                              nrow := 21,
                              masking := .uniqueDecoding },
                  packing := [{ child := "GF(p^1)",
                                parent := "Goldilocks^4",
                                mode := .subfieldMasks,
                                degree := 4,
                                measurements := 4,
                                masks := 16,
                                childDegree := 1,
                                parentDegree := 4,
                                declared := true,
                                routedRows := 0 }],
                  coords := [{ name := "mac.target_bits",
                               offset := 1,
                               length := 256,
                               cellType := "Bit",
                               storage := "public",
                               phase := 1 },
                             { name := "mac.acc",
                               offset := 257,
                               length := 256,
                               cellType := "Subfield",
                               storage := "message",
                               phase := 1 },
                             { name := "mac.low",
                               offset := 513,
                               length := 256,
                               cellType := "Subfield",
                               storage := "message",
                               phase := 1 },
                             { name := "range.dynamic:A.128",
                               offset := 769,
                               length := 128,
                               cellType := "Subfield",
                               storage := "message",
                               phase := 1 },
                             { name := "alpha:A",
                               offset := 897,
                               length := 1,
                               cellType := "Field",
                               storage := "public",
                               phase := 2 },
                             { name := "range.weights:A.128",
                               offset := 898,
                               length := 128,
                               cellType := "Field",
                               storage := "public",
                               phase := 2 },
                             { name := "samples",
                               offset := 1026,
                               length := 8192,
                               cellType := "Bit",
                               storage := "committed" },
                             { name := "mac.blind",
                               offset := 9218,
                               length := 256,
                               cellType := "Bit",
                               storage := "committed" },
                             { name := "range.v.d0",
                               offset := 9474,
                               length := 4,
                               cellType := "Subfield",
                               storage := "committed" },
                             { name := "range.v.d1",
                               offset := 9478,
                               length := 4,
                               cellType := "Subfield",
                               storage := "committed" },
                             { name := "pad(mac.acc)",
                               offset := 9482,
                               length := 256,
                               cellType := "Subfield",
                               storage := "pad" },
                             { name := "pad(mac.low)",
                               offset := 9738,
                               length := 256,
                               cellType := "Subfield",
                               storage := "pad" },
                             { name := "pad(range.dynamic:A.128)",
                               offset := 9994,
                               length := 128,
                               cellType := "Subfield",
                               storage := "pad" }],
                  inputs := 10151,
                  publicInputs := 1026,
                  circuits := [{ name := "A", layers := 12, wires := 12258, quadTerms := 6223 }],
                  circuitId := "ad8ce39e5d89e9899eabc4bff649536da93b0371d5102fc55921157d061ea6965c88ba1c462cd536a62298ef593c2611",
                  affineRows := [("mac.A", 256)],
                  quadTriples := 1,
                  batches := [{ name := "A.boolean",
                                operandField := "GF(p^1)",
                                arity := 1,
                                degree := 2,
                                instances := 8448,
                                width := 4,
                                rounds := 12,
                                pads := 29 }],
                  streamPoints := [{ name := "root", rows := 271, streamBytes := 241584 },
                                   { name := "ligero.alphal", rows := 5, streamBytes := 207536 }],
                  characteristicFloor := 18446744069414584321 }],
    requests := [{ name := "v",
                   domain := "A",
                   dim := 4,
                   expr := { terms := [.node "v"], coeffs := [1], const := 0 },
                   honest := 3000,
                   max := 4194304,
                   phase := 0,
                   realization := { kind := .digits,
                                    limbs := 2,
                                    bound := 16384,
                                    staticNeedles := 2,
                                    lateNeedles := 0 } },
                 { name := "mac.low",
                   domain := "A",
                   dim := 256,
                   expr := { terms := [.node "mac.low"], coeffs := [1], const := 0 },
                   honest := 128,
                   max := 71499008020986761,
                   phase := 1,
                   realization := { kind := .directLate,
                                    bound := 128,
                                    staticNeedles := 0,
                                    lateNeedles := 1 } },
                 { name := "mac.high",
                   domain := "A",
                   dim := 256,
                   expr := { terms := [.node "mac.high"], coeffs := [1], const := 0 },
                   honest := 128,
                   max := 71499008020986761,
                   phase := 1,
                   realization := { kind := .directLate,
                                    bound := 128,
                                    staticNeedles := 0,
                                    lateNeedles := 1 } },
                 { name := "mac.nowrap",
                   domain := "A",
                   dim := 256,
                   expr := { terms := [.node "mac.low", .node "mac.high"],
                             coeffs := [2, 256],
                             const := 0 },
                   honest := 32546,
                   max := 18446744069414584320,
                   phase := 1,
                   realization := { kind := .implied,
                                    intervalHi := 32766,
                                    bound := 32767,
                                    staticNeedles := 0,
                                    lateNeedles := 0 } }],
    bindings := [{ value := "v", request := "v", kind := .digits }],
    tables := [{ domain := "A",
                 size := 128,
                 sdyn := 128,
                 staticNeedles := 8,
                 lateNeedles := 512,
                 challenge := "alpha:A",
                 name := "A.128",
                 capacity := 18446744069414584320,
                 histogram := .lateOnly }],
    macs := [{ name := "mac",
               tagDomain := "H",
               accDomain := "A",
               width := 256,
               nch := 32,
               taps := [0, 2, 5, 10],
               convMax := 1017,
               accMax := 32545,
               radixBits := 8,
               tail := .digits,
               tailDigits := 2,
               nLow := 128,
               nHigh := 128,
               challenge := "mac.beta" }],
    selections := [{ name := "select",
                     domain := "H",
                     kind := .fixedCutoff,
                     candidates := 520,
                     outputs := 512,
                     width := 16,
                     bound := 60000,
                     challenge := "select.delta" }],
    modEqualities := [{ name := "mac",
                        domain := "A",
                        modulus := 2,
                        expr := { terms := [.node "mac.blind",
                                            .op "mac_conv(samples)",
                                            .node "mac.target_bits"],
                                  coeffs := [1, 1, -1],
                                  const := 0 },
                        dim := 256,
                        quotient := .digits,
                        digits := 2,
                        base := 128,
                        topDerived := true,
                        intervalLo := -1,
                        intervalHi := 32545 }],
    gadgets := [{ name := "mac.leftSpan",
                  kind := "certify",
                  domain := "A",
                  params := [("lhs", 32545), ("rhs", 18446744069414584321), ("op", 0)] },
                { name := "mac.rightSpan",
                  kind := "certify",
                  domain := "A",
                  params := [("lhs", 32545), ("rhs", 18446744069414584321), ("op", 0)] },
                { name := "mac.digits",
                  kind := "certify",
                  domain := "A",
                  params := [("lhs", 18446744069414584081),
                             ("rhs", 18446744069414584321),
                             ("op", 0)] },
                { name := "range.v.table",
                  kind := "certify",
                  domain := "A",
                  params := [("lhs", 128), ("rhs", 18446744069414584321), ("op", 1)] },
                { name := "range.v.digits",
                  kind := "certify",
                  domain := "A",
                  params := [("lhs", 16384), ("rhs", 18446744069414584321), ("op", 1)] },
                { name := "range.mac.low.table",
                  kind := "certify",
                  domain := "A",
                  params := [("lhs", 128), ("rhs", 18446744069414584321), ("op", 1)] },
                { name := "range.mac.high.table",
                  kind := "certify",
                  domain := "A",
                  params := [("lhs", 128), ("rhs", 18446744069414584321), ("op", 1)] },
                { name := "range.table:A.128.counts",
                  kind := "certify",
                  domain := "A",
                  params := [("lhs", 520), ("rhs", 18446744069414584321), ("op", 0)] },
                { name := "range.table:A.128.support",
                  kind := "certify",
                  domain := "A",
                  params := [("lhs", 128), ("rhs", 128), ("op", 1)] },
                { name := "mac_conv(samples)",
                  kind := "op-bound",
                  domain := "A",
                  params := [("rowSum", 32544)] },
                { name := "mac.powers",
                  kind := "public-compute",
                  domain := "H",
                  params := [("cached", 0), ("perMessage", 1), ("n", 32), ("phase", 1)] },
                { name := "mac.target_bits",
                  kind := "public-compute",
                  domain := "A",
                  params := [("cached", 0), ("perMessage", 1), ("n", 256), ("phase", 1)] },
                { name := "range.weights:A.128",
                  kind := "public-compute",
                  domain := "A",
                  params := [("cached", 0), ("perMessage", 1), ("n", 128), ("phase", 2)] }],
    sampleInBalls := [],
    challenges := [{ label := "select.delta",
                     domain := "H",
                     phase := 1,
                     sampler := "field",
                     degreeBound := 520,
                     tests := ["stream", "select.raw", "select.count", "select.full"] },
                   { label := "mac.beta",
                     domain := "H",
                     phase := 1,
                     sampler := "field",
                     degreeBound := 32,
                     tests := ["select.raw", "samples", "pad8", "mac.blind"] },
                   { label := "alpha:A",
                     domain := "A",
                     phase := 2,
                     sampler := "field-minus-tables",
                     degreeBound := 775,
                     tests := ["mac.low",
                               "mac.high",
                               "range.v.d0",
                               "range.v.d1",
                               "range.dynamic:A.128"] }],
    messages := [{ name := "mac.value",
                   domain := "H",
                   phase := 1,
                   size := 1,
                   bytes := 32,
                   maskingSpace := "Field",
                   subfieldMessage := false,
                   padSpace := "GF(2^256)" },
                 { name := "mac.acc",
                   domain := "A",
                   phase := 1,
                   size := 256,
                   bytes := 2048,
                   maskingSpace := "Subfield",
                   subfieldMessage := true,
                   padSpace := "GF(p^1)" },
                 { name := "mac.low",
                   domain := "A",
                   phase := 1,
                   size := 256,
                   bytes := 2048,
                   maskingSpace := "Subfield",
                   subfieldMessage := true,
                   padSpace := "GF(p^1)" },
                 { name := "range.dynamic:A.128",
                   domain := "A",
                   phase := 1,
                   size := 128,
                   bytes := 1024,
                   maskingSpace := "Subfield",
                   subfieldMessage := true,
                   padSpace := "GF(p^1)" }] }

end GordieHowe.Generated.Toy.QROMParams.Plan
)lean";

// A late value of GF(2^32) < GF(2^256): its message lies in a proper
// subfield, and its pad in the packing tree's GF(2^32) node, named as the
// packing edge's child is; the pad's cell is a GF(2^32) cell.
TEST(GordieHowePlanExport, LateSubfieldPadSpace) {
  static const Env *e = new Env;
  Sys cs{"gh-plan-export-late"};
  auto &H = cs.domain(e->h_profile(), "H");
  auto w = H.priv(Subfield<GF<32>>{}, "w", 3);
  auto c = H.challenge("c", Subfield{});
  const HF *ph = &e->hf;
  auto x = H.priv(Subfield<GF<32>>{}, "x", 3, depends_on(c, w),
                  [ph](const HV &c, const HV &w) {
                    HV x(w.size());
                    for (size_t i = 0; i < w.size(); ++i)
                      x[i] = ph->mulf(c[0], w[i]);
                    return x;
                  });
  assert_equal(x, c * w, "x = c w").pin(Placement::kCircuit);
  const std::string out = compiler::export_lean_plan(
      *compile(cs), compiler::ExportMeta{"late", "wide", "c0ffee", "run-0", 0});
  EXPECT_NE(out.find("maskingSpace := \"Subfield\",\n"
                     "                   subfieldMessage := true,\n"
                     "                   padSpace := \"GF(2^32)\""),
            std::string::npos)
      << out;
  EXPECT_NE(out.find("child := \"GF(2^32)\""), std::string::npos) << out;
  EXPECT_NE(out.find("{ name := \"pad(x)\",\n"
                     "                               offset := 8,\n"
                     "                               length := 3,\n"
                     "                               cellType := "
                     "\"Subfield<GF<32>>\",\n"
                     "                               storage := \"pad\" }"),
            std::string::npos)
      << out;
}

// Two bit-sliced predicates of different forms on the same coordinates,
// merged into one batch (Domain::merge_batch): s = m & y (m y + s = 0) and
// t = m ^ y (m + y + t = 0). The program has one batch of both parts with
// its merged flag set, the plan its merge group; an honest proof verifies, and a
// witness that violates one relation is rejected.
TEST(GordieHowePlanExport, MergedBitBatch) {
  static const Env *e = new Env;
  const HF &f = e->hf;
  constexpr size_t n = 128;
  Sys cs{"gh-plan-export-merged"};
  auto &H = cs.domain(e->h_profile(), "H");
  auto m = H.priv(Bit{}, "m", n);
  auto y = H.priv(Bit{}, "y", n);
  auto s = H.priv(Bit{}, "s", n);
  auto t = H.priv(Bit{}, "t", n);
  const auto chi = assert_zero((m & y) ^ s, "chi");
  const auto xr = assert_zero(m ^ y ^ t, "xor");
  H.merge_batch("merged", {chi, xr});
  const auto comp = compile(cs);
  const compiler::ExportMeta meta{"merged", "wide", "c0ffee", "run-0", 0};
  const auto p = compiler::build_program(*comp, meta);
  for (const auto &x : compiler::program_errors(p)) ADD_FAILURE() << x;
  for (const auto &x : compiler::module_errors(p)) ADD_FAILURE() << x;
  const std::string prog = compiler::export_lean_program(*comp, meta);
  const size_t at = prog.find("name := \"merged\"");
  ASSERT_NE(at, std::string::npos) << prog;
  const std::string batch = prog.substr(at, prog.find('}', at) - at);
  EXPECT_NE(batch.find("operands := .bits"), std::string::npos) << batch;
  EXPECT_NE(batch.find("degree := 2"), std::string::npos) << batch;
  EXPECT_NE(batch.find("merged := true"), std::string::npos) << batch;
  EXPECT_NE(batch.find("bitSumcheck := true"), std::string::npos) << batch;
  const std::string plan = compiler::export_lean_plan(*comp, meta);
  EXPECT_NE(plan.find("mergeGroup := some \"merged\""), std::string::npos)
      << plan;
  EXPECT_EQ(comp->compiled_domain(0).plan().batches.size(), 1u);
  EXPECT_TRUE(comp->compiled_domain(0).plan().batches[0].merged);
  // With GH_MERGED_LEAN_DIR set, the same relations on the default narrow
  // GF(2^128) domain profile (whose masks, tableau and packing edges the
  // Lean check accepts) are exported there as
  // GordieHowe.Generated.Heldout.MergedBits.ROMParams, for a Lean check of a
  // merged batch.
  if (const char *dir = std::getenv("GH_MERGED_LEAN_DIR")) {
    using P = param_sets::ROMParams;
    using NF = GF2_128<>;
    static const NF *nf = new NF;
    static const auto *nrs = new LCH14ReedSolomonFactory<NF>(*nf);
    ConstraintSystem<P::ProtocolHash, NF> ls{"gh-plan-export-merged-lean"};
    auto &LH = ls.domain(examples::domain_profile<P>(*nf, *nrs), "H");
    auto lm = LH.priv(Bit{}, "m", n);
    auto ly = LH.priv(Bit{}, "y", n);
    auto lsv = LH.priv(Bit{}, "s", n);
    auto lt = LH.priv(Bit{}, "t", n);
    const auto lchi = assert_zero((lm & ly) ^ lsv, "chi");
    const auto lxr = assert_zero(lm ^ ly ^ lt, "xor");
    LH.merge_batch("merged", {lchi, lxr});
    compiler::ExportMeta lean{"merged", P::kId, "c0ffee", "run-0", 0};
    lean.lean_name = "Heldout.MergedBits.ROMParams";
    examples::write_plan(*compile(ls), dir, lean);
  }

  std::mt19937_64 g(9);
  HV vm(n), vy(n), vs(n), vt(n);
  for (size_t i = 0; i < n; ++i) {
    const bool a = g() & 1, b = g() & 1;
    vm[i] = a ? f.one() : f.zero();
    vy[i] = b ? f.one() : f.zero();
    vs[i] = (a && b) ? f.one() : f.zero();
    vt[i] = (a != b) ? f.one() : f.zero();
  }
  Sys::Assignment w;
  w.set(m, vm).set(y, vy).set(s, vs).set(t, vt);
  auto prep = comp->prepare(Sys::Assignment{});
  SecureRandomEngine rng;
  EXPECT_TRUE(prep.verify(prep.prove(w, rng))) << comp->report();
  Sys::ProveOptions opt;
  opt.require_satisfied = false;
  for (auto *v : {&vs, &vt}) {
    auto cheat = w;
    HV bad = *v;
    f.add(bad[37], f.one());
    cheat.set(v == &vs ? s : t, bad);
    EXPECT_FALSE(prep.verify(prep.prove(cheat, rng, opt)));
  }
}

// A domain with no circuit constraint runs no GKR: its plan lists no
// circuit, and its first stream point counts its own rows only.
TEST(GordieHowePlanExport, CircuitFreeDomain) {
  static const Env *e = new Env;
  Sys cs{"gh-plan-export-nogkr"};
  auto &A = cs.domain(e->a_profile(), "A");
  auto t = A.pub(Subfield{}, "t", 4);
  auto v = A.priv(Subfield{}, "v", 4);
  assert_zero(v - t);
  const auto c = compile(cs);
  EXPECT_FALSE(c->compiled_domain(0).plan().gkr);
  const std::string out = compiler::export_lean_plan(
      *c, compiler::ExportMeta{"nogkr", "wide", "c0ffee", "run-0", 0});
  EXPECT_NE(out.find("circuits := [],"), std::string::npos) << out;
}

// A domain whose size search takes untested masks exports the masking the
// Lean's LigeroCert.matchesB reads for them, .listRadius (Masking.kind),
// with its tableau's numbers; split masks export .split. The masking is
// forced through the mask-test ablation's hook, at the post-quantum target.
TEST(GordieHowePlanExport, UntestedMasksExportAsListRadius) {
  static const Env *e = new Env;
  for (const LigeroMasking m :
       {LigeroMasking::kUntested, LigeroMasking::kSplit}) {
    Sys cs{"gh-plan-export-untested"};
    auto p = e->a_profile();
    p.block_enc = nullptr;
    p.target = compiler::LigeroTarget::kPostQuantum;
    p.rate = 6;
    p.block_grid = compiler::BlockGrid::kPowerOfTwoBlock;
    auto &A = cs.domain(p, "A");
    auto v = A.priv(Subfield{}, "v", 4);
    assert_range(v, 3000, MaxBound{Bound(1) << 22}, "v");
    CompileOptions o;
    o.ligero_masking = m;
    const auto c = compile(cs, CompileProfile{}, o);
    const DomainPlan pl = c->compiled_domain(0).plan();
    EXPECT_TRUE(pl.list_radius);
    EXPECT_EQ(pl.split, m == LigeroMasking::kSplit);
    const std::string out = compiler::export_lean_plan(
        *c, compiler::ExportMeta{"untested", "wide", "c0ffee", "run-0", 0});
    EXPECT_NE(out.find(m == LigeroMasking::kSplit ? "masking := .split"
                                                  : "masking := .listRadius"),
              std::string::npos)
        << out;
    EXPECT_EQ(out.find("masking := .uniqueDecoding"), std::string::npos)
        << out;
    EXPECT_NE(out.find("t := " + std::to_string(pl.t)), std::string::npos)
        << out;
    EXPECT_NE(out.find("k := " + std::to_string(pl.k)), std::string::npos)
        << out;
    EXPECT_NE(out.find("N := " + std::to_string(pl.N)), std::string::npos)
        << out;
  }
}

// assert_int_equal is the program's mod_0: the integer form with the
// sides' intervals, their span below p and the field equation's target.
// Its Slack operands' in records carry the honest bound and the maximum
// the equality derived.
TEST(GordieHowePlanExport, IntegerEquality) {
  static const Env *e = new Env;
  Sys cs{"gh-plan-export-int"};
  auto &A = cs.domain(e->a_profile(), "A");
  auto x = A.priv(Subfield{}, "x", 4);
  auto y = A.priv(Subfield{}, "y", 4);
  auto c = A.priv(Subfield{}, "c", 4);
  assert_range(x, 100, Slack{}, "x");
  assert_range(y, 100, Slack{}, "y");
  assert_range(c, 200, "c");
  assert_int_equal(x + y, c, "sum");
  const auto comp = compile(cs);
  const auto p = compiler::build_program(
      *comp, compiler::ExportMeta{"int", "wide", "c0ffee", "run-0", 0});
  for (const auto &x : compiler::program_errors(p)) ADD_FAILURE() << x;
  for (const auto &x : compiler::module_errors(p)) ADD_FAILURE() << x;
  auto body = [&](const std::string &nm) {
    for (const auto &q : p.predicates)
      if (q.name == nm) return q.body;
    ADD_FAILURE() << "no predicate " << nm;
    return std::string();
  };
  // m = 100 + D for the largest D with 2 (99 + D) < p.
  const Bound pc = field_characteristic(e->af);
  const Bound m = 100 + (pc - 199) / 2;
  const std::string hi = bound_str(2 * (m - 1));
  const std::string sum = body("sum");
  for (const std::string want :
       {std::string(".mod 0 0 ("), std::string("form := .integer"),
        "lhsLo := 0, lhsHi := " + hi + ", rhsLo := 0, rhsHi := 199",
        std::string("quotient := none"), std::string("ranges := [], bounds := []"),
        std::string("target := some .affine"), "span := some " + hi})
    EXPECT_NE(sum.find(want), std::string::npos) << want << "\n" << sum;
  EXPECT_EQ(sum.find(".equal"), std::string::npos) << sum;
  const std::string honest = "honest := 100, max := " + bound_str(m);
  EXPECT_NE(body("x").find(honest), std::string::npos) << body("x");
  EXPECT_NE(body("y").find(honest), std::string::npos) << body("y");
}

// NegacyclicConv's forms: by h with an entry bound, the coefficient form
// (its parameters hold the bound, no root); by a spectrum, the NTT form
// with the scheme root psi, psi^n = -1 in the prime field (the exporter
// fails on any other root).
TEST(GordieHowePlanExport, NegacyclicConvForms) {
  static const Env *e = new Env;
  const AF &af = e->af;
  constexpr size_t n = 8;
  Sys cs{"gh-plan-export-negacyclic"};
  auto &A = cs.domain(e->a_profile(), "A");
  auto h = A.pub(Subfield{}, "h", n);
  auto khat = A.pub(Subfield{}, "khat", n);
  auto x = A.priv(Subfield{}, "x", n);
  auto y = A.priv(Subfield{}, "y", n);
  auto z = A.priv(Subfield{}, "z", n);
  assert_range(x, 100, "x");
  assert_equal(y, ops::NegacyclicConv(h, ops::EntryBound{100})(x), "y = h * x");
  assert_equal(z, ops::NegacyclicConv(ops::Spectrum{khat})(x), "z = khat * x");
  const auto comp = compile(cs);
  const auto p = compiler::build_program(
      *comp, compiler::ExportMeta{"negacyclic", "wide", "c0ffee", "run-0", 0});
  for (const auto &m : compiler::program_errors(p)) ADD_FAILURE() << m;
  const auto psi = ops::FieldNtt<AF>::scheme_psi(af, n);
  ASSERT_TRUE(psi.has_value());
  AF::Elt pw = af.one();
  for (size_t i = 0; i < n; ++i) pw = af.mulf(pw, *psi);
  ASSERT_EQ(pw, af.mone());
  const std::string root = bound_str(nat_of(af, *psi));
  EXPECT_NE(p.text.find(" .coefficients"), std::string::npos) << p.text;
  EXPECT_NE(p.text.find("(.ntt " + root + ")"), std::string::npos) << p.text;
  // One NTT-form operator: the entry-bound one has no root.
  size_t ntt = 0;
  for (size_t at = p.text.find("(.ntt "); at != std::string::npos;
       at = p.text.find("(.ntt ", at + 1))
    ++ntt;
  EXPECT_EQ(ntt, 1u) << p.text;
}

// A public computation that reads the statement's bytes is a function of
// the statement, not of the values it reads: it exports as an opaque value
// with no argument (read from the statement). One that reads only values
// exports them as its arguments.
TEST(GordieHowePlanExport, OpaqueOfStatementBytesHasNoArguments) {
  static const Env *e = new Env;
  const AF &af = e->af;
  Sys cs{"gh-plan-export-opaque-bytes"};
  auto &A = cs.domain(e->a_profile(), "A");
  auto msg = A.pub_bytes("msg", 4);
  auto t = A.pub(Subfield{}, "t", 2);
  auto u = A.pub(Subfield{}, "u", 2, depends_on(t, msg), computes("u_of_t_msg"),
                 [&af](const std::vector<AF::Elt> &tv,
                       const std::vector<uint8_t> &m) {
                   AV out;
                   for (size_t i = 0; i < 2; ++i)
                     out.push_back(af.addf(tv[i], af.of_scalar(m[i])));
                   return out;
                 });
  auto w = A.pub(Subfield{}, "w", 2, depends_on(t), computes("w_of_t"),
                 [&af](const std::vector<AF::Elt> &tv) {
                   AV out;
                   for (size_t i = 0; i < 2; ++i)
                     out.push_back(af.addf(tv[i], tv[i]));
                   return out;
                 });
  auto x = A.priv(Subfield{}, "x", 2);
  auto y = A.priv(Subfield{}, "y", 2);
  assert_zero(x - u);
  assert_zero(y - w);
  const auto c = compile(cs);
  const auto p = compiler::build_program(
      *c, compiler::ExportMeta{"opaque-bytes", "wide", "c0ffee", "run-0", 0});
  for (const auto &m : compiler::program_errors(p)) ADD_FAILURE() << m;
  auto value = [&](const std::string &nm) -> const compiler::ProgramData::Value * {
    for (const auto &v : p.values)
      if (v.name == nm) return &v;
    return nullptr;
  };
  const auto *vu = value("u");
  const auto *vw = value("w");
  ASSERT_NE(value("t"), nullptr);
  ASSERT_NE(vu, nullptr);
  ASSERT_NE(vw, nullptr);
  EXPECT_EQ(vu->kind, "opaque");
  EXPECT_TRUE(vu->args.empty());
  EXPECT_EQ(vw->kind, "opaque");
  ASSERT_EQ(vw->args.size(), 1u);
  EXPECT_EQ(p.values.at(vw->args[0]).name, "t");
  EXPECT_NE(p.text.find("(.«opaque» \"u\" [])"), std::string::npos)
      << p.text;
}

// Constant shapes preserve every entry, including zeros and repeated entries.
TEST(GordieHowePlanExport, ShapeConstant) {
  ir::Program prog;
  ir::Value value;
  value.name = "constant";
  value.kind = ir::Value::kConstant;
  value.entries = {"38", "0", "38", "1"};
  prog.values.push_back(value);
  const auto facts = compiler::shape_facts_of(prog, {"constant-test", {0}, {}});
  ASSERT_EQ(facts.size(), 1u);
  EXPECT_EQ(facts[0].claim, ".kindConstant 0 [38, 0, 38, 1]");
  EXPECT_EQ(facts[0].statement,
            "(Program.program.value 0).kind = .constant [38, 0, 38, 1]");
  EXPECT_EQ(facts[0].sound, "kindConstant");
}

TEST(GordieHowePlanExport, ShapeEqualityHeader) {
  ir::Program prog;
  ir::Predicate q;
  q.name = "padding";
  q.reads = {{ir::Read::kChal, 2}};
  q.degree = {{2, 3}};
  q.role = ir::Predicate::Role::kType;
  q.owner = 7;
  q.target = {ir::Target::kGkr, 4};
  // No expression arena is needed to read only the predicate header.
  prog.predicates.push_back(q);
  const compiler::ShapeInputs inputs{"header-test", {}, {}, {}, {0}};
  const auto facts = compiler::shape_facts_of(prog, inputs);
  ASSERT_EQ(facts.size(), 1u);
  EXPECT_EQ(facts[0].name, "predicate_0_header");
  EXPECT_EQ(facts[0].claim,
      ".equalHeader 0 (\"padding\", [.chal 2], [(2, 3)], .type 7, some (.gkr 4))");
  EXPECT_EQ(facts[0].sound, "equalHeader");
  prog.predicates[0].body = ir::Predicate::kMem;
  EXPECT_THROW(compiler::shape_facts_of(prog, inputs), std::runtime_error);
  prog.predicates.clear();
  EXPECT_THROW(compiler::shape_facts_of(prog, inputs), std::runtime_error);
}

// The shape facts (shape_facts_of, shapes_module, shape_check_modules): one claim and one
// named fact per listed value (its kind) and predicate (its body's parts),
// checked once by shapesB; a kind or body no claim states is refused; a
// configuration with no shape inputs has no Shapes module.
TEST(GordieHowePlanExport, ShapeFacts) {
  static const Env *e = new Env;
  const AF &af = e->af;
  Sys cs{"gh-plan-export-shape-facts"};
  auto &A = cs.domain(e->a_profile(), "A");
  auto t = A.pub(Subfield{}, "t", 2);
  auto w = A.pub(Subfield{}, "w", 2, depends_on(t), computes("w_of_t"),
                 [&af](const std::vector<AF::Elt> &tv) {
                   AV out;
                   for (size_t i = 0; i < 2; ++i) out.push_back(af.addf(tv[i], tv[i]));
                   return out;
                 });
  auto y = A.priv(Subfield{}, "y", 2);
  assert_zero(y - w);
  const auto c = compile(cs);
  const ir::Program &prog = c->program();
  auto id = [&](const std::string &nm) {
    for (size_t i = 0; i < prog.values.size(); ++i)
      if (prog.values[i].name == nm) return i;
    ADD_FAILURE() << "no value " << nm;
    return size_t(0);
  };
  size_t eq = SIZE_MAX;
  for (size_t i = 0; i < prog.predicates.size(); ++i)
    if (prog.predicates[i].body == ir::Predicate::kEqual && eq == SIZE_MAX) eq = i;
  ASSERT_NE(eq, SIZE_MAX);
  const size_t vy = id("y"), vw = id("w");
  const compiler::ShapeInputs in{"shape-test", {vy, vw}, {eq}};
  const auto facts = compiler::shape_facts_of(prog, in);
  ASSERT_EQ(facts.size(), 3u);
  EXPECT_EQ(facts[0].claim, ".kindPriv " + std::to_string(vy));
  EXPECT_EQ(facts[0].name, "value_" + std::to_string(vy) + "_kind");
  EXPECT_EQ(facts[0].statement,
            "(Program.program.value " + std::to_string(vy) + ").kind = .priv");
  EXPECT_EQ(facts[1].claim, ".kindOpaque " + std::to_string(vw) + " \"w\" [" +
                                std::to_string(id("t")) + "]");
  EXPECT_EQ(facts[1].sound, "kindOpaque");
  EXPECT_EQ(facts[2].name, "predicate_" + std::to_string(eq) + "_body");
  EXPECT_EQ(facts[2].claim.rfind(".equalParts " + std::to_string(eq) + " ", 0), 0u)
      << facts[2].claim;
  EXPECT_EQ(facts[2].statement.rfind("∃ t, (Program.program.predicate " +
                                         std::to_string(eq) + ").body = .equal ",
                                     0),
            0u)
      << facts[2].statement;
  // The claim's parts are the statement's.
  const std::string parts = facts[2].claim.substr(std::string(".equalParts ").size() +
                                                  std::to_string(eq).size() + 1);
  EXPECT_NE(facts[2].statement.find(".equal " + parts + " t"), std::string::npos)
      << facts[2].statement;
  // Plain public inputs have no claim; out-of-range indices are refused.
  const compiler::ShapeInputs input{"shape-test", {id("t")}, {}};
  EXPECT_THROW(compiler::shape_facts_of(prog, input), std::runtime_error);
  const compiler::ShapeInputs past{"shape-test", {prog.values.size()}, {}};
  EXPECT_THROW(compiler::shape_facts_of(prog, past), std::runtime_error);
  const compiler::ShapeInputs past_expr{"shape-test", {}, {}, {prog.exprs.size()}};
  EXPECT_THROW(compiler::shape_facts_of(prog, past_expr), std::runtime_error);
  // A shared expression's entry: its claim and its fact name the same text.
  if (!prog.exprs.empty()) {
    const auto ef = compiler::shape_facts_of(prog, {"shape-test", {}, {}, {0}});
    ASSERT_EQ(ef.size(), 1u);
    EXPECT_EQ(ef[0].claim.rfind(".exprEq 0 (", 0), 0u) << ef[0].claim;
    EXPECT_EQ(ef[0].statement, "Program.program.expr 0 = " + ef[0].claim.substr(9));
    EXPECT_EQ(ef[0].sound, "exprEq");
  }
  // The modules: the data, the condition from the program's check, then one
  // fact per claim at its position.
  compiler::ProofModuleData d;
  d.meta = compiler::ExportMeta{"toy", "wide", "c0ffee", "run-0", 0};
  for (const auto &m : compiler::proof_modules(d))
    EXPECT_EQ(m.leaf.rfind("Shape", 0), std::string::npos) << m.leaf;
  d.shape_facts = facts;
  const compiler::ProofModule shapes = compiler::shapes_module(d);
  EXPECT_EQ(shapes.leaf, "Shapes");
  const auto mods = compiler::shape_check_modules(d);
  ASSERT_EQ(mods.size(), 2u);
  EXPECT_EQ(mods[0].leaf, "ShapesCheck");
  EXPECT_EQ(mods[1].leaf, "ShapeFacts");
  const std::string &data = shapes.text;
  EXPECT_NE(data.find("public import GordieHoweNative.Language.RealizedProgram.Shapes\n"),
            std::string::npos);
  EXPECT_NE(data.find("def shapes : List ShapeClaim := [\n  .kindPriv " + std::to_string(vy) +
                      ",\n  " + facts[1].claim + ",\n  " + facts[2].claim + "]"),
            std::string::npos)
      << data;
  const std::string &check = mods[0].text;
  EXPECT_NE(check.find("public import GordieHoweCheck.Toy.QROMParams\n"), std::string::npos)
      << check;
  EXPECT_NE(check.find("theorem shapesHold : ShapesHold Program.program Shapes.shapes :=\n"
                       "  (programOk_sound data GordieHoweCheck.Toy.QROMParams.programOk)."
                       "shapes\n"),
            std::string::npos)
      << check;
  const std::string &text = mods[1].text;
  for (size_t i = 0; i < facts.size(); ++i) {
    EXPECT_NE(text.find("theorem " + facts[i].name + " :\n    " + facts[i].statement +
                        " :=\n  ShapesCheck.shapesHold." + facts[i].sound + " (k := " +
                        std::to_string(i) + ") rfl"),
              std::string::npos)
        << text;
  }

}

TEST(GordieHowePlanExport, EmbeddingFactsSelectTheProfileAndNameTheSource) {
  compiler::ExportMeta meta;
  meta.config = "mldsa-emulated";
  meta.profile = "narrow";
  ProgramEmbeddingDecl d;
  d.name = "native.H";
  d.source_config = "mldsa-native";
  d.vals = {1, 2};
  d.refs = {2};
  d.chals = {0};
  d.values = {0, 1};
  d.exprs = {0};
  d.equals = {{3, 5}};
  ProgramEmbeddingDecl other = d;
  other.profile = "wide";
  std::vector<compiler::ProofModuleData::ShapeFact> facts;
  compiler::append_embedding_facts(meta, {d, other}, facts);
  ASSERT_EQ(facts.size(), 1u);
  EXPECT_EQ(facts[0].claim, ".embedding embedding_native_2eH_data");
  EXPECT_EQ(facts[0].import_module, "GordieHoweCerts.Generated.MLDSA44.Native.ROMParams.Program");
  EXPECT_NE(facts[0].definition.find("source := GordieHowe.Generated.MLDSA44.Native.ROMParams.Program.program"),
            std::string::npos);
  EXPECT_NE(facts[0].definition.find("equals := [(3, 5)]"), std::string::npos);
}

TEST(GordieHowePlanExport, RequestedPhaseCountAndExprTableAreClaimed) {
  ir::Program p;
  p.phases = 3;
  p.nodes.resize(1);
  p.nodes[0].op = ir::Expr::kLeaf;
  p.exprs = {0, 0};
  p.values.resize(1);
  compiler::ResolvedShapeInputs in;
  in.names.phase_count = true;
  in.names.exprs = {"first"};
  in.exprs = {0};
  in.names.expr_table_end = "first";
  std::vector<compiler::ProofModuleData::ShapeFact> facts;
  compiler::append_named_shape_metadata(p, in, facts);
  auto named = [&](const std::string &name) {
    return std::find_if(facts.begin(), facts.end(),
        [&](const auto &f) { return f.name == name; });
  };
  ASSERT_NE(named("phases_count"), facts.end());
  EXPECT_EQ(named("phases_count")->claim, ".phaseCount 3");
  ASSERT_NE(named("expr_table_holds"), facts.end());
  EXPECT_EQ(named("expr_table_holds")->claim, ".exprTable exprTable");
  in.names.expr_table_end = "absent";
  facts.clear();
  EXPECT_THROW(compiler::append_named_shape_metadata(p, in, facts), std::runtime_error);
}

TEST(GordieHowePlanExport, SourcePredicateRangesResolveByName) {
  NamedShapeInputs names;
  names.source_predicate_ranges = {{"first", "last"}};
  const compiler::NamedIds predicates{{"first", 2}, {"last", 7}};
  const auto in = compiler::resolve_shape_inputs(names, {}, predicates, {});
  ASSERT_EQ(in.source_predicate_ranges.size(), 1u);
  EXPECT_EQ(in.source_predicate_ranges[0], (std::pair<size_t, size_t>{2, 7}));
  names.source_predicate_ranges = {{"last", "first"}};
  EXPECT_THROW(compiler::resolve_shape_inputs(names, {}, predicates, {}), std::runtime_error);
}

TEST(GordieHowePlanExport, MldsaRingFrontendsNameTheirConsumerInputs) {
  using namespace examples::mldsa;
  auto has = [](const std::vector<std::string> &names, const char *name) {
    return std::find(names.begin(), names.end(), name) != names.end();
  };
  auto check = [&](const NamedShapeInputs &shapes) {
    EXPECT_EQ(std::set<std::string>(shapes.values.begin(), shapes.values.end()).size(),
              shapes.values.size());
    EXPECT_EQ(std::set<std::string>(shapes.exprs.begin(), shapes.exprs.end()).size(),
              shapes.exprs.size());
    EXPECT_EQ(std::set<std::string>(shapes.predicates.begin(), shapes.predicates.end()).size(),
              shapes.predicates.size());
    for (const char *name : {"member.select.shape.right", "hint.decompose.shape.one",
        "norm.z.offset"})
      EXPECT_TRUE(has(shapes.values, name)) << name;
    for (const char *name : {"member.select", "member.mu.boolean", "challenge.c.boolean"})
      EXPECT_TRUE(has(shapes.predicates, name)) << name;
    for (const char *name : {"member.table.powers.shape.definition.first.first",
        "member.table.powers.shape.definition.first.second",
        "member.table.digests.shape.definition.first.first.first",
        "mac.equal.shape.left.shared.first.second.second.first",
        "mac.equal.shape.left.shared.first.second.second.second"})
      EXPECT_TRUE(has(shapes.exprs, name)) << name;
  };
  Sys native("mldsa-ring-native-metadata");
  check(mldsa_ring_native_shape_inputs(native));
  Sys carrier("mldsa-ring-carrier-metadata");
  check(mldsa_ring_carrier_shape_inputs(carrier));
}

TEST(GordieHowePlanExport, MldsaSemanticMetadataUsesUniqueNames) {
  using namespace examples::mldsa;
  Sys cs("mldsa-semantic-metadata");
  auto shapes = mldsa_native_shape_inputs(cs);
  EXPECT_EQ(shapes.private_field_sources, std::vector<std::string>({"w1.words"}));
  mldsa_source_roles<MLDSA44>(cs, shapes, SourceFamily::kPossession);
  EXPECT_EQ(std::set<std::string>(shapes.values.begin(), shapes.values.end()).size(),
            shapes.values.size());
  for (const char *name : {"z", "h", "challenge.c", "signature.w", "hint.w1",
      "hint.nonpositive", "hint.offset", "hint.slack", "msg", "msg.in_message",
      "h2c.mu.blocks.r0.value.words", "h2c.mu.blocks.r0.value",
      "h2c.c_tilde.r167.value.words", "h2c.c_tilde.r167.value",
      "h2c.sib.r47.value.words", "h2c.sib.r47.value", "h2c.sample.mem.origin",
      "h2c.sample.select.threshold", "z.digit.low", "z.digit.high",
      "z.completion.low", "z.completion.high", "hint.offset.digit.low",
      "hint.offset.digit.high", "hint.slack.digit.low", "hint.slack.digit.high",
      "range.static:A.512", "mac.blind"})
    EXPECT_NE(std::find(shapes.values.begin(), shapes.values.end(), name), shapes.values.end());
  EXPECT_THROW(mldsa_source_roles<MLDSA44>(cs, shapes,
      static_cast<SourceFamily>(999)), std::runtime_error);
  EXPECT_THROW(mldsa_source_roles<MLDSA44>(cs, shapes,
      SourceFamily::kPossession, 0), std::runtime_error);
  Sys coeff("mldsa-coefficient-metadata");
  auto coefficient_shapes = mldsa_emulated_shape_inputs(coeff);
  mldsa_source_roles<MLDSA44>(coeff, coefficient_shapes,
      SourceFamily::kPossession, 1, 0, "key.a");
  EXPECT_NE(std::find(coefficient_shapes.values.begin(), coefficient_shapes.values.end(),
                      "key.a"), coefficient_shapes.values.end());
  EXPECT_EQ(std::find(coefficient_shapes.values.begin(), coefficient_shapes.values.end(),
                      "key.a_hat"), coefficient_shapes.values.end());
}

TEST(GordieHowePlanExport, PadCopyAndNamedPrivateFieldOwnership) {
  ir::Program p;
  p.values.resize(2);
  p.domains.resize(2);
  p.domains[0].field = 3;
  p.domains[1].field = 4;
  p.values[0].name = "mac.blind";
  p.values[0].kind = ir::Value::kPadCopy;
  p.values[0].ref = 7;
  p.values[0].domain = 0;
  p.values[1].name = "w1.words";
  p.values[1].kind = ir::Value::kPriv;
  p.values[1].domain = 1;
  compiler::ShapeInputs raw{"test", {0}, {}};
  auto kinds = compiler::shape_facts_of(p, raw);
  ASSERT_EQ(kinds.size(), 1);
  EXPECT_EQ(kinds[0].claim, ".kindPadCopy 0 7 \"polynomialBits\"");
  NamedShapeInputs names;
  names.private_field_sources = {"w1.words"};
  auto resolved = compiler::resolve_shape_inputs(names, {{"mac.blind", 0}, {"w1.words", 1}}, {}, {});
  std::vector<compiler::ProofModuleData::ShapeFact> facts;
  compiler::append_named_shape_metadata(p, resolved, facts);
  ASSERT_FALSE(facts.empty());
  EXPECT_EQ(facts[0].claim, ".privateFieldSources 4");
  EXPECT_EQ(facts[0].name, "value_w1_2ewords_private_field_sources");
  std::swap(p.values[0], p.values[1]);
  resolved = compiler::resolve_shape_inputs(names, {{"w1.words", 0}, {"mac.blind", 1}}, {}, {});
  facts.clear();
  compiler::append_named_shape_metadata(p, resolved, facts);
  EXPECT_EQ(facts[0].claim, ".privateFieldSources 4");
  names.private_field_sources = {"absent"};
  EXPECT_THROW(compiler::resolve_shape_inputs(names, {{"w1.words", 0}}, {}, {}), std::runtime_error);
  names.private_field_sources = {"w1.words", "w1.words"};
  EXPECT_THROW(compiler::resolve_shape_inputs(names, {{"w1.words", 0}}, {}, {}), std::runtime_error);
}

TEST(GordieHowePlanExport, ShapeFamilyRowsGroupByShape) {
  ir::Program p;
  p.values.resize(4);
  p.domains.resize(1);
  p.values[0].name = "a0";
  p.values[1].name = "a1";
  p.values[2].name = "view";
  p.values[3].name = "constant";
  for (auto &v : p.values) {
    v.kind = ir::Value::kPriv;
    v.domain = 0;
  }
  p.values[2].kind = ir::Value::kBits;
  p.values[2].ref = 1;
  p.values[2].select = 0;
  p.values[3].kind = ir::Value::kConstant;
  const compiler::NamedIds values{{"a0", 0}, {"a1", 1}, {"view", 2}, {"constant", 3}};
  NamedShapeInputs names;
  names.families = {{"f", {{{}, {}, {"a0"}}, {{}, {}, {"a1"}}, {{}, {}, {"view"}}}}};
  auto resolved = compiler::resolve_shape_inputs(names, values, {}, {});
  std::vector<compiler::ProofModuleData::ShapeFact> facts;
  compiler::append_shape_families(p, resolved, facts);
  // The two committed rows share one template; the bit view has its own.
  ASSERT_EQ(facts.size(), 2);
  EXPECT_EQ(facts[0].rows_name, "family_f_0_rows");
  EXPECT_NE(facts[0].definition.find("[[0],\n  [1]]"), std::string::npos);
  EXPECT_EQ(facts[0].claim.rfind(".family family_f_0_rows [\n      .kindPriv 0,", 0), 0);
  ASSERT_EQ(facts[0].parts.size(), 3);
  EXPECT_EQ(facts[0].parts[0].name, "family_f_0_value0_kind");
  EXPECT_EQ(facts[0].parts[0].statement, "(Program.program.value (r.getD 0 0)).kind = .priv");
  EXPECT_NE(facts[1].definition.find("[[2, 1]]"), std::string::npos);
  EXPECT_EQ(facts[1].parts[0].statement,
            "(Program.program.value (r.getD 0 0)).kind = .bits (r.getD 1 0) idx0");
  // Expressions whose ids Expr.atRow keeps literal are export failures.
  compiler::ShapeFamilyRowBuilder builder;
  EXPECT_THROW(builder.expr("(.logic .lt 16 [.leaf 1])"), std::runtime_error);
  EXPECT_THROW(builder.expr("(.linear [] (.leaf 1))"), std::runtime_error);
  EXPECT_THROW(builder.expr("(.scale (.value 3) (.leaf 1))"), std::runtime_error);
  EXPECT_EQ(builder.expr("(.scale (.const 3) (.leaf 9))").first, "(.scale (.const 3) (.leaf 0))");
  // A value kind a family cannot state is an export failure.
  names.families = {{"f", {{{}, {}, {"constant"}}}}};
  resolved = compiler::resolve_shape_inputs(names, values, {}, {});
  facts.clear();
  EXPECT_THROW(compiler::append_shape_families(p, resolved, facts), std::runtime_error);
  names.families = {{"f", {{{}, {}, {"absent"}}}}};
  EXPECT_THROW(compiler::resolve_shape_inputs(names, values, {}, {}), std::runtime_error);
}

TEST(GordieHowePlanExport, PrivateFieldOwnershipOnlyRequestIsEmitted) {
  Env e;
  Sys cs("private-field-only");
  auto &A = cs.domain(e.a_profile(), "A");
  const auto x = A.priv(Subfield{}, "x", 4);
  const auto y = A.priv(Subfield{}, "y", 4);
  assert_equal(y, x, "copy");
  NamedShapeInputs names;
  names.private_field_sources = {"x"};
  cs.shape_inputs(std::move(names));
  const auto compiled = compile(cs);
  const compiler::ExportMeta meta{"private-field-only", "narrow", "EXPORTER_COMMIT", "exports", 0};
  const auto program = compiler::build_program(*compiled, meta);
  ASSERT_TRUE(program.source_metadata.shapes.values.empty());
  ASSERT_EQ(program.source_metadata.shapes.private_field_sources.size(), 1);
  const auto data = compiler::proof_module_data(*compiled, meta, program);
  ASSERT_FALSE(data.shape_facts.empty());
  EXPECT_EQ(data.shape_facts[0].name, "value_x_private_field_sources");
  EXPECT_EQ(data.shape_facts[0].claim, ".privateFieldSources 0");
}

TEST(GordieHowePlanExport, NamedShapesFollowActualProfileIndices) {
  const std::vector<std::string> names = {"ring.keys", "ring.mu", "member.select.index",
      "member.table.gamma", "member.table.powers", "member.table.digests"};
  const std::vector<size_t> rom = {53, 54, 58, 59, 527, 528};
  const std::vector<size_t> qrom = {52, 53, 57, 58, 526, 527};
  compiler::NamedIds a, b;
  for (size_t i = 0; i < names.size(); ++i) {
    a.emplace_back(names[i], rom[i]);
    b.emplace_back(names[i], qrom[i]);
  }
  EXPECT_EQ(compiler::resolve_shape_names("value", a, names), rom);
  EXPECT_EQ(compiler::resolve_shape_names("value", b, names), qrom);
  std::swap(b[0], b[4]);
  EXPECT_EQ(compiler::resolve_shape_names("value", b, names), qrom);
  EXPECT_THROW(compiler::resolve_shape_names("value", a, {"absent"}), std::runtime_error);
  EXPECT_THROW(compiler::resolve_shape_names("value", a, {""}), std::runtime_error);
  EXPECT_THROW(compiler::resolve_shape_names("value", a, {"ring.keys", "ring.keys"}),
               std::runtime_error);
  a.push_back(a[0]);
  EXPECT_THROW(compiler::resolve_shape_names("value", a, {"ring.keys"}), std::runtime_error);
  a.back().second = 999;
  EXPECT_THROW(compiler::resolve_shape_names("value", a, {"ring.keys"}), std::runtime_error);
  EXPECT_THROW(compiler::resolve_shape_names("expression", {}, {"norm.squares"}),
               std::runtime_error);
  EXPECT_NE(compiler::shape_fact_name("value", "a.b", "kind"),
            compiler::shape_fact_name("value", "a_2eb", "kind"));
  EXPECT_NE(compiler::shape_fact_name("value", "a-b", "kind"),
            compiler::shape_fact_name("value", "a_b", "kind"));
}

TEST(GordieHowePlanExport, NamedExpressionSelectorsFollowStructure) {
  using Root = ShapeExprSelector::Root;
  using Edge = ShapeExprSelector::Edge;
  ir::Program p;
  p.values.resize(1);
  p.values[0].kind = ir::Value::kBound;
  p.values[0].expr = 3;
  p.nodes.resize(5);
  p.nodes[0].op = ir::Expr::kLeaf;
  p.nodes[1].op = ir::Expr::kRef;
  p.nodes[1].x = 0;
  p.nodes[2].op = ir::Expr::kAdd;
  p.nodes[2].a = 1;
  p.nodes[2].b = 0;
  p.nodes[3].op = ir::Expr::kRef;
  p.nodes[3].x = 1;
  p.nodes[4].op = ir::Expr::kLogic;
  p.nodes[4].args = {3};
  p.exprs = {0, 2};
  p.predicates.resize(1);
  p.predicates[0].lhs = 3;
  compiler::NamedIds values{{"bound", 0}}, predicates{{"equation", 0}};
  const ShapeExprSelector outer{Root::kPredicateLeft, "equation", {}};
  const ShapeExprSelector inner{Root::kPredicateLeft, "equation",
      {{Edge::kShared}, {Edge::kFirst}}};
  EXPECT_EQ(compiler::resolve_shape_expr(p, values, predicates, outer), 1);
  EXPECT_EQ(compiler::resolve_shape_expr(p, values, predicates, inner), 0);
  EXPECT_EQ(compiler::resolve_shape_expr(p, values, predicates,
      {Root::kValueDefinition, "bound", {{Edge::kShared}, {Edge::kFirst}}}), 0);
  // The same semantic selectors survive different profile pool positions.
  auto shifted = p;
  shifted.exprs.insert(shifted.exprs.begin(), 0);
  ++shifted.nodes[1].x;
  ++shifted.nodes[3].x;
  EXPECT_EQ(compiler::resolve_shape_expr(shifted, values, predicates, outer), 2);
  EXPECT_EQ(compiler::resolve_shape_expr(shifted, values, predicates, inner), 1);
  auto logic = p;
  logic.predicates[0].lhs = 4;
  EXPECT_EQ(compiler::resolve_shape_expr(logic, values, predicates,
      {Root::kPredicateLeft, "equation", {{Edge::kArgument, 0}}}), 1);
  EXPECT_THROW(compiler::resolve_shape_expr(logic, values, predicates,
      {Root::kPredicateLeft, "equation", {{Edge::kArgument, 1}}}), std::runtime_error);
  EXPECT_THROW(compiler::resolve_shape_expr(p, values, predicates,
      {Root::kPredicateLeft, "absent", {}}), std::runtime_error);
  EXPECT_THROW(compiler::resolve_shape_expr(p, values, {{"equation", 0}, {"equation", 0}},
      outer), std::runtime_error);
  EXPECT_THROW(compiler::resolve_shape_expr(p, values, predicates,
      {Root::kPredicateLeft, "equation", {{Edge::kFirst}}}), std::runtime_error);
  EXPECT_THROW(compiler::resolve_shape_expr(p, values, predicates,
      {Root::kPredicateLeft, "equation", {{Edge::kShared}, {Edge::kSecond}}}), std::runtime_error);
  EXPECT_EQ(compiler::resolve_shape_value(p, values, predicates,
      {Root::kPredicateLeft, "equation", {{Edge::kShared}, {Edge::kSecond}}}), 0);
  EXPECT_THROW(compiler::resolve_shape_value(p, values, predicates, outer), std::runtime_error);
  auto bad = p;
  bad.nodes[3].x = bad.exprs.size();
  EXPECT_THROW(compiler::resolve_shape_expr(bad, values, predicates, outer), std::runtime_error);
  bad = p;
  bad.values[0].kind = ir::Value::kPriv;
  EXPECT_THROW(compiler::resolve_shape_expr(bad, values, predicates,
      {Root::kValueDefinition, "bound", {}}), std::runtime_error);
}

TEST(GordieHowePlanExport, PredicateAliasesDistinguishSourceAndRealization) {
  using Role = PredicateShapeSelector::Role;
  using Body = PredicateShapeSelector::Body;
  const PredicateShapeSelector source{"equation", Role::kSource, Body::kMod};
  const PredicateShapeSelector realized{"equation", Role::kRealization, Body::kEqual};
  ir::Program p;
  ir::Predicate q;
  q.name = "equation";
  q.body = ir::Predicate::kMod;
  p.predicates.push_back(q);
  q.role = ir::Predicate::Role::kRealization;
  q.body = ir::Predicate::kEqual;
  p.predicates.push_back(q);
  EXPECT_EQ(compiler::resolve_shape_predicate(p, source), 0);
  EXPECT_EQ(compiler::resolve_shape_predicate(p, realized), 1);
  std::swap(p.predicates[0], p.predicates[1]);
  EXPECT_EQ(compiler::resolve_shape_predicate(p, source), 1);
  EXPECT_EQ(compiler::resolve_shape_predicate(p, realized), 0);
  EXPECT_THROW(compiler::resolve_shape_predicate(p, {"missing", Role::kSource, Body::kMod}),
               std::runtime_error);
  EXPECT_THROW(compiler::resolve_shape_predicate(p, {"equation", Role::kSource, Body::kEqual}),
               std::runtime_error);
  EXPECT_THROW(compiler::resolve_shape_predicate(p, {"equation", Role::kType, Body::kMod}),
               std::runtime_error);
  EXPECT_THROW(compiler::resolve_shape_predicate(p, {"", Role::kSource, Body::kMod}),
               std::runtime_error);
  p.predicates.push_back(p.predicates[1]);
  EXPECT_THROW(compiler::resolve_shape_predicate(p, source), std::runtime_error);
}

TEST(GordieHowePlanExport, ApplicationShapeAliasesResolveWithoutChangingProgram) {
  Env e;
  auto make = [&](bool metadata) {
    auto sys = std::make_unique<Sys>("named-shape-aliases");
    Sys &cs = *sys;
    auto &A = cs.domain(e.a_profile(), "A");
    auto x = A.priv(Subfield{}, "x", 4);
    auto y = A.priv(Subfield{}, "y", 4);
    auto z = A.priv(Subfield{}, "z", 4);
    const auto square = x * x;
    assert_equal(y, square, "square");
    assert_equal(z, square, "square.again");
    if (metadata) {
      cs.shape_value("witness.x", x);
      cs.shape_predicate("square.body", {"square", PredicateShapeSelector::Role::kSource,
          PredicateShapeSelector::Body::kEqual});
      const auto owners = square.node.use_count();
      cs.shape_expr("witness.square", square);
      EXPECT_EQ(square.node.use_count(), owners);
      cs.shape_expr("witness.square.fromPredicate",
          {ShapeExprSelector::Root::kPredicateLeft, "square",
              {{ShapeExprSelector::Edge::kSecond}, {ShapeExprSelector::Edge::kFirst}}});
      cs.shape_value("equation.zero",
          {ShapeExprSelector::Root::kPredicateRight, "square", {}});
      cs.source_role(x, SourceRole::kAWitness, 0);
      cs.shape_inputs({{"witness.x", "equation.zero"}, {"square.body"},
          {"witness.square", "witness.square.fromPredicate"}, {"square"}});
    }
    auto c = compile(cs);
    return Toy{std::move(sys), std::move(c)};
  };
  auto plain = make(false);
  auto named = make(true);
  const compiler::ExportMeta meta{"alias-toy", "narrow", "EXPORTER_COMMIT", "exports", 0};
  // Includes the realized circuits and all program records; metadata changes
  // neither these bytes nor the plan, digest or emitted Lean program.
  EXPECT_EQ(ir::write_program(plain.c->program()), ir::write_program(named.c->program()));
  EXPECT_EQ(compiler::export_lean_plan(*plain.c, meta), compiler::export_lean_plan(*named.c, meta));
  EXPECT_EQ(compiler::export_lean_program(*plain.c, meta),
            compiler::export_lean_program(*named.c, meta));
  auto p = compiler::build_program(*named.c, meta);
  const auto &m = p.source_metadata;
  ASSERT_EQ(m.shapes.values.size(), 2);
  EXPECT_EQ(named.c->program().values.at(m.shapes.values[1]).kind, ir::Value::kConstant);
  ASSERT_EQ(m.shapes.predicates.size(), 1);
  ASSERT_EQ(m.shapes.exprs.size(), 2);
  EXPECT_EQ(m.shapes.exprs[0], m.shapes.exprs[1]);
  EXPECT_EQ(named.c->program().values.at(m.shapes.values[0]).name, "x");
  EXPECT_EQ(named.c->program().predicates.at(m.shapes.predicates[0]).name, "square");
  EXPECT_LT(m.shapes.exprs[0], named.c->program().exprs.size());
  ASSERT_EQ(m.roles.size(), 1);
  EXPECT_EQ(m.roles[0].value, m.shapes.values[0]);
  EXPECT_EQ(m.roles[0].role, SourceRole::kAWitness);
  const auto data = compiler::proof_module_data(*named.c, meta, p);
  ASSERT_EQ(data.shape_facts.size(), 20);
  EXPECT_EQ(data.shape_facts[0].name, "value_witness_2ex_kind");
  EXPECT_EQ(data.shape_facts[1].name, "value_equation_2ezero_kind");
  EXPECT_EQ(data.shape_facts[2].name, "predicate_square_2ebody_body");
  EXPECT_EQ(data.shape_facts[3].name, "expr_witness_2esquare_eq");
  EXPECT_EQ(data.shape_facts[4].name, "expr_witness_2esquare_2efromPredicate_eq");
  EXPECT_EQ(data.shape_facts[5].name, "predicate_square_header");
  EXPECT_EQ(data.shape_facts[6].name, "value_witness_2ex_header");
  EXPECT_EQ(data.shape_facts[7].name, "value_equation_2ezero_header");
  EXPECT_EQ(data.shape_facts[8].name, "predicate_square_2ebody_role");
  EXPECT_EQ(data.shape_facts[9].name, "values_length");
  EXPECT_EQ(data.shape_facts[10].name, "predicates_length");
  EXPECT_EQ(data.shape_facts[11].name, "statement_checks");
  EXPECT_EQ(data.shape_facts[12].name, "statement_ranges");
  EXPECT_EQ(data.shape_facts[13].name, "cross_predicates");
  const compiler::ShapeInputs numeric{"test", m.shapes.values,
      m.shapes.predicates, m.shapes.exprs, m.shapes.equal_headers};
  auto malformed = named.c->program();
  malformed.predicates.at(m.shapes.equal_headers.at(0)).body = ir::Predicate::kCross;
  EXPECT_THROW(compiler::named_shape_facts_of(malformed, m.shapes), std::runtime_error);
  auto unresolved = m.shapes;
  unresolved.equal_headers[0] = malformed.predicates.size();
  EXPECT_THROW(compiler::named_shape_facts_of(named.c->program(), unresolved),
               std::runtime_error);
  const auto prior = compiler::shape_facts_of(named.c->program(), numeric);
  for (size_t i = 0; i < prior.size(); ++i) {
    EXPECT_EQ(data.shape_facts[i].claim, prior[i].claim);
    EXPECT_EQ(data.shape_facts[i].statement, prior[i].statement);
    EXPECT_EQ(data.shape_facts[i].sound, prior[i].sound);
  }
}

TEST(GordieHowePlanExport, NamedMetadataUsesResolvedFieldsAndCompleteSummaries) {
  ir::Program p;
  p.domains.resize(1);
  p.domains[0].field = 3;
  ir::Value x;
  x.name = "witness";
  x.shape = {2, 3};
  x.node = "packing";
  x.type_source = ir::Value::TypeSource::kNode;
  x.phase = 2;
  x.owner = 4;
  p.values.push_back(x);
  x.kind = ir::Value::kChallenge;
  x.domain = ir::kNone;
  x.field = 9;
  x.shape = {};
  x.owner = ir::kNone;
  x.type_source = ir::Value::TypeSource::kNone;
  p.values.push_back(x);
  x.kind = ir::Value::kOpaque;
  x.opaque = "statement.ring";
  x.bound = "12289";
  p.values.push_back(x);
  // A non-statement bound must not leak into the declared statement summary.
  x.kind = ir::Value::kPriv;
  p.values.push_back(x);
  ir::Predicate q;
  q.body = ir::Predicate::kCross;
  q.role = ir::Predicate::Role::kType;
  q.owner = 0;
  p.predicates.push_back(q);
  q.body = ir::Predicate::kEqual;
  p.predicates.push_back(q);
  q.body = ir::Predicate::kCross;
  p.predicates.push_back(q);
  compiler::ResolvedShapeInputs in;
  in.values = {0, 1};
  in.names.values = {"witness", "challenge"};
  in.predicates = {0};
  in.names.predicates = {"crossing"};
  std::vector<compiler::ProofModuleData::ShapeFact> facts;
  compiler::append_named_shape_metadata(p, in, facts);
  ASSERT_EQ(facts.size(), 14);
  EXPECT_NE(facts[0].claim.find("domain := 0, field := 3, size := 6, phase := 2"), std::string::npos);
  EXPECT_NE(facts[0].claim.find("node := some { name := \"packing\" }"), std::string::npos);
  EXPECT_NE(facts[0].claim.find("typeSource := .node, role := .realization 4"), std::string::npos);
  EXPECT_NE(facts[1].claim.find("domain := 0, field := 9, size := 1"), std::string::npos);
  EXPECT_NE(facts[1].claim.find("node := none"), std::string::npos);
  EXPECT_EQ(facts[2].claim, ".predicateRole 0 (.type 0)");
  EXPECT_EQ(facts[3].claim, ".valueCount 4");
  EXPECT_EQ(facts[4].claim, ".predicateCount 3");
  EXPECT_EQ(facts[5].claim, ".statementChecks []");
  EXPECT_EQ(facts[6].claim, ".statementRanges [(2, 12289)]");
  EXPECT_EQ(facts[7].claim, ".crossPredicates [0, 2]");
  EXPECT_EQ(facts[8].claim, ".valueType 0 (.field)");
  EXPECT_EQ(facts[9].claim, ".valueType 1 (.field)");

  EXPECT_EQ(facts[11].claim, ".exprCount 0");
  EXPECT_EQ(facts[12].claim, ".domainCount 1");
  EXPECT_EQ(facts[13].claim, ".challengeCount 0");

  // A packing node is independent of the declared type.
  p.values[0].type = ir::VType::kSub;
  p.values[0].sub = "actual-subfield";
  p.values[1].kind = ir::Value::kPubExpr;
  p.values[1].type = ir::VType::kBit;
  ir::Expr leaf;
  leaf.op = ir::Expr::kLeaf;
  leaf.x = 0;
  leaf.n = 6;
  p.nodes.push_back(leaf);
  p.values[1].expr = 0;
  facts.clear();
  compiler::append_named_shape_metadata(p, in, facts);
  ASSERT_EQ(facts.size(), 15);
  EXPECT_EQ(facts[8].claim, ".valueType 0 (.sub \"actual-subfield\")");
  EXPECT_EQ(facts[9].claim, ".valueType 1 (.bit)");
  EXPECT_EQ(facts[10].claim, ".kindExprEq 1 (.leaf 0)");
  EXPECT_EQ(facts[10].sound, "kindExprEq");
}

TEST(GordieHowePlanExport, NamedChallengesKeepSamplerAndSourceCoverageSeparate) {
  ir::Program p;
  ir::Challenge c;
  c.name = "gamma"; c.field = 3; c.size = 2;
  p.challenges.push_back(c);
  c.name = "alpha"; c.field = 4; c.size = 1;
  c.role = ir::Challenge::Role::kRealization;
  c.sampler = ir::Challenge::Sampler::kNode;
  c.node = "bit";
  p.challenges.push_back(c);
  c.name = "delta"; c.field = 5;
  c.role = ir::Challenge::Role::kSource;
  c.sampler = ir::Challenge::Sampler::kFull;
  p.challenges.push_back(c);
  compiler::ResolvedShapeInputs in;
  std::vector<compiler::ProofModuleData::ShapeFact> facts;
  compiler::append_named_shape_metadata(p, in, facts);
  ASSERT_EQ(facts.size(), 11);
  EXPECT_EQ(facts[5].name, "challenge_gamma_full");
  EXPECT_EQ(facts[5].claim, ".fullChallenge 0 3 2");
  EXPECT_EQ(facts[6].name, "challenge_delta_full");
  EXPECT_EQ(facts[6].claim, ".fullChallenge 2 5 1");
  EXPECT_EQ(facts[7].claim, ".sourceChallenges [0, 2]");
  EXPECT_EQ(facts[8].claim, ".exprCount 0");
  EXPECT_EQ(facts[9].claim, ".domainCount 0");
  EXPECT_EQ(facts[10].claim, ".challengeCount 3");
  std::swap(p.challenges[0], p.challenges[1]);
  facts.clear();
  compiler::append_named_shape_metadata(p, in, facts);
  EXPECT_EQ(facts[5].name, "challenge_gamma_full");
  EXPECT_EQ(facts[5].claim, ".fullChallenge 1 3 2");
  EXPECT_EQ(facts[7].claim, ".sourceChallenges [1, 2]");
}

TEST(GordieHowePlanExport, NamedSourceRolesResolveAndRejectMalformedNames) {
  Env e;
  auto make = [&](int mode) {
    auto sys = std::make_unique<Sys>("named-source-roles");
    Sys &cs = *sys;
    auto &A = cs.domain(e.a_profile(), "A");
    auto x = A.priv(Subfield{}, "x", 4);
    auto y = A.priv(Subfield{}, "y", 4);
    assert_equal(y, x, "copy");
    if (mode == 0) cs.source_role("x", SourceRole::kAWitness, 3);
    if (mode == 1) cs.source_role("absent", SourceRole::kAWitness, 3);
    if (mode == 2) {
      cs.shape_value("x", y);
      cs.source_role("x", SourceRole::kAWitness, 3);
    }
    if (mode == 3) {
      cs.source_role(x, SourceRole::kAWitness, 3);
      cs.source_role("x", SourceRole::kCarry, 4);
    }
    auto c = compile(cs);
    return Toy{std::move(sys), std::move(c)};
  };
  const compiler::ExportMeta meta{"role-toy", "narrow", "EXPORTER_COMMIT", "exports", 0};
  auto good = make(0);
  const auto p = compiler::build_program(*good.c, meta);
  ASSERT_EQ(p.source_metadata.roles.size(), 1);
  const auto &role = p.source_metadata.roles.front();
  EXPECT_EQ(good.c->program().values.at(role.value).name, "x");
  EXPECT_EQ(role.role, SourceRole::kAWitness);
  EXPECT_EQ(role.slot, 3);
  EXPECT_EQ(role.name, "x");
  const auto data = compiler::proof_module_data(*good.c, meta, p);
  const auto module = compiler::source_roles_module(data);
  EXPECT_NE(module.text.find("def roles : List SourceRoleEntry"), std::string::npos);
  EXPECT_NE(module.text.find(".aWitness, 3"), std::string::npos);
  EXPECT_NE(module.text.find("theorem roles_eq : roles = ["), std::string::npos);
  EXPECT_NE(module.text.find("def classifier : SourceRoleClassifier := sourceRoleClassifier roles"),
            std::string::npos);
  EXPECT_EQ(module.text.find("noncomputable"), std::string::npos);
  EXPECT_EQ(module.text.find("ProgramData"), std::string::npos);
  const auto facts = compiler::source_role_facts_module(data);
  EXPECT_NE(facts.text.find("theorem role_x_lookup"), std::string::npos);
  EXPECT_NE(facts.text.find(" = some (.aWitness, 3)"), std::string::npos);
  EXPECT_NE(facts.text.find("rolesOk.lookup_at (k := 0) (by rw [SourceRoles.roles_eq]; rfl)"), std::string::npos);
  EXPECT_NE(facts.text.find("programOk_sound data"), std::string::npos);
  EXPECT_NE(facts.text.find(".sourceRoles.present rfl"), std::string::npos);
  for (int mode : {1, 2, 3}) {
    auto bad = make(mode);
    EXPECT_THROW(compiler::build_program(*bad.c, meta), std::runtime_error);
  }
  Sys empty("empty-source-role");
  EXPECT_THROW(empty.source_role("", SourceRole::kInput, 0), std::runtime_error);
}

TEST(GordieHowePlanExport, NamedShapeExpiredAliasIsRejected) {
  Env e;
  Sys cs("expired-shape-alias");
  auto &A = cs.domain(e.a_profile(), "A");
  auto x = A.priv(Subfield{}, "x", 4);
  {
    const auto unused = x * x;
    cs.shape_expr("unused", unused);
  }
  cs.shape_inputs({{}, {}, {"unused"}, {}});
  auto c = compile(cs);
  const compiler::ExportMeta meta{"alias-toy", "narrow", "EXPORTER_COMMIT", "exports", 0};
  EXPECT_THROW(compiler::build_program(*c, meta), std::runtime_error);
}

TEST(GordieHowePlanExport, ToyIsStable) {
  const std::string out = toy_export();
  if (std::getenv("GH_PRINT_GOLDEN")) std::printf("%s", out.c_str());
  EXPECT_EQ(out, std::string(kGolden));
  // A second build of the same system exports the same text.
  EXPECT_EQ(toy_export(), out);
}

// The Lean configuration names and module paths (lean_config_name): every
// configuration the bench and export_plans.sh export, in each profile it is
// exported in, has the name below, and no two share one; an explicit
// lean_name wins; a test's own profile names its parameter set; a
// malformed family member has no name.
TEST(GordieHowePlanExport, LeanNames) {
  const std::vector<std::tuple<std::string, std::string, std::string>> named =
      {
          {"mldsa-emulated", "narrow", "MLDSA44.Emulated.ROMParams"},
          {"mldsa-emulated", "wide", "MLDSA44.Emulated.QROMParams"},
          {"mldsa-native", "narrow", "MLDSA44.Native.ROMParams"},
          {"mldsa-native", "wide", "MLDSA44.Native.QROMParams"},
          {"mldsa-ring-native", "narrow", "MLDSA44.Ring.Native.ROMParams"},
          {"mldsa-ring-native", "wide", "MLDSA44.Ring.Native.QROMParams"},
          {"mldsa-ring-carrier", "narrow", "MLDSA44.Ring.Carrier.ROMParams"},
          {"mldsa-ring-carrier", "wide", "MLDSA44.Ring.Carrier.QROMParams"},
          {"falcon-emulated", "narrow", "Falcon512.Emulated.ROMParams"},
          {"falcon-emulated", "wide", "Falcon512.Emulated.QROMParams"},
          {"falcon-native", "narrow", "Falcon512.Native.ROMParams"},
          {"falcon-native", "wide", "Falcon512.Native.QROMParams"},
          {"falcon-ring-native", "narrow", "Falcon512.Ring.Native.ROMParams"},
          {"falcon-ring-native", "wide", "Falcon512.Ring.Native.QROMParams"},
          {"falcon-ring-carrier", "narrow", "Falcon512.Ring.Carrier.ROMParams"},
          {"falcon-ring-carrier", "wide", "Falcon512.Ring.Carrier.QROMParams"},
          {"mdoc", "narrow", "MDL.ECDSA.ROMParams"},
          {"composite", "narrow", "Composite.ROMParams"},
          {"composite", "wide", "Composite.QROMParams"},
          {"pq-mdoc-goldilocks-1", "narrow", "MDL.MLDSA44.Attrs1.ROMParams"},
          {"pq-mdoc-goldilocks-2", "narrow", "MDL.MLDSA44.Attrs2.ROMParams"},
          {"pq-mdoc-goldilocks-4", "narrow", "MDL.MLDSA44.Attrs4.ROMParams"},
          {"pq-mdoc-goldilocks-1", "wide", "MDL.MLDSA44.Attrs1.QROMParams"},
          {"pq-mdoc-fq-1", "narrow", "MDL.MLDSA44Fq.Attrs1.ROMParams"},
          {"pq-mdoc-fq-2", "narrow", "MDL.MLDSA44Fq.Attrs2.ROMParams"},
          {"pq-mdoc-fq-4", "narrow", "MDL.MLDSA44Fq.Attrs4.ROMParams"},
          {"pq-mdoc-fq-1", "wide", "MDL.MLDSA44Fq.Attrs1.QROMParams"},
          {"rsa-auto_t9_m2_64_batched", "narrow",
           "RSA2048.Goldilocks2.Msg64B.ROMParams"},
          {"rsa-auto_t9_m2_2048_batched", "narrow",
           "RSA2048.Goldilocks2.Msg2KiB.ROMParams"},
          {"rsa-fp128_auto_t11_m3_64_batched", "narrow-fp128",
           "RSA2048.Fp128.Msg64B.ROMParams"},
          {"rsa-fp128_auto_t11_m3_2048_batched", "narrow-fp128",
           "RSA2048.Fp128.Msg2KiB.ROMParams"},
          {"rsa-direct_t9_2048_batched", "narrow",
           "RSA2048.Goldilocks2.Msg2KiB.DirectT9M1.ROMParams"},
          {"sha256-batched-8", "narrow", "SHA256.Batched8Blocks.ROMParams"},
          {"sha256-batched-8", "wide", "SHA256.Batched8Blocks.QROMParams"},
          {"sha256-gkr-8", "narrow", "SHA256.Gkr8Blocks.ROMParams"},
          {"sha256-batched-1024B", "narrow", "SHA256.Batched1KiB.ROMParams"},
          {"sha256-batched-8192B", "narrow", "SHA256.Batched8KiB.ROMParams"},
          {"sha256-batched-32768B", "wide", "SHA256.Batched32KiB.QROMParams"},
          {"sha256-batched-503B", "narrow", "SHA256.Batched503B.ROMParams"},
          {"sha3-256-batched-8", "narrow", "SHA3.Batched8Perms.ROMParams"},
          {"sha3-256-batched-64", "narrow", "SHA3.Batched64Perms.ROMParams"},
          {"sha3-256-batched-256", "wide", "SHA3.Batched256Perms.QROMParams"},
          {"sha3-256-batched-1024B", "narrow", "SHA3.Batched1KiB.ROMParams"},
          {"sha3-256-batched-32768B", "wide", "SHA3.Batched32KiB.QROMParams"},
          {"keccak-perms-batched-8", "narrow",
           "KeccakPerms.Batched8.ROMParams"},
          {"keccak-perms-batched-256", "wide",
           "KeccakPerms.Batched256.QROMParams"},
          {"toy", "wide", "Toy.QROMParams"},
      };
  std::set<std::string> seen;
  for (const auto &[config, profile, name] : named) {
    EXPECT_EQ(compiler::lean_config_name(config, profile), name) << config;
    EXPECT_TRUE(seen.insert(name).second) << name;
  }
  EXPECT_EQ(compiler::lean_config_name("mldsa-native", "test"),
            "MLDSA44.Native.TestParams");
  EXPECT_THROW(compiler::lean_config_name("pq-mdoc-ecdsa-1", "narrow"),
               std::runtime_error);
  EXPECT_THROW(compiler::lean_config_name("rsa-auto_9_2048", "narrow"),
               std::runtime_error);

  const compiler::ExportMeta ring{"falcon-ring-carrier", "narrow", "c", "r", 0};
  EXPECT_EQ(compiler::lean_plan_module(ring),
            "GordieHoweCerts/Generated/Falcon512/Ring/Carrier/ROMParams/Plan");
  EXPECT_EQ(compiler::lean_program_module(ring),
            "GordieHoweCerts/Generated/Falcon512/Ring/Carrier/ROMParams/Program");
  EXPECT_EQ(compiler::lean_module_name(ring, "Plan"),
            "GordieHoweCerts.Generated.Falcon512.Ring.Carrier.ROMParams.Plan");
  EXPECT_EQ(compiler::lean_namespace(ring, "Plan"),
            "GordieHowe.Generated.Falcon512.Ring.Carrier.ROMParams.Plan");
  compiler::ExportMeta named_toy{"toy", "wide", "c0ffee", "run-0", 0};
  named_toy.lean_name = "Toy.Named.QROMParams";
  EXPECT_EQ(compiler::lean_plan_module(named_toy),
            "GordieHoweCerts/Generated/Toy/Named/QROMParams/Plan");
}

// Two exports never write one module path: an export to a path that holds
// another configuration's module fails, and a rerun of the same export
// replaces its own.
TEST(GordieHowePlanExport, ModulePathsAreNotShared) {
  const std::filesystem::path dir =
      std::filesystem::temp_directory_path() /
      ("gh-plan-export-" + std::to_string(::getpid()));
  std::filesystem::remove_all(dir);
  const compiler::ExportMeta toy{"toy", "wide", "c0ffee", "run-0", 0};
  const std::string path = compiler::lean_plan_file(dir.string(), toy);
  EXPECT_EQ(path, (dir / "GordieHoweCerts/Generated/Toy/QROMParams/Plan.lean")
                      .string());
  std::ofstream(path, std::ios::binary) << toy_export();
  EXPECT_EQ(compiler::lean_plan_file(dir.string(), toy), path);
  compiler::ExportMeta other{"other", "wide", "c0ffee", "run-0", 0};
  other.lean_name = "Toy.QROMParams";
  EXPECT_THROW(compiler::lean_plan_file(dir.string(), other),
               std::runtime_error);
  std::filesystem::remove_all(dir);
}

// The toy's realized program (plan_program.h): its structural invariants
// hold; the MAC's H part <mac>.H is an affine realization part of the
// cross-field equality, of degree nch = 32 in mac.beta; the selection's
// predicates are the source program's; the late values' reads are closed.
TEST(GordieHowePlanExport, ToyProgram) {
  const Toy t = toy_system();
  const auto p = compiler::build_program(
      *t.c, compiler::ExportMeta{"toy", "wide", "c0ffee", "run-0", 0});
  const auto err = compiler::program_errors(p);
  for (const auto &x : err) ADD_FAILURE() << x;
  // Every index map, decoded from the runs the text writes, equals its
  // explicit entries; the maps with no run longer than one entry.
  for (const auto &e : compiler::index_map_errors(p)) ADD_FAILURE() << e;
  for (const auto &e : compiler::module_errors(p)) ADD_FAILURE() << e;
  for (size_t k : compiler::maps_without_runs(p))
    std::printf("GH_MAP_WITHOUT_RUNS idx%zu length %zu\n", k,
                p.index_maps[k].size());

  auto pred = [&](const std::string &nm) -> const compiler::ProgramData::Predicate * {
    for (const auto &q : p.predicates)
      if (q.name == nm) return &q;
    return nullptr;
  };
  const auto *h = pred("mac.H");
  const auto *eq = pred("mac.equal");
  ASSERT_NE(h, nullptr);
  ASSERT_NE(eq, nullptr);
  EXPECT_EQ(h->role, "realization");
  EXPECT_EQ(p.predicates.at(h->owner).name, "mac.equal");
  EXPECT_EQ(h->target, ".affine");
  // alpha:A is drawn outside [0, 128), the domain's one table (the
  // planner's, from the MAC quotient's bound).
  for (size_t i = 0; i < p.challenges.size(); ++i)
    if (p.challenges[i].first == "alpha:A")
      EXPECT_EQ(p.samplers[i], "(.fieldMinusTables (.range 128))");
  size_t beta = SIZE_MAX;
  for (size_t i = 0; i < p.challenges.size(); ++i)
    if (p.challenges[i].first == "mac.beta") beta = i;
  ASSERT_NE(beta, SIZE_MAX);
  ASSERT_EQ(h->degree.size(), 1u);
  EXPECT_EQ(h->degree[0], std::make_pair(beta, size_t(32)));
  EXPECT_EQ(eq->role, "source");
  EXPECT_EQ(pred("select.step")->role, "source");
  // The tail is a realization part of the cross-field equality.
  EXPECT_EQ(p.predicates.at(pred("mac")->owner).name, "mac.equal");
  EXPECT_NE(p.text.find("def program : RealizedProgram"), std::string::npos);
  // v's range is realized by two digits, looked up as two needles; the
  // MAC tail's quotient is the two-digit form, bounded by the in
  // predicates of its digits.
  const std::string v = pred("v")->body;
  EXPECT_NE(v.find("kind := .digits"), std::string::npos) << v;
  EXPECT_NE(v.find("honest := 3000, max := 4194304"), std::string::npos) << v;
  EXPECT_EQ(v.find("needles := []"), std::string::npos) << v;
  const std::string tail = pred("mac")->body;
  EXPECT_NE(tail.find("form := .digits"), std::string::npos) << tail;
  EXPECT_NE(tail.find("lhsLo := "), std::string::npos) << tail;
  // Every message carries its pad realization.
  size_t pads = 0;
  for (size_t at = p.text.find("realization := .pad"); at != std::string::npos;
       at = p.text.find("realization := .pad", at + 1))
    ++pads;
  EXPECT_GE(pads, 2 * p.messages.size());
  // A second build of the same system exports the same text.
  EXPECT_EQ(compiler::export_lean_program(
                *toy_system().c,
                compiler::ExportMeta{"toy", "wide", "c0ffee", "run-0", 0}),
            p.text);
}

// A long constant whose entries never repeat the one before them is written as
// its entries (constEntries definitions chained by their tails); a long
// constant with repeats as its runs (constRuns definitions). Both decode to
// their entries, and a changed entry does not.
TEST(GordieHowePlanExport, IndexMapsHaveNamedConstructionEquations) {
  ir::Program p;
  p.index_maps = {{0, 1, 2}, {1, 3}};
  p.index_map_forms = {"[(0, 1, 3)]", ""};
  const auto text = compiler::print_program(
      p, compiler::ExportMeta{"map-equations", "wide", "c0ffee", "run-0", 0}, {});
  EXPECT_NE(text.find("def idx0 : IndexMap :=\n  [(0, 1, 3)]\n\n"), std::string::npos);
  EXPECT_NE(text.find("theorem idx0_eq : idx0 =\n  [(0, 1, 3)] := rfl"), std::string::npos);
  const auto start = text.find("def idx1 : IndexMap :=\n  ");
  ASSERT_NE(start, std::string::npos);
  const auto body = start + std::string("def idx1 : IndexMap :=\n  ").size();
  const auto end = text.find("\n\n", body);
  ASSERT_NE(end, std::string::npos);
  EXPECT_NE(text.find("theorem idx1_eq : idx1 =\n  " + text.substr(body, end - body) + " := rfl"),
            std::string::npos);
}

TEST(GordieHowePlanExport, LongConstantForms) {
  ir::Program P;
  P.domains.push_back({"A", 0});
  ir::Value a, b;
  a.name = "a";
  b.name = "b";
  a.kind = b.kind = ir::Value::kConstant;
  a.shape = b.shape = {600};
  for (size_t i = 0; i < 600; ++i) {
    a.entries.push_back(std::to_string(i));
    b.entries.push_back(std::to_string(i / 50));
  }
  P.values = {a, b};
  const std::string text = compiler::print_program(
      P, compiler::ExportMeta{"long-constants", "wide", "c0ffee", "run-0", 0}, {});
  EXPECT_NE(text.find(".constant constEntries0,"), std::string::npos);
  EXPECT_NE(text.find("def constEntries0 : List Nat :=\n  %[(nat_lit 0), (nat_lit 1)"),
            std::string::npos);
  EXPECT_NE(text.find("(nat_lit 511) | constEntries1]"), std::string::npos);
  EXPECT_NE(text.find("def constEntries1 : List Nat :=\n  [(nat_lit 512), (nat_lit 513)"),
            std::string::npos);
  EXPECT_LT(text.find("def constEntries1 "), text.find("def constEntries0 "));
  EXPECT_NE(text.find(".constant (ConstRuns.expand constRuns0)"), std::string::npos);
  EXPECT_EQ(text.find("constEntries2"), std::string::npos);
  for (const auto &e : compiler::index_map_errors(compiler::plan_program_internal::data_of(P, text)))
    ADD_FAILURE() << e;
  std::string bad = text;
  const size_t at = bad.find("(nat_lit 7)");
  ASSERT_NE(at, std::string::npos);
  bad.replace(at, 11, "(nat_lit 8)");
  EXPECT_FALSE(compiler::index_map_errors(compiler::plan_program_internal::data_of(P, bad)).empty());
}

// A program list longer than a chunk (1,024 entries) is written as chunk
// definitions chained by their tails (`%[x, … | next]`), the last chunk
// first, the field naming the first; reading the field follows the chain to
// every entry in order, and a constant's chain likewise. A chain to a
// missing definition does not decode.
TEST(GordieHowePlanExport, LongListsChainedByTails) {
  ir::Program P;
  P.domains.push_back({"A", 0});
  for (size_t i = 0; i < 2100; ++i) {
    ir::Value v;
    v.name = "v" + std::to_string(i);
    v.kind = ir::Value::kConstant;
    v.shape = {1};
    v.entries = {std::to_string(i % 7)};
    P.values.push_back(v);
  }
  ir::Value c;
  c.name = "c";
  c.kind = ir::Value::kConstant;
  c.shape = {1100};
  for (size_t i = 0; i < 1100; ++i) c.entries.push_back(std::to_string(i));
  P.values.push_back(c);
  const std::string text = compiler::print_program(
      P, compiler::ExportMeta{"long-lists", "wide", "c0ffee", "run-0", 0}, {});
  EXPECT_NE(text.find("    values := valuesChunk0,\n"), std::string::npos);
  const size_t d0 = text.find("\ndef valuesChunk0 : List Value :=\n  %[");
  const size_t d1 = text.find("\ndef valuesChunk1 : List Value :=\n  %[");
  const size_t d2 = text.find("\ndef valuesChunk2 : List Value :=\n  [");
  ASSERT_NE(d0, std::string::npos);
  ASSERT_NE(d1, std::string::npos);
  ASSERT_NE(d2, std::string::npos);
  EXPECT_LT(d2, d1);
  EXPECT_LT(d1, d0);
  EXPECT_NE(text.find(" |\n    valuesChunk1]"), std::string::npos);
  EXPECT_EQ(text.find(" ++ "), std::string::npos);
  const auto items = compiler::program_list_items(text, "values");
  ASSERT_EQ(items.size(), P.values.size());
  for (size_t i = 0; i < P.values.size(); ++i)
    EXPECT_EQ(items[i].rfind("({ name := \"" + P.values[i].name + "\"", 0), 0u) << i;
  EXPECT_NE(text.find(".constant constEntries0,"), std::string::npos);
  EXPECT_NE(text.find("| constEntries2]"), std::string::npos);
  for (const auto &e : compiler::index_map_errors(compiler::plan_program_internal::data_of(P, text)))
    ADD_FAILURE() << e;
  std::string bad = text;
  const size_t at = bad.find("| constEntries2]");
  bad.replace(at, 16, "| constEntries9]");
  EXPECT_FALSE(compiler::index_map_errors(compiler::plan_program_internal::data_of(P, bad)).empty());
}

// The toy's proof modules (plan_proofs.h): the certificates (Cert), the
// structure records (Structure), the challenge order and the pad order, the
// nodes containing `1`, and with a proof system the program's data and its
// check; every import written before its importer, the check's tactic
// imported with each import also as `meta`, and the data and check modules
// with no heartbeat options.
TEST(GordieHowePlanExport, ToyProofModules) {
  const Toy t = toy_system();
  const compiler::ExportMeta meta{"toy", "wide", "c0ffee", "run-0", 0};
  const auto p = compiler::build_program(*t.c, meta);
  const compiler::ProofModuleData d = compiler::proof_module_data(*t.c, meta, p);
  // The toy's mod_q has the digit form, not the field form.
  EXPECT_FALSE(d.field_form);
  const auto mods = compiler::proof_modules(d);
  std::map<std::string, std::string> text;
  std::vector<std::string> order;
  for (const auto &m : mods) {
    const std::string key = m.root.empty() ? m.leaf : m.root + ":" + m.leaf;
    EXPECT_TRUE(text.emplace(key, m.text).second) << key;
    order.push_back(m.root.empty() ? compiler::lean_module_name(meta, m.leaf)
                                   : compiler::check_module_name(meta, m.leaf));
  }
  const bool sys = compiler::system_plan(d).ok;
  for (const char *leaf : {"Cert", "Structure", "Honest.Nodes"})
    EXPECT_EQ(text.count(leaf), 1u) << leaf;
  // The removed modules: the dropped conditions and the modules the library
  // core absorbs.
  for (const char *leaf :
       {"Valid", "Valid.WellFormed", "Valid.Targets", "Valid.Messages", "Valid.Reads",
        "Valid.Degrees", "Valid.Types", "Valid.PadRealized", "Valid.DomainsMatch",
        "Valid.PlanLigero", "Valid.StructureKeys", "Annotations", "Annotations.ExprAnn",
        "Annotations.DegZero", "Annotations.Closures", "Realize", "Facts", "Facts.Model",
        "Facts.SourceValid", "Ready", "Interp", "CertifiedProgram", "Valid.Order", "Valid.Pads"})
    EXPECT_EQ(text.count(leaf), 0u) << leaf;
  if (sys) {
    for (const char *leaf : {"FieldTable", "Tableau", "Data", "Pending.Small", "Pending.Model",
                             "Core", "Certified"})
      EXPECT_EQ(text.count(leaf), 1u) << leaf;
    EXPECT_EQ(text.count("Check/Native:"), 1u);
    EXPECT_EQ(text.count("Check/Kernel:"), 1u);
    EXPECT_EQ(text.count("Check/Kernel:GKR"), 1u);
    EXPECT_EQ(text.count("Pending.Circuits"), 0u);
    // The toy states no figures: no Figures, no honest strategy's modules.
    for (const char *leaf : {"Figures", "Pending.Figures", "Completion"})
      EXPECT_EQ(text.count(leaf), 0u) << leaf;
  }
  auto has = [](const std::string &s, const std::string &x) {
    return s.find(x) != std::string::npos;
  };
  const std::string ns = "GordieHowe.Generated.Toy.QROMParams.";
  const std::string mod_prefix = "GordieHoweCerts.Generated.Toy.QROMParams.";
  for (size_t i = 0; i < mods.size(); ++i) {
    const std::string &m = mods[i].text;
    // The data and check modules (no heartbeat options) and the others.
    const bool core = mods[i].leaf != "Cert" &&
                      mods[i].leaf != "Structure" && mods[i].leaf != "Honest.Nodes";
    EXPECT_EQ(has(m, compiler::kLeanModuleOptions), !core) << mods[i].leaf;
    // A module closing a native check or registering loaded data readers
    // imports their implementation, and each import also as `meta`.
    const bool checks = has(m, "gh_native_check") || has(m, "load_ghc") ||
                        has(m, "load_program_ghc");
    EXPECT_EQ(checks, has(m, "public import " +
                                 std::string(compiler::plan_proofs_internal::kCheckModule) + "\n"))
        << mods[i].leaf;
    EXPECT_EQ(checks, has(m, "\nmeta import ")) << mods[i].leaf;
    for (size_t at = m.find("\npublic import "); at != std::string::npos;
         at = m.find("\npublic import ", at + 1)) {
      const size_t from = at + 15;
      const std::string imp = m.substr(from, m.find('\n', from) - from);
      if (checks) EXPECT_TRUE(has(m, "\nmeta import " + imp + "\n")) << mods[i].leaf << " " << imp;
      // An import of the export is written before its importer, or by the
      // data modules' and the GKR modules' writers.
      std::string leaf;
      if (imp.rfind(mod_prefix, 0) == 0) leaf = imp.substr(mod_prefix.size());
      else if (imp.rfind("GordieHoweCheck.", 0) != 0) continue;
      if (leaf == "Program" || leaf == "Plan" || leaf == "Derivs" || leaf.rfind("GKR.", 0) == 0)
        continue;
      const auto it = std::find(order.begin(), order.end(), imp);
      ASSERT_NE(it, order.end()) << imp;
      EXPECT_LT(size_t(it - order.begin()), i) << mods[i].leaf << " " << imp;
    }
  }
  // The structure records retain one typed compiled payload with a checked hash.
  const std::string &st = text["Structure"];
  EXPECT_TRUE(has(st, "\n# The structure records of `toy-wide`\n"));
  EXPECT_TRUE(has(st, "public import GordieHoweNative.Language.RealizedProgram.Structure\n"));
  EXPECT_TRUE(has(st, "namespace " + ns + "Structure\n"));
  EXPECT_TRUE(has(st, "load_program_ghc \"Structure.ghc\""));
  EXPECT_FALSE(has(st, "def records"));
  EXPECT_TRUE(has(st, "theorem memberValues_eq : records.memberValues = "));
  const auto structure_sections = ghc::read(d.structure_ghc, ghc::gkr_schema());
  ASSERT_EQ(structure_sections.size(), 1u);
  EXPECT_EQ(structure_sections[0].name, "records");
  EXPECT_EQ(structure_sections[0].type.text(), "GordieHowe.RealizedProgram.Structure");
  EXPECT_EQ(structure_sections[0].flags, uint64_t(ghc::kCompile | ghc::kReader));
  // Cert holds the annotations and the completeness certificate the
  // compiler printed, and nothing the dropped conditions read.
  EXPECT_FALSE(d.cert_ghc.empty());
  const std::string &cert = text["Cert"];
  EXPECT_TRUE(has(cert, "load_ghc \"Cert.ghc\""));
  EXPECT_FALSE(has(cert, "def exprAnn"));
  EXPECT_FALSE(has(cert, "def closures"));
  EXPECT_FALSE(has(cert, "def degAnn"));
  EXPECT_FALSE(has(cert, "def readsAnn"));
  EXPECT_FALSE(has(cert, "HonestCert"));
  EXPECT_FALSE(has(cert, "def gens"));
  EXPECT_FALSE(has(cert, "def cderivs"));
  // The MAC's tail is derived at site 1 of the macSite record 0, its first
  // gadget record (Structure).
  EXPECT_TRUE(has(ghc::show(d.cert_ghc, ghc::gkr_schema()), "(.macRow 0 1 .tail)"));
  EXPECT_TRUE(has(ghc::show(d.structure_ghc, ghc::gkr_schema()), ".macSite"));
  // The nodes containing 1: every committed cell's node and every subfield
  // type, in its field (Lean domainField / valueField), each once, in field
  // order.
  using NodeSet = std::set<std::pair<size_t, std::string>>;
  NodeSet want;
  for (const auto &v : p.values) {
    const size_t f = v.field != SIZE_MAX ? v.field : p.domain_fields.at(v.domain);
    if (compiler::program_kind_has_node(v.kind)) {
      EXPECT_FALSE(v.node_name.empty()) << v.name;
      want.insert({f, v.node_name});
    }
    if (v.type.rfind(".sub \"", 0) == 0)
      want.insert({f, v.type.substr(6, v.type.size() - 7)});
  }
  EXPECT_FALSE(want.empty());
  EXPECT_EQ(NodeSet(d.one_nodes.begin(), d.one_nodes.end()), want);
  EXPECT_EQ(d.one_nodes.size(), want.size());
  for (size_t i = 1; i < d.one_nodes.size(); ++i)
    EXPECT_LE(d.one_nodes[i - 1].first, d.one_nodes[i].first);
  EXPECT_TRUE(has(text["Honest.Nodes"], "load_ghc \"Nodes.ghc\""));
  EXPECT_FALSE(has(text["Honest.Nodes"], "def nodes"));
  // No docstring line runs past 100 columns but for one backticked span.
  for (const auto &m : mods) {
    const std::string &s = m.text;
    size_t start = 0;
    while (start < s.size()) {
      size_t end = s.find('\n', start);
      if (end == std::string::npos) end = s.size();
      const std::string line = s.substr(start, end - start);
      if (line.size() > 100) {
        // UTF-8 lines (the anonymous constructors) count bytes; only an
        // unbreakable word may overflow, or a statement's application.
        EXPECT_TRUE(line.find(' ') == std::string::npos || has(line, "⟨") ||
                    line.rfind("    ", 0) == 0)
            << line;
      }
      start = end + 1;
    }
  }
  // A second build renders the same modules.
  const Toy t2 = toy_system();
  const auto d2 = compiler::proof_module_data(
      *t2.c, meta, compiler::build_program(*t2.c, meta));
  const auto mods2 = compiler::proof_modules(d2);
  ASSERT_EQ(mods2.size(), mods.size());
  for (size_t i = 0; i < mods.size(); ++i) {
    EXPECT_EQ(mods2[i].leaf, mods[i].leaf);
    EXPECT_EQ(mods2[i].text, mods[i].text);
  }
}

// The opaque-function set (field_registry.h's opaque_set, the plan's
// `opaqueSet`): one row per kind, in the table's order.
TEST(GordieHowePlanExport, OpaqueSet) {
  using compiler::Frontend;
  EXPECT_STREQ(compiler::opaque_set(false, Frontend::kMdoc, 2), "none");
  EXPECT_STREQ(compiler::opaque_set(false, Frontend::kFalcon, 2), "none");
  EXPECT_STREQ(compiler::opaque_set(true, Frontend::kMdoc, 2), "mdoc");
  EXPECT_STREQ(compiler::opaque_set(true, Frontend::kFalcon, 2), "falcon");
  EXPECT_STREQ(compiler::opaque_set(true, Frontend::kFalcon, 1), "targetBits");
  EXPECT_STREQ(compiler::opaque_set(true, Frontend::kMLDSA, 2), "targetBits");
  EXPECT_STREQ(compiler::opaque_set(true, Frontend::kNone, 2), "targetBits");
  // The toy's opaque values read arguments, and it has no frontend.
  EXPECT_NE(toy_export().find("    hash := \"SHA-384\",\n    opaqueSet := \"targetBits\",\n"),
            std::string::npos);
}

// The program's data and check modules (plan_proofs.h's program_data_modules,
// the descriptors from field_registry.h): the field table's interpretation
// descriptor by the fields' keys and the opaque-function set, every domain's
// tableau descriptor (the library's by its Ligero numbers, or the compiler's
// Johnson certificate), the data, the check (native and kernel), the pending
// conditions, the core conditions and the certified program; none for a
// field the library has no model of.
TEST(GordieHowePlanExport, ProgramDataModules) {
  using Data = compiler::ProofModuleData;
  auto has = [](const std::string &s, const std::string &x) {
    return s.find(x) != std::string::npos;
  };
  auto modules = [](const Data &d) {
    std::map<std::string, std::string> out;
    const compiler::SystemPlan sp = compiler::system_plan(d);
    if (!sp.ok) return out;
    for (const auto &m : compiler::program_data_modules(d, sp))
      out[m.root.empty() ? m.leaf : m.root + ":" + m.leaf] = m.text;
    return out;
  };
  auto domain = [](const std::string &name, size_t field, size_t rate, size_t t,
                   size_t block_enc, size_t reps) {
    Data::Domain dm;
    dm.name = name;
    dm.field = field;
    dm.rate = rate;
    dm.t = t;
    dm.r = t;
    dm.block_enc = block_enc;
    dm.reps = reps;
    dm.k = (block_enc + 1) / (2 + rate);
    dm.N = block_enc - (2 * dm.k - 1);
    dm.split = true;
    return dm;
  };
  // A Falcon-like program: two fields, a circuit per domain, the library's
  // tableaus, the MAC in field 0, a field-form mod_q in field 1.
  Data f;
  f.meta = compiler::ExportMeta{"falcon-native", "narrow", "c0ffee", "run-0", 0, 0,
                                "Sys.Falcon.ROMParams"};
  // A profile with no figure inputs: the core conditions only.
  f.meta.profile = "test";
  f.fields = {{"GF(2^128)", "2", 128}, {"F_q^9", "12289", 9}};
  f.domain_data = {domain("H", 0, 12, 63, 4203, 2), domain("A", 1, 5, 90, 2369, 2)};
  f.circuit_domains = {0, 1};
  f.opaque_args = true;
  f.mac_field = 0;
  f.field_form_fields = {1};
  f.field_form = true;
  ASSERT_TRUE(compiler::system_plan(f).ok) << compiler::system_plan(f).why;
  EXPECT_EQ(compiler::system_plan(f).opaque, "falcon");
  auto t = modules(f);
  std::vector<std::string> leaves;
  for (const auto &m : compiler::program_data_modules(f, compiler::system_plan(f)))
    leaves.push_back(m.root.empty() ? m.leaf : m.root + ":" + m.leaf);
  EXPECT_EQ(leaves,
            (std::vector<std::string>{
                "FieldTable", "Tableau", "Data", "Check/Native:", "Check/Kernel:WellFormed",
                "Check/Kernel:Order", "Check/Kernel:Pads",
                "Check/Kernel:ExprAnn", "Check/Kernel:Derivs", "Check/Kernel:Cells",
                "Check/Kernel:Source", "Check/Kernel:AssignmentReads", "Check/Kernel:Locality", "Check/Kernel:Fields",
                "Check/Kernel:Tableaus", "Check/Kernel:Selections", "Check/Kernel:Completion", "Check/Kernel:Roles", "Check/Kernel:NoFieldForm", "Check/Kernel:Shapes", "Check/Kernel:Figures", "Check/Kernel:SourceRoles", "Check/Kernel:OpaqueSet", "Check/Kernel:",
                "Pending.Small", "Pending.Model", "Check/Kernel:GKR", "Core", "Certified"}));
  const std::string g = "public import GordieHoweCerts.Generated.Sys.Falcon.ROMParams.";
  EXPECT_TRUE(has(t["FieldTable"], "  { interp := .two .gf128 .fq9 .falcon, domainFields := "
                                   "[0, 1],\n    circuitDomains := [0, 1],\n    packing := [\n"
                                   "      { n := 128, q := 2 ^ 2 ^ 4,\n        edges := [],\n"))
      << t["FieldTable"];
  // Each field's packing descriptor (no queries here), by field identifier;
  // its check against the registry's packing facts and the tableaus' fit
  // pending.
  EXPECT_TRUE(has(t["FieldTable"], "        hasNodes := true,\n        masks := [] },\n      { n := 9, q := 12289,\n"))
      << t["FieldTable"];
  EXPECT_TRUE(has(t["FieldTable"], "        hasNodes := true,\n        masks := [] }],\n    noFieldForm := false }\n"))
      << t["FieldTable"];
  EXPECT_TRUE(has(t["Pending.Small"], "theorem packingsOk : data.PackingsOk := by\n"
                                      "  decide +kernel\n"));
  EXPECT_FALSE(has(t["Pending.Small"], "tableausFit"));
  EXPECT_TRUE(has(t["Check/Kernel:Tableaus"],
                  "theorem tableausFitOk : data.tableausB = true := by\n  decide +kernel\n"));
  EXPECT_TRUE(has(t["Check/Kernel:Fields"],
                  "theorem fieldsOk : data.fieldsB = true := by\n"
                  "  rw [← ProgramData.fieldsWithAssignmentReadsB_eq data assignmentReadsOk]\n"
                  "  decide +kernel\n"));
  EXPECT_TRUE(has(t["Check/Kernel:AssignmentReads"],
                  "theorem assignmentReadsOk : data.assignmentReadsB = true := by\n"
                  "  decide +kernel\n"));
  EXPECT_TRUE(has(t["Tableau"], "  [.library .gf128K300R2,\n    .library .falconNativeROMA]\n"))
      << t["Tableau"];
  EXPECT_TRUE(has(t["Data"], "  { inputs := runtimeInputs, completion := completionInputs, "
                             "hints := hints,\n    circuits := [GKR.H.cert, GKR.A.cert],\n"
                             "    shapes := [],\n    sourceRoles := none }\n"))
      << t["Data"];
  EXPECT_TRUE(has(t["Data"], "abbrev runtimeInputs : GordieHowe.RuntimeInputs :=\n"
                             "  { program := Program.program, plan := Plan.plan, fieldTable := "
                             "fieldTable,\n    tableaus := tableaus, figures := "
                             "GordieHowe.FiguresData.none }\n"))
      << t["Data"];
  EXPECT_TRUE(has(t["Data"], "abbrev completionInputs : GordieHowe.CompletionInputs :=\n"));
  EXPECT_TRUE(has(t["Data"], "  { exprAnn := Cert.exprAnn, derivs := Derivs.derivations,\n"
                             "    assignmentReads := Cert.assignmentReads }\n"))
      << t["Data"];
  for (const char *x : {"GKR.H\n", "GKR.A\n", "Tableau\n", "FieldTable\n"})
    EXPECT_TRUE(has(t["Data"], g + x)) << x;
  EXPECT_FALSE(has(t["Data"], g + "Figures\n"));
  // The check: one compiled run at the unfolded data; for the kernel, a leaf
  // per part and their composition in the shape of programOkB.
  const std::string &native = t["Check/Native:"];
  EXPECT_TRUE(has(native, "namespace GordieHoweCheck.Sys.Falcon.ROMParams\n"));
  EXPECT_TRUE(has(native, "theorem programOk : data.programOkB false = true := by\n  delta data\n"
                          "  gh_native_check\n"));
  EXPECT_TRUE(has(native, "meta import GordieHoweCerts.Generated.Sys.Falcon.ROMParams.GKR.A\n"));
  EXPECT_FALSE(has(native, compiler::kLeanModuleOptions));
  EXPECT_TRUE(has(t["Check/Kernel:Locality"],
                  "theorem localityOk : data.localityB = true := by\n"
                  "  rw [← ProgramData.localityWithAssignmentReadsB_eq data assignmentReadsOk]\n"
                  "  decide +kernel\n"));
  EXPECT_FALSE(has(t["Check/Kernel:Locality"], "meta import"));
  const std::string &kernel = t["Check/Kernel:"];
  EXPECT_TRUE(has(kernel, "and_intro assignmentReadsOk"));
  EXPECT_TRUE(has(kernel, "public import GordieHoweCheck.Sys.Falcon.ROMParams.Shapes\n"));
  EXPECT_TRUE(has(kernel, "public import GordieHoweCheck.Sys.Falcon.ROMParams.Figures\n"));
  EXPECT_TRUE(has(kernel, "            shapesOk)\n          figuresPartOk)\n        sourceRolesOk)\n      gkrOk)\n    opaqueSetOk\n"));
  EXPECT_TRUE(has(kernel, "public import GordieHoweCheck.Sys.Falcon.ROMParams.OpaqueSet\n"));
  EXPECT_TRUE(has(t["Check/Kernel:OpaqueSet"],
                  "theorem opaqueSetOk : data.opaqueSetB = true := by\n  decide +kernel\n"));
  EXPECT_TRUE(has(t["Check/Kernel:Figures"],
                  "theorem figuresPartOk : data.figuresPartB false = true := by\n  decide +kernel\n"));
  EXPECT_TRUE(has(t["Check/Kernel:SourceRoles"],
                  "theorem sourceRolesOk : data.sourceRolesB = true := by\n  decide +kernel\n"));
  EXPECT_FALSE(has(t["Data"], g + "SourceRoles\n"));
  // The pending conditions, the core conditions from the check.
  EXPECT_FALSE(has(t["Pending.Small"], "coded"));
  EXPECT_FALSE(has(t["Pending.Small"], "selections"));
  EXPECT_TRUE(has(t["Core"], "  selections := checked.selections\n"));
  const std::string &model = t["Pending.Model"];
  EXPECT_TRUE(has(model, "  .of_models data.fieldTable.interp.models (by decide +kernel) "));
  EXPECT_TRUE(has(model, "(falconOps_opaqueBit (by decide +kernel))"));
  EXPECT_TRUE(has(model, "Interp.macModel_of_tails (f := 0) (nm := \"mac.target_bits\") (by "
                         "decide +kernel)\n      RealizedProgram.gf128_macFieldOk "
                         "falconOps_target_bits"));
  EXPECT_TRUE(has(model, "Interp.fieldFormModel_of_fields (L := [1]) (by decide +kernel)\n      "
                         "RealizedProgram.fq9_readLinear"));
  EXPECT_TRUE(has(model, "public import GordieHowe.Applications.Falcon512.Frontend.Fields\n"));
  EXPECT_TRUE(has(t["Check/Kernel:GKR"], "  | 1, _ => exact ⟨GKR.A.cert.circuit_ok, rfl⟩\n"));
  EXPECT_TRUE(has(t["Check/Kernel:GKR"], "GordieHoweCheck.Sys.Falcon.ROMParams.GKR.A.Circuit\n"));
  EXPECT_TRUE(has(t["Check/Kernel:GKR"], "apply (ProgramData.gkrPartB_iff data).2"));
  EXPECT_FALSE(has(t["Check/Kernel:GKR"], "decide +kernel"));
  EXPECT_EQ(t.count("Pending.Circuits"), 0u);
  const std::string &core = t["Core"];
  EXPECT_TRUE(has(core, "public import GordieHoweCheck.Sys.Falcon.ROMParams\n"));
  EXPECT_TRUE(has(core, "theorem checked : CheckedConditions data false :=\n"
                        "  programOk_sound data GordieHoweCheck.Sys.Falcon.ROMParams.programOk\n"));
  EXPECT_TRUE(has(core, "  fields := .of_descs fieldTableOk checked.fieldDescs packingsOk\n"
                        "    (.of_descs packingsOk checked.tableaus)\n"));
  EXPECT_TRUE(has(core, "  order := checked.order\n  pads := checked.pads\n"));
  EXPECT_TRUE(has(core, "  circuits := checked.circuits\n"));
  EXPECT_FALSE(has(core, "Pending.Circuits"));
  // No figures: the proof system at the core conditions.
  const std::string &cert = t["Certified"];
  EXPECT_TRUE(has(cert, "abbrev interp : Interp :=\n  Interp.twoField RealizedProgram.gf128 "
                        "RealizedProgram.fq9 RealizedProgram.falconOps\n"));
  EXPECT_TRUE(has(cert, "theorem interp_eq : interp = data.interp := by\n  with_reducible rfl\n"));
  EXPECT_TRUE(has(cert, "def proofSystem : ProofSystems :=\n"
                        "  runtimeInputs.proofSystemOf runtimeParts (core.certs runtimeParts_eq)\n"
                        "    core.coreFacts\n"));
  EXPECT_FALSE(has(cert, "SelSound"));
  EXPECT_FALSE(has(cert, "theorem conditions"));
  EXPECT_FALSE(has(cert, "noncomputable"));
  EXPECT_TRUE(has(cert, "theorem runtimeParts_eq : runtimeParts = data.parts :=\n"
                        "  data.sourceParts_eq\n"));
  EXPECT_FALSE(has(cert, "abbrev runtimeInputs"));
  EXPECT_FALSE(has(cert, "CertifiedCore"));
  EXPECT_TRUE(has(cert, "def runtimeParts : SourceParts :=\n  .ofTriples ["));
  // An ML-DSA-like program: domain A's tableau is the compiler's Johnson
  // certificate (agreement threshold 975), the MAC in field 1.
  Data ml = f;
  ml.meta.config = "mldsa-native";
  ml.meta.lean_name = "Sys.MLDSA.ROMParams";
  ml.fields = {{"F_q^6", "8380417", 6}, {"GF(2^128)", "2", 128}};
  Data::Domain ma = domain("A", 0, 9, 74, 3376, 1);
  ma.agree = 975;
  ma.line = compiler::ligero_choice_detail::best_line_exhaustive(ma.N, ma.k, ma.agree);
  ml.domain_data = {ma, domain("H", 1, 12, 63, 3955, 2)};
  ml.mac_field = 1;
  ml.field_form_fields = {};
  ml.field_form = false;
  EXPECT_EQ(compiler::system_plan(ml).opaque, "targetBits");
  t = modules(ml);
  EXPECT_TRUE(has(t["Tableau"], "  [.johnson ⟨9, 74, 3376, 1, 74, 975, 17258473, 8, 24, 163⟩,\n"
                                "    .library .gf128K282R2]\n"))
      << t["Tableau"];
  EXPECT_TRUE(has(t["Certified"], "  Interp.twoField RealizedProgram.fq6 RealizedProgram.gf128 "
                                  "RealizedProgram.targetBitsFn\n"));
  EXPECT_TRUE(has(t["Pending.Model"], "Interp.opaqueBit_of_lt_two targetBitsFn_lt_two"));
  EXPECT_TRUE(has(t["Pending.Model"], "Interp.fieldFormModel_of_fields (L := []) (by decide "
                                      "+kernel)\n      trivial"));
  // A configuration with figures: the figures, the honest strategy's
  // conditions and the certified program.
  Data mf = ml;
  mf.meta.config = "mldsa-native";
  mf.meta.profile = "narrow";
  mf.phases = 2;
  mf.digest_bytes = 32;
  mf.source_challenges = {{0, 1, "264"}, {1, 1, "295"}};
  t = modules(mf);
  for (const char *leaf : {"Figures", "Completion", "Check/Kernel:Figures"})
    EXPECT_EQ(t.count(leaf), 1u) << leaf;
  EXPECT_TRUE(has(t["FieldTable"], " noFieldForm := true }\n"));
  EXPECT_TRUE(has(t["Figures"], "def sourceErrors (j : Nat) : Nat × Nat :=\n  if j = 0 then "
                                "(264, 2 ^ 128) else (295, 2 ^ 128)\n"));
  EXPECT_TRUE(has(t["Figures"], "  { present := true, figures := figures, maxArray := [1024, 1024], maxRead := "
                                "[2200, 1250],\n    restRead := [2200, 1250], grants := [], "
                                "grantMax := 0, sourceErrors := sourceErrors,\n"
                                "    defaultLoads := true }\n"))
      << t["Figures"];
  EXPECT_TRUE(has(t["Data"], "figures := figuresData"));
  EXPECT_TRUE(has(t["Completion"], "theorem rolesOk : data.RolesOk data.completion :=\n"
                                   "  (programOk_sound data GordieHoweCheck.Sys.MLDSA.ROMParams.programOk).roles\n"));
  EXPECT_TRUE(has(t["Completion"], ".programOk).noFieldForm\n"));
  EXPECT_FALSE(has(t["Completion"], "gh_native_check"));
  EXPECT_FALSE(has(t["Completion"], "meta import"));
  EXPECT_EQ(t.count("Pending.Figures"), 0u);
  const std::string &mc = t["Certified"];
  EXPECT_FALSE(has(mc, "figuresPresent"));
  EXPECT_TRUE(has(mc, "  .of_descs data packingsOk checked.figures"));
  EXPECT_TRUE(has(t["Core"], "theorem checked : CheckedConditions data true :=\n"));
  EXPECT_TRUE(has(t["Check/Native:"], "theorem programOk : data.programOkB true = true := by\n"));
  EXPECT_TRUE(has(t["Check/Kernel:Figures"],
                  "theorem figuresPartOk : data.figuresPartB true = true := by\n"));
  EXPECT_TRUE(has(t["Figures"], "  chernoff := 2800\n  zNum := 65\n  zDen := 64\n"))
      << t["Figures"];
  EXPECT_FALSE(has(mc, "noncomputable"));
  EXPECT_FALSE(has(mc, "def system"));
  EXPECT_TRUE(has(mc, "  runtimeInputs.ready conditions.readyFacts\n"));
  EXPECT_TRUE(has(mc, "theorem conditions : ProgramConditions data :=\n  { core with\n"));
  EXPECT_TRUE(has(mc, "def certified : CertifiedProgram Plan.plan Program.program interp :=\n"
                      "  { runtimeInputs.certified completionInputs conditions.fullFacts with\n"
                      "    ready := ready }\n"));
  EXPECT_TRUE(has(mc, "def proofSystem : ProofSystems :=\n"
                      "  runtimeInputs.proofSystemOf runtimeParts "
                      "(conditions.toCoreConditions.certs runtimeParts_eq)\n"
                      "    conditions.toCoreConditions.coreFacts\n"));
  // A field-form mod_q: no noFieldForm in the field table.
  Data mff = mf;
  mff.field_form = true;
  t = modules(mff);
  EXPECT_TRUE(has(t["FieldTable"], " noFieldForm := false }\n"));
  EXPECT_TRUE(has(t["Completion"], ".programOk).noFieldForm\n"));
  // A one-field program with no circuit and a Johnson tableau.
  Data sha;
  sha.meta = compiler::ExportMeta{"sha256-batched-1024", "narrow", "c0ffee", "run-0", 0, 0,
                                  "Sys.SHA.ROMParams"};
  sha.fields = {{"GF(2^128)", "2", 128}};
  Data::Domain h = domain("H", 0, 12, 63, 4096, 2);
  h.agree = 1100;
  h.line = compiler::ligero_choice_detail::best_line_exhaustive(h.N, h.k, h.agree);
  ASSERT_TRUE(h.line.has_value());
  ASSERT_FALSE(h.line->unique_decoding);
  sha.domain_data = {h};
  EXPECT_EQ(compiler::system_plan(sha).opaque, "none");
  t = modules(sha);
  EXPECT_TRUE(has(t["FieldTable"], "{ interp := .one .gf128 .none, domainFields := [0],\n"));
  EXPECT_TRUE(has(t["Tableau"], "  [.johnson ⟨12, 63, 4096, 2, 63, 1100, " +
                                    std::to_string(h.line->count) + ", " +
                                    std::to_string(h.line->m) + ", " +
                                    std::to_string(h.line->bj) + ", " +
                                    std::to_string(h.line->h) + "⟩]\n"))
      << t["Tableau"];
  EXPECT_TRUE(has(t["Certified"], "  ⟨fun _ => RealizedProgram.gf128, fun _ _ _ => 0⟩\n"));
  EXPECT_TRUE(has(t["Pending.Model"], "Interp.macModel_of_noTail"));
  EXPECT_TRUE(has(t["Data"], "    circuits := [],\n"));
  EXPECT_TRUE(has(t["Check/Kernel:GKR"],
                  "  have hl : data.fieldTable.circuitDomains.length = 0 := rfl\n  omega\n"));
  // Two fields with no frontend: the two-field interpretation.
  Data rsa = f;
  rsa.meta.config = "rsa-auto_t9_m2_2048_batched";
  rsa.meta.lean_name = "Sys.RSA.ROMParams";
  rsa.fields = {{"GF(2^128)", "2", 128}, {"Goldilocks^2", "18446744069414584321", 2}};
  rsa.domain_data = {domain("H", 0, 12, 63, 4203, 2), domain("A", 1, 5, 96, 3583, 2)};
  rsa.field_form_fields = {};
  t = modules(rsa);
  EXPECT_TRUE(has(t["Certified"], "  Interp.twoField RealizedProgram.gf128 RealizedProgram.gold2 "
                                  "RealizedProgram.targetBitsFn\n"));
  EXPECT_TRUE(has(t["Pending.Model"], "targetBitsFn_target"));
  // Table selections: their certificates in Selections, read by the data; the
  // proof system is the same.
  Data prod = f;
  prod.selections = {"⟨0, { dom := 0 }⟩"};
  t = modules(prod);
  EXPECT_FALSE(has(t["FieldTable"], "productFree"));
  EXPECT_TRUE(has(t["Selections"], "abbrev selections : List GordieHowe.RealizedProgram.SelCert :=\n"
                                   "  [⟨0, { dom := 0 }⟩]\n"));
  EXPECT_TRUE(has(t["Data"], ",\n    selections := selections }"));
  EXPECT_TRUE(has(t["Certified"], "def proofSystem : ProofSystems :=\n"));
  EXPECT_FALSE(has(t["Certified"], "proofSystemOf (hsel"));
  // No proof system for a field the library has no model of, nor for a
  // tableau with neither a library certificate nor the compiler's.
  Data p384 = rsa;
  p384.fields[1] = {"F_p384", "3940", 1};
  EXPECT_FALSE(compiler::system_plan(p384).ok);
  EXPECT_TRUE(has(compiler::system_plan(p384).why, "F_p384"));
  for (const auto &m : compiler::proof_modules(p384)) EXPECT_NE(m.leaf, "Data");
  Data bare = rsa;
  bare.domain_data[0] = domain("H", 0, 12, 63, 4096, 2);
  EXPECT_FALSE(compiler::system_plan(bare).ok);
  EXPECT_TRUE(has(compiler::system_plan(bare).why, "tableau"));
  // A packing edge the field's packing facts do not realize.
  Data edge = sha;
  edge.domain_data[0].edges = {"1:16:s", "16:2:m", "32:2:m", "64:2:m"};
  EXPECT_FALSE(compiler::system_plan(edge).ok);
  EXPECT_TRUE(has(compiler::system_plan(edge).why, "32:2:m"));
  edge.domain_data[0].edges = {"1:16:s", "16:8:m"};
  EXPECT_TRUE(compiler::system_plan(edge).ok);
  // The tree through GF(2^32).
  edge.domain_data[0].edges = {"1:16:s", "16:2:m", "32:4:m"};
  EXPECT_TRUE(compiler::system_plan(edge).ok);
  // The ECDSA mDL: domain A over F_p256, the mDL frontend's opaque
  // functions; every field, P-256's included, has a codec.
  Data md = rsa;
  md.meta.config = "mdoc-narrow";
  md.meta.lean_name = "Sys.MDL.ROMParams";
  md.fields = {{"GF(2^128)", "2", 128},
               {"F_p256",
                "115792089210356248762697446949407573530086143415290314195533631308867097853951",
                1}};
  ASSERT_TRUE(compiler::system_plan(md).ok) << compiler::system_plan(md).why;
  EXPECT_EQ(compiler::system_plan(md).opaque, "mdoc");
  t = modules(md);
  EXPECT_TRUE(has(t["FieldTable"], "{ interp := .two .gf128 .p256 .mdoc,"));
  EXPECT_TRUE(has(t["Certified"], "  Interp.twoField RealizedProgram.gf128 RealizedProgram.p256 "
                                  "RealizedProgram.mdocOps\n"));
  EXPECT_TRUE(has(t["Pending.Model"], "public import GordieHowe.Applications.MDL.Frontend\n"));
  EXPECT_TRUE(has(t["Pending.Model"], "(mdocOps_opaqueBit rfl (by decide +kernel))"));
  EXPECT_TRUE(has(t["Pending.Model"], "RealizedProgram.gf128_macFieldOk mdocOps_target_bits"));
  EXPECT_FALSE(has(t["Pending.Small"], "coded"));
  // P-256's q has a Lean name outside GordieHoweNative (`P256.p`), which the field table does not
  // import: the descriptor prints its numeral.
  EXPECT_TRUE(has(t["FieldTable"], "{ n := 1, q := 1157920892103562487626974469494075735300861434152"
                                   "90314195533631308867097853951,"))
      << t["FieldTable"];
  EXPECT_FALSE(has(t["FieldTable"], "P256.p"));
  // A field-form mod_q in a field without a linear reading.
  Data form = rsa;
  form.field_form_fields = {1};
  EXPECT_FALSE(compiler::system_plan(form).ok);
}

// Typed record diagnostics keep the established textual assertions readable.
std::vector<std::pair<size_t, std::string>> route_text(const compiler::StructureRecords &r) {
  std::vector<std::pair<size_t, std::string>> out;
  for (const auto &[key, value] : r.routes)
    out.push_back({key, compiler::structure_records_internal::route(value)});
  return out;
}

std::vector<std::pair<size_t, std::string>> ivl_text(const compiler::StructureRecords &r) {
  std::vector<std::pair<size_t, std::string>> out;
  for (const auto &[key, value] : r.ivl_sources)
    out.push_back({key, compiler::structure_records_internal::ivl_source(value)});
  return out;
}

// The structure records' printer: every list keyed and sorted, a list out
// of order refused.
TEST(GordieHowePlanExport, StructureRecordsPrint) {
  compiler::StructureRecords r;
  r.gadgets.push_back({compiler::StructureRecords::GadgetKind::macSite, {7, 5}, {3, 4}, {1, 2, 3}, {}});
  r.origins = {{3, {0, 0}}, {4, {0, 1}}};
  r.logup_hosts = {{{0, 1}, {2, 3}}};
  using K = compiler::StructureRecords::IvlSource::Kind;
  r.ivl_sources = {{3, {K::prime, {}}}, {9, {K::range, {4}}}};
  r.mac_requests = {{0, {5, 6, 7}}};
  const std::string o = compiler::print_structure(r);
  EXPECT_NE(o.find("  gadgets := [\n    { kind := .macSite, preds := [7, 5], values := [3, 4], "
                   "params := [1, 2, 3], parts := [] }]\n"),
            std::string::npos)
      << o;
  EXPECT_NE(o.find("  origins := [(3, ⟨0, 0⟩),\n    (4, ⟨0, 1⟩)]\n"), std::string::npos) << o;
  EXPECT_NE(o.find("  logupHosts := [((0, 1), (2, 3))]\n"), std::string::npos) << o;
  EXPECT_NE(o.find("  ivlSources := [(3, .prime),\n    (9, .range 4)]\n"), std::string::npos)
      << o;
  EXPECT_NE(o.find("  macRequests := [(0, [5, 6, 7])]\n"), std::string::npos) << o;
  EXPECT_NE(o.find("  messages := []\n"), std::string::npos) << o;
  r.origins = {{4, {0, 1}}, {3, {0, 0}}};
  EXPECT_THROW(compiler::print_structure(r), std::runtime_error);
  r.origins = {{3, {0, 0}}, {3, {0, 1}}};
  EXPECT_THROW(compiler::print_structure(r), std::runtime_error);
}

// The digit requests of a modular equality (Lean
// `Export.ModEquality.digitRequests`).
TEST(GordieHowePlanExport, StructureDigitRequests) {
  using compiler::structure_records_internal::digit_requests;
  EXPECT_EQ(digit_requests("m", 1, true), (std::vector<std::string>{"m.q"}));
  EXPECT_EQ(digit_requests("m", 1, false), (std::vector<std::string>{"m.q"}));
  EXPECT_EQ(digit_requests("m", 2, true), (std::vector<std::string>{"m.low", "m.high"}));
  EXPECT_EQ(digit_requests("m", 3, true),
            (std::vector<std::string>{"m.d0", "m.d1", "m.high"}));
  EXPECT_EQ(digit_requests("m", 2, false), (std::vector<std::string>{"m.d0", "m.d1"}));
}

// The bound values' record lookups (Structure.boundRecs): a private input
// bound to its digits and one bound to the digits of itself + c each name
// the range lookup whose record they are; a bound value without a record
// fails the export.
TEST(GordieHowePlanExport, StructureBoundRecs) {
  static const Env *e = new Env;
  Sys cs{"gh-plan-export-bound"};
  auto &A = cs.domain(e->a_profile(), "A");
  auto y = A.priv(Subfield{}, "y", 4);
  assert_range(y, 3000, "y");
  auto z = A.priv(Subfield{}, "z", 4);
  auto off = A.constant("z.offset", AV(4, e->af.of_scalar(2999)));
  assert_range(z + off, 5999, "z");
  const auto c = compile(cs);
  const compiler::ExportMeta meta{"bound", "wide", "c0ffee", "run-0", 0};
  const auto p = compiler::build_program(*c, meta);
  const ir::Certificates certs = compiler::export_certificates(*c);
  const compiler::StructureRecords r = compiler::build_structure(*c, p, certs);
  std::set<size_t> bound, keyed;
  for (size_t v = 0; v < p.values.size(); ++v)
    if (p.values[v].kind == "bound") bound.insert(v);
  EXPECT_EQ(bound.size(), 2u);
  std::string want = "  boundRecs := [";
  for (const auto &[v, pid] : r.bound_recs) {
    keyed.insert(v);
    ASSERT_LT(pid, p.predicates.size());
    const auto &q = p.predicates[pid];
    // The request's in predicate, named after the request, the value its
    // record (v, or v + c).
    EXPECT_EQ(q.name, p.values[v].name);
    EXPECT_EQ(q.kind, "mem") << q.body;
    const std::string sv = std::to_string(v);
    EXPECT_TRUE(q.body.find("[.leaf " + sv + "] (.range ") != std::string::npos ||
                q.body.find("[.add (.leaf " + sv + ") (.leaf ") != std::string::npos)
        << q.body;
    want += (want.back() == '[' ? "(" : ",\n    (") + std::to_string(v) + ", " +
            std::to_string(pid) + ")";
  }
  EXPECT_EQ(keyed, bound);
  const std::string o = compiler::print_structure(r);
  EXPECT_NE(o.find(want + "]\n"), std::string::npos) << o;
  // A bound value with no record lookup: the export fails.
  compiler::ProgramData q = p;
  size_t other = 0;
  while (bound.count(other)) ++other;
  q.values.at(other).kind = "bound";
  compiler::StructureRecords r2;
  EXPECT_THROW(compiler::fill_bound_recs(*c, q, certs, r2), std::runtime_error);
}

// The late values' messages (Structure.messages): the toy's MAC tag is a
// late value whose message is listed, keyed by the tag; every message value
// is listed. Two messages of one late value fail the export.
TEST(GordieHowePlanExport, StructureMessages) {
  const Toy t = toy_system();
  const ir::Program &P = t.c->program();
  const auto ms = compiler::structure_records_internal::messages_of(P);
  size_t messages = 0;
  for (const ir::Value &x : P.values)
    if (x.kind == ir::Value::kMessage) ++messages;
  EXPECT_GE(messages, 1u);
  ASSERT_EQ(ms.size(), messages);
  for (size_t i = 0; i < ms.size(); ++i) {
    const auto [u, m] = ms[i];
    if (i > 0) EXPECT_LT(ms[i - 1].first, u);
    EXPECT_EQ(P.values.at(m).kind, ir::Value::kMessage);
    EXPECT_EQ(size_t(P.values.at(m).ref), u);
    EXPECT_EQ(P.values.at(u).kind, ir::Value::kLate);
  }
  const compiler::ExportMeta meta{"toy", "wide", "c0ffee", "run-0", 0};
  const auto p = compiler::build_program(*t.c, meta);
  const compiler::StructureRecords r =
      compiler::build_structure(*t.c, p, compiler::export_certificates(*t.c));
  EXPECT_EQ(r.messages, ms);
  EXPECT_NE(compiler::print_structure(r).find(
                "  messages := [(" + std::to_string(ms[0].first) + ", " +
                std::to_string(ms[0].second) + ")"),
            std::string::npos);
  // A second message of the same late value: the export fails.
  ir::Program Q = P;
  ir::Value dup = Q.values.at(ms[0].second);
  dup.name += ".again";
  Q.values.push_back(dup);
  EXPECT_THROW(compiler::structure_records_internal::messages_of(Q), std::runtime_error);
}

// The names of the domains a module's text lists, in order: each
// `domains := [` list's `{ name := "…"` entries (the plan's and the
// program's printers both open a domain so).
std::vector<std::string> domain_names(const std::string &text) {
  std::vector<std::string> out;
  const size_t at = text.find("domains := [");
  if (at == std::string::npos) return out;
  // The list ends at the first "]\n" closing it at depth 0.
  size_t depth = 0, i = at + std::string("domains := ").size();
  const std::string key = "{ name := \"";
  for (; i < text.size(); ++i) {
    if (text[i] == '[' || text[i] == '{' || text[i] == '(') ++depth;
    if (text[i] == ']' || text[i] == '}' || text[i] == ')') {
      if (--depth == 0) break;
    }
    if (depth == 2 && text.compare(i, key.size(), key) == 0) {
      const size_t s = i + key.size();
      out.push_back(text.substr(s, text.find('"', s) - s));
    }
  }
  return out;
}

// The plan lists domain d at position d of the program's domains (Lean
// `Plan.domainAt`, checked by `domainsAlignedB`): the toy's plan and
// program name H, A in that order; a program whose domains are swapped
// does not.
TEST(GordieHowePlanExport, DomainOrder) {
  const Toy t = toy_system();
  const compiler::ExportMeta meta{"toy", "wide", "c0ffee", "run-0", 0};
  const std::string plan = compiler::export_lean_plan(*t.c, meta);
  const std::string program = compiler::export_lean_program(*t.c, meta);
  const std::vector<std::string> pd = domain_names(plan), qd = domain_names(program);
  EXPECT_EQ(pd, (std::vector<std::string>{"H", "A"})) << plan;
  EXPECT_EQ(qd, pd) << program;
  for (size_t d = 0; d < t.c->num_domains(); ++d) EXPECT_EQ(qd.at(d), t.c->domain(d).name);
  // The program's domains hand-swapped: the positions disagree.
  std::vector<std::string> swapped = qd;
  std::swap(swapped[0], swapped[1]);
  EXPECT_NE(swapped, pd);
}

// The Honest module's nodes, whole.
TEST(GordieHowePlanExport, HonestNodesModuleText) {
  compiler::ProofModuleData d;
  d.meta = compiler::ExportMeta{"mldsa-native", "narrow", "d42b085", "exports", 0};
  d.one_nodes = {{0, "GF(p^1)"}, {1, "bit"}, {1, "GF(2^16)"}};
  std::string golden = R"lean(module

public import GordieHowe.Language.Honest.Check
public import GordieHowe.Language.Realizations.Circuit.LoadNative
meta import GordieHowe.Language.Honest.Check
meta import GordieHowe.Language.Realizations.Circuit.LoadNative

@[expose] public section

/-!
# The nodes containing `1` in `mldsa-native-narrow`

Generated by `lib/gordiehowe/compiler/plan_proofs.h` from the compiled system; do not edit.

- C++ commit: `d42b085`
- bench run: `exports`

The nodes `GordieHowe.Generated.MLDSA44.Native.ROMParams.Honest.nodes` the honest strategy's checks
read: the node of every committed cell and the subfield of every subfield-typed value, by field
identifier and name.
-/

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace GordieHowe.Generated.MLDSA44.Native.ROMParams.Honest

load_ghc "Nodes.ghc" "NODES_HASH"

/-- The finite node list used by the completion checks. -/
theorem nodes_eq : nodes = [(0, "GF(p^1)"), (1, "bit"), (1, "GF(2^16)")] := rfl

end GordieHowe.Generated.MLDSA44.Native.ROMParams.Honest
)lean";
  char hash[17];
  std::snprintf(hash, sizeof(hash), "%016llx", static_cast<unsigned long long>(
      ghc::fnv1a(ghc::honest_nodes_file(d.one_nodes))));
  golden.replace(golden.find("NODES_HASH"), 10, hash);
  const compiler::ProofModule m = compiler::honest_nodes_module(d);
  EXPECT_EQ(m.leaf, "Honest.Nodes");
  EXPECT_EQ(m.text, std::string(compiler::kLeanLicenseHeader) + golden);
  // No node: the same module shape, loading a typed empty list.
  d.one_nodes.clear();
  EXPECT_NE(compiler::honest_nodes_module(d).text.find("load_ghc \"Nodes.ghc\""),
            std::string::npos);
  EXPECT_NE(ghc::show(ghc::honest_nodes_file(d.one_nodes), ghc::gkr_schema()).find("[]"),
            std::string::npos);
}

// The figures the compiler computes (program_figures), each the Lean
// function of the ready data (ProgramFigures.lean): rounds `figRounds`,
// leaves, queries, verifier queries `figKq`, digests `figDigests` and
// positions, on two domains with one batch and one circuit each.
TEST(GordieHowePlanExport, ProgramFiguresArithmetic) {
  compiler::ProofModuleData d;
  d.phases = 2;
  d.digest_bytes = 32;
  compiler::ProofModuleData::Domain a, h;
  a.name = "A";
  a.N = 2763;
  a.t = 74;
  a.edges = {"1:6:m"};
  a.batches = {{false, 12}};
  a.circuits = {{17, 16}};
  h.name = "H";
  h.N = 3392;
  h.t = 63;
  h.edges = {"1:16:s", "16:4:m", "64:2:m", "16:8:m"};
  h.batches = {{true, 15}};
  h.circuits = {{17, 15}};
  d.domain_data = {a, h};
  const compiler::ProgramFigureValues v = compiler::program_figures(d);
  // 1 + 2 · 2 + 2 · 2, A: (2 · 12 + 5) + 1 + (2 · 1 + 3) + (2 + 4 · 17) · 16 + 1,
  // H: (2 · 15 + 13) + 1 + (2 · 4 + 3) + (2 + 4 · 17) · 15 + 1.
  EXPECT_EQ(v.rounds, 9u + 1156u + 1106u);
  EXPECT_EQ(v.N, 3392u);
  EXPECT_EQ(v.nq, 137u);
  EXPECT_EQ(v.pos, 6155u);
  // 2 · rounds + two branches per domain + 137 · (1 + log₂ 6784).
  EXPECT_EQ(v.kq, 2u * 2271u + 4u + 137u * 13u);
  // max 2 (rounds · 2) + the largest branch count + 1.
  EXPECT_EQ(v.D, 2u * 2271u + 2u + 1u);
  // One domain: rounds · 1.
  d.domain_data = {a};
  const compiler::ProgramFigureValues w = compiler::program_figures(d);
  EXPECT_EQ(w.D, w.rounds + 2u + 1u);
}

// The configurations' figure inputs: today's values, and none (no Figures
// module) for a configuration that states no figures.
TEST(GordieHowePlanExport, FigureInputs) {
  const compiler::FigureInputs *in = compiler::figure_inputs("mldsa-native-narrow");
  ASSERT_NE(in, nullptr);
  EXPECT_EQ(in->chernoff, 2800u);
  EXPECT_EQ(in->error_max, 69439724u);
  EXPECT_EQ(in->error_exp, 140u);
  ASSERT_EQ(in->domains.size(), 2u);
  EXPECT_EQ(in->domains[0].max_read, 2200u);
  const compiler::FigureInputs *w = compiler::figure_inputs("falcon-native-wide");
  ASSERT_NE(w, nullptr);
  EXPECT_TRUE(w->domains[1].grant_stage);
  EXPECT_EQ(w->domains[1].rest_read, 200u);
  EXPECT_EQ(in->z_num, 65u);
  EXPECT_EQ(in->z_den, 64u);
  EXPECT_TRUE(in->configuration);
  EXPECT_EQ(compiler::figure_inputs("toy-wide"), nullptr);
  // The ECDSA mDL states figures that no configuration reads, at a point `z`
  // with `z^64 < 2` (its range challenges draw 64 bytes per value).
  const compiler::FigureInputs *md = compiler::figure_inputs("mdoc-narrow");
  ASSERT_NE(md, nullptr);
  EXPECT_FALSE(md->configuration);
  EXPECT_LT(std::pow(double(md->z_num) / double(md->z_den), 64.0), 2.0);
  compiler::ProofModuleData d;
  d.meta = compiler::ExportMeta{"toy", "wide", "c0ffee", "run-0", 0};
  for (const auto &m : compiler::proof_modules(d)) EXPECT_NE(m.leaf, "Figures");
}

// The packing descriptors: one per field a domain has, at its queries (an
// edge the field does not realize answered `false`).
TEST(GordieHowePlanExport, PackingDescriptors) {
  compiler::ProofModuleData d;
  d.meta = compiler::ExportMeta{"toy", "wide", "c0ffee", "run-0", 0};
  d.fields = {{"GF(2^128)", "2", 128}};
  compiler::ProofModuleData::Domain h;
  h.name = "H";
  h.field = 0;
  h.edges = {"1:16:s", "16:8:m", "64:2:m"};
  d.domain_data = {h};
  d.packing_queries.resize(1);
  d.packing_queries[0].edges = h.edges;
  d.packing_queries[0].nodes = {{"GF(2^16)", 16}, {"bit", 1}};
  d.packing_queries[0].skips = {{16, 2}};
  const compiler::SystemPlan sp = compiler::system_plan(d);
  EXPECT_EQ(compiler::packing_desc_text(d, sp, 0),
            "{ n := 128, q := 2 ^ 2 ^ 4,\n"
            "  edges := [(1, 16, .squaringChain, true), (16, 8, .subfieldMasks, true), "
            "(64, 2, .subfieldMasks, true)],\n"
            "  nodeDegs := [(\"GF(2^16)\", some 16), (\"bit\", some 1)],\n"
            "  skips := [(16, 2, true)],\n  hasNodes := true,\n"
            "  masks := [(1, 16, .squaringChain, 0, 136), "
            "(16, 8, .subfieldMasks, 64, 0), (64, 2, .subfieldMasks, 16, 0)] }");
  d.packing_queries[0].edges.push_back("2:8:s");
  EXPECT_NE(compiler::packing_desc_text(d, sp, 0).find("(2, 8, .squaringChain, false)"),
            std::string::npos);
  EXPECT_NE(compiler::packing_desc_text(d, sp, 0).find("(2, 8, .squaringChain, 0, 0)"),
            std::string::npos);
}

// Mask counts for both a non-prime mask subfield and the multi-stage odd
// field. A key that the registry does not recognize must not invent a kit.
TEST(GordieHowePlanExport, PackingMaskCounts) {
  const auto *binary = compiler::field_model("GF(2^256)");
  const auto *odd = compiler::field_model("F_q^20");
  ASSERT_NE(binary, nullptr);
  ASSERT_NE(odd, nullptr);
  EXPECT_EQ(compiler::field_mask_nums(*binary, 256, "16:4:m"),
            (std::pair<size_t, size_t>{64, 0}));
  EXPECT_EQ(compiler::field_mask_nums(*odd, 20, "1:4:m"),
            (std::pair<size_t, size_t>{80, 0}));
  EXPECT_EQ(compiler::field_mask_nums(*odd, 20, "4:5:m"),
            (std::pair<size_t, size_t>{100, 0}));
  EXPECT_EQ(compiler::field_mask_nums(*odd, 20, "bad-key"),
            (std::pair<size_t, size_t>{0, 0}));
}

// A proof module's path is guarded like the data modules': a rerun of the
// same export replaces its file, another configuration's export fails. A
// dotted leaf is a module below its group's.
TEST(GordieHowePlanExport, ProofModulePathsAreNotShared) {
  const std::filesystem::path dir =
      std::filesystem::temp_directory_path() /
      ("gh-plan-proofs-" + std::to_string(::getpid()));
  std::filesystem::remove_all(dir);
  const compiler::ExportMeta toy{"toy", "wide", "c0ffee", "run-0", 0};
  compiler::ProofModuleData d;
  d.meta = toy;
  compiler::ExportMeta other{"other", "wide", "c0ffee", "run-0", 0};
  other.lean_name = "Toy.QROMParams";
  compiler::ProofModuleData od = d;
  od.meta = other;
  const auto mods = compiler::proof_modules(d);
  const auto others = compiler::proof_modules(od);
  ASSERT_EQ(others.size(), mods.size());
  for (size_t i = 0; i < mods.size(); ++i) {
    const auto &mod = mods[i];
    const std::string path = compiler::lean_proof_file(dir.string(), toy, mod);
    std::string rel = mod.leaf;
    std::replace(rel.begin(), rel.end(), '.', '/');
    EXPECT_EQ(path, (dir / ("GordieHoweCerts/Generated/Toy/QROMParams/" + rel +
                            ".lean"))
                        .string());
    std::ofstream(path, std::ios::binary) << mod.text;
    EXPECT_EQ(compiler::lean_proof_file(dir.string(), toy, mod), path);
    EXPECT_THROW(compiler::lean_proof_file(dir.string(), other, others[i]),
                 std::runtime_error);
  }
  // A check module is below its source tree, the root at the program's path.
  const compiler::ProofModule leaf{"WellFormed", "# leaf", "",
                                   compiler::plan_proofs_internal::kKernelCheckRoot};
  EXPECT_EQ(compiler::lean_proof_file(dir.string(), toy, leaf),
            (dir / "Check/Kernel/GordieHoweCheck/Toy/QROMParams/WellFormed.lean").string());
  const compiler::ProofModule root{"", "# root", "",
                                   compiler::plan_proofs_internal::kNativeCheckRoot};
  EXPECT_EQ(compiler::lean_proof_file(dir.string(), toy, root),
            (dir / "Check/Native/GordieHoweCheck/Toy/QROMParams.lean").string());
  std::filesystem::remove_all(dir);
}

// A field-form assert_mod (m = p): its modField record names it and its
// field row, whose role is the realization of the mod; without the
// lowering's kField row record the export fails naming the mod.
TEST(GordieHowePlanExport, StructureModField) {
  static const Env *e = new Env;
  Sys cs{"gh-plan-export-modfield"};
  auto &A = cs.domain(e->a_profile(), "A");
  auto x = A.priv(Subfield{}, "x", 4);
  auto y = A.priv(Subfield{}, "y", 4);
  auto z = A.priv(Subfield{}, "z", 4);
  assert_mod(x + y, z, field_characteristic(e->af), "fm");
  const auto comp = compile(cs);
  const auto p = compiler::build_program(
      *comp, compiler::ExportMeta{"modfield", "wide", "c0ffee", "run-0", 0});
  size_t m = SIZE_MAX;
  for (size_t i = 0; i < p.predicates.size(); ++i)
    if (p.predicates[i].name == "fm") m = i;
  ASSERT_NE(m, SIZE_MAX);
  const compiler::StructureRecords r =
      compiler::build_structure(*comp, p, compiler::export_certificates(*comp));
  std::vector<const compiler::StructureRecords::Gadget *> fields;
  for (const auto &g : r.gadgets)
    if (g.kind == compiler::StructureRecords::GadgetKind::modField) fields.push_back(&g);
  ASSERT_EQ(fields.size(), 1u);
  ASSERT_EQ(fields[0]->preds.size(), 2u);
  EXPECT_EQ(fields[0]->preds[0], m);
  const size_t row = fields[0]->preds[1];
  ASSERT_LT(row, p.predicates.size());
  EXPECT_EQ(p.predicates[row].role, "realization");
  EXPECT_EQ(p.predicates[row].owner, m);
  EXPECT_NE(p.text.find("role := .realization " + std::to_string(m) + " }"), std::string::npos);
  // The proof modules' data records the field form (Completion's noFieldForm).
  EXPECT_TRUE(compiler::proof_module_data(
                  *comp, compiler::ExportMeta{"modfield", "wide", "c0ffee", "run-0", 0}, p)
                  .field_form);
  const std::string o = compiler::print_structure(r);
  EXPECT_NE(o.find("{ kind := .modField, preds := [" + std::to_string(m) + ", " +
                   std::to_string(row) + "], values := [], params := [], parts := [] }"),
            std::string::npos)
      << o;
  // The lowering's records without the kField row.
  std::vector<PlanRecords::ModRow> rows = comp->records().mod_rows;
  rows.erase(std::remove_if(rows.begin(), rows.end(),
                            [](const PlanRecords::ModRow &w) {
                              return w.kind == PlanRecords::ModRow::kField;
                            }),
             rows.end());
  compiler::StructureRecords out;
  try {
    compiler::structure_records_internal::mod_fields(comp->program(), rows, out);
    ADD_FAILURE() << "a field-form mod_q without its row exported";
  } catch (const std::runtime_error &err) {
    EXPECT_NE(std::string(err.what()).find("'fm'"), std::string::npos) << err.what();
  }
}

// The interval sources (Lean `IvlSource`, as the old `leafIvl` picks
// them): a constant its entries, a value with a range request of the
// lookup table's size (looked up directly) that range, a statement value with a
// declared bound its entry of the declared bounds, a bound value (a range
// request over digits) the in on it.
struct IvlToy {
  std::unique_ptr<Sys> cs;
  std::unique_ptr<Sys::Compiled> c;
};
IvlToy ivl_toy(Bound declared) {
  static const Env *e = new Env;
  auto sys = std::make_unique<Sys>("gh-plan-export-ivl");
  Sys &cs = *sys;
  auto &A = cs.domain(e->a_profile(), "A");
  auto st = A.pub_bytes("st", 4);
  auto h = A.pub(Subfield{}, "h", 2, depends_on(st), computes("first_two"),
                 [](const std::vector<uint8_t> &b) {
                   return std::vector<uint64_t>{b.at(0), b.at(1)};
                 })
               .cache()
               .bounded(declared);
  auto y = A.priv(Subfield{}, "y", 2);
  assert_equal(y, h, "y = h");
  auto x = A.priv(Subfield{}, "x", 4);
  assert_range(x, 100, "x");
  auto v = A.priv(Subfield{}, "v", 4);
  assert_range(v, 3000, MaxBound{Bound(1) << 22}, "v");
  auto w = A.priv(Subfield{}, "w", 4);
  assert_range(w, 8, "w");
  auto w2 = A.priv(Subfield{}, "w2", 4);
  assert_range(w2, 10, "w2");
  auto c = compile(cs);
  return IvlToy{std::move(sys), std::move(c)};
}

TEST(GordieHowePlanExport, StructureIvlSources) {
  const IvlToy t = ivl_toy(50);
  const auto p = compiler::build_program(
      *t.c, compiler::ExportMeta{"ivl", "wide", "c0ffee", "run-0", 0});
  const compiler::StructureRecords r =
      compiler::build_structure(*t.c, p, compiler::export_certificates(*t.c));
  const auto ivls = ivl_text(r);
  std::map<size_t, std::string> src(ivls.begin(), ivls.end());
  auto value = [&](const std::string &nm) {
    for (size_t i = 0; i < p.values.size(); ++i)
      if (p.values[i].name == nm) return i;
    ADD_FAILURE() << "no value " << nm;
    return SIZE_MAX;
  };
  auto pred = [&](const std::string &nm) {
    for (size_t i = 0; i < p.predicates.size(); ++i)
      if (p.predicates[i].name == nm) return i;
    ADD_FAILURE() << "no predicate " << nm;
    return SIZE_MAX;
  };
  if (std::getenv("GH_PRINT_GOLDEN") != nullptr) {
    for (const auto &[v, s] : ivl_text(r))
      std::printf("ivl %zu %s %s: %s\n", v, p.values[v].name.c_str(),
                  p.values[v].kind.c_str(), s.c_str());
    for (size_t i = 0; i < p.predicates.size(); ++i)
      std::printf("pred %zu %s: %s\n", i, p.predicates[i].name.c_str(),
                  p.predicates[i].body.c_str());
  }
  EXPECT_EQ(src[value("h")], ".declared 0");
  EXPECT_EQ(src[value("w2")], ".range " + std::to_string(pred("w2")));
  size_t consts = 0, bounds = 0;
  for (size_t i = 0; i < p.values.size(); ++i) {
    if (p.values[i].kind == "constant") {
      ++consts;
      EXPECT_EQ(src[i], ".const") << p.values[i].name;
    }
    if (p.values[i].kind == "bound") {
      ++bounds;
      // The first in on the bound value or on it plus a constant.
      size_t q = SIZE_MAX;
      const std::string leaf = "[.leaf " + std::to_string(i) + "]";
      const std::string plus = "[.add (.leaf " + std::to_string(i) + ") (.leaf ";
      for (size_t k = 0; k < p.predicates.size() && q == SIZE_MAX; ++k)
        if (p.predicates[k].body.rfind(".mem ", 0) == 0 &&
            (p.predicates[k].body.find(leaf) != std::string::npos ||
             p.predicates[k].body.find(plus) != std::string::npos))
          q = k;
      EXPECT_EQ(src[i], ".shiftRange " + std::to_string(q)) << p.values[i].name;
    }
  }
  EXPECT_GT(consts, 0u);
  EXPECT_GT(bounds, 0u);
  // The printed entries.
  const std::string o = compiler::print_structure(r);
  EXPECT_NE(o.find("(" + std::to_string(value("h")) + ", .declared 0)"), std::string::npos) << o;
  const std::string range =
      "(" + std::to_string(value("w2")) + ", .range " + std::to_string(pred("w2")) + ")";
  EXPECT_NE(o.find(range), std::string::npos) << o;
}

// The export check (decision D1): a declared statement bound wider than a
// range on the same value would widen the interval the honest checks read,
// and the export fails naming the value; one within it exports. A program
// cannot state a range on a statement value (a constraint reads a
// committed value), so the test adds one to the toy's program: a direct
// lookup of h below 100, the in of w2 read at h.
TEST(GordieHowePlanExport, StructureIvlDeclaredWiderFails) {
  for (const Bound declared : {Bound(1000), Bound(50)}) {
    const IvlToy t = ivl_toy(declared);
    ir::Program P = t.c->program();
    size_t h = SIZE_MAX, w = SIZE_MAX;
    for (size_t i = 0; i < P.values.size(); ++i)
      if (P.values[i].name == "h") h = i;
    for (size_t i = 0; i < P.predicates.size(); ++i)
      if (P.predicates[i].name == "w2") w = i;
    ASSERT_NE(h, SIZE_MAX);
    ASSERT_NE(w, SIZE_MAX);
    ir::Expr leaf;
    leaf.op = ir::Expr::kLeaf;
    leaf.x = h;
    leaf.n = P.values[h].size();
    P.nodes.push_back(leaf);
    ir::Predicate q = P.predicates[w];
    q.name = "hr";
    q.lhs = ir::Id(P.nodes.size() - 1);
    q.range = "100";
    q.in.lookup.kind = ir::LookupKind::kDirect;
    P.predicates.push_back(q);
    compiler::StructureRecords out;
    compiler::structure_records_internal::ivl::Mirror m(P);
    if (declared == 50) {
      EXPECT_NO_THROW(m.fill(out));
      continue;
    }
    try {
      m.fill(out);
      ADD_FAILURE() << "a declared bound wider than a range exported";
    } catch (const std::runtime_error &err) {
      const std::string msg = err.what();
      EXPECT_NE(msg.find("'h' (" + std::to_string(h) + ")"), std::string::npos) << msg;
      EXPECT_NE(msg.find("[0, 999]"), std::string::npos) << msg;
      EXPECT_NE(msg.find("[0, 99]"), std::string::npos) << msg;
    }
  }
}

// The placement records (Structure.routes, logupHosts, macHosts,
// chalValues) of program P against the program itself: every route points
// where it says, exactly the predicates that need a route have one, every
// table group and every MAC whose H half no domain checks has a host, and
// each challenge's value is the least holding it.
void check_placement(const ir::Program &P, const compiler::StructureRecords &r) {
  const auto texts = route_text(r);
  std::map<size_t, std::string> routes(texts.begin(), texts.end());
  EXPECT_EQ(routes.size(), r.routes.size());
  size_t needs = 0;
  for (size_t pid = 0; pid < P.predicates.size(); ++pid) {
    const ir::Predicate &q = P.predicates[pid];
    const bool product = q.body == ir::Predicate::kMod &&
                         (q.mod.form == ir::ModForm::kProduct ||
                          q.mod.form == ir::ModForm::kSpectralProduct);
    const bool need = q.body == ir::Predicate::kEqual ||
                      (q.body == ir::Predicate::kMod && q.q == "0") || product;
    auto it = routes.find(pid);
    ASSERT_EQ(need, it != routes.end()) << q.name;
    if (!need) continue;
    ++needs;
    const ir::Target *t = q.body == ir::Predicate::kEqual ? &q.target
                          : q.mod.target                  ? &*q.mod.target
                                                          : nullptr;
    std::istringstream in(it->second);
    std::string kind;
    in >> kind;
    if (kind == ".batch") {
      size_t b = 0, j = 0;
      in >> b >> j;
      ASSERT_NE(t, nullptr);
      EXPECT_EQ(t->kind, ir::Target::kBatch);
      EXPECT_EQ(b, t->id);
      ASSERT_LT(b, P.batches.size());
      ASSERT_LT(j, P.batches[b].parts.size());
      EXPECT_EQ(P.batches[b].parts[j], pid);
    } else if (kind == ".gkr") {
      size_t c = 0, k = 0;
      in >> c >> k;
      if (t != nullptr) {
        EXPECT_EQ(t->kind, ir::Target::kGkr);
        EXPECT_EQ(c, t->id);
      }
      ASSERT_LT(c, P.circuits.size());
      ASSERT_LT(k, P.circuits[c].entries.size());
      const ir::CircuitEntry &e = P.circuits[c].entries[k];
      EXPECT_TRUE(e.kind == ir::CircuitEntry::kPred || e.kind == ir::CircuitEntry::kTypeCheck);
      EXPECT_EQ(e.id, pid);
    } else if (kind == ".affine") {
      std::string views;
      in >> views;
      ASSERT_NE(t, nullptr);
      EXPECT_EQ(t->kind, ir::Target::kAffine);
      EXPECT_EQ(views == "true",
                compiler::structure_records_internal::place::reads_bits(P, {q.lhs, q.rhs}));
    } else if (kind == ".quadratic") {
      ASSERT_NE(t, nullptr);
      EXPECT_EQ(t->kind, ir::Target::kQuadratic);
    } else if (kind == ".realized") {
      size_t rq = 0;
      in >> rq;
      ASSERT_NE(t, nullptr);
      EXPECT_EQ(t->kind, ir::Target::kRealized);
      EXPECT_EQ(rq, t->id);
    } else {
      ADD_FAILURE() << "route " << it->second;
    }
  }
  EXPECT_EQ(needs, r.routes.size());
  // Every group, in order, hosted by an entry realizing its LogUp identity.
  std::vector<std::pair<size_t, size_t>> keys;
  for (size_t t = 0; t < P.tables.size(); ++t)
    for (size_t g = 0; g < P.tables[t].groups.size(); ++g) keys.push_back({t, g});
  ASSERT_EQ(r.logup_hosts.size(), keys.size());
  for (size_t i = 0; i < keys.size(); ++i) {
    EXPECT_EQ(r.logup_hosts[i].first, keys[i]);
    const auto [c, k] = r.logup_hosts[i].second;
    ASSERT_LT(c, P.circuits.size());
    EXPECT_LT(P.circuits[c].domain, P.domains.size());
    ASSERT_LT(k, P.circuits[c].entries.size());
    const ir::CircuitEntry &e = P.circuits[c].entries[k];
    EXPECT_EQ(e.kind, ir::CircuitEntry::kRealization);
    EXPECT_EQ(e.real.kind, ir::RealRef::kLogup);
    EXPECT_EQ(e.real.a, keys[i].first);
    EXPECT_EQ(e.real.b, keys[i].second);
  }
  // The MACs whose H half a circuit hosts, each at its entry.
  std::map<size_t, std::pair<size_t, size_t>> mac(r.mac_hosts.begin(), r.mac_hosts.end());
  for (size_t pid = 0; pid < P.predicates.size(); ++pid) {
    const ir::Predicate &q = P.predicates[pid];
    const bool need = q.body == ir::Predicate::kCross && q.mac.h_predicate == ir::kNone &&
                      q.mac.blind_x == ir::kNone;
    auto it = mac.find(pid);
    ASSERT_EQ(need, it != mac.end()) << q.name;
    if (!need) continue;
    const auto [c, k] = it->second;
    ASSERT_LT(c, P.circuits.size());
    ASSERT_LT(k, P.circuits[c].entries.size());
    const ir::CircuitEntry &e = P.circuits[c].entries[k];
    EXPECT_EQ(e.kind, ir::CircuitEntry::kRealization);
    EXPECT_EQ(e.real.kind, ir::RealRef::kMacH);
    EXPECT_EQ(e.real.a, pid);
  }
  // Each challenge's least value.
  std::map<size_t, size_t> chal(r.chal_values.begin(), r.chal_values.end());
  for (size_t v = 0; v < P.values.size(); ++v) {
    if (P.values[v].kind != ir::Value::kChallenge) continue;
    auto it = chal.find(P.values[v].ref);
    ASSERT_NE(it, chal.end());
    EXPECT_LE(it->second, v);
  }
  for (const auto &[j, v] : r.chal_values) {
    ASSERT_LT(v, P.values.size());
    EXPECT_EQ(P.values[v].kind, ir::Value::kChallenge);
    EXPECT_EQ(P.values[v].ref, j);
  }
}

TEST(GordieHowePlanExport, StructurePlacement) {
  const Toy t = toy_system();
  const auto p = compiler::build_program(
      *t.c, compiler::ExportMeta{"toy", "wide", "c0ffee", "run-0", 0});
  const compiler::StructureRecords r =
      compiler::build_structure(*t.c, p, compiler::export_certificates(*t.c));
  const ir::Program &P = t.c->program();
  check_placement(P, r);
  // The toy has a range lookup, a MAC and a challenge.
  EXPECT_FALSE(r.routes.empty());
  EXPECT_FALSE(r.logup_hosts.empty());
  EXPECT_FALSE(r.chal_values.empty());
  if (std::getenv("GH_PRINT_GOLDEN") != nullptr) {
    for (const auto &[pid, s] : route_text(r))
      std::printf("route %zu %s: %s\n", pid, P.predicates[pid].name.c_str(), s.c_str());
  }
  const std::string o = compiler::print_structure(r);
  ASSERT_FALSE(r.routes.empty());
  EXPECT_NE(o.find("  routes := [(" + std::to_string(r.routes[0].first) + ", " +
                   compiler::structure_records_internal::route(r.routes[0].second) + ")"),
            std::string::npos)
      << o;
  // The other structure tests' programs.
  {
    const IvlToy u = ivl_toy(50);
    const auto pu = compiler::build_program(
        *u.c, compiler::ExportMeta{"ivl", "wide", "c0ffee", "run-0", 0});
    check_placement(u.c->program(),
                    compiler::build_structure(*u.c, pu, compiler::export_certificates(*u.c)));
  }
  // A predicate whose target batch lacks it fails the export.
  ir::Program Q = P;
  size_t moved = SIZE_MAX;
  for (size_t pid = 0; pid < Q.predicates.size() && moved == SIZE_MAX; ++pid)
    if (Q.predicates[pid].body == ir::Predicate::kEqual &&
        Q.predicates[pid].target.kind == ir::Target::kBatch)
      moved = pid;
  if (moved != SIZE_MAX) {
    auto &parts = Q.batches.at(Q.predicates[moved].target.id).parts;
    parts.erase(std::remove(parts.begin(), parts.end(), ir::Id(moved)), parts.end());
    compiler::StructureRecords out;
    EXPECT_THROW(compiler::structure_records_internal::place::routes(Q, out),
                 std::runtime_error);
  }
}

// A hand-built program for the placement records: shared entries 0-3 (each
// a leaf of value 0), conversions 0 (source 0, read 1) and 1 (source 2,
// read 3), predicate 0 a field equal realized by predicate 1.
ir::Program placement_program() {
  ir::Program P;
  P.domains.push_back({"A", 0});
  ir::Value v;
  v.name = "x";
  P.values.push_back(v);
  ir::Expr leaf;
  leaf.op = ir::Expr::kLeaf;
  leaf.x = 0;
  leaf.n = 1;
  for (size_t k = 0; k < 4; ++k) {
    P.nodes.push_back(leaf);
    P.exprs.push_back(ir::Id(P.nodes.size() - 1));
  }
  P.convs.push_back({0, 1, 0, 1, 1, 1, 1, "1"});
  P.convs.push_back({2, 3, 0, 1, 1, 1, 1, "1"});
  ir::Predicate q;
  q.name = "src";
  q.body = ir::Predicate::kEqual;
  q.target.kind = ir::Target::kRealized;
  q.target.id = 1;
  P.predicates.push_back(q);
  q.name = "src.realized";
  q.target.kind = ir::Target::kAffine;
  q.target.id = ir::kNone;
  P.predicates.push_back(q);
  return P;
}

ir::Id add_node(ir::Program &P, ir::Expr::Op op, uint64_t x, ir::Id a = ir::kNone,
                ir::Id b = ir::kNone) {
  ir::Expr e;
  e.op = op;
  e.x = x;
  e.a = a;
  e.b = b;
  e.n = 1;
  P.nodes.push_back(e);
  return ir::Id(P.nodes.size() - 1);
}

// The conversions a realized predicate reads, in Lean's `Expr.matchB`
// order: the left sides first, then the right, pre-order, a before b;
// equal shared entries and identical subexpressions consume none; equal
// parameters at distinct ids (a coefficient) match.
TEST(GordieHowePlanExport, StructureRealizedMismatchOrder) {
  using ir::Expr;
  ir::Program P = placement_program();
  P.coefs.push_back({true, "3", ir::kNone, 0});
  P.coefs.push_back({true, "3", ir::kNone, 0});
  const ir::Id leaf = add_node(P, Expr::kLeaf, 0);
  // lhs: (ref 2 + 3 · ref 0) - x, against (ref 3 + 3 · ref 1) - x.
  const ir::Id l = add_node(
      P, Expr::kSub,
      0, add_node(P, Expr::kAdd, 0, add_node(P, Expr::kRef, 2),
                  add_node(P, Expr::kScale, 0, add_node(P, Expr::kRef, 0))),
      leaf);
  const ir::Id lr = add_node(
      P, Expr::kSub,
      0, add_node(P, Expr::kAdd, 0, add_node(P, Expr::kRef, 3),
                  add_node(P, Expr::kScale, 1, add_node(P, Expr::kRef, 1))),
      leaf);
  // rhs: ref 0 · ref 2 against ref 1 · ref 2.
  const ir::Id r = add_node(P, Expr::kMul, 0, add_node(P, Expr::kRef, 0),
                            add_node(P, Expr::kRef, 2));
  const ir::Id rr = add_node(P, Expr::kMul, 0, add_node(P, Expr::kRef, 1),
                             add_node(P, Expr::kRef, 2));
  P.predicates[0].lhs = l;
  P.predicates[0].rhs = r;
  P.predicates[1].lhs = lr;
  P.predicates[1].rhs = rr;
  {
    compiler::StructureRecords out;
    compiler::structure_records_internal::place::routes(P, out);
    ASSERT_EQ(out.routes.size(), 2u);
    EXPECT_EQ(route_text(out)[0], (std::pair<size_t, std::string>{0, ".realized 1 [1, 0, 0]"}));
    EXPECT_EQ(route_text(out)[1], (std::pair<size_t, std::string>{1, ".affine false"}));
  }
  // No conversions: the realized predicate's own sides.
  {
    ir::Program Q = P;
    Q.predicates[0].lhs = lr;
    Q.predicates[0].rhs = rr;
    compiler::StructureRecords out;
    compiler::structure_records_internal::place::routes(Q, out);
    EXPECT_EQ(route_text(out).at(0).second, ".realized 1 []");
  }
  // A difference other than at shared entries: another leaf.
  {
    ir::Program Q = P;
    Q.values.push_back(Q.values[0]);
    const ir::Id other = add_node(Q, Expr::kLeaf, 1);
    Q.nodes[lr].b = other;
    compiler::StructureRecords out;
    EXPECT_THROW(compiler::structure_records_internal::place::routes(Q, out),
                 std::runtime_error);
  }
  // A different coefficient.
  {
    ir::Program Q = P;
    Q.coefs[1].c = "4";
    compiler::StructureRecords out;
    EXPECT_THROW(compiler::structure_records_internal::place::routes(Q, out),
                 std::runtime_error);
  }
  // A shared-entry pair no conversion pairs (the reading as the source).
  {
    ir::Program Q = P;
    std::swap(Q.convs[0].source, Q.convs[0].read);
    compiler::StructureRecords out;
    EXPECT_THROW(compiler::structure_records_internal::place::routes(Q, out),
                 std::runtime_error);
  }
}

// The other routes and the hosts on the hand-built program: a batch part,
// a circuit entry, a row on bit views; rejections: a predicate its target
// batch lacks, a group with no host, a MAC with no H host.
TEST(GordieHowePlanExport, StructureUnknownTargetRejects) {
  ir::Program P = placement_program();
  P.predicates.resize(1);
  P.predicates[0].target.kind = static_cast<ir::Target::Kind>(255);
  compiler::StructureRecords out;
  EXPECT_THROW(compiler::structure_records_internal::place::routes(P, out),
               std::runtime_error);
  EXPECT_TRUE(out.routes.empty());
}

TEST(GordieHowePlanExport, StructurePlacementRejects) {
  using ir::Expr;
  ir::Program P = placement_program();
  P.predicates.resize(1);
  P.predicates[0].target.kind = ir::Target::kBatch;
  P.predicates[0].target.id = 0;
  P.predicates[0].lhs = P.exprs[0];
  P.predicates[0].rhs = P.exprs[1];
  ir::Batch b;
  b.parts = {7, 0};
  P.batches.push_back(b);
  ir::Predicate g = P.predicates[0];
  g.target.kind = ir::Target::kGkr;
  P.predicates.push_back(g);
  ir::Predicate a = P.predicates[0];
  a.target.kind = ir::Target::kAffine;
  ir::Value bits;
  bits.kind = ir::Value::kBits;
  P.values.push_back(bits);
  a.rhs = add_node(P, Expr::kRef, 4);
  P.exprs.push_back(add_node(P, Expr::kLeaf, 1));
  P.predicates.push_back(a);
  ir::Circuit c;
  ir::CircuitEntry e;
  e.kind = ir::CircuitEntry::kPred;
  e.id = 0;
  c.entries.push_back(e);
  e.id = 1;
  c.entries.push_back(e);
  ir::CircuitEntry h;
  h.kind = ir::CircuitEntry::kRealization;
  h.real.kind = ir::RealRef::kLogup;
  c.entries.push_back(h);
  P.circuits.push_back(c);
  ir::Table t;
  t.groups.resize(1);
  P.tables.push_back(t);
  compiler::StructureRecords out;
  compiler::structure_records_internal::place::routes(P, out);
  compiler::structure_records_internal::place::hosts(P, out);
  EXPECT_EQ(route_text(out), (std::vector<std::pair<size_t, std::string>>{
                            {0, ".batch 0 1"}, {1, ".gkr 0 1"}, {2, ".affine true"}}));
  EXPECT_EQ(out.logup_hosts.size(), 1u);
  EXPECT_EQ(out.logup_hosts.at(0).second, (std::pair<size_t, size_t>{0, 2}));
  EXPECT_TRUE(out.mac_hosts.empty());
  auto rejects = [](const ir::Program &Q, bool route) {
    compiler::StructureRecords o;
    if (route)
      EXPECT_THROW(compiler::structure_records_internal::place::routes(Q, o),
                   std::runtime_error);
    else
      EXPECT_THROW(compiler::structure_records_internal::place::hosts(Q, o),
                   std::runtime_error);
  };
  {
    ir::Program Q = P;
    Q.batches[0].parts = {7};
    rejects(Q, true);
  }
  {
    ir::Program Q = P;
    Q.circuits[0].entries[1].id = 5;
    rejects(Q, true);
  }
  {
    ir::Program Q = P;
    Q.tables[0].groups.resize(2);
    rejects(Q, false);
  }
  {
    ir::Program Q = P;
    ir::Predicate x;
    x.name = "mac";
    x.body = ir::Predicate::kCross;
    Q.predicates.push_back(x);
    rejects(Q, false);
    ir::CircuitEntry m;
    m.kind = ir::CircuitEntry::kRealization;
    m.real.kind = ir::RealRef::kMacH;
    m.real.a = ir::Id(Q.predicates.size() - 1);
    Q.circuits[0].entries.push_back(m);
    compiler::StructureRecords o;
    compiler::structure_records_internal::place::hosts(Q, o);
    EXPECT_EQ(o.mac_hosts, (std::vector<std::pair<size_t, std::pair<size_t, size_t>>>{
                               {Q.predicates.size() - 1, {0, 3}}}));
  }
}

}  // namespace
}  // namespace proofs::gordiehowe

TEST(GordieHoweDerivsExport, ExplicitLiteralProfile) {
  using namespace proofs::gordiehowe;
  const compiler::ExportMeta meta{"toy", "wide", "EXPORTER_COMMIT", "exports", 0};
  ir::Program p;
  ir::Certificates c;
  const std::string text = compiler::print_derivations_module(p, c, meta, "0123456789abcdef");
  EXPECT_NE(text.find("load_program_ghc \"Derivs.ghc\" \"0123456789abcdef\""), std::string::npos);
  EXPECT_NE(text.find("public import GordieHowe.Language.Realizations.Circuit.LoadNative"),
            std::string::npos);
  EXPECT_NE(text.find("meta import GordieHowe.Language.Realizations.Circuit.LoadNative"),
            std::string::npos);
  EXPECT_EQ(text.find("def derivs :"), std::string::npos);
  EXPECT_EQ(text.find("def ranks :"), std::string::npos);
  EXPECT_EQ(text.find("def shared :"), std::string::npos);
  EXPECT_NE(text.find("def derivations : Derivations := { derivs := derivs, ranks := ranks, shared := shared }"),
            std::string::npos);
}
