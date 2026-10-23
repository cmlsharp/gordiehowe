// Copyright 2026 Chad Sharp and Paul Grubbs
// SPDX-License-Identifier: Apache-2.0

// User-defined linear operators (custom_ops.h): the Walsh-Hadamard
// transform in its sparse and dense forms, and the cyclic convolution by
// a public kernel. Honest transforms verify; a wrong output, a changed
// input and a tampered square are rejected.

#include "gordiehowe/heldout/custom_ops.h"

#include <string>
#include <utility>
#include <vector>

#include "gordiehowe/heldout/heldout_testing.h"
#include "gtest/gtest.h"

namespace proofs::gordiehowe::heldout::custom_ops {
namespace {

void check_hadamard(bool sparse) {
  const auto rel = hadamard(sparse);
  const HadamardInstance in = hadamard_instance(23);
  HadamardStatement<Value> s = in.statement;
  fields().gf.add(s.y[9], fields().gf.one());
  HadamardWitness<Value> w = in.witness;
  w.x[0] += 1;
  const std::string config = sparse ? "hadamard-sparse" : "hadamard-dense";
  check_relation<GoldSys>(
      rel,
      Case<HadamardStatement<Value>, HadamardWitness<Value>>{in.statement,
                                                             in.witness},
      {{"x", w}}, {{"y", s}}, config);
  if (!sparse) return;
  const auto &typed = rel.typed<GoldSys>();
  const auto &c = typed.compiled();
  EXPECT_FALSE(proves(c, typed.statement(in.statement),
                      typed.witness(in.witness),
                      bump<GoldSys::Set>(fields().gf,
                                         node_named(c, "squares.value"), 4)));
}

TEST(HeldoutCustomOps, HadamardSparse) { check_hadamard(true); }
TEST(HeldoutCustomOps, HadamardDense) { check_hadamard(false); }

TEST(HeldoutCustomOps, CyclicConv) {
  const auto rel = cyclic_conv();
  const ConvInstance in = conv_instance(29);
  ConvStatement<Value> s = in.statement;
  fields().gf.add(s.y[1], fields().gf.one());
  ConvStatement<Value> k = in.statement;
  k.kernel[0] ^= 1;
  ConvWitness<Value> w = in.witness;
  w.x[15] ^= 2;
  check_relation<GoldSys>(
      rel, Case<ConvStatement<Value>, ConvWitness<Value>>{in.statement,
                                                          in.witness},
      {{"x", w}}, {{"y", s}, {"kernel", k}}, "cyclic-conv", false);
  // The operator's matrix reads the kernel: the export states it by its
  // rows over the kernel's coordinates (`.linear` with `Coef.node`).
  const auto &c = rel.typed<GoldSys>().compiled();
  const auto p = program_of(c, "cyclic-conv");
  EXPECT_NE(p.text.find(".linear [[(0, .node "), std::string::npos) << p.text;
}

}  // namespace
}  // namespace proofs::gordiehowe::heldout::custom_ops
