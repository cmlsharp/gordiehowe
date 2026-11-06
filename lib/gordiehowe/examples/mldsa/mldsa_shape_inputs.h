// Copyright 2026 Chad Sharp and Paul Grubbs
// SPDX-License-Identifier: Apache-2.0

// Named frontend inputs for the ML-DSA-44 formal relations. Shared expressions
// are selected by semantic application roots and explicit operand paths.
#ifndef PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_EXAMPLES_MLDSA_MLDSA_SHAPE_INPUTS_H_
#define PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_EXAMPLES_MLDSA_MLDSA_SHAPE_INPUTS_H_

#include "gordiehowe/system.h"

namespace proofs::gordiehowe::examples::mldsa {

// The part of the native program at the same parameters that an emulated
// program holds: every native value one identifier larger and every native shared
// expression two larger, domain `H`'s values and expressions, and native predicate
// `k` of domain `H` at `k + 2`. The compiled programs check these lists against
// both tables (ShapeClaim.embedding).
inline ProgramEmbeddingDecl mldsa_emulated_native_embedding() {
  constexpr size_t kValueIds = 600, kExprIds = 530, kChallenges = 4;
  ProgramEmbeddingDecl d;
  d.name = "native.H";
  d.source_config = "mldsa-native";
  for (size_t v = 0; v < kValueIds; ++v) d.vals.push_back(v + 1);
  for (size_t k = 0; k < kExprIds; ++k) d.refs.push_back(k + 2);
  for (size_t j = 0; j < kChallenges; ++j) d.chals.push_back(j);
  d.values.push_back(6);
  for (size_t v = 8; v < 55; ++v) d.values.push_back(v);
  for (size_t v = 66; v < 567; ++v) d.values.push_back(v);
  for (size_t k = 11; k < 526; ++k) d.exprs.push_back(k);
  for (size_t k = 18; k <= 270; ++k) d.equals.emplace_back(k, k + 2);
  return d;
}

// The Keccak rounds of the native program's SHAKE calls, one family row per
// round: the round relation, its linear part and that part's column parities,
// and the round's output view. `μ`'s absorb is `h2c.mu.blocks`, `c̃'`'s absorbs
// `h2c.c_tilde`, SampleInBall's stream `h2c.sib`.
inline ShapeFamilyInput mldsa_keccak_rounds(const Scope &s) {
  using Root = ShapeExprSelector::Root;
  using Edge = ShapeExprSelector::Edge;
  ShapeFamilyInput f;
  f.name = "keccak_rounds";
  auto round = [&](const std::string &pred) {
    s.shape_expr(pred + ".shape.linear",
        {Root::kPredicateLeft, pred, {{Edge::kSecond}, {Edge::kFirst}, {Edge::kFirst}}});
    s.shape_expr(pred + ".shape.columns",
        {Root::kPredicateLeft, pred,
         {{Edge::kSecond}, {Edge::kFirst}, {Edge::kFirst}, {Edge::kShared}, {Edge::kFirst},
          {Edge::kFirst}, {Edge::kSecond}, {Edge::kFirst}, {Edge::kFirst}}});
    s.shape_value(pred + ".shape.output", {Root::kPredicateLeft, pred, {{Edge::kFirst}}});
    f.rows.push_back({{pred}, {pred + ".shape.linear", pred + ".shape.columns"},
                      {pred + ".shape.output"}});
  };
  // The absorbed blocks of `c̃'`'s later permutations: the input of each one's
  // first round.
  for (size_t p = 2; p <= 7; ++p) {
    const std::string pred = "h2c.c_tilde.r" + std::to_string(24 * (p - 1));
    s.shape_expr(pred + ".shape.absorbed",
        {Root::kPredicateLeft, pred,
         {{Edge::kSecond}, {Edge::kFirst}, {Edge::kFirst}, {Edge::kShared}, {Edge::kFirst},
          {Edge::kFirst}, {Edge::kFirst}}});
  }
  for (size_t r = 0; r < 24; ++r) round("h2c.mu.blocks.r" + std::to_string(r));
  for (size_t r = 0; r < 168; ++r) round("h2c.c_tilde.r" + std::to_string(r));
  for (size_t r = 0; r < 48; ++r) round("h2c.sib.r" + std::to_string(r));
  return f;
}

inline NamedShapeInputs mldsa_native_shape_inputs(const Scope &s) {
  using Root = ShapeExprSelector::Root;
  using Edge = ShapeExprSelector::Edge;
  // Completion witnesses remain checked value metadata, not source roles.
  s.shape_value("z.digit.low",
      {Root::kValueDefinition, "z",
       {{Edge::kFirst}, {Edge::kFirst}}});
  s.shape_value("z.digit.high",
      {Root::kValueDefinition, "z",
       {{Edge::kFirst}, {Edge::kSecond}, {Edge::kFirst}}});
  s.shape_value("z.completion.low",
      {Root::kPredicateLeft, "range.norm.z.top",
       {{Edge::kFirst}, {Edge::kSecond}, {Edge::kFirst}}});
  s.shape_value("z.completion.high",
      {Root::kPredicateLeft, "range.norm.z.top",
       {{Edge::kSecond}, {Edge::kFirst}}});
  s.shape_value("hint.offset.digit.low",
      {Root::kValueDefinition, "hint.offset",
       {{Edge::kFirst}}});
  s.shape_value("hint.offset.digit.high",
      {Root::kValueDefinition, "hint.offset",
       {{Edge::kSecond}, {Edge::kFirst}}});
  s.shape_value("hint.slack.digit.low",
      {Root::kValueDefinition, "hint.slack",
       {{Edge::kFirst}}});
  s.shape_value("hint.slack.digit.high",
      {Root::kValueDefinition, "hint.slack",
       {{Edge::kSecond}, {Edge::kFirst}}});

  s.shape_expr("signature.relation.shape.left.first.second.first.first",
      {Root::kPredicateLeft, "signature.relation",
       {{Edge::kFirst}, {Edge::kSecond}, {Edge::kFirst}, {Edge::kFirst}}});
  s.shape_expr("signature.relation.shape.left.second.first.first",
      {Root::kPredicateLeft, "signature.relation",
       {{Edge::kSecond}, {Edge::kFirst}, {Edge::kFirst}}});
  s.shape_expr("hint.interval.shape.right.first.shared.second.shared.first",
      {Root::kPredicateRight, "hint.interval",
       {{Edge::kFirst}, {Edge::kShared}, {Edge::kSecond}, {Edge::kShared}, {Edge::kFirst}}});
  s.shape_expr("hint.decompose.shape.left.first.first.second.first.first.first.first.second.first",
      {Root::kPredicateLeft, "hint.decompose",
       {{Edge::kFirst}, {Edge::kFirst}, {Edge::kSecond}, {Edge::kFirst}, {Edge::kFirst}, {Edge::kFirst}, {Edge::kFirst}, {Edge::kSecond}, {Edge::kFirst}}});
  s.shape_expr("hint.interval.shape.right.first.shared.first.second",
      {Root::kPredicateRight, "hint.interval",
       {{Edge::kFirst}, {Edge::kShared}, {Edge::kFirst}, {Edge::kSecond}}});
  s.shape_expr("hint.interval.shape.right.first.shared.second",
      {Root::kPredicateRight, "hint.interval",
       {{Edge::kFirst}, {Edge::kShared}, {Edge::kSecond}}});
  s.shape_expr("hint.interval.shape.right.first",
      {Root::kPredicateRight, "hint.interval",
       {{Edge::kFirst}}});
  s.shape_expr("mac.equal.shape.right",
      {Root::kPredicateRight, "mac.equal",
       {}});
  s.shape_expr("h2c.mu.padding.suffix.shape.left.second.first.shared.first.first.first.first",
      {Root::kPredicateLeft, "h2c.mu.padding.suffix",
       {{Edge::kSecond}, {Edge::kFirst}, {Edge::kShared}, {Edge::kFirst}, {Edge::kFirst}, {Edge::kFirst}, {Edge::kFirst}}});
  s.shape_expr("h2c.mu.blocks.r0.shape.left.second.first.first.shared.first.first.first",
      {Root::kPredicateLeft, "h2c.mu.blocks.r0",
       {{Edge::kSecond}, {Edge::kFirst}, {Edge::kFirst}, {Edge::kShared}, {Edge::kFirst}, {Edge::kFirst}, {Edge::kFirst}}});
  s.shape_expr("h2c.mu.padding.suffix.shape.left.first.first",
      {Root::kPredicateLeft, "h2c.mu.padding.suffix",
       {{Edge::kFirst}, {Edge::kFirst}}});
  s.shape_expr("h2c.mu.padding.suffix.shape.left.second.first",
      {Root::kPredicateLeft, "h2c.mu.padding.suffix",
       {{Edge::kSecond}, {Edge::kFirst}}});
  s.shape_expr("h2c.mu.padding.output.shape.left.first.first.shared.first.first",
      {Root::kPredicateLeft, "h2c.mu.padding.output",
       {{Edge::kFirst}, {Edge::kFirst}, {Edge::kShared}, {Edge::kFirst}, {Edge::kFirst}}});
  s.shape_expr("h2c.mu.padding.output.shape.left.first.first",
      {Root::kPredicateLeft, "h2c.mu.padding.output",
       {{Edge::kFirst}, {Edge::kFirst}}});
  s.shape_expr("h2c.mu.padding.output.shape.left.second.second.first",
      {Root::kPredicateLeft, "h2c.mu.padding.output",
       {{Edge::kSecond}, {Edge::kSecond}, {Edge::kFirst}}});
  s.shape_expr("h2c.c_tilde.r0.shape.left.second.first.first.shared.first.first.first.shared.first.first.first.first",
      {Root::kPredicateLeft, "h2c.c_tilde.r0",
       {{Edge::kSecond}, {Edge::kFirst}, {Edge::kFirst}, {Edge::kShared}, {Edge::kFirst}, {Edge::kFirst}, {Edge::kFirst}, {Edge::kShared}, {Edge::kFirst}, {Edge::kFirst}, {Edge::kFirst}, {Edge::kFirst}}});
  s.shape_expr("h2c.c_tilde.r0.shape.left.second.first.first.shared.first.first.first",
      {Root::kPredicateLeft, "h2c.c_tilde.r0",
       {{Edge::kSecond}, {Edge::kFirst}, {Edge::kFirst}, {Edge::kShared}, {Edge::kFirst}, {Edge::kFirst}, {Edge::kFirst}}});
  s.shape_expr("h2c.sib.r0.shape.left.second.first.first.shared.first.first.first",
      {Root::kPredicateLeft, "h2c.sib.r0",
       {{Edge::kSecond}, {Edge::kFirst}, {Edge::kFirst}, {Edge::kShared}, {Edge::kFirst}, {Edge::kFirst}, {Edge::kFirst}}});
  s.shape_expr("h2c.sib.r24.shape.left.second.first.first.shared.first.first.first",
      {Root::kPredicateLeft, "h2c.sib.r24",
       {{Edge::kSecond}, {Edge::kFirst}, {Edge::kFirst}, {Edge::kShared}, {Edge::kFirst}, {Edge::kFirst}, {Edge::kFirst}}});
  s.shape_expr("h2c.sample.select.start.shape.left.first.first",
      {Root::kPredicateLeft, "h2c.sample.select.start",
       {{Edge::kFirst}, {Edge::kFirst}}});
  s.shape_expr("h2c.sample.select.step.shape.left.second.first",
      {Root::kPredicateLeft, "h2c.sample.select.step",
       {{Edge::kSecond}, {Edge::kFirst}}});
  s.shape_expr("h2c.sample.select.route.shape.left.first.first.first.shared.first.first.first.shared.argument0",
      {Root::kPredicateLeft, "h2c.sample.select.route",
       {{Edge::kFirst}, {Edge::kFirst}, {Edge::kFirst}, {Edge::kShared}, {Edge::kFirst}, {Edge::kFirst}, {Edge::kFirst}, {Edge::kShared}, {Edge::kArgument, 0}}});
  s.shape_expr("h2c.sample.select.route.shape.left.first.first.first.shared.first.first.first",
      {Root::kPredicateLeft, "h2c.sample.select.route",
       {{Edge::kFirst}, {Edge::kFirst}, {Edge::kFirst}, {Edge::kShared}, {Edge::kFirst}, {Edge::kFirst}, {Edge::kFirst}}});
  s.shape_expr("h2c.sample.select.route.shape.left.first.first.first",
      {Root::kPredicateLeft, "h2c.sample.select.route",
       {{Edge::kFirst}, {Edge::kFirst}, {Edge::kFirst}}});
  s.shape_expr("h2c.sample.select.step.shape.left.second.second.first.second.first.first",
      {Root::kPredicateLeft, "h2c.sample.select.step",
       {{Edge::kSecond}, {Edge::kSecond}, {Edge::kFirst}, {Edge::kSecond}, {Edge::kFirst}, {Edge::kFirst}}});
  s.shape_expr("h2c.sample.select.step.shape.left.second.second.first.second.first.second.second.shared.second.shared.second",
      {Root::kPredicateLeft, "h2c.sample.select.step",
       {{Edge::kSecond}, {Edge::kSecond}, {Edge::kFirst}, {Edge::kSecond}, {Edge::kFirst}, {Edge::kSecond}, {Edge::kSecond}, {Edge::kShared}, {Edge::kSecond}, {Edge::kShared}, {Edge::kSecond}}});
  s.shape_expr("h2c.sample.select.step.shape.left.second.second.first.second.first.second.second.shared.second",
      {Root::kPredicateLeft, "h2c.sample.select.step",
       {{Edge::kSecond}, {Edge::kSecond}, {Edge::kFirst}, {Edge::kSecond}, {Edge::kFirst}, {Edge::kSecond}, {Edge::kSecond}, {Edge::kShared}, {Edge::kSecond}}});
  s.shape_expr("h2c.sample.select.step.shape.left.second.second.first.second.first.second.second.shared.first.second",
      {Root::kPredicateLeft, "h2c.sample.select.step",
       {{Edge::kSecond}, {Edge::kSecond}, {Edge::kFirst}, {Edge::kSecond}, {Edge::kFirst}, {Edge::kSecond}, {Edge::kSecond}, {Edge::kShared}, {Edge::kFirst}, {Edge::kSecond}}});
  s.shape_expr("h2c.sample.select.step.shape.left.second.second.first.second.first.second.second",
      {Root::kPredicateLeft, "h2c.sample.select.step",
       {{Edge::kSecond}, {Edge::kSecond}, {Edge::kFirst}, {Edge::kSecond}, {Edge::kFirst}, {Edge::kSecond}, {Edge::kSecond}}});
  s.shape_expr("h2c.sample.select.step.shape.left.second.second.first.second.first.second.first.second.shared.second",
      {Root::kPredicateLeft, "h2c.sample.select.step",
       {{Edge::kSecond}, {Edge::kSecond}, {Edge::kFirst}, {Edge::kSecond}, {Edge::kFirst}, {Edge::kSecond}, {Edge::kFirst}, {Edge::kSecond}, {Edge::kShared}, {Edge::kSecond}}});
  s.shape_expr("h2c.sample.select.step.shape.left.second.second.first.second.first.second.first.second",
      {Root::kPredicateLeft, "h2c.sample.select.step",
       {{Edge::kSecond}, {Edge::kSecond}, {Edge::kFirst}, {Edge::kSecond}, {Edge::kFirst}, {Edge::kSecond}, {Edge::kFirst}, {Edge::kSecond}}});
  s.shape_expr("h2c.sample.mem.unit.shape.left.second.first.first",
      {Root::kPredicateLeft, "h2c.sample.mem.unit",
       {{Edge::kSecond}, {Edge::kFirst}, {Edge::kFirst}}});
  s.shape_expr("h2c.sample.mem.shape.left.first.first.second.first.first.first.first.first",
      {Root::kPredicateLeft, "h2c.sample.mem",
       {{Edge::kFirst}, {Edge::kFirst}, {Edge::kSecond}, {Edge::kFirst}, {Edge::kFirst}, {Edge::kFirst}, {Edge::kFirst}, {Edge::kFirst}}});
  s.shape_expr("mac.equal.shape.left.shared.first.second.second.shared",
      {Root::kPredicateLeft, "mac.equal",
       {{Edge::kShared}, {Edge::kFirst}, {Edge::kSecond}, {Edge::kSecond}, {Edge::kShared}}});
  s.shape_expr("mac.equal.shape.left.shared.first.second.first",
      {Root::kPredicateLeft, "mac.equal",
       {{Edge::kShared}, {Edge::kFirst}, {Edge::kSecond}, {Edge::kFirst}}});
  s.shape_expr("mac.equal.shape.left.shared.first.second.second",
      {Root::kPredicateLeft, "mac.equal",
       {{Edge::kShared}, {Edge::kFirst}, {Edge::kSecond}, {Edge::kSecond}}});
  s.shape_expr("mac.equal.shape.left",
      {Root::kPredicateLeft, "mac.equal",
       {}});
  s.shape_value("signature.relation.shape.right",
      {Root::kPredicateRight, "signature.relation",
       {}});
  s.shape_value("hint.w1_bound.shape.left.argument1.first",
      {Root::kPredicateLeft, "hint.w1_bound",
       {{Edge::kArgument, 1}, {Edge::kFirst}}});
  s.shape_value("hint.w1_bound.shape.right",
      {Root::kPredicateRight, "hint.w1_bound",
       {}});
  s.shape_value("hint.interval.shape.right.first.shared.first.second.shared.argument1.first",
      {Root::kPredicateRight, "hint.interval",
       {{Edge::kFirst}, {Edge::kShared}, {Edge::kFirst}, {Edge::kSecond}, {Edge::kShared}, {Edge::kArgument, 1}, {Edge::kFirst}}});
  s.shape_value("hint.decompose.shape.left.first.second.first.first.second.first",
      {Root::kPredicateLeft, "hint.decompose",
       {{Edge::kFirst}, {Edge::kSecond}, {Edge::kFirst}, {Edge::kFirst}, {Edge::kSecond}, {Edge::kFirst}}});
  s.shape_value("hint.interval.shape.right.second.first",
      {Root::kPredicateRight, "hint.interval",
       {{Edge::kSecond}, {Edge::kFirst}}});
  s.shape_value("h2c.mu.padding.min.shape.left.second",
      {Root::kPredicateLeft, "h2c.mu.padding.min",
       {{Edge::kSecond}}});
  s.shape_value("h2c.mu.padding.suffix.shape.left.second.first.shared.first.first.first.first.shared.first.first.first.second",
      {Root::kPredicateLeft, "h2c.mu.padding.suffix",
       {{Edge::kSecond}, {Edge::kFirst}, {Edge::kShared}, {Edge::kFirst}, {Edge::kFirst}, {Edge::kFirst}, {Edge::kFirst}, {Edge::kShared}, {Edge::kFirst}, {Edge::kFirst}, {Edge::kFirst}, {Edge::kSecond}}});
  s.shape_value("h2c.mu.padding.output.shape.right",
      {Root::kPredicateRight, "h2c.mu.padding.output",
       {}});
  s.shape_value("h2c.mu.blocks.r0.shape.left.second.first.second.first.first",
      {Root::kPredicateLeft, "h2c.mu.blocks.r0",
       {{Edge::kSecond}, {Edge::kFirst}, {Edge::kSecond}, {Edge::kFirst}, {Edge::kFirst}}});
  s.shape_value("h2c.mu.blocks.r0.shape.left.second.second",
      {Root::kPredicateLeft, "h2c.mu.blocks.r0",
       {{Edge::kSecond}, {Edge::kSecond}}});
  s.shape_value("h2c.mu.blocks.r0.shape.right",
      {Root::kPredicateRight, "h2c.mu.blocks.r0",
       {}});
  s.shape_value("h2c.mu.blocks.r1.shape.left.second.second",
      {Root::kPredicateLeft, "h2c.mu.blocks.r1",
       {{Edge::kSecond}, {Edge::kSecond}}});
  s.shape_value("h2c.mu.blocks.r2.shape.left.second.second",
      {Root::kPredicateLeft, "h2c.mu.blocks.r2",
       {{Edge::kSecond}, {Edge::kSecond}}});
  s.shape_value("h2c.mu.blocks.r3.shape.left.second.second",
      {Root::kPredicateLeft, "h2c.mu.blocks.r3",
       {{Edge::kSecond}, {Edge::kSecond}}});
  s.shape_value("h2c.mu.blocks.r4.shape.left.second.second",
      {Root::kPredicateLeft, "h2c.mu.blocks.r4",
       {{Edge::kSecond}, {Edge::kSecond}}});
  s.shape_value("h2c.mu.blocks.r5.shape.left.second.second",
      {Root::kPredicateLeft, "h2c.mu.blocks.r5",
       {{Edge::kSecond}, {Edge::kSecond}}});
  s.shape_value("h2c.mu.blocks.r6.shape.left.second.second",
      {Root::kPredicateLeft, "h2c.mu.blocks.r6",
       {{Edge::kSecond}, {Edge::kSecond}}});
  s.shape_value("h2c.mu.blocks.r7.shape.left.second.second",
      {Root::kPredicateLeft, "h2c.mu.blocks.r7",
       {{Edge::kSecond}, {Edge::kSecond}}});
  s.shape_value("h2c.mu.blocks.r8.shape.left.second.second",
      {Root::kPredicateLeft, "h2c.mu.blocks.r8",
       {{Edge::kSecond}, {Edge::kSecond}}});
  s.shape_value("h2c.mu.blocks.r9.shape.left.second.second",
      {Root::kPredicateLeft, "h2c.mu.blocks.r9",
       {{Edge::kSecond}, {Edge::kSecond}}});
  s.shape_value("h2c.mu.blocks.r10.shape.left.second.second",
      {Root::kPredicateLeft, "h2c.mu.blocks.r10",
       {{Edge::kSecond}, {Edge::kSecond}}});
  s.shape_value("h2c.mu.blocks.r11.shape.left.second.second",
      {Root::kPredicateLeft, "h2c.mu.blocks.r11",
       {{Edge::kSecond}, {Edge::kSecond}}});
  s.shape_value("h2c.mu.blocks.r12.shape.left.second.second",
      {Root::kPredicateLeft, "h2c.mu.blocks.r12",
       {{Edge::kSecond}, {Edge::kSecond}}});
  s.shape_value("h2c.mu.blocks.r13.shape.left.second.second",
      {Root::kPredicateLeft, "h2c.mu.blocks.r13",
       {{Edge::kSecond}, {Edge::kSecond}}});
  s.shape_value("h2c.mu.blocks.r14.shape.left.second.second",
      {Root::kPredicateLeft, "h2c.mu.blocks.r14",
       {{Edge::kSecond}, {Edge::kSecond}}});
  s.shape_value("h2c.mu.blocks.r15.shape.left.second.second",
      {Root::kPredicateLeft, "h2c.mu.blocks.r15",
       {{Edge::kSecond}, {Edge::kSecond}}});
  s.shape_value("h2c.mu.blocks.r16.shape.left.second.second",
      {Root::kPredicateLeft, "h2c.mu.blocks.r16",
       {{Edge::kSecond}, {Edge::kSecond}}});
  s.shape_value("h2c.mu.blocks.r17.shape.left.second.second",
      {Root::kPredicateLeft, "h2c.mu.blocks.r17",
       {{Edge::kSecond}, {Edge::kSecond}}});
  s.shape_value("h2c.mu.blocks.r18.shape.left.second.second",
      {Root::kPredicateLeft, "h2c.mu.blocks.r18",
       {{Edge::kSecond}, {Edge::kSecond}}});
  s.shape_value("h2c.mu.blocks.r19.shape.left.second.second",
      {Root::kPredicateLeft, "h2c.mu.blocks.r19",
       {{Edge::kSecond}, {Edge::kSecond}}});
  s.shape_value("h2c.mu.blocks.r21.shape.left.second.second",
      {Root::kPredicateLeft, "h2c.mu.blocks.r21",
       {{Edge::kSecond}, {Edge::kSecond}}});
  s.shape_value("h2c.mu.blocks.r23.shape.left.second.second",
      {Root::kPredicateLeft, "h2c.mu.blocks.r23",
       {{Edge::kSecond}, {Edge::kSecond}}});
  s.shape_value("h2c.mu.padding.monotone.shape.right",
      {Root::kPredicateRight, "h2c.mu.padding.monotone",
       {}});
  s.shape_value("h2c.mu.padding.max.shape.right",
      {Root::kPredicateRight, "h2c.mu.padding.max",
       {}});
  s.shape_value("h2c.mu.padding.suffix.shape.left.second.first.shared.first.second.first",
      {Root::kPredicateLeft, "h2c.mu.padding.suffix",
       {{Edge::kSecond}, {Edge::kFirst}, {Edge::kShared}, {Edge::kFirst}, {Edge::kSecond}, {Edge::kFirst}}});
  s.shape_value("h2c.mu.padding.suffix.shape.left.second.second",
      {Root::kPredicateLeft, "h2c.mu.padding.suffix",
       {{Edge::kSecond}, {Edge::kSecond}}});
  s.shape_value("h2c.mu.padding.suffix.shape.right",
      {Root::kPredicateRight, "h2c.mu.padding.suffix",
       {}});
  s.shape_value("h2c.mu.padding.zeros.shape.left.second.second.second",
      {Root::kPredicateLeft, "h2c.mu.padding.zeros",
       {{Edge::kSecond}, {Edge::kSecond}, {Edge::kSecond}}});
  s.shape_value("h2c.c_tilde.r0.shape.left.second.first.first.shared.first.first.first.shared.first.first.first.first.shared.first.second",
      {Root::kPredicateLeft, "h2c.c_tilde.r0",
       {{Edge::kSecond}, {Edge::kFirst}, {Edge::kFirst}, {Edge::kShared}, {Edge::kFirst}, {Edge::kFirst}, {Edge::kFirst}, {Edge::kShared}, {Edge::kFirst}, {Edge::kFirst}, {Edge::kFirst}, {Edge::kFirst}, {Edge::kShared}, {Edge::kFirst}, {Edge::kSecond}}});
  s.shape_value("h2c.sib.r0.shape.left.second.first.first.shared.first.first.first.shared.first.first.first.first.first.second",
      {Root::kPredicateLeft, "h2c.sib.r0",
       {{Edge::kSecond}, {Edge::kFirst}, {Edge::kFirst}, {Edge::kShared}, {Edge::kFirst}, {Edge::kFirst}, {Edge::kFirst}, {Edge::kShared}, {Edge::kFirst}, {Edge::kFirst}, {Edge::kFirst}, {Edge::kFirst}, {Edge::kFirst}, {Edge::kSecond}}});
  s.shape_value("h2c.sample.select.start.shape.left.second",
      {Root::kPredicateLeft, "h2c.sample.select.start",
       {{Edge::kSecond}}});
  s.shape_value("h2c.sample.select.start.shape.right",
      {Root::kPredicateRight, "h2c.sample.select.start",
       {}});
  s.shape_value("h2c.sample.select.route.shape.left.first.first.first.shared.first.second.second.first",
      {Root::kPredicateLeft, "h2c.sample.select.route",
       {{Edge::kFirst}, {Edge::kFirst}, {Edge::kFirst}, {Edge::kShared}, {Edge::kFirst}, {Edge::kSecond}, {Edge::kSecond}, {Edge::kFirst}}});
  s.shape_value("h2c.sample.select.step.shape.right",
      {Root::kPredicateRight, "h2c.sample.select.step",
       {}});
  s.shape_value("h2c.sample.select.route.shape.left.second.first.second.first",
      {Root::kPredicateLeft, "h2c.sample.select.route",
       {{Edge::kSecond}, {Edge::kFirst}, {Edge::kSecond}, {Edge::kFirst}}});
  s.shape_value("h2c.sample.mem.unit.shape.right",
      {Root::kPredicateRight, "h2c.sample.mem.unit",
       {}});
  s.shape_value("h2c.sample.mem.origin.shape.left.second.first.second.first",
      {Root::kPredicateLeft, "h2c.sample.mem.origin",
       {{Edge::kSecond}, {Edge::kFirst}, {Edge::kSecond}, {Edge::kFirst}}});
  s.shape_value("h2c.sample.mem.shape.left.first.first.second.first.first.first.second.first",
      {Root::kPredicateLeft, "h2c.sample.mem",
       {{Edge::kFirst}, {Edge::kFirst}, {Edge::kSecond}, {Edge::kFirst}, {Edge::kFirst}, {Edge::kFirst}, {Edge::kSecond}, {Edge::kFirst}}});
  s.shape_value("h2c.sample.mem.shape.left.second.first.second.first.first.first.first.first.first",
      {Root::kPredicateLeft, "h2c.sample.mem",
       {{Edge::kSecond}, {Edge::kFirst}, {Edge::kSecond}, {Edge::kFirst}, {Edge::kFirst}, {Edge::kFirst}, {Edge::kFirst}, {Edge::kFirst}, {Edge::kFirst}}});
  s.shape_value("h2c.sample.mem.shape.left.second.first.second.second.first.first.first.first.first",
      {Root::kPredicateLeft, "h2c.sample.mem",
       {{Edge::kSecond}, {Edge::kFirst}, {Edge::kSecond}, {Edge::kSecond}, {Edge::kFirst}, {Edge::kFirst}, {Edge::kFirst}, {Edge::kFirst}, {Edge::kFirst}}});
  s.shape_value("h2c.sample.mem.shape.left.second.first.second.second.first.first.first.first.second.first",
      {Root::kPredicateLeft, "h2c.sample.mem",
       {{Edge::kSecond}, {Edge::kFirst}, {Edge::kSecond}, {Edge::kSecond}, {Edge::kFirst}, {Edge::kFirst}, {Edge::kFirst}, {Edge::kFirst}, {Edge::kSecond}, {Edge::kFirst}}});
  s.shape_value("h2c.sample.mem.fresh.shape.left.argument1",
      {Root::kPredicateLeft, "h2c.sample.mem.fresh",
       {{Edge::kArgument, 1}}});
  s.shape_value("h2c.sample.mem.fresh.shape.right",
      {Root::kPredicateRight, "h2c.sample.mem.fresh",
       {}});
  return {
      {"z.digit.low",
       "z.digit.high",
       "z.completion.low",
       "z.completion.high",
       "hint.offset.digit.low",
       "hint.offset.digit.high",
       "hint.slack.digit.low",
       "hint.slack.digit.high",
       "range.static:A.512",
       "mac.blind",
       "key.a_hat",
       "key.t1",
       "z",
       "hint.offset",
       "hint.slack",
       "tr",
       "msg",
       "w1",
       "h2c.mu.out",
       "h2c.c_tilde.r167.value.words",
       "h2c.c_tilde.r167.value",
       "h2c.c_tilde.out",
       "h2c.sib.r23.value.words",
       "h2c.sib.r23.value",
       "h2c.sib.r47.value.words",
       "h2c.sib.r47.value",
       "h2c.sib.out.p0",
       "h2c.sib.out.p1",
       "signature.relation.shape.right",
       "hint.w1_bound.shape.left.argument1.first",
       "hint.w1_bound.shape.right",
       "hint.interval.shape.right.first.shared.first.second.shared.argument1.first",
       "hint.decompose.shape.left.first.second.first.first.second.first",
       "hint.interval.shape.right.second.first",
       "h2c.mu.padding.min.shape.left.second",
       "h2c.mu.padding.suffix.shape.left.second.first.shared.first.first.first.first.shared.first.first.first.second",
       "h2c.mu.padding.output.shape.right",
       "h2c.mu.blocks.r0.shape.left.second.first.second.first.first",
       "h2c.mu.blocks.r0.shape.left.second.second",
       "h2c.mu.blocks.r0.shape.right",
       "h2c.mu.blocks.r1.shape.left.second.second",
       "h2c.mu.blocks.r2.shape.left.second.second",
       "h2c.mu.blocks.r3.shape.left.second.second",
       "h2c.mu.blocks.r4.shape.left.second.second",
       "h2c.mu.blocks.r5.shape.left.second.second",
       "h2c.mu.blocks.r6.shape.left.second.second",
       "h2c.mu.blocks.r7.shape.left.second.second",
       "h2c.mu.blocks.r8.shape.left.second.second",
       "h2c.mu.blocks.r9.shape.left.second.second",
       "h2c.mu.blocks.r10.shape.left.second.second",
       "h2c.mu.blocks.r11.shape.left.second.second",
       "h2c.mu.blocks.r12.shape.left.second.second",
       "h2c.mu.blocks.r13.shape.left.second.second",
       "h2c.mu.blocks.r14.shape.left.second.second",
       "h2c.mu.blocks.r15.shape.left.second.second",
       "h2c.mu.blocks.r16.shape.left.second.second",
       "h2c.mu.blocks.r17.shape.left.second.second",
       "h2c.mu.blocks.r18.shape.left.second.second",
       "h2c.mu.blocks.r19.shape.left.second.second",
       "h2c.mu.blocks.r21.shape.left.second.second",
       "h2c.mu.blocks.r23.shape.left.second.second",
       "h2c.mu.padding.monotone.shape.right",
       "h2c.mu.padding.max.shape.right",
       "h2c.mu.padding.suffix.shape.left.second.first.shared.first.second.first",
       "h2c.mu.padding.suffix.shape.left.second.second",
       "h2c.mu.padding.suffix.shape.right",
       "h2c.mu.padding.zeros.shape.left.second.second.second",
       "h2c.c_tilde.r0.shape.left.second.first.first.shared.first.first.first.shared.first.first.first.first.shared.first.second",
       "h2c.sib.r0.shape.left.second.first.first.shared.first.first.first.shared.first.first.first.first.first.second",
       "h2c.sample.select.start.shape.left.second",
       "h2c.sample.select.start.shape.right",
       "h2c.sample.select.route.shape.left.first.first.first.shared.first.second.second.first",
       "h2c.sample.select.step.shape.right",
       "h2c.sample.select.route.shape.left.second.first.second.first",
       "h2c.sample.mem.unit.shape.right",
       "h2c.sample.mem.origin.shape.left.second.first.second.first",
       "h2c.sample.mem.shape.left.first.first.second.first.first.first.second.first",
       "h2c.sample.mem.shape.left.second.first.second.first.first.first.first.first.first",
       "h2c.sample.mem.shape.left.second.first.second.second.first.first.first.first.first",
       "h2c.sample.mem.shape.left.second.first.second.second.first.first.first.first.second.first",
       "h2c.sample.mem.fresh.shape.left.argument1",
       "h2c.sample.mem.fresh.shape.right",
       "norm.z.offset",
       "h2c.sample.select.delta",
       "h2c.sample.mem.delta"},
      {"signature.relation",
       "hint.w1_bound",
       "hint.decompose",
       "hint.interval",
       "norm.z",
       "hint.offset",
       "hint.slack",
       "hint_weight.weight",
       "h2c.mu.padding.monotone",
       "h2c.mu.padding.max",
       "h2c.mu.padding.min",
       "h2c.mu.padding.suffix",
       "h2c.mu.padding.zeros",
       "h2c.mu.padding.output",
       "h2c.sample.select.start",
       "h2c.sample.select.step",
       "h2c.sample.select.route",
       "h2c.sample.mem.unit",
       "h2c.sample.mem.origin",
       "h2c.sample.mem",
       "h2c.sample.mem.fresh",
       "mac.equal",
       "mac.A",
       "range.norm.z.top",
       "mac.blind.boolean",
       "mac.low",
       "mac.high",
       "mac.nowrap",
       "mac",
       "h.boolean",
       "challenge.c.boolean",
       "hint.w1.boolean",
       "hint.nonpositive.boolean"},
      {"signature.relation.shape.left.first.second.first.first",
       "signature.relation.shape.left.second.first.first",
       "hint.interval.shape.right.first.shared.second.shared.first",
       "hint.decompose.shape.left.first.first.second.first.first.first.first.second.first",
       "hint.interval.shape.right.first.shared.first.second",
       "hint.interval.shape.right.first.shared.second",
       "hint.interval.shape.right.first",
       "mac.equal.shape.right",
       "h2c.mu.padding.suffix.shape.left.second.first.shared.first.first.first.first",
       "h2c.mu.blocks.r0.shape.left.second.first.first.shared.first.first.first",
       "h2c.mu.padding.suffix.shape.left.first.first",
       "h2c.mu.padding.suffix.shape.left.second.first",
       "h2c.mu.padding.output.shape.left.first.first.shared.first.first",
       "h2c.mu.padding.output.shape.left.first.first",
       "h2c.mu.padding.output.shape.left.second.second.first",
       "h2c.c_tilde.r0.shape.left.second.first.first.shared.first.first.first.shared.first.first.first.first",
       "h2c.c_tilde.r0.shape.left.second.first.first.shared.first.first.first",
       "h2c.sib.r0.shape.left.second.first.first.shared.first.first.first",
       "h2c.sib.r24.shape.left.second.first.first.shared.first.first.first",
       "h2c.sample.select.start.shape.left.first.first",
       "h2c.sample.select.step.shape.left.second.first",
       "h2c.sample.select.route.shape.left.first.first.first.shared.first.first.first.shared.argument0",
       "h2c.sample.select.route.shape.left.first.first.first.shared.first.first.first",
       "h2c.sample.select.route.shape.left.first.first.first",
       "h2c.sample.select.step.shape.left.second.second.first.second.first.first",
       "h2c.sample.select.step.shape.left.second.second.first.second.first.second.second.shared.second.shared.second",
       "h2c.sample.select.step.shape.left.second.second.first.second.first.second.second.shared.second",
       "h2c.sample.select.step.shape.left.second.second.first.second.first.second.second.shared.first.second",
       "h2c.sample.select.step.shape.left.second.second.first.second.first.second.second",
       "h2c.sample.select.step.shape.left.second.second.first.second.first.second.first.second.shared.second",
       "h2c.sample.select.step.shape.left.second.second.first.second.first.second.first.second",
       "h2c.sample.mem.unit.shape.left.second.first.first",
       "h2c.sample.mem.shape.left.first.first.second.first.first.first.first.first",
       "mac.equal.shape.left.shared.first.second.second.shared",
       "mac.equal.shape.left.shared.first.second.first",
       "mac.equal.shape.left.shared.first.second.second",
       "mac.equal.shape.left"},
      {}, {"w1.words"}};
}

inline NamedShapeInputs mldsa_emulated_shape_inputs(const Scope &s) {
  using Root = ShapeExprSelector::Root;
  s.shape_predicate("signature.relation.source",
      {"signature.relation", PredicateShapeSelector::Role::kSource,
       PredicateShapeSelector::Body::kMod});
  s.shape_predicate("signature.relation.realized",
      {"signature.relation", PredicateShapeSelector::Role::kRealization,
       PredicateShapeSelector::Body::kEqual});
  using Edge = ShapeExprSelector::Edge;
  // Completion witnesses remain checked value metadata, not source roles.
  s.shape_value("z.digit.low",
      {Root::kValueDefinition, "z",
       {{Edge::kFirst}, {Edge::kFirst}}});
  s.shape_value("z.digit.high",
      {Root::kValueDefinition, "z",
       {{Edge::kFirst}, {Edge::kSecond}, {Edge::kFirst}}});
  s.shape_value("z.completion.low",
      {Root::kPredicateLeft, "range.norm.z.top",
       {{Edge::kFirst}, {Edge::kSecond}, {Edge::kFirst}}});
  s.shape_value("z.completion.high",
      {Root::kPredicateLeft, "range.norm.z.top",
       {{Edge::kSecond}, {Edge::kFirst}}});
  s.shape_value("hint.offset.digit.low",
      {Root::kValueDefinition, "hint.offset",
       {{Edge::kFirst}}});
  s.shape_value("hint.offset.digit.high",
      {Root::kValueDefinition, "hint.offset",
       {{Edge::kSecond}, {Edge::kFirst}}});
  s.shape_value("hint.slack.digit.low",
      {Root::kValueDefinition, "hint.slack",
       {{Edge::kFirst}}});
  s.shape_value("hint.slack.digit.high",
      {Root::kValueDefinition, "hint.slack",
       {{Edge::kSecond}, {Edge::kFirst}}});

  s.shape_expr("hint.interval.shape.right.first.shared.second.shared.first",
      {Root::kPredicateRight, "hint.interval",
       {{Edge::kFirst}, {Edge::kShared}, {Edge::kSecond}, {Edge::kShared}, {Edge::kFirst}}});
  s.shape_expr("hint.decompose.shape.left.first.shared.first.first.second.first.first.first.first.second.first",
      {Root::kPredicateLeft, "hint.decompose",
       {{Edge::kFirst}, {Edge::kShared}, {Edge::kFirst}, {Edge::kFirst}, {Edge::kSecond}, {Edge::kFirst}, {Edge::kFirst}, {Edge::kFirst}, {Edge::kFirst}, {Edge::kSecond}, {Edge::kFirst}}});
  s.shape_expr("hint.interval.shape.right.first.shared.first.second",
      {Root::kPredicateRight, "hint.interval",
       {{Edge::kFirst}, {Edge::kShared}, {Edge::kFirst}, {Edge::kSecond}}});
  s.shape_expr("hint.interval.shape.right.first.shared.second",
      {Root::kPredicateRight, "hint.interval",
       {{Edge::kFirst}, {Edge::kShared}, {Edge::kSecond}}});
  s.shape_expr("hint.interval.shape.right.first",
      {Root::kPredicateRight, "hint.interval",
       {{Edge::kFirst}}});
  s.shape_expr("hint.decompose.shape.left.first",
      {Root::kPredicateLeft, "hint.decompose",
       {{Edge::kFirst}}});
  s.shape_expr("mac.equal.shape.right",
      {Root::kPredicateRight, "mac.equal",
       {}});
  s.shape_expr("signature.relation.shape.left.first.second.first.first",
      {Root::kPredicateLeft, "signature.relation.source",
       {{Edge::kFirst}, {Edge::kSecond}, {Edge::kFirst}, {Edge::kFirst}}});
  s.shape_expr("signature.relation.shape.left.second.first.first",
      {Root::kPredicateLeft, "signature.relation.source",
       {{Edge::kSecond}, {Edge::kFirst}, {Edge::kFirst}}});
  s.shape_value("hint.w1_bound.shape.left.argument1.first",
      {Root::kPredicateLeft, "hint.w1_bound",
       {{Edge::kArgument, 1}, {Edge::kFirst}}});
  s.shape_value("hint.w1_bound.shape.right",
      {Root::kPredicateRight, "hint.w1_bound",
       {}});
  s.shape_value("hint.interval.shape.right.first.shared.first.second.shared.argument1.first",
      {Root::kPredicateRight, "hint.interval",
       {{Edge::kFirst}, {Edge::kShared}, {Edge::kFirst}, {Edge::kSecond}, {Edge::kShared}, {Edge::kArgument, 1}, {Edge::kFirst}}});
  s.shape_value("hint.decompose.shape.left.first.shared.first.second.first.first.second.first",
      {Root::kPredicateLeft, "hint.decompose",
       {{Edge::kFirst}, {Edge::kShared}, {Edge::kFirst}, {Edge::kSecond}, {Edge::kFirst}, {Edge::kFirst}, {Edge::kSecond}, {Edge::kFirst}}});
  s.shape_value("hint.decompose.shape.left.second.second.first",
      {Root::kPredicateLeft, "hint.decompose",
       {{Edge::kSecond}, {Edge::kSecond}, {Edge::kFirst}}});
  s.shape_value("hint.decompose.shape.right",
      {Root::kPredicateRight, "hint.decompose",
       {}});
  s.shape_value("hint.interval.shape.right.second.first",
      {Root::kPredicateRight, "hint.interval",
       {{Edge::kSecond}, {Edge::kFirst}}});
  s.shape_expr("mac.equal.shape.left",
      {Root::kPredicateLeft, "mac.equal",
       {}});
  return {
      {"z.digit.low",
       "z.digit.high",
       "z.completion.low",
       "z.completion.high",
       "hint.offset.digit.low",
       "hint.offset.digit.high",
       "hint.slack.digit.low",
       "hint.slack.digit.high",
       "z",
       "signature.w",
       "hint.offset",
       "hint.slack",
       "hint.w1_bound.shape.left.argument1.first",
       "hint.w1_bound.shape.right",
       "hint.interval.shape.right.first.shared.first.second.shared.argument1.first",
       "hint.decompose.shape.left.first.shared.first.second.first.first.second.first",
       "hint.decompose.shape.left.second.second.first",
       "hint.decompose.shape.right",
       "hint.interval.shape.right.second.first",
       "norm.z.offset",
       "mac.blind"},
      {"hint.w1_bound",
       "hint.decompose",
       "hint.interval",
       "signature.w",
       "norm.z",
       "hint.offset",
       "hint.slack",
       "hint_weight.weight",
       "signature.relation.source",
       "mac.equal",
       "h.boolean",
       "challenge.c.boolean",
       "hint.w1.boolean",
       "hint.nonpositive.boolean",
       "mac.A",
       "range.norm.z.top",
       "mac.blind.boolean",
       "mac.low",
       "mac.high",
       "mac.nowrap",
       "signature.relation.realized",
       "signature.relation.q",
       "mac"},
      {"hint.interval.shape.right.first.shared.second.shared.first",
       "hint.decompose.shape.left.first.shared.first.first.second.first.first.first.first.second.first",
       "hint.interval.shape.right.first.shared.first.second",
       "hint.interval.shape.right.first.shared.second",
       "hint.interval.shape.right.first",
       "hint.decompose.shape.left.first",
       "mac.equal.shape.right",
       "signature.relation.shape.left.first.second.first.first",
       "signature.relation.shape.left.second.first.first",
       "mac.equal.shape.left"},
      {}};
}

// The ring programs' parts of the native and emulated programs. The lists
// mirror the frontends' renamings (`Ring.Native.σR`, `σQ`, `Ring.Carrier.σH`,
// `σA`) over every identifier the programs have; the embedding check reads both
// programs, so a wrong list fails the export's certificate.
namespace mldsa_embedding_internal {
constexpr size_t kValueIds = 600, kExprIds = 530;
inline std::vector<size_t> append_range(std::vector<size_t> xs, size_t lo, size_t count) {
  for (size_t i = 0; i < count; ++i) xs.push_back(lo + i);
  return xs;
}
inline size_t ring_val_rom(size_t v) {
  static const size_t low[] = {6, 3, 4, 5, 1, 7, 8, 9, 8, 11};
  static const size_t mid[] = {34, 43, 41, 37, 38, 39, 10, 36, 37, 38, 39, 40, 42};
  if (v < 10) return low[v];
  if (v < 34) return v + 2;
  if (v < 47) return mid[v - 34];
  if (v < 55) return v - 3;
  if (v < 57) return v;
  if (v < 66) return v + 3;
  if (v < 69) return v;
  if (v < 71) return v + 2;
  if (v < 119) return v;
  if (v < 121) return v - 50;
  if (v < 575) return v - 48;
  return v - 46;
}
inline size_t ring_val_qrom(size_t v) {
  const size_t r = ring_val_rom(v);
  return r >= 10 ? r - 1 : r;
}
inline size_t ring_pred_map(size_t k) {
  if (k <= 5) return k + 4;
  if (k <= 14) return k + 6;
  return k - 24;
}
inline size_t carrier_val_h(size_t v) {
  if (v == 6) return 8;
  if (v < 9) return v;
  if (v < 34) return v + 2;
  if (v == 35) return 43;
  if (v == 36) return 41;
  if (v < 40) return v;
  if (v == 40) return 10;
  if (v < 46) return v - 5;
  if (v == 46) return 42;
  if (v < 55) return v - 3;
  if (v < 69) return v;
  if (v < 71) return v + 3;
  if (v < 119) return v;
  if (v < 121) return v - 49;
  return v - 47;
}
inline size_t carrier_val_a(size_t v) {
  static const size_t low[] = {2, 3, 4, 1, 5, 6, 7};
  if (v < 7) return low[v];
  if (v < 58) return v;
  if (v < 62) return v + 2;
  if (v == 62) return 65;
  if (v < 67) return v + 3;
  if (v < 577) return v;
  return v - 47;
}
inline size_t carrier_pred_a(size_t k) {
  if (k < 2) return k + 1;
  if (k < 5) return k + 2;
  if (k < 6) return k + 1;
  return k + 3;
}
}  // namespace mldsa_embedding_internal

inline ProgramEmbeddingDecl mldsa_ring_native_embedding(const std::string &profile) {
  using namespace mldsa_embedding_internal;
  ProgramEmbeddingDecl d;
  d.name = "native.parts";
  d.source_config = "mldsa-native";
  d.profile = profile;
  const bool rom = profile == "narrow";
  for (size_t v = 0; v < kValueIds; ++v) d.vals.push_back(rom ? ring_val_rom(v) : ring_val_qrom(v));
  for (size_t k = 0; k < kExprIds; ++k) d.refs.push_back(k < 66 ? k + 43 : k - 12);
  d.chals = {1, 2, 3, 4};
  d.values = append_range(append_range({}, 0, 7), 9, 25);
  d.values.push_back(35);
  d.values.push_back(36);
  d.values = append_range(append_range(d.values, 40, 15), 57, 9);
  d.values.push_back(69);
  d.values.push_back(70);
  d.values = append_range(append_range(d.values, 119, 449), 575, 9);
  d.exprs = append_range({}, 2, 5);
  d.exprs.push_back(8);
  d.exprs = append_range(d.exprs, 66, 459);
  for (size_t k = 48; k <= 270; ++k) d.equals.emplace_back(k, k - 24);
  for (size_t k : {1, 2, 3, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14}) d.bodies.emplace_back(k, ring_pred_map(k));
  for (size_t k : {1, 2, 3, 6, 7, 8, 9, 11, 12, 13, 14}) d.sources.push_back(ring_pred_map(k));
  return d;
}

inline ProgramEmbeddingDecl mldsa_ring_carrier_native_embedding() {
  using namespace mldsa_embedding_internal;
  ProgramEmbeddingDecl d;
  d.name = "native.core";
  d.source_config = "mldsa-native";
  for (size_t v = 0; v < kValueIds; ++v) d.vals.push_back(carrier_val_h(v));
  for (size_t k = 0; k < kExprIds; ++k) d.refs.push_back(k < 20 ? 0 : k - 20);
  d.chals = {1, 2, 3, 4};
  d.values = {6};
  d.values = append_range(d.values, 9, 25);
  d.values.push_back(35);
  d.values.push_back(36);
  d.values = append_range(d.values, 40, 15);
  d.values.push_back(69);
  d.values.push_back(70);
  d.values = append_range(d.values, 119, 448);
  d.exprs = append_range({}, 66, 459);
  for (size_t k = 48; k <= 270; ++k) d.equals.emplace_back(k, k - 25);
  return d;
}

inline ProgramEmbeddingDecl mldsa_ring_carrier_emulated_embedding() {
  using namespace mldsa_embedding_internal;
  ProgramEmbeddingDecl d;
  d.name = "emulated.A";
  d.source_config = "mldsa-emulated";
  for (size_t v = 0; v < kValueIds; ++v) d.vals.push_back(carrier_val_a(v));
  for (size_t k = 0; k < kExprIds; ++k) d.refs.push_back(k < 6 ? k + 30 : k + 33);
  d.chals = {1, 2, 3, 4};
  d.values = append_range(append_range(append_range({}, 0, 7), 58, 9), 577, 13);
  d.exprs = {0, 1, 2, 3, 4, 5, 10, 11};
  for (size_t k : {0, 1, 2, 5, 6, 7, 8, 9, 11, 12, 13, 14, 15}) d.bodies.emplace_back(k, carrier_pred_a(k));
  for (size_t k : {0, 1, 2, 6, 7, 8, 9, 11, 12, 13, 14, 15}) d.sources.push_back(carrier_pred_a(k));
  return d;
}

inline NamedShapeInputs mldsa_ring_native_shape_inputs(const Scope &s) {
  using Root = ShapeExprSelector::Root;
  using Edge = ShapeExprSelector::Edge;
  // Completion witnesses remain checked value metadata, not source roles.
  s.shape_value("z.digit.low",
      {Root::kValueDefinition, "z",
       {{Edge::kFirst}, {Edge::kFirst}}});
  s.shape_value("z.digit.high",
      {Root::kValueDefinition, "z",
       {{Edge::kFirst}, {Edge::kSecond}, {Edge::kFirst}}});
  s.shape_value("z.completion.low",
      {Root::kPredicateLeft, "range.norm.z.top",
       {{Edge::kFirst}, {Edge::kSecond}, {Edge::kFirst}}});
  s.shape_value("z.completion.high",
      {Root::kPredicateLeft, "range.norm.z.top",
       {{Edge::kSecond}, {Edge::kFirst}}});
  s.shape_value("hint.offset.digit.low",
      {Root::kValueDefinition, "hint.offset",
       {{Edge::kFirst}}});
  s.shape_value("hint.offset.digit.high",
      {Root::kValueDefinition, "hint.offset",
       {{Edge::kSecond}, {Edge::kFirst}}});
  s.shape_value("hint.slack.digit.low",
      {Root::kValueDefinition, "hint.slack",
       {{Edge::kFirst}}});
  s.shape_value("hint.slack.digit.high",
      {Root::kValueDefinition, "hint.slack",
       {{Edge::kSecond}, {Edge::kFirst}}});

  s.shape_expr("member.select.shape.left.first.second.second.first.first.first.shared.first.second.first.first",
      {Root::kPredicateLeft, "member.select",
       {{Edge::kFirst}, {Edge::kSecond}, {Edge::kSecond}, {Edge::kFirst}, {Edge::kFirst}, {Edge::kFirst}, {Edge::kShared}, {Edge::kFirst}, {Edge::kSecond}, {Edge::kFirst}, {Edge::kFirst}}});
  s.shape_expr("member.select.shape.left.first.second.second.first.first.first",
      {Root::kPredicateLeft, "member.select",
       {{Edge::kFirst}, {Edge::kSecond}, {Edge::kSecond}, {Edge::kFirst}, {Edge::kFirst}, {Edge::kFirst}}});
  s.shape_expr("signature.relation.0.shape.left.first.first",
      {Root::kPredicateLeft, "signature.relation.0",
       {{Edge::kFirst}, {Edge::kFirst}}});
  s.shape_expr("signature.relation.0.shape.left.second.first.first.second.first.first.first",
      {Root::kPredicateLeft, "signature.relation.0",
       {{Edge::kSecond}, {Edge::kFirst}, {Edge::kFirst}, {Edge::kSecond}, {Edge::kFirst}, {Edge::kFirst}, {Edge::kFirst}}});
  s.shape_expr("signature.relation.0.shape.left.second.first.first.second.second.first.first",
      {Root::kPredicateLeft, "signature.relation.0",
       {{Edge::kSecond}, {Edge::kFirst}, {Edge::kFirst}, {Edge::kSecond}, {Edge::kSecond}, {Edge::kFirst}, {Edge::kFirst}}});
  s.shape_expr("signature.relation.0.shape.left.second.first.second.first.first.first.first",
      {Root::kPredicateLeft, "signature.relation.0",
       {{Edge::kSecond}, {Edge::kFirst}, {Edge::kSecond}, {Edge::kFirst}, {Edge::kFirst}, {Edge::kFirst}, {Edge::kFirst}}});
  s.shape_expr("signature.relation.0.shape.left.second.first.second.first.second.first.first.first.first",
      {Root::kPredicateLeft, "signature.relation.0",
       {{Edge::kSecond}, {Edge::kFirst}, {Edge::kSecond}, {Edge::kFirst}, {Edge::kSecond}, {Edge::kFirst}, {Edge::kFirst}, {Edge::kFirst}, {Edge::kFirst}}});
  s.shape_expr("signature.relation.0.shape.left.second.first.second.first.second.first.first.first.second.first",
      {Root::kPredicateLeft, "signature.relation.0",
       {{Edge::kSecond}, {Edge::kFirst}, {Edge::kSecond}, {Edge::kFirst}, {Edge::kSecond}, {Edge::kFirst}, {Edge::kFirst}, {Edge::kFirst}, {Edge::kSecond}, {Edge::kFirst}}});
  s.shape_expr("signature.relation.1.shape.left.first.first",
      {Root::kPredicateLeft, "signature.relation.1",
       {{Edge::kFirst}, {Edge::kFirst}}});
  s.shape_expr("signature.relation.1.shape.left.second.first.first.second.first.first.first",
      {Root::kPredicateLeft, "signature.relation.1",
       {{Edge::kSecond}, {Edge::kFirst}, {Edge::kFirst}, {Edge::kSecond}, {Edge::kFirst}, {Edge::kFirst}, {Edge::kFirst}}});
  s.shape_expr("signature.relation.1.shape.left.second.first.second.first.first.first.first",
      {Root::kPredicateLeft, "signature.relation.1",
       {{Edge::kSecond}, {Edge::kFirst}, {Edge::kSecond}, {Edge::kFirst}, {Edge::kFirst}, {Edge::kFirst}, {Edge::kFirst}}});
  s.shape_expr("signature.relation.2.shape.left.first.first",
      {Root::kPredicateLeft, "signature.relation.2",
       {{Edge::kFirst}, {Edge::kFirst}}});
  s.shape_expr("signature.relation.2.shape.left.second.first.first.second.first.first.first",
      {Root::kPredicateLeft, "signature.relation.2",
       {{Edge::kSecond}, {Edge::kFirst}, {Edge::kFirst}, {Edge::kSecond}, {Edge::kFirst}, {Edge::kFirst}, {Edge::kFirst}}});
  s.shape_expr("signature.relation.2.shape.left.second.first.second.first.first.first.first",
      {Root::kPredicateLeft, "signature.relation.2",
       {{Edge::kSecond}, {Edge::kFirst}, {Edge::kSecond}, {Edge::kFirst}, {Edge::kFirst}, {Edge::kFirst}, {Edge::kFirst}}});
  s.shape_expr("signature.relation.3.shape.left.first.first",
      {Root::kPredicateLeft, "signature.relation.3",
       {{Edge::kFirst}, {Edge::kFirst}}});
  s.shape_expr("signature.relation.3.shape.left.second.first.first.second.first.first.first",
      {Root::kPredicateLeft, "signature.relation.3",
       {{Edge::kSecond}, {Edge::kFirst}, {Edge::kFirst}, {Edge::kSecond}, {Edge::kFirst}, {Edge::kFirst}, {Edge::kFirst}}});
  s.shape_expr("signature.relation.3.shape.left.second.first.second.first.first.first.first",
      {Root::kPredicateLeft, "signature.relation.3",
       {{Edge::kSecond}, {Edge::kFirst}, {Edge::kSecond}, {Edge::kFirst}, {Edge::kFirst}, {Edge::kFirst}, {Edge::kFirst}}});
  s.shape_expr("mac.equal.shape.right",
      {Root::kPredicateRight, "mac.equal",
       {}});
  s.shape_expr("mac.equal.shape.left",
      {Root::kPredicateLeft, "mac.equal",
       {}});
  s.shape_expr("member.table.powers.shape.definition.first.first.shared.first.first.first.first.first.first.first.first.shared.first.first.shared.first.first.shared.first.first.shared.first.first.shared.first.first.shared.first.first",
      {Root::kValueDefinition, "member.table.powers",
       {{Edge::kFirst}, {Edge::kFirst}, {Edge::kShared}, {Edge::kFirst}, {Edge::kFirst}, {Edge::kFirst}, {Edge::kFirst}, {Edge::kFirst}, {Edge::kFirst}, {Edge::kFirst}, {Edge::kFirst}, {Edge::kShared}, {Edge::kFirst}, {Edge::kFirst}, {Edge::kShared}, {Edge::kFirst}, {Edge::kFirst}, {Edge::kShared}, {Edge::kFirst}, {Edge::kFirst}, {Edge::kShared}, {Edge::kFirst}, {Edge::kFirst}, {Edge::kShared}, {Edge::kFirst}, {Edge::kFirst}, {Edge::kShared}, {Edge::kFirst}, {Edge::kFirst}}});
  s.shape_expr("member.table.powers.shape.definition.first.first.shared.first.first.first.first.first.second.shared.first.shared.first.shared.first.shared.first.shared.first.shared.first.shared.first",
      {Root::kValueDefinition, "member.table.powers",
       {{Edge::kFirst}, {Edge::kFirst}, {Edge::kShared}, {Edge::kFirst}, {Edge::kFirst}, {Edge::kFirst}, {Edge::kFirst}, {Edge::kFirst}, {Edge::kSecond}, {Edge::kShared}, {Edge::kFirst}, {Edge::kShared}, {Edge::kFirst}, {Edge::kShared}, {Edge::kFirst}, {Edge::kShared}, {Edge::kFirst}, {Edge::kShared}, {Edge::kFirst}, {Edge::kShared}, {Edge::kFirst}, {Edge::kShared}, {Edge::kFirst}}});
  s.shape_expr("member.table.powers.shape.definition.first.first.shared.first.first.first.first.first.first.first.first.shared.first.first.shared.first.first.shared.first.first.shared.first.first.shared.first.first",
      {Root::kValueDefinition, "member.table.powers",
       {{Edge::kFirst}, {Edge::kFirst}, {Edge::kShared}, {Edge::kFirst}, {Edge::kFirst}, {Edge::kFirst}, {Edge::kFirst}, {Edge::kFirst}, {Edge::kFirst}, {Edge::kFirst}, {Edge::kFirst}, {Edge::kShared}, {Edge::kFirst}, {Edge::kFirst}, {Edge::kShared}, {Edge::kFirst}, {Edge::kFirst}, {Edge::kShared}, {Edge::kFirst}, {Edge::kFirst}, {Edge::kShared}, {Edge::kFirst}, {Edge::kFirst}, {Edge::kShared}, {Edge::kFirst}, {Edge::kFirst}}});
  s.shape_expr("member.table.powers.shape.definition.first.first.shared.first.first.first.first.first.second.shared.first.shared.first.shared.first.shared.first.shared.first.shared.first",
      {Root::kValueDefinition, "member.table.powers",
       {{Edge::kFirst}, {Edge::kFirst}, {Edge::kShared}, {Edge::kFirst}, {Edge::kFirst}, {Edge::kFirst}, {Edge::kFirst}, {Edge::kFirst}, {Edge::kSecond}, {Edge::kShared}, {Edge::kFirst}, {Edge::kShared}, {Edge::kFirst}, {Edge::kShared}, {Edge::kFirst}, {Edge::kShared}, {Edge::kFirst}, {Edge::kShared}, {Edge::kFirst}, {Edge::kShared}, {Edge::kFirst}}});
  s.shape_expr("member.table.powers.shape.definition.first.first.shared.first.first.first.first.first.first.first.first.shared.first.first.shared.first.first.shared.first.first.shared.first.first",
      {Root::kValueDefinition, "member.table.powers",
       {{Edge::kFirst}, {Edge::kFirst}, {Edge::kShared}, {Edge::kFirst}, {Edge::kFirst}, {Edge::kFirst}, {Edge::kFirst}, {Edge::kFirst}, {Edge::kFirst}, {Edge::kFirst}, {Edge::kFirst}, {Edge::kShared}, {Edge::kFirst}, {Edge::kFirst}, {Edge::kShared}, {Edge::kFirst}, {Edge::kFirst}, {Edge::kShared}, {Edge::kFirst}, {Edge::kFirst}, {Edge::kShared}, {Edge::kFirst}, {Edge::kFirst}}});
  s.shape_expr("member.table.powers.shape.definition.first.first.shared.first.first.first.first.first.second.shared.first.shared.first.shared.first.shared.first.shared.first",
      {Root::kValueDefinition, "member.table.powers",
       {{Edge::kFirst}, {Edge::kFirst}, {Edge::kShared}, {Edge::kFirst}, {Edge::kFirst}, {Edge::kFirst}, {Edge::kFirst}, {Edge::kFirst}, {Edge::kSecond}, {Edge::kShared}, {Edge::kFirst}, {Edge::kShared}, {Edge::kFirst}, {Edge::kShared}, {Edge::kFirst}, {Edge::kShared}, {Edge::kFirst}, {Edge::kShared}, {Edge::kFirst}}});
  s.shape_expr("member.table.powers.shape.definition.first.first.shared.first.first.first.first.first.first.first.first.shared.first.first.shared.first.first.shared.first.first",
      {Root::kValueDefinition, "member.table.powers",
       {{Edge::kFirst}, {Edge::kFirst}, {Edge::kShared}, {Edge::kFirst}, {Edge::kFirst}, {Edge::kFirst}, {Edge::kFirst}, {Edge::kFirst}, {Edge::kFirst}, {Edge::kFirst}, {Edge::kFirst}, {Edge::kShared}, {Edge::kFirst}, {Edge::kFirst}, {Edge::kShared}, {Edge::kFirst}, {Edge::kFirst}, {Edge::kShared}, {Edge::kFirst}, {Edge::kFirst}}});
  s.shape_expr("member.table.powers.shape.definition.first.first.shared.first.first.first.first.first.second.shared.first.shared.first.shared.first.shared.first",
      {Root::kValueDefinition, "member.table.powers",
       {{Edge::kFirst}, {Edge::kFirst}, {Edge::kShared}, {Edge::kFirst}, {Edge::kFirst}, {Edge::kFirst}, {Edge::kFirst}, {Edge::kFirst}, {Edge::kSecond}, {Edge::kShared}, {Edge::kFirst}, {Edge::kShared}, {Edge::kFirst}, {Edge::kShared}, {Edge::kFirst}, {Edge::kShared}, {Edge::kFirst}}});
  s.shape_expr("member.table.powers.shape.definition.first.first.shared.first.first.first.first.first.first.first.first.shared.first.first.shared.first.first",
      {Root::kValueDefinition, "member.table.powers",
       {{Edge::kFirst}, {Edge::kFirst}, {Edge::kShared}, {Edge::kFirst}, {Edge::kFirst}, {Edge::kFirst}, {Edge::kFirst}, {Edge::kFirst}, {Edge::kFirst}, {Edge::kFirst}, {Edge::kFirst}, {Edge::kShared}, {Edge::kFirst}, {Edge::kFirst}, {Edge::kShared}, {Edge::kFirst}, {Edge::kFirst}}});
  s.shape_expr("member.table.powers.shape.definition.first.first.shared.first.first.first.first.first.second.shared.first.shared.first.shared.first",
      {Root::kValueDefinition, "member.table.powers",
       {{Edge::kFirst}, {Edge::kFirst}, {Edge::kShared}, {Edge::kFirst}, {Edge::kFirst}, {Edge::kFirst}, {Edge::kFirst}, {Edge::kFirst}, {Edge::kSecond}, {Edge::kShared}, {Edge::kFirst}, {Edge::kShared}, {Edge::kFirst}, {Edge::kShared}, {Edge::kFirst}}});
  s.shape_expr("member.table.powers.shape.definition.first.first.shared.first.first.first.first.first.first.first.first.shared.first.first",
      {Root::kValueDefinition, "member.table.powers",
       {{Edge::kFirst}, {Edge::kFirst}, {Edge::kShared}, {Edge::kFirst}, {Edge::kFirst}, {Edge::kFirst}, {Edge::kFirst}, {Edge::kFirst}, {Edge::kFirst}, {Edge::kFirst}, {Edge::kFirst}, {Edge::kShared}, {Edge::kFirst}, {Edge::kFirst}}});
  s.shape_expr("member.table.powers.shape.definition.first.first.shared.first.first.first.first.first.second.shared.first.shared.first",
      {Root::kValueDefinition, "member.table.powers",
       {{Edge::kFirst}, {Edge::kFirst}, {Edge::kShared}, {Edge::kFirst}, {Edge::kFirst}, {Edge::kFirst}, {Edge::kFirst}, {Edge::kFirst}, {Edge::kSecond}, {Edge::kShared}, {Edge::kFirst}, {Edge::kShared}, {Edge::kFirst}}});
  s.shape_expr("member.table.powers.shape.definition.first.first.shared.first.first.first.first.first.first.first.first",
      {Root::kValueDefinition, "member.table.powers",
       {{Edge::kFirst}, {Edge::kFirst}, {Edge::kShared}, {Edge::kFirst}, {Edge::kFirst}, {Edge::kFirst}, {Edge::kFirst}, {Edge::kFirst}, {Edge::kFirst}, {Edge::kFirst}, {Edge::kFirst}}});
  s.shape_expr("member.table.powers.shape.definition.first.first.shared.first.first.first.first.first.second.shared.first",
      {Root::kValueDefinition, "member.table.powers",
       {{Edge::kFirst}, {Edge::kFirst}, {Edge::kShared}, {Edge::kFirst}, {Edge::kFirst}, {Edge::kFirst}, {Edge::kFirst}, {Edge::kFirst}, {Edge::kSecond}, {Edge::kShared}, {Edge::kFirst}}});
  s.shape_expr("member.table.powers.shape.definition.first.first.shared.first.first.first.first.first.second",
      {Root::kValueDefinition, "member.table.powers",
       {{Edge::kFirst}, {Edge::kFirst}, {Edge::kShared}, {Edge::kFirst}, {Edge::kFirst}, {Edge::kFirst}, {Edge::kFirst}, {Edge::kFirst}, {Edge::kSecond}}});
  s.shape_expr("member.table.powers.shape.definition.first.first.shared.first.first.first.second.first.first",
      {Root::kValueDefinition, "member.table.powers",
       {{Edge::kFirst}, {Edge::kFirst}, {Edge::kShared}, {Edge::kFirst}, {Edge::kFirst}, {Edge::kFirst}, {Edge::kSecond}, {Edge::kFirst}, {Edge::kFirst}}});
  s.shape_expr("member.table.powers.shape.definition.first.first.shared.first.second.first.first.first.first.second",
      {Root::kValueDefinition, "member.table.powers",
       {{Edge::kFirst}, {Edge::kFirst}, {Edge::kShared}, {Edge::kFirst}, {Edge::kSecond}, {Edge::kFirst}, {Edge::kFirst}, {Edge::kFirst}, {Edge::kFirst}, {Edge::kSecond}}});
  s.shape_expr("member.table.powers.shape.definition.first.second.shared.first.first.first.first.first.first.second",
      {Root::kValueDefinition, "member.table.powers",
       {{Edge::kFirst}, {Edge::kSecond}, {Edge::kShared}, {Edge::kFirst}, {Edge::kFirst}, {Edge::kFirst}, {Edge::kFirst}, {Edge::kFirst}, {Edge::kFirst}, {Edge::kSecond}}});
  s.shape_expr("member.table.powers.shape.definition.first.first",
      {Root::kValueDefinition, "member.table.powers",
       {{Edge::kFirst}, {Edge::kFirst}}});
  s.shape_expr("member.table.powers.shape.definition.first.second.shared.first.second.first.second.first.first.second",
      {Root::kValueDefinition, "member.table.powers",
       {{Edge::kFirst}, {Edge::kSecond}, {Edge::kShared}, {Edge::kFirst}, {Edge::kSecond}, {Edge::kFirst}, {Edge::kSecond}, {Edge::kFirst}, {Edge::kFirst}, {Edge::kSecond}}});
  s.shape_expr("member.table.powers.shape.definition.first.second",
      {Root::kValueDefinition, "member.table.powers",
       {{Edge::kFirst}, {Edge::kSecond}}});
  s.shape_expr("member.table.digests.shape.definition.first.first.first.shared.first.first.first.first.first.first.first.first.first",
      {Root::kValueDefinition, "member.table.digests",
       {{Edge::kFirst}, {Edge::kFirst}, {Edge::kFirst}, {Edge::kShared}, {Edge::kFirst}, {Edge::kFirst}, {Edge::kFirst}, {Edge::kFirst}, {Edge::kFirst}, {Edge::kFirst}, {Edge::kFirst}, {Edge::kFirst}, {Edge::kFirst}}});
  s.shape_expr("member.table.digests.shape.definition.first.first.first",
      {Root::kValueDefinition, "member.table.digests",
       {{Edge::kFirst}, {Edge::kFirst}, {Edge::kFirst}}});
  s.shape_expr("mac.equal.shape.left.shared.first.second.second.first",
      {Root::kPredicateLeft, "mac.equal",
       {{Edge::kShared}, {Edge::kFirst}, {Edge::kSecond}, {Edge::kSecond}, {Edge::kFirst}}});
  s.shape_expr("mac.equal.shape.left.shared.first.second.second.second",
      {Root::kPredicateLeft, "mac.equal",
       {{Edge::kShared}, {Edge::kFirst}, {Edge::kSecond}, {Edge::kSecond}, {Edge::kSecond}}});
  s.shape_value("member.select.shape.right",
      {Root::kPredicateRight, "member.select",
       {}});
  s.shape_value("hint.decompose.shape.one",
      {Root::kPredicateLeft, "hint.decompose",
       {{Edge::kFirst}, {Edge::kSecond}, {Edge::kFirst}, {Edge::kFirst}, {Edge::kSecond}, {Edge::kFirst}}});
  s.shape_value("signature.relation.0.shape.right",
      {Root::kPredicateRight, "signature.relation.0",
       {}});
  s.shape_expr("mac.equal.shape.left.shared.first.second.second.second.shared",
      {Root::kPredicateLeft, "mac.equal",
       {{Edge::kShared}, {Edge::kFirst}, {Edge::kSecond}, {Edge::kSecond}, {Edge::kSecond}, {Edge::kShared}}});
  s.shape_expr("member.select.shape.left.second.first.second.first.shared.second.first.shared.second.first.shared.second.first.shared.second.first",
      {Root::kPredicateLeft, "member.select",
       {{Edge::kSecond}, {Edge::kFirst}, {Edge::kSecond}, {Edge::kFirst}, {Edge::kShared}, {Edge::kSecond}, {Edge::kFirst}, {Edge::kShared}, {Edge::kSecond}, {Edge::kFirst}, {Edge::kShared}, {Edge::kSecond}, {Edge::kFirst}, {Edge::kShared}, {Edge::kSecond}, {Edge::kFirst}}});
  s.shape_expr("member.select.shape.left.second.first.second.first.shared.second.first.shared.second.first.shared.second.first",
      {Root::kPredicateLeft, "member.select",
       {{Edge::kSecond}, {Edge::kFirst}, {Edge::kSecond}, {Edge::kFirst}, {Edge::kShared}, {Edge::kSecond}, {Edge::kFirst}, {Edge::kShared}, {Edge::kSecond}, {Edge::kFirst}, {Edge::kShared}, {Edge::kSecond}, {Edge::kFirst}}});
  s.shape_expr("member.select.shape.left.second.first.second.first.shared.second.first.shared.second.first",
      {Root::kPredicateLeft, "member.select",
       {{Edge::kSecond}, {Edge::kFirst}, {Edge::kSecond}, {Edge::kFirst}, {Edge::kShared}, {Edge::kSecond}, {Edge::kFirst}, {Edge::kShared}, {Edge::kSecond}, {Edge::kFirst}}});
  s.shape_expr("member.select.shape.left.second.first.second.first.shared.second.first",
      {Root::kPredicateLeft, "member.select",
       {{Edge::kSecond}, {Edge::kFirst}, {Edge::kSecond}, {Edge::kFirst}, {Edge::kShared}, {Edge::kSecond}, {Edge::kFirst}}});
  s.shape_expr("member.select.shape.left.second.first.second.first",
      {Root::kPredicateLeft, "member.select",
       {{Edge::kSecond}, {Edge::kFirst}, {Edge::kSecond}, {Edge::kFirst}}});
  return {
      {"z.digit.low",
       "z.digit.high",
       "z.completion.low",
       "z.completion.high",
       "hint.offset.digit.low",
       "hint.offset.digit.high",
       "hint.slack.digit.low",
       "hint.slack.digit.high",
       "range.static:A.512",
       "ring.keys",
       "ring.mu",
       "member.select.index",
       "member.table.gamma",
       "member.table.powers",
       "member.table.digests",
       "member.select.shape.right",
       "hint.decompose.shape.one",
       "signature.relation.0.shape.right",
       "h2c.c_tilde.out",
       "mac.blind",
       "norm.z.offset"},
      {"signature.relation.0",
       "signature.relation.1",
       "signature.relation.2",
       "signature.relation.3",
       "member.select.index.boolean",
       "norm.z",
       "mac.equal",
       "mac.A",
       "range.norm.z.top",
       "mac.blind.boolean",
       "mac.low",
       "mac.high",
       "mac.nowrap",
       "mac",
       "member.select",
       "member.mu.boolean",
       "challenge.c.boolean"},
      {"member.select.shape.left.first.second.second.first.first.first.shared.first.second.first.first",
       "member.select.shape.left.first.second.second.first.first.first",
       "signature.relation.0.shape.left.first.first",
       "signature.relation.0.shape.left.second.first.first.second.first.first.first",
       "signature.relation.0.shape.left.second.first.first.second.second.first.first",
       "signature.relation.0.shape.left.second.first.second.first.first.first.first",
       "signature.relation.0.shape.left.second.first.second.first.second.first.first.first.first",
       "signature.relation.0.shape.left.second.first.second.first.second.first.first.first.second.first",
       "signature.relation.1.shape.left.first.first",
       "signature.relation.1.shape.left.second.first.first.second.first.first.first",
       "signature.relation.1.shape.left.second.first.second.first.first.first.first",
       "signature.relation.2.shape.left.first.first",
       "signature.relation.2.shape.left.second.first.first.second.first.first.first",
       "signature.relation.2.shape.left.second.first.second.first.first.first.first",
       "signature.relation.3.shape.left.first.first",
       "signature.relation.3.shape.left.second.first.first.second.first.first.first",
       "signature.relation.3.shape.left.second.first.second.first.first.first.first",
       "mac.equal.shape.right",
       "mac.equal.shape.left",
       "member.table.powers.shape.definition.first.first.shared.first.first.first.first.first.first.first.first.shared.first.first.shared.first.first.shared.first.first.shared.first.first.shared.first.first.shared.first.first",
       "member.table.powers.shape.definition.first.first.shared.first.first.first.first.first.second.shared.first.shared.first.shared.first.shared.first.shared.first.shared.first.shared.first",
       "member.table.powers.shape.definition.first.first.shared.first.first.first.first.first.first.first.first.shared.first.first.shared.first.first.shared.first.first.shared.first.first.shared.first.first",
       "member.table.powers.shape.definition.first.first.shared.first.first.first.first.first.second.shared.first.shared.first.shared.first.shared.first.shared.first.shared.first",
       "member.table.powers.shape.definition.first.first.shared.first.first.first.first.first.first.first.first.shared.first.first.shared.first.first.shared.first.first.shared.first.first",
       "member.table.powers.shape.definition.first.first.shared.first.first.first.first.first.second.shared.first.shared.first.shared.first.shared.first.shared.first",
       "member.table.powers.shape.definition.first.first.shared.first.first.first.first.first.first.first.first.shared.first.first.shared.first.first.shared.first.first",
       "member.table.powers.shape.definition.first.first.shared.first.first.first.first.first.second.shared.first.shared.first.shared.first.shared.first",
       "member.table.powers.shape.definition.first.first.shared.first.first.first.first.first.first.first.first.shared.first.first.shared.first.first",
       "member.table.powers.shape.definition.first.first.shared.first.first.first.first.first.second.shared.first.shared.first.shared.first",
       "member.table.powers.shape.definition.first.first.shared.first.first.first.first.first.first.first.first.shared.first.first",
       "member.table.powers.shape.definition.first.first.shared.first.first.first.first.first.second.shared.first.shared.first",
       "member.table.powers.shape.definition.first.first.shared.first.first.first.first.first.first.first.first",
       "member.table.powers.shape.definition.first.first.shared.first.first.first.first.first.second.shared.first",
       "member.table.powers.shape.definition.first.first.shared.first.first.first.first.first.second",
       "member.table.powers.shape.definition.first.first.shared.first.first.first.second.first.first",
       "member.table.powers.shape.definition.first.first.shared.first.second.first.first.first.first.second",
       "member.table.powers.shape.definition.first.second.shared.first.first.first.first.first.first.second",
       "member.table.powers.shape.definition.first.first",
       "member.table.powers.shape.definition.first.second.shared.first.second.first.second.first.first.second",
       "member.table.powers.shape.definition.first.second",
       "member.table.digests.shape.definition.first.first.first.shared.first.first.first.first.first.first.first.first.first",
       "member.table.digests.shape.definition.first.first.first",
       "mac.equal.shape.left.shared.first.second.second.first",
       "mac.equal.shape.left.shared.first.second.second.second",
       "mac.equal.shape.left.shared.first.second.second.second.shared",
       "member.select.shape.left.second.first.second.first.shared.second.first.shared.second.first.shared.second.first.shared.second.first",
       "member.select.shape.left.second.first.second.first.shared.second.first.shared.second.first.shared.second.first",
       "member.select.shape.left.second.first.second.first.shared.second.first.shared.second.first",
       "member.select.shape.left.second.first.second.first.shared.second.first",
       "member.select.shape.left.second.first.second.first"},
      {}};
}

inline NamedShapeInputs mldsa_ring_carrier_shape_inputs(const Scope &s) {
  using Root = ShapeExprSelector::Root;
  using Edge = ShapeExprSelector::Edge;
  // Completion witnesses remain checked value metadata, not source roles.
  s.shape_value("z.digit.low",
      {Root::kValueDefinition, "z",
       {{Edge::kFirst}, {Edge::kFirst}}});
  s.shape_value("z.digit.high",
      {Root::kValueDefinition, "z",
       {{Edge::kFirst}, {Edge::kSecond}, {Edge::kFirst}}});
  s.shape_value("z.completion.low",
      {Root::kPredicateLeft, "range.norm.z.top",
       {{Edge::kFirst}, {Edge::kSecond}, {Edge::kFirst}}});
  s.shape_value("z.completion.high",
      {Root::kPredicateLeft, "range.norm.z.top",
       {{Edge::kSecond}, {Edge::kFirst}}});
  s.shape_value("hint.offset.digit.low",
      {Root::kValueDefinition, "hint.offset",
       {{Edge::kFirst}}});
  s.shape_value("hint.offset.digit.high",
      {Root::kValueDefinition, "hint.offset",
       {{Edge::kSecond}, {Edge::kFirst}}});
  s.shape_value("hint.slack.digit.low",
      {Root::kValueDefinition, "hint.slack",
       {{Edge::kFirst}}});
  s.shape_value("hint.slack.digit.high",
      {Root::kValueDefinition, "hint.slack",
       {{Edge::kSecond}, {Edge::kFirst}}});

  s.shape_expr("member.select.shape.left.first.second.second.first.first.first.shared.first.second.first.first",
      {Root::kPredicateLeft, "member.select",
       {{Edge::kFirst}, {Edge::kSecond}, {Edge::kSecond}, {Edge::kFirst}, {Edge::kFirst}, {Edge::kFirst}, {Edge::kShared}, {Edge::kFirst}, {Edge::kSecond}, {Edge::kFirst}, {Edge::kFirst}}});
  s.shape_expr("member.select.shape.left.first.second.second.first.first.first",
      {Root::kPredicateLeft, "member.select",
       {{Edge::kFirst}, {Edge::kSecond}, {Edge::kSecond}, {Edge::kFirst}, {Edge::kFirst}, {Edge::kFirst}}});
  s.shape_expr("signature.relation.shape.left.first",
      {Root::kPredicateLeft, "signature.relation",
       {{Edge::kFirst}}});
  s.shape_expr("signature.relation.shape.right.first.second.first.first.first.first",
      {Root::kPredicateRight, "signature.relation",
       {{Edge::kFirst}, {Edge::kSecond}, {Edge::kFirst}, {Edge::kFirst}, {Edge::kFirst}, {Edge::kFirst}}});
  s.shape_expr("signature.relation.shape.right.first.second.first.first.first.second.first",
      {Root::kPredicateRight, "signature.relation",
       {{Edge::kFirst}, {Edge::kSecond}, {Edge::kFirst}, {Edge::kFirst}, {Edge::kFirst}, {Edge::kSecond}, {Edge::kFirst}}});
  s.shape_expr("signature.relation.shape.left.second.first",
      {Root::kPredicateLeft, "signature.relation",
       {{Edge::kSecond}, {Edge::kFirst}}});
  s.shape_expr("signature.relation.shape.left.second.second.first",
      {Root::kPredicateLeft, "signature.relation",
       {{Edge::kSecond}, {Edge::kSecond}, {Edge::kFirst}}});
  s.shape_expr("signature.relation.shape.left.second.second.second",
      {Root::kPredicateLeft, "signature.relation",
       {{Edge::kSecond}, {Edge::kSecond}, {Edge::kSecond}}});
  s.shape_expr("mac.equal.shape.right",
      {Root::kPredicateRight, "mac.equal",
       {}});
  s.shape_expr("mac.equal.shape.left.shared.first.second.second.second",
      {Root::kPredicateLeft, "mac.equal",
       {{Edge::kShared}, {Edge::kFirst}, {Edge::kSecond}, {Edge::kSecond}, {Edge::kSecond}}});
  s.shape_expr("mac.equal.shape.left",
      {Root::kPredicateLeft, "mac.equal",
       {}});
  s.shape_expr("member.table.powers.shape.definition.first.first.shared.first.first.first.first.first.first.first.first.shared.first.first.shared.first.first.shared.first.first.shared.first.first.shared.first.first.shared.first.first",
      {Root::kValueDefinition, "member.table.powers",
       {{Edge::kFirst}, {Edge::kFirst}, {Edge::kShared}, {Edge::kFirst}, {Edge::kFirst}, {Edge::kFirst}, {Edge::kFirst}, {Edge::kFirst}, {Edge::kFirst}, {Edge::kFirst}, {Edge::kFirst}, {Edge::kShared}, {Edge::kFirst}, {Edge::kFirst}, {Edge::kShared}, {Edge::kFirst}, {Edge::kFirst}, {Edge::kShared}, {Edge::kFirst}, {Edge::kFirst}, {Edge::kShared}, {Edge::kFirst}, {Edge::kFirst}, {Edge::kShared}, {Edge::kFirst}, {Edge::kFirst}, {Edge::kShared}, {Edge::kFirst}, {Edge::kFirst}}});
  s.shape_expr("member.table.powers.shape.definition.first.first.shared.first.first.first.first.first.second.shared.first.shared.first.shared.first.shared.first.shared.first.shared.first.shared.first",
      {Root::kValueDefinition, "member.table.powers",
       {{Edge::kFirst}, {Edge::kFirst}, {Edge::kShared}, {Edge::kFirst}, {Edge::kFirst}, {Edge::kFirst}, {Edge::kFirst}, {Edge::kFirst}, {Edge::kSecond}, {Edge::kShared}, {Edge::kFirst}, {Edge::kShared}, {Edge::kFirst}, {Edge::kShared}, {Edge::kFirst}, {Edge::kShared}, {Edge::kFirst}, {Edge::kShared}, {Edge::kFirst}, {Edge::kShared}, {Edge::kFirst}, {Edge::kShared}, {Edge::kFirst}}});
  s.shape_expr("member.table.powers.shape.definition.first.first.shared.first.first.first.first.first.first.first.first.shared.first.first.shared.first.first.shared.first.first.shared.first.first.shared.first.first",
      {Root::kValueDefinition, "member.table.powers",
       {{Edge::kFirst}, {Edge::kFirst}, {Edge::kShared}, {Edge::kFirst}, {Edge::kFirst}, {Edge::kFirst}, {Edge::kFirst}, {Edge::kFirst}, {Edge::kFirst}, {Edge::kFirst}, {Edge::kFirst}, {Edge::kShared}, {Edge::kFirst}, {Edge::kFirst}, {Edge::kShared}, {Edge::kFirst}, {Edge::kFirst}, {Edge::kShared}, {Edge::kFirst}, {Edge::kFirst}, {Edge::kShared}, {Edge::kFirst}, {Edge::kFirst}, {Edge::kShared}, {Edge::kFirst}, {Edge::kFirst}}});
  s.shape_expr("member.table.powers.shape.definition.first.first.shared.first.first.first.first.first.second.shared.first.shared.first.shared.first.shared.first.shared.first.shared.first",
      {Root::kValueDefinition, "member.table.powers",
       {{Edge::kFirst}, {Edge::kFirst}, {Edge::kShared}, {Edge::kFirst}, {Edge::kFirst}, {Edge::kFirst}, {Edge::kFirst}, {Edge::kFirst}, {Edge::kSecond}, {Edge::kShared}, {Edge::kFirst}, {Edge::kShared}, {Edge::kFirst}, {Edge::kShared}, {Edge::kFirst}, {Edge::kShared}, {Edge::kFirst}, {Edge::kShared}, {Edge::kFirst}, {Edge::kShared}, {Edge::kFirst}}});
  s.shape_expr("member.table.powers.shape.definition.first.first.shared.first.first.first.first.first.first.first.first.shared.first.first.shared.first.first.shared.first.first.shared.first.first",
      {Root::kValueDefinition, "member.table.powers",
       {{Edge::kFirst}, {Edge::kFirst}, {Edge::kShared}, {Edge::kFirst}, {Edge::kFirst}, {Edge::kFirst}, {Edge::kFirst}, {Edge::kFirst}, {Edge::kFirst}, {Edge::kFirst}, {Edge::kFirst}, {Edge::kShared}, {Edge::kFirst}, {Edge::kFirst}, {Edge::kShared}, {Edge::kFirst}, {Edge::kFirst}, {Edge::kShared}, {Edge::kFirst}, {Edge::kFirst}, {Edge::kShared}, {Edge::kFirst}, {Edge::kFirst}}});
  s.shape_expr("member.table.powers.shape.definition.first.first.shared.first.first.first.first.first.second.shared.first.shared.first.shared.first.shared.first.shared.first",
      {Root::kValueDefinition, "member.table.powers",
       {{Edge::kFirst}, {Edge::kFirst}, {Edge::kShared}, {Edge::kFirst}, {Edge::kFirst}, {Edge::kFirst}, {Edge::kFirst}, {Edge::kFirst}, {Edge::kSecond}, {Edge::kShared}, {Edge::kFirst}, {Edge::kShared}, {Edge::kFirst}, {Edge::kShared}, {Edge::kFirst}, {Edge::kShared}, {Edge::kFirst}, {Edge::kShared}, {Edge::kFirst}}});
  s.shape_expr("member.table.powers.shape.definition.first.first.shared.first.first.first.first.first.first.first.first.shared.first.first.shared.first.first.shared.first.first",
      {Root::kValueDefinition, "member.table.powers",
       {{Edge::kFirst}, {Edge::kFirst}, {Edge::kShared}, {Edge::kFirst}, {Edge::kFirst}, {Edge::kFirst}, {Edge::kFirst}, {Edge::kFirst}, {Edge::kFirst}, {Edge::kFirst}, {Edge::kFirst}, {Edge::kShared}, {Edge::kFirst}, {Edge::kFirst}, {Edge::kShared}, {Edge::kFirst}, {Edge::kFirst}, {Edge::kShared}, {Edge::kFirst}, {Edge::kFirst}}});
  s.shape_expr("member.table.powers.shape.definition.first.first.shared.first.first.first.first.first.second.shared.first.shared.first.shared.first.shared.first",
      {Root::kValueDefinition, "member.table.powers",
       {{Edge::kFirst}, {Edge::kFirst}, {Edge::kShared}, {Edge::kFirst}, {Edge::kFirst}, {Edge::kFirst}, {Edge::kFirst}, {Edge::kFirst}, {Edge::kSecond}, {Edge::kShared}, {Edge::kFirst}, {Edge::kShared}, {Edge::kFirst}, {Edge::kShared}, {Edge::kFirst}, {Edge::kShared}, {Edge::kFirst}}});
  s.shape_expr("member.table.powers.shape.definition.first.first.shared.first.first.first.first.first.first.first.first.shared.first.first.shared.first.first",
      {Root::kValueDefinition, "member.table.powers",
       {{Edge::kFirst}, {Edge::kFirst}, {Edge::kShared}, {Edge::kFirst}, {Edge::kFirst}, {Edge::kFirst}, {Edge::kFirst}, {Edge::kFirst}, {Edge::kFirst}, {Edge::kFirst}, {Edge::kFirst}, {Edge::kShared}, {Edge::kFirst}, {Edge::kFirst}, {Edge::kShared}, {Edge::kFirst}, {Edge::kFirst}}});
  s.shape_expr("member.table.powers.shape.definition.first.first.shared.first.first.first.first.first.second.shared.first.shared.first.shared.first",
      {Root::kValueDefinition, "member.table.powers",
       {{Edge::kFirst}, {Edge::kFirst}, {Edge::kShared}, {Edge::kFirst}, {Edge::kFirst}, {Edge::kFirst}, {Edge::kFirst}, {Edge::kFirst}, {Edge::kSecond}, {Edge::kShared}, {Edge::kFirst}, {Edge::kShared}, {Edge::kFirst}, {Edge::kShared}, {Edge::kFirst}}});
  s.shape_expr("member.table.powers.shape.definition.first.first.shared.first.first.first.first.first.first.first.first.shared.first.first",
      {Root::kValueDefinition, "member.table.powers",
       {{Edge::kFirst}, {Edge::kFirst}, {Edge::kShared}, {Edge::kFirst}, {Edge::kFirst}, {Edge::kFirst}, {Edge::kFirst}, {Edge::kFirst}, {Edge::kFirst}, {Edge::kFirst}, {Edge::kFirst}, {Edge::kShared}, {Edge::kFirst}, {Edge::kFirst}}});
  s.shape_expr("member.table.powers.shape.definition.first.first.shared.first.first.first.first.first.second.shared.first.shared.first",
      {Root::kValueDefinition, "member.table.powers",
       {{Edge::kFirst}, {Edge::kFirst}, {Edge::kShared}, {Edge::kFirst}, {Edge::kFirst}, {Edge::kFirst}, {Edge::kFirst}, {Edge::kFirst}, {Edge::kSecond}, {Edge::kShared}, {Edge::kFirst}, {Edge::kShared}, {Edge::kFirst}}});
  s.shape_expr("member.table.powers.shape.definition.first.first.shared.first.first.first.first.first.first.first.first",
      {Root::kValueDefinition, "member.table.powers",
       {{Edge::kFirst}, {Edge::kFirst}, {Edge::kShared}, {Edge::kFirst}, {Edge::kFirst}, {Edge::kFirst}, {Edge::kFirst}, {Edge::kFirst}, {Edge::kFirst}, {Edge::kFirst}, {Edge::kFirst}}});
  s.shape_expr("member.table.powers.shape.definition.first.first.shared.first.first.first.first.first.second.shared.first",
      {Root::kValueDefinition, "member.table.powers",
       {{Edge::kFirst}, {Edge::kFirst}, {Edge::kShared}, {Edge::kFirst}, {Edge::kFirst}, {Edge::kFirst}, {Edge::kFirst}, {Edge::kFirst}, {Edge::kSecond}, {Edge::kShared}, {Edge::kFirst}}});
  s.shape_expr("member.table.powers.shape.definition.first.first.shared.first.first.first.first.first.second",
      {Root::kValueDefinition, "member.table.powers",
       {{Edge::kFirst}, {Edge::kFirst}, {Edge::kShared}, {Edge::kFirst}, {Edge::kFirst}, {Edge::kFirst}, {Edge::kFirst}, {Edge::kFirst}, {Edge::kSecond}}});
  s.shape_expr("member.table.powers.shape.definition.first.first.shared.first.first.first.second.first.first",
      {Root::kValueDefinition, "member.table.powers",
       {{Edge::kFirst}, {Edge::kFirst}, {Edge::kShared}, {Edge::kFirst}, {Edge::kFirst}, {Edge::kFirst}, {Edge::kSecond}, {Edge::kFirst}, {Edge::kFirst}}});
  s.shape_expr("member.table.powers.shape.definition.first.first.shared.first.second.first.first.first.first.second",
      {Root::kValueDefinition, "member.table.powers",
       {{Edge::kFirst}, {Edge::kFirst}, {Edge::kShared}, {Edge::kFirst}, {Edge::kSecond}, {Edge::kFirst}, {Edge::kFirst}, {Edge::kFirst}, {Edge::kFirst}, {Edge::kSecond}}});
  s.shape_expr("member.table.powers.shape.definition.first.second.shared.first.first.first.first.first.first.second",
      {Root::kValueDefinition, "member.table.powers",
       {{Edge::kFirst}, {Edge::kSecond}, {Edge::kShared}, {Edge::kFirst}, {Edge::kFirst}, {Edge::kFirst}, {Edge::kFirst}, {Edge::kFirst}, {Edge::kFirst}, {Edge::kSecond}}});
  s.shape_expr("member.table.powers.shape.definition.first.first",
      {Root::kValueDefinition, "member.table.powers",
       {{Edge::kFirst}, {Edge::kFirst}}});
  s.shape_expr("member.table.powers.shape.definition.first.second.shared.first.second.first.second.first.first.second",
      {Root::kValueDefinition, "member.table.powers",
       {{Edge::kFirst}, {Edge::kSecond}, {Edge::kShared}, {Edge::kFirst}, {Edge::kSecond}, {Edge::kFirst}, {Edge::kSecond}, {Edge::kFirst}, {Edge::kFirst}, {Edge::kSecond}}});
  s.shape_expr("member.table.powers.shape.definition.first.second",
      {Root::kValueDefinition, "member.table.powers",
       {{Edge::kFirst}, {Edge::kSecond}}});
  s.shape_expr("member.table.digests.shape.definition.first.first.first.shared.first.first.first.first.first.first.first.first.first.first",
      {Root::kValueDefinition, "member.table.digests",
       {{Edge::kFirst}, {Edge::kFirst}, {Edge::kFirst}, {Edge::kShared}, {Edge::kFirst}, {Edge::kFirst}, {Edge::kFirst}, {Edge::kFirst}, {Edge::kFirst}, {Edge::kFirst}, {Edge::kFirst}, {Edge::kFirst}, {Edge::kFirst}, {Edge::kFirst}}});
  s.shape_expr("member.table.digests.shape.definition.first.first.first",
      {Root::kValueDefinition, "member.table.digests",
       {{Edge::kFirst}, {Edge::kFirst}, {Edge::kFirst}}});
  s.shape_expr("mac.equal.shape.left.shared.first.second.second.first",
      {Root::kPredicateLeft, "mac.equal",
       {{Edge::kShared}, {Edge::kFirst}, {Edge::kSecond}, {Edge::kSecond}, {Edge::kFirst}}});
  s.shape_value("member.select.shape.right",
      {Root::kPredicateRight, "member.select",
       {}});
  s.shape_value("hint.decompose.shape.one",
      {Root::kPredicateLeft, "hint.decompose",
       {{Edge::kFirst}, {Edge::kShared}, {Edge::kFirst}, {Edge::kSecond}, {Edge::kFirst}, {Edge::kFirst}, {Edge::kSecond}, {Edge::kFirst}}});
  s.shape_value("hint.w1_bound.shape.left.argument1.first",
      {Root::kPredicateLeft, "hint.w1_bound",
       {{Edge::kArgument, 1}, {Edge::kFirst}}});
  s.shape_value("signature.relation.q.digit.low",
      {Root::kValueDefinition, "signature.relation.q",
       {{Edge::kFirst}, {Edge::kFirst}}});
  s.shape_value("signature.relation.q.digit.middle",
      {Root::kValueDefinition, "signature.relation.q",
       {{Edge::kFirst}, {Edge::kSecond}, {Edge::kFirst}}});
  s.shape_value("signature.relation.q.digit.high",
      {Root::kValueDefinition, "signature.relation.q",
       {{Edge::kSecond}, {Edge::kFirst}}});
  s.shape_expr("mac.equal.shape.left.shared.first.second.second.second.shared",
      {Root::kPredicateLeft, "mac.equal",
       {{Edge::kShared}, {Edge::kFirst}, {Edge::kSecond}, {Edge::kSecond}, {Edge::kSecond}, {Edge::kShared}}});
  s.shape_expr("member.select.shape.left.second.first.second.first.shared.second.first.shared.second.first.shared.second.first.shared.second.first",
      {Root::kPredicateLeft, "member.select",
       {{Edge::kSecond}, {Edge::kFirst}, {Edge::kSecond}, {Edge::kFirst}, {Edge::kShared}, {Edge::kSecond}, {Edge::kFirst}, {Edge::kShared}, {Edge::kSecond}, {Edge::kFirst}, {Edge::kShared}, {Edge::kSecond}, {Edge::kFirst}, {Edge::kShared}, {Edge::kSecond}, {Edge::kFirst}}});
  s.shape_expr("member.select.shape.left.second.first.second.first.shared.second.first.shared.second.first.shared.second.first",
      {Root::kPredicateLeft, "member.select",
       {{Edge::kSecond}, {Edge::kFirst}, {Edge::kSecond}, {Edge::kFirst}, {Edge::kShared}, {Edge::kSecond}, {Edge::kFirst}, {Edge::kShared}, {Edge::kSecond}, {Edge::kFirst}, {Edge::kShared}, {Edge::kSecond}, {Edge::kFirst}}});
  s.shape_expr("member.select.shape.left.second.first.second.first.shared.second.first.shared.second.first",
      {Root::kPredicateLeft, "member.select",
       {{Edge::kSecond}, {Edge::kFirst}, {Edge::kSecond}, {Edge::kFirst}, {Edge::kShared}, {Edge::kSecond}, {Edge::kFirst}, {Edge::kShared}, {Edge::kSecond}, {Edge::kFirst}}});
  s.shape_expr("member.select.shape.left.second.first.second.first.shared.second.first",
      {Root::kPredicateLeft, "member.select",
       {{Edge::kSecond}, {Edge::kFirst}, {Edge::kSecond}, {Edge::kFirst}, {Edge::kShared}, {Edge::kSecond}, {Edge::kFirst}}});
  s.shape_expr("member.select.shape.left.second.first.second.first",
      {Root::kPredicateLeft, "member.select",
       {{Edge::kSecond}, {Edge::kFirst}, {Edge::kSecond}, {Edge::kFirst}}});
  return {
      {"z.digit.low",
       "z.digit.high",
       "z.completion.low",
       "z.completion.high",
       "hint.offset.digit.low",
       "hint.offset.digit.high",
       "hint.slack.digit.low",
       "hint.slack.digit.high",
       "ring.keys",
       "ring.mu",
       "member.select.index",
       "member.table.gamma",
       "challenge.c",
       "signature.relation.q",
       "member.table.powers",
       "member.table.digests",
       "member.select.shape.right",
       "hint.decompose.shape.one",
       "hint.w1_bound.shape.left.argument1.first",
       "h2c.c_tilde.out",
       "mac.blind",
       "signature.relation.q.digit.low",
       "signature.relation.q.digit.middle",
       "signature.relation.q.digit.high",
       "norm.z.offset"},
      {"signature.relation",
       "member.select.index.boolean",
       "signature.w",
       "norm.z",
       "signature.relation.q",
       "mac.equal",
       "mac.A",
       "range.norm.z.top",
       "mac.blind.boolean",
       "mac.low",
       "mac.high",
       "mac.nowrap",
       "mac",
       "member.select",
       "member.mu.boolean",
       "challenge.c.boolean"},
      {"member.select.shape.left.first.second.second.first.first.first.shared.first.second.first.first",
       "member.select.shape.left.first.second.second.first.first.first",
       "signature.relation.shape.left.first",
       "signature.relation.shape.right.first.second.first.first.first.first",
       "signature.relation.shape.right.first.second.first.first.first.second.first",
       "signature.relation.shape.left.second.first",
       "signature.relation.shape.left.second.second.first",
       "signature.relation.shape.left.second.second.second",
       "mac.equal.shape.right",
       "mac.equal.shape.left.shared.first.second.second.second",
       "mac.equal.shape.left",
       "member.table.powers.shape.definition.first.first.shared.first.first.first.first.first.first.first.first.shared.first.first.shared.first.first.shared.first.first.shared.first.first.shared.first.first.shared.first.first",
       "member.table.powers.shape.definition.first.first.shared.first.first.first.first.first.second.shared.first.shared.first.shared.first.shared.first.shared.first.shared.first.shared.first",
       "member.table.powers.shape.definition.first.first.shared.first.first.first.first.first.first.first.first.shared.first.first.shared.first.first.shared.first.first.shared.first.first.shared.first.first",
       "member.table.powers.shape.definition.first.first.shared.first.first.first.first.first.second.shared.first.shared.first.shared.first.shared.first.shared.first.shared.first",
       "member.table.powers.shape.definition.first.first.shared.first.first.first.first.first.first.first.first.shared.first.first.shared.first.first.shared.first.first.shared.first.first",
       "member.table.powers.shape.definition.first.first.shared.first.first.first.first.first.second.shared.first.shared.first.shared.first.shared.first.shared.first",
       "member.table.powers.shape.definition.first.first.shared.first.first.first.first.first.first.first.first.shared.first.first.shared.first.first.shared.first.first",
       "member.table.powers.shape.definition.first.first.shared.first.first.first.first.first.second.shared.first.shared.first.shared.first.shared.first",
       "member.table.powers.shape.definition.first.first.shared.first.first.first.first.first.first.first.first.shared.first.first.shared.first.first",
       "member.table.powers.shape.definition.first.first.shared.first.first.first.first.first.second.shared.first.shared.first.shared.first",
       "member.table.powers.shape.definition.first.first.shared.first.first.first.first.first.first.first.first.shared.first.first",
       "member.table.powers.shape.definition.first.first.shared.first.first.first.first.first.second.shared.first.shared.first",
       "member.table.powers.shape.definition.first.first.shared.first.first.first.first.first.first.first.first",
       "member.table.powers.shape.definition.first.first.shared.first.first.first.first.first.second.shared.first",
       "member.table.powers.shape.definition.first.first.shared.first.first.first.first.first.second",
       "member.table.powers.shape.definition.first.first.shared.first.first.first.second.first.first",
       "member.table.powers.shape.definition.first.first.shared.first.second.first.first.first.first.second",
       "member.table.powers.shape.definition.first.second.shared.first.first.first.first.first.first.second",
       "member.table.powers.shape.definition.first.first",
       "member.table.powers.shape.definition.first.second.shared.first.second.first.second.first.first.second",
       "member.table.powers.shape.definition.first.second",
       "member.table.digests.shape.definition.first.first.first.shared.first.first.first.first.first.first.first.first.first.first",
       "member.table.digests.shape.definition.first.first.first",
       "mac.equal.shape.left.shared.first.second.second.first",
       "mac.equal.shape.left.shared.first.second.second.second.shared",
       "member.select.shape.left.second.first.second.first.shared.second.first.shared.second.first.shared.second.first.shared.second.first",
       "member.select.shape.left.second.first.second.first.shared.second.first.shared.second.first.shared.second.first",
       "member.select.shape.left.second.first.second.first.shared.second.first.shared.second.first",
       "member.select.shape.left.second.first.second.first.shared.second.first",
       "member.select.shape.left.second.first.second.first"},
      {}};
}

}  // namespace proofs::gordiehowe::examples::mldsa

#endif  // PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_EXAMPLES_MLDSA_MLDSA_SHAPE_INPUTS_H_
