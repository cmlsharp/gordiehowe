// Copyright 2026 Chad Sharp and Paul Grubbs
// SPDX-License-Identifier: Apache-2.0

// Named frontend inputs for the ML-DSA-44 formal relations. Shared expressions
// are selected by semantic application roots and explicit operand paths.
#ifndef PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_EXAMPLES_MLDSA_MLDSA_SHAPE_INPUTS_H_
#define PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_EXAMPLES_MLDSA_MLDSA_SHAPE_INPUTS_H_

#include "gordiehowe/system.h"

namespace proofs::gordiehowe::examples::mldsa {

// The part of the native program at the same parameters that an emulated
// program holds: domain `H` (the hash of mu, c-tilde's absorbs,
// SampleInBall and its memory check), with the native crossing's operand
// of domain `H` (`mac.equal`'s left side), which the emulated crossing reads
// as its own. Its values keep their names.
inline ProgramEmbeddingSpec mldsa_emulated_native_embedding() {
  ProgramEmbeddingSpec d{"native.H", "mldsa-native", {{"h2c.mu.blocks.r0", "h2c.sample.mem.fresh"}}};
  d.exprs = {{ShapeExprSelector::Root::kPredicateLeft, "mac.equal", {}}};
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

// Domain `A`'s gadgets that the ring programs hold, by their predicates:
// the hint's w1 bound, decomposition and interval, the norm range's top
// row, the Booleanities of h, c and the hint's flags, then MIDDLE, then the
// norm of z, the hint's offset and slack and the hint weight. The relation
// is not held: the ring programs read the public key from the committed
// member.
inline std::vector<std::string> mldsa_held_gadgets(const std::string &middle) {
  return {"hint.w1_bound", "hint.decompose", "hint.interval", "range.norm.z.top",
          "h.boolean", "challenge.c.boolean", "hint.w1.boolean", "hint.nonpositive.boolean",
          middle, "norm.z", "hint.offset", "hint.slack", "hint_weight.weight"};
}

// The native program's domain `H` core (c-tilde's absorbs, SampleInBall and
// its memory check) that a ring program holds, with the support and sign of
// H's decoded challenge in the native crossing's operand (`mac.equal`'s
// left side: w1, then support, then sign), which the ring's crossing reads
// in its own operand.
//
// The ring programs commit mu in domain `H` (`mu.words`, `mu`) in place of
// hashing it from tr and the message, so the core's mu (`h2c.mu.out.words`,
// `h2c.mu.out`, the hash's output) is the ring's committed mu. The alias is
// declared here, not inferred: the two values have different names and
// different definitions in their programs, and nothing but this declaration
// says that the ring's committed mu stands for the native hash's output.
inline ProgramEmbeddingSpec mldsa_native_core_embedding(const std::string &name,
                                                        bool gadgets) {
  using Root = ShapeExprSelector::Root;
  using Edge = ShapeExprSelector::Edge;
  ProgramEmbeddingSpec d{name, "mldsa-native", {{"h2c.c_tilde.r0", "h2c.sample.mem.fresh"}}};
  if (gadgets) d.bodies = mldsa_held_gadgets("mac.blind.boolean");
  for (Edge last : {Edge::kFirst, Edge::kSecond})
    d.exprs.push_back({Root::kPredicateLeft, "mac.equal",
                       {{Edge::kShared}, {Edge::kFirst}, {Edge::kSecond}, {last}}});
  d.aliases = {{"h2c.mu.out.words", "mu.words"}, {"h2c.mu.out", "mu"}};
  return d;
}

inline ProgramEmbeddingSpec mldsa_ring_native_embedding() {
  return mldsa_native_core_embedding("native.parts", true);
}

inline ProgramEmbeddingSpec mldsa_ring_carrier_native_embedding() {
  return mldsa_native_core_embedding("native.core", false);
}

// The emulated program's domain `A` gadgets that the carrier holds, with
// the range of w'.
inline ProgramEmbeddingSpec mldsa_ring_carrier_emulated_embedding() {
  ProgramEmbeddingSpec d{"emulated.A", "mldsa-emulated", {}};
  d.bodies = mldsa_held_gadgets("signature.w");
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
  // The last row's last block of a_hat: the end of the checked expression
  // table, which holds the relation's shared expressions (mldsa_ring_carrier.h).
  s.shape_expr("signature.relation.3.shape.left.second.first.first.first.first",
      {Root::kPredicateLeft, "signature.relation.3",
       {{Edge::kSecond}, {Edge::kFirst}, {Edge::kFirst}, {Edge::kFirst}, {Edge::kFirst}}});
  // The relation's constant -q qlo (the rows' E_i = w' - q q' - q qlo).
  s.shape_value("signature.relation.0.shape.left.first.first.first.first.first.first.first.first.second.first",
      {Root::kPredicateLeft, "signature.relation.0",
       {{Edge::kFirst}, {Edge::kFirst}, {Edge::kFirst}, {Edge::kFirst}, {Edge::kFirst}, {Edge::kFirst},
        {Edge::kFirst}, {Edge::kFirst}, {Edge::kSecond}, {Edge::kFirst}}});
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
       "signature.Q",
       "signature.r",
       "signature.relation.0.public0",
       "signature.relation.0.public1",
       "signature.lambda",
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
       "norm.z.offset",
       "signature.relation.0.shape.left.first.first.first.first.first.first.first.first.second.first"},
      {"signature.relation.0",
       "signature.relation.1",
       "signature.relation.2",
       "signature.relation.3",
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
       "member.select.shape.left.second.first.second.first",
       "signature.relation.3.shape.left.second.first.first.first.first"},
      {}};
}

}  // namespace proofs::gordiehowe::examples::mldsa

#endif  // PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_EXAMPLES_MLDSA_MLDSA_SHAPE_INPUTS_H_
