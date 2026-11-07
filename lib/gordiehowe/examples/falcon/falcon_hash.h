// Copyright 2026 Chad Sharp and Paul Grubbs
// SPDX-License-Identifier: Apache-2.0

// GordieHowe: domain H of the Falcon proofs of possession of a parameter
// set S (falcon_params.h), which both arms share. Domain H is a binary
// field with the GF(2^16) subfield. It commits the witness's 40-byte nonce
// and the message, whose private length L is at most the relation's
// maximum (lib/message.h), and computes HashToPoint: SHAKE256 of
// nonce || message in one Keccak batch, then the first n of S::kSamples
// 16-bit samples below 5q (lib/cutoff_select.h). Each arm copies the
// selected samples c_H into its domain A.
//
// This header also holds the proof of possession's inputs, FalconInputs<S>
// (FalconStatement: the key's NTT coordinates; FalconWitness: nonce,
// message part, length, s2); falcon_builders.h builds them.

#ifndef PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_EXAMPLES_FALCON_FALCON_HASH_H_
#define PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_EXAMPLES_FALCON_FALCON_HASH_H_

#include <algorithm>
#include <array>
#include <cstddef>
#include <cstdint>
#include <string>
#include <type_traits>
#include <vector>

#include "gordiehowe/core.h"
#include "gordiehowe/examples/falcon/falcon_params.h"
#include "gordiehowe/lib/cutoff_select.h"
#include "gordiehowe/lib/keccak.h"
#include "gordiehowe/lib/message.h"
#include "gordiehowe/lib/select.h"
#include "gordiehowe/relation.h"
#include "gordiehowe/system.h"

namespace proofs::gordiehowe::examples::falcon {

// The hash buffer of messages of at most MAX bytes: the nonce in front of
// the message part.
inline lib::message::Layout falcon_layout(size_t max) {
  return lib::message::shake256_layout(kNonceBytes, max);
}

// HashToPoint(nonce || message) of set S in scope S of domain H for a
// message of private length in the part MESSAGE of LAYOUT's buffer, with
// the buffer's in-message flags IN_MESSAGE: the selected samples c_H,
// Bit [n, 16].
template <class Set, class D, class F, class P1, class P2, class P3>
Ref<F, Bit, Committed> hash_to_point(const Scope &s, D &H,
                                     Ref<F, Bit, P1> nonce,
                                     Ref<F, Bit, P2> message,
                                     Ref<F, Bit, P3> in_message,
                                     const lib::message::Layout &layout) {
  const auto input = nonce.concat(message).named(s.scoped("input"));
  const auto keccak = lib::keccak::keccak_batch(s[H], "keccak");
  const auto out = lib::message::shake256_message(
      keccak, "shake", layout, lib::keccak::sponge_input(input), in_message,
      Set::kOutBytes);
  // Falcon reads sample i from bytes 2i, 2i + 1 big-endian: its low byte
  // is byte 2i + 1, its high byte byte 2i.
  const auto stream = out.reshape({Set::kSamples, 2, 8})
                          .reverse(1)
                          .reshape({Set::kSamples, 16})
                          .named(s.scoped("stream"));
  return lib::select::select_first_n(s, H, stream,
                                     lib::select::Cutoff{uint32_t(kCutoff)},
                                     lib::select::Count{Set::kN})
      .raw;
}

// Domain H and the selected samples, which the caller reads.
template <class D, class F>
struct FalconHashDomain {
  D &H;
  Ref<F, Bit, Committed> c_H;
};

// Domain H of profile H_PROFILE in system CS, the Witness members NONCE
// (kNonceBytes bytes) and MESSAGE (falcon_layout(MAX)'s part) committed in
// it as bits, the in-message flags from the Witness member LENGTH, and
// HashToPoint of set S.
template <class S, class Sys, class HP, class NM, class MM, class LM>
auto falcon_hash_domain(Sys &cs, const HP &h_profile, const In<NM> &nonce,
                      const In<MM> &message, const In<LM> &length,
                      size_t max) {
  auto &H = cs.domain(h_profile, "H");
  using D = std::decay_t<decltype(H)>;
  using F = std::decay_t<decltype(H.field())>;
  const lib::message::Layout layout = falcon_layout(max);
  const auto nonce_bits = H.priv(nonce).flat();
  if (nonce_bits.n != 8 * kNonceBytes)
    fail("falcon_hash_domain: a nonce of " + std::to_string(nonce_bits.n / 8) +
         " bytes");
  const auto msg = lib::message::committed_message(H, message, layout, length,
                                                   "message.in_message");
  const auto c_H = hash_to_point<S>(cs.scope("h2p"), H, nonce_bits, msg.bits,
                                 msg.flags, layout);
  return FalconHashDomain<D, F>{H, c_H};
}

// The proof of possession's inputs of set S, both arms. The statement:
// the key's n NTT coordinates, each canonical below q (a codec). The
// witness: the nonce, the message's part of the hash buffer
// (falcon_layout(MAX), MAX fixed per relation by the shape value), the
// message length L <= MAX and s2's coefficients, canonical in [0, q).
template <class S>
struct FalconInputs {
  template <template <class> class F>
  struct Statement {
    F<std::array<uint16_t, S::kN>> hhat;
  };
  template <template <class> class F>
  struct Witness {
    F<std::array<uint8_t, kNonceBytes>> nonce;
    F<std::vector<uint8_t>> message;
    F<uint16_t> msg_length;
    F<std::array<uint16_t, S::kN>> s2;
  };
};
template <class S, template <class> class F>
using FalconStatement = typename FalconInputs<S>::template Statement<F>;
template <class S, template <class> class F>
using FalconWitness = typename FalconInputs<S>::template Witness<F>;

// The shape of the witness for messages of at most MAX bytes.
template <class S>
FalconWitness<S, Value> falcon_witness_shape(size_t max) {
  FalconWitness<S, Value> w{};
  w.message.resize(falcon_layout(max).part);
  return w;
}

// Named finite metadata of the Falcon512 hash and selection, shared by the
// checked frontends: the rounds as one family, their constants, the padding,
// the selection and the hash's and selection's source roles.
inline void falcon_hash_shape_inputs(const Scope &cs) {
  using Root = ShapeExprSelector::Root;
  using Edge = ShapeExprSelector::Edge;
  cs.shape_expr("h2p.shake.padding.suffix.shape.left.second.first.shared.first.first.first.first.shared.first",
      {Root::kPredicateLeft, "h2p.shake.padding.suffix", {{Edge::kSecond}, {Edge::kFirst}, {Edge::kShared}, {Edge::kFirst}, {Edge::kFirst}, {Edge::kFirst}, {Edge::kFirst}, {Edge::kShared}, {Edge::kFirst}}});
  cs.shape_expr("h2p.shake.padding.suffix.shape.left.second.first.shared.first.first.first.first",
      {Root::kPredicateLeft, "h2p.shake.padding.suffix", {{Edge::kSecond}, {Edge::kFirst}, {Edge::kShared}, {Edge::kFirst}, {Edge::kFirst}, {Edge::kFirst}, {Edge::kFirst}}});
  cs.shape_expr("h2p.shake.blocks.r0.shape.left.second.first.first.shared.first.first.first",
      {Root::kPredicateLeft, "h2p.shake.blocks.r0", {{Edge::kSecond}, {Edge::kFirst}, {Edge::kFirst}, {Edge::kShared}, {Edge::kFirst}, {Edge::kFirst}, {Edge::kFirst}}});
  cs.shape_expr("h2p.shake.padding.suffix.shape.left.first.first",
      {Root::kPredicateLeft, "h2p.shake.padding.suffix", {{Edge::kFirst}, {Edge::kFirst}}});
  cs.shape_expr("h2p.shake.padding.suffix.shape.left.second.first",
      {Root::kPredicateLeft, "h2p.shake.padding.suffix", {{Edge::kSecond}, {Edge::kFirst}}});
  cs.shape_expr("h2p.shake.padding.output.shape.left.first.first.shared.first.first",
      {Root::kPredicateLeft, "h2p.shake.padding.output", {{Edge::kFirst}, {Edge::kFirst}, {Edge::kShared}, {Edge::kFirst}, {Edge::kFirst}}});
  cs.shape_expr("h2p.shake.padding.output.shape.left.first.first",
      {Root::kPredicateLeft, "h2p.shake.padding.output", {{Edge::kFirst}, {Edge::kFirst}}});
  cs.shape_expr("h2p.shake.padding.output.shape.left.second.second.first",
      {Root::kPredicateLeft, "h2p.shake.padding.output", {{Edge::kSecond}, {Edge::kSecond}, {Edge::kFirst}}});
  cs.shape_expr("h2p.shake.squeeze.r0.shape.left.second.first.first.shared.first.first.first",
      {Root::kPredicateLeft, "h2p.shake.squeeze.r0", {{Edge::kSecond}, {Edge::kFirst}, {Edge::kFirst}, {Edge::kShared}, {Edge::kFirst}, {Edge::kFirst}, {Edge::kFirst}}});
  cs.shape_expr("h2p.select.route.shape.left.first.first.first.shared.first.first.first.shared.argument.0",
      {Root::kPredicateLeft, "h2p.select.route", {{Edge::kFirst}, {Edge::kFirst}, {Edge::kFirst}, {Edge::kShared}, {Edge::kFirst}, {Edge::kFirst}, {Edge::kFirst}, {Edge::kShared}, {Edge::kArgument, 0}}});
  cs.shape_expr("h2p.select.route.shape.left.first.first.first",
      {Root::kPredicateLeft, "h2p.select.route",
       {{Edge::kFirst}, {Edge::kFirst}, {Edge::kFirst}}});
  cs.shape_expr("h2p.select.route.shape.left.first.first.first.shared.first.first.first",
      {Root::kPredicateLeft, "h2p.select.route",
       {{Edge::kFirst}, {Edge::kFirst}, {Edge::kFirst}, {Edge::kShared}, {Edge::kFirst},
        {Edge::kFirst}, {Edge::kFirst}}});
  cs.shape_value("h2p.shake.blocks.r0.constant.left.second.first.first.shared.first.first.first.shared.first.first.second",
      {Root::kPredicateLeft, "h2p.shake.blocks.r0", {{Edge::kSecond}, {Edge::kFirst}, {Edge::kFirst}, {Edge::kShared}, {Edge::kFirst}, {Edge::kFirst}, {Edge::kFirst}, {Edge::kShared}, {Edge::kFirst}, {Edge::kFirst}, {Edge::kSecond}}});
  cs.shape_value("h2p.shake.blocks.r0.constant.left.second.first.second.first.first",
      {Root::kPredicateLeft, "h2p.shake.blocks.r0", {{Edge::kSecond}, {Edge::kFirst}, {Edge::kSecond}, {Edge::kFirst}, {Edge::kFirst}}});
  cs.shape_value("h2p.shake.blocks.r0.constant.left.second.second",
      {Root::kPredicateLeft, "h2p.shake.blocks.r0", {{Edge::kSecond}, {Edge::kSecond}}});
  cs.shape_value("h2p.shake.blocks.r0.constant.right",
      {Root::kPredicateRight, "h2p.shake.blocks.r0", {}});
  cs.shape_value("h2p.shake.blocks.r1.constant.left.second.second",
      {Root::kPredicateLeft, "h2p.shake.blocks.r1", {{Edge::kSecond}, {Edge::kSecond}}});
  cs.shape_value("h2p.shake.blocks.r2.constant.left.second.second",
      {Root::kPredicateLeft, "h2p.shake.blocks.r2", {{Edge::kSecond}, {Edge::kSecond}}});
  cs.shape_value("h2p.shake.blocks.r3.constant.left.second.second",
      {Root::kPredicateLeft, "h2p.shake.blocks.r3", {{Edge::kSecond}, {Edge::kSecond}}});
  cs.shape_value("h2p.shake.blocks.r4.constant.left.second.second",
      {Root::kPredicateLeft, "h2p.shake.blocks.r4", {{Edge::kSecond}, {Edge::kSecond}}});
  cs.shape_value("h2p.shake.blocks.r5.constant.left.second.second",
      {Root::kPredicateLeft, "h2p.shake.blocks.r5", {{Edge::kSecond}, {Edge::kSecond}}});
  cs.shape_value("h2p.shake.blocks.r6.constant.left.second.second",
      {Root::kPredicateLeft, "h2p.shake.blocks.r6", {{Edge::kSecond}, {Edge::kSecond}}});
  cs.shape_value("h2p.shake.blocks.r7.constant.left.second.second",
      {Root::kPredicateLeft, "h2p.shake.blocks.r7", {{Edge::kSecond}, {Edge::kSecond}}});
  cs.shape_value("h2p.shake.blocks.r8.constant.left.second.second",
      {Root::kPredicateLeft, "h2p.shake.blocks.r8", {{Edge::kSecond}, {Edge::kSecond}}});
  cs.shape_value("h2p.shake.blocks.r9.constant.left.second.second",
      {Root::kPredicateLeft, "h2p.shake.blocks.r9", {{Edge::kSecond}, {Edge::kSecond}}});
  cs.shape_value("h2p.shake.blocks.r10.constant.left.second.second",
      {Root::kPredicateLeft, "h2p.shake.blocks.r10", {{Edge::kSecond}, {Edge::kSecond}}});
  cs.shape_value("h2p.shake.blocks.r11.constant.left.second.second",
      {Root::kPredicateLeft, "h2p.shake.blocks.r11", {{Edge::kSecond}, {Edge::kSecond}}});
  cs.shape_value("h2p.shake.blocks.r12.constant.left.second.second",
      {Root::kPredicateLeft, "h2p.shake.blocks.r12", {{Edge::kSecond}, {Edge::kSecond}}});
  cs.shape_value("h2p.shake.blocks.r13.constant.left.second.second",
      {Root::kPredicateLeft, "h2p.shake.blocks.r13", {{Edge::kSecond}, {Edge::kSecond}}});
  cs.shape_value("h2p.shake.blocks.r14.constant.left.second.second",
      {Root::kPredicateLeft, "h2p.shake.blocks.r14", {{Edge::kSecond}, {Edge::kSecond}}});
  cs.shape_value("h2p.shake.blocks.r15.constant.left.second.second",
      {Root::kPredicateLeft, "h2p.shake.blocks.r15", {{Edge::kSecond}, {Edge::kSecond}}});
  cs.shape_value("h2p.shake.blocks.r16.constant.left.second.second",
      {Root::kPredicateLeft, "h2p.shake.blocks.r16", {{Edge::kSecond}, {Edge::kSecond}}});
  cs.shape_value("h2p.shake.blocks.r17.constant.left.second.second",
      {Root::kPredicateLeft, "h2p.shake.blocks.r17", {{Edge::kSecond}, {Edge::kSecond}}});
  cs.shape_value("h2p.shake.blocks.r18.constant.left.second.second",
      {Root::kPredicateLeft, "h2p.shake.blocks.r18", {{Edge::kSecond}, {Edge::kSecond}}});
  cs.shape_value("h2p.shake.blocks.r19.constant.left.second.second",
      {Root::kPredicateLeft, "h2p.shake.blocks.r19", {{Edge::kSecond}, {Edge::kSecond}}});
  cs.shape_value("h2p.shake.blocks.r21.constant.left.second.second",
      {Root::kPredicateLeft, "h2p.shake.blocks.r21", {{Edge::kSecond}, {Edge::kSecond}}});
  cs.shape_value("h2p.shake.blocks.r23.constant.left.second.second",
      {Root::kPredicateLeft, "h2p.shake.blocks.r23", {{Edge::kSecond}, {Edge::kSecond}}});
  cs.shape_value("h2p.shake.padding.min.constant.left.second",
      {Root::kPredicateLeft, "h2p.shake.padding.min", {{Edge::kSecond}}});
  cs.shape_value("h2p.shake.padding.monotone.constant.right",
      {Root::kPredicateRight, "h2p.shake.padding.monotone", {}});
  cs.shape_value("h2p.shake.padding.max.constant.right",
      {Root::kPredicateRight, "h2p.shake.padding.max", {}});
  cs.shape_value("h2p.shake.padding.suffix.constant.left.second.first.shared.first.second.first",
      {Root::kPredicateLeft, "h2p.shake.padding.suffix", {{Edge::kSecond}, {Edge::kFirst}, {Edge::kShared}, {Edge::kFirst}, {Edge::kSecond}, {Edge::kFirst}}});
  cs.shape_value("h2p.shake.padding.suffix.constant.left.second.second",
      {Root::kPredicateLeft, "h2p.shake.padding.suffix", {{Edge::kSecond}, {Edge::kSecond}}});
  cs.shape_value("h2p.shake.padding.suffix.constant.right",
      {Root::kPredicateRight, "h2p.shake.padding.suffix", {}});
  cs.shape_value("h2p.shake.padding.zeros.constant.left.second.second.second",
      {Root::kPredicateLeft, "h2p.shake.padding.zeros", {{Edge::kSecond}, {Edge::kSecond}, {Edge::kSecond}}});
  cs.shape_value("h2p.select.route.constant.left.first.first.first.shared.first.first.first.shared.argument.1.first",
      {Root::kPredicateLeft, "h2p.select.route", {{Edge::kFirst}, {Edge::kFirst}, {Edge::kFirst}, {Edge::kShared}, {Edge::kFirst}, {Edge::kFirst}, {Edge::kFirst}, {Edge::kShared}, {Edge::kArgument, 1}, {Edge::kFirst}}});
  cs.shape_value("h2p.select.route.constant.left.first.first.first.shared.first.second.second.first",
      {Root::kPredicateLeft, "h2p.select.route", {{Edge::kFirst}, {Edge::kFirst}, {Edge::kFirst}, {Edge::kShared}, {Edge::kFirst}, {Edge::kSecond}, {Edge::kSecond}, {Edge::kFirst}}});
  cs.shape_value("h2p.select.step.constant.left.second.second.second.first",
      {Root::kPredicateLeft, "h2p.select.step", {{Edge::kSecond}, {Edge::kSecond}, {Edge::kSecond}, {Edge::kFirst}}});
  cs.shape_value("h2p.select.step.constant.right",
      {Root::kPredicateRight, "h2p.select.step", {}});
  cs.shape_value("h2p.select.done.constant.left.second.second.first",
      {Root::kPredicateLeft, "h2p.select.done", {{Edge::kSecond}, {Edge::kSecond}, {Edge::kFirst}}});
  cs.shape_value("h2p.select.done.constant.right",
      {Root::kPredicateRight, "h2p.select.done", {}});
  cs.shape_value("h2p.select.route.constant.left.second.first.second.second.first.first.second.first",
      {Root::kPredicateLeft, "h2p.select.route", {{Edge::kSecond}, {Edge::kFirst}, {Edge::kSecond}, {Edge::kSecond}, {Edge::kFirst}, {Edge::kFirst}, {Edge::kSecond}, {Edge::kFirst}}});
  cs.shape_value("h2p.select.route.constant.left.second.first.second.first",
      {Root::kPredicateLeft, "h2p.select.route", {{Edge::kSecond}, {Edge::kFirst}, {Edge::kSecond}, {Edge::kFirst}}});
  NamedShapeInputs inputs{
    {
      "h2p.shake.out.p1", "h2p.shake.out.p2", "h2p.shake.out.p3", "h2p.shake.out.p4",
      "h2p.shake.out.p5", "h2p.shake.out.p6", "h2p.shake.out.p7", "h2p.shake.out.p8",
      "h2p.shake.out.p9", "h2p.shake.out.p10", "h2p.select.delta"
    },
    {
      "h2p.shake.padding.monotone", "h2p.shake.padding.max", "h2p.shake.padding.min",
      "h2p.shake.padding.suffix", "h2p.shake.padding.zeros", "h2p.shake.padding.output",
      "h2p.select.start", "h2p.select.step", "h2p.select.done", "h2p.select.route"
    },
    {
      "h2p.shake.padding.suffix.shape.left.second.first.shared.first.first.first.first.shared.first",
      "h2p.shake.padding.suffix.shape.left.second.first.shared.first.first.first.first",
      "h2p.shake.blocks.r0.shape.left.second.first.first.shared.first.first.first",
      "h2p.shake.padding.suffix.shape.left.first.first",
      "h2p.shake.padding.suffix.shape.left.second.first",
      "h2p.shake.padding.output.shape.left.first.first.shared.first.first",
      "h2p.shake.padding.output.shape.left.first.first",
      "h2p.shake.padding.output.shape.left.second.second.first",
      "h2p.shake.squeeze.r0.shape.left.second.first.first.shared.first.first.first",
      "h2p.select.route.shape.left.first.first.first.shared.first.first.first.shared.argument.0"
    },
    {
      "h2p.shake.padding.monotone", "h2p.shake.padding.max", "h2p.shake.padding.min",
      "h2p.shake.padding.suffix", "h2p.shake.padding.zeros", "h2p.shake.padding.output"
    }
  };
  const auto request_value = [&inputs](const std::string &name) {
    if (std::find(inputs.values.begin(), inputs.values.end(), name) == inputs.values.end())
      inputs.values.push_back(name);
  };
  const auto role = [&cs, &request_value](const std::string &name, SourceRole tag, size_t slot) {
    request_value(name);
    cs.source_role(name, tag, slot);
  };
  role("nonce", SourceRole::kHashBit, 0);
  role("message", SourceRole::kHashBit, 1);
  role("message.in_message", SourceRole::kHashBit, 2);
  role("h2p.shake.state.words", SourceRole::kHashWord, 0);
  request_value("h2p.shake.state");
  ShapeFamilyInput rounds{"rounds", {}};
  for (size_t p = 0; p < 11; ++p) {
    for (size_t t = 0; t < 24; ++t) {
      const std::string round = p == 0
          ? "h2p.shake.blocks.r" + std::to_string(t)
          : "h2p.shake.squeeze.r" + std::to_string(24 * (p - 1) + t);
      cs.source_role(round + ".value.words", SourceRole::kHashWord, 1 + 24 * p + t);
      cs.shape_expr(round + ".linear",
          {Root::kPredicateLeft, round,
           {{Edge::kSecond}, {Edge::kFirst}, {Edge::kFirst}}});
      cs.shape_expr(round + ".columns",
          {Root::kPredicateLeft, round,
           {{Edge::kSecond}, {Edge::kFirst}, {Edge::kFirst}, {Edge::kShared},
            {Edge::kFirst}, {Edge::kFirst}, {Edge::kSecond}, {Edge::kFirst},
            {Edge::kFirst}}});
      rounds.rows.push_back({{round}, {round + ".linear", round + ".columns"},
                             {round + ".value", round + ".value.words"}});
    }
  }
  inputs.families.push_back(std::move(rounds));
  role("h2p.select.raw.words", SourceRole::kSelection, 0);
  role("h2p.select.count", SourceRole::kSelection, 1);
  role("h2p.select.full", SourceRole::kSelection, 2);
  request_value("h2p.select.raw");
  inputs.exprs.push_back("h2p.select.route.shape.left.first.first.first");
  inputs.exprs.push_back("h2p.select.route.shape.left.first.first.first.shared.first.first.first");
  request_value("h2p.shake.state");
  request_value("h2p.select.raw");
  request_value("h2p.shake.blocks.r0.constant.left.second.first.first.shared.first.first.first.shared.first.first.second");
  request_value("h2p.shake.blocks.r0.constant.left.second.first.second.first.first");
  request_value("h2p.shake.blocks.r0.constant.left.second.second");
  request_value("h2p.shake.blocks.r0.constant.right");
  request_value("h2p.shake.blocks.r1.constant.left.second.second");
  request_value("h2p.shake.blocks.r2.constant.left.second.second");
  request_value("h2p.shake.blocks.r3.constant.left.second.second");
  request_value("h2p.shake.blocks.r4.constant.left.second.second");
  request_value("h2p.shake.blocks.r5.constant.left.second.second");
  request_value("h2p.shake.blocks.r6.constant.left.second.second");
  request_value("h2p.shake.blocks.r7.constant.left.second.second");
  request_value("h2p.shake.blocks.r8.constant.left.second.second");
  request_value("h2p.shake.blocks.r9.constant.left.second.second");
  request_value("h2p.shake.blocks.r10.constant.left.second.second");
  request_value("h2p.shake.blocks.r11.constant.left.second.second");
  request_value("h2p.shake.blocks.r12.constant.left.second.second");
  request_value("h2p.shake.blocks.r13.constant.left.second.second");
  request_value("h2p.shake.blocks.r14.constant.left.second.second");
  request_value("h2p.shake.blocks.r15.constant.left.second.second");
  request_value("h2p.shake.blocks.r16.constant.left.second.second");
  request_value("h2p.shake.blocks.r17.constant.left.second.second");
  request_value("h2p.shake.blocks.r18.constant.left.second.second");
  request_value("h2p.shake.blocks.r19.constant.left.second.second");
  request_value("h2p.shake.blocks.r21.constant.left.second.second");
  request_value("h2p.shake.blocks.r23.constant.left.second.second");
  request_value("h2p.shake.padding.min.constant.left.second");
  request_value("h2p.shake.padding.monotone.constant.right");
  request_value("h2p.shake.padding.max.constant.right");
  request_value("h2p.shake.padding.suffix.constant.left.second.first.shared.first.second.first");
  request_value("h2p.shake.padding.suffix.constant.left.second.second");
  request_value("h2p.shake.padding.suffix.constant.right");
  request_value("h2p.shake.padding.zeros.constant.left.second.second.second");
  request_value("h2p.select.route.constant.left.first.first.first.shared.first.first.first.shared.argument.1.first");
  request_value("h2p.select.route.constant.left.first.first.first.shared.first.second.second.first");
  request_value("h2p.select.step.constant.left.second.second.second.first");
  request_value("h2p.select.step.constant.right");
  request_value("h2p.select.done.constant.left.second.second.first");
  request_value("h2p.select.done.constant.right");
  request_value("h2p.select.route.constant.left.second.first.second.second.first.first.second.first");
  request_value("h2p.select.route.constant.left.second.first.second.first");
  cs.shape_inputs(inputs);
}

}  // namespace proofs::gordiehowe::examples::falcon

#endif  // PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_EXAMPLES_FALCON_FALCON_HASH_H_
