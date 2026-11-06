// Copyright 2026 Chad Sharp and Paul Grubbs
// SPDX-License-Identifier: Apache-2.0

// Semantic source-value roles for the ML-DSA possession and ring relations.
// These names resolve after compilation; realization digits are not source roles.

#ifndef PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_EXAMPLES_MLDSA_MLDSA_SOURCE_ROLES_H_
#define PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_EXAMPLES_MLDSA_MLDSA_SOURCE_ROLES_H_

#include <algorithm>
#include <cstddef>
#include <string>
#include <type_traits>

#include "gordiehowe/examples/mldsa/mldsa_params.h"
#include "gordiehowe/system.h"

namespace proofs::gordiehowe::examples::mldsa {

enum class SourceFamily { kPossession, kRingNative, kRingCarrier };

// Hash-word slots zero and one are w1 and mu. Subsequent slots enumerate
// permutation rounds. The ring's supplied mu occupies the same input slot as
// the possession hash's output; its absent mu permutation retains a reserved slot.
template <class S>
void mldsa_source_roles(const Scope &s, NamedShapeInputs &shapes, SourceFamily family,
                        size_t mu_blocks = 1, size_t ctx_bytes = 0,
                        const std::string &key_a_name = "key.a_hat") {
  // The checked application semantics currently cover ML-DSA-44. Other
  // parameter sets retain their existing metadata-free compilation.
  if constexpr (!std::is_same_v<S, MLDSA44>) return;
  switch (family) {
    case SourceFamily::kPossession:
    case SourceFamily::kRingNative:
    case SourceFamily::kRingCarrier:
      break;
    default:
      fail("ML-DSA source roles: unknown family");
  }
  const auto value = [&](const std::string &name) {
    if (std::find(shapes.values.begin(), shapes.values.end(), name) == shapes.values.end())
      shapes.values.push_back(name);
  };
  const auto role = [&](const std::string &name, SourceRole tag, size_t slot) {
    s.source_role(name, tag, slot);
    value(name);
  };
  const bool ring = family != SourceFamily::kPossession;
  const char *a_names[] = {"z", "h", "challenge.c", "signature.w", "hint.w1",
                           "hint.nonpositive", "hint.offset", "hint.slack"};
  for (size_t i = 0; i < 8; ++i)
    role(a_names[i], SourceRole::kAWitness, i);
  if (family == SourceFamily::kRingCarrier)
    role("signature.relation.q", SourceRole::kCarry, 0);

  const char *selection_names[] = {
      "h2c.sample.select.j", "h2c.sample.select.threshold.words",
      "h2c.sample.mem.read_value", "h2c.sample.mem.read_origin",
      "h2c.sample.mem.c_enc", "h2c.sample.mem.final_origin",
      "h2c.sample.mem.unit", "h2c.sample.mem.origin"};
  for (size_t i = 0; i < 8; ++i)
    role(selection_names[i], SourceRole::kSelection, i);
  value("h2c.sample.select.threshold");
  value("w1");
  value(ring ? "mu" : "h2c.mu.out");
  role("w1.words", SourceRole::kHashWord, 0);
  role(ring ? "mu.words" : "h2c.mu.out.words", SourceRole::kHashWord, 1);

  const auto rounds = [&](const std::string &name, size_t blocks, size_t first) {
    for (size_t r = 0; r < 24 * blocks; ++r) {
      const std::string output = name + ".r" + std::to_string(r) + ".value";
      role(output + ".words", SourceRole::kHashWord, 2 + 24 * first + r);
      value(output);
    }
  };
  const size_t c_blocks = (8 * kMuBytes + S::kW1Bits) / 1088 + 1;
  const size_t sib_blocks = (kSibBytes + 135) / 136;
  if (ring) {
    role("member.a_hat", SourceRole::kRingSigma, 0);
    role("member.t1", SourceRole::kRingSigma, 1);
    role("member.mu", SourceRole::kRingSigma, 2);
    role("member.select.index", SourceRole::kSelection, 8);
    role("ring.tr", SourceRole::kStmtMember, 0);
    role("ring.keys", SourceRole::kStmtMember, 1);
    role("ring.mu", SourceRole::kStmtMember, 2);
    role("member.table.powers", SourceRole::kInput, 0);
    role("member.table.digests", SourceRole::kInput, 1);
    mu_blocks = 1;
  } else {
    if (mu_blocks == 0) fail("ML-DSA source roles: empty mu permutation range");
    role("msg", SourceRole::kHashBit, 0);
    role("msg.in_message", SourceRole::kHashBit, 1);
    role(key_a_name, SourceRole::kStmtMember, 0);
    role("key.t1", SourceRole::kStmtMember, 1);
    role("tr", SourceRole::kInput, 0);
    if (ctx_bytes != 0) role("ctx", SourceRole::kInput, 1);
    rounds("h2c.mu.blocks", mu_blocks, 0);
  }
  rounds("h2c.c_tilde", c_blocks, mu_blocks);
  rounds("h2c.sib", sib_blocks, mu_blocks + c_blocks);
}

}  // namespace proofs::gordiehowe::examples::mldsa

#endif  // PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_EXAMPLES_MLDSA_MLDSA_SOURCE_ROLES_H_
