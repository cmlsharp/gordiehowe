// Copyright 2026 Google LLC.
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.
// Modified 2026 by Chad Sharp and Paul Grubbs: hash-policy parameter with a domain-separated statement prefix; id also covers protocol field id, packed bits, aliases and input products

#ifndef PRIVACY_PROOFS_ZK_LIB_SUMCHECK_CIRCUIT_ID_H_
#define PRIVACY_PROOFS_ZK_LIB_SUMCHECK_CIRCUIT_ID_H_

#include <stddef.h>

#include <cstdint>
#include <type_traits>

#include "sumcheck/circuit.h"
#include "util/crypto.h"

namespace proofs {
namespace circuit_id_detail {
template <class F, class = void> struct HasFieldId : std::false_type {};
template <class F>
struct HasFieldId<F, std::void_t<decltype(F::kProtocolFieldId)>>
    : std::true_type {};
} // namespace circuit_id_detail

// This method produces a unique name for a circuit, a digest of the hash
// policy Hash. It does not match the serialization method for the circuit.
// The input is the statement-digest prefix 0x04 || u8(10) || "circuit-id"
// (util/crypto.h), then the field and the circuit.
template <class Field, class Hash = UpstreamHash>
void circuit_id(uint8_t id[/*Hash::kDigestSize*/], const Circuit<Field> &c,
                const Field &F) {
  const uint64_t CHAR2 = 0x2;
  const uint64_t ODD = 0x1;
  Hash sha;
  begin_statement_digest(sha, "circuit-id");
  uint8_t tmp[Field::kBytes];
  if (F.kCharacteristicTwo) {
    // Characteristic two fields are uniquely determined by their length
    // in our codebase.
    sha.Update8(CHAR2); // Indicates binary field.
    sha.Update8(F.kBits);
  } else {
    // Prime fields are determined by -1.
    sha.Update8(ODD); // Indicates odd prime field.
    F.to_bytes_field(tmp, F.mone());
    sha.Update(tmp, sizeof(tmp));
  }
  if constexpr (circuit_id_detail::HasFieldId<Field>::value) {
    sha.Update8(0x70716669656c6431ULL); // pqfield1
    for (auto x : Field::kProtocolFieldId)
      sha.Update8(x);
    sha.Update8(Hash::kDigestSize);
  }
  sha.Update8(c.nv);
  sha.Update8(c.logv);
  sha.Update8(c.nc);
  sha.Update8(c.logc);
  sha.Update8(c.nl);
  sha.Update8(c.ninputs);
  sha.Update8(c.npub_in);
  sha.Update8(c.subfield_boundary);
  // Packed inputs change the relation (their wires are not asserted Boolean),
  // so they are part of the name.  Hashed only when present, so that the
  // names of ordinary circuits are unchanged.
  if (!c.packed_bits.empty()) {
    const uint64_t PACKED = 0x7061636b6564ull; // "packed"
    sha.Update8(PACKED);
    sha.Update8(c.packed_bits.size());
    for (const auto &r : c.packed_bits) {
      sha.Update8(r.first);
      sha.Update8(r.second);
    }
  }
  if (!c.packed_input_aliases.empty()) {
    sha.Update8(0x616c6961736573ULL);
    sha.Update8(c.packed_input_aliases.size());
    for (auto a : c.packed_input_aliases) {
      sha.Update8(a.first);
      sha.Update8(a.second);
    }
  }
  if (!c.input_products.empty()) {
    sha.Update8(0x70726f6475637473ULL);
    sha.Update8(c.input_products.size());
    for (const auto &q : c.input_products)
      for (auto i : q)
        sha.Update8(i);
  }
  for (const auto &layer : c.l) {
    sha.Update8(layer.nw);
    sha.Update8(layer.logw);
    sha.Update8(layer.quad->size());
    for (const auto &ec : *layer.quad) {
      sha.Update8(static_cast<uint64_t>(ec.g));
      sha.Update8(static_cast<uint64_t>(ec.h[0]));
      sha.Update8(static_cast<uint64_t>(ec.h[1]));
      F.to_bytes_field(tmp, ec.v);
      sha.Update(tmp, sizeof(tmp));
    }
  }
  sha.DigestData(id);
}

} // namespace proofs

#endif // PRIVACY_PROOFS_ZK_LIB_SUMCHECK_CIRCUIT_ID_H_
