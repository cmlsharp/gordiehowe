// Copyright 2026 Chad Sharp and Paul Grubbs
// SPDX-License-Identifier: Apache-2.0

// GordieHowe: the storage and packing plan of a domain, and
// the subfield step that establishes Subfield membership.
//
// A domain whose field supports relative packing (ExtensionTraits) commits
// its subfield cells packed relative to the source subfield S: [K:S]
// coordinates per ambient word (zk/zk_extension_packed.h). Every linear row
// of the opening reaches the coordinates through trace forms and masked
// measurements, and a coordinate decoded from an ambient word lies in S by
// construction. What the verifier must still check is that the prefix rows,
// the masks of those measurements, lie in S. PrefixSubfieldTest is that
// check, run once per domain on the prefix rows as a unit.
//
// In characteristic 2 with a GF(2^16) source subfield, every Bit cell and
// GF(2) pad is also bit packed, sixteen to a subfield word (zk/zk_packed.h):
// the circuit reads one wire per bit, the commitment holds the word, and a
// bit is the trace of the word against the dual basis, so it is a bit by
// construction and needs no b*b = b check. This holds whichever constraints
// read the bit: an affine row's terms on packed bits or view bits are claims
// on the bit node, which its stage (GF(2) < GF(2^16), squaring-chain masks)
// opens together with the GKR input claim when there is one
// (CompiledDomain::extra_nodes). A bit view of a Subfield word is a group of
// sixteen such wires aliased onto the word itself
// (Circuit::packed_input_aliases): its bits are the word's canonical
// coordinates, and it allocates no second witness. A word of a larger
// subfield on the packing tree's path above the bit node (a GF(2^32) word
// over GF(2) < GF(2^16) < GF(2^32)) has one wire per bit, D / 16 groups,
// decoded through the nodes between (TreeInputs::composed, ComposedBits).
//
// Storage of a packed domain (circuit inputs, in order):
//   0, public slots
//   unpacked subfield cells   Subfield cells and subfield pads
//   alignment                 zero inputs up to a multiple of 16, each
//                             asserted zero by a circuit constraint
//   bit views                 D aliased wires per viewed word of GF(2^D)
//   packed bits               Bit cells and GF(2) pads, then zero bits up
//                             to a multiple of 16
//   ambient cells, batch pads
// The committed coordinates follow PackedLayout (packed words, then the
// unpacked subfield inputs, then the full-field inputs), and relative packing
// packs everything before the full-field inputs.

#ifndef PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_COMPILER_PACKING_H_
#define PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_COMPILER_PACKING_H_

#include <array>
#include <cstddef>
#include <cstdint>
#include <string>
#include <utility>
#include <vector>

#include "gordiehowe/subfield.h"
#include "ligero/ligero_param.h"
#include "sumcheck/circuit.h"
#include "zk/zk_common.h"
#include "zk/zk_extension_packed.h"

namespace proofs::gordiehowe::compiler {

// Whether a domain over F packs its subfield cells relative to the source
// subfield, and whether it also packs bits sixteen to a subfield word.
template <class F>
constexpr bool relative_packing() {
  return domain_subfield<F>::kRelativePacking;
}
template <class F>
constexpr bool bit_packing() {
  return domain_subfield<F>::kBitPacking;
}

// The canonical 16-bit coordinates of a subfield word.
template <class F>
uint16_t word_bits(const F &f, const typename F::Elt &w) {
  uint8_t b[domain_subfield<F>::kBytes];
  subfield_to_bytes(f, b, w);
  return uint16_t(b[0] | (b[1] << 8));
}

// The canonical 16-bit coordinates of GF(2^16) subfield words, by the
// inverse of a 16 x 16 bit matrix instead of a subfield solve: 16 pivot
// bits of the word's field bytes determine its coordinates on the
// subfield, and the rows of the inverse are combined under masks of those
// bits (no branch on them, no table indexed by them). Prover side only: a word
// outside the subfield decodes to some value without an error (the
// commitment refuses such a word).
template <class F>
class SubfieldDecoder {
  using Bytes = std::array<uint8_t, F::kBytes>;

 public:
  explicit SubfieldDecoder(const F &f) : f_(f) {
    static_assert(domain_subfield<F>::kBitWords);
    // Rows beta_k as bit vectors, reduced to echelon form; each reduced row
    // contributes its leading bit as a pivot.
    std::array<Bytes, 16> rows;
    for (size_t k = 0; k < 16; ++k) rows[k] = bytes(f.beta(k));
    std::array<Bytes, 16> red = rows;
    for (size_t k = 0; k < 16; ++k) {
      size_t b = 0;
      while (b < 8 * F::kBytes && !bit(red[k], b)) ++b;
      check(b < 8 * F::kBytes, "subfield basis is dependent");
      pivot_[k] = b;
      for (size_t j = k + 1; j < 16; ++j)
        if (bit(red[j], b))
          for (size_t i = 0; i < red[j].size(); ++i) red[j][i] ^= red[k][i];
    }
    // A[k] = pivot bits of beta_k; g = u A, so u = g A^-1.
    uint16_t a[16], inv[16];
    for (size_t k = 0; k < 16; ++k) {
      a[k] = 0;
      for (size_t i = 0; i < 16; ++i)
        if (bit(rows[k], pivot_[i])) a[k] |= uint16_t(1u << i);
      inv[k] = uint16_t(1u << k);
    }
    for (size_t c = 0; c < 16; ++c) {
      size_t r = c;
      while (r < 16 && !((a[r] >> c) & 1)) ++r;
      check(r < 16, "pivot bits of the subfield basis are singular");
      std::swap(a[r], a[c]);
      std::swap(inv[r], inv[c]);
      for (size_t j = 0; j < 16; ++j)
        if (j != c && ((a[j] >> c) & 1)) {
          a[j] ^= a[c];
          inv[j] ^= inv[c];
        }
    }
    for (size_t k = 0; k < 16; ++k) inv_[k] = inv[k];
  }
  // u = sum over set bits i of g of row i of A^-1.
  uint16_t operator()(const typename F::Elt &x) const {
    const auto b = bytes(x);
    uint64_t u = 0;
    for (size_t i = 0; i < 16; ++i)
      u ^= inv_[i] & ct::mask(uint64_t(bit(b, pivot_[i])));
    return uint16_t(u);
  }

 private:
  Bytes bytes(const typename F::Elt &x) const {
    Bytes b;
    f_.to_bytes_field(b.data(), x);
    return b;
  }
  static bool bit(const Bytes &b, size_t i) {
    return (b[i / 8] >> (i % 8)) & 1;
  }
  const F &f_;
  size_t pivot_[16];
  uint64_t inv_[16];
};

// The subfield step of a relatively packed domain. The prover commits the
// [K:S]^2 measurement masks of relative packing as the first witness
// coordinates, sampled uniformly in S and padded to whole tableau rows
// (ExtensionLayout::pack); Ligero commits those rows as subfield rows. The
// verifier checks that every opened column lies in S on each of those rows.
// Ligero's own check is turned off for the domain
// (ZkVerifier::enforce_subfield_rows), so this is the only place that reads
// the prefix rows, and another subfield test can replace it here.
template <class F, class Hash>
class PrefixSubfieldTest {
 public:
  PrefixSubfieldTest() = default;
  // ROWS prefix rows holding COORDINATES mask coordinates (tree_zk.h) and,
  // under DomainProfile::unpacked_s0 (a test-only ablation), UNPACKED
  // subfield cells after them.
  PrefixSubfieldTest(size_t rows, size_t coordinates, size_t unpacked = 0)
      : rows_(rows), coordinates_(coordinates), unpacked_(unpacked) {}
  size_t rows() const { return rows_; }
  size_t coordinates() const { return coordinates_; }

  bool verify(const LigeroParam<F, Hash> &p, const LigeroProof<F, Hash> &proof,
              const F &f) const {
    if (rows_ > p.nwrow) return false;
    for (size_t i = 0; i < rows_; ++i)
      for (size_t j = 0; j < p.nreq; ++j)
        if (!subfield_contains(f, proof.req_at(i + p.iw, j))) return false;
    return true;
  }

  std::string report() const {
    return "prefix subfield test on " + std::to_string(rows_) + " rows (" +
           std::to_string(coordinates_) + " mask coordinates" +
           (unpacked_ ? ", " + std::to_string(unpacked_) + " unpacked cells"
                      : std::string()) +
           ")";
  }

 private:
  size_t rows_ = 0, coordinates_ = 0, unpacked_ = 0;
};

}  // namespace proofs::gordiehowe::compiler

#endif  // PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_COMPILER_PACKING_H_
