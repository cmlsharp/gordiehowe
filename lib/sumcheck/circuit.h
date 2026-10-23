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
// Modified 2026 by Chad Sharp and Paul Grubbs: layer unit-coefficient flag, packed-bit and input-product fields, extension-packing flag, variable-size circuit id and set_optimizations

#ifndef PRIVACY_PROOFS_ZK_LIB_SUMCHECK_CIRCUIT_H_
#define PRIVACY_PROOFS_ZK_LIB_SUMCHECK_CIRCUIT_H_

#include <stddef.h>

#include <array>
#include <cstdint>
#include <memory>
#include <utility>
#include <vector>

#include "algebra/poly.h"
#include "arrays/affine.h"
#include "sumcheck/quad.h"
#include "util/crypto.h"
#include "util/optimization_options.h"

namespace proofs {
template <class Field>
struct Layer {
  corner_t nw;  // number of inputs
  size_t logw;  // number of binding rounds for the hand variables
  std::unique_ptr<const Quad<Field>> quad;

  // Execution policy only: not part of the circuit relation or serialization.
  // Off by default, so a circuit that does not opt in keeps Longfellow's
  // arithmetic.
  bool unit_coefficient_shortcuts = false;

  size_t nterms() const { return quad->size(); }
};

template <class Field>
struct Circuit {
  static constexpr size_t kMaxLayers = 10000;
  static constexpr corner_t kMaxCopies = 1ULL << 24;
  static constexpr corner_t kMaxOutputs = 1ULL << 24;

  corner_t nv;  // number of outputs for one copy
  size_t logv;  // number of G variables in V[G,C] in the final output
  corner_t nc;  // number of copies
  size_t logc;  // number of sumcheck rounds for the C variables
  size_t nl;    // number of layers

  size_t ninputs;  //  number of inputs
  size_t npub_in;  //  number of public inputs, index of first private input
  size_t subfield_boundary;  // Least input wire not known to be in the
                             // subfield

  // Private input ranges [a, b), aligned to Field::kSubFieldBits, whose wires
  // are bits committed packed into subfield elements (zk/zk_packed.h).  The
  // circuit does not assert these wires Boolean; the commitment makes them
  // bits.  Empty for ordinary circuits.
  std::vector<std::pair<size_t, size_t>> packed_bits;

  // Public, pre-commit constraints on absolute private circuit input indices.
  // These products are checked by Ligero independently of the GKR circuit.
  std::vector<std::array<size_t,3>> input_products;
  // An aligned packed input group reads the canonical bits of an existing
  // subfield input. Both indices are absolute circuit input indices.
  std::vector<std::pair<size_t,size_t>> packed_input_aliases;
  // Commit the subfield inputs packed relative to the subfield
  // (zk/zk_extension_packed.h) when the field supports it. Not part of the
  // circuit id: the packed transcript binds its own tag
  // (ExtensionLayout::bind).
  bool extension_packing = false;

  std::vector<Layer<Field>> l;  // layers

  // Unique id for the circuit, created by the compiler: a digest of the
  // protocol hash policy (sumcheck/circuit_id.h), in the first
  // Hash::kDigestSize bytes.
  uint8_t id[kMaxProtocolDigestSize] = {};

  void set_optimizations(const OptimizationOptions& options) {
    for (auto& layer : l)
      layer.unit_coefficient_shortcuts = options.unit_coefficients;
  }

  size_t nterms() const {
    size_t n = 0;
    for (const auto& layer : l) {
      n += layer.nterms();
    }
    return n;
  }
};

template <class Field>
struct LayerProof {
  using Elt = typename Field::Elt;
  // For efficiency, we distinguish polynomials needed to bind copy
  // variables (CPoly, degree 3) from polynomials needed to bind
  // wire variables (WPoly, degree 2).
  using CPoly = Poly<4, Field>;
  using WPoly = Poly<3, Field>;

  // Maximum 2^40 gates/wires/copies per layer.
  static constexpr size_t kMaxBindings = 40;

  CPoly cp[kMaxBindings];  // polys for the C variables

  // The binding order we use is "for (round) { for (hand) ... }", and
  // thus one can organize this array as [kMaxBindings][2] for better
  // memory locality.
  // However, the corresponding challenges are organized as [2][kMaxBindings]
  // to allow easier binding by hand, and so it makes sense to keep this
  // array in the same order as the challenges.
  WPoly hp[2][kMaxBindings];  // polys for each hand \in {right,left}

  // prover provides W[R,C] and W[L,C], which serve as claims
  // for the next layer
  Elt wc[2];
};

template <class Field>
struct LayerChallenge {
  using Elt = typename Field::Elt;
  static constexpr size_t kMaxBindings = LayerProof<Field>::kMaxBindings;

  // verifier: coefficient for the random linear combination
  // claim[0] + alpha * claim[1] of the two input claims.
  Elt alpha;
  Elt beta;                 // random coefficient for assert-zero
  Elt cb[kMaxBindings];     // bindings for the C variables
  Elt hb[2][kMaxBindings];  // bindings for each hand
};

template <class Field>
struct Challenge {
  using Elt = typename Field::Elt;
  static constexpr size_t kMaxBindings = LayerProof<Field>::kMaxBindings;

  // verifier picks Q for EQ[Q|c]
  Elt q[kMaxBindings];  // [logC]

  // verifier picks G for V[G,c]
  Elt g[kMaxBindings];  // [logV]
  std::vector<LayerChallenge<Field>> l;
  explicit Challenge(size_t nl) : l(nl) {}
};

// Full proof:
template <class Field>
struct Proof {
  typedef typename LayerProof<Field>::CPoly CPoly;
  typedef typename LayerProof<Field>::WPoly WPoly;

  using Elt = typename Field::Elt;
  static constexpr size_t kMaxBindings = LayerProof<Field>::kMaxBindings;

  // then engage in sumcheck one per layer
  std::vector<LayerProof<Field>> l;

  explicit Proof(size_t nl) : l(nl) {}
  size_t size() const {
    return l.size() * (kMaxBindings * 4 + kMaxBindings * 3 * 2 + 2);
  }
};

// Auxiliary information generated by the prover to be
// used by the ZK prover
template <class Field>
struct ProofAux {
  using Elt = typename Field::Elt;
  std::vector<Elt> bound_quad;
  explicit ProofAux(size_t nl) : bound_quad(nl) {}
};
}  // namespace proofs

#endif  // PRIVACY_PROOFS_ZK_LIB_SUMCHECK_CIRCUIT_H_
