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
// Modified 2026 by Chad Sharp and Paul Grubbs: Hash-templated digest and tree, leaf and node role tag bytes, level-by-level parallel tree build

#ifndef PRIVACY_PROOFS_ZK_LIB_MERKLE_MERKLE_TREE_H_
#define PRIVACY_PROOFS_ZK_LIB_MERKLE_MERKLE_TREE_H_

#include <stddef.h>
#include <stdint.h>

#include <cstring>
#include <algorithm>
#include <vector>

#include "util/crypto.h"
#include "util/parallel.h"
#include "util/panic.h"

namespace proofs {

// This package computes and verifies Merkle Tree inclusion claims.
// The folklore Merkle tree algorithm has been implemented, with the following
// constraints:
//   1. A Merkle tree proof must reveal at least one leaf. We do not define
//      empty proofs.
//   2. The list of leaves must be a set, i.e., with no duplicates.  All usage
//      within this library satisfies this requirement because the FS methods
//      that produce the challenge set of indices includes no duplicates.
//   3. The generated proof of inclusion for a set of leaves is compressed.
//      That is, if a node in the Merkle tree can be deduced, it is not included
//      in the proof. This makes the proof shorter, but the proof length varies
//      depending on the included leaves.

// Role bytes that open every Merkle hash input, so that leaf, node and
// transcript inputs of the protocol hash are disjoint. A leaf hashes
// kMerkleLeafTag || nonce || column (merkle_commitment.h), a node hashes
// kMerkleNodeTag || left || right (hash2 below), and a transcript input opens
// with its first write's tag, TAG_BSTR = 0 (random/transcript.h).
constexpr uint8_t kMerkleLeafTag = 0x01;
constexpr uint8_t kMerkleNodeTag = 0x02;

// A digest of a Merkle tree over the hash policy Hash (util/crypto.h).
template <class Hash = UpstreamHash>
struct BasicDigest {
  static constexpr size_t kLength = Hash::kDigestSize;
  uint8_t data[kLength];

  bool operator==(const BasicDigest& y) const {
    return memcmp(data, y.data, kLength) == 0;
  }

  static BasicDigest hash2(const BasicDigest& L, const BasicDigest& R) {
    Hash sha;
    sha.Update(&kMerkleNodeTag, 1);
    sha.Update(L.data, kLength);
    sha.Update(R.data, kLength);
    BasicDigest output;
    sha.DigestData(output.data);
    return output;
  }
};

// Return the length of the proof for N leaves.
// Mimic the code in generate_proof() without actually
// computing the proof
inline size_t merkle_tree_len(size_t n) {
  size_t r = 1;
  size_t pos = (n - 1);  // maximum possible value
  for (pos += n; pos > 1; pos >>= 1) {
    ++r;
  }
  return r;
}

// compute the set of all nodes on the path from the
// root to any leaf in POS.
inline std::vector<bool> compressed_merkle_proof_tree(size_t n,
                                                      const size_t pos[/*np*/],
                                                      size_t np) {
  check(np > 0, "A Merkle proof with 0 leaves is not defined.");
  std::vector<bool> tree(2 * n, false);

  // leaves are in TREE
  for (size_t ip = 0; ip < np; ++ip) {
    check(pos[ip] < n, "Invalid position for leaf in Merkle tree");
    check(tree[pos[ip] + n] == false,
          "duplicate position in merkle tree requested");
    tree[pos[ip] + n] = true;
  }

  // If a child of an inner node is in TREE, then the parent is in TREE.
  for (size_t i = n; i-- > 1;) {
    tree[i] = (tree[2 * i] || tree[2 * i + 1]);
  }

  // Assert that the root is in TREE.
  check(tree[1], "tree[1]");

  return tree;
}

template <class Hash = UpstreamHash>
class BasicMerkleTree {
 public:
  using Digest = BasicDigest<Hash>;
  explicit BasicMerkleTree(size_t n) : n_(n), layers_(2 * n) {}

  void set_leaf(size_t pos, const Digest& leaf) {
    check(pos < n_, "Invalid position for leaf in Merkle tree");
    layers_[pos + n_] = leaf;
  }

  // Level by level from the deepest: the inner nodes of depth k are
  // [2^k, min(2^(k+1), n)), and their children lie deeper; each level's
  // nodes in parallel chunks (util/parallel.h).
  Digest build_tree() {
    size_t top = 1;
    while (2 * top < n_) top *= 2;
    for (size_t lo = top; lo >= 1; lo /= 2) {
      const size_t hi = std::min(2 * lo, n_);
      if (hi > lo)
        parallel::for_each(hi - lo, std::max<size_t>(256, (hi - lo) / parallel::kChunks + 1),
                           [&](size_t k) {
          const size_t i = lo + k;
          layers_[i] = Digest::hash2(layers_[2 * i], layers_[2 * i + 1]);
        });
    }
    return layers_[1];
  }

  // Compressed Merkle proofs over a set POS[NP] of leaves.
  //
  // We first compute the set TREE of all nodes that are on the path
  // from the root to any leaf in POS.  Then, for each inner node in
  // TREE, we include in the proof the child that is not in TREE, if
  // any.  Note, this method requires pos to contain no duplicates.
  size_t generate_compressed_proof(std::vector<Digest>& proof,
                                   const size_t pos[/*np*/], size_t np) {
    std::vector<bool> tree = compressed_merkle_proof_tree(n_, pos, np);

    // For each TREE node, include in the proof the
    // child that is not TREE, if any.
    size_t sz = 0;
    for (size_t i = n_; i-- > 1;) {
      if (tree[i]) {
        size_t child = 2 * i;
        if (tree[child]) {
          // try the other child
          child = 2 * i + 1;
        }
        if (!tree[child]) {
          proof.push_back(layers_[child]);
          ++sz;
        }
      }
    }
    return sz;
  }

  size_t n_;
  // layers_[n, 2 * n) stores the leaves (nodes at layer 0).
  // layers_[n/2, n) stores nodes at layer 1.
  // layers_[n/4, n/2) stores nodes at layer 2, etc.
  // The root is at layers_[1] where layers_[0] is not used.
  std::vector<Digest> layers_;
};

template <class Hash = UpstreamHash>
class BasicMerkleTreeVerifier {
 public:
  using Digest = BasicDigest<Hash>;
  explicit BasicMerkleTreeVerifier(size_t n, const Digest& root)
      : n_(n), root_(root) {}

  // Verify a compressed Merkle proof.
  // As mentioned above, this method assumes that pos contains no duplicates.
  bool verify_compressed_proof(const Digest* proof, size_t proof_len,
                               const Digest leaves[/*np*/],
                               const size_t pos[/*np*/], size_t np) const {
    // Reconstructed layers_, where only the DEFINED subset is
    // defined.
    std::vector<Digest> layers(2 * n_, Digest{});
    std::vector<bool> defined(2 * n_, false);

    /*scope for TREE */ {
      std::vector<bool> tree = compressed_merkle_proof_tree(n_, pos, np);

      // read the proof
      size_t sz = 0;
      for (size_t i = n_; i-- > 1;) {
        if (tree[i]) {
          size_t child = 2 * i;
          if (tree[child]) {
            // try the other child
            child = 2 * i + 1;
          }
          if (!tree[child]) {
            if (sz >= proof_len) {
              return false;
            }
            layers[child] = proof[sz++];
            defined[child] = true;
          }
        }
      }
      // Ensure entire proof is consumed.
      if (sz != proof_len) return false;
    }

    // set LAYERS at all leaves in POS
    for (size_t ip = 0; ip < np; ++ip) {
      size_t l = pos[ip] + n_;
      layers[l] = leaves[ip];
      defined[l] = true;
    }

    // Recompute as many inner nodes as we can
    for (size_t i = n_; i-- > 1;) {
      if (defined[2 * i] && defined[2 * i + 1]) {
        layers[i] = Digest::hash2(layers[2 * i], layers[2 * i + 1]);
        defined[i] = true;
      }
    }

    return (defined[1] && (root_ == layers[1]));
  }

 private:
  size_t n_;
  Digest root_;
};

using Digest = BasicDigest<>;
using MerkleTree = BasicMerkleTree<>;
using MerkleTreeVerifier = BasicMerkleTreeVerifier<>;

}  // namespace proofs

#endif  // PRIVACY_PROOFS_ZK_LIB_MERKLE_MERKLE_TREE_H_
