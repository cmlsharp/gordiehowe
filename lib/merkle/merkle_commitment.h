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
// Modified 2026 by Chad Sharp and Paul Grubbs: Hash-templated Merkle commitment with leaf tag and 2k-byte nonces, leaf hashing in parallel chunks

#ifndef PRIVACY_PROOFS_ZK_LIB_MERKLE_MERKLE_COMMITMENT_H_
#define PRIVACY_PROOFS_ZK_LIB_MERKLE_MERKLE_COMMITMENT_H_

#include <stddef.h>
#include <stdint.h>

#include <cstring>
#include <functional>
#include <vector>

#include "merkle/merkle_tree.h"
#include "random/random.h"
#include "util/crypto.h"
#include "util/parallel.h"

namespace proofs {

// A leaf nonce of 2k bytes, twice the digest length k = Hash::kDigestSize
// (64 bytes with SHA-256, 96 with SHA-384), drawn from the prover's RNG.
template <class Hash = UpstreamHash>
struct BasicMerkleNonce {
  static constexpr size_t kLength = 2 * Hash::kDigestSize;
  uint8_t bytes[kLength];
};

// Open the hash of a leaf: kMerkleLeafTag || nonce, followed by the leaf's
// column bytes (updhash).
template <class Hash>
void merkle_leaf_begin(Hash &sha, const BasicMerkleNonce<Hash> &nonce) {
  sha.Update(&kMerkleLeafTag, 1);
  sha.Update(nonce.bytes, BasicMerkleNonce<Hash>::kLength);
}

template <class Hash = UpstreamHash>
struct BasicMerkleProof {
  explicit BasicMerkleProof(size_t nreq) : nonce(nreq), path() {}

  std::vector<BasicMerkleNonce<Hash>> nonce;  // [nreq]
  // variable size, but < nreq * mt_pathlen
  std::vector<BasicDigest<Hash>> path;
};

inline size_t merkle_commitment_len(size_t n) { return merkle_tree_len(n); }

// prover-side
template <class Hash = UpstreamHash>
class BasicMerkleCommitment {
  using Digest = BasicDigest<Hash>;
  using MerkleNonce = BasicMerkleNonce<Hash>;

 public:
  explicit BasicMerkleCommitment(size_t n) : n_(n), mt_(n), nonce_(n) {}

  Digest commit(const std::function<void(size_t, Hash &)> &updhash,
                RandomEngine &rng) {
    // The nonces in leaf order (the RNG's order), then the leaves in
    // parallel chunks (util/parallel.h).
    for (size_t i = 0; i < n_; ++i)
      rng.bytes(nonce_[i].bytes, MerkleNonce::kLength);
    parallel::for_each(n_, parallel::grain_for(n_, parallel::kChunks),
                       [&](size_t i) {
      Hash sha;
      merkle_leaf_begin(sha, nonce_[i]);
      updhash(i, sha);

      Digest dig;
      sha.DigestData(dig.data);
      mt_.set_leaf(i, dig);
    });

    return mt_.build_tree();
  }

  void open(BasicMerkleProof<Hash> &proof, const size_t pos[/*np*/],
            size_t np) {
    // fill in the nonces of the opening
    for (size_t i = 0; i < np; ++i) {
      proof.nonce[i] = nonce_[pos[i]];
    }

    (void)mt_.generate_compressed_proof(proof.path, pos, np);
  }

 private:
  size_t n_;
  BasicMerkleTree<Hash> mt_;
  std::vector<MerkleNonce> nonce_;
};

// Declare a class for symmetry, but this class is never instantiated
template <class Hash = UpstreamHash>
class BasicMerkleCommitmentVerifier {
  using Digest = BasicDigest<Hash>;

 public:
  static bool verify(size_t n, const Digest &root,
                     const BasicMerkleProof<Hash> &proof,
                     const size_t pos[/*nreq*/], size_t nreq,
                     const std::function<void(size_t, Hash &)> &updhash) {
    // Assemble the expected leaf values
    std::vector<Digest> leaves(nreq);
    parallel::for_each(nreq, parallel::grain_for(nreq, parallel::kChunks),
                       [&](size_t r) {
      Hash sha;
      merkle_leaf_begin(sha, proof.nonce[r]);
      updhash(r, sha);
      sha.DigestData(leaves[r].data);
    });

    BasicMerkleTreeVerifier<Hash> mtv(n, root);
    return mtv.verify_compressed_proof(proof.path.data(), proof.path.size(),
                                       &leaves[0], pos, nreq);
  }
};

using MerkleNonce = BasicMerkleNonce<>;
using MerkleProof = BasicMerkleProof<>;
using MerkleCommitment = BasicMerkleCommitment<>;
using MerkleCommitmentVerifier = BasicMerkleCommitmentVerifier<>;

}  // namespace proofs

#endif  // PRIVACY_PROOFS_ZK_LIB_MERKLE_MERKLE_COMMITMENT_H_
