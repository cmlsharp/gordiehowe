// Copyright 2026 Chad Sharp and Paul Grubbs
// SPDX-License-Identifier: Apache-2.0

// Held-out program: a Merkle authentication path with SHA-256.
//
// The statement is a Merkle root; the witness is a leaf, its position (a
// 32-bit index whose bit i says whether the node at level i is a right
// child) and the siblings on its path. The depth is a parameter of the
// relation: the number of siblings, and the index lies below 2^depth. Each
// level hashes the 64-byte concatenation of its two children,
//   node_{i+1} = SHA-256(left_i || right_i),
// where (left_i, right_i) is (node_i, sibling_i) for a left child and
// (sibling_i, node_i) for a right one, selected by the index bit with one
// multiplexer per side. One binary domain holds everything.

#ifndef PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_HELDOUT_MERKLE_SHA256_H_
#define PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_HELDOUT_MERKLE_SHA256_H_

#include <array>
#include <cstddef>
#include <cstdint>
#include <random>
#include <string>
#include <vector>

#include "gordiehowe/heldout/heldout_env.h"
#include "gordiehowe/lib/sha256.h"
#include "util/crypto.h"

namespace proofs::gordiehowe::heldout::merkle {

using Digest = std::array<uint8_t, 32>;

template <template <class> class F>
struct Statement {
  F<Digest> root;
};
template <template <class> class F>
struct Witness {
  F<Digest> leaf;
  // Bit i: the node at level i is a right child.
  F<uint32_t> index;
  // The sibling at each level, leaf level first.
  F<std::vector<Digest>> siblings;
};

// The relation at DEPTH levels (1 <= DEPTH <= 32).
inline auto relation(size_t depth) {
  Statement<Value> st_shape{};
  Witness<Value> w_shape{};
  w_shape.siblings.resize(depth);
  return compile<Statement, Witness>(
      compile_profile("merkle"),
      [depth](BinarySys &cs, Statement<In> st, Witness<In> w) {
        auto &H = cs.domain(binary_profile(), "H");
        auto node = H.priv(w.leaf).flat();
        const auto index = H.priv(Bit{}, w.index).flat();
        const auto siblings = H.priv(w.siblings);
        // The index lies below 2^depth.
        if (depth < 32) assert_zero(index.slice(depth, 32), "index_high");
        const auto batch = lib::sha256::sha256_batch(H, "hash");
        // Every bit of a child reads the level's index bit.
        const std::vector<size_t> each(256, 0);
        for (size_t i = 0; i < depth; ++i) {
          const Scope level = cs.scope("level" + std::to_string(i));
          const auto right_child = index.slice(i, i + 1).reindex(each);
          const auto sibling = siblings.at(0, i).flat();
          const auto left = level[H].priv("left",
                                          right_child.mux(sibling, node));
          const auto right = level[H].priv("right",
                                           right_child.mux(node, sibling));
          node = lib::sha256::sha256(batch, "level" + std::to_string(i),
                                     left.concat(right));
        }
        assert_equal(node, st.root.bits(H).flat(), "root");
      },
      "heldout-merkle-" + std::to_string(depth), st_shape, w_shape);
}

// ------------------------------------------------------------------ host --

inline Digest hash_pair(const Digest &l, const Digest &r) {
  SHA256 sha;
  sha.Update(l.data(), l.size());
  sha.Update(r.data(), r.size());
  Digest d;
  sha.DigestData(d.data());
  return d;
}

// The root of the path from LEAF at INDEX through SIBLINGS.
inline Digest root_of(const Digest &leaf, uint32_t index,
                      const std::vector<Digest> &siblings) {
  Digest node = leaf;
  for (size_t i = 0; i < siblings.size(); ++i)
    node = (index >> i) & 1 ? hash_pair(siblings[i], node)
                            : hash_pair(node, siblings[i]);
  return node;
}

struct Instance {
  Statement<Value> statement;
  Witness<Value> witness;
};

// A random leaf, index below 2^DEPTH and siblings, and their root.
inline Instance instance(size_t depth, uint64_t seed) {
  std::mt19937_64 g(seed);
  Instance in;
  for (auto &b : in.witness.leaf) b = uint8_t(g());
  in.witness.index =
      depth >= 32 ? uint32_t(g()) : uint32_t(g() & ((1ull << depth) - 1));
  in.witness.siblings.resize(depth);
  for (auto &s : in.witness.siblings)
    for (auto &b : s) b = uint8_t(g());
  in.statement.root =
      root_of(in.witness.leaf, in.witness.index, in.witness.siblings);
  return in;
}

}  // namespace proofs::gordiehowe::heldout::merkle

#endif  // PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_HELDOUT_MERKLE_SHA256_H_
