// Copyright 2026 Chad Sharp and Paul Grubbs
// SPDX-License-Identifier: Apache-2.0

// GordieHowe: the packing tree of a domain.
//
// Nodes are the subfields the domain's values declare (Bit is GF(2) in
// characteristic 2; the designated subfield; Subfield<GF<d>>) and K. Each
// node's parent is the smallest node containing it; among several minimal
// containing nodes (GF(q^2) and GF(q^3) over GF(q) in GF(q^6)) the one with
// the lowest edge cost plus the parent's path cost to the root, then the
// smaller degree, then declaration order. An edge of degree above D_max
// gets intermediate fields from the divisor lattice: the fewest edges, then
// the most even split (least largest degree), among the splits whose
// subfield-masks stages the prefix-row test covers. A subfield-masks stage
// commits its masks in the prefix rows of the designated subfield S0
// (stage.h), which needs S0 ⊆ B. An edge in characteristic 2 whose base the
// prefix-row test does not cover (GF(2), GF(2^4), GF(2^8) under
// S0 = GF(2^16)) uses squaring-chain masks: full-field masks and squaring
// chains for their Frobenius twists. Every other edge uses subfield masks.
// In odd characteristic an uncovered base fails the plan.
//
// Each node's region holds its own values and the packed words of its
// children; the root's is the commitment.

#ifndef PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_COMPILER_TREE_H_
#define PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_COMPILER_TREE_H_

#include <algorithm>
#include <cstddef>
#include <cstdint>
#include <limits>
#include <map>
#include <tuple>
#include <string>
#include <utility>
#include <vector>

namespace proofs::gordiehowe::compiler {

struct PackingTree {
  struct Node {
    size_t degree = 0;      // over the prime field
    bool declared = false;  // a declared type, not an intermediate
    size_t order = 0;       // declaration order (intermediates after)
    int parent = -1;        // node index; -1 for the root
    std::vector<int> children;
    size_t depth = 0;
  };
  size_t n = 0, s0 = 0, d_max = 16;
  bool char2 = false;
  // Chains the compiler chose by cost for edges B < T (compiled_domain.h's
  // choose_chains, under the stage rates): split() returns them in place
  // of the default.
  std::map<std::pair<size_t, size_t>, std::vector<size_t>> chosen;
  // Chains a compile forces for edges B < T (CompileOptions::forced_chains,
  // the tree-cost experiment): split() returns them before any other.
  std::map<std::pair<size_t, size_t>, std::vector<size_t>> forced;
  std::vector<Node> nodes;  // nodes[0] is K
  std::string error;        // nonempty: the plan is not realizable

  int node_of(size_t degree) const {
    for (size_t i = 0; i < nodes.size(); ++i)
      if (nodes[i].degree == degree) return int(i);
    return -1;
  }
  bool squaring_chain(int i) const {
    return squaring_chain_base(nodes[size_t(i)].degree);
  }
  // Whether the prefix-row test covers a subfield-masks stage over a base
  // of degree B (S0 ⊆ B).
  bool prefix_covered(size_t b) const { return b % s0 == 0; }
  // Whether an edge over a base of degree B uses squaring-chain masks: in
  // characteristic 2, GF(2) and every base the prefix-row test does not
  // cover.
  bool squaring_chain_base(size_t b) const {
    return char2 && (b == 1 || !prefix_covered(b));
  }
  // Whether a stage over B is GF(2)'s bit stage or a covered
  // subfield-masks stage, the splits the planner prefers.
  bool covered(size_t b) const { return (char2 && b == 1) || prefix_covered(b); }
  // Mask cells, chain cells and revealed elements of an edge B < T. A
  // squaring-chain-masks stage has d masks and b k squarings for the
  // twist phi^k, k < d.
  size_t masks(size_t b, size_t t) const {
    const size_t d = t / b;
    return squaring_chain_base(b) ? d : d * (n / s0);
  }
  size_t chain_cells(size_t b, size_t t) const {
    const size_t d = t / b;
    return squaring_chain_base(b) ? b * d * (d - 1) / 2 : 0;
  }
  size_t edge_cost(size_t b, size_t t) const {
    return masks(b, t) + chain_cells(b, t) + t / b;
  }
  // Non-root nodes, deepest first, then by degree: the order of the stages.
  std::vector<int> bottom_up() const {
    std::vector<int> v;
    for (size_t i = 1; i < nodes.size(); ++i) v.push_back(int(i));
    std::stable_sort(v.begin(), v.end(), [&](int a, int b) {
      const Node &x = nodes[size_t(a)], &y = nodes[size_t(b)];
      return x.depth != y.depth ? x.depth > y.depth : x.degree < y.degree;
    });
    return v;
  }

  // The nodes whose stage runs before the root's: bottom_up() without the
  // root's children, whose stages the root runs.
  std::vector<int> inner() const {
    std::vector<int> v;
    for (int x : bottom_up())
      if (nodes[size_t(x)].parent != 0) v.push_back(x);
    return v;
  }

  // DECLARED: the declared degrees in declaration order (K's own may appear;
  // duplicates are ignored).
  static PackingTree plan(
      size_t n, size_t s0, bool char2, const std::vector<size_t> &declared,
      size_t d_max = 16,
      const std::map<std::pair<size_t, size_t>, std::vector<size_t>> &chosen =
          {},
      const std::map<std::pair<size_t, size_t>, std::vector<size_t>> *forced =
          nullptr) {
    PackingTree t;
    if (forced != nullptr) t.forced = *forced;
    t.n = n;
    t.s0 = s0;
    t.char2 = char2;
    t.d_max = d_max;
    t.chosen = chosen;
    t.nodes.push_back(Node{n, true, 0, -1, {}, 0});
    for (size_t d : declared) {
      if (d == n || t.node_of(d) >= 0) continue;
      if (d == 0 || n % d != 0) {
        t.error = "degree " + std::to_string(d) + " is not a subfield of K";
        return t;
      }
      t.nodes.push_back(Node{d, true, t.nodes.size(), -1, {}, 0});
    }
    // Parents, from the top down so that every candidate's path cost is
    // known.
    std::vector<size_t> by_degree;
    for (size_t i = 1; i < t.nodes.size(); ++i) by_degree.push_back(i);
    std::sort(by_degree.begin(), by_degree.end(), [&](size_t a, size_t b) {
      return t.nodes[a].degree > t.nodes[b].degree;
    });
    std::vector<size_t> cost(t.nodes.size(), 0);
    std::vector<std::vector<size_t>> path_of(t.nodes.size());
    const size_t declared_nodes = t.nodes.size();
    for (size_t x : by_degree) {
      const size_t dx = t.nodes[x].degree;
      std::vector<size_t> cand;
      for (size_t y = 0; y < declared_nodes; ++y)
        if (y != x && t.nodes[y].degree > dx && t.nodes[y].degree % dx == 0)
          cand.push_back(y);
      std::vector<size_t> minimal;
      for (size_t y : cand) {
        bool min = true;
        for (size_t z : cand)
          if (z != y && t.nodes[y].degree % t.nodes[z].degree == 0) min = false;
        if (min) minimal.push_back(y);
      }
      size_t best = SIZE_MAX, best_cost = 0;
      std::vector<size_t> best_path;
      for (size_t y : minimal) {
        const auto p = t.split(dx, t.nodes[y].degree);
        size_t c = cost[y];
        for (size_t i = 0; i + 1 < p.size(); ++i) c += t.edge_cost(p[i], p[i + 1]);
        auto key = [&](size_t yy, size_t cc) {
          return std::make_tuple(cc, t.nodes[yy].degree, t.nodes[yy].order);
        };
        if (best == SIZE_MAX || key(y, c) < key(best, best_cost)) {
          best = y;
          best_cost = c;
          best_path = p;
        }
      }
      cost[x] = best_cost;
      path_of[x] = best_path;
      t.nodes[x].parent = int(best);
    }
    // Intermediates: each long edge becomes its chain, created from the top
    // down; an intermediate another chain created keeps its parent.
    for (size_t x = 1; x < declared_nodes; ++x) {
      const auto &p = path_of[x];
      int above = t.nodes[x].parent;
      for (size_t i = p.size() - 1; i-- > 1;) {
        int at = t.node_of(p[i]);
        if (at < 0) {
          t.nodes.push_back(Node{p[i], false, t.nodes.size(), above, {}, 0});
          at = int(t.nodes.size() - 1);
        }
        above = at;
      }
      t.nodes[x].parent = above;
    }
    for (size_t i = 1; i < t.nodes.size(); ++i)
      t.nodes[size_t(t.nodes[i].parent)].children.push_back(int(i));
    for (auto &nd : t.nodes)
      std::stable_sort(nd.children.begin(), nd.children.end(), [&](int a, int b) {
        return t.nodes[size_t(a)].degree != t.nodes[size_t(b)].degree
                   ? t.nodes[size_t(a)].degree < t.nodes[size_t(b)].degree
                   : t.nodes[size_t(a)].order < t.nodes[size_t(b)].order;
      });
    for (size_t i = 1; i < t.nodes.size(); ++i) {
      size_t depth = 0;
      for (int u = int(i); u != 0; u = t.nodes[size_t(u)].parent) ++depth;
      t.nodes[i].depth = depth;
    }
    // Every edge must be realizable: a subfield-masks stage needs S0 in its
    // base, and squaring-chain masks need characteristic 2.
    for (size_t i = 1; i < t.nodes.size() && t.error.empty(); ++i) {
      const size_t b = t.nodes[i].degree;
      const size_t top = t.nodes[size_t(t.nodes[i].parent)].degree;
      if (!t.squaring_chain(int(i)) && !t.prefix_covered(b))
        t.error = "the subfield-masks stage GF(p^" + std::to_string(b) +
                  ") < GF(p^" + std::to_string(top) +
                  ") has its masks in a base without the designated subfield "
                  "GF(p^" + std::to_string(s0) +
                  "), which the prefix-row test does not cover; squaring-chain "
                  "masks need characteristic 2";
    }
    return t;
  }

  // The chain of degrees from B up to T (inclusive): one edge when T/B <=
  // D_max, else the fewest edges of degree <= D_max, the least largest
  // edge, preferring chains whose bases are GF(2) or covered by the
  // prefix-row test (no squaring-chain-masks stage over b > 1), then the
  // lexicographically least.
  std::vector<size_t> split(size_t b, size_t top) const {
    // A forced chain (the tree-cost experiment).
    if (const auto f = forced.find({b, top}); f != forced.end())
      return f->second;
    const auto it = chosen.find({b, top});
    if (it != chosen.end()) return it->second;
    return default_split(b, top);
  }
  // The default chain of B < T, the D_max rule.
  std::vector<size_t> default_split(size_t b, size_t top) const {
    if (top / b <= d_max) return {b, top};
    std::vector<std::vector<size_t>> all;
    std::vector<size_t> cur{b};
    enumerate(top, cur, all);
    auto key = [&](const std::vector<size_t> &p) {
      bool ok = true;
      size_t mx = 0;
      for (size_t i = 0; i + 1 < p.size(); ++i) {
        if (!covered(p[i])) ok = false;
        mx = std::max(mx, p[i + 1] / p[i]);
      }
      return std::make_tuple(!ok, p.size(), mx, p);
    };
    if (all.empty()) return {b, top};
    return *std::min_element(all.begin(), all.end(),
                             [&](const auto &x, const auto &y) {
                               return key(x) < key(y);
                             });
  }

  // Whether every stage of CHAIN is realizable: a subfield-masks stage needs
  // the designated subfield in its base, squaring-chain masks need
  // characteristic 2, and a binary intermediate has degree at most 64
  // (SubfieldInfo::unsupported).
  bool admissible(const std::vector<size_t> &chain) const {
    for (size_t i = 0; i + 1 < chain.size(); ++i) {
      if (!squaring_chain_base(chain[i]) && !prefix_covered(chain[i]))
        return false;
      if (char2 && i > 0 && chain[i] > 64) return false;
    }
    return true;
  }
  // The chains the compiler weighs for B < T:
  // the default first, then the single edge and every chain through one
  // intermediate degree, those admissible.
  std::vector<std::vector<size_t>> candidates(size_t b, size_t top) const {
    std::vector<std::vector<size_t>> out = {default_split(b, top)};
    auto add = [&](std::vector<size_t> c) {
      if (!admissible(c)) return;
      for (const auto &o : out)
        if (o == c) return;
      out.push_back(std::move(c));
    };
    add({b, top});
    for (size_t m = 2 * b; m < top; m += b)
      if (m % b == 0 && top % m == 0) add({b, m, top});
    return out;
  }

 private:
  void enumerate(size_t top, std::vector<size_t> &cur,
                 std::vector<std::vector<size_t>> &all) const {
    const size_t at = cur.back();
    if (cur.size() > 8) return;
    for (size_t r = 2; r <= d_max && at * r <= top; ++r) {
      if ((top / at) % r != 0) continue;
      cur.push_back(at * r);
      if (at * r == top)
        all.push_back(cur);
      else
        enumerate(top, cur, all);
      cur.pop_back();
    }
  }
};

}  // namespace proofs::gordiehowe::compiler

#endif  // PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_COMPILER_TREE_H_
