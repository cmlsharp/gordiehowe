// Copyright 2026 Chad Sharp and Paul Grubbs
// SPDX-License-Identifier: Apache-2.0

// GordieHowe: a batch's operand maps, built from its predicates' views.
//
// A batch merges predicates of one batched form (batch_form.h): one Q, K
// affine operands per predicate, each an affine view of the domain's
// phase-0 cells, public values and constants. The instances are the
// predicates' coordinates, concatenated in declaration order. The operand
// map is built from the views themselves:
//
//   ViewDag      one predicate's operands as a DAG of affine steps (leaves,
//                constants, sums, scalings, index maps, broadcasts, sums
//                along an axis, constant factors), its leaves resolved by
//                the domain into spaces: a committed table (words of a
//                cell, or the bits of the packed run) or a public value.
//   BitViewMap   Bit operands in characteristic 2 (the bit-sliced
//                evaluator). Instances are 64-bit lanes. Predicates of one
//                structure (a loop of rounds, differing only in the cells
//                they read and in their constants) share a template: a lane
//                program compiled once, whose steps are lane rotations and
//                masks. Each predicate is a binding of the template's
//                leaves to table lanes. Values a template reads twice (a
//                column parity, a permuted state) are lanes of their own, so
//                the host and the adjoint compute them once.
//   FieldViewMap Field-element operands (the subfield and full-field
//                evaluators): each operand coordinate's terms, the index
//                maps composed at compile time.
//
// Adjoints. Every view is applied by composing index maps; nothing is
// copied or permuted. The bit adjoint propagates, from each operand lane, a
// weight pattern (a rotation and a mask of the instance weights) through
// the lane program, and contracts a pattern with the dual basis into
// Frobenius forms on the table words where the remaining steps move whole
// words: per lane and Frobenius twist, a handful of products. The forms
// are the only buffer of the
// tables' size. A template's steps also run once symbolically at compile
// time (fold_steps): the weights are u_j eq(s, lane) and the patterns'
// contractions do not depend on the lane, so per proof each template's
// terms fold into tables with u_j taken in, and per instance the adjoint
// is one product of eq per (block, source lane, chunk). Each template
// takes the way of fewer products over the proof; both give the same
// forms.
//
// The bit phase (bit_phase.h) runs the same
// programs with one untwisted weight per entry and the basis eq(rho, b) in
// place of the dual basis (word_weights). Its prover reads them as weighted
// word references, grouped by the weight pattern over a word's bits that
// they carry (bit_phase_tables).

#ifndef PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_COMPILER_VIEW_MAP_H_
#define PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_COMPILER_VIEW_MAP_H_

#include <algorithm>
#include <array>
#include <cstddef>
#include <cstdint>
#include <functional>
#include <map>
#include <memory>
#include <optional>
#include <string>
#include <tuple>
#include <type_traits>
#include <unordered_map>
#include <utility>
#include <vector>

#if defined(__linux__)
#include <sys/mman.h>
#endif
#if defined(__x86_64__)
#include <immintrin.h>
#endif

#include "arrays/eqs.h"
#include "gordiehowe/compiler/batch_form.h"
#include "gordiehowe/compiler/bit_planes.h"
#include "gordiehowe/compiler/counting_field.h"
#include "gordiehowe/compiler/test_switches.h"
#include "gordiehowe/core.h"
#include "gordiehowe/expr.h"
#include "sumcheck/boolean_skip.h"
#include "util/parallel.h"
#include "util/prover_profile.h"
#include "zk/zk_packed.h"

namespace proofs::gordiehowe::compiler {

// ------------------------------------------------------------- spaces --

// A coordinate a leaf reads: position POS of space SPACE (kZero: a zero).
struct SourceRef {
  static constexpr uint32_t kZero = ~uint32_t(0);
  uint32_t space = kZero;
  size_t pos = 0;
};

// A space a batch reads. Tables are committed: bit-sliced, the bits of a
// cell's words (or of the packed run's groups); otherwise a cell's
// coordinates. Publics are values both parties know when they prove and
// verify.
struct BatchSpace {
  enum Kind : uint8_t { kTable = 0, kPublic = 1 };
  Kind kind = kTable;
  // The cell or public node; kRun for the packed run.
  static constexpr size_t kRun = SIZE_MAX;
  size_t node = 0;
  // Positions: bits (bit-sliced) or coordinates.
  size_t size = 0;
};

// Resolves coordinates COORDS (null: all) of the node of a leaf term into
// their sources; false and WHY when the leaf is not admissible.
using LeafResolver =
    std::function<bool(size_t node, const std::vector<size_t> *coords,
                       std::vector<SourceRef> &, std::string &why)>;

// ------------------------------------------------------------ ViewDag --

// One predicate's operands as affine steps. Node kinds:
//   kLeaf       REFS (one per coordinate)
//   kConst      VALUES (a constant of the predicate, in the instance)
//   kAdd        kids[0] + kids[1]
//   kScale      K kids[0]
//   kGather     coordinate i is coordinate IDX[i] of the kids, concatenated
//   kBroadcast  kids[0] (one coordinate) repeated
//   kSum        sums of groups of W along the last axis (W = 0: all)
//   kMask       FACTOR[i] kids[0][i] (a constant factor per coordinate)
//   kNot        1 - kids[0]
template <class F>
struct ViewDag {
  using Elt = typename F::Elt;
  enum Op : uint8_t {
    kLeaf,
    kConst,
    kAdd,
    kScale,
    kGather,
    kBroadcast,
    kSum,
    kMask,
    kNot
  };
  struct Node {
    Op op = kLeaf;
    size_t n = 0;
    std::vector<uint32_t> kids;
    IndexArray idx;
    size_t w = 0;
    Elt k{};
    std::shared_ptr<const std::vector<Elt>> values;  // kConst, kMask
    std::vector<SourceRef> refs;                     // kLeaf
  };
  std::vector<Node> nodes;  // kids before parents
  std::vector<uint32_t> roots;
  // Spaces each leaf reads, in order of first use, and the position of the
  // first coordinate read from each (the leaf's binding).
  struct Binding {
    std::vector<uint32_t> space;
    std::vector<size_t> off;
  };
  std::vector<Binding> bind;  // per node (leaves only)

  // The template key: the structure, leaves by their positions relative to
  // their bindings (and, for lanes, each binding's offset mod ALIGN), and
  // constant factors by value; constants by their size. The key is the
  // bytes themselves (no digest): a leaf's coordinates as maximal runs of
  // consecutive positions in one binding, a factor of bits as a bitmap.
  std::vector<uint8_t> key(const F &f, size_t align) const {
    std::vector<uint8_t> out;
    put_u64(out, nodes.size());
    for (size_t v = 0; v < nodes.size(); ++v) {
      const Node &x = nodes[v];
      put_u64(out, x.op);
      put_u64(out, x.n);
      put_u64(out, x.kids.size());
      for (uint32_t k : x.kids) put_u64(out, k);
      put_u64(out, x.w);
      if (x.op == kGather)
        out.insert(out.end(), x.idx.digest().begin(), x.idx.digest().end());
      if (x.op == kScale) put_elt(f, out, x.k);
      if (x.op == kMask) put_values(f, out, *x.values);
      if (x.op == kLeaf) {
        const Binding &b = bind[v];
        put_u64(out, b.space.size());
        for (size_t s = 0; s < b.space.size(); ++s)
          put_u64(out, align ? b.off[s] % align : 0);
        put_refs(out, b, x.refs);
      }
    }
    put_u64(out, roots.size());
    for (uint32_t r : roots) put_u64(out, r);
    return out;
  }
  // A leaf's coordinates: each its binding's ordinal and position relative
  // to the binding (a zero coordinate: ordinal ~0), written as maximal runs
  // (ordinal, first position, length) of one ordinal and consecutive
  // positions, after the number of runs.
  static void put_refs(std::vector<uint8_t> &out, const Binding &b,
                       const std::vector<SourceRef> &refs) {
    size_t runs = 0;
    std::vector<uint8_t> body;
    uint64_t ord = 0, first = 0, len = 0;
    auto flush = [&]() {
      if (len == 0) return;
      put_u64(body, ord);
      put_u64(body, first);
      put_u64(body, len);
      ++runs;
    };
    for (const auto &r : refs) {
      uint64_t o = ~uint64_t(0), pos = 0;
      if (r.space != SourceRef::kZero) {
        const size_t s = ordinal(b, r.space);
        o = s;
        pos = uint64_t(r.pos - b.off[s]);
      }
      if (len > 0 && o == ord && pos == first + len) {
        ++len;
        continue;
      }
      flush();
      ord = o;
      first = pos;
      len = 1;
    }
    flush();
    put_u64(out, runs);
    out.insert(out.end(), body.begin(), body.end());
  }
  static size_t ordinal(const Binding &b, uint32_t space) {
    for (size_t s = 0; s < b.space.size(); ++s)
      if (b.space[s] == space) return s;
    check(false, "a leaf's binding");
    return 0;
  }
  static void put_elt(const F &f, std::vector<uint8_t> &out, const Elt &x) {
    uint8_t b[F::kBytes];
    f.to_bytes_field(b, x);
    out.insert(out.end(), b, b + F::kBytes);
  }
};

// The ViewDag of ATOMS (affine expressions of N coordinates), its leaves
// resolved by RESOLVE; BITS asks for GF(2) steps only (a scaling by 0 or 1,
// constants and factors that are bits). None, and WHY, when an atom is not
// an affine view the batch reads.
template <class F>
std::optional<ViewDag<F>> view_dag(const F &f,
                                   const std::vector<ExprPtr<F>> &atoms,
                                   const LeafResolver &resolve, bool bits,
                                   std::string &why) {
  using Elt = typename F::Elt;
  using D = ViewDag<F>;
  D g;
  std::unordered_map<const ExprNode<F> *, uint32_t> memo;
  bool ok = true;
  auto refuse = [&](std::string w) {
    if (ok) why = std::move(w);
    ok = false;
    return uint32_t(0);
  };
  auto is_bit = [&](const Elt &x) { return x == f.zero() || x == f.one(); };
  auto add = [&](typename D::Node nd) {
    g.nodes.push_back(std::move(nd));
    g.bind.emplace_back();
    return uint32_t(g.nodes.size() - 1);
  };
  // One evaluator for the constants of all atoms, so a subexpression they
  // share is computed once.
  const batch_form_internal::NoValues none;
  DirectEval<F> direct(f, none);
  // The values of a node that reads no leaf, shared with it when it is a
  // constant.
  auto konst = [&](const ExprPtr<F> &x) {
    if (x->op == ExprOp::kConst)
      return std::shared_ptr<const std::vector<Elt>>(x, &x->c);
    return std::shared_ptr<const std::vector<Elt>>(
        std::make_shared<const std::vector<Elt>>(
            batch_form_internal::constant_values<F>(x, direct)));
  };
  batch_form_internal::Affinity<F> aff;
  // A leaf node of REFS, with its binding.
  auto add_leaf = [&](std::vector<SourceRef> refs) {
    typename D::Node leaf;
    leaf.op = D::kLeaf;
    leaf.n = refs.size();
    typename D::Binding b;
    for (const auto &r : refs) {
      if (r.space == SourceRef::kZero) continue;
      if (std::find(b.space.begin(), b.space.end(), r.space) == b.space.end()) {
        b.space.push_back(r.space);
        b.off.push_back(r.pos);
      }
    }
    leaf.refs = std::move(refs);
    const uint32_t v = add(std::move(leaf));
    g.bind[v] = std::move(b);
    return v;
  };
  // A leaf read whole by one unscaled term without an operator.
  auto plain = [&](const ExprNode<F> &x) {
    return x.op == ExprOp::kLin && x.lin.terms.size() == 1 &&
           x.lin.terms[0].chain.empty() &&
           x.lin.terms[0].scale == f.one() && x.lin.terms[0].in_n == x.n;
  };
  // A view whose every path ends at a plain leaf or at a constant.
  std::unordered_map<const ExprNode<F> *, bool> lv_memo;
  std::function<bool(const ExprNode<F> &)> leaf_view =
      [&](const ExprNode<F> &x) -> bool {
    if (plain(x)) return true;
    if (!aff.of(x).second) return true;
    if (x.op != ExprOp::kGather) return false;
    auto it = lv_memo.find(&x);
    if (it != lv_memo.end()) return it->second;
    bool r = true;
    for (const auto &k : x.kids) r = r && leaf_view(*k);
    lv_memo[&x] = r;
    return r;
  };
  std::function<uint32_t(const ExprPtr<F> &)> go =
      [&](const ExprPtr<F> &xp) -> uint32_t {
    if (!ok) return 0;
    const ExprNode<F> &x = *xp;
    auto it = memo.find(&x);
    if (it != memo.end()) return it->second;
    typename D::Node nd;
    nd.n = x.n;
    const auto [is_aff, reads] = aff.of(x);
    if (!is_aff) return refuse("an operand is not affine");
    uint32_t out = 0;
    if (!reads) {
      // A constant: its values (a lifted constant shares its node's).
      nd.op = D::kConst;
      if (x.op == ExprOp::kConst)
        nd.values = std::shared_ptr<const std::vector<Elt>>(xp, &x.c);
      else
        nd.values = konst(xp);
      if (bits)
        for (const auto &c : *nd.values)
          if (!is_bit(c)) return refuse("a constant of an operand is not a bit");
      out = add(std::move(nd));
      memo[&x] = out;
      return out;
    }
    switch (x.op) {
      case ExprOp::kLin: {
        std::optional<uint32_t> sum;
        for (const auto &t : x.lin.terms) {
          if (!t.chain.empty())
            return refuse("an operand applies the operator '" +
                          t.chain[0]->name + "'");
          std::vector<SourceRef> refs;
          if (!resolve(t.node, nullptr, refs, why)) {
            ok = false;
            return 0;
          }
          if (refs.size() != x.n)
            return refuse("an operand's leaf has another size");
          uint32_t v = add_leaf(std::move(refs));
          if (t.scale != f.one()) {
            if (bits && t.scale != f.zero())
              return refuse("an operand scales a Bit by a field element");
            typename D::Node s;
            s.op = D::kScale;
            s.n = x.n;
            s.kids = {v};
            s.k = t.scale;
            v = add(std::move(s));
          }
          if (sum) {
            typename D::Node a;
            a.op = D::kAdd;
            a.n = x.n;
            a.kids = {*sum, v};
            v = add(std::move(a));
          }
          sum = v;
        }
        if (!sum) return refuse("an empty leaf");
        out = *sum;
        break;
      }
      case ExprOp::kAdd:
        nd.op = D::kAdd;
        nd.kids = {go(x.kids[0]), go(x.kids[1])};
        out = add(std::move(nd));
        break;
      case ExprOp::kScale:
        if (bits && !is_bit(x.c.at(0)))
          return refuse("an operand scales a Bit by a field element");
        nd.op = D::kScale;
        nd.k = x.c.at(0);
        nd.kids = {go(x.kids[0])};
        out = add(std::move(nd));
        break;
      case ExprOp::kGather: {
        // A view of leaves and constants (through views) is a leaf of the
        // coordinates it reads, resolved alone, plus a constant of the
        // coordinates it takes from constants: a round reads one state of a
        // call's many, a sponge block a slice of the message and the
        // padding, and their index maps compose into the leaf's.
        if (leaf_view(x)) {
          // Each coordinate's leaf and its coordinate there; a constant's
          // coordinates read a zero and enter the constant part.
          std::map<const ExprNode<F> *, size_t> leaf_of;
          std::vector<const ExprNode<F> *> leaves;
          std::vector<std::vector<size_t>> coords;
          std::vector<std::pair<size_t, size_t>> at(x.n);
          std::map<const ExprNode<F> *,
                   std::shared_ptr<const std::vector<Elt>>>
              const_of;
          std::shared_ptr<std::vector<Elt>> cpart;
          // The last coordinate's node and its leaf's index (consecutive
          // coordinates mostly read one node).
          const ExprNode<F> *last = nullptr;
          size_t last_leaf = 0;
          const std::vector<Elt> *last_const = nullptr;
          // Per depth of the walk: the view last met there, the operand
          // last taken, that operand's first coordinate, and whether that
          // operand is a view the walk continues into (consecutive
          // coordinates mostly take one path).
          struct Step {
            const ExprNode<F> *y = nullptr;
            size_t k = 0, start = 0;
            bool down = false;
          };
          std::vector<Step> path;
          for (size_t i = 0; i < x.n; ++i) {
            const ExprNode<F> *y = &x;
            const ExprPtr<F> *yp = nullptr;
            size_t j = i;
            for (size_t d = 0;; ++d) {
              if (path.size() <= d) path.emplace_back();
              Step &st = path[d];
              const size_t q = y->idx[j];
              if (st.y != y || q < st.start ||
                  q >= st.start + y->kids[st.k]->n) {
                size_t k = 0, start = 0;
                while (q >= start + y->kids[k]->n) start += y->kids[k++]->n;
                const ExprNode<F> &kid = *y->kids[k];
                st = Step{y, k, start,
                          kid.op == ExprOp::kGather && aff.of(kid).second};
              }
              yp = &y->kids[st.k];
              j = q - st.start;
              const bool down = st.down;
              y = yp->get();
              if (!down) break;
            }
            if (!plain(*y)) {
              if (y != last) {
                auto [ct, cfresh] = const_of.emplace(y, nullptr);
                if (cfresh) ct->second = konst(*yp);
                last = y;
                last_const = ct->second.get();
              }
              const Elt &c = last_const->at(j);
              if (bits && !is_bit(c))
                return refuse("a constant of an operand is not a bit");
              if (!cpart)
                cpart = std::make_shared<std::vector<Elt>>(x.n, f.zero());
              (*cpart)[i] = c;
              at[i] = {SIZE_MAX, 0};
              continue;
            }
            if (y != last) {
              auto [it, fresh] = leaf_of.emplace(y, leaves.size());
              if (fresh) {
                leaves.push_back(y);
                coords.emplace_back();
              }
              last = y;
              last_leaf = it->second;
            }
            at[i] = {last_leaf, coords[last_leaf].size()};
            coords[last_leaf].push_back(j);
          }
          std::vector<std::vector<SourceRef>> part(leaves.size());
          for (size_t k = 0; k < leaves.size(); ++k)
            if (!resolve(leaves[k]->lin.terms[0].node, &coords[k], part[k],
                         why)) {
              ok = false;
              return 0;
            }
          std::vector<SourceRef> refs(x.n);
          for (size_t i = 0; i < x.n; ++i)
            if (at[i].first != SIZE_MAX)
              refs[i] = part[at[i].first][at[i].second];
          out = add_leaf(std::move(refs));
          if (cpart) {
            typename D::Node k;
            k.op = D::kConst;
            k.n = x.n;
            k.values = std::move(cpart);
            const uint32_t kv = add(std::move(k));
            typename D::Node a;
            a.op = D::kAdd;
            a.n = x.n;
            a.kids = {out, kv};
            out = add(std::move(a));
          }
          break;
        }
        nd.op = D::kGather;
        nd.idx = x.idx;
        for (const auto &k : x.kids) nd.kids.push_back(go(k));
        out = add(std::move(nd));
        break;
      }
      case ExprOp::kBroadcast:
        nd.op = D::kBroadcast;
        nd.kids = {go(x.kids[0])};
        out = add(std::move(nd));
        break;
      case ExprOp::kSum:
        nd.op = D::kSum;
        nd.w = x.w;
        nd.kids = {go(x.kids[0])};
        out = add(std::move(nd));
        break;
      case ExprOp::kNot:
        nd.op = D::kNot;
        nd.kids = {go(x.kids[0])};
        out = add(std::move(nd));
        break;
      case ExprOp::kXor:
      case ExprOp::kMul:
      case ExprOp::kAnd:
      case ExprOp::kOr: {
        if constexpr (F::kCharacteristicTwo) {
          if (x.op == ExprOp::kXor) {
            nd.op = D::kAdd;
            nd.kids = {go(x.kids[0]), go(x.kids[1])};
            out = add(std::move(nd));
            break;
          }
        }
        // One side reads no leaf: a constant factor C. a b = C a,
        // a | b = (1 - C) a + C, a ^ b = (1 - 2 C) a + C.
        const int ks = aff.of(*x.kids[0]).second ? 1 : 0;
        const ExprPtr<F> &kx = x.kids[size_t(ks)];
        const ExprPtr<F> &ax = x.kids[size_t(1 - ks)];
        const auto c = konst(kx);
        if (c->size() != x.n) return refuse("a broadcast constant factor");
        auto factor = std::make_shared<std::vector<Elt>>(*c);
        if (x.op == ExprOp::kOr || x.op == ExprOp::kXor) {
          const Elt two = f.addf(f.one(), f.one());
          for (auto &y : *factor)
            y = f.subf(f.one(), x.op == ExprOp::kOr ? y : f.mulf(two, y));
        }
        if (bits)
          for (const auto &y : *factor)
            if (!is_bit(y))
              return refuse("an operand's constant factor is not a bit");
        nd.op = D::kMask;
        nd.values = std::move(factor);
        nd.kids = {go(ax)};
        out = add(std::move(nd));
        if (x.op != ExprOp::kMul && x.op != ExprOp::kAnd) {
          typename D::Node k;
          k.op = D::kConst;
          k.n = x.n;
          k.values = c;
          const uint32_t kv = add(std::move(k));
          typename D::Node a;
          a.op = D::kAdd;
          a.n = x.n;
          a.kids = {out, kv};
          out = add(std::move(a));
        }
        break;
      }
      case ExprOp::kApply:
        return refuse("an operand applies the operator '" + x.apply->name +
                      "'");
      default:
        return refuse("an operand is not an affine view");
    }
    memo[&x] = out;
    return out;
  };
  for (const auto &a : atoms) {
    const uint32_t r = go(a);
    if (!ok) return std::nullopt;
    g.roots.push_back(r);
  }
  return g;
}

// ------------------------------------------------------ large buffers --

// N copies of X in a buffer whose pages the kernel may back with huge
// pages (Linux transparent huge pages in madvise mode): the bit forms are
// W words per table word, about 90 MB in the post-quantum mDL's hash
// domain, and faulting them in 4 KB pages costs about 80 ms per proof and
// per verification.
template <class T>
std::vector<T> filled_large(size_t n, const T &x) {
  std::vector<T> v;
  v.reserve(n);
#if defined(__linux__) && defined(MADV_HUGEPAGE)
  constexpr uintptr_t kHuge = uintptr_t(1) << 21;
  const uintptr_t lo = (reinterpret_cast<uintptr_t>(v.data()) + kHuge - 1) &
                       ~(kHuge - 1);
  const uintptr_t hi =
      (reinterpret_cast<uintptr_t>(v.data() + n)) & ~(kHuge - 1);
  if (hi > lo)
    (void)madvise(reinterpret_cast<void *>(lo), hi - lo, MADV_HUGEPAGE);
#endif
  v.resize(n, x);
  return v;
}

// ----------------------------------------------------------- patterns --

// A weight pattern on a lane: bit b carries low[(b + s) mod 64] when MASK
// has bit b (low: the instance weights within an operand lane).
struct LanePattern {
  uint8_t s = 0;
  uint64_t mask = 0;
  bool operator<(const LanePattern &o) const {
    return s != o.s ? s < o.s : mask < o.mask;
  }
  bool operator==(const LanePattern &o) const {
    return s == o.s && mask == o.mask;
  }
};
inline uint64_t rotl64(uint64_t x, unsigned r) {
  r &= 63;
  return r == 0 ? x : (x << r) | (x >> (64 - r));
}
inline uint64_t rotr64(uint64_t x, unsigned r) { return rotl64(x, 64 - (r & 63)); }

// ------------------------------------------------------------- twists --

// Elementwise arithmetic on the W twists of a bit adjoint's weight, side by
// side: Y = A B and Y += X, k < W, and the transposed sum of four words
// into the forms. The products are the field's own, so each twist's value
// is the one an elementwise loop of F's mulf gives; only the instructions
// differ.
template <class F, size_t W>
struct Twists {
  using Elt = typename F::Elt;
  static void mul(const F &f, Elt *y, const Elt *a, const Elt *b) {
    for (size_t k = 0; k < W; ++k) y[k] = f.mulf(a[k], b[k]);
  }
  static void add(const F &f, Elt *y, const Elt *x) {
    for (size_t k = 0; k < W; ++k) f.add(y[k], x[k]);
  }
  // Four words of twists K0 .. K0 + 3, transposed: A[k STRIDE + c] +=
  // X[c W + k], c < 4.
  static void add_words4(const F &f, Elt *a, size_t stride, const Elt *x,
                         size_t k0) {
    for (size_t k = k0; k < k0 + 4; ++k)
      for (size_t c = 0; c < 4; ++c) f.add(a[k * stride + c], x[c * W + k]);
  }
};
// One weight per entry (the bit phase's word weights): F's own arithmetic.
template <class F>
struct OneTwist {
  using Elt = typename F::Elt;
  static void mul(const F &f, Elt *y, const Elt *a, const Elt *b) {
    y[0] = f.mulf(a[0], b[0]);
  }
  static void add(const F &f, Elt *y, const Elt *x) { f.add(y[0], x[0]); }
};
// The arithmetic of NT weights side by side.
template <class F, size_t NT>
using TwistOps = std::conditional_t<NT == 1, OneTwist<F>, Twists<F, NT>>;

#if defined(__x86_64__) && defined(__AVX512F__) && defined(__VPCLMULQDQ__)
// Four GF(2^128) products, one per 128-bit lane: gf2_128_mul's schoolbook
// product and reduction modulo x^128 + x^7 + x^2 + x + 1 (gf2k/sysdep.h).
inline __m512i gf2_128_mul_x4(__m512i x, __m512i y) {
  const __m512i poly = _mm512_set1_epi64(0x87);
  const __m512i t0 = _mm512_clmulepi64_epi128(x, y, 0x00);
  __m512i t1 = _mm512_xor_si512(_mm512_clmulepi64_epi128(x, y, 0x01),
                                _mm512_clmulepi64_epi128(x, y, 0x10));
  const __m512i t2 = _mm512_clmulepi64_epi128(x, y, 0x11);
  // t1 + x^64 t2, then t0 + x^64 t1, each reduced.
  t1 = _mm512_ternarylogic_epi64(t1, _mm512_bslli_epi128(t2, 8),
                                 _mm512_clmulepi64_epi128(t2, poly, 0x01),
                                 0x96);
  return _mm512_ternarylogic_epi64(t0, _mm512_bslli_epi128(t1, 8),
                                   _mm512_clmulepi64_epi128(t1, poly, 0x01),
                                   0x96);
}

// GF(2^128): four twists per 512-bit register.
template <size_t kSub, size_t W>
struct Twists<GF2_128<kSub>, W> {
  static_assert(W % 4 == 0, "twists in groups of four");
  using F = GF2_128<kSub>;
  using Elt = typename F::Elt;
  static_assert(sizeof(Elt) == 16, "a GF(2^128) element is 128 bits");
  static __m512i load(const Elt *x) { return _mm512_loadu_si512(x); }
  static void store(Elt *y, __m512i v) { _mm512_storeu_si512(y, v); }
  static void mul(const F &, Elt *y, const Elt *a, const Elt *b) {
    for (size_t i = 0; i < W; i += 4)
      store(y + i, gf2_128_mul_x4(load(a + i), load(b + i)));
  }
  static void add(const F &, Elt *y, const Elt *x) {
    for (size_t i = 0; i < W; i += 4)
      store(y + i, _mm512_xor_si512(load(y + i), load(x + i)));
  }
  static void add_words4(const F &, Elt *a, size_t stride, const Elt *x,
                         size_t k0) {
    // Row c: twists K0 .. K0 + 3 of word c; a 4 x 4 transpose of 128-bit
    // lanes makes row k: words 0 .. 3 of twist K0 + k.
    const __m512i r0 = load(x + k0), r1 = load(x + W + k0);
    const __m512i r2 = load(x + 2 * W + k0), r3 = load(x + 3 * W + k0);
    const __m512i t0 = _mm512_shuffle_i64x2(r0, r1, 0x44);
    const __m512i t1 = _mm512_shuffle_i64x2(r0, r1, 0xEE);
    const __m512i t2 = _mm512_shuffle_i64x2(r2, r3, 0x44);
    const __m512i t3 = _mm512_shuffle_i64x2(r2, r3, 0xEE);
    const __m512i c[4] = {_mm512_shuffle_i64x2(t0, t2, 0x88),
                          _mm512_shuffle_i64x2(t0, t2, 0xDD),
                          _mm512_shuffle_i64x2(t1, t3, 0x88),
                          _mm512_shuffle_i64x2(t1, t3, 0xDD)};
    for (size_t k = 0; k < 4; ++k) {
      Elt *y = a + (k0 + k) * stride;
      store(y, _mm512_xor_si512(load(y), c[k]));
    }
  }
};
#endif

// --------------------------------------------------------- BitViewMap --

// The bit-sliced operand map of a batch: Bit operands in characteristic 2,
// over tables of W-bit words (the bit node's parent). Instance 64 l + z of
// the batch is bit z of operand lane l.
// BitViewMap's program types, which do not depend on its field: a map over
// CountingField<F> (op_counts.h) copies a map over F.
namespace bit_view_internal {

// A source of a lane term.
enum SrcKind : uint8_t { kNode = 0, kLeaf = 1, kConst = 2, kOne = 3 };
// rotl(src lane, rot) & mask, the source a lane of an IR node (kNode),
// leaf source LEAF of the template (kLeaf, lane relative to its
// binding's base lane), constant CONST (kConst) or all ones (kOne).
struct LaneTerm {
  SrcKind kind;
  uint32_t src;
  int64_t lane;
  uint8_t rot;
  uint64_t mask;
};
struct IrNode {
  size_t lanes = 0;
  std::vector<uint32_t> start;  // CSR into terms, lanes + 1
  bool contractible = false;
  size_t slot = 0;  // contractible: its first chunk slot
  // Its first lane in the forward pass's lane buffer, and whether it
  // reads a public value or a constant (else it is zero when the tables
  // read as zero).
  size_t off = 0;
  bool konst_dep = false;
};
// The adjoint program's steps, in order:
//   kSum       var[a] = sum of var[list]
//   kContract  target += var[a] * d[pattern] per chunk (one product for
//              every target of the same var and pattern)
//   kChunks    slot chunks of B += slot chunks of A, through the shift
//   kOut       output words of leaf LEAF, lane L += slot chunks of A
struct Step {
  enum Kind : uint8_t { kSum, kContract, kChunk, kOut } kind;
  uint32_t a = 0, b = 0;
  uint32_t pattern = 0;
  // kContract: into slot B (to_leaf false) or leaf B's lane L, and into
  // each of LEAVES.
  bool to_leaf = false;
  int64_t lane = 0;
  struct Leaf {
    uint32_t b;
    int64_t lane;
  };
  std::vector<Leaf> leaves;
  static constexpr size_t kMaxLeaves = 8;
  // kChunk / kOut: chunk c of A goes to chunk (c - shift) of the target
  // when bit c of MASK.
  uint8_t shift = 0, chunk_mask = 0;
  std::vector<uint32_t> list;  // kSum
  // The template's blocks of its leaf targets: kContract's (the target
  // leaf B's first, then LEAVES'), kOut's one.
  std::vector<uint32_t> blocks;
};
// A leaf lane the steps write: lane LANE of leaf source LEAF, its chunks
// CHUNK_MASK. An instance's steps add into its blocks, [block][chunk][W],
// and the blocks then into the forms' words.
struct Block {
  uint32_t leaf;
  int64_t lane;
  uint8_t chunk_mask;
};
// Leaf source: template leaf node LEAF_NODE's binding ordinal ORD.
struct LeafSource {
  uint32_t leaf_node;
  uint32_t ord;
};
struct Template {
  size_t n = 0, lanes = 0;  // instance coordinates and lanes
  std::vector<IrNode> ir;
  std::vector<LaneTerm> terms;
  std::vector<uint32_t> roots;  // IR node per operand
  std::vector<LeafSource> leaves;
  std::vector<uint32_t> konst;  // DAG node of each constant source
  std::vector<Step> steps;
  std::vector<Block> blocks;
  // The patterns its contractions read, each once.
  std::vector<uint32_t> patterns;
  size_t vars = 0, slots = 0;
  size_t ir_lanes = 0;  // the forward pass's lanes
  bool reads_public = false;
  // The steps folded (BitViewMap::fold_steps): block BLOCK's chunk c gains
  // eq(lane0 + SRC) times chunk c of table TABLE, for each chunk c in
  // CHUNKS. Sorted by SRC.
  struct FoldEntry {
    uint32_t block;
    uint32_t table;
    int64_t src;
    uint8_t chunks;
  };
  // A term of a folded table: its chunk C_OUT gains Frob^-k(u_J) times
  // chunk C_SRC of pattern PATTERN, per twist k.
  struct FoldTerm {
    uint32_t j;
    uint32_t pattern;
    uint8_t c_src;
    uint8_t c_out;
    bool operator<(const FoldTerm &o) const {
      if (c_out != o.c_out) return c_out < o.c_out;
      if (j != o.j) return j < o.j;
      if (pattern != o.pattern) return pattern < o.pattern;
      return c_src < o.c_src;
    }
    bool operator==(const FoldTerm &o) const {
      return c_out == o.c_out && j == o.j && pattern == o.pattern &&
             c_src == o.c_src;
    }
  };
  std::vector<FoldEntry> fold;
  std::vector<std::vector<FoldTerm>> fold_tables;
  // Products of W twists: per instance by the steps (the operand lanes'
  // weights and the contractions) and by the folded entries (the eq
  // weights and the tables' chunks), and per proof and shift the folded
  // tables'.
  size_t step_products = 0, fold_products = 0, table_products = 0;
  // Its instances at shift 0 and at shift 32.
  size_t uses[2] = {0, 0};
};
// A predicate: its template, its first lane, its leaf sources' tables
// and base lanes, its constants, and its operand lanes' constant parts
// (all leaves zero) when it reads no public value.
struct Instance {
  uint32_t tmpl;
  size_t lane0;
  // The instance's first bit within its lane: 0, or 32 for an instance
  // of at most 32 coordinates that shares the lane of the one before.
  uint8_t shift = 0;
  std::vector<uint32_t> space;
  std::vector<int64_t> base;
  // Per leaf source: the forms' word of its base lane's first chunk and
  // the end of its table's words (kPublicWord for a public space).
  std::vector<int64_t> word0;
  std::vector<size_t> word_end;
  // Each constant source's bits, in lanes.
  std::vector<std::vector<uint64_t>> konst;
  std::vector<uint64_t> konst_lanes;  // [K][lanes]
  std::string name;
};
// Per leaf source of a template: the first and last lane (relative to
// its base) its adjoint steps write; first > last when they write none.
struct LeafLanes {
  std::vector<int64_t> first, last;
};
// Per leaf source of an instance: the forms' words its adjoint steps
// write lie in [lo, hi) (empty for none).
struct LeafWords {
  std::vector<size_t> lo, hi;
};
// A weight class of the bit phase (BitViewMap::bit_phase_tables): a folded
// template's (TMPL, SHIFT, table ID, CHUNK), or a pattern's chunk (pattern
// ID, CHUNK, SHIFT) for the templates on their steps.
struct PhaseClass {
  bool folded;
  uint32_t tmpl;
  uint8_t shift;
  uint32_t id;
  uint8_t chunk;
};
// The bit phase's references, by class: class k's references are START[k]
// .. START[k + 1]; reference r has weight LAM[r] (a lane below the map's
// lanes, else the steps vars from there) and words WORDS[WSTART[r] ..
// WSTART[r + 1]]. VAR_OFF: per instance on its steps, its vars' offset.
struct PhaseRefs {
  static constexpr uint64_t kNoVars = ~uint64_t(0);
  std::vector<PhaseClass> classes;
  std::vector<uint64_t> start;
  std::vector<uint32_t> lam;
  std::vector<uint64_t> wstart;
  std::vector<uint32_t> words;
  std::vector<uint64_t> var_off;
  uint64_t nvars = 0;
};

}  // namespace bit_view_internal

// Whether F counts its operations (CountingField, op_counts.h).
template <class F>
struct IsCountingField : std::false_type {};
template <class G>
struct IsCountingField<CountingField<G>> : std::true_type {};

template <class F, size_t W = 16>
class BitViewMap {
 public:
  using Elt = typename F::Elt;
  static constexpr size_t kChunks = 64 / W;
  static_assert(64 % W == 0, "words of a power-of-two width up to 64");
  static_assert(W % 4 == 0, "the adjoint's twists in groups of four");
  static_assert(kChunks <= 8, "a lane's chunks in a byte mask");
  // The op counts' map (op_counts.h) takes the chosen way always and runs
  // no self-check.
  static constexpr bool kCounting = IsCountingField<F>::value;

  using SrcKind = bit_view_internal::SrcKind;
  using LaneTerm = bit_view_internal::LaneTerm;
  using IrNode = bit_view_internal::IrNode;
  using Step = bit_view_internal::Step;
  using LeafSource = bit_view_internal::LeafSource;
  using Template = bit_view_internal::Template;
  using Instance = bit_view_internal::Instance;
  using Block = bit_view_internal::Block;
  using LeafLanes = bit_view_internal::LeafLanes;
  using LeafWords = bit_view_internal::LeafWords;
  static constexpr SrcKind kNode = bit_view_internal::kNode;
  static constexpr SrcKind kLeaf = bit_view_internal::kLeaf;
  static constexpr SrcKind kConst = bit_view_internal::kConst;
  static constexpr SrcKind kOne = bit_view_internal::kOne;

  BitViewMap(const F &f, std::string name, unsigned k,
             std::vector<BatchSpace> spaces, std::vector<Elt> dual)
      : f_(f), name_(std::move(name)), K_(k), dual_(std::move(dual)) {
    check(dual_.size() == W, "bit view map: the dual basis");
    for (const auto &s : spaces) add_space(s);
  }
  // O over the field F of the same elements (CountingField<G> over G, for
  // op_counts.h): the same program, instances and dual basis.
  template <class G>
  BitViewMap(const F &f, const BitViewMap<G, W> &o)
      : f_(f), name_(o.name_), K_(o.K_), spaces_(o.spaces_),
        space_word0_(o.space_word0_), words_(o.words_), dual_(o.dual_),
        tmpls_(o.tmpls_), tmpl_lanes_(o.tmpl_lanes_),
        inst_words_(o.inst_words_), tmpl_of_(o.tmpl_of_), insts_(o.insts_),
        lanes_(o.lanes_), half_open_(o.half_open_),
        pattern_used_{o.pattern_used_[0], o.pattern_used_[1]},
        patterns_(o.patterns_), pattern_of_(o.pattern_of_) {}

  // Appends space S (a predicate added later may read it); the earlier
  // spaces' words keep their places.
  void add_space(const BatchSpace &s) {
    space_word0_.push_back(words_);
    if (s.kind == BatchSpace::kTable) words_ += (s.size + W - 1) / W;
    spaces_.push_back(s);
  }

  // Adds predicate NAME with operands DAG (its roots, K of them).
  void add(const ViewDag<F> &dag, std::string name) {
    check(dag.roots.size() == K_, "bit view map: operands");
    std::vector<uint8_t> key = dag.key(f_, 64);
    // Which bindings read a public space: a template's constant part and
    // its adjoint's leaf steps follow from it, so a predicate whose leaf
    // reads a public value never shares the template of one whose leaf at
    // the same place reads a table.
    for (const auto &b : dag.bind)
      for (uint32_t sp : b.space) put_u64(key, spaces_.at(sp).kind);
    auto it = tmpl_of_.find(key);
    uint32_t t;
    if (it == tmpl_of_.end()) {
      t = uint32_t(tmpls_.size());
      tmpls_.push_back(compile(dag));
      tmpl_lanes_.push_back(out_lanes(tmpls_.back()));
      tmpl_of_[key] = t;
    } else {
      t = it->second;
    }
    const Template &tp = tmpls_[t];
    Instance in;
    in.tmpl = t;
    in.lane0 = lanes_;
    in.name = std::move(name);
    // Instances of at most 32 coordinates go two to a lane: the second
    // takes the upper half of the first's. A lane program's output bits
    // lie below its instance's size, so the halves do not overlap.
    const bool half = tp.lanes == 1 && tp.n <= 32;
    if (half && half_open_) {
      in.lane0 = lanes_ - 1;
      in.shift = 32;
    }
    for (const auto &ls : tp.leaves) {
      const auto &b = dag.bind[ls.leaf_node];
      const uint32_t sp = b.space[ls.ord];
      in.space.push_back(sp);
      in.base.push_back(int64_t(b.off[ls.ord] / 64));
      if (spaces_[sp].kind != BatchSpace::kTable) {
        in.word0.push_back(kPublicWord);
        in.word_end.push_back(0);
        continue;
      }
      in.word0.push_back(int64_t(space_word0_[sp]) +
                         in.base.back() * int64_t(kChunks));
      in.word_end.push_back(space_word0_[sp] +
                            (spaces_[sp].size + W - 1) / W);
    }
    for (uint32_t c : tp.konst) {
      const auto &x = *dag.nodes[c].values;
      std::vector<uint64_t> l((x.size() + 63) / 64, 0);
      for (size_t i = 0; i < x.size(); ++i)
        if (x[i] == f_.one()) l[i / 64] |= uint64_t(1) << (i % 64);
      in.konst.push_back(std::move(l));
    }
    // The d table of the instance's shift needs the template's patterns.
    auto &used = pattern_used_[in.shift == 0 ? 0 : 1];
    for (uint32_t q : tp.patterns) {
      if (used.size() <= q) used.resize(q + 1, false);
      used[q] = true;
    }
    ++tmpls_[t].uses[in.shift == 0 ? 0 : 1];
    if (in.shift == 0) lanes_ += tp.lanes;
    half_open_ = half && in.shift == 0;
    if (!tp.reads_public) {
      in.konst_lanes = forward(in, nullptr, nullptr, /*leaves=*/false);
    }
    inst_words_.push_back(leaf_words(tmpl_lanes_[t], in));
    insts_.push_back(std::move(in));
  }

  std::string name() const { return name_; }
  unsigned operands() const { return K_; }
  size_t lanes() const { return lanes_; }
  size_t words() const { return words_; }
  size_t templates() const { return tmpls_.size(); }
  size_t predicates() const { return insts_.size(); }
  const std::vector<BatchSpace> &spaces() const { return spaces_; }
  // The trace-dual basis of the words' bits the forms contract with.
  const std::vector<Elt> &dual() const { return dual_; }
  // The map's parameters for the digest: each template's structure and
  // each predicate's binding.
  std::vector<uint8_t> params() const {
    std::vector<uint8_t> out;
    put_u64(out, K_);
    put_u64(out, W);
    put_u64(out, spaces_.size());
    for (const auto &s : spaces_) {
      put_u64(out, s.kind);
      put_u64(out, s.node);
      put_u64(out, s.size);
    }
    put_u64(out, tmpls_.size());
    for (const auto &t : tmpls_) {
      put_u64(out, t.n);
      put_u64(out, t.ir.size());
      put_u64(out, t.terms.size());
      for (const auto &x : t.terms) {
        put_u64(out, x.kind);
        put_u64(out, x.src);
        put_u64(out, uint64_t(x.lane));
        put_u64(out, x.rot);
        put_u64(out, x.mask);
      }
      for (const auto &x : t.ir) {
        put_u64(out, x.lanes);
        for (uint32_t s : x.start) put_u64(out, s);
      }
      for (uint32_t r : t.roots) put_u64(out, r);
    }
    put_u64(out, insts_.size());
    for (const auto &in : insts_) {
      put_u64(out, in.tmpl);
      put_u64(out, in.shift);
      for (size_t s = 0; s < in.space.size(); ++s) {
        put_u64(out, in.space[s]);
        put_u64(out, uint64_t(in.base[s]));
      }
      for (const auto &c : in.konst) {
        put_u64(out, c.size());
        for (uint64_t x : c) put_u64(out, x);
      }
    }
    return out;
  }

  // The lane terms the forward pass reads over every instance (apply's
  // work; op_counts.h).
  uint64_t lane_terms() const {
    uint64_t n = 0;
    for (const auto &in : insts_) n += tmpls_[in.tmpl].terms.size();
    return n;
  }

  // The operand lanes of every instance, [lane][K], from the tables'
  // host words (W bits each, per table space) and the public values. Under
  // a runner (util/parallel.h) the instances run in chunks. A chunk
  // boundary never falls before an instance at shift 32, which shares the
  // lane of the one before it, so each chunk writes its own lanes. The
  // boundaries depend on the instances' shifts only.
  std::vector<uint64_t> apply(
      const std::vector<std::vector<uint64_t>> &table_lanes,
      const std::vector<std::vector<uint64_t>> &public_lanes) const {
    std::vector<uint64_t> out;
    apply_into(table_lanes, public_lanes, out);
    return out;
  }
  // apply into OUT, which keeps its capacity.
  void apply_into(const std::vector<std::vector<uint64_t>> &table_lanes,
                  const std::vector<std::vector<uint64_t>> &public_lanes,
                  std::vector<uint64_t> &out) const {
    out.assign(lanes_ * K_, 0);
    const size_t ni = insts_.size();
    const size_t grain = parallel::grain_for(ni, parallel::kChunks);
    const size_t nc = parallel::chunks(ni, grain);
    std::vector<size_t> bnd(nc + 1, ni);
    if (nc > 0) bnd[0] = 0;
    for (size_t q = 1; q < nc; ++q) {
      size_t i = std::max(q * grain, bnd[q - 1]);
      while (i < ni && insts_[i].shift != 0) ++i;
      bnd[q] = i;
    }
    parallel::for_each(nc, 1, [&](size_t q) {
      for (size_t i = bnd[q]; i < bnd[q + 1]; ++i) {
        const Instance &in = insts_[i];
        const auto v = forward(in, &table_lanes, &public_lanes, true);
        const Template &t = tmpls_[in.tmpl];
        for (unsigned j = 0; j < K_; ++j)
          for (size_t l = 0; l < t.lanes; ++l)
            out[(in.lane0 + l) * K_ + j] |= v[j * t.lanes + l] << in.shift;
      }
    });
  }

  // sum_j u_j L_j(r, s) = constant + sum_k Frob^k(<a_k, words>): the
  // operand claims at the skip point R (Lagrange weights LB over the w
  // skip points) and the row point S, combined by U, as W Frobenius forms
  // on the tables' words (concatenated in space order).
  BitForms<F> adjoint(unsigned width, const std::vector<Elt> &lb,
                      const std::vector<Elt> &s, const std::vector<Elt> &u,
                      const std::vector<std::vector<uint64_t>> &public_lanes)
      const {
    return adjoint_impl<W>(width, lb, s, u, public_lanes, dual_);
  }
  // The bit phase's word weights (bit_phase.h): with W_q[b] the claim's
  // coefficient on bit b of word q (sum_j u_j L_j(r, s) = constant +
  // sum_{q,b} W_q[b] t_{q,b}), alpha_q = sum_b EQ[b] W_q[b], one value per
  // word, and the same constant. The adjoint's programs with one untwisted
  // weight per entry and the basis EQ in place of the dual basis.
  BitForms<F> word_weights(unsigned width, const std::vector<Elt> &lb,
                           const std::vector<Elt> &s,
                           const std::vector<Elt> &u,
                           const std::vector<std::vector<uint64_t>> &public_lanes,
                           const std::vector<Elt> &eq) const {
    return adjoint_impl<1>(width, lb, s, u, public_lanes, eq);
  }

  // The bit phase's word references (bit_phase.h), built once before the
  // first bit_phase_tables (at compile time, single-threaded).
  void prepare_bit_phase() const {
    if (!phase_) phase_ = std::make_shared<const PhaseRefs>(phase_refs());
  }
  // The prover's tables of the bit phase: the claim's coefficients as
  // W_q[b] = sum_kappa lambda_{kappa,q} sigma_kappa[b] over weight classes
  // kappa, each class a public pattern sigma_kappa over a word's W bits and
  // a list of references (lambda, words) with public weights lambda.
  //   - A folded template's class is (template, shift, table, chunk): sigma
  //     is the chunk of its folded table untwisted, sum over its terms of
  //     u_j pattern[c_src][b], and a reference is an instance's fold entry
  //     with lambda = eq(s, lane0 + src), its word the entry's block word.
  //   - A template on its steps has a class per (pattern, chunk, shift):
  //     sigma is the pattern's chunk, and a reference is a contraction's
  //     chunk with lambda its var (a sum of u_j eq(s, lane)), its words
  //     every word the steps route the product to.
  // SIGMA[kappa W + b] = sigma_kappa[b] and G[kappa W + b] = sum over the
  // class's references of lambda times bit b of the XOR of their words'
  // host values HOST (W bits each, in the forms' word order).
  void bit_phase_tables(unsigned width, const std::vector<Elt> &lb,
                        const std::vector<Elt> &s, const std::vector<Elt> &u,
                        const std::vector<uint64_t> &host,
                        std::vector<Elt> &sigma, std::vector<Elt> &g) const {
    const F &f = f_;
    check(phase_ != nullptr, "bit phase: references not prepared");
    check(host.size() == words_, "bit phase: the tables' host words");
    const PhaseRefs &pr = *phase_;
    size_t nchunk = 64 / width, lgchunk = 0;
    while ((size_t(1) << lgchunk) < nchunk) ++lgchunk;
    check(s.size() >= lgchunk, "operand claim dimensions");
    const size_t lglane = s.size() - lgchunk;
    Eqs<F> eql(lgchunk, nchunk, s.data(), f);
    std::array<Elt, 64> low;
    for (size_t z = 0; z < 64; ++z)
      low[z] = f.mulf(eql.at(z / width), lb[z % width]);
    // The weights: eq(s, lane) for every lane, then the steps instances'
    // vars (W = 1).
    auto wscope = std::make_unique<profiling::Scope>("batch.bitphase.weights");
    std::vector<Elt> lam(lanes_ + pr.nvars, f.zero());
    {
      // eq(s, l) = lo[l mod 2^h] hi[l >> h], h = lglane / 2, in chunks of
      // lanes under a runner (field products are exact: Eqs' elements).
      const size_t h = lglane / 2, nlo = size_t(1) << h;
      const size_t nhi = std::max<size_t>((lanes_ + nlo - 1) >> h, 1);
      const Eqs<F> elo(h, nlo, s.data() + lgchunk, f);
      const Eqs<F> ehi(lglane - h, nhi, s.data() + lgchunk + h, f);
      parallel::for_chunks(lanes_, parallel::grain_for(lanes_, parallel::kChunks),
                           [&](size_t b, size_t e) {
                             for (size_t l = b; l < e; ++l)
                               lam[l] = f.mulf(elo.at(l & (nlo - 1)), ehi.at(l >> h));
                           });
    }
    parallel::for_chunks(
        insts_.size(), parallel::grain_for(insts_.size(), parallel::kChunks),
        [&](size_t b, size_t e) {
          for (size_t i = b; i < e; ++i) {
            if (pr.var_off[i] == kNoVars) continue;
            const Instance &in = insts_[i];
            const Template &t = tmpls_[in.tmpl];
            Elt *var = &lam[lanes_ + pr.var_off[i]];
            for (unsigned j = 0; j < K_; ++j)
              for (size_t l = 0; l < t.lanes; ++l)
                var[j * t.lanes + l] = f.mulf(u[j], lam[in.lane0 + l]);
            for (const Step &st : t.steps) {
              if (st.kind != Step::kSum) continue;
              Elt v = var[st.list[0]];
              for (size_t q = 1; q < st.list.size(); ++q) f.add(v, var[st.list[q]]);
              var[st.a] = v;
            }
          }
        });
    wscope.reset();
    // The classes' patterns.
    const size_t nk = pr.classes.size();
    sigma.assign(nk * W, f.zero());
    auto pat = [&](uint32_t p, size_t c, size_t shift, size_t b) {
      const LanePattern &pt = patterns_[p];
      const size_t z = W * c + b;
      if (((pt.mask >> z) & 1) == 0) return f.zero();
      return low[(z + pt.s + shift) % 64];
    };
    for (size_t k = 0; k < nk; ++k) {
      const PhaseClass &cl = pr.classes[k];
      Elt *sg = &sigma[k * W];
      if (cl.folded) {
        for (const auto &x : tmpls_[cl.tmpl].fold_tables[cl.id]) {
          if (x.c_out != cl.chunk) continue;
          for (size_t b = 0; b < W; ++b)
            f.add(sg[b], f.mulf(u[x.j], pat(x.pattern, x.c_src, cl.shift, b)));
        }
      } else {
        for (size_t b = 0; b < W; ++b) sg[b] = pat(cl.id, cl.chunk, cl.shift, b);
      }
    }
    // G per class, the classes in chunks: each reference's weight and the
    // XOR of its words' host values, a tile at a time, into bit-plane sums
    // (bit_planes.h). Every index is public; the host values are data.
    profiling::Scope gscope("batch.bitphase.accumulate");
    g.assign(nk * W, f.zero());
    parallel::for_chunks(nk, parallel::grain_for(nk, parallel::kChunks),
                         [&](size_t k0, size_t k1) {
      constexpr size_t kTile = BitPlaneSums<F>::kTile;
      std::vector<Elt> et(kTile);
      std::vector<uint64_t> tt(kTile);
      for (size_t k = k0; k < k1; ++k) {
        BitPlaneSums<F> acc(f, unsigned(W));
        const uint64_t r0 = pr.start[k], r1 = pr.start[k + 1];
        for (uint64_t r = r0; r < r1; r += kTile) {
          const size_t n = size_t(std::min<uint64_t>(kTile, r1 - r));
          for (size_t i = 0; i < n; ++i) {
            const uint64_t ref = r + i;
            et[i] = lam[pr.lam[ref]];
            uint64_t x = 0;
            for (uint64_t q = pr.wstart[ref]; q < pr.wstart[ref + 1]; ++q)
              x ^= host[pr.words[q]];
            tt[i] = x;
          }
          acc.add(et.data(), tt.data(), n);
        }
        for (size_t b = 0; b < W; ++b) g[k * W + b] = acc.get(unsigned(b));
      }
    });
  }

  // The adjoint with NT weights per entry: NT = W the Frobenius twists
  // k < W, NT = 1 the untwisted weight. Each pattern chunk is contracted
  // with BASIS (W elements): d[p][c][k] = sum_b Frob^-k(low[...]) basis_b.
  template <size_t NT>
  BitForms<F> adjoint_impl(
      unsigned width, const std::vector<Elt> &lb, const std::vector<Elt> &s,
      const std::vector<Elt> &u,
      const std::vector<std::vector<uint64_t>> &public_lanes,
      const std::vector<Elt> &basis) const {
    static_assert(NT == W || NT == 1, "the twists of a bit adjoint");
    const F &f = f_;
    check(basis.size() == W, "bit view map: the contraction basis");
    size_t nchunk = 64 / width, lgchunk = 0;
    while ((size_t(1) << lgchunk) < nchunk) ++lgchunk;
    check(s.size() >= lgchunk, "operand claim dimensions");
    const size_t lglane = s.size() - lgchunk, nlane = size_t(1) << lglane;
    check(nlane >= lanes_, "operand claim lane dimension");
    Eqs<F> eql(lgchunk, nchunk, s.data(), f);
    std::array<Elt, 64> low;
    for (size_t z = 0; z < 64; ++z)
      low[z] = f.mulf(eql.at(z / width), lb[z % width]);
    // The phase timers (util/prover_profile.h).
    auto fill_scope = std::make_unique<profiling::Scope>("batch.forms.fill");
    BitForms<F> out{filled_large(NT * words_, f.zero()), f.zero(), words_};
    fill_scope.reset();
    auto const_scope =
        std::make_unique<profiling::Scope>("batch.forms.constant");
    out.constant = constant(low, s, u, lglane, lgchunk, public_lanes);
    const_scope.reset();
    auto tab_scope = std::make_unique<profiling::Scope>("batch.forms.tables");
    // Every x^(2^-k), k < NT, of the point, u and low.
    std::vector<Elt> tw(lglane * NT), uk(K_ * NT), lk(64 * NT);
    for (size_t i = 0; i < lglane; ++i)
      inverse_frobenius_powers(s[lgchunk + i], NT, &tw[i * NT], f);
    for (unsigned j = 0; j < K_; ++j)
      inverse_frobenius_powers(u[j], NT, &uk[j * NT], f);
    for (size_t z = 0; z < 64; ++z)
      inverse_frobenius_powers(low[z], NT, &lk[z * NT], f);
    // The NT twists side by side: every weight below is NT elements, one
    // per k, so each step of the lane programs is decoded once for all of
    // them. eq(Frob^-k(s), l) = lo[l mod 2^h][k] hi[l >> h][k], h = lglane
    // / 2: two tables of about sqrt(lanes) entries per twist in place of
    // one of the lanes per twist.
    const size_t h = lglane / 2, nlo = size_t(1) << h;
    const size_t nhi = std::max<size_t>((lanes_ + nlo - 1) >> h, 1);
    std::vector<Elt> lo(nlo * NT), hi(nhi * NT);
    {
      std::vector<Elt> twisted(lglane);
      for (size_t k = 0; k < NT; ++k) {
        for (size_t i = 0; i < lglane; ++i) twisted[i] = tw[i * NT + k];
        Eqs<F> elo(h, nlo, twisted.data(), f);
        Eqs<F> ehi(lglane - h, nhi, twisted.data() + h, f);
        for (size_t l = 0; l < nlo; ++l) lo[l * NT + k] = elo.at(l);
        for (size_t l = 0; l < nhi; ++l) hi[l * NT + k] = ehi.at(l);
      }
    }
    // d[p][c][k] = sum_b Frob^-k(low[(W c + b + s_p + shift) mod 64])
    // [mask_p bit W c + b] basis_b, for the instances at bit SHIFT of their
    // lane (0, and 32 for those in an upper half), for the patterns USED at
    // that shift (the others stay zero; no step reads them).
    auto d_table = [&](size_t shift, const std::vector<bool> &used) {
      std::vector<Elt> d(patterns_.size() * kChunks * NT, f.zero());
      for (size_t p = 0; p < patterns_.size(); ++p) {
        if (p >= used.size() || !used[p]) continue;
        const LanePattern &pt = patterns_[p];
        for (size_t c = 0; c < kChunks; ++c)
          for (size_t k = 0; k < NT; ++k) {
            typename F::Accum acc{};
            bool any = false;
            for (size_t b = 0; b < W; ++b) {
              const size_t z = W * c + b;
              if (((pt.mask >> z) & 1) == 0) continue;
              f.mac(acc, lk[((z + pt.s + shift) % 64) * NT + k], basis[b]);
              any = true;
            }
            d[(p * kChunks + c) * NT + k] = any ? f.reduce(acc) : f.zero();
          }
      }
      return d;
    };
    const std::vector<Elt> d = d_table(0, pattern_used_[0]);
    const std::vector<Elt> d32 = pattern_used_[1].empty()
                                     ? std::vector<Elt>{}
                                     : d_table(32, pattern_used_[1]);
    // Per template: whether its instances take the folded products
    // (folded), and whether they also run the steps, for the test-only
    // self-check (test_switches.h). Both follow from the public shape only.
    const bool self_check = !kCounting && test_switches().adjoint_check;
    std::vector<uint8_t> use_fold(tmpls_.size());
    bool any_steps = self_check;
    for (size_t ti = 0; ti < tmpls_.size(); ++ti) {
      use_fold[ti] = folded(tmpls_[ti]);
      if (!use_fold[ti]) any_steps = true;
    }
    using Tw = TwistOps<F, NT>;
    // The folded tables of each template at each shift its instances take:
    // chunk c of table q is the sum over its terms of Frob^-k(u_j) d[p]
    // [c_src], per twist k, into [tables][chunks][NT].
    std::vector<std::array<std::vector<Elt>, 2>> ftab(tmpls_.size());
    {
      std::array<Elt, NT> pr;
      for (size_t ti = 0; ti < tmpls_.size(); ++ti) {
        const Template &t = tmpls_[ti];
        if (!use_fold[ti] && !self_check) continue;
        for (size_t sh = 0; sh < 2; ++sh) {
          if (t.uses[sh] == 0) continue;
          const std::vector<Elt> &dd = sh == 0 ? d : d32;
          auto &tab = ftab[ti][sh];
          tab.assign(t.fold_tables.size() * kChunks * NT, f.zero());
          for (size_t q = 0; q < t.fold_tables.size(); ++q)
            for (const auto &x : t.fold_tables[q]) {
              Tw::mul(f, pr.data(), &uk[size_t(x.j) * NT],
                      &dd[(size_t(x.pattern) * kChunks + x.c_src) * NT]);
              Tw::add(f, &tab[(q * kChunks + x.c_out) * NT], pr.data());
            }
        }
      }
    }
    tab_scope.reset();
    profiling::Scope steps_scope("batch.forms.steps");
    // u_j eq(Frob^-k(s), hi part), per hi entry: an operand lane's weight
    // is then one product with its lo part, u_j hi lo = u_j eq.
    std::vector<Elt> uh;
    if (any_steps) {
      uh.resize(nhi * K_ * NT);
      for (size_t x = 0; x < nhi; ++x)
        for (unsigned j = 0; j < K_; ++j)
          Tw::mul(f, &uh[(x * K_ + j) * NT], &uk[j * NT], &hi[x * NT]);
    }
    // The instances' steps or folded products, from B to E, into the
    // forms A ([NT][STRIDE]); with PLACED, DELTA(I, DL) sets each leaf
    // source's word offset (place).
    auto steps = [&](auto placed, size_t b, size_t e, Elt *a, size_t stride,
                     const auto &delta) {
      constexpr bool kPlaced = decltype(placed)::value;
      std::vector<Elt> var, slot, loc, chk;
      std::vector<int64_t> dl;
      std::vector<size_t> first;
      for (size_t i = b; i < e; ++i) {
        const Instance &in = insts_[i];
        const Template &t = tmpls_[in.tmpl];
        const size_t nloc = t.blocks.size() * kChunks * NT;
        if (loc.size() < nloc) loc.resize(nloc, f.zero());
        const bool fold = use_fold[in.tmpl] != 0;
        if (fold || self_check) {
          run_fold<NT>(t, ftab[in.tmpl][in.shift == 0 ? 0 : 1], in.lane0, lo,
                       hi, h, loc);
        }
        if (self_check) {
          chk.assign(loc.begin(), loc.begin() + nloc);
          std::fill(loc.begin(), loc.begin() + nloc, f.zero());
        }
        if (!fold || self_check) {
          // Every var is written (an operand lane's weight or a sum) before
          // it is read; slots and blocks accumulate (flush zeros the
          // blocks).
          if (var.size() < t.vars * NT) var.resize(t.vars * NT);
          slot.assign(t.slots * kChunks * NT, f.zero());
          for (size_t l = 0; l < t.lanes; ++l) {
            const size_t g = in.lane0 + l;
            const Elt *el = &lo[(g & (nlo - 1)) * NT];
            const Elt *ul = &uh[(g >> h) * K_ * NT];
            for (unsigned j = 0; j < K_; ++j)
              Tw::mul(f, &var[(j * t.lanes + l) * NT], &ul[j * NT], el);
          }
          run_steps<NT>(t, in.shift == 0 ? d : d32, var, slot, loc);
        }
        if (self_check) {
          for (size_t q = 0; q < nloc; ++q)
            check(chk[q] == loc[q],
                  "bit view map: the folded adjoint differs from the steps");
        }
        if constexpr (kPlaced) delta(i, dl);
        place(t, in, kPlaced ? dl.data() : nullptr, stride, first);
        flush<NT>(t, loc, first, a, stride);
      }
    };
    // Chunks of instances (util/parallel.h), each into its own forms over
    // the words its instances write (chunk_words), then added into OUT
    // word by word in chunk order. One chunk, or chunks whose words add up
    // to more than four times the forms' (a bound on the copies' memory),
    // write OUT directly in instance order.
    const size_t ni = insts_.size();
    const size_t grain = parallel::grain_for(ni, parallel::kChunks);
    const size_t nc = parallel::chunks(ni, grain);
    std::vector<ChunkWords> cws(nc);
    if (nc > 1)
      parallel::for_chunks(ni, grain, [&](size_t b, size_t e) {
        cws[b / grain] = chunk_words(b, e);
      });
    size_t total = 0;
    for (const auto &cw : cws) total += cw.size;
    if (nc < 2 || total > 4 * words_) {
      steps(std::false_type{}, 0, ni, out.a.data(), words_,
            [](size_t, std::vector<int64_t> &) {});
      return out;
    }
    std::vector<std::vector<Elt>> part(nc);
    parallel::for_chunks(ni, grain, [&](size_t b, size_t e) {
      const ChunkWords &cw = cws[b / grain];
      auto &pa = part[b / grain];
      pa.assign(NT * cw.size, f.zero());
      steps(std::true_type{}, b, e, pa.data(), cw.size,
            [&](size_t i, std::vector<int64_t> &dl) { deltas(i, cw, dl); });
    });
    const size_t wgrain = parallel::grain_for(words_, parallel::kChunks);
    parallel::for_chunks(words_, wgrain, [&](size_t wb, size_t we) {
      for (size_t c = 0; c < nc; ++c)
        for (const Interval &x : cws[c].iv) {
          const size_t b = std::max(wb, x.lo);
          const size_t e = std::min(we, x.hi);
          if (b >= e) continue;
          for (size_t k = 0; k < NT; ++k) {
            Elt *o = out.a.data() + k * words_;
            const Elt *p = part[c].data() + k * cws[c].size + x.off;
            for (size_t w = b; w < e; ++w) f.add(o[w], p[w - x.lo]);
          }
        }
    });
    return out;
  }

 private:
  using PhaseClass = bit_view_internal::PhaseClass;
  using PhaseRefs = bit_view_internal::PhaseRefs;
  static constexpr uint64_t kNoVars = bit_view_internal::PhaseRefs::kNoVars;

  // Per contraction step and chunk of T (index step kChunks + c), the
  // (block, chunk) its product reaches through the chunk steps, pairs
  // cancelled: the steps run symbolically on the products' indices.
  std::vector<std::vector<std::pair<uint32_t, uint8_t>>> routes(
      const Template &t) const {
    constexpr uint64_t kFull = W == 64 ? ~uint64_t(0) : (uint64_t(1) << W) - 1;
    std::vector<std::vector<uint32_t>> slot(t.slots * kChunks),
        blk(t.blocks.size() * kChunks);
    for (size_t si = 0; si < t.steps.size(); ++si) {
      const Step &s = t.steps[si];
      if (s.kind == Step::kContract) {
        const uint64_t mask = patterns_[s.pattern].mask;
        for (size_t c = 0; c < kChunks; ++c) {
          if (((mask >> (W * c)) & kFull) == 0) continue;
          const uint32_t id = uint32_t(si * kChunks + c);
          if (!s.to_leaf) slot[s.b * kChunks + c].push_back(id);
          for (uint32_t b : s.blocks) blk[b * kChunks + c].push_back(id);
        }
      } else if (s.kind == Step::kChunk || s.kind == Step::kOut) {
        for (size_t c = 0; c < kChunks; ++c) {
          if (((s.chunk_mask >> c) & 1) == 0) continue;
          const size_t c2 = (c + kChunks - s.shift) % kChunks;
          auto &dst = s.kind == Step::kChunk ? slot[s.b * kChunks + c2]
                                             : blk[s.blocks[0] * kChunks + c2];
          // A copy: the target may be the source.
          const std::vector<uint32_t> src = slot[s.a * kChunks + c];
          dst.insert(dst.end(), src.begin(), src.end());
        }
      }
    }
    std::vector<std::vector<std::pair<uint32_t, uint8_t>>> out(t.steps.size() *
                                                               kChunks);
    for (size_t b = 0; b < t.blocks.size(); ++b)
      for (size_t c = 0; c < kChunks; ++c) {
        auto &x = blk[b * kChunks + c];
        std::sort(x.begin(), x.end());
        for (size_t i = 0; i < x.size();) {
          size_t j = i;
          while (j < x.size() && x[j] == x[i]) ++j;
          if ((j - i) % 2 == 1) out[x[i]].push_back({uint32_t(b), uint8_t(c)});
          i = j;
        }
      }
    return out;
  }

  // The bit phase's classes and references (bit_phase_tables), from the
  // public templates and bindings only.
  PhaseRefs phase_refs() const {
    constexpr uint64_t kFull = W == 64 ? ~uint64_t(0) : (uint64_t(1) << W) - 1;
    PhaseRefs pr;
    std::map<std::tuple<bool, uint32_t, uint8_t, uint32_t, uint8_t>, uint32_t>
        id_of;
    // Per class, its references' weights, word counts and words.
    std::vector<std::vector<uint32_t>> lam, cnt, wds;
    auto cls = [&](bool folded, uint32_t tmpl, uint8_t sh, uint32_t id,
                   uint8_t c) {
      auto [it, fresh] = id_of.emplace(std::make_tuple(folded, tmpl, sh, id, c),
                                       uint32_t(pr.classes.size()));
      if (fresh) {
        pr.classes.push_back({folded, tmpl, sh, id, c});
        lam.emplace_back();
        cnt.emplace_back();
        wds.emplace_back();
      }
      return it->second;
    };
    std::vector<uint8_t> fold(tmpls_.size());
    std::vector<std::vector<std::vector<std::pair<uint32_t, uint8_t>>>> rt(
        tmpls_.size());
    for (size_t ti = 0; ti < tmpls_.size(); ++ti) {
      fold[ti] = folded(tmpls_[ti]);
      if (!fold[ti]) rt[ti] = routes(tmpls_[ti]);
    }
    pr.var_off.assign(insts_.size(), kNoVars);
    std::vector<size_t> first;
    for (size_t i = 0; i < insts_.size(); ++i) {
      const Instance &in = insts_[i];
      const Template &t = tmpls_[in.tmpl];
      const uint8_t sh = in.shift;
      place(t, in, nullptr, words_, first);
      if (fold[in.tmpl]) {
        for (const auto &x : t.fold)
          for (size_t c = 0; c < kChunks; ++c) {
            if (((x.chunks >> c) & 1) == 0 || first[x.block] == SIZE_MAX)
              continue;
            const uint32_t k = cls(true, in.tmpl, sh, x.table, uint8_t(c));
            lam[k].push_back(uint32_t(in.lane0 + size_t(x.src)));
            cnt[k].push_back(1);
            wds[k].push_back(uint32_t(first[x.block] + c));
          }
        continue;
      }
      pr.var_off[i] = pr.nvars;
      for (size_t si = 0; si < t.steps.size(); ++si) {
        const Step &s = t.steps[si];
        if (s.kind != Step::kContract) continue;
        const uint64_t mask = patterns_[s.pattern].mask;
        for (size_t c = 0; c < kChunks; ++c) {
          if (((mask >> (W * c)) & kFull) == 0) continue;
          const auto &dest = rt[in.tmpl][si * kChunks + c];
          uint32_t n = 0;
          for (const auto &[b, co] : dest)
            if (first[b] != SIZE_MAX) ++n;
          if (n == 0) continue;
          const uint32_t k = cls(false, 0, sh, s.pattern, uint8_t(c));
          lam[k].push_back(uint32_t(lanes_ + pr.nvars + s.a));
          cnt[k].push_back(n);
          for (const auto &[b, co] : dest)
            if (first[b] != SIZE_MAX) wds[k].push_back(uint32_t(first[b] + co));
        }
      }
      pr.nvars += t.vars;
    }
    check(lanes_ + pr.nvars < (uint64_t(1) << 32) && words_ < (uint64_t(1) << 32),
          "bit phase: 32-bit reference indices");
    pr.start.push_back(0);
    pr.wstart.push_back(0);
    for (size_t k = 0; k < pr.classes.size(); ++k) {
      for (size_t r = 0, q = 0; r < lam[k].size(); ++r) {
        pr.lam.push_back(lam[k][r]);
        for (uint32_t m = 0; m < cnt[k][r]; ++m) pr.words.push_back(wds[k][q++]);
        pr.wstart.push_back(pr.words.size());
      }
      pr.start.push_back(pr.lam.size());
      std::vector<uint32_t>().swap(lam[k]);
      std::vector<uint32_t>().swap(cnt[k]);
      std::vector<uint32_t>().swap(wds[k]);
    }
    return pr;
  }

  // The adjoint's constant: sum_j u_j eq(s, l) <low, constant lane>,
  // untwisted, from the instance weights LOW within a lane and the lane
  // variables of S (LGLANE of them after LGCHUNK).
  Elt constant(const std::array<Elt, 64> &low, const std::vector<Elt> &s,
               const std::vector<Elt> &u, size_t lglane, size_t lgchunk,
               const std::vector<std::vector<uint64_t>> &public_lanes) const {
    const F &f = f_;
    Elt out = f.zero();
    // Sums of low over each byte's set bits.
    std::vector<std::array<Elt, 256>> lowbyte(8);
    for (size_t b = 0; b < 8; ++b) {
      lowbyte[b][0] = f.zero();
      for (size_t v = 1; v < 256; ++v) {
        const size_t z = size_t(__builtin_ctz(unsigned(v)));
        lowbyte[b][v] = f.addf(lowbyte[b][v & (v - 1)], low[8 * b + z]);
      }
    }
    // eq(s, l) = lo[l mod 2^h] hi[l >> h], h = lglane / 2: two tables of
    // about sqrt(lanes) entries (field products are exact, so the same
    // element as one table of the lanes).
    const size_t h = lglane / 2, nlo = size_t(1) << h;
    const size_t nhi = std::max<size_t>((lanes_ + nlo - 1) >> h, 1);
    const Eqs<F> elo(h, nlo, s.data() + lgchunk, f);
    const Eqs<F> ehi(lglane - h, nhi, s.data() + lgchunk + h, f);
    // The instances in chunks under a runner (util/parallel.h), each
    // chunk's sum added in chunk order. Every value here is public.
    const size_t ni = insts_.size();
    const size_t grain = parallel::grain_for(ni, parallel::kChunks);
    std::vector<Elt> part(parallel::chunks(ni, grain), f.zero());
    parallel::for_chunks(ni, grain, [&](size_t i0, size_t i1) {
      Elt acc = f.zero();
      std::vector<uint64_t> cl;
      for (size_t i = i0; i < i1; ++i) {
        const Instance &in = insts_[i];
        const Template &t = tmpls_[in.tmpl];
        const std::vector<uint64_t> *kc = &in.konst_lanes;
        if (t.reads_public) {
          cl = forward(in, nullptr, &public_lanes, false);
          kc = &cl;
        }
        // Per lane: sum_j u_j <low, constant lane j>, then its eq weight.
        for (size_t l = 0; l < t.lanes; ++l) {
          Elt x = f.zero();
          bool any = false;
          for (unsigned j = 0; j < K_; ++j) {
            const uint64_t c = (*kc)[j * t.lanes + l] << in.shift;
            if (c == 0) continue;
            Elt v = f.zero();
            for (size_t b = 0; b < 8; ++b)
              f.add(v, lowbyte[b][(c >> (8 * b)) & 255]);
            f.add(x, f.mulf(u[j], v));
            any = true;
          }
          if (!any) continue;
          const size_t g = in.lane0 + l;
          f.add(acc, f.mulf(f.mulf(elo.at(g & (nlo - 1)), ehi.at(g >> h)), x));
        }
      }
      part[i0 / grain] = acc;
    });
    for (const Elt &x : part) f.add(out, x);
    return out;
  }

  // The lane program of DAG, with its adjoint steps.
  Template compile(const ViewDag<F> &dag) {
    using D = ViewDag<F>;
    Template t;
    const size_t nv = dag.nodes.size();
    t.n = dag.nodes[dag.roots[0]].n;
    for (uint32_t r : dag.roots)
      check(dag.nodes[r].n == t.n, "bit view map: operand sizes");
    t.lanes = (t.n + 63) / 64;
    // Materialized nodes: the operands, values read twice, and sums.
    std::vector<size_t> parents(nv, 0);
    for (const auto &x : dag.nodes)
      for (uint32_t k : x.kids) ++parents[k];
    std::vector<int64_t> ir_of(nv, -1);
    std::vector<uint32_t> ir_dag;
    auto is_source = [&](size_t v) {
      return dag.nodes[v].op == D::kLeaf || dag.nodes[v].op == D::kConst;
    };
    std::vector<bool> root(nv, false);
    for (uint32_t r : dag.roots) root[r] = true;
    for (size_t v = 0; v < nv; ++v) {
      if (is_source(v) && !root[v]) continue;
      if (root[v] || parents[v] >= 2 || dag.nodes[v].op == D::kSum) {
        ir_of[v] = int64_t(ir_dag.size());
        ir_dag.push_back(uint32_t(v));
      }
    }
    // Leaf sources and constant sources, numbered on first use.
    std::map<std::pair<uint32_t, uint32_t>, uint32_t> leaf_src;
    std::map<uint32_t, uint32_t> const_src;
    auto leaf_id = [&](uint32_t v, uint32_t ord) {
      auto [it, fresh] = leaf_src.emplace(std::make_pair(v, ord),
                                          uint32_t(t.leaves.size()));
      if (fresh) t.leaves.push_back({v, ord});
      return it->second;
    };
    auto const_id = [&](uint32_t v) {
      auto [it, fresh] = const_src.emplace(v, uint32_t(t.konst.size()));
      if (fresh) t.konst.push_back(v);
      return it->second;
    };
    struct Src {
      SrcKind kind;
      uint32_t id;
      size_t pos;
      bool operator<(const Src &o) const {
        return std::tie(kind, id, pos) < std::tie(o.kind, o.id, o.pos);
      }
      bool operator==(const Src &o) const {
        return kind == o.kind && id == o.id && pos == o.pos;
      }
    };
    // The sources of coordinate I of node V, read from inside the IR node
    // SELF.
    std::function<void(uint32_t, size_t, uint32_t, std::vector<Src> &)> exp =
        [&](uint32_t v, size_t i, uint32_t self, std::vector<Src> &out) {
          const auto &x = dag.nodes[v];
          if (v != self && ir_of[v] >= 0) {
            out.push_back({kNode, uint32_t(ir_of[v]), i});
            return;
          }
          switch (x.op) {
            case D::kLeaf: {
              const SourceRef &r = x.refs[i];
              if (r.space == SourceRef::kZero) return;
              const uint32_t ord =
                  uint32_t(D::ordinal(dag.bind[v], r.space));
              out.push_back({kLeaf, leaf_id(v, ord), r.pos});
              return;
            }
            case D::kConst:
              out.push_back({kConst, const_id(v), i});
              return;
            case D::kAdd:
              exp(x.kids[0], i, self, out);
              exp(x.kids[1], i, self, out);
              return;
            case D::kScale:
              if (x.k == f_.one()) exp(x.kids[0], i, self, out);
              return;
            case D::kGather: {
              size_t j = x.idx[i];
              for (uint32_t k : x.kids) {
                if (j < dag.nodes[k].n) {
                  exp(k, j, self, out);
                  return;
                }
                j -= dag.nodes[k].n;
              }
              check(false, "a gather's index");
              return;
            }
            case D::kBroadcast:
              exp(x.kids[0], 0, self, out);
              return;
            case D::kSum: {
              const size_t m = dag.nodes[x.kids[0]].n;
              const size_t w = x.w == 0 ? m : x.w;
              for (size_t j = 0; j < w; ++j)
                exp(x.kids[0], (x.w == 0 ? 0 : i * w) + j, self, out);
              return;
            }
            case D::kMask:
              if ((*x.values)[i] == f_.one()) exp(x.kids[0], i, self, out);
              return;
            case D::kNot:
              exp(x.kids[0], i, self, out);
              out.push_back({kOne, 0, i});
              return;
          }
        };
    // Each IR node's lanes: per coordinate its sources (pairs cancel),
    // grouped by (source, source lane, rotation) into masks.
    for (uint32_t v : ir_dag) {
      IrNode node;
      const size_t n = dag.nodes[v].n;
      node.lanes = (n + 63) / 64;
      node.start.push_back(uint32_t(t.terms.size()));
      std::vector<Src> src;
      for (size_t l = 0; l < node.lanes; ++l) {
        std::map<std::tuple<SrcKind, uint32_t, int64_t, uint8_t>, uint64_t> by;
        for (size_t z = 0; z < 64 && 64 * l + z < n; ++z) {
          src.clear();
          exp(v, 64 * l + z, v, src);
          std::sort(src.begin(), src.end());
          for (size_t a = 0; a < src.size();) {
            size_t b = a;
            while (b < src.size() && src[b] == src[a]) ++b;
            if ((b - a) % 2 == 1) {
              const Src &x = src[a];
              int64_t lane = 0;
              size_t p = 0;
              if (x.kind == kLeaf) {
                // Relative to the binding's base lane.
                const auto &ls = t.leaves[x.id];
                const size_t off = dag.bind[ls.leaf_node].off[ls.ord];
                lane = int64_t(x.pos / 64) - int64_t(off / 64);
                p = x.pos % 64;
              } else if (x.kind == kOne) {
                lane = 0;
                p = z;
              } else {
                lane = int64_t(x.pos / 64);
                p = x.pos % 64;
              }
              const uint8_t rot = uint8_t((z + 64 - p) % 64);
              by[{x.kind, x.id, lane, rot}] ^= uint64_t(1) << z;
            }
            a = b;
          }
        }
        for (const auto &[k, m] : by) {
          if (m == 0) continue;
          t.terms.push_back({std::get<0>(k), std::get<1>(k), std::get<2>(k),
                             std::get<3>(k), m});
        }
        node.start.push_back(uint32_t(t.terms.size()));
      }
      t.ir.push_back(std::move(node));
    }
    for (uint32_t r : dag.roots) t.roots.push_back(uint32_t(ir_of[r]));
    std::vector<bool> public_leaf(t.leaves.size(), false);
    for (size_t q = 0; q < t.leaves.size(); ++q) {
      const auto &ls = t.leaves[q];
      if (spaces_[dag.bind[ls.leaf_node].space[ls.ord]].kind ==
          BatchSpace::kPublic) {
        t.reads_public = true;
        public_leaf[q] = true;
      }
    }
    for (auto &x : t.ir) {
      x.off = t.ir_lanes;
      t.ir_lanes += x.lanes;
      for (uint32_t q = x.start.front(); q < x.start.back(); ++q) {
        const LaneTerm &term = t.terms[q];
        if (term.kind == kConst || term.kind == kOne ||
            (term.kind == kLeaf && public_leaf[term.src]) ||
            (term.kind == kNode && t.ir[term.src].konst_dep))
          x.konst_dep = true;
      }
    }
    adjoint_steps(t);
    leaf_blocks(t);
    fold_steps(t);
    for (const Step &st : t.steps)
      if (st.kind == Step::kContract) t.patterns.push_back(st.pattern);
    std::sort(t.patterns.begin(), t.patterns.end());
    t.patterns.erase(std::unique(t.patterns.begin(), t.patterns.end()),
                     t.patterns.end());
    return t;
  }

  // Whether a term moves whole words: a rotation by whole words and a mask
  // of whole words. Then CHUNK_MASK has bit c for each word c it keeps.
  static bool whole_words(const LaneTerm &x, uint8_t &chunk_mask) {
    if (x.rot % W != 0) return false;
    chunk_mask = 0;
    const uint64_t full = W == 64 ? ~uint64_t(0) : (uint64_t(1) << W) - 1;
    for (size_t c = 0; c < kChunks; ++c) {
      const uint64_t part = (x.mask >> (W * c)) & full;
      if (part == full) {
        chunk_mask |= uint8_t(1) << c;
      } else if (part != 0) {
        return false;
      }
    }
    return true;
  }
  uint32_t pattern_id(const LanePattern &p) {
    auto [it, fresh] = pattern_of_.emplace(p, uint32_t(patterns_.size()));
    if (fresh) patterns_.push_back(p);
    return it->second;
  }

  // The adjoint steps of T: weight patterns from the operand lanes
  // backwards, contracted where the rest moves whole words.
  void adjoint_steps(Template &t) {
    const size_t nir = t.ir.size();
    // Contractible: every term of every lane moves whole words, from a
    // contractible node or a leaf. Kids come first in t.ir.
    for (size_t v = 0; v < nir; ++v) {
      bool ok = true;
      const IrNode &x = t.ir[v];
      for (uint32_t q = x.start.front(); q < x.start.back() && ok; ++q) {
        const LaneTerm &term = t.terms[q];
        if (term.kind == kConst || term.kind == kOne) continue;
        uint8_t cm;
        if (!whole_words(term, cm)) ok = false;
        if (term.kind == kNode && !t.ir[term.src].contractible) ok = false;
      }
      t.ir[v].contractible = ok;
      if (ok) {
        t.ir[v].slot = t.slots;
        t.slots += x.lanes;
      }
    }
    // Entries: per (node, lane) and (leaf, lane), pattern -> vars.
    using Entries = std::map<LanePattern, std::vector<uint32_t>>;
    std::vector<std::vector<Entries>> at(nir);
    for (size_t v = 0; v < nir; ++v) at[v].resize(t.ir[v].lanes);
    std::map<std::pair<uint32_t, int64_t>, Entries> leaf_at;
    t.vars = K_ * t.lanes;
    for (unsigned j = 0; j < K_; ++j)
      for (size_t l = 0; l < t.lanes; ++l)
        at[t.roots[j]][l][LanePattern{0, ~uint64_t(0)}].push_back(
            uint32_t(j * t.lanes + l));
    // The var of one entry: pairs cancel (a weight reached twice adds to
    // zero in characteristic 2); several make a sum.
    auto resolve = [&](std::vector<uint32_t> vars) -> std::optional<uint32_t> {
      std::sort(vars.begin(), vars.end());
      std::vector<uint32_t> odd;
      for (size_t a = 0; a < vars.size();) {
        size_t b = a;
        while (b < vars.size() && vars[b] == vars[a]) ++b;
        if ((b - a) % 2 == 1) odd.push_back(vars[a]);
        a = b;
      }
      if (odd.empty()) return std::nullopt;
      if (odd.size() == 1) return odd[0];
      Step s;
      s.kind = Step::kSum;
      s.a = uint32_t(t.vars++);
      s.list = std::move(odd);
      t.steps.push_back(std::move(s));
      return t.steps.back().a;
    };
    // The contraction of each (var, pattern), whose product later leaf
    // targets reuse.
    std::map<std::pair<uint32_t, uint32_t>, size_t> contracted;
    auto contract = [&](uint32_t var, const LanePattern &p, bool to_leaf,
                        uint32_t target, int64_t lane) {
      const uint32_t pid = pattern_id(p);
      const auto key = std::make_pair(var, pid);
      const auto it = contracted.find(key);
      // At most kMaxLeaves leaf targets per product.
      if (to_leaf && it != contracted.end() &&
          t.steps[it->second].leaves.size() + 1 < Step::kMaxLeaves) {
        t.steps[it->second].leaves.push_back({target, lane});
        return;
      }
      contracted[key] = t.steps.size();
      Step s;
      s.kind = Step::kContract;
      s.a = var;
      s.pattern = pid;
      s.to_leaf = to_leaf;
      s.b = target;
      s.lane = lane;
      t.steps.push_back(std::move(s));
    };
    for (size_t v = nir; v-- > 0;) {
      const IrNode &x = t.ir[v];
      for (size_t l = 0; l < x.lanes; ++l) {
        for (const auto &[p, vars] : at[v][l]) {
          const auto var = resolve(vars);
          if (!var) continue;
          if (x.contractible) {
            contract(*var, p, false, uint32_t(x.slot + l), 0);
            continue;
          }
          for (uint32_t q = x.start[l]; q < x.start[l + 1]; ++q) {
            const LaneTerm &term = t.terms[q];
            if (term.kind == kConst || term.kind == kOne) continue;
            // Through rotl(src, rot) & mask: s' = s + rot, mask' =
            // rotr(mask & term mask, rot).
            const LanePattern q2{uint8_t((p.s + term.rot) % 64),
                                 rotr64(p.mask & term.mask, term.rot)};
            if (q2.mask == 0) continue;
            if (term.kind == kNode) {
              at[term.src][size_t(term.lane)][q2].push_back(*var);
            } else {
              leaf_at[{term.src, term.lane}][q2].push_back(*var);
            }
          }
        }
        at[v][l].clear();
        if (!x.contractible) continue;
        // Whole words onward: the slot's chunks to each source.
        for (uint32_t q = x.start[l]; q < x.start[l + 1]; ++q) {
          const LaneTerm &term = t.terms[q];
          if (term.kind == kConst || term.kind == kOne) continue;
          uint8_t cm = 0;
          check(whole_words(term, cm), "a contractible node's term");
          Step s;
          s.kind = term.kind == kNode ? Step::kChunk : Step::kOut;
          s.a = uint32_t(x.slot + l);
          s.b = term.kind == kNode
                    ? uint32_t(t.ir[term.src].slot + size_t(term.lane))
                    : term.src;
          s.lane = term.lane;
          s.shift = uint8_t(term.rot / W);
          s.chunk_mask = cm;
          t.steps.push_back(std::move(s));
        }
      }
    }
    for (const auto &[key, e] : leaf_at)
      for (const auto &[p, vars] : e) {
        const auto var = resolve(vars);
        if (var) contract(*var, p, true, key.first, key.second);
      }
  }

  // The blocks of T's leaf targets, each (leaf, lane) once, with the chunks
  // its steps write.
  void leaf_blocks(Template &t) const {
    constexpr uint64_t kFull = W == 64 ? ~uint64_t(0) : (uint64_t(1) << W) - 1;
    std::map<std::pair<uint32_t, int64_t>, uint32_t> id;
    auto block = [&](uint32_t leaf, int64_t lane, uint8_t chunks) {
      auto [it, fresh] =
          id.emplace(std::make_pair(leaf, lane), uint32_t(t.blocks.size()));
      if (fresh) t.blocks.push_back({leaf, lane, 0});
      t.blocks[it->second].chunk_mask |= chunks;
      return it->second;
    };
    for (Step &s : t.steps) {
      uint8_t chunks = 0;
      if (s.kind == Step::kContract) {
        const uint64_t mask = patterns_[s.pattern].mask;
        for (size_t c = 0; c < kChunks; ++c)
          if (((mask >> (W * c)) & kFull) != 0) chunks |= uint8_t(1) << c;
        if (s.to_leaf) s.blocks.push_back(block(s.b, s.lane, chunks));
        for (const auto &x : s.leaves)
          s.blocks.push_back(block(x.b, x.lane, chunks));
      } else if (s.kind == Step::kOut) {
        for (size_t c = 0; c < kChunks; ++c)
          if ((s.chunk_mask >> c) & 1)
            chunks |= uint8_t(1) << ((c + kChunks - s.shift) % kChunks);
        s.blocks.push_back(block(s.b, s.lane, chunks));
      }
    }
  }

  // T's steps run symbolically. Every var is a sum of root vars (operand
  // j's lane l weight u_j eq(lane0 + l), var j lanes + l); every product
  // of a contraction is a var times a pattern's chunk; the chunk steps only
  // route products. So each chunk of a block is a sum of terms (root var,
  // pattern, source chunk), pairs cancelling in characteristic 2. A
  // block's terms group by their root's lane l into one table per (block,
  // l), which takes u_j in once per proof: per instance, one product of
  // eq(lane0 + l) per (block, l, chunk). Tables of the same terms are one.
  // Also T's product counts per instance, the steps' and the folded
  // entries', and the tables' per proof.
  void fold_steps(Template &t) const {
    using FoldTerm = typename Template::FoldTerm;
    constexpr uint64_t kFull = W == 64 ? ~uint64_t(0) : (uint64_t(1) << W) - 1;
    const size_t nroot = K_ * t.lanes;
    auto cancel = [](auto &x) {
      std::sort(x.begin(), x.end());
      std::remove_reference_t<decltype(x)> odd;
      for (size_t a = 0; a < x.size();) {
        size_t b = a;
        while (b < x.size() && x[b] == x[a]) ++b;
        if ((b - a) % 2 == 1) odd.push_back(x[a]);
        a = b;
      }
      x = std::move(odd);
    };
    // The root vars of each var.
    std::vector<std::vector<uint32_t>> roots(t.vars);
    for (size_t v = 0; v < nroot; ++v) roots[v] = {uint32_t(v)};
    // A routed product: root var R times chunk C of pattern P.
    struct Prod {
      uint32_t r, p;
      uint8_t c;
    };
    std::vector<std::vector<Prod>> slot(t.slots * kChunks),
        blk(t.blocks.size() * kChunks);
    t.step_products = nroot;
    for (const Step &s : t.steps) {
      switch (s.kind) {
        case Step::kSum: {
          std::vector<uint32_t> x;
          for (uint32_t v : s.list)
            x.insert(x.end(), roots[v].begin(), roots[v].end());
          cancel(x);
          roots[s.a] = std::move(x);
          break;
        }
        case Step::kContract: {
          const uint64_t mask = patterns_[s.pattern].mask;
          for (size_t c = 0; c < kChunks; ++c) {
            if (((mask >> (W * c)) & kFull) == 0) continue;
            ++t.step_products;
            for (uint32_t r : roots[s.a]) {
              const Prod pr{r, s.pattern, uint8_t(c)};
              if (!s.to_leaf) slot[s.b * kChunks + c].push_back(pr);
              for (uint32_t b : s.blocks) blk[b * kChunks + c].push_back(pr);
            }
          }
          break;
        }
        case Step::kChunk:
        case Step::kOut:
          for (size_t c = 0; c < kChunks; ++c) {
            if (((s.chunk_mask >> c) & 1) == 0) continue;
            const size_t c2 = (c + kChunks - s.shift) % kChunks;
            auto &dst = s.kind == Step::kChunk
                            ? slot[s.b * kChunks + c2]
                            : blk[s.blocks[0] * kChunks + c2];
            // A copy: the target may be the source.
            const std::vector<Prod> src = slot[s.a * kChunks + c];
            dst.insert(dst.end(), src.begin(), src.end());
          }
          break;
      }
    }
    // Per (block, root lane): its terms, pairs cancelled.
    std::map<std::pair<uint32_t, int64_t>, std::vector<FoldTerm>> by;
    for (size_t b = 0; b < t.blocks.size(); ++b)
      for (size_t c = 0; c < kChunks; ++c)
        for (const Prod &pr : blk[b * kChunks + c])
          by[{uint32_t(b), int64_t(pr.r % t.lanes)}].push_back(
              {uint32_t(pr.r / t.lanes), pr.p, pr.c, uint8_t(c)});
    std::map<std::vector<FoldTerm>, uint32_t> table_of;
    t.fold.clear();
    t.fold_tables.clear();
    for (auto &[key, terms] : by) {
      cancel(terms);
      if (terms.empty()) continue;
      uint8_t chunks = 0;
      for (const FoldTerm &x : terms) chunks |= uint8_t(1) << x.c_out;
      auto [it, fresh] =
          table_of.emplace(terms, uint32_t(t.fold_tables.size()));
      if (fresh) t.fold_tables.push_back(terms);
      t.fold.push_back({key.first, it->second, key.second, chunks});
    }
    std::stable_sort(
        t.fold.begin(), t.fold.end(),
        [](const auto &x, const auto &y) { return x.src < y.src; });
    t.fold_products = 0;
    for (size_t q = 0; q < t.fold.size(); ++q) {
      if (q == 0 || t.fold[q].src != t.fold[q - 1].src) ++t.fold_products;
      t.fold_products += size_t(__builtin_popcount(t.fold[q].chunks));
    }
    t.table_products = 0;
    for (const auto &x : t.fold_tables) t.table_products += x.size();
  }
  // Whether T's instances take the folded products: when, over a proof,
  // they cost fewer products than the steps, the tables included (or as
  // a test sets, test_switches.h).
  bool folded(const Template &t) const {
    if constexpr (!kCounting) {
      if (test_switches().adjoint_path == AdjointPath::kSteps) return false;
      if (test_switches().adjoint_path == AdjointPath::kFolded) return true;
    }
    const size_t n = t.uses[0] + t.uses[1];
    const size_t shifts = size_t(t.uses[0] > 0) + size_t(t.uses[1] > 0);
    return n * t.fold_products + shifts * t.table_products <
           n * t.step_products;
  }
  // T's folded products for an instance at LANE0 into its blocks LOC
  // [blocks][chunks][NT], from its shift's tables TAB and the eq tables LO
  // and HI (eq(Frob^-k(s), l) = lo[l mod 2^H][k] hi[l >> H][k]).
  template <size_t NT>
  void run_fold(const Template &t, const std::vector<Elt> &tab, size_t lane0,
                const std::vector<Elt> &lo, const std::vector<Elt> &hi,
                size_t h, std::vector<Elt> &loc) const {
    const F &f = f_;
    using Tw = TwistOps<F, NT>;
    const size_t nlo = size_t(1) << h;
    std::array<Elt, NT> eq, prod;
    for (size_t q = 0; q < t.fold.size(); ++q) {
      const auto &x = t.fold[q];
      if (q == 0 || x.src != t.fold[q - 1].src) {
        const size_t g = lane0 + size_t(x.src);
        Tw::mul(f, eq.data(), &lo[(g & (nlo - 1)) * NT], &hi[(g >> h) * NT]);
      }
      for (size_t c = 0; c < kChunks; ++c) {
        if (((x.chunks >> c) & 1) == 0) continue;
        Tw::mul(f, prod.data(), eq.data(),
                &tab[(size_t(x.table) * kChunks + c) * NT]);
        Tw::add(f, &loc[(size_t(x.block) * kChunks + c) * NT], prod.data());
      }
    }
  }

  static constexpr int64_t kPublicWord = INT64_MIN;
  // The first output word of leaf source LS of IN, lane LANE (relative),
  // and the end of its table's words; SIZE_MAX for a public space.
  std::pair<size_t, size_t> out_words(const Instance &in, uint32_t ls,
                                      int64_t lane) const {
    const int64_t w0 = in.word0[ls];
    if (w0 == kPublicWord) return {SIZE_MAX, 0};
    check(in.base[ls] + lane >= 0, "a leaf lane before its table");
    return {size_t(w0 + lane * int64_t(kChunks)), in.word_end[ls]};
  }

  // The lanes each leaf source of T's adjoint steps write.
  static LeafLanes out_lanes(const Template &t) {
    LeafLanes out;
    out.first.assign(t.leaves.size(), INT64_MAX);
    out.last.assign(t.leaves.size(), INT64_MIN);
    auto note = [&](uint32_t b, int64_t lane) {
      out.first[b] = std::min(out.first[b], lane);
      out.last[b] = std::max(out.last[b], lane);
    };
    for (const Step &s : t.steps) {
      if (s.kind == Step::kContract) {
        if (s.to_leaf) note(s.b, s.lane);
        for (const auto &x : s.leaves) note(x.b, x.lane);
      } else if (s.kind == Step::kOut) {
        note(s.b, s.lane);
      }
    }
    return out;
  }
  // The words each leaf source of IN writes, from its template's LANES.
  static LeafWords leaf_words(const LeafLanes &lanes, const Instance &in) {
    LeafWords out;
    out.lo.assign(in.word0.size(), 0);
    out.hi.assign(in.word0.size(), 0);
    for (size_t b = 0; b < in.word0.size(); ++b) {
      if (in.word0[b] == kPublicWord || lanes.first[b] > lanes.last[b])
        continue;
      const int64_t w0 = in.word0[b] + lanes.first[b] * int64_t(kChunks);
      const int64_t w1 = in.word0[b] + (lanes.last[b] + 1) * int64_t(kChunks);
      const size_t hi =
          std::min(size_t(std::max<int64_t>(w1, 0)), in.word_end[b]);
      out.lo[b] = std::min(size_t(std::max<int64_t>(w0, 0)), hi);
      out.hi[b] = hi;
    }
    return out;
  }
  // The words a chunk of instances writes: disjoint intervals [lo, hi) in
  // increasing order, word w of one at OFF + w - lo of the chunk's forms,
  // SIZE words in all.
  struct Interval {
    size_t lo, hi, off;
  };
  struct ChunkWords {
    std::vector<Interval> iv;
    size_t size = 0;
  };
  ChunkWords chunk_words(size_t b, size_t e) const {
    std::vector<std::pair<size_t, size_t>> raw;
    for (size_t i = b; i < e; ++i) {
      const LeafWords &lw = inst_words_[i];
      for (size_t l = 0; l < lw.lo.size(); ++l)
        if (lw.lo[l] < lw.hi[l]) raw.push_back({lw.lo[l], lw.hi[l]});
    }
    std::sort(raw.begin(), raw.end());
    ChunkWords cw;
    for (const auto &[lo, hi] : raw) {
      if (!cw.iv.empty() && lo <= cw.iv.back().hi) {
        if (hi > cw.iv.back().hi) {
          cw.size += hi - cw.iv.back().hi;
          cw.iv.back().hi = hi;
        }
        continue;
      }
      cw.iv.push_back({lo, hi, cw.size});
      cw.size += hi - lo;
    }
    return cw;
  }
  // Per leaf source of instance I: word w's place in the chunk's forms is
  // w - delta (the interval holding the leaf's words).
  void deltas(size_t i, const ChunkWords &cw, std::vector<int64_t> &out) const {
    const LeafWords &lw = inst_words_[i];
    out.assign(lw.lo.size(), 0);
    for (size_t l = 0; l < out.size(); ++l) {
      if (lw.lo[l] >= lw.hi[l]) continue;
      auto it = std::upper_bound(
          cw.iv.begin(), cw.iv.end(), lw.lo[l],
          [](size_t w, const Interval &x) { return w < x.lo; });
      check(it != cw.iv.begin(), "a leaf's words outside its chunk");
      --it;
      out[l] = int64_t(it->lo) - int64_t(it->off);
    }
  }

  // The steps of T, every weight NT elements wide (one per twist k): VAR
  // [vars][NT], SLOT [slots][chunks][NT], D [patterns][chunks][NT], and LOC
  // T's blocks [blocks][chunks][NT] (flush adds them to the forms).
  template <size_t NT>
  void run_steps(const Template &t, const std::vector<Elt> &d,
                 std::vector<Elt> &var, std::vector<Elt> &slot,
                 std::vector<Elt> &loc) const {
    const F &f = f_;
    using Tw = TwistOps<F, NT>;
    constexpr uint64_t kFull = W == 64 ? ~uint64_t(0) : (uint64_t(1) << W) - 1;
    for (const Step &s : t.steps) {
      switch (s.kind) {
        case Step::kSum: {
          Elt *v = &var[size_t(s.a) * NT];
          const Elt *x0 = &var[size_t(s.list[0]) * NT];
          for (size_t k = 0; k < NT; ++k) v[k] = x0[k];
          for (size_t i = 1; i < s.list.size(); ++i)
            Tw::add(f, v, &var[size_t(s.list[i]) * NT]);
          break;
        }
        case Step::kContract: {
          const Elt *v = &var[size_t(s.a) * NT];
          const uint64_t mask = patterns_[s.pattern].mask;
          std::array<Elt, NT> prod;
          for (size_t c = 0; c < kChunks; ++c) {
            if (((mask >> (W * c)) & kFull) == 0) continue;
            Tw::mul(f, prod.data(), v,
                    &d[(size_t(s.pattern) * kChunks + c) * NT]);
            if (!s.to_leaf)
              Tw::add(f, &slot[(size_t(s.b) * kChunks + c) * NT], prod.data());
            for (uint32_t b : s.blocks)
              Tw::add(f, &loc[(size_t(b) * kChunks + c) * NT], prod.data());
          }
          break;
        }
        case Step::kChunk:
        case Step::kOut: {
          for (size_t c = 0; c < kChunks; ++c) {
            if (((s.chunk_mask >> c) & 1) == 0) continue;
            const Elt *x = &slot[(size_t(s.a) * kChunks + c) * NT];
            const size_t c2 = (c + kChunks - s.shift) % kChunks;
            Elt *o = s.kind == Step::kChunk
                         ? &slot[(size_t(s.b) * kChunks + c2) * NT]
                         : &loc[(size_t(s.blocks[0]) * kChunks + c2) * NT];
            Tw::add(f, o, x);
          }
          break;
        }
      }
    }
  }

  // The first column of each of T's blocks for instance IN in forms of
  // STRIDE columns, into FIRST (SIZE_MAX: a public space). DELTA null: word
  // w is column w (the whole forms); otherwise word w of leaf source b is
  // column w - DELTA[b] (a chunk's forms, chunk_words).
  void place(const Template &t, const Instance &in, const int64_t *delta,
             size_t stride, std::vector<size_t> &first) const {
    const size_t nb = t.blocks.size();
    first.resize(nb);
    for (size_t b = 0; b < nb; ++b) {
      const Block &bl = t.blocks[b];
      const auto ow = out_words(in, bl.leaf, bl.lane);
      first[b] = ow.first;
      if (ow.first == SIZE_MAX) continue;
      for (size_t c = 0; c < kChunks; ++c)
        if ((bl.chunk_mask >> c) & 1)
          check(ow.first + c < ow.second, "a leaf word past its table");
      if (delta == nullptr) continue;
      first[b] = size_t(int64_t(ow.first) - delta[bl.leaf]);
      for (size_t c = 0; c < kChunks; ++c)
        if ((bl.chunk_mask >> c) & 1)
          check(first[b] + c < stride, "a leaf word outside its chunk's words");
    }
  }

  // Adds T's blocks LOC to the forms A [NT][STRIDE] at FIRST (a block of a
  // public space adds nothing), and zeros LOC. Four twists at a time: the
  // blocks of a leaf are consecutive lanes, so each pass writes four forms
  // in runs of consecutive words. One weight (NT = 1): word by word.
  template <size_t NT>
  void flush(const Template &t, std::vector<Elt> &loc,
             const std::vector<size_t> &first, Elt *a, size_t stride) const {
    const F &f = f_;
    const size_t nb = t.blocks.size();
    if constexpr (NT == 1) {
      for (size_t b = 0; b < nb; ++b) {
        if (first[b] == SIZE_MAX) continue;
        const uint8_t cm = t.blocks[b].chunk_mask;
        const Elt *x = &loc[b * kChunks];
        for (size_t c = 0; c < kChunks; ++c)
          if ((cm >> c) & 1) f.add(a[first[b] + c], x[c]);
      }
    } else {
      for (size_t k0 = 0; k0 < NT; k0 += 4) {
        for (size_t b = 0; b < nb; ++b) {
          if (first[b] == SIZE_MAX) continue;
          const uint8_t cm = t.blocks[b].chunk_mask;
          const Elt *x = &loc[b * kChunks * NT];
          if (kChunks == 4 && cm == 0xF) {
            Twists<F, NT>::add_words4(f, a + first[b], stride, x, k0);
            continue;
          }
          for (size_t k = k0; k < k0 + 4; ++k)
            for (size_t c = 0; c < kChunks; ++c)
              if ((cm >> c) & 1)
                f.add(a[k * stride + first[b] + c], x[c * NT + k]);
        }
      }
    }
    std::fill(loc.begin(), loc.begin() + nb * kChunks * NT, f.zero());
  }

  // The lanes of every IR node of IN, the operands' first: [K][lanes].
  // LEAVES false: the leaves of tables read as zero (the constant parts);
  // TABLES null with LEAVES false. PUBLICS null: publics zero.
  std::vector<uint64_t> forward(
      const Instance &in, const std::vector<std::vector<uint64_t>> *tables,
      const std::vector<std::vector<uint64_t>> *publics, bool leaves) const {
    const Template &t = tmpls_[in.tmpl];
    // Every IR node's lanes in one buffer; with LEAVES false, a node that
    // reads no public value or constant stays zero.
    std::vector<uint64_t> v(t.ir_lanes, 0);
    const auto &kl = in.konst;
    auto lane_of = [](const std::vector<uint64_t> &x, int64_t l) {
      return l >= 0 && size_t(l) < x.size() ? x[size_t(l)] : uint64_t(0);
    };
    for (size_t q = 0; q < t.ir.size(); ++q) {
      const IrNode &x = t.ir[q];
      if (!leaves && !x.konst_dep) continue;
      for (size_t l = 0; l < x.lanes; ++l) {
        uint64_t r = 0;
        for (uint32_t i = x.start[l]; i < x.start[l + 1]; ++i) {
          const LaneTerm &term = t.terms[i];
          uint64_t s = 0;
          switch (term.kind) {
            case kNode: {
              const IrNode &y = t.ir[term.src];
              if (term.lane >= 0 && size_t(term.lane) < y.lanes)
                s = v[y.off + size_t(term.lane)];
              break;
            }
            case kLeaf: {
              const uint32_t sp = in.space[term.src];
              const int64_t abs = in.base[term.src] + term.lane;
              if (spaces_[sp].kind == BatchSpace::kPublic) {
                if (publics != nullptr) s = lane_of((*publics)[sp], abs);
              } else if (leaves) {
                s = lane_of((*tables)[sp], abs);
              }
              break;
            }
            case kConst:
              s = lane_of(kl[term.src], term.lane);
              break;
            case kOne:
              s = ~uint64_t(0);
              break;
          }
          r ^= rotl64(s, term.rot) & term.mask;
        }
        v[x.off + l] = r;
      }
    }
    std::vector<uint64_t> out(K_ * t.lanes);
    for (unsigned j = 0; j < K_; ++j)
      for (size_t l = 0; l < t.lanes; ++l)
        out[j * t.lanes + l] = v[t.ir[t.roots[j]].off + l];
    return out;
  }

  template <class, size_t>
  friend class BitViewMap;
  const F &f_;
  std::string name_;
  unsigned K_;
  std::vector<BatchSpace> spaces_;
  std::vector<size_t> space_word0_;
  size_t words_ = 0;
  std::vector<Elt> dual_;
  std::vector<Template> tmpls_;
  // Per template and per instance: the lanes and the words their adjoint
  // steps write (the adjoint's chunks).
  std::vector<LeafLanes> tmpl_lanes_;
  std::vector<LeafWords> inst_words_;
  std::map<std::vector<uint8_t>, uint32_t> tmpl_of_;
  std::vector<Instance> insts_;
  size_t lanes_ = 0;
  // Whether the last lane holds one instance of at most 32 coordinates in
  // its lower half, so the next such instance may take the upper half.
  bool half_open_ = false;
  // Per shift (0, 32): the patterns its instances' templates read.
  std::vector<bool> pattern_used_[2];
  std::vector<LanePattern> patterns_;
  std::map<LanePattern, uint32_t> pattern_of_;
  // The bit phase's references (prepare_bit_phase), shared by the copies.
  mutable std::shared_ptr<const PhaseRefs> phase_;
};

// ------------------------------------------------------- FieldViewMap --

// The field-element operand map of a batch: operand j of instance t is
// constant_{j,t} + sum over its terms k W_space[pos], the views composed at
// compile time. Tables are cells (their coordinates); publics enter the
// constants when the parties prove and verify.
template <class F>
class FieldViewMap {
 public:
  using Elt = typename F::Elt;
  struct Term {
    uint32_t space;
    uint32_t coeff;  // into coeffs
    size_t pos;
  };

  FieldViewMap(const F &f, std::string name, unsigned k,
               std::vector<BatchSpace> spaces)
      : f_(f), name_(std::move(name)), K_(k) {
    for (const auto &s : spaces) add_space(s);
    start_.assign(K_, {0});
    terms_.resize(K_);
    konst_.resize(K_);
  }

  // O over the field F of the same elements (CountingField<G> over G, for
  // op_counts.h): the same terms, constants and coefficients.
  template <class G>
  FieldViewMap(const F &f, const FieldViewMap<G> &o)
      : f_(f), name_(o.name_), K_(o.K_), spaces_(o.spaces_),
        space_word0_(o.space_word0_), words_(o.words_),
        instances_(o.instances_), start_(o.start_), konst_(o.konst_),
        coeffs_(o.coeffs_), names_(o.names_), reads_public_(o.reads_public_) {
    terms_.resize(o.terms_.size());
    for (size_t j = 0; j < o.terms_.size(); ++j)
      for (const auto &t : o.terms_[j])
        terms_[j].push_back({t.space, t.coeff, t.pos});
  }

  // Appends space S (a predicate added later may read it); the earlier
  // spaces' words keep their places.
  void add_space(const BatchSpace &s) {
    space_word0_.push_back(words_);
    if (s.kind == BatchSpace::kTable) words_ += s.size;
    spaces_.push_back(s);
  }

  // Adds predicate NAME with operands DAG.
  void add(const ViewDag<F> &dag, std::string name) {
    using D = ViewDag<F>;
    check(dag.roots.size() == K_, "field view map: operands");
    const size_t n = dag.nodes[dag.roots[0]].n;
    // Coordinate I of node V times K: its terms and constant.
    std::vector<std::pair<std::pair<uint32_t, size_t>, Elt>> terms;
    Elt c;
    std::function<void(uint32_t, size_t, const Elt &)> exp =
        [&](uint32_t v, size_t i, const Elt &k) {
          if (k == f_.zero()) return;
          const auto &x = dag.nodes[v];
          switch (x.op) {
            case D::kLeaf: {
              const SourceRef &r = x.refs[i];
              if (r.space != SourceRef::kZero)
                terms.push_back({{r.space, r.pos}, k});
              return;
            }
            case D::kConst:
              f_.add(c, f_.mulf(k, (*x.values)[i]));
              return;
            case D::kAdd:
              exp(x.kids[0], i, k);
              exp(x.kids[1], i, k);
              return;
            case D::kScale:
              exp(x.kids[0], i, f_.mulf(k, x.k));
              return;
            case D::kGather: {
              size_t j = x.idx[i];
              for (uint32_t kid : x.kids) {
                if (j < dag.nodes[kid].n) {
                  exp(kid, j, k);
                  return;
                }
                j -= dag.nodes[kid].n;
              }
              check(false, "a gather's index");
              return;
            }
            case D::kBroadcast:
              exp(x.kids[0], 0, k);
              return;
            case D::kSum: {
              const size_t m = dag.nodes[x.kids[0]].n;
              const size_t w = x.w == 0 ? m : x.w;
              for (size_t j = 0; j < w; ++j)
                exp(x.kids[0], (x.w == 0 ? 0 : i * w) + j, k);
              return;
            }
            case D::kMask:
              exp(x.kids[0], i, f_.mulf(k, (*x.values)[i]));
              return;
            case D::kNot:
              f_.add(c, k);
              exp(x.kids[0], i, f_.negf(k));
              return;
          }
        };
    for (unsigned j = 0; j < K_; ++j)
      for (size_t i = 0; i < n; ++i) {
        terms.clear();
        c = f_.zero();
        exp(dag.roots[j], i, f_.one());
        std::sort(terms.begin(), terms.end(),
                  [](const auto &a, const auto &b) { return a.first < b.first; });
        for (size_t a = 0; a < terms.size();) {
          Elt k = f_.zero();
          size_t b = a;
          for (; b < terms.size() && terms[b].first == terms[a].first; ++b)
            f_.add(k, terms[b].second);
          if (k != f_.zero())
            terms_[j].push_back({terms[a].first.first, coeff_id(k),
                                 terms[a].first.second});
          if (spaces_[terms[a].first.first].kind == BatchSpace::kPublic)
            reads_public_ = true;
          a = b;
        }
        start_[j].push_back(terms_[j].size());
        konst_[j].push_back(c);
      }
    instances_ += n;
    names_.push_back(std::move(name));
  }

  std::string name() const { return name_; }
  unsigned operands() const { return K_; }
  size_t instances() const { return instances_; }
  size_t words() const { return words_; }
  size_t predicates() const { return names_.size(); }
  const std::vector<BatchSpace> &spaces() const { return spaces_; }
  std::vector<uint8_t> params() const {
    std::vector<uint8_t> out;
    put_u64(out, K_);
    put_u64(out, spaces_.size());
    for (const auto &s : spaces_) {
      put_u64(out, s.kind);
      put_u64(out, s.node);
      put_u64(out, s.size);
    }
    put_u64(out, instances_);
    for (unsigned j = 0; j < K_; ++j) {
      for (size_t x : start_[j]) put_u64(out, x);
      for (const auto &c : konst_[j]) put_elt(out, c);
    }
    for (const auto &tj : terms_)
      for (const auto &t : tj) {
        put_u64(out, t.space);
        put_u64(out, t.pos);
        put_elt(out, coeffs_[t.coeff]);
      }
    return out;
  }

  // The operands of every instance, [t][j], from the tables' words (in
  // space order, tables only) and the public values (by space).
  std::vector<std::vector<Elt>> apply(
      const std::vector<Elt> &words,
      const std::vector<const std::vector<Elt> *> &publics) const {
    std::vector<std::vector<Elt>> out(instances_, std::vector<Elt>(K_));
    for (unsigned j = 0; j < K_; ++j)
      for (size_t t = 0; t < instances_; ++t) {
        Elt v = konst_[j][t];
        for (size_t q = start_[j][t]; q < start_[j][t + 1]; ++q) {
          const Term &x = terms_[j][q];
          f_.add(v, f_.mulf(coeffs_[x.coeff], value(x, words, publics)));
        }
        out[t][j] = v;
      }
    return out;
  }
  // sum_t weight_t sum_j u_j L_j(t) = constant + sum_c a_c W_c.
  void adjoint(const std::vector<Elt> &weight, const std::vector<Elt> &u,
               const std::vector<const std::vector<Elt> *> &publics,
               std::vector<Elt> &a, Elt &constant) const {
    a.assign(words_, f_.zero());
    constant = f_.zero();
    for (unsigned j = 0; j < K_; ++j)
      for (size_t t = 0; t < instances_; ++t) {
        const Elt w = f_.mulf(weight[t], u[j]);
        f_.add(constant, f_.mulf(w, konst_[j][t]));
        for (size_t q = start_[j][t]; q < start_[j][t + 1]; ++q) {
          const Term &x = terms_[j][q];
          const Elt c = f_.mulf(w, coeffs_[x.coeff]);
          if (spaces_[x.space].kind == BatchSpace::kPublic) {
            f_.add(constant, f_.mulf(c, (*publics.at(x.space))[x.pos]));
          } else {
            f_.add(a[space_word0_[x.space] + x.pos], c);
          }
        }
      }
  }

 private:
  Elt value(const Term &x, const std::vector<Elt> &words,
            const std::vector<const std::vector<Elt> *> &publics) const {
    if (spaces_[x.space].kind == BatchSpace::kPublic)
      return (*publics.at(x.space))[x.pos];
    return words[space_word0_[x.space] + x.pos];
  }
  uint32_t coeff_id(const Elt &k) {
    for (size_t i = 0; i < coeffs_.size(); ++i)
      if (coeffs_[i] == k) return uint32_t(i);
    coeffs_.push_back(k);
    return uint32_t(coeffs_.size() - 1);
  }
  void put_elt(std::vector<uint8_t> &out, const Elt &x) const {
    uint8_t b[F::kBytes];
    f_.to_bytes_field(b, x);
    out.insert(out.end(), b, b + F::kBytes);
  }

  template <class>
  friend class FieldViewMap;
  const F &f_;
  std::string name_;
  unsigned K_;
  std::vector<BatchSpace> spaces_;
  std::vector<size_t> space_word0_;
  size_t words_ = 0, instances_ = 0;
  std::vector<std::vector<size_t>> start_;
  std::vector<std::vector<Elt>> konst_;
  std::vector<std::vector<Term>> terms_;  // per operand
  std::vector<Elt> coeffs_;
  std::vector<std::string> names_;
  bool reads_public_ = false;
};

}  // namespace proofs::gordiehowe::compiler

#endif  // PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_COMPILER_VIEW_MAP_H_
