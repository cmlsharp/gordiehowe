// Copyright 2026 Chad Sharp and Paul Grubbs
// SPDX-License-Identifier: Apache-2.0

// GordieHowe: a domain's proof over its packing tree (tree.h, stage.h).
//
// The commitment is the root's region; every other node's region is packed
// into its parent's. Claims are linear rows over the logical coordinates L:
//
//   L = [root own: full inputs, GKR pads, squaring-chain masks
//        | prefix: subfield masks (S0 coordinates)
//        | each non-root node's region: its children's words, its own
//          values]
//
// A bit node's region is the packed bit run of the circuit inputs; its
// groups are words of its parent's region, or (bit views) the parent's own
// values they alias. A bit view of a word higher on the path (composed) is
// decoded stage by stage: its groups alias uncommitted coordinates of the
// word in the regions between, and the top level's alias the word
// (TreeLayout::View, ComposedBits). A word claim in Frobenius form whose
// degree exceeds the stage it reaches (a bit batch's on GF(2^32) words over
// a GF(2^16) bit stage) leaves each measurement row a smaller such claim,
// which the stage above opens (TreeRows::Formed): every claim joins one
// measurement per edge.
//
// The protocol, after the batched relations: GKR (zk_common.h's layer rows,
// then the input row, whose packed bits are an eq-structured part); then
// each non-root node from the deepest up runs its stage on the rows that
// touch its region (one row as it is, several combined by fresh challenges),
// revealing [parent : node] masked measurements (ring switching, stage.h);
// then the root combines every row with fresh challenges and runs each root
// child's stage (zk_extension_packed.h's ExtensionForms), and Ligero opens
// the measurement rows and the combined row. A root without children hands
// the rows to Ligero directly. A squaring-chain-masks stage's masks and squaring chains
// are root own cells, at the root as below it; a subfield-masks stage's
// masks are prefix cells.
//
// A domain without GKR (TreePlan::gkr false, a circuit without layers)
// skips GKR and its input row: its rows are the domain's own, and the
// stages, the root and Ligero run on them alone.
//
// For the trees bits < GF(2^16) < K and S0 < K the
// layout, masks, transcript and rows are ZkProver's, so the proofs are its
// proofs.
//
// Test-only ablation (DomainProfile::unpacked_s0): a root child of degree
// S0 may instead be flat, Longfellow's layout. Its coordinates are
// committed one per cell in the subfield rows after the prefix masks, it
// runs no stage and has no masks, and the root's combined row reads its
// coordinates directly. Its membership in S0 is the prefix test's
// (packing.h), whose rows then hold these cells too.

#ifndef PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_COMPILER_TREE_ZK_H_
#define PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_COMPILER_TREE_ZK_H_

#include <algorithm>
#include <cstddef>
#include <cstdint>
#include <deque>
#include <functional>
#include <map>
#include <memory>
#include <optional>
#include <string>
#include <utility>
#include <vector>

#include "arrays/dense.h"
#include "arrays/eqs.h"
#include "gordiehowe/compiler/bit_phase.h"
#include "gordiehowe/compiler/bit_planes.h"
#include "gordiehowe/compiler/prover_scratch.h"
#include "gordiehowe/compiler/stage.h"
#include "gordiehowe/compiler/test_switches.h"
#include "gordiehowe/subfield.h"
#include "gordiehowe/compiler/tree.h"
#include "ligero/ligero_param.h"
#include "ligero/ligero_prover.h"
#include "ligero/ligero_verifier.h"
#include "random/random.h"
#include "random/transcript.h"
#include "sumcheck/circuit.h"
#include "sumcheck/prover_layers.h"
#include "sumcheck/transcript_sumcheck.h"
#include "util/panic.h"
#include "util/parallel.h"
#include "util/prover_profile.h"
#include "zk/zk_common.h"
#include "zk/zk_proof.h"

namespace proofs::gordiehowe::compiler {

// The phase-timer key of a packing sub-phase (util/prover_profile.h):
// "bin.<name>" in characteristic 2, "odd.<name>" otherwise.
#define GH_TREE_KEY(F, name) ((F::kCharacteristicTwo) ? "bin." name : "odd." name)

// Test seams of a domain's row reductions (prover and verifier alike),
// which a test sets through CompiledDomainBase::tree_test_hooks.
// ZERO_INPUTS, when set, lists circuit inputs whose coefficient in the GKR
// input row is zero (a valid row when their values are zero); STAGE_DRAWS,
// when set, receives each stage's number of weights.
struct TreeTestHooks {
  const std::vector<size_t> *zero_inputs = nullptr;
  std::vector<size_t> *stage_draws = nullptr;
};

// The rows a domain adds after GKR (affine rows and batch rows), over L.
template <class F>
struct ExtraRows {
  using Elt = typename F::Elt;
  size_t n = 0;
  std::vector<LigeroLinearConstraint<F>> a;  // sparse terms, rows 0..n-1
  std::vector<Elt> b;                        // right-hand sides
  // coeff[l] += sum_r weights[r] row_r[l], the dense part of the rows.
  std::function<void(Elt *coeff, const Elt *weights)> accumulate;
  // Per row, the tree nodes (bit i: node i) the row reads.
  std::vector<uint64_t> nodes;
  // Rows whose part on the bit node is a claim on the bits of words at
  // WORD_AT (L positions in the bit node's parent region): sum_k
  // Frob^k(<a_k, words>), a_k FORMS's form k (a bit batch's terminal claim),
  // or with the bit phase the claim PRODUCT in product form, a_k[q] = D_k
  // Frob^-k(alpha_q) (bit_phase.h), FORMS then null.
  struct Claim {
    size_t row;
    std::shared_ptr<const BitForms<F>> forms;
    std::vector<size_t> word_at;
    std::shared_ptr<const ProductClaim<F>> product = nullptr;
  };
  std::vector<Claim> claims;
};

// Where a domain's circuit inputs lie in the tree.
struct TreeInputs {
  std::vector<int> node_of_input;  // per input; -1 public; the bit node for
                                   // the packed run
  size_t run_begin = 0, run_end = 0;  // the packed bit run
  // (first input of a run group, the input it aliases).
  std::vector<std::pair<size_t, size_t>> aliases;
  // Composed bit views: DEGREE run inputs from FIRST (whole groups) are the
  // canonical bits of the GF(2^DEGREE) word at input TARGET, whose node
  // lies above the bit node's parent (ComposedBits).
  struct Composed {
    size_t first, target, degree;
  };
  std::vector<Composed> composed;
};

template <class F>
class TreeLayout {
 public:
  using Elt = typename F::Elt;
  static constexpr size_t kNone = ~size_t(0);
  struct Region {
    size_t off = 0, n = 0;           // L range
    size_t groups = 0;               // words of [parent : node] coordinates
    std::vector<size_t> group_at;    // L position (non-root parent), or
                                     // committed index (root parent)
    std::vector<bool> alias;         // per group
    size_t words = 0;                // groups that are words (not aliases)
  };
  const PackingTree *tree = nullptr;
  // The row reductions' test seams.
  mutable TreeTestHooks test_hooks;
  std::vector<PackingStage<F>> stages;  // per node (index 0 unused)
  std::vector<Region> region;           // per node (index 0: root own)
  std::vector<size_t> input_L;          // circuit input -> L
  size_t L = 0;
  size_t own = 0;                       // root own size
  size_t pad_L = 0;                     // GKR pads
  std::vector<size_t> mask_L;           // per node: first mask (L)
  size_t prefix_L = 0, prefix = 0, prefix_padded = 0;
  size_t words_at = 0;                  // committed index of the first word
  std::vector<size_t> word_at;          // per root child: first word
  // Test-only ablation (DomainProfile::unpacked_s0): a root child of
  // degree S0 whose coordinates are committed one per subfield cell, after
  // the prefix masks and in the same subfield rows, in place of its words
  // of [K : S0] coordinates; it runs no stage and has no masks. FLAT_AT is
  // its first committed index.
  std::vector<bool> flat;               // per node
  std::vector<size_t> flat_at;          // per node
  size_t nflat = 0;                     // flat coordinates
  size_t nw = 0;                        // committed size
  int bits = -1;                        // the bit node, if any
  size_t nquad = 0;                     // chain-stage quadratic constraints
  // A composed bit view of one word: its first bit group, and its virtual
  // coordinates. PATH holds the nodes from the bit node's parent up to
  // below the word's node; AT[m] is the L position of the word's first
  // virtual coordinate in PATH[m]'s region: D / deg(PATH[m]) of them, the
  // word's coordinates over PATH[m] in the tower basis (ComposedBits),
  // never committed. PATH[m]'s groups of them alias the next level's
  // coordinates, the top level's the word itself.
  struct View {
    size_t group = 0, degree = 0, target = 0;
    std::vector<int> path;
    std::vector<size_t> at;
  };
  std::vector<View> views;
  std::map<size_t, ComposedBits<F>> bases;  // per composed word degree

  TreeLayout(const F &f, const PackingTree &t, const TreeInputs &in,
             size_t ninputs, size_t npub, size_t gkr_pads, size_t w,
             bool unpacked_s0 = false)
      : tree(&t) {
    const size_t N = t.nodes.size();
    flat.assign(N, false);
    flat_at.assign(N, kNone);
    if (unpacked_s0)
      for (int c : t.nodes[0].children)
        if (t.nodes[size_t(c)].degree == t.s0) flat[size_t(c)] = true;
    stages.resize(N);
    for (size_t i = 1; i < N; ++i)
      stages[i] = PackingStage<F>(
          f, t.nodes[i].degree, t.nodes[size_t(t.nodes[i].parent)].degree);
    for (size_t i = 1; i < N; ++i)
      if (t.nodes[i].degree == 1 && t.squaring_chain(int(i)) &&
          in.run_end > in.run_begin)
        bits = int(i);
    // Composed views: the path from the bit node up to the word's node, and
    // the virtual coordinates each path node holds.
    std::vector<size_t> nvirt(N, 0);
    for (const auto &cv : in.composed) {
      check(bits >= 0, "a composed bit view without a bit node");
      const size_t d = stages[size_t(bits)].d;
      check(cv.first >= in.run_begin && cv.first + cv.degree <= in.run_end &&
                (cv.first - in.run_begin) % d == 0,
            "a composed bit view lies in whole groups of the run");
      View v;
      v.group = (cv.first - in.run_begin) / d;
      v.degree = cv.degree;
      v.target = cv.target;
      for (int u = t.nodes[size_t(bits)].parent;;
           u = t.nodes[size_t(u)].parent) {
        check(u > 0, "a composed bit view's word lies above the bit node, "
                     "below K");
        if (t.nodes[size_t(u)].degree == cv.degree) break;
        v.path.push_back(u);
      }
      check(!v.path.empty(), "a composed bit view passes an intermediate");
      if (!bases.count(cv.degree)) {
        std::vector<const PackingStage<F> *> lin;
        for (int u : v.path) lin.push_back(&stages[size_t(u)]);
        bases.emplace(cv.degree,
                      ComposedBits<F>(f, stages[size_t(bits)], lin));
      }
      for (int u : v.path) nvirt[size_t(u)] += cv.degree / t.nodes[size_t(u)].degree;
      views.push_back(std::move(v));
    }
    std::vector<size_t> vfirst(N, 0);  // region index of the first virtual
    region.resize(N);
    mask_L.assign(N, kNone);
    input_L.assign(ninputs, kNone);
    // Own inputs per node, in input order.
    std::vector<std::vector<size_t>> owns(N);
    for (size_t i = npub; i < ninputs; ++i) {
      if (i >= in.run_begin && i < in.run_end) continue;
      const int nd = in.node_of_input.at(i);
      check(nd >= 0 && size_t(nd) < N, "tree input node");
      owns[size_t(nd)].push_back(i);
    }
    // Root own: inputs, GKR pads, squaring-chain masks.
    size_t at = 0;
    for (size_t i : owns[0]) input_L[i] = at++;
    pad_L = at;
    at += gkr_pads;
    const auto order = t.bottom_up();
    for (int x : order)
      if (stages[size_t(x)].squaring_chain()) {
        mask_L[size_t(x)] = at;
        at += stages[size_t(x)].mask_cells();
        nquad += stages[size_t(x)].chain_cells();
      }
    own = at;
    // Prefix: the root children's subfield masks first, then the others.
    prefix_L = at;
    for (int c : t.nodes[0].children)
      if (!stages[size_t(c)].squaring_chain() && !flat[size_t(c)]) {
        mask_L[size_t(c)] = at;
        at += stages[size_t(c)].mask_cells();
      }
    for (int x : order)
      if (!stages[size_t(x)].squaring_chain() && !flat[size_t(x)] &&
          mask_L[size_t(x)] == kNone) {
        mask_L[size_t(x)] = at;
        at += stages[size_t(x)].mask_cells();
      }
    prefix = at - prefix_L;
    // Region sizes, bottom-up: words of the children, compatibility zeros,
    // own values.
    std::vector<size_t> nzero(N, 0);
    for (int x : order) {
      Region &r = region[size_t(x)];
      const size_t d = stages[size_t(x)].d;
      if (x == bits) {
        check(in.run_begin % d == 0 && in.run_end % d == 0,
              "packed bit run is not aligned to its words");
        r.n = in.run_end - in.run_begin;
        r.groups = r.n / d;
        r.alias.assign(r.groups, false);
        for (const auto &a : in.aliases) {
          check(a.first >= in.run_begin && a.first < in.run_end &&
                    (a.first - in.run_begin) % d == 0,
                "alias of a run group");
          r.alias.at((a.first - in.run_begin) / d) = true;
        }
        for (const auto &v : views)
          for (size_t i = 0; i < v.degree / d; ++i) r.alias.at(v.group + i) = true;
      } else {
        size_t n = 0;
        for (int c : t.nodes[size_t(x)].children) n += region[size_t(c)].words;
        // ZkProver's PackedLayout zeros: the bit words and the unpacked
        // subfield inputs fill whole rows of a root child.
        if (bits >= 0 && t.nodes[size_t(bits)].parent == x &&
            t.nodes[size_t(x)].parent == 0 && w > 0) {
          const size_t npacked = region[size_t(bits)].words;
          const size_t nsub = owns[size_t(x)].size();
          size_t need = ceildiv(npacked, w) * w;
          if (!in.aliases.empty()) need = ceildiv(npacked + nsub, w) * w;
          if (npacked + nsub < need) nzero[size_t(x)] = need - (npacked + nsub);
        }
        n += nzero[size_t(x)] + owns[size_t(x)].size();
        // Composed views' virtual coordinates, in whole groups after the
        // rest.
        if (nvirt[size_t(x)] > 0) {
          vfirst[size_t(x)] = ceildiv(n, d) * d;
          n = vfirst[size_t(x)] + nvirt[size_t(x)];
        }
        r.n = n;
        r.groups = ceildiv(n, d);
        r.alias.assign(r.groups, false);
        if (nvirt[size_t(x)] > 0)
          for (size_t g = vfirst[size_t(x)] / d; g < r.groups; ++g)
            r.alias[g] = true;
      }
      r.words = 0;
      for (bool a : r.alias) r.words += a ? 0 : 1;
    }
    // The subfield rows: the prefix masks, then the flat coordinates.
    for (int c : t.nodes[0].children)
      if (flat[size_t(c)]) {
        flat_at[size_t(c)] = prefix + nflat;
        nflat += region[size_t(c)].n;
      }
    prefix_padded = w ? ceildiv(prefix + nflat, w) * w : prefix + nflat;
    // L offsets of the regions, in bottom-up order after the prefix.
    for (int x : order) {
      region[size_t(x)].off = at;
      at += region[size_t(x)].n;
    }
    L = at;
    // Entries: the children's words, zeros, own values; group positions.
    for (int x : order) {
      Region &r = region[size_t(x)];
      if (x == bits) {
        for (size_t i = in.run_begin; i < in.run_end; ++i)
          input_L[i] = r.off + (i - in.run_begin);
        continue;
      }
      size_t e = r.off;
      for (int c : t.nodes[size_t(x)].children) {
        Region &rc = region[size_t(c)];
        rc.group_at.assign(rc.groups, kNone);
        for (size_t g = 0; g < rc.groups; ++g)
          if (!rc.alias[g]) rc.group_at[g] = e++;
      }
      e += nzero[size_t(x)];
      for (size_t i : owns[size_t(x)]) input_L[i] = e++;
    }
    // Alias groups read their parent's own values.
    if (bits >= 0) {
      Region &rb = region[size_t(bits)];
      const size_t d = stages[size_t(bits)].d;
      for (const auto &a : in.aliases) {
        check(input_L.at(a.second) != kNone, "alias target");
        rb.group_at.at((a.first - in.run_begin) / d) = input_L[a.second];
      }
    }
    // Committed: [prefix | root children's words | root own].
    words_at = prefix_padded;
    size_t cw = words_at;
    word_at.assign(N, kNone);
    for (int c : t.nodes[0].children) {
      if (flat[size_t(c)]) continue;
      Region &rc = region[size_t(c)];
      word_at[size_t(c)] = cw;
      rc.group_at.assign(rc.groups, kNone);
      for (size_t g = 0; g < rc.groups; ++g) rc.group_at[g] = cw++;
    }
    // Composed views: the bit groups read the first level's virtual
    // coordinates, each level's groups the next level's, the top level's
    // the word.
    {
      std::vector<size_t> next(N, 0);
      for (auto &v : views) {
        for (int u : v.path) {
          v.at.push_back(region[size_t(u)].off + vfirst[size_t(u)] +
                         next[size_t(u)]);
          next[size_t(u)] += v.degree / t.nodes[size_t(u)].degree;
        }
        Region &rb = region[size_t(bits)];
        for (size_t i = 0; i < v.degree / stages[size_t(bits)].d; ++i)
          rb.group_at.at(v.group + i) = v.at[0] + i;
        for (size_t m = 0; m < v.path.size(); ++m) {
          const int u = v.path[m];
          Region &ru = region[size_t(u)];
          const size_t du = stages[size_t(u)].d;
          const size_t ngroups = v.degree / t.nodes[size_t(u)].degree / du;
          for (size_t q = 0; q < ngroups; ++q)
            ru.group_at.at((v.at[m] - ru.off) / du + q) =
                m + 1 < v.path.size() ? v.at[m + 1] + q
                                      : input_L.at(v.target);
        }
      }
    }
    nw = cw + own;
    region[0].off = 0;
    region[0].n = own;
  }

  // The tree node an L position lies in (0: root own or prefix).
  int node_of(size_t l) const {
    if (l < prefix_L + prefix) return 0;
    for (size_t x = 1; x < region.size(); ++x)
      if (l >= region[x].off && l < region[x].off + region[x].n) return int(x);
    check(false, "L position");
    return 0;
  }
  // The committed index of an L position of the root (own or prefix).
  size_t committed(size_t l) const {
    if (l < own) return nw - own + l;
    for (size_t x = 1; nflat > 0 && x < region.size(); ++x)
      if (flat[x] && l >= region[x].off && l < region[x].off + region[x].n)
        return flat_at[x] + (l - region[x].off);
    check(l < prefix_L + prefix, "committed position of a packed value");
    return l - prefix_L;
  }
  // The coordinate of L position L in ZkProver's committed order before
  // relative packing ([the root child's region | root own]), for the system
  // description of the trees bits < GF(2^16) < K and S0 < K; L itself
  // otherwise.
  size_t legacy_coord(size_t l) const {
    const auto &ch = tree->nodes[0].children;
    if (ch.size() != 1) return l;
    const Region &r = region[size_t(ch[0])];
    if (l >= r.off && l < r.off + r.n) return l - r.off;
    if (l < own) return r.n + l;
    return l;
  }
  bool legacy_root() const {
    const auto &ch = tree->nodes[0].children;
    return ch.size() == 1 && stages[size_t(ch[0])].legacy_root && nflat == 0;
  }
  // The root children that run the root's stage (all but the flat ones).
  std::vector<int> packed_children() const {
    std::vector<int> v;
    for (int c : tree->nodes[0].children)
      if (!flat[size_t(c)]) v.push_back(c);
    return v;
  }
  // The commitment's binding: zk_extension_packed.h's for a root with one
  // child, the designated subfield; the tree otherwise.
  template <class Hash>
  void bind(BasicTranscript<Hash> &ts) const {
    const auto &ch = tree->nodes[0].children;
    if (ch.empty()) return;
    if (legacy_root()) {
      static const char tag[] = "experimental/relative-input-packing/v1";
      ts.write(reinterpret_cast<const uint8_t *>(tag), sizeof(tag));
      uint8_t dims[32];
      const size_t sub = region[size_t(ch[0])].n;
      u64_to_le(dims, stages[size_t(ch[0])].d);
      u64_to_le(dims + 8, sub + own);
      u64_to_le(dims + 16, sub);
      u64_to_le(dims + 24, prefix_padded);
      ts.write(dims, sizeof(dims));
      return;
    }
    static const char tag[] = "gordiehowe/packing-tree/v1";
    static const char tag_flat[] = "gordiehowe/packing-tree-unpacked-s0/v1";
    if (nflat > 0)
      ts.write(reinterpret_cast<const uint8_t *>(tag_flat), sizeof(tag_flat));
    else
      ts.write(reinterpret_cast<const uint8_t *>(tag), sizeof(tag));
    std::vector<uint8_t> b(8 * (3 + (nflat > 0 ? 1 : 0) + 3 * tree->nodes.size()));
    size_t o = 0;
    auto put = [&](size_t v) {
      u64_to_le(&b[o], v);
      o += 8;
    };
    put(tree->nodes.size());
    put(own);
    put(prefix_padded);
    if (nflat > 0) put(nflat);
    for (size_t i = 0; i < tree->nodes.size(); ++i) {
      put(tree->nodes[i].degree);
      put(size_t(tree->nodes[i].parent + 1));
      put(region[i].n);
    }
    ts.write(b.data(), b.size());
  }

  static size_t ceildiv(size_t a, size_t b) { return (a + b - 1) / b; }
};

// The rows of one domain's proof, in Ligero order, and the stage
// reductions over them. Shared by prover and verifier: the prover passes
// its L values (VALS) and receives the measurements, the verifier passes
// the measurements from the proof.
template <class F>
class TreeRows {
 public:
  using Elt = typename F::Elt;
  using Llc = LigeroLinearConstraint<F>;
  // SCALE * a[y] at positions AT[y]: a word claim's form in a measurement
  // row, kept structured (it has as many terms as the batch has words). A
  // product part (ALPHA set, A null) is the form of a claim in product
  // form (bit_phase.h): SCALE * Frob^-TWIST(alpha[y]), SCALE holding D_k.
  struct Part {
    const std::vector<size_t> *at;
    const Elt *a;
    Elt scale;
    const Elt *alpha = nullptr;
    size_t twist = 0;
  };
  // A claim on words W at AT in Frobenius form, sum_{k<e} phi^k(c_k <a_k,
  // W>) with phi = x^(p^BASE), from a word claim whose degree exceeds the
  // stages below it: the stage of the node of degree BASE opens it.
  struct Formed {
    const std::vector<size_t> *at;
    std::vector<const Elt *> a;
    std::vector<Elt> c;
    size_t base;
  };
  struct Row {
    std::vector<std::pair<size_t, Elt>> terms;
    Elt rhs;
    bool eq = false;  // the GKR input row's packed bits
    std::vector<Part> parts;
    std::vector<Formed> formed;
    // Nodes the row reads beyond its terms (bit i: node i): a remainder's,
    // the nodes the rows it combines read.
    uint64_t nodes = 0;
  };
  struct Item {
    bool extra;
    size_t idx;
    bool disabled = false;
  };
  struct Eq {
    size_t logv = 0;
    const Elt *g0 = nullptr, *g1 = nullptr;
    Elt alpha;
  };

  // The rows' term lists go back to the scratch, when set.
  ~TreeRows() {
    if (scratch == nullptr) return;
    for (auto &r : rows) scratch->give_terms(std::move(r.terms));
  }
  TreeRows(const TreeRows &) = delete;
  TreeRows &operator=(const TreeRows &) = delete;
  TreeRows(const F &f, const TreeLayout<F> &l) : f_(f), l_(l) {
    // The bit stage's measurement by bit planes, for a GF(2) < GF(2^16)
    // stage where the target has the kernel (bit_planes.h).
    if (l.bits >= 0) {
      const auto &st = l.stages[size_t(l.bits)];
      if (st.b == 1 && st.d == BitPlaneDots<F>::kBits &&
          BitPlaneDots<F>::kBytes != 0) {
        planes_ = BitPlaneDots<F>(f, st.beta);
        // Frob^k(gamma_j), the measurement of a claim in product form.
        constexpr size_t kB = BitPlaneDots<F>::kBits;
        gamma_twist_.resize(kB * kB);
        for (size_t k = 0; k < kB; ++k)
          for (size_t j = 0; j < kB; ++j)
            gamma_twist_[k * kB + j] = frobenius_power(f, planes_.gamma(j), k);
      }
    }
  }

  std::vector<Row> rows;
  std::vector<Item> order;
  Eq eq;
  const ExtraRows<F> *extra = nullptr;
  // Per node, the rows its stage combines by the plan (TreePlan::routed),
  // checked against the routing on every stage.
  const std::vector<size_t> *routed = nullptr;
  // The prover's working buffers (prover_scratch.h), when set: the stages'
  // and the root's combination buffers, the GKR input row's eq tables and
  // the rows' term lists.
  DomainScratch<F> *scratch = nullptr;

  void add_sparse(const std::vector<Llc> &a, const std::vector<Elt> &b,
                  size_t first) {
    // Rows first .. first + b.size() - 1 of the sparse list A.
    const size_t base = rows.size();
    for (size_t r = 0; r < b.size(); ++r) {
      rows.push_back(Row{{}, b[r], false});
      order.push_back(Item{false, base + r});
    }
    for (const auto &t : a)
      if (t.c >= first && t.c < first + b.size())
        rows[base + t.c - first].terms.push_back({t.w, t.k});
  }
  void add_extra(const ExtraRows<F> &x) {
    extra = &x;
    for (size_t r = 0; r < x.n; ++r) order.push_back(Item{true, r});
  }

  // The stage of node X (non-root): combines the rows reading its region,
  // reveals M (prover: from VALS), and replaces them by the remainder and
  // the measurement rows. Returns false when no row reads the region.
  template <class Hash>
  bool stage(int x, BasicTranscript<Hash> &ts, const std::vector<Elt> *vals,
             std::vector<Elt> &m) {
    const auto &st = l_.stages[size_t(x)];
    const auto &rg = l_.region[size_t(x)];
    auto route = std::make_unique<profiling::Scope>(GH_TREE_KEY(F, "stage.route"));
    std::vector<size_t> touching;
    for (size_t o = 0; o < order.size(); ++o)
      if (!order[o].disabled && reads(order[o], x)) touching.push_back(o);
    if (touching.empty()) return false;
    if (routed != nullptr)
      check(touching.size() == routed->at(size_t(x)),
            "a stage combines the rows its plan routes to it");
    // A lone row runs as it is: no label, no weight. Several are combined
    // with one weight per routed row, from a point extended by the row
    // slots so far (stream_points): every slot of ORDER, the routed ones
    // and the rest, a count the plan fixes.
    std::vector<Elt> w(touching.size(), f_.one());
    if (touching.size() > 1) {
      const std::string label = "gordiehowe.stage:" + st.transcript_label();
      ts.write(reinterpret_cast<const uint8_t *>(label.data()), label.size());
      ts.extend_point_budget_for(order.size(), f_);
      for (auto &v : w) v = ts.elt(f_);
    }
    if (l_.test_hooks.stage_draws != nullptr)
      l_.test_hooks.stage_draws->push_back(touching.size() > 1 ? w.size() : 0);
    // The nodes other than X that the routed rows read: the remainder's.
    uint64_t rem_nodes = 0;
    for (size_t y = 1; y < l_.region.size(); ++y) {
      if (int(y) == x) continue;
      for (size_t t : touching)
        if (reads(order[t], int(y))) {
          rem_nodes |= uint64_t(1) << y;
          break;
        }
    }
    route.reset();
    auto phase = std::make_unique<profiling::Scope>(GH_TREE_KEY(F, "stage.combine"));
    // The combination, split into the region's coordinates and the rest,
    // over L positions: written in chunks under a runner (util/parallel.h's
    // Buffer), so each chunk's thread first touches its own pages.
    parallel::Buffer<Elt> rest_own, cx_own;
    parallel::Buffer<Elt> &rest =
        scratch != nullptr ? scratch->combination : rest_own;
    parallel::fill(rest, size_t(l_.L), f_.zero());
    Elt rhs = f_.zero();
    bool any_extra = false, eq_part = false;
    Elt eq_scale = f_.zero();
    std::vector<Elt> xw;
    const size_t d = st.d, n = field_degree<F>();
    // Word claims in Frobenius form that this stage opens, weighted:
    //   w sum_k phi^k(c_k <a_k, W>) = sum_k phi^k(phi^-k(w) c_k <a_k, W>).
    // Of degree d, a part of measurement row k (Scaled). Of degree e = d e'
    // (words above the stage's top field T), with k = k0 + d k' and
    // phi^d = phi_T, x^(|T|):
    //   sum_{k0} phi^k0( sum_{k'} phi_T^k'(phi_T^-k'(phi^-k0(w)) c_k
    //                                       <a_k, W>) ),
    // so measurement row k0 carries a claim of degree e' in phi_T, which
    // the stage of T opens (Formed).
    // A claim in product form (PROD set, A empty) has a_k = D_k
    // Frob^-k(alpha) (bit_phase.h).
    struct Scaled {
      const std::vector<size_t> *at;
      std::vector<const Elt *> a;  // per k
      std::vector<Elt> c;          // per k
      const ProductClaim<F> *prod = nullptr;
    };
    std::vector<Scaled> words;
    std::vector<std::vector<Formed>> lifted(d);
    std::vector<Formed> kept;  // claims for other stages, into the remainder
    auto take = [&](const std::vector<size_t> *at,
                    const std::vector<const Elt *> &fa, const Elt *c,
                    const Elt &wt) {
      const size_t e = fa.size();
      check(e % d == 0, "a word claim's degree is a multiple of its stage's");
      if (e == d) {
        Scaled sc{at, fa, {}};
        for (size_t k = 0; k < d; ++k) {
          Elt ck = st.phi_inv(f_, wt, k);
          if (c != nullptr) f_.mul(ck, c[k]);
          sc.c.push_back(ck);
        }
        words.push_back(std::move(sc));
        return;
      }
      for (size_t k0 = 0; k0 < d; ++k0) {
        Formed fm{at, {}, {}, st.t};
        const Elt s = st.phi_inv(f_, wt, k0);
        for (size_t kp = 0; kp < e / d; ++kp) {
          const size_t k = k0 + d * kp;
          fm.a.push_back(fa[k]);
          Elt ck = frobenius_power(f_, s, (n - (st.t * kp) % n) % n);
          if (c != nullptr) f_.mul(ck, c[k]);
          fm.c.push_back(ck);
        }
        lifted[k0].push_back(std::move(fm));
      }
    };
    // The routed rows' product parts, by claim (position list and alpha):
    // each part's twist and scale times its row's weight.
    struct ProdParts {
      const std::vector<size_t> *at;
      const Elt *alpha;
      std::vector<std::pair<size_t, Elt>> terms;
    };
    std::vector<ProdParts> prod_parts;
    for (size_t i = 0; i < touching.size(); ++i) {
      const Item &it = order[touching[i]];
      if (it.extra) {
        for (const auto &cl : extra->claims) {
          if (cl.row != it.idx) continue;
          if (cl.product) {
            // A claim in product form on words of the stage's top field.
            check(st.squaring_chain() && st.b == 1 &&
                      cl.product->d.size() == d &&
                      cl.product->alpha.size() == cl.word_at.size(),
                  "a product-form word-bits claim on the bit node's stage");
            Scaled sc{&cl.word_at, {}, {}, cl.product.get()};
            for (size_t k = 0; k < d; ++k) sc.c.push_back(st.phi_inv(f_, w[i], k));
            words.push_back(std::move(sc));
            continue;
          }
          check(st.squaring_chain() && st.b == 1 &&
                    cl.forms->a.size() % cl.forms->stride == 0,
                "a word-bits claim on the bit node's stage");
          std::vector<const Elt *> fa;
          for (size_t k = 0; k < cl.forms->a.size() / cl.forms->stride; ++k)
            fa.push_back(cl.forms->a.data() + k * cl.forms->stride);
          take(&cl.word_at, fa, nullptr, w[i]);
        }
        if (!any_extra) xw.assign(extra->n, f_.zero());
        any_extra = true;
        xw[it.idx] = w[i];
        f_.add(rhs, f_.mulf(w[i], extra->b[it.idx]));
        for (const auto &t : extra->a)
          if (t.c == it.idx) f_.add(rest[t.w], f_.mulf(w[i], t.k));
        continue;
      }
      const Row &r = rows[it.idx];
      f_.add(rhs, f_.mulf(w[i], r.rhs));
      // A lone row's weight is one: the unit optimization adds its terms
      // (and a part of scale one) without the multiplication.
      const bool unit = test_switches().stage_opt_on(StageOpt::kUnit);
      if (unit && w[i] == f_.one()) {
        for (const auto &[pos, k] : r.terms) f_.add(rest[pos], k);
      } else {
        for (const auto &[pos, k] : r.terms) f_.add(rest[pos], f_.mulf(w[i], k));
      }
      for (const auto &pt : r.parts) {
        const Elt c = f_.mulf(w[i], pt.scale);
        if (pt.alpha != nullptr) {
          size_t q = 0;
          while (q < prod_parts.size() && (prod_parts[q].at != pt.at ||
                                           prod_parts[q].alpha != pt.alpha))
            ++q;
          if (q == prod_parts.size()) prod_parts.push_back({pt.at, pt.alpha, {}});
          prod_parts[q].terms.push_back({pt.twist, c});
          continue;
        }
        if (unit && c == f_.one()) {
          for (size_t y = 0; y < pt.at->size(); ++y)
            f_.add(rest[(*pt.at)[y]], pt.a[y]);
        } else {
          for (size_t y = 0; y < pt.at->size(); ++y)
            f_.add(rest[(*pt.at)[y]], f_.mulf(c, pt.a[y]));
        }
      }
      for (const auto &fm : r.formed) {
        if (fm.base == st.b) {
          take(fm.at, fm.a, fm.c.data(), w[i]);
          continue;
        }
        Formed kf = fm;
        for (size_t k = 0; k < kf.c.size(); ++k)
          f_.mul(kf.c[k], frobenius_power(f_, w[i], (n - (fm.base * k) % n) % n));
        kept.push_back(std::move(kf));
      }
      if (r.eq) {
        eq_part = true;
        eq_scale = w[i];
      }
    }
    // The routed rows' product parts (bit_phase.h) of one claim: their sum
    // C_j Frob^-k_j(alpha[y]) is one GF(2)-linear map of alpha[y]
    // (twist_sum), applied once per word.
    for (const auto &pp : prod_parts) {
      const LinearMap<F> lm = twist_sum(f_, pp.terms);
      const size_t ny = pp.at->size();
      std::vector<Elt> v(ny);
      parallel::for_chunks(ny, parallel::grain_for(ny, parallel::kChunks),
                           [&](size_t b, size_t e) {
                             lm.apply(pp.alpha + b, v.data() + b, e - b);
                           });
      for (size_t y = 0; y < ny; ++y) f_.add(rest[(*pp.at)[y]], v[y]);
    }
    if (any_extra) extra->accumulate(rest.data(), xw.data());
    // The region's coordinates move to CX, in chunks.
    parallel::Buffer<Elt> &cx = scratch != nullptr ? scratch->region : cx_own;
    cx.resize(rg.n);
    parallel::for_chunks(rg.n, parallel::grain_for(rg.n, parallel::kChunks),
                         [&](size_t b, size_t e) {
                           for (size_t i = b; i < e; ++i) {
                             cx[i] = rest[rg.off + i];
                             rest[rg.off + i] = f_.zero();
                           }
                         });
    phase = std::make_unique<profiling::Scope>(GH_TREE_KEY(F, "stage.forms"));
    // Forms over the groups. A composed view's coefficients take its basis
    // change (ComposedBits).
    std::vector<Elt> a;
    if (x == l_.bits)
      for (const auto &v : l_.views) {
        const size_t lo = v.group * d;
        bool any = false;
        for (size_t i = 0; i < v.degree; ++i) any = any || cx[lo + i] != f_.zero();
        if (!any) continue;
        l_.bases.at(v.degree).add_forms(f_, st, &cx[lo], rg.groups, v.group, a);
        for (size_t i = 0; i < v.degree; ++i) cx[lo + i] = f_.zero();
      }
    st.add_forms(f_, cx.data(), rg.n, rg.groups, a);
    if (eq_part && x == l_.bits) {
      // The eq forms index absolute input groups; take the run's.
      std::vector<Elt> ae;
      const size_t g0 = run_begin / d;
      std::vector<typename PackingStage<F>::Block> blocks;
      for (const auto &v : l_.views) {
        const auto &cb = l_.bases.at(v.degree);
        blocks.push_back({g0 + v.group, cb.r, cb.tau.data()});
      }
      st.add_eq_forms(f_, eq.logv, g0 + rg.groups, eq.g0, eq.g1, eq.alpha,
                      eq_scale, ae, blocks);
      const size_t ng = g0 + rg.groups;
      for (size_t k = 0; k < d; ++k)
        for (size_t g = 0; g < rg.groups; ++g)
          f_.add(a[k * rg.groups + g], ae[k * ng + g0 + g]);
    }
    // The bit stage's words by bit planes (bit_planes.h): the pivot bits
    // of the groups' words and of each word claim's words, once per
    // position list, in chunks under a runner.
    const bool by_planes =
        vals != nullptr && x == l_.bits && planes_.has_kernel();
    std::vector<const std::vector<size_t> *> plane_at;
    std::vector<std::vector<uint8_t>> plane_piv;
    std::vector<size_t> word_list;
    if (by_planes) {
      phase = std::make_unique<profiling::Scope>(
          GH_TREE_KEY(F, "stage.pivots"));
      auto list_of = [&](const std::vector<size_t> *at) {
        size_t i = 0;
        while (i < plane_at.size() && plane_at[i] != at) ++i;
        if (i == plane_at.size()) plane_at.push_back(at);
        return i;
      };
      list_of(&rg.group_at);
      for (const auto &sc : words) word_list.push_back(list_of(sc.at));
      plane_piv.resize(plane_at.size());
      for (size_t i = 0; i < plane_at.size(); ++i) {
        const std::vector<size_t> &at = *plane_at[i];
        plane_piv[i].resize(2 * at.size());
        uint8_t *out = plane_piv[i].data();
        parallel::for_chunks(
            at.size(), parallel::grain_for(at.size(), parallel::kChunks),
            [&](size_t lo, size_t hi) {
              planes_.pivots(at, *vals, lo, hi, out);
            });
      }
    }
    phase = std::make_unique<profiling::Scope>(GH_TREE_KEY(F, "stage.measure"));
    // A claim in product form, a_k[q] = D_k Frob^-k(alpha_q) (bit_phase.h):
    //   z_k = sum_q a_k[q] y_q = D_k Frob^-k(sum_q alpha_q Frob^k(y_q))
    //       = D_k Frob^-k(sum_i Frob^k(gamma_i) G_i),
    // with y_q = sum_i gamma_i g_{q,i} by its pivot bits and G_i = sum_q
    // alpha_q g_{q,i}: one bit-plane pass for all k. Without the kernel its
    // forms are materialized (phase_forms) and measured as the others.
    std::vector<std::array<Elt, BitPlaneDots<F>::kBits>> prod_g(words.size());
    std::deque<BitForms<F>> prod_forms;
    std::vector<std::vector<const Elt *>> prod_a(words.size());
    if (vals != nullptr)
      for (size_t i = 0; i < words.size(); ++i) {
        const auto &sc = words[i];
        if (sc.prod == nullptr) continue;
        if (by_planes) {
          // In chunks of words under a runner, each chunk's sums added in
          // chunk order (sums of field elements are exact).
          constexpr size_t kB = BitPlaneDots<F>::kBits;
          const size_t ny = sc.at->size();
          const size_t grain = parallel::grain_for(ny, parallel::kChunks);
          std::vector<std::array<Elt, kB>> part(parallel::chunks(ny, grain));
          const Elt *alpha = sc.prod->alpha.data();
          const uint8_t *piv = plane_piv[word_list[i]].data();
          parallel::for_chunks(ny, grain, [&](size_t b, size_t e) {
            planes_.sums(f_, alpha, piv, ny, b, e, part[b / grain].data());
          });
          prod_g[i].fill(f_.zero());
          for (const auto &pc : part)
            for (size_t j = 0; j < kB; ++j) f_.add(prod_g[i][j], pc[j]);
          continue;
        }
        prod_forms.push_back(phase_forms(f_, *sc.prod));
        for (size_t k = 0; k < d; ++k)
          prod_a[i].push_back(prod_forms.back().a.data() + k * sc.at->size());
      }
    // Masked measurements, each its own task under a runner
    // (util/parallel.h).
    if (vals != nullptr) {
      m.assign(d, f_.zero());
      parallel::for_each(d, parallel::grain_for(d, parallel::kChunks),
                         [&](size_t k) {
        Elt z = f_.zero();
        if (by_planes) {
          if (rg.groups > 0)
            f_.add(z, planes_.dot(f_, &a[k * rg.groups], plane_piv[0].data(),
                                  rg.groups));
          for (size_t i = 0; i < words.size(); ++i) {
            const auto &sc = words[i];
            if (sc.at->empty()) continue;
            if (sc.prod != nullptr) {
              Elt s = f_.zero();
              for (size_t j = 0; j < BitPlaneDots<F>::kBits; ++j)
                f_.add(s, f_.mulf(gamma_twist_[k * BitPlaneDots<F>::kBits + j],
                                  prod_g[i][j]));
              // S is a witness value: frobenius_power_ct.
              s = frobenius_power_ct(f_, s, (n - k % n) % n);
              f_.add(z, f_.mulf(f_.mulf(sc.c[k], sc.prod->d[k]), s));
              continue;
            }
            const Elt s = planes_.dot(f_, sc.a[k],
                                      plane_piv[word_list[i]].data(),
                                      sc.at->size());
            f_.add(z, f_.mulf(sc.c[k], s));
          }
        } else {
          for (size_t g = 0; g < rg.groups; ++g)
            f_.add(z, f_.mulf(a[k * rg.groups + g], (*vals)[rg.group_at[g]]));
          for (size_t i = 0; i < words.size(); ++i) {
            const auto &sc = words[i];
            const Elt *ak = sc.prod != nullptr ? prod_a[i][k] : sc.a[k];
            f_.add(z, f_.mulf(sc.c[k], dot(sc.at, ak, *vals)));
          }
        }
        for (const auto &fm : lifted[k]) f_.add(z, formed_value(fm, *vals));
        f_.add(z, mask_value(x, k, *vals));
        m[k] = z;
      });
    }
    check(m.size() == d, "stage measurement count");
    ts.write(m.data(), 1, d, f_);
    phase = std::make_unique<profiling::Scope>(GH_TREE_KEY(F, "stage.rows"));
    // The remainder row: its nonzero coefficients (public values) in
    // position order. In chunks under a runner, each chunk of positions
    // counts its own, then writes them at its place among the earlier
    // chunks'.
    Row rem{{}, rhs, false};
    if (scratch != nullptr) rem.terms = scratch->take_terms();
    const size_t nl = l_.L;
    const size_t grain = parallel::grain_for(nl, parallel::kChunks);
    if (parallel::chunks(nl, grain) < 2) {
      for (size_t pos = 0; pos < nl; ++pos)
        if (rest[pos] != f_.zero()) rem.terms.push_back({pos, rest[pos]});
    } else {
      std::vector<size_t> at(parallel::chunks(nl, grain) + 1, 0);
      parallel::for_chunks(nl, grain, [&](size_t b, size_t e) {
        size_t k = 0;
        for (size_t pos = b; pos < e; ++pos) k += rest[pos] != f_.zero();
        at[b / grain + 1] = k;
      });
      for (size_t c = 1; c < at.size(); ++c) at[c] += at[c - 1];
      rem.terms.resize(at.back());
      parallel::for_chunks(nl, grain, [&](size_t b, size_t e) {
        auto *out = rem.terms.data() + at[b / grain];
        for (size_t pos = b; pos < e; ++pos)
          if (rest[pos] != f_.zero()) *out++ = {pos, rest[pos]};
      });
    }
    for (size_t k = 0; k < d; ++k) {
      f_.sub(rem.rhs, st.phi(f_, m[k], k));
      add_mask_twist(x, k, rem.terms);
    }
    rem.formed = std::move(kept);
    rem.nodes = rem_nodes;
    phase = std::make_unique<profiling::Scope>(GH_TREE_KEY(F, "stage.meas_rows"));
    const bool parts = test_switches().stage_opt_on(StageOpt::kParts);
    const Elt *stored = nullptr;
    if (parts) {
      forms_.push_back(std::move(a));
      stored = forms_.back().data();
    }
    std::vector<Item> out;
    for (size_t o = 0; o < order.size(); ++o) {
      if (o == touching[0]) {
        rows.push_back(std::move(rem));
        out.push_back(Item{false, rows.size() - 1});
        for (size_t k = 0; k < d; ++k) {
          Row mr{{}, m[k], false};
          // Every group, a zero coefficient's included: the row's
          // routing is structural. The parts optimization keeps them as
          // one part of scale one over the forms, which it stores.
          if (parts) {
            mr.parts.push_back({&rg.group_at, stored + k * rg.groups, f_.one()});
          } else {
            for (size_t g = 0; g < rg.groups; ++g)
              mr.terms.push_back({rg.group_at[g], a[k * rg.groups + g]});
          }
          for (const auto &sc : words) {
            if (sc.prod != nullptr) {
              mr.parts.push_back({sc.at, nullptr,
                                  f_.mulf(sc.c[k], sc.prod->d[k]),
                                  sc.prod->alpha.data(), k});
              continue;
            }
            mr.parts.push_back({sc.at, sc.a[k], sc.c[k]});
          }
          mr.formed = std::move(lifted[k]);
          add_mask(x, k, mr.terms);
          rows.push_back(std::move(mr));
          out.push_back(Item{false, rows.size() - 1});
        }
        continue;
      }
      Item it = order[o];
      for (size_t t : touching)
        if (t == o) it.disabled = true;
      out.push_back(it);
    }
    order = std::move(out);
    if (scratch != nullptr && !scratch->keep()) {
      release(rest);
      release(cx);
    }
    return true;
  }

  // The root: every row combined with fresh challenges, then each root
  // child's measurements; the Ligero rows' right-hand sides and their
  // accumulator. The prover passes the committed vector W.
  struct Root {
    // Over L, written in chunks (util/parallel.h's Buffer).
    parallel::Buffer<Elt> coeff;
    Elt target;
    // Per root child: d * groups, or none when the child's Ligero
    // coefficients come without them (the verifier, add_coefficients).
    std::vector<std::vector<Elt>> forms;
    std::vector<int> children;
  };
  // With FORMS false (the verifier, which measures nothing), a root child
  // whose stage has add_coefficients gets no forms; root_accumulate then
  // computes its coefficients from COEFF.
  template <class Hash>
  Root root(BasicTranscript<Hash> &ts, bool forms = true) const {
    static const char tag[] = "relative-pack/linear-batch/v1";
    ts.write(reinterpret_cast<const uint8_t *>(tag), sizeof(tag));
    std::vector<Elt> alpha(order.size());
    ts.extend_point_budget_for(alpha.size(), f_);
    for (auto &x : alpha) x = ts.elt(f_);
    auto phase = std::make_unique<profiling::Scope>(GH_TREE_KEY(F, "root.combine"));
    Root r;
    if (scratch != nullptr) r.coeff = std::move(scratch->combination);
    parallel::fill(r.coeff, size_t(l_.L), f_.zero());
    r.target = f_.zero();
    std::vector<Elt> xw;
    if (extra) xw.assign(extra->n, f_.zero());
    // The rows' parts and their scales, added after the loop (add_parts).
    std::vector<const Part *> parts;
    std::vector<Elt> scales;
    auto sub_phase =
        std::make_unique<profiling::Scope>(GH_TREE_KEY(F, "root.combine.rows"));
    for (size_t o = 0; o < order.size(); ++o) {
      const Item &it = order[o];
      if (it.disabled) continue;
      if (it.extra) {
        for (const auto &cl : extra->claims)
          check(cl.row != it.idx, "a word-bits claim reaches the root");
        xw[it.idx] = alpha[o];
        f_.add(r.target, f_.mulf(alpha[o], extra->b[it.idx]));
        continue;
      }
      const Row &row = rows[it.idx];
      check(!row.eq, "the input row's packed bits reach the root");
      check(row.formed.empty(), "a word claim in Frobenius form reaches the root");
      f_.add(r.target, f_.mulf(alpha[o], row.rhs));
      for (const auto &[pos, k] : row.terms)
        f_.add(r.coeff[pos], f_.mulf(alpha[o], k));
      for (const auto &pt : row.parts) {
        parts.push_back(&pt);
        scales.push_back(f_.mulf(alpha[o], pt.scale));
      }
    }
    sub_phase =
        std::make_unique<profiling::Scope>(GH_TREE_KEY(F, "root.combine.parts"));
    add_parts(r.coeff.data(), parts, scales);
    sub_phase =
        std::make_unique<profiling::Scope>(GH_TREE_KEY(F, "root.combine.extra"));
    if (extra) {
      for (const auto &t : extra->a)
        f_.add(r.coeff[t.w], f_.mulf(xw[t.c], t.k));
      if (extra->accumulate) extra->accumulate(r.coeff.data(), xw.data());
    }
    sub_phase.reset();
    phase = std::make_unique<profiling::Scope>(GH_TREE_KEY(F, "root.forms"));
    r.children = l_.packed_children();
    for (int c : r.children) {
      const auto &rg = l_.region[size_t(c)];
      std::vector<Elt> a;
      if (!forms && PackingStage<F>::kCoefficients) {
        r.forms.push_back(std::move(a));
        continue;
      }
      l_.stages[size_t(c)].add_forms(f_, r.coeff.data() + rg.off, rg.n,
                                     rg.groups, a);
      r.forms.push_back(std::move(a));
    }
    phase = std::make_unique<profiling::Scope>(GH_TREE_KEY(F, "root.check"));
    // No coordinate of a deeper region is left.
    for (size_t x = 1; x < l_.region.size(); ++x) {
      if (l_.tree->nodes[x].parent == 0) continue;
      const auto &rg = l_.region[x];
      for (size_t i = 0; i < rg.n; ++i)
        check(r.coeff[rg.off + i] == f_.zero(),
              "a claim on a packed region reaches the root");
    }
    return r;
  }
  // The root's measurements from the committed vector W.
  void root_measure(const Root &r, const std::vector<Elt> &W,
                    std::vector<Elt> &m) const {
    m.clear();
    for (size_t ci = 0; ci < r.children.size(); ++ci) {
      const int c = r.children[ci];
      const auto &st = l_.stages[size_t(c)];
      const auto &rg = l_.region[size_t(c)];
      const size_t mask = l_.mask_L[size_t(c)];
      // The groups' sums per k, in chunks of groups under a runner
      // (util/parallel.h), each chunk's partial sums added in chunk order;
      // field sums are exact, so the measurements are the same elements.
      const size_t grain = parallel::grain_for(rg.groups, parallel::kChunks);
      const size_t nc = parallel::chunks(rg.groups, grain);
      std::vector<Elt> part(nc * st.d, f_.zero());
      parallel::for_chunks(rg.groups, grain, [&](size_t b, size_t e) {
        Elt *pz = &part[(b / grain) * st.d];
        for (size_t k = 0; k < st.d; ++k) {
          const Elt *fk = &r.forms[ci][k * rg.groups];
          for (size_t g = b; g < e; ++g)
            f_.add(pz[k], f_.mulf(fk[g], W[rg.group_at[g]]));
        }
      });
      for (size_t k = 0; k < st.d; ++k) {
        Elt z = f_.zero();
        for (size_t q = 0; q < nc; ++q) f_.add(z, part[q * st.d + k]);
        if (st.squaring_chain())
          f_.add(z, W[l_.committed(mask + st.sigma(k))]);
        for (size_t i = 0; i < st.m; ++i)
          f_.add(z, f_.mulf(st.gamma[i], W[l_.committed(mask + k * st.m + i)]));
        m.push_back(z);
      }
    }
  }
  size_t root_measurements() const {
    size_t n = 0;
    for (int c : l_.packed_children()) n += l_.stages[size_t(c)].d;
    return n;
  }
  // Right-hand sides of the root's Ligero rows.
  std::vector<Elt> root_rhs(const Root &r, const std::vector<Elt> &m) const {
    auto out = m;
    Elt last = r.target;
    size_t at = 0;
    for (int c : r.children) {
      const auto &st = l_.stages[size_t(c)];
      for (size_t k = 0; k < st.d; ++k) f_.sub(last, st.phi(f_, m[at++], k));
    }
    out.push_back(last);
    return out;
  }
  // The root's Ligero rows into A, by Ligero's challenges ALPHA.
  void root_accumulate(const Root &r, Elt *out, const Elt *alpha) const {
    const size_t last = root_measurements();
    size_t row = 0;
    for (size_t ci = 0; ci < r.children.size(); ++ci) {
      const int c = r.children[ci];
      const auto &st = l_.stages[size_t(c)];
      const auto &rg = l_.region[size_t(c)];
      // Each group's coefficient sum_k alpha_k forms_k[g], in chunks of
      // groups under a runner (util/parallel.h), then added at its word
      // in group order (aliased groups share a word); field sums are
      // exact, so OUT is the same. Without forms (the verifier), the
      // stage's add_coefficients gives the same coefficients from the
      // root's coefficients on the child's region.
      if (r.forms[ci].empty()) {
        if constexpr (PackingStage<F>::kCoefficients) {
          std::vector<Elt> v(rg.groups, f_.zero());
          st.add_coefficients(f_, &alpha[row], r.coeff.data() + rg.off, rg.n,
                              rg.groups, v.data());
          for (size_t g = 0; g < rg.groups; ++g)
            f_.add(out[rg.group_at[g]], v[g]);
        }
      } else {
        std::vector<Elt> v(rg.groups);
        parallel::for_chunks(
            rg.groups, parallel::grain_for(rg.groups, parallel::kChunks),
            [&](size_t b, size_t e) {
              for (size_t g = b; g < e; ++g) v[g] = f_.zero();
              for (size_t k = 0; k < st.d; ++k) {
                const Elt a = alpha[row + k];
                const Elt *fk = &r.forms[ci][k * rg.groups];
                for (size_t g = b; g < e; ++g) f_.add(v[g], f_.mulf(a, fk[g]));
              }
            });
        for (size_t g = 0; g < rg.groups; ++g) f_.add(out[rg.group_at[g]], v[g]);
      }
      for (size_t k = 0; k < st.d; ++k, ++row) {
        // A squaring-chain-masks child: sigma_k in row k, its twist
        // -phi^k(sigma_k) = -s_{k,bk} in the last.
        if (st.squaring_chain()) {
          const size_t mask = l_.mask_L[size_t(c)];
          f_.add(out[l_.committed(mask + st.sigma(k))], alpha[row]);
          f_.sub(out[l_.committed(mask + st.twist(k))], alpha[last]);
        }
        for (size_t i = 0; i < st.m; ++i) {
          const size_t at =
              l_.committed(l_.mask_L[size_t(c)] + k * st.m + i);
          f_.add(out[at], f_.mulf(alpha[row], st.gamma[i]));
          f_.sub(out[at], f_.mulf(alpha[last], st.gamma_phi[k * st.m + i]));
        }
      }
    }
    // Root own coordinates, then the other stages' prefix masks.
    for (size_t l = 0; l < l_.own; ++l)
      f_.add(out[l_.committed(l)], f_.mulf(alpha[last], r.coeff[l]));
    for (size_t l = l_.prefix_L; l < l_.prefix_L + l_.prefix; ++l)
      if (r.coeff[l] != f_.zero())
        f_.add(out[l_.committed(l)], f_.mulf(alpha[last], r.coeff[l]));
    // Flat root children: their coordinates are committed cells.
    for (size_t x = 1; x < l_.region.size(); ++x) {
      if (!l_.flat[x]) continue;
      const auto &rg = l_.region[x];
      for (size_t i = 0; i < rg.n; ++i)
        if (r.coeff[rg.off + i] != f_.zero())
          f_.add(out[l_.flat_at[x] + i], f_.mulf(alpha[last], r.coeff[rg.off + i]));
    }
  }

  // A root without children: the rows as Ligero's, over committed indices.
  void flat(std::vector<Llc> &a, std::vector<Elt> &b, size_t &extra_base) const {
    extra_base = 0;
    size_t ci = 0;
    bool seen_extra = false;
    for (const Item &it : order) {
      check(!it.disabled, "flat rows");
      if (it.extra) {
        if (!seen_extra) extra_base = ci;
        seen_extra = true;
        b.push_back(extra->b[it.idx]);
        ++ci;
        continue;
      }
      check(!seen_extra, "flat rows: the extra rows come last");
      const Row &row = rows[it.idx];
      check(row.formed.empty(), "flat rows: a word claim in Frobenius form");
      for (const auto &[pos, k] : row.terms) a.push_back(Llc{ci, pos, k});
      for (const auto &pt : row.parts) {
        if (pt.alpha != nullptr) {
          const auto v = product_part(pt, pt.scale);
          for (size_t y = 0; y < pt.at->size(); ++y)
            a.push_back(Llc{ci, (*pt.at)[y], v[y]});
          continue;
        }
        for (size_t y = 0; y < pt.at->size(); ++y)
          a.push_back(Llc{ci, (*pt.at)[y], f_.mulf(pt.scale, pt.a[y])});
      }
      b.push_back(row.rhs);
      ++ci;
    }
    if (!seen_extra) extra_base = ci;
    if (extra)
      for (const auto &t : extra->a) a.push_back(Llc{extra_base + t.c, t.w, t.k});
  }

  size_t run_begin = 0;

 private:
  // Whether a row reads node X's region, by structure alone: a term's
  // position, never its coefficient's value, so the routing is a function
  // of the plan.
  bool reads(const Item &it, int x) const {
    if (it.extra) return (extra->nodes.at(it.idx) >> x) & 1;
    const Row &r = rows[it.idx];
    if (r.eq && x == l_.bits) return true;
    if ((r.nodes >> x) & 1) return true;
    const auto &rg = l_.region[size_t(x)];
    for (const auto &[pos, k] : r.terms)
      if (pos >= rg.off && pos < rg.off + rg.n) return true;
    for (const auto &pt : r.parts)
      for (size_t pos : *pt.at)
        if (pos >= rg.off && pos < rg.off + rg.n) return true;
    for (const auto &fm : r.formed)
      if (fm.base == l_.stages[size_t(x)].b) return true;
    return false;
  }
  // COEFF[at[y]] += C_i a_i[y] over the parts PS (scales CS), the parts of
  // one position list fused: per y one unreduced sum of the list's
  // products and one reduction. Under a runner (util/parallel.h) a list's
  // y run in chunks: chunks of y when the chunks' position spans do not
  // overlap (each chunk then writes its own positions), and otherwise
  // chunks by position range. Then the positions split into
  // parallel::kChunks ranges of about equal entry counts, a stable
  // counting sort orders the y by range, and each chunk adds the y of its
  // range, so no coefficient is written by two chunks. The chunks and the
  // order follow from the public layout only. Field sums are exact, so
  // COEFF is the same in both modes, and the same as the parts added one
  // at a time.
  void add_parts(Elt *coeff, const std::vector<const Part *> &ps,
                 const std::vector<Elt> &cs) const {
    // The parts' position lists in their first part's order.
    std::vector<std::pair<const std::vector<size_t> *, std::vector<size_t>>>
        lists;
    for (size_t i = 0; i < ps.size(); ++i) {
      size_t l = 0;
      while (l < lists.size() && lists[l].first != ps[i]->at) ++l;
      if (l == lists.size()) lists.push_back({ps[i]->at, {}});
      lists[l].second.push_back(i);
    }
    for (const auto &[atp, idx] : lists) {
      const std::vector<size_t> &at = *atp;
      const size_t ny = at.size();
      std::vector<const Elt *> a;
      std::vector<Elt> c;
      // Product parts (bit_phase.h) of one alpha: their sum C_j
      // Frob^-k_j(alpha[y]) is one GF(2)-linear map of alpha[y]
      // (twist_sum), materialized once and fused as a part of scale one.
      std::vector<std::pair<const Elt *, std::vector<std::pair<size_t, Elt>>>>
          prods;
      for (size_t j : idx) {
        const Part &p = *ps[j];
        if (p.alpha == nullptr) {
          a.push_back(p.a);
          c.push_back(cs[j]);
          continue;
        }
        size_t q = 0;
        while (q < prods.size() && prods[q].first != p.alpha) ++q;
        if (q == prods.size()) prods.push_back({p.alpha, {}});
        prods[q].second.push_back({p.twist, cs[j]});
      }
      // Each written in its chunks (util/parallel.h's Buffer).
      std::deque<parallel::Buffer<Elt>> mats;
      for (const auto &[alpha, terms] : prods) {
        const LinearMap<F> lm = twist_sum(f_, terms);
        mats.emplace_back(ny);
        Elt *v = mats.back().data();
        parallel::for_chunks(ny, parallel::grain_for(ny, parallel::kChunks),
                             [&](size_t b, size_t e) {
                               lm.apply(alpha + b, v + b, e - b);
                             });
        a.push_back(v);
        c.push_back(f_.one());
      }
      const size_t np = a.size();
      auto add_y = [&](size_t y) {
        typename F::Accum acc{};
        for (size_t j = 0; j < np; ++j) f_.mac(acc, c[j], a[j][y]);
        f_.add(coeff[at[y]], f_.reduce(acc));
      };
      const size_t nq =
          parallel::chunks(ny, parallel::grain_for(ny, parallel::kChunks));
      if (nq < 2) {
        for (size_t y = 0; y < ny; ++y) add_y(y);
        continue;
      }
      const size_t yg = parallel::grain_for(ny, parallel::kChunks);
      // Each chunk of y's positions span [lo, hi].
      std::vector<size_t> lo(nq, SIZE_MAX), hi(nq, 0);
      parallel::for_chunks(ny, yg, [&](size_t b, size_t e) {
        const auto [mn, mx] = std::minmax_element(at.begin() + long(b),
                                                  at.begin() + long(e));
        lo[b / yg] = *mn;
        hi[b / yg] = *mx;
      });
      // Spans that do not overlap (positions that increase with y, a few
      // runs of them): each chunk of y writes its own positions.
      std::vector<size_t> by_lo(nq);
      for (size_t q = 0; q < nq; ++q) by_lo[q] = q;
      std::sort(by_lo.begin(), by_lo.end(),
                [&](size_t a, size_t b) { return lo[a] < lo[b]; });
      bool disjoint = true;
      for (size_t q = 1; q < nq; ++q)
        disjoint = disjoint && hi[by_lo[q - 1]] < lo[by_lo[q]];
      if (disjoint) {
        parallel::for_chunks(ny, yg, [&](size_t b, size_t e) {
          for (size_t y = b; y < e; ++y) add_y(y);
        });
        continue;
      }
      // Otherwise a counting sort by range of positions, on the same chunks
      // of y: each chunk's range counts, then each chunk places its y after
      // the earlier chunks' y of the same range, so ORDER is the stable
      // sort's.
      // The ranges balance the entries: the positions fall into kFine
      // buckets of equal width per range, and consecutive buckets join
      // into nq ranges of about ny / nq entries each (a bucket stays
      // whole, so the ranges still split the positions).
      constexpr size_t kFine = 64;
      const size_t nf = nq * kFine;
      const size_t base = *std::min_element(lo.begin(), lo.end());
      const size_t span = (*std::max_element(hi.begin(), hi.end()) - base) / nf + 1;
      std::vector<size_t> fine(nq * nf, 0);
      parallel::for_chunks(ny, yg, [&](size_t b, size_t e) {
        size_t *fc = &fine[(b / yg) * nf];
        for (size_t y = b; y < e; ++y) ++fc[(at[y] - base) / span];
      });
      std::vector<size_t> range_of(nf);
      for (size_t k = 0, r = 0, seen = 0; k < nf; ++k) {
        range_of[k] = r;
        for (size_t c = 0; c < nq; ++c) seen += fine[c * nf + k];
        while (r + 1 < nq && seen * nq >= (r + 1) * ny) ++r;
      }
      // CNT[c nq + r]: chunk c's y in range r, then their first place.
      std::vector<size_t> cnt(nq * nq, 0), start(nq + 1, 0);
      // Every place written by the placement below.
      parallel::Buffer<size_t> order(ny);
      for (size_t c = 0; c < nq; ++c)
        for (size_t k = 0; k < nf; ++k)
          cnt[c * nq + range_of[k]] += fine[c * nf + k];
      for (size_t r = 0; r < nq; ++r) {
        size_t s = start[r];
        for (size_t c = 0; c < nq; ++c) {
          const size_t k = cnt[c * nq + r];
          cnt[c * nq + r] = s;
          s += k;
        }
        start[r + 1] = s;
      }
      parallel::for_chunks(ny, yg, [&](size_t b, size_t e) {
        size_t *next = &cnt[(b / yg) * nq];
        for (size_t y = b; y < e; ++y)
          order[next[range_of[(at[y] - base) / span]]++] = y;
      });
      parallel::for_each(nq, 1, [&](size_t q) {
        for (size_t x = start[q]; x < start[q + 1]; ++x) add_y(order[x]);
      });
    }
  }
  // A product part's coefficients times C: C Frob^-twist(alpha[y]).
  std::vector<Elt> product_part(const Part &pt, const Elt &c) const {
    const size_t ny = pt.at->size();
    std::vector<Elt> v(ny);
    const LinearMap<F> lm = twist_sum(f_, {{pt.twist, c}});
    parallel::for_chunks(ny, parallel::grain_for(ny, parallel::kChunks),
                         [&](size_t b, size_t e) {
                           lm.apply(pt.alpha + b, v.data() + b, e - b);
                         });
    return v;
  }
  // <a, W> on the prover's values.
  Elt dot(const std::vector<size_t> *at, const Elt *a,
          const std::vector<Elt> &vals) const {
    typename F::Accum acc{};
    for (size_t y = 0; y < at->size(); ++y) f_.mac(acc, a[y], vals[(*at)[y]]);
    return f_.reduce(acc);
  }
  // A Frobenius-form claim's value on the prover's values.
  Elt formed_value(const Formed &fm, const std::vector<Elt> &vals) const {
    Elt z = f_.zero();
    for (size_t k = 0; k < fm.a.size(); ++k)
      f_.add(z, frobenius_power_ct(f_, f_.mulf(fm.c[k], dot(fm.at, fm.a[k], vals)),
                                   fm.base * k));
    return z;
  }
  Elt mask_value(int x, size_t k, const std::vector<Elt> &vals) const {
    const auto &st = l_.stages[size_t(x)];
    const size_t at = l_.mask_L[size_t(x)];
    if (st.squaring_chain()) return vals[at + st.sigma(k)];
    Elt s = f_.zero();
    for (size_t i = 0; i < st.m; ++i)
      f_.add(s, f_.mulf(st.gamma[i], vals[at + k * st.m + i]));
    return s;
  }
  // sigma_k's terms in the measurement row.
  void add_mask(int x, size_t k,
                std::vector<std::pair<size_t, Elt>> &terms) const {
    const auto &st = l_.stages[size_t(x)];
    const size_t at = l_.mask_L[size_t(x)];
    if (st.squaring_chain()) {
      terms.push_back({at + st.sigma(k), f_.one()});
      return;
    }
    for (size_t i = 0; i < st.m; ++i)
      terms.push_back({at + k * st.m + i, st.gamma[i]});
  }
  // The mask's twist -phi^k(sigma_k): its terms in the remainder row.
  void add_mask_twist(int x, size_t k,
                      std::vector<std::pair<size_t, Elt>> &terms) const {
    const auto &st = l_.stages[size_t(x)];
    const size_t at = l_.mask_L[size_t(x)];
    if (st.squaring_chain()) {
      terms.push_back({at + st.twist(k), f_.one()});  // characteristic 2
      return;
    }
    for (size_t i = 0; i < st.m; ++i)
      terms.push_back({at + k * st.m + i, f_.negf(st.gamma_phi[k * st.m + i])});
  }

  const F &f_;
  const TreeLayout<F> &l_;
  BitPlaneDots<F> planes_;
  std::vector<Elt> gamma_twist_;  // [k * 16 + j] = Frob^k(gamma_j)
  // The parts optimization's stored forms, which measurement rows point
  // into (a deque: its elements never move).
  std::deque<std::vector<Elt>> forms_;
};

// One domain's circuit, layout and Ligero parameters, shared by its prover
// and verifier.
template <class F, class Hash>
struct TreePlan {
  using Elt = typename F::Elt;
  const Circuit<F> *c = nullptr;
  const PackingTree *tree = nullptr;
  TreeInputs in;
  size_t rate = 0, nreq = 0, block_enc = 0;
  std::unique_ptr<TreeLayout<F>> layout;
  std::unique_ptr<LigeroParam<F, Hash>> param;
  std::vector<LigeroQuadraticConstraint> lqc;  // committed indices
  size_t nq = 0;
  // Whether the domain runs GKR; without it the circuit has no layers and
  // no input row is proved.
  bool gkr = true;

  TreePlan(const F &f, const Circuit<F> &circ, const PackingTree &t,
           TreeInputs inputs, size_t r, size_t queries, size_t be,
           LigeroMode mode = {}, bool unpacked_s0 = false, bool with_gkr = true)
      : c(&circ), tree(&t), in(std::move(inputs)), rate(r), nreq(queries),
        gkr(with_gkr) {
    check(gkr || circ.nl == 0, "a domain without GKR has a layerless circuit");
    const size_t gkr_pads = ZkCommon<F>::pad_size(circ);
    TreeLayout<F> unaligned(f, t, in, circ.ninputs, circ.npub_in, gkr_pads, 0,
                            unpacked_s0);
    nq = circ.nl + unaligned.nquad + circ.input_products.size();
    auto mk = [&](size_t nw, size_t b) {
      return b == 0 ? LigeroParam<F, Hash>(nw, nq, rate, nreq, mode)
                    : LigeroParam<F, Hash>(nw, nq, rate, nreq, b, mode);
    };
    if (t.nodes[0].children.empty()) {
      param = std::make_unique<LigeroParam<F, Hash>>(mk(unaligned.nw, be));
      layout = std::make_unique<TreeLayout<F>>(f, t, in, circ.ninputs,
                                               circ.npub_in, gkr_pads, 0,
                                               unpacked_s0);
    } else {
      const auto p0 = mk(unaligned.nw, be);
      layout = std::make_unique<TreeLayout<F>>(f, t, in, circ.ninputs,
                                               circ.npub_in, gkr_pads, p0.w,
                                               unpacked_s0);
      param = std::make_unique<LigeroParam<F, Hash>>(mk(layout->nw, p0.block_enc));
    }
    block_enc = param->block_enc;
    // Quadratic constraints: layers, squaring chains (bottom-up), input
    // products.
    const TreeLayout<F> &l = *layout;
    std::vector<LigeroQuadraticConstraint> q(nq);
    ZkCommon<F>::setup_lqc(circ, q, l.pad_L);
    size_t at = circ.nl;
    for (int x : t.bottom_up()) {
      const auto &st = l.stages[size_t(x)];
      if (!st.squaring_chain()) continue;
      const size_t base = l.mask_L[size_t(x)];
      for (size_t k = 1; k < st.d; ++k)
        for (size_t j = 1; j <= st.squarings(k); ++j) {
          const size_t x0 = base + (j == 1 ? st.sigma(k) : st.chain_cell(k, j - 1));
          q.at(at++) = {x0, x0, base + st.chain_cell(k, j)};
        }
    }
    for (const auto &p : circ.input_products) {
      for (size_t i : p)
        check(i >= circ.npub_in && l.input_L.at(i) != TreeLayout<F>::kNone &&
                  l.node_of(l.input_L[i]) == 0 && l.input_L[i] < l.own,
              "an input product reads a packed input");
      q.at(at++) = {l.input_L[p[0]], l.input_L[p[1]], l.input_L[p[2]]};
    }
    check(at == nq, "quadratic constraint count");
    for (auto &x : q) {
      x.x = l.committed(x.x);
      x.y = l.committed(x.y);
      x.z = l.committed(x.z);
    }
    lqc = std::move(q);
  }
  // Per node, the rows its stage combines (index 0 unused), by the
  // routing's structure (TreeRows::reads), from the nodes each of the
  // domain's rows after GKR reads (EXTRA_NODES, ExtraRows::nodes). The GKR
  // rows read the root's pads; the input row reads its private inputs'
  // nodes and, with packed bits, the bit node; a domain without GKR has
  // neither. A stage replaces the rows reading its node by the remainder,
  // which reads every other node they read, and its d measurement rows,
  // which read its parent's region (the groups) and nodes whose stages
  // have run.
  std::vector<size_t> routed;
  void route(const std::vector<uint64_t> &extra_nodes) {
    const TreeLayout<F> &l = *layout;
    std::vector<uint64_t> live(c->nl, uint64_t(1));
    if (gkr) {
      uint64_t input = 1;
      for (size_t i = c->npub_in; i < c->ninputs; ++i)
        if (i < in.run_begin || i >= in.run_end)
          input |= uint64_t(1) << l.node_of(l.input_L.at(i));
      if (l.bits >= 0) input |= uint64_t(1) << l.bits;
      live.push_back(input);
    }
    live.insert(live.end(), extra_nodes.begin(), extra_nodes.end());
    routed.assign(tree->nodes.size(), 0);
    for (int x : tree->inner()) {
      const uint64_t bx = uint64_t(1) << x;
      std::vector<uint64_t> next;
      uint64_t rem = 0;
      for (uint64_t r : live) {
        if ((r & bx) == 0) {
          next.push_back(r);
          continue;
        }
        rem |= r;
        ++routed[size_t(x)];
      }
      if (routed[size_t(x)] == 0) continue;
      next.push_back(rem & ~bx);
      const uint64_t meas =
          uint64_t(1) | (uint64_t(1) << tree->nodes[size_t(x)].parent);
      next.insert(next.end(), l.stages[size_t(x)].d, meas);
      live = std::move(next);
    }
  }
  // The points whose stream a proof over this plan extends, in transcript
  // order, with the row slots each is extended by, after EXTRA rows of the
  // domain's own: the slots start at the GKR rows (one per layer), the
  // input row (both absent without GKR) and EXTRA; a stage that combines
  // rows (two or more routed, ROUTED) draws one weight per routed slot, and every stage replaces its
  // first by the remainder and d measurement rows (d more slots); the root
  // draws one weight per slot; Ligero's linear test, one per row (the
  // root's measurements and its combined row, or every slot when the root
  // has no children).
  std::vector<std::pair<std::string, size_t>> stream_rows(size_t extra) const {
    std::vector<std::pair<std::string, size_t>> out;
    size_t slots = c->nl + (gkr ? 1 : 0) + extra;
    for (int x : tree->inner()) {
      if (routed.at(size_t(x)) > 1)
        out.push_back({"stage:" + std::to_string(x), slots});
      slots += layout->stages[size_t(x)].d;
    }
    if (tree->nodes[0].children.empty()) {
      out.push_back({"ligero.alphal", slots});
    } else {
      out.push_back({"root", slots});
      out.push_back({"ligero.alphal", root_m() + 1});
    }
    return out;
  }
  size_t prefix_rows() const {
    return param->w ? layout->prefix_padded / param->w : 0;
  }
  size_t packed_m() const {
    size_t n = 0;
    for (int x : tree->inner()) n += layout->stages[size_t(x)].d;
    return n;
  }
  size_t root_m() const {
    size_t n = 0;
    for (int c : layout->packed_children()) n += layout->stages[size_t(c)].d;
    return n;
  }
};

// The GKR rows (zk_common.h) and the input row over L.
template <class F, class Hash>
void gkr_rows(const TreePlan<F, Hash> &plan, const Dense<F> &pub,
              const Proof<F> &proof, const ProofAux<F> *aux,
              BasicTranscript<Hash> &ts, Challenge<F> &ch, TreeRows<F> &rows,
              const F &f) {
  using Llc = LigeroLinearConstraint<F>;
  const Circuit<F> &c = *plan.c;
  const TreeLayout<F> &l = *plan.layout;
  std::vector<Llc> a;
  std::vector<typename F::Elt> b;
  size_t ci = 0;
  GkrTrace trace(F::kCharacteristicTwo ? "bin" : "odd");
  std::optional<typename ZkCommon<F>::InputClaim> in_claim;
  trace.step("rows.layers", 0, 0, -1, c.nl, [&] {
    in_claim.emplace(ZkCommon<F>::layer_constraints(c, proof, aux, a, b, ts,
                                                    l.pad_L, f, ch, ci));
    rows.add_sparse(a, b, 0);
  });
  const auto &in = *in_claim;
  // The input row. Its eq tables are the prover's scratch's when set
  // (prover_scratch.h).
  typename TreeRows<F>::Row row;
  if (rows.scratch != nullptr) row.terms = rows.scratch->take_terms();
  row.terms.reserve(c.ninputs - c.npub_in + 2);
  std::vector<typename F::Elt> own[2];
  std::vector<typename F::Elt> *eq =
      rows.scratch != nullptr ? rows.scratch->input_eq : own;
  trace.step("rows.eq", 0, 0, -1, c.ninputs, [&] {
    for (size_t h = 0; h < 2; ++h)
      fill_eq(f, in.logv, c.ninputs, in.g[h], eq[h]);
  });
  const typename F::Elt *eq0 = eq[0].data(), *eq1 = eq[1].data();
  typename F::Elt pub_binding = f.zero();
  for (size_t i = 0; i < c.ninputs; ++i) {
    if (i >= plan.in.run_begin && i < plan.in.run_end) continue;
    auto bi = f.addf(eq0[i], f.mulf(in.alpha, eq1[i]));
    if (l.test_hooks.zero_inputs != nullptr)
      for (size_t z : *l.test_hooks.zero_inputs)
        if (z == i) bi = f.zero();
    if (i < c.npub_in)
      f.add(pub_binding, f.mulf(bi, pub.at(i)));
    else
      row.terms.push_back({l.input_L.at(i), bi});
  }
  if (rows.scratch != nullptr && !rows.scratch->keep()) {
    release(eq[0]);
    release(eq[1]);
  }
  const size_t claim_pad_m1 = in.pi - 3;  // PadLayout(0).ovp_poly_pad(0, 0)
  row.terms.push_back({claim_pad_m1 + 0, f.mone()});
  row.terms.push_back({claim_pad_m1 + 1, f.negf(in.alpha)});
  row.rhs = f.subf(in.got, pub_binding);
  row.eq = plan.in.run_end > plan.in.run_begin;
  rows.eq.logv = in.logv;
  rows.eq.g0 = in.g[0];
  rows.eq.g1 = in.g[1];
  rows.eq.alpha = in.alpha;
  rows.run_begin = plan.in.run_begin;
  rows.rows.push_back(std::move(row));
  rows.order.push_back({false, rows.rows.size() - 1});
}

// The rows of one proof or verification and the GKR challenges they point
// into (the input row's eq tables read them), kept alive together from GKR
// to the opening.
template <class F>
struct ProofRows {
  ProofRows(const F &f, const TreeLayout<F> &l, size_t nl) : rows(f, l), ch(nl) {}
  TreeRows<F> rows;
  Challenge<F> ch;
};

template <class F, class RSF, class Hash>
class TreeProver : public ProverLayers<F> {
  using super = ProverLayers<F>;
  using typename super::bindings;
  using typename super::inputs;
  using Elt = typename F::Elt;

 public:
  TreeProver(const TreePlan<F, Hash> &plan, const F &f, const RSF &rsf)
      : ProverLayers<F>(f), plan_(plan), c_(*plan.c), f_(f), rsf_(rsf),
        pad_(c_.nl) {}

  void commit(ZkProof<F, Hash> &zkp, const Dense<F> &W,
              BasicTranscript<Hash> &tp, RandomEngine &rng) {
    commit_compute(zkp, W, rng);
    commit_write(zkp, tp);
  }
  // The commitment's computation (the words, the tableau, the Merkle tree),
  // which touches no transcript.
  void commit_compute(ZkProof<F, Hash> &zkp, const Dense<F> &W,
                      RandomEngine &rng) {
    const TreeLayout<F> &l = *plan_.layout;
    // The phase timers (util/prover_profile.h): the words'
    // layout and packing until the Ligero commitment.
    auto pack = std::make_unique<profiling::Scope>(F::kCharacteristicTwo ? "bin.pack.witness" : "odd.pack.witness");
    auto sub_phase =
        std::make_unique<profiling::Scope>(GH_TREE_KEY(F, "pack.w.inputs"));
    vals_.assign(l.L, f_.zero());
    // The witness checks accumulate bits and fail once (ct.h).
    // The inputs in chunks under a runner (util/parallel.h): distinct inputs
    // have distinct positions, and each chunk's bit check is combined in
    // chunk order.
    uint64_t bits_ok = 1, sub_ok = 1;
    {
      const size_t n_in = c_.ninputs - c_.npub_in;
      const size_t grain = parallel::grain_for(n_in, parallel::kChunks);
      std::vector<uint64_t> ok(parallel::chunks(n_in, grain), 1);
      check(l.input_L.size() >= c_.ninputs, "input positions");
      const size_t *const pos = l.input_L.data();
      const Elt *const w = W.v_.data();
      Elt *const vals = vals_.data();
      const size_t p0 = c_.npub_in, rb = plan_.in.run_begin,
                   re = plan_.in.run_end;
      parallel::for_chunks(n_in, grain, [&, pos, w, vals](size_t b, size_t e) {
        uint64_t c = 1;
        for (size_t i = p0 + b; i < p0 + e; ++i) {
          if (i >= rb && i < re) c &= ct::is_bit(f_, w[i]);
          vals[pos[i]] = w[i];
        }
        ok[b / grain] = c;
      });
      for (uint64_t c : ok) bits_ok &= c;
    }
    check(bits_ok != 0, "packed input is not a bit");
    sub_phase = std::make_unique<profiling::Scope>(GH_TREE_KEY(F, "pack.w.masks"));
    fill_pad(rng, l.pad_L);
    // Squaring-chain masks (bottom-up), then subfield masks (prefix
    // order).
    for (int x : plan_.tree->bottom_up()) {
      const auto &st = l.stages[size_t(x)];
      if (!st.squaring_chain()) continue;
      const size_t base = l.mask_L[size_t(x)];
      for (size_t k = 0; k < st.d; ++k) vals_[base + st.sigma(k)] = rng.elt(f_);
      for (size_t k = 1; k < st.d; ++k) {
        Elt s = vals_[base + st.sigma(k)];
        for (size_t j = 1; j <= st.squarings(k); ++j) {
          s = f_.mulf(s, s);
          vals_[base + st.chain_cell(k, j)] = s;
        }
      }
    }
    for (size_t i = 0; i < l.prefix; ++i)
      vals_[l.prefix_L + i] = rng.subfield_elt(f_);
    // Composed views' virtual coordinates, top-down from the word.
    sub_phase = std::make_unique<profiling::Scope>(GH_TREE_KEY(F, "pack.w.views"));
    for (const auto &v : l.views)
      for (size_t m = v.path.size(); m-- > 0;) {
        const auto &st = l.stages[size_t(v.path[m])];
        for (size_t q = 0; q < v.degree / st.t; ++q) {
          const Elt p = m + 1 < v.path.size() ? vals_[v.at[m + 1] + q]
                                              : vals_[l.input_L.at(v.target)];
          st.coordinates(f_, p, &vals_[v.at[m] + q * st.d]);
        }
      }
    // Words, bottom-up; the root children's into the commitment.
    sub_phase.reset();
    witness_.assign(l.nw, f_.zero());
    for (int x : plan_.tree->bottom_up()) {
      const auto &st = l.stages[size_t(x)];
      const auto &rg = l.region[size_t(x)];
      const auto &sub = SubfieldInfo<F>::get(f_, st.b);
      const bool bit = x == l.bits;
      auto phase = std::make_unique<profiling::Scope>(GH_TREE_KEY(F, "pack.w.check"));
      // An intermediate node's region holds only its children's words
      // (and zeros), in its subfield by construction: the check
      // optimization skips it. The check guards the honest witness only,
      // which the proof does not need: a test-only self-check
      // (test_switches.h), in chunks under a runner, each chunk's verdict
      // combined in chunk order.
      const bool skip = !plan_.tree->nodes[size_t(x)].declared &&
                        test_switches().stage_opt_on(StageOpt::kCheck);
      if (!bit && !skip && test_switches().subfield_check) {
        const size_t grain = parallel::grain_for(rg.n, parallel::kChunks);
        std::vector<uint64_t> ok(parallel::chunks(rg.n, grain), 1);
        parallel::for_chunks(rg.n, grain, [&](size_t b, size_t e) {
          uint64_t c = 1;
          for (size_t i = b; i < e; ++i)
            c &= sub.contains_bit(f_, vals_[rg.off + i]);
          ok[b / grain] = c;
        });
        for (uint64_t c : ok) sub_ok &= c;
      }
      phase = std::make_unique<profiling::Scope>(GH_TREE_KEY(F, "pack.w.words"));
      check(sub_ok != 0, "a packed value lies outside its subfield");
      const bool top = plan_.tree->nodes[size_t(x)].parent == 0;
      if (top && l.flat[size_t(x)]) {
        for (size_t i = 0; i < rg.n; ++i)
          witness_[l.flat_at[size_t(x)] + i] = vals_[rg.off + i];
        continue;
      }
      // The groups in chunks under a runner (util/parallel.h): a group
      // reads its node's region and writes its word, in the parent's region
      // or the commitment, and the unaliased groups' words are distinct.
      const bool legacy = top && st.legacy_root;
      const bool checked = test_switches().stage_opt_on(StageOpt::kPack);
      if (legacy) (void)ExtensionBasis<F>::get(f_);
      parallel::for_chunks(
          rg.groups, parallel::grain_for(rg.groups, parallel::kChunks),
          [&](size_t g0, size_t g1) {
            for (size_t g = g0; g < g1; ++g) {
              if (rg.alias[g]) continue;
              const size_t lo = g * st.d;
              const size_t n = std::min(st.d, rg.n - lo);
              Elt p;
              if (legacy) {
                const auto &eb = ExtensionBasis<F>::get(f_);
                p = f_.zero();
                for (size_t j = 0; j < n; ++j)
                  eb.pack_coordinate(p, j, vals_[rg.off + lo + j], f_);
              } else if (checked) {
                p = st.pack_checked(f_, &vals_[rg.off + lo], n);
              } else {
                p = st.pack(f_, &vals_[rg.off + lo], n);
              }
              if (top)
                witness_[rg.group_at[g]] = p;
              else
                vals_[rg.group_at[g]] = p;
            }
          });
    }
    sub_phase = std::make_unique<profiling::Scope>(GH_TREE_KEY(F, "pack.w.copy"));
    for (size_t i = 0; i < l.prefix; ++i)
      witness_[l.committed(l.prefix_L + i)] = vals_[l.prefix_L + i];
    for (size_t i = 0; i < l.own; ++i) witness_[l.committed(i)] = vals_[i];
    sub_phase.reset();
    check(witness_.size() == zkp.param.nw, "committed witness size");
    pack.reset();
    lp_ = std::make_unique<LigeroProver<F, RSF, Hash>>(zkp.param);
    if (scratch != nullptr) lp_->a_buffer = &scratch->region;
    lp_->commit_compute(zkp.com, witness_.data(), l.prefix_padded,
                        plan_.lqc.data(), rsf_, rng, f_);
  }
  // The commitment's transcript writes: the layout's binding, then the root.
  void commit_write(ZkProof<F, Hash> &zkp, BasicTranscript<Hash> &tp) {
    check(lp_ != nullptr, "must run commit_compute before commit_write");
    plan_.layout->bind(tp);
    lp_->commit_write(zkp.com, tp);
  }

  // List-radius Ligero: the low-degree round of this commitment, after
  // every commitment (zk_prover.h's ldt_commit).
  void ldt_commit(ZkProof<F, Hash> &zkp, BasicTranscript<Hash> &tp) {
    check(lp_ != nullptr, "must run commit before ldt_commit");
    lp_->ldt_commit(zkp.com_proof, tp, f_);
  }

  bool prove(ZkProof<F, Hash> &zkp, const Dense<F> &W,
             BasicTranscript<Hash> &tsp, const ExtraRows<F> &extra) {
    auto rows = new_rows();
    if (!prove_gkr(zkp, W, tsp, *rows)) return false;
    return prove_rest(zkp, tsp, extra, *rows);
  }
  // The rows of one proof (prove_gkr's, then prove_rest's).
  std::unique_ptr<ProofRows<F>> new_rows() const {
    auto rows = std::make_unique<ProofRows<F>>(f_, *plan_.layout, c_.nl);
    rows->rows.routed = &plan_.routed;
    return rows;
  }
  // GKR on TST and its rows into ROWS; nothing without GKR. False when the
  // circuit is unsatisfied and require_satisfied holds.
  bool prove_gkr(ZkProof<F, Hash> &zkp, const Dense<F> &W,
                 BasicTranscript<Hash> &tsp, ProofRows<F> &pr) {
    check(lp_ != nullptr, "must run commit before prove");
    if (!plan_.gkr) return true;
    Challenge<F> &ch = pr.ch;
    TreeRows<F> &rows = pr.rows;
    ZkCommon<F>::initialize_sumcheck_fiat_shamir(tsp, c_, f_);
    BasicTranscript<Hash> tst = tsp.clone();
    inputs in;
    auto gkr = std::make_unique<profiling::Scope>(F::kCharacteristicTwo ? "bin.gkr.eval" : "odd.gkr.eval");
    auto V = super::eval_circuit(&in, &c_, W.clone(), f_);
    if (V == nullptr) return false;
    for (size_t i = 0; this->require_satisfied && i < V->n1_; ++i)
      if (V->v_[i] != f_.zero()) return false;
    gkr = std::make_unique<profiling::Scope>(F::kCharacteristicTwo ? "bin.gkr.sumcheck" : "odd.gkr.sumcheck");
    bindings bnd;
    ProofAux<F> aux(c_.nl);
    TranscriptSumcheck<F, Hash> tsts(tst, f_);
    super::prove(&zkp.proof, &pad_, &c_, in, &aux, bnd, tsts, f_);
    gkr = std::make_unique<profiling::Scope>(F::kCharacteristicTwo ? "bin.gkr.rows" : "odd.gkr.rows");
    gkr_rows(plan_, W, zkp.proof, &aux, tsp, ch, rows, f_);
    return true;
  }
  // The domain's own rows, the packing stages, the root and the Ligero
  // opening, on TSP.
  bool prove_rest(ZkProof<F, Hash> &zkp, BasicTranscript<Hash> &tsp,
                  const ExtraRows<F> &extra, ProofRows<F> &pr) {
    check(lp_ != nullptr, "must run commit before prove");
    TreeRows<F> &rows = pr.rows;
    const TreeLayout<F> &l = *plan_.layout;
    rows.add_extra(extra);
    zkp.packed_m.clear();
    auto pack = std::make_unique<profiling::Scope>(F::kCharacteristicTwo ? "bin.pack.stages" : "odd.pack.stages");
    for (int x : plan_.tree->inner()) {
      std::vector<Elt> m;
      if (rows.stage(x, tsp, &vals_, m))
        zkp.packed_m.insert(zkp.packed_m.end(), m.begin(), m.end());
    }
    pack.reset();
    if (plan_.tree->nodes[0].children.empty()) {
      std::vector<LigeroLinearConstraint<F>> a;
      std::vector<Elt> b;
      size_t base = 0;
      rows.flat(a, b, base);
      // L and committed indices agree without a prefix or words.
      for (auto &t : a) t.w = l.committed(t.w);
      typename LigeroProver<F, RSF, Hash>::Accumulator acc =
          [&](Elt *A, const Elt *alphal) {
            if (!extra.accumulate) return;
            std::vector<Elt> tmp(l.L, f_.zero());
            extra.accumulate(tmp.data(), alphal + base);
            for (size_t i = 0; i < l.L; ++i)
              if (tmp[i] != f_.zero()) f_.add(A[l.committed(i)], tmp[i]);
          };
      lp_->prove(zkp.com_proof, tsp, b.size(), a.size(), a.data(),
                 plan_.lqc.data(), rsf_, f_, &acc);
      if (scratch != nullptr && !scratch->keep()) release(scratch->region);
      return true;
    }
    pack = std::make_unique<profiling::Scope>(F::kCharacteristicTwo ? "bin.pack.root" : "odd.pack.root");
    auto r = rows.root(tsp);
    auto measure =
        std::make_unique<profiling::Scope>(GH_TREE_KEY(F, "root.measure"));
    rows.root_measure(r, witness_, zkp.extension_m);
    measure.reset();
    pack.reset();
    tsp.write(zkp.extension_m.data(), 1, zkp.extension_m.size(), f_);
    typename LigeroProver<F, RSF, Hash>::Accumulator acc =
        [&](Elt *out, const Elt *alpha) { rows.root_accumulate(r, out, alpha); };
    lp_->prove(zkp.com_proof, tsp, zkp.extension_m.size() + 1, 0, nullptr,
               plan_.lqc.data(), rsf_, f_, &acc);
    if (scratch != nullptr && scratch->keep())
      scratch->combination = std::move(r.coeff);
    if (scratch != nullptr && !scratch->keep()) release(scratch->region);
    return true;
  }

  // The prover's working buffers (prover_scratch.h), when set: the Ligero
  // inner-product vector's.
  DomainScratch<F> *scratch = nullptr;

 private:
  // zk_prover.h's fill_pad, writing the pads at L position AT.
  void fill_pad(RandomEngine &rng, size_t at) {
    for (size_t i = 0; i < c_.nl; ++i) {
      for (size_t j = 0; j < c_.logc; ++j)
        for (size_t k = 0; k < 4; ++k) {
          if (k != 1) {
            Elt r = rng.elt(f_);
            pad_.l[i].cp[j].t_[k] = r;
            vals_[at++] = r;
          } else {
            pad_.l[i].cp[j].t_[k] = f_.zero();
          }
        }
      for (size_t j = 0; j < c_.l[i].logw; ++j)
        for (size_t h = 0; h < 2; ++h)
          for (size_t k = 0; k < 3; ++k) {
            if (k != 1) {
              Elt r = rng.elt(f_);
              pad_.l[i].hp[h][j].t_[k] = r;
              vals_[at++] = r;
            } else {
              pad_.l[i].hp[h][j].t_[k] = f_.zero();
            }
          }
      for (size_t k = 0; k < 2; ++k) {
        Elt r = rng.elt(f_);
        pad_.l[i].wc[k] = r;
        vals_[at++] = r;
      }
      vals_[at++] = f_.mulf(pad_.l[i].wc[0], pad_.l[i].wc[1]);
    }
  }

  const TreePlan<F, Hash> &plan_;
  const Circuit<F> &c_;
  const F &f_;
  const RSF &rsf_;
  Proof<F> pad_;
  std::vector<Elt> vals_, witness_;
  std::unique_ptr<LigeroProver<F, RSF, Hash>> lp_;
};

template <class F, class RSF, class Hash>
class TreeVerifier {
  using Elt = typename F::Elt;

 public:
  TreeVerifier(const TreePlan<F, Hash> &plan, const RSF &rsf, const F &f)
      : plan_(plan), rsf_(rsf), f_(f) {}

  void recv_commitment(const ZkProof<F, Hash> &zk,
                       BasicTranscript<Hash> &t) const {
    plan_.layout->bind(t);
    LigeroVerifier<F, RSF, Hash>::receive_commitment(zk.com, t);
  }

  // List-radius Ligero: the low-degree round (zk_verifier.h's recv_ldt).
  void recv_ldt(const ZkProof<F, Hash> &zk, BasicTranscript<Hash> &t) {
    LigeroVerifier<F, RSF, Hash>::receive_ldt(*plan_.param, zk.com_proof, t,
                                              u_ldt_, f_);
    have_ldt_ = true;
  }

  bool verify(const ZkProof<F, Hash> &zk, const Dense<F> &pub,
              BasicTranscript<Hash> &tv, const ExtraRows<F> &extra) const {
    auto rows = new_rows();
    verify_gkr(zk, pub, tv, *rows);
    return verify_rest(zk, tv, extra, *rows);
  }
  std::unique_ptr<ProofRows<F>> new_rows() const {
    auto rows = std::make_unique<ProofRows<F>>(f_, *plan_.layout, plan_.c->nl);
    rows->rows.routed = &plan_.routed;
    return rows;
  }
  // GKR's rows on TV into ROWS; nothing without GKR.
  void verify_gkr(const ZkProof<F, Hash> &zk, const Dense<F> &pub,
                  BasicTranscript<Hash> &tv, ProofRows<F> &pr) const {
    if (!plan_.gkr) return;
    const Circuit<F> &c = *plan_.c;
    Challenge<F> &ch = pr.ch;
    TreeRows<F> &rows = pr.rows;
    profiling::Scope sc(F::kCharacteristicTwo ? "bin.v.gkr" : "odd.v.gkr");
    ZkCommon<F>::initialize_sumcheck_fiat_shamir(tv, c, f_);
    gkr_rows(plan_, pub, zk.proof,
             static_cast<const ProofAux<F> *>(nullptr), tv, ch, rows, f_);
  }
  // The domain's own rows, the packing stages, the root and the Ligero
  // check, on TV.
  bool verify_rest(const ZkProof<F, Hash> &zk, BasicTranscript<Hash> &tv,
                   const ExtraRows<F> &extra, ProofRows<F> &pr) const {
    TreeRows<F> &rows = pr.rows;
    const TreeLayout<F> &l = *plan_.layout;
    if (zk.packed_m.size() != plan_.packed_m() ||
        zk.extension_m.size() != plan_.root_m())
      return false;
    rows.add_extra(extra);
    size_t at = 0;
    auto pack = std::make_unique<profiling::Scope>(F::kCharacteristicTwo ? "bin.v.pack.stages" : "odd.v.pack.stages");
    for (int x : plan_.tree->inner()) {
      const size_t d = l.stages[size_t(x)].d;
      std::vector<Elt> m(zk.packed_m.begin() + long(at),
                         zk.packed_m.begin() + long(at + d));
      if (rows.stage(x, tv, nullptr, m)) at += d;
    }
    pack.reset();
    if (at != zk.packed_m.size()) return false;
    const char *why = "";
    if (plan_.tree->nodes[0].children.empty()) {
      std::vector<LigeroLinearConstraint<F>> a;
      std::vector<Elt> b;
      size_t base = 0;
      rows.flat(a, b, base);
      for (auto &t : a) t.w = l.committed(t.w);
      typename LigeroVerifier<F, RSF, Hash>::Accumulator acc =
          [&](Elt *A, const Elt *alphal) {
            if (!extra.accumulate) return;
            std::vector<Elt> tmp(l.L, f_.zero());
            extra.accumulate(tmp.data(), alphal + base);
            for (size_t i = 0; i < l.L; ++i)
              if (tmp[i] != f_.zero()) f_.add(A[l.committed(i)], tmp[i]);
          };
      const bool ok = LigeroVerifier<F, RSF, Hash>::verify(
          &why, *plan_.param, zk.com, zk.com_proof, tv, b.size(), a.size(),
          a.data(), b.data(), plan_.lqc.data(), rsf_, f_, &acc, 0, ldt());
      return ok;
    }
    pack = std::make_unique<profiling::Scope>(F::kCharacteristicTwo ? "bin.v.pack.root" : "odd.v.pack.root");
    // The verifier measures nothing: the root children's coefficients come
    // without their forms (root_accumulate).
    const auto r = rows.root(tv, false);
    tv.write(zk.extension_m.data(), 1, zk.extension_m.size(), f_);
    const auto rhs = rows.root_rhs(r, zk.extension_m);
    pack.reset();
    typename LigeroVerifier<F, RSF, Hash>::Accumulator acc =
        [&](Elt *out, const Elt *alpha) { rows.root_accumulate(r, out, alpha); };
    const bool ok = LigeroVerifier<F, RSF, Hash>::verify(
        &why, *plan_.param, zk.com, zk.com_proof, tv, rhs.size(), 0, nullptr,
        rhs.data(), plan_.lqc.data(), rsf_, f_, &acc, 0, ldt());
    return ok;
  }

 private:
  const std::vector<Elt> *ldt() const { return have_ldt_ ? &u_ldt_ : nullptr; }
  const TreePlan<F, Hash> &plan_;
  const RSF &rsf_;
  const F &f_;
  std::vector<Elt> u_ldt_;
  bool have_ldt_ = false;
};

}  // namespace proofs::gordiehowe::compiler

#endif  // PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_COMPILER_TREE_ZK_H_
