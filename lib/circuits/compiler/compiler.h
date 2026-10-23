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
// Modified 2026 by Chad Sharp and Paul Grubbs: packed-bit support (enable_packed_bits, deferred Boolean assertions), Hash-templated mkcircuit, circuit shape and size estimates

#ifndef PRIVACY_PROOFS_ZK_LIB_CIRCUITS_COMPILER_COMPILER_H_
#define PRIVACY_PROOFS_ZK_LIB_CIRCUITS_COMPILER_COMPILER_H_

#include <stddef.h>
#include <stdint.h>

#include <algorithm>
#include <memory>
#include <utility>
#include <vector>

#include "algebra/hash.h"
#include "circuits/compiler/node.h"
#include "circuits/compiler/pdqhash.h"
#include "circuits/compiler/schedule.h"
#include "sumcheck/circuit.h"
#include "sumcheck/circuit_id.h"
#include "sumcheck/quad.h"
#include "util/panic.h"

namespace proofs {
/*
QuadCircuit contains methods that facilitate defining circuits used to
express predicates that are to be proven or verified. This class allows one
to use basic arithmetic circuit operations (add, mul, input, assert0, ...)
to define the circuit on a set of abstract wire labels.

The "mkcircuit" compiler method than optimizes the circuit by applying all of
the basic tricks of constant propagation, common sub-expression elimination,
squashing layers into as few as possible, and grouping terms into quads.

Quads are a new form of gate (in contrast to the add and mul gates in most
sumcheck proof systems). Quads represent a "sum of quadratic terms" where
each term is w_l * w_r * v for two wire labels and a constant v.
*/
template <class Field>
class QuadCircuit {
 public:
  using Elt = typename Field::Elt;
  using nodeinfo = NodeInfoF<Field>;
  using node = NodeF<Field>;
  using size_t_for_storage = term::size_t_for_storage;
  using quad_corner_t = typename Quad<Field>::quad_corner_t;

  const Field& f_;

 public:
  // Variables for informational purposes:
  size_t ninput_;
  size_t npub_input_;         // number of public inputs, index of 1st private
  size_t subfield_boundary_;  // least wire not known to be in the subfield
  size_t noutput_;

  // set by the algebraic simplifiers in this file
  size_t depth_;
  size_t nwires_cse_eliminated_;
  size_t nwires_not_needed_;

  // set by the scheduler
  size_t nwires_;
  size_t nquad_terms_;
  size_t nwires_overhead_;
  size_t npacked_assertions_ = 0;  // deferred bits left unpacked

  explicit QuadCircuit(const Field& f)
      : f_(f),
        ninput_(0),
        npub_input_(0),
        subfield_boundary_(0),
        noutput_(0),
        depth_(0),
        nwires_cse_eliminated_(0),
        nwires_not_needed_(0),
        nwires_(-1),  // undefined until set in mkcircuit()
        nquad_terms_(-1),
        nwires_overhead_(-1) {
    // make sure that Elt(0) is represented as index 0 in the constant
    // table.
    size_t ki0 = kstore(f.zero());
    proofs::check(ki0 == 0, "ki0 == 0");
    size_t ki1 = kstore(f.one());
    proofs::check(ki1 == 1, "ki1 == 1");

    // make sure node 0 exists, carrying input[0] = F.one()
    input_wire();
  }

  // Produce a linear term 1 * op0 that the compiler will not
  // attempt to optimize to op0.  The reason for this function
  // is to implement linear terms such as a*x in the quadratic form
  // a*x+b*x*y.  Left to its own devices, the compiler peeks into x,
  // and if x=k*z*w, it produces a term (a*k)*z*w in the previous
  // layer, possibly destroying common subexpressions.  linear(op)
  // introduces an explicit multiplication by wire 0, which the
  // compiler does not attempt to optimize away.
  size_t linear(size_t op0) { return mul(0, op0); }
  size_t linear(const Elt& k, size_t op0) { return mul(k, 0, op0); }

  size_t mul(const Elt& k, size_t op) {
    if (k == f_.zero()) {
      return konst(k);
    } else if (k == f_.one() || nodes_[op].zero()) {
      return op;
    } else {
      return push_node(scale(k, op));
    }
  }

  size_t mul(size_t op0, size_t op1) { return mul(f_.one(), op0, op1); }

  size_t mul(const Elt& k, size_t op0, size_t op1) {
    const auto& n0 = nodes_[op0];
    const auto& n1 = nodes_[op1];

    if (n0.zero()) {
      return op0;
    } else if (n0.constant()) {
      // k * (k1 * op1) -> (k * k1) * op1
      return mul(f_.mulf(k, kload(n0.terms[0].ki)), op1);
    } else if (n0.linearp()) {
      // k * ((k1 * op0) * op1) -> (k * k1) * op0 * op1
      return mul(f_.mulf(k, kload(n0.terms[0].ki)), n0.terms[0].op1, op1);
    } else if (n1.zero() || n1.constant() || n1.linearp()) {
      return mul(k, op1, op0);
    } else {
      // general term k * op0 * op1
      return push_node(node(kstore(k), op0, op1));
    }
  }

  size_t add(size_t op0, size_t op1) {
    const auto& n0 = nodes_[op0];
    const auto& n1 = nodes_[op1];

    if (n0.zero()) {
      return op1;
    } else if (n1.zero()) {
      return op0;
    } else {
      // If the two addends are of different depth, do not merge
      // them, which is accomplished by multiplying the shallower
      // node by 1 and treating it as a single term of the final
      // sum.
      //
      // Like many other "optimizations", this is a heuristic
      // that may or may not work, but it seems to be uniformly
      // beneficial or at least not harmful for all our circuits
      // as of 2023-11-15.
      if (n0.info.depth < n1.info.depth) {
        op0 = linear(op0);
      } else if (n1.info.depth < n0.info.depth) {
        op1 = linear(op1);
      }
      return push_node(merge(op0, op1));
    }
  }
  size_t sub(size_t op0, size_t op1) { return add(op0, mul(f_.mone(), op1)); }

  size_t konst(const Elt& k) { return push_node(node(kstore(k), 0, 0)); }

  // Generate a special node that asserts that op == 0.
  // The node has the form 0*(1*op), which does not normally
  // appear in circuits.
  size_t assert0(size_t op) {
    const node* n = &nodes_[op];
    if (n->zero()) {
      // Identically zero, so nothing to generate.
      // More importantly, we cannot multiply OP by 1,
      // since OP doesn't really exist.
      return op;
    } else if (n->linearp()) {
      // n = k * (1 * op1).
      //
      // Reduce to assert0(op1), but handle the screw case k==0,
      // which shouldn't happen but just in case...
      if (n->terms[0].ki == 0) {
        return op;
      } else {
        return assert0(n->terms[0].op1);
      }
    } else {
      typename term::assert0_type_hack hack;
      std::vector<term> terms;
      terms.push_back(term(op, hack));
      node nn(std::move(terms));
      nn.info.is_assert0 = true;
      return push_node(std::move(nn));
    }
  }

  // Wrappers to avoid creating unnecessary wires.  The
  // compiler will discard them anyway, but they still take
  // time and space.
  size_t axpy(size_t y, const Elt& a, size_t x) {
    if (a == f_.zero()) {
      return y;
    }
    return add(y, linear(a, x));
  }
  size_t apy(size_t y, const Elt& a) {
    if (a == f_.zero()) {
      return y;
    }
    return add(y, konst(a));
  }

  // Create an input wire.
  //
  // Most code should never call this function directly.  Call
  // Logic::eltw_input() instead.
  size_t input_wire() { return push_node(node(quad_corner_t(ninput_++))); }

  // This function demarcates the end of the public inputs and beginning of
  // private inputs. It can only be called once.
  void private_input() {
    proofs::check(
        npub_input_ == 0,
        "private_input can only be called once after setting public inputs");
    npub_input_ = ninput_;
  }

  // This function demarcates the end of the private inputs in the
  // subfield and beginning of the full-field private inputs. It can
  // only be called once.
  void begin_full_field() {
    proofs::check(subfield_boundary_ == 0,
                  "begin_full_field() can only be called once");
    subfield_boundary_ = ninput_;
  }

  size_t ninput() const { return ninput_; }

  // Packed bits (zk/zk_packed.h).  After enable_packed_bits(), private
  // Boolean inputs declared before begin_full_field() are not asserted by the
  // circuit: the compiler packs the aligned interior of each run of them into
  // subfield elements, which are bits by construction, and emits the
  // assertion x - x*x = 0 at mkcircuit() for every one it leaves unpacked.
  // Only characteristic-two fields have the trace identity packing relies on.
  void enable_packed_bits() {
    proofs::check(Field::kCharacteristicTwo,
                  "packed bits need a characteristic-two field");
    proofs::check(npub_input_ != 0 && subfield_boundary_ == 0,
                  "enable_packed_bits() between private_input() and "
                  "begin_full_field()");
    packed_bits_enabled_ = true;
  }

  // True while private Boolean inputs are packing candidates: after
  // enable_packed_bits() and before begin_full_field().
  bool packs_bits() const {
    return packed_bits_enabled_ && subfield_boundary_ == 0;
  }

  // Called for each Boolean input.  Returns true if the compiler takes over
  // the input's Boolean assertion.
  bool defer_bit_assertion(size_t op) {
    if (!packed_bits_enabled_ || subfield_boundary_ != 0) {
      return false;
    }
    const node& n = nodes_[op];
    proofs::check(n.info.is_input, "defer_bit_assertion on a non-input");
    const size_t i = static_cast<size_t>(n.info.desired_wire_id_for_input);
    proofs::check(i >= npub_input_, "packed bits must be private inputs");
    packed_marks_.push_back({i, op});
    return true;
  }

  void output_wire(size_t n, size_t wire_id) {
    output_internal(n, quad_corner_t(wire_id));
  }

  // Hash is the protocol hash policy of the circuit id (util/crypto.h).
  template <class Hash = UpstreamHash>
  std::unique_ptr<Circuit<Field>> mkcircuit(size_t nc) {
    std::unique_ptr<Circuit<Field>> c = mkcircuit_without_id(nc);
    circuit_id<Field, Hash>(c->id, *c, f_);
    return c;
  }

  // mkcircuit(NC) without the circuit id, for a caller that adds to the
  // circuit what its id covers (input products) and computes the id once.
  std::unique_ptr<Circuit<Field>> mkcircuit_without_id(size_t nc) {
    return schedule(nc);
  }

  // The circuit's quad terms and layers, as mkcircuit(NC) builds it,
  // without its id (a cost estimate's circuit).
  std::pair<size_t, size_t> mkcircuit_size(size_t nc) {
    const std::unique_ptr<Circuit<Field>> c = schedule(nc);
    return {c->nterms(), c->nl};
  }

  // The circuit mkcircuit(NC) would build, reduced to its shape: the layer
  // count, each layer's input wires nw and logw, and the inputs, without
  // the layers' quads or the id. Each layer's wires are
  // counted as the scheduler lays them out (Scheduler::order_by_layer):
  // every needed nonzero node at its depth, and one copy wire at each depth
  // strictly between it and the deepest layer that reads it. Like
  // mkcircuit, it finalizes the circuit: call it once, instead of
  // mkcircuit.
  std::unique_ptr<Circuit<Field>> mkcircuit_shape(size_t nc) {
    std::vector<std::pair<size_t, size_t>> packed = pack_deferred_bits();
    const size_t depth_ub = compute_depth_ub();
    fixup_last_layer_assertions(depth_ub);
    compute_needed(depth_ub);

    std::vector<size_t> width(depth_ub, 0);
    for (const auto& n : nodes_) {
      const nodeinfo& nfo = n.info;
      if (!nfo.is_needed || n.zero()) continue;
      ++width.at(nfo.depth);
      for (size_t d = nfo.depth + 1; d < nfo.max_needed_depth; ++d)
        ++width.at(d);
    }
    auto c = std::make_unique<Circuit<Field>>();
    c->nl = depth_ub - 1;
    c->nc = nc;
    c->logc = lg(nc);
    c->nv = width.at(depth_ub - 1);
    c->logv = lg(c->nv);
    // As Scheduler::fill_layers: from the output layer down, layer d reads
    // the wires at depth d - 1.
    for (size_t d = depth_ub; d-- > 1;) {
      const corner_t nw = corner_t(width.at(d - 1));
      c->l.push_back(Layer<Field>{.nw = nw, .logw = lg(nw), .quad = nullptr});
    }
    c->ninputs = ninput();
    c->npub_in = npub_input_;
    c->subfield_boundary = subfield_boundary_;
    c->packed_bits = std::move(packed);
    return c;
  }

 private:
  // The circuit's layers (mkcircuit without the id and the Boolean plan).
  std::unique_ptr<Circuit<Field>> schedule(size_t nc) {
    std::vector<std::pair<size_t, size_t>> packed = pack_deferred_bits();
    size_t depth_ub = compute_depth_ub();
    fixup_last_layer_assertions(depth_ub);
    compute_needed(depth_ub);

    Scheduler<Field> sched(nodes_, f_);
    std::unique_ptr<Circuit<Field>> c =
        sched.mkcircuit(constants_, depth_ub, nc);

    // re-export the scheduler telemetry
    nwires_ = sched.nwires_;
    nquad_terms_ = sched.nquad_terms_;
    nwires_overhead_ = sched.nwires_overhead_;

    c->ninputs = ninput();
    c->npub_in = npub_input_;
    c->subfield_boundary = subfield_boundary_;
    c->packed_bits = std::move(packed);
    return c;
  }

  // Chooses the packed runs among the deferred inputs and emits the Boolean
  // assertion for every deferred input left out of them.  Returns the runs.
  std::vector<std::pair<size_t, size_t>> pack_deferred_bits() {
    std::vector<std::pair<size_t, size_t>> runs;
    if (packed_marks_.empty()) {
      return runs;
    }
    proofs::check(subfield_boundary_ != 0,
                  "packed bits need begin_full_field()");
    size_t kPack = 1;
    if constexpr (Field::kCharacteristicTwo) {
      kPack = Field::kSubFieldBits;
    }
    std::sort(packed_marks_.begin(), packed_marks_.end());

    // Maximal runs of consecutive input indices; keep each aligned interior.
    for (size_t s = 0; s < packed_marks_.size();) {
      size_t e = s + 1;
      while (e < packed_marks_.size() &&
             packed_marks_[e].first == packed_marks_[e - 1].first + 1) {
        ++e;
      }
      const size_t a = packed_marks_[s].first;
      const size_t b = packed_marks_[e - 1].first + 1;
      const size_t a16 = (a + kPack - 1) / kPack * kPack;
      const size_t b16 = b / kPack * kPack;
      if (a16 < b16) {
        runs.push_back({a16, b16});
      }
      s = e;
    }

    auto in_run = [&](size_t i) {
      for (const auto& r : runs) {
        if (i >= r.first && i < r.second) return true;
      }
      return false;
    };
    for (const auto& m : packed_marks_) {
      if (!in_run(m.first)) {
        assert0(sub(m.second, mul(m.second, m.second)));
        ++npacked_assertions_;
      }
    }
    return runs;
  }

  void output_internal(size_t n, quad_corner_t wire_id) {
    node* nn = &nodes_[n];
    proofs::check(!nn->info.is_output, "outputting the same node twice");
    nn->info.is_output = true;
    nn->info.desired_wire_id_for_output = wire_id;
    noutput_++;
  }

  size_t push_node(node n) {
    // common-subexpression elimination: if we have already seen a
    // node equal to n, return that node.
    uint64_t d = n.hash();

    auto pred = [&](PdqHash::value_t op) { return n == nodes_[op]; };
    if (size_t op = cse_.find(d, pred); op != PdqHash::kNil) {
      // do not linear terms as eliminated by the CSE, since they are
      // likely placeholder nodes absorbed by the next layer.
      if (!n.linearp()) {
        ++nwires_cse_eliminated_;
      }
      return op;
    }

    // compute the node depth, which has been so far uninitialized
    n.info.depth = 0;
    for (const auto& t : n.terms) {
      n.info.depth = std::max<size_t>(
          n.info.depth, 1 + std::max<size_t>(nodes_[t.op0].info.depth,
                                             nodes_[t.op1].info.depth));
    }

    size_t nid = nodes_.size();
    nodes_.push_back(std::move(n));

    // record NID into the common-subexpression elimination table
    cse_.insert(d, nid);

    return nid;
  }

  node materialize_input(size_t op) {
    node* nn = &nodes_[op];
    if (nn->info.is_input) {
      return node(/*kstore(f.one())=*/1, 0, op);
    } else {
      return nn->clone();
    }
  }

  node scale(const Elt& k, size_t op) {
    node n = materialize_input(op);
    for (auto& t : n.terms) {
      t.ki = kstore(f_.mulf(kload(t.ki), k));
    }
    return n;
  }

  void push_back_unless_zero(std::vector<term>& terms, const term& t) const {
    if (t.ki != 0) {
      terms.push_back(t);
    }
  }

  node merge(size_t op0, size_t op1) {
    const node n0 = materialize_input(op0);
    const node n1 = materialize_input(op1);
    const std::vector<term>& t0 = n0.terms;
    const std::vector<term>& t1 = n1.terms;
    std::vector<term> terms;
    size_t i0 = 0, i1 = 0;
    while (i0 < t0.size() && i1 < t1.size()) {
      if (t0[i0].eqndx(t1[i1])) {
        term t = t0[i0];
        t.ki = kstore(f_.addf(kload(t.ki), kload(t1[i1].ki)));
        push_back_unless_zero(terms, t);
        i0++;
        i1++;
      } else if (t0[i0].ltndx(t1[i1])) {
        push_back_unless_zero(terms, t0[i0++]);
      } else {
        push_back_unless_zero(terms, t1[i1++]);
      }
    }

    while (i0 < t0.size()) {
      push_back_unless_zero(terms, t0[i0++]);
    }

    while (i1 < t1.size()) {
      push_back_unless_zero(terms, t1[i1++]);
    }

    return node(std::move(terms));
  }

  // constants_[n] stores the n-th constant, once.
  // Modulo collisions, constants_[constttab_[hash(k)]] == k
  // for k \in Elt.
  std::vector<Elt> constants_;
  PdqHash consttab_;

  std::vector<node> nodes_;
  PdqHash cse_;

  bool packed_bits_enabled_ = false;
  std::vector<std::pair<size_t, size_t>> packed_marks_;  // (input, node)

  size_t kstore(const Elt& k) {
    uint64_t d = elt_hash(k, f_);
    auto pred = [&](PdqHash::value_t ki) { return k == constants_[ki]; };
    size_t ki = consttab_.find(d, pred);

    if (ki == PdqHash::kNil) {
      ki = constants_.size();
      constants_.push_back(k);
      consttab_.insert(d, ki);
    }
    return ki;
  }
  Elt& kload(size_t ki) { return constants_[ki]; }

  void mark_needed(size_t op, size_t depth_at_which_needed) {
    nodeinfo* nfo = &nodes_[op].info;
    nfo->is_needed = true;
    nfo->max_needed_depth =
        std::max<size_t>(depth_at_which_needed, nfo->max_needed_depth);

    // If DEPTH_AT_WHICH_NEEDED > DEPTH + 1, we need a constant 1 at
    // depth DEPTH_AT_WHICH_NEEDED-1 (and implicily any lower depths) in
    // order to copy the node across levels.
    if (depth_at_which_needed > nfo->depth + 1) {
      nodeinfo* nfo0 = &nodes_[0].info;
      nfo0->is_needed = true;
      nfo0->max_needed_depth =
          std::max<size_t>(depth_at_which_needed - 1, nfo0->max_needed_depth);
    }
  }

  size_t compute_depth_ub() {
    size_t r = 0;
    for (auto& n : nodes_) {
      if (n.info.is_output) {
        r = std::max<size_t>(r, 1 + n.info.depth);
      } else if (n.info.is_assert0) {
        // Assertions of the form 0*(1*OP) contribute n.info.depth and
        // not 1 + n.info.depth.  If the assertion is in the last
        // layer, it will be transformed in an output of OP at
        // n.info.depth.  If the assertion is not in the last layer,
        // then it doesn't matter whether we use DEPTH or 1 + DEPTH.
        if (n.linearp()) {
          r = std::max<size_t>(r, n.info.depth);
        } else {
          r = std::max<size_t>(r, 1 + n.info.depth);
        }
      }
    }
    depth_ = r;
    return r;
  }

  void fixup_last_layer_assertions(size_t depth_ub) {
    // convert assertions in the last layer into outputs
    for (auto& n : nodes_) {
      if (!n.info.is_output && n.info.is_assert0 && n.info.depth == depth_ub &&
          n.linearp()) {
        n.info.is_assert0 = false;
        output_internal(n.terms[0].op1, nodeinfo::kWireIdUndefined);
      }
    }
  }

  void compute_needed(size_t depth_ub) {
    nwires_not_needed_ = 0;
    for (size_t i = nodes_.size(); i-- > 0;) {
      nodeinfo* nfo = &nodes_[i].info;

      // mark all inputs as needed, to prevent ambiguity
      // in the layout of the W[] vector.
      if (nfo->is_input) {
        mark_needed(i, 1);
      }
      // outputs are needed at depth_ub_
      if (nfo->is_output) {
        mark_needed(i, depth_ub);
      }
      // assertions are needed in the next layer
      if (nfo->is_assert0) {
        mark_needed(i, nfo->depth + 1);
      }

      if (nfo->is_needed) {
        for (const auto& t : nodes_[i].terms) {
          mark_needed(t.op0, nfo->depth);
          mark_needed(t.op1, nfo->depth);
        }
      } else {
        ++nwires_not_needed_;
      }
    }
  }
};

}  // namespace proofs

#endif  // PRIVACY_PROOFS_ZK_LIB_CIRCUITS_COMPILER_COMPILER_H_
