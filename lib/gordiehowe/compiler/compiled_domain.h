// Copyright 2026 Chad Sharp and Paul Grubbs
// SPDX-License-Identifier: Apache-2.0

// GordieHowe: a domain's compiler, the domain prover and the domain
// verifier.
//
// A domain compiles to one Circuit<Field> proved by the existing ZkProver:
// the circuit kind is its GKR kernel, the affine kind enters as
// ZkCommon::ExtraConstraints computed with transpose_apply, and quadratic
// triples are Circuit::input_products.
//
// Storage (circuit inputs, in order):
//   0                         the constant one
//   public slots              every public value or masked message t that a
//                             circuit reads, ordered by node id
//   subfield cells            phase-0 Bit/Subfield variables and subfield pads
//                             (packing.h: unpacked cells, bit views, packed
//                             bits)
//   ambient cells             phase-0 Field variables and field pads
//   batch pads                each batched relation's reduction pads
// A late variable has no cell: its pad P is a cell and circuits read
// t - P with t a public slot. When the field supports relative packing the
// domain packs its subfield cells (packing.h), and its subfield step checks
// the prefix rows.
//
// A domain's reductions run in a fixed order before its opening: each
// batched relation's masked skip, in declaration order, then masked GKR.
//
// A domain with no circuit constraint (its predicates affine rows,
// quadratic triples or field batches, and no Boolean check, late bit or
// checked derived value in the circuit) runs no GKR: its Circuit has no
// layers and only describes the inputs (ninputs, npub_in, the packed run,
// input products), so it has no GKR pads, no sumcheck, no GKR transcript
// section and no input claim. Its affine and batch rows reach the opening
// through the packing tree, as in a domain with GKR.

#ifndef PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_COMPILER_COMPILED_DOMAIN_H_
#define PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_COMPILER_COMPILED_DOMAIN_H_

#include <cmath>
#include <cstddef>
#include <cstdint>
#include <chrono>
#include <cstdio>
#include <cstdlib>
#include <functional>
#include <map>
#include <memory>
#include <optional>
#include <set>
#include <sstream>
#include <string>
#include <utility>
#include <vector>

#include "arrays/dense.h"
#include "circuits/compiler/compiler.h"
#include "circuits/logic/compiler_backend.h"
#include "circuits/logic/logic.h"
#include "gordiehowe/compiler/batch.h"
#include "gordiehowe/compiler/batch_form.h"
#include "gordiehowe/compiler/compile_cache.h"
#include "gordiehowe/compiler/compile_times.h"
#include "gordiehowe/compiler/packing.h"
#include "gordiehowe/compiler/placement.h"
#include "gordiehowe/compiler/prover_scratch.h"
#include "gordiehowe/compiler/tree.h"
#include "gordiehowe/compiler/tree_zk.h"
#include "gordiehowe/compiler/op_counts.h"
#include "gordiehowe/compiler/view_batch.h"
#include "gordiehowe/compiler/view_map.h"
#include "gordiehowe/core.h"
#include "gordiehowe/threads.h"
#include "gordiehowe/transcript_fork.h"
#include "gordiehowe/ct.h"
#include "gordiehowe/domain.h"
#include "gordiehowe/expr.h"
#include "gordiehowe/linear.h"
#include "gordiehowe/ops/operators.h"
#include "sumcheck/circuit.h"
#include "util/diagnostics.h"
#include "util/prover_profile.h"
#include "sumcheck/circuit_id.h"
#include "util/optimization_options.h"
#include "zk/zk_common.h"
#include "zk/zk_proof.h"
#include "zk/zk_prover.h"
#include "zk/zk_verifier.h"

namespace proofs::gordiehowe::compiler {
template <class F, class RSF, class S>
class CompiledDomain final : public CompiledDomainBase<S> {
  using Hash = typename S::Hash;
  using Elt = typename F::Elt;
  using D = DomainImpl<F, RSF, S>;
  using CLogic = typename D::CLogic;
  using Wires = std::vector<size_t>;
  using Extra = typename ZkCommon<F>::ExtraConstraints;

  // A public slot: the value of a public node, or the message of a late one.
  struct Slot {
    size_t id;
    bool msg;
    size_t at;  // first circuit input
    bool operator<(const Slot &o) const {
      return id != o.id ? id < o.id : msg < o.msg;
    }
  };
  // A flattened affine term: scale * chain(value) where the value is a
  // committed cell (at = first witness index) or a public vector.
  // A predicate's constants are a term of their own (kConst, KONST).
  struct Flat {
    Elt scale;
    std::vector<std::shared_ptr<const OpSpec<F>>> chain;
    size_t id;
    enum { kCell, kPublic, kMessage, kConst } src;
    size_t at = 0;
    size_t in_n = 0;
    std::vector<Elt> konst = {};
  };
  // Where each predicate landed, and why (the report): the candidates the
  // placement rule weighed (COSTS, empty when it had no choice), its
  // batched form and the batch group it joined (kBatch).
  struct PredPlan {
    Placement where = Placement::kCircuit;
    std::string why;
    std::string costs;
    std::optional<AffineForm<F>> aff;
    TripleForm tri;
    std::optional<BatchForm<F>> form;
    // The form's operand class: bit-sliced, or the node degree of its
    // committed leaves.
    BatchEval eval = BatchEval::kField;
    size_t word_degree = 0;
    // The form's operands, the count the placement rule's batch cost reads.
    size_t operands = 0;
    long group = -1;
    // The pin that applies (Predicate::pin, or the measurement hook's).
    Placement pin = Placement::kAuto;
  };
  // Predicates of one batched form placed together: one batch when placed
  // in a batch (kernel built after the cells), or, merged for costing, the
  // circuit or triples.
  struct Group {
    std::vector<size_t> preds;
    BatchEval eval = BatchEval::kField;
    size_t word_degree = 0;
    size_t n = 0;  // instances (bit-sliced: padded to whole lanes)
    unsigned degree = 0;  // Q's
    unsigned width = 0;
    std::string name;
    PlacementChoice choice;
    bool pinned = false;
    // Its counted work in one proof (op_counts.h), as placed.
    OpCounts work;
  };
  struct Rows {
    std::string name;
    size_t row0, n;
    std::vector<Flat> terms;
  };

 public:
  // With CACHED, a compile cache record of the domain (compile_cache.h):
  // its decisions, read in place of the placement rule, the chain choice
  // and the tableau search, and its circuit, loaded in place of emitting
  // and scheduling it when its inputs are the ones the domain allocates.
  // The tableau of the provisional pass (DomainImpl::compile): its
  // witness row width w = k - r, its block_enc and its quadratic
  // constraints, against which the placement costs count the rows a
  // candidate adds.
  struct ProvisionalTableau {
    size_t w = 0, block_enc = 0, nq = 0, nrow = 0;
    // The groups of the bit node's region (0 without one).
    size_t bit_groups = 0;
  };
  // The provisional tableau as the placement costs read it. The bit node's
  // groups come from the inputs-only pass (InputsOnly), which emits no
  // circuit. The rest comes from FULL, the provisional pass that emits the
  // circuit with every group at its default: only the cost of an
  // admissible triple reads it, so it runs on the first such read, and its
  // tableau is kept.
  class Provisional {
   public:
    Provisional(size_t bit_groups, std::function<ProvisionalTableau()> full)
        : bit_groups_(bit_groups), full_(std::move(full)) {}
    // A tableau computed in full up front.
    explicit Provisional(const ProvisionalTableau &t)
        : bit_groups_(t.bit_groups), tableau_(t) {}
    size_t bit_groups() const { return bit_groups_; }
    const ProvisionalTableau &tableau() {
      if (!tableau_) tableau_ = full_();
      return *tableau_;
    }

   private:
    size_t bit_groups_;
    std::function<ProvisionalTableau()> full_;
    std::optional<ProvisionalTableau> tableau_;
  };
  // The tag of the inputs-only provisional pass.
  struct InputsOnly {};

  // PROV (read during the build only): the provisional tableau the
  // placement costs read, none without measured rates. With SOURCE, the
  // domain is built from the realized program (DomainSource).
  CompiledDomain(const D &d, const CompilePlan &plan,
                 const DomainSource *source, Provisional *prov = nullptr)
      : d_(d), plan_(plan), prov_(prov), source_(source) {
    build();
    source_ = nullptr;
    prov_ = nullptr;
  }
  // The inputs-only provisional pass, under ProvisionalPass: every group at
  // its default, the inputs allocated and the tree laid out, then
  // bit_groups(); no circuit is emitted.
  CompiledDomain(const D &d, const CompilePlan &plan, InputsOnly)
      : d_(d), plan_(plan), inputs_only_(true) {
    build();
  }
  ProvisionalTableau provisional_tableau() const {
    size_t bit_groups = 0;
    if (tplan_->layout && tplan_->layout->bits >= 0)
      bit_groups = tplan_->layout->region[size_t(tplan_->layout->bits)].groups;
    return {param_w_, block_enc_, tplan_->param->nq, param_nrow_, bit_groups};
  }
  // The inputs-only pass's groups of the bit node's region (0 without one).
  size_t bit_groups() const { return bit_groups_; }
  // The compressions N triples' rows add to hashing one column of the
  // provisional tableau (its nrow elements of F::kBytes, Hash::kBlockSize
  // bytes a compression).
  size_t triple_hash_blocks(size_t n) const {
    if (!prov_) return 0;
    constexpr size_t b = Hash::kBlockSize;
    const size_t nrow = prov_->tableau().nrow;
    const size_t before = nrow * F::kBytes;
    const size_t after = (nrow + triple_rows(n)) * F::kBytes;
    return (after + b - 1) / b - (before + b - 1) / b;
  }
  // The quadratic rows N triples add to the provisional tableau: three per
  // row of w constraints its nq do not fill (0 without one).
  size_t triple_rows(size_t n) const {
    if (!prov_ || prov_->tableau().w == 0) return 0;
    const size_t w = prov_->tableau().w, q = prov_->tableau().nq;
    return 3 * ((q + n + w - 1) / w - (q + w - 1) / w);
  }

  std::optional<ir::DomainRealization> realization() const override {
    ir::DomainRealization r;
    r.decisions = realization_bytes();
    if (gkr_) {
      r.circuit = compiler::circuit_record(d_.field(), *circ_, sched_packed_);
      if (r.circuit.empty()) return std::nullopt;
    }
    return r;
  }
  bool loaded() const override { return loaded_; }
  std::string misfit() const override { return misfit_; }

  const uint8_t *circuit_id() const override { return circ_->id; }

  std::vector<size_t> views_read() const override {
    std::vector<size_t> out;
    for (const auto &[id, at] : view_at_) out.push_back(id);
    return out;
  }
  std::vector<size_t> batch_message_bytes() const override {
    std::vector<size_t> out;
    for (const auto &b : bplan_)
      out.push_back(b.kernel->message_elts() * F::kBytes);
    return out;
  }

  // A batched relation as compiled: its kernel, the circuit input and the
  // witness coordinate of its pad 0, and the witness coordinate of every
  // table word.
  struct BatchPlan {
    std::string name;
    const BatchKernel<F, Hash> *kernel;
    size_t pad_input;
    size_t pad_coord = 0;
    std::vector<size_t> word_at;
    int table_node = 0;  // the packing-tree node of its tables
    // Its counted work (op_counts.h; zero for a declared batch).
    OpCounts work = {};
  };
  using BatchRows = typename BatchKernel<F, Hash>::Rows;
  const std::vector<BatchPlan> &batches() const { return bplan_; }
  size_t npub() const { return circ_->npub_in; }
  // The batch's table words, from the prover's values and its circuit
  // inputs IN (the packed run's bits), into OUT, which keeps its capacity
  // (prover_scratch.h).
  void batch_words(const BatchPlan &b, const ValueStore<S> &v,
                   const std::vector<Elt> &in, std::vector<Elt> &out) const {
    const F &f = d_.field();
    // The tables' segments of OUT: each a node's values, or the run's
    // groups (SRC null), at its first word; a last entry closes OUT. Their
    // words run in one range, in chunks under a runner (util/parallel.h),
    // each chunk writing its own words; the boundaries depend on the
    // segments' sizes only.
    const size_t W = word_bits_;
    std::vector<const std::vector<Elt> *> src;
    std::vector<size_t> at0(1, 0);
    for (size_t id : btables_[size_t(&b - bplan_.data())]) {
      if (id == BatchSpace::kRun) {
        if constexpr (!F::kCharacteristicTwo) continue;
        src.push_back(nullptr);
        at0.push_back(at0.back() + (run_end_ - run_begin_ + W - 1) / W);
        continue;
      }
      src.push_back(&v.template get<F>(id));
      at0.push_back(at0.back() + src.back()->size());
    }
    const size_t n = at0.back();
    out.resize(n);
    parallel::for_chunks(n, parallel::grain_for(n, parallel::kChunks),
                         [&](size_t q0, size_t q1) {
      size_t k = size_t(std::upper_bound(at0.begin(), at0.end(), q0) -
                        at0.begin()) -
                 1;
      for (size_t q = q0; q < q1; ++k) {
        const size_t e = std::min(q1, at0[k + 1]);
        if (src[k] != nullptr) {
          std::copy(src[k]->begin() + long(q - at0[k]),
                    src[k]->begin() + long(e - at0[k]), out.begin() + long(q));
        } else if constexpr (F::kCharacteristicTwo) {
          // Each group of the run as a word: bit j the coefficient of basis
          // element j (an aliased group's bits are its word's).
          const auto &sub = SubfieldInfo<F>::get(f, W);
          for (size_t i = q; i < e; ++i) {
            const size_t at = run_begin_ + (i - at0[k]) * W;
            uint64_t u = 0;
            for (size_t j = 0; j < W; ++j)
              u |= uint64_t(ct::bit_of(f, in[at + j])) << j;
            out[i] = W == 16 && F::kSubFieldBits == 16 ? f.of_scalar(u)
                                                       : sub.word(f, u);
          }
        }
        q = e;
      }
    });
  }
  // The public values batch B's operands read, by its spaces.
  BatchPublics<F> batch_publics(const BatchPlan &b,
                                const ValueStore<S> &v) const {
    BatchPublics<F> pub;
    for (size_t id : b.kernel->public_nodes())
      pub.values.push_back(id == SIZE_MAX ? nullptr
                                          : &v.template get<F>(id));
    return pub;
  }

  void describe(std::vector<uint8_t> &out) const override {
    put_str(out, d_.name);
    put_str(out, d_.p_.field_name);
    put_u64(out, d_.p_.rate);
    if (lig_) {
      // The chosen parameters: the target (whole bits, then its half bits
      // when it has a half, then the fallback), block_enc, t and the
      // masking.
      put_str(out, "ligero.target");
      put_u64(out, d_.p_.target_half() / 2);
      if (d_.p_.target_half() % 2 != 0) {
        put_str(out, "ligero.target_half_bits");
        put_u64(out, d_.p_.target_half());
      }
      if (lig_->fallback) {
        put_str(out, "ligero.target_fallback");
        put_u64(out, lig_->goal_num);
      }
      put_u64(out, block_enc_);
      put_str(out, "ligero.list_radius");
      put_u64(out, lig_->t);
      put_u64(out, lig_->masking == LigeroMasking::kSplit ? 1 : 0);
      if (lig_->reps > 1) {
        put_str(out, "ligero.ldt_reps");
        put_u64(out, lig_->reps);
      }
    } else {
      put_u64(out, d_.p_.nreq);
      put_u64(out, block_enc_);
      if (d_.p_.list_radius) {
        put_str(out, "ligero.list_radius");
        put_u64(out, d_.p_.t);
        put_u64(out, d_.p_.masking == LigeroMasking::kSplit ? 1 : 0);
      }
    }
    // A domain without GKR says so; its id is that of the layerless
    // circuit, which describes the inputs.
    if (!gkr_) put_str(out, "no-gkr");
    out.insert(out.end(), circ_->id, circ_->id + Hash::kDigestSize);
    put_u64(out, circ_->extension_packing ? 1 : 0);
    put_u64(out, subfield_.rows());
    if (tplan_->layout->nflat > 0) {
      put_str(out, "unpacked-s0");
      put_u64(out, tplan_->layout->nflat);
    }
    if (!legacy_tree()) {
      // A tree other than GF(2) < S0 < K: its nodes and edges.
      put_str(out, "packing-tree");
      put_u64(out, tree_.d_max);
      put_u64(out, tree_.nodes.size());
      for (const auto &nd : tree_.nodes) {
        put_u64(out, nd.degree);
        put_u64(out, size_t(nd.parent + 1));
        put_u64(out, tplan_->layout->region[&nd - tree_.nodes.data()].n);
      }
    }
    if (!tplan_->layout->views.empty()) {
      // Composed bit views: per word degree D, the basis change P from the
      // tower bits to the canonical bits (row l: tower bits m with canonical
      // coordinate l), then each view's first group, word and degree.
      put_str(out, "bit-views-composed");
      put_u64(out, tplan_->layout->bases.size());
      for (const auto &[D, cb] : tplan_->layout->bases) {
        put_u64(out, D);
        for (uint64_t row : cb.P) put_u64(out, row);
      }
      put_u64(out, tplan_->layout->views.size());
      for (const auto &v : tplan_->layout->views) {
        put_u64(out, v.group);
        put_u64(out, v.target);
        put_u64(out, v.degree);
      }
    }
    put_u64(out, circ_->input_products.size());
    for (const auto &q : circ_->input_products)
      for (size_t x : q) put_u64(out, x);
    // Every list is length-prefixed, so the description is injective.
    put_u64(out, rows_.size());
    for (const auto &r : rows_) {
      put_str(out, r.name);
      put_u64(out, r.n);
      put_u64(out, r.terms.size());
      for (const auto &t : r.terms) {
        uint8_t b[F::kBytes];
        d_.field().to_bytes_field(b, t.scale);
        out.insert(out.end(), b, b + F::kBytes);
        put_u64(out, t.id);
        put_u64(out, t.src);
        put_u64(out, t.src == Flat::kCell ? tplan_->layout->legacy_coord(t.at)
                                          : t.at);
        put_u64(out, t.in_n);
        put_u64(out, t.chain.size());
        for (const auto &op : t.chain) {
          put_str(out, op->name);
          put_u64(out, op->rows);
          put_u64(out, op->cols);
          put_u64(out, op->params.size());
          out.insert(out.end(), op->params.begin(), op->params.end());
          put_u64(out, op->deps.size());
          for (size_t x : op->deps) put_u64(out, x);
        }
        // A predicate's constants (src kConst marks the term).
        for (const auto &c : t.konst) {
          d_.field().to_bytes_field(b, c);
          out.insert(out.end(), b, b + F::kBytes);
        }
      }
    }
    put_u64(out, d_.bound_.size());
    for (const auto &[x, view] : d_.bound_) {
      put_u64(out, x);
      const auto e = d_.describe_lin(view);
      put_u64(out, e.size());
      out.insert(out.end(), e.begin(), e.end());
    }
    // Predicates are described below, with their placements.
    put_u64(out, d_.circuits_.size() - d_.preds_.size());
    for (const auto &c : d_.circuits_) {
      if (c.pred >= 0) continue;
      put_str(out, c.name);
      put_u64(out, c.reads.size());
      for (size_t r : c.reads) put_u64(out, r);
    }
    put_u64(out, bplan_.size());
    for (size_t i = 0; i < bplan_.size(); ++i) {
      put_str(out, bplan_[i].name);
      put_u64(out, btables_[i].size());
      for (size_t t : btables_[i]) put_u64(out, t);
      put_u64(out, bplan_[i].pad_input);
      bplan_[i].kernel->describe(out);
    }
    if (!d_.preds_.empty()) {
      // Each predicate: name, kind, placement and expression.
      put_str(out, "predicates");
      put_u64(out, d_.preds_.size());
      for (size_t k = 0; k < d_.preds_.size(); ++k) {
        const auto &p = d_.preds_[k];
        put_str(out, p.name);
        put_u64(out, p.truth ? 1 : 0);
        put_u64(out, uint64_t(pplan_[k].where));
        describe_expr<F>(
            p.e, [this](const Lin<F> &l) { return d_.describe_lin(l); }, out);
      }
    }
  }

  // The target the tableau was planned at, in bits: the profile's, or a
  // fallback's -log2(GOAL_NUM/|K|).
  double planned_bits() const {
    if (lig_->goal_num == 0) return double(lig_->half) / 2;
    return compiler::field_order(d_.field()).log2() -
           std::log2(double(lig_->goal_num));
  }
  std::string report() const override {
    std::ostringstream o;
    const size_t nw = circ_->ninputs - circ_->npub_in;
    // The circuit's wires (every layer's inputs) and quad terms, and the
    // first bytes of its id: equal ids are equal circuits.
    size_t wires = 0;
    for (const auto &layer : circ_->l) wires += layer.nw;
    char idhex[17];
    for (size_t i = 0; i < 8; ++i)
      std::snprintf(idhex + 2 * i, 3, "%02x", circ_->id[i]);
    o << "domain " << d_.name << " (" << d_.p_.field_name << ")\n"
      << "  circuit: " << (gkr_ ? "" : "none (no circuit constraint, no GKR) ")
      << "ninputs=" << circ_->ninputs << " public=" << circ_->npub_in
      << " committed=" << nw << " subfield="
      << (circ_->subfield_boundary > circ_->npub_in
              ? circ_->subfield_boundary - circ_->npub_in
              : 0)
      << " layers=" << circ_->nl
      << " gkr_pads=" << ZkCommon<F>::pad_size(*circ_) << " wires=" << wires
      << " quad_terms=" << circ_->nterms() << " id=" << idhex
      << "\n  ligero: rate=" << d_.p_.rate << " nreq="
      << (lig_ ? lig_->t : d_.p_.nreq) << " block_enc=" << block_enc_
      << " nw=" << param_nw_ << " nq=" << ZkCommon<F>::num_quadratic(*circ_)
      << "\n";
    if (list_radius()) {
      const size_t t = lig_ ? lig_->t : d_.p_.t;
      const LigeroMasking m = lig_ ? lig_->masking : d_.p_.masking;
      o << "  ligero list radius: (N, k)=(" << param_N_ << ", " << param_k_
        << ") t=" << t << " r=" << t << " masking="
        << (m == LigeroMasking::kSplit ? "split" : "untested")
        << " rows=" << param_nrow_ << " w=" << param_w_;
      if (lig_ && lig_->reps > 1) o << " ldt_reps=" << lig_->reps;
      o << "\n";
    }
    if (lig_) {
      char buf[160];
      std::snprintf(buf, sizeof(buf),
                    "  ligero choice: target 2^-%g A=%zu a=%zu l=%zu rounds "
                    "-log2: commit %.3f test %.3f column %.3f\n",
                    planned_bits(), lig_->A, lig_->a, lig_->l, lig_->commit,
                    lig_->test, lig_->column);
      o << buf;
      if (lig_->fallback) {
        std::snprintf(buf, sizeof(buf),
                      "  ligero target fallback: the profile's 2^-%g is out "
                      "of reach (largest own round 2^-%.3f); planned at "
                      "2^-%g\n",
                      double(d_.p_.target_half()) / 2, lig_->ip_bits,
                      planned_bits());
        o << buf;
      }
      o << "  ligero certificate: B=" << lig_->cert.count << " "
        << lig_->cert.name() << "\n";
      // The domain's own rounds besides Ligero's, each on its own.
      const OwnRounds own = own_rounds();
      const double lq = compiler::field_order(d_.field()).log2();
      auto b = [&](double num) { return lq - std::log2(num); };
      std::snprintf(buf, sizeof(buf),
                    "  own rounds -log2: batches %.3f gkr %.3f "
                    "combinations %.3f",
                    own.batches ? b(double(own.batches)) : INFINITY,
                    own.gkr ? b(double(own.gkr)) : INFINITY,
                    own.combinations ? b(double(own.combinations)) : INFINITY);
      o << buf;
      for (const auto &[ph, num] : own.phases) {
        std::snprintf(buf, sizeof(buf), " phase%zu %.3f", ph,
                      b(double(num)));
        o << buf;
      }
      o << "\n";
    }
    o
      << "  constraints: circuit=" << ncircuits_
      << " late_bit_checks=" << late_bits_
      << " cell_bit_checks=" << cell_bit_checks_
      << " batch_bit_checks=" << batch_bit_checks_
      << " derived_bit_checks=" << derived_bit_checks_
      << " affine_rows=" << total_rows_
      << " quadratic=" << circ_->input_products.size() << " (bit checks "
      << bit_products_ << ")\n";
    if (!tree_.nodes[0].children.empty()) {
      const auto &l = *tplan_->layout;
      size_t sub_n = 0, words = 0, deg = 0;
      for (int c : tree_.nodes[0].children) {
        sub_n += l.region[size_t(c)].n;
        words += l.region[size_t(c)].groups;
        deg = l.stages[size_t(c)].d;
      }
      const size_t npacked = l.bits >= 0 ? l.region[size_t(l.bits)].words : 0;
      o << "  packing: packed_bits=" << packed_bits_ << " (" << npacked
        << " words committed, " << packed_zero_bits_
        << " zero) bit_views=" << view_words_ << " words (aliased)"
        << " alignment=" << filler_.size();
      if (l.nflat > 0)
        o << "; unpacked: " << l.nflat
          << " subfield coordinates, one per cell (DomainProfile::unpacked_s0)";
      else
        o << "; relative: " << sub_n << " subfield coordinates in " << words
          << " words of degree " << deg;
      o << "; " << subfield_.report() << "\n";
      o << tree_report();
    } else {
      o << "  packing: none (no subfield cells)\n";
    }
    for (const auto &[x, note] : d_.bound_note_)
      o << "  " << nodes()[x].name << ": no cell; view " << note << "\n";
    // Each check group: its target, why, and the candidates' costs when the
    // placement rule weighed them; predicates merged into one group, once.
    for (size_t k = 0; k < d_.preds_.size(); ++k) {
      const PredPlan &pp = pplan_[k];
      const Group *g = pp.group >= 0 ? &groups_[size_t(pp.group)] : nullptr;
      if (g != nullptr && g->preds.size() > 1) {
        if (g->preds[0] != k) continue;
        o << "  assert_zero group '" << d_.preds_[k].name << "' ("
          << g->preds.size() << " predicates, "
          << batch_eval_name(g->eval) << ", degree "
          << g->degree << ") n=" << g->n << ": "
          << placement_name(g->choice.where) << " (" << pp.why;
        if (!pp.costs.empty()) o << "; " << pp.costs;
        o << ")\n";
      } else {
        o << "  " << (d_.preds_[k].truth ? "assert_true" : "assert_zero")
          << " '" << d_.preds_[k].name << "' n=" << d_.preds_[k].e->n << ": "
          << placement_name(pp.where) << " (" << pp.why;
        if (!pp.costs.empty()) o << "; " << pp.costs;
        o << ")\n";
      }
      if (g != nullptr && g->preds[0] == k && g->choice.growth > kFlagBytes) {
        char b[160];
        std::snprintf(b, sizeof(b),
                      "  warning: the placement of '%s' grows the proof by "
                      "%.1f KB over its smallest candidate\n",
                      d_.preds_[k].name.c_str(), g->choice.growth / 1024);
        o << b;
      }
    }
    if (bit_group_n_ > 0) {
      o << "  Boolean checks n=" << bit_group_n_ << ": "
        << placement_name(bit_choice_.where) << " (" << bit_choice_.why;
      o << "; " << bit_choice_.costs();
      o << ")\n";
    }
    for (size_t id : d_.unchecked_bits_)
      o << "  unchecked Bit '" << nodes()[id].name << "' n=" << nodes()[id].n
        << ": bit_from_unchecked, Booleanity is the caller's "
           "responsibility\n";
    for (const auto &b : bplan_) {
      o << "  batch " << b.name << ": " << b.kernel->report()
        << "; skip domain of " << b.kernel->skip_points() << " points in "
        << skip_node(b.kernel->skip_points()) << "\n";
    }
    if (d_.p_.no_skip)
      o << "  batches: no univariate skip, width 1 (DomainProfile::no_skip, "
           "a test-only ablation)\n";
    return o.str();
  }

  std::unique_ptr<DomainProverBase<S>> prover() const override;
  // The provers' working buffers (prover_scratch.h): one DomainScratch per
  // proof in flight, which its DomainProver holds for its proof.
  typename ScratchPool<DomainScratch<F>>::Lease scratch() const {
    return scratch_.lease();
  }

  // Each request's value as canonical integers below the bound N its
  // realization establishes (n for an exact request; the selected N in
  // [n, m] for one with slack). Every coordinate is read before any branch:
  // a request's flag is accumulated with no branch on the witness.
  std::string unmet_range(const ValueStore<S> &v) const override {
    if constexpr (F::kCharacteristicTwo) {
      return "";
    } else {
      const F &f = d_.field();
      const auto &reqs = d_.requests();
      std::vector<uint64_t> held(reqs.size(), 1);
      for (size_t k = 0; k < reqs.size(); ++k) {
        const auto &r = reqs[k];
        Bound N = r.n;
        if (r.interval)
          N = r.realization.established != 0 ? r.realization.established
                                             : r.m;
        const std::vector<Elt> x = eval_lin(r.v, v);
        uint64_t ok = 1;
        // A bound beyond 128 bits exceeds every NatInt (a public choice).
        const bool wide = !N.fits128();
        const NatInt n = wide ? NatInt(0) : static_cast<NatInt>(N);
        for (const Elt &e : x) {
          const NatInt a = nat_of_ct(f, e, ok);
          ok &= wide ? 1 : ct::lt128(a, n);
        }
        held[k] = ok;
      }
      for (size_t k = 0; k < reqs.size(); ++k)
        if (!held[k]) return reqs[k].name;
      return "";
    }
  }

  DomainPlan plan() const override {
    DomainPlan p;
    const auto &prm = *tplan_->param;
    p.rate = prm.rateinv;
    p.block_enc = prm.block_enc;
    p.N = prm.block_ext;
    p.k = prm.block;
    p.t = prm.nreq;
    p.r = prm.r;
    p.nrow = prm.nrow;
    p.list_radius = prm.mode.list_radius;
    p.split = prm.mode.split();
    p.ldt_reps = prm.mode.ldt_reps;
    if (lig_) {
      p.target = planned_bits();
      p.target_fallback = lig_->fallback;
      p.target_num = lig_->goal_num;
      p.agreement = lig_->A;
      p.exceptions = lig_->cert.count;
      p.commit_bits = lig_->commit;
      p.test_bits = lig_->test;
      p.column_bits = lig_->column;
    }
    p.nw = prm.nw;
    p.nq = prm.nq;
    if constexpr (circuit_id_detail::HasFieldId<F>::value) {
      p.characteristic = F::kProtocolFieldId[0];
      p.protocol_degree = F::kProtocolFieldId[1];
    }
    p.field_bytes = F::kBytes;
    p.field_degree = tree_.n;
    p.s0 = tree_.s0;
    const auto &l = *tplan_->layout;
    for (int x : tree_.bottom_up()) {
      const auto &nd = tree_.nodes[size_t(x)];
      const auto &st = l.stages[size_t(x)];
      DomainPlan::TreeNode t;
      t.degree = nd.degree;
      t.parent_degree = st.t;
      t.declared = nd.declared;
      t.squaring_chain = st.squaring_chain();
      t.revealed = st.d;
      t.masks = st.squaring_chain() ? st.d : st.mask_cells();
      t.chain_cells = st.chain_cells();
      t.routed = tplan_->routed.at(size_t(x));
      p.tree.push_back(t);
    }
    p.gkr = gkr_;
    p.ninputs = circ_->ninputs;
    p.npub = circ_->npub_in;
    p.layers = circ_->nl;
    for (const auto &layer : circ_->l) p.wires += layer.nw;
    p.quad_terms = circ_->nterms();
    p.circuit_id.assign(circ_->id, circ_->id + Hash::kDigestSize);
    for (const auto &r : rows_) p.affine_rows.push_back({r.name, r.n});
    p.quad_triples = circ_->input_products.size();
    for (const auto &[id, in_circuit] : bit_checks_)
      p.bit_checks.push_back({id, nodes()[id].n, in_circuit});
    for (const auto &[nm, n] : tplan_->stream_rows(extra_rows()))
      p.stream_points.push_back(DomainPlan::StreamPoint{
          nm, n, fs_stream_budget<Hash>() + 4 * n * F::kBytes});
    using In = DomainPlan::Input;
    for (const auto &sl : slots_)
      p.inputs.push_back(In{sl.id, sl.at, nodes()[sl.id].n,
                            sl.msg ? In::kMessage : In::kPublic});
    for (const auto &[id, at] : cells_)
      p.inputs.push_back(In{id, at, nodes()[id].n, In::kCell});
    for (const auto &[id, at] : view_at_)
      p.inputs.push_back(In{id, at, nodes()[id].n, In::kView});
    std::stable_sort(p.inputs.begin(), p.inputs.end(),
                     [](const In &a, const In &b) { return a.at < b.at; });
    for (const auto &bp : bplan_) {
      const auto sh = bp.kernel->shape();
      DomainPlan::Batch b;
      b.name = bp.name;
      b.table_degree = tree_.nodes.at(size_t(bp.table_node)).degree;
      b.pads = bp.kernel->pads();
      b.pad_input = bp.pad_input;
      b.bit_operands = bp.kernel->bit_operands();
      b.arity = sh.arity;
      b.degree = sh.degree;
      b.instances = sh.instances;
      b.width = sh.width;
      b.rounds = sh.rounds;
      b.bit_phase = bp.kernel->bit_phase_rounds();
      b.parts = sh.parts;
      b.work = bp.work;
      const auto &tables = btables_[size_t(&bp - bplan_.data())];
      if (!sh.call_instances.empty()) {
        check(sh.call_instances.size() == tables.size(),
              "a batch's calls and tables");
        for (size_t i = 0; i < tables.size(); ++i)
          b.calls.push_back({tables[i], sh.call_instances[i]});
      }
      p.batches.push_back(std::move(b));
    }
    for (size_t k = 0; k < d_.preds_.size(); ++k) {
      const PredPlan &pp = pplan_[k];
      const Group *g = pp.group >= 0 ? &groups_[size_t(pp.group)] : nullptr;
      DomainPlan::Placed x;
      x.name = d_.preds_[k].name;
      x.where = pp.where;
      x.instances = d_.preds_[k].e->n;
      if (g != nullptr && g->preds.size() > 1) {
        if (g->preds[0] != k) continue;
        x.predicates = g->preds.size();
        x.instances = 0;
        for (size_t j : g->preds) x.instances += d_.preds_[j].e->n;
      }
      if (g != nullptr && pp.where == Placement::kBatch) x.batch = g->name;
      if (pp.where == Placement::kBatch) x.operands = pp.operands;
      p.placements.push_back(std::move(x));
    }
    for (size_t k = 0; k < d_.preds_.size(); ++k) {
      const PredPlan &pp = pplan_[k];
      const Group *g = pp.group >= 0 ? &groups_[size_t(pp.group)] : nullptr;
      DomainPlan::PredTarget t;
      t.where = pp.where;
      if (g != nullptr && pp.where == Placement::kBatch) t.batch = g->name;
      if (pp.where == Placement::kQuadratic) {
        t.a = pp.tri.a;
        t.b = pp.tri.b;
        t.c = pp.tri.c;
      }
      p.pred_targets.push_back(std::move(t));
    }
    p.type_checks = type_checks_;
    p.circuit_entries = circuit_entries_;
    p.filler = filler_;
    return p;
  }

  // The packing tree: each node's region, its edge to its parent (mode,
  // degree, masks, chain cells, revealed elements) and the membership test.
  std::string tree_report() const {
    std::ostringstream o;
    const auto &l = *tplan_->layout;
    auto name = [](size_t d) {
      return std::string(F::kCharacteristicTwo ? "GF(2^" : "GF(p^") +
             std::to_string(d) + ")";
    };
    o << "  packing tree (D_max=" << tree_.d_max << "): K = "
      << name(tree_.n) << ", own " << l.own << " coordinates, prefix "
      << l.prefix << " mask coordinates in " << tplan_->prefix_rows()
      << " rows, " << l.nw << " committed\n";
    size_t revealed = 0;
    for (int x : tree_.bottom_up()) {
      const auto &nd = tree_.nodes[size_t(x)];
      const auto &st = l.stages[size_t(x)];
      const auto &rg = l.region[size_t(x)];
      if (l.flat[size_t(x)]) {
        o << "    " << name(nd.degree) << ": region " << rg.n
          << " coordinates committed unpacked, one per cell in "
          << tplan_->prefix_rows() << " subfield rows (with the prefix), "
          << "no stage (DomainProfile::unpacked_s0)\n";
        continue;
      }
      revealed += st.d;
      o << "    " << name(nd.degree) << (nd.declared ? "" : " (intermediate)")
        << ": region " << rg.n << " coordinates in " << rg.groups
        << " groups (" << rg.words << " words, " << rg.groups - rg.words
        << " aliased); edge to " << name(st.t) << ": "
        << (st.squaring_chain() ? "squaring-chain masks" : "subfield masks")
        << ", degree " << st.d << ", " << st.d << " revealed ("
        << st.d * F::kBytes << " bytes), ";
      if (st.squaring_chain())
        o << st.d << " masks and " << st.chain_cells()
          << " chain cells in K (" << st.chain_cells()
          << " quadratic constraints"
          << (st.b > 1 ? "; " + std::to_string(st.b) +
                             " squarings per Frobenius twist, since the "
                             "prefix-row test in " + name(tree_.s0) +
                             " does not cover " + name(st.b)
                       : std::string())
          << ")\n";
      else
        o << st.mask_cells() << " mask coordinates in " << name(tree_.s0)
          << " (prefix)\n";
    }
    for (const auto &[D, cb] : l.bases) {
      size_t nviews = 0;
      std::string path;
      for (const auto &v : l.views) {
        if (v.degree != D) continue;
        if (nviews++ == 0)
          for (int u : v.path)
            path += " < " + name(tree_.nodes[size_t(u)].degree);
      }
      o << "    composed bit views: " << nviews << " words of " << name(D)
        << ", decoded GF(2^1)" << path << " < " << name(D) << " ("
        << cb.r << " uncommitted GF(2^" << cb.d
        << ") coordinates per word); the bit stage's forms change the "
           "tower basis to the canonical bits\n";
    }
    o << "    membership: decoded coordinates lie in their base; "
      << (l.prefix ? "the prefix-row test in " + name(tree_.s0) +
                         " covers every subfield-masks stage's masks"
                   : std::string("no subfield-masks stage"))
      << "; " << revealed * F::kBytes << " revealed bytes per proof\n"
      << chain_costs_;
    return o.str();
  }
  std::unique_ptr<DomainVerifierBase<S>> verifier() const override;
  size_t branches() const override { return bplan_.size() + 1; }
  size_t tableau_size() const override {
    const auto &p = *tree_plan().param;
    return p.nrow * p.block_enc;
  }
  // The nested fork's branches (transcript_fork.h), for the profiler's
  // names: each batch's, in compiled order, then GKR's.
  std::vector<std::string> branch_labels() const {
    std::vector<std::string> out;
    for (const auto &b : bplan_) out.push_back("batch:" + b.name);
    out.push_back("gkr");
    return out;
  }
  // The domain's index in the system (compiled order) and its field's name,
  // which the fork labels carry.
  uint64_t domain_index() const { return uint64_t(d_.index); }
  const std::string &field_name() const { return d_.p_.field_name; }
  // The profiler: a branch's session name, "<field>/<label>".
  std::string branch_profile_name(size_t b) const {
    return d_.p_.field_name + "/" + branch_labels().at(b);
  }

  // ------------------------------------------------- shared by both sides

  void fill_cells(Dense<F> &W, const ValueStore<S> &v) const {
    W.v_[0] = d_.field().one();
    for (const auto &s : slots_)
      for (size_t i = 0; i < nodes()[s.id].n; ++i)
        W.v_[s.at + i] = d_.field().zero();
    // The nodes' values at their cells, then the bit views', each list's
    // elements in one range in chunks under a runner (util/parallel.h);
    // a list's nodes have distinct cells. The boundaries depend on the
    // nodes' sizes only.
    const auto copy_all = [&](const auto &list, const char *what) {
      std::vector<const std::vector<Elt> *> src;
      std::vector<size_t> dst, at0(1, 0);
      for (const auto &[id, at] : list) {
        src.push_back(&v.template get<F>(id));
        check(src.back()->size() == nodes()[id].n, what);
        dst.push_back(at);
        at0.push_back(at0.back() + src.back()->size());
      }
      const size_t n = at0.back();
      parallel::for_chunks(n, parallel::grain_for(n, parallel::kChunks),
                           [&](size_t q0, size_t q1) {
        size_t k = size_t(std::upper_bound(at0.begin(), at0.end(), q0) -
                          at0.begin()) -
                   1;
        for (size_t q = q0; q < q1; ++k) {
          const size_t e = std::min(q1, at0[k + 1]);
          std::copy(src[k]->begin() + long(q - at0[k]),
                    src[k]->begin() + long(e - at0[k]),
                    W.v_.begin() + long(dst[k] + (q - at0[k])));
          q = e;
        }
      });
    };
    copy_all(cells_, "cell size");
    // Bit views: the bits of the aliased words, which GKR reads.
    copy_all(view_at_, "bit view size");
    for (size_t i : filler_) W.v_[i] = d_.field().zero();
  }
  void fill_public(Dense<F> &W, const ValueStore<S> &v) const {
    W.v_[0] = d_.field().one();
    for (const auto &s : slots_) {
      const auto &x =
          s.msg ? v.template message<F>(s.id) : v.template get<F>(s.id);
      check(x.size() == nodes()[s.id].n, "public slot size");
      for (size_t i = 0; i < x.size(); ++i) W.v_[s.at + i] = x[i];
    }
  }

  // The affine rows: instantiated operators from public values, the
  // right-hand side, and the transpose accumulation into Ligero's A.
  ExtraRows<F> extra(const ValueStore<S> &v,
                     const std::vector<BatchRows> &runs = {}) const {
    const F &f = d_.field();
    struct Inst {
      Elt scale;
      std::vector<std::shared_ptr<const LinearOperator<F>>> ops;
      size_t row0, out_n, at, in_n;
    };
    std::vector<Inst> insts;
    std::vector<Elt> rhs(total_rows_, f.zero());
    for (const auto &r : rows_) {
      for (const auto &t : r.terms) {
        if (t.src == Flat::kConst) {
          // Constants, through their operators when they have some.
          std::vector<Elt> x = t.konst;
          for (const auto &spec : t.chain) {
            std::vector<Elt> y(spec->rows);
            instantiate(*spec, v)->apply(x.data(), y.data());
            x = std::move(y);
          }
          for (size_t i = 0; i < r.n; ++i)
            f.sub(rhs[r.row0 + i], f.mulf(t.scale, x[i]));
          continue;
        }
        std::vector<std::shared_ptr<const LinearOperator<F>>> ops;
        for (const auto &spec : t.chain) ops.push_back(instantiate(*spec, v));
        if (t.src == Flat::kCell) {
          insts.push_back(Inst{t.scale, std::move(ops), r.row0, r.n, t.at,
                               t.in_n});
          continue;
        }
        std::vector<Elt> x =
            t.src == Flat::kMessage ? v.template message<F>(t.id)
                                    : v.template get<F>(t.id);
        for (const auto &op : ops) {
          std::vector<Elt> y(op->rows());
          op->apply(x.data(), y.data());
          x = std::move(y);
        }
        for (size_t i = 0; i < r.n; ++i)
          f.sub(rhs[r.row0 + i], f.mulf(t.scale, x[i]));
      }
    }
    // Batch rows follow the affine rows: run i starts at row brow[i].
    auto shared = std::make_shared<std::vector<BatchRows>>(runs);
    std::vector<size_t> brow;
    size_t next = total_rows_;
    for (const auto &r : runs) {
      brow.push_back(next);
      next += r.b.size();
    }
    ExtraRows<F> ex;
    ex.n = next;
    ex.b = rhs;
    ex.nodes.assign(next, 0);
    // The tree nodes each row reads.
    for (const auto &r : rows_) {
      uint64_t m = 0;
      for (const auto &t : r.terms)
        if (t.src == Flat::kCell)
          m |= uint64_t(1) << tree_.node_of(degree_of(t.id));
      for (size_t i = 0; i < r.n; ++i) ex.nodes[r.row0 + i] = m;
    }
    for (size_t i = 0; i < runs.size(); ++i) {
      const auto &r = runs[i];
      for (auto t : r.a) {
        t.c += brow[i];
        ex.a.push_back(t);
      }
      ex.b.insert(ex.b.end(), r.b.begin(), r.b.end());
      for (size_t k = 0; k < r.b.size(); ++k) ex.nodes[brow[i] + k] = 1;
      if (r.bit_claim) {
        // A claim on the table words' bits: the bit node's stage opens it.
        ex.nodes[brow[i] + r.form_row] |= uint64_t(1) << tree_.node_of(1);
        ex.claims.push_back(
            {brow[i] + r.form_row, r.forms, bplan_[i].word_at, r.product});
        continue;
      }
      const size_t nforms = r.forms->a.size() / r.forms->stride;
      for (size_t k = 0; k < nforms; ++k)
        ex.nodes[brow[i] + r.form_row + k] |= uint64_t(1)
                                              << bplan_[i].table_node;
    }
    if (runs.size() == bplan_.size())
      check(ex.nodes == extra_nodes(), "the rows' nodes are the plan's");
    std::vector<const std::vector<size_t> *> word_at;
    for (const auto &b : bplan_) word_at.push_back(&b.word_at);
    const F *pf = &f;
    ex.accumulate = [insts = std::move(insts), pf, shared, brow,
                     word_at](Elt *A, const Elt *alphal) {
      for (size_t i = 0; i < shared->size(); ++i) {
        const auto &r = (*shared)[i];
        if (r.bit_claim) continue;  // the bit node's stage opens it
        const auto &forms = *r.forms;
        const size_t nforms = forms.a.size() / forms.stride;
        const size_t row = brow[i] + r.form_row;
        for (size_t y = 0; y < forms.stride; ++y) {
          typename F::Accum sum{};
          for (size_t k = 0; k < nforms; ++k)
            pf->mac(sum, alphal[row + k], forms.a[k * forms.stride + y]);
          pf->add(A[(*word_at[i])[y]], pf->reduce(sum));
        }
      }
      // The terms of one row share the forward transforms of its
      // multipliers (TransposeRun). A term whose rows all have multiplier
      // zero adds nothing: a packing stage passes the rows it combines
      // and zeros elsewhere, and the root zeros for the rows a stage took.
      ops::TransposeRun<F> run;
      for (const auto &in : insts) {
        bool any = false;
        for (size_t i = 0; i < in.out_n && !any; ++i)
          any = alphal[in.row0 + i] != pf->zero();
        if (!any) continue;
        run.accumulate(*pf, in.ops, alphal + in.row0, in.out_n, in.scale,
                       A + in.at);
      }
    };
    return ex;
  }

  // The rows the domain adds after GKR: its affine rows, then each
  // batch's reduction rows (ExtraRows::n).
  size_t extra_rows() const {
    size_t n = total_rows_;
    for (const auto &b : bplan_) n += b.kernel->reduction_rows();
    return n;
  }
  // The tree nodes each of those rows reads (ExtraRows::nodes), from the
  // plan: an affine row reads its cells' nodes; a batch's rows read the
  // root, and its last row, the form row, also the node of its tables (the
  // bit node for a claim on the table words' bits).
  std::vector<uint64_t> extra_nodes() const {
    std::vector<uint64_t> out(total_rows_, 0);
    for (const auto &r : rows_) {
      uint64_t m = 0;
      for (const auto &t : r.terms)
        if (t.src == Flat::kCell)
          m |= uint64_t(1) << tree_.node_of(degree_of(t.id));
      for (size_t i = 0; i < r.n; ++i) out[r.row0 + i] = m;
    }
    for (const auto &b : bplan_) {
      const size_t n = b.kernel->reduction_rows();
      out.insert(out.end(), n, uint64_t(1));
      out.back() |= uint64_t(1) << (b.kernel->bit_operands()
                                        ? tree_.node_of(1)
                                        : b.table_node);
    }
    return out;
  }
  const Circuit<F> &circuit() const { return *circ_; }
  // Whether the domain runs GKR (it has a circuit constraint).
  bool gkr() const { return gkr_; }
  // The branch of the domain's nested fork with the largest estimated
  // cost, which its prover and verifier run on the calling thread (the
  // others go to the pool's workers, whose cores may still be clocking up).
  // The estimate is the placement rule's (placement_rates.h): a batch at
  // its evaluator, degree, instances and operands, GKR at its quad terms.
  // Index i < batches().size() is batch i, and batches().size() is GKR,
  // which is also the choice when the profile has no rates. Which thread
  // runs a branch does not change the proof: each branch has its own
  // transcript.
  size_t heaviest_branch() const override {
    const PlacementRates rates = d_.p_.rates.or_unit();
    const size_t nb = bplan_.size();
    size_t best = nb;
    double best_us = gkr_ ? double(circ_->nterms()) * rates.gkr_term : 0;
    for (size_t i = 0; i < nb; ++i) {
      const BatchKernel<F, Hash> &k = *bplan_[i].kernel;
      const auto sh = k.shape();
      BatchEval eval = BatchEval::kField;
      if (k.bit_operands())
        eval = BatchEval::kBitSliced;
      else if (k.word_degree() < field_degree<F>())
        eval = BatchEval::kSubfield;
      // The placement rule's estimate: the batch's counted work at its
      // evaluator's rates (unit rates: 1 + n).
      double us = 1 + double(sh.instances);
      if (!rates.unit_rates) {
        const auto r =
            rates.batch_rates(eval, unsigned(sh.degree), sh.instances);
        if (!r) continue;
        us = r->cost(bplan_[i].work);
      }
      if (us > best_us) {
        best = i;
        best_us = us;
      }
    }
    return best;
  }
  const D &domain() const { return d_; }
  size_t block_enc() const { return block_enc_; }
  // The Ligero parameters the compiler chose from the profile's target
  // (DomainProfile::target), or none under explicit parameters.
  const std::optional<compiler::LigeroChoice> &ligero_choice() const {
    return lig_;
  }
  // Whether the domain runs list-radius Ligero (its low-degree round in
  // the commit phase).
  bool list_radius() const { return lig_.has_value() || d_.p_.list_radius; }
  const PrefixSubfieldTest<F, Hash> &subfield_test() const { return subfield_; }
  const TreePlan<F, Hash> &tree_plan() const { return *tplan_; }
  TreeTestHooks &tree_test_hooks() const override {
    return tplan_->layout->test_hooks;
  }
  const PackingTree &tree() const { return tree_; }

 private:
  static constexpr char kTag[] = "gordiehowe.affine";
  const std::vector<Node> &nodes() const { return *plan_.nodes; }
  ScratchPool<DomainScratch<F>> scratch_;

  // A committed cell of the subfield space: a Subfield variable or a
  // subfield pad (a Bit pad in odd characteristic).
  bool subfield_cell(size_t id) const {
    const Node &n = nodes()[id];
    if (n.kind == Kind::kPad)
      return d_.resolve(n.pad_space) == Space::kSubfield;
    return n.type.base == Base::kSubfield;
  }
  // Cells committed before the full-field region: every cell of a packed
  // domain that lies in the subfield. A domain without relative packing
  // commits Bit cells as field cells (b * b = b).
  bool in_subfield_region(size_t id) const {
    const Node &n = nodes()[id];
    if (!d_.has_subfield || !relative_packing<F>()) return false;
    if (n.kind == Kind::kPad) {
      const Space s = d_.resolve(n.pad_space);
      return s == Space::kSubfield || s == Space::kPrime;
    }
    return n.type.base == Base::kBit || n.type.base == Base::kSubfield;
  }

  // The smallest packing-tree node with at least N elements (in
  // characteristic 2, one holding the GF(2^8) subspace): where a batch's
  // skip points lie.
  std::string skip_node(size_t n) const {
    size_t best = 0;
    for (const auto &nd : tree_.nodes) {
      const size_t d = nd.degree;
      bool fits;
      if constexpr (F::kCharacteristicTwo) {
        fits = d % 8 == 0 && (d >= 64 || (size_t(1) << d) >= n);
      } else {
        // n <= p.
        fits = n == 0 || characteristic_above(d_.field(), Bound(n) - 1);
      }
      if (fits && (best == 0 || d < best)) best = d;
    }
    return std::string(F::kCharacteristicTwo ? "GF(2^" : "GF(p^") +
           std::to_string(best) + ")";
  }
  // Whether the node of degree D lies on the path from the bit node up,
  // below K: the words whose bits a view or a bit batch may read.
  bool above_bits(size_t D) const {
    const int b = tree_.node_of(1);
    if (b < 0) return false;
    for (int u = tree_.nodes[size_t(b)].parent; u > 0;
         u = tree_.nodes[size_t(u)].parent)
      if (tree_.nodes[size_t(u)].degree == D) return true;
    return false;
  }
  // Whether the tree is GF(2) < S0 < K or a part of it, the shape
  // ZkProver packed (its description adds nothing).
  bool legacy_tree() const {
    for (size_t i = 1; i < tree_.nodes.size(); ++i) {
      const auto &nd = tree_.nodes[i];
      const size_t up = tree_.nodes[size_t(nd.parent)].degree;
      const bool bits = F::kCharacteristicTwo && nd.degree == 1 &&
                        up == designated_degree<F>();
      const bool s0 = nd.degree == designated_degree<F>() && nd.parent == 0;
      if (!bits && !s0) return false;
    }
    return true;
  }
  // The packing-tree node (its degree) a committed cell lies in, from its
  // type alone: a Bit lies in the prime subfield (subfield_of<Bit> is
  // GF<1>), as does a pad of the prime space; a Subfield value in its
  // subfield; a subfield pad in the subfield of the value it masks (its
  // pad_degree; the designated one by default); everything else in K. A
  // bit view's bits are coordinates of the degree-1 node.
  size_t degree_of(size_t id) const {
    const Node &n = nodes()[id];
    if (n.kind == Kind::kBitView) return 1;
    if (!in_subfield_region(id)) return field_degree<F>();
    if (n.kind == Kind::kPad)
      return d_.resolve(n.pad_space) == Space::kPrime
                 ? 1
                 : subfield_degree<F>(n.pad_degree);
    if (n.type.base == Base::kBit)
      return unpacked_bits() ? designated_degree<F>()
                             : subfield_of<Bit>::type::kDegree;
    return subfield_degree<F>(n.type.degree);
  }
  // A Bit cell in odd characteristic: the prime subfield's value plus the
  // core's Boolean check (has_boolean_check).
  bool boolean_checked(size_t id) const {
    const Node &n = nodes()[id];
    return (has_boolean_check<F>() || unpacked_bits()) &&
           n.kind != Kind::kPad && n.type.base == Base::kBit;
  }

  void same_field(size_t id, const char *what) const {
    if (nodes()[id].fobj != d_.fobj)
      fail(std::string(what) + " '" + nodes()[id].name + "' of domain " +
           d_.name + " lies in another field; a domain reads public values "
           "only in its own field");
  }

  // Public slots that VIEW(id) needs.
  void need(size_t id, std::set<std::pair<size_t, bool>> &keys) {
    const Node &n = nodes()[id];
    if (plan_.late(id)) {
      if (n.domain != d_.index)
        fail("circuit of domain " + d_.name + " reads the late value '" +
             n.name + "' of another domain; read its public message");
      keys.insert({id, true});
    } else if (n.kind == Kind::kBitView) {
      if (n.domain != d_.index)
        fail("circuit of domain " + d_.name + " reads the bit view '" +
             n.name + "' of another domain");
      views_read_.insert(id);
    } else if (auto x = d_.exprs_.find(id); x != d_.exprs_.end()) {
      if (n.domain != d_.index)
        fail("circuit of domain " + d_.name + " reads the expression value '" +
             n.name + "' of another domain");
      for (size_t r : expr_deps(x->second)) need(r, keys);
    } else if (n.kind == Kind::kDerived || plan_.bound.count(id)) {
      if (n.domain != d_.index)
        fail("circuit of domain " + d_.name + " reads the derived value '" +
             n.name + "' of another domain");
      for (const auto &t : expr(id).terms) {
        // A circuit reads an operator through its circuit expansion only.
        for (const auto &op : t.chain)
          if (!circuit_expandable(*op))
            fail("derived value '" + n.name + "' read by a circuit applies "
                 "the structured operator '" + op->name + "', which has no "
                 "circuit expansion (OpSpec::emit or a staged transform)");
        need(t.node, keys);
      }
    } else if (is_public(n.kind)) {
      if (n.type.base == Base::kBytes)
        fail("circuit of domain " + d_.name + " reads the Bytes statement '" +
             n.name + "'; read it through a public computation");
      same_field(id, "public value");
      keys.insert({id, false});
    } else if (plan_.cell(id)) {
      if (n.domain != d_.index)
        fail("circuit of domain " + d_.name + " reads '" + n.name +
             "' of another domain");
    } else {
      fail("circuit reads unsupported value '" + n.name + "'");
    }
  }

  Wires view(const CLogic &lc, size_t id) const {
    const Node &n = nodes()[id];
    if (plan_.late(id)) {
      const Wires &t = pub_wires_.at({id, true});
      const Wires &p = cell_wires_.at(static_cast<size_t>(plan_.pad_of[id]));
      Wires out(n.n);
      for (size_t i = 0; i < n.n; ++i) out[i] = lc.sub(t[i], p[i]);
      return out;
    }
    if (auto w = d_.wiring_.find(id); w != d_.wiring_.end()) {
      // A wiring view: the source wires themselves.
      std::map<size_t, Wires> part;
      Wires out(w->second.size());
      for (size_t i = 0; i < out.size(); ++i) {
        const auto &[node, k] = w->second[i];
        if (node == kZeroCoordinate) {
          out[i] = lc.konst(lc.elt(0));
          continue;
        }
        auto it = part.find(node);
        if (it == part.end()) it = part.emplace(node, view(lc, node)).first;
        out[i] = it->second.at(k);
      }
      return out;
    }
    if (auto x = d_.exprs_.find(id); x != d_.exprs_.end()) {
      // An expression value: emitted in place, once per build.
      Wires out;
      for (const auto &b : (*emitter_)(x->second))
        out.push_back(emitter_->wire(b));
      return out;
    }
    if (n.kind == Kind::kDerived || plan_.bound.count(id)) {
      const Lin<F> &e = expr(id);
      Wires out(e.n);
      for (size_t k = 0; k < e.terms.size(); ++k) {
        const auto &t = e.terms[k];
        Wires w = view(lc, t.node);
        for (const auto &op : t.chain) w = expand(lc, *op, w);
        for (size_t i = 0; i < e.n; ++i) {
          const size_t s = lc.mul(t.scale, w[i]);
          out[i] = k == 0 ? s : lc.add(out[i], s);
        }
      }
      return out;
    }
    if (is_public(n.kind)) return pub_wires_.at({id, false});
    if (n.kind == Kind::kBitView) return view_wires_.at(id);
    return cell_wires_.at(id);
  }

  // Flatten an affine expression into cell and public terms.
  void flatten(const Term<F> &t, std::vector<Flat> &out) const {
    const F &f = d_.field();
    const Node &n = nodes()[t.node];
    if (n.fobj != d_.fobj)
      fail("affine term '" + n.name + "' lies in another field");
    if (d_.circuit_only(t.node))
      fail("affine constraint of domain " + d_.name + " reads '" + n.name +
           "', a value defined by a non-affine expression; only a circuit "
           "reads it");
    // Both parties instantiate operators from public values only.
    for (const auto &op : t.chain)
      for (size_t dep : op->deps)
        if (!is_public(nodes()[dep].kind))
          fail("operator '" + op->name + "' applied to '" + n.name +
               "' reads private value '" + nodes()[dep].name + "'");
    if (n.kind == Kind::kDerived || plan_.bound.count(t.node)) {
      if (n.domain != d_.index)
        fail("derived value '" + n.name + "' read from another domain");
      for (const auto &s : expr(t.node).terms) {
        Term<F> u = s;
        u.scale = f.mulf(t.scale, s.scale);
        u.chain.insert(u.chain.end(), t.chain.begin(), t.chain.end());
        flatten(u, out);
      }
    } else if (plan_.late(t.node)) {
      if (n.domain != d_.index)
        fail("affine constraint of domain " + d_.name + " reads the late "
             "value '" + n.name + "' of another domain; read its public "
             "message");
      // x = t - P.
      out.push_back(Flat{t.scale, t.chain, t.node, Flat::kMessage, 0, n.n});
      const size_t p = static_cast<size_t>(plan_.pad_of[t.node]);
      out.push_back(Flat{f.negf(t.scale), t.chain, p, Flat::kCell,
                         coord(cells_.at(p)), n.n});
    } else if (is_public(n.kind)) {
      if (n.type.base == Base::kBytes)
        fail("affine constraint of domain " + d_.name +
             " reads the Bytes statement '" + n.name +
             "'; read it through a public computation");
      out.push_back(Flat{t.scale, t.chain, t.node, Flat::kPublic, 0, n.n});
    } else if (plan_.cell(t.node)) {
      if (n.domain != d_.index)
        fail("affine constraint of domain " + d_.name + " reads '" + n.name +
             "' of another domain");
      out.push_back(Flat{t.scale, t.chain, t.node, Flat::kCell,
                         coord(cells_.at(t.node)), n.n});
    } else if (n.kind == Kind::kBitView) {
      if (n.domain != d_.index)
        fail("affine constraint of domain " + d_.name +
             " reads the bit view '" + n.name + "' of another domain");
      // Its bits are packed run inputs; the bit stage reads them.
      out.push_back(Flat{t.scale, t.chain, t.node, Flat::kCell,
                         coord(view_at_.at(t.node)), n.n});
    } else {
      fail("affine constraint reads unsupported value '" + n.name + "'");
    }
  }

  // The committed witness coordinate of circuit input I (PackedLayout when
  // bits are packed), before relative packing.
  size_t coord(size_t i) const {
    const size_t c = tplan_->layout->input_L.at(i);
    check(c != TreeLayout<F>::kNone, "no coordinate for a public input");
    return c;
  }
  // A Bit cell: a phase-0 Bit variable, or a GF(2) pad in characteristic 2.
  bool bit_cell(size_t id) const {
    const Node &n = nodes()[id];
    if (n.kind == Kind::kPad)
      return d_.resolve(n.pad_space) == Space::kPrime &&
             d_.prime == Space::kPrime;
    return n.type.base == Base::kBit;
  }
  // Committed cells an affine expression term reads.
  void affine_cells(size_t id, std::set<size_t> &out) const {
    const Node &n = nodes()[id];
    if (d_.circuit_only(id)) return;  // flatten refuses it
    if ((n.kind == Kind::kDerived || plan_.bound.count(id)) &&
        n.domain == d_.index) {
      for (const auto &t : expr(id).terms) affine_cells(t.node, out);
    } else if (plan_.late(id)) {
      out.insert(static_cast<size_t>(plan_.pad_of[id]));
    } else if (plan_.cell(id) || n.kind == Kind::kBitView) {
      out.insert(id);
    }
  }

  // The affine expression a derived node is, or a bound node is read as.
  const Lin<F> &expr(size_t id) const {
    auto b = d_.bound_.find(id);
    if (b != d_.bound_.end() && plan_.bound.count(id)) return b->second;
    return d_.lins_.at(id);
  }
  // The circuit expansion of an operator without dependencies.
  static Wires expand(const CLogic &lc, const OpSpec<F> &op, const Wires &w) {
    return expand_operator<F>(lc, op, w);
  }
  // The storage-binding checks B1-B5.
  void check_bindings() const;
  // Places each predicate (PredPlan).
  // With DEC (a compile cache hit), the stored placements and groups, and
  // only the forms they use: affine forms of the predicates placed in
  // affine rows, batched forms of those placed in a batch.
  struct Decisions;
  void place_predicates(const Decisions *dec = nullptr);

  // A measurement hook: CompileOptions::placement_force ("D/NAME=TARGET;...",
  // NAME a predicate's name with '*' matching any characters, or "boolean"
  // for the domain's Boolean checks; TARGET affine, quadratic, circuit or
  // batch) pins what PIN leaves to the rule, so that a benchmark can force
  // each admissible target of a placement and measure it. Empty, it changes
  // nothing.
  Placement forced(const std::string &name, Placement pin) const {
    if (pin != Placement::kAuto) return pin;
    const std::string &spec = plan_.options.placement_force;
    if (spec.empty()) return pin;
    auto match = [](const std::string &pat, const std::string &s) {
      // Glob with '*'.
      std::vector<std::vector<bool>> m(pat.size() + 1,
                                       std::vector<bool>(s.size() + 1));
      m[0][0] = true;
      for (size_t i = 1; i <= pat.size(); ++i)
        for (size_t j = 0; j <= s.size(); ++j)
          m[i][j] = pat[i - 1] == '*'
                        ? (m[i - 1][j] || (j > 0 && m[i][j - 1]))
                        : (j > 0 && m[i - 1][j - 1] && pat[i - 1] == s[j - 1]);
      return bool(m[pat.size()][s.size()]);
    };
    size_t at = 0;
    while (at <= spec.size()) {
      size_t end = spec.find(';', at);
      if (end == std::string::npos) end = spec.size();
      const std::string item = spec.substr(at, end - at);
      at = end + 1;
      const size_t slash = item.find('/'), eq = item.find('=');
      if (slash == std::string::npos || eq == std::string::npos || eq < slash)
        continue;
      if (!match(item.substr(0, slash), d_.name)) continue;
      if (!match(item.substr(slash + 1, eq - slash - 1), name)) continue;
      const std::string t = item.substr(eq + 1);
      if (t == "affine") return Placement::kAffine;
      if (t == "quadratic") return Placement::kQuadratic;
      if (t == "circuit") return Placement::kCircuit;
      if (t == "batch") return Placement::kBatch;
    }
    return pin;
  }

  // ------------------------------------------------- batch candidates --

  // The kind of value a batch operand's leaf reads, by node: a public value
  // (a Bit, or any type), a bit view of committed words, a Bit cell of the
  // packed run, or a committed cell of any type.
  enum class LeafKind : uint8_t {
    kPublicBit,
    kPublic,
    kBitView,
    kRunBit,
    kCell
  };
  // Whether the tableau may have subfield rows (the column round's
  // subfield term, compiler/ligero_choice.h).
  bool subfield_rows() const { return d_.p_.has_subfield; }
  // Whether the domain packs bits (characteristic 2, relative packing).
  bool packs_bits() const {
    return F::kCharacteristicTwo && d_.has_subfield && relative_packing<F>() &&
           !d_.no_bit_packing;
  }
  // Under the no_bit_packing ablation in characteristic 2, a Bit cell is a
  // coordinate of the designated subfield, with an explicit Boolean check.
  bool unpacked_bits() const {
    return F::kCharacteristicTwo && d_.no_bit_packing;
  }
  // The kind and degree of the value node ID holds, or why a batch does
  // not read it.
  std::string base_kind(size_t id, LeafKind &k, size_t &deg) const {
    const Node &n = nodes()[id];
    if (is_public(n.kind)) {
      if (n.fobj != d_.fobj)
        return "it reads '" + n.name + "' of another field";
      if (n.type.base == Base::kBytes)
        return "it reads the Bytes statement '" + n.name + "'";
      k = n.type.base == Base::kBit ? LeafKind::kPublicBit : LeafKind::kPublic;
      deg = 0;
      return "";
    }
    if (n.domain != d_.index)
      return "it reads '" + n.name + "' of another domain";
    if (n.kind == Kind::kBitView) {
      const size_t w = n.deps.at(0);
      if (!plan_.cell(w) || nodes()[w].type.base != Base::kSubfield ||
          !in_subfield_region(w))
        return "it reads the bit view '" + n.name +
               "' of a value that is no phase-0 subfield cell";
      k = LeafKind::kBitView;
      deg = degree_of(w);
      return "";
    }
    if (plan_.late(id)) return "it reads the late value '" + n.name + "'";
    if (d_.exprs_.count(id))
      return "it reads the expression value '" + n.name + "'";
    if (plan_.bound.count(id))
      return "it reads '" + n.name + "', whose storage is a view";
    if (n.kind == Kind::kDerived)
      return "it reads the derived value '" + n.name + "'";
    if (!plan_.cell(id) || n.kind == Kind::kPad || n.kind == Kind::kPadCopy)
      return "it reads '" + n.name + "', which is no phase-0 cell";
    if (n.type.base == Base::kBit && packs_bits()) {
      k = LeafKind::kRunBit;
      deg = 1;
      return "";
    }
    k = LeafKind::kCell;
    deg = degree_of(id);
    return "";
  }
  // The leaves' kinds of the operands of Q, or why a batch does not read
  // them; a wiring view by its sources.
  std::string leaf_kinds(const BatchForm<F> &q,
                         std::set<std::pair<LeafKind, size_t>> &out) const {
    std::set<const ExprNode<F> *> seen;
    std::vector<const ExprNode<F> *> st;
    for (const auto &a : q.atoms) st.push_back(a.get());
    auto one = [&](size_t id) {
      LeafKind k;
      size_t deg = 0;
      const std::string why = base_kind(id, k, deg);
      if (why.empty()) out.insert({k, deg});
      return why;
    };
    while (!st.empty()) {
      const ExprNode<F> *x = st.back();
      st.pop_back();
      if (!seen.insert(x).second) continue;
      for (const auto &k : x->kids) st.push_back(k.get());
      if (x->op != ExprOp::kLin) continue;
      for (const auto &t : x->lin.terms) {
        auto w = d_.wiring_.find(t.node);
        if (w == d_.wiring_.end()) {
          const std::string why = one(t.node);
          if (!why.empty()) return why;
          continue;
        }
        std::set<size_t> bases;
        for (const auto &[node, c] : w->second)
          if (node != kZeroCoordinate) bases.insert(node);
        for (size_t b : bases) {
          const std::string why = one(b);
          if (!why.empty()) return why;
        }
      }
    }
    return "";
  }
  // The batch class of Q (its evaluator and the node degree of its
  // committed leaves), or why it has none.
  std::string batch_class(const BatchForm<F> &q, BatchEval &eval,
                          size_t &deg) const {
    std::set<std::pair<LeafKind, size_t>> kinds;
    const std::string why = leaf_kinds(q, kinds);
    if (!why.empty()) return why;
    bool bits = false, cells = false, pub_any = false;
    std::set<size_t> degrees;
    for (const auto &[k, d] : kinds) {
      if (k == LeafKind::kRunBit || k == LeafKind::kBitView) {
        bits = true;
        if (k == LeafKind::kBitView) degrees.insert(d);
      } else if (k == LeafKind::kCell) {
        cells = true;
        degrees.insert(d);
      } else if (k == LeafKind::kPublic) {
        pub_any = true;
      }
    }
    if (bits && (cells || pub_any))
      return "it reads Bit values and field values together";
    if (bits) {
      if (degrees.size() > 1)
        return "it reads the bits of words of several degrees";
      for (const auto &m : q.monos)
        if (m.coeff != d_.field().one())
          return "a coefficient of its polynomial lies outside GF(2)";
      eval = BatchEval::kBitSliced;
      // Bit views' words, or the packed run's (the designated subfield's).
      deg = degrees.empty() ? designated_degree<F>() : *degrees.begin();
      if (deg != 8 && deg != 16 && deg != 32)
        return "it reads the bits of GF(2^" + std::to_string(deg) +
               ") words; bit batches read words of 8, 16 or 32 bits";
      return "";
    }
    if (!cells) return "it reads no committed value";
    if (degrees.size() > 1)
      return "its cells lie in subfields of several degrees";
    deg = *degrees.begin();
    eval = deg < field_degree<F>() ? BatchEval::kSubfield : BatchEval::kField;
    return "";
  }
  // The packing tree's chains by cost: for the
  // designated subfield's node B, when it is declared and its default path
  // reaches K through intermediates only, when the edge B < K has more than one admissible chain
  // (PackingTree::candidates) and the domain's placement rates are
  // measured, the chain of least fitted packing cost (the stage rates,
  // prover plus verifier) at the domain's N, B's region in B-coordinates
  // (its own values and its children's words), and M, the positions
  // outside it, unless that beats the default chain by no more than
  // kDefaultMarginPercent; a candidate without a rate takes no part in
  // the choice, and without the default's rate the edge keeps it.
  // Every other edge (GF(2)'s bit stage, a further declared subfield's)
  // keeps its default chain, a forced edge (CompileOptions::forced_chains)
  // its forced chain, and a profile without measured rates or under the
  // unpacked_s0 ablation the default tree.
  // NOTE gets one report line per weighed edge: each candidate's modeled
  // cost and the chain taken.
  std::map<std::pair<size_t, size_t>, std::vector<size_t>> choose_chains(
      const std::vector<size_t> &declared, const std::vector<size_t> &sub,
      const std::vector<size_t> &packed, const std::vector<size_t> &full,
      std::string &note) const {
    std::map<std::pair<size_t, size_t>, std::vector<size_t>> chosen;
    // The provisional pass keeps the default tree, and so does the
    // unpacked_s0 ablation, which commits a root child unpacked.
    if (provisional_pass() || d_.p_.unpacked_s0) return chosen;
    const auto &N = nodes();
    const size_t s0 = designated_degree<F>(), nK = field_degree<F>();
    const PackingTree base =
        PackingTree::plan(nK, s0, F::kCharacteristicTwo, declared, d_.p_.d_max,
                          {}, &plan_.options.forced_chains);
    if (!base.error.empty()) return chosen;
    // Each node's region, bottom up: its own coordinates and its children's
    // groups.
    std::vector<double> region(base.nodes.size(), 0);
    for (size_t id : sub) {
      const int x = base.node_of(degree_of(id));
      if (x > 0) region[size_t(x)] += double(N[id].n);
    }
    for (size_t id : packed) {
      const int x = base.node_of(1);
      if (x > 0) region[size_t(x)] += double(N[id].n);
    }
    double L = 0;
    for (size_t id : full) L += double(N[id].n);
    for (int x : base.bottom_up()) {
      const auto &nd = base.nodes[size_t(x)];
      const double d = double(base.nodes[size_t(nd.parent)].degree / nd.degree);
      if (nd.parent != 0) region[size_t(nd.parent)] += std::ceil(region[size_t(x)] / d);
      L += region[size_t(x)];
    }
    const PlacementRates &rates = d_.p_.rates;
    for (size_t x = 1; x < base.nodes.size(); ++x) {
      const auto &nd = base.nodes[x];
      if (!nd.declared) continue;
      if (nd.degree != s0) continue;
      bool through = true;
      double chain_region = region[x];
      for (int u = nd.parent; u != 0; u = base.nodes[size_t(u)].parent) {
        if (base.nodes[size_t(u)].declared) through = false;
        chain_region += region[size_t(u)];
      }
      if (!through) continue;
      // A forced chain (CompileOptions::forced_chains) takes the edge
      // without a choice.
      if (plan_.options.forced_chains.count({nd.degree, nK}) != 0) continue;
      const auto cands = base.candidates(nd.degree, nK);
      if (cands.size() < 2 || !rates.measured()) continue;
      const double n = region[x], m = L - chain_region;
      std::vector<double> cost;
      std::vector<bool> priced;
      std::vector<std::string> names;
      for (const auto &c : cands) {
        std::string nm;
        for (size_t dg : c) nm += (nm.empty() ? "" : "<") + std::to_string(dg);
        names.push_back(nm);
        record_rate_request(rates.field, "stage " + nm);
        const auto *r = rates.stage.find(c);
        priced.push_back(r != nullptr);
        cost.push_back(r ? r->prover(n, m) + r->verifier(n, m) : 0);
      }
      size_t best = 0;
      for (size_t i = 1; i < cands.size(); ++i)
        if (priced[i] && (!priced[best] || cost[i] < cost[best])) best = i;
      const size_t taken = best != 0 && priced[0] && priced[best] &&
                                   beats_default(cost[best], cost[0])
                               ? best
                               : 0;
      if (taken != 0) chosen[{nd.degree, nK}] = cands[taken];
      std::ostringstream o;
      o << "    chains by cost at N=" << n << " M=" << m
        << " (us, prover + verifier):";
      for (size_t i = 0; i < cands.size(); ++i) {
        char us[32];
        if (priced[i])
          std::snprintf(us, sizeof(us), "%.1f", cost[i]);
        else
          std::snprintf(us, sizeof(us), "no rates");
        o << (i == 0 ? " " : ", ") << names[i] << " " << us
          << (i == 0 ? " (default)" : "");
      }
      o << "; taken " << names[taken] << "\n";
      note += o.str();
    }
    return chosen;
  }

  // The skip width of a batch of class EVAL: 16 bit-sliced, 4 otherwise
  // (the widths the batch rates are measured at).
  static unsigned batch_width(BatchEval eval) {
    return eval == BatchEval::kBitSliced ? 16 : 4;
  }
  // The width a placed batch's kernel runs at: WIDTH, or 1 under the
  // test-only univariate-skip ablation (DomainProfile::no_skip), where the
  // first round is a multilinear round like the others.
  unsigned kernel_width(unsigned width) const {
    return d_.p_.no_skip ? 1u : width;
  }
  // Why Q of class EVAL is no batch at skip width WIDTH, or "": its points
  // fit the skip domain, its operand count the evaluator, and its operands
  // are affine views.
  std::string batch_shape_error(const BatchForm<F> &q, BatchEval eval,
                                unsigned width) const {
    const unsigned D = q.degree();
    const size_t pts = size_t(D) * (width - 1) + 1;
    if (F::kCharacteristicTwo && pts > 256)
      return "of degree " + std::to_string(D) + ": D (w - 1) + 1 = " +
             std::to_string(pts) +
             " skip points exceed the 256 of the binary skip subfield";
    if (!F::kCharacteristicTwo &&
        !characteristic_above(d_.field(), Bound(pts)))
      return "of degree " + std::to_string(D) +
             ": its skip points exceed the characteristic";
    if (eval == BatchEval::kBitSliced && q.atoms.size() > kMaxBitOperands)
      return "it has " + std::to_string(q.atoms.size()) + " operands";
    // The operands' views, every leaf read as zeros.
    std::string why;
    const LeafResolver none = [this](size_t id,
                                     const std::vector<size_t> *coords,
                                     std::vector<SourceRef> &r,
                                     std::string &) {
      r.assign(coords ? coords->size() : nodes()[id].n, SourceRef{});
      return true;
    };
    if (!view_dag<F>(d_.field(), q.atoms, none,
                     eval == BatchEval::kBitSliced, why))
      return why;
    return "";
  }
  // The proof bytes of one committed coordinate, through Ligero's opened
  // columns at an estimated tableau: a coordinate takes 1 / k of a row, and
  // each opened column holds one element of each row; k balances the rows
  // against the opened columns.
  double coord_bytes() const {
    size_t nw = 0;
    for (size_t id = 0; id < nodes().size(); ++id)
      if (nodes()[id].domain == d_.index && plan_.cell(id))
        nw += in_subfield_region(id) ? (nodes()[id].n + 7) / 8
                                     : nodes()[id].n;
    double opened = double(d_.p_.opened());
    double k = 64;
    while (k * k < double(nw) * opened) k *= 2;
    // Under a target, the opened columns of the estimated tableau (N, k) =
    // (rate k, k), to a fixed point of the estimate.
    for (size_t it = 0; d_.p_.target && it < 4; ++it) {
      const auto c = compiler::choose_ligero_half(
          d_.p_.rate * size_t(k), size_t(k), compiler::field_order(d_.field()),
          d_.p_.target_half(), subfield_rows());
      if (!c || double(c->t) == opened) break;
      opened = double(c->t);
      k = 64;
      while (k * k < double(nw) * opened) k *= 2;
    }
    return opened * double(F::kBytes) / k;
  }
  // The domain's own rounds besides Ligero's, as numerators over |K|, each
  // charged on its own (the Lean's FieldRoundsLe, formal
  // GordieHowe/ProofSystem/Program/FieldDomain.lean; ForkFigures.lean's
  // batchesNum; FieldClaim.lean's gkrRoundError):
  //   batches       its batches' errors summed: per batch r + D (w - 1) +
  //                 (D + 1) r + 1 (r rounds, degree D, width w), the
  //                 merging challenge's parts - 1 when merged, and 2 per
  //                 bit-phase round;
  //   gkr           a GKR round, max(3, 2 gkrWidth), gkrWidth = clog2
  //                 max(wires, inputs) (0 without GKR);
  //   combinations  one per packing combination (edge of the packing tree);
  //   phases        per phase, the exact numerators (CompilePlan::charges)
  //                 of its challenges drawn in the domain's field, summed:
  //                 at most the Lean's phaseError times |K|, so a tableau
  //                 planned at it keeps every round at most the phase's.
  struct OwnRounds {
    uint64_t batches = 0, gkr = 0, combinations = 0;
    std::map<size_t, Bound> phases;
  };
  OwnRounds own_rounds() const {
    OwnRounds r;
    for (const auto &bp : bplan_) {
      const auto sh = bp.kernel->shape();
      const uint64_t rounds = sh.rounds, deg = sh.degree;
      r.batches += rounds + deg * (uint64_t(sh.width) - 1) + (deg + 1) * rounds + 1;
      if (sh.parts.size() > 1) r.batches += sh.parts.size() - 1;
      r.batches += 2 * uint64_t(bp.kernel->bit_phase_rounds());
    }
    if (gkr_) {
      size_t wires = 0;
      for (const auto &layer : circ_->l) wires += layer.nw;
      const size_t m = std::max(wires, size_t(circ_->ninputs));
      size_t w = 0;
      while (w < 64 && (uint64_t{1} << w) < m) ++w;
      r.gkr = std::max<uint64_t>(3, 2 * w);
    }
    r.combinations = uint64_t(tree_.bottom_up().size());
    for (const auto &c : plan_.charges)
      if (c.field == d_.field_id && c.fobj == d_.fobj)
        r.phases[c.phase] += c.exact;
    return r;
  }
  // The largest of the domain's own rounds besides Ligero's: the masked
  // inner-product rounds, the test round's 1 and the phases' sums, as a
  // numerator over |K|, saturated.
  uint64_t own_round_max(const OwnRounds &r) const {
    uint64_t m = std::max({r.batches, r.gkr, r.combinations, uint64_t(1)});
    for (const auto &[ph, num] : r.phases)
      m = std::max(m, num > Bound(UINT64_MAX) ? UINT64_MAX : uint64_t(num));
    return m;
  }
  // Every masked inner-product round of the domain (its batches summed, a
  // GKR round, its packing combinations) and each phase's challenges in
  // the domain's field meet the target the tableau C was planned at,
  // exactly: numerator <= floor(|K| / 2^(HALF/2)), or <= GOAL_NUM at a
  // fallback. A miss fails the compile.
  void check_own_rounds(const compiler::LigeroChoice &c) const {
    const auto order = compiler::field_order(d_.field());
    const size_t half = c.half;
    const uint64_t budget =
        c.goal_num != 0 ? c.goal_num : compiler::power_budget(order, half, 1);
    const OwnRounds r = own_rounds();
    const std::string goal =
        c.goal_num != 0 ? std::to_string(c.goal_num) + "/|K|"
                        : "2^-" + std::to_string(half / 2) +
                              (half % 2 ? ".5" : "");
    auto need = [&](const char *what, uint64_t num) {
      if (num > budget)
        fail("domain " + d_.name + ": its " + what + " round, " +
             std::to_string(num) + "/|K|, exceeds the Ligero target " + goal +
             " (each round is charged on its own)");
    };
    need("batches", r.batches);
    need("GKR", r.gkr);
    need("packing combinations", r.combinations);
    for (const auto &[ph, num] : r.phases)
      if (num > Bound(budget))
        fail("domain " + d_.name + ": phase " + std::to_string(ph) +
             "'s challenges in its field exceed the Ligero target " + goal);
  }
  // The Ligero parameters of the domain under its profile's target: over
  // the profile's block grid and the low-degree repetitions rho in {1, 2,
  // 3}, each candidate block_enc's tableau (N, k) at the profile's rate
  // with the opened columns, masking and agreement threshold of
  // compiler::choose_ligero at rho (whose column round meets the target
  // on its own), and of those the one
  // with the smallest predicted proof. The prediction is LigeroParam's
  // estimate at the candidate's opened columns, masking and repetitions,
  // for the committed size of the tree's layout at the candidate's row
  // width (the subfield prefix padded to whole rows), with the subfield
  // rows' opened entries at the subfield's width and the others at the
  // field's. Candidates are evaluated in the order of their estimate at a
  // lower bound on t (the column round at the least threshold A = k), until
  // that bound cannot beat the best. The repetitions: rho = 1 unless a
  // larger rho predicts a proof more than 5% smaller (kLdtRepsSaving), and
  // then the rho of the smallest prediction.
  static constexpr double kLdtRepsSaving = 0.05;
  static constexpr size_t kMaxLdtReps = 3;
  compiler::LigeroChoice choose_tableau(const TreeInputs &ti) const {
    const F &f = d_.field();
    const auto order = compiler::field_order(f);
    const compiler::LigeroTarget target = *d_.p_.target;
    const size_t rate = d_.p_.rate;
    const size_t gkr_pads = ZkCommon<F>::pad_size(*circ_);
    const TreeLayout<F> unaligned(f, tree_, ti, circ_->ninputs, circ_->npub_in,
                                  gkr_pads, 0, d_.p_.unpacked_s0);
    const size_t nq =
        circ_->nl + unaligned.nquad + circ_->input_products.size();
    const bool packed = !tree_.nodes[0].children.empty();
    const size_t sub_cells = unaligned.prefix + unaligned.nflat;
    // The predicted bytes of block_enc E at T opened columns, MASKING and
    // REPS low-degree repetitions.
    auto bytes = [&](size_t e, size_t t, LigeroMasking masking,
                     size_t reps) -> uint64_t {
      const size_t k = (e + 1) / (rate + 2);
      if (k <= t) return UINT64_MAX;
      const size_t w = k - t;
      const size_t prefix_padded = (sub_cells + w - 1) / w * w;
      const size_t nw =
          packed ? unaligned.nw - sub_cells + prefix_padded : unaligned.nw;
      LigeroParam<F, Hash> p(nw, nq, rate, t,
                             LigeroMode{true, masking, reps});
      const size_t sz = p.layout(e);
      if (sz == SIZE_MAX) return UINT64_MAX;
      const uint64_t sub_rows = packed ? prefix_padded / w : 0;
      const uint64_t all_sub = uint64_t(p.nrow) * t * F::kSubFieldBytes;
      const uint64_t exact =
          uint64_t(t) * (sub_rows * F::kSubFieldBytes +
                         (uint64_t(p.nrow) - sub_rows) * F::kBytes);
      return uint64_t(sz) - all_sub + exact;
    };
    // The search at the target 2^-(HALF/2), or GOAL_NUM/|K| when nonzero.
    auto search = [&](size_t half, uint64_t goal_num)
        -> std::optional<compiler::LigeroChoice> {
      // The least t at which the column round alone, at A = k, meets the
      // target with split masks: no choice at (N, k) opens fewer.
      auto t_lower = [&](size_t N, size_t k) -> size_t {
        const long double goal =
            goal_num != 0 ? (long double)goal_num *
                                std::exp2l(-(long double)order.log2())
                          : std::exp2l(-(long double)half / 2);
        for (size_t t = 1; t <= k; ++t) {
          long double r = 1, m = 1;
          for (size_t i = 0; i < t; ++i) {
            r *= (long double)(k - 1 - i) / (N - i);
            m *= (long double)(2 * k - 1 - i) / (N - i);
          }
          if (r + m <= goal) return t;
        }
        return k;
      };
      struct Cand {
        uint64_t bound;
        size_t e, N, k;
      };
      // The best choice at REPS repetitions and its predicted bytes.
      auto best_at = [&](size_t reps)
          -> std::pair<std::optional<compiler::LigeroChoice>, uint64_t> {
        std::vector<Cand> cands;
        const std::vector<size_t> grid =
            d_.p_.block_enc_fixed != 0
                ? std::vector<size_t>{d_.p_.block_enc_fixed}
                : compiler::block_candidates(d_.p_.block_grid, rate,
                                             d_.p_.max_block_enc);
        for (size_t e : grid) {
          const auto nk = compiler::tableau_of(e, rate);
          if (!nk) continue;
          const auto [N, k] = *nk;
          const size_t tl = t_lower(N, k);
          // The bound at untested masks is no lower (four fewer rows, more
          // columns), so split masks bound both.
          const uint64_t b =
              std::min(bytes(e, tl, LigeroMasking::kSplit, reps),
                       bytes(e, tl, LigeroMasking::kUntested, reps));
          if (b != UINT64_MAX) cands.push_back({b, e, N, k});
        }
        std::stable_sort(
            cands.begin(), cands.end(),
            [](const Cand &a, const Cand &b) { return a.bound < b.bound; });
        std::optional<compiler::LigeroChoice> best;
        uint64_t best_bytes = UINT64_MAX;
        size_t best_e = 0;
        // Both maskings, split masks first (they keep a tie), or the
        // ablation's forced one (CompileOptions::ligero_masking).
        const auto forced = plan_.options.ligero_masking;
        const std::vector<LigeroMasking> maskings =
            forced ? std::vector<LigeroMasking>{*forced}
                   : std::vector<LigeroMasking>{LigeroMasking::kSplit,
                                                LigeroMasking::kUntested};
        for (const Cand &c : cands) {
          if (c.bound > best_bytes) break;
          for (const LigeroMasking m : maskings) {
            const auto lc = compiler::choose_ligero_half(
                c.N, c.k, order, half, subfield_rows(), reps, m, goal_num);
            if (!lc) continue;
            const uint64_t b = bytes(c.e, lc->t, lc->masking, reps);
            if (b < best_bytes || (b == best_bytes && c.e < best_e)) {
              best = lc;
              best_bytes = b;
              best_e = c.e;
            }
          }
        }
        return {best, best_bytes};
      };
      std::optional<compiler::LigeroChoice> best;
      uint64_t best_bytes = UINT64_MAX;
      // rho = 1's prediction (UINT64_MAX when rho = 1 has no choice).
      uint64_t base_bytes = UINT64_MAX;
      // Forced repetitions (CompileOptions): this domain's (by name), else
      // every domain's, else none.
      const auto &by_domain = plan_.options.domain_ldt_reps;
      const auto own = by_domain.find(d_.name);
      const size_t forced =
          own != by_domain.end() ? own->second : plan_.options.ldt_reps;
      for (size_t reps = 1; reps <= kMaxLdtReps; ++reps) {
        if (forced != 0 && reps != forced) continue;
        const auto [lc, b] = best_at(reps);
        if (!lc) continue;
        if (reps == 1) base_bytes = b;
        // rho > 1 replaces the choice only when more than 5% smaller than
        // rho = 1's (or when rho = 1 has none), and smaller than the best.
        const bool saves =
            best && double(b) < (1 - kLdtRepsSaving) * double(base_bytes) &&
            b < best_bytes;
        if (!best || saves) {
          best = lc;
          best_bytes = b;
        }
      }
      if (best) best->half = half;
      return best;
    };
    const size_t half = compiler::target_half(target);
    // The fallback: a domain at
    // the
    // classical target 2^-113.5 one of whose own rounds besides Ligero's
    // (own_round_max: its masked inner-product rounds, the test round, and
    // per phase the challenges drawn in its field) exceeds it is planned
    // at the largest of them, OWN/|K|, its field-limited ceiling: no round
    // of the domain is then above that round.
    const uint64_t own = own_round_max(own_rounds());
    const bool out_of_reach = own > compiler::power_budget(order, half, 1);
    const bool fallback =
        out_of_reach && target == compiler::LigeroTarget::kClassical;
    auto best = search(half, fallback ? own : 0);
    if (!best)
      fail("domain " + d_.name + ": no tableau on its block grid meets the " +
           "Ligero target 2^-" + std::to_string(half / 2) +
           (half % 2 ? ".5" : "") +
           (fallback ? " or its fallback " + std::to_string(own) + "/|K|"
                     : std::string()));
    best->fallback = fallback;
    best->goal_num = fallback ? own : 0;
    best->ip_bits = double(order.log2()) - std::log2(double(own));
    return *best;
  }
  // The counted bytes of a batch of N instances, K operands and degree D at
  // skip WIDTH: its messages, and its pads as committed coordinates.
  double batch_bytes(size_t n, unsigned k, unsigned d, unsigned width) const {
    FieldRelation<F> rel;
    rel.operands = k;
    std::vector<unsigned> m(d);
    for (unsigned j = 0; j < d; ++j) m[j] = j % k;
    std::sort(m.begin(), m.end());
    rel.monomials = {{d_.field().one(), m}};
    for (unsigned j = 0; j < k; ++j)
      rel.monomials.push_back({d_.field().one(), {j}});
    const MaskedFieldSkip<F> sk(d_.field(), rel, n, width);
    return double(sk.message_elts() * F::kBytes) +
           double(sk.layout.count) * coord_bytes();
  }
  // The counted bytes of DEPTH layers of a circuit of TERMS quad terms:
  // per layer its sumcheck rounds (two per input bit, three elements each)
  // and its claims.
  static double circuit_bytes(size_t depth, size_t terms) {
    size_t lg = 1;
    while ((size_t(1) << lg) < terms) ++lg;
    return double(depth) * double(2 * lg * 3 + 4) * double(F::kBytes);
  }
  // A key of E's structure for its circuit cost: its operations and sizes,
  // each view by its size (a view is wiring, so which coordinates it reads
  // costs no term), constants by value (put_values). A plain leaf (one
  // term, no operator) has no size of its own: the circuit gives each
  // coordinate the predicate reads an input, and the others one shared
  // input no gate reads, so its size changes the inputs only; an operation
  // that reads its operands whole (any but a view) carries their sizes.
  // Predicates of one structure share their circuit cost.
  std::vector<uint8_t> structure_key(const ExprPtr<F> &e) const {
    std::vector<uint8_t> out;
    std::map<const ExprNode<F> *, size_t> index;
    auto plain = [](const ExprNode<F> &x) {
      return x.op == ExprOp::kLin && x.lin.terms.size() == 1 &&
             x.lin.terms[0].chain.empty();
    };
    std::function<size_t(const ExprNode<F> &)> go =
        [&](const ExprNode<F> &x) -> size_t {
      auto it = index.find(&x);
      if (it != index.end()) return it->second;
      std::vector<size_t> kids;
      for (const auto &k : x.kids) kids.push_back(go(*k));
      put_u64(out, uint64_t(x.op));
      put_u64(out, plain(x) ? 0 : x.n);
      put_u64(out, x.w);
      put_u64(out, (x.imm ? 1 : 0) | (x.bit ? 2 : 0));
      put_u64(out, x.value);
      put_u64(out, kids.size());
      for (size_t k : kids) put_u64(out, k);
      if (x.op != ExprOp::kGather)
        for (const auto &k : x.kids) put_u64(out, k->n);
      if (x.op == ExprOp::kLin) {
        put_u64(out, x.lin.terms.size());
        for (const auto &t : x.lin.terms) {
          put_u64(out, plain(x) ? uint64_t(t.in_n == x.n) : t.in_n);
          put_u64(out, t.chain.size());
          for (const auto &op : t.chain) put_str(out, op->name);
        }
      }
      if (x.op == ExprOp::kApply) put_str(out, x.apply->name);
      if (x.op == ExprOp::kConst || x.op == ExprOp::kScale) {
        if (x.has_cdigest) {
          out.insert(out.end(), x.cdigest.begin(), x.cdigest.end());
        } else {
          put_values(d_.field(), out, x.c);
        }
      }
      const size_t k = index.size();
      index[&x] = k;
      return k;
    };
    go(*e);
    // The predicate's size (a plain leaf's own is left out above).
    put_u64(out, e->n);
    return out;
  }
  // The coordinates of each node expression E reads through its affine
  // leaves (a superset): coordinate i of a view reads the coordinates its
  // index maps name, of a group operation the group, of a coordinatewise
  // operation the same coordinate; anything else reads every coordinate.
  static std::map<size_t, std::vector<bool>> read_coordinates(
      const ExprPtr<F> &e) {
    std::vector<const ExprNode<F> *> order;
    std::set<const ExprNode<F> *> seen;
    std::function<void(const ExprNode<F> &)> visit =
        [&](const ExprNode<F> &x) {
          if (!seen.insert(&x).second) return;
          for (const auto &k : x.kids) visit(*k);
          order.push_back(&x);
        };
    visit(*e);
    std::map<const ExprNode<F> *, std::vector<bool>> want;
    want[e.get()].assign(e->n, true);
    std::map<size_t, std::vector<bool>> out;
    for (size_t q = order.size(); q-- > 0;) {
      const ExprNode<F> &x = *order[q];
      auto it = want.find(&x);
      if (it == want.end()) continue;
      const std::vector<bool> &dm = it->second;
      auto mark = [&](const ExprNode<F> &k, size_t j) {
        auto &v = want[&k];
        if (v.empty()) v.assign(k.n, false);
        v[j] = true;
      };
      auto all = [&](const ExprNode<F> &k) { want[&k].assign(k.n, true); };
      switch (x.op) {
        case ExprOp::kLin:
          for (const auto &t : x.lin.terms) {
            auto &v = out[t.node];
            if (v.empty()) v.assign(t.in_n, false);
            if (!t.chain.empty() || t.in_n != x.n) {
              v.assign(t.in_n, true);
              continue;
            }
            for (size_t i = 0; i < x.n; ++i)
              if (dm[i]) v[i] = true;
          }
          break;
        case ExprOp::kConst:
          break;
        case ExprOp::kGather:
          for (size_t i = 0; i < x.n; ++i) {
            if (!dm[i]) continue;
            size_t j = x.idx[i], k = 0;
            while (j >= x.kids[k]->n) j -= x.kids[k++]->n;
            mark(*x.kids[k], j);
          }
          break;
        case ExprOp::kBroadcast:
          for (size_t i = 0; i < x.n; ++i)
            if (dm[i]) mark(*x.kids[0], i % x.kids[0]->n);
          break;
        case ExprOp::kSum:
        case ExprOp::kProd:
        case ExprOp::kAny:
        case ExprOp::kAll:
        case ExprOp::kLt:
        case ExprOp::kLeq:
        case ExprOp::kEq:
          // Groups of G contiguous coordinates of each kid.
          for (const auto &k : x.kids) {
            if (x.n == 0 || k->n % x.n != 0) {
              all(*k);
              continue;
            }
            const size_t g = k->n / x.n;
            for (size_t i = 0; i < x.n; ++i)
              if (dm[i])
                for (size_t j = 0; j < g; ++j) mark(*k, i * g + j);
          }
          break;
        case ExprOp::kAdd:
        case ExprOp::kScale:
        case ExprOp::kMul:
        case ExprOp::kNot:
        case ExprOp::kAnd:
        case ExprOp::kOr:
        case ExprOp::kXor:
        case ExprOp::kMux:
        case ExprOp::kMaterialize:
          for (const auto &k : x.kids) {
            if (k->n != x.n) {
              all(*k);
              continue;
            }
            for (size_t i = 0; i < x.n; ++i)
              if (dm[i]) mark(*k, i);
          }
          break;
        default:
          for (const auto &k : x.kids) all(*k);
          break;
      }
    }
    return out;
  }

  // The quad terms and layers of predicate P alone, emitted as the circuit
  // would, its cells read as inputs: the coordinates it reads, each its own
  // input; the rest one shared input, which nothing the predicate checks
  // reads (so a predicate over a few coordinates of a large cell does not
  // build the cell's every input).
  std::pair<size_t, size_t> predicate_terms(
      const typename D::PredDecl &p) const {
    const std::vector<Node> &N = nodes();
    QuadCircuit<F> Q(d_.field());
    const typename D::Backend cbk(&Q);
    const CLogic lc(&cbk, d_.field());
    Q.private_input();
    const auto reads = read_coordinates(p.e);
    std::optional<typename Wires::value_type> unread;
    std::map<size_t, Wires> in;
    ExprEmitter<F, CLogic> em(lc, [&](const Term<F> &t) {
      auto it = in.find(t.node);
      if (it == in.end()) {
        Wires w(N[t.node].n);
        const auto r = reads.find(t.node);
        for (size_t i = 0; i < w.size(); ++i) {
          if (r == reads.end() || i >= r->second.size() || r->second[i]) {
            w[i] = lc.eltw_input();
            continue;
          }
          if (!unread) unread = lc.eltw_input();
          w[i] = *unread;
        }
        it = in.emplace(t.node, std::move(w)).first;
      }
      Wires w = it->second;
      for (const auto &op : t.chain) w = expand(lc, *op, w);
      return w;
    });
    em.lean_views(true);
    if (p.truth)
      em.assert_true(p.e);
    else
      em.assert_zero(p.e);
    return Q.mkcircuit_size(/*nc=*/1);
  }

  // The kernel of batch group G: its operand map from the predicates'
  // views, after the cells are laid out (a Bit cell's source is its place
  // in the packed run).
  std::shared_ptr<BatchKernel<F, Hash>> group_kernel(const Group &g) {
    std::vector<BatchSpace> spaces;
    auto ops = group_operands(d_.field(), g, false, spaces);
    group_spaces_.push_back(spaces);
    return std::make_shared<BatchKernel<F, Hash>>(
        d_.field(), std::move(ops), kernel_width(g.width), d_.p_.bit_phase);
  }
  // The work of one proof of group G as the placement rule weighs it
  // (op_counts.h): its kernel over CountingField<F>, its operand map built
  // from the views before the cells are laid out, each node read as a
  // table of its own (PROVISIONAL in group_operands).
  OpCounts group_work(const Group &g) const {
    const CountingField<F> cf(d_.field());
    std::vector<BatchSpace> spaces;
    const auto t0 = std::chrono::steady_clock::now();
    auto ops = group_operands(cf, g, true, spaces);
    const auto t1 = std::chrono::steady_clock::now();
    const OpCounts c = batch_ops<F, Hash>(cf, std::move(ops), g.width);
    const auto t2 = std::chrono::steady_clock::now();
    // The count_times switch (util/diagnostics.h): each candidate's map
    // build and count times (ms).
    if (diagnostics::options().count_times)
      std::fprintf(stderr, "GH_COUNT_TIME group=%s n=%zu map=%.1f count=%.1f\n",
                   g.name.c_str(), g.n,
                   std::chrono::duration<double, std::milli>(t1 - t0).count(),
                   std::chrono::duration<double, std::milli>(t2 - t1).count());
    return c;
  }
  // The operands of batch group G over the field FG (F, or
  // CountingField<F>): its operand map from the predicates' views, SPACES
  // the spaces they read. PROVISIONAL (before the cells are laid out):
  // every node read is a table of its own, its coordinates (bits, for a
  // bit-sliced batch) in order.
  template <class G>
  std::shared_ptr<const BatchOperands<G>> group_operands(
      const G &fg, const Group &g, bool provisional,
      std::vector<BatchSpace> &spaces) const {
    const std::vector<Node> &N = nodes();
    const F &f = d_.field();
    const bool bits = g.eval == BatchEval::kBitSliced;
    spaces.clear();
    std::map<size_t, uint32_t> space_of;
    auto space = [&](BatchSpace::Kind k, size_t node, size_t size) {
      auto it = space_of.find(node);
      if (it == space_of.end()) {
        it = space_of.emplace(node, uint32_t(spaces.size())).first;
        spaces.push_back(BatchSpace{k, node, size});
      }
      return it->second;
    };
    // Where node ID's coordinates lie as sources: its space (registered at
    // its first use) and the place of its coordinate 0 there, or, for a bit
    // view, its selection of its source's words.
    struct Base {
      uint32_t space = 0;
      size_t first = 0;
      size_t D = 0;
      const std::vector<size_t> *sel = nullptr;
    };
    auto base_of = [&](size_t id) -> Base {
      const Node &n = N[id];
      if (is_public(n.kind)) return {space(BatchSpace::kPublic, id, n.n)};
      if (n.kind == Kind::kBitView) {
        const size_t w = n.deps.at(0);
        const size_t D = degree_of(w);
        return {space(BatchSpace::kTable, w, D * N[w].n), 0, D,
                &d_.views_.at(id)};
      }
      if (provisional) return {space(BatchSpace::kTable, id, n.n)};
      if (bits) {
        // The packed run's groups are words of the bit node's parent.
        if (word_bits_ != g.word_degree)
          fail("batch '" + g.name + "' reads the packed run's bits, words of " +
               std::to_string(word_bits_) + " bits, and bits of GF(2^" +
               std::to_string(g.word_degree) + ") words");
        return {space(BatchSpace::kTable, BatchSpace::kRun,
                      run_end_ - run_begin_),
                cells_.at(id) - run_begin_};
      }
      return {space(BatchSpace::kTable, id, n.n)};
    };
    // Coordinate C of a node at B as a source.
    auto ref_at = [](const Base &b, size_t c) -> SourceRef {
      if (b.sel != nullptr)
        return {b.space, b.D * b.sel->at(c / b.D) + c % b.D};
      return {b.space, b.first + c};
    };
    const LeafResolver resolve = [&](size_t id,
                                     const std::vector<size_t> *coords,
                                     std::vector<SourceRef> &r,
                                     std::string &) {
      r.clear();
      auto w = d_.wiring_.find(id);
      const size_t n = coords ? coords->size() : N[id].n;
      r.reserve(n);
      if (w == d_.wiring_.end()) {
        if (n == 0) return true;
        const Base b = base_of(id);
        for (size_t i = 0; i < n; ++i)
          r.push_back(ref_at(b, coords ? (*coords)[i] : i));
        return true;
      }
      // A wired node's coordinates lie in other nodes, runs of one node
      // in the common case: the last node's base is kept.
      size_t last = kZeroCoordinate;
      Base b;
      for (size_t i = 0; i < n; ++i) {
        const size_t c = coords ? (*coords)[i] : i;
        const auto &[node, k] = w->second.at(c);
        if (node == kZeroCoordinate) {
          r.push_back(SourceRef{});
          continue;
        }
        if (node != last) {
          b = base_of(node);
          last = node;
        }
        r.push_back(ref_at(b, k));
      }
      return true;
    };
    // Each predicate's views, resolved (the spaces they read registered at
    // first use) and added to MAP, which learns the new spaces first; one
    // predicate's views are held at a time.
    auto add_one = [&](auto &map, const std::vector<ExprPtr<F>> &atoms,
                       const std::string &name) {
      std::string why;
      const auto dag = view_dag<F>(f, atoms, resolve, bits, why);
      if (!dag) fail("predicate '" + name + "' in a batch: " + why);
      for (size_t s = map.spaces().size(); s < spaces.size(); ++s)
        map.add_space(spaces[s]);
      map.add(*dag, name);
    };
    auto add_all = [&](auto &map) {
      if (!bits) {
        for (size_t k : g.preds)
          add_one(map, pplan_[k].form->atoms, d_.preds_[k].name);
        return;
      }
      // Bit-sliced: the predicates of one form over the same values (a
      // hash's round at every round of a block, say), in order, merge into
      // instances of up to kMergeCoordinates coordinates, each operand the
      // concatenation of theirs. Their conjunction is the same relation;
      // an instance's lanes read consecutive rows where the predicates read
      // consecutive rows of the same values, and the map's work per
      // instance (the lane programs' steps, the weights) is paid once per
      // merged instance. The key (the values read, the size, each operand's
      // operation and size) is a cheap stand-in for the structure: two
      // predicates of one key but another structure merge into a larger
      // template, which is the same relation.
      constexpr size_t kMergeCoordinates = 2048;
      std::vector<std::vector<uint8_t>> keys;
      std::map<std::vector<uint8_t>, std::vector<size_t>> runs;
      for (size_t k : g.preds) {
        std::vector<uint8_t> key;
        put_u64(key, d_.preds_[k].e->n);
        for (const auto &a : pplan_[k].form->atoms) {
          put_u64(key, uint64_t(a->op));
          put_u64(key, a->kids.size());
        }
        for (size_t id : expr_deps(d_.preds_[k].e)) put_u64(key, id);
        auto [it, fresh] = runs.try_emplace(key);
        if (fresh) keys.push_back(key);
        it->second.push_back(k);
      }
      for (const auto &key : keys) {
        const std::vector<size_t> &ks = runs.at(key);
        for (size_t i = 0; i < ks.size();) {
          size_t j = i, n = 0;
          while (j < ks.size() &&
                 (j == i || n + d_.preds_[ks[j]].e->n <= kMergeCoordinates)) {
            n += d_.preds_[ks[j]].e->n;
            ++j;
          }
          if (j == i + 1) {
            add_one(map, pplan_[ks[i]].form->atoms, d_.preds_[ks[i]].name);
            i = j;
            continue;
          }
          // Operand a of the instance: the predicates' operands a, side by
          // side (a view of them).
          std::vector<ExprPtr<F>> atoms;
          for (size_t a = 0; a < pplan_[ks[i]].form->atoms.size(); ++a) {
            std::vector<ExprPtr<F>> parts;
            for (size_t q = i; q < j; ++q)
              parts.push_back(pplan_[ks[q]].form->atoms.at(a));
            std::vector<size_t> idx(n);
            for (size_t c = 0; c < n; ++c) idx[c] = c;
            atoms.push_back(expr_internal::gather_node<F>(
                std::move(parts), std::move(idx), {n}));
          }
          add_one(map, atoms, d_.preds_[ks[i]].name);
          i = j;
        }
      }
    };
    const auto rel = form_relation(*pplan_[g.preds[0]].form, g.name);
    const unsigned K = rel.operands;
    // REL over G: the same monomials and coefficients.
    FieldRelation<G> rg;
    rg.name = rel.name;
    rg.operands = rel.operands;
    for (const auto &m : rel.monomials)
      rg.monomials.push_back({m.coeff, m.ops});
    std::shared_ptr<const BatchOperands<G>> ops;
    if (bits) {
      if constexpr (F::kCharacteristicTwo) {
        // Its words: the packed run's groups (words of the bit node's
        // parent; base_of checks them), or the bit views' words, on the path
        // from the bit node up.
        if (!provisional && g.word_degree != word_bits_ &&
            !above_bits(g.word_degree))
          fail("batch '" + g.name + "' reads the bits of GF(2^" +
               std::to_string(g.word_degree) + ") words, but domain " + d_.name +
               "'s packing tree has no path from GF(2) to them below K");
        auto make = [&](auto wtag) {
          constexpr size_t W = decltype(wtag)::value;
          std::vector<Elt> dual;
          if constexpr (W == F::kSubFieldBits) {
            const PackedBasis<F> basis(f);
            for (size_t j = 0; j < W; ++j) dual.push_back(basis.dual(j));
          } else {
            dual = PackingStage<F>(f, 1, W).dual;
          }
          auto map = std::make_shared<BitViewMap<F, W>>(
              f, g.name, K, std::vector<BatchSpace>{}, std::move(dual));
          add_all(*map);
          std::shared_ptr<const BitViewMap<G, W>> mg;
          if constexpr (std::is_same_v<G, F>)
            mg = std::move(map);
          else
            mg = std::make_shared<BitViewMap<G, W>>(fg, *map);
          return std::shared_ptr<const BatchOperands<G>>(
              std::make_shared<ViewBitOperands<G, W>>(fg, rg, std::move(mg),
                                                      kernel_width(g.width)));
        };
        if (g.word_degree == 16)
          ops = make(std::integral_constant<size_t, 16>{});
        else if (g.word_degree == 8)
          ops = make(std::integral_constant<size_t, 8>{});
        else
          ops = make(std::integral_constant<size_t, 32>{});
      }
    } else {
      auto map = std::make_shared<FieldViewMap<F>>(f, g.name, K,
                                                   std::vector<BatchSpace>{});
      add_all(*map);
      std::shared_ptr<const FieldViewMap<G>> mg;
      if constexpr (std::is_same_v<G, F>)
        mg = std::move(map);
      else
        mg = std::make_shared<FieldViewMap<G>>(fg, *map);
      ops = std::make_shared<ViewFieldOperands<G>>(fg, rg, std::move(mg),
                                                   g.word_degree, g.eval);
    }
    return ops;
  }

  void build();

  // ------------------------------------------- the domain's realization --
  // The domain's decisions beyond the realized program's elements
  // (ir::DomainRealization::decisions): each predicate's reasons and costs
  // and its batched form's class, the batch groups with their choices and
  // counted work (a group placed in a batch without its predicates and
  // width, which are its batch's), the packing chains and their report
  // note, the Boolean group's choice (without its target, which is its
  // checks') and work, and the Ligero choice. The placements, the triples'
  // operands, the batches' parts and widths and the Boolean checks' target
  // are read from the program (read_realization).
  struct Decisions {
    std::vector<PredPlan> preds;
    std::vector<Group> groups;
    std::map<std::pair<size_t, size_t>, std::vector<size_t>> chains;
    std::string chain_costs;
    PlacementChoice bit_choice;
    OpCounts bool_work;
    std::optional<compiler::LigeroChoice> lig;
    // The target of each Boolean check, by node, from the program.
    std::map<size_t, Placement> type_where;
  };
  static void put_counts(std::vector<uint8_t> &out, const OpCounts &c) {
    for (uint64_t x : {c.mul, c.add, c.mac, c.reduce, c.inv, c.lane_lookup,
                       c.lane_mul, c.lane_term, c.lin, c.map_mul, c.map_add,
                       c.map_mac, c.region})
      put_u64(out, x);
  }
  static OpCounts get_counts(compiler::CacheReader &r) {
    OpCounts c;
    for (uint64_t *x : {&c.mul, &c.add, &c.mac, &c.reduce, &c.inv,
                        &c.lane_lookup, &c.lane_mul, &c.lane_term, &c.lin,
                        &c.map_mul, &c.map_add, &c.map_mac, &c.region})
      *x = r.u64();
    return c;
  }
  // A placement choice, its target written when WHERE.
  static void put_choice(std::vector<uint8_t> &out, const PlacementChoice &c,
                         bool where = true) {
    if (where) put_u64(out, uint64_t(c.where));
    put_u64(out, c.width);
    put_str(out, c.why);
    put_u64(out, c.candidates.size());
    for (const auto &k : c.candidates) {
      put_u64(out, uint64_t(k.where));
      put_u64(out, k.admissible ? 1 : 0);
      compiler::put_f64(out, k.us);
      compiler::put_f64(out, k.bytes);
      put_u64(out, k.terms);
      put_u64(out, k.width);
      put_str(out, k.why_not);
    }
    compiler::put_f64(out, c.growth);
  }
  static Placement get_placement(compiler::CacheReader &r) {
    const uint64_t p = r.u64();
    if (p > uint64_t(Placement::kBatch)) r.fail();
    return Placement(uint8_t(p));
  }
  static BatchEval get_eval(compiler::CacheReader &r) {
    const uint64_t e = r.u64();
    if (e > uint64_t(BatchEval::kField)) r.fail();
    return BatchEval(uint8_t(e));
  }
  static PlacementChoice get_choice(compiler::CacheReader &r,
                                    bool where = true) {
    PlacementChoice c;
    if (where) c.where = get_placement(r);
    c.width = unsigned(r.u64());
    c.why = r.str();
    const size_t n = r.count(48);
    for (size_t i = 0; r.ok() && i < n; ++i) {
      PlacementCandidate k;
      k.where = get_placement(r);
      k.admissible = r.u64() != 0;
      k.us = r.f64();
      k.bytes = r.f64();
      k.terms = r.u64();
      k.width = unsigned(r.u64());
      k.why_not = r.str();
      c.candidates.push_back(std::move(k));
    }
    c.growth = r.f64();
    return c;
  }
  // This domain's realization record, as read_realization reads it.
  std::vector<uint8_t> realization_bytes() const {
    std::vector<uint8_t> out;
    put_u64(out, pplan_.size());
    for (const PredPlan &pp : pplan_) {
      put_str(out, pp.why);
      put_str(out, pp.costs);
      put_u64(out, uint64_t(pp.eval));
      put_u64(out, pp.word_degree);
      put_u64(out, pp.operands);
      // A batched predicate's group is its batch's.
      put_u64(out, pp.where == Placement::kBatch ? 0 : uint64_t(pp.group + 1));
      put_u64(out, uint64_t(pp.pin));
    }
    put_u64(out, groups_.size());
    for (const Group &g : groups_) {
      const bool batched = g.choice.where == Placement::kBatch;
      put_u64(out, batched ? 1 : 0);
      if (!batched) {
        put_u64(out, g.preds.size());
        for (size_t k : g.preds) put_u64(out, k);
        put_u64(out, g.width);
      }
      put_u64(out, uint64_t(g.eval));
      put_u64(out, g.word_degree);
      put_u64(out, g.n);
      put_u64(out, g.degree);
      put_str(out, g.name);
      put_choice(out, g.choice, !batched);
      put_u64(out, g.pinned ? 1 : 0);
      put_counts(out, g.work);
    }
    put_u64(out, chains_.size());
    for (const auto &[edge, chain] : chains_) {
      put_u64(out, edge.first);
      put_u64(out, edge.second);
      put_u64(out, chain.size());
      for (size_t x : chain) put_u64(out, x);
    }
    put_str(out, chain_costs_);
    put_choice(out, bit_choice_, false);
    put_counts(out, bool_work_);
    put_u64(out, lig_ ? 1 : 0);
    if (lig_) {
      const compiler::LigeroChoice &c = *lig_;
      for (uint64_t x : {uint64_t(c.N), uint64_t(c.k), uint64_t(c.t),
                         uint64_t(c.masking), uint64_t(c.reps),
                         uint64_t(c.half), uint64_t(c.fallback ? 1 : 0),
                         c.goal_num,
                         uint64_t(c.A), uint64_t(c.a), uint64_t(c.l),
                         c.cert.count,
                         uint64_t(c.cert.unique_decoding ? 1 : 0), c.cert.m,
                         c.cert.bj, c.cert.h})
        put_u64(out, x);
      for (double x : {c.ip_bits, c.commit, c.test, c.column})
        compiler::put_f64(out, x);
    }
    return out;
  }

  // The program P's target of predicate Q as a placement: its own (equal),
  // or its realization's (an integer mod_0); the realized predicate's for a
  // predicate realized by another (Target::kRealized); none for another
  // body.
  static std::optional<Placement> placement_of(const ir::Program &P,
                                               const ir::Predicate &q,
                                               int depth = 0) {
    const ir::Target *t = nullptr;
    if (q.body == ir::Predicate::kEqual) t = &q.target;
    if (q.body == ir::Predicate::kMod && q.mod.target) t = &*q.mod.target;
    if (t == nullptr) return std::nullopt;
    if (t->kind == ir::Target::kRealized) {
      if (t->id >= P.predicates.size() || depth > 0) return std::nullopt;
      return placement_of(P, P.predicates[t->id], depth + 1);
    }
    switch (t->kind) {
      case ir::Target::kAffine:
        return Placement::kAffine;
      case ir::Target::kQuadratic:
        return Placement::kQuadratic;
      case ir::Target::kBatch:
        return Placement::kBatch;
      default:
        return Placement::kCircuit;
    }
  }
  // The node of leaf E of program P, or none.
  static std::optional<size_t> leaf_node(const ir::Program &P, ir::Id e) {
    if (e == ir::kNone || e >= P.nodes.size()) return std::nullopt;
    const ir::Expr &x = P.nodes[e];
    if (x.op != ir::Expr::kLeaf || x.x >= P.values.size()) return std::nullopt;
    const ir::Id c = P.values[x.x].cnode;
    if (c == ir::kNone) return std::nullopt;
    return size_t(c);
  }

  // The decisions of this domain: from the realized program P, each
  // predicate's placement (its predicate's target), a triple's operands,
  // each batch group's predicates and width (its batch's parts and width)
  // and the Boolean checks' targets; the rest from the realization record
  // B. None, with misfit_ set, when B is malformed or the program does not
  // hold this domain's declarations.
  std::optional<Decisions> read_realization(const ir::Program &P,
                                            const std::vector<uint8_t> &b) {
    const ir::Id di = ir::Id(d_.index);
    // The program's predicates of the domain's declarations.
    std::vector<const ir::Predicate *> decl(d_.preds_.size(), nullptr);
    Decisions d;
    for (const ir::Predicate &q : P.predicates) {
      if (q.origin.domain != di) continue;
      if (q.origin.kind == ir::Origin::kDecl) {
        if (q.origin.index >= decl.size() || decl[q.origin.index] != nullptr) {
          misfit_ = "the realized program's predicate '" + q.name +
                    "' is no declaration of the domain";
          return std::nullopt;
        }
        decl[q.origin.index] = &q;
      } else if (q.origin.kind == ir::Origin::kTypeCheck) {
        const auto w = placement_of(P, q);
        if (w) d.type_where[size_t(q.origin.index)] = *w;
      }
    }
    for (size_t k = 0; k < decl.size(); ++k)
      if (decl[k] == nullptr) {
        misfit_ = "the predicate '" + d_.preds_[k].name +
                  "' is no predicate of the realized program";
        return std::nullopt;
      }
    compiler::CacheReader r(b);
    const size_t np = r.count(48);
    if (np != d_.preds_.size()) {
      misfit_ = "its realization has another number of predicates";
      return std::nullopt;
    }
    for (size_t k = 0; r.ok() && k < np; ++k) {
      PredPlan pp;
      pp.why = r.str();
      pp.costs = r.str();
      pp.eval = get_eval(r);
      pp.word_degree = r.u64();
      pp.operands = r.u64();
      pp.group = long(r.u64()) - 1;
      pp.pin = get_placement(r);
      const auto w = placement_of(P, *decl[k]);
      if (!w) {
        misfit_ = "the predicate '" + d_.preds_[k].name + "' has no target";
        return std::nullopt;
      }
      pp.where = *w;
      if (pp.where == Placement::kQuadratic) {
        const ir::Expr *l = decl[k]->lhs < P.nodes.size() ? &P.nodes[decl[k]->lhs]
                                                          : nullptr;
        const auto a = l && l->op == ir::Expr::kMul ? leaf_node(P, l->a) : std::nullopt;
        const auto bb = l && l->op == ir::Expr::kMul ? leaf_node(P, l->b) : std::nullopt;
        const auto c = leaf_node(P, decl[k]->rhs);
        if (!a || !bb || !c) {
          misfit_ = "the triple '" + d_.preds_[k].name + "' is not a b = c";
          return std::nullopt;
        }
        pp.tri = TripleForm{*a, *bb, *c};
      }
      if (pp.where == Placement::kBatch) pp.group = -1;
      d.preds.push_back(std::move(pp));
    }
    const size_t ng = r.count(8);
    for (size_t i = 0; r.ok() && i < ng; ++i) {
      Group g;
      const bool batched = r.u64() != 0;
      if (!batched) {
        const size_t n = r.count(8);
        for (size_t j = 0; r.ok() && j < n; ++j) {
          const size_t k = r.u64();
          if (k >= np) r.fail();
          g.preds.push_back(k);
        }
        g.width = unsigned(r.u64());
      }
      g.eval = get_eval(r);
      g.word_degree = r.u64();
      g.n = r.u64();
      g.degree = unsigned(r.u64());
      g.name = r.str();
      g.choice = get_choice(r, !batched);
      if (batched) {
        // Its predicates and width are its batch's.
        g.choice.where = Placement::kBatch;
        const ir::Batch *bt = nullptr;
        for (const ir::Batch &x : P.batches)
          if (x.domain == di && x.name == g.name) bt = &x;
        if (bt == nullptr) {
          misfit_ = "the batch '" + g.name + "' is no batch of the realized program";
          return std::nullopt;
        }
        for (ir::Id part : bt->parts) {
          const ir::Predicate &q = P.predicates.at(part);
          if (q.origin.kind != ir::Origin::kDecl || q.origin.domain != di ||
              q.origin.index >= np) {
            misfit_ = "a part of the batch '" + g.name +
                      "' is no predicate of the domain";
            return std::nullopt;
          }
          g.preds.push_back(size_t(q.origin.index));
          if (d.preds[q.origin.index].where != Placement::kBatch) r.fail();
          d.preds[q.origin.index].group = long(i);
        }
        g.width = unsigned(bt->width);
      }
      g.pinned = r.u64() != 0;
      g.work = get_counts(r);
      d.groups.push_back(std::move(g));
    }
    for (const PredPlan &pp : d.preds)
      if (pp.group >= long(ng) || pp.group < -1 ||
          (pp.where == Placement::kBatch && pp.group < 0))
        r.fail();
    const size_t nc = r.count(24);
    for (size_t i = 0; r.ok() && i < nc; ++i) {
      const size_t lo = r.u64(), hi = r.u64();
      std::vector<size_t> chain(r.count(8));
      for (size_t &x : chain) x = r.u64();
      d.chains[{lo, hi}] = std::move(chain);
    }
    d.chain_costs = r.str();
    d.bit_choice = get_choice(r, false);
    d.bool_work = get_counts(r);
    if (r.u64() != 0) {
      compiler::LigeroChoice c;
      c.N = r.u64();
      c.k = r.u64();
      c.t = r.u64();
      const uint64_t m = r.u64();
      if (m > uint64_t(LigeroMasking::kSplit)) r.fail();
      c.masking = LigeroMasking(m);
      c.reps = r.u64();
      c.half = r.u64();
      c.fallback = r.u64() != 0;
      c.goal_num = r.u64();
      c.A = r.u64();
      c.a = r.u64();
      c.l = r.u64();
      c.cert.count = r.u64();
      c.cert.unique_decoding = r.u64() != 0;
      c.cert.m = r.u64();
      c.cert.bj = r.u64();
      c.cert.h = r.u64();
      c.ip_bits = r.f64();
      c.commit = r.f64();
      c.test = r.f64();
      c.column = r.f64();
      d.lig = c;
    }
    if (!r.done()) return std::nullopt;
    return d;
  }

  // The checks that every element of this domain's realization is one of
  // the realized program P's, and every element of P on the domain one of
  // its: the batches in order, the lowerings' affine rows and the declared
  // triples, the circuit and its emission order. Sets misfit_ on the first
  // that fails.
  void check_claims(const ir::Program &P) {
    const ir::Id di = ir::Id(d_.index);
    auto fail_claim = [&](const std::string &why) {
      if (misfit_.empty()) misfit_ = why;
    };
    // The batches, in the kernels' order, each with its parts.
    std::vector<const ir::Batch *> bs;
    for (const ir::Batch &b : P.batches)
      if (b.domain == di) bs.push_back(&b);
    if (bs.size() != bplan_.size())
      fail_claim("the realized program has " + std::to_string(bs.size()) +
                 " batches of the domain, its realization " +
                 std::to_string(bplan_.size()));
    for (size_t i = 0; i < bs.size() && i < bplan_.size(); ++i) {
      const auto sh = bplan_[i].kernel->shape();
      if (bs[i]->name != bplan_[i].name || bs[i]->instances != sh.instances ||
          bs[i]->degree != sh.degree || bs[i]->rounds != sh.rounds)
        fail_claim("the batch '" + bplan_[i].name +
                   "' is not the realized program's batch " + std::to_string(i));
    }
    // The lowerings' affine rows and the declared triples.
    std::set<uint64_t> rows, quads;
    for (const ir::Predicate &q : P.predicates) {
      if (q.origin.domain != di) continue;
      if (q.origin.kind == ir::Origin::kAffineRow &&
          placement_of(P, q) == Placement::kAffine)
        rows.insert(q.origin.index);
      if (q.origin.kind == ir::Origin::kQuad &&
          placement_of(P, q) == Placement::kQuadratic)
        quads.insert(q.origin.index);
    }
    for (size_t i = 0; i < d_.affine_.size(); ++i)
      if (d_.affine_[i].pred < 0 && !rows.count(i))
        fail_claim("the affine row '" + d_.affine_[i].name +
                   "' is no predicate of the realized program");
    for (size_t i = 0; i < d_.quads_.size(); ++i)
      if (!quads.count(i))
        fail_claim("a declared triple of the domain is no predicate of the "
                   "realized program");
    // The circuit and its emission order.
    const ir::Circuit *c = nullptr;
    for (const ir::Circuit &x : P.circuits)
      if (x.domain == di) c = &x;
    if ((c != nullptr) != gkr_) {
      fail_claim(gkr_ ? "the realized program has no circuit of the domain"
                      : "the realized program has a circuit of a domain "
                        "without GKR");
      return;
    }
    if (c == nullptr) return;
    if (c->entries.size() != circuit_entries_.size()) {
      fail_claim("the realized program's circuit has another emission order");
      return;
    }
    using CE = DomainPlan::CircuitEntry;
    for (size_t i = 0; i < circuit_entries_.size(); ++i) {
      const CE &e = circuit_entries_[i];
      const ir::CircuitEntry &x = c->entries[i];
      bool same = false;
      switch (e.kind) {
        case CE::kTypeCheck: {
          const ir::Predicate *q =
              x.id < P.predicates.size() ? &P.predicates[x.id] : nullptr;
          same = x.kind == ir::CircuitEntry::kTypeCheck && q != nullptr &&
                 q->origin.kind == ir::Origin::kTypeCheck &&
                 q->origin.index == e.id;
          break;
        }
        case CE::kAlignment:
          same = x.kind == ir::CircuitEntry::kAlignment && x.id == e.id;
          break;
        case CE::kPredicate: {
          const ir::Predicate *q =
              x.id < P.predicates.size() ? &P.predicates[x.id] : nullptr;
          same = x.kind == ir::CircuitEntry::kPred && q != nullptr &&
                 q->origin.kind == ir::Origin::kDecl && q->origin.index == e.id;
          break;
        }
        default:
          same = x.kind == ir::CircuitEntry::kRealization && x.real.name == e.name;
      }
      if (!same) {
        fail_claim("entry " + std::to_string(i) +
                   " of the circuit is not the realized program's");
        return;
      }
    }
  }

  const D &d_;
  const CompilePlan &plan_;
  Provisional *prov_ = nullptr;
  // The inputs-only provisional pass, and its bit_groups().
  bool inputs_only_ = false;
  size_t bit_groups_ = 0;
  // The expression emitter of the circuit being built (build() only).
  ExprEmitter<F, CLogic> *emitter_ = nullptr;
  std::unique_ptr<Circuit<F>> circ_;
  // The compile cache: the record build() reads, whether the domain was
  // restored from it, and what the circuit's record holds beyond its
  // layers (the scheduler's packed bits).
  // The realized program the domain is built from (build() only).
  const DomainSource *source_ = nullptr;
  bool loaded_ = false;
  // Why a record did not restore the domain ("" when it did, or none was
  // given).
  std::string misfit_;
  std::vector<std::pair<size_t, size_t>> sched_packed_;
  std::vector<Slot> slots_;
  std::map<size_t, size_t> cells_;  // node id -> first circuit input
  std::map<std::pair<size_t, bool>, Wires> pub_wires_;
  std::map<size_t, Wires> cell_wires_;
  std::set<size_t> views_read_;          // bit views a circuit reads
  std::map<size_t, size_t> view_at_;     // bit view -> first circuit input
  std::map<size_t, Wires> view_wires_;
  std::vector<size_t> filler_;           // zero inputs (alignment)
  PackingTree tree_;
  // The packing chains' modeled costs (choose_chains), for the report.
  std::string chain_costs_;
  // The packing chains taken (choose_chains; empty: the default tree).
  std::map<std::pair<size_t, size_t>, std::vector<size_t>> chains_;
  std::unique_ptr<TreePlan<F, Hash>> tplan_;
  size_t word_bits_ = 0;                 // bits per packed word
  PrefixSubfieldTest<F, Hash> subfield_;
  std::vector<Rows> rows_;
  std::vector<PredPlan> pplan_;
  size_t ncircuits_ = 0;  // circuit constraints: closures and predicates
  // Whether the domain runs GKR: false when it has no circuit constraint.
  bool gkr_ = true;
  std::vector<BatchPlan> bplan_;
  // Each batch's table nodes, parallel to bplan_ (the declared batches,
  // then the batched Boolean checks).
  std::vector<std::vector<size_t>> btables_;
  // The Boolean checks' group: its placement and the costs weighed; the
  // Bit cells checked as triples; the batch's kernel and tables (null when
  // it is not batched).
  static constexpr size_t kBitCheckTerms = 3;
  PlacementChoice bit_choice_;
  OpCounts bool_work_;
  size_t bit_group_n_ = 0;
  std::set<size_t> triple_bits_;
  // The Boolean checks by value and target (DomainPlan::type_checks).
  std::vector<DomainPlan::TypeCheck> type_checks_;
  // The circuit's constraints in emission order (DomainPlan).
  std::vector<DomainPlan::CircuitEntry> circuit_entries_;
  std::shared_ptr<BatchKernel<F, Hash>> bool_kernel_;
  std::vector<size_t> bool_tables_;
  // The kernels of the declared batches (Domain::batch), in order.
  std::vector<std::shared_ptr<const BatchKernel<F, Hash>>> decl_kernels_;
  // The predicates' batch groups (merged for costing; placed in a batch or
  // not), and the kernels of those placed in a batch.
  std::vector<Group> groups_;
  std::vector<std::shared_ptr<BatchKernel<F, Hash>>> group_kernels_;
  // Each batch group's spaces, in table order.
  std::vector<std::vector<BatchSpace>> group_spaces_;
  // The packed run of Bit cells and bit views: its first and last inputs.
  size_t run_begin_ = 0, run_end_ = 0;
  size_t batch_bit_checks_ = 0;
  size_t total_rows_ = 0, late_bits_ = 0, bit_products_ = 0;
  size_t cell_bit_checks_ = 0, packed_bits_ = 0, packed_zero_bits_ = 0;
  // Without relative packing: each Bit cell node's Boolean check, by node
  // id (true: a circuit constraint; false: quadratic triples).
  std::map<size_t, bool> bit_checks_;
  size_t view_words_ = 0, derived_bit_checks_ = 0;
  size_t block_enc_ = 0, param_nw_ = 0, param_w_ = 0;
  std::optional<compiler::LigeroChoice> lig_;
  // The tableau: code length N = block_ext, k = block, and its rows.
  size_t param_N_ = 0, param_k_ = 0, param_nrow_ = 0;
};

template <class F, class RSF, class S>
void CompiledDomain<F, RSF, S>::check_bindings() const {
  const std::vector<Node> &N = nodes();
  const F &f = d_.field();
  for (const auto &[x, view] : d_.bound_) {
    const Node &xn = N[x];
    const std::string what = "binding of '" + xn.name + "'";
    // B1: phase-0 advice or a private input, of type Subfield or Field. A
    // view of digits does not preserve Booleanity, so a Bit is never bound.
    if ((xn.kind != Kind::kAdvice && xn.kind != Kind::kPrivateInput) ||
        plan_.phase[x] != 0)
      fail(
          what + ": only phase-0 advice and private inputs are bound; '" +
          xn.name + "' is a phase-" + std::to_string(plan_.phase[x]) + " " +
          (xn.kind == Kind::kAdvice ? "advice value" : "node of another kind"));
    if (xn.type.base == Base::kBit)
      fail(what + ": a Bit value is not bound (a view of digits does not "
           "preserve Booleanity)");
    // B2: not a batch table, a bit-view source or a quadratic operand.
    for (const auto &b : d_.batches_)
      for (size_t t : b.tables)
        if (t == x)
          fail(what + ": it is a table of the batch '" + b.name + "'");
    for (const auto &[v, sel] : d_.views_)
      if (N[v].deps.at(0) == x)
        fail(what + ": it is the source of the bit view '" + N[v].name + "'");
    for (const auto &q : d_.quads_)
      if (q.a == x || q.b == x || q.c == x)
        fail(what + ": it is a quadratic triple operand");
    for (const auto &t : view.terms) {
      const Node &tn = N[t.node];
      // B3: operator-free terms reading unbound phase-0 cells of this domain
      // computed from X alone (no chain, no cycle), and constants (the
      // offset of an x + c request).
      if (!t.chain.empty())
        fail(what + ": the view applies the operator '" + t.chain[0]->name +
             "'");
      if (tn.kind == Kind::kConstant) {
        if (xn.type.base == Base::kSubfield && d_.prime != Space::kField &&
            !subfield_contains(f, t.scale))
          fail(what + ": a coefficient lies outside the prime field");
        continue;
      }
      if (tn.domain != d_.index || !plan_.cell(t.node) ||
          tn.kind != Kind::kAdvice || tn.deps != std::vector<size_t>{x})
        fail(what + ": the view reads '" + tn.name + "', which is not a "
             "phase-0 advice cell of domain " + d_.name + " computed from '" +
             xn.name + "' alone");
      // B4: a Subfield X is viewed in S: prime-field coefficients and
      // Subfield or Bit terms. In a prime field (DomainProfile::prime =
      // kField) the designated subfield is the field, so a Field term lies
      // in it (the range planner declares its digits Field there).
      if (xn.type.base == Base::kSubfield && d_.prime != Space::kField) {
        if (!subfield_contains(f, t.scale))
          fail(what + ": a coefficient lies outside the prime field");
        if (tn.type.base == Base::kField)
          fail(what + ": the Subfield value is viewed through the Field "
               "value '" + tn.name + "'");
      }
      // B5: the digits share X's phase (0).
      if (plan_.phase[t.node] != 0)
        fail(what + ": the view reads the late value '" + tn.name + "'");
    }
  }
}

// Each predicate's placement (Placement, expr.h; placement.h). A predicate
// that reads a structured operator (no circuit expansion) is pinned to
// affine rows: a pin elsewhere, or an expression that is not affine, is a
// CompileError. Otherwise a pin decides, then affine rows when the
// expression is affine, then the placement rule. The predicates of one
// batched form (batch_form.h: one polynomial Q, operands of one class: Bit
// views in characteristic 2, or cells of one subfield, or of the field)
// merge into one group, which goes to the cheapest admissible target among
// one batch over all their instances, the circuit, and quadratic triples
// (a b - c on committed phase-0 Field cells: Ligero's quadratic test, no
// circuit term), by the profile's rates. A predicate pinned to a batch
// joins its form's batch, or makes one. The compiler adds no layer
// boundary; materialize does.
template <class F, class RSF, class S>
void CompiledDomain<F, RSF, S>::place_predicates(const Decisions *dec) {
  const std::vector<Node> &N = nodes();
  const F &f = d_.field();
  auto pub = [&](size_t id) { return is_public(N[id].kind); };
  // Whether an affine row reads ID: not a value only a circuit reads, nor
  // a view of one (flatten reads a derived or bound node through its
  // terms).
  std::map<size_t, bool> readable_at;
  std::function<bool(size_t)> readable = [&](size_t id) -> bool {
    if (d_.circuit_only(id) || N[id].type.base == Base::kBytes) return false;
    if (!((N[id].kind == Kind::kDerived || plan_.bound.count(id)) &&
          N[id].domain == d_.index))
      return true;
    auto it = readable_at.find(id);
    if (it != readable_at.end()) return it->second;
    bool ok = true;
    for (const auto &t : expr(id).terms) ok = ok && readable(t.node);
    readable_at[id] = ok;
    return ok;
  };
  // A committed phase-0 Field cell of this domain, which a triple reads.
  auto field_cell = [&](size_t id) {
    return N[id].domain == d_.index && plan_.cell(id) &&
           N[id].kind != Kind::kPad && N[id].kind != Kind::kPadCopy &&
           N[id].type.base == Base::kField && !in_subfield_region(id);
  };
  const PlacementRates &rates = d_.p_.rates;
  // The largest degree any batch here admits: D (w - 1) + 1 skip points at
  // the narrowest width a profile measures.
  constexpr size_t kMaxBatchDegree = 17;
  std::vector<std::optional<TripleForm>> tris(d_.preds_.size());
  std::vector<std::string> batch_nots(d_.preds_.size());
  std::vector<size_t> pending;
  pplan_.assign(d_.preds_.size(), PredPlan{});
  // Predicates that certainly have no affine form skip affine_form, whose
  // forms of their operands cost the size of every value a view reads.
  AffineScreen<F> screen(pub, readable);
  if (dec != nullptr) {
    pplan_ = dec->preds;
    groups_ = dec->groups;
    for (size_t k = 0; k < d_.preds_.size(); ++k) {
      const auto &p = d_.preds_[k];
      PredPlan &pp = pplan_[k];
      ExprPtr<F> body = p.e;
      if (p.truth)
        body = expr_internal::binary(
            ExprOp::kAdd, expr_internal::scale(p.e, f.mone()),
            expr_internal::constant<F>(&f, {f.one()}, {}), "assert_true");
      if (pp.where == Placement::kAffine) {
        pp.aff = affine_form(body, pub, readable);
        check(pp.aff.has_value(), "a cached affine placement has a form");
      } else if (pp.where == Placement::kBatch) {
        std::string why;
        pp.form = batch_form<F>(body, why, 64, /*pad_affine=*/true);
        check(pp.form.has_value(), "a cached batch placement has a form");
      }
    }
    return;
  }
  for (size_t k = 0; k < d_.preds_.size(); ++k) {
    const auto &p = d_.preds_[k];
    PredPlan &pp = pplan_[k];
    const std::string what =
        std::string(p.truth ? "assert_true" : "assert_zero") + " '" + p.name +
        "'";
    // assert_true(b) is 1 - b = 0 in affine rows.
    ExprPtr<F> body = p.e;
    if (p.truth)
      body = expr_internal::binary(
          ExprOp::kAdd, expr_internal::scale(p.e, f.mone()),
          expr_internal::constant<F>(&f, {f.one()}, {}), "assert_true");
    // assert_true's 1 - b has a form exactly when b does.
    if (screen.possible(*p.e)) pp.aff = affine_form(body, pub, readable);
    const size_t degree = expr_degree(p.e);
    std::optional<TripleForm> tri;
    if (!p.truth) tri = triple_form(body);
    if (tri &&
        !(field_cell(tri->a) && field_cell(tri->b) && field_cell(tri->c)))
      tri.reset();
    tris[k] = tri;
    const Placement pin = forced(p.name, *p.pin);
    pp.pin = pin;
    // The batched form, or why there is none.
    std::string &batch_not = batch_nots[k];
    if (p.e->structured) {
      batch_not = "it reads the structured operator '" +
                  p.e->structured_op + "'";
    } else if (pp.aff) {
      batch_not = "it is affine";
    } else if (degree == kCircuitDegree) {
      batch_not = "Logic builds its comparisons and reductions";
    } else if (degree > kMaxBatchDegree) {
      batch_not = "it is of degree " + std::to_string(degree) +
                  ", above the " + std::to_string(kMaxBatchDegree) +
                  " a batch admits";
    } else {
      // No affine form (gates on constants that only fold here): an affine
      // polynomial joins a batch in the shape a b + c.
      auto form = batch_form<F>(body, batch_not, 64, /*pad_affine=*/true);
      if (!form && degree > 2)
        batch_not = "it is of degree " + std::to_string(degree) + " (" +
                    batch_not + ")";
      if (form) {
        BatchEval eval = BatchEval::kField;
        size_t wdeg = 0;
        batch_not = batch_class(*form, eval, wdeg);
        // A predicate pinned to another target needs no batch rate.
        if (batch_not.empty() && pin != Placement::kAuto &&
            pin != Placement::kBatch)
          batch_not = std::string("pinned to ") + placement_name(pin);
        if (batch_not.empty()) {
          const unsigned w =
              batch_width(eval);
          batch_not = batch_shape_error(*form, eval, w);
        }
        if (batch_not.empty()) {
          pp.form = std::move(form);
          pp.operands = pp.form->atoms.size();
          pp.eval = eval;
          pp.word_degree = wdeg;
        }
      }
    }
    if (p.e->structured) {
      const std::string op = "'" + p.e->structured_op + "'";
      if (pin == Placement::kCircuit || pin == Placement::kQuadratic ||
          pin == Placement::kBatch)
        fail(what + " reads the structured operator " + op + ", which a "
             "circuit cannot expand, so it is pinned to affine rows; the pin "
             "to " + placement_name(pin) + " is refused");
      if (!pp.aff)
        fail(what + " reads the structured operator " + op + ", so it is "
             "pinned to affine rows, but it is not affine");
      pp.where = Placement::kAffine;
      pp.why = "reads the structured operator " + op;
    } else if (pin == Placement::kAffine) {
      if (!pp.aff) fail(what + " is pinned to affine rows but is not affine");
      pp.where = Placement::kAffine;
      pp.why = "pinned";
    } else if (pin == Placement::kQuadratic) {
      if (!tri)
        fail(what + " is pinned to quadratic triples but is not a b - c on "
             "committed phase-0 Field cells");
      pp.where = Placement::kQuadratic;
      pp.tri = *tri;
      pp.why = "pinned";
    } else if (pin == Placement::kCircuit) {
      pp.where = Placement::kCircuit;
      pp.why = "pinned";
    } else if (pin == Placement::kBatch) {
      if (!pp.form)
        fail(what + " is pinned to a field batch, but " + batch_not);
      pp.where = Placement::kBatch;
      pp.why = "pinned";
      pending.push_back(k);
    } else if (pp.aff) {
      pp.where = Placement::kAffine;
      pp.why = "affine";
    } else if (!tri && !pp.form) {
      pp.where = Placement::kCircuit;
      pp.why = p.e->logic   ? "Logic gadgets"
               : degree > 2 && degree != kCircuitDegree
                   ? "degree " + std::to_string(degree)
                   : "not affine";
    } else {
      pending.push_back(k);
    }
  }

  // The circuit's quad terms and layers of predicate K, shared by the
  // predicates of one structure, and kept on the domain for the system's
  // next compile, which then gives each predicate the cost this one did.
  std::map<std::vector<uint8_t>, std::pair<size_t, size_t>> terms_of;
  auto terms = [&](size_t k) {
    const auto &p = d_.preds_[k];
    const auto at = std::make_pair(p.e.get(), p.truth);
    auto done = d_.pred_terms_.find(at);
    if (done != d_.pred_terms_.end()) return done->second;
    const auto key = structure_key(p.e);
    auto it = terms_of.find(key);
    if (it == terms_of.end())
      it = terms_of.emplace(key, predicate_terms(p)).first;
    d_.pred_terms_.emplace(at, it->second);
    return it->second;
  };
  // A predicate's instances in a batch: bit-sliced lanes are whole.
  auto instances = [&](size_t k) {
    const size_t n = d_.preds_[k].e->n;
    return pplan_[k].eval == BatchEval::kBitSliced ? (n + 63) / 64 * 64 : n;
  };

  // Groups by form: the evaluator, the leaves' degree and Q.
  auto key_of = [&](size_t k) {
    const PredPlan &pp = pplan_[k];
    std::vector<uint8_t> key = pp.form->shape_key(f);
    put_u64(key, uint64_t(pp.eval));
    put_u64(key, pp.word_degree);
    return key;
  };
  std::map<std::vector<uint8_t>, size_t> auto_of, pin_of;
  std::vector<Group> autos, pins;
  for (size_t k : pending) {
    const PredPlan &pp = pplan_[k];
    if (!pp.form) continue;
    const bool pinned = pp.pin == Placement::kBatch;
    auto &of = pinned ? pin_of : auto_of;
    auto &gs = pinned ? pins : autos;
    const auto key = key_of(k);
    auto it = of.find(key);
    if (it == of.end()) {
      it = of.emplace(key, gs.size()).first;
      Group g;
      g.eval = pp.eval;
      g.word_degree = pp.word_degree;
      g.degree = pp.form->degree();
      g.name = d_.preds_[k].name;
      g.pinned = pinned;
      gs.push_back(std::move(g));
    }
    Group &g = gs[it->second];
    g.preds.push_back(k);
    g.n += instances(k);
  }
  // The costs of a group (or of one predicate without a form).
  auto check_group = [&](const std::vector<size_t> &ks, const Group *g) {
    CheckGroup cg;
    size_t depth = 0;
    for (size_t k : ks) {
      cg.n += g ? instances(k) : d_.preds_[k].e->n;
      const auto [t, l] = terms(k);
      cg.circuit_terms += t;
      depth = std::max(depth, l);
      if (!tris[k]) cg.triple_not = "not a b - c on full-field cells";
    }
    cg.bytes_circuit = circuit_bytes(depth, cg.circuit_terms);
    cg.bytes_triple = 3 * double(cg.n) * coord_bytes();
    // Only an admissible triple's cost reads the provisional tableau.
    if (cg.triple_not.empty()) {
      cg.triple_rows = triple_rows(cg.n);
      cg.triple_hash_blocks = triple_hash_blocks(cg.n);
      cg.block_enc = prov_ ? prov_->tableau().block_enc : 0;
    }
    if (g == nullptr) {
      cg.batch_not = batch_nots[ks[0]];
      return cg;
    }
    const auto &q = *pplan_[ks[0]].form;
    cg.degree = q.degree();
    cg.eval = g->eval;
    cg.parts = ks.size();
    cg.operands = q.atoms.size();
    cg.batch_not = batch_shape_error(q, g->eval, batch_width(g->eval));
    // A batch without rates takes no part in the choice (placement.h), so
    // its work is not counted.
    if (cg.batch_not.empty() && !rates.or_unit().unit_rates &&
        !provisional_pass() && rates.has_batch(g->eval)) {
      Group tg = *g;
      tg.preds = ks;
      tg.width = batch_width(g->eval);
      cg.work = group_work(tg);
      // A bit-sliced batch's claim row at the root: its forms over the bit
      // node's region (OpCounts::region), at the provisional tableau's.
      if (g->eval == BatchEval::kBitSliced && prov_)
        cg.work.region = uint64_t(g->word_degree) * prov_->bit_groups();
    }
    const size_t n = cg.n, K = q.atoms.size();
    const unsigned D = cg.degree;
    cg.bytes_batch = [this, n, K, D](unsigned w) {
      return batch_bytes(n, unsigned(K), D, w);
    };
    return cg;
  };
  auto assign = [&](size_t k, const PlacementChoice &ch, long group) {
    PredPlan &pp = pplan_[k];
    pp.where = ch.where;
    pp.why = ch.why;
    pp.costs = ch.costs();
    pp.group = group;
    if (ch.where == Placement::kQuadratic) pp.tri = *tris[k];
  };
  // Predicates with a triple and no batched form: triples or the circuit.
  for (size_t k : pending) {
    if (pplan_[k].form) continue;
    const CheckGroup cg = check_group({k}, nullptr);
    assign(k, choose_placement(rates, cg, Placement::kAuto), -1);
  }
  // Each group of the rule: one target for all its predicates.
  for (Group &g : autos) {
    const CheckGroup cg = check_group(g.preds, &g);
    // The measurement hook may force the whole group ("D/group:NAME=T",
    // NAME its first predicate's): an admissible target only.
    Placement gp = forced("group:" + g.name, Placement::kAuto);
    if ((gp == Placement::kQuadratic && !cg.triple_not.empty()) ||
        (gp == Placement::kBatch && !cg.batch_not.empty()) ||
        gp == Placement::kAffine)
      fail("group '" + g.name + "' forced to " + placement_name(gp) +
           ", which it does not admit");
    g.choice = choose_placement(rates, cg, gp);
    if (gp == Placement::kBatch && g.choice.width == 0)
      g.choice.width = batch_width(g.eval);
    g.width = g.choice.width;
    g.work = cg.work;
    const long gi = long(groups_.size());
    for (size_t k : g.preds) assign(k, g.choice, gi);
    groups_.push_back(g);
  }
  // Pinned predicates join their form's batch, or make one.
  for (Group &g : pins) {
    bool joined = false;
    for (Group &a : groups_) {
      if (a.choice.where != Placement::kBatch) continue;
      if (key_of(a.preds[0]) != key_of(g.preds[0])) continue;
      for (size_t k : g.preds) {
        a.preds.push_back(k);
        a.n += instances(k);
        pplan_[k].group = long(&a - groups_.data());
      }
      std::sort(a.preds.begin(), a.preds.end());
      joined = true;
      break;
    }
    if (joined) continue;
    const CheckGroup cg = check_group(g.preds, &g);
    g.choice = choose_placement(rates, cg, Placement::kBatch);
    g.width = g.choice.width != 0
                  ? g.choice.width
                  : batch_width(g.eval);
    g.work = cg.work;
    const long gi = long(groups_.size());
    for (size_t k : g.preds) {
      assign(k, g.choice, gi);
      pplan_[k].why = "pinned";
    }
    groups_.push_back(g);
  }
  // Forms are kept for the batches only.
  for (PredPlan &pp : pplan_)
    if (pp.where != Placement::kBatch) pp.form.reset();
}

template <class F, class RSF, class S>
void CompiledDomain<F, RSF, S>::build() {
  const std::vector<Node> &N = nodes();
  const int di = d_.index;
  std::optional<CompileRegion> ph;
  ph.emplace(compile_times_on() ? "checks" : "");
  check_bindings();
  // Relative packing needs a designated subfield; bits pack in
  // characteristic 2 under it (the packing tree's GF(2) node).
  const bool packing = d_.has_subfield && relative_packing<F>();
  const bool char2pack =
      F::kCharacteristicTwo && packing && !d_.no_bit_packing;

  // The profile's prime field against F's characteristic: a GF(2) pad
  // masks a Bit value only in characteristic 2 (t = b + b' leaks b
  // otherwise).
  if (F::kCharacteristicTwo && d_.prime != Space::kPrime)
    fail("domain " + d_.name + " has characteristic 2, so its prime field is "
         "GF(2): DomainProfile::prime must be kPrime");
  if (!F::kCharacteristicTwo && d_.prime == Space::kPrime)
    fail("domain " + d_.name + " has odd characteristic, so its prime field "
         "is not GF(2): DomainProfile::prime must be kSubfield (the subfield "
         "is the prime field) or kField (the field is prime)");
  // kField says every value of F lies in the prime field (interval
  // propagation gives each one [0, p - 1], range.h's prime_node), so F
  // must be its designated subfield, of degree 1 over the prime field.
  if (!F::kCharacteristicTwo && d_.prime == Space::kField &&
      (domain_subfield<F>::kCoordinates != 1 || field_degree<F>() != 1))
    fail("domain " + d_.name + " declares its field prime "
         "(DomainProfile::prime = kField), but the field has degree " +
         std::to_string(field_degree<F>()) + " over its prime field and " +
         std::to_string(domain_subfield<F>::kCoordinates) +
         " coordinates over its designated subfield");
  if (d_.prime == Space::kSubfield && !d_.has_subfield)
    fail("domain " + d_.name + " places its prime field in its subfield "
         "(DomainProfile::prime = kSubfield) but declares no subfield");

  // A compile cache record (compile_cache.h): its decisions replace the
  // placement rule, the counting kernels, the chain choice and the tableau
  // search below, and its circuit is loaded in place of emitting and
  // scheduling one. A record whose decisions do not read back is not used
  // (loaded() is false, and the system compiles afresh).
  const ir::DomainRealization *rec = nullptr;
  std::optional<Decisions> dec;
  if (source_ != nullptr) {
    const ir::Program &P = *source_->program;
    if (source_->domain >= P.realizations.size()) {
      misfit_ = "the realized program has no realization of it";
    } else {
      rec = &P.realizations[source_->domain];
      dec = read_realization(P, rec->decisions);
      if (!dec && misfit_.empty()) misfit_ = "its realization does not read back";
    }
  }
  if (!dec) rec = nullptr;
  ph.reset();
  ph.emplace(compile_times_on() ? "placement" : "");
  place_predicates(dec ? &*dec : nullptr);
  ph.reset();
  ph.emplace(compile_times_on() ? "cells" : "");

  // Bit views that affine rows read: their bits are packed run inputs, as
  // a circuit's are.
  {
    std::set<size_t> affine_read;
    for (const auto &a : d_.affine_) {
      const Lin<F> &e = a.pred >= 0 && pplan_[a.pred].aff
                            ? pplan_[a.pred].aff->lin
                            : a.e;
      if (a.pred >= 0 && pplan_[a.pred].where != Placement::kAffine) continue;
      for (const auto &t : e.terms) affine_cells(t.node, affine_read);
    }
    for (size_t id : affine_read)
      if (N[id].kind == Kind::kBitView) views_read_.insert(id);
  }

  // Cells, and capability checks on types. SUB: unpacked subfield cells;
  // PACKED: bit-packed Bit cells; FULL: ambient cells. BIT_GROUP: the Bit
  // cells whose Boolean check the placement rule places (Bit cells, and
  // GF(2) pads, committed as full-field cells without relative packing;
  // relatively packed Bit cells in odd characteristic). CHECKED_BITS: those
  // whose check is a circuit constraint.
  std::vector<size_t> sub, packed, full, late_bits, checked_bits, bit_group;
  for (size_t id = 0; id < N.size(); ++id) {
    const Node &n = N[id];
    if (n.domain != di) continue;
    if (n.kind != Kind::kPad && n.type.base == Base::kSubfield &&
        !d_.has_subfield)
      fail("'" + n.name + "' has type Subfield but domain " + d_.name +
           " declares no source subfield");
    if (n.kind == Kind::kPad && d_.resolve(n.pad_space) == Space::kSubfield &&
        !d_.has_subfield)
      fail("subfield pad in domain " + d_.name +
           ", which declares no source subfield");
    // The no_bit_packing ablation has no GF(2) node, so a GF(2) pad (a late
    // Bit's) would need a Boolean check of its own, which it does not
    // implement.
    if (unpacked_bits() && n.kind == Kind::kPad &&
        d_.resolve(n.pad_space) == Space::kPrime)
      fail("GF(2) pad '" + n.name + "' in domain " + d_.name +
           " under the no_bit_packing ablation, which supports no late Bit");
    if (n.kind == Kind::kBitView) {
      const size_t w = n.deps.at(0);
      if (!char2pack)
        fail("bit view '" + n.name + "' in domain " + d_.name +
             ", which does not pack bits (characteristic 2 with relative "
             "packing)");
      if (N[w].domain != di || !plan_.cell(w) || N[w].kind == Kind::kPad ||
          N[w].kind == Kind::kPadCopy || N[w].type.base != Base::kSubfield)
        fail("bit view '" + n.name + "' reads '" + N[w].name +
             "', which is not a phase-0 Subfield variable of domain " +
             d_.name);
      continue;
    }
    if (plan_.cell(id)) {
      // Subfield membership comes from relative packing and the domain's
      // subfield step, so a domain without them commits no Subfield cell,
      // unless its field is prime (DomainProfile::prime = kField): the
      // designated subfield is then the field itself, and every cell lies
      // in it (F_p256).
      if (!packing && subfield_cell(id) && d_.prime != Space::kField)
        fail("'" + n.name + "' is a Subfield cell of domain " + d_.name +
             ", whose field has no relative packing (ExtensionTraits), so "
             "nothing would check its subfield membership; declare it Field, "
             "or use a field that supports relative packing");
      if (!in_subfield_region(id)) {
        full.push_back(id);
        // Without relative packing a Bit cell's Boolean check is the triple
        // b * b = b or a circuit constraint.
        if (bit_cell(id)) bit_group.push_back(id);
      } else if (F::kCharacteristicTwo && degree_of(id) == 1) {
        // GF(2): bit packed (the tree's degree-1 node is the bit stage, with
        // squaring-chain masks).
        packed.push_back(id);
      } else {
        sub.push_back(id);
        // Under relative packing a subfield cell enters no quadratic row,
        // so a Bit's Boolean check is a circuit constraint or a field batch.
        if (boolean_checked(id)) bit_group.push_back(id);
      }
    } else if (plan_.late(id) && n.type.base == Base::kBit) {
      late_bits.push_back(id);
    }
  }

  // Quadratic triples act on committed phase-0 cells only (design section 1),
  // and, under relative packing, on ambient cells only.
  for (const auto &q : d_.quads_) {
    for (size_t id : {q.a, q.b, q.c}) {
      if (plan_.late(id))
        fail("late variable '" + N[id].name + "' (phase " +
             std::to_string(plan_.phase[id]) +
             ") in a quadratic triple; write the product as a circuit "
             "constraint");
      if (!plan_.cell(id) || N[id].domain != di)
        fail("quadratic triple operand '" + N[id].name +
             "' is not a committed phase-0 variable of domain " + d_.name);
      if (packing && in_subfield_region(id))
        fail("quadratic triple operand '" + N[id].name + "' is a " +
             type_name(N[id].type) + " cell, which domain " + d_.name +
             " packs relative to its source subfield; quadratic rows read "
             "Field cells only, so write the product as a circuit "
             "constraint, which reads packed cells through relative packing");
    }
  }

  // The packing tree: the degrees of the domain's subfield cells in
  // declaration order (a Bit cell's is 1: GF(2), bit packed, in
  // characteristic 2, and the prime field otherwise), and GF(2) when bits
  // are viewed or a bit batch reads them.
  ph.reset();
  ph.emplace(compile_times_on() ? "packing tree" : "");
  const size_t s0 = designated_degree<F>(), nK = field_degree<F>();
  std::vector<size_t> declared;
  {
    std::set<size_t> in_sub(sub.begin(), sub.end());
    std::set<size_t> in_packed(packed.begin(), packed.end());
    for (size_t id = 0; id < N.size(); ++id) {
      if (N[id].domain != di) continue;
      if (in_packed.count(id) || N[id].kind == Kind::kBitView)
        declared.push_back(1);
      if (in_sub.count(id)) declared.push_back(degree_of(id));
    }
    // A bit batch's claim is on bits: the tree has GF(2). The
    // no_bit_packing ablation has no GF(2) node, so it takes no bit batch.
    for (const auto &b : d_.batches_)
      if (b.ops && b.ops->bit_operands()) {
        if (unpacked_bits())
          fail("batch '" + b.name + "' of domain " + d_.name +
               " reads bits, which the no_bit_packing ablation does not "
               "pack");
        declared.push_back(1);
      }
    for (const auto &g : groups_)
      if (g.choice.where == Placement::kBatch &&
          g.eval == BatchEval::kBitSliced)
        declared.push_back(1);
  }
  if (dec) {
    chains_ = dec->chains;
    chain_costs_ = dec->chain_costs;
  } else if (packing) {
    chains_ = choose_chains(declared, sub, packed, full, chain_costs_);
  }
  tree_ = PackingTree::plan(nK, s0, F::kCharacteristicTwo,
                            packing ? declared : std::vector<size_t>{},
                            d_.p_.d_max, chains_,
                            &plan_.options.forced_chains);
  if (!tree_.error.empty())
    fail("domain " + d_.name + ": packing tree: " + tree_.error);
  const int bit_node = tree_.node_of(1);
  const bool bitpack =
      char2pack && bit_node >= 0 && tree_.squaring_chain(bit_node);
  // Bits per packed word: the degree of the bit node's parent.
  word_bits_ =
      bitpack ? tree_.nodes[size_t(tree_.nodes[size_t(bit_node)].parent)].degree
              : 0;
  if (bitpack && word_bits_ > 64)
    fail("domain " + d_.name + ": bits pack into words of " +
         std::to_string(word_bits_) + " bits; at most 64 are supported");
  const size_t W = word_bits_;

  for (const auto &c : d_.circuits_)
    if (c.pred < 0 || pplan_[c.pred].where == Placement::kCircuit) ++ncircuits_;

  // The Boolean checks of BIT_GROUP, one group of the placement rule
  // (placement.h): quadratic triples without relative packing, the circuit
  // (x - x x, in the input layer), or one field batch x^2 - x over their
  // coordinates in node order under relative packing in odd
  // characteristic. The circuit keeps them when it would otherwise be
  // empty.
  ph.reset();
  ph.emplace(compile_times_on() ? "boolean group" : "");
  if (!bit_group.empty()) {
    const F &f = d_.field();
    CheckGroup g;
    for (size_t id : bit_group) g.n += N[id].n;
    bit_group_n_ = g.n;
    g.circuit_terms = kBitCheckTerms * g.n;
    // In the circuit the checks join the input layer, which adds no layer
    // and so no counted bytes; a triple opens its three coordinates.
    // A hit reads the choice, so it needs none of its costs.
    g.bytes_triple = dec ? 0 : 3 * double(g.n) * coord_bytes();
    std::vector<FieldBatchPart<F>> parts;
    if (packing) {
      g.triple_not = "relatively packed subfield cells";
      FieldRelation<F> rel;
      rel.name = "boolean";
      rel.operands = 1;
      rel.monomials = {{f.one(), {0, 0}}, {f.negf(f.one()), {0}}};
      parts = {{rel, AffineOperandMap<F>::columns(f, "boolean", 1, g.n)}};
      g.batch_not = field_batch_error(f, parts, 4);
      const size_t n = g.n;
      g.bytes_batch = [this, n](unsigned w) { return batch_bytes(n, 1, 2, w); };
      if (!dec && d_.p_.rates.measured() && !provisional_pass() &&
          d_.p_.rates.has_batch(g.eval)) {
        // The batch's work (op_counts.h): its kernel over the counting
        // field (none without rates: the batch takes no part in the
        // choice).
        const CountingField<F> cf(f);
        FieldRelation<CountingField<F>> crel;
        crel.name = rel.name;
        crel.operands = rel.operands;
        for (const auto &m : rel.monomials)
          crel.monomials.push_back({m.coeff, m.ops});
        std::vector<FieldBatchPart<CountingField<F>>> cparts = {
            {crel, AffineOperandMap<CountingField<F>>::columns(cf, "boolean",
                                                              1, g.n)}};
        g.work = batch_ops<F, Hash>(
            cf,
            std::make_shared<FieldOperands<CountingField<F>>>(
                cf, std::move(cparts), designated_degree<F>()),
            4);
      }
      for (size_t id : bit_group)
        if (degree_of(id) != degree_of(bit_group[0]))
          g.batch_not = "Bit cells in subfields of several degrees";
    } else {
      g.batch_not = "no relative packing";
    }
    // Only an admissible triple's cost reads the provisional tableau.
    if (!dec && g.triple_not.empty()) {
      g.triple_rows = triple_rows(g.n);
      g.triple_hash_blocks = triple_hash_blocks(g.n);
      g.block_enc = prov_ ? prov_->tableau().block_enc : 0;
    }
    const bool other = ncircuits_ > 0 || !late_bits.empty() ||
                       !d_.checked_derived_.empty();
    const Placement pin = forced("boolean", d_.bit_pin_);
    if (pin == Placement::kQuadratic && !g.triple_not.empty())
      fail("domain " + d_.name + ": Boolean checks pinned to quadratic "
           "triples, but its Bit cells are " + g.triple_not);
    if (pin == Placement::kBatch && !g.batch_not.empty())
      fail("domain " + d_.name + ": Boolean checks pinned to a field batch, "
           "but " + g.batch_not);
    if (dec) {
      // The choice's reasons from the realization; its target is the
      // program's Boolean checks'.
      bit_choice_ = dec->bit_choice;
      bool_work_ = dec->bool_work;
      auto it = dec->type_where.find(bit_group[0]);
      if (it == dec->type_where.end()) {
        if (misfit_.empty())
          misfit_ = "the Boolean check of '" + N[bit_group[0]].name +
                    "' is no predicate of the realized program";
      } else {
        bit_choice_.where = it->second;
      }
      for (size_t id : bit_group) {
        auto jt = dec->type_where.find(id);
        if ((jt == dec->type_where.end() || jt->second != bit_choice_.where) &&
            misfit_.empty())
          misfit_ = "the Boolean checks of the realized program are not one "
                    "group's";
      }
    } else {
      bit_choice_ = choose_placement(d_.p_.rates, g, pin);
      bool_work_ = g.work;
    }
    if (bit_choice_.where != Placement::kCircuit && !other &&
        bit_choice_.where != Placement::kQuadratic) {
      bit_choice_.where = Placement::kCircuit;
      bit_choice_.why = "the circuit would otherwise be empty";
    }
    for (size_t id : bit_group)
      type_checks_.push_back({id, bit_choice_.where});
    if (bit_choice_.where == Placement::kCircuit) {
      checked_bits = bit_group;
    } else if (bit_choice_.where == Placement::kQuadratic) {
      triple_bits_.insert(bit_group.begin(), bit_group.end());
    } else {
      const unsigned w = kernel_width(bit_choice_.width);
      bool_kernel_ = make_field_batch<Hash>(f, std::move(parts), w,
                                            degree_of(bit_group[0]));
      bool_tables_ = bit_group;
      batch_bit_checks_ = g.n;
    }
  }
  // A domain with no circuit constraint (its predicates affine rows,
  // triples or batches) runs no GKR.
  gkr_ = ncircuits_ > 0 || !late_bits.empty() || !checked_bits.empty() ||
         !d_.checked_derived_.empty();

  ph.reset();
  ph.emplace(compile_times_on() ? "input allocation" : "");
  // Public slots and bit views read by circuits.
  std::set<std::pair<size_t, bool>> keys;
  for (const auto &c : d_.circuits_) {
    if (c.pred >= 0 && pplan_[c.pred].where != Placement::kCircuit) continue;
    for (size_t r : c.reads) need(r, keys);
  }
  for (size_t id : d_.checked_derived_) need(id, keys);
  for (size_t id : late_bits) keys.insert({id, true});

  QuadCircuit<F> Q(d_.field());
  const typename D::Backend cbk(&Q);
  const CLogic lc(&cbk, d_.field());
  // On a compile cache hit the circuit comes from the record, and the
  // inputs-only pass builds none: the inputs are counted (their positions,
  // the public and subfield boundaries), and the circuit builder creates
  // none.
  const bool counting = rec != nullptr || inputs_only_;
  size_t counted_pub = 0, counted_sub = 0;
  size_t at = 1;
  for (const auto &k : keys) {
    const size_t n = N[k.first].n;
    slots_.push_back(Slot{k.first, k.second, at});
    at += n;
    if (counting) continue;
    Wires w(n);
    for (auto &x : w) x = lc.eltw_input();
    pub_wires_[k] = std::move(w);
  }
  if (counting)
    counted_pub = at;
  else
    Q.private_input();
  auto alloc = [&](size_t id) {
    cells_[id] = at;
    at += N[id].n;
    if (counting) return;
    Wires w(N[id].n);
    for (auto &x : w) x = lc.eltw_input();
    cell_wires_[id] = std::move(w);
  };
  auto zero_input = [&]() -> size_t {
    filler_.push_back(at++);
    return counting ? 0 : lc.eltw_input();
  };
  // N inputs without wires: a batch's pads.
  auto pad_inputs = [&](size_t n) {
    at += n;
    if (counting) return;
    for (size_t j = 0; j < n; ++j) (void)lc.eltw_input();
  };
  // The alignment inputs before the packed run, asserted zero below.
  Wires alignment;
  for (size_t id : sub) alloc(id);
  std::vector<std::pair<size_t, size_t>> aliases;
  std::vector<TreeInputs::Composed> composed;
  size_t run_begin = at;
  if (bitpack && (!packed.empty() || !views_read_.empty())) {
    while (at % W) alignment.push_back(zero_input());
    run_begin = at;
    // Bit views first, each word's D wires aligned onto the word: a word of
    // the bit node's parent (D = W) aliases one run group; a word of a node
    // above it is a composed view of D / W groups (ComposedBits).
    for (size_t id : views_read_) {
      const size_t words = N[id].deps.at(0);
      const size_t D = degree_of(words);
      if (!above_bits(D))
        fail("bit view '" + N[id].name + "' reads '" + N[words].name +
             "', of type " + type_name(N[words].type) + ", but domain " +
             d_.name + "'s packing tree has no path from GF(2) to GF(2^" +
             std::to_string(D) + ") below K");
      const auto &sel = d_.views_.at(id);
      view_at_[id] = at;
      Wires w(counting ? 0 : N[id].n);
      for (size_t k = 0; k < sel.size(); ++k) {
        if (D == W)
          aliases.push_back({at + D * k, cells_.at(words) + sel[k]});
        else
          composed.push_back({at + D * k, cells_.at(words) + sel[k], D});
        if (counting) continue;
        for (size_t j = 0; j < D; ++j) w[D * k + j] = lc.eltw_input();
      }
      at += N[id].n;
      view_words_ += sel.size();
      if (!counting) view_wires_[id] = std::move(w);
    }
    for (size_t id : packed) {
      alloc(id);
      packed_bits_ += N[id].n;
    }
    while (at % W) {
      zero_input();
      ++packed_zero_bits_;
    }
    packed_bits_ += packed_zero_bits_;
  }
  const size_t run_end = at;
  run_begin_ = run_begin;
  run_end_ = run_end;
  if (counting)
    counted_sub = at;
  else
    Q.begin_full_field();
  for (size_t id : full) alloc(id);

  ph.reset();
  ph.emplace(compile_times_on() ? "batch kernels" : "");
  // Batched relations: tables are phase-0 Subfield variables of this domain;
  // each reduction's pads are committed ambient cells after every variable.
  for (const auto &b : d_.batches_) {
    if (!b.ops) fail("batched relation '" + b.name + "': " + b.missing);
    // Its operands were built at the declared width, which the ablation
    // cannot change.
    if (d_.p_.no_skip)
      fail("batched relation '" + b.name + "': a declared batch keeps its "
           "declared skip width " + std::to_string(b.width) + ", so "
           "DomainProfile::no_skip does not apply to it");
    decl_kernels_.push_back(
        std::make_shared<BatchKernel<F, Hash>>(d_.field(), b.ops, b.width));
    const BatchKernel<F, Hash> &kernel = *decl_kernels_.back();
    size_t words = 0;
    for (size_t id : b.tables) {
      const Node &n = N[id];
      if (n.domain != di || !plan_.cell(id) || n.kind == Kind::kPad ||
          n.kind == Kind::kPadCopy || n.type.base != Base::kSubfield)
        fail("batched relation '" + b.name + "' reads '" + n.name +
             "', which is not a phase-0 Subfield variable of domain " +
             d_.name);
      if (kernel.bit_operands() &&
          (bit_node < 0 || !above_bits(kernel.word_degree())))
        fail("batched relation '" + b.name + "' reads the bits of GF(2^" +
             std::to_string(kernel.word_degree()) + ") words, but domain " +
             d_.name + "'s packing tree has no path from GF(2) to them "
             "below K");
      if (degree_of(id) != kernel.word_degree())
        fail("batched relation '" + b.name + "' reads '" + n.name +
             "' of type " + type_name(n.type) + "; its realization reads "
             "words of degree " + std::to_string(kernel.word_degree()));
      words += n.n;
    }
    if (words != kernel.words())
      fail("batched relation '" + b.name + "': its tables hold " +
           std::to_string(words) + " words, its operand map reads " +
           std::to_string(kernel.words()));
    bplan_.push_back(BatchPlan{b.name, &kernel, at, 0, {}});
    btables_.push_back(b.tables);
    pad_inputs(kernel.pads());
  }
  // The predicates' batches, in group order, then the batched Boolean
  // checks. A batch's operand map is built from its predicates' views; its
  // tables are the cells (and the packed run) the views read, the Boolean
  // checks' the relatively packed Bit cells.
  // The donor (DomainSource::donor) when its layout is this one's: its
  // group kernels are taken for the groups that match.
  const CompiledDomain *donor = nullptr;
  if (source_ != nullptr && source_->donor != nullptr) {
    donor = dynamic_cast<const CompiledDomain *>(
        static_cast<const CompiledDomainBase<S> *>(source_->donor));
    if (donor != nullptr && (donor->cells_ != cells_ ||
                             donor->view_at_ != view_at_ ||
                             donor->groups_.size() != groups_.size()))
      donor = nullptr;
  }
  size_t donor_space = 0;
  for (Group &g : groups_) {
    if (g.choice.where != Placement::kBatch) {
      group_kernels_.push_back(nullptr);
      continue;
    }
    std::shared_ptr<BatchKernel<F, Hash>> kernel;
    const size_t gi = size_t(&g - groups_.data());
    if (donor != nullptr) {
      const Group &h = donor->groups_[gi];
      if (h.choice.where == Placement::kBatch && h.preds == g.preds &&
          h.eval == g.eval && h.word_degree == g.word_degree &&
          h.width == g.width && h.n == g.n && h.degree == g.degree &&
          donor->group_kernels_.at(gi) && donor_space < donor->group_spaces_.size()) {
        kernel = donor->group_kernels_[gi];
        group_spaces_.push_back(donor->group_spaces_[donor_space]);
      }
    }
    if (donor != nullptr && donor->groups_[gi].choice.where == Placement::kBatch)
      ++donor_space;
    if (!kernel) kernel = group_kernel(g);
    std::vector<size_t> tables;
    for (const auto &s : group_spaces_.back())
      if (s.kind == BatchSpace::kTable) tables.push_back(s.node);
    bplan_.push_back(BatchPlan{g.name, kernel.get(), at, 0, {}, 0, g.work});
    btables_.push_back(std::move(tables));
    pad_inputs(kernel->pads());
    group_kernels_.push_back(std::move(kernel));
  }
  // The operand maps hold what the batches read; the batched forms (new
  // expression nodes per predicate, hundreds of MB in the post-quantum
  // mDL's hash domain) are not needed after them.
  for (PredPlan &pp : pplan_) pp.form.reset();
  if (bool_kernel_) {
    for (size_t id : bool_tables_)
      check(degree_of(id) == bool_kernel_->word_degree(),
            "batched Boolean checks: one word degree");
    bplan_.push_back(BatchPlan{d_.name + ".boolean", bool_kernel_.get(), at,
                               0, {}, 0, bool_work_});
    btables_.push_back(bool_tables_);
    pad_inputs(bool_kernel_->pads());
  }

  // The tree's inputs: each of the NINPUTS circuit inputs' node, and the
  // packed run (its aliases and composed views are the caller's).
  auto tree_inputs = [&](size_t ninputs) {
    TreeInputs ti;
    ti.node_of_input.assign(ninputs, -1);
    for (const auto &[id, first] : cells_) {
      const int nd = tree_.node_of(degree_of(id));
      for (size_t i = 0; i < N[id].n; ++i) ti.node_of_input[first + i] = nd;
    }
    for (size_t i : filler_)
      ti.node_of_input[i] =
          tree_.node_of(i >= run_begin && i < run_end ? 1 : W);
    for (const auto &bp : bplan_)
      for (size_t j = 0; j < bp.kernel->pads(); ++j)
        ti.node_of_input[bp.pad_input + j] = 0;
    if (run_end > run_begin) {
      ti.run_begin = run_begin;
      ti.run_end = run_end;
      for (size_t i = run_begin; i < run_end; ++i)
        ti.node_of_input[i] = bit_node;
    }
    return ti;
  };
  // The inputs-only pass ends at the bit node's region of the tree's
  // layout, which the packed run fixes: the GKR pads and the row width,
  // which the circuit and the tableau fix, do not enter it.
  if (inputs_only_) {
    TreeInputs ti = tree_inputs(at);
    ti.aliases = aliases;
    ti.composed = composed;
    const TreeLayout<F> layout(d_.field(), tree_, ti, at, counted_pub,
                               /*gkr_pads=*/0, /*w=*/0, d_.p_.unpacked_s0);
    if (layout.bits >= 0)
      bit_groups_ = layout.region[size_t(layout.bits)].groups;
    return;
  }

  // The record's scheduled circuit is loaded when its input counts are the
  // ones counted above; the constraints below then add their bookkeeping
  // without emitting gates.
  ph.reset();
  ph.emplace(compile_times_on() ? "circuit load" : "");
  std::unique_ptr<Circuit<F>> loaded;
  if (rec && gkr_ && !rec->circuit.empty()) {
    loaded = compiler::circuit_of_record(d_.field(), rec->circuit,
                                         sched_packed_);
    if (loaded == nullptr) {
      misfit_ = "its circuit record is malformed";
    } else if (loaded->ninputs != at || loaded->npub_in != counted_pub ||
               loaded->subfield_boundary != counted_sub) {
      misfit_ = "its circuit's inputs (" + std::to_string(loaded->ninputs) +
                ", public " + std::to_string(loaded->npub_in) +
                ", subfield " + std::to_string(loaded->subfield_boundary) +
                ") are not the domain's (" + std::to_string(at) + ", " +
                std::to_string(counted_pub) + ", " +
                std::to_string(counted_sub) + ")";
      loaded.reset();
    }
  } else if (rec && gkr_) {
    misfit_ = "its record has no circuit";
  } else if (rec && !rec->circuit.empty()) {
    misfit_ = "its record has a circuit, but it runs no GKR";
  }
  loaded_ = rec && misfit_.empty() &&
            (gkr_ ? loaded != nullptr : rec->circuit.empty());
  // A record that does not fit leaves the domain unbuilt (no wires to emit
  // from); the system compiles every domain afresh (system.h).
  if (counting && !loaded_) return;
  const bool emit = loaded == nullptr;

  // Expressions (expr.h) emit through one emitter, so a node that several
  // constraints or views read is emitted once. An affine term's wires are
  // its node's view through its operators' circuit expansions; a staged
  // transform refuses its expansion (OpSpec::emit), so it is never dense.
  ph.reset();
  ph.emplace(compile_times_on() ? "emission" : "");
  ExprEmitter<F, CLogic> emitter(lc, [this, &lc](const Term<F> &t) {
    Wires w = view(lc, t.node);
    for (const auto &op : t.chain) {
      if (!circuit_expandable(*op))
        fail("an expression read by a circuit applies the structured "
             "operator '" + op->name + "', which has no circuit expansion; "
             "place it in affine rows");
      w = expand(lc, *op, w);
    }
    return w;
  });
  emitter_ = &emitter;

  // Boolean checks the circuit carries: late bits, x (x - 1) = 0 on the
  // private view x = t - P, and the Bit cells whose check the placement rule
  // puts in the circuit (full-field Bit cells without relative packing,
  // relatively packed Bit cells in odd characteristic). A bit-packed Bit
  // cell has none.
  using CE = DomainPlan::CircuitEntry;
  for (size_t id : late_bits) {
    type_checks_.push_back({id, Placement::kCircuit});
    circuit_entries_.push_back({CE::kTypeCheck, id, ""});
    if (emit)
      for (size_t x : view(lc, id))
        lc.assert0(lc.mul(x, lc.sub(x, lc.konst(lc.one()))));
    ++late_bits_;
  }
  // Alignment only: each input is zero (fill_cells writes it so). Only the
  // GKR input row reads these inputs, so a domain without GKR checks none.
  if (gkr_ && !alignment.empty())
    circuit_entries_.push_back({CE::kAlignment, alignment.size(), ""});
  if (gkr_ && emit)
    for (size_t x : alignment) lc.assert0(x);
  // A Bit cell is a circuit input, so its check x - x x = 0 is in the
  // input layer: x x and -x are two terms of layer 1, the assertion one
  // term of layer 2 (kBitCheckTerms).
  for (size_t id : checked_bits) {
    circuit_entries_.push_back({CE::kTypeCheck, id, ""});
    if (emit)
      for (size_t x : cell_wires_.at(id)) lc.assert0(lc.sub(x, lc.mul(x, x)));
    cell_bit_checks_ += N[id].n;
    if (!packing) bit_checks_[id] = true;
  }
  // derive(Bit{}): each coordinate of the view is 0 or 1.
  for (size_t id : d_.checked_derived_) {
    type_checks_.push_back({id, Placement::kCircuit});
    circuit_entries_.push_back({CE::kTypeCheck, id, ""});
    if (emit)
      for (size_t x : view(lc, id))
        lc.assert0(lc.mul(x, lc.sub(x, lc.konst(lc.one()))));
    derived_bit_checks_ += N[id].n;
  }
  for (const auto &c : d_.circuits_) {
    if (c.pred >= 0) {
      // A predicate placed in the circuit: its expression, emitted once.
      if (pplan_[c.pred].where != Placement::kCircuit) continue;
      circuit_entries_.push_back({CE::kPredicate, size_t(c.pred), ""});
      const auto &p = d_.preds_[size_t(c.pred)];
      if (!emit) continue;
      if (p.truth)
        emitter.assert_true(p.e);
      else
        emitter.assert_zero(p.e);
      continue;
    }
    circuit_entries_.push_back({CE::kRealization, 0, c.name});
    if (!emit) continue;
    std::vector<Wires> w;
    for (size_t r : c.reads) w.push_back(view(lc, r));
    c.emit(lc, w);
  }
  emitter_ = nullptr;
  // The provisional pass reads the circuit's shape only (its layers' input
  // wires, which fix the GKR pads, and its inputs): the scheduler's quads,
  // the id and the Boolean plan are not built.
  ph.reset();
  ph.emplace(compile_times_on() ? "mkcircuit" : "");
  const bool shape_only =
      provisional_pass() && !plan_.options.full_provisional;
  if (gkr_ && !emit) {
    circ_ = std::move(loaded);
  } else if (gkr_ && shape_only) {
    circ_ = Q.mkcircuit_shape(/*nc=*/1);
  } else if (gkr_) {
    // The id once, below, after the input products it covers.
    circ_ = Q.mkcircuit_without_id(/*nc=*/1);
    sched_packed_ = circ_->packed_bits;
  } else {
    // No layers: the circuit only lays out the inputs.
    circ_ = std::make_unique<Circuit<F>>();
    circ_->nc = 1;
    circ_->ninputs = counting ? at : Q.ninput();
    circ_->npub_in = counting ? counted_pub : Q.npub_input_;
    circ_->subfield_boundary = counting ? counted_sub : Q.subfield_boundary_;
  }
  if (run_end > run_begin) circ_->packed_bits.push_back({run_begin, run_end});
  circ_->packed_input_aliases = std::move(aliases);
  circ_->extension_packing = packing && !d_.p_.unpacked_s0;

  ph.reset();
  ph.emplace(compile_times_on() ? "input products and id" : "");
  // Quadratic rows: Boolean cells (b * b = b) placed there, and user
  // triples.
  if (!packing) {
    for (const auto &[id, first] : cells_) {
      if (!triple_bits_.count(id)) continue;
      bit_checks_[id] = false;
      for (size_t i = 0; i < N[id].n; ++i) {
        circ_->input_products.push_back({first + i, first + i, first + i});
        ++bit_products_;
      }
    }
  }
  for (const auto &q : d_.quads_)
    for (size_t i = 0; i < N[q.a].n; ++i)
      circ_->input_products.push_back(
          {cells_.at(q.a) + i, cells_.at(q.b) + i, cells_.at(q.c) + i});
  // Predicates placed as quadratic triples.
  for (const auto &pp : pplan_) {
    if (pp.where != Placement::kQuadratic) continue;
    for (size_t i = 0; i < N[pp.tri.a].n; ++i)
      circ_->input_products.push_back({cells_.at(pp.tri.a) + i,
                                       cells_.at(pp.tri.b) + i,
                                       cells_.at(pp.tri.c) + i});
  }
  // Batch pads: products of terminal pads, squaring chains.
  for (const auto &bp : bplan_)
    for (const auto &q : bp.kernel->pad_quadratic())
      circ_->input_products.push_back(
          {bp.pad_input + q.x, bp.pad_input + q.y, bp.pad_input + q.z});
  if (!shape_only) {
    // A circuit from the compile cache's record carries its id.
    if (!(gkr_ && !emit))
      ::proofs::circuit_id<F, Hash>(circ_->id, *circ_, d_.field());
    circ_->set_optimizations(d_.p_.optimizations);
  }

  TreeInputs ti = tree_inputs(circ_->ninputs);
  ti.aliases = circ_->packed_input_aliases;
  ti.composed = std::move(composed);

  ph.reset();
  ph.emplace(compile_times_on() ? "ligero choice" : "");
  // Ligero parameters, the tree's layout and the subfield step.
  {
    const size_t nw0 =
        (circ_->ninputs - circ_->npub_in) + ZkCommon<F>::pad_size(*circ_);
    size_t opened = d_.p_.opened();
    LigeroMode mode = d_.p_.ligero_mode();
    if (d_.p_.target) {
      lig_ = dec && dec->lig ? *dec->lig : choose_tableau(ti);
      check_own_rounds(*lig_);
      block_enc_ = lig_->N + 2 * lig_->k - 1;
      opened = lig_->t;
      mode = LigeroMode{true, lig_->masking, lig_->reps};
    } else {
      block_enc_ = d_.p_.block_enc
                       ? d_.p_.block_enc(*circ_, nw0,
                                         ZkCommon<F>::num_quadratic(*circ_))
                       : 0;
    }
    ph.reset();
    ph.emplace(compile_times_on() ? "tree plan" : "");
    tplan_ = std::make_unique<TreePlan<F, Hash>>(
        d_.field(), *circ_, tree_, std::move(ti), d_.p_.rate, opened,
        block_enc_, mode, d_.p_.unpacked_s0, gkr_);
    param_nw_ = tplan_->param->nw;
    param_w_ = tplan_->param->w;
    param_N_ = tplan_->param->block_ext;
    param_k_ = tplan_->param->block;
    param_nrow_ = tplan_->param->nrow;
    // The provisional pass ends at the tableau (provisional_tableau).
    if (provisional_pass()) return;
    subfield_ = PrefixSubfieldTest<F, Hash>(tplan_->prefix_rows(),
                                            tplan_->layout->prefix,
                                            tplan_->layout->nflat);
  }
  ph.reset();
  ph.emplace(compile_times_on() ? "batch coordinates and rows" : "");
  for (auto &bp : bplan_) {
    bp.pad_coord = coord(bp.pad_input);
    for (size_t id : btables_[size_t(&bp - bplan_.data())]) {
      if (id == BatchSpace::kRun) {
        // The packed run's groups: words of the bit node's parent (an
        // aliased group is the word it aliases).
        const auto &l = *tplan_->layout;
        check(l.bits >= 0, "a batch reads the packed run, which has no node");
        const auto &rg = l.region[size_t(l.bits)];
        check(rg.groups * word_bits_ == run_end_ - run_begin_,
              "the packed run's groups");
        bp.table_node = tree_.node_of(word_bits_);
        for (size_t g = 0; g < rg.groups; ++g)
          bp.word_at.push_back(rg.group_at.at(g));
        continue;
      }
      bp.table_node = tree_.node_of(degree_of(id));
      for (size_t j = 0; j < N[id].n; ++j)
        bp.word_at.push_back(coord(cells_.at(id) + j));
    }
  }

  // Affine rows, predicates placed there among them.
  for (const auto &a : d_.affine_) {
    if (a.pred >= 0) {
      const PredPlan &pp = pplan_[size_t(a.pred)];
      if (pp.where != Placement::kAffine) continue;
      const AffineForm<F> &af = *pp.aff;
      const size_t n = af.c.size();
      Rows r{a.name, total_rows_, n, {}};
      for (const auto &t : af.lin.terms) {
        if (t.out_n() != n) fail("predicate '" + a.name + "': term length");
        flatten(t, r.terms);
      }
      bool constant = false;
      for (const auto &c : af.c) constant |= c != d_.field().zero();
      if (constant)
        r.terms.push_back(Flat{d_.field().one(), {}, SIZE_MAX, Flat::kConst,
                               0, n, af.c});
      // Constants through operators of public values: instantiated with
      // the row's other operators (extra).
      for (const auto &k : af.kc)
        r.terms.push_back(Flat{k.scale, k.chain, SIZE_MAX, Flat::kConst, 0,
                               k.values.size(), k.values});
      total_rows_ += n;
      rows_.push_back(std::move(r));
      continue;
    }
    Rows r{a.name, total_rows_, a.e.n, {}};
    for (const auto &t : a.e.terms) {
      if (t.out_n() != a.e.n) fail("affine '" + a.name + "': term length");
      flatten(t, r.terms);
    }
    total_rows_ += a.e.n;
    rows_.push_back(std::move(r));
  }
  ph.reset();
  ph.emplace(compile_times_on() ? "route" : "");
  tplan_->route(extra_nodes());
  // Built from a realized program: every element of the domain is one of
  // the program's.
  if (source_ != nullptr && misfit_.empty()) check_claims(*source_->program);
  if (!misfit_.empty()) loaded_ = false;
}

template <class F, class RSF, class S>
class DomainProver final : public DomainProverBase<S> {
 public:
  using Hash = typename S::Hash;
  using Transcript = BasicTranscript<Hash>;
  using BatchTamper = typename DomainProverBase<S>::BatchTamper;
  explicit DomainProver(const CompiledDomain<F, RSF, S> &cd)
      : cd_(cd),
        scratch_(cd.scratch()),
        f_(cd.domain().field()),
        zk_(cd.circuit(), *cd.tree_plan().param, cd.tree_plan().packed_m(),
            cd.tree_plan().root_m()),
        p_(cd.tree_plan(), f_, *cd.domain().profile().rsf),
        W_(1, cd.circuit().ninputs) {
    p_.scratch = &*scratch_;
  }
  // The scratch's proofs: from the next one on, it keeps its buffers.
  ~DomainProver() override { ++scratch_->proofs; }
  void commit_compute(const ValueStore<S> &v, RandomEngine &rng) override {
    // The phase timers (util/prover_profile.h).
    {
      profiling::Scope sc(F::kCharacteristicTwo ? "bin.fill" : "odd.fill");
      cd_.fill_cells(W_, v);
      for (const auto &b : cd_.batches())
        b.kernel->fill_pads(&W_.v_[b.pad_input], rng);
    }
    p_.commit_compute(zk_, W_, rng);
  }
  void commit_write(Transcript &t) override { p_.commit_write(zk_, t); }
  void ldt(Transcript &t) override {
    if (cd_.list_radius()) p_.ldt_commit(zk_, t);
  }
  // The batches' masked skips and GKR, each on its branch of the nested
  // fork of T (transcript_fork.h), on POOL when given; after the join, the
  // domain's rows, the packing stages and the opening on T.
  bool prove(const ValueStore<S> &v, Transcript &t, bool require_satisfied,
             const BatchTamper &batch_tamper, const BatchTamper &batch_words,
             int swap_round, internal::TaskPool *pool) override {
    auto pub_scope = std::make_unique<profiling::Scope>(
        F::kCharacteristicTwo ? "bin.public" : "odd.public");
    cd_.fill_public(W_, v);
    pub_scope.reset();
    p_.require_satisfied = require_satisfied;
    const size_t nb = cd_.batches().size();
    const std::vector<std::unique_ptr<Transcript>> br =
        fork::split(t, cd_.domain_index(), cd_.field_name(), nb + 1);
    std::vector<typename CompiledDomain<F, RSF, S>::BatchRows> runs(nb);
    msgs_.assign(nb, {});
    auto rows = p_.new_rows();
    rows->rows.scratch = &*scratch_;
    bool gkr_ok = true;
    const auto branch = [&](size_t i) {
      std::string pname;
      if (profiling::enabled()) pname = cd_.branch_profile_name(i);
      profiling::Session ses("gh.prove.branch", pname.c_str(), i, 0);
      Transcript &bt = *br[i];
      if (i == nb) {
        gkr_ok = p_.prove_gkr(zk_, W_, bt, *rows);
        return;
      }
      const auto &b = cd_.batches()[i];
      // The batch's buffers, its own while the branch runs (prover_scratch.h).
      const auto lease = scratch_->batches.lease();
      BatchScratch<F> &bs = *lease;
      bs.keep = scratch_->keep();
      profiling::Scope sc(F::kCharacteristicTwo ? "bin.batch" : "odd.batch");
      auto words_scope = std::make_unique<profiling::Scope>("batch.words");
      std::vector<typename F::Elt> &words = bs.words;
      cd_.batch_words(b, v, W_.v_, words);
      words_scope.reset();
      if (batch_words) {
        typename S::Value a = S::template wrap<F>(words);
        batch_words(i, a);
        words = S::template get<F>(a);
      }
      typename BatchKernel<F, Hash>::Tamper tamper;
      tamper.swap_round = swap_round;
      if (batch_tamper)
        tamper.messages = [&batch_tamper, i](std::vector<typename F::Elt> &m) {
          typename S::Value a = S::template wrap<F>(m);
          batch_tamper(i, a);
          m = S::template get<F>(a);
        };
      runs[i] = b.kernel->reduce(bt, msgs_[i], b.pad_coord, &words,
                                 &W_.v_[b.pad_input], tamper,
                                 cd_.batch_publics(b, v), &bs);
      if (!scratch_->keep()) bs = BatchScratch<F>{};
    };
    internal::run_tasks(pool, nb + 1, branch, cd_.heaviest_branch());
    fork::join(t, br, cd_.domain_index());
    if (!gkr_ok) return false;
    auto prof = std::make_unique<profiling::Scope>(F::kCharacteristicTwo ? "bin.rows.extra" : "odd.rows.extra");
    const auto ex = cd_.extra(v, runs);
    prof.reset();
    check(ex.n == cd_.extra_rows(), "a domain's rows after GKR");
    return p_.prove_rest(zk_, t, ex, *rows);
  }
  void write(std::vector<uint8_t> &out) const override {
    for (const auto &m : msgs_)
      for (const auto &x : m) {
        uint8_t b[F::kBytes];
        f_.to_bytes_field(b, x);
        out.insert(out.end(), b, b + F::kBytes);
      }
    zk_.write(out, f_);
  }

 private:
  const CompiledDomain<F, RSF, S> &cd_;
  // This proof's working buffers, returned to CD_'s pool with the prover.
  typename ScratchPool<DomainScratch<F>>::Lease scratch_;
  const F &f_;
  using Elt = typename F::Elt;
  ZkProof<F, Hash> zk_;
  TreeProver<F, RSF, Hash> p_;
  Dense<F> W_;
  std::vector<std::vector<Elt>> msgs_;
};

template <class F, class RSF, class S>
class DomainVerifier final : public DomainVerifierBase<S> {
 public:
  using Hash = typename S::Hash;
  using Transcript = BasicTranscript<Hash>;
  explicit DomainVerifier(const CompiledDomain<F, RSF, S> &cd)
      : cd_(cd),
        f_(cd.domain().field()),
        zk_(cd.circuit(), *cd.tree_plan().param, cd.tree_plan().packed_m(),
            cd.tree_plan().root_m()),
        v_(cd.tree_plan(), *cd.domain().profile().rsf, f_) {}
  bool read(ReadBuffer &rb) override {
    msgs_.assign(cd_.batches().size(), {});
    for (size_t i = 0; i < msgs_.size(); ++i)
      for (size_t j = 0; j < cd_.batches()[i].kernel->message_elts(); ++j) {
        if (!rb.have(F::kBytes)) return false;
        auto x = f_.of_bytes_field(rb.next(F::kBytes));
        if (!x) return false;
        msgs_[i].push_back(*x);
      }
    return zk_.read(rb, f_);
  }
  void recv(Transcript &t) override { v_.recv_commitment(zk_, t); }
  void ldt(Transcript &t) override {
    if (cd_.list_radius()) v_.recv_ldt(zk_, t);
  }
  bool verify(const ValueStore<S> &v, Transcript &t,
              internal::TaskPool *pool) override {
    auto pub_scope = std::make_unique<profiling::Scope>(
        F::kCharacteristicTwo ? "bin.v.public" : "odd.v.public");
    Dense<F> pub(1, cd_.circuit().ninputs);
    for (auto &x : pub.v_) x = f_.zero();
    cd_.fill_public(pub, v);
    pub_scope.reset();
    const size_t nb = cd_.batches().size();
    const std::vector<std::unique_ptr<Transcript>> br =
        fork::split(t, cd_.domain_index(), cd_.field_name(), nb + 1);
    std::vector<typename CompiledDomain<F, RSF, S>::BatchRows> runs(nb);
    auto rows = v_.new_rows();
    const auto branch = [&](size_t i) {
      std::string pname;
      if (profiling::enabled()) pname = cd_.branch_profile_name(i);
      profiling::Session ses("gh.verify.branch", pname.c_str(), i, 0);
      Transcript &bt = *br[i];
      if (i == nb) {
        v_.verify_gkr(zk_, pub, bt, *rows);
        return;
      }
      const auto &b = cd_.batches()[i];
      profiling::Scope sc(F::kCharacteristicTwo ? "bin.v.batch" : "odd.v.batch");
      runs[i] = b.kernel->reduce(bt, msgs_[i], b.pad_coord, nullptr, nullptr,
                                 {}, cd_.batch_publics(b, v));
    };
    internal::run_tasks(pool, nb + 1, branch, cd_.heaviest_branch());
    fork::join(t, br, cd_.domain_index());
    auto prof = std::make_unique<profiling::Scope>(F::kCharacteristicTwo ? "bin.v.rows.extra" : "odd.v.rows.extra");
    const auto ex = cd_.extra(v, runs);
    prof.reset();
    check(ex.n == cd_.extra_rows(), "a domain's rows after GKR");
    const bool opened = v_.verify_rest(zk_, t, ex, *rows);
    // The subfield step reads the prefix rows of the same openings.
    profiling::Scope sc(F::kCharacteristicTwo ? "bin.v.subfield" : "odd.v.subfield");
    return opened && cd_.subfield_test().verify(*cd_.tree_plan().param,
                                                zk_.com_proof, f_);
  }

 private:
  const CompiledDomain<F, RSF, S> &cd_;
  const F &f_;
  ZkProof<F, Hash> zk_;
  TreeVerifier<F, RSF, Hash> v_;
  std::vector<std::vector<typename F::Elt>> msgs_;
};

template <class F, class RSF, class S>
std::unique_ptr<DomainProverBase<S>> CompiledDomain<F, RSF, S>::prover()
    const {
  return std::make_unique<DomainProver<F, RSF, S>>(*this);
}
template <class F, class RSF, class S>
std::unique_ptr<DomainVerifierBase<S>>
CompiledDomain<F, RSF, S>::verifier() const {
  return std::make_unique<DomainVerifier<F, RSF, S>>(*this);
}
}  // namespace proofs::gordiehowe::compiler

namespace proofs::gordiehowe {
template <class F, class RSF, class S>
std::unique_ptr<CompiledDomainBase<S>> DomainImpl<F, RSF, S>::compile(
    const CompilePlan &plan, const DomainSource *source) const {
  // With measured rates, a provisional pass first: every group at its
  // default target, whose tableau the placement costs count rows against.
  // The inputs-only pass gives the bit node's groups; the full pass, which
  // emits the circuit, runs when an admissible triple's cost first reads
  // its tableau. A test that records the tableau, or asks for it up front
  // (CompileOptions::eager_provisional), reads it whole.
  using CD = compiler::CompiledDomain<F, RSF, S>;
  using Tableau = typename CD::ProvisionalTableau;
  // A domain built from a realized program reads its decisions, which no
  // cost enters, so it runs no provisional pass.
  std::optional<typename CD::Provisional> prov;
  if (source == nullptr && p_.rates.measured() && !compiler::provisional_pass()) {
    auto full = [this, &plan]() -> Tableau {
      const compiler::ProvisionalPass pass;
      GH_COMPILE_REGION("provisional");
      return CD(*this, plan, nullptr).provisional_tableau();
    };
    if (plan.options.eager_provisional) {
      prov.emplace(full());
    } else {
      const compiler::ProvisionalPass pass;
      GH_COMPILE_REGION("provisional inputs");
      prov.emplace(CD(*this, plan, typename CD::InputsOnly{}).bit_groups(),
                   full);
    }
  }
  std::unique_ptr<CD> cd;
  {
    GH_COMPILE_REGION("final");
    cd = std::make_unique<CD>(*this, plan, source, prov ? &*prov : nullptr);
  }
  if (auto *r = plan.options.provisional_record; r && prov) {
    const Tableau &t = prov->tableau();
    (*r)[this->name] = {t.w, t.block_enc, t.nq, t.nrow, prov->bit_groups()};
  }
  return cd;
}

}  // namespace proofs::gordiehowe

#endif  // PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_COMPILER_COMPILED_DOMAIN_H_
