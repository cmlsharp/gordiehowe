// Copyright 2026 Chad Sharp and Paul Grubbs
// SPDX-License-Identifier: Apache-2.0

// GordieHowe: the realizations of conv(x, y).
//
// conv(x, y) (expr.h) is the acyclic convolution of x [..., lx] and
// y [..., ly] along the last axis. Interval propagation reads it as such
// (range.h's expr_interval), before this lowering runs, so a no-wrap check
// (assert_mod's m = 0, the integer equality) holds whatever the
// realization. The conv lowering replaces each conv node of a predicate,
// once per node, by an affine expression in new committed values, with the
// predicates that define them. Each realization computes conv mod p
// exactly: the transform length M is the least power of two with
// M >= lx + ly - 1, so the negacyclic product of the zero-extended operands
// has no wrapped term.
//
//   kDirect  C = conv(x, y) committed ([..., lx + ly - 1]), and
//            C_i = sum_{a+b=i} x_a y_b as one predicate in the circuit
//            (sparse sums of products; a row whose two operands are the
//            same row of one value sums a <= b, 2 x_a x_b for a < b).
//            conv(x, y) reads as C.
//   kBatch   z = NTT_M(x) NTT_M(y) committed ([..., M]) and proved by one
//            field batch (a masked zerocheck over B M instances) over the
//            affine views NTT_M(x), NTT_M(y) (SpectralConvMap, whose
//            adjoint is the transposed transform). In a predicate affine in
//            its convolutions, conv(x, y) reads as the first lx + ly - 1
//            coordinates of INTT_M(z), an affine view. In any other
//            predicate (INTT_M has no circuit expansion) C is committed
//            too, with the affine rows C = INTT_M(z)[0, lx + ly - 1), and
//            conv(x, y) reads as C. It needs x and y to be rows of
//            committed phase-0 values of the designated subfield (a
//            handle, or a row reindex of one), read directly or through
//            one public operator batched over blocks inside rows (the
//            limbs of digit rows, from_digits), and a transform of length
//            M over the field.
//
// The choice is the placement rule's (placement.h) over one check group
// per conv: the direct form is its circuit target (the products' quad
// terms and C's committed coordinates), the batch its batch target (B M
// instances of three operands at degree 2, z's committed coordinates, and
// C's where it is committed), each costed by the domain's rates (unit
// rates without measured ones), the direct form the default
// (placement.h). The direct form is the only one where the batch is not
// admissible: a field without the transform, or an operand that is not
// rows of a committed value. A pin (ConvExpr::pin) fixes the realization; a pinned batch
// that is not admissible is a CompileError naming why.

#ifndef PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_COMPILER_CONV_H_
#define PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_COMPILER_CONV_H_

#include <algorithm>
#include <cstddef>
#include <cstdint>
#include <functional>
#include <map>
#include <memory>
#include <optional>
#include <set>
#include <string>
#include <utility>
#include <vector>

#include "gordiehowe/closure_expr.h"
#include "gordiehowe/compiler/batch.h"
#include "gordiehowe/compiler/lowering.h"
#include "gordiehowe/compiler/op_counts.h"
#include "gordiehowe/compiler/placement.h"
#include "gordiehowe/core.h"
#include "gordiehowe/domain.h"
#include "gordiehowe/expr.h"
#include "gordiehowe/ops/ntt.h"
#include "gordiehowe/ops/operators.h"
#include "gordiehowe/subfield.h"
#include "gordiehowe/system.h"

namespace proofs::gordiehowe::compiler {

// The batch realization's operands: instance (b, j) reads
// x_hat_j = NTT_M(x_b)_j, y_hat_j = NTT_M(y_b)_j and z_bj. Each operand
// side is a table of R rows of l entries, x_b its row ROWS[b], zero-padded
// to M; z ([B][M]) starts at word Z_AT. A side's table is R rows of IN_L
// words at word offset AT, read through OP when it has one (a public
// block-diagonal operator, a row of IN_L words to a row of l entries: the
// limbs of digit rows, from_digits), as the words themselves otherwise
// (IN_L = l). The relation is x_hat y_hat - z. The adjoint applies the transform's transpose
// (M^T w = n R M^-1 w, ops::InverseNttOperator), so the verifier's
// terminal row costs 2 B transforms.
template <class F>
class SpectralConvMap final : public FieldOperandMap<F> {
  using Elt = typename F::Elt;

 public:
  struct Side {
    size_t at = 0, R = 0, l = 0;
    std::vector<size_t> rows;
    size_t in_l = 0;
    std::shared_ptr<const LinearOperator<F>> op = nullptr;
    // OP's name and parameters (the system digest).
    std::vector<uint8_t> op_id = {};
    size_t words() const { return R * (op ? in_l : l); }
  };
  SpectralConvMap(const F &f, size_t M, const Elt &psi, Side a, Side b,
                  size_t z_at, size_t words)
      : f_(f), ntt_(f, M, psi), psi_(psi), M_(M), a_(std::move(a)),
        b_(std::move(b)), z_at_(z_at), words_(words) {}
  std::string name() const override { return "conv_spectral_product"; }
  std::vector<uint8_t> params() const override {
    std::vector<uint8_t> out;
    put_u64(out, M_);
    for (const Side *s : {&a_, &b_}) {
      put_u64(out, s->at);
      put_u64(out, s->R);
      put_u64(out, s->l);
      put_u64(out, s->rows.size());
      for (size_t r : s->rows) put_u64(out, r);
      if (s->op) {
        put_u64(out, s->in_l);
        out.insert(out.end(), s->op_id.begin(), s->op_id.end());
      }
    }
    put_u64(out, z_at_);
    put_u64(out, words_);
    ops::poly_detail::put_elt(out, f_, psi_);
    return out;
  }
  size_t operands() const override { return 3; }
  size_t instances() const override { return a_.rows.size() * M_; }
  size_t words() const override { return words_; }
  std::vector<std::vector<Elt>> apply(
      const F &f, const std::vector<Elt> &w) const override {
    const auto ha = spectra(f, w, a_);
    const bool shared = same_table();
    const auto hb = shared ? std::vector<std::vector<Elt>>{} : spectra(f, w, b_);
    const auto &hbr = shared ? ha : hb;
    std::vector<std::vector<Elt>> out(instances());
    for (size_t b = 0; b < a_.rows.size(); ++b)
      for (size_t j = 0; j < M_; ++j)
        out[b * M_ + j] = {ha[a_.rows[b]][j], hbr[b_.rows[b]][j],
                           w[z_at_ + b * M_ + j]};
    return out;
  }
  void adjoint(const F &f, const std::vector<Elt> &weight,
               const std::vector<Elt> &u, std::vector<Elt> &a,
               Elt &constant) const override {
    a.assign(words(), f.zero());
    constant = f.zero();
    const Elt nn = f.of_scalar(uint64_t(M_));
    std::vector<Elt> v(M_);
    // The adjoint on each side's table entries ([R][l]), then on its words.
    std::vector<Elt> ga(a_.R * a_.l, f.zero()), gb(b_.R * b_.l, f.zero());
    for (size_t b = 0; b < a_.rows.size(); ++b) {
      for (unsigned op = 0; op < 2; ++op) {
        const Side &s = op == 0 ? a_ : b_;
        // x = M^T (u_op w_b): x_0 = n (M^-1 y)_0, x_i = -n (M^-1 y)_(n-i).
        for (size_t j = 0; j < M_; ++j)
          v[j] = f.mulf(u[op], weight[b * M_ + j]);
        ntt_.inverse(v);
        Elt *dst = &(op == 0 ? ga : gb)[s.rows[b] * s.l];
        f.add(dst[0], f.mulf(nn, v[0]));
        for (size_t i = 1; i < s.l; ++i) f.sub(dst[i], f.mulf(nn, v[M_ - i]));
      }
      for (size_t j = 0; j < M_; ++j)
        f.add(a[z_at_ + b * M_ + j], f.mulf(u[2], weight[b * M_ + j]));
    }
    words_adjoint(f, a_, ga, a);
    words_adjoint(f, b_, gb, a);
  }

 private:
  // Whether both sides read one table the same way.
  bool same_table() const {
    return a_.at == b_.at && a_.l == b_.l && a_.op == b_.op;
  }
  // A += the words' part of G, the adjoint on side S's entries: G itself,
  // or OP^T G.
  static void words_adjoint(const F &f, const Side &s,
                            const std::vector<Elt> &g, std::vector<Elt> &a) {
    if (!s.op) {
      for (size_t i = 0; i < g.size(); ++i) f.add(a[s.at + i], g[i]);
      return;
    }
    std::vector<Elt> x(s.words());
    s.op->transpose_apply(g.data(), x.data());
    for (size_t i = 0; i < x.size(); ++i) f.add(a[s.at + i], x[i]);
  }
  // The transforms of every row of side S's table.
  std::vector<std::vector<Elt>> spectra(const F &f, const std::vector<Elt> &w,
                                        const Side &s) const {
    std::vector<Elt> rows(s.R * s.l);
    if (s.op) {
      s.op->apply(w.data() + s.at, rows.data());
    } else {
      std::copy(w.begin() + long(s.at), w.begin() + long(s.at + rows.size()),
                rows.begin());
    }
    std::vector<std::vector<Elt>> hat(s.R);
    for (size_t r = 0; r < s.R; ++r) {
      hat[r].assign(M_, f.zero());
      std::copy(rows.begin() + long(r * s.l),
                rows.begin() + long((r + 1) * s.l), hat[r].begin());
      ntt_.forward(hat[r]);
    }
    return hat;
  }

  const F &f_;
  ops::NegacyclicNtt<F> ntt_;
  Elt psi_;
  size_t M_;
  Side a_, b_;
  size_t z_at_, words_;
};

// The conv lowering of one domain (realize_convs).
template <class F, class S>
class ConvRealizer : Lowering {
  using Elt = typename F::Elt;
  using Node_ = ExprNode<F>;

 public:
  ConvRealizer(Domain<F> &d, ConstraintSystemBuilder<S> &b)
      : d_(d), b_(b), f_(d.field()) {}

  // Rewrites every predicate that holds a conv; whether one did.
  bool run() {
    bool any = false;
    const size_t np = predicate_count(d_);
    for (size_t k = 0; k < np; ++k) {
      const ExprPtr<F> e = predicate_expr(d_, k);
      if (!has_conv(*e)) continue;
      if (!any) phase_ = b_.phases();
      any = true;
      pred_ = predicate_name(d_, k);
      affine_ctx_ = affine_in_convs(*e);
      const ExprPtr<F> ne = go(e);
      rewrite_predicate(d_, k, ne);
    }
    return any;
  }

 private:
  // A row view: x [B][l] is rows ROWS of a table [R][l]: the committed
  // node NODE itself, or NODE ([R][in_l]) through the public block-diagonal
  // operator OP (each row of in_l words to a row of l entries; the limbs of
  // digit rows, from_digits), the table expression TABLE.
  struct RowView {
    size_t node = 0, R = 0, l = 0;
    std::vector<size_t> rows;
    size_t in_l = 0;
    std::shared_ptr<const OpSpec<F>> op = nullptr;
    ExprPtr<F> table = nullptr;
  };
  // Whether two row views read one table the same way.
  static bool same_table(const RowView &a, const RowView &b) {
    return a.node == b.node && a.l == b.l && a.op == b.op;
  }

  bool has_conv(const Node_ &x) {
    auto it = seen_.find(&x);
    if (it != seen_.end()) return it->second;
    bool any = x.op == ExprOp::kConv;
    for (const auto &k : x.kids) any = has_conv(*k) || any;
    seen_[&x] = any;
    return any;
  }
  // Whether X is affine once each conv of affine operands is a leaf: the
  // context in which INTT_M(z) may stand for a conv (elsewhere the batch
  // commits C).
  bool affine_in_convs(const Node_ &x) const {
    switch (x.op) {
      case ExprOp::kLin:
      case ExprOp::kConst:
        return true;
      case ExprOp::kConv:
        return expr_degree(x.kids[0]) <= 1 && expr_degree(x.kids[1]) <= 1;
      case ExprOp::kAdd:
      case ExprOp::kGather:
        for (const auto &k : x.kids)
          if (!affine_in_convs(*k)) return false;
        return true;
      case ExprOp::kScale:
      case ExprOp::kApply:
      case ExprOp::kSum:
      case ExprOp::kBroadcast:
        return affine_in_convs(*x.kids[0]);
      case ExprOp::kMul:
        for (int s = 0; s < 2; ++s)
          if (expr_degree(x.kids[s]) == 0) return affine_in_convs(*x.kids[1 - s]);
        return false;
      default:
        return false;
    }
  }

  // X rebuilt over its rewritten kids (each conv realized once).
  ExprPtr<F> go(const ExprPtr<F> &x) {
    auto it = memo_.find(x.get());
    if (it != memo_.end()) return it->second;
    std::vector<ExprPtr<F>> kids;
    bool changed = false;
    for (const auto &k : x->kids) {
      kids.push_back(go(k));
      changed |= kids.back() != k;
    }
    ExprPtr<F> out = x;
    if (x->op == ExprOp::kConv) {
      out = realize(*x, kids[0], kids[1]);
    } else if (changed) {
      auto n = std::make_shared<Node_>(*x);
      n->kids = std::move(kids);
      // The derived flags of the new kids: a leaf's own operators, an
      // operator node's own, and the kids'.
      n->structured = false;
      n->structured_op.clear();
      if (n->op == ExprOp::kApply && !circuit_expandable(*n->apply)) {
        n->structured = true;
        n->structured_op = n->apply->name;
      }
      expr_internal::inherit(*n);
      out = n;
    }
    memo_[x.get()] = out;
    return out;
  }

  // The row view X is, or none: a handle on a whole node (its rows), or a
  // reindex of whole rows of one; the node read directly or through one
  // public operator, batched over blocks that each lie in one row.
  std::optional<RowView> row_view(const ExprPtr<F> &xp, size_t l) const {
    const Node_ &x = *xp;
    ExprPtr<F> leafp = xp;
    const std::vector<size_t> *idx = nullptr;
    if (x.op == ExprOp::kGather && x.kids.size() == 1) {
      leafp = x.kids[0];
      idx = &x.idx.vec();
    }
    const Node_ *leaf = leafp.get();
    if (leaf->op != ExprOp::kLin || leaf->lin.terms.size() != 1) return {};
    const Term<F> &t = leaf->lin.terms[0];
    if (t.scale != f_.one() || t.chain.size() > 1) return {};
    if (l == 0 || leaf->n % l != 0 || x.n % l != 0) return {};
    RowView v;
    v.node = t.node;
    v.R = leaf->n / l;
    v.l = l;
    v.in_l = l;
    if (t.chain.empty()) {
      if (t.in_n != leaf->n) return {};
    } else {
      // One batched operator of no dependencies whose blocks lie in rows:
      // B blocks with R | B.
      const auto &op = t.chain[0];
      if (op->name != "batched" || !op->deps.empty() || !op->make ||
          op->params.size() < 8 || op->rows != leaf->n || t.in_n % v.R != 0)
        return {};
      uint64_t blocks = 0;
      for (size_t i = 0; i < 8; ++i)
        blocks |= uint64_t(op->params[i]) << (8 * i);
      if (blocks == 0 || blocks % v.R != 0) return {};
      v.in_l = t.in_n / v.R;
      v.op = op;
      v.table = leafp;
    }
    for (size_t b = 0; b < x.n / l; ++b) {
      const size_t j0 = idx ? (*idx)[b * l] : b * l;
      if (j0 % l != 0) return {};
      for (size_t i = 0; i < l; ++i) {
        const size_t j = idx ? (*idx)[b * l + i] : b * l + i;
        if (j != j0 + i) return {};
      }
      v.rows.push_back(j0 / l);
    }
    return v;
  }
  // Why the batch cannot realize a conv over A and B (empty: it can).
  std::string batch_not(const std::optional<RowView> &a,
                        const std::optional<RowView> &b,
                        const std::optional<Elt> &psi) const {
    if (!psi) return "the field has no transform of the length";
    const auto &N = b_.system().graph().nodes;
    for (const auto *v : {&a, &b}) {
      if (!*v) return "an operand is not rows of one committed value";
      const Node &n = N.at((*v)->node);
      if (n.domain != d_.index) return "an operand lies in another domain";
      if (n.kind != Kind::kPrivateInput && n.kind != Kind::kAdvice)
        return "the operand '" + n.name + "' is not a committed value";
      if (n.type.base != Base::kSubfield || n.type.degree != 0)
        return "the operand '" + n.name + "' is not of the designated subfield";
      if (phase_.at((*v)->node) != 0)
        return "the operand '" + n.name + "' is a late value";
    }
    return "";
  }

  // The name of the next realization's values.
  std::string next_name() {
    const std::string nm =
        pred_ + ".conv" + (count_ == 0 ? "" : std::to_string(count_));
    ++count_;
    return nm;
  }

  // C = conv(a, b) committed, of shape OUT: a Subfield value when both
  // operands lie in the designated subfield. The generator multiplies by
  // the transform of length M when the field has one (PSI), schoolbook
  // otherwise.
  Ref<F> commit_product(const std::string &nm, const Shape &out,
                        const ExprPtr<F> &a, const ExprPtr<F> &b, size_t la,
                        size_t lb, size_t M, const std::optional<Elt> &psi) {
    const F *pf = &f_;
    auto fn = [pf, la, lb, M, psi](const Tensor<Elt> &x, const Tensor<Elt> &y) {
      const F &f = *pf;
      const size_t lo = la + lb - 1;
      const size_t rows = x.size() / la;
      std::vector<Elt> c(rows * lo, f.zero());
      if constexpr (ops::kFieldNtt<F>) {
        if (psi) {
          const ops::NegacyclicNtt<F> ntt(f, M, *psi);
          std::vector<Elt> u(M), v(M);
          for (size_t r = 0; r < rows; ++r) {
            std::fill(u.begin(), u.end(), f.zero());
            std::fill(v.begin(), v.end(), f.zero());
            std::copy(x.begin() + r * la, x.begin() + (r + 1) * la, u.begin());
            std::copy(y.begin() + r * lb, y.begin() + (r + 1) * lb, v.begin());
            ntt.forward(u);
            ntt.forward(v);
            for (size_t j = 0; j < M; ++j) u[j] = f.mulf(u[j], v[j]);
            ntt.inverse(u);
            std::copy(u.begin(), u.begin() + long(lo), c.begin() + r * lo);
          }
          return c;
        }
      }
      for (size_t r = 0; r < rows; ++r)
        for (size_t u = 0; u < la; ++u)
          for (size_t v = 0; v < lb; ++v)
            f.add(c[r * lo + u + v], f.mulf(x[r * la + u], y[r * lb + v]));
      return c;
    };
    const auto deps = depends_on(Expr<F>(a), Expr<F>(b));
    if (in_sub(a) && in_sub(b))
      return Ref<F>(priv(d_, Subfield{}, nm, out, deps, fn));
    return Ref<F>(priv(d_, Field{}, nm, out, deps, fn));
  }
  bool in_sub(const ExprPtr<F> &e) const {
    if (!d_.has_subfield) return false;
    const Graph &g = b_.system().graph();
    std::string why;
    return in_subfield_expr<F>(
        f_, e, [&g](size_t id) { return g.nodes.at(id).type; }, why);
  }
  std::shared_ptr<Placement> circuit_pin() const {
    return std::make_shared<Placement>(Placement::kCircuit);
  }
  static Lin<F> leaf_lin(const Ref<F> &r, const std::vector<size_t> &dims) {
    Lin<F> l = Lin<F>(r);
    l.shape = dims;
    return l;
  }

  // The direct form's products over row views RA, RB of B rows: la lb per
  // row, la (la + 1) / 2 for a row whose operands are one row of one value.
  static size_t products(const std::optional<RowView> &ra,
                         const std::optional<RowView> &rb, size_t la,
                         size_t lb, size_t B) {
    const bool same = ra && rb && same_table(*ra, *rb);
    size_t n = 0;
    for (size_t r = 0; r < B; ++r) {
      const bool square = same && ra->rows[r] == rb->rows[r];
      n += square ? la * lb - la * (la - 1) / 2 : la * lb;
    }
    return n;
  }

  // The realization of a conv of B rows of LO coefficients, transform
  // length M and PRODUCTS direct products, its C in the subfield when SUB,
  // under PIN: the placement rule over its check group (the direct form
  // its circuit target, the batch its batch target). WHY is the reason,
  // with the candidates' costs.
  ConvRealization choose(ConvRealization pin, const std::string &no_batch,
                         size_t B, size_t lo, size_t M, size_t products,
                         bool sub, const OpCounts &work,
                         std::string &why) const {
    const PlacementRates &rates = d_.rates();
    CheckGroup g;
    g.n = B * M;
    g.work = work;
    g.operands = 3;
    g.degree = 2;
    g.eval = designated_degree<F>() < field_degree<F>() ? BatchEval::kSubfield
                                                         : BatchEval::kField;
    g.triple_not = "a convolution is not a b - c";
    g.circuit_terms = products + B * lo;
    g.batch_not = no_batch;
    g.cells_circuit = B * lo;
    g.cells_batch = B * M + (affine_ctx_ ? 0 : B * lo);
    g.cells_sub = sub;
    const Placement p = pin == ConvRealization::kDirect  ? Placement::kCircuit
                        : pin == ConvRealization::kBatch ? Placement::kBatch
                                                         : Placement::kAuto;
    const PlacementChoice ch = choose_placement(rates, g, p);
    why = ch.why + ": " + ch.costs();
    return ch.where == Placement::kBatch ? ConvRealization::kBatch
                                         : ConvRealization::kDirect;
  }

  // The realization of the conv node X over the rewritten operands A, B.
  ExprPtr<F> realize(const Node_ &x, const ExprPtr<F> &a,
                     const ExprPtr<F> &b) {
    const size_t la = a->dims().back();
    const size_t lb = b->dims().back();
    const size_t lo = la + lb - 1;
    const size_t B = x.n / lo;
    size_t M = 1;
    while (M < lo) M *= 2;
    const std::vector<size_t> out = x.dims();
    std::optional<Elt> psi;
    if constexpr (ops::kFieldNtt<F>) psi = ops::FieldNtt<F>::root(f_, 2 * M);
    const auto ra = row_view(a, la);
    const auto rb = row_view(b, lb);
    const std::string no_batch = batch_not(ra, rb, psi);
    const std::string nm = next_name();
    if (*x.conv_pin == ConvRealization::kBatch && !no_batch.empty())
      fail("conv in '" + pred_ + "' is pinned to the batch, but " + no_batch);
    std::string why;
    OpCounts work;
    if constexpr (ops::kFieldNtt<F>) {
      // Counted only when the rates price the batch (placement.h).
      const BatchEval eval = designated_degree<F>() < field_degree<F>()
                                 ? BatchEval::kSubfield
                                 : BatchEval::kField;
      if (no_batch.empty() && d_.rates().has_batch(eval))
        work = batch_work(*ra, *rb, M, B);
    }
    const ConvRealization r =
        choose(*x.conv_pin, no_batch, B, lo, M, products(ra, rb, la, lb, B),
               in_sub(a) && in_sub(b), work, why);
    const bool commit_c = r == ConvRealization::kDirect || !affine_ctx_;
    auto &sum = b_.summary();
    sum.report.push_back(
        "conv '" + nm + "': [" + std::to_string(B) + "] x (" +
        std::to_string(la) + " * " + std::to_string(lb) + ") -> " +
        std::to_string(lo) + ", M = " + std::to_string(M) + ", " +
        conv_realization_name(r) +
        (r == ConvRealization::kBatch && commit_c ? " with C committed" : "") +
        " (" + (*x.conv_pin == ConvRealization::kAuto ? why : "pinned") +
        ")");
    put_str(sum.descr, nm);
    put_u64(sum.descr, uint64_t(r));
    put_u64(sum.descr, B);
    put_u64(sum.descr, la);
    put_u64(sum.descr, lb);
    put_u64(sum.descr, M);
    if (r == ConvRealization::kBatch && commit_c) put_str(sum.descr, "c");
    if (r == ConvRealization::kBatch) {
      if constexpr (ops::kFieldNtt<F>) {
        return batch(nm, a, b, *ra, *rb, out, la, lb, M, *psi, commit_c, &x, B);
      }
    }
    const Ref<F> C =
        commit_product(nm + ".c", Shape(out), a, b, la, lb, M, psi);
    direct(nm, C, a, b, ra, rb, la, lb, B);
    return expr_internal::leaf(leaf_lin(C, out));
  }

  // The work of one proof of the spectral batch over the row views RA, RB
  // of B rows at transform length M (op_counts.h): the zerocheck's kernel
  // over CountingField<F> on three operand columns, and the operand map's
  // transforms by their butterflies (a negacyclic transform of length M:
  // its M twists and (M / 2) log2 M butterflies of a product and two
  // sums), forward on each side's rows (apply) and inverse twice per row
  // (adjoint), with the adjoint's per-coordinate products and sums. A
  // view's operator (row_view's OP) is not counted.
  OpCounts batch_work(const RowView &ra, const RowView &rb, size_t M,
                      size_t B) const {
    using CF = CountingField<F>;
    const CF cf(f_);
    FieldRelation<CF> rel;
    rel.name = "x_hat y_hat - z";
    rel.operands = 3;
    rel.monomials = {{f_.one(), {0, 1}}, {f_.mone(), {2}}};
    std::vector<FieldBatchPart<CF>> parts = {
        {rel, AffineOperandMap<CF>::columns(cf, rel.name, 3, B * M)}};
    OpCounts w = batch_ops<F, typename S::Hash>(
        cf,
        std::make_shared<FieldOperands<CF>>(cf, std::move(parts),
                                            field_degree<F>()),
        4);
    size_t lg = 0;
    while ((size_t(1) << lg) < M) ++lg;
    const uint64_t butterflies = uint64_t(M / 2) * lg;
    const uint64_t forward = (same_table(ra, rb) ? ra.R : ra.R + rb.R);
    const uint64_t inverse = 2 * uint64_t(B);
    const uint64_t transforms = forward + inverse;
    w.mul += transforms * (M + butterflies) + inverse * (M + ra.l) +
             uint64_t(B) * M;
    w.add += transforms * 2 * butterflies + inverse * ra.l + uint64_t(B) * M;
    return w;
  }

  // C - sum_{u+v=i} a_u b_v = 0 in the circuit.
  void direct(const std::string &nm, const Ref<F> &C, const ExprPtr<F> &a,
              const ExprPtr<F> &b, const std::optional<RowView> &ra,
              const std::optional<RowView> &rb, size_t la, size_t lb,
              size_t B) {
    const size_t lo = la + lb - 1;
    const bool same = ra && rb && same_table(*ra, *rb);
    std::vector<size_t> ia, ib;
    std::vector<std::vector<std::pair<size_t, uint64_t>>> rows(B * lo);
    for (size_t r = 0; r < B; ++r) {
      const bool square = same && ra->rows[r] == rb->rows[r];
      for (size_t u = 0; u < la; ++u)
        for (size_t v = square ? u : 0; v < lb; ++v) {
          rows[r * lo + u + v].push_back({ia.size(), square && u != v ? 2 : 1});
          ia.push_back(r * la + u);
          ib.push_back(r * lb + v);
        }
    }
    const Expr<F> prod =
        Expr<F>(a).flat().reindex(ia) * Expr<F>(b).flat().reindex(ib);
    const Expr<F> sums =
        ops::sparse_matrix(f_, "conv_sums", ia.size(), rows)(prod);
    const Expr<F> e = Expr<F>(C).flat() - sums;
    add_predicate(d_, nm + ".products", e.node, circuit_pin());
  }

  // z = NTT_M(a) NTT_M(b) committed and batched; conv reads as the first
  // lo coordinates of INTT_M(z), or, when COMMIT_C, as C committed with
  // the affine rows C = INTT_M(z)[0, lo).
  ExprPtr<F> batch(const std::string &nm, const ExprPtr<F> &a,
                   const ExprPtr<F> &b, const RowView &ra, const RowView &rb,
                   const std::vector<size_t> &out, size_t la, size_t lb,
                   size_t M, const Elt &psi, bool commit_c, const Node_ *x,
                   size_t B) {
    const size_t lo = la + lb - 1;
    std::vector<size_t> zdims = out;
    zdims.back() = M;
    const F *pf = &f_;
    auto fn = [pf, la, lb, M, psi](const Tensor<Elt> &x, const Tensor<Elt> &y) {
      const F &f = *pf;
      const ops::NegacyclicNtt<F> ntt(f, M, psi);
      const size_t rows = x.size() / la;
      std::vector<Elt> z;
      z.reserve(rows * M);
      std::vector<Elt> u(M), v(M);
      for (size_t r = 0; r < rows; ++r) {
        std::fill(u.begin(), u.end(), f.zero());
        std::fill(v.begin(), v.end(), f.zero());
        std::copy(x.begin() + r * la, x.begin() + (r + 1) * la, u.begin());
        std::copy(y.begin() + r * lb, y.begin() + (r + 1) * lb, v.begin());
        ntt.forward(u);
        ntt.forward(v);
        for (size_t j = 0; j < M; ++j) z.push_back(f.mulf(u[j], v[j]));
      }
      return z;
    };
    const auto z = priv(d_, Subfield{}, nm + ".z", Shape(zdims),
                        depends_on(Expr<F>(a), Expr<F>(b)), fn);
    const auto &N = b_.system().graph().nodes;
    auto table = [&](size_t id) {
      const Node &n = N.at(id);
      return Ref<F, Subfield<>, Committed>(id, n.n, &f_, ref_of(d_, id).g,
                                           n.shape);
    };
    std::vector<Ref<F, Subfield<>, Committed>> tables{table(ra.node)};
    const bool same = same_table(ra, rb);
    auto side = [&](const RowView &v) {
      typename SpectralConvMap<F>::Side s{0, v.R, v.l, v.rows, v.in_l};
      if (v.op) {
        // The operator has no dependencies (row_view), so it instantiates
        // from none.
        s.op = v.op->make(OpArgs{});
        put_str(s.op_id, v.op->name);
        put_u64(s.op_id, v.op->params.size());
        s.op_id.insert(s.op_id.end(), v.op->params.begin(),
                       v.op->params.end());
      }
      return s;
    };
    typename SpectralConvMap<F>::Side sa = side(ra);
    typename SpectralConvMap<F>::Side sb = side(rb);
    size_t words = sa.words();
    if (!same) {
      tables.push_back(table(rb.node));
      sb.at = words;
      words += sb.words();
    } else if (sa.op) {
      // One instance of the shared operator.
      sb.op = sa.op;
    }
    tables.push_back(Ref<F, Subfield<>, Committed>(z));
    const size_t z_at = words;
    words += z.n;
    FieldRelation<F> rel;
    rel.name = "x_hat y_hat - z";
    rel.operands = 3;
    rel.monomials = {{f_.one(), {0, 1}}, {f_.mone(), {2}}};
    d_.batch(nm + ".spectra", tables, rel,
             std::make_shared<const SpectralConvMap<F>>(f_, M, psi, sa, sb,
                                                        z_at, words));
    std::vector<size_t> first(lo);
    for (size_t i = 0; i < lo; ++i) first[i] = i;
    Lin<F> c = Gather(f_, first, M)(ops::InverseNtt(f_, M, psi)(
        Lin<F>(Ref<F>(z))));
    c.shape = out;
    if (!commit_c) {
      // The plan export states this realization (plan_program.h).
      PlanRecords::SpectralConv rec;
      rec.pred = pred_;
      rec.batch = nm + ".spectra";
      rec.conv = x;
      rec.z = z.id;
      rec.blocks = B;
      rec.left = la;
      rec.right = lb;
      rec.length = M;
      rec.psi.resize(F::kBytes);
      f_.to_bytes_field(rec.psi.data(), psi);
      b_.records().spectral_convs.push_back(std::move(rec));
      return expr_internal::leaf(c);
    }
    const Ref<F> C =
        commit_product(nm + ".c", Shape(out), a, b, la, lb, M, psi);
    const Lin<F> cl = leaf_lin(C, out);
    d_.affine(nm + ".intt", cl - c);
    return expr_internal::leaf(cl);
  }

  Domain<F> &d_;
  ConstraintSystemBuilder<S> &b_;
  const F &f_;
  std::vector<size_t> phase_;
  std::map<const Node_ *, ExprPtr<F>> memo_;
  std::map<const Node_ *, bool> seen_;
  std::string pred_;
  bool affine_ctx_ = false;
  size_t count_ = 0;
};

template <class S, class F>
bool realize_convs(ConstraintSystemBuilder<S> &b, Domain<F> &d) {
  if constexpr (F::kCharacteristicTwo) {
    return false;
  } else {
    return ConvRealizer<F, S>(d, b).run();
  }
}

}  // namespace proofs::gordiehowe::compiler

#endif  // PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_COMPILER_CONV_H_
