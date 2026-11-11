// Copyright 2026 Chad Sharp and Paul Grubbs
// SPDX-License-Identifier: Apache-2.0

// GordieHowe: the GKR export of a circuit's expression emission, the
// relational certificate the Lean checker reads
// (formal/GordieHowe/Language/Realizations/Circuit/RelEntry.lean):
//   the DAG       the compiler's nodes, constants and schedule
//                 (circuits/compiler/gkr_certificate.h)
//   the table     every node the emitter completed (expr.h's EmitWalk), in
//                 completion order, as an ENode with its length, whether a
//                 chain flattened it, the shared expression it is printed as
//                 (.ref j), and per coordinate the wire c0 + c1 n the
//                 emission produced, with the aux wires of its own emission
//                 a product reads; a value is a leaf naming where the
//                 circuit reads it (Place)
//   the entries   per circuit entry its block of node ids, its asserted
//                 root and per root coordinate the assertion pair (Z, U):
//                 Z the node assert0 created, U the node its term reads;
//                 for a realization circuit or an alignment its family
//                 record (the nodes of its reads' views, its input blocks,
//                 and the wires of what its closure built: a LogUp
//                 group's fraction tree and sum, a MAC H half's chunks)
// Before writing, the table is checked against the printed program the way
// the Lean check reads it (Mirror: every node's kids lie below it, its
// length is its row's, a node printed as .ref j has the shared expression j
// as its row), and against the DAG by the C++ mirror of the relational
// check (RelMirror, GKR/Rel.lean's relOk over field elements): per cut node
// and coordinate, the wire equals the node's one-level expression over its
// kids' wires and its aux wires by the lazy difference check, and every
// assertion pair asserts its root's wire; every family record passes the
// family check (its guards, cuts and item), and every asserted DAG node is
// some entry's. Any mismatch fails the export.
//
// emit_tables(cs, meta) returns, per domain whose circuit was emitted here,
// its certificate as a GHC file (GKR/<domain>.ghc, ghc_gkr.h's sections of
// `cert : CircuitData`, written by ghc.h's writer) and its Lean modules (GKR/<domain>.lean,
// GKR/<domain>/E<k>.lean, an entry's part modules GKR/<domain>/E<k>/P<j>.lean
// when its check is over the module budget (plan_entry),
// GKR/<domain>/Circuit.lean).

#ifndef PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_COMPILER_EMIT_EXPORT_H_
#define PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_COMPILER_EMIT_EXPORT_H_

#include <algorithm>
#include <cmath>
#include <cstddef>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <functional>
#include <map>
#include <optional>
#include <set>
#include <stdexcept>
#include <string>
#include <unordered_map>
#include <unordered_set>
#include <utility>
#include <vector>

#include "circuits/compiler/gkr_certificate.h"
#include "gordiehowe/compiler/ghc.h"
#include "gordiehowe/compiler/ghc_gkr.h"
#include "gordiehowe/compiler/plan_export.h"
#include "gordiehowe/compiler/program_builder.h"
#include "gordiehowe/compiler/program_printer.h"
#include "gordiehowe/compiler/realized_program.h"
#include "gordiehowe/expr.h"

namespace proofs::gordiehowe::compiler {
namespace emit_export_internal {

using ir::Id;
using ir::kNone;
using plan_export_internal::export_fail;

// A circuit the export does not cover (a node the program prints no form
// of): the export skips the circuit's modules and says why
// (GH_EMIT_TABLE_UNSUPPORTED), as it does for any failure while it builds
// the table. A table a mirror refuses fails the export.
struct EmitUnsupported : std::runtime_error {
  using std::runtime_error::runtime_error;
};

// The GKR certificate's code of field element X: to_bytes_field's
// little-endian bytes as a natural.
template <class F>
std::string elt_code(const F &f, const typename F::Elt &x) {
  std::vector<uint8_t> b(F::kBytes);
  f.to_bytes_field(b.data(), x);
  return program_builder_internal::BigNat::of_bytes(b.data(), b.size()).dec();
}

// An operator a circuit expands (Lean `EOp`).
struct EOp {
  enum Kind : uint8_t { kView, kNamed, kSparse, kStaged };
  Kind kind = kView;
  // kView: the index map, and the constant of one zero when a row is empty.
  Id idx = kNone;
  bool has_zero = false;
  size_t zero = 0;
  // kNamed, kStaged: the named operator; kSparse: the rows (linears).
  Id op = kNone;
  Id rows = kNone;
  uint64_t mask = 0;
  // kNamed, kStaged: its columns and rows (the length of its output).
  size_t cols = 1, nrows = 1;
  // The operator (OpSpec<F>), for the relational mirror.
  const void *spec = nullptr;
};

// A term of an affine combination (Lean `ETerm`): its scale's code, its
// view's node, its operators first to last.
struct ETerm {
  std::string scale;
  size_t view = 0;
  std::vector<EOp> ops;
};

// Where a value leaf reads its value (Lean `GKR.Rel.Place`): input block B
// of the circuit, a late value's message and pad blocks, or the node X
// computing its definition.
struct Place {
  enum Kind : uint8_t { kBlock, kLate, kDefined };
  Kind kind = kBlock;
  size_t b = 0, pub = 0, pad = 0, x = 0;
};

// A node of the table (Lean `ENode`; the kinds' numbers are the binary
// certificate's constructor tags).
struct ENode {
  enum Kind : uint8_t {
    kLin,
    kConst,
    kBin,
    kScale,
    kSum,
    kProd,
    kBroadcast,
    kNot,
    kMux,
    kCmp,
    kTree,
    kMaterialize,
    kGather,
    kApply,
    kValue
  };
  // BinOp: add mul and or xor; CmpOp: lt leq eq.
  enum Bin : uint8_t { kAdd, kMul, kAnd, kOr, kXor };
  enum Cmp : uint8_t { kLt, kLeq, kEq };
  Kind kind = kGather;
  uint8_t op = 0;
  // The kids, by id: bin a b; scale, sum, prod, broadcast, lnot, tree,
  // materialize, apply a; mux c t e; cmp a (b when not imm); gather its
  // parts.
  std::vector<size_t> kids;
  // scale: the code.
  std::string code;
  // const: v; lnot: the ones; cmp imm: the constant; value: u; sum,
  // prod, cmp, tree: w.
  size_t v = 0, u = 0, w = 0;
  // broadcast, gather, cmp imm: the index map.
  Id idx = kNone;
  // mux: bit; tree: any; cmp: imm.
  bool flag = false;
  std::vector<ETerm> terms;
  // lin: the zeros' constant (always written).
  size_t zero = 0;
  EOp eop;
  Place pl;
  // The expression node (ExprNode<F>) or affine combination (Lin<F>) the
  // node emitted, for the relational mirror.
  const void *src = nullptr;
  const void *lin = nullptr;
};

// A node with what the printer drops (Lean `ENodeInfo` less its wires).
struct ENodeInfo {
  ENode node;
  size_t len = 0;
  bool flat = false;
  bool has_ref = false;
  size_t ref = 0;
  // A step node (a Boolean check's or an asserted truth's), not exported.
  bool step = false;
};

// The node table of one circuit's emission: per node its wires and aux
// wires, and per circuit entry its block.
template <class F>
struct EmitTable {
  using Wire = typename EmitWalk<F>::Wire;
  std::vector<ENodeInfo> nodes;
  std::vector<std::vector<Wire>> W, aux;
  // Per node, whether it is a check point (mark_cuts): only a cut node
  // carries wires.
  std::vector<uint8_t> cut;
  // A realization or alignment entry's family record (Lean `FamCert`):
  // the pointers into the table and the input blocks; its wires are LOG's
  // DAG nodes, each read as the wire 0 + 1 n.
  struct Fam {
    enum Kind : uint8_t { kNone, kAlignment, kLogup, kMacH };
    Kind kind = kNone;
    // alignment: the filler block; logup: the weights block.
    size_t block = 0;
    // logup: the nodes of alpha's, the needles' and the histograms' views.
    size_t alpha = 0;
    std::vector<size_t> needles, hists;
    // macH: the nodes of the operand's, the powers' and the tag's views.
    size_t bits = 0, powers = 0, tag = 0;
  };
  struct Block {
    size_t lo = 0, hi = 0;
    bool has_root = false;
    size_t root = 0;
    // The nodes assert0 returned, and for an alignment the filler inputs.
    std::vector<size_t> Z, inputs;
    // A realization entry: per read the node of its view (SIZE_MAX: none,
    // the weights), what its closure built, and its family record.
    std::vector<size_t> reads;
    FamilyLog log;
    Fam fam;
  };
  std::vector<Block> blocks;
};

// The C++ mirror of the Lean check of TABLE against the printed program P
// (Emit.lean's ETable.eqB and nodeRowOkB). CHAR2 and TWO are the field's
// characteristic-two flag and the code of 2.
class Mirror {
 public:
  Mirror(const ir::Program &p, const std::vector<ENodeInfo> &t, bool char2,
         std::string two)
      : p_(p), t_(t), pr_(p), char2_(char2), two_(std::move(two)) {}

  // Empty when every node checks (nodeOkB), else why the first does not.
  std::string table_errors() {
    for (size_t k = 0; k < t_.size(); ++k) {
      const std::string why = node_error(k);
      if (!why.empty()) return "node " + std::to_string(k) + ": " + why;
    }
    return "";
  }
  // Node K's print is the program's expression E (ETable.eqB).
  bool eq_print(size_t k, Id e) {
    if (k >= t_.size()) return false;
    const ENodeInfo &n = t_[k];
    if (n.has_ref) return op(e) == ir::Expr::kRef && x(e) == n.ref;
    const uint64_t key = (uint64_t(k) << 32) ^ uint64_t(e);
    if (done_.count(key)) return true;
    const bool ok = eq_row(n.node, e);
    if (ok) done_.insert(key);
    return ok;
  }

 private:
  const ir::Expr &nd(Id e) const { return p_.nodes.at(e); }
  ir::Expr::Op op(Id e) const { return nd(e).op; }
  uint64_t x(Id e) const { return nd(e).x; }

  std::string node_error(size_t k) {
    const ENodeInfo &n = t_[k];
    for (size_t a : refs(n.node))
      if (a >= k) return "a kid " + std::to_string(a) + " not below it";
    const size_t L = row_len(n.node);
    if (L != n.len)
      return "kind " + std::to_string(int(n.node.kind)) + " length " +
             std::to_string(n.len) + ", its row's " + std::to_string(L);
    if (n.has_ref) {
      if (n.ref >= p_.exprs.size()) return "a .ref past the shared expressions";
      if (!eq_row(n.node, p_.exprs[n.ref])) {
        std::string kids;
        for (size_t a : n.node.kids) {
          const ENodeInfo &x = t_[a];
          kids += " " + std::to_string(a) + ":" + std::to_string(int(x.node.kind)) +
                  (x.has_ref ? "/ref" + std::to_string(x.ref)
                   : x.node.kind == ENode::kValue ? "/leaf" + std::to_string(x.node.u)
                                                  : "");
        }
        std::string want = pr_.expr(p_.exprs[n.ref]);
        if (want.size() > 160) want = want.substr(0, 160) + "...";
        return "its row (kind " + std::to_string(int(n.node.kind)) + ", index map " +
               std::to_string(n.node.idx) + ", kids" + kids +
               ") is not the shared expression " + std::to_string(n.ref) + ", " + want;
      }
    }
    return "";
  }

  // The kids a node's row reads (Expr.refs of its row), and a defined
  // value's node.
  static std::vector<size_t> refs(const ENode &n) {
    std::vector<size_t> r = n.kids;
    for (const auto &t : n.terms) r.push_back(t.view);
    if (n.kind == ENode::kValue && n.pl.kind == Place::kDefined)
      r.push_back(n.pl.x);
    return r;
  }

  size_t value_size(size_t v) const {
    if (v >= p_.values.size()) return 0;
    size_t s = 1;
    for (size_t d : p_.values[v].shape) s *= d;
    return s;
  }
  size_t len(size_t a) const { return a < t_.size() ? t_[a].len : 0; }
  size_t idx_size(Id i) const {
    return i < p_.index_maps.size() ? p_.index_maps[i].size() : 0;
  }
  size_t wrap_len(const EOp &o, size_t in) const {
    switch (o.kind) {
      case EOp::kView:
        return idx_size(o.idx);
      case EOp::kSparse:
        return o.rows < p_.linears.size() ? p_.linears[o.rows].size() : 0;
      default:
        return o.cols == 0 ? 0 : in / o.cols * o.nrows;
    }
  }
  size_t term_len(const ETerm &t) const {
    size_t l = len(t.view);
    for (const auto &o : t.ops) l = wrap_len(o, l);
    return l;
  }
  // Expr.len of node N's row, its kids' lengths the table's.
  size_t row_len(const ENode &n) const {
    switch (n.kind) {
      case ENode::kLin:
        return n.terms.empty() ? value_size(n.zero) : term_len(n.terms[0]);
      case ENode::kConst:
        return value_size(n.v);
      case ENode::kBin:
      case ENode::kScale:
      case ENode::kMaterialize:
        return len(n.kids[0]);
      case ENode::kSum:
      case ENode::kProd:
        return n.w == 0 ? 0 : len(n.kids[0]) / n.w;
      case ENode::kBroadcast:
      case ENode::kGather:
        return idx_size(n.idx);
      case ENode::kNot:
        return value_size(n.v);
      case ENode::kMux:
        return len(n.kids[1]);
      case ENode::kCmp:
      case ENode::kTree:
        return n.w == 0 ? 0 : len(n.kids[0]) / n.w;
      case ENode::kApply:
        return wrap_len(n.eop, len(n.kids[0]));
      case ENode::kValue:
        return value_size(n.u);
    }
    return 0;
  }

  bool same_idx(Id a, Id b) const {
    return a == b ||
           (a < p_.index_maps.size() && b < p_.index_maps.size() &&
            p_.index_maps[a] == p_.index_maps[b]);
  }
  bool same_coef(const ir::Coef &a, const ir::Coef &b) const {
    return a.is_const == b.is_const &&
           (a.is_const ? a.c == b.c : a.v == b.v && a.i == b.i);
  }
  bool is_const_coef(Id c, const std::string &code) const {
    if (c >= p_.coefs.size()) return false;
    const ir::Coef &k = p_.coefs[c];
    return k.is_const && k.c == code;
  }
  bool same_rows(Id a, Id b) const {
    if (a == b) return true;
    if (a >= p_.linears.size() || b >= p_.linears.size()) return false;
    const auto &ra = p_.linears[a], &rb = p_.linears[b];
    if (ra.size() != rb.size()) return false;
    for (size_t i = 0; i < ra.size(); ++i) {
      if (ra[i].size() != rb[i].size()) return false;
      for (size_t j = 0; j < ra[i].size(); ++j)
        if (ra[i][j].first != rb[i][j].first ||
            !same_coef(p_.coefs.at(ra[i][j].second), p_.coefs.at(rb[i][j].second)))
          return false;
    }
    return true;
  }
  bool same_op(Id a, Id b) const {
    return a == b || pr_.named_op(a) == pr_.named_op(b);
  }
  bool leaf(Id e, size_t v) const { return op(e) == ir::Expr::kLeaf && x(e) == v; }

  // An operator's printed form around INNER (EOp.wrap) is E; INNER(e) on
  // the operand.
  template <class Inner>
  bool eq_wrap(const EOp &o, Id e, Inner inner) {
    switch (o.kind) {
      case EOp::kView: {
        if (op(e) != ir::Expr::kReindex || !same_idx(o.idx, Id(x(e)))) return false;
        const Id a = nd(e).a;
        if (!o.has_zero) return inner(a);
        return op(a) == ir::Expr::kConcat && leaf(nd(a).b, o.zero) && inner(nd(a).a);
      }
      case EOp::kNamed:
      case EOp::kStaged:
        return op(e) == ir::Expr::kApply && same_op(o.op, Id(x(e))) && inner(nd(e).a);
      case EOp::kSparse:
        return op(e) == ir::Expr::kLinear && same_rows(o.rows, Id(x(e))) &&
               inner(nd(e).a);
    }
    return false;
  }
  // A term's row (ETerm.row) is E, its view read through its print.
  bool eq_term(const ETerm &t, Id e) {
    if (t.scale != "1") {
      if (op(e) != ir::Expr::kScale || !is_const_coef(Id(x(e)), t.scale)) return false;
      e = nd(e).a;
    }
    return eq_ops(t, t.ops.size(), e);
  }
  bool eq_ops(const ETerm &t, size_t k, Id e) {
    if (k == 0) return eq_print(t.view, e);
    return eq_wrap(t.ops[k - 1], e, [&](Id a) { return eq_ops(t, k - 1, a); });
  }
  // linRow TS Z is E.
  bool eq_lin(const std::vector<ETerm> &ts, size_t z, Id e) {
    if (ts.empty()) return leaf(e, z);
    for (size_t i = ts.size(); i-- > 1;) {
      if (op(e) != ir::Expr::kAdd || !eq_term(ts[i], nd(e).b)) return false;
      e = nd(e).a;
    }
    return eq_term(ts[0], e);
  }
  // concatRow of the prints of PARTS is E.
  bool eq_concat(const std::vector<size_t> &parts, Id e) {
    const size_t n = parts.size();
    if (n == 0) return leaf(e, 0);
    for (size_t i = 0; i < n; ++i) {
      const bool last = i + 1 == n;
      Id here = e;
      if (!last) {
        if (op(e) != ir::Expr::kConcat) return false;
        here = nd(e).a;
      }
      if (!eq_print(parts[i], here)) return false;
      if (!last) e = nd(e).b;
    }
    return true;
  }
  bool bin2(ir::Expr::Op o, Id e, size_t a, size_t b) {
    return op(e) == o && eq_print(a, nd(e).a) && eq_print(b, nd(e).b);
  }
  // Node N's row, its kids read through their prints, is E.
  bool eq_row(const ENode &n, Id e) {
    using E = ir::Expr;
    switch (n.kind) {
      case ENode::kLin:
        return eq_lin(n.terms, n.zero, e);
      case ENode::kConst:
        return leaf(e, n.v);
      case ENode::kBin: {
        const size_t a = n.kids[0], b = n.kids[1];
        switch (n.op) {
          case ENode::kAdd:
            return bin2(E::kAdd, e, a, b);
          case ENode::kMul:
          case ENode::kAnd:
            return bin2(E::kMul, e, a, b);
          case ENode::kOr:
            return op(e) == E::kSub && bin2(E::kAdd, nd(e).a, a, b) &&
                   bin2(E::kMul, nd(e).b, a, b);
          default:
            if (char2_) return bin2(E::kAdd, e, a, b);
            return op(e) == E::kSub && bin2(E::kAdd, nd(e).a, a, b) &&
                   op(nd(e).b) == E::kScale &&
                   is_const_coef(Id(x(nd(e).b)), two_) &&
                   bin2(E::kMul, nd(nd(e).b).a, a, b);
        }
      }
      case ENode::kScale:
        if (n.code == "1") return eq_print(n.kids[0], e);
        return op(e) == E::kScale && is_const_coef(Id(x(e)), n.code) &&
               eq_print(n.kids[0], nd(e).a);
      case ENode::kSum: {
        if (op(e) != E::kApply) return false;
        const ir::NamedOp &o = p_.ops.at(Id(x(e)));
        return o.kind == ir::NamedOp::kSum && o.nats.size() == 1 &&
               o.nats[0] == n.w && eq_print(n.kids[0], nd(e).a);
      }
      case ENode::kProd:
        return op(e) == E::kProd && x(e) == n.w && eq_print(n.kids[0], nd(e).a);
      case ENode::kBroadcast:
        return op(e) == E::kReindex && same_idx(n.idx, Id(x(e))) &&
               eq_print(n.kids[0], nd(e).a);
      case ENode::kNot:
        return op(e) == E::kSub && leaf(nd(e).a, n.v) &&
               eq_print(n.kids[0], nd(e).b);
      case ENode::kMux:
        return op(e) == E::kMux && eq_print(n.kids[0], nd(e).a) &&
               eq_print(n.kids[1], nd(e).b) && eq_print(n.kids[2], nd(e).c);
      case ENode::kCmp: {
        const ir::LogicOp lo = n.op == ENode::kLt    ? ir::LogicOp::kLt
                               : n.op == ENode::kLeq ? ir::LogicOp::kLeq
                                                     : ir::LogicOp::kEq;
        if (op(e) != E::kLogic || nd(e).logic != lo || x(e) != n.w ||
            nd(e).args.size() != 2 || !eq_print(n.kids[0], nd(e).args[0]))
          return false;
        const Id b = nd(e).args[1];
        if (!n.flag) return eq_print(n.kids[1], b);
        return op(b) == E::kReindex && same_idx(n.idx, Id(x(b))) &&
               leaf(nd(b).a, n.v);
      }
      case ENode::kTree: {
        const ir::LogicOp lo = n.flag ? ir::LogicOp::kAny : ir::LogicOp::kAll;
        return op(e) == E::kLogic && nd(e).logic == lo && x(e) == n.w &&
               nd(e).args.size() == 1 && eq_print(n.kids[0], nd(e).args[0]);
      }
      case ENode::kMaterialize:
        return eq_print(n.kids[0], e);
      case ENode::kGather:
        return op(e) == E::kReindex && same_idx(n.idx, Id(x(e))) &&
               eq_concat(n.kids, nd(e).a);
      case ENode::kApply:
        return eq_wrap(n.eop, e, [&](Id a) { return eq_print(n.kids[0], a); });
      case ENode::kValue:
        return leaf(e, n.u);
    }
    return false;
  }

  const ir::Program &p_;
  const std::vector<ENodeInfo> &t_;
  program_printer_internal::Printer pr_;
  bool char2_;
  std::string two_;
  std::unordered_set<uint64_t> done_;
};

// ------------------------------------------------------------ the table --

// The index in P of the circuit of domain DI (the one circuit the domain
// emits, CompiledDomain::gkr_emit_walk).
inline size_t emitted_circuit(const ir::Program &p, size_t di) {
  size_t k = SIZE_MAX;
  for (size_t c = 0; c < p.circuits.size(); ++c) {
    if (p.circuits[c].domain != Id(di)) continue;
    if (k != SIZE_MAX)
      export_fail("domain " + std::to_string(di) + " has more than one circuit");
    k = c;
  }
  if (k == SIZE_MAX) export_fail("domain " + std::to_string(di) + " has no circuit");
  return k;
}

// The node table of domain D's emission WALK, from the program builder PB
// after its run, which returned P.
template <class S, class F>
class TableBuilder : Lowering {
 public:
  using PB = program_builder_internal::ProgramBuilder<S>;
  using Wire = typename EmitWalk<F>::Wire;
  using Walk = EmitWalk<F>;
  // CIRC is the index in P of the circuit emitted (emitted_circuit).
  TableBuilder(const PB &pb, const ir::Program &p, size_t circ, const Domain<F> &d,
               const std::vector<Node> &N, const EmitWalk<F> &walk)
      : pb_(pb), p_(p), circ_(circ), d_(d), N_(N), walk_(walk), f_(d.field()) {}

  EmitTable<F> build() {
    if (!walk_.problem.empty()) export_fail("the emission walk: " + walk_.problem);
    const size_t n = walk_.nodes.size();
    tid_.assign(n, SIZE_MAX);
    std::vector<size_t> start(n + 1, 0);
    for (size_t k = 0; k < n; ++k) {
      start[k] = out_.nodes.size();
      cur_ = k;
      const auto &en = walk_.nodes[k];
      if (en.e != nullptr) {
        tid_[k] = expr_entry(en);
      } else if (en.step != Walk::kNoStep) {
        tid_[k] = step_entry(en);
      } else {
        tid_[k] = view_entry(en);
      }
    }
    start[n] = out_.nodes.size();
    for (const auto &b : walk_.blocks) {
      typename EmitTable<F>::Block blk;
      blk.lo = start.at(b.lo);
      blk.hi = start.at(b.hi);
      if (b.root != SIZE_MAX) {
        blk.has_root = true;
        blk.root = tid_.at(b.root);
      }
      blk.Z = b.Z;
      blk.inputs = b.U;
      for (size_t r : b.reads) blk.reads.push_back(r == SIZE_MAX ? SIZE_MAX : tid_.at(r));
      blk.log = b.fam;
      out_.blocks.push_back(std::move(blk));
    }
    return std::move(out_);
  }

 private:
  // A wire with no node term when its coefficient is zero (n = 0 for a
  // constant).
  Wire norm(Wire w) const {
    if (w.c1 == f_.zero()) w.x = 0;
    return w;
  }
  std::vector<Wire> norm(const std::vector<Wire> &v) const {
    std::vector<Wire> out;
    out.reserve(v.size());
    for (const auto &w : v) out.push_back(norm(w));
    return out;
  }
  size_t push(ENodeInfo ni, const std::vector<Wire> &W,
              const std::vector<Wire> &aux = {}) {
    out_.nodes.push_back(std::move(ni));
    out_.W.push_back(norm(W));
    out_.aux.push_back(norm(aux));
    return out_.nodes.size() - 1;
  }

  // The kid whose print is node N's whole row, SIZE_MAX when none.
  static size_t alias_kid(const ENode &n) {
    switch (n.kind) {
      case ENode::kMaterialize:
        return n.kids[0];
      case ENode::kScale:
        return n.code == "1" ? n.kids[0] : SIZE_MAX;
      case ENode::kLin:
        return n.terms.size() == 1 && n.terms[0].scale == "1" &&
                       n.terms[0].ops.empty()
                   ? n.terms[0].view
                   : SIZE_MAX;
      default:
        return SIZE_MAX;
    }
  }
  // NI printed as PRINTED: a .ref j sets its ref, unless its row aliases a
  // kid carrying it.
  void set_ref(ENodeInfo &ni, Id printed) const {
    if (printed == kNone || p_.nodes.at(printed).op != ir::Expr::kRef) return;
    const size_t j = p_.nodes.at(printed).x;
    const size_t a = alias_kid(ni.node);
    if (a != SIZE_MAX && out_.nodes[a].has_ref && out_.nodes[a].ref == j) return;
    ni.has_ref = true;
    ni.ref = j;
  }

  size_t expr_entry(const typename Walk::Entry &en) {
    ENodeInfo ni;
    ni.len = en.len;
    ni.flat = en.flat;
    // The node is alive and still its completion's contents.
    if (expr_fingerprint(*en.e) != en.fp)
      export_fail("the emission walk: an expression node's address reused "
                  "with other contents");
    const Id printed = pb_.printed_expr(en.e);
    ni.node = expr_node(*en.e, printed, cur_);
    set_ref(ni, printed);
    if (!en.flat && en.W.size() != en.len)
      export_fail("an expression node of " + std::to_string(en.len) +
                  " coordinates has " + std::to_string(en.W.size()) + " wires");
    return push(std::move(ni), en.W, en.aux);
  }

  // The circuit's domain's constant of L ones (the printer's lnot constant,
  // which it adds for every step node: ProgramBuilder::step_ones).
  size_t ones(size_t L) const {
    const std::string one = PB::code_of(f_, f_.one());
    for (size_t v = 0; v < p_.values.size(); ++v) {
      const ir::Value &x = p_.values[v];
      if (x.kind != ir::Value::kConstant || x.size() != L || x.entries.size() != L ||
          x.domain != p_.circuits.at(circ_).domain)
        continue;
      bool all = true;
      for (const auto &e : x.entries) all = all && e == one;
      if (all) return v;
    }
    export_fail("the program has no constant of " + std::to_string(L) +
                " ones in the circuit's domain for a step ones - x");
  }

  size_t step_entry(const typename Walk::Entry &en) {
    ENodeInfo ni;
    ni.len = en.len;
    ni.step = true;
    ENode &n = ni.node;
    const size_t a = tid_.at(en.a);
    switch (en.step) {
      case Walk::kCellMul:
        n.kind = ENode::kBin;
        n.op = ENode::kMul;
        n.kids = {a, a};
        break;
      case Walk::kViewMul:
        n.kind = ENode::kBin;
        n.op = ENode::kMul;
        n.kids = {a, tid_.at(en.b)};
        break;
      case Walk::kCellNeg:
        n.kind = ENode::kScale;
        n.code = PB::code_of(f_, f_.mone());
        n.kids = {a};
        break;
      case Walk::kCellAdd:
        n.kind = ENode::kBin;
        n.op = ENode::kAdd;
        n.kids = {a, tid_.at(en.b)};
        break;
      case Walk::kViewNot:
      case Walk::kTrueNot:
        n.kind = ENode::kNot;
        n.v = ones(en.len);
        n.kids = {a};
        break;
      default:
        export_fail("an unknown step node");
    }
    return push(std::move(ni), en.W);
  }

  const ir::Expr &nd(Id e) const { return p_.nodes.at(e); }
  // E with a top-level .ref read through its shared expression.
  Id deref(Id e) const {
    if (e != kNone && nd(e).op == ir::Expr::kRef) return p_.exprs.at(nd(e).x);
    return e;
  }
  // The program's code of X, which must be its certificate code (the
  // checker decodes both with the field's decode).
  std::string code(const typename F::Elt &x) const {
    const std::string c = PB::code_of(f_, x);
    if (c != elt_code(f_, x))
      throw EmitUnsupported("a coefficient's program code " + c +
                            " is not its certificate code " + elt_code(f_, x));
    return c;
  }

  size_t id_of(const ExprNode<F> *x) const {
    auto it = walk_.expr_id.find(x);
    if (it == walk_.expr_id.end())
      export_fail("an expression node's kid was never emitted");
    return tid_.at(it->second);
  }
  // The table id of value V's view as read by the node being built.
  size_t view_of(size_t v) const {
    const size_t k = walk_.view_before(v, cur_);
    if (k == SIZE_MAX)
      export_fail("value '" + N_.at(v).name + "' was read but never viewed");
    return tid_.at(k);
  }
  size_t vid(size_t key) const {
    const size_t v = pb_.value_id(key);
    if (v == SIZE_MAX) export_fail("node " + std::to_string(key) + " is no value");
    return v;
  }
  Id need(Id printed, const char *what) const {
    if (printed == kNone)
      throw EmitUnsupported(std::string("the program prints no form of ") +
                            what + " the circuit emits");
    return deref(printed);
  }

  // The operator OP's printed form E around its operand: the EOp, and the
  // operand's printed node in INNER.
  EOp eop(const OpSpec<F> &op, Id e, Id *inner) const {
    EOp o;
    o.spec = &op;
    const ir::Expr &n = nd(e);
    switch (n.op) {
      case ir::Expr::kReindex: {
        o.kind = EOp::kView;
        o.idx = Id(n.x);
        const ir::Expr &a = nd(n.a);
        if (a.op == ir::Expr::kConcat && nd(a.b).op == ir::Expr::kLeaf) {
          o.has_zero = true;
          o.zero = nd(a.b).x;
          *inner = a.a;
        } else {
          *inner = n.a;
        }
        return o;
      }
      case ir::Expr::kApply:
        o.kind = op.staged != nullptr ? EOp::kStaged : EOp::kNamed;
        o.op = Id(n.x);
        if (op.staged != nullptr) o.mask = op.staged->mask;
        o.cols = op.cols;
        o.nrows = op.rows;
        *inner = n.a;
        return o;
      case ir::Expr::kLinear:
        o.kind = EOp::kSparse;
        o.rows = Id(n.x);
        *inner = n.a;
        return o;
      default:
        export_fail("operator '" + op.name + "' has a printed form no circuit "
                    "operator has");
    }
  }

  // The terms of affine combination L from its printed form E.
  void lin_terms(const Lin<F> &L, Id e, ENode &out) const {
    out.lin = &L;
    const size_t nt = L.terms.size();
    if (nt == 0) {
      if (nd(e).op != ir::Expr::kLeaf)
        export_fail("an affine combination of no terms printed as no constant");
      out.zero = nd(e).x;
      return;
    }
    std::vector<Id> forms(nt);
    for (size_t i = nt; i-- > 1;) {
      if (nd(e).op != ir::Expr::kAdd)
        export_fail("an affine combination printed as no sum of its terms");
      forms[i] = nd(e).b;
      e = nd(e).a;
    }
    forms[0] = e;
    for (size_t i = 0; i < nt; ++i) {
      const Term<F> &t = L.terms[i];
      ETerm et;
      Id x = forms[i];
      if (t.scale == f_.one()) {
        et.scale = "1";
      } else {
        if (nd(x).op != ir::Expr::kScale)
          export_fail("a scaled term printed with no scale");
        const ir::Coef &c = p_.coefs.at(Id(nd(x).x));
        if (!c.is_const) export_fail("a term's scale printed as no constant");
        et.scale = c.c;
        if (et.scale != code(t.scale))
          export_fail("a term's printed scale is not its coefficient's code");
        x = nd(x).a;
      }
      std::vector<EOp> ops(t.chain.size());
      for (size_t k = t.chain.size(); k-- > 0;) {
        Id inner = kNone;
        ops[k] = eop(*t.chain[k], x, &inner);
        if (ops[k].kind == EOp::kStaged)
          throw EmitUnsupported("an affine term applies the staged transform '" +
                                t.chain[k]->name + "' (no aux rule for a term)");
        x = inner;
      }
      et.ops = std::move(ops);
      et.view = view_of(t.node);
      out.terms.push_back(std::move(et));
    }
  }

  ENode expr_node(const ExprNode<F> &x, Id printed, size_t self) const {
    ENode n;
    n.src = &x;
    auto kid = [&](size_t i) { return id_of(x.kids.at(i).get()); };
    switch (x.op) {
      case ExprOp::kLin: {
        n.kind = ENode::kLin;
        lin_terms(x.lin, need(printed, "an affine leaf"), n);
        break;
      }
      case ExprOp::kConst: {
        n.kind = ENode::kConst;
        const Id e = need(printed, "a constant");
        if (nd(e).op != ir::Expr::kLeaf)
          export_fail("a constant of " + std::to_string(x.c.size()) +
                      " values for " + std::to_string(x.n) + " coordinates");
        n.v = nd(e).x;
        break;
      }
      case ExprOp::kAdd:
      case ExprOp::kMul:
      case ExprOp::kAnd:
      case ExprOp::kOr:
      case ExprOp::kXor:
        n.kind = ENode::kBin;
        n.op = x.op == ExprOp::kAdd   ? ENode::kAdd
               : x.op == ExprOp::kMul ? ENode::kMul
               : x.op == ExprOp::kAnd ? ENode::kAnd
               : x.op == ExprOp::kOr  ? ENode::kOr
                                      : ENode::kXor;
        if (x.kids.size() != 2) export_fail("a chain node of other than two operands");
        n.kids = {kid(0), kid(1)};
        break;
      case ExprOp::kScale:
        n.kind = ENode::kScale;
        n.code = x.c.at(0) == f_.one() ? std::string("1") : code(x.c.at(0));
        n.kids = {kid(0)};
        break;
      case ExprOp::kSum:
        n.kind = ENode::kSum;
        n.kids = {kid(0)};
        n.w = x.w == 0 ? x.kids[0]->n : x.w;
        break;
      case ExprOp::kProd:
        n.kind = ENode::kProd;
        n.kids = {kid(0)};
        n.w = x.w;
        break;
      case ExprOp::kBroadcast: {
        n.kind = ENode::kBroadcast;
        n.kids = {kid(0)};
        const Id e = need(printed, "a broadcast");
        if (nd(e).op != ir::Expr::kReindex) export_fail("a broadcast printed as no view");
        n.idx = Id(nd(e).x);
        break;
      }
      case ExprOp::kNot: {
        n.kind = ENode::kNot;
        n.kids = {kid(0)};
        const Id e = need(printed, "a negation");
        if (nd(e).op != ir::Expr::kSub || nd(nd(e).a).op != ir::Expr::kLeaf)
          export_fail("a negation printed as no difference from ones");
        n.v = nd(nd(e).a).x;
        break;
      }
      case ExprOp::kMux:
        n.kind = ENode::kMux;
        n.flag = x.bit;
        n.kids = {kid(0), kid(1), kid(2)};
        break;
      case ExprOp::kLt:
      case ExprOp::kLeq:
      case ExprOp::kEq: {
        n.kind = ENode::kCmp;
        n.op = x.op == ExprOp::kLt ? ENode::kLt : x.op == ExprOp::kLeq ? ENode::kLeq
                                                                      : ENode::kEq;
        n.w = x.w;
        n.flag = x.imm;
        n.kids = {kid(0)};
        if (x.imm) {
          const Id e = need(printed, "a comparison with a constant");
          const ir::Expr &l = nd(e);
          if (l.op != ir::Expr::kLogic || l.args.size() != 2 ||
              nd(l.args[1]).op != ir::Expr::kReindex ||
              nd(nd(l.args[1]).a).op != ir::Expr::kLeaf)
            export_fail("a comparison with a constant printed otherwise");
          n.idx = Id(nd(l.args[1]).x);
          n.v = nd(nd(l.args[1]).a).x;
        } else {
          n.kids.push_back(kid(1));
        }
        break;
      }
      case ExprOp::kAny:
      case ExprOp::kAll:
        n.kind = ENode::kTree;
        n.flag = x.op == ExprOp::kAny;
        n.w = x.w;
        n.kids = {kid(0)};
        break;
      case ExprOp::kMaterialize:
        n.kind = ENode::kMaterialize;
        n.kids = {kid(0)};
        break;
      case ExprOp::kGather: {
        n.kind = ENode::kGather;
        for (size_t i = 0; i < x.kids.size(); ++i) n.kids.push_back(kid(i));
        const Id e = need(printed, "a view");
        if (nd(e).op != ir::Expr::kReindex) export_fail("a view printed as no reindex");
        n.idx = Id(nd(e).x);
        break;
      }
      case ExprOp::kApply: {
        n.kind = ENode::kApply;
        n.kids = {kid(0)};
        if (x.apply == nullptr) export_fail("an operator node with no operator");
        Id inner = kNone;
        n.eop = eop(*x.apply, need(printed, "an operator node"), &inner);
        break;
      }
      default:
        throw EmitUnsupported("expression operation " + std::to_string(int(x.op)) +
                              " (node " + std::to_string(self) +
                              ") has no node export");
    }
    return n;
  }

  // The block of the emitted circuit holding value U at inputs [AT, AT + L)
  // (a committed, view or public block), SIZE_MAX when none.
  size_t block_of(size_t u, size_t at, size_t L) const {
    const auto &in = p_.circuits.at(circ_).inputs;
    for (size_t b = 0; b < in.size(); ++b) {
      const auto k = in[b].kind;
      if ((k == ir::InputBlock::kCommitted || k == ir::InputBlock::kView ||
           k == ir::InputBlock::kPub) &&
          in[b].value == Id(u) && in[b].at == at && in[b].n == L)
        return b;
    }
    return SIZE_MAX;
  }

  // The view of value V, completed at the current id with wires EN.W: its
  // table node (a value leaf, a definition's node, or the root of an
  // expression value), pushing what it needs.
  size_t view_entry(const typename Walk::Entry &en) {
    const size_t v = en.value;
    // A realization's weights: no value of the program, an input block the
    // family record names (no node).
    if (pb_.value_id(v) == SIZE_MAX)
      for (const auto &in : p_.circuits.at(circ_).inputs)
        if (in.kind == ir::InputBlock::kRealizationPub &&
            in.real.kind == ir::RealRef::kWeights && in.name == N_.at(v).name)
          return SIZE_MAX;
    const std::string kind = pb_.value_kind(v);
    ENodeInfo ni;
    ni.len = en.len;
    if (en.len != N_.at(v).n)
      export_fail("the view of value '" + N_.at(v).name + "' has " +
                  std::to_string(en.len) + " wires for " +
                  std::to_string(N_.at(v).n) + " coordinates");
    // A value leaf of value id U at place PL.
    auto leaf = [&](size_t u, Place pl) {
      ENodeInfo li;
      li.len = en.len;
      li.node.kind = ENode::kValue;
      li.node.u = u;
      li.node.pl = pl;
      return push(std::move(li), en.W);
    };
    if (kind == "late") {
      const size_t u = vid(v);
      const auto &in = p_.circuits.at(circ_).inputs;
      const size_t msg = pb_.message_of(v);
      Place pl;
      pl.kind = Place::kLate;
      pl.pub = pl.pad = SIZE_MAX;
      for (size_t b = 0; b < in.size(); ++b) {
        if (in[b].kind == ir::InputBlock::kPub && pl.pub == SIZE_MAX &&
            (in[b].value == Id(u) || size_t(in[b].value) == msg))
          pl.pub = b;
        if (in[b].kind == ir::InputBlock::kPad && pl.pad == SIZE_MAX &&
            in[b].value == Id(u))
          pl.pad = b;
      }
      if (pl.pub == SIZE_MAX || pl.pad == SIZE_MAX)
        export_fail("the circuit reads late value '" + N_.at(v).name +
                    "' with no public block of its message or no pad block");
      return leaf(u, pl);
    }
    if (auto w = wiring_views(d_).find(v); w != wiring_views(d_).end()) {
      const Id printed =
          kind.empty() ? pb_.printed_derived(v) : pb_.printed_value_def(v);
      const Id e = need(printed, "a wiring view");
      if (nd(e).op != ir::Expr::kReindex)
        export_fail("the circuit reads value '" + N_.at(v).name +
                    "' as its wiring view, the program prints its " +
                    (bindings(d_).count(v)        ? "binding"
                     : derived_views(d_).count(v) ? "affine view"
                                                  : "definition") +
                    " (expression op " + std::to_string(int(nd(e).op)) + ")");
      ni.node.kind = ENode::kGather;
      ni.node.idx = Id(nd(e).x);
      std::set<size_t> seen;
      bool zero = false;
      for (const auto &[node, i] : w->second) {
        if (node == kZeroCoordinate) {
          zero = true;
          continue;
        }
        if (seen.insert(node).second) ni.node.kids.push_back(view_of(node));
      }
      if (zero) {
        // The concatenation's last part, the zero's constant, as a node.
        Id c = nd(e).a;
        while (nd(c).op == ir::Expr::kConcat) c = nd(c).b;
        if (nd(c).op != ir::Expr::kLeaf)
          export_fail("a wiring view's zero printed as no constant");
        ENodeInfo ci;
        ci.node.kind = ENode::kConst;
        ci.node.v = nd(c).x;
        ci.len = p_.values.at(ci.node.v).size();
        std::vector<Wire> cw(ci.len, Wire{f_.zero(), f_.zero(), 0});
        ni.node.kids.push_back(push(std::move(ci), cw));
      }
      if (kind.empty()) {
        set_ref(ni, printed);
        return push(std::move(ni), en.W);
      }
      Place pl;
      pl.kind = Place::kDefined;
      pl.x = push(std::move(ni), en.W);
      return leaf(vid(v), pl);
    }
    if (auto x = expr_values(d_).find(v); x != expr_values(d_).end()) {
      if (!kind.empty())
        throw EmitUnsupported("expression value '" + N_.at(v).name +
                              "' is a value of the program");
      auto r = walk_.expr_id.find(x->second.get());
      if (r == walk_.expr_id.end() || r->second >= cur_)
        export_fail("expression value '" + N_.at(v).name +
                    "' read before its expression was emitted");
      const size_t root = tid_.at(r->second);
      // The value prints as .ref j when the program shares its expression.
      const Id printed = pb_.printed_derived(v);
      const size_t j = printed != kNone && nd(printed).op == ir::Expr::kRef
                           ? size_t(nd(printed).x)
                           : SIZE_MAX;
      const ENodeInfo &ri = out_.nodes[root];
      const bool same_ref = j == SIZE_MAX || (ri.has_ref && ri.ref == j);
      // The view reads the root's wires evaluated: the root itself when they
      // are its wires and it prints as the value, else the root scaled by
      // one at the view's wires, printed as the value's .ref j.
      if (out_.W[root] == norm(en.W) && same_ref) return root;
      ni.node.kind = ENode::kScale;
      ni.node.code = "1";
      ni.node.kids = {root};
      if (j != SIZE_MAX) {
        ni.has_ref = true;
        ni.ref = j;
      }
      return push(std::move(ni), en.W);
    }
    // A derived value, or a realization's value bound to its digits (no
    // value of the program: it prints as a derived value, its binding).
    const bool derived = N_.at(v).kind == Kind::kDerived ||
                         (kind.empty() && bindings(d_).count(v) != 0);
    if (derived || kind == "bound") {
      auto b = bindings(d_).find(v);
      const Lin<F> *L = nullptr;
      if (b != bindings(d_).end()) {
        L = &b->second;
      } else if (auto l = derived_views(d_).find(v); l != derived_views(d_).end()) {
        L = &l->second;
      } else {
        export_fail("derived value '" + N_.at(v).name + "' has no terms");
      }
      // CompiledDomain::view returns default wires (node 0, the constant
      // one) for a value of no terms, where the program prints zeros.
      if (L->terms.empty())
        throw EmitUnsupported("derived value '" + N_.at(v).name +
                              "' of no terms is read by the circuit: its "
                              "view's wires are node 0, not zeros");
      ni.node.kind = ENode::kLin;
      if (kind.empty()) {
        const Id printed = pb_.printed_derived(v);
        lin_terms(*L, need(printed, "a derived value"), ni.node);
        set_ref(ni, printed);
        return push(std::move(ni), en.W);
      }
      lin_terms(*L, need(pb_.printed_value_def(v), "a value's definition"), ni.node);
      Place pl;
      pl.kind = Place::kDefined;
      pl.x = push(std::move(ni), en.W);
      return leaf(vid(v), pl);
    }
    // A value the circuit reads from its inputs: its committed, view or
    // public block.
    const size_t u = vid(v);
    {
      const ir::Value &pv = p_.values.at(u);
      if (pv.size() != N_.at(v).n)
        export_fail("the input view of node '" + N_.at(v).name + "' (" +
                    std::to_string(N_.at(v).n) + " coordinates) is program "
                    "value " + std::to_string(u) + " '" + pv.name + "' of " +
                    std::to_string(pv.size()) + " (kind " + kind + ")");
    }
    const size_t at = en.W.empty() ? 0 : en.W[0].x;
    Place pl;
    pl.kind = Place::kBlock;
    pl.b = block_of(u, at, en.len);
    if (pl.b == SIZE_MAX)
      export_fail("value '" + N_.at(v).name + "' (program value " +
                  std::to_string(u) + ") is read from inputs " +
                  std::to_string(at) + "... that no block of the circuit holds");
    return leaf(u, pl);
  }

  const PB &pb_;
  const ir::Program &p_;
  const size_t circ_;
  const Domain<F> &d_;
  const std::vector<Node> &N_;
  const EmitWalk<F> &walk_;
  const F &f_;
  EmitTable<F> out_;
  std::vector<size_t> tid_;
  size_t cur_ = 0;
};

// The check points (cuts) of table T, by one rule: a node is cut iff it is an operand the relational
// check reads as an atom (a leaf of a mul, and, or chain, or of an xor
// chain in odd characteristic; a mux operand; a prod, cmp or tree input; a
// staged transform's input) whose one-level form is no atom already (a
// constant, a leaf, or a view of kids' wires, whose kids are then the
// operands), an entry root, a value leaf, read by a number of parent nodes
// other than one, a node a value leaf's .defined place reads, or a node a
// family record names (step 4). An uncut node carries no wires: its
// parents' cuts expand its one-level form.
template <class F>
void mark_cuts(EmitTable<F> &t, const ir::Program &p) {
  const size_t n = t.nodes.size();
  t.cut.assign(n, 0);
  // A view each of whose coordinates is a kid's wire (a gather, broadcast
  // or materialize that computed nothing).
  auto wire_view = [&](size_t k) {
    const ENode &x = t.nodes[k].node;
    if (x.kind != ENode::kGather && x.kind != ENode::kBroadcast &&
        x.kind != ENode::kMaterialize)
      return false;
    std::vector<typename EmitTable<F>::Wire> cat;
    for (size_t a : x.kids) cat.insert(cat.end(), t.W[a].begin(), t.W[a].end());
    const std::vector<size_t> *idx = nullptr;
    if (x.kind != ENode::kMaterialize) {
      if (x.idx >= p.index_maps.size()) return false;
      idx = &p.index_maps[x.idx];
    }
    if (t.W[k].size() != t.nodes[k].len) return false;
    for (size_t i = 0; i < t.W[k].size(); ++i) {
      const size_t j = idx == nullptr ? i : idx->at(i);
      if (j >= cat.size() || !(cat[j] == t.W[k][i])) return false;
    }
    return true;
  };
  // Operand A must read as an atom (A12): a constant or a leaf is one, a
  // view of kids' wires is one when its kids are; any other node is cut.
  std::function<void(size_t)> atom = [&](size_t a) {
    const ENode &x = t.nodes[a].node;
    if (x.kind == ENode::kConst || x.kind == ENode::kValue) return;
    if (wire_view(a)) {
      for (size_t b : x.kids) atom(b);
      return;
    }
    t.cut[a] = 1;
  };
  std::vector<size_t> parents(n, 0), last(n, SIZE_MAX);
  auto read = [&](size_t a, size_t by) {
    if (a < n && last[a] != by) {
      last[a] = by;
      ++parents[a];
    }
  };
  auto multiplies = [](uint8_t op) {
    if (op == ENode::kAdd) return false;
    if (op == ENode::kXor) return !F::kCharacteristicTwo;
    return true;
  };
  // The leaves of the chain rooted at K (through its flattened kids).
  std::function<void(size_t, uint8_t)> leaves = [&](size_t k, uint8_t op) {
    for (size_t a : t.nodes[k].node.kids) {
      const ENodeInfo &x = t.nodes[a];
      if (x.flat && x.node.kind == ENode::kBin && x.node.op == op)
        leaves(a, op);
      else
        atom(a);
    }
  };
  for (size_t k = 0; k < n; ++k) {
    const ENode &x = t.nodes[k].node;
    for (size_t a : x.kids) read(a, k);
    for (const auto &term : x.terms) read(term.view, k);
    switch (x.kind) {
      case ENode::kValue:
        t.cut[k] = 1;
        if (x.pl.kind == Place::kDefined) {
          read(x.pl.x, k);
          t.cut[x.pl.x] = 1;
        }
        break;
      case ENode::kBin:
        if (!t.nodes[k].flat && multiplies(x.op)) leaves(k, x.op);
        break;
      case ENode::kMux:
      case ENode::kProd:
      case ENode::kCmp:
      case ENode::kTree:
        for (size_t a : x.kids) atom(a);
        break;
      case ENode::kApply:
        if (x.eop.kind == EOp::kStaged) atom(x.kids[0]);
        break;
      default:
        break;
    }
  }
  for (const auto &b : t.blocks) {
    if (b.has_root) t.cut[b.root] = 1;
    const auto &g = b.fam;
    std::vector<size_t> named;
    if (g.kind == EmitTable<F>::Fam::kLogup) {
      named = g.needles;
      named.insert(named.end(), g.hists.begin(), g.hists.end());
      named.push_back(g.alpha);
    } else if (g.kind == EmitTable<F>::Fam::kMacH) {
      named = {g.bits, g.powers, g.tag};
    }
    for (size_t k : named)
      if (k < n) t.cut[k] = 1;
  }
  for (size_t k = 0; k < n; ++k) {
    if (parents[k] != 1) t.cut[k] = 1;
    if (!t.cut[k]) t.W[k].clear();
  }
}

// The family record of each realization and alignment entry of table T,
// circuit PC of program P (Lean `FamCert`): an alignment names its filler
// block; a range LogUp group (.logup t g) its reads' views (the members'
// needles in member order, the present histograms static then late, alpha)
// and the weights' input block; a MAC H half (.macH p) the views of its
// operand, powers and tag. The closure's log gives the wires. A record the
// entry's reads do not fit fails the export.
template <class F>
void family_records(EmitTable<F> &t, const ir::Program &p, const ir::Circuit &pc) {
  using Fam = typename EmitTable<F>::Fam;
  for (size_t k = 0; k < t.blocks.size(); ++k) {
    auto &b = t.blocks[k];
    const ir::CircuitEntry &ce = pc.entries.at(k);
    const std::string at = "entry " + std::to_string(k) + ": ";
    if (ce.kind == ir::CircuitEntry::kAlignment) {
      b.fam.kind = Fam::kAlignment;
      b.fam.block = SIZE_MAX;
      for (size_t i = 0; i < pc.inputs.size(); ++i) {
        const auto &in = pc.inputs[i];
        if (in.kind == ir::InputBlock::kFiller && in.n == ce.id && !b.inputs.empty() &&
            in.at == b.inputs[0])
          b.fam.block = i;
      }
      if (b.fam.block == SIZE_MAX)
        export_fail(at + "an alignment of " + std::to_string(ce.id) +
                    " inputs reads no filler block of the circuit");
      continue;
    }
    if (ce.kind != ir::CircuitEntry::kRealization) continue;
    if (ce.real.kind == ir::RealRef::kLogup) {
      const ir::Table &tb = p.tables.at(ce.real.a);
      const ir::TableGroup &gr = tb.groups.at(ce.real.b);
      const size_t nn = gr.members.size();
      const size_t nh = (gr.static_mult != kNone) + (gr.late_mult != kNone);
      if (b.reads.size() != nn + nh + 2)
        export_fail(at + "a LogUp group of " + std::to_string(nn) + " members and " +
                    std::to_string(nh) + " histograms has " +
                    std::to_string(b.reads.size()) + " reads");
      b.fam.kind = Fam::kLogup;
      b.fam.needles.assign(b.reads.begin(), b.reads.begin() + long(nn));
      b.fam.hists.assign(b.reads.begin() + long(nn), b.reads.begin() + long(nn + nh));
      if (b.reads[nn + nh] != SIZE_MAX)
        export_fail(at + "the LogUp weights were read as a value");
      b.fam.alpha = b.reads[nn + nh + 1];
      b.fam.block = SIZE_MAX;
      for (size_t i = 0; i < pc.inputs.size(); ++i) {
        const auto &in = pc.inputs[i];
        if (in.kind == ir::InputBlock::kRealizationPub &&
            in.real.kind == ir::RealRef::kWeights && in.real.a == ce.real.a)
          b.fam.block = i;
      }
      if (b.fam.block == SIZE_MAX)
        export_fail(at + "no input block holds table " + std::to_string(ce.real.a) +
                    "'s weights");
      if (b.log.dens.empty() || b.log.sum == SIZE_MAX || b.log.z == SIZE_MAX)
        export_fail(at + "the LogUp closure recorded no fraction tree");
    } else if (ce.real.kind == ir::RealRef::kMacH) {
      if (b.reads.size() != 3)
        export_fail(at + "a MAC H circuit has " + std::to_string(b.reads.size()) +
                    " reads");
      b.fam.kind = Fam::kMacH;
      b.fam.bits = b.reads[0];
      b.fam.powers = b.reads[1];
      b.fam.tag = b.reads[2];
      if (b.log.chunks.empty() || b.log.z == SIZE_MAX)
        export_fail(at + "the MAC H closure recorded no chunks");
    }
    for (size_t r : b.reads)
      if (r != SIZE_MAX && r >= t.nodes.size())
        export_fail(at + "a read's view is no node");
  }
}

// ------------------------------------------------- the relational mirror --

// The C++ mirror of the relational check (GKR/Rel.lean) over field
// elements: per cut node of the table and coordinate, the wire equals the
// node's one-level expression over its kids' wires (and its aux wires) by
// the lazy difference check (A14), and every assertion pair asserts its
// root's wire. The DAG
// is the certificate's (kept nodes; any other node is zero).
//
// The mirror also records what the check plan prices (plan_entries): per
// cut node and per entry's family, its cuts in the order the Lean check
// lists them (nodeCutsE: the coordinates, then the aux cuts; famCuts), in
// blocks of kCutBlock cuts.
inline constexpr size_t kCutBlock = 64;
// A block of consecutive cuts: how many, how many are one wire, and over
// the others the wires and constants their tree expressions read and their
// scales by a constant other than 1 and -1.
struct CutBlock {
  size_t cuts = 0, free = 0, leaves = 0, scales = 0;
};
template <class F>
class RelMirror {
 public:
  using Elt = typename F::Elt;
  using Wire = typename EmitWalk<F>::Wire;

  // A monomial c v_a v_b (a <= b, node 0 the constant one).
  struct Mono {
    size_t a, b;
    Elt c;
  };
  using Poly = std::vector<Mono>;

  // A tree expression over wires (Lean `GKR.Rel.TE`, with n-ary sums).
  struct TE {
    enum K : uint8_t { kWire, kConst, kSum, kScale, kMul };
    K k = kConst;
    Wire w;
    Elt c;
    std::vector<TE> kids;
  };

  RelMirror(const F &f, const GkrCertificate<F> &cert, const ir::Program &p,
            const std::vector<ir::InputBlock> &inputs, const EmitTable<F> &t)
      : f_(f), c_(cert), p_(p), in_(inputs), t_(t), pos_(cert.nnodes, UINT32_MAX) {
    for (size_t i = 0; i < cert.node_id.size(); ++i) pos_[cert.node_id[i]] = uint32_t(i);
    for (uint32_t z : cert.asserted()) asserted_.insert(z);
  }

  // The assertion pair (Z, U) of the node assert0 returned, Z = 0 when it
  // folded away; why not in WHY.
  bool pair(size_t z, size_t *Z, size_t *U, std::string *why) const {
    if (z < c_.ninput) {
      *why = "assert0 returned an input";
      return false;
    }
    auto [b, e] = span(z);
    if (b == e) {
      *Z = 0;
      *U = 0;
      return true;
    }
    for (size_t t = b; t < e; ++t)
      if (c_.node_terms[3 * t] == 0 && c_.node_terms[3 * t + 1] == 0) {
        *Z = z;
        *U = c_.node_terms[3 * t + 2];
        return true;
      }
    *why = "assert0 returned node " + std::to_string(z) + " of no assertion term";
    return false;
  }

  // Empty when entry block BLK (its assertion pairs ZU) checks, else why the
  // first item does not: the cuts of the block's nodes, then the
  // assertions.
  std::string entry_errors(size_t k, const typename EmitTable<F>::Block &blk,
                           const std::vector<std::pair<size_t, size_t>> &zu) {
    if (entry_stats_.size() <= k) entry_stats_.resize(k + 1);
    auto &st = entry_stats_[k];
    for (size_t n = blk.lo; n < blk.hi; ++n) {
      std::string why;
      cuts_.clear();
      // An uncut node carries no wires; its parent's cuts check it.
      if (!t_.cut[n]) {
        if (!t_.W[n].empty())
          return "entry " + std::to_string(k) + ", node " + std::to_string(n) +
                 ": an uncut node carries wires";
        continue;
      }
      if (!node_cuts(n, &why))
        return "entry " + std::to_string(k) + ", node " + std::to_string(n) +
               " (kind " + std::to_string(int(t_.nodes[n].node.kind)) + "): " + why;
      for (size_t i = 0; i < cuts_.size(); ++i) {
        const std::string w = cut_error(cuts_[i].w, cuts_[i].e, &st);
        if (!w.empty())
          return "entry " + std::to_string(k) + ", node " + std::to_string(n) +
                 " (kind " + std::to_string(int(t_.nodes[n].node.kind)) + "), cut " +
                 std::to_string(i) + " (" + cuts_[i].what + "): " + w;
      }
      ncuts_ += cuts_.size();
      st.nodes += 1;
      st.items += cuts_.size();
      // node_cuts appends the coordinates' cuts after the aux cuts the
      // expansion recorded; the Lean check lists the coordinates first.
      if (node_census_.size() <= n) node_census_.resize(n + 1);
      std::vector<CutBlock> &cen = node_census_[n];
      const size_t first = cuts_.size() - t_.nodes[n].len;
      for (size_t i = first; i < cuts_.size(); ++i) census_add(cen, cuts_[i].e);
      for (size_t i = 0; i < first; ++i) census_add(cen, cuts_[i].e);
    }
    cur_entry_ = k;
    // A realization's assertion is its family's item.
    if (blk.fam.kind == EmitTable<F>::Fam::kLogup || blk.fam.kind == EmitTable<F>::Fam::kMacH)
      return family_errors(k, blk, zu, &st);
    for (size_t i = 0; i < zu.size(); ++i) {
      const TE e = blk.has_root ? wire(t_.W[blk.root].at(i))
                                : wire(Wire{f_.zero(), f_.one(), blk.inputs.at(i)});
      const std::string w = zero_error(zu[i].first, zu[i].second, e, &st);
      if (!w.empty())
        return "entry " + std::to_string(k) + ", assertion " + std::to_string(i) +
               ": " + w;
    }
    return family_errors(k, blk, zu, &st);
  }
  size_t cuts_checked() const { return ncuts_; }
  // Per table node, its cuts' blocks (empty for an uncut node); per entry,
  // its family cuts' blocks.
  const std::vector<std::vector<CutBlock>> &node_census() const { return node_census_; }
  const std::vector<std::vector<CutBlock>> &family_census() const { return family_census_; }

  // Per entry: its cut nodes and checked cuts, the DAG terms the checks
  // read, and the largest difference polynomial.
  struct EntryStats {
    size_t nodes = 0, items = 0, touched = 0, max_d = 0;
  };
  const std::vector<EntryStats> &entry_stats() const { return entry_stats_; }

  // The circuit whose table this is, and the print comparison
  // (Mirror::eq_print) the family guards use; set before entry_errors.
  void set_circuit(const ir::Circuit &pc, std::function<bool(size_t, Id)> eqb) {
    pc_ = &pc;
    eqb_ = std::move(eqb);
  }

  // Empty when the family record of entry K (block BLK, its assertion
  // pairs ZU, printed entry CE) checks as the Lean family check reads it
  // (RelFamily.lean): its guards, then its cuts and its one assertion item
  // through the lazy difference check; else why not.
  std::string family_errors(size_t k, const typename EmitTable<F>::Block &blk,
                            const std::vector<std::pair<size_t, size_t>> &zu,
                            EntryStats *st) {
    using Fam = typename EmitTable<F>::Fam;
    const std::string at = "entry " + std::to_string(k) + ", family: ";
    if (pc_ == nullptr) return at + "no circuit";
    const ir::CircuitEntry &ce = pc_->entries.at(k);
    const Fam &g = blk.fam;
    std::string why;
    if (ce.kind == ir::CircuitEntry::kAlignment) {
      if (g.kind != Fam::kAlignment) return at + "an alignment without its record";
      why = alignment_error(ce.id, g.block, zu);
    } else if (ce.kind != ir::CircuitEntry::kRealization) {
      return g.kind == Fam::kNone ? "" : at + "a record on a placed entry";
    } else if (ce.real.kind == ir::RealRef::kLogup && g.kind == Fam::kLogup) {
      why = logup_error(ce.real.a, ce.real.b, blk, zu, st);
    } else if (ce.real.kind == ir::RealRef::kMacH && g.kind == Fam::kMacH) {
      why = mach_error(ce.real.a, blk, zu, st);
    } else {
      why = "a realization of no checked family, or a record of another";
    }
    return why.empty() ? "" : at + why;
  }

  // Empty when the cut W = E checks (A14), else why not; ST, when given,
  // accumulates the terms read and the largest difference.
  std::string cut_error(const Wire &w, const TE &e, EntryStats *st = nullptr) {
    if (is_wire(e, w)) return "";
    return diff_error(&w, e, st);
  }

 private:
  struct Cut {
    Wire w;
    TE e;
    std::string what;
  };

  // ------------------------------------------------------- polynomials --
  static bool mono_lt(const Mono &m, const Mono &n) {
    return m.a < n.a || (m.a == n.a && m.b < n.b);
  }
  Poly add(const Poly &p, const Poly &q) const {
    Poly out;
    out.reserve(p.size() + q.size());
    size_t i = 0, j = 0;
    while (i < p.size() && j < q.size()) {
      if (mono_lt(p[i], q[j])) {
        out.push_back(p[i++]);
      } else if (mono_lt(q[j], p[i])) {
        out.push_back(q[j++]);
      } else {
        const Elt c = f_.addf(p[i].c, q[j].c);
        if (c != f_.zero()) out.push_back(Mono{p[i].a, p[i].b, c});
        ++i;
        ++j;
      }
    }
    while (i < p.size()) out.push_back(p[i++]);
    while (j < q.size()) out.push_back(q[j++]);
    return out;
  }
  Poly sum(std::vector<Poly> ps) const {
    if (ps.empty()) return {};
    while (ps.size() > 1) {
      std::vector<Poly> nx;
      for (size_t i = 0; i + 1 < ps.size(); i += 2) nx.push_back(add(ps[i], ps[i + 1]));
      if (ps.size() % 2) nx.push_back(std::move(ps.back()));
      ps = std::move(nx);
    }
    return std::move(ps[0]);
  }
  Poly scale(const Elt &c, const Poly &p) const {
    Poly out;
    if (c == f_.zero()) return out;
    out.reserve(p.size());
    for (const Mono &m : p) {
      const Elt d = f_.mulf(c, m.c);
      if (d != f_.zero()) out.push_back(Mono{m.a, m.b, d});
    }
    return out;
  }
  Poly cnst(const Elt &c) const {
    if (c == f_.zero()) return {};
    return {Mono{0, 0, c}};
  }
  static Mono mono2(size_t x, size_t y, const Elt &c) {
    return x <= y ? Mono{x, y, c} : Mono{y, x, c};
  }

  // The DAG.
  std::pair<size_t, size_t> span(size_t n) const {
    if (n < c_.ninput || n >= pos_.size() || pos_[n] == UINT32_MAX) return {0, 0};
    return {c_.node_term_begin[pos_[n]], c_.node_term_begin[pos_[n] + 1]};
  }
  const Elt &kload(size_t t) const { return c_.constants.at(c_.node_terms[3 * t]); }

  // Peel (Rel.lean `peel`): a non-input node of one term k 1 z is k z,
  // repeated; none for a zero node.
  std::optional<std::pair<Elt, size_t>> peel(size_t n) const {
    Elt c = f_.one();
    for (;;) {
      if (n < c_.ninput) return std::make_pair(c, n);
      auto [b, e] = span(n);
      if (b == e) return std::nullopt;
      if (e == b + 1 && c_.node_terms[3 * b + 1] == 0 && c_.node_terms[3 * b + 2] < n) {
        c = f_.mulf(c, kload(b));
        n = c_.node_terms[3 * b + 2];
        continue;
      }
      return std::make_pair(c, n);
    }
  }
  // The product of two polynomials of degree at most one.
  Poly mul1(const Poly &p, const Poly &q) const {
    std::vector<Poly> ps;
    for (const Mono &m : p)
      for (const Mono &n : q) {
        const Elt k = f_.mulf(m.c, n.c);
        if (k != f_.zero()) ps.push_back({mono2(m.b, n.b, k)});
      }
    return sum(std::move(ps));
  }
  // Node N peeled to c x, as c [x] (the constant c for x = 0, zero for a
  // zero node).
  Poly peeled(size_t n) const {
    const auto pl = peel(n);
    if (!pl) return {};
    if (pl->second == 0) return cnst(pl->first);
    if (pl->first == f_.zero()) return {};
    return {Mono{0, pl->second, pl->first}};
  }
  // A wire c0 + c1 x as c0 + c1 [peel x].
  Poly wire_poly(const Wire &w) const { return add(cnst(w.c0), scale(w.c1, peeled(w.x))); }
  // The tree side: wires as atoms, product monomials over peeled atoms.
  bool te_poly(const TE &e, Poly *out) {
    switch (e.k) {
      case TE::kWire:
        *out = wire_poly(e.w);
        return true;
      case TE::kConst:
        *out = cnst(e.c);
        return true;
      case TE::kSum: {
        std::vector<Poly> ps(e.kids.size());
        for (size_t i = 0; i < e.kids.size(); ++i)
          if (!te_poly(e.kids[i], &ps[i])) return false;
        *out = sum(std::move(ps));
        return true;
      }
      case TE::kScale: {
        Poly q;
        if (!te_poly(e.kids[0], &q)) return false;
        *out = scale(e.c, q);
        return true;
      }
      case TE::kMul: {
        Poly x[2];
        for (int j = 0; j < 2; ++j) {
          const TE &o = e.kids[j];
          if (o.k == TE::kConst)
            x[j] = cnst(o.c);
          else if (o.k == TE::kWire)
            x[j] = wire_poly(o.w);
          else
            return false;
        }
        *out = mul1(x[0], x[1]);
        return true;
      }
    }
    return false;
  }
  static bool is_wire(const TE &e, const Wire &w) { return e.k == TE::kWire && e.w == w; }

  // ---- The lazy difference check (A14). D = (c0 + c1 [peel W.n]) - the
  // tree side, as a map from monomial (a, b) to its nonzero coefficient.
  // While D is nonzero, its linear atom [x] of the largest node id is
  // replaced by x's terms (k 1 b as k [peel b], a product k a b as
  // k [peel a][peel b]); an input atom there refuses. Unfolding keeps D's
  // value, and the atom never returns (term operands are below their
  // node), so the loop ends; once no non-input linear atom is left, D is
  // the difference of the two full normal forms.
  using DMap = std::map<std::pair<size_t, size_t>, Elt>;
  void dadd(DMap &D, const Mono &m, const Elt &k) const {
    const Elt c = f_.mulf(k, m.c);
    if (c == f_.zero()) return;
    auto [it, fresh] = D.try_emplace({m.a, m.b}, c);
    if (fresh) return;
    it->second = f_.addf(it->second, c);
    if (it->second == f_.zero()) D.erase(it);
  }
  void dadd(DMap &D, const Poly &p, const Elt &k) const {
    for (const Mono &m : p) dadd(D, m, k);
  }
  // Empty when D for wire W (null: zero) against E reduces to zero.
  std::string diff_error(const Wire *w, const TE &e, EntryStats *st) {
    DMap D;
    if (w != nullptr) dadd(D, wire_poly(*w), f_.one());
    Poly q;
    if (!te_poly(e, &q)) return "the tree's form fails";
    dadd(D, q, f_.mone());
    size_t touched = 0, max_d = D.size();
    std::string why;
    for (;;) {
      if (D.empty()) break;
      // The linear atoms (0, x) sort first; the last of them has the
      // largest x.
      auto it = D.lower_bound({1, 0});
      const size_t x = it == D.begin() ? 0 : std::prev(it)->first.second;
      if (x < c_.ninput) {
        const auto &m = *D.rbegin();
        why = "the difference does not vanish: " + std::to_string(D.size()) +
              " monomials left, the last [" + std::to_string(m.first.first) + "," +
              std::to_string(m.first.second) + "]";
        break;
      }
      --it;
      const Elt c = it->second;
      D.erase(it);
      auto [b, en] = span(x);
      for (size_t t = b; t < en; ++t) {
        ++touched;
        const size_t a0 = c_.node_terms[3 * t + 1], a1 = c_.node_terms[3 * t + 2];
        if (a0 >= x || a1 >= x) {
          why = "node " + std::to_string(x) + " reads a node not below it";
          break;
        }
        const Elt k = f_.mulf(c, kload(t));
        if (a0 == 0)
          dadd(D, peeled(a1), k);
        else
          dadd(D, mul1(peeled(a0), peeled(a1)), k);
      }
      if (!why.empty()) break;
      max_d = std::max(max_d, D.size());
    }
    if (st != nullptr) {
      st->touched += touched;
      st->max_d = std::max(st->max_d, max_d);
    }
    return why;
  }
  std::string zero_error(size_t Z, size_t U, const TE &e, EntryStats *st) {
    if (Z == 0) {
      const std::string w = diff_error(nullptr, e, st);
      return w.empty() ? "" : "folded away, but the root is not zero: " + w;
    }
    if (Z < c_.ninput) return "an input asserted";
    if (!asserted_.count(uint32_t(Z)))
      return "node " + std::to_string(Z) + " is no asserted node";
    auto [b, en] = span(Z);
    bool term = false;
    for (size_t t = b; t < en; ++t)
      term = term || (c_.node_terms[3 * t] == 0 && c_.node_terms[3 * t + 1] == 0 &&
                      c_.node_terms[3 * t + 2] == U);
    if (!term)
      return "node " + std::to_string(Z) + " has no assertion term reading " +
             std::to_string(U);
    if (e.k == TE::kWire && e.w.c0 == f_.zero() && e.w.x == U) return "";
    const std::string w = cut_error(Wire{f_.zero(), f_.one(), U}, e, st);
    return w.empty() ? "" : "the asserted node is not the root's wire: " + w;
  }

  // ---- The family checks (step 4, RelFamily.lean). ----
  size_t value_field(size_t u) const {
    const ir::Value &v = p_.values.at(u);
    return v.domain != kNone ? size_t(p_.domains.at(v.domain).field) : size_t(v.field);
  }
  size_t circ_field() const { return p_.domains.at(pc_->domain).field; }
  // Node K is a cut value leaf of a value id; its id in *U.
  bool value_node(size_t k, size_t *u) const {
    if (k >= t_.nodes.size() || !t_.cut[k]) return false;
    const ENode &x = t_.nodes[k].node;
    if (x.kind != ENode::kValue) return false;
    *u = x.u;
    return x.u < p_.values.size();
  }
  size_t len(size_t k) const { return t_.nodes.at(k).len; }
  const Wire &Wk(size_t k, size_t i) const { return t_.W.at(k).at(i); }
  // Checks the cuts CS, then the item (Z, U, E) of the one pair.
  std::string family_cuts(const std::vector<std::pair<Wire, TE>> &cs,
                          const std::vector<std::pair<size_t, size_t>> &zu, const TE &item,
                          EntryStats *st) {
    for (size_t i = 0; i < cs.size(); ++i) {
      const std::string w = cut_error(cs[i].first, cs[i].second, st);
      if (!w.empty()) return "cut " + std::to_string(i) + ": " + w;
    }
    ncuts_ += cs.size();
    if (st != nullptr) st->items += cs.size();
    if (family_census_.size() <= cur_entry_) family_census_.resize(cur_entry_ + 1);
    for (const auto &c : cs) census_add(family_census_[cur_entry_], c.second);
    if (zu.size() != 1) return "asserts: " + std::to_string(zu.size()) + " pairs, not one";
    const std::string w = zero_error(zu[0].first, zu[0].second, item, st);
    return w.empty() ? "" : "the item: " + w;
  }
  Wire node_wire(size_t n) const { return Wire{f_.zero(), f_.one(), n}; }
  std::string alignment_error(size_t count, size_t b,
                              const std::vector<std::pair<size_t, size_t>> &zu) const {
    if (b >= in_.size() || in_[b].kind != ir::InputBlock::kFiller || in_[b].n != count)
      return "the filler block";
    if (zu.size() != count) return "asserts";
    for (size_t i = 0; i < count; ++i)
      if (zu[i].second != in_[b].at + i) return "asserts: pair " + std::to_string(i);
    return "";
  }
  // The spans of a fraction tree of N leaves and inner nodes INNER (Lean
  // FracTree.spans/okB): false unless every inner node's kids come before
  // it and are adjacent, and the last fraction spans [0, N).
  static bool spans_ok(size_t n, const std::vector<FamilyLog::Inner> &inner) {
    if (n == 0) return false;
    std::vector<std::pair<size_t, size_t>> sp;
    for (size_t i = 0; i < n; ++i) sp.push_back({i, i + 1});
    for (size_t k = 0; k < inner.size(); ++k) {
      const auto &x = inner[k];
      if (x.l >= n + k || x.r >= n + k || sp[x.l].second != sp[x.r].first) return false;
      sp.push_back({sp[x.l].first, sp[x.r].second});
    }
    return sp.back() == std::make_pair(size_t(0), n);
  }
  std::string logup_error(size_t tt, size_t gg, const typename EmitTable<F>::Block &blk,
                          const std::vector<std::pair<size_t, size_t>> &zu, EntryStats *st) {
    const auto &g = blk.fam;
    const FamilyLog &lg = blk.log;
    // 1. the table, the group, the range, alpha's field.
    if (tt >= p_.tables.size() || gg >= p_.tables[tt].groups.size()) return "field";
    const ir::Table &tb = p_.tables[tt];
    if (tb.rows_expr != kNone) return "field";
    size_t T = 0;
    try {
      T = std::stoull(tb.size);
    } catch (...) {
      return "field";
    }
    if (tb.alpha >= p_.challenges.size() || p_.challenges[tb.alpha].field != circ_field())
      return "field";
    // 2. alpha.
    size_t ua = 0;
    if (!value_node(g.alpha, &ua) || p_.values[ua].kind != ir::Value::kChallenge ||
        p_.values[ua].ref != tb.alpha || value_field(ua) != circ_field() || len(g.alpha) < 1)
      return "alpha";
    // 3. the needles.
    const ir::TableGroup &gr = tb.groups[gg];
    if (g.needles.size() != gr.members.size()) return "needle count";
    size_t n = 0;
    for (size_t m = 0; m < gr.members.size(); ++m) {
      const auto &mb = gr.members[m];
      const size_t y = g.needles[m];
      if (y >= t_.nodes.size() || !t_.cut[y] || mb[0] >= p_.predicates.size())
        return "needle " + std::to_string(m);
      const auto &nd = p_.predicates[mb[0]].in.lookup.needles;
      if (mb[1] >= nd.size() || !eqb_(y, nd[mb[1]]) || mb[2] + mb[3] > len(y))
        return "needle " + std::to_string(m);
      n += mb[3];
    }
    // 4. the histograms.
    std::vector<size_t> hv;
    if (gr.static_mult != kNone) hv.push_back(gr.static_mult);
    if (gr.late_mult != kNone) hv.push_back(gr.late_mult);
    if (hv.empty() || g.hists.size() != hv.size()) return "hist";
    for (size_t h = 0; h < hv.size(); ++h) {
      size_t u = 0;
      if (!value_node(g.hists[h], &u) || u != hv[h] || len(g.hists[h]) != p_.values[u].size() ||
          len(g.hists[h]) > T)
        return "hist";
    }
    // 5. the weights.
    if (g.block >= in_.size()) return "weights";
    const ir::InputBlock &wb = in_[g.block];
    if (wb.kind != ir::InputBlock::kRealizationPub || wb.real.kind != ir::RealRef::kWeights ||
        wb.real.a != tt || wb.n != T || wb.at < 1 || wb.at + T > pc_->public_inputs)
      return "weights";
    // 6. the tree.
    if (lg.dens.size() != n) return "span: " + std::to_string(lg.dens.size()) + " leaves";
    if (!spans_ok(n, lg.inner)) return "span";
    // The cuts: each leaf alpha - needle, each inner node, S.
    const Elt m1 = f_.mone();
    std::vector<std::pair<Wire, TE>> cs;
    size_t i = 0;
    for (size_t m = 0; m < gr.members.size(); ++m)
      for (size_t j = 0; j < gr.members[m][3]; ++j)
        cs.push_back({node_wire(lg.dens[i++]),
                      add_te(wire(Wk(g.alpha, 0)),
                             scale_te(m1, wire(Wk(g.needles[m], gr.members[m][2] + j))))});
    auto den = [&](size_t a) {
      return wire(node_wire(a < n ? lg.dens[a] : lg.inner[a - n].den));
    };
    // n_a d_b: d_b alone when a is a leaf.
    auto term = [&](size_t a, size_t b) {
      return a < n ? den(b) : mul_te(wire(node_wire(lg.inner[a - n].num)), den(b));
    };
    for (const auto &x : lg.inner) {
      cs.push_back({node_wire(x.num), add_te(term(x.l, x.r), term(x.r, x.l))});
      cs.push_back({node_wire(x.den), mul_te(den(x.l), den(x.r))});
    }
    std::vector<TE> ps;
    for (size_t h : g.hists)
      for (size_t j = 0; j < len(h); ++j)
        ps.push_back(mul_te(wire(Wk(h, j)), wire(node_wire(wb.at + j))));
    cs.push_back({node_wire(lg.sum), sum_te(std::move(ps))});
    // The item N - D S.
    const size_t r = n + lg.inner.size() - 1;
    const TE N = r < n ? konst(f_.one()) : wire(node_wire(lg.inner[r - n].num));
    const TE item = add_te(N, scale_te(m1, mul_te(den(r), wire(node_wire(lg.sum)))));
    return family_cuts(cs, zu, item, st);
  }
  std::string mach_error(size_t pp, const typename EmitTable<F>::Block &blk,
                         const std::vector<std::pair<size_t, size_t>> &zu, EntryStats *st) {
    const auto &g = blk.fam;
    const FamilyLog &lg = blk.log;
    // 1. the predicate, its MAC, its fields.
    if (pp >= p_.predicates.size()) return "field";
    const ir::Predicate &pd = p_.predicates[pp];
    const ir::MacRealization &mr = pd.mac;
    if (pd.body != ir::Predicate::kCross || mr.h_predicate != kNone ||
        pd.domain != pc_->domain || mr.mac_field != circ_field() ||
        mr.mac_field >= p_.fields.size())
      return "field";
    const std::string &ch = p_.fields[mr.mac_field].characteristic;
    if (ch == "0" || ch == "1") return "field";
    const size_t nch = mr.chunks, w = mr.width;
    // 2. the powers.
    size_t ur = 0;
    if (!value_node(g.powers, &ur) || len(g.powers) < nch || !powers_ok(ur, mr, nch))
      return "powers";
    // 3. the tag.
    size_t ut = 0;
    if (!value_node(g.tag, &ut) || ut != mr.tag || len(g.tag) < 1 ||
        value_field(ut) != mr.mac_field || p_.values[ut].size() == 0 ||
        p_.values[ut].kind != ir::Value::kLate)
      return "tag";
    // 4. the operand: its print is the predicate's x of nch w coordinates
    // (zeroPadB's first form; its coordinatewise form is not mirrored).
    if (g.bits >= t_.nodes.size() || !t_.cut[g.bits] || len(g.bits) != nch * w)
      return "bits";
    // 5. the chunks.
    if (lg.chunks.size() != nch) return "chunks";
    // The generator x: the element of code 2 (Lean codePow ar 2 i).
    const Elt gen = f_.of_scalar_field(2);
    if (elt_code(f_, gen) != "2") return "powers: no element of code 2";
    const Elt m1 = f_.mone();
    std::vector<std::pair<Wire, TE>> cs;
    for (size_t c = 0; c < nch; ++c) {
      std::vector<TE> ts;
      Elt gp = f_.one();
      for (size_t i = 0; i < w; ++i) {
        ts.push_back(scale_te(gp, wire(Wk(g.bits, c * w + i))));
        gp = f_.mulf(gp, gen);
      }
      cs.push_back({node_wire(lg.chunks[c]), sum_te(std::move(ts))});
    }
    std::vector<TE> ps;
    for (size_t c = 0; c < nch; ++c)
      ps.push_back(mul_te(wire(node_wire(lg.chunks[c])), wire(Wk(g.powers, c))));
    const TE item = add_te(wire(Wk(g.tag, 0)), scale_te(m1, sum_te(std::move(ps))));
    return family_cuts(cs, zu, item, st);
  }
  // Lean powersB, less its index map's runs and the constant's entries:
  // value R is prod NCH (reindex _ (concat (leaf kv) (leaf one))), kv the
  // key's value of one coordinate, all in the MAC field.
  bool powers_ok(size_t r, const ir::MacRealization &mr, size_t nch) const {
    const size_t f = mr.mac_field;
    if (r >= p_.values.size() || value_field(r) != f || mr.key >= p_.challenges.size() ||
        p_.challenges[mr.key].field != f)
      return false;
    const ir::Value &v = p_.values[r];
    if (v.kind != ir::Value::kPubExpr || v.expr == kNone) return false;
    const ir::Expr &e = p_.nodes.at(v.expr);
    if (e.op != ir::Expr::kProd || e.x != nch) return false;
    const ir::Expr &ri = p_.nodes.at(e.a);
    if (ri.op != ir::Expr::kReindex) return false;
    const ir::Expr &cc = p_.nodes.at(ri.a);
    if (cc.op != ir::Expr::kConcat) return false;
    const ir::Expr &kl = p_.nodes.at(cc.a), &ol = p_.nodes.at(cc.b);
    if (kl.op != ir::Expr::kLeaf || ol.op != ir::Expr::kLeaf) return false;
    const size_t kv = kl.x;
    return kv < p_.values.size() && p_.values[kv].size() == 1 && value_field(kv) == f &&
           p_.values[kv].kind == ir::Value::kChallenge && p_.values[kv].ref == mr.key &&
           ol.x < p_.values.size() && p_.values[ol.x].kind == ir::Value::kConstant;
  }

  // ------------------------------------------------------- tree sides --
  TE wire(const Wire &w) const {
    TE e;
    e.k = TE::kWire;
    e.w = w;
    return e;
  }
  TE konst(const Elt &c) const {
    TE e;
    e.k = TE::kConst;
    e.c = c;
    return e;
  }
  TE sum_te(std::vector<TE> v) const {
    if (v.size() == 1) return std::move(v[0]);
    TE e;
    e.k = TE::kSum;
    e.kids = std::move(v);
    return e;
  }
  TE add_te(TE a, TE b) const {
    std::vector<TE> v;
    v.push_back(std::move(a));
    v.push_back(std::move(b));
    return sum_te(std::move(v));
  }
  TE scale_te(const Elt &c, TE a) const {
    TE e;
    e.k = TE::kScale;
    e.c = c;
    e.kids.push_back(std::move(a));
    return e;
  }
  TE mul_te(TE a, TE b) const {
    TE e;
    e.k = TE::kMul;
    e.kids.push_back(std::move(a));
    e.kids.push_back(std::move(b));
    return e;
  }
  Elt mone() const { return f_.mone(); }

  // Adds the wires and constants E reads, and its scales by a constant
  // other than 1 and -1, to B.
  void te_census(const TE &e, CutBlock *b) const {
    if (e.k == TE::kWire || e.k == TE::kConst) {
      ++b->leaves;
      return;
    }
    if (e.k == TE::kScale && !(e.c == f_.one() || e.c == f_.mone())) ++b->scales;
    for (const TE &x : e.kids) te_census(x, b);
  }
  // Appends a cut of tree expression E to the blocks V.
  void census_add(std::vector<CutBlock> &v, const TE &e) const {
    if (v.empty() || v.back().cuts == kCutBlock) v.emplace_back();
    CutBlock &b = v.back();
    ++b.cuts;
    if (e.k == TE::kWire) {
      ++b.free;
      return;
    }
    te_census(e, &b);
  }

  const Wire &W(size_t k, size_t i) const { return t_.W.at(k).at(i); }

  // The aux wires of the node being cut, read in order.
  struct AuxReader {
    const std::vector<Wire> *aux;
    size_t at = 0;
    bool ok = true;
    const Wire *next() {
      if (at >= aux->size()) {
        ok = false;
        return nullptr;
      }
      return &(*aux)[at++];
    }
  };
  // Records the cut of the next aux wire against E; its wire.
  TE aux_cut(AuxReader &r, TE e, const std::string &what) {
    const Wire *a = r.next();
    if (a == nullptr) return e;
    cuts_.push_back(Cut{*a, std::move(e), what});
    return wire(*a);
  }

  // The leaves of the chain rooted at K (through its flattened kids).
  // (A chain's interiors: its uncut kids of its own operation.)
  void chain_leaves(size_t k, std::vector<size_t> &out) const {
    const ENode &r = t_.nodes[k].node;
    for (size_t a : r.kids) {
      const ENode &x = t_.nodes[a].node;
      if (!t_.cut[a] && x.kind == ENode::kBin && x.op == r.op)
        chain_leaves(a, out);
      else
        out.push_back(a);
    }
  }
  // A combination of two operands: x + y, x y, x + y - x y, and x + y - 2 x y
  // (x + y in characteristic two).
  TE combine(uint8_t op, TE a, TE b) const {
    switch (op) {
      case ENode::kAdd:
        return sum_te({std::move(a), std::move(b)});
      case ENode::kMul:
      case ENode::kAnd:
        return mul_te(std::move(a), std::move(b));
      case ENode::kOr: {
        TE p = mul_te(a, b);
        return sum_te({std::move(a), std::move(b), scale_te(mone(), std::move(p))});
      }
      default: {
        if (F::kCharacteristicTwo) return sum_te({std::move(a), std::move(b)});
        TE p = mul_te(a, b);
        const Elt m2 = f_.negf(f_.addf(f_.one(), f_.one()));
        return sum_te({std::move(a), std::move(b), scale_te(m2, std::move(p))});
      }
    }
  }
  static bool multiplies(uint8_t op) {
    if (op == ENode::kAdd) return false;
    if (op == ENode::kXor) return !F::kCharacteristicTwo;
    return true;
  }
  TE chain_tree(uint8_t op, const std::vector<size_t> &leaves, size_t i, size_t j0,
                size_t j1, bool root, AuxReader &r) {
    if (j1 == j0 + 1) return kid(leaves[j0], i);
    const size_t jm = j0 + (j1 - j0) / 2;
    TE lo = chain_tree(op, leaves, i, j0, jm, false, r);
    TE hi = chain_tree(op, leaves, i, jm, j1, false, r);
    TE c = combine(op, std::move(lo), std::move(hi));
    if (root || !multiplies(op)) return c;
    return aux_cut(r, std::move(c), "chain aux");
  }
  // Logic::land / lor (balanced) over A[i0, i1).
  TE range_tree(bool any, const std::vector<TE> &a, size_t i0, size_t i1, bool root,
                AuxReader &r) {
    if (i1 <= i0) return konst(any ? f_.zero() : f_.one());
    if (i1 == i0 + 1) return a[i0];
    const size_t im = i0 + (i1 - i0) / 2;
    TE lo = range_tree(any, a, i0, im, false, r);
    TE hi = range_tree(any, a, im, i1, false, r);
    TE c = combine(any ? ENode::kOr : ENode::kAnd, std::move(lo), std::move(hi));
    if (root) return c;
    return aux_cut(r, std::move(c), "tree aux");
  }
  // 1 - (a xor b).
  TE xnor(const TE &a, const TE &b) const {
    TE x = combine(ENode::kXor, a, b);
    return sum_te({konst(f_.one()), scale_te(mone(), std::move(x))});
  }
  void lt_reduce(size_t i0, size_t i1, TE *xeq, TE *xlt, const std::vector<TE> &a,
                 const std::vector<TE> &b, bool root, bool lower, AuxReader &r) {
    if (i1 - i0 > 1) {
      TE eq0, eq1, lt0, lt1;
      const size_t im = i0 + (i1 - i0) / 2;
      lt_reduce(i0, im, &eq0, &lt0, a, b, false, true, r);
      lt_reduce(im, i1, &eq1, &lt1, a, b, false, false, r);
      *xeq = mul_te(eq1, eq0);
      *xlt = sum_te({std::move(lt1), mul_te(eq1, lt0)});
    } else {
      *xeq = xnor(a[i0], b[i0]);
      // (1 - a) b = b - a b.
      *xlt = sum_te({b[i0], scale_te(mone(), mul_te(a[i0], b[i0]))});
    }
    if (!root) {
      *xeq = aux_cut(r, std::move(*xeq), "comparison aux");
      if (lower) *xlt = aux_cut(r, std::move(*xlt), "comparison aux");
    }
  }
  TE eq_reduce(size_t i0, size_t i1, const std::vector<TE> &a, const std::vector<TE> &b,
               bool root, AuxReader &r) {
    if (i1 <= i0) return konst(f_.one());
    TE e;
    if (i1 == i0 + 1) {
      e = xnor(a[i0], b[i0]);
    } else {
      const size_t im = i0 + (i1 - i0) / 2;
      TE lo = eq_reduce(i0, im, a, b, false, r);
      TE hi = eq_reduce(im, i1, a, b, false, r);
      e = mul_te(std::move(lo), std::move(hi));
    }
    if (root) return e;
    return aux_cut(r, std::move(e), "comparison aux");
  }

  // The coordinates of operator O's output over input coordinates IN (a
  // view, or the constant rows of a named or sparse operator).
  bool op_rows(const EOp &o, const std::vector<TE> &in, std::vector<TE> *out,
               std::string *why) {
    out->clear();
    if (o.kind == EOp::kView) {
      if (o.idx >= p_.index_maps.size()) return *why = "no index map", false;
      std::vector<TE> cat = in;
      if (o.has_zero) {
        const ir::Value &z = p_.values.at(o.zero);
        for (const auto &x : z.entries) {
          if (x != "0") return *why = "a view's zero constant is not zero", false;
          cat.push_back(konst(f_.zero()));
        }
      }
      for (size_t j : p_.index_maps[o.idx]) {
        if (j >= cat.size()) return *why = "an index past the operand", false;
        out->push_back(cat[j]);
      }
      return true;
    }
    if (o.kind == EOp::kStaged) return *why = "a staged transform in an affine term", false;
    const auto *spec = static_cast<const OpSpec<F> *>(o.spec);
    if (spec == nullptr || !spec->emit)
      return *why = "an operator with no constant rows", false;
    const auto rows = spec->emit();
    for (const auto &row : rows) {
      std::vector<TE> s;
      for (const auto &[c, a] : row) {
        if (c >= in.size()) return *why = "a row reads past the operand", false;
        s.push_back(a == f_.one() ? in[c] : scale_te(a, in[c]));
      }
      out->push_back(s.empty() ? konst(f_.zero()) : sum_te(std::move(s)));
    }
    return true;
  }

  // A symbolic Logic over linear combinations of the previous stage's
  // coordinates (index SIZE_MAX: the constant one), for a staged
  // transform's stages.
  struct SymLC {
    using Elt = typename F::Elt;
    using EltW = std::vector<std::pair<size_t, Elt>>;
    const F &f_;
    explicit SymLC(const F &f) : f_(f) {}
    EltW lin(const EltW &x, const Elt &k, const EltW &y) const {
      std::map<size_t, Elt> m;
      for (const auto &[i, c] : x) m[i] = c;
      for (const auto &[i, c] : y) {
        const Elt d = f_.mulf(k, c);
        auto it = m.find(i);
        if (it == m.end())
          m[i] = d;
        else
          it->second = f_.addf(it->second, d);
      }
      EltW out;
      for (const auto &[i, c] : m)
        if (c != f_.zero()) out.push_back({i, c});
      return out;
    }
    EltW konst(uint64_t v) const {
      if (v == 0) return {};
      return {{SIZE_MAX, f_.of_scalar(v)}};
    }
    EltW mul(const Elt &k, const EltW &x) const { return lin({}, k, x); }
    EltW add(const EltW &a, const EltW &b) const { return lin(a, f_.one(), b); }
    EltW sub(const EltW &a, const EltW &b) const { return lin(a, f_.mone(), b); }
    EltW axpy(const EltW &y, const Elt &a, const EltW &x) const { return lin(y, a, x); }
  };

  // Staged transform O on input coordinates IN (one block): its outputs,
  // each stage but the last cut at its aux wires.
  bool staged_rows(const EOp &o, const std::vector<TE> &in, AuxReader &r,
                   std::vector<TE> *out, std::string *why) {
    const auto *spec = static_cast<const OpSpec<F> *>(o.spec);
    if (spec == nullptr || spec->staged == nullptr)
      return *why = "a staged node with no staged transform", false;
    const size_t n = in.size();
    SymLC lc(f_);
    std::vector<typename SymLC::EltW> a(n);
    for (size_t i = 0; i < n; ++i) a[i] = {{i, f_.one()}};
    std::vector<std::vector<typename SymLC::EltW>> stages;
    const std::function<void(std::vector<typename SymLC::EltW> &)> hook =
        [&](std::vector<typename SymLC::EltW> &x) {
          stages.push_back(x);
          for (size_t i = 0; i < x.size(); ++i) x[i] = {{i, f_.one()}};
        };
    spec->staged->forward(lc, a, &hook);
    std::vector<TE> prev = in;
    for (size_t s = 0; s < stages.size(); ++s) {
      std::vector<TE> cur;
      for (const auto &comb : stages[s]) {
        std::vector<TE> parts;
        for (const auto &[i, c] : comb) {
          if (i == SIZE_MAX)
            parts.push_back(konst(c));
          else
            parts.push_back(c == f_.one() ? prev.at(i) : scale_te(c, prev.at(i)));
        }
        cur.push_back(parts.empty() ? konst(f_.zero()) : sum_te(std::move(parts)));
      }
      if (s + 1 < stages.size()) {
        for (auto &e : cur) e = aux_cut(r, std::move(e), "stage aux");
        if (!r.ok) return *why = "too few aux wires for the stages", false;
      }
      prev = std::move(cur);
    }
    *out = std::move(prev);
    return true;
  }

  // Coordinate I of kid A as its parent reads it: a cut node's wire, an
  // uncut node's one-level form (its own kids read the same way).
  TE kid(size_t a, size_t i) {
    if (t_.cut.at(a)) return wire(W(a, i));
    auto it = uncut_.find(a);
    if (it == uncut_.end()) {
      std::vector<TE> te;
      std::string why;
      if (!node_te(a, &te, &why)) {
        expand_error_ = "uncut node " + std::to_string(a) + ": " + why;
        te.assign(t_.nodes[a].len, konst(f_.zero()));
      }
      it = uncut_.emplace(a, std::move(te)).first;
    }
    return it->second.at(i);
  }
  // The cuts of cut node K (into cuts_): per coordinate its wire against its
  // one-level expression, and its aux wires'.
  bool node_cuts(size_t k, std::string *why) {
    if (t_.W[k].size() != t_.nodes[k].len) return *why = "wires of another length", false;
    std::vector<TE> te;
    expand_error_.clear();
    if (!node_te(k, &te, why)) return false;
    if (!expand_error_.empty()) return *why = expand_error_, false;
    for (size_t i = 0; i < te.size(); ++i)
      cuts_.push_back(Cut{W(k, i), std::move(te[i]), "coordinate " + std::to_string(i)});
    return true;
  }
  // Node K's one-level expression per coordinate (into OUT), over its kids
  // as kid() reads them; its aux wires' cuts into cuts_.
  bool node_te(size_t k, std::vector<TE> *out_te, std::string *why) {
    const ENodeInfo &ni = t_.nodes[k];
    const ENode &n = ni.node;
    const size_t L = ni.len;
    AuxReader r{&t_.aux[k]};
    out_te->assign(L, TE{});
    auto kid_wires = [&](size_t a) {
      std::vector<TE> v;
      for (size_t i = 0; i < t_.nodes.at(a).len; ++i) v.push_back(kid(a, i));
      return v;
    };
    auto cut = [&](size_t i, TE e) { (*out_te)[i] = std::move(e); };
    switch (n.kind) {
      case ENode::kLin: {
        const auto *lin = static_cast<const Lin<F> *>(n.lin);
        if (n.terms.empty()) {
          for (size_t i = 0; i < L; ++i) cut(i, konst(f_.zero()));
          break;
        }
        if (lin == nullptr) return *why = "a lin node with no combination", false;
        std::vector<std::vector<TE>> terms;
        for (size_t t = 0; t < n.terms.size(); ++t) {
          std::vector<TE> v = kid_wires(n.terms[t].view);
          for (const EOp &o : n.terms[t].ops) {
            std::vector<TE> nx;
            if (!op_rows(o, v, &nx, why)) return false;
            v = std::move(nx);
          }
          if (v.size() != L) return *why = "a term of another length", false;
          terms.push_back(std::move(v));
        }
        for (size_t i = 0; i < L; ++i) {
          std::vector<TE> s;
          for (size_t t = 0; t < terms.size(); ++t) {
            const Elt &c = lin->terms.at(t).scale;
            s.push_back(c == f_.one() ? terms[t][i] : scale_te(c, terms[t][i]));
          }
          cut(i, sum_te(std::move(s)));
        }
        break;
      }
      case ENode::kConst: {
        const auto *x = static_cast<const ExprNode<F> *>(n.src);
        for (size_t i = 0; i < L; ++i) {
          if (x != nullptr) {
            cut(i, konst(x->c.at(i)));
          } else {
            const ir::Value &cv = p_.values.at(n.v);
            if (cv.entries.at(i) != "0")
              return *why = "a constant node with no expression is not zero", false;
            cut(i, konst(f_.zero()));
          }
        }
        break;
      }
      case ENode::kBin: {
        std::vector<size_t> leaves;
        chain_leaves(k, leaves);
        for (size_t i = 0; i < L; ++i)
          cut(i, chain_tree(n.op, leaves, i, 0, leaves.size(), true, r));
        break;
      }
      case ENode::kScale: {
        Elt c = f_.one();
        if (n.code != "1")
          c = n.src != nullptr ? static_cast<const ExprNode<F> *>(n.src)->c.at(0)
                               : f_.mone();
        for (size_t i = 0; i < L; ++i) cut(i, scale_te(c, kid(n.kids[0], i)));
        break;
      }
      case ENode::kSum: {
        for (size_t i = 0; i < L; ++i) {
          std::vector<TE> s;
          for (size_t j = 0; j < n.w; ++j) s.push_back(kid(n.kids[0], i * n.w + j));
          cut(i, s.empty() ? konst(f_.zero()) : sum_te(std::move(s)));
        }
        break;
      }
      case ENode::kProd: {
        for (size_t i = 0; i < L; ++i) {
          std::vector<TE> w;
          for (size_t j = 0; j < n.w; ++j) w.push_back(kid(n.kids[0], i * n.w + j));
          if (w.empty()) {
            cut(i, konst(f_.one()));
            continue;
          }
          while (w.size() > 1) {
            std::vector<TE> nx;
            const bool last = w.size() == 2;
            for (size_t j = 0; j + 1 < w.size(); j += 2) {
              TE p = mul_te(w[j], w[j + 1]);
              nx.push_back(last ? std::move(p) : aux_cut(r, std::move(p), "product aux"));
            }
            if (w.size() % 2) nx.push_back(w.back());
            w = std::move(nx);
          }
          cut(i, std::move(w[0]));
        }
        break;
      }
      case ENode::kBroadcast: {
        const auto &idx = p_.index_maps.at(n.idx);
        for (size_t i = 0; i < L; ++i) cut(i, kid(n.kids[0], idx.at(i)));
        break;
      }
      case ENode::kNot: {
        const ir::Value &ones = p_.values.at(n.v);
        for (size_t i = 0; i < L; ++i) {
          if (ones.entries.at(i) != "1")
            return *why = "a negation's constant is not ones", false;
          cut(i, sum_te({konst(f_.one()), scale_te(mone(), kid(n.kids[0], i))}));
        }
        break;
      }
      case ENode::kMux: {
        for (size_t i = 0; i < L; ++i) {
          TE c = kid(n.kids[0], i), t = kid(n.kids[1], i),
             e = kid(n.kids[2], i);
          if (n.flag) {
            // c t + (1 - c) e = c t + e - c e.
            TE ct = mul_te(c, t), ce = mul_te(c, e);
            cut(i, sum_te({std::move(ct), e, scale_te(mone(), std::move(ce))}));
          } else {
            TE d = aux_cut(r, sum_te({t, scale_te(mone(), e)}), "mux aux");
            cut(i, sum_te({e, mul_te(c, std::move(d))}));
          }
        }
        break;
      }
      case ENode::kCmp: {
        const auto *x = static_cast<const ExprNode<F> *>(n.src);
        if (x == nullptr) return *why = "a comparison with no expression", false;
        const size_t w = n.w;
        for (size_t i = 0; i < L; ++i) {
          std::vector<TE> a, b;
          for (size_t j = 0; j < w; ++j) a.push_back(kid(n.kids[0], i * w + j));
          for (size_t j = 0; j < w; ++j)
            b.push_back(n.flag ? konst(((x->value >> j) & 1) ? f_.one() : f_.zero())
                               : kid(n.kids[1], i * w + j));
          TE e;
          if (n.op == ENode::kEq) {
            e = eq_reduce(0, w, a, b, true, r);
          } else {
            const bool leq = n.op == ENode::kLeq;
            if (w == 0) {
              e = konst(f_.zero());
            } else {
              TE xeq, xlt;
              lt_reduce(0, w, &xeq, &xlt, leq ? b : a, leq ? a : b, true, false, r);
              e = std::move(xlt);
            }
            if (leq) e = sum_te({konst(f_.one()), scale_te(mone(), std::move(e))});
          }
          cut(i, std::move(e));
        }
        break;
      }
      case ENode::kTree: {
        const size_t w = n.w;
        for (size_t i = 0; i < L; ++i) {
          std::vector<TE> a;
          for (size_t j = 0; j < w; ++j) a.push_back(kid(n.kids[0], i * w + j));
          cut(i, range_tree(n.flag, a, 0, w, true, r));
        }
        break;
      }
      case ENode::kMaterialize:
        for (size_t i = 0; i < L; ++i) cut(i, kid(n.kids[0], i));
        break;
      case ENode::kGather: {
        std::vector<TE> cat;
        for (size_t a : n.kids)
          for (size_t i = 0; i < t_.nodes.at(a).len; ++i) cat.push_back(kid(a, i));
        const auto &idx = p_.index_maps.at(n.idx);
        for (size_t i = 0; i < L; ++i) {
          if (idx.at(i) >= cat.size()) return *why = "a gather index past its parts", false;
          cut(i, cat[idx[i]]);
        }
        break;
      }
      case ENode::kApply: {
        const std::vector<TE> in = kid_wires(n.kids[0]);
        std::vector<TE> outs;
        if (n.eop.kind == EOp::kStaged) {
          const auto *spec = static_cast<const OpSpec<F> *>(n.eop.spec);
          const size_t m = spec == nullptr || spec->staged == nullptr ? 0 : spec->staged->n;
          if (m == 0 || in.size() % m != 0)
            return *why = "a staged transform's operand of another length", false;
          for (size_t at = 0; at < in.size(); at += m) {
            std::vector<TE> blk(in.begin() + long(at), in.begin() + long(at + m)), o;
            if (!staged_rows(n.eop, blk, r, &o, why)) return false;
            outs.insert(outs.end(), o.begin(), o.end());
          }
        } else if (!op_rows(n.eop, in, &outs, why)) {
          return false;
        }
        if (outs.size() != L) return *why = "an operator's output of another length", false;
        for (size_t i = 0; i < L; ++i) cut(i, std::move(outs[i]));
        break;
      }
      case ENode::kValue: {
        switch (n.pl.kind) {
          case Place::kBlock: {
            if (n.pl.b >= in_.size() || in_[n.pl.b].value != Id(n.u) ||
                in_[n.pl.b].n != L)
              return *why = "its block holds another value", false;
            for (size_t i = 0; i < L; ++i)
              cut(i, wire(Wire{f_.zero(), f_.one(), in_[n.pl.b].at + i}));
            break;
          }
          case Place::kLate: {
            if (n.pl.pub >= in_.size() || n.pl.pad >= in_.size() ||
                in_[n.pl.pad].value != Id(n.u) || in_[n.pl.pub].n != L ||
                in_[n.pl.pad].n != L)
              return *why = "its late blocks hold another value", false;
            for (size_t i = 0; i < L; ++i)
              cut(i, sum_te({wire(Wire{f_.zero(), f_.one(), in_[n.pl.pub].at + i}),
                             scale_te(mone(), wire(Wire{f_.zero(), f_.one(),
                                                        in_[n.pl.pad].at + i}))}));
            break;
          }
          case Place::kDefined:
            if (n.pl.x >= k || !t_.cut.at(n.pl.x) || t_.W[n.pl.x].size() != L)
              return *why = "its defining node is not a cut below it", false;
            for (size_t i = 0; i < L; ++i) cut(i, wire(W(n.pl.x, i)));
            break;
        }
        break;
      }
    }
    if (!r.ok || r.at != t_.aux[k].size())
      return *why = std::to_string(t_.aux[k].size()) + " aux wires, the rule reads " +
                    std::to_string(r.at) + (r.ok ? "" : " (too few)"),
             false;
    return true;
  }

  const F &f_;
  const GkrCertificate<F> &c_;
  const ir::Program &p_;
  const std::vector<ir::InputBlock> &in_;
  const EmitTable<F> &t_;
  const ir::Circuit *pc_ = nullptr;
  std::function<bool(size_t, Id)> eqb_;
  std::vector<uint32_t> pos_;
  std::unordered_set<uint32_t> asserted_;
  std::vector<Cut> cuts_;
  size_t ncuts_ = 0;
  // The one-level forms of the uncut nodes expanded so far.
  std::unordered_map<size_t, std::vector<TE>> uncut_;
  std::vector<EntryStats> entry_stats_;
  std::string expand_error_;
  std::vector<std::vector<CutBlock>> node_census_, family_census_;
  size_t cur_entry_ = 0;
};

// ------------------------------------------------- the binary certificate --

// The natural of decimal text S as little-endian bytes.
inline std::vector<uint8_t> dec_bytes(const std::string &s) {
  program_builder_internal::BigNat b;
  for (char ch : s) {
    if (ch < '0' || ch > '9') export_fail("a code that is no decimal natural: " + s);
    b.mul_add(10, uint64_t(ch - '0'));
  }
  std::vector<uint8_t> out;
  for (uint32_t limb : b.d)
    for (int i = 0; i < 4; ++i) out.push_back(uint8_t(limb >> (8 * i)));
  if (out.empty()) out.push_back(0);
  return out;
}
inline void dec_nat(ghc::Bytes &o, const std::string &s) {
  const auto b = dec_bytes(s);
  o.nat_le(b.data(), b.size());
}

// The encoders of the node table's Lean types (Data.lean's ENodeInfo and
// EntryCert's family record, by their derived encodings: ghc.h): the
// records of the table as the certificate's sections hold them.
template <class F>
class GhcNodes {
 public:
  using Wire = typename EmitWalk<F>::Wire;
  GhcNodes(const ir::Program &p, const F &f) : p_(p), f_(f) {}

  // A NamedOp (RealizedProgram.lean's constructor order).
  void named(ghc::Bytes &o, Id k) const {
    const ir::NamedOp &op = p_.ops.at(k);
    using NO = ir::NamedOp;
    o.nat(uint64_t(op.kind));
    auto form = [&]() {
      if (!op.ntt_form) {
        o.nat(0);
      } else {
        o.nat(op.natural_order ? 2 : 1);
        dec_nat(o, op.elt);
      }
    };
    switch (op.kind) {
      case NO::kNegacyclicConv:
        o.nat(op.value);
        form();
        break;
      case NO::kPolyMatVec:
        o.nat(op.value);
        o.nat(op.nats.at(0));
        o.nat(op.nats.at(1));
        form();
        break;
      case NO::kPolyBroadcast:
        o.nat(op.value);
        o.nat(op.nats.at(0));
        form();
        break;
      case NO::kNtt:
        o.nat(op.nats.at(0));
        dec_nat(o, op.elt);
        o.nat(op.natural_order ? 1 : 0);
        break;
      case NO::kInverseNtt:
      case NO::kNttTranspose:
        o.nat(op.nats.at(0));
        dec_nat(o, op.elt);
        break;
      case NO::kRowDot:
        o.nat(op.value);
        o.nat(op.nats.at(0));
        o.nat(op.nats.at(1));
        break;
      case NO::kMacConv:
        o.nat(op.value);
        o.nat(op.nats.at(0));
        o.nat(op.nats.at(1));
        o.nat(op.taps.size());
        for (size_t t : op.taps) o.nat(t);
        break;
      case NO::kAcyclicConv:
        o.nat(op.value);
        o.nat(op.nats.at(0));
        break;
      case NO::kDiagonal:
      case NO::kScale:
      case NO::kConstDiagonal:
        o.nat(op.value);
        break;
      case NO::kSum:
        o.nat(op.nats.at(0));
        break;
      case NO::kFromDigits:
        o.nat(op.nats.at(0));
        dec_nat(o, op.elt);
        break;
      case NO::kBatched:
        o.nat(op.nats.at(0));
        named(o, op.inner);
        break;
    }
  }
  void coef(ghc::Bytes &o, Id c) const {
    const ir::Coef &k = p_.coefs.at(c);
    if (k.is_const) {
      o.nat(0);
      dec_nat(o, k.c);
    } else {
      o.nat(1);
      o.nat(k.v);
      o.nat(k.i);
    }
  }
  void eop(ghc::Bytes &o, const EOp &e) const {
    o.nat(uint64_t(e.kind));
    switch (e.kind) {
      case EOp::kView:
        o.nat(e.idx);
        if (e.has_zero) {
          o.nat(1);
          o.nat(e.zero);
        } else {
          o.nat(0);
        }
        break;
      case EOp::kNamed:
        named(o, e.op);
        break;
      case EOp::kSparse: {
        const ir::LinearRows &rows = p_.linears.at(e.rows);
        o.nat(rows.size());
        for (const auto &row : rows) {
          o.nat(row.size());
          for (const auto &[c, k] : row) {
            o.nat(c);
            coef(o, k);
          }
        }
        break;
      }
      case EOp::kStaged:
        named(o, e.op);
        o.nat(e.mask);
        break;
    }
  }
  void node(ghc::Bytes &o, const ENode &n) const {
    o.nat(uint64_t(n.kind));
    auto k = [&](size_t i) { o.nat(n.kids.at(i)); };
    switch (n.kind) {
      case ENode::kLin:
        o.nat(n.terms.size());
        for (const auto &t : n.terms) {
          dec_nat(o, t.scale);
          o.nat(t.view);
          o.nat(t.ops.size());
          for (const auto &x : t.ops) eop(o, x);
        }
        o.nat(n.zero);
        break;
      case ENode::kConst:
        o.nat(n.v);
        break;
      case ENode::kBin:
        o.nat(n.op);
        k(0);
        k(1);
        break;
      case ENode::kScale:
        dec_nat(o, n.code);
        k(0);
        break;
      case ENode::kSum:
      case ENode::kProd:
        o.nat(n.w);
        k(0);
        break;
      case ENode::kBroadcast:
        o.nat(n.idx);
        k(0);
        break;
      case ENode::kNot:
        o.nat(n.v);
        k(0);
        break;
      case ENode::kMux:
        o.boolean(n.flag);
        k(0);
        k(1);
        k(2);
        break;
      case ENode::kCmp:
        o.nat(n.op);
        o.nat(n.w);
        k(0);
        if (n.flag) {
          o.nat(1);
          o.nat(n.v);
          o.nat(n.idx);
        } else {
          o.nat(0);
          k(1);
        }
        break;
      case ENode::kTree:
        o.boolean(n.flag);
        o.nat(n.w);
        k(0);
        break;
      case ENode::kMaterialize:
        k(0);
        break;
      case ENode::kGather:
        o.nat(n.idx);
        o.nat(n.kids.size());
        for (size_t a : n.kids) o.nat(a);
        break;
      case ENode::kApply:
        eop(o, n.eop);
        k(0);
        break;
      case ENode::kValue:
        o.nat(n.u);
        o.nat(uint64_t(n.pl.kind));
        switch (n.pl.kind) {
          case Place::kBlock:
            o.nat(n.pl.b);
            break;
          case Place::kLate:
            o.nat(n.pl.pub);
            o.nat(n.pl.pad);
            break;
          case Place::kDefined:
            o.nat(n.pl.x);
            break;
        }
        break;
    }
  }
  // A field element's code (to_bytes_field's little-endian natural).
  void code(ghc::Bytes &o, const typename F::Elt &x) const {
    std::vector<uint8_t> b(F::kBytes);
    f_.to_bytes_field(b.data(), x);
    o.nat_le(b);
  }
  void wire(ghc::Bytes &o, const Wire &w) const {
    code(o, w.c0);
    code(o, w.c1);
    o.nat(w.x);
  }
  void info(ghc::Bytes &o, const ENodeInfo &ni, bool cut,
            const std::vector<Wire> &W,
            const std::vector<Wire> &aux) const {
    node(o, ni.node);
    o.nat(ni.len);
    o.boolean(cut);
    if (ni.has_ref) {
      o.nat(1);
      o.nat(ni.ref);
    } else {
      o.nat(0);
    }
    o.nat(W.size());
    for (const auto &w : W) wire(o, w);
    o.nat(aux.size());
    for (const auto &w : aux) wire(o, w);
  }
  // An entry's family record (Lean `Option FamCert`): none, or
  // alignment block | logup alpha needles hists weights tree sum |
  // macH bits powers tag chunks, the wires 0 + 1 n of LOG's nodes.
  void fam(ghc::Bytes &o, const typename EmitTable<F>::Fam &g, const FamilyLog &lg) const {
    using Fam = typename EmitTable<F>::Fam;
    auto node = [&](size_t n) { wire(o, Wire{f_.zero(), f_.one(), n}); };
    auto nats = [&](const std::vector<size_t> &v) {
      o.nat(v.size());
      for (size_t x : v) o.nat(x);
    };
    switch (g.kind) {
      case Fam::kNone:
        o.nat(0);
        return;
      case Fam::kAlignment:
        o.nat(1);
        o.nat(0);
        o.nat(g.block);
        return;
      case Fam::kLogup:
        o.nat(1);
        o.nat(1);
        o.nat(g.alpha);
        nats(g.needles);
        nats(g.hists);
        o.nat(g.block);
        o.nat(lg.dens.size());
        for (size_t d : lg.dens) node(d);
        o.nat(lg.inner.size());
        for (const auto &x : lg.inner) {
          o.nat(x.l);
          o.nat(x.r);
          node(x.num);
          node(x.den);
        }
        node(lg.sum);
        return;
      case Fam::kMacH:
        o.nat(1);
        o.nat(2);
        o.nat(g.bits);
        o.nat(g.powers);
        o.nat(g.tag);
        o.nat(lg.chunks.size());
        for (size_t c : lg.chunks) node(c);
        return;
    }
  }

 private:
  const ir::Program &p_;
  const F &f_;
};

// The code arithmetic of field FD (Lean CodeArith), the module defining it,
// and whether the fast path's prime applies (the arithmetic is primeArith,
// or an extension tower over a prime-on base at any depth, A15: F_q^20 over
// F_q has p = 12289; binary fields have none).
struct FieldArith {
  std::string ar, mod;
  bool fast = true;
};
inline FieldArith field_arith(const ir::FieldDecl &fd) {
  static const std::map<std::string, FieldArith> named = {
      {"GF(2^128)",
       {"RealizedProgram.gf2_128Code.arith", "GordieHowe.Applications.FieldInterps.Basic",
        false}},
      {"GF(2^256)",
       {"RealizedProgram.gf2_256Code.arith", "GordieHowe.Applications.FieldInterps.GF256",
        false}},
      {"F_q^9",
       {"RealizedProgram.fq9Code.arith", "GordieHowe.Applications.FieldInterps.Basic", true}},
      {"F_q^20",
       {"RealizedProgram.fq20Code.arith", "GordieHowe.Applications.FieldInterps.Fq20",
        true}},
      {"F_q^6",
       {"RealizedProgram.fq6Code.arith", "GordieHowe.Applications.FieldInterps.Odd", true}},
      {"F_q^11",
       {"RealizedProgram.fq11Code.arith", "GordieHowe.Applications.FieldInterps.Odd", true}},
      {"Goldilocks^2",
       {"RealizedProgram.gold2Code.arith", "GordieHowe.Applications.FieldInterps.Odd", true}},
      {"Goldilocks^4",
       {"RealizedProgram.gold4Code.arith", "GordieHowe.Applications.FieldInterps.Odd", true}},
  };
  auto it = named.find(fd.name);
  if (it != named.end()) return it->second;
  if (fd.degree == 1)
    return {"GKR.Fold.primeArith " + fd.characteristic,
            "GordieHowe.ProofSystem.GKR.FieldCodes", true};
  export_fail("field " + fd.name + " has no code arithmetic");
}

// The check plan of a circuit's entries: the theorems Load.lean's
// check_entry proves per entry (its leaves) and the Lean modules they go in.
// It is the one planner; Lean reads an entry's parts from its module text.
//
// The parts of an entry, as triples: (0, 0, m) a run of m consecutive nodes;
// (1, S, m) one node's cuts in m slices of S (the last one every cut left);
// then (2, S, m) the family cuts in m slices of S. The leaves, in order: the
// entry's head, then per part its one theorem (tag 0) or its m slices. An
// entry whose leaves cost at most kModuleMs in all is one module; a larger
// one is split into at most ceil(cost / kModuleMs) part modules of
// contiguous leaves, balanced by cost, and its entry module only composes
// their theorems.
//
// Costs are predicted kernel milliseconds. The kernel shares nothing between
// declarations, so a leaf checking cuts [s, s + S) of an object (a cut
// node's cuts, nodeCutsE, or an entry's family cuts, famCuts) builds the
// object's whole cut list, drops s cuts and checks S:
//   kLeafMs + F + beta s + the cost of its S cuts.
// F, a node's expansion: for the node and each uncut node it expands (its
// uncut cone, once per reference), kOwnMs per coordinate, plus per
// coordinate of their kids kOwnMs, or kIndexMs when read through an index
// map (gather, broadcast, a lin term's view), or kOperatorMs when read
// through an operator (a lin term's named, sparse or staged operator, apply,
// prod, tree, cmp); plus kRampMs per coordinate read through an index map or
// an operator, times the share of the node's cuts that are not one wire
// (those cuts force the lookup tries of the coordinates they read). A
// family's F: kLogupBuildMs per cut of a LogUp family, kMacBuildMs per
// coordinate of a MAC H family's bits.
// beta: kDropPlaceMs for a value leaf, kDropMs for any other node, kFamDropMs
// for a family.
// A cut: kCutPlaceMs for a value leaf's, kCutMs for any other node's,
// kLogupCutMs for a LogUp family's, none for a MAC H family's; and when its
// tree expression is not one wire, kTermMs per wire or constant it reads and
// kScaleMs per scale by a constant other than 1 and -1. A cut whose tree
// expression is one wire (a placement, a coordinate taken from a cut kid) costs
// only its base, so a node's coordinates pay for its uncut cone only when their
// expressions pass through it.
//
// The constants, from the kernel-mode profile of 2026-11-07 (one
// declaration per Lean process, kernel type-checking time from
// `set_option profiler true`; the GKR circuits A and H of
// MDL/MLDSA44/Attrs1/ROMParams):
//   A node 57, a value leaf of 94,208 coordinates: cuts [0, 1) 6.5 s,
//     [93184, 93185) 20.1 s, whole 30.8 s (kOwnMs, kDropPlaceMs, kCutPlaceMs);
//   A node 58, a lin node of 4,096 cuts over node 57 through a named
//     operator, each cut a sum of 23 wires scaled by powers of 2: cuts
//     [0, 1) 59.2 s, [0, 64) 112 s, [0, 1024) 283 s (kOperatorMs; kRampMs, the
//     excess of the first 64 cuts over the steady 0.18 s per cut);
//   H node 2740, a gather of 117,760 coordinates over value leaves of
//     118,528: the slice of 113 cuts at s = 565 36.4 s, at s = 105,655 121 s,
//     whole 232 s (kIndexMs, kDropMs, kCutMs);
//   H entry 88's MAC H family, 920 cuts of 128 scaled bits each over 117,760
//     bits: 4 cuts 90 s, whole 1,180 s (kMacBuildMs; kScaleMs from its 1.2 s
//     and node 58's 0.18 s per cut, after kTermMs);
//   A entry 10's LogUp family of 107,000 cuts: slice 0 of 256 cuts 3.6 s, the
//     slice at s = 106,496 80.6 s (kLogupBuildMs, kFamDropMs, kTermMs from its
//     two-wire cuts);
//   leaves of one or two small nodes 0.4 s (kLeafMs);
//   A entry 10's LogUp family again, slices at s = 0 of 256, 1,024, 4,096
//     and 13,344 cuts: 3.4, 12.8, 55 and 215 s; the last 248 cuts, at
//     s = 106,752, 81 s (kLogupCutMs, from the largest slice);
//   MLDSA44/Ring/Carrier/ROMParams A node 280, an apply node of 1,024
//     coordinates and 8,192 cuts: cuts [0, 256), [0, 1024), [0, 4096) 16.7,
//     64.7 and 231 s; the same circuit's node 482, a gather of 8,192
//     cuts: cuts [0, 1) 6.8 s, [0, 1024) 108 s, [0, 4096) 278 s (both
//     priced 12 to 14 ms per cut, so kMaxSliceHard).
//
// The slices: an object whose whole check costs at most kLeafBudgetMs is
// not sliced (a node joins a run of consecutive nodes of at most that cost
// in all). A larger one is checked in m slices, m the least count whose
// leaves each cost at most the cap: kLeafBudgetMs, or, when the rebuild and
// the drop to the object's last cut alone cost more than three quarters of
// it, the larger of twice kLeafBudgetMs and that cost plus a quarter of
// kLeafBudgetMs. Every slice pays F and the drops add up, so the least such
// m also minimizes the total. The budget: node 58's slice of 1,024 cuts ran
// into the kernel's limit of 200,000 heartbeats at 275 s, so a quarter of
// the limit is about 69 s of such checking, and kLeafBudgetMs stays below
// it (layerSliceGates' rule in check_circuit). A node's slice also holds at
// most about kMaxSliceHard cuts whose tree expressions are not one wire: such
// cuts of the ring carrier's nodes 280 and 482 cost five to seven times their
// price, and 1,024 of them stay under the limit.
inline constexpr double kLeafMs = 300;
inline constexpr double kHeadMs = 2000;
inline constexpr double kLogupCutMs = 14;
inline constexpr size_t kMaxSliceHard = 1024;
inline constexpr double kOwnMs = 0.069;
inline constexpr double kIndexMs = 0.235;
inline constexpr double kOperatorMs = 0.625;
inline constexpr double kRampMs = 0.44;
inline constexpr double kDropPlaceMs = 0.145;
inline constexpr double kDropMs = 0.81;
inline constexpr double kCutPlaceMs = 0.26;
inline constexpr double kCutMs = 1.66;
inline constexpr double kTermMs = 1.2;
inline constexpr double kScaleMs = 8;
inline constexpr double kLogupBuildMs = 0.028;
inline constexpr double kMacBuildMs = 0.72;
inline constexpr double kFamDropMs = 0.73;
inline constexpr double kLeafBudgetMs = 60000;
inline constexpr double kModuleMs = 300000;

// A node of the table as the planner reads it: its length, whether it is
// cut, its aux wires, how it reads its kids (a value leaf reads none), its
// kids, and a cut node's cuts in check order (RelMirror::node_census; when
// empty, its coordinates and aux wires as one-wire cuts).
struct PlanNode {
  enum Read : uint8_t { kPlace, kOwn, kIndex, kOperator };
  size_t len = 0;
  bool cut = false;
  size_t aux = 0;
  Read read = kOwn;
  std::vector<size_t> kids;
  std::vector<CutBlock> cuts;
};

// An object of cut checks as the planner prices it: its rebuild F, its drop
// per cut beta, and per block of its cuts the count and cost (an uncut node
// has no cuts and costs nothing).
struct PlanObject {
  double F = 0, beta = 0;
  size_t hard = 0;
  std::vector<size_t> n;
  std::vector<double> cost;
  size_t cuts() const {
    size_t s = 0;
    for (size_t x : n) s += x;
    return s;
  }
  double total() const {
    double s = 0;
    for (double x : cost) s += x;
    return s;
  }
};

// The cost of each leaf checking OBJ in slices of S cuts (the last one every
// cut left), each block's cost spread evenly over its cuts.
inline std::vector<double> slice_costs(const PlanObject &o, size_t S) {
  const size_t N = o.cuts();
  const size_t m = std::max<size_t>(1, (N + S - 1) / S);
  std::vector<double> out;
  out.reserve(m);
  // the cost of cuts [0, i), for nondecreasing i
  size_t b = 0, start = 0;
  double done = 0;
  auto prefix = [&](size_t i) {
    while (b < o.n.size() && start + o.n[b] <= i) {
      done += o.cost[b];
      start += o.n[b];
      ++b;
    }
    if (b == o.n.size() || i == start) return done;
    return done + o.cost[b] * double(i - start) / double(o.n[b]);
  };
  double before = 0;
  for (size_t i = 0; i < m; ++i) {
    const size_t s = i * S, e = i + 1 == m ? N : std::min(N, s + S);
    const double after = prefix(e);
    out.push_back(kLeafMs + o.F + o.beta * double(s) + after - before);
    before = after;
  }
  return out;
}

// The slices of OBJ: their size S and count m (m = 1: one leaf of every cut)
// and their leaves' costs.
struct SlicePlan {
  size_t S = 1, m = 1;
  std::vector<double> leaves;
};
inline SlicePlan plan_slices(const PlanObject &o) {
  const size_t N = o.cuts();
  const double whole = kLeafMs + o.F + o.total();
  // a node's slice holds at most about kMaxSliceHard cuts that are not one
  // wire
  const size_t Smax =
      o.hard <= kMaxSliceHard ? N : std::max<size_t>(1, kMaxSliceHard * N / o.hard);
  if (N <= 1 || (whole <= kLeafBudgetMs && N <= Smax))
    return {std::max<size_t>(1, N), 1, {whole}};
  // The least possible leaf at the end: the rebuild, the drop to a block's
  // last cut and that cut.
  double last = 0;
  size_t at = 0;
  for (size_t b = 0; b < o.n.size(); ++b) {
    if (o.n[b] == 0) continue;
    at += o.n[b];
    last = std::max(last, kLeafMs + o.F + o.beta * double(at - 1) + o.cost[b] / double(o.n[b]));
  }
  const double cap = last <= 0.75 * kLeafBudgetMs
                         ? kLeafBudgetMs
                         : std::max(2 * kLeafBudgetMs, last + 0.25 * kLeafBudgetMs);
  auto fits = [&](size_t S) {
    for (double x : slice_costs(o, S))
      if (x > cap) return false;
    return true;
  };
  // The largest slice size that fits (a leaf grows with its slice, so by
  // bisection), then the least count of slices of at most that size,
  // balanced.
  size_t lo = 1, hi = Smax;
  while (lo < hi) {
    const size_t mid = lo + (hi - lo + 1) / 2;
    if (fits(mid)) lo = mid;
    else hi = mid - 1;
  }
  const size_t m = (N + lo - 1) / lo;
  size_t S = (N + m - 1) / m;
  if (!fits(S)) S = lo;
  SlicePlan p;
  p.S = S;
  p.leaves = slice_costs(o, S);
  p.m = p.leaves.size();
  return p;
}

// Per node of INFO (the table in order) its object: a cut node's expansion
// and cuts; an uncut node's none.
inline std::vector<PlanObject> plan_node_objects(const std::vector<PlanNode> &info) {
  // per node: the expansion of its uncut cone (itself included when uncut),
  // and the coordinates it reads through an index map or an operator
  constexpr double kMax = 1e18;
  std::vector<std::pair<double, double>> cone;
  std::vector<PlanObject> out;
  cone.reserve(info.size());
  out.reserve(info.size());
  for (const PlanNode &x : info) {
    double kid_len = 0, E = kOwnMs * double(x.len), R = 0;
    for (size_t k : x.kids) {
      if (k >= cone.size()) continue;
      kid_len += double(info[k].len);
      if (!info[k].cut) {
        E += cone[k].first;
        R += cone[k].second;
      }
    }
    switch (x.read) {
      case PlanNode::kPlace:
        break;
      case PlanNode::kOwn:
        E += kOwnMs * kid_len;
        break;
      case PlanNode::kIndex:
        E += kIndexMs * kid_len;
        R += kid_len;
        break;
      case PlanNode::kOperator:
        E += kOperatorMs * kid_len;
        R += kid_len;
        break;
    }
    E = std::min(E, kMax);
    R = std::min(R, kMax);
    PlanObject o;
    if (!x.cut) {
      cone.emplace_back(E, R);
      out.push_back(std::move(o));
      continue;
    }
    cone.emplace_back(0, 0);
    const bool place = x.read == PlanNode::kPlace;
    const double base = place ? kCutPlaceMs : kCutMs;
    o.beta = place ? kDropPlaceMs : kDropMs;
    size_t cuts = 0, free = 0;
    if (x.cuts.empty()) {
      for (size_t left = x.len + x.aux; left > 0;) {
        const size_t b = std::min(left, kCutBlock);
        o.n.push_back(b);
        o.cost.push_back(base * double(b));
        left -= b;
      }
      cuts = free = x.len + x.aux;
    } else {
      for (const CutBlock &b : x.cuts) {
        o.n.push_back(b.cuts);
        o.cost.push_back(base * double(b.cuts) + kTermMs * double(b.leaves) +
                         kScaleMs * double(b.scales));
        cuts += b.cuts;
        free += b.free;
      }
    }
    o.F = E + (cuts == 0 ? 0 : kRampMs * R * double(cuts - free) / double(cuts));
    o.hard = cuts - free;
    out.push_back(std::move(o));
  }
  return out;
}

// A family's object: rebuild F, its cuts' blocks CUTS (empty: COUNT cuts of
// DEFAULT_COST each), each cut BASE more.
inline PlanObject plan_family_object(double F, const std::vector<CutBlock> &cuts, size_t count,
                                     double default_cost, double base = 0) {
  PlanObject o;
  o.F = F;
  o.beta = kFamDropMs;
  if (cuts.empty()) {
    for (size_t left = count; left > 0;) {
      const size_t b = std::min(left, kCutBlock);
      o.n.push_back(b);
      o.cost.push_back((base + default_cost) * double(b));
      left -= b;
    }
  } else {
    for (const CutBlock &b : cuts) {
      o.n.push_back(b.cuts);
      o.cost.push_back(base * double(b.cuts) + kTermMs * double(b.leaves) +
                       kScaleMs * double(b.scales));
    }
  }
  return o;
}

// The part modules of leaves of costs LEAVES (total COST, in milliseconds)
// under the module budget: the leaf ranges [lo, hi) of
// ceil(COST / BUDGET) modules, a leaf in the module its cost's midpoint
// falls in; none when they fit one module.
inline std::vector<std::pair<size_t, size_t>> split_leaves(const std::vector<size_t> &leaves,
                                                           size_t cost, double budget) {
  std::vector<std::pair<size_t, size_t>> out;
  const size_t B = size_t(std::max(1.0, std::ceil(budget)));
  if (cost <= B) return out;
  const size_t G = (cost + B - 1) / B;
  size_t before = 0, g = SIZE_MAX;
  for (size_t i = 0; i < leaves.size(); ++i) {
    const size_t gi = std::min(G - 1, (2 * before + leaves[i]) * G / (2 * cost));
    if (gi != g) {
      out.emplace_back(i, i + 1);
      g = gi;
    } else {
      out.back().second = i + 1;
    }
    before += leaves[i];
  }
  if (out.size() == 1) out.clear();
  return out;
}

// An entry's plan: its parts (triples), its leaves' costs, their total, and
// its part modules (the leaf ranges [lo, hi); none when it is one module).
struct EntryPlan {
  std::vector<size_t> parts;
  std::vector<size_t> leaves;
  size_t cost = 0;
  std::vector<std::pair<size_t, size_t>> modules;
};

// The plan of an entry from its nodes' objects NODES (plan_node_objects
// over the table, the entry's block) and its family's object FAM.
inline EntryPlan plan_entry(const std::vector<PlanObject> &nodes, const PlanObject &fam,
                            double budget = kModuleMs) {
  EntryPlan e;
  auto ms = [](double x) { return size_t(std::max(1.0, std::ceil(x))); };
  e.leaves.push_back(ms(kHeadMs));
  size_t cur = 0;
  double cost = 0;
  auto flush = [&]() {
    if (cur == 0) return;
    e.parts.insert(e.parts.end(), {0, 0, cur});
    e.leaves.push_back(ms(kLeafMs + cost));
    cur = 0;
    cost = 0;
  };
  for (const PlanObject &o : nodes) {
    const SlicePlan sp = plan_slices(o);
    if (sp.m > 1) {
      flush();
      e.parts.insert(e.parts.end(), {1, sp.S, sp.m});
      for (double x : sp.leaves) e.leaves.push_back(ms(x));
      continue;
    }
    const double x = o.F + o.total();
    if (cur > 0 && kLeafMs + cost + x > kLeafBudgetMs) flush();
    ++cur;
    cost += x;
  }
  flush();
  const SlicePlan fp = plan_slices(fam);
  e.parts.insert(e.parts.end(), {2, fp.S, fp.m});
  for (double x : fp.leaves) e.leaves.push_back(ms(x));
  for (size_t x : e.leaves) e.cost += x;
  e.modules = split_leaves(e.leaves, e.cost, budget);
  return e;
}

// How node ND reads its kids (PlanNode::Read).
inline PlanNode::Read plan_read(const ENode &nd) {
  switch (nd.kind) {
    case ENode::kValue:
    case ENode::kConst:
      return PlanNode::kPlace;
    case ENode::kGather:
    case ENode::kBroadcast:
      return PlanNode::kIndex;
    case ENode::kApply:
    case ENode::kProd:
    case ENode::kTree:
    case ENode::kCmp:
      return PlanNode::kOperator;
    case ENode::kLin: {
      PlanNode::Read r = PlanNode::kOwn;
      for (const ETerm &tm : nd.terms)
        for (const EOp &o : tm.ops) {
          if (o.kind != EOp::kView) return PlanNode::kOperator;
          r = PlanNode::kIndex;
        }
      return r;
    }
    default:
      return PlanNode::kOwn;
  }
}

// The plan of every entry of table T: its nodes in block order (Lean's kids
// of a node: a lin node's term views, any other node's kids), each block's
// nodes' objects and its family's (a LogUp's cuts, its leaves, two per
// inner node and its sum; a MAC H's chunks; none otherwise). NODE_CUTS and
// FAM_CUTS are the relational mirror's census of the cuts (RelMirror::
// node_census, family_census); without them every cut is priced as one
// wire.
template <class F>
std::vector<EntryPlan> plan_entries(const EmitTable<F> &t,
                                    const std::vector<std::vector<CutBlock>> &node_cuts = {},
                                    const std::vector<std::vector<CutBlock>> &fam_cuts = {},
                                    double budget = kModuleMs) {
  using Fam = typename EmitTable<F>::Fam;
  std::vector<PlanNode> info;
  for (const auto &b : t.blocks) {
    for (size_t n = b.lo; n < b.hi; ++n) {
      const ENode &nd = t.nodes[n].node;
      PlanNode x;
      x.len = t.nodes[n].len;
      x.cut = t.cut[n] != 0;
      x.aux = t.aux[n].size();
      x.read = plan_read(nd);
      if (nd.kind == ENode::kLin) {
        for (const ETerm &tm : nd.terms) x.kids.push_back(tm.view);
      } else if (nd.kind != ENode::kConst && nd.kind != ENode::kValue) {
        x.kids = nd.kids;
      }
      if (x.cut && n < node_cuts.size()) x.cuts = node_cuts[n];
      info.push_back(std::move(x));
    }
  }
  const std::vector<PlanObject> objs = plan_node_objects(info);
  std::vector<EntryPlan> out;
  size_t pos = 0;
  for (size_t k = 0; k < t.blocks.size(); ++k) {
    const auto &b = t.blocks[k];
    const size_t len = b.hi - b.lo;
    const std::vector<PlanObject> c(objs.begin() + pos, objs.begin() + pos + len);
    pos += len;
    static const std::vector<CutBlock> none;
    const std::vector<CutBlock> &fc = k < fam_cuts.size() ? fam_cuts[k] : none;
    switch (b.fam.kind) {
      case Fam::kLogup: {
        const size_t n = b.log.dens.size() + 2 * b.log.inner.size() + 1;
        out.push_back(plan_entry(
            c, plan_family_object(kLogupBuildMs * double(n), fc, n, 2 * kTermMs, kLogupCutMs),
            budget));
        break;
      }
      case Fam::kMacH: {
        const size_t n = b.log.chunks.size();
        const size_t bits = b.fam.bits < t.nodes.size() ? t.nodes[b.fam.bits].len : 0;
        const double w = n == 0 ? 0 : double(bits) / double(n);
        out.push_back(plan_entry(c,
                                 plan_family_object(kMacBuildMs * double(bits), fc, n,
                                                    kTermMs * w + kScaleMs * w),
                                 budget));
        break;
      }
      default:
        out.push_back(plan_entry(c, plan_family_object(0, {}, 0, 0), budget));
        break;
    }
  }
  return out;
}

// The header's leaf theorems (Load.lean's runCheckCircuit, in its order) and
// their predicted costs, measured in kernel mode on the MDL circuits: per
// header part 0, 3, 4, 5, 7, 8 one leaf (part 3, the node table's check,
// kTableNodeMs per node); per layer of at most kLayerSliceGates gates its
// check and its counts; per larger layer the previous layer's length
// (kLenGateMs per gate of it), then per slice of kLayerSliceGates its check
// (kGateMs per gate), its counts (kInfoGateMs per gate) and, but for the last
// slice, the equation of the next slice's tail; the last suffix and the shape;
// the asserted nodes in slices of kAssertSliceNodes (their witnesses), then
// the same slices' assertion terms (kAssertMs per node); part 6's merge-join
// (kCoverMs per asserted node); and four small checks.
inline constexpr size_t kLayerSliceGates = 2048;
inline constexpr size_t kAssertSliceNodes = 512;
inline constexpr double kTableNodeMs = 6.0;
inline constexpr double kGateMs = 4.0;
inline constexpr double kInfoGateMs = 0.6;
inline constexpr double kLenGateMs = 0.042;
inline constexpr double kAssertMs = 2.5;
inline constexpr double kCoverMs = 0.4;

// A circuit's header plan: its leaves' costs, their total, and its part
// modules (the leaf ranges [lo, hi); none when it is one module).
struct HeaderPlan {
  std::vector<size_t> leaves;
  size_t cost = 0;
  std::vector<std::pair<size_t, size_t>> modules;
};

// The header plan of a circuit of layers of LAYER_GATES gates, ASSERTS
// asserted nodes and TABLE_NODES table nodes.
inline HeaderPlan plan_header(const std::vector<size_t> &layer_gates, size_t asserts,
                              size_t table_nodes, double budget = kModuleMs) {
  HeaderPlan h;
  auto add = [&](double x) { h.leaves.push_back(size_t(std::max(1.0, std::ceil(kLeafMs + x)))); };
  // parts 0, 3, 4, 5, 7, 8
  add(0);
  add(kTableNodeMs * double(table_nodes));
  for (int i = 0; i < 4; ++i) add(0);
  for (size_t i = 0; i < layer_gates.size(); ++i) {
    const size_t g = layer_gates[i];
    const size_t S = kLayerSliceGates;
    const size_t m = std::max<size_t>(1, (g + S - 1) / S);
    if (m == 1) {
      add(kGateMs * double(g) + kLenGateMs * double(i == 0 ? 0 : layer_gates[i - 1]));
      add(kInfoGateMs * double(g));
      continue;
    }
    if (i > 0) add(kLenGateMs * double(layer_gates[i - 1]));
    for (size_t j = 0; j < m; ++j) {
      const size_t n = j + 1 == m ? g - j * S : S;
      add(kGateMs * double(n));
      add(kInfoGateMs * double(n));
      if (j + 1 < m) add(0);
    }
  }
  // the last suffix, the shape
  add(0);
  add(0);
  const size_t A = kAssertSliceNodes;
  const size_t ma = std::max<size_t>(1, (asserts + A - 1) / A);
  for (int pass = 0; pass < 2; ++pass)
    for (size_t j = 0; j < ma; ++j) add(kAssertMs * double(j + 1 == ma ? asserts - j * A : A));
  // part 6's merge-join (or part 6), chk_one, chk_inputs, chk_count, chk_cover
  add(kCoverMs * double(asserts));
  for (int i = 0; i < 4; ++i) add(0);
  for (size_t x : h.leaves) h.cost += x;
  h.modules = split_leaves(h.leaves, h.cost, budget);
  return h;
}

// An entry's parts as Lean list text, "[a, b, …]".
inline std::string plan_text(const std::vector<size_t> &parts) {
  std::string s = "[";
  for (size_t i = 0; i < parts.size(); ++i) s += (i ? ", " : "") + std::to_string(parts[i]);
  return s + "]";
}

}  // namespace emit_export_internal

// The export of one emitted circuit: its certificate file, its Lean
// modules (path relative to the plan's directory, text), and counts for the
// report.
struct EmitExport {
  std::string domain;
  std::vector<uint8_t> ghc;
  // The certificate's data as written (ghc_gkr.h).
  ghc::GkrCore core;
  ghc::GkrTable table;
  std::vector<std::pair<std::string, std::string>> modules;
  // Mode-specific proofs, relative to the export root (Check/<mode>/GordieHoweCheck/...).
  std::vector<std::pair<std::string, std::string>> check_modules;
  size_t nodes = 0, wires = 0, aux = 0, entries = 0, cuts = 0;
};

// How emit_tables treats the tables (tests): MUTATE changes each table (an
// emit_export_internal::EmitTable<F> of the domain named, F its field)
// before the mirrors read it; without MIRROR the mirrors are skipped (a test
// of the Lean check's rejection); with ERRORS the mirrors' findings are
// collected (domain: why) instead of failing the export.
struct EmitOptions {
  std::function<void(void *table, const std::string &domain)> mutate;
  bool mirror = true;
  std::vector<std::string> *errors = nullptr;
};

// The GKR export of every domain of CS whose circuit was emitted here, each
// table checked against the program and the DAG first.
template <class S>
std::vector<EmitExport> emit_tables(const BasicCompiledSystem<S> &cs,
                                    const ExportMeta &meta,
                                    const EmitOptions &opt = {}) {
  using namespace emit_export_internal;
  program_builder_internal::ProgramBuilder<S> pb(cs);
  pb.report_mod0();
  const ir::Program p = pb.run();
  std::vector<EmitExport> out;
  for (size_t di = 0; di < cs.num_domains(); ++di) {
    const auto &cd = cs.compiled_domain(di);
    const void *walk = cd.gkr_emit_walk();
    const void *cert = cd.gkr_cert_data();
    if (walk == nullptr || cert == nullptr) continue;
    const DomainBase<S> &dm = cs.domain(di);
    S::dispatch(dm.field_id, [&](auto tag) {
      using F = typename decltype(tag)::type;
      using PBF = program_builder_internal::ProgramBuilder<S>;
      const auto *dp = dynamic_cast<const Domain<F> *>(&dm);
      if (dp == nullptr) export_fail("domain " + dm.name + " is untyped");
      const Domain<F> &d = *dp;
      const auto &Wk = *static_cast<const EmitWalk<F> *>(walk);
      const auto &C = *static_cast<const GkrCertificate<F> *>(cert);
      const F &f = d.field();
      const size_t circ = emitted_circuit(p, di);
      const ir::Circuit &pc = p.circuits.at(circ);
      EmitTable<F> t;
      try {
        t = TableBuilder<S, F>(pb, p, circ, d, cs.nodes(), Wk).build();
      } catch (const std::runtime_error &e) {
        std::fprintf(stderr,
                     "GH_EMIT_TABLE_UNSUPPORTED config=%s-%s domain=%s why=%s\n",
                     meta.config.c_str(), meta.profile.c_str(), d.name.c_str(),
                     e.what());
        return;
      }
      if (t.blocks.size() != pc.entries.size())
        export_fail("domain " + d.name + ": " + std::to_string(t.blocks.size()) +
                    " entry blocks for " + std::to_string(pc.entries.size()) +
                    " printed entries");
      {
        size_t at = 0;
        for (const auto &b : t.blocks) {
          if (b.lo != at || b.hi < b.lo)
            export_fail("domain " + d.name + ": the entry blocks do not partition "
                        "the table");
          at = b.hi;
        }
        if (at != t.nodes.size())
          export_fail("domain " + d.name + ": nodes past the last entry block");
      }
      // The emitter's wires per coordinate before the cuts drop the uncut
      // nodes' (the report's comparison).
      size_t emitted = 0, cutn = 0;
      for (const auto &w : t.W) emitted += w.size();
      family_records<F>(t, p, pc);
      mark_cuts<F>(t, p);
      for (const uint8_t c : t.cut) cutn += c;
      const std::string two = PBF::code_of(f, f.addf(f.one(), f.one()));
      if (opt.mutate) opt.mutate(&t, d.name);
      // The assertion pairs.
      RelMirror<F> rel(f, C, p, pc.inputs, t);
      std::vector<std::vector<std::pair<size_t, size_t>>> zu(t.blocks.size());
      std::string why;
      for (size_t k = 0; k < t.blocks.size() && why.empty(); ++k) {
        const auto &b = t.blocks[k];
        for (size_t i = 0; i < b.Z.size(); ++i) {
          size_t Z = 0, U = 0;
          std::string w;
          if (!rel.pair(b.Z[i], &Z, &U, &w)) {
            why = "entry " + std::to_string(k) + ": " + w;
            break;
          }
          zu[k].push_back({Z, U});
        }
        if (why.empty() && b.has_root && b.Z.size() != t.nodes.at(b.root).len)
          why = "entry " + std::to_string(k) + ": " + std::to_string(b.Z.size()) +
                " assertions for a root of " + std::to_string(t.nodes.at(b.root).len);
      }
      if (opt.mirror && why.empty()) {
        Mirror mir(p, t.nodes, F::kCharacteristicTwo, two);
        why = mir.table_errors();
        // A placed predicate's root prints as its side (an asserted truth's
        // step reads it); integer equalities keep their own shapes, as
        // does an integer equality's realized predicate (its
        // sides those of the root lhs + (-1) rhs, the conv read as its
        // committed C; Lean's entryMeaningB takes X = l - r).
        for (size_t k = 0; k < t.blocks.size() && why.empty(); ++k) {
          const ir::CircuitEntry &ce = pc.entries[k];
          if (ce.kind != ir::CircuitEntry::kPred) continue;
          const auto &b = t.blocks[k];
          const ir::Predicate &pd = p.predicates.at(ce.id);
          bool skip = false;
          for (const auto &eq : cs.records().mod_equalities)
            skip = skip || (eq.integer && eq.domain == d.name &&
                            (eq.name == pd.name || eq.name + ".realized" == pd.name));
          if (skip || !b.has_root) continue;
          const ENodeInfo &r = t.nodes[b.root];
          const size_t x = r.step ? r.node.kids[0] : b.root;
          if (!mir.eq_print(x, pd.lhs))
            why = "entry " + std::to_string(k) + " (predicate '" + pd.name +
                  "'): its root does not print as its side";
        }
        rel.set_circuit(pc, [&mir](size_t k, Id e) { return mir.eq_print(k, e); });
        for (size_t k = 0; k < t.blocks.size() && why.empty(); ++k)
          why = rel.entry_errors(k, t.blocks[k], zu[k]);
        // The header: the circuit has no outputs of its own (its last layer
        // carries assertions only).
        if (why.empty() && !C.outputs.empty())
          why = std::to_string(C.outputs.size()) + " circuit outputs";
        // Every asserted node of the DAG is some entry's Z (assertsCoveredB).
        if (why.empty()) {
          std::set<size_t> zs;
          for (const auto &v : zu)
            for (const auto &[Z, U] : v)
              if (Z != 0) zs.insert(Z);
          for (uint32_t z : C.asserted())
            if (!zs.count(z)) {
              why = "asserted node " + std::to_string(z) + " is no entry's assertion";
              break;
            }
        }
      }
      if (!why.empty()) {
        if (opt.errors != nullptr) {
          opt.errors->push_back(d.name + ": " + why);
          return;
        }
        export_fail("the GKR export of domain " + d.name + " fails its check: " + why);
      }
      // The certificate: the DAG, constants and schedule (gkr_core), the
      // node table and the entries' blocks, as the sections of `cert`.
      const ir::FieldDecl &fd = p.fields.at(p.domains.at(di).field);
      const FieldArith ar = field_arith(fd);
      const bool fast = ar.fast && !F::kCharacteristicTwo;
      GhcNodes<F> gn(p, f);
      ghc::GkrCore core;
      ghc::gkr_core(core, C, f);
      core.c = circ;
      core.chr = dec_bytes(fd.characteristic);
      if (fast) core.prime = core.chr;
      core.char2 = F::kCharacteristicTwo;
      {
        std::vector<uint8_t> b(F::kBytes);
        f.to_bytes_field(b.data(), f.mone());
        core.neg1 = b;
        if constexpr (!F::kCharacteristicTwo) {
          f.to_bytes_field(b.data(), f.invertf(f.addf(f.one(), f.one())));
          core.half = b;
        }
      }
      ghc::GkrTable gt;
      gt.size = t.nodes.size();
      size_t nwires = 0, naux = 0;
      for (size_t k = 0; k < t.blocks.size(); ++k) {
        const auto &b = t.blocks[k];
        ghc::Bytes e;
        e.nat(k);
        e.nat(b.lo);
        e.nat(b.hi);
        if (b.has_root) {
          e.nat(1);
          e.nat(b.root);
        } else {
          e.nat(0);
        }
        e.nat(zu[k].size());
        for (const auto &[Z, U] : zu[k]) {
          e.nat(Z);
          e.nat(U);
        }
        gn.fam(e, b.fam, b.log);
        gt.entries.push_back(std::move(e));
        for (size_t n = b.lo; n < b.hi; ++n) {
          if (n != gt.nodes.size()) export_fail("the entries' blocks are not in node order");
          ghc::Bytes ni;
          gn.info(ni, t.nodes[n], t.cut[n] != 0, t.W[n], t.aux[n]);
          gt.nodes.push_back(std::move(ni));
          nwires += t.W[n].size();
          naux += t.aux[n].size();
        }
      }
      if (gt.nodes.size() != gt.size) export_fail("the entries' blocks do not cover the node table");
      ghc::File file(ghc::gkr_schema());
      ghc::write_gkr(file, "cert", core, gt);
      std::vector<uint8_t> bytes = file.bytes();
      // The Lean modules.
      char hash[17];
      std::snprintf(hash, sizeof(hash), "%016llx",
                    static_cast<unsigned long long>(ghc::fnv1a(bytes)));
      const std::string mod = lean_module_name(meta, "GKR." + d.name);
      const std::string prog = lean_module_name(meta, "Program");
      const std::string ns = lean_namespace(meta, "GKR." + d.name);
      const std::string prog_ns = lean_namespace(meta, "Program");
      const std::string head = std::string(kLeanLicenseHeader) + "module\n\n";
      std::string arith = "(" + ar.ar + ")";
      if (fast) arith += ".withPrime " + fd.characteristic;
      EmitExport ex;
      ex.domain = d.name;
      {
        std::string o = head;
        o += "public import GordieHowe.Language.Realizations.Circuit.RelEntry\n";
        o += "public import " + prog + "\n";
        o += "public import GordieHowe.Applications.FieldInterps.Basic\n";
        if (ar.mod != "GordieHowe.Applications.FieldInterps.Basic")
          o += "public import " + ar.mod + "\n";
        o += "\n@[expose] public section\n\n";
        o += "/-!\n# GordieHowe GKR certificate: " + meta.config + "-" + meta.profile +
             ", circuit of domain " + d.name + "\n\n";
        o += "Generated by `lib/gordiehowe/compiler/emit_export.h` from the compiled "
             "system; do not edit. Untrusted hint data, loaded from `" + d.name +
             ".ghc`: the scheduling DAG, the node table with its wires, and per "
             "circuit entry its block, assertion pairs and family record.\n\n";
        o += "- C++ commit: `" + meta.cpp_commit + "`\n";
        o += "- bench run: `" + meta.run_id + "`\n-/\n\n";
        o += "namespace " + ns + "\n\n";
        o += "open GordieHowe GordieHowe.RealizedProgram GordieHowe.GKR.Certificate "
             "GordieHowe.GKR.Fold GordieHowe.GKR.Rel\n";
        o += "open " + prog_ns + "\n\n";
        o += "/-- The code arithmetic of the circuit's field. -/\n";
        o += "def ar : CodeArith := " + arith + "\n\n";
        o += "load_ghc \"" + d.name + ".ghc\" \"" + hash + "\"\n\n";
        o += "end " + ns + "\n";
        ex.modules.emplace_back("GKR/" + d.name + ".lean", std::move(o));
      }
      // The entries' modules, by the check plan: an entry over the module
      // budget has part modules E<k>/P<j>, each proving a range of its leaf
      // theorems, and its module E<k> composes them.
      const std::vector<EntryPlan> plans =
          plan_entries(t, rel.node_census(), rel.family_census());
      const std::string check_mod = "GordieHoweCheck." + lean_name(meta) + ".GKR." + d.name;
      std::string circuit = head;
      std::string planlog, modlog;
      const bool log_modules = std::getenv("GH_EMIT_PLAN_MODULES") != nullptr;
      const bool log_leaves = std::getenv("GH_EMIT_PLAN_LEAVES") != nullptr;
      // Per module: its name below the circuit's check module, its leaves'
      // predicted cost and its largest leaf's, in milliseconds.
      auto log_module = [&](const std::string &path, const EntryPlan &pl, size_t lo, size_t hi) {
        if (!log_modules) return;
        size_t sum = 0, top = 0;
        for (size_t i = lo; i < hi; ++i) {
          sum += pl.leaves[i];
          top = std::max(top, pl.leaves[i]);
        }
        modlog += (modlog.empty() ? "" : " ") + path + ":" + std::to_string(sum) + ":" +
                  std::to_string(top);
      };
      for (size_t k = 0; k < t.blocks.size(); ++k) {
        const EntryPlan &pl = plans[k];
        const std::string ks = std::to_string(k);
        const std::string ps = plan_text(pl.parts);
        // A module whose command checks leaves (check_entry, check_entry_leaves)
        // also imports the circuit's data module as `meta`: native mode's check
        // compiles the checker and the data in the module's own environment
        // (LoadNative.lean). It evaluates the sealed program, so it imports the
        // program module with `import all`. A compose_entry module checks nothing.
        auto module = [&](const std::string &what, const std::string &how,
                          const std::string &imports, const std::string &cmd) {
          std::string o = head;
          o += "public import " + mod + "\n";
          o += imports;
          if (cmd.rfind("compose_entry", 0) != 0) {
            o += "meta import " + mod + "\n";
            o += "import all " + prog + "\n";
          }
          o += "\n";
          o += "@[expose] public section\n\n";
          o += "/-! The relational check of " + what + " of the GKR circuit of domain " +
               d.name + how + " (generated; do not edit). -/\n\n";
          o += "namespace " + ns + "\n\n";
          o += cmd + "\n\n";
          o += "end " + ns + "\n";
          return o;
        };
        if (pl.modules.empty()) {
          log_module("E" + ks, pl, 0, pl.leaves.size());
          ex.modules.emplace_back(
              "GKR/" + d.name + "/E" + ks + ".lean",
              module("entry " + ks, "", "", "check_entry cert ar " + ks + " " + ps));
        } else {
          std::string imports;
          for (size_t j = 0; j < pl.modules.size(); ++j) {
            const std::string js = std::to_string(j);
            const auto [lo, hi] = pl.modules[j];
            log_module("E" + ks + ".P" + js, pl, lo, hi);
            ex.modules.emplace_back(
                "GKR/" + d.name + "/E" + ks + "/P" + js + ".lean",
                module("leaves " + std::to_string(lo) + " to " + std::to_string(hi - 1) +
                           " of entry " + ks,
                       "", "", "check_entry_leaves cert ar " + ks + " " + ps + " " +
                               std::to_string(lo) + " " + std::to_string(hi)));
            imports += "public import " + mod + ".E" + ks + ".P" + js + "\n";
          }
          ex.modules.emplace_back(
              "GKR/" + d.name + "/E" + ks + ".lean",
              module("entry " + ks, ", composed from its part modules", imports,
                     "compose_entry cert ar " + ks + " " + ps));
        }
        circuit += "public import " + mod + ".E" + ks + "\n";
        // With GH_EMIT_PLAN_LEAVES set: per entry its leaves' predicted costs
        // in milliseconds, in order.
        if (log_leaves) {
          std::string ls;
          for (size_t i = 0; i < pl.leaves.size(); ++i)
            ls += (i ? "," : "") + std::to_string(pl.leaves[i]);
          std::fprintf(stderr, "GH_EMIT_PLAN_LEAVES %s E%s %s\n", check_mod.c_str(), ks.c_str(),
                       ls.c_str());
        }
        planlog += (k ? " " : "") + ks + ":" + std::to_string(pl.cost) + ":" +
                   std::to_string(pl.leaves.size()) + ":" +
                   std::to_string(std::max<size_t>(1, pl.modules.size()));
      }
      // Per entry: index, plan cost, leaf theorems, modules.
      std::fprintf(stderr, "GH_EMIT_PLAN config=%s-%s domain=%s %s\n", meta.config.c_str(),
                   meta.profile.c_str(), d.name.c_str(), planlog.c_str());
      // With GH_EMIT_PLAN_MODULES set: the circuit's check module, then per
      // entry module its name, predicted cost and largest leaf
      // (formal/scripts/stage0.py reads them).
      if (log_modules)
        std::fprintf(stderr, "GH_EMIT_PLAN_MODULES %s %s\n", check_mod.c_str(),
                     modlog.c_str());
      // The header's check reads only the circuit's data, so its modules
      // import no entry and build beside them: its leaf theorems in part
      // modules Header/P<j> by the header plan (one module Header when they
      // fit), composed in Header. Each module checking leaves imports the
      // data module as `meta` too, and the sealed program with `import all`,
      // which the leaves evaluate.
      std::vector<size_t> layer_gates;
      for (const auto &l : core.layers) layer_gates.push_back(l.size());
      const HeaderPlan hp = plan_header(layer_gates, core.asserts.size(), t.nodes.size());
      auto hmodule = [&](const std::string &what, const std::string &imports,
                         const std::string &cmd) {
        std::string o = head;
        o += "public import " + mod + "\n";
        o += imports;
        o += "meta import " + mod + "\n";
        o += "import all " + prog + "\n\n";
        o += "@[expose] public section\n\n";
        o += "/-! The relational check of " + what + " of the GKR circuit of domain " + d.name +
             " (generated; do not edit). -/\n\n";
        o += "namespace " + ns + "\n\n" + cmd + "\n\nend " + ns + "\n";
        return o;
      };
      const std::string nleaves = std::to_string(hp.leaves.size());
      std::string hlog;
      if (hp.modules.empty()) {
        ex.modules.emplace_back(
            "GKR/" + d.name + "/Header.lean",
            hmodule("the header", "",
                    "check_header_leaves cert ar 0 " + nleaves + "\n\ncompose_header cert ar"));
        hlog = "Header:" + std::to_string(hp.cost) + ":" +
               std::to_string(*std::max_element(hp.leaves.begin(), hp.leaves.end()));
      } else {
        std::string imports;
        for (size_t j = 0; j < hp.modules.size(); ++j) {
          const std::string js = std::to_string(j);
          const auto [lo, hi] = hp.modules[j];
          ex.modules.emplace_back(
              "GKR/" + d.name + "/Header/P" + js + ".lean",
              hmodule("the header's leaves " + std::to_string(lo) + " to " +
                          std::to_string(hi - 1),
                      "", "check_header_leaves cert ar " + std::to_string(lo) + " " +
                              std::to_string(hi)));
          imports += "public import " + mod + ".Header.P" + js + "\n";
          size_t sum = 0, top = 0;
          for (size_t i = lo; i < hi; ++i) {
            sum += hp.leaves[i];
            top = std::max(top, hp.leaves[i]);
          }
          hlog += (hlog.empty() ? "" : " ") + std::string("Header.P") + js + ":" +
                  std::to_string(sum) + ":" + std::to_string(top);
        }
        ex.modules.emplace_back("GKR/" + d.name + "/Header.lean",
                                hmodule("the header", imports, "compose_header cert ar"));
      }
      if (log_modules)
        std::fprintf(stderr, "GH_EMIT_PLAN_MODULES %s %s\n", check_mod.c_str(), hlog.c_str());
      // The circuit's theorem from the header's and the entries', checking
      // nothing.
      circuit += "public import " + mod + ".Header\n";
      circuit += "meta import " + mod + "\n";
      circuit += "import all " + prog + "\n\n";
      circuit += "@[expose] public section\n\n";
      circuit += "/-! The relational check of the GKR circuit of domain " + d.name +
                 ", from its header's and entries' (generated; do not edit). -/\n\n";
      circuit += "namespace " + ns + "\n\ncompose_circuit cert ar\n\nend " + ns + "\n";
      ex.modules.emplace_back("GKR/" + d.name + "/Circuit.lean", std::move(circuit));
      // Data is mode independent. The kernel retains its bounded proof modules;
      // Native checks the complete GKR part once inside programOkB.
      std::string check_path = check_mod;
      std::replace(check_path.begin(), check_path.end(), '.', '/');
      for (size_t i = 1; i < ex.modules.size(); ++i) {
        const auto &[path, source] = ex.modules[i];
        std::string text = source;
        const std::string old_import = "public import " + mod + ".";
        const std::string new_import = "public import " + check_mod + ".";
        size_t at = 0;
        while ((at = text.find(old_import, at)) != std::string::npos) {
          text.replace(at, old_import.size(), new_import);
          at += new_import.size();
        }
        const std::string suffix = path.substr(("GKR/" + d.name).size());
        ex.check_modules.emplace_back("Check/Kernel/" + check_path + suffix, std::move(text));
      }
      ex.modules.resize(1);
      ex.ghc = std::move(bytes);
      ex.core = std::move(core);
      ex.table = std::move(gt);
      ex.nodes = t.nodes.size();
      ex.wires = nwires;
      ex.aux = naux;
      ex.entries = t.blocks.size();
      ex.cuts = rel.cuts_checked();
      {
        // Per entry: index, root (- for none), cut nodes, checked cuts, DAG
        // terms read, largest difference polynomial.
        std::string per;
        const auto &es = rel.entry_stats();
        for (size_t k = 0; k < t.blocks.size(); ++k) {
          const auto st = k < es.size() ? es[k] : typename RelMirror<F>::EntryStats{};
          per += (k ? " " : "") + std::to_string(k) + ":" +
                 (t.blocks[k].has_root ? std::to_string(t.blocks[k].root) : "-") + ":" +
                 std::to_string(st.nodes) + ":" + std::to_string(st.items) + ":" +
                 std::to_string(st.touched) + ":" + std::to_string(st.max_d);
        }
        std::fprintf(stderr, "GH_EMIT_ENTRIES config=%s-%s domain=%s %s\n",
                     meta.config.c_str(), meta.profile.c_str(), d.name.c_str(),
                     per.c_str());
      }
      std::fprintf(stderr,
                   "GH_EMIT_TABLE config=%s-%s domain=%s nodes=%zu cut_nodes=%zu "
                   "emitted_wires=%zu wires=%zu aux=%zu entries=%zu cuts=%zu "
                   "ghc_bytes=%zu\n",
                   meta.config.c_str(), meta.profile.c_str(), d.name.c_str(), ex.nodes,
                   cutn, emitted, ex.wires, ex.aux, ex.entries, ex.cuts, ex.ghc.size());
      out.push_back(std::move(ex));
    });
  }
  return out;
}

}  // namespace proofs::gordiehowe::compiler

#endif  // PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_COMPILER_EMIT_EXPORT_H_
