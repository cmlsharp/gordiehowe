// Copyright 2026 Chad Sharp and Paul Grubbs
// SPDX-License-Identifier: Apache-2.0

// GordieHowe: the structure records of a realized program (Lean
// `GordieHowe.RealizedProgram.Structure`, the module Structure of an
// export).
//
// The compiler names the objects it creates, so the Lean checkers read
// pointers instead of searching: gadget records
// (kind, predicates, values, parameters, parts), value back-pointers
// (origins, messages, bound records, member checks' values), placement
// pointers (routes, hosting circuit entries, challenge values), each value's
// interval source, and the plan's range requests each MAC record and each
// modular equality reads. Ids are the exported program's (Program.lean) and
// plan's (Plan.lean). Every field is a claim the Lean checkers verify at the
// pointer; nothing here is trusted.
//
// build_structure() fills the records, one function per group of records
// (fill_*). The export writes them to Structure.ghc, which Structure.lean
// loads; print_structure() prints them as a Lean definition, for tests.

#ifndef PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_COMPILER_STRUCTURE_RECORDS_H_
#define PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_COMPILER_STRUCTURE_RECORDS_H_

#include <algorithm>
#include <cstddef>
#include <map>
#include <optional>
#include <stdexcept>
#include <string>
#include <utility>
#include <vector>

#include "gordiehowe/compiler/plan_program.h"
#include "gordiehowe/compiler/structure_data.h"

namespace proofs::gordiehowe::compiler {

namespace structure_records_internal {

// The plan's range request names in the plan's order (plan_export.h,
// Exporter::requests_of: the domains in order, each typed domain's
// requests; a characteristic-two domain has none).
template <class S>
std::vector<std::string> request_names(const BasicCompiledSystem<S> &cs) {
  std::vector<std::string> out;
  for (size_t di = 0; di < cs.num_domains(); ++di) {
    const DomainBase<S> &dm = cs.domain(di);
    S::dispatch(dm.field_id, [&](auto tag) {
      using F = typename decltype(tag)::type;
      if constexpr (!F::kCharacteristicTwo) {
        const auto *fd = dynamic_cast<const Domain<F> *>(&dm);
        if (fd == nullptr) throw std::runtime_error("structure records: untyped domain");
        for (const auto &r : fd->requests()) out.push_back(r.name);
      }
    });
  }
  return out;
}

// The decimal numeral of N (Lean `Export.decimal`).
inline std::string decimal(size_t n) { return std::to_string(n); }

// The names of a modular equality's quotient digit requests (Lean
// `Export.ModEquality.digitRequests`), from its printed form: DIGITS digits,
// the top digit derived when TOP_DERIVED.
inline std::vector<std::string> digit_requests(const std::string &name, size_t digits,
                                               bool top_derived) {
  std::vector<std::string> out;
  if (digits == 1) return {name + ".q"};
  if (top_derived) {
    if (digits == 2) return {name + ".low", name + ".high"};
    for (size_t j = 0; j + 1 < digits; ++j) out.push_back(name + ".d" + decimal(j));
    out.push_back(name + ".high");
    return out;
  }
  for (size_t j = 0; j < digits; ++j) out.push_back(name + ".d" + decimal(j));
  return out;
}

}  // namespace structure_records_internal

// Batch 1 (MAC sites): the macSite gadget records and their origins. One
// record per cross equal, in predicate order, first among the gadgets (the
// completeness steps name a site by its record's index and slot,
// program_builder.h, completion_certs): preds = [cross, tails], the x
// side's tail first where no domain hosts the MAC (the plan's MAC records
// A's first, the cross's origin naming A's); values = [tag, key], KEY the
// value holding the MAC's key challenge; params = [macField, chunks,
// width]. A tail is the realization of the cross named as the lowering
// named it (mac.h, `rec.tail`); a tail the program lacks refuses the
// export. The origins: the tag at slot 0, the key at slot 1 (a key value
// that an earlier record already originates keeps that origin).
template <class S>
void fill_mac_sites(const BasicCompiledSystem<S> &cs, const ProgramData &,
                    StructureRecords &out) {
  const ir::Program &P = cs.program();
  const auto &macs = cs.records().macs;
  const size_t np = P.predicates.size();
  std::map<size_t, std::pair<size_t, size_t>> origins(out.origins.begin(), out.origins.end());
  for (size_t pid = 0; pid < np; ++pid) {
    const ir::Predicate &c = P.predicates[pid];
    if (c.body != ir::Predicate::kCross) continue;
    const size_t first = size_t(c.origin.index);
    const bool hosted = c.mac.blind_x == ir::kNone;
    if (c.origin.kind != ir::Origin::kCross || first + (hosted ? 0 : 1) >= macs.size())
      throw std::runtime_error("structure records: MAC '" + c.name + "' has no plan record");
    std::vector<std::string> tails = {macs[first].tail};
    if (!hosted) tails.push_back(macs[first + 1].tail);
    StructureRecords::Gadget g;
    g.kind = StructureRecords::GadgetKind::macSite;
    g.preds = {pid};
    for (const std::string &t : tails) {
      size_t found = SIZE_MAX;
      for (size_t q = 0; q < np; ++q) {
        const ir::Predicate &pr = P.predicates[q];
        if (pr.name != t || pr.role != ir::Predicate::Role::kRealization || pr.owner != pid)
          continue;
        if (found != SIZE_MAX)
          throw std::runtime_error("structure records: MAC '" + c.name + "' has two tails '" +
                                   t + "'");
        found = q;
      }
      if (found == SIZE_MAX)
        throw std::runtime_error("structure records: MAC '" + c.name + "' has no tail '" + t +
                                 "'");
      g.preds.push_back(found);
    }
    size_t key = SIZE_MAX;
    for (size_t v = 0; v < P.values.size() && key == SIZE_MAX; ++v)
      if (P.values[v].kind == ir::Value::kChallenge && P.values[v].ref == c.mac.key) key = v;
    if (key == SIZE_MAX)
      throw std::runtime_error("structure records: MAC '" + c.name + "' has no key value");
    g.values = {size_t(c.mac.tag), key};
    g.params = {size_t(c.mac.mac_field), c.mac.chunks, c.mac.width};
    const size_t gi = out.gadgets.size();
    out.gadgets.push_back(std::move(g));
    if (!origins.emplace(size_t(c.mac.tag), std::make_pair(gi, size_t(0))).second)
      throw std::runtime_error("structure records: MAC '" + c.name + "' shares its tag");
    origins.emplace(key, std::make_pair(gi, size_t(1)));
  }
  out.origins.assign(origins.begin(), origins.end());
}

namespace structure_records_internal {

// The modField gadget records of program P from the lowerings' row records
// ROWS (PlanRecords::mod_rows): for each field-form mod_q m, its field row
// r, the predicate the first kField row record of m names (as the
// completeness certificate resolves it, program_builder.h's mod_row), whose
// role is the realization of m.
inline void mod_fields(const ir::Program &P, const std::vector<PlanRecords::ModRow> &rows,
                       StructureRecords &out) {
  // The first predicate of each name.
  std::map<std::string, size_t> by_name;
  for (size_t i = 0; i < P.predicates.size(); ++i) by_name.emplace(P.predicates[i].name, i);
  for (size_t m = 0; m < P.predicates.size(); ++m) {
    const ir::Predicate &q = P.predicates[m];
    if (q.body != ir::Predicate::kMod || q.mod.form != ir::ModForm::kField) continue;
    const PlanRecords::ModRow *row = nullptr;
    for (const auto &r : rows)
      if (r.mod == q.name && r.kind == PlanRecords::ModRow::kField) {
        row = &r;
        break;
      }
    size_t rid = SIZE_MAX;
    if (row != nullptr && !row->row.empty())
      if (auto it = by_name.find(row->row); it != by_name.end()) rid = it->second;
    if (rid == SIZE_MAX) {
      if (q.q != "0")
        plan_export_internal::export_fail("structure records: the field-form mod_q '" + q.name +
                                          "' (" + std::to_string(m) + ") has no field row");
      continue;
    }
    const ir::Predicate &r = P.predicates[rid];
    if (r.role != ir::Predicate::Role::kRealization || r.owner != m)
      plan_export_internal::export_fail(
          "structure records: the field row '" + r.name + "' (" + std::to_string(rid) +
          ") of the field-form mod_q '" + q.name + "' (" + std::to_string(m) +
          ") is not its realization");
    out.gadgets.push_back({StructureRecords::GadgetKind::modField, {m, rid}, {}, {}, {}});
  }
}

// Each value's interval source (Lean `IvlSource`), as the old Lean
// `leafIvl primeNodes f v declaredRanges` (RealizationValid.lean) picks it,
// by the same priority, so that every interval the checks read is the one
// they read before the table. The functions mirror their Lean namesakes
// over the exported program, matching nodes as Lean matches `Expr`
// constructors.
namespace ivl {

using I = WideInt;

inline I parse(const std::string &s) {
  I v(0);
  size_t i = 0;
  const bool neg = !s.empty() && s[0] == '-';
  if (neg) i = 1;
  for (; i < s.size(); ++i) v = v * I(10) + I(int(s[i] - '0'));
  return neg ? -v : v;
}
inline I iabs(const I &x) { return x.negative() ? -x : x; }

struct Ivl {
  I lo, hi;
};

// A root product's reading (Lean `rootsAt`'s (u, j, r)): coordinate i is
// coordinate G(i) of value U, vanishing exactly at the roots R(i).
struct Roots {
  uint64_t u = 0;
  std::function<uint64_t(uint64_t)> g;
  std::function<std::vector<I>(uint64_t)> r;
};
using View = std::pair<uint64_t, std::function<uint64_t(uint64_t)>>;
// A root-set equation's reading (Lean `rootSetView`).
struct RootSet {
  std::function<uint64_t(uint64_t)> j;
  uint64_t len = 0;
  Ivl ivl;
};

class Mirror {
 public:
  explicit Mirror(const ir::Program &P) : P_(P) {
    for (const auto &f : P.fields) chars_.push_back(parse(f.characteristic));
    default_leaf_.op = ir::Expr::kLeaf;
    default_leaf_.x = 0;
  }

  // ---------------------------------------------------- program reads --

  const ir::Expr &node(uint64_t e) const {
    return e < P_.nodes.size() ? P_.nodes[e] : default_leaf_;
  }
  // Lean `ir.expr k` (a default `.leaf 0` past the end), as a node id.
  uint64_t expr(uint64_t k) const { return k < P_.exprs.size() ? P_.exprs[k] : kNoNode; }
  const ir::Value &value(uint64_t v) const {
    return v < P_.values.size() ? P_.values[v] : default_value_;
  }
  uint64_t domain_field(uint64_t d) const {
    return d < P_.domains.size() ? P_.domains[d].field : 0;
  }
  I char_of(uint64_t f) const { return f < chars_.size() ? chars_[f] : I(0); }
  // Lean `valueField`: the printed `field` of a kind that allows one,
  // else the printed domain's field.
  uint64_t value_field(uint64_t v) const {
    const ir::Value &x = value(v);
    const bool allows = x.kind == ir::Value::kChallenge || x.kind == ir::Value::kPubExpr ||
                        x.kind == ir::Value::kLate || x.kind == ir::Value::kMessage;
    if (allows && x.domain == ir::kNone) return x.field;
    return domain_field(x.domain == ir::kNone ? 0 : x.domain);
  }
  uint64_t entry(uint64_t idx, uint64_t i) const {
    if (idx >= P_.index_maps.size()) return 0;
    const auto &m = P_.index_maps[idx];
    return i < m.size() ? m[i] : 0;
  }
  // A constant's entries, parsed once.
  const std::vector<I> &entries(uint64_t c) {
    auto it = consts_.find(c);
    if (it != consts_.end()) return it->second;
    std::vector<I> es;
    for (const auto &e : value(c).entries) es.push_back(parse(e));
    return consts_.emplace(c, std::move(es)).first->second;
  }
  bool is_const(uint64_t c) const { return value(c).kind == ir::Value::kConstant; }
  std::optional<I> const_coef(const ir::Expr &n) const {
    if (n.op != ir::Expr::kScale || n.x >= P_.coefs.size() || !P_.coefs[n.x].is_const)
      return std::nullopt;
    return parse(P_.coefs[n.x].c);
  }

  // ------------------------------------------------ the Lean matchers --

  bool zero_const(uint64_t z) {
    if (!is_const(z)) return false;
    for (const I &e : entries(z))
      if (!e.is_zero()) return false;
    return true;
  }
  bool const_all(uint64_t u, const I &c, uint64_t n, uint64_t f) {
    if (!is_const(u)) return false;
    const auto &es = entries(u);
    if (n > es.size()) return false;
    for (const I &e : es)
      if (e != c) return false;
    return value_field(u) == f;
  }
  std::optional<I> const_entry(uint64_t c, uint64_t n, uint64_t f) {
    if (!is_const(c) || entries(c).empty()) return std::nullopt;
    const I k = entries(c)[0];
    if (const_all(c, k, n, f) && k < char_of(f)) return k;
    return std::nullopt;
  }
  static I centered(const I &p, const I &c) { return I(2) * c < p ? c : c - p; }

  // The `in` of predicate Q: `.mem d [rec] (.range N) (.lookup r)`.
  const ir::Predicate *range_mem(uint64_t q) const {
    const ir::Predicate &p = P_.predicates[q];
    if (p.body != ir::Predicate::kMem || p.set != ir::kNone || p.in.implied) return nullptr;
    return &p;
  }
  std::optional<I> range_bound_of(uint64_t v, uint64_t q) const {
    const ir::Predicate *p = range_mem(q);
    if (p == nullptr) return std::nullopt;
    const ir::Expr &rec = node(p->lhs);
    const auto k = p->in.lookup.kind;
    const uint64_t f = value_field(v);
    const I N = parse(p->range);
    if (rec.op == ir::Expr::kLeaf && rec.x == v &&
        (k == ir::LookupKind::kDirect || k == ir::LookupKind::kDigits) && !N.is_zero() &&
        N <= char_of(f) && domain_field(p->domain) == f)
      return N;
    return std::nullopt;
  }
  std::optional<std::pair<I, I>> shift_range_of(uint64_t v, uint64_t q) {
    const ir::Predicate *p = range_mem(q);
    if (p == nullptr) return std::nullopt;
    const auto k = p->in.lookup.kind;
    const uint64_t f = value_field(v);
    const I pc = char_of(f);
    const I N = parse(p->range);
    if (!(!N.is_zero() && N <= pc && domain_field(p->domain) == f &&
          (k == ir::LookupKind::kDirect || k == ir::LookupKind::kDigits ||
           k == ir::LookupKind::kTwoSided)))
      return std::nullopt;
    const ir::Expr &rec = node(p->lhs);
    if (rec.op == ir::Expr::kLeaf) {
      if (rec.x == v) return std::make_pair(I(0), N);
      return std::nullopt;
    }
    if (rec.op == ir::Expr::kAdd) {
      const ir::Expr &a = node(rec.a), &b = node(rec.b);
      if (a.op != ir::Expr::kLeaf || b.op != ir::Expr::kLeaf) return std::nullopt;
      if (a.x != v) return std::nullopt;
      const auto c = const_entry(b.x, value(v).size(), f);
      if (!c) return std::nullopt;
      return std::make_pair(centered(pc, *c), N);
    }
    return std::nullopt;
  }
  std::optional<Ivl> centred_ivl(uint64_t v, const std::pair<I, I> &cN) const {
    const I p = char_of(value_field(v));
    const I hi = cN.second - I(1) - cN.first;
    if (I(2) * iabs(-cN.first) < p && I(2) * iabs(hi) < p) return Ivl{-cN.first, hi};
    return std::nullopt;
  }
  // Lean `boundIvl`, with the predicate of the first `in` it reads
  // (SIZE_MAX: none).
  std::pair<uint64_t, std::optional<Ivl>> bound_ivl(uint64_t v) {
    for (uint64_t q : shift_preds(v))
      if (auto cN = shift_range_of(v, q)) return {q, centred_ivl(v, *cN)};
    return {SIZE_MAX, std::nullopt};
  }
  std::optional<I> const_of(uint64_t n, uint64_t f, uint64_t C) {
    const ir::Expr &e = node(C);
    if (e.op == ir::Expr::kLeaf) return const_entry(e.x, n, f);
    if (e.op == ir::Expr::kReindex && node(e.a).op == ir::Expr::kLeaf) {
      const uint64_t c = node(e.a).x;
      for (uint64_t i = 0; i < n; ++i)
        if (!(entry(e.x, i) < value(c).size())) return std::nullopt;
      return const_entry(c, value(c).size(), f);
    }
    return std::nullopt;
  }
  // The v₁ of a quadratic root equation's shape in predicate Q (SIZE_MAX:
  // not that shape).
  uint64_t quad_candidate(uint64_t q) const {
    const ir::Predicate &p = P_.predicates[q];
    if (p.body != ir::Predicate::kEqual || node(p.rhs).op != ir::Expr::kLeaf) return SIZE_MAX;
    const ir::Expr &l = node(p.lhs);
    if (l.op != ir::Expr::kMul) return SIZE_MAX;
    const ir::Expr &A = node(l.a);
    if (A.op != ir::Expr::kAdd || node(A.b).op != ir::Expr::kScale) return SIZE_MAX;
    const ir::Expr &v1 = node(node(A.b).a);
    return v1.op == ir::Expr::kLeaf ? v1.x : SIZE_MAX;
  }
  std::optional<std::pair<uint64_t, I>> quad_root_view(uint64_t v, uint64_t q) {
    const ir::Predicate &p = P_.predicates[q];
    if (p.body != ir::Predicate::kEqual) return std::nullopt;
    const ir::Expr &zn = node(p.rhs);
    if (zn.op != ir::Expr::kLeaf) return std::nullopt;
    const uint64_t z = zn.x;
    const ir::Expr &lhs = node(p.lhs);
    if (lhs.op != ir::Expr::kMul) return std::nullopt;
    const ir::Expr &A = node(lhs.a), &B = node(lhs.b);
    if (A.op != ir::Expr::kAdd || B.op != ir::Expr::kAdd) return std::nullopt;
    const ir::Expr &Am = node(A.a), &As = node(A.b), &Bm = node(B.a), &Bs = node(B.b);
    if (Am.op != ir::Expr::kLeaf || Bm.op != ir::Expr::kLeaf) return std::nullopt;
    const auto a = const_coef(As), a2 = const_coef(Bs);
    if (!a || !a2) return std::nullopt;
    const ir::Expr &v1 = node(As.a), &X = node(Bs.a);
    if (v1.op != ir::Expr::kLeaf || X.op != ir::Expr::kAdd) return std::nullopt;
    const ir::Expr &Xs = node(X.a);
    const auto a3 = const_coef(Xs);
    if (!a3) return std::nullopt;
    const ir::Expr &v2 = node(Xs.a);
    if (v2.op != ir::Expr::kLeaf) return std::nullopt;
    const uint64_t m = Am.x, f = value_field(v);
    if (v1.x == v && v2.x == v && Bm.x == m && *a + I(1) == char_of(f) && *a2 == *a &&
        *a3 == *a && domain_field(p.domain) == f && value_field(m) == f &&
        value_field(z) == f && value(v).size() <= lhs.n && zero_const(z)) {
      if (auto c = const_of(value(v).size(), f, X.b)) return std::make_pair(m, *c);
    }
    return std::nullopt;
  }

  std::optional<View> leaf_view_at(uint64_t fuel, uint64_t level, uint64_t e) const {
    const ir::Expr &n = node(e);
    if (n.op == ir::Expr::kLeaf)
      return View{n.x, [](uint64_t i) { return i; }};
    if (fuel == 0) return std::nullopt;
    if (n.op == ir::Expr::kReindex) {
      auto in = leaf_view_at(fuel - 1, level, n.a);
      if (!in) return std::nullopt;
      const uint64_t idx = n.x;
      auto g = in->second;
      return View{in->first, [this, idx, g](uint64_t i) { return g(entry(idx, i)); }};
    }
    if (n.op == ir::Expr::kRef && level > 0) return leaf_view_at(fuel - 1, level - 1, expr(n.x));
    return std::nullopt;
  }
  std::optional<std::function<I(uint64_t)>> const_read_at(uint64_t f, uint64_t fuel,
                                                          uint64_t level, uint64_t C) {
    auto lv = leaf_view_at(fuel, level, C);
    if (!lv) return std::nullopt;
    const uint64_t c = lv->first;
    if (!is_const(c) || value_field(c) != f) return std::nullopt;
    const std::vector<I> *es = &entries(c);
    auto gc = lv->second;
    return std::function<I(uint64_t)>([es, gc](uint64_t i) {
      const uint64_t k = gc(i);
      return k < es->size() ? (*es)[k] : I(0);
    });
  }
  std::optional<std::function<I(uint64_t)>> factor_roots(uint64_t f, uint64_t fuel,
                                                         uint64_t level, uint64_t L, uint64_t C) {
    const I p = char_of(f);
    const ir::Expr &n = node(C);
    if (auto a = const_coef(n)) {
      auto cv = const_read_at(f, fuel, level, n.a);
      if (!cv) return std::nullopt;
      if (!(*a + I(1) == p)) return std::nullopt;
      for (uint64_t i = 0; i < L; ++i)
        if (!((*cv)(i) < p)) return std::nullopt;
      return cv;
    }
    auto cv = const_read_at(f, fuel, level, C);
    if (!cv) return std::nullopt;
    for (uint64_t i = 0; i < L; ++i)
      if (!((*cv)(i) < p)) return std::nullopt;
    auto c = *cv;
    return std::function<I(uint64_t)>([c, p](uint64_t i) {
      const I x = c(i);
      const I d = p >= x ? p - x : I(0);
      return p.is_zero() ? d : d % p;
    });
  }
  std::optional<Roots> roots_at(uint64_t f, uint64_t fuel, uint64_t level, uint64_t L,
                                uint64_t e) {
    if (fuel == 0) return std::nullopt;
    const uint64_t fu = fuel - 1;
    const ir::Expr &n = node(e);
    switch (n.op) {
      case ir::Expr::kMul: {
        auto a = roots_at(f, fu, level, L, n.a);
        if (!a) return std::nullopt;
        auto b = roots_at(f, fu, level, L, n.b);
        if (!b) return std::nullopt;
        if (a->u != b->u) return std::nullopt;
        for (uint64_t i = 0; i < L; ++i)
          if (a->g(i) != b->g(i)) return std::nullopt;
        auto ra = a->r, rb = b->r;
        return Roots{a->u, a->g, [ra, rb](uint64_t i) {
                       std::vector<I> x = ra(i);
                       const std::vector<I> y = rb(i);
                       x.insert(x.end(), y.begin(), y.end());
                       return x;
                     }};
      }
      case ir::Expr::kRef:
        if (level == 0) return std::nullopt;
        return roots_at(f, fu, level - 1, L, expr(n.x));
      case ir::Expr::kProd: {
        const uint64_t k = n.x;
        auto in = roots_at(f, fu, level, L * k, n.a);
        if (!in) return std::nullopt;
        for (uint64_t i = 0; i < L; ++i)
          for (uint64_t t = 0; t < k; ++t)
            if (in->g(i * k + t) != in->g(i * k)) return std::nullopt;
        auto g = in->g;
        auto r = in->r;
        return Roots{in->u, [g, k](uint64_t i) { return g(i * k); },
                     [r, k](uint64_t i) {
                       std::vector<I> x;
                       for (uint64_t t = 0; t < k; ++t) {
                         const std::vector<I> y = r(i * k + t);
                         x.insert(x.end(), y.begin(), y.end());
                       }
                       return x;
                     }};
      }
      case ir::Expr::kAdd: {
        auto lv = leaf_view_at(fu, level, n.a);
        if (!lv) return std::nullopt;
        auto rho = factor_roots(f, fu, level, L, n.b);
        if (!rho) return std::nullopt;
        auto r = *rho;
        return Roots{lv->first, lv->second,
                     [r](uint64_t i) { return std::vector<I>{r(i)}; }};
      }
      default:
        break;
    }
    if (n.op == ir::Expr::kScale) {
      if (auto s = const_coef(n)) {
        if (!s->is_zero() && *s < char_of(f)) return roots_at(f, fu, level, L, n.a);
        return std::nullopt;
      }
    }
    auto lv = leaf_view_at(fu, level, e);
    if (!lv) return std::nullopt;
    return Roots{lv->first, lv->second, [](uint64_t) { return std::vector<I>{I(0)}; }};
  }
  static constexpr uint64_t kRootFuel = 64;
  // The value a root-set equation's shape in predicate Q reads (Lean
  // `rootsAt` at no coordinates; SIZE_MAX: none).
  uint64_t root_candidate(uint64_t q) {
    const ir::Predicate &p = P_.predicates[q];
    if (p.body != ir::Predicate::kEqual || node(p.rhs).op != ir::Expr::kLeaf) return SIZE_MAX;
    auto r = roots_at(domain_field(p.domain), kRootFuel, P_.exprs.size(), 0, p.lhs);
    return r ? r->u : SIZE_MAX;
  }
  // Lean `rootSetView v` at predicate Q, whose `rootsAt` at no
  // coordinates reads V (root_candidate).
  std::optional<RootSet> root_set_view(uint64_t v, uint64_t q) {
    const ir::Predicate &p = P_.predicates[q];
    const uint64_t z = node(p.rhs).x;
    if (!zero_const(z)) return std::nullopt;
    const uint64_t L = node(p.lhs).n;
    const uint64_t df = domain_field(p.domain);
    auto r = roots_at(df, kRootFuel, P_.exprs.size(), L, p.lhs);
    if (!r) return std::nullopt;
    std::vector<I> rs;
    for (uint64_t i = 0; i < L; ++i) {
      const std::vector<I> x = r->r(i);
      rs.insert(rs.end(), x.begin(), x.end());
    }
    I lo = rs.empty() ? I(0) : rs[0], hi(0);
    for (const I &x : rs) {
      if (x < lo) lo = x;
      if (x > hi) hi = x;
    }
    const uint64_t f = value_field(v);
    if (!(r->u == v && df == f && value_field(z) == f)) return std::nullopt;
    for (const I &x : rs)
      if (!(x < char_of(f))) return std::nullopt;
    return RootSet{r->g, L, Ivl{lo, hi}};
  }
  bool root_set_hull(uint64_t v, const std::vector<RootSet> &ws) {
    const uint64_t n = value(v).size();
    std::vector<bool> seen(n, false);
    for (const auto &w : ws)
      for (uint64_t i = 0; i < w.len; ++i) {
        const uint64_t c = w.j(i);
        if (c < n) seen[c] = true;
      }
    return std::all_of(seen.begin(), seen.end(), [](bool b) { return b; });
  }
  bool bool_check_ok(uint64_t v, uint64_t q) const {
    if (q >= P_.predicates.size()) return false;
    const ir::Predicate &p = P_.predicates[q];
    if (p.body != ir::Predicate::kEqual) return false;
    const ir::Expr &l = node(p.lhs), &c = node(p.rhs);
    if (l.op != ir::Expr::kMul || c.op != ir::Expr::kLeaf) return false;
    const ir::Expr &a = node(l.a), &b = node(l.b);
    return a.op == ir::Expr::kLeaf && b.op == ir::Expr::kLeaf && a.x == v && b.x == v &&
           c.x == v && domain_field(p.domain) == value_field(v);
  }

  // ------------------------------------------- per-value predicate lists --

  // The predicates, in order, whose matchers can read value v: the `in`s on
  // v or v + c, the quadratic and root-set shapes on v. A matcher at any
  // other predicate returns none, so the first match over these is the
  // first over every predicate.
  void index() {
    const size_t nv = P_.values.size();
    range_.assign(nv, {});
    quad_.assign(nv, {});
    root_.assign(nv, {});
    for (uint64_t q = 0; q < P_.predicates.size(); ++q) {
      if (const ir::Predicate *p = range_mem(q)) {
        const ir::Expr &rec = node(p->lhs);
        uint64_t u = SIZE_MAX;
        if (rec.op == ir::Expr::kLeaf) u = rec.x;
        if (rec.op == ir::Expr::kAdd && node(rec.a).op == ir::Expr::kLeaf) u = node(rec.a).x;
        if (u < nv) range_[u].push_back(q);
      }
      if (const uint64_t u = quad_candidate(q); u < nv) quad_[u].push_back(q);
      if (const uint64_t u = root_candidate(q); u < nv) root_[u].push_back(q);
    }
  }
  const std::vector<uint64_t> &shift_preds(uint64_t v) const {
    return v < range_.size() ? range_[v] : empty_;
  }

  // Lean `restIvl` at a value with no root equation consulted: the first
  // range, else a Bit prime-subfield read; NONE_KNOWN: a Sub value at a
  // node (a prime-subfield read whose node the export does not know).
  struct Rest {
    std::optional<Ivl> ivl;
    uint64_t range = SIZE_MAX;
    bool unknown = false;
  };
  Rest rest(uint64_t v) {
    Rest o;
    for (uint64_t q : shift_preds(v))
      if (auto N = range_bound_of(v, q)) {
        o.range = q;
        o.ivl = Ivl{I(0), *N - I(1)};
        return o;
      }
    const ir::Value &x = value(v);
    const uint64_t dom = x.domain == ir::kNone ? 0 : x.domain;
    if (dom >= P_.domains.size()) return o;
    using TS = ir::Value::TypeSource;
    if (x.type == ir::VType::kBit &&
        (x.type_source == TS::kNode ||
         (x.type_source == TS::kPred && bool_check_ok(v, x.type_pred))))
      o.ivl = Ivl{I(0), I(1)};
    if (x.type == ir::VType::kSub && x.type_source == TS::kNode) o.unknown = true;
    return o;
  }

  // The source of value V's interval, none when leafIvl gives none at every
  // source; DECLARED: V's entry of the declared statement bounds.
  std::optional<StructureRecords::IvlSource> source(uint64_t v, size_t declared) {
    using Src = StructureRecords::IvlSource;
    using K = Src::Kind;
    const ir::Value &x = value(v);
    const uint64_t f = value_field(v);
    if (!(f < chars_.size() && I(2) < char_of(f))) return std::nullopt;
    switch (x.kind) {
      case ir::Value::kConstant:
        return Src{K::constant, {}};
      case ir::Value::kOpaque:
        if (declared != SIZE_MAX) return Src{K::declared, {declared}};
        if (!x.args.empty()) {
          if (x.type == ir::VType::kBit) return Src{K::opaqueBit, {}};
          return std::nullopt;
        }
        {
          const Rest r = rest(v);
          if (r.range != SIZE_MAX) return Src{K::range, {size_t(r.range)}};
        }
        return Src{K::prime, {}};
      case ir::Value::kBound: {
        const auto b = bound_ivl(v);
        if (b.first == SIZE_MAX) return std::nullopt;
        return Src{K::shiftRange, {size_t(b.first)}};
      }
      default:
        break;
    }
    for (uint64_t q : quad_[v]) {
      auto mc = quad_root_view(v, q);
      if (!mc) continue;
      const auto b = bound_ivl(mc->first);
      if (!b.second) continue;
      if (b.second->lo.is_zero() && b.second->hi <= mc->second)
        return Src{K::quadRoot, {size_t(q), size_t(b.first)}};
    }
    if (x.type != ir::VType::kBit) {
      std::vector<RootSet> ws;
      std::vector<uint64_t> qs;
      for (uint64_t q : root_[v])
        if (auto w = root_set_view(v, q)) {
          ws.push_back(std::move(*w));
          qs.push_back(q);
        }
      if (!ws.empty() && root_set_hull(v, ws)) {
        return Src{K::rootSet, std::vector<size_t>(qs.begin(), qs.end())};
      }
    }
    const Rest r = rest(v);
    if (r.range != SIZE_MAX) return Src{K::range, {size_t(r.range)}};
    return Src{K::prime, {}};
  }

  // The export check (decision D1): the honest checks read an opaque
  // statement value with a declared bound N at [0, N − 1], where they read
  // restIvl before; the export fails unless that is within restIvl's
  // interval (or restIvl gives none).
  void check_declared(uint64_t v) {
    const ir::Value &x = value(v);
    const I p = char_of(value_field(v));
    const I N = parse(x.bound);
    std::optional<Ivl> now;
    if (!N.is_zero() && N <= p) now = Ivl{I(0), N - I(1)};
    const Rest old = rest(v);
    auto text = [](const std::optional<Ivl> &j) {
      return j ? "[" + j->lo.str() + ", " + j->hi.str() + "]" : std::string("none");
    };
    const std::string who = "the declared statement value '" + x.name + "' (" +
                            std::to_string(v) + ")";
    if (old.ivl && (!now || now->lo < old.ivl->lo || now->hi > old.ivl->hi))
      plan_export_internal::export_fail(
          "structure records: " + who + " has the interval " + text(now) +
          " at its declared bound, not within " + text(old.ivl) + " that the honest checks read");
    if (!old.ivl && old.unknown && !now)
      plan_export_internal::export_fail("structure records: " + who +
                                        " has no interval at its declared bound, where "
                                        "a prime-subfield read may give one");
  }

  void fill(StructureRecords &out) {
    index();
    size_t declared = 0;
    for (uint64_t v = 0; v < P_.values.size(); ++v) {
      const ir::Value &x = P_.values[v];
      // Lean declaredRanges: the statement values with a bound.
      size_t k = SIZE_MAX;
      if (ir::is_stmt_value(P_, size_t(v)) && !x.bound.empty()) k = declared++;
      const auto s = source(v, k);
      if (!s) continue;
      if (s->kind == StructureRecords::IvlSource::Kind::declared) check_declared(v);
      out.ivl_sources.push_back({size_t(v), *s});
    }
  }

 private:
  static constexpr uint64_t kNoNode = ~uint64_t(0);
  const ir::Program &P_;
  std::vector<I> chars_;
  ir::Expr default_leaf_;
  ir::Value default_value_;
  std::map<uint64_t, std::vector<I>> consts_;
  std::vector<std::vector<uint64_t>> range_, quad_, root_;
  std::vector<uint64_t> empty_;
};

}  // namespace ivl

}  // namespace structure_records_internal

// Batch 2 (companion rows): the modField gadget records.
template <class S>
void fill_mod_fields(const BasicCompiledSystem<S> &cs, const ProgramData &,
                     StructureRecords &out) {
  structure_records_internal::mod_fields(cs.program(), cs.records().mod_rows, out);
}

// Batch 2 (V8): each value's interval source.
template <class S>
void fill_ivl_sources(const BasicCompiledSystem<S> &cs, const ProgramData &,
                      StructureRecords &out) {
  structure_records_internal::ivl::Mirror m(cs.program());
  m.fill(out);
}

// Batch 3 (lookups): each bound value's record lookup, (v, pid) in
// increasing v. The range lowering names the node a lookup's digits bind
// (RangeRealization::bound_id, range.h) and the program builder the
// lookup's predicate (Certificates::bound_recs, the certificates C of the
// compiled system); a value of kind bound without one fails the export.
template <class S>
void fill_bound_recs(const BasicCompiledSystem<S> &, const ProgramData &p,
                     const ir::Certificates &c, StructureRecords &out) {
  for (size_t v = 0; v < p.values.size(); ++v) {
    const ir::Id pid = v < c.bound_recs.size() ? c.bound_recs[v] : ir::kNone;
    if (pid != ir::kNone) {
      if (pid >= p.predicates.size())
        plan_export_internal::export_fail("structure records: the record lookup of bound value " +
                                          p.values[v].name + " is no predicate");
      out.bound_recs.push_back({v, size_t(pid)});
    } else if (p.values[v].kind == "bound") {
      plan_export_internal::export_fail("structure records: bound value " + p.values[v].name +
                                        " names no record lookup");
    }
  }
}

namespace structure_records_internal {

namespace place {

inline std::string pred_name(const ir::Program &P, size_t pid) {
  return "'" + P.predicates[pid].name + "' (" + std::to_string(pid) + ")";
}

// Whether the parameters of nodes X and Y (same op) are equal as Lean
// terms: the coefficient, the index map's entries, the named operator, the
// linear rows, prod's n, the leaf, the shared entry, the logic builder and
// its w.
inline bool same_params(const ir::Program &P, program_printer_internal::Printer &pr,
                        const ir::Expr &x, const ir::Expr &y) {
  switch (x.op) {
    case ir::Expr::kScale:
      return pr.coef(ir::Id(x.x)) == pr.coef(ir::Id(y.x));
    case ir::Expr::kReindex:
      return P.index_maps.at(x.x) == P.index_maps.at(y.x);
    case ir::Expr::kApply:
      return pr.named_op(ir::Id(x.x)) == pr.named_op(ir::Id(y.x));
    case ir::Expr::kLinear: {
      const ir::LinearRows &a = P.linears.at(x.x), &b = P.linears.at(y.x);
      if (a.size() != b.size()) return false;
      for (size_t i = 0; i < a.size(); ++i) {
        if (a[i].size() != b[i].size()) return false;
        for (size_t j = 0; j < a[i].size(); ++j)
          if (a[i][j].first != b[i][j].first ||
              pr.coef(a[i][j].second) != pr.coef(b[i][j].second))
            return false;
      }
      return true;
    }
    case ir::Expr::kLogic:
      return x.logic == y.logic && x.x == y.x && x.args.size() == y.args.size();
    case ir::Expr::kAdd:
    case ir::Expr::kSub:
    case ir::Expr::kMul:
    case ir::Expr::kConcat:
    case ir::Expr::kMux:
      return true;
    default:
      // kLeaf, kProd, kRef.
      return x.x == y.x;
  }
}

// The children of node X, in Lean's argument order.
inline std::vector<ir::Id> kids(const ir::Expr &x) {
  switch (x.op) {
    case ir::Expr::kLeaf:
    case ir::Expr::kRef:
      return {};
    case ir::Expr::kAdd:
    case ir::Expr::kSub:
    case ir::Expr::kMul:
    case ir::Expr::kConcat:
      return {x.a, x.b};
    case ir::Expr::kMux:
      return {x.a, x.b, x.c};
    case ir::Expr::kLogic:
      return x.args;
    default:
      return {x.a};
  }
}

// Whether arena nodes A and B are the same Lean expression (`Expr.beq`):
// the same constructor, parameters and children, shared entries by index.
inline bool same(const ir::Program &P, program_printer_internal::Printer &pr, ir::Id a,
                 ir::Id b) {
  std::vector<std::pair<ir::Id, ir::Id>> st{{a, b}};
  while (!st.empty()) {
    auto [x, y] = st.back();
    st.pop_back();
    if (x == y) continue;
    const ir::Expr &nx = P.nodes.at(x), &ny = P.nodes.at(y);
    if (nx.op != ny.op || !same_params(P, pr, nx, ny)) return false;
    const std::vector<ir::Id> kx = kids(nx), ky = kids(ny);
    if (kx.size() != ky.size()) return false;
    for (size_t i = 0; i < kx.size(); ++i) st.push_back({kx[i], ky[i]});
  }
  return true;
}

// The conversions the source side E is read through as the realized side
// F, in mismatch order, appended to OUT (Lean `Expr.matchL`, mirroring
// `Expr.matchB`, Valid.lean): pre-order, a before b, through add, sub,
// mul, concat (both children) and scale, reindex, apply (equal parameters,
// one child). At a pair of shared entries k, k' with k != k' the conversion
// j with convs[j].source == k and convs[j].read or committed == k' (the
// first); equal entries consume nothing; any other difference fails the
// export, naming WHO.
inline void mismatches(const ir::Program &P, ir::Id e, ir::Id f, std::vector<size_t> &out,
                       const std::string &who) {
  program_printer_internal::Printer pr(P);
  // Pending pairs, the next on top: pushing b's pair before a's walks a
  // first.
  std::vector<std::pair<ir::Id, ir::Id>> st{{e, f}};
  while (!st.empty()) {
    auto [x, y] = st.back();
    st.pop_back();
    if (x == y) continue;
    const ir::Expr &nx = P.nodes.at(x), &ny = P.nodes.at(y);
    if (nx.op == ir::Expr::kRef && ny.op == ir::Expr::kRef) {
      if (nx.x == ny.x) continue;
      size_t j = 0;
      while (j < P.convs.size() &&
             !(P.convs[j].source == nx.x &&
               (P.convs[j].read == ny.x || P.convs[j].committed == ny.x)))
        ++j;
      if (j == P.convs.size())
        plan_export_internal::export_fail(
            "structure records: " + who + " reads shared expression " +
            std::to_string(nx.x) + " as " + std::to_string(ny.x) +
            ", which no spectral conversion pairs");
      out.push_back(j);
      continue;
    }
    if (nx.op == ny.op) {
      switch (nx.op) {
        case ir::Expr::kAdd:
        case ir::Expr::kSub:
        case ir::Expr::kMul:
        case ir::Expr::kConcat:
          st.push_back({nx.b, ny.b});
          st.push_back({nx.a, ny.a});
          continue;
        case ir::Expr::kScale:
        case ir::Expr::kReindex:
        case ir::Expr::kApply:
          if (!same_params(P, pr, nx, ny))
            plan_export_internal::export_fail("structure records: " + who +
                                              " differs from its realized form at node " +
                                              std::to_string(x) + " in a parameter");
          st.push_back({nx.a, ny.a});
          continue;
        default:
          break;
      }
    }
    if (!same(P, pr, x, y))
      plan_export_internal::export_fail("structure records: " + who +
                                        " differs from its realized form at node " +
                                        std::to_string(x) + " (realized " + std::to_string(y) +
                                        ") other than at a convolution's reading");
  }
}

// Whether a value read by the expressions ROOTS, through their shared
// entries (Lean `exprNodes`: leaves, coefficients' values, named operators'
// operands), is a bit view (kind bits).
inline bool reads_bits(const ir::Program &P, const std::vector<ir::Id> &roots) {
  std::vector<bool> seen(P.nodes.size(), false);
  std::vector<ir::Id> st(roots.begin(), roots.end());
  auto bits = [&](ir::Id v) {
    return v != ir::kNone && v < P.values.size() && P.values[v].kind == ir::Value::kBits;
  };
  auto coef_bits = [&](ir::Id c) {
    const ir::Coef &k = P.coefs.at(c);
    return !k.is_const && bits(k.v);
  };
  while (!st.empty()) {
    const ir::Id x = st.back();
    st.pop_back();
    if (x == ir::kNone || seen.at(x)) continue;
    seen[x] = true;
    const ir::Expr &n = P.nodes[x];
    switch (n.op) {
      case ir::Expr::kLeaf:
        if (bits(ir::Id(n.x))) return true;
        break;
      case ir::Expr::kScale:
        if (coef_bits(ir::Id(n.x))) return true;
        break;
      case ir::Expr::kLinear:
        for (const auto &row : P.linears.at(n.x))
          for (const auto &t : row)
            if (coef_bits(t.second)) return true;
        break;
      case ir::Expr::kApply:
        for (ir::Id o = ir::Id(n.x); o != ir::kNone; o = P.ops.at(o).inner)
          if (bits(P.ops.at(o).value)) return true;
        break;
      case ir::Expr::kRef:
        st.push_back(P.exprs.at(n.x));
        break;
      default:
        break;
    }
    for (ir::Id k : kids(n)) st.push_back(k);
  }
  return false;
}

// The routes of program P (Lean `Structure.routes`): one per predicate
// that needs one (Lean `PredBody.needsRoute`: a field equal, a mod_0), by
// its printed target.
inline void routes(const ir::Program &P, StructureRecords &out) {
  using Route = StructureRecords::Route;
  using K = Route::Kind;
  // The first circuit entry placing or type-checking each predicate.
  std::map<size_t, std::pair<size_t, size_t>> entry_of;
  for (size_t c = 0; c < P.circuits.size(); ++c)
    for (size_t k = 0; k < P.circuits[c].entries.size(); ++k) {
      const ir::CircuitEntry &e = P.circuits[c].entries[k];
      if (e.kind == ir::CircuitEntry::kPred || e.kind == ir::CircuitEntry::kTypeCheck)
        entry_of.emplace(e.id, std::make_pair(c, k));
    }
  auto gkr = [&](size_t c, size_t k) {
    return Route{K::gkr, {c, k}};
  };
  for (size_t pid = 0; pid < P.predicates.size(); ++pid) {
    const ir::Predicate &q = P.predicates[pid];
    const bool int_eq = q.body == ir::Predicate::kMod && q.q == "0";
    if (q.body != ir::Predicate::kEqual && !int_eq) continue;
    const std::string who = "the predicate " + pred_name(P, pid);
    const ir::Target *t = q.body == ir::Predicate::kEqual ? &q.target
                          : q.mod.target                  ? &*q.mod.target
                                                          : nullptr;
    Route r;
    if (t == nullptr) {
      auto it = entry_of.find(pid);
      if (it == entry_of.end())
        plan_export_internal::export_fail("structure records: " + who +
                                          " has no target and no circuit entry");
      r = gkr(it->second.first, it->second.second);
    } else {
      switch (t->kind) {
        case ir::Target::kAffine:
          r = {K::affine, {}, reads_bits(P, {q.lhs, q.rhs})};
          break;
        case ir::Target::kQuadratic:
          r = {K::quadratic, {}};
          break;
        case ir::Target::kBatch: {
          if (t->id >= P.batches.size())
            plan_export_internal::export_fail("structure records: " + who +
                                              " targets batch " + std::to_string(t->id) +
                                              ", which the program lacks");
          const std::vector<ir::Id> &parts = P.batches[t->id].parts;
          const auto it = std::find(parts.begin(), parts.end(), ir::Id(pid));
          if (it == parts.end())
            plan_export_internal::export_fail("structure records: " + who +
                                              " is no part of its target batch " +
                                              std::to_string(t->id));
          r = {K::batch, {size_t(t->id), size_t(it - parts.begin())}};
          break;
        }
        case ir::Target::kGkr: {
          size_t k = SIZE_MAX;
          if (t->id < P.circuits.size()) {
            const auto &es = P.circuits[t->id].entries;
            for (size_t i = 0; i < es.size() && k == SIZE_MAX; ++i)
              if ((es[i].kind == ir::CircuitEntry::kPred ||
                   es[i].kind == ir::CircuitEntry::kTypeCheck) &&
                  es[i].id == pid)
                k = i;
          }
          if (k == SIZE_MAX)
            plan_export_internal::export_fail("structure records: " + who +
                                              " is no entry of its target circuit " +
                                              std::to_string(t->id));
          r = gkr(t->id, k);
          break;
        }
        case ir::Target::kRealized: {
          if (t->id >= P.predicates.size() ||
              P.predicates[t->id].body != ir::Predicate::kEqual)
            plan_export_internal::export_fail("structure records: " + who +
                                              " is realized by " + std::to_string(t->id) +
                                              ", which is no field equal");
          const ir::Predicate &rq = P.predicates[t->id];
          std::vector<size_t> js;
          mismatches(P, q.lhs, rq.lhs, js, who);
          mismatches(P, q.rhs, rq.rhs, js, who);
          js.insert(js.begin(), size_t(t->id));
          r = {K::realized, std::move(js)};
          break;
        }
        default:
          plan_export_internal::export_fail("structure records: " + who +
                                            " has an unknown target kind");
      }
    }
    out.routes.push_back({pid, r});
  }
}

// The hosting circuit entries of program P: per table group (t, g) the
// first entry realizing its LogUp identity, every group hosted; per cross
// equal whose H half no domain checks and no blind hides (Lean
// `PredBody.needsH`), the first entry realizing its H half.
inline void hosts(const ir::Program &P, StructureRecords &out) {
  std::map<std::pair<size_t, size_t>, std::pair<size_t, size_t>> logup;
  std::map<size_t, std::pair<size_t, size_t>> mac;
  for (size_t c = 0; c < P.circuits.size(); ++c)
    for (size_t k = 0; k < P.circuits[c].entries.size(); ++k) {
      const ir::CircuitEntry &e = P.circuits[c].entries[k];
      if (e.kind != ir::CircuitEntry::kRealization) continue;
      if (P.circuits[c].domain >= P.domains.size())
        plan_export_internal::export_fail("structure records: circuit " + std::to_string(c) +
                                          " has no domain");
      if (e.real.kind == ir::RealRef::kLogup)
        logup.emplace(std::make_pair(size_t(e.real.a), size_t(e.real.b)),
                      std::make_pair(c, k));
      else if (e.real.kind == ir::RealRef::kMacH)
        mac.emplace(size_t(e.real.a), std::make_pair(c, k));
    }
  for (size_t t = 0; t < P.tables.size(); ++t)
    for (size_t g = 0; g < P.tables[t].groups.size(); ++g) {
      auto it = logup.find({t, g});
      if (it == logup.end())
        plan_export_internal::export_fail("structure records: group " + std::to_string(g) +
                                          " of table '" + P.tables[t].name + "' (" +
                                          std::to_string(t) +
                                          ") has no circuit entry hosting its LogUp identity");
      out.logup_hosts.push_back({{t, g}, it->second});
    }
  for (size_t pid = 0; pid < P.predicates.size(); ++pid) {
    const ir::Predicate &q = P.predicates[pid];
    if (q.body != ir::Predicate::kCross || q.mac.h_predicate != ir::kNone ||
        q.mac.blind_x != ir::kNone)
      continue;
    auto it = mac.find(pid);
    if (it == mac.end())
      plan_export_internal::export_fail("structure records: the MAC " + pred_name(P, pid) +
                                        " has no circuit entry hosting its H half");
    out.mac_hosts.push_back({pid, it->second});
  }
}

// Per challenge some value holds, the least such value of program P.
inline void chal_values(const ir::Program &P, StructureRecords &out) {
  std::map<size_t, size_t> first;
  for (size_t v = 0; v < P.values.size(); ++v)
    if (P.values[v].kind == ir::Value::kChallenge) first.emplace(P.values[v].ref, v);
  out.chal_values.assign(first.begin(), first.end());
}

}  // namespace place

}  // namespace structure_records_internal

// Batch 4 (placement): each predicate's route.
template <class S>
void fill_routes(const BasicCompiledSystem<S> &cs, const ProgramData &,
                 StructureRecords &out) {
  structure_records_internal::place::routes(cs.program(), out);
}

// Batch 4 (placement): the circuit entries hosting the LogUp identities
// and the MACs' H halves.
template <class S>
void fill_hosts(const BasicCompiledSystem<S> &cs, const ProgramData &,
                StructureRecords &out) {
  structure_records_internal::place::hosts(cs.program(), out);
}

// Batch 4 (placement): each challenge's value.
template <class S>
void fill_chal_values(const BasicCompiledSystem<S> &cs, const ProgramData &,
                      StructureRecords &out) {
  structure_records_internal::place::chal_values(cs.program(), out);
}

// Batch 5 (gadgets): the selectRow gadget records.
template <class S>
void fill_select_rows(const BasicCompiledSystem<S> &, const ProgramData &,
                      StructureRecords &) {}

// Batch 5 (gadgets): the selectFirst gadget records.
template <class S>
void fill_select_first(const BasicCompiledSystem<S> &, const ProgramData &,
                       StructureRecords &) {}

// Batch 5 (gadgets): the keccak gadget records and their words' origins.
template <class S>
void fill_keccak(const BasicCompiledSystem<S> &, const ProgramData &,
                 StructureRecords &) {}

// Batch 5 (gadgets): the packedTable gadget records and tableGadgets.
template <class S>
void fill_packed(const BasicCompiledSystem<S> &, const ProgramData &,
                 StructureRecords &) {}

namespace structure_records_internal {

// Each late value's message in the realized program P, (late, message) in
// increasing late value: the values of kind message, keyed by the late value
// they send (Value::ref). A message that sends no value, or two messages of
// one late value, fail the export.
inline std::vector<std::pair<size_t, size_t>> messages_of(const ir::Program &P) {
  std::map<size_t, size_t> msgs;
  for (size_t i = 0; i < P.values.size(); ++i) {
    const ir::Value &x = P.values[i];
    if (x.kind != ir::Value::kMessage) continue;
    if (x.ref == ir::kNone || size_t(x.ref) >= P.values.size())
      plan_export_internal::export_fail("structure records: message " + x.name +
                                        " sends no value");
    if (!msgs.emplace(size_t(x.ref), i).second)
      plan_export_internal::export_fail("structure records: late value " +
                                        P.values[size_t(x.ref)].name + " has two messages");
  }
  return {msgs.begin(), msgs.end()};
}

// Each member check's value in the realized program P, (k, v) in
// increasing check index k: the first value that is check k's member (Lean
// `isMemberOf`: a public opaque value of no argument named
// `statement.<member>` or `<member>`). A check whose member has no value
// fails the export.
inline std::vector<std::pair<size_t, size_t>> member_values_of(const ir::Program &P) {
  std::vector<std::pair<size_t, size_t>> out;
  for (size_t k = 0; k < P.checks.size(); ++k) {
    const std::string &m = P.checks[k].member;
    size_t found = SIZE_MAX;
    for (size_t i = 0; i < P.values.size() && found == SIZE_MAX; ++i) {
      const ir::Value &x = P.values[i];
      if (x.kind == ir::Value::kOpaque && x.args.empty() &&
          (x.opaque == "statement." + m || x.opaque == m))
        found = i;
    }
    if (found == SIZE_MAX)
      plan_export_internal::export_fail("structure records: member check " + std::to_string(k) +
                                        " (" + m + ") reads no value");
    out.push_back({k, found});
  }
  return out;
}

}  // namespace structure_records_internal

// Batch 6 (names): each late value's message (messages_of).
template <class S>
void fill_messages(const BasicCompiledSystem<S> &cs, const ProgramData &,
                   StructureRecords &out) {
  out.messages = structure_records_internal::messages_of(cs.program());
}

// Batch 6 (names): each member check's value (member_values_of).
template <class S>
void fill_member_values(const BasicCompiledSystem<S> &cs, const ProgramData &,
                        StructureRecords &out) {
  out.member_values = structure_records_internal::member_values_of(cs.program());
}

// The range requests each MAC record and each modular equality of the plan
// reads, by their index in the plan's requests (plan_export.h's order). A
// MAC record reads the requests of its lowering's form: `<name>.low`,
// `.high`, `.nowrap` (two quotient digits), `<name>.gq`, `.final.q` (the
// grouped form) or `<name>.q` (one derived digit). A modular equality whose
// quotient has digits reads its digit requests (Lean
// `Export.ModEquality.digitRequests`); the other forms read none. A request
// the plan lacks ends the list there, so the Lean check refuses it.
template <class S>
void fill_requests(const BasicCompiledSystem<S> &cs, const ProgramData &,
                   StructureRecords &out) {
  namespace in = structure_records_internal;
  const std::vector<std::string> names = in::request_names(cs);
  // The first request of each name (Lean `Plan.request`).
  std::map<std::string, size_t> index;
  for (size_t i = 0; i < names.size(); ++i) index.emplace(names[i], i);
  auto ptrs = [&](const std::vector<std::string> &want) {
    std::vector<size_t> v;
    for (const std::string &n : want) {
      auto it = index.find(n);
      if (it == index.end()) break;
      v.push_back(it->second);
    }
    return v;
  };
  const auto &rec = cs.records();
  for (size_t i = 0; i < rec.macs.size(); ++i) {
    const std::string &n = rec.macs[i].name;
    std::vector<size_t> v;
    if (index.count(n + ".low")) {
      v = ptrs({n + ".low", n + ".high", n + ".nowrap"});
    } else if (index.count(n + ".gq")) {
      v = ptrs({n + ".gq", n + ".final.q"});
    } else {
      v = ptrs({n + ".q"});
    }
    if (!v.empty()) out.mac_requests.push_back({i, std::move(v)});
  }
  // The plan's modular equalities: the non-integer assert_mods
  // (plan_export.h, mod_equalities()), with their quotient's form.
  size_t k = 0;
  for (const auto &e : rec.mod_equalities) {
    if (e.integer || e.expr_sides) continue;
    const size_t idx = k++;
    // Its quotient (plan_export.h, quotient_of): the grouped form's final
    // quotient, else the Mod of its name.
    std::string qn = e.name;
    bool grouped = false;
    for (const auto &m : rec.mods)
      if (!grouped && m.name == e.name && m.form == PlanRecords::Mod::kGrouped) {
        qn = m.final_quotient;
        grouped = true;
      }
    const PlanRecords::Mod *q = nullptr;
    for (const auto &m : rec.mods)
      if (q == nullptr && m.name == qn && m.form != PlanRecords::Mod::kGrouped) q = &m;
    if (q == nullptr) continue;
    size_t digits = 0;
    bool top = false;
    switch (q->form) {
      case PlanRecords::Mod::kField:
      case PlanRecords::Mod::kBitQuotient:
      case PlanRecords::Mod::kConstant:
        break;
      case PlanRecords::Mod::kOneDigit:
        digits = 1;
        top = true;
        break;
      default:
        digits = q->k;
        top = q->form == PlanRecords::Mod::kDigits;
    }
    if (digits == 0) continue;
    std::vector<size_t> v = ptrs(in::digit_requests(e.name, digits, top));
    if (!v.empty()) out.mod_requests.push_back({idx, std::move(v)});
  }
}

// The structure records of the compiled system CS, its exported program P
// and its certificates CERTS (export_certificates).
template <class S>
StructureRecords build_structure(const BasicCompiledSystem<S> &cs, const ProgramData &p,
                                 const ir::Certificates &certs) {
  StructureRecords r;
  fill_mac_sites(cs, p, r);
  fill_mod_fields(cs, p, r);
  fill_ivl_sources(cs, p, r);
  fill_bound_recs(cs, p, certs, r);
  fill_routes(cs, p, r);
  fill_hosts(cs, p, r);
  fill_chal_values(cs, p, r);
  fill_select_rows(cs, p, r);
  fill_select_first(cs, p, r);
  fill_keccak(cs, p, r);
  fill_packed(cs, p, r);
  fill_messages(cs, p, r);
  fill_member_values(cs, p, r);
  fill_requests(cs, p, r);
  return r;
}

}  // namespace proofs::gordiehowe::compiler

#endif  // PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_COMPILER_STRUCTURE_RECORDS_H_
