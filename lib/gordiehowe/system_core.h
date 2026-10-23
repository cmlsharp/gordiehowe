// Copyright 2026 Chad Sharp and Paul Grubbs
// SPDX-License-Identifier: Apache-2.0

// GordieHowe: the parts of a system that do not depend on its field set.
//
// A ConstraintSystem<Hash, Fields...> is a SystemCore (its graph, its
// domains as DomainCore, the requests its lowerings take) and its root
// Scope. A domain is a Domain<F> (domain.h), typed by its field alone, so
// a library function that declares values or predicates is templated on
// the fields it uses and never on the system's field set: the field set
// appears where the system compiles, proves and verifies.
//
//   DomainCore      what the system reads of a domain without its field
//   SystemCore      the graph, the domains, the pending equalities,
//                   assert_mod declarations and grouped requests
//   LoweringContext what a grouped lowering reads (Scope::defer)
//   Scope           a naming prefix onto a system: value forms through
//                   sc[D], notes, grouped requests, host inputs and records
//   ScopedDomain<F> a domain through a scope

#ifndef PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_SYSTEM_CORE_H_
#define PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_SYSTEM_CORE_H_

#include <cstddef>
#include <cstdint>
#include <functional>
#include <map>
#include <memory>
#include <optional>
#include <string>
#include <tuple>
#include <type_traits>
#include <utility>
#include <vector>

#include "gordiehowe/certify.h"
#include "gordiehowe/core.h"
#include "gordiehowe/expr.h"
#include "gordiehowe/ops/operators.h"

namespace proofs::gordiehowe {

template <class F>
class Domain;
template <class F>
class ScopedDomain;
class Scope;
class SystemCore;
namespace compiler {
class Lowering;
}  // namespace compiler
namespace internal {
struct RelationAccess;
}  // namespace internal
template <class St, class W>
class Relation;

// What one lowering reports: its report lines (one per realization, the
// numbers it computed) and its digest bytes.
struct LoweringSummary {
  std::vector<std::string> report;
  std::vector<uint8_t> descr;
};

// The width of the integers assert_same_bits compares in its integer form.
struct BitWidth {
  size_t bits;
};

// A gadget's named integers, as note records them (PlanRecords::Gadget).
using NoteValues = std::vector<std::pair<std::string, SignedInt>>;
// The degree a challenge's bad event is charged with (note "charge"). For a
// challenge of the source program (a library function's) it is only
// reported: the compile report lists it beside the degree bound compile()
// computes from the predicates, which the plan carries. A core
// realization's lowering declares its challenge's degree bound this way.
template <class F, class T, class P>
struct ChallengeCharge {
  Ref<F, T, P> challenge;
  Bound degree = 0;
};
template <class F, class T, class P>
ChallengeCharge(Ref<F, T, P>, Bound) -> ChallengeCharge<F, T, P>;

// ---------------------------------------------------------- DomainCore --

// What the system reads of a domain without its field type: its index and
// name, its field (index in the field set, object and tag), where its
// subfields live, and the declarations compile() checks.
class DomainCore {
 public:
  virtual ~DomainCore() = default;
  int index = -1;
  std::string name;
  // The domain's field: its index in the system's field set, the field
  // object, and field_tag<F>() of its type.
  size_t field_id = 0;
  const void *fobj = nullptr;
  const void *ftag = nullptr;
  bool has_subfield = false;
  // DomainProfile::no_bit_packing, the test-only ablation: no bit packing.
  bool no_bit_packing = false;
  Space prime = Space::kField;
  // kPrime resolves to wherever the domain's prime subfield lives.
  Space resolve(Space s) const { return s == Space::kPrime ? prime : s; }
  // Each constraint the application declared: its name and the nodes it
  // reads directly (the challenge-use check in compile()).
  virtual std::vector<std::pair<std::string, std::vector<size_t>>>
  constraint_reads() const = 0;
  // Each predicate's name and (challenge, deg_c) for each challenge it
  // reads (the degree bounds in compile()).
  virtual std::vector<
      std::pair<std::string, std::vector<std::pair<size_t, size_t>>>>
  predicate_degrees() const = 0;
  // Nodes whose storage a lowering bound to a view (no cell).
  virtual std::vector<size_t> bound_ids() const = 0;
  // Range requests not yet lowered.
  virtual size_t pending_requests() const = 0;
  // The realization of the range request named NM, null when the domain
  // has none; LOWERED tells whether the lowering selected it.
  virtual const RangeRealization *find_request(const std::string &nm,
                                               bool &lowered) const = 0;
  // The name of the domain's field (DomainProfile::field_name).
  virtual std::string field_name() const = 0;
  // An unnamed view node over SRC (values of this domain), for the view
  // operations of a handle.
  virtual size_t wire(const ViewSource &src) = 0;
};

// An assert_mod declaration of a domain of field F (Scope::assert_mod),
// lowered at compile by mod.h. For M >= 2 the sides are the affine LHS and
// RHS. For M = 0, the integer equality, they are any expressions L and R
// (products and conv included), lowered to assert_zero(l - r) under PIN
// once interval propagation keeps both sides in [0, p).
template <class F>
struct ModDecl {
  Lin<F> lhs, rhs;
  Bound m = 0;
  std::string name;
  ExprPtr<F> l, r;
  std::shared_ptr<Placement> pin;
};

class LoweringContext;

// ---------------------------------------------------------- SystemCore --

// A system without its field set: the graph of its nodes, its domains, and
// the declarations its lowerings take at compile. ConstraintSystem derives
// from it, adding the generators' types and the domains' compilers.
class SystemCore {
 public:
  virtual ~SystemCore() = default;
  SystemCore(const SystemCore &) = delete;
  SystemCore &operator=(const SystemCore &) = delete;

  const std::string &system_name() const { return name_; }
  // The nodes of the system.
  const Graph &graph() const { return *graph_; }
  // The domain of field F, or null when the system has none.
  template <class F>
  Domain<F> *domain_of() const {
    for (DomainCore *d : cores_)
      if (d->ftag == field_tag<F>()) return dynamic_cast<Domain<F> *>(d);
    return nullptr;
  }
  // The domain of index I, of field F; a domain of another field is a
  // CompileError naming WHAT.
  template <class F>
  Domain<F> &domain_at(size_t i, const std::string &what) const {
    auto *d = dynamic_cast<Domain<F> *>(cores_.at(i));
    if (d == nullptr) fail(what + ": a domain of another field");
    return *d;
  }

  // The profile this system was lowered under (compile(System&, profile)),
  // and each lowering's name and summary.
  const std::optional<CompileProfile> &lowered_with() const { return profile_; }
  const std::vector<std::pair<std::string, LoweringSummary>> &summaries()
      const {
    return summaries_;
  }
  // Equalities (and assert_mod declarations and grouped requests) not yet
  // lowered.
  size_t pending_equalities() const {
    size_t k = 0;
    for (const auto &e : equalities_) k += e.lowered ? 0 : 1;
    for (const auto &e : mods_) k += e.lowered ? 0 : 1;
    for (const auto &e : grouped_) k += e.lowered ? 0 : 1;
    return k;
  }
  const std::string &lowering_failure() const { return failure_; }
  // The name of the lowering running now ("" outside compile).
  const std::string &lowering() const { return lowering_; }
  // The root scope.
  const Scope &root() const { return *root_; }
  // The node holding the statement's canonical bytes (relation.h), when
  // the system is compiled from a Statement struct: a Bytes statement
  // named "statement", declared where the relation first reads the
  // statement (or after the relation, when it never does), in the field of
  // the system's first binary domain, else of its first domain. SIZE_MAX
  // for a system without a Statement struct.
  size_t statement_node() {
    if (statement_node_ == SIZE_MAX && statement_bytes_ != SIZE_MAX)
      statement_node_ = declare_statement(statement_bytes_);
    return statement_node_;
  }
  // The values of the constant node ID, of field F (a constant's generator
  // reads nothing).
  template <class F>
  std::vector<typename F::Elt> constant_values(size_t id) const {
    const auto p = constant_elements(id, field_tag<F>());
    return *static_cast<const std::vector<typename F::Elt> *>(p.get());
  }

 protected:
  // The values of the constant node ID as a std::vector of its field's
  // elements; a field whose tag is not TAG is a CompileError.
  virtual std::shared_ptr<const void> constant_elements(
      size_t id, const void *tag) const = 0;
  // Declares the statement's Bytes node of N bytes (statement_node).
  virtual size_t declare_statement(size_t n) = 0;
  // Sets the codec of the statement node ID (relation.h's Input::check).
  virtual void statement_codec(
      size_t id, std::function<long(const std::vector<uint8_t> &)> accepts) = 0;
  friend class Scope;
  friend class compiler::Lowering;
  template <class>
  friend class Domain;

  // The domains in declaration order (index order), for the compiler
  // (Lowering::domains). Library code finds a value's domain from its
  // handle.
  const std::vector<DomainCore *> &domain_list() const { return cores_; }

  // The derived system sets graph_ and root_ once its members exist.
  explicit SystemCore(std::string name) : name_(std::move(name)) {}

  // A node with no generator (a host input, a pad, a public message).
  virtual size_t add_plain(Node nd) = 0;
  Graph &mutable_graph() { return *graph_; }

  // A cross-field equality: the nodes of its two sides, lowered by the MAC
  // lowering (mac.h) with the equalities of the same domain pair and phase.
  struct PendingEquality {
    size_t x = 0, y = 0;
    bool lowered = false;
  };
  // An assert_mod of domain DOMAIN: DECL is its ModDecl<F>, F the domain's
  // field. ZERO marks the modulus 0 (the integer equality).
  struct PendingMod {
    int domain = -1;
    std::shared_ptr<const void> decl;
    bool zero = false;
    bool lowered = false;
  };
  // A request of Scope::defer.
  struct PendingGroup {
    std::string key;
    std::shared_ptr<const void> request;
    std::function<void(LoweringContext &,
                       const std::vector<std::shared_ptr<const void>> &)>
        lower;
    bool lowered = false;
  };

  std::string name_;
  Graph *graph_ = nullptr;
  const Scope *root_ = nullptr;
  std::vector<DomainCore *> cores_;
  std::vector<PendingEquality> equalities_;
  std::vector<PendingMod> mods_;
  std::vector<PendingGroup> grouped_;
  std::optional<CompileProfile> profile_;
  std::vector<std::pair<std::string, LoweringSummary>> summaries_;
  std::string failure_;
  std::string lowering_;
  // The statement's size in bytes when a Statement struct declares it
  // (SIZE_MAX: none), and its node once the first domain exists.
  size_t statement_bytes_ = SIZE_MAX;
  size_t statement_node_ = SIZE_MAX;
  // The checks of the statement's members (Input::check): each a byte
  // range of the statement and a predicate, true when the range is well
  // formed.
  struct StatementCheck {
    size_t offset = 0, len = 0;
    std::function<bool(const std::vector<uint8_t> &)> pred;
  };
  std::shared_ptr<std::vector<StatementCheck>> statement_checks_ =
      std::make_shared<std::vector<StatementCheck>>();
  template <class, class>
  friend class Relation;
  friend struct internal::RelationAccess;
};

// What a grouped lowering (Scope::defer) reads: the system's root scope and
// core, the profile, the phases of the graph so far, the summary it fills
// and the plan records. ConstraintSystemBuilder is one.
class LoweringContext {
 public:
  virtual ~LoweringContext() = default;
  virtual const Scope &scope() const = 0;
  virtual SystemCore &core() = 0;
  virtual const CompileProfile &profile() const = 0;
  virtual LoweringSummary &summary() = 0;
  // Inferred phases of every node declared so far.
  virtual std::vector<size_t> phases() const = 0;
  virtual PlanRecords &records() = 0;
};

// The name of a declaration: NAME in the scope of prefix PREFIX (empty at
// the root). A string names it at the root, sc.name(nm) in the scope sc,
// and sc.name() leaves it unnamed in sc (its default name carries sc's
// prefix).
struct Name {
  std::string prefix, name;
  Name() = default;
  Name(const char *nm) : name(nm) {}                 // NOLINT
  Name(std::string nm) : name(std::move(nm)) {}      // NOLINT
  Name(std::string p, std::string nm)
      : prefix(std::move(p)), name(std::move(nm)) {}
};

namespace internal {
struct Predicates;
}  // namespace internal

// --------------------------------------------------------------- Scope --

// A scope: a handle onto a system that prefixes the names of everything
// declared through it ("sig0.norm.x"), challenge labels among them. The
// system is the root scope (empty prefix); s.scope(name, params) and
// sc.scope(...) nest, and sc[D] is the domain D through the scope. Gadgets
// take a const Scope& and work at top level or nested. The scopes' names
// and parameters enter the system digest, and the compile report groups
// its node lines by scope.
class Scope {
 public:
  // A nested scope. Its name and parameters (computes(...)) enter the
  // digest; a scope of an existing name is a CompileError.
  [[nodiscard]] Scope scope(std::string nm,
                            const Computes &params = Computes{}) const {
    const std::string full = scoped(nm);
    Graph &g = sys_->mutable_graph();
    for (const auto &sc : g.scopes)
      if (sc.first == full) fail("a scope named '" + full + "' exists");
    std::vector<uint8_t> b;
    put_str(b, params.name);
    put_u64(b, params.params.size());
    b.insert(b.end(), params.params.begin(), params.params.end());
    g.scopes.push_back({full, b});
    return Scope(sys_, full);
  }
  // NM within this scope.
  std::string scoped(const std::string &nm) const {
    return prefix_.empty() ? nm : prefix_ + "." + nm;
  }
  const std::string &prefix() const { return prefix_; }
  SystemCore &system() const { return *sys_; }
  // The name NM in this scope (a predicate's trailing argument); empty, an
  // unnamed declaration of this scope.
  Name name(std::string nm = "") const { return Name(prefix_, std::move(nm)); }

  // ------------------------------------------------- system constraints
  // A constraint's domain is inferred from what it reads: the one domain
  // of its field (public values belong to the constraint's domain). A
  // constraint that reads public values only, or a field without a domain,
  // is a CompileError; assert_same_bits is the one constraint across
  // domains (its lowering builds the MAC). The domain-level forms
  // (D.affine, ...) are the same declarations, with the domain given.

  // The affine constraint e = 0, one row per coordinate.
  template <class X, class = std::enable_if_t<kIsExpr<X>>>
  void affine(const std::string &nm, const X &e) const {
    const auto l = as_lin(e);
    infer<ExprField<X>>(l.deps(), nm).affine(scoped(nm), l);
  }
 protected:
  // The predicates' implementations, which the free functions of
  // predicates.h reach through internal::Predicates in the scope their
  // name gives.
  friend struct internal::Predicates;

  // A GKR circuit constraint over the domain its reads give (FN as for
  // Domain::gkr). Compiler tier: lowerings reach it through Lowering::gkr.
  template <class... R, class Fn>
  void gkr(const std::string &nm, Deps<R...> r, Fn fn,
           std::optional<std::vector<uint8_t>> key = std::nullopt) const {
    static_assert(sizeof...(R) >= 1, "gkr: depends on nothing");
    using F = typename std::tuple_element_t<0, std::tuple<R...>>::field_type;
    infer<F>(r.ids(), nm).gkr(scoped(nm), r, std::move(fn), std::move(key));
  }
  template <class F, class Fn>
  void gkr(const std::string &nm, const std::vector<Ref<F>> &r,
           Fn fn) const {
    std::vector<size_t> ids;
    for (const auto &x : r) ids.push_back(x.id);
    infer<F>(ids, nm).gkr(scoped(nm), r, std::move(fn));
  }

  // lhs = rhs (mod M) as integers (mod.h), lowered at compile (values read in
  // [0, p), constants and coefficients in (-p/2, p/2)). M = 0 is the integer
  // equality: LHS and RHS are any expressions of one odd-characteristic domain,
  // products and convolutions included, lowered to assert_zero(lhs - rhs),
  // placed as usual (pin() on the returned predicate fixes it), once interval
  // propagation shows that both sides lie in [0, p) after one common shift;
  // otherwise compilation fails naming the widest term. M >= 2 takes affine
  // sides: the field equality when M is the domain's characteristic, otherwise
  // a quotient with its range requests and no-wrap condition, grouped when LHS
  // is a sum of nonnegative terms whose total reaches p; its lowering realizes
  // it, so the returned predicate has no placement. NM names it (assert_mod.<k>
  // by default).
  template <class X, class Y,
            class = std::enable_if_t<kIsPoly<X> && kIsPoly<Y>>>
  Predicate assert_mod(const X &lhs, const Y &rhs, Bound m,
                       const std::string &nm = "") const {
    static_assert(std::is_same_v<PolyField<X>, PolyField<Y>>,
                  "assert_mod: both sides lie in one field");
    using F = PolyField<X>;
    static_assert(!F::kCharacteristicTwo,
                  "assert_mod: integers mod m exist in odd characteristic");
    const std::string label =
        nm.empty() ? "assert_mod." + std::to_string(sys_->mods_.size()) : nm;
    if (m == 0) return integer_equality(lhs, rhs, label);
    if constexpr (kIsExpr<X> && kIsExpr<Y>) {
      const Lin<F> l = as_lin(lhs), r = as_lin(rhs);
      if (l.n != r.n)
        fail("assert_mod '" + nm + "': the sides' lengths differ");
      std::vector<size_t> ids = l.deps();
      const auto rd = r.deps();
      ids.insert(ids.end(), rd.begin(), rd.end());
      auto &d = infer<F>(ids, label);
      if (sys_->profile_)
        fail("assert_mod '" + scoped(label) + "' declared after the system "
             "was lowered");
      SystemCore::PendingMod pm;
      pm.domain = d.index;
      ModDecl<F> decl;
      decl.lhs = l;
      decl.rhs = r;
      decl.m = m;
      decl.name = scoped(label);
      pm.decl = std::make_shared<const ModDecl<F>>(std::move(decl));
      sys_->mods_.push_back(std::move(pm));
      return Predicate::unplaced("assert_mod (lowered to its own rows)");
    } else {
      fail("assert_mod '" + scoped(label) + "': a modulus m >= 2 takes affine "
           "sides; only m = 0 (the integer equality) takes products");
    }
  }
  // assert_mod(lhs, rhs, 0) under LABEL: the integer equality's
  // declaration, its sides as expressions and a pin.
  template <class X, class Y>
  Predicate integer_equality(const X &lhs, const Y &rhs,
                             const std::string &label) const {
    using F = PolyField<X>;
    const auto l = expr_node(lhs);
    const auto r = expr_node(rhs);
    std::vector<size_t> ids = expr_deps(l);
    const auto rd = expr_deps(r);
    ids.insert(ids.end(), rd.begin(), rd.end());
    auto &d = infer<F>(ids, label);
    if (sys_->profile_)
      fail("assert_int_equal '" + scoped(label) + "' declared after the "
           "system was lowered");
    if (l->n != r->n && l->n != 1 && r->n != 1)
      fail("assert_int_equal '" + scoped(label) + "': the sides' lengths "
           "differ");
    auto pin = std::make_shared<Placement>(Placement::kAuto);
    SystemCore::PendingMod pm;
    pm.domain = d.index;
    pm.zero = true;
    ModDecl<F> decl;
    decl.name = scoped(label);
    decl.l = l;
    decl.r = r;
    decl.pin = pin;
    pm.decl = std::make_shared<const ModDecl<F>>(std::move(decl));
    sys_->mods_.push_back(std::move(pm));
    return Predicate(pin);
  }
  // The same with an integer right side (a constant node NM.rhs).
  template <class X, class = std::enable_if_t<kIsExpr<X>>>
  Predicate assert_mod(const X &lhs, uint64_t rhs, Bound m,
                       const std::string &nm = "") const {
    using F = ExprField<X>;
    const Lin<F> l = as_lin(lhs);
    const std::string label =
        nm.empty() ? "assert_mod." + std::to_string(sys_->mods_.size()) : nm;
    const auto c = constant_in(
        domain_for<F>(label), label + ".rhs",
        std::vector<typename F::Elt>(l.n, l.f->of_scalar(rhs)));
    return assert_mod(l, c, m, label);
  }

  // Range requests (Domain::assert_range).
  template <class X, class = std::enable_if_t<kIsExpr<X>>>
  RangeHandle<ExprField<X>> assert_range(const X &v, Bound n,
                                         const std::string &nm = "") const {
    const auto l = as_lin(v);
    return infer<ExprField<X>>(l.deps(), nm).assert_range(l, n, scoped_opt(nm));
  }
  template <class X, class = std::enable_if_t<kIsExpr<X>>>
  RangeHandle<ExprField<X>> assert_range(const X &v, Bound n, MaxBound m,
                                         const std::string &nm = "") const {
    const auto l = as_lin(v);
    return infer<ExprField<X>>(l.deps(), nm)
        .assert_range(l, n, m, scoped_opt(nm));
  }
  template <class X, class = std::enable_if_t<kIsExpr<X>>>
  RangeHandle<ExprField<X>> assert_range(const X &v, Bound n, Slack s,
                                         const std::string &nm = "") const {
    const auto l = as_lin(v);
    return infer<ExprField<X>>(l.deps(), nm)
        .assert_range(l, n, s, scoped_opt(nm));
  }
  template <class X, class = std::enable_if_t<kIsExpr<X>>>
  RangeHandle<ExprField<X>> assert_range_implied(const X &v, Bound n,
                                                 MaxBound m,
                                                 const std::string &nm) const {
    const auto l = as_lin(v);
    return infer<ExprField<X>>(l.deps(), nm)
        .assert_range_implied(l, n, m, scoped(nm));
  }
  // E = 0 at every coordinate, for any expression of handles, constants,
  // affine expressions, products and builders (expr.h); the domain places
  // it when it compiles (Domain::assert_zero, Placement). NM names it
  // (assert_zero.<k> by default).
  template <class X, class = std::enable_if_t<kIsPoly<X>>>
  Predicate assert_zero(const X &e, const std::string &nm = "") const {
    const auto x = as_expr(e);
    auto &d = infer<PolyField<X>>(expr_deps(x.node),
                                  nm.empty() ? std::string("assert_zero") : nm);
    return d.assert_zero(pred_name(d, nm, "assert_zero"), x);
  }
  // B = 1 at every coordinate of the Bit expression B.
  template <class X, class = std::enable_if_t<kIsPoly<X>>>
  Predicate assert_true(const X &b, const std::string &nm = "") const {
    static_assert(is_bit_v<PolyType<X>>,
                  "assert_true: the expression is a Bit (a Bit handle, a "
                  "gate or a builder)");
    const auto x = as_expr(b);
    auto &d = infer<PolyField<X>>(expr_deps(x.node),
                                  nm.empty() ? std::string("assert_true") : nm);
    return d.assert_true(pred_name(d, nm, "assert_true"), x);
  }
  // Range requests on any expression: an affine one is read as it is (its
  // constants as a constant node); otherwise an advice value equal to the
  // expression carries the request, its definition a predicate.
  template <class F, class T>
  RangeHandle<F> assert_range(const Expr<F, T> &v, Bound n,
                              const std::string &nm = "") const {
    return assert_range(range_value(v, nm), n, nm);
  }
  template <class F, class T>
  RangeHandle<F> assert_range(const Expr<F, T> &v, Bound n, MaxBound m,
                              const std::string &nm = "") const {
    return assert_range(range_value(v, nm), n, m, nm);
  }
  template <class F, class T>
  RangeHandle<F> assert_range(const Expr<F, T> &v, Bound n, Slack s,
                              const std::string &nm = "") const {
    return assert_range(range_value(v, nm), n, s, nm);
  }
  template <class F, class T>
  RangeHandle<F> assert_range_implied(const Expr<F, T> &v, Bound n, MaxBound m,
                                      const std::string &nm) const {
    return assert_range_implied(range_value(v, nm), n, m, nm);
  }
 public:
  // Elementwise a * b = c on committed Field cells.
  template <class F>
  void quadratic(Ref<F, Field, Committed> a, Ref<F, Field, Committed> b,
                 Ref<F, Field, Committed> c) const {
    infer<F>({a.id, b.id, c.id}, "quadratic").quadratic(a, b, c);
  }
  // A batched relation (Domain::batch) over TABLES: a relation tag over a
  // BitOperandMap (bit operands, characteristic 2), or a FieldRelation over
  // a FieldOperandMap (field operands, any characteristic).
  template <class F, class Rel, class Map>
  void batch(const std::string &nm,
             std::vector<Ref<F, Subfield<>, Committed>> tables, Rel rel,
             std::shared_ptr<const Map> map,
             unsigned width = Domain<F>::template default_batch_width<Map>())
      const {
    batch<F, Designated, Rel, Map>(nm, std::move(tables), std::move(rel), map,
                                   width);
  }
  template <class F, class Sb, class Rel, class Map>
  void batch(const std::string &nm,
             std::vector<Ref<F, Subfield<Sb>, Committed>> tables, Rel rel,
             std::shared_ptr<const Map> map,
             unsigned width = Domain<F>::template default_batch_width<Map>())
      const {
    std::vector<size_t> ids;
    for (const auto &t : tables) ids.push_back(t.id);
    infer<F>(ids, nm).batch(scoped(nm), std::move(tables), std::move(rel),
                            map, width);
  }
  // Several field relations merged into one zerocheck (Domain::batch).
  template <class F, class Sb>
  void batch(const std::string &nm,
             std::vector<Ref<F, Subfield<Sb>, Committed>> tables,
             std::vector<compiler::FieldBatchPart<NonDeduced<F>>> parts,
             unsigned width = 4) const {
    std::vector<size_t> ids;
    for (const auto &t : tables) ids.push_back(t.id);
    infer<F>(ids, nm).batch(scoped(nm), std::move(tables), std::move(parts),
                            width);
  }

  // Domain D through this scope: its declarations' names are prefixed.
  template <class F>
  ScopedDomain<F> operator[](Domain<F> &d) const {
    return ScopedDomain<F>(d, *this);
  }

  // ------------------------------------------------------------ metadata
  // note(kind, name, params[, domain]): plan-export metadata a library
  // function records (PlanRecords) under NAME in this scope. A note states
  // nothing about the relation and enters no digest; a certify note's
  // marker node is the one exception (below). PARAMS is one of:
  //   NoteValues           a gadget's named integers (PlanRecords::Gadget of
  //                        KIND), with DOMAIN its domain (a domain, or a
  //                        handle or expression of the domain's field;
  //                        none for a statement value);
  //   Condition            KIND "certify" (certify.h), with DOMAIN a domain,
  //                        or a handle or expression of its field:
  //                        the condition is checked here, a CompileError
  //                        naming both sides' values when it fails, and
  //                        recorded both as a Gadget and as a constant node
  //                        of the domain's field with no coordinates, named
  //                        certify:<name> [<condition>], which enters the
  //                        digest;
  //   PlanRecords::Permutation, Selection, SampleInBall or
  //   FilteredPermutation  KIND "permutation", "selection", "sample-in-ball"
  //                        or "filtered-permutation": the record, named NAME;
  //   ChallengeCharge      KIND "charge": the degree a challenge's bad event
  //                        is charged with, and NAME the library function
  //                        that drew it (the compile report's by=);
  //   a challenge handle   KIND "origin": NAME is the library function that
  //                        drew the challenge.
  void note(const std::string &kind, const std::string &name,
            NoteValues params) const {
    gadget_note(kind, name, std::move(params), std::string());
  }
  template <class D>
  void note(const std::string &kind, const std::string &name,
            NoteValues params, const D &domain) const {
    gadget_note(kind, name, std::move(params), note_domain(domain, name).name);
  }
  template <class F>
  void note(const std::string &kind, const std::string &name,
            const Condition &c, const Domain<F> &d) const {
    if (kind != "certify")
      fail("note '" + scoped(name) + "': a Condition is a certify note");
    if (!c.holds)
      fail("certify '" + scoped(name) + "': " + c.text() + " does not hold");
    PlanRecords::Gadget rec;
    rec.name = scoped(name);
    rec.kind = "certify";
    rec.domain = d.name;
    // The sides' Bound bits; the plan export reads them back as nats.
    rec.params = {{"lhs", static_cast<SignedInt>(c.lhs.value)},
                  {"rhs", static_cast<SignedInt>(c.rhs.value)},
                  {"op", c.op == "<" ? 0 : c.op == "<=" ? 1 : 2}};
    records().gadgets.push_back(rec);
    (void)constant_in(d, "certify:" + name + " [" + c.text() + "]",
                      std::vector<typename F::Elt>{});
  }
  template <class X, class = std::enable_if_t<kIsPoly<X>>>
  void note(const std::string &kind, const std::string &name,
            const Condition &c, const X &x) const {
    note(kind, name, c, note_domain(x, name));
  }
  void note(const std::string &kind, const std::string &name,
            PlanRecords::Permutation rec) const {
    note_kind(kind, "permutation", name);
    rec.name = scoped(name);
    records().permutations.push_back(std::move(rec));
  }
  void note(const std::string &kind, const std::string &name,
            PlanRecords::Selection rec) const {
    note_kind(kind, "selection", name);
    rec.name = scoped(name);
    records().selections.push_back(std::move(rec));
  }
  void note(const std::string &kind, const std::string &name,
            PlanRecords::SampleInBall rec) const {
    note_kind(kind, "sample-in-ball", name);
    rec.name = scoped(name);
    records().sample_in_balls.push_back(std::move(rec));
  }
  void note(const std::string &kind, const std::string &name,
            PlanRecords::FilteredPermutation rec) const {
    note_kind(kind, "filtered-permutation", name);
    rec.name = scoped(name);
    records().filtered_permutations.push_back(std::move(rec));
  }
  template <class F, class T, class P>
  void note(const std::string &kind, const std::string &name,
            ChallengeCharge<F, T, P> c) const {
    note_kind(kind, "charge", name);
    Node &n = challenge_node(name, c.challenge.id);
    n.origin = name;
    records().charges.push_back({n.name, c.degree});
  }
  template <class F, class T, class P>
  void note(const std::string &kind, const std::string &name,
            Ref<F, T, P> challenge) const {
    note_kind(kind, "origin", name);
    challenge_node(name, challenge.id).origin = name;
  }

  // A request that compile() lowers together with the other requests of
  // its KEY, before the equality, mod and range lowerings: LOWER receives
  // the LoweringContext and every request of the key, in declaration order
  // (the first request's LOWER runs). A gadget whose uses share one
  // argument declares through it, as lookups into one public table do
  // (table.h).
  template <class Req, class Lower>
  void defer(const std::string &key, Req request, Lower lower) const {
    SystemCore::PendingGroup g;
    g.key = key;
    g.request = std::make_shared<const Req>(std::move(request));
    g.lower = [lower](LoweringContext &b,
                      const std::vector<std::shared_ptr<const void>> &rs) {
      std::vector<const Req *> typed;
      for (const auto &r : rs) typed.push_back(static_cast<const Req *>(r.get()));
      lower(b, typed);
    };
    sys_->grouped_.push_back(std::move(g));
  }

  // A per-proof input of N_BYTES bytes that generators read and nothing
  // commits (the uncommitted counterpart of a private input): ML-DSA's c~,
  // which the generators need and the circuit recomputes. The prover sets
  // it through the Assignment. It is not a value handle, so a constraint,
  // view, test or public computation that reads it is a C++ compile error.
  HostInput host_input(std::string nm, size_t n_bytes) const {
    Node nd;
    nd.kind = Kind::kHostInput;
    nd.name = scoped(nm);
    nd.n = n_bytes;
    return HostInput{sys_->add_plain(std::move(nd)), n_bytes};
  }

  // A record generator: one closure FN that fills several declared slots,
  // possibly in several domains (D.slot(T{}, name, shape), and
  // D.nat_slot(T{}, ...) for canonical integers), from the values DEPENDS_ON
  // lists. FN takes one argument per depends_on entry (as advice's vector
  // form: a Tensor, or a host input's bytes), then one std::vector& per
  // slot, sized to the slot, of the slot's field elements or (nat slots)
  // NatInt. It runs once per proof, and each slot is an advice value of its
  // domain. Returns the slots' handles, in order.
  template <class... R, class Fn, class... Sl>
  std::tuple<typename Sl::Handle...> advice_record(Deps<R...> deps, Fn fn,
                                                   Sl... slots) const {
    static_assert(sizeof...(Sl) >= 1, "advice_record: no slot");
    static_assert(std::is_invocable_v<const Fn &, const RecordArg<R> &...,
                                      typename Sl::Out &...>,
                  "advice_record: the closure takes one argument per depends_on "
                  "entry (a Tensor, or a host input's bytes), then one "
                  "std::vector& per slot (the slot's field elements, or "
                  "NatInt for a nat slot)");
    const auto ids = deps.ids();
    auto refs = deps.refs;
    const std::vector<std::string> names = {slots.name...};
    const std::vector<size_t> sizes = {slots.shape.size()...};
    auto domains = std::make_tuple(slots.d...);
    auto run = std::make_shared<std::function<
        std::vector<std::shared_ptr<void>>(const ValueReader &)>>(
        [fn, refs, names, sizes, domains](const ValueReader &v) {
          std::tuple<typename Sl::Out...> out;
          std::apply(
              [&](auto &...o) {
                size_t k = 0;
                ((o.resize(sizes[k++])), ...);
              },
              out);
          std::apply(
              [&](const auto &...r) {
                std::apply(
                    [&](auto &...o) { fn(record_arg(v, r)..., o...); }, out);
              },
              refs);
          return record_values<Sl...>(out, domains, names,
                                      std::index_sequence_for<Sl...>{});
        });
    return add_slots(run, ids, std::index_sequence_for<Sl...>{}, slots...);
  }

 protected:
  // ---------------------------------------------------------- equalities
  // x = y, coordinate by coordinate. In one field it is assert_zero(x - y)
  // for any handles and expressions, which the domain places
  // (Domain::assert_zero); pin() on the returned predicate fixes the
  // placement. Across a binary and an odd field, or two odd fields, it is
  // assert_same_bits(x, y).
  template <class X, class Y,
            class = std::enable_if_t<kIsPoly<X> && kIsPoly<Y> &&
                                     std::is_same_v<PolyField<X>, PolyField<Y>>>>
  Predicate assert_equal(const X &x, const Y &y,
                         const std::string &nm = "") const {
    return assert_zero(x - y, nm);
  }
  template <class F1, class T1, class P1, class F2, class T2, class P2,
            class = std::enable_if_t<!std::is_same_v<F1, F2>>>
  void assert_equal(Ref<F1, T1, P1> x, Ref<F2, T2, P2> y,
                    const std::string & = "") const {
    assert_same_bits(x, y);
  }

  // The same bit string is committed in two fields, a binary field (x_H)
  // and an odd one (x_A), or two odd fields, coordinate by coordinate: Bit
  // values on both sides, merged with the system's other such equalities
  // between the same two domains into one polynomial MAC (mac.h,
  // lower_equality). Between two odd fields the MAC lies in the binary
  // field the compile profile names (CompileProfile::security), which no
  // domain hosts. The arguments come in
  // either order. A typed side that is not Bit, two binary fields, one
  // field, or an odd side that is CircuitOnly (the MAC's rows read it in
  // affine rows) is a C++ compile error.
  template <class F1, class T1, class P1, class F2, class T2, class P2>
  void assert_same_bits(Ref<F1, T1, P1> xt, Ref<F2, T2, P2> yt) const {
    static_assert(!std::is_same_v<F1, F2>,
                  "assert_same_bits: the MAC equality relates two fields; "
                  "in one field, use assert_equal");
    static_assert(!(F1::kCharacteristicTwo && F2::kCharacteristicTwo),
                  "assert_same_bits: the MAC equality needs an "
                  "odd-characteristic field on at least one side");
    static_assert((is_bit_v<T1> || is_any_type_v<T1>) &&
                      (is_bit_v<T2> || is_any_type_v<T2>),
                  "assert_same_bits: the MAC equality compares Bit values; "
                  "pass integer words with a BitWidth");
    static_assert(!((!F1::kCharacteristicTwo &&
                     std::is_same_v<P1, CircuitOnly>) ||
                    (!F2::kCharacteristicTwo &&
                     std::is_same_v<P2, CircuitOnly>)),
                  "assert_same_bits: the MAC's rows read the odd side in "
                  "affine rows, which read no bit view");
    SystemCore::PendingEquality e;
    e.x = xt.id;
    e.y = yt.id;
    sys_->equalities_.push_back(std::move(e));
  }
  // The integer form: each side holds integers of W.bits bits, either as
  // Bit values (W.bits per integer, least significant first) or as
  // integer-valued Subfield words, one integer per word. A binary side's
  // words are read through their bit view (polynomial-basis coordinates,
  // the high ones zero); an odd side's words are decomposed into W.bits Bit
  // cells NM.bits, whose Boolean checks the placement rule places, with
  // x = bits.from_digits(2). The integers' bits are then the same.
  template <class F1, class T1, class P1, class F2, class T2, class P2>
  void assert_same_bits(Ref<F1, T1, P1> x, Ref<F2, T2, P2> y, BitWidth w,
                        const std::string &nm = "same_bits") const {
    assert_same_bits(integer_bits(x, w, nm + ".x"),
                     integer_bits(y, w, nm + ".y"));
  }

 protected:
  friend class SystemCore;
  friend class compiler::Lowering;
  template <class>
  friend class Domain;
  template <class, class...>
  friend class BasicConstraintSystem;

  explicit Scope(SystemCore *s) : sys_(s) {}
  Scope(SystemCore *s, std::string prefix)
      : sys_(s), prefix_(std::move(prefix)) {}

  PlanRecords &records() const { return sys_->mutable_graph().records; }

  // The masked message t = x + P of the late value x, readable as public
  // (Lowering::public_message).
  template <class F, class T, class P>
  Ref<F, T, Public> public_message(Ref<F, T, P> x) const {
    const Node &xn = sys_->graph().nodes.at(x.id);
    const Shape sh(x.dims());
    Node nd;
    nd.kind = Kind::kPublicMessage;
    nd.name = scoped("msg(" + xn.name + ")");
    nd.field = xn.field;
    nd.fobj = xn.fobj;
    nd.n = sh.size();
    nd.shape = sh.dims;
    nd.deps = {x.id};
    const size_t id = sys_->add_plain(std::move(nd));
    return Ref<F, T, Public>(id, sh.size(), x.f, &sys_->mutable_graph(),
                             sh.dims);
  }
  // A constant of domain D's field named NM in this scope (D.constant).
  template <class F>
  Ref<F, Field, Public> constant_in(const Domain<F> &d, const std::string &nm,
                                    std::vector<typename F::Elt> v) const {
    return d.constant_in(*this, nm, std::move(v));
  }
  // The domain of field F, for a declaration named NM that reads no node
  // (a constant of the field).
  template <class F>
  Domain<F> &domain_for(const std::string &what) const {
    Domain<F> *fd = sys_->template domain_of<F>();
    if (fd == nullptr)
      fail("constraint '" + scoped(what) + "': the system has no domain of "
           "its field");
    return *fd;
  }
  // X's integers of W.bits bits as Bit values [n, W.bits] (integer form of
  // assert_same_bits). NM names what it declares.
  template <class F, class T, class P>
  auto integer_bits(Ref<F, T, P> x, BitWidth w, const std::string &nm) const {
    const size_t k = w.bits;
    if (k == 0 || k > 63)
      fail("assert_same_bits '" + nm + "': integers of " + std::to_string(k) +
           " bits; 1 to 63 are supported");
    if constexpr (is_bit_v<T>) {
      if (x.n % k != 0)
        fail("assert_same_bits '" + nm + "': " + std::to_string(x.n) +
             " bits are no whole integers of " + std::to_string(k) + " bits");
      return Ref<F, Bit, P>(x).reshape({x.n / k, k});
    } else if constexpr (F::kCharacteristicTwo) {
      static_assert(is_subfield_v<T> && std::is_same_v<P, Committed>,
                    "assert_same_bits: a binary side's integers are Bit "
                    "values or committed Subfield words");
      auto &d = infer<F>({x.id}, nm);
      const auto all = (*this)[d].bits(nm + ".view", x);
      const size_t deg = all.n / x.n;
      if (k > deg)
        fail("assert_same_bits '" + nm + "': " + std::to_string(k) +
             "-bit integers in words of " + std::to_string(deg) + " bits");
      const auto rows = all.reshape({x.n, deg});
      if (k < deg) assert_zero(rows.slice(k, deg, 1), nm + ".high");
      return rows.slice(0, k, 1);
    } else {
      static_assert(is_subfield_v<T> || is_field_v<T>,
                    "assert_same_bits: an odd side's integers are Bit values "
                    "or field words");
      auto &d = infer<F>({x.id}, nm);
      if ((Bound(1) << k) > field_characteristic(*x.f))
        fail("assert_same_bits '" + nm + "': " + std::to_string(k) +
             "-bit integers do not all lie below the characteristic of "
             "domain " + d.name);
      const F *pf = x.f;
      const auto bits = (*this)[d].priv(
          Bit{}, nm + ".bits", Shape{x.n, k}, depends_on(x),
          [pf, k](const std::vector<typename F::Elt> &v) {
            std::vector<typename F::Elt> out;
            out.reserve(v.size() * k);
            uint64_t ok = 1;
            for (const auto &e : v) {
              const NatInt u = nat_of_ct(*pf, e, ok);
              for (size_t j = 0; j < k; ++j)
                out.push_back(ct::bit_elt(*pf, uint64_t(u >> j) & 1));
            }
            if (!ok)
              throw std::runtime_error("assert_same_bits: a word is no "
                                       "canonical integer");
            return out;
          });
      assert_zero(x - bits.from_digits(2), nm + ".digits");
      return bits;
    }
  }
  void note_kind(const std::string &kind, const char *want,
                 const std::string &name) const {
    if (kind != want)
      fail("note '" + scoped(name) + "': a " + std::string(want) +
           " record is noted as kind \"" + want + "\", not \"" + kind + "\"");
  }
  Node &challenge_node(const std::string &name, size_t id) const {
    Node &n = sys_->mutable_graph().nodes.at(id);
    if (n.kind != Kind::kChallenge)
      fail("note '" + name + "': '" + n.name + "' is not a challenge");
    return n;
  }
  // A note's domain: D itself, or the domain of the field of the handle or
  // expression D.
  template <class D>
  decltype(auto) note_domain(const D &d, const std::string &name) const {
    if constexpr (kIsPoly<D>) {
      return infer<PolyField<D>>(expr_deps(as_expr(d).node),
                                 "note '" + name + "'");
    } else {
      return (d);
    }
  }
  void gadget_note(const std::string &kind, const std::string &name,
                   NoteValues params, std::string domain) const {
    if (kind == "certify")
      fail("note '" + scoped(name) + "': a certify note takes a Condition");
    PlanRecords::Gadget rec;
    rec.name = scoped(name);
    rec.kind = kind;
    rec.domain = std::move(domain);
    rec.params = std::move(params);
    records().gadgets.push_back(std::move(rec));
  }
  std::string scoped_opt(const std::string &nm) const {
    return nm.empty() ? nm : scoped(nm);
  }
  template <class D>
  std::string pred_name(const D &d, const std::string &nm,
                        const char *kind) const {
    return nm.empty() ? scoped(std::string(kind) + "." +
                               std::to_string(d.predicates().size()))
                      : scoped(nm);
  }
  // The affine expression a range request on X reads (assert_range).
  template <class F, class T>
  Lin<F> range_value(const Expr<F, T> &x, const std::string &nm) const {
    const auto &N = sys_->graph().nodes;
    auto &d = infer<F>(expr_deps(x.node),
                       nm.empty() ? std::string("assert_range") : nm);
    const std::string label =
        nm.empty() ? "range.expr" + std::to_string(N.size()) : nm;
    auto pub = [&](size_t id) { return is_public(N.at(id).kind); };
    auto readable = [&](size_t id) { return !d.circuit_only(id); };
    auto a = affine_form(x.node, pub, readable);
    // Constants through operators of public values have no constant node.
    if (a && a->kc.empty()) {
      const F &f = *x.f();
      bool zero = true;
      for (const auto &c : a->c) zero &= c == f.zero();
      Lin<F> l = a->lin;
      if (!zero) {
        const auto k = constant_in(d, label + ".offset", a->c);
        l = l.terms.empty() ? Lin<F>(k) : l + k;
      }
      if (l.terms.empty())
        fail("assert_range '" + scoped(label) + "': a constant expression");
      return l;
    }
    if (x.node->structured)
      fail("assert_range '" + scoped(label) + "': the expression applies the "
           "structured operator '" + x.node->structured_op +
           "' and is not affine");
    const auto v = d.expr_value(scoped(label + ".value"), x.node);
    assert_zero(Expr<F, Field>(v) - x, label + ".value");
    return Lin<F>(v);
  }
  // The domain of a constraint of field F over the nodes IDS: the field's
  // one domain. A constraint that reads public values only, or a field
  // without a domain, is a CompileError.
  template <class F>
  Domain<F> &infer(const std::vector<size_t> &ids,
                   const std::string &what) const {
    const auto &N = sys_->graph().nodes;
    bool reads = false;
    for (size_t id : ids) reads = reads || N.at(id).domain >= 0;
    if (!reads)
      fail("constraint '" + scoped(what) + "' reads no value of a domain");
    return domain_for<F>(what);
  }

  // A record's dependency argument: a Tensor of a value's elements, or a
  // host input's bytes.
  template <class R>
  using RecordArg = typename DepArg<R>::type;
  template <class R>
  static decltype(auto) record_arg(const ValueReader &v, const R &r) {
    if constexpr (IsBytesArg<R>::value) {
      return dep_bytes(v, r);
    } else {
      return Tensor<typename R::field_type::Elt>(dep_values(v, r), r.dims());
    }
  }
  // The slots' values, each a std::vector of its field's elements (nat
  // slots' integers become elements below p).
  template <class... Sl, class Out, class Doms, size_t... I>
  static std::vector<std::shared_ptr<void>> record_values(
      Out &out, const Doms &doms, const std::vector<std::string> &names,
      std::index_sequence<I...>) {
    std::vector<std::shared_ptr<void>> vals;
    (vals.push_back(record_value<Sl>(std::get<I>(out), *std::get<I>(doms),
                                     names[I])),
     ...);
    return vals;
  }
  template <class Sl, class D>
  static std::shared_ptr<void> record_value(typename Sl::Out &o, const D &d,
                                            const std::string &name) {
    using F = typename Sl::field_type;
    using V = std::vector<typename F::Elt>;
    if constexpr (Sl::kNat) {
      const Bound p = field_characteristic(d.field());
      return std::make_shared<V>(D::elements(d.field(), p, o, name));
    } else {
      return std::make_shared<V>(std::move(o));
    }
  }
  // The slots' handles: slot I reads entry I of RUN's outputs, which run
  // once per proof.
  template <class Run, class... Sl, size_t... I>
  static std::tuple<typename Sl::Handle...> add_slots(
      const Run &run, const std::vector<size_t> &ids,
      std::index_sequence<I...>, const Sl &...slots) {
    return std::tuple<typename Sl::Handle...>{
        slots.d->add_record_slot(slots, ids, slot_eval<Sl>(run, I))...};
  }
  template <class Sl, class Run>
  static auto slot_eval(const Run &run, size_t idx) {
    using V = std::vector<typename Sl::field_type::Elt>;
    return [run, idx](const ValueReader &v) {
      auto &cell = v.records[run.get()];
      if (!cell)
        cell = std::make_shared<std::vector<std::shared_ptr<void>>>((*run)(v));
      const auto &all =
          *std::static_pointer_cast<std::vector<std::shared_ptr<void>>>(cell);
      return *static_cast<const V *>(all.at(idx).get());
    };
  }

  SystemCore *sys_;
  std::string prefix_;
};

namespace internal {

// The free predicates' (predicates.h) access to a scope's implementations:
// the scope of a prefix on a system, and each predicate declared in it.
struct Predicates {
  static Scope at(SystemCore &s, const std::string &prefix) {
    return Scope(&s, prefix);
  }
  template <class X>
  static Predicate zero(const Scope &sc, const X &e, const std::string &nm) {
    return sc.assert_zero(e, nm);
  }
  template <class X>
  static Predicate truth(const Scope &sc, const X &b, const std::string &nm) {
    return sc.assert_true(b, nm);
  }
  template <class... A>
  static auto range(const Scope &sc, A &&...a) {
    return sc.assert_range(std::forward<A>(a)...);
  }
  template <class... A>
  static auto range_implied(const Scope &sc, A &&...a) {
    return sc.assert_range_implied(std::forward<A>(a)...);
  }
  template <class... A>
  static Predicate mod(const Scope &sc, A &&...a) {
    return sc.assert_mod(std::forward<A>(a)...);
  }
  template <class... A>
  static void same_bits(const Scope &sc, A &&...a) {
    sc.assert_same_bits(std::forward<A>(a)...);
  }
};

}  // namespace internal

// A domain through a scope: its declarations' names carry the scope's
// prefix.
template <class F>
class ScopedDomain {
 public:
  using Elt = typename F::Elt;
  ScopedDomain(Domain<F> &d, const Scope &sc) : d_(&d), sc_(&sc) {}
  Domain<F> &domain() const { return *d_; }
  std::string scoped(const std::string &nm) const { return sc_->scoped(nm); }
  const F &field() const { return d_->field(); }
  int index() const { return d_->index; }
  // The value forms (Domain::priv, ...), named in this scope.
  template <class T, class... A>
  auto priv(T t, const std::string &nm, A &&...a) const {
    static_assert(!is_bytes_v<T>, "priv: a value is Bit, Subfield or Field");
    return d_->priv_in(*sc_, t, nm, std::forward<A>(a)...);
  }
  template <class T, class... A>
  auto pub(T t, const std::string &nm, A &&...a) const {
    static_assert(!is_bytes_v<T>,
                  "pub: a value is Bit, Subfield or Field; a byte string is "
                  "pub_bytes");
    return d_->pub_in(*sc_, t, nm, std::forward<A>(a)...);
  }
  template <class... A>
  auto pub_bytes(const std::string &nm, A &&...a) const {
    return d_->pub_in(*sc_, Bytes{}, nm, std::forward<A>(a)...);
  }
  auto constant(const std::string &nm, std::vector<Elt> v) const {
    return d_->constant_in(*sc_, nm, std::move(v));
  }
  template <class... A>
  auto challenge(A &&...a) const {
    return d_->challenge_in(*sc_, std::forward<A>(a)...);
  }
  auto challenge_outside(std::string label, std::vector<size_t> reads,
                         ExcludedSet<F> in_u) const {
    return d_->challenge_outside_in(*sc_, std::move(label), std::move(reads),
                                    std::move(in_u));
  }
  // Domain::priv(nm, e) for an expression E, named in this scope.
  template <class X,
            class = std::enable_if_t<Domain<F>::template kIsExprArg<X>>>
  auto priv(const std::string &nm, const X &e) const {
    return d_->priv(scoped(nm), e);
  }
  // Domain::copy_of(nm, x), the copy named in this scope (predicates.h).
  template <class G, class T, class P>
  Ref<F, Bit, Committed> copy_of(const std::string &nm,
                                 const Ref<G, T, P> &x) const;
  auto derive(const std::string &nm, const Lin<F> &e) const {
    return d_->derive(scoped(nm), e);
  }
  template <class T>
  auto derive(T t, const std::string &nm, const Lin<F> &e) const {
    return d_->derive(t, scoped(nm), e);
  }
  auto bit_from_unchecked(const std::string &nm, const Lin<F> &e) const {
    return d_->bit_from_unchecked(scoped(nm), e);
  }
  template <class T, class P>
  auto bit_from_unchecked(const std::string &nm, const Ref<F, T, P> &e) const {
    return d_->bit_from_unchecked(scoped(nm), Lin<F>(e));
  }
  template <class T>
  auto bit_from_unchecked(const std::string &nm, const Expr<F, T> &e) const {
    return d_->bit_from_unchecked(scoped(nm), e);
  }
  template <class... A>
  auto bits(const std::string &nm, A &&...a) const {
    return d_->bits(scoped(nm), std::forward<A>(a)...);
  }
  template <class T>
  auto slot(T t, const std::string &nm, Shape shape) const {
    return d_->slot(t, scoped(nm), shape);
  }
  template <class T>
  auto nat_slot(T t, const std::string &nm, Shape shape) const {
    return d_->nat_slot(t, scoped(nm), shape);
  }

 private:
  Domain<F> *d_;
  const Scope *sc_;
};

}  // namespace proofs::gordiehowe

#endif  // PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_SYSTEM_CORE_H_
