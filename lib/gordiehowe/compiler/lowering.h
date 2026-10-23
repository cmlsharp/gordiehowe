// Copyright 2026 Chad Sharp and Paul Grubbs
// SPDX-License-Identifier: Apache-2.0

// GordieHowe: the lowering tier:
// pads and the other compiler-internal declarations a lowering reaches
// through Lowering, phase inference, the builder a lowering rewrites the
// system through, and the passes compile() runs (equalities, assert_mod,
// grouped requests, ranges).

#ifndef PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_COMPILER_LOWERING_H_
#define PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_COMPILER_LOWERING_H_

#include <algorithm>
#include <cstddef>
#include <cstdint>
#include <functional>
#include <map>
#include <memory>
#include <optional>
#include <set>
#include <string>
#include <tuple>
#include <utility>
#include <vector>

#include "gordiehowe/core.h"
#include "gordiehowe/domain.h"
#include "gordiehowe/linear.h"
#include "gordiehowe/system_core.h"

namespace proofs::gordiehowe::compiler {

// The cross-domain equality lowering (mac.h).
template <class S, class F1, class F2>
void lower_equality(ConstraintSystemBuilder<S> &b, Ref<F1> x, Ref<F2> y,
                    const std::vector<std::pair<size_t, size_t>> &members,
                    size_t index);
// The modular equality lowering (mod.h), the integer equality (m = 0)
// among its forms.
template <class S, class F>
void lower_assert_mod(ConstraintSystemBuilder<S> &b, int domain,
                      const ModDecl<F> &decl);
// The conv realizations of a domain's predicates (conv.h); whether any
// predicate held a conv.
template <class S, class F>
bool realize_convs(ConstraintSystemBuilder<S> &b, Domain<F> &d);
// The public expressions of a domain's predicates, lifted into public
// values (public_expr.h); whether any predicate held one.
template <class S, class F>
bool lift_public_exprs(ConstraintSystemBuilder<S> &b, Domain<F> &d);

// Library-internal access to pads, for lowerings: a lowering derives from
// Lowering and calls these. Application code holds no pad: it cannot
// declare one, mask a value by one, or copy one. No closure ever receives a
// pad's value: a pad listed as a generator's dependency is a compile error,
// and a pad copy is filled by the core through a declared PadMap.
class Lowering {
 protected:
  template <class Sys, class F>
  static Ref<F, AnyType, Committed> pad(Sys &s, Domain<F> &d, Type space,
                                        size_t n = 1) {
    return s.pad(d, space, n);
  }
  // A pad the core sets to zero (Node::zero_pad): the late value it masks
  // is sent in the clear. Only the per-chunk MAC ablation
  // (CompileProfile::unsound_per_chunk_mac, a measurement control) declares
  // one, for its public tags.
  template <class Sys, class F>
  static Ref<F, AnyType, Committed> zero_pad(Sys &s, Domain<F> &d,
                                             Type space, size_t n = 1) {
    auto p = s.pad(d, space, n);
    d.g_->nodes.at(p.id).zero_pad = true;
    return p;
  }
  // A pad that masks no message (Node::key_pad): uniform prover
  // randomness, drawn with the other pads, that constraints and generators
  // read directly, named NM. Only the per-chunk MAC ablation declares one,
  // for its key shares.
  template <class Sys, class F>
  static Ref<F, AnyType, Committed> key_pad(Sys &s, Domain<F> &d,
                                            std::string nm, Type space,
                                            size_t n = 1) {
    auto p = s.pad(d, space, n);
    Node &nd = d.g_->nodes.at(p.id);
    nd.key_pad = true;
    nd.name = std::move(nm);
    return p;
  }
  template <class F, class T, class P>
  static MaskedBy masked_by(Ref<F, T, P> p) {
    return MaskedBy(static_cast<long>(p.id));
  }
  template <class FD, class FS, class T, class P>
  static Ref<FD, AnyType, Committed> pad_copy(Domain<FD> &d, std::string nm,
                                              Ref<FS, T, P> p,
                                              const PadMap<FS, FD> &map) {
    return d.pad_copy(std::move(nm), p, map);
  }
  // Deferred storage binding: X keeps its kind,
  // dependencies and closure, but has no cell; constraints read VIEW, an
  // affine view of phase-0 digit cells computed from X alone, in its place.
  // compile() checks B1-B5. NOTE is the report line. A view of digits
  // does not preserve Booleanity, and a public or CircuitOnly value has no
  // cell to drop: a typed Bit, Public or CircuitOnly X is a C++ compile
  // error.
  template <class F, class T, class P>
  static void bind_view(Domain<F> &d, Ref<F, T, P> x,
                        const NonDeduced<Lin<F>> &view,
                        std::string note) {
    static_assert(!is_bit_v<T>,
                  "bind_view: a Bit value is not bound (a view of digits "
                  "does not preserve Booleanity)");
    static_assert(std::is_same_v<P, Committed> || std::is_same_v<P, AnyPlace>,
                  "bind_view: only a committed value has a cell to bind");
    d.bind_view(Ref<F>(x), view, std::move(note));
  }
  // Declarations with a pad: priv's forms, and a late value masked by the
  // declared pad MB (masked_by).
  template <class F, class T>
  static Ref<F, T, Committed> priv(Domain<F> &d, T, std::string nm,
                                   Shape shape) {
    return d.declare_input(T{}, std::move(nm), std::move(shape));
  }
  template <class F, class T, class Deps, class Fn>
  static Ref<F, T, Committed> priv(Domain<F> &d, T, std::string nm,
                                   Shape shape, Deps deps, Fn fn,
                                   MaskedBy mb = {}) {
    return d.declare_advice(T{}, std::move(nm), std::move(shape),
                            std::move(deps), std::move(fn), mb);
  }
  // The masked message t = x + P of the late value x, readable as public.
  template <class F, class T, class P>
  static Ref<F, T, Public> public_message(const Scope &s, Ref<F, T, P> x) {
    return s.public_message(x);
  }
  // A batch whose tables grow as it is used (Domain::reserve_batch).
  template <class F>
  static size_t reserve_batch(Domain<F> &d, std::string nm,
                              std::string missing) {
    return d.reserve_batch(std::move(nm), std::move(missing));
  }
  template <class F, class... A>
  static void set_batch(Domain<F> &d, size_t slot, A &&...a) {
    d.set_batch(slot, std::forward<A>(a)...);
  }
  // A domain's range requests and range tables, to lower them.
  template <class F>
  static std::vector<RangeRequest<F>> &requests(Domain<F> &d) {
    return d.requests_;
  }
  template <class F>
  static std::vector<RangeTableStats> &range_tables(Domain<F> &d) {
    return d.range_tables_;
  }
  // The domain's LogUp challenge alpha:<D> (none until a lowering declares
  // it) and the range tables' bound T_max its excluded set reads.
  template <class F>
  static std::optional<Ref<F, Field, Public>> &logup_alpha(Domain<F> &d) {
    return d.logup_alpha_;
  }
  template <class F>
  static const std::shared_ptr<Bound> &logup_tmax(Domain<F> &d) {
    return d.logup_tmax_;
  }
  // Sets the sampler of challenge C of D (Node::sampler).
  template <class F, class T, class P>
  static void set_sampler(Domain<F> &d, const Ref<F, T, P> &c,
                          std::string sampler) {
    d.g_->nodes.at(c.id).sampler = std::move(sampler);
  }
  // The predicate NM, E = 0, under the pin PIN (a lowering's own
  // assert_zero that keeps the pin of the declaration it realizes).
  template <class F>
  static void add_predicate(Domain<F> &d, std::string nm, ExprPtr<F> e,
                            std::shared_ptr<Placement> pin) {
    d.add_predicate(std::move(nm), std::move(e), false, std::move(pin));
  }
  // The number of predicates of D, and the rewrite of predicate K's
  // expression into E (the conv realizations): its circuit entry's reads
  // follow.
  template <class F>
  static size_t predicate_count(const Domain<F> &d) {
    return d.preds_.size();
  }
  template <class F>
  static const ExprPtr<F> &predicate_expr(const Domain<F> &d, size_t k) {
    return d.preds_.at(k).e;
  }
  template <class F>
  static const std::string &predicate_name(const Domain<F> &d, size_t k) {
    return d.preds_.at(k).name;
  }
  // Marks the challenge C of D's field as a core realization's: its degree
  // bound is the one its lowering declares, from the error of the
  // realization's identity, and a lowering's closure may read it (degree
  // bounds, and the check of closures over challenges, in compile()).
  template <class F, class T, class P>
  static void realization(Domain<F> &d, const Ref<F, T, P> &c) {
    Node &n = d.g_->nodes.at(c.id);
    if (n.kind != Kind::kChallenge)
      fail("realization: '" + n.name + "' is not a challenge");
    n.realization = true;
  }
  // The public value NM equal to the public expression E, which both
  // parties evaluate outside the circuit (Domain::public_expr).
  template <class F>
  static Ref<F, Field, Public> public_value(Domain<F> &d, std::string nm,
                                            const ExprPtr<F> &e) {
    return d.public_expr(std::move(nm), e);
  }
  template <class F>
  static void rewrite_predicate(Domain<F> &d, size_t k, ExprPtr<F> e) {
    const auto deps = expr_deps(e);
    for (auto &c : d.circuits_)
      if (c.pred == long(k)) c.reads = deps;
    d.preds_.at(k).e = std::move(e);
  }
  // A GKR circuit constraint NM over D, FN(lc, wires_1, ..., wires_k)
  // reading R's values as wire vectors (Domain::gkr); or over the domain a
  // scope infers from R, NM in that scope. The compiler's own circuits
  // (the MAC, the range and assert_in lookups) are declared here;
  // applications and library functions state predicates pinned to the
  // circuit instead. KEY describes what FN's circuit depends on beyond the
  // compiler's code and R, for the compile cache's key; a circuit without
  // one makes its system uncacheable.
  template <class F, class... R, class Fn>
  static void gkr(Domain<F> &d, std::string nm, Deps<R...> r, Fn fn,
                  std::optional<std::vector<uint8_t>> key = std::nullopt) {
    d.gkr(std::move(nm), r, std::move(fn), std::move(key));
  }
  template <class F, class Fn>
  static void gkr(Domain<F> &d, std::string nm, const std::vector<Ref<F>> &r,
                  Fn fn,
                  std::optional<std::vector<uint8_t>> key = std::nullopt) {
    d.gkr(std::move(nm), r, std::move(fn), std::move(key));
  }
  // The description bytes of expression E of D (the system digest's form),
  // for a closure's key (Domain::gkr).
  template <class F>
  static void describe(const Domain<F> &d, const ExprPtr<F> &e,
                       std::vector<uint8_t> &out) {
    describe_expr<F>(
        e, [&d](const Lin<F> &l) { return d.describe_lin(l); }, out);
  }
  template <class... R, class Fn>
  static void gkr(const Scope &s, const std::string &nm, Deps<R...> r,
                  Fn fn,
                  std::optional<std::vector<uint8_t>> key = std::nullopt) {
    s.gkr(nm, r, std::move(fn), std::move(key));
  }
  template <class F, class Fn>
  static void gkr(const Scope &s, const std::string &nm,
                  const std::vector<Ref<F>> &r, Fn fn) {
    s.gkr(nm, r, std::move(fn));
  }
  // The system's domains in declaration order (index order).
  static const std::vector<DomainCore *> &domains(const SystemCore &s) {
    return s.domain_list();
  }
  // A handle on node ID of D, and D's graph.
  template <class F>
  static Ref<F> ref_of(const Domain<F> &d, size_t id) {
    return d.ref_of(id);
  }
  template <class F>
  static const Graph &graph(const Domain<F> &d) {
    return *d.g_;
  }
  // A domain's declarations as compiled, read by the plan export
  // (plan_export.h): its circuit entries (a predicate's, or a lowering's
  // own circuit), affine rows, quadratic triples, affine views (derived
  // values), expression values, wiring views (concat, gather), bindings
  // (a value bound to its digits), public expression values, bit views
  // (each view's words), the derived Bit values it checks, and its range
  // requests and tables.
  template <class F>
  static const auto &circuit_decls(const Domain<F> &d) {
    return d.circuits_;
  }
  template <class F>
  static const auto &affine_decls(const Domain<F> &d) {
    return d.affine_;
  }
  template <class F>
  static const auto &quad_decls(const Domain<F> &d) {
    return d.quads_;
  }
  template <class F>
  static const std::map<size_t, Lin<F>> &derived_views(const Domain<F> &d) {
    return d.lins_;
  }
  template <class F>
  static const std::map<size_t, ExprPtr<F>> &expr_values(const Domain<F> &d) {
    return d.exprs_;
  }
  template <class F>
  static const std::map<size_t, ExprPtr<F>> &public_exprs(const Domain<F> &d) {
    return d.pub_exprs_;
  }
  template <class F>
  static const std::map<size_t, std::vector<std::pair<size_t, size_t>>> &
  wiring_views(const Domain<F> &d) {
    return d.wiring_;
  }
  template <class F>
  static const std::map<size_t, Lin<F>> &bindings(const Domain<F> &d) {
    return d.bound_;
  }
  template <class F>
  static const std::map<size_t, std::vector<size_t>> &bit_views(
      const Domain<F> &d) {
    return d.views_;
  }
  template <class F>
  static const std::vector<RangeRequest<F>> &range_requests(
      const Domain<F> &d) {
    return d.requests_;
  }
  template <class F>
  static const std::vector<RangeTableStats> &table_stats(const Domain<F> &d) {
    return d.range_tables_;
  }
  // The plan records, which lowerings and gadgets without a scope write.
  static PlanRecords &records(Graph &g) { return g.records; }
  // A challenge of field F, which may have no domain (an operator's
  // parameter field: the MAC tests' chunk powers), declared at the root of
  // the system SYS.
  template <class Sys, class F, class... A>
  static Ref<F, Field, Public> challenge(Sys &s, const F &f, A &&...a) {
    return s.bare_field(f).challenge_in(s, std::forward<A>(a)...);
  }
  // A public value of field F, which may have no domain. A closure over a
  // challenge declared here is a core realization's (compile()'s check of
  // closures over challenges).
  template <class Sys, class F, class T, class... A>
  static auto pub(Sys &s, const F &f, T t, const std::string &nm, A &&...a) {
    auto r = s.bare_field(f).pub_in(s, t, nm, std::forward<A>(a)...);
    static_cast<SystemCore &>(s).mutable_graph().nodes.at(r.id).origin =
        "lowering";
    return r;
  }
  // The value forms of field F with no domain: the odd MAC's tag, its pad
  // and its key live there, and no domain commits them.
  template <class Sys, class F>
  static Domain<F> &bare_field(Sys &s, const F &f) {
    return s.bare_field(f);
  }
  // The value forms of the field object FOBJ with no domain in system S,
  // or null (the plan export).
  template <class Sys>
  static const DomainCore *bare_domain(const Sys &s, const void *fobj) {
    return s.bare_domain(fobj);
  }
};


// Phases and the values each challenge tests (design section 1), with the
// tests inferred from the constraints.
//
// A challenge c tests every prover-chosen value that a constraint reads
// together with c and that is not computed from c: the values the
// challenge-use rule needs fixed before c is drawn. A constraint reads c
// when c is reachable from its reads through derived views, public
// computations and bit views. From each read, the walk descends into a
// node computed from c of those kinds, and stops at a node independent of c
// (tested itself unless it is a statement value, constant, challenge, host
// input, or a public computation of those) or at a value computed from c
// of another kind; a late value read in a constraint is read as t - P, so
// its declared pad is tested. The declared depends_on(...) are kept as hints
// (an ordering for a challenge that no constraint reads), and the tests are
// the sorted union. Phases: a challenge one more than the largest phase
// among its tests, every other node the largest among its dependencies,
// computed in one topological pass; a challenge that would test a value of
// its own phase or later through another challenge is a cycle
// (CompileError, naming the cycle phase_cycle finds).
struct PhasePlan {
  std::vector<size_t> phase;
  std::vector<std::vector<size_t>> tests;  // per node (challenges)
  // Per node, the challenges among its transitive dependencies, sorted
  // (the only ancestors the phase rules ask about: a graph of long
  // dependency chains, such as a hash's rounds, has quadratically many
  // ancestor pairs but few challenges).
  std::vector<std::vector<size_t>> challenges;
  // Whether node X is computed from challenge C.
  bool from(size_t x, size_t c) const {
    return std::binary_search(challenges[x].begin(), challenges[x].end(), c);
  }
};

inline std::string phase_cycle(const std::vector<Node> &N,
                               const PhasePlan &pp);
inline PhasePlan infer_phases(const std::vector<Node> &N,
                              const std::vector<std::vector<size_t>> &reads) {
  const size_t n0 = N.size();
  PhasePlan pp;
  // Dependencies come before their dependents (compile() checks it), so
  // one pass in id order sees every dependency's sets complete.
  pp.challenges.resize(n0);
  // Whether a node is, or is computed from, a prover-chosen value.
  std::vector<bool> chosen(n0, false);
  for (size_t id = 0; id < n0; ++id) {
    const Kind k = N[id].kind;
    bool c = !(k == Kind::kPublicInput || k == Kind::kConstant ||
               k == Kind::kChallenge || k == Kind::kPublicCompute ||
               k == Kind::kHostInput);
    std::vector<size_t> ch;
    for (size_t d : N[id].deps) {
      c = c || chosen[d];
      if (N[d].kind == Kind::kChallenge) ch.push_back(d);
      ch.insert(ch.end(), pp.challenges[d].begin(), pp.challenges[d].end());
    }
    std::sort(ch.begin(), ch.end());
    ch.erase(std::unique(ch.begin(), ch.end()), ch.end());
    pp.challenges[id] = std::move(ch);
    chosen[id] = c;
  }
  pp.tests.resize(n0);
  for (size_t c = 0; c < n0; ++c) {
    if (N[c].kind != Kind::kChallenge) continue;
    std::set<size_t> t(N[c].tests.begin(), N[c].tests.end());
    for (const auto &roots : reads) {
      bool reads_c = false;
      std::set<size_t> cand, seen;
      std::vector<size_t> stack(roots.begin(), roots.end());
      while (!stack.empty()) {
        const size_t x = stack.back();
        stack.pop_back();
        if (!seen.insert(x).second) continue;
        if (x == c) {
          reads_c = true;
          continue;
        }
        const Kind k = N[x].kind;
        if (pp.from(x, c)) {
          if (k == Kind::kDerived || k == Kind::kPublicCompute ||
              k == Kind::kBitView)
            stack.insert(stack.end(), N[x].deps.begin(), N[x].deps.end());
          else if (k == Kind::kAdvice && N[x].masked_by >= 0)
            cand.insert(size_t(N[x].masked_by));
        } else if (k != Kind::kChallenge && chosen[x]) {
          cand.insert(x);
        }
      }
      if (reads_c) t.insert(cand.begin(), cand.end());
    }
    pp.tests[c].assign(t.begin(), t.end());
  }
  // Phases are longest paths in the graph whose edges run from a node to
  // what it waits for: a challenge to its tests (weight 1), every other node
  // to its dependencies (weight 0). Kahn's algorithm orders the graph; a
  // node left unordered lies on or behind a cycle, which goes through a
  // test since the dependencies alone are acyclic.
  auto preds = [&](size_t u) -> const std::vector<size_t> & {
    return N[u].kind == Kind::kChallenge ? pp.tests[u] : N[u].deps;
  };
  std::vector<size_t> waiting(n0, 0);
  std::vector<std::vector<size_t>> succ(n0);
  for (size_t u = 0; u < n0; ++u)
    for (size_t p : preds(u)) {
      succ[p].push_back(u);
      ++waiting[u];
    }
  std::vector<size_t> ready;
  for (size_t u = 0; u < n0; ++u)
    if (waiting[u] == 0) ready.push_back(u);
  pp.phase.assign(n0, 0);
  size_t done = 0;
  while (!ready.empty()) {
    const size_t u = ready.back();
    ready.pop_back();
    ++done;
    size_t ph = 0;
    for (size_t p : preds(u)) ph = std::max(ph, pp.phase[p]);
    if (N[u].kind == Kind::kChallenge) ++ph;
    pp.phase[u] = ph;
    for (size_t v : succ[u])
      if (--waiting[v] == 0) ready.push_back(v);
  }
  if (done != n0)
    fail("the challenges' phases form a cycle: " + phase_cycle(N, pp));
  return pp;
}

// A cycle among the challenges of PP: "c tests t (computed from c'); ...",
// each step a challenge, a value it tests and the challenge that value is
// computed from, back to the first challenge.
inline std::string phase_cycle(const std::vector<Node> &N,
                               const PhasePlan &pp) {
  // Edge c -> (t, c'): c tests t, and t is computed from the challenge c'.
  std::map<size_t, std::vector<std::pair<size_t, size_t>>> next;
  for (size_t c = 0; c < N.size(); ++c) {
    if (N[c].kind != Kind::kChallenge) continue;
    for (size_t t : pp.tests[c])
      for (size_t a : pp.challenges[t])
        if (N[a].kind == Kind::kChallenge) next[c].push_back({t, a});
  }
  // Depth-first search for a back edge; PATH holds (challenge, step taken).
  std::map<size_t, int> state;
  std::vector<std::pair<size_t, std::pair<size_t, size_t>>> path;
  std::function<long(size_t)> dfs = [&](size_t c) -> long {
    state[c] = 1;
    for (const auto &st : next[c]) {
      path.push_back({c, st});
      if (state[st.second] == 1) return long(st.second);
      if (state[st.second] == 0) {
        const long r = dfs(st.second);
        if (r >= 0) return r;
      }
      path.pop_back();
    }
    state[c] = 2;
    return -1;
  };
  for (const auto &[c, e] : next) {
    if (state[c] != 0) continue;
    path.clear();
    const long start = dfs(c);
    if (start < 0) continue;
    size_t k = 0;
    while (path[k].first != size_t(start)) ++k;
    std::string out;
    for (; k < path.size(); ++k) {
      const auto &[ch, st] = path[k];
      if (!out.empty()) out += "; ";
      out += N[ch].name + " tests " + N[st.first].name + " (computed from " +
             N[st.second].name + ")";
    }
    return out;
  }
  return "a challenge tests a value computed from a challenge that tests a "
         "value computed from it";
}


// What a lowering sees: the system and its domains, the profile, the
// phases of the graph so far, and the summary it fills. It has no
// transcript, prover or verifier access. A grouped lowering reads it as a
// LoweringContext, without the field set.
template <class S>
class ConstraintSystemBuilder : public LoweringContext {
 public:
  using System = typename S::System;
  ConstraintSystemBuilder(System &s, const CompileProfile &p) : s_(s), p_(p) {}
  System &system() { return s_; }
  const Scope &scope() const override { return s_; }
  SystemCore &core() override { return s_; }
  const CompileProfile &profile() const override { return p_; }
  // Inferred phases of every node declared so far (design section 1).
  std::vector<size_t> phases() const override {
    std::vector<std::vector<size_t>> reads;
    for (const auto &d : s_.domains())
      for (auto &[nm, r] : d->constraint_reads()) reads.push_back(r);
    return infer_phases(s_.g_.nodes, reads).phase;
  }
  LoweringSummary &summary() override { return *summary_; }
  void set_summary(LoweringSummary *s) { summary_ = s; }
  // What the lowerings chose, for the plan export (PlanRecords).
  PlanRecords &records() override { return s_.g_.records; }
  const BasicGraph<S> &graph() const { return s_.g_; }

 private:
  System &s_;
  const CompileProfile &p_;
  LoweringSummary *summary_ = nullptr;
};

// A lowering pass: it rewrites the system through the builder and reports
// its summary.
template <class S>
class BasicLowering : public Lowering {
 public:
  virtual ~BasicLowering() = default;
  virtual std::string name() const = 0;
  virtual void rewrite(ConstraintSystemBuilder<S> &b) = 0;
  virtual LoweringSummary summary() const = 0;
};

// Design pass 2: every assert_same_bits. The equalities across two domains
// whose operands share a phase lower to one MAC (mac.h), named after the
// first of them. Each equality's sides are typed here, from their nodes'
// fields in S.
template <class S>
class MacEqualityLowering final : public BasicLowering<S> {
 public:
  std::string name() const override { return "mac-equality"; }
  void rewrite(ConstraintSystemBuilder<S> &b) override {
    b.set_summary(&summary_);
    auto &eqs = b.system().equalities_;
    // The MAC ablation (CompileProfile::unsound_no_mac): the cross-domain
    // equalities are marked lowered and lower to nothing; the summary names
    // the ablation, so the system's digest differs from the full system's.
    const bool ablated = b.profile().unsound_no_mac;
    if (ablated) put_str(summary_.descr, "mac-ablated");
    // The per-chunk MAC ablation (CompileProfile::unsound_per_chunk_mac):
    // the equalities lower to Longfellow's per-chunk MAC (mac.h); the
    // summary names it, so the digest differs from the full system's.
    if (b.profile().unsound_per_chunk_mac) {
      if (ablated)
        fail("the compile profile sets both unsound_no_mac and "
             "unsound_per_chunk_mac; they are alternative MAC ablations");
      put_str(summary_.descr, "mac-per-chunk");
    }
    const auto &N = b.system().graph().nodes;
    const auto phase = b.phases();
    using Key = std::tuple<int, int, size_t>;
    auto key = [&](const auto &e) -> std::optional<Key> {
      const int dx = N.at(e.x).domain, dy = N.at(e.y).domain;
      if (dx < 0 || dy < 0 || dx == dy) return std::nullopt;
      return Key{std::min(dx, dy), std::max(dx, dy),
                 std::max(phase.at(e.x), phase.at(e.y))};
    };
    for (size_t i = 0; i < eqs.size(); ++i) {
      if (eqs[i].lowered) continue;
      if (ablated && key(eqs[i])) {
        summary_.report.push_back("MAC ablation: dropped " +
                                  N.at(eqs[i].x).name + " = " +
                                  N.at(eqs[i].y).name);
        eqs[i].lowered = true;
        continue;
      }
      std::vector<std::pair<size_t, size_t>> members{{eqs[i].x, eqs[i].y}};
      const auto k = key(eqs[i]);
      if (k)
        for (size_t j = i + 1; j < eqs.size(); ++j)
          if (!eqs[j].lowered && key(eqs[j]) == k) {
            members.push_back({eqs[j].x, eqs[j].y});
            eqs[j].lowered = true;
          }
      lower(b, eqs[i].x, eqs[i].y, members, i);
      eqs[i].lowered = true;
    }
  }
  LoweringSummary summary() const override { return summary_; }

 private:
  // lower_equality on the handles of nodes X and Y, typed by their fields.
  static void lower(ConstraintSystemBuilder<S> &b, size_t x, size_t y,
                    const std::vector<std::pair<size_t, size_t>> &members,
                    size_t index) {
    Graph *g = &b.system().g_;
    const Node &nx = g->nodes.at(x), &ny = g->nodes.at(y);
    S::dispatch(nx.field, [&](auto t1) {
      using F1 = typename decltype(t1)::type;
      S::dispatch(ny.field, [&](auto t2) {
        using F2 = typename decltype(t2)::type;
        lower_equality<S>(
            b,
            Ref<F1>(x, nx.n, static_cast<const F1 *>(nx.fobj), g, nx.shape),
            Ref<F2>(y, ny.n, static_cast<const F2 *>(ny.fobj), g, ny.shape),
            members, index);
      });
    });
  }

  LoweringSummary summary_;
};

// The application's assert_mod declarations (mod.h): those of modulus
// m >= 2 in one pass, and those of modulus 0 (the integer equality) in a
// second pass after it, under the digest label int-equal, since their
// intervals read the range requests the first pass states. A system
// without a declaration of a pass records no summary for it, so its digest
// does not name it.
template <class S>
class ModLowering final : public BasicLowering<S> {
 public:
  explicit ModLowering(bool zero) : zero_(zero) {}
  std::string name() const override { return zero_ ? "int-equal" : "mod"; }
  void rewrite(ConstraintSystemBuilder<S> &b) override {
    b.set_summary(&summary_);
    auto &sys = b.system();
    for (auto &e : sys.mods_) {
      if (e.lowered || e.zero != zero_) continue;
      S::dispatch(sys.cores_.at(size_t(e.domain))->field_id, [&](auto tag) {
        using F = typename decltype(tag)::type;
        if constexpr (!F::kCharacteristicTwo) {
          const auto &d = *static_cast<const ModDecl<F> *>(e.decl.get());
          lower_assert_mod<S>(b, e.domain, d);
        }
      });
      e.lowered = true;
      ran_ = true;
    }
  }
  LoweringSummary summary() const override { return summary_; }
  bool ran() const { return ran_; }

 private:
  bool zero_ = false;
  LoweringSummary summary_;
  bool ran_ = false;
};

// The conv(x, y) nodes of every predicate, each realized once (conv.h),
// after the lowerings that state predicates (assert_mod's m = 0 among them)
// and before the range lowering. A system without one records no summary.
template <class S>
class ConvLowering final : public BasicLowering<S> {
 public:
  std::string name() const override { return "conv"; }
  void rewrite(ConstraintSystemBuilder<S> &b) override {
    b.set_summary(&summary_);
    auto &sys = b.system();
    for (DomainCore *dc : sys.cores_) {
      S::dispatch(dc->field_id, [&](auto tag) {
        using F = typename decltype(tag)::type;
        auto *d = dynamic_cast<Domain<F> *>(dc);
        if (d != nullptr && realize_convs<S>(b, *d)) ran_ = true;
      });
    }
  }
  LoweringSummary summary() const override { return summary_; }
  bool ran() const { return ran_; }

 private:
  LoweringSummary summary_;
  bool ran_ = false;
};

// The public expressions of every predicate (public_expr.h), lifted into
// public values after the lowerings that state predicates and before the
// range lowering. A system without one records no summary.
template <class S>
class PublicExprLowering final : public BasicLowering<S> {
 public:
  std::string name() const override { return "public-expr"; }
  void rewrite(ConstraintSystemBuilder<S> &b) override {
    b.set_summary(&summary_);
    auto &sys = b.system();
    for (DomainCore *dc : sys.cores_) {
      S::dispatch(dc->field_id, [&](auto tag) {
        using F = typename decltype(tag)::type;
        auto *d = dynamic_cast<Domain<F> *>(dc);
        if (d != nullptr && lift_public_exprs<S>(b, *d)) ran_ = true;
      });
    }
  }
  LoweringSummary summary() const override { return summary_; }
  bool ran() const { return ran_; }

 private:
  LoweringSummary summary_;
  bool ran_ = false;
};

// The grouped requests (Scope::defer): each key's requests lower
// together, keys in the order of their first request.
template <class S>
class GroupedLowering final : public BasicLowering<S> {
 public:
  std::string name() const override { return "grouped"; }
  void rewrite(ConstraintSystemBuilder<S> &b) override {
    b.set_summary(&summary_);
    auto &gs = b.system().grouped_;
    for (size_t i = 0; i < gs.size(); ++i) {
      if (gs[i].lowered) continue;
      std::vector<std::shared_ptr<const void>> members;
      for (size_t j = i; j < gs.size(); ++j)
        if (!gs[j].lowered && gs[j].key == gs[i].key) {
          members.push_back(gs[j].request);
          if (j != i) gs[j].lowered = true;
        }
      put_str(summary_.descr, gs[i].key);
      put_u64(summary_.descr, members.size());
      gs[i].lower(b, members);
      gs[i].lowered = true;
      ran_ = true;
    }
  }
  LoweringSummary summary() const override { return summary_; }
  bool ran() const { return ran_; }

 private:
  LoweringSummary summary_;
  bool ran_ = false;
};

// Design pass 3: every domain's range requests, those of pass 2 included.
template <class S>
class RangeLowering final : public BasicLowering<S> {
 public:
  std::string name() const override { return "range"; }
  void rewrite(ConstraintSystemBuilder<S> &b) override {
    b.set_summary(&summary_);
    put_str(summary_.descr, b.profile().range.name);
    put_u64(summary_.descr, b.profile().range.version);
    for (const auto &d : b.system().domains()) d->lower_ranges(b);
  }
  LoweringSummary summary() const override { return summary_; }

 private:
  LoweringSummary summary_;
};

}  // namespace proofs::gordiehowe::compiler

#endif  // PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_COMPILER_LOWERING_H_
