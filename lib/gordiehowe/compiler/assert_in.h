// Copyright 2026 Chad Sharp and Paul Grubbs
// SPDX-License-Identifier: Apache-2.0

// GordieHowe: the realization of assert_in: every request of a domain lowers
// together, one log-derivative argument per table with its multiplicities,
// fixed-kappa or challenge-gamma record packing and one alpha per domain,
// alpha:<D>, which the range lowering shares.

#ifndef PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_COMPILER_ASSERT_IN_H_
#define PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_COMPILER_ASSERT_IN_H_

#include <algorithm>
#include <cstddef>
#include <cstdint>
#include <functional>
#include <memory>
#include <optional>
#include <set>
#include <string>
#include <type_traits>
#include <utility>
#include <vector>

#include "gordiehowe/certify.h"
#include "gordiehowe/closure_expr.h"
#include "gordiehowe/compiler/derivation.h"
#include "gordiehowe/compiler/log_derivative.h"
#include "gordiehowe/compiler/lowering.h"
#include "gordiehowe/compiler/range.h"
#include "gordiehowe/core.h"
#include "gordiehowe/ct.h"
#include "gordiehowe/domain.h"
#include "gordiehowe/expr.h"
#include "gordiehowe/lib/permutation.h"
#include "gordiehowe/lib/lookup_counts.h"
#include "gordiehowe/system_core.h"

namespace proofs::gordiehowe {
// A public table of assert_in (membership.h).
template <class F>
struct InTable;
}  // namespace proofs::gordiehowe

namespace proofs::gordiehowe::compiler {

namespace membership_internal {

// The compiler tier this lowering reads: its lookup circuits and the
// system's domains.
struct InLowering : Lowering {
  using Lowering::describe;
  using Lowering::domains;
  using Lowering::gkr;
  using Lowering::logup_alpha;
  using Lowering::logup_tmax;
  using Lowering::realization;
  using Lowering::set_sampler;
};

// One assert_in request on a list of rows: its table, its records (n
// records of the table's arity), its domain and its scoped name.
template <class F>
struct Request {
  InTable<F> table;
  ExprPtr<F> records;
  size_t n = 0;
  int domain = -1;
  std::string name;
};

enum class Packing : uint8_t { kFixed = 1, kChallenge = 2 };

// The packing powers 1, X, ..., X^(A-1).
template <class F>
std::vector<typename F::Elt> powers_of(const F &f, const typename F::Elt &x,
                                       size_t A) {
  std::vector<typename F::Elt> p(A, f.one());
  for (size_t k = 1; k < A; ++k) p[k] = f.mulf(p[k - 1], x);
  return p;
}

// The fixed packing's kappa: selection_kappa over a field with relative
// packing; a prime field packs arity 1 alone and has none.
template <class F>
std::optional<typename F::Elt> fixed_kappa(const F &f) {
  if constexpr (field_degree<F>() > 1) {
    return lib::permutation::selection_kappa(f);
  } else {
    return std::nullopt;
  }
}

// Whether every row entry of the committed table T lies in the designated
// subfield, by structure (in_subfield_expr).
template <class F>
bool rows_in_subfield(const F &f, const InTable<F> &t,
                      const std::vector<Node> &N) {
  std::string why;
  return in_subfield_expr<F>(
      f, t.committed, [&](size_t id) { return N.at(id).type; }, why,
      /*digits=*/true);
}

// One table of a domain's requests, and how it packs.
template <class F>
struct Table {
  const InTable<F> *t = nullptr;
  std::vector<const Request<F> *> rq;
  size_t n = 0;
  Packing packing = Packing::kFixed;
  // Why the fixed packing does not apply ("" when it does).
  std::string why;
};

// Every assert_in request of one domain (the grouped lowering).
template <class F>
void lower(LoweringContext &b, const std::vector<const Request<F> *> &rq) {
  using Elt = typename F::Elt;
  const Scope &s = b.scope();
  const Graph &g = b.core().graph();
  const auto &N = g.nodes;
  Domain<F> &D = b.core().template domain_at<F>(
      size_t(rq.at(0)->domain), "assert_in: the records' domain");
  const F &f = D.field();
  const F *pf = &f;
  const size_t KE = field_degree<F>() / designated_degree<F>();
  const std::optional<Elt> kappa = fixed_kappa(f);

  // The tables, in the order of their first request.
  std::vector<Table<F>> tabs;
  for (const auto *r : rq) {
    auto it = std::find_if(tabs.begin(), tabs.end(), [&](const Table<F> &x) {
      return x.t->name == r->table.name;
    });
    if (it == tabs.end()) {
      tabs.push_back(Table<F>{&r->table, {}, 0, Packing::kFixed, ""});
      it = tabs.end() - 1;
    } else if (it->t->rows.id != r->table.rows.id ||
               it->t->committed != r->table.committed ||
               it->t->A != r->table.A) {
      fail("assert_in: two tables named '" + r->table.name + "'");
    }
    it->rq.push_back(r);
    it->n += r->n;
  }

  // The packing of each table: fixed when exact, otherwise gamma.
  for (auto &tb : tabs) {
    const size_t A = tb.t->A;
    if (A == 1) continue;
    if (A > KE) {
      tb.why =
          "arity " + std::to_string(A) + " > [K : E] = " + std::to_string(KE);
    } else if (!tb.t->committed && !tb.t->rows_in_subfield) {
      tb.why = "the rows are not typed subfield values";
    } else if (tb.t->committed && !rows_in_subfield(f, *tb.t, N)) {
      tb.why = "the committed rows are not subfield values";
    } else if (!lib::permutation::permutation_internal::independent(f, *kappa,
                                                                    A)) {
      tb.why = "1, kappa, ..., kappa^" + std::to_string(A - 1) +
               " are dependent over the subfield";
    } else {
      for (const auto *r : tb.rq) {
        std::string w;
        if (!in_subfield_expr<F>(
                f, r->records, [&](size_t id) { return N.at(id).type; }, w,
                /*digits=*/true)) {
          tb.why = "the records of '" + r->name +
                   "' are not subfield values (" + w + ")";
          break;
        }
      }
    }
    if (!tb.why.empty()) tb.packing = Packing::kChallenge;
  }

  const Bound pfloor = field_characteristic(f);
  size_t amax = 0;
  for (const auto &tb : tabs)
    if (tb.packing == Packing::kChallenge) amax = std::max(amax, tb.t->A);

  // Multiplicities: R counts per table over its requests' records,
  // exact component matches, the first matching row taking the count
  // (table_internal::first_match_counts, oblivious).
  std::vector<Ref<F>> mult;
  std::vector<ClosureExprs<F>> ces;
  for (const auto &tb : tabs) {
    const std::string what = "assert_in '" + tb.t->name + "'";
    if (Bound(tb.n) >= pfloor) fail(what + ": more records than p");
    // The table cap (RangePolicy::max_table), which the domain's
    // max_table raises.
    const Bound policy_cap = b.profile().range.max_table;
    const Bound cap = D.max_table() != 0 ? D.max_table() : policy_cap;
    if (Bound(tb.t->R) > cap)
      fail(what + ": the table has " + std::to_string(tb.t->R) +
           " rows, above the table cap " + bound_str(cap) +
           " (raise it with max_table on domain " + D.name + ")");
    if (Bound(tb.t->R) > policy_cap)
      b.summary().report.push_back(
          "warning: public table " + tb.t->name + " has " +
          std::to_string(tb.t->R) + " rows, above the cap " +
          bound_str(policy_cap) + " (max_table of domain " + D.name + ")");
    s.note("certify", tb.t->name + ".counts",
           term("records", Bound(tb.n)) < term("p", pfloor), D);
    std::vector<ExprPtr<F>> roots;
    std::vector<size_t> ms;
    for (const auto *r : tb.rq) {
      roots.push_back(r->records);
      ms.push_back(r->n);
    }
    // The rows are the last root, read with the records: a committed
    // table's expression, or a public table's rows value.
    const bool committed = tb.t->committed != nullptr;
    roots.push_back(committed ? tb.t->committed : expr_node(tb.t->rows));
    ClosureExprs<F> ce(roots, what);
    std::vector<Ref<F>> deps = ce.refs(g, f);
    const size_t nd = deps.size();
    // Every committed leaf of the rows lies in the records' domain (a
    // public leaf belongs to any).
    for (size_t id : ce.deps())
      if (N.at(id).domain >= 0 && N.at(id).domain != D.index)
        fail(what + ": the rows read '" + N.at(id).name +
             "', a value of another domain");
    const size_t R = tb.t->R, A = tb.t->A;
    auto counts = [ce, nd, pf, R, A,
                   ms](const std::vector<const std::vector<Elt> *> &in) {
      const F &f = *pf;
      std::vector<const std::vector<Elt> *> dv(in.begin(),
                                               in.begin() + long(nd));
      std::vector<Elt> rec;
      for (size_t k = 0; k < ms.size(); ++k) {
        const std::vector<Elt> rk = ce.eval(f, k, dv);
        rec.insert(rec.end(), rk.begin(), rk.end());
      }
      const std::vector<Elt> rows = ce.eval(f, ms.size(), dv);
      const std::vector<uint64_t> cnt =
          lib::table::table_internal::first_match_counts(
              rec.size() / A, R, [&](size_t t, size_t j) {
                uint64_t eq = 1;
                for (size_t c = 0; c < A; ++c)
                  eq &= ct::equal(rec[t * A + c], rows[j * A + c]);
                return eq;
              });
      std::vector<Elt> out(R);
      for (size_t j = 0; j < R; ++j) out[j] = f.of_scalar(cnt[j]);
      return out;
    };
    Ref<F> m;
    // Late when a record is (the phases infer it).
    if (D.prime == Space::kField)
      m = s[D].priv(Field{}, tb.t->name + ".mult", R, deps, counts);
    else
      m = s[D].priv(Subfield{}, tb.t->name + ".mult", R, deps, counts);
    mult.push_back(m);
    ces.push_back(std::move(ce));
  }

  // The challenges: gamma (when a table packs with it), then alpha:<D>, the
  // domain's one LogUp challenge, which the range lowering (after this one)
  // reads too.
  Ref<F, Field, Public> gamma, powers;
  if (amax != 0) {
    gamma = s[D].challenge("in.gamma:" + D.name);
    InLowering::realization(D, gamma);
    powers = s[D].pub(
        Field{}, "in.powers:" + D.name, amax, depends_on(gamma),
        computes("assert_in_powers", {uint64_t(amax)}),
        [pf, amax](const std::vector<Elt> &g) {
          return powers_of(*pf, g[0], amax);
        });
  }
  // Alpha is uniform in K, or, when the domain also has range tables,
  // outside their rows [0, T_max) (the range lowering sets T_max, TMAX). No
  // other table is excluded: every table, public or committed, is checked
  // by the identity after clearing denominators, which holds as a
  // polynomial in alpha and has no weight, so no pole.
  const std::shared_ptr<Bound> tmax = InLowering::logup_tmax(D);
  auto in_u = [pf, tmax](const ValueReader &) {
    const Bound tm = *tmax;
    return std::function<bool(const Elt &)>([pf, tm](const Elt &x) {
      return tm != 0 && range_internal::in_range_table(*pf, x, tm);
    });
  };
  if (InLowering::logup_alpha(D))
    fail("assert_in: domain " + D.name + " already draws alpha:" + D.name);
  // U is empty until the range lowering sets T_max: the sampler then draws
  // once, as challenge() does, and is "field".
  auto alpha = s[D].challenge_outside("alpha:" + D.name, {}, in_u);
  InLowering::set_sampler(D, alpha, "field");
  InLowering::logup_alpha(D) = alpha;
  InLowering::realization(D, alpha);

  Bound alpha_charge = 0, gamma_charge = 0;
  auto &sum = b.summary();
  put_str(sum.descr, D.name);
  put_u64(sum.descr, tabs.size());
  for (size_t ti = 0; ti < tabs.size(); ++ti) {
    const Table<F> &tb = tabs[ti];
    const InTable<F> &t = *tb.t;
    const size_t R = t.R, A = t.A;
    const bool fixed = tb.packing == Packing::kFixed;
    const std::vector<Elt> kp =
        fixed && A > 1 ? powers_of(f, *kappa, A) : std::vector<Elt>(A, f.one());
    const ClosureExprs<F> &ce = ces[ti];
    std::vector<size_t> ms;
    for (const auto *r : tb.rq) ms.push_back(r->n);
    // The lookup closure's key (the compile cache): its records'
    // expressions, needle counts and packing.
    std::vector<uint8_t> key;
    put_str(key, t.committed ? "assert_in.committed" : "assert_in.public");
    put_u64(key, ce.roots().size());
    for (const auto &e : ce.roots()) InLowering::describe(D, e, key);
    put_u64(key, ms.size());
    for (size_t m : ms) put_u64(key, m);
    put_u64(key, A);
    put_u64(key, fixed ? 1 : 0);
    for (const auto &k : kp) {
      std::vector<uint8_t> b(F::kBytes);
      f.to_bytes_field(b.data(), k);
      key.insert(key.end(), b.begin(), b.end());
    }
    // The circuit reads the rows (the closure's last root: a committed
    // table's expression or a public table's rows) and packs them as the
    // records; both sides are fraction trees whose roots agree after
    // clearing denominators, and alpha tests the rows with the records
    // and counts.
    std::vector<Ref<F>> rd = ce.refs(g, f);
    const size_t nd = rd.size();
    rd.push_back(mult[ti]);
    rd.push_back(alpha);
    if (!fixed) rd.push_back(powers);
    InLowering::gkr(
        D, t.name + ".lookup", rd,
        [ce, nd, ms, A, fixed, kp](const auto &lc, const auto &w) {
          std::vector<std::vector<size_t>> dw(w.begin(),
                                              w.begin() + long(nd));
          auto em = ce.emitter(lc, dw);
          const auto &mw = w[nd];
          const size_t a = w[nd + 1][0];
          // pack: products by the constants kappa^c (no gate), or by
          // gamma's power wires.
          auto pack = [&](const std::vector<size_t> &v, size_t r) {
            size_t x = v.at(r * A);
            for (size_t c = 1; c < A; ++c)
              x = fixed ? lc.axpy(x, kp[c], v.at(r * A + c))
                        : lc.add(x, lc.mul(w[nd + 2].at(c),
                                           v.at(r * A + c)));
            return x;
          };
          auto wires = [&](size_t k) {
            std::vector<size_t> v;
            for (const auto &x : em(ce.roots()[k])) v.push_back(em.wire(x));
            return v;
          };
          std::vector<size_t> needles;
          for (size_t k = 0; k < ms.size(); ++k) {
            const std::vector<size_t> rec = wires(k);
            for (size_t r = 0; r < ms[k]; ++r)
              needles.push_back(pack(rec, r));
          }
          const std::vector<size_t> rows = wires(ms.size());
          std::vector<size_t> packed;
          for (size_t j = 0; j < mw.size(); ++j)
            packed.push_back(pack(rows, j));
          assert_log_derivative_committed(lc, needles, a, mw, packed);
        },
        key);
    // The charges: the identity after clearing denominators (n + R - 1),
    // which has no weight and so no pole; gamma packing a record onto one
    // of the R rows (R (A - 1)). Alpha is uniform in K minus U = [0, T_max)
    // (the range tables'), so the identities' event has probability at
    // most sum (n + R - 1) / (|K| - |U|) over the tables; the range
    // lowering's charge includes P = T_max >= |U|, and with A the sum's
    // numerator, A / (|K| - |U|) <= (A + P) / |K| whenever A + P <= |K|
    // (otherwise the charge bounds nothing), so the charge over |K| still
    // bounds the event.
    const Bound ac = Bound(tb.n) + Bound(R) - 1;
    const Bound gc = fixed ? 0 : bound_mul(Bound(R), Bound(A - 1));
    alpha_charge = bound_add(alpha_charge, ac);
    gamma_charge = bound_add(gamma_charge, gc);
    NoteValues nv{{"rows", SignedInt(R)},
                  {"arity", SignedInt(A)},
                  {"records", SignedInt(tb.n)},
                  {"requests", SignedInt(tb.rq.size())},
                  {"packing", SignedInt(uint8_t(tb.packing))},
                  {"extensionDegree", SignedInt(KE)},
                  {"alphaDegree", SignedInt(ac)},
                  {"gammaDegree", SignedInt(gc)}};
    if (t.committed) nv.push_back({"committed", 1});
    s.note("assert-in", t.name, nv, D);
    // The table as the realized program states it.
    {
      PlanRecords::InLookup rec;
      rec.table = t.name;
      rec.domain = D.name;
      rec.circuit = t.name + ".lookup";
      for (const auto *r : tb.rq) {
        rec.requests.push_back(r->name);
        rec.records.push_back(std::make_shared<const ExprPtr<F>>(r->records));
        rec.counts.push_back(r->n);
      }
      if (t.committed)
        rec.rows = std::make_shared<const ExprPtr<F>>(t.committed);
      else
        rec.rows_node = t.rows.id;
      rec.arity = A;
      rec.nrows = R;
      rec.fixed = fixed;
      for (const auto &k : kp) {
        std::vector<uint8_t> kb(F::kBytes);
        f.to_bytes_field(kb.data(), k);
        rec.kappa.push_back(std::move(kb));
      }
      if (!fixed) {
        rec.powers = powers.id;
        rec.gamma = gamma.id;
      }
      rec.alpha = alpha.id;
      rec.mult = mult[ti].id;
      // Each request's derivation: its packed records are rows of the
      // table's packed rows, by its one LogUp member (the lookup lemma).
      for (const auto &rq : rec.requests) {
        Deriv dv(rq, rec.domain);
        dv.conclude(dv.lookup(rq, 0));
        dv.commit(b.records());
      }
      b.records().in_lookups.push_back(std::move(rec));
    }
    put_str(sum.descr, t.name);
    put_u64(sum.descr, R);
    put_u64(sum.descr, A);
    put_u64(sum.descr, tb.n);
    // A committed table adds its marker; a public one's description is
    // unchanged.
    put_u64(sum.descr, uint64_t(tb.packing) | (t.committed ? 0x100 : 0));
    std::string names;
    for (const auto *r : tb.rq) names += (names.empty() ? "" : ", ") + r->name;
    sum.report.push_back(
        "in " + t.name + ": " + std::to_string(tb.rq.size()) + " request" +
        (tb.rq.size() == 1 ? "" : "s") + " (" + names + "), " +
        std::to_string(tb.n) + " records, " + std::to_string(R) +
        (t.committed ? " committed" : "") + " rows of arity " +
        std::to_string(A) + ", " +
        (fixed ? std::string(A == 1 ? "no packing" : "fixed kappa packing")
               : "gamma packing (" + tb.why + ")"));
  }
  s.note("charge", "assert_in", ChallengeCharge{alpha, alpha_charge});
  if (amax != 0)
    s.note("charge", "assert_in", ChallengeCharge{gamma, gamma_charge});
}

// The domain of the records' nodes IDS (public nodes belong to any).
template <class F>
Domain<F> &domain_of(const Scope &s, const std::vector<size_t> &ids,
                     const std::string &what) {
  const auto &N = s.system().graph().nodes;
  int dom = -1;
  for (size_t id : ids) {
    const int d = N.at(id).domain;
    if (d < 0) continue;
    if (dom >= 0 && d != dom)
      fail(what + ": the records read values of two domains");
    dom = d;
  }
  if (dom < 0) fail(what + ": the records read no value of a domain");
  auto *fd = dynamic_cast<Domain<F> *>(
      InLowering::domains(s.system()).at(size_t(dom)));
  if (fd == nullptr) fail(what + ": the records' domain has another field");
  return *fd;
}

}  // namespace membership_internal

}  // namespace proofs::gordiehowe::compiler

#endif  // PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_COMPILER_ASSERT_IN_H_
