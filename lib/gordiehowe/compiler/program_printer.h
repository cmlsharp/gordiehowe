// Copyright 2026 Chad Sharp and Paul Grubbs
// SPDX-License-Identifier: Apache-2.0

// GordieHowe: the realized program (realized_program.h) as its Lean
// module, `def program : GordieHowe.RealizedProgram` in the namespace
// GordieHowe.Generated.<lean_name>.Program.
//
// One definition per value, shared expression, predicate and circuit, each
// on one line; the program lists them by name. Every distinct index map is
// one definition idx<k>, written as runs and repetitions (IndexMap.ofSegs).
// A field element is a natural; a negative integer is Int.negSucc.
//
// Certificate printers (data aligned with the program's lists) write their
// lists with aligned_list: entry i is a fact about element i.

#ifndef PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_COMPILER_PROGRAM_PRINTER_H_
#define PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_COMPILER_PROGRAM_PRINTER_H_

#include <algorithm>
#include <array>
#include <cstddef>
#include <cstdint>
#include <functional>
#include <map>
#include <string>
#include <utility>
#include <vector>

#include "gordiehowe/compiler/plan_export.h"
#include "gordiehowe/compiler/realized_program.h"

namespace proofs::gordiehowe::compiler {

// A run of an index map: START, START + STEP, ..., COUNT entries.
struct IndexRun {
  size_t start = 0;
  long long step = 0;
  size_t count = 0;
};

// The greedy maximal runs of V: each run takes
// every following entry at its step; a run of one entry has step 0.
inline std::vector<IndexRun> index_runs(const std::vector<size_t> &v) {
  std::vector<IndexRun> out;
  for (size_t i = 0; i < v.size();) {
    if (i + 1 == v.size()) {
      out.push_back({v[i], 0, 1});
      break;
    }
    const long long step = (long long)v[i + 1] - (long long)v[i];
    size_t j = i + 1;
    while (j + 1 < v.size() && (long long)v[j + 1] - (long long)v[j] == step) ++j;
    out.push_back({v[i], step, j - i + 1});
    i = j + 1;
  }
  return out;
}

// The entries of RUNS, in order.
inline std::vector<size_t> decode_index_runs(const std::vector<IndexRun> &runs) {
  std::vector<size_t> out;
  for (const auto &r : runs)
    for (size_t k = 0; k < r.count; ++k)
      out.push_back(size_t((long long)r.start + r.step * (long long)k));
  return out;
}

// A segment of an index map's runs: one run,
// or a pattern of runs repeated K times, run t of repetition j the base
// BASE[t] advanced j times by DELTA[t] (start, step, count).
struct IndexSeg {
  bool rep = false;
  std::vector<std::array<long long, 3>> base, delta;
  size_t k = 1;
};

// The greedy segmentation of RUNS: at each run, the pattern length
// p <= min(64, half the runs left) whose repetitions (each advancing every
// field of every run by one delta per run) save the most numbers,
// 3 p k - (6 p + 1) > 0, the first p among equals; else one run.
inline std::vector<IndexSeg> index_segments(const std::vector<IndexRun> &runs) {
  std::vector<std::array<long long, 3>> rs;
  for (const auto &r : runs)
    rs.push_back({(long long)r.start, r.step, (long long)r.count});
  std::vector<IndexSeg> out;
  const size_t n = rs.size();
  size_t i = 0;
  while (i < n) {
    size_t best_p = 0, best_k = 0;
    long long best_saved = 0;
    std::vector<std::array<long long, 3>> best_d;
    for (size_t p = 1; p <= std::min<size_t>(64, (n - i) / 2); ++p) {
      std::vector<std::array<long long, 3>> d(p);
      for (size_t t = 0; t < p; ++t)
        for (size_t f = 0; f < 3; ++f) d[t][f] = rs[i + p + t][f] - rs[i + t][f];
      size_t k = 2;
      while (i + (k + 1) * p <= n) {
        bool same = true;
        for (size_t t = 0; t < p && same; ++t)
          for (size_t f = 0; f < 3 && same; ++f)
            same = rs[i + k * p + t][f] - rs[i + (k - 1) * p + t][f] == d[t][f];
        if (!same) break;
        ++k;
      }
      const long long saved = 3LL * p * k - (6LL * p + 1);
      if (saved > 0 && (best_p == 0 || saved > best_saved)) {
        best_p = p;
        best_k = k;
        best_saved = saved;
        best_d = d;
      }
    }
    IndexSeg seg;
    if (best_p == 0) {
      seg.base = {rs[i]};
      ++i;
    } else {
      seg.rep = true;
      seg.k = best_k;
      seg.base.assign(rs.begin() + long(i), rs.begin() + long(i + best_p));
      seg.delta = best_d;
      i += best_p * best_k;
    }
    out.push_back(std::move(seg));
  }
  return out;
}

// The runs of SEGS (IdxSeg.expand): a run, or each repetition's pattern
// in order, start and count clamped at 0.
inline std::vector<IndexRun> expand_index_segments(
    const std::vector<IndexSeg> &segs) {
  std::vector<IndexRun> out;
  for (const auto &g : segs) {
    if (!g.rep) {
      out.push_back({size_t(g.base[0][0]), g.base[0][1], size_t(g.base[0][2])});
      continue;
    }
    for (size_t j = 0; j < g.k; ++j)
      for (size_t t = 0; t < g.base.size(); ++t) {
        const long long jj = (long long)j;
        const long long st = g.base[t][0] + jj * g.delta[t][0];
        const long long ct = g.base[t][2] + jj * g.delta[t][2];
        out.push_back({size_t(std::max(0LL, st)), g.base[t][1] + jj * g.delta[t][1],
                       size_t(std::max(0LL, ct))});
      }
  }
  return out;
}

// Maximal runs of equal values (ConstRuns): (value, count) pairs.
inline std::vector<std::pair<std::string, size_t>> const_runs(
    const std::vector<std::string> &v) {
  std::vector<std::pair<std::string, size_t>> out;
  for (const auto &x : v) {
    if (!out.empty() && out.back().first == x)
      ++out.back().second;
    else
      out.push_back({x, 1});
  }
  return out;
}

namespace program_printer_internal {

using plan_export_internal::str;
using ir::Id;
using ir::kNone;

// One line of naturals per twenty entries, at column COL.
inline std::string nat_list(const std::vector<std::string> &xs, size_t col) {
  if (xs.empty()) return "[]";
  std::string s = "[";
  for (size_t i = 0; i < xs.size(); ++i) {
    if (i) s += (i % 20 == 0) ? ",\n" + std::string(col + 1, ' ') : ", ";
    s += xs[i];
  }
  return s + "]";
}

inline std::string paren(const std::string &s) { return "(" + s + ")"; }
inline std::string num(size_t x) { return std::to_string(x); }

// A Lean integer from its signed decimal: -k as (Int.negSucc (k - 1)),
// which elaborates faster than a negation.
inline std::string int_text(const std::string &s) {
  if (s.empty() || s[0] != '-') return s;
  std::string m = s.substr(1);
  // m - 1 in decimal (m >= 1).
  size_t i = m.size();
  while (i-- > 0) {
    if (m[i] != '0') {
      --m[i];
      break;
    }
    m[i] = '9';
  }
  const size_t nz = m.find_first_not_of('0');
  m = nz == std::string::npos ? "0" : m.substr(nz);
  return "(Int.negSucc " + m + ")";
}

// A Lean list of the items' texts, separated by SEP.
template <class T, class Fn>
std::string list_of(const std::vector<T> &v, Fn fn, const char *sep = ", ") {
  std::string o = "[";
  for (size_t i = 0; i < v.size(); ++i) o += (i ? sep : "") + fn(v[i]);
  return o + "]";
}

class Printer {
 public:
  explicit Printer(const ir::Program &p) : p_(p), text_(p.nodes.size()) {}

  // The text of node E (Lean `Expr`), memoized.
  const std::string &expr(Id e) {
    // Post-order with an explicit stack: an affine sum is a left-deep
    // chain as long as its terms.
    std::vector<std::pair<Id, bool>> st{{e, false}};
    while (!st.empty()) {
      auto [x, ready] = st.back();
      st.pop_back();
      if (done(x)) continue;
      const ir::Expr &n = p_.nodes.at(x);
      if (!ready) {
        st.push_back({x, true});
        for (Id k : kids(n))
          if (!done(k)) st.push_back({k, false});
        continue;
      }
      text_[x] = render(n);
      done_.resize(std::max(done_.size(), size_t(x) + 1));
      done_[x] = true;
    }
    return text_[e];
  }

  std::string named_op(Id o) const {
    const ir::NamedOp &op = p_.ops.at(o);
    using NO = ir::NamedOp;
    auto v = [&]() { return num(op.value); };
    auto form = [&]() {
      return op.ntt_form ? "(.ntt " + op.elt + ")" : std::string(".coefficients");
    };
    switch (op.kind) {
      case NO::kNegacyclicConv:
        return ".negacyclicConv " + v() + " " + form();
      case NO::kPolyMatVec:
        return ".polyMatVec " + v() + " " + num(op.nats.at(0)) + " " +
               num(op.nats.at(1)) + " " + form();
      case NO::kPolyBroadcast:
        return ".polyBroadcast " + v() + " " + num(op.nats.at(0)) + " " + form();
      case NO::kNtt:
        return ".ntt " + num(op.nats.at(0)) + " " + op.elt +
               (op.natural_order ? " .natural" : " .scheme");
      case NO::kInverseNtt:
        return ".inverseNtt " + num(op.nats.at(0)) + " " + op.elt;
      case NO::kNttTranspose:
        return ".nttTranspose " + num(op.nats.at(0)) + " " + op.elt;
      case NO::kRowDot:
        return ".rowDot " + v() + " " + num(op.nats.at(0)) + " " +
               num(op.nats.at(1));
      case NO::kMacConv: {
        std::string taps;
        for (size_t t : op.taps) taps += (taps.empty() ? "" : ", ") + num(t);
        return ".macConv " + v() + " " + num(op.nats.at(0)) + " " +
               num(op.nats.at(1)) + " [" + taps + "]";
      }
      case NO::kAcyclicConv:
        return ".acyclicConv " + v() + " " + num(op.nats.at(0));
      case NO::kDiagonal:
        return ".diagonal " + v();
      case NO::kScale:
        return ".scale " + v();
      case NO::kConstDiagonal:
        return ".constDiagonal " + v();
      case NO::kSum:
        return ".sum " + num(op.nats.at(0));
      case NO::kFromDigits:
        return ".fromDigits " + num(op.nats.at(0)) + " " + op.elt;
      case NO::kBatched:
        return ".batched " + num(op.nats.at(0)) + " " + paren(named_op(op.inner));
    }
    return "";
  }

  std::string coef(Id c) const {
    const ir::Coef &k = p_.coefs.at(c);
    return k.is_const ? "(.const " + k.c + ")"
                      : "(.node " + num(k.v) + " " + num(k.i) + ")";
  }

  std::string reads(const std::vector<ir::Read> &rs) const {
    return list_of(rs, [](const ir::Read &r) {
      switch (r.kind) {
        case ir::Read::kChal:
          return ".chal " + num(r.id);
        case ir::Read::kLate:
          return ".late " + num(r.id);
        default:
          return ".pad " + num(r.id);
      }
    });
  }
  static std::string degree(const std::vector<std::pair<Id, size_t>> &d) {
    std::string o = "[";
    bool first = true;
    for (const auto &[c, k] : d) {
      if (k == 0) continue;
      o += (first ? "(" : ", (") + num(c) + ", " + num(k) + ")";
      first = false;
    }
    return o + "]";
  }
  static std::string space(const ir::Space &s) {
    return s.full ? std::string(".full") : "(.node " + str(s.node) + ")";
  }
  static std::string target(const ir::Target &t) {
    switch (t.kind) {
      case ir::Target::kAffine:
        return ".affine";
      case ir::Target::kQuadratic:
        return ".quadratic";
      case ir::Target::kBatch:
        return "(.batch " + num(t.id) + ")";
      case ir::Target::kRealized:
        return "(.realized " + num(t.id) + ")";
      default:
        return "(.gkr " + num(t.id) + ")";
    }
  }
  static std::string real(const ir::RealRef &r) {
    switch (r.kind) {
      case ir::RealRef::kLogup:
        return "(.logup " + num(r.a) + " " + num(r.b) + ")";
      case ir::RealRef::kMacH:
        return "(.macH " + num(r.a) + ")";
      case ir::RealRef::kWeights:
        return "(.weights " + num(r.a) + ")";
      default:
        return "(.unmodeled " + num(r.a) + ")";
    }
  }
  static std::string ids(const std::vector<Id> &v) {
    return list_of(v, [](Id x) { return num(x); });
  }

  std::string value(const ir::Value &v) {
    using K = ir::Value;
    if (!v.unmodeled.empty())
      plan_export_internal::export_fail("value '" + v.name +
                                        "' has no description: " + v.unmodeled);
    std::string k;
    switch (v.kind) {
      case K::kPriv:
        k = ".priv";
        break;
      case K::kInput:
        k = ".pub .input";
        break;
      case K::kOpaque:
        k = ".pub (.«opaque» " + str(v.opaque) + " " + ids(v.args) + ")";
        break;
      case K::kPubExpr:
        k = ".pub (.expr (" + expr(v.expr) + "))";
        break;
      case K::kBound:
        k = ".bound (" + expr(v.expr) + ")";
        break;
      case K::kConstant:
        k = ".constant (ConstRuns.expand " + const_runs_text(v.entries) + ")";
        break;
      case K::kChallenge:
        k = ".challenge " + num(v.ref);
        break;
      case K::kLate:
        k = ".late";
        break;
      case K::kBits:
        k = ".bits " + num(v.ref) + " idx" + num(v.select);
        break;
      case K::kPadCopy:
        k = ".padCopy " + num(v.ref) + " \"polynomialBits\"";
        break;
      case K::kMessage:
        k = ".message " + num(v.ref);
        break;
    }
    const std::string where = v.domain == kNone
                                  ? "field := some " + num(v.field)
                                  : "domain := " + num(v.domain);
    const std::string type = v.type == ir::VType::kBit   ? ".bit"
                             : v.type == ir::VType::kSub ? ".sub " + str(v.sub)
                                                         : ".field";
    std::string s = "{ name := " + str(v.name) + ", " + where + ", shape := " +
                    list_of(v.shape, [](size_t x) { return num(x); }) +
                    ", kind := " + k + ", type := " + type;
    if (v.phase) s += ", phase := " + num(v.phase);
    // Written only when declared (the Lean default is none).
    if (!v.bound.empty()) s += ", bound := some " + v.bound;
    if (v.kind == K::kPriv || v.kind == K::kBits || v.kind == K::kPadCopy)
      s += ", node := some { name := " + str(v.node) + " }";
    if (v.type_source == ir::Value::TypeSource::kNode) s += ", typeSource := .node";
    if (v.type_source == ir::Value::TypeSource::kPred)
      s += ", typeSource := .pred " + num(v.type_pred);
    if (v.kind == K::kLate)
      s += ", reads := " + reads(v.reads) + ", realization := .pad " +
           space(v.pad_space);
    if (v.kind == K::kPubExpr && !v.degree.empty())
      s += ", degree := " + degree(v.degree);
    s += ", role := " + (v.owner == kNone ? std::string(".source")
                                          : ".realization " + num(v.owner));
    return s + " }";
  }

  std::string mod_real(const ir::ModRealization &m) {
    static const char *forms[] = {".field",   ".constant",        ".bit",
                                  ".oneDigit", ".digits", ".committedDigits",
                                  ".grouped", ".integer"};
    std::string out = "{ form := " + std::string(forms[int(m.form)]);
    if (m.has_interval)
      out += ", lhsLo := " + int_text(m.lhs_lo) + ", lhsHi := " +
             int_text(m.lhs_hi) + ", rhsLo := " + int_text(m.rhs_lo) +
             ", rhsHi := " + int_text(m.rhs_hi);
    std::string digits = "[";
    for (size_t i = 0; i < m.digits.size(); ++i)
      digits += (i ? ", " : "") + expr(m.digits[i]);
    digits += "]";
    std::string bounds = "[";
    for (size_t i = 0; i < m.bounds.size(); ++i)
      bounds += (i ? ", (" : "(") + m.bounds[i][0] + ", " + m.bounds[i][1] +
                ", " + m.bounds[i][2] + ")";
    bounds += "]";
    std::string grouped = "none";
    if (m.grouped) {
      const ir::GroupedMod &g = *m.grouped;
      std::string gs = "[";
      for (size_t i = 0; i < g.groups.size(); ++i)
        gs += (i ? ", (" : "(") + num(g.groups[i].first) + ", " +
              num(g.groups[i].second) + ")";
      gs += "]";
      grouped = "(some { base := " + g.base + ", digitCount := " +
                num(g.digit_count) + ", groups := " + gs + ", groupBound := " +
                g.group_bound + ", groupDigits := " + expr(g.group_digits) +
                ", residues := " + expr(g.residues) + ", accumulators := " +
                (g.accumulators == kNone ? std::string("none")
                                         : "some (" + expr(g.accumulators) + ")") +
                " })";
    }
    out += ", quotientLo := " + int_text(m.quotient_lo) + ", qmax := " + m.qmax +
           ", quotient := " +
           (m.quotient == kNone ? std::string("none")
                                : "some (" + expr(m.quotient) + ")") +
           ", digits := " + digits + ", radix := " + m.radix +
           ", ranges := " + ids(m.ranges) + ", bounds := " + bounds +
           ", grouped := " + grouped;
    if (m.target) out += ", target := some " + target(*m.target);
    if (!m.span.empty()) out += ", span := some " + m.span;
    return out + " }";
  }

  std::string body(const ir::Predicate &q) {
    if (!q.unmodeled.empty())
      plan_export_internal::export_fail("predicate '" + q.name +
                                        "' has no description: " + q.unmodeled);
    const std::string d = num(q.domain);
    switch (q.body) {
      case ir::Predicate::kEqual:
        return ".equal " + d + " " + paren(expr(q.lhs)) + " " +
               paren(expr(q.rhs)) + " " + target(q.target);
      case ir::Predicate::kMem: {
        std::string real;
        if (q.in.implied) {
          real = "(.implied " + int_text(q.in.lo) + " " + int_text(q.in.hi) + ")";
        } else {
          const ir::LookupRealization &l = q.in.lookup;
          static const char *kinds[] = {"direct", "scaled", "shifted",
                                        "digits", "twoSided", "complement"};
          std::string nd = "[";
          for (size_t i = 0; i < l.needles.size(); ++i)
            nd += (i ? ", " : "") + expr(l.needles[i]);
          nd += "]";
          // The schema's scale is 0: no realization scales its needle.
          real = "(.lookup { table := " + num(l.table) + ", group := " +
                 num(l.group) + ", kind := ." + kinds[int(l.kind)] +
                 ", digits := " + num(l.digits) + ", base := " + l.base +
                 ", digitValues := " + ids(l.digit_values) + ", second := " +
                 ids(l.second) + ", needles := " + nd + ", honest := " +
                 l.honest + ", max := " + l.max + ", scale := 0, shift := 0 })";
        }
        const std::string set = q.set != kNone
                                    ? "(.expr (" + expr(q.set) + "))"
                                    : "(.range " + q.range + ")";
        return ".mem " + d + " [" + expr(q.lhs) + "] " + set + " " + real;
      }
      case ir::Predicate::kMod:
        return ".mod " + d + " " + q.q + " " + paren(expr(q.lhs)) + " " +
               paren(expr(q.rhs)) + " " + mod_real(q.mod);
      case ir::Predicate::kCross: {
        const ir::MacRealization &m = q.mac;
        return ".cross " + d + " " + paren(expr(q.lhs)) + " " + num(q.dy) + " " +
               paren(expr(q.rhs)) + " {} { macField := " + num(m.mac_field) +
               ", key := " + num(m.key) +
               (m.blind_x == kNone ? std::string()
                                   : ", blindX := some " + num(m.blind_x)) +
               ", blind := some " + num(m.blind) + ", tag := " + num(m.tag) +
               ", hPredicate := " +
               (m.h_predicate == kNone ? std::string("none")
                                       : "some " + num(m.h_predicate)) +
               ", chunks := " + num(m.chunks) + ", width := " + num(m.width) +
               ", accumulators := " + ids(m.accumulators) +
               ", quotientDigits := " + ids(m.quotient_digits) + " }";
      }
    }
    return "";
  }

  std::string predicate(const ir::Predicate &q) {
    std::string role = ".source";
    if (q.role == ir::Predicate::Role::kRealization) role = ".realization " + num(q.owner);
    if (q.role == ir::Predicate::Role::kType) role = ".type " + num(q.owner);
    return "{ name := " + str(q.name) + ", body := " + body(q) +
           ", reads := " + reads(q.reads) + ", degree := " + degree(q.degree) +
           ", role := " + role + " }";
  }

  std::string table(const ir::Table &t) {
    auto opt = [](Id v) {
      return v == kNone ? std::string("none") : "some " + num(v);
    };
    std::string g = "[";
    for (size_t k = 0; k < t.groups.size(); ++k) {
      const auto &x = t.groups[k];
      std::string ms;
      for (const auto &m : x.members)
        ms += (ms.empty() ? "(" : ", (") + num(m[0]) + ", " + num(m[1]) + ", " +
              num(m[2]) + ", " + num(m[3]) + ")";
      g += (k ? ", " : "") + std::string("{ capacity := ") + num(x.capacity) +
           ", staticMult := " + opt(x.static_mult) + ", lateMult := " +
           opt(x.late_mult) + ", merged := " + (x.merged ? "true" : "false") +
           ", members := [" + ms + "] }";
    }
    const std::string rows = t.rows_expr != kNone
                                 ? "(.expr (" + expr(t.rows_expr) + "))"
                                 : ".range " + t.size;
    return "{ name := " + str(t.name) + ", domain := " + num(t.domain) +
           ", rows := " + rows + ", alpha := " + num(t.alpha) +
           ", groups := " + g + "] }";
  }

  static std::string sampler(const ir::Challenge &c) {
    switch (c.sampler) {
      case ir::Challenge::Sampler::kNode:
        return "(.node " + str(c.node) + ")";
      case ir::Challenge::Sampler::kMinusRange:
        return "(.fieldMinusTables (.range " + c.tmax + "))";
      default:
        return ".full";
    }
  }
  static std::string challenge(const ir::Challenge &c) {
    std::string role = ".source";
    if (c.role == ir::Challenge::Role::kRealization)
      role = ".realization " + num(c.owner);
    if (c.role == ir::Challenge::Role::kUnmodeled) role = ".unmodeled";
    return "{ name := " + str(c.name) + ", field := " + num(c.field) +
           ", phase := " + num(c.phase) + ", size := " + num(c.size) +
           ", sampler := " + sampler(c) + ", role := " + role + " }";
  }
  static std::string message(const ir::Message &m) {
    const std::string where = m.domain == kNone ? "field := some " + num(m.field)
                                                : "domain := " + num(m.domain);
    return "{ value := " + num(m.value) + ", " + where + ", phase := " +
           num(m.phase) + ", size := " + num(m.size) + ", space := " +
           space(m.space) + ", subfieldMessage := " +
           (m.subfield_message ? "true" : "false") + ", realization := .pad " +
           space(m.space) + ", pad := " + str(m.pad) + " }";
  }
  static std::string batch(const ir::Batch &b) {
    return "{ name := " + str(b.name) + ", domain := " + num(b.domain) +
           ", operands := " + (b.bit_operands ? ".bits" : ".columns") +
           ", degree := " + num(b.degree) + ", instances := " +
           num(b.instances) + ", width := " + num(b.width) + ", rounds := " +
           num(b.rounds) + ", pads := " + num(b.pads) +
           // The bit-index sumcheck (compiler/bit_phase.h; the Lean's
           // Batch.bitSumcheck, default false): only when the batch has it.
           (b.bit_sumcheck ? ", bitSumcheck := true" : "") + ", skipDomain := " +
           (b.char2 ? "\"gf256\"" : "\"integers\"") + ", parts := " +
           ids(b.parts) + " }";
  }
  static std::string circuit(const ir::Circuit &c) {
    std::string ents;
    for (const auto &e : c.entries) {
      std::string t;
      switch (e.kind) {
        case ir::CircuitEntry::kTypeCheck:
          t = ".typeCheck " + num(e.id);
          break;
        case ir::CircuitEntry::kAlignment:
          t = ".alignment " + num(e.id);
          break;
        case ir::CircuitEntry::kPred:
          t = ".pred " + num(e.id);
          break;
        default:
          t = ".realization " + real(e.real);
      }
      ents += (ents.empty() ? "" : ", ") + t;
    }
    static const char *kinds[] = {"pub",  "realizationPub", "committed", "pad",
                                  "view", "batchPads",      "filler"};
    std::string ins;
    for (const auto &b : c.inputs) {
      std::string t = "." + std::string(kinds[int(b.kind)]) + " ";
      if (b.kind == ir::InputBlock::kRealizationPub) t += real(b.real) + " ";
      else if (b.kind != ir::InputBlock::kFiller) t += num(b.value) + " ";
      t += num(b.at) + " " + num(b.n);
      ins += (ins.empty() ? "" : ", ") + t;
    }
    return "{ name := " + str(c.name) + ", domain := " + num(c.domain) +
           ", predicates := " + ids(c.predicates) + ", entries := [" + ents +
           "], inputs := [" + ins + "], publicInputs := " + num(c.public_inputs) +
           ", inputCount := " + num(c.input_count) + ", layers := " +
           num(c.layers) + ", wires := " + num(c.wires) + ", terms := " +
           num(c.terms) + " }";
  }

  // Long constants' runs as definitions of their own: with a sink, a
  // constant of more than kRunsInline runs has its runs written into SINK
  // as definitions `constRunsN` of at most kRunsPart runs each, in raw
  // literals (`nat_lit`, so no OfNat instance is synthesized), runs all of
  // length one as their values mapped to (x, 1); the constant reads the
  // definitions appended. The list is the same. Without a sink every
  // constant is written in place.
  void set_runs_sink(std::string *sink) { runs_sink_ = sink; }

 private:
  static constexpr size_t kRunsInline = 8;
  static constexpr size_t kRunsPart = 512;

  std::string const_runs_text(const std::vector<std::string> &entries) {
    const auto runs = const_runs(entries);
    auto digits = [](const std::string &x) {
      return !x.empty() && std::all_of(x.begin(), x.end(), [](char ch) {
               return ch >= '0' && ch <= '9';
             });
    };
    bool split = runs_sink_ != nullptr && runs.size() > kRunsInline;
    bool ones = true;
    for (const auto &[x, c] : runs) {
      split = split && digits(x);
      ones = ones && c == 1;
    }
    if (!split) {
      std::string r;
      for (const auto &[x, c] : runs)
        r += (r.empty() ? "(" : ", (") + x + ", " + num(c) + ")";
      return "[" + r + "]";
    }
    auto lit = [](const std::string &x) { return "(nat_lit " + x + ")"; };
    std::string appended;
    for (size_t at = 0; at < runs.size(); at += kRunsPart) {
      const std::string nm = "constRuns" + std::to_string(runs_defs_++);
      std::vector<std::string> xs;
      for (size_t i = at; i < std::min(runs.size(), at + kRunsPart); ++i)
        xs.push_back(ones ? lit(runs[i].first)
                          : "(" + lit(runs[i].first) + ", " +
                                lit(num(runs[i].second)) + ")");
      *runs_sink_ += "/-- Runs of a constant of the program. -/\ndef " + nm +
                     " : List (Nat × Nat) :=\n  " +
                     (ones ? "List.map (fun x => (x, 1)) " : "") +
                     nat_list(xs, 2) + "\n\n";
      appended += (appended.empty() ? "" : " ++ ") + nm;
    }
    return runs.size() > kRunsPart ? "(" + appended + ")" : appended;
  }

  bool done(Id x) const { return x < done_.size() && done_[x]; }
  static std::vector<Id> kids(const ir::Expr &n) {
    std::vector<Id> k;
    for (Id x : {n.a, n.b, n.c})
      if (x != kNone && n.op != ir::Expr::kRef) k.push_back(x);
    for (Id x : n.args) k.push_back(x);
    return k;
  }
  std::string render(const ir::Expr &n) const {
    auto t = [&](Id k) { return paren(text_[k]); };
    switch (n.op) {
      case ir::Expr::kLeaf:
        return ".leaf " + num(n.x);
      case ir::Expr::kAdd:
        return ".add " + t(n.a) + " " + t(n.b);
      case ir::Expr::kSub:
        return ".sub " + t(n.a) + " " + t(n.b);
      case ir::Expr::kScale:
        return ".scale " + coef(Id(n.x)) + " " + t(n.a);
      case ir::Expr::kMul:
        return ".mul " + t(n.a) + " " + t(n.b);
      case ir::Expr::kReindex:
        return ".reindex idx" + num(n.x) + " " + t(n.a);
      case ir::Expr::kConcat:
        return ".concat " + t(n.a) + " " + t(n.b);
      case ir::Expr::kLinear: {
        const ir::LinearRows &rows = p_.linears.at(n.x);
        std::string r = "[";
        for (size_t i = 0; i < rows.size(); ++i) {
          r += i ? ", [" : "[";
          for (size_t j = 0; j < rows[i].size(); ++j)
            r += (j ? ", (" : "(") + num(rows[i][j].first) + ", " +
                 coef(rows[i][j].second).substr(1);
          r += "]";
        }
        r += "]";
        return ".linear " + r + " " + t(n.a);
      }
      case ir::Expr::kProd:
        return ".prod " + num(n.x) + " " + t(n.a);
      case ir::Expr::kMux:
        return ".mux " + t(n.a) + " " + t(n.b) + " " + t(n.c);
      case ir::Expr::kApply:
        return ".apply " + paren(named_op(Id(n.x))) + " " + t(n.a);
      case ir::Expr::kRef:
        return ".ref " + num(n.x);
      case ir::Expr::kLogic: {
        static const char *ops[] = {".lt", ".leq", ".eq", ".any", ".all"};
        std::string a = "[";
        for (size_t i = 0; i < n.args.size(); ++i)
          a += (i ? ", " : "") + text_[n.args[i]];
        return ".logic " + std::string(ops[int(n.logic)]) + " " + num(n.x) +
               " " + a + "]";
      }
    }
    return "";
  }

  const ir::Program &p_;
  std::string *runs_sink_ = nullptr;
  size_t runs_defs_ = 0;
  std::vector<std::string> text_;
  std::vector<bool> done_;
};

}  // namespace program_printer_internal

// A Lean list literal aligned with a program list of N entries: entry i is
// FN(i), one entry per line at column COL. For certificate printers.
template <class Fn>
std::string aligned_list(size_t n, Fn fn, size_t col = 4) {
  std::string o = "[";
  for (size_t i = 0; i < n; ++i)
    o += (i ? ",\n" + std::string(col, ' ') : "") + fn(i);
  return o + "]";
}

namespace program_printer_internal {

// The natural whose bits are BITS (bit i the i-th), in decimal.
inline std::string mask_decimal(const std::vector<bool> &bits) {
  // Little-endian 32-bit limbs, divided by 10^9 repeatedly.
  std::vector<uint32_t> limbs((bits.size() + 31) / 32, 0);
  for (size_t i = 0; i < bits.size(); ++i)
    if (bits[i]) limbs[i / 32] |= uint32_t(1) << (i % 32);
  while (!limbs.empty() && limbs.back() == 0) limbs.pop_back();
  if (limbs.empty()) return "0";
  std::vector<uint32_t> chunks;
  while (!limbs.empty()) {
    uint64_t rem = 0;
    for (size_t i = limbs.size(); i-- > 0;) {
      const uint64_t cur = (rem << 32) | limbs[i];
      limbs[i] = uint32_t(cur / 1000000000u);
      rem = cur % 1000000000u;
    }
    chunks.push_back(uint32_t(rem));
    while (!limbs.empty() && limbs.back() == 0) limbs.pop_back();
  }
  std::string o = std::to_string(chunks.back());
  for (size_t i = chunks.size() - 1; i-- > 0;) {
    const std::string c = std::to_string(chunks[i]);
    o += std::string(9 - c.size(), '0') + c;
  }
  return o;
}

}  // namespace program_printer_internal

namespace program_printer_internal {

// The natural holding the W-bit entries XS, entry i at bits [W i, W (i+1)),
// in decimal.
inline std::string packed_decimal(const std::vector<uint64_t> &xs, size_t w) {
  std::vector<bool> bits(xs.size() * w, false);
  for (size_t i = 0; i < xs.size(); ++i)
    for (size_t b = 0; b < w; ++b) bits[i * w + b] = (xs[i] >> b) & 1;
  return mask_decimal(bits);
}

// The bits a natural below N needs, at least 1.
inline size_t width_below(uint64_t n) {
  size_t w = 1;
  while (w < 64 && (uint64_t(1) << w) < n) ++w;
  return w;
}

}  // namespace program_printer_internal

// The shared entries' value lists of certificates C as one Lean definition,
// `closures : RealizedProgram.PackedLists`: the entries one after another,
// and each list's first position.
inline std::string print_closures(const ir::Certificates &c) {
  using program_printer_internal::num;
  std::vector<uint64_t> ids, offs{0};
  uint64_t top = 1;
  for (const auto &l : c.expr_vals) {
    for (ir::Id v : l) {
      ids.push_back(v);
      top = std::max<uint64_t>(top, uint64_t(v) + 1);
    }
    offs.push_back(ids.size());
  }
  const size_t idw = program_printer_internal::width_below(top);
  const size_t offw = program_printer_internal::width_below(ids.size() + 1);
  return "/-- The shared expressions' values, packed: each entry's values, sorted, one "
         "after another,\nand each entry's first position. -/\n"
         "def closures : RealizedProgram.PackedLists :=\n  ⟨" +
         program_printer_internal::packed_decimal(ids, idw) + ",\n    " +
         program_printer_internal::packed_decimal(offs, offw) + ", " + num(idw) + ", " +
         num(offw) + "⟩\n\n";
}

// The shared entries' structural annotations of certificates C as one Lean
// definition, `exprAnn : RealizedProgram.ExprAnn`: the bounds, field sets and
// lengths packed, the public mask, and the widths; NFIELDS fields.
inline std::string print_expr_ann(const ir::Certificates &c, size_t nfields) {
  using program_printer_internal::num;
  using program_printer_internal::packed_decimal;
  using program_printer_internal::width_below;
  uint64_t top = 1, ltop = 1, dtop = 1;
  for (uint64_t x : c.expr_max) top = std::max(top, x + 1);
  for (uint64_t x : c.expr_len) ltop = std::max(ltop, x + 1);
  for (uint64_t x : c.expr_deg) dtop = std::max(dtop, x + 1);
  const size_t mw = width_below(top), fw = std::max<size_t>(1, nfields), lw = width_below(ltop),
               dw = width_below(dtop);
  return "/-- The shared expressions' structural annotations: per entry one past the values "
         "it reads,\nthe fields it reads in its own field, whether its coefficient values are "
         "public, its length. -/\n"
         "def exprAnn : RealizedProgram.ExprAnn :=\n  ⟨" +
         packed_decimal(c.expr_max, mw) + ",\n    " + packed_decimal(c.expr_fields, fw) +
         ",\n    " + program_printer_internal::mask_decimal(c.expr_pub) + ",\n    " +
         packed_decimal(c.expr_len, lw) + ",\n    " + packed_decimal(c.expr_deg, dw) + ",\n    " +
         program_printer_internal::mask_decimal(c.expr_zero) + ", " + num(mw) + ", " + num(fw) +
         ", " + num(lw) + ", " + num(dw) + "⟩\n\n";
}

// The degree annotations of certificates C as one Lean definition, `degAnn :
// List RealizedProgram.DegAnn`: per challenge the values' and the shared
// entries' degrees, packed, and their width.
inline std::string print_deg_ann(const ir::Certificates &c) {
  using program_printer_internal::num;
  using program_printer_internal::packed_decimal;
  using program_printer_internal::width_below;
  std::string o =
      "/-- The degree annotations: per challenge the degrees of the values' and the shared "
      "expressions'\ncoordinates, packed. -/\ndef degAnn : List RealizedProgram.DegAnn :=\n  [";
  for (size_t k = 0; k < c.deg_vals.size(); ++k) {
    uint64_t top = 1;
    for (uint64_t x : c.deg_vals[k]) top = std::max(top, x + 1);
    for (uint64_t x : c.deg_refs[k]) top = std::max(top, x + 1);
    const size_t w = width_below(top);
    o += std::string(k ? ",\n   " : "") + "⟨" + packed_decimal(c.deg_vals[k], w) + ", " +
         packed_decimal(c.deg_refs[k], w) + ", " + num(w) + "⟩";
  }
  return o + "]\n\n";
}

// The reads annotation of certificates C as one Lean definition, `readsAnn :
// RealizedProgram.ReadsAnn`: per value the codes of its reads, packed one
// after another, and each list's first position.
inline std::string print_reads_ann(const ir::Certificates &c) {
  using program_printer_internal::num;
  std::vector<uint64_t> ids, offs{0};
  uint64_t top = 1;
  for (const auto &l : c.val_reads) {
    for (uint64_t x : l) {
      ids.push_back(x);
      top = std::max<uint64_t>(top, x + 1);
    }
    offs.push_back(ids.size());
  }
  const size_t idw = program_printer_internal::width_below(top);
  const size_t offw = program_printer_internal::width_below(ids.size() + 1);
  return "/-- The values' reads, packed: each value's read codes, sorted, one after another, "
         "and each\nvalue's first position. -/\n"
         "def readsAnn : RealizedProgram.ReadsAnn :=\n  ⟨⟨" +
         program_printer_internal::packed_decimal(ids, idw) + ",\n    " +
         program_printer_internal::packed_decimal(offs, offw) + ", " + num(idw) + ", " +
         num(offw) + "⟩⟩\n\n";
}

// The honest checks' shared tables of certificates C as one Lean definition,
// `tables : RealizedProgram.HonestTables`: the value lists aligned with the
// program's predicates, the two masks as naturals, the owners' lists.
inline std::string print_honest_tables(const ir::Certificates &c) {
  using program_printer_internal::num;
  auto ids = [](const std::vector<ir::Id> &v) {
    std::string o = "[";
    for (size_t i = 0; i < v.size(); ++i) o += (i ? ", " : "") + num(v[i]);
    return o + "]";
  };
  std::string o =
      "/-- The honest checks' shared tables: per predicate its values, the masks of the values\n"
      "reading a late and a generated late value, the lookups' digits and the committed digits. -/\n"
      "def tables : RealizedProgram.HonestTables where\n  predVals := ";
  o += aligned_list(c.pred_vals.size(), [&](size_t i) { return ids(c.pred_vals[i]); }) +
       "\n";
  o += "  lateBad := " + program_printer_internal::mask_decimal(c.late_bad) + "\n";
  o += "  genBad := " + program_printer_internal::mask_decimal(c.gen_bad) + "\n";
  o += "  lookupOwners := " +
       aligned_list(c.lookup_owners.size(), [&](size_t i) {
         const auto &x = c.lookup_owners[i];
         return "(" + num(x.value) + ", ⟨" + num(x.pid) + ", " +
                (x.second ? "true" : "false") + ", " + num(x.idx) + "⟩)";
       }) +
       "\n";
  o += "  commOwners := " +
       aligned_list(c.comm_owners.size(), [&](size_t i) {
         const auto &x = c.comm_owners[i];
         return "(" + num(x.value) + ", ⟨" + num(x.mod) + ", " + num(x.j) + ", " +
                num(x.lk) + ", " + num(x.k) + "⟩)";
       }) +
       "\n\n";
  return o;
}

// The completeness certificate of certificates C as Lean definitions,
// `gens : RealizedProgram.Gens` aligned with the program's values and
// `cderivs : RealizedProgram.CDerivations` aligned with its predicates.
inline std::string print_completion(const ir::Certificates &c) {
  using program_printer_internal::num;
  using G = ir::Certificates::Gen;
  using S = ir::Certificates::CStep;
  auto gen = [](const G &g) -> std::string {
    switch (g.kind) {
      case G::kNone: return ".none";
      case G::kSource: return ".source";
      case G::kLookupDigit:
        return "(.lookupDigit " + num(g.a) + " " + (g.second ? "true" : "false") + " " +
               num(g.b) + ")";
      case G::kCommDigit:
        return "(.commDigit " + num(g.a) + " " + num(g.b) + " " + num(g.c) + " " + num(g.d) +
               ")";
      case G::kSpec: return "(.spec " + num(g.a) + ")";
      case G::kStaticHist: return "(.staticHist " + num(g.a) + " " + num(g.b) + ")";
      case G::kTag: return "(.tag " + num(g.a) + ")";
      case G::kAcc: return "(.acc " + num(g.a) + ")";
      case G::kQuotDigit: return "(.quotDigit " + num(g.a) + ")";
      case G::kDigitsAcc: return "(.digitsAcc " + num(g.a) + ")";
      case G::kLowDigit: return "(.lowDigit " + num(g.a) + " " + num(g.b) + ")";
      case G::kLateHist: return "(.lateHist " + num(g.a) + " " + num(g.b) + ")";
    }
    return ".none";
  };
  auto step = [](const S &x) -> std::string {
    switch (x.kind) {
      case S::kSource: return ".source";
      case S::kQuotIn: return ".quotIn " + num(x.id);
      case S::kDigitRow: return ".digitRow " + num(x.id);
      case S::kMacRow:
        return ".macRow ⟨" + num(x.id) + ", " + (x.x_side ? "true" : "false") + "⟩";
      case S::kPadBool: return ".padBool";
      case S::kHyp: return ".hyp " + num(x.id);
      case S::kCommIn: return "(.commIn " + num(x.id) + " " + num(x.j) + ")";
      case S::kCommRow: {
        std::string l = "[";
        for (size_t k = 0; k < x.lks.size(); ++k) l += (k ? ", " : "") + num(x.lks[k]);
        return "(.commRow " + num(x.id) + " " + l + "])";
      }
      case S::kSpecProd: return ".specProd " + num(x.id);
      case S::kSpecRow: return ".specRow " + num(x.id);
      case S::kFieldRow: return ".fieldRow";
      case S::kTwoTail:
        return ".twoTail ⟨" + num(x.id) + ", " + (x.x_side ? "true" : "false") + "⟩";
    }
    return ".hyp 0";
  };
  std::string o =
      "/-- The completeness certificate's generators, per value. -/\n"
      "def gens : RealizedProgram.Gens :=\n  " +
      aligned_list(c.gens.size(), [&](size_t i) { return gen(c.gens[i]); }) + "\n\n";
  o += "/-- The completeness derivations, per predicate, and their packed ranks. -/\n"
       "def cderivs : RealizedProgram.CDerivations :=\n  ⟨" +
       aligned_list(c.comp_derivs.size(),
                    [&](size_t i) {
                      std::string d = "[";
                      for (size_t k = 0; k < c.comp_derivs[i].size(); ++k)
                        d += (k ? ", " : "") + step(c.comp_derivs[i][k]);
                      return d + "]";
                    }) +
       ",\n    " + program_printer_internal::packed_decimal(c.comp_ranks, 32) + "⟩\n\n";
  return o;
}

// The honest strategy's certificate of certificates C as its Lean
// definition (`honest : RealizedProgram.HonestCert`), each list aligned
// with the program's; an absent predicate (kNone) is written as the number
// of predicates, which names none.
inline std::string print_certificates(const ir::Certificates &c) {
  const size_t np = c.roles.size();
  using program_printer_internal::num;
  auto id = [np](ir::Id x) { return num(x == ir::kNone ? np : size_t(x)); };
  auto ids = [&](const std::vector<ir::Id> &v) {
    std::string o = "[";
    for (size_t i = 0; i < v.size(); ++i) o += (i ? ", " : "") + id(v[i]);
    return o + "]";
  };
  std::string o;
  o += "/-- The honest checks' pointers: per predicate its MAC site, per value its bound record,\n"
       "per predicate its committed digits' lookups. -/\n"
       "def honest : RealizedProgram.HonestCert :=\n  ⟨" +
       aligned_list(c.roles.size(), [&](size_t i) { return num(c.roles[i]); }) +
       ",\n    " +
       // A value that is not bound has any entry: 0.
       aligned_list(c.bound_recs.size(), [&](size_t i) {
         return c.bound_recs[i] == ir::kNone ? std::string("0") : id(c.bound_recs[i]);
       }) +
       ",\n    " +
       aligned_list(c.comm_digits.size(), [&](size_t i) { return ids(c.comm_digits[i]); }) +
       "⟩\n\n";
  return o;
}

// The derivations of certificates C of program P (Lean `derivs : List
// RealizedProgram.Derivation`, aligned with the predicates): each step a
// `Step` constructor, its expressions as Lean `Expr` terms (a program node
// as the program writes it), integers as Lean Ints. A predicate without a
// derivation has `[]`, and its gap as a comment line above the list.
// MUTANTS, when given, are printed instead as `def mutants : List (ℕ ×
// List Step)` (the derivation cross-test's variants, steps over C's
// expressions).
inline std::string print_derivations(
    const ir::Program &p, const ir::Certificates &c,
    const std::vector<std::pair<size_t, std::vector<ir::DStep>>> *mutants = nullptr) {
  using namespace program_printer_internal;
  Printer pr(p);
  std::vector<std::string> ctext(c.exprs.size());
  std::vector<bool> cdone(c.exprs.size(), false);
  std::function<const std::string &(ir::Id)> ex = [&](ir::Id e) -> const std::string & {
    if (cdone.at(e)) return ctext[e];
    const ir::DExpr &x = c.exprs[e];
    std::string t;
    switch (x.kind) {
      case ir::DExpr::kProgram:
        t = pr.expr(x.id);
        break;
      case ir::DExpr::kLeaf:
        t = ".leaf " + num(x.id);
        break;
      case ir::DExpr::kRef:
        t = ".ref " + num(x.id);
        break;
      case ir::DExpr::kAdd:
        t = ".add " + paren(ex(x.a)) + " " + paren(ex(x.b));
        break;
      case ir::DExpr::kSub:
        t = ".sub " + paren(ex(x.a)) + " " + paren(ex(x.b));
        break;
      case ir::DExpr::kMul:
        t = ".mul " + paren(ex(x.a)) + " " + paren(ex(x.b));
        break;
      case ir::DExpr::kScale:
        t = ".scale (.const " + x.c + ") " + paren(ex(x.a));
        break;
    }
    ctext[e] = std::move(t);
    cdone[e] = true;
    return ctext[e];
  };
  auto nums = [](const std::vector<size_t> &v) {
    std::string o = "[";
    for (size_t i = 0; i < v.size(); ++i) o += (i ? ", " : "") + num(v[i]);
    return o + "]";
  };
  std::function<std::string(const ir::DStep &)> step;
  auto bare = [&](const ir::DStep &s) -> std::string {
    using D = ir::DStep;
    // (a refused derivation, printed as a comment, may lack them)
    auto pr0 = [&]() { return s.premises.empty() ? std::string("?") : num(s.premises[0]); };
    auto ii = [&](size_t i) { return i < s.ints.size() ? int_text(s.ints[i]) : std::string("?"); };
    auto e = [&](size_t i) { return paren(ex(s.exprs.at(i))); };
    switch (s.rule) {
      case D::kRealized:
        return ".realized " + num(s.id);
      case D::kSubst:
        return ".subst " + e(0) + " " + e(1);
      case D::kLinear: {
        std::string o = "[";
        for (size_t i = 0; i < s.premises.size(); ++i)
          o += (i ? ", (" : "(") + num(s.premises[i]) + ", " + int_text(s.coeffs[i]) + ")";
        return ".linear " + o + "] " + e(0) + " " + e(1);
      }
      case D::kLookup: {
        std::string o = "[";
        for (size_t i = 0; i < s.members.size(); ++i)
          o += (i ? ", (" : "(") + num(s.members[i][0]) + ", " + num(s.members[i][1]) +
               ", " + num(s.members[i][2]) + ")";
        return ".lookup " + o + "]";
      }
      case D::kRangeNat:
        return ".rangeNat " + pr0();
      case D::kHoldsIn:
        return ".holdsIn " + pr0();
      case D::kSrc: {
        static const char *src[] = {".const", "(.declared ", "(.nat ", ".prime",
                                    ".opaqueBit", "(.quadRoot ", "(.rootSet ", "(.shift "};
        std::string a = src[s.src];
        if (s.src == D::kDeclared) a += num(s.src_arg) + ")";
        if (s.src == D::kNat || s.src == D::kShift) a += pr0() + ")";
        if (s.src == D::kQuadRoot) a += num(s.tails.at(0)) + " " + pr0() + ")";
        if (s.src == D::kRootSet)
          a += nums(std::vector<size_t>(s.tails.begin(), s.tails.end())) + ")";
        return ".src " + num(s.id) + " " + a;
      }
      case D::kIvlNat:
        return ".ivlNat " + pr0();
      case D::kIvlExpr:
        return ".ivlExpr " + nums(s.premises) + " " + e(0) + " " +
               ii(0) + " " + ii(1);
      case D::kIvlSolve: {
        std::vector<size_t> ks(s.premises.begin() + 1, s.premises.end());
        return ".ivlSolve " + pr0() + " " + nums(ks) + " " + e(0) + " " +
               ii(0) + " " + ii(1);
      }
      case D::kIvlMeet:
        return ".ivlMeet " + pr0() + " " + num(s.premises.at(1));
      case D::kNatIvl:
        return ".natIvl " + pr0();
      case D::kNatComp:
        return ".natComp " + pr0() + " " + num(s.premises.at(1));
      case D::kNatLin: {
        std::vector<size_t> ks(s.premises.begin() + 1, s.premises.end());
        return ".natLin " + pr0() + " " + nums(ks);
      }
      case D::kNatBool:
        return ".natBool " + num(s.id);
      case D::kIvlApply:
        return ".ivlApply " + pr0() + " " +
               (s.premises.size() > 1 ? "(some " + num(s.premises[1]) + ")" : std::string("none")) +
               " " + e(0) + " " + ii(0) + " " + ii(1);
      case D::kIvlLogic:
        return ".ivlLogic " + nums(s.premises) + " " + e(0);
      case D::kGroupedMod:
        return ".groupedMod " + nums(std::vector<size_t>(s.tails.begin(), s.tails.end())) +
               " " + nums(s.premises);
      case D::kFieldDvd:
        return ".fieldDvd " + pr0() + " " + num(s.premises.at(1)) + " " +
               num(s.premises.at(2));
      case D::kLiftConst:
        return ".liftConst " + pr0() + " " + num(s.premises.at(1));
      case D::kTransport:
        return ".transport " + pr0() + " " + num(s.premises.at(1));
      case D::kLift:
        return ".lift " + pr0() + " " + num(s.premises.at(1)) + " " + num(s.premises.at(2));
      case D::kDigits: {
        std::vector<size_t> ds(s.premises.begin() + 1, s.premises.end());
        return ".digits " + pr0() + " " + nums(ds) + " " + ii(0);
      }
      case D::kCongr:
        return ".congr " + pr0();
      case D::kMac: {
        std::vector<size_t> ts(s.tails.begin(), s.tails.end());
        return ".mac " + nums(ts) + " " +
               (s.h == ir::kNone ? std::string("none") : "(some " + num(s.h) + ")") +
               " " + nums(s.premises);
      }
      case D::kLinop:
        // The spectral instance: convolution SRC_ARG, its products' holds.
        return ".linop (.spectral " + num(s.src_arg) + " " + pr0() + ")";
      case D::kConclude:
        return ".conclude " + pr0();
      case D::kHyp:
        return ".hyp " + num(s.id);
      case D::kFact:
        return ".fact " + num(s.id);
      case D::kIvlDisjoint:
        return ".ivlDisjoint " + pr0() + " " + num(s.premises.at(1));
    }
    return "";
  };
  step = [&](const ir::DStep &s) -> std::string {
    const std::string t = bare(s);
    return s.in_dom == ir::kNone ? t : ".inDom " + num(s.in_dom) + " (" + t + ")";
  };
  std::string o;
  for (size_t i = 0; i < c.deriv_gaps.size(); ++i)
    if (!c.deriv_gaps[i].empty()) {
      o += "-- gap " + num(i) + " (" + p.predicates.at(i).name + "): " + c.deriv_gaps[i] + "\n";
      if (i < c.deriv_refused.size() && !c.deriv_refused[i].empty())
        o += "--   refused: " + list_of(c.deriv_refused[i], step) + "\n";
    }
  if (mutants != nullptr)
    return "def mutants : List (ℕ × List Step) :=\n  " +
           aligned_list(mutants->size(), [&](size_t k) {
             return "(" + num((*mutants)[k].first) + ", " +
                    list_of((*mutants)[k].second, step) + ")";
           }) +
           "\n";
  // Sparse: (pid, steps) for every predicate whose derivation is not the
  // default [.realized pid, .conclude 0], in increasing pid.
  std::vector<size_t> listed;
  for (size_t i = 0; i < c.derivations.size(); ++i) {
    const auto &d = c.derivations[i];
    const bool dflt = d.size() == 2 && d[0].rule == ir::DStep::kRealized &&
                      d[0].id == i && d[0].in_dom == ir::kNone &&
                      d[1].rule == ir::DStep::kConclude && d[1].premises == std::vector<size_t>{0} &&
                      d[1].in_dom == ir::kNone;
    if (!dflt) listed.push_back(i);
  }
  o += "/-- The derivations other than [.realized pid, .conclude 0], by predicate. -/\n"
       "def derivs : List (ℕ × List Step) :=\n  " +
       aligned_list(listed.size(), [&](size_t k) {
         const size_t i = listed[k];
         return "(" + num(i) + ", " + list_of(c.derivations[i], step) + ")";
       }) +
       "\n\n";
  o += "/-- Each predicate's rank: above every predicate its derivation cites. -/\n"
       "def ranks : List ℕ :=\n  " +
       nat_list([&] {
         std::vector<std::string> r;
         for (size_t x : c.deriv_ranks) r.push_back(num(x));
         return r;
       }(), 2) +
       "\n\n";
  o += "/-- The shared facts: each with its rank and the steps that state it. -/\n"
       "def shared : List SharedEntry :=\n  " +
       aligned_list(c.shared.size(), [&](size_t k) {
         const ir::SharedFact &e = c.shared[k];
         return "{ fact := .ivl " + num(e.dom) + " " + paren(ex(e.expr)) + " " +
                int_text(e.lo) + " " + int_text(e.hi) + ", rank := " + num(e.rank) +
                ", steps := " + list_of(e.steps, step) + " }";
       }) +
       "\n\n";
  o += "/-- The derivations, as the checker reads them. -/\n"
       "def derivations : Derivations := { derivs := derivs, ranks := ranks, shared := shared }\n\n";
  return o;
}

// The derivations' module of program P with certificates C (META's
// `Derivs`, beside its Program module): print_derivations under the
// Program module's namespace, whose index maps its expressions read.
inline std::string print_derivations_module(const ir::Program &p,
                                            const ir::Certificates &c,
                                            const ExportMeta &meta) {
  const std::string prog = lean_module_name(meta, "Program");
  std::string o;
  o += kLeanLicenseHeader;
  o += "module\n\n"
       "public import GordieHowe.Language.Realizations.Derivation\n"
       "public import " + prog + "\n\n";
  o += "@[expose] public section\n\n";
  o += "/-!\n# GordieHowe derivations: " + meta.config + "-" + meta.profile +
       "\n\n";
  o += "Generated by `lib/gordiehowe/compiler/program_builder.h` from the "
       "lowerings' records; do not edit.\n\n";
  o += "- C++ commit: `" + meta.cpp_commit + "`\n";
  o += "- bench run: `" + meta.run_id + "`\n-/\n\n";
  o += kLeanModuleOptions;
  o += "namespace " + lean_module_name(meta, "Derivs") + "\n\n";
  o += "open GordieHowe.RealizedProgram " + prog + "\n\n";
  o += print_derivations(p, c);
  o += "end " + lean_module_name(meta, "Derivs") + "\n";
  return o;
}

// The Lean module of program P: META names it, DIGEST is the compiled
// system's digest (the module's provenance).
inline std::string print_program(const ir::Program &p, const ExportMeta &meta,
                                 const std::vector<uint8_t> &digest) {
  using namespace program_printer_internal;
  if (!p.unmodeled.empty())
    plan_export_internal::export_fail(p.unmodeled.front());
  Printer pr(p);
  std::string defs;
  std::map<std::string, size_t> seen;
  auto def_name = [&seen](const char *prefix, const std::string &name) {
    // A quoted name cannot hold a newline, « or » (whose UTF-8 starts
    // with the byte 0xc2).
    std::string n;
    for (char ch : name) n += (ch == '\n' || ch == '\xc2') ? '_' : ch;
    std::string base = std::string("\xc2\xab") + prefix + "." + n;
    const size_t k = ++seen[base];
    if (k > 1) base += "#" + std::to_string(k);
    return base + "\xc2\xbb";
  };
  std::vector<std::string> nvalues, nexprs, npreds, ncircs;
  auto add_def = [&defs](std::vector<std::string> &list, const char *type,
                         const char *doc, const std::string &name,
                         const std::string &body) {
    defs += "/-- " + std::string(doc) + " -/\ndef " + name + " : " + type +
            " :=\n  " + body + "\n\n";
    list.push_back(name);
  };
  // The values and the shared expressions are written in place in their
  // lists (no definition of their own: nothing reads them by name), the
  // long constants' runs as definitions before them; the predicates and
  // circuits keep their named definitions.
  std::string runs;
  pr.set_runs_sink(&runs);
  for (const auto &v : p.values) nvalues.push_back(paren(pr.value(v)));
  for (size_t i = 0; i < p.exprs.size(); ++i)
    nexprs.push_back(paren(pr.expr(p.exprs[i])));
  for (const auto &q : p.predicates)
    add_def(npreds, "Predicate", "A predicate of the program.",
            def_name("p", q.name), pr.predicate(q));
  std::string tables, chals, msgs, bts;
  for (size_t t = 0; t < p.tables.size(); ++t)
    tables += (t ? ", " : "") + pr.table(p.tables[t]);
  for (size_t c = 0; c < p.challenges.size(); ++c)
    chals += (c ? ", " : "") + Printer::challenge(p.challenges[c]);
  for (size_t i = 0; i < p.messages.size(); ++i)
    msgs += (i ? ", " : "") + Printer::message(p.messages[i]);
  for (size_t b = 0; b < p.batches.size(); ++b)
    bts += (b ? ", " : "") + Printer::batch(p.batches[b]);
  for (const auto &c : p.circuits)
    add_def(ncircs, "Circuit", "A GKR circuit of the program.",
            def_name("c", c.name), Printer::circuit(c));
  std::string reals;
  for (size_t i = 0; i < p.realization_circuits.size(); ++i)
    reals += (i ? ", " : "") + std::string("(") +
             Printer::real(p.realization_circuits[i].first) + ", " +
             num(p.realization_circuits[i].second) + ")";
  // The spectrally realized convolutions, when there are any (Lean
  // `RealizedProgram.convs`, default []).
  std::string convs;
  for (size_t i = 0; i < p.convs.size(); ++i) {
    const ir::SpectralConv &c = p.convs[i];
    convs += (i ? ", " : "") + std::string("{ source := ") + num(c.source) +
             ", read := " + num(c.read) + ", products := " + num(c.products) +
             ", blocks := " + num(c.blocks) + ", left := " + num(c.left) +
             ", right := " + num(c.right) + ", length := " + num(c.length) +
             ", root := " + c.root + " }";
  }
  if (!convs.empty()) convs = ",\n    convs := [" + convs + "]";
  std::string doms;
  for (size_t d = 0; d < p.domains.size(); ++d)
    doms += (d ? ", " : "") + std::string("{ name := ") + str(p.domains[d].name) +
            ", field := " + num(p.domains[d].field) + " }";
  std::string fl;
  for (size_t i = 0; i < p.fields.size(); ++i)
    fl += (i ? ", " : "") + std::string("{ name := ") + str(p.fields[i].name) +
          ", characteristic := " + p.fields[i].characteristic +
          ", degree := " + num(p.fields[i].degree) + " }";

  const std::string mod = lean_module_name(meta, "Program");
  std::string o;
  o += kLeanLicenseHeader;
  o += "module\n\n"
       "public import GordieHowe.Language.RealizedProgram.Encoding\n\n";
  o += "@[expose] public section\n\n";
  o += "/-!\n# GordieHowe realized program: " + meta.config + "-" +
       meta.profile + "\n\n";
  o += "Generated by `lib/gordiehowe/compiler/plan_program.h` from the "
       "compiled system; do not edit.\n\n";
  o += "- C++ commit: `" + meta.cpp_commit + "`\n";
  o += "- bench run: `" + meta.run_id + "`\n";
  o += "- system digest: `" +
       plan_export_internal::hex(digest.data(), digest.size()) + "`\n-/\n\n";
  o += kLeanModuleOptions;
  // The definitions are data: their compiled code is never run, so the
  // compiler does not extract their closed terms (the module's peak
  // memory).
  o += "set_option compiler.extract_closed false\n\n";
  o += "namespace " + mod + "\n\n";
  o += "open GordieHowe.RealizedProgram\n\n";
  for (size_t i = 0; i < p.index_maps.size(); ++i) {
    if (i < p.index_map_forms.size() && !p.index_map_forms[i].empty()) {
      o += "/-- An index map. -/\ndef idx" + std::to_string(i) +
           " : IndexMap :=\n  " + p.index_map_forms[i] + "\n\n";
      continue;
    }
    auto inum = [](long long x) {
      return x < 0 ? "Int.negSucc " + std::to_string(-x - 1) : std::to_string(x);
    };
    auto triple = [&inum](const std::array<long long, 3> &r) {
      return "(" + inum(r[0]) + ", " + inum(r[1]) + ", " + inum(r[2]) + ")";
    };
    std::vector<std::string> xs;
    for (const auto &g : index_segments(index_runs(p.index_maps[i]))) {
      if (!g.rep) {
        xs.push_back(".run " + triple(g.base[0]));
        continue;
      }
      std::string pat;
      for (size_t t = 0; t < g.base.size(); ++t)
        pat += (t ? ", " : "") + std::string("⟨") + triple(g.base[t]) + ", " +
               triple(g.delta[t]) + "⟩";
      xs.push_back(".rep [" + pat + "] " + std::to_string(g.k));
    }
    o += "/-- An index map. -/\ndef idx" + std::to_string(i) +
         " : IndexMap :=\n  IndexMap.ofSegs " + nat_list(xs, 2) + "\n\n";
  }
  o += runs;
  o += defs;
  // The program's lists: a list of at most kChunk entries is written in
  // place; a longer one is chunks of kChunk entries, each its own
  // definition, appended, so that a list literal's elaboration stays
  // bounded whatever the program's size.
  constexpr size_t kChunk = 1024;
  auto names = [&o](const char *field, const char *type,
                    const std::vector<std::string> &ns) {
    if (ns.size() <= kChunk) {
      std::string l;
      for (const auto &n : ns) l += (l.empty() ? "\n      " : ",\n      ") + n;
      return l;
    }
    std::string appended;
    for (size_t c = 0; c * kChunk < ns.size(); ++c) {
      const std::string nm = std::string(field) + "Chunk" + std::to_string(c);
      std::string l;
      for (size_t i = c * kChunk; i < std::min(ns.size(), (c + 1) * kChunk); ++i)
        l += (l.empty() ? "\n    " : ",\n    ") + ns[i];
      o += "/-- The program's " + std::string(field) + ", chunk " +
           std::to_string(c) + ". -/\ndef " + nm + " : List " + type +
           " :=\n  [" + l + "]\n\n";
      appended += (c ? " ++ " : "") + nm;
    }
    return std::string("\x01") + appended;
  };
  // A list field: its literal, or its chunks appended.
  auto field = [](const std::string &l) {
    return !l.empty() && l[0] == '\x01' ? l.substr(1) : "[" + l + "]";
  };
  const std::string values = field(names("values", "Value", nvalues));
  const std::string exprs = field(names("exprs", "Expr", nexprs));
  const std::string preds = field(names("predicates", "Predicate", npreds));
  const std::string circs = field(names("circuits", "Circuit", ncircs));
  // The statement's member checks, when a member has one.
  std::string checks;
  for (const auto &c : p.checks) {
    std::string args;
    for (uint64_t a : c.args) args += (args.empty() ? "" : ", ") + std::to_string(a);
    checks += std::string(checks.empty() ? "" : ", ") + "{ member := " +
              str(c.member) + ", offset := " + num(c.offset) +
              ", bytes := " + num(c.bytes) + ", check := " + str(c.check) +
              ", args := [" + args + "] }";
  }
  if (!checks.empty()) checks = ", checks := [" + checks + "]";
  o += "/-- The realized program of `" + meta.config + "-" + meta.profile +
       "`. -/\ndef program : RealizedProgram :=\n  { phases := " +
       num(p.phases) + ",\n    statement := { msgLen := " + num(meta.msg_len) +
       ", ctxLen := " + num(meta.ctx_len) + checks + " },\n    fields := [" +
       fl + "],\n    domains := [" + doms + "],\n    values := " + values +
       ",\n    exprs := " + exprs + ",\n    predicates := " + preds +
       ",\n    tables := [" + tables + "],\n    challenges := [" + chals +
       "],\n    messages := [" + msgs + "],\n    batches := [" + bts +
       "],\n    circuits := " + circs + ",\n    realizationCircuits := [" +
       reals + "]" + convs + " }\n\nend " + mod + "\n";
  return o;
}

}  // namespace proofs::gordiehowe::compiler

#endif  // PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_COMPILER_PROGRAM_PRINTER_H_
