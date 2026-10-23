// Copyright 2026 Chad Sharp and Paul Grubbs
// SPDX-License-Identifier: Apache-2.0

// GordieHowe: the compiler's last stage, the realized program of a compiled
// system (realized_program.h).
//
// build_ir(cs) reads the compiled system's value table and predicates:
// every value node with its kind, type, phase, packing-tree node and type
// source, a late value's closed reads and its pad space; every predicate as
// a core predicate over expressions (equal with its target, in with its
// lookup realization, mod_q, the cross-field equal with its MAC), with the
// challenges and late values it reads, its degree in each challenge, and
// its role (source, a realization part of a named predicate, or the type
// check of a value); the lookup tables, challenges, messages, batches and
// GKR circuits.
//
// Numbering: value ids are the constants the expressions read first, then
// the exported nodes in node-id order (so MsgBefore on ids is the C++'s
// message order); an expression DAG node read more than once, and every
// derived value (an affine view, a wiring view, a binding, an expression
// value), is one shared entry, read as kRef; every distinct index map is
// interned once.
//
// An element the structure cannot describe (an operator with no name in
// the schema, an expression operation with no Lean form) fails the build
// with ProgramError; build_ir_or_reason returns why instead.

#ifndef PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_COMPILER_PROGRAM_BUILDER_H_
#define PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_COMPILER_PROGRAM_BUILDER_H_

#include <algorithm>
#include <array>
#include <cstddef>
#include <cstdint>
#include <functional>
#include <map>
#include <optional>
#include <set>
#include <stdexcept>
#include <string>
#include <tuple>
#include <type_traits>
#include <utility>
#include <vector>

#include "gordiehowe/compiler/derivation_check.h"
#include "gordiehowe/compiler/lowering.h"
#include "gordiehowe/compiler/plan_export.h"
#include "gordiehowe/compiler/realized_program.h"
#include "gordiehowe/expr.h"
#include "gordiehowe/ops/operators.h"
#include "gordiehowe/system.h"

namespace proofs::gordiehowe::compiler {

// What a value or a predicate reads from the run, during the build: the
// challenge (its index), the late value or the pad of a late value (value
// keys: node ids, or a constant's key past them).
struct ProgramRead {
  enum Kind { kChal, kLate, kPad } kind = kChal;
  size_t id = 0;
  bool operator<(const ProgramRead &o) const {
    return kind != o.kind ? kind < o.kind : id < o.id;
  }
  bool operator==(const ProgramRead &o) const {
    return kind == o.kind && id == o.id;
  }
};

namespace program_builder_internal {

using plan_export_internal::export_fail;
using ir::Id;
using ir::kNone;

// A natural in base 2^32, for field elements wider than a Bound.
struct BigNat {
  std::vector<uint32_t> d;  // little-endian limbs
  void mul_add(uint64_t m, uint64_t a) {
    unsigned __int128 carry = a;
    for (auto &x : d) {
      const unsigned __int128 t = (unsigned __int128)x * m + carry;
      x = uint32_t(t);
      carry = t >> 32;
    }
    while (carry != 0) {
      d.push_back(uint32_t(carry));
      carry >>= 32;
    }
  }
  std::string dec() const {
    std::vector<uint32_t> v = d;
    std::string out;
    auto zero = [&]() {
      for (uint32_t x : v)
        if (x) return false;
      return true;
    };
    if (zero()) return "0";
    while (!zero()) {
      uint64_t r = 0;
      for (size_t i = v.size(); i-- > 0;) {
        const uint64_t cur = (r << 32) | v[i];
        v[i] = uint32_t(cur / 1000000000u);
        r = cur % 1000000000u;
      }
      std::string part = std::to_string(r);
      if (!zero()) part = std::string(9 - part.size(), '0') + part;
      out = part + out;
    }
    return out;
  }
  static BigNat of_bytes(const uint8_t *b, size_t n) {
    BigNat x;
    for (size_t i = n; i-- > 0;) x.mul_add(256, b[i]);
    return x;
  }
};

template <class S>
class ProgramBuilder : Lowering {
 public:
  using CS = BasicCompiledSystem<S>;
  explicit ProgramBuilder(const CS &cs) : cs_(cs) {}

  // The export's certificates, after run().
  ir::Certificates take_certificates() { return std::move(certs_); }
  // Builds the derivations with the certificates.
  void want_derivations() { want_derivations_ = true; }

  ir::Program run() {
    const auto &N = cs_.nodes();
    classify();
    for (size_t id = 0; id < N.size(); ++id)
      if (N[id].kind == Kind::kChallenge) {
        chal_of_[id] = chals_.size();
        chals_.push_back(id);
      }
    // Every expression's DAG edges, so that a node read twice is shared.
    with_domain_all([&](const auto &d) {
      for (const auto &p : d.predicates()) count_refs(*p.e);
      for (const auto &[id, e] : public_exprs(d)) count_refs(*e);
      for (const auto &[id, e] : expr_values(d)) count_refs(*e);
    });
    // The values, in node order.
    for (size_t d = 0; d < cs_.num_domains(); ++d)
      with_domain(d, [&](const auto &dm) { domain_values(dm); });
    for (size_t k = 0; k < bare_.size(); ++k)
      with_domain(cs_.num_domains() + k, [&](const auto &dm) { bare_values(dm); });
    for (size_t d = 0; d < cs_.num_domains(); ++d)
      with_domain(d, [&](const auto &dm) { domain_predicates(dm); });
    with_domain_all([&](const auto &dm) { mod_predicates(dm); });
    cross_predicates();
    finish();
    return std::move(P_);
  }

 private:
  // ------------------------------------------------------------ records --

  struct ValueRec {
    size_t key = 0, node = SIZE_MAX, domain = 0, phase = 0, size = 0;
    std::vector<size_t> shape;
    // kind: priv, input, opaque, expr, constant, challenge, late, bits,
    // padCopy, message, bound.
    std::string name, kind, node_name, opaque;
    ir::VType type = ir::VType::kField;
    std::string sub;
    Id expr = kNone;                   // expr, bound: its node
    std::vector<std::string> entries;  // constant
    size_t ref = SIZE_MAX;             // challenge / words / late value
    std::vector<size_t> args;          // opaque arguments (keys)
    std::set<ProgramRead> reads;       // late: closed reads
    std::map<size_t, size_t> degree;   // expr: per challenge
    std::string pad_space;             // late
    Id select = kNone;                 // bits: the words' index map
    std::set<size_t> sources;          // a public view's values (keys)
    std::string owner;                 // a realization value's owner
    std::string type_source = "none";  // node | pred | none
    std::string type_pred;             // the check's predicate name
    std::string unmodeled;             // why it has no description
    // A statement value's declared bound N (Ref::bounded); 0: none.
    Bound bound = 0;
  };
  // A predicate's target before batches and circuits are numbered.
  struct TargetRec {
    ir::Target::Kind kind = ir::Target::kAffine;
    size_t domain = 0;
    std::string batch;
    // kRealized: the realized predicate's id.
    size_t realized = 0;
    bool operator==(const TargetRec &o) const {
      return kind == o.kind && domain == o.domain && batch == o.batch;
    }
  };
  struct PredRec {
    std::string name, owner_name, role = "source";
    size_t domain = 0;
    // A lowering's affine row, and an in predicate.
    bool row = false, mem = false;
    size_t needles = 0, size = 0;
    size_t type_value = SIZE_MAX;
    TargetRec target;
    // The body, its value keys and names unresolved.
    ir::Predicate p;
    // A mod's ranges (by the mod's name), a MAC's H half (by name).
    std::string mod_ranges, h_predicate;
    // An integer mod_0, whose realization's target is the predicate's.
    bool mod_target = false;
    // The certificates' records: a two-sided lookup's reconstruction and
    // top rows (by name, "" for none), a MAC's tails.
    std::string recon_row, top_row;
    std::vector<std::string> tails;
    std::set<ProgramRead> reads;
    std::map<size_t, size_t> degree;
    std::set<size_t> values;
  };
  // An expression's node, length, reads, degrees and the value keys it
  // reads.
  struct Ex {
    Id e = kNone;
    size_t n = 0;
    std::set<ProgramRead> reads;
    std::map<size_t, size_t> deg;
    std::set<size_t> values;
  };

  // A spectrally realized convolution (PlanRecords::spectral_convs): its
  // shared source and reading (their entries KS, KR), its operands and the
  // root.
  struct SpecConv {
    const PlanRecords::SpectralConv *rec = nullptr;
    size_t ks = 0, kr = 0;
    Ex src, read, a, b, zero;
    std::string psi;
  };

  static void merge(Ex &a, const Ex &b) {
    a.reads.insert(b.reads.begin(), b.reads.end());
    a.values.insert(b.values.begin(), b.values.end());
  }
  static std::map<size_t, size_t> deg_max(const std::map<size_t, size_t> &a,
                                          const std::map<size_t, size_t> &b) {
    auto o = a;
    for (const auto &[c, x] : b) o[c] = std::max(o[c], x);
    return o;
  }
  static std::map<size_t, size_t> deg_sum(const std::map<size_t, size_t> &a,
                                          const std::map<size_t, size_t> &b) {
    auto o = a;
    for (const auto &[c, x] : b) o[c] += x;
    return o;
  }

  // A node of the arena.
  Id node_of(ir::Expr x) {
    P_.nodes.push_back(std::move(x));
    return Id(P_.nodes.size() - 1);
  }
  Id leaf_node(size_t key, size_t n) {
    ir::Expr x;
    x.op = ir::Expr::kLeaf;
    x.x = key;
    x.n = n;
    return node_of(std::move(x));
  }
  Id unary(ir::Expr::Op op, uint64_t xv, Id a, size_t n) {
    ir::Expr x;
    x.op = op;
    x.x = xv;
    x.a = a;
    x.n = n;
    return node_of(std::move(x));
  }
  Id binary(ir::Expr::Op op, Id a, Id b, size_t n) {
    ir::Expr x;
    x.op = op;
    x.a = a;
    x.b = b;
    x.n = n;
    return node_of(std::move(x));
  }
  Id const_coef(std::string c) {
    ir::Coef k;
    k.c = std::move(c);
    P_.coefs.push_back(std::move(k));
    return Id(P_.coefs.size() - 1);
  }
  Id op_of(ir::NamedOp op) {
    P_.ops.push_back(std::move(op));
    return Id(P_.ops.size() - 1);
  }

  // FN on place D: domain D, or for D past the domains the value forms of
  // field D - num_domains() of bare_, a field no domain commits.
  template <class Fn>
  void with_domain(size_t d, Fn fn) {
    if (d >= cs_.num_domains()) {
      const auto &[field, fobj] = bare_.at(d - cs_.num_domains());
      const auto *sys = static_cast<const typename S::System *>(system());
      const DomainCore *bare = bare_domain(*sys, fobj);
      if (bare == nullptr) export_fail("a field with no domain has no values");
      S::dispatch(field, [&](auto tag) {
        using F = typename decltype(tag)::type;
        const auto *fd = dynamic_cast<const Domain<F> *>(bare);
        if (fd == nullptr) export_fail("a field with no domain is untyped");
        fn(*fd);
      });
      return;
    }
    const DomainBase<S> &dm = cs_.domain(d);
    S::dispatch(dm.field_id, [&](auto tag) {
      using F = typename decltype(tag)::type;
      const auto *fd = dynamic_cast<const Domain<F> *>(&dm);
      if (fd == nullptr) export_fail("domain " + dm.name + " is untyped");
      fn(*fd);
    });
  }
  // The system the compiled system was compiled from, through its first
  // domain's graph.
  const SystemCore *system() {
    if (sys_ == nullptr)
      with_domain(0, [&](const auto &dm) { sys_ = graph(dm).system; });
    return sys_;
  }
  // The place of domain object D: its index, or past the domains for the
  // value forms of a field no domain commits.
  template <class F>
  size_t place_of(const Domain<F> &d) const {
    if (d.index >= 0) return size_t(d.index);
    for (size_t k = 0; k < bare_.size(); ++k)
      if (bare_[k].second == d.fobj) return cs_.num_domains() + k;
    export_fail("a field with no domain that no value reads");
  }
  bool bare_place(size_t d) const { return d >= cs_.num_domains(); }
  template <class Fn>
  void with_domain_all(Fn fn) {
    for (size_t d = 0; d < cs_.num_domains(); ++d) with_domain(d, fn);
  }

  // ------------------------------------------------------- classification --

  // Whether node ID is late (advice of phase >= 1).
  bool late(size_t id) const {
    return cs_.nodes()[id].kind == Kind::kAdvice && cs_.phase(id) >= 1;
  }

  // The domain of node ID: its own, or the domain of its field.
  // A node of a field no domain commits has its field's place past the
  // domains (bare_).
  int domain_of(size_t id) const {
    const Node &n = cs_.nodes()[id];
    if (n.domain >= 0) return n.domain;
    for (size_t d = 0; d < cs_.num_domains(); ++d)
      if (cs_.domain(d).field_id == n.field && cs_.domain(d).fobj == n.fobj)
        return int(d);
    for (size_t k = 0; k < bare_.size(); ++k)
      if (bare_[k].second == n.fobj) return int(cs_.num_domains() + k);
    return -1;
  }

  // Whether public computation ID reads a challenge, through public
  // computations and derived values; a message ends the walk.
  bool reads_challenge(size_t id, std::map<size_t, bool> &memo) const {
    auto it = memo.find(id);
    if (it != memo.end()) return it->second;
    memo[id] = false;
    const Node &n = cs_.nodes()[id];
    bool r = n.kind == Kind::kChallenge;
    if (!r && n.kind != Kind::kPublicMessage)
      for (size_t d : n.deps) r = r || reads_challenge(d, memo);
    memo[id] = r;
    return r;
  }

  // A parameter reader over an operator's bytes.
  struct Params {
    const std::vector<uint8_t> &b;
    size_t at = 0;
    uint64_t u64() {
      if (at + 8 > b.size()) export_fail("operator parameters end early");
      uint64_t x = 0;
      for (size_t i = 0; i < 8; ++i) x |= uint64_t(b[at + i]) << (8 * i);
      at += 8;
      return x;
    }
    std::string str() {
      const size_t n = size_t(u64());
      if (at + n > b.size()) export_fail("operator parameters end early");
      std::string s(b.begin() + long(at), b.begin() + long(at + n));
      at += n;
      return s;
    }
    std::vector<uint8_t> bytes(size_t n) {
      if (at + n > b.size()) export_fail("operator parameters end early");
      std::vector<uint8_t> s(b.begin() + long(at), b.begin() + long(at + n));
      at += n;
      return s;
    }
    bool done() const { return at == b.size(); }
  };

  // The sources of public view N (its description: "wiring", then each
  // coordinate's node, ~0 for a zero, and index), or false.
  static bool public_wiring(const Node &n,
                            std::vector<std::pair<size_t, size_t>> &src) {
    Params p{n.descr};
    if (n.descr.size() < 14 ||
        std::string(n.descr.begin() + 8, n.descr.begin() + 14) != "wiring")
      return false;
    if (p.str() != "wiring") return false;
    p.u64();
    const size_t c = size_t(p.u64());
    for (size_t i = 0; i < c; ++i) {
      const uint64_t nd = p.u64(), k = p.u64();
      src.push_back({nd == ~uint64_t(0) ? kZeroCoordinate : size_t(nd), size_t(k)});
    }
    return p.done();
  }

  // Whether node ID was declared by a core realization's lowering (the
  // MAC, assert_mod, assert_int_equal, conv, range), and that lowering.
  std::string core_pass(size_t id) const {
    static const std::set<std::string> core = {"mac-equality", "mod",
                                               "int-equal", "conv", "range"};
    for (const auto &l : cs_.records().lowered)
      if (id >= l.first && id < l.end && core.count(l.name)) return l.name;
    return "";
  }
  bool core_lowered(size_t id) const { return !core_pass(id).empty(); }
  // The bound N on every coordinate of the statement value NAME that the
  // member checks recorded against it imply, by the checks' meanings (Lean
  // `MemberCheck.kind?`, `MemberCheck.entryBound?`, `MemberHolds`): an entry
  // check `below q` (falcon_key_canonical [q], falcon_challenge_canonical
  // [q], falcon_ring_key_u16le [n, q], u128_halves [] with q = 2^128) bounds
  // every coordinate by q, and rsa_modulus_2048 [b, w, L] (`limbBits`) every
  // limb by 2^w; the smallest such bound. The verifier rejects every
  // statement outside it, so the program declares it as the value's
  // statement bound (Lean `Value.bound`, `declaredRanges`), which the
  // interval checks read. 0: no check bounds the value.
  Bound check_bound(const std::string &name) const {
    Bound out = 0;
    auto take = [&out](Bound b) {
      if (b != 0 && (out == 0 || b < out)) out = b;
    };
    for (const auto &c : cs_.records().member_checks) {
      // The value of member c (Lean `isMemberOf`): `statement.<member>`, or
      // the member's name itself (`In::check_value`).
      if (name != "statement." + c.member && name != c.member) continue;
      const auto &a = c.args;
      if ((c.check == "falcon_key_canonical" ||
           c.check == "falcon_challenge_canonical") &&
          a.size() == 1)
        take(Bound(a[0]));
      else if (c.check == "falcon_ring_key_u16le" && a.size() == 2)
        take(Bound(a[1]));
      else if (c.check == "u128_halves" && a.empty())
        take(Bound(1) << 127 << 1);
      else if (c.check == "rsa_modulus_2048" && a.size() == 3 && a[1] < 128)
        take(Bound(1) << a[1]);
    }
    return out;
  }
  // Whether NAME is the direct conv realization's predicate <conv>.products,
  // its <conv>.c declared by the conv lowering.
  bool conv_products(const std::string &name) const {
    static const std::string suffix = ".products";
    if (name.size() <= suffix.size() ||
        name.compare(name.size() - suffix.size(), suffix.size(), suffix) != 0)
      return false;
    const std::string c = name.substr(0, name.size() - suffix.size()) + ".c";
    const auto &N = cs_.nodes();
    for (size_t id = 0; id < N.size(); ++id)
      if (N[id].name == c && core_pass(id) == "conv") return true;
    return false;
  }

  // Each node's class: a value, a derived value (an expression), a pad
  // (implicit), or none (host inputs, Bytes statements, values only a
  // realization circuit reads).
  void classify() {
    const auto &N = cs_.nodes();
    cls_.assign(N.size(), kValue);
    std::map<size_t, bool> memo;
    for (const auto &m : cs_.records().macs) powers_of_[m.powers] = &m;
    // assert_in's powers of gamma, a public expression of it.
    for (const auto &t : cs_.records().in_lookups)
      if (t.powers != SIZE_MAX) in_powers_[t.powers] = &t;
    // The fields no domain commits that values lie in (the odd/odd MAC's
    // key, powers, tag and pad), in node order.
    for (const Node &n : N) {
      if (n.domain >= 0 || n.fobj == nullptr || n.kind == Kind::kHostInput ||
          n.type.base == Base::kBytes)
        continue;
      bool domain = false;
      for (size_t d = 0; d < cs_.num_domains(); ++d)
        domain = domain || (cs_.domain(d).field_id == n.field &&
                            cs_.domain(d).fobj == n.fobj);
      bool known = false;
      for (const auto &b : bare_) known = known || b.second == n.fobj;
      if (!domain && !known) bare_.push_back({n.field, n.fobj});
    }
    for (size_t id = 0; id < N.size(); ++id) {
      const Node &n = N[id];
      if (n.kind == Kind::kPad) {
        cls_[id] = kPadNode;
      } else if (n.kind == Kind::kHostInput || n.type.base == Base::kBytes ||
                 (n.kind == Kind::kConstant && n.n == 0)) {
        // Host inputs, Bytes statements and the certify notes' empty
        // constants.
        cls_[id] = kNoClass;
      } else if (n.kind == Kind::kDerived) {
        cls_[id] = kDerivedNode;
      } else if (std::vector<std::pair<size_t, size_t>> src;
                 n.kind == Kind::kPublicCompute && public_wiring(n, src)) {
        // A view of public values (system.h's wire): a public value
        // defined by its view.
        public_wiring_[id] = std::move(src);
      } else if (n.kind == Kind::kPublicCompute && !n.expression &&
                 !powers_of_.count(id) && !in_powers_.count(id) &&
                 reads_challenge(id, memo)) {
        // A compiler closure over a challenge that only a realization
        // circuit reads (the lookups' weights).
        cls_[id] = kNoClass;
      }
    }
    with_domain_all([&](const auto &d) {
      // A source value bound to its digits has no cell; it stays a value
      // of the source program, defined by its binding (kind bound). A
      // core realization's bound value is a derived value.
      for (const auto &[id, l] : bindings(d)) {
        cls_[id] = core_lowered(id) ? kDerivedNode : kValue;
        if (cls_[id] == kValue) bound_.insert(id);
      }
      for (const auto &[id, e] : expr_values(d)) cls_[id] = kDerivedNode;
    });
    // A view of public values is a public value, defined by its view (an
    // operator's public operand: a slice of the MAC's powers).
    std::map<size_t, std::vector<size_t>> sources;
    with_domain_all([&](const auto &d) {
      for (const auto &[id, l] : derived_views(d))
        for (const auto &t : l.terms) {
          sources[id].push_back(t.node);
          for (const auto &op : t.chain)
            sources[id].insert(sources[id].end(), op->deps.begin(), op->deps.end());
        }
      for (const auto &[id, w] : wiring_views(d))
        for (const auto &[nd, i] : w)
          if (nd != kZeroCoordinate) sources[id].push_back(nd);
    });
    for (size_t id = 0; id < N.size(); ++id) {
      if (cls_[id] != kDerivedNode || N[id].kind != Kind::kDerived) continue;
      const auto &src = sources[id];
      bool pub = !src.empty();
      for (size_t d : src)
        pub = pub && cls_[d] == kValue &&
              (is_public(N[d].kind) || public_view_.count(d));
      if (pub) {
        cls_[id] = kValue;
        public_view_.insert(id);
      }
    }
    // Pads and the late values they mask.
    for (size_t id = 0; id < N.size(); ++id) {
      if (!late(id)) continue;
      size_t p = SIZE_MAX;
      if (N[id].masked_by >= 0) {
        p = size_t(N[id].masked_by);
      } else {
        for (size_t q = 0; q < N.size(); ++q)
          if (N[q].kind == Kind::kPad && N[q].auto_pad &&
              N[q].name == "pad(" + N[id].name + ")")
            p = q;
      }
      if (p == SIZE_MAX) {
        gap("late value '" + N[id].name + "' has no pad");
        continue;
      }
      late_of_pad_[p] = id;
      pad_of_late_[id] = p;
    }
  }

  // ---------------------------------------------------------- encoding --

  template <class F>
  static std::string enc(const F &f, const typename F::Elt &x) {
    if constexpr (F::kCharacteristicTwo) {
      uint8_t b[F::kBytes];
      f.to_bytes_field(b, x);
      return BigNat::of_bytes(b, F::kBytes).dec();
    } else {
      if (characteristic_wide(f)) {
        uint8_t b[F::kBytes];
        f.to_bytes_field(b, x);
        return BigNat::of_bytes(b, F::kBytes).dec();
      }
      if (subfield_contains(f, x)) return bound_str(nat_of(f, x));
      return extension_nat(f, x);
    }
  }
  // An odd extension element as sum_i c_i p^i over its stored coordinates.
  template <class F>
  static std::string extension_nat(const F &f, const typename F::Elt &x) {
    using plan_export_internal::has_coordinate_array;
    const Bound p = field_characteristic(f);
    if (p >> 64) export_fail("an extension of a prime above 2^64");
    std::vector<Bound> c;
    if constexpr (has_coordinate_array<F>::value) {
      for (size_t i = 0; i < x.e.size(); ++i) {
        typename F::Elt y{};
        y.e[0] = x.e[i];
        c.push_back(nat_of(f, y));
      }
    } else if constexpr (std::is_same_v<F, Fp64G2>) {
      typename F::Elt y{};
      y.re = x.re;
      c.push_back(nat_of(f, y));
      y.re = x.im;
      c.push_back(nat_of(f, y));
    } else {
      export_fail("an extension element with no known coordinates");
    }
    BigNat b;
    for (size_t i = c.size(); i-- > 0;) b.mul_add(uint64_t(p), uint64_t(c[i]));
    return b.dec();
  }

  // ------------------------------------------------------ value tables --

  // The constant of domain D with ENTRIES (interned), its key.
  size_t constant(size_t d, std::vector<std::string> entries) {
    auto k = std::make_pair(d, entries);
    auto it = consts_.find(k);
    if (it != consts_.end()) return it->second;
    ValueRec v;
    v.key = cs_.nodes().size() + const_recs_.size();
    v.kind = "constant";
    v.type = ir::VType::kField;
    v.domain = d;
    v.size = entries.size();
    v.shape = {entries.size()};
    v.entries = std::move(entries);
    v.name = "const" + std::to_string(const_recs_.size());
    const_recs_.push_back(v);
    consts_.emplace(std::move(k), v.key);
    return v.key;
  }
  template <class F>
  size_t constant_elts(const Domain<F> &d, const std::vector<typename F::Elt> &c) {
    std::vector<std::string> e;
    for (const auto &x : c) e.push_back(enc(d.field(), x));
    return constant(place_of(d), std::move(e));
  }
  template <class F>
  size_t repeat_const(const Domain<F> &d, const typename F::Elt &x, size_t n) {
    return constant(place_of(d),
                    std::vector<std::string>(n, enc(d.field(), x)));
  }

  // Index map IDX (interned).
  Id index_map(std::vector<size_t> idx) {
    auto it = idx_.find(idx);
    if (it != idx_.end()) return it->second;
    const Id k = Id(P_.index_maps.size());
    P_.index_maps.push_back(idx);
    idx_.emplace(std::move(idx), k);
    return k;
  }

  // Index map IDX (interned), written as the Lean definition FORM (an
  // `IndexMap.*` constructor of Encoding.lean whose entries are IDX) in
  // place of its runs.
  Id index_map_named(std::vector<size_t> idx, const std::string &form) {
    const Id k = index_map(std::move(idx));
    if (P_.index_map_forms.size() <= k) P_.index_map_forms.resize(k + 1);
    P_.index_map_forms[k] = form;
    return k;
  }

  // The packing-tree node of a value of degree D in domain DM, or the
  // field's name when D is no node.
  template <class F>
  std::string tree_node(const Domain<F> &dm, size_t D) const {
    const DomainPlan &p = plan_of(size_t(dm.index));
    bool node = false;
    for (const auto &t : p.tree) node = node || t.degree == D;
    const bool char2 = F::kCharacteristicTwo;
    const size_t deg = node ? D : p.field_degree;
    if (deg == p.field_degree) return dm.field_name();
    if (char2 && deg == 1) return "bit";
    return std::string(char2 ? "GF(2^" : "GF(p^") + std::to_string(deg) + ")";
  }
  const DomainPlan &plan_of(size_t d) const {
    auto it = plans_.find(d);
    if (it == plans_.end())
      it = plans_.emplace(d, cs_.compiled_domain(d).plan()).first;
    return it->second;
  }

  // The type of node N, its subfield's name, and its packing-tree node.
  template <class F>
  void type_of(const Domain<F> &dm, const Node &n, ValueRec &v) const {
    const size_t K = plan_of(size_t(dm.index)).field_degree;
    switch (n.type.base) {
      case Base::kBit:
        v.type = ir::VType::kBit;
        v.node_name = tree_node(dm, 1);
        return;
      case Base::kSubfield: {
        const size_t D = subfield_degree<F>(n.type.degree);
        v.type = ir::VType::kSub;
        v.sub = tree_node(dm, D);
        v.node_name = v.sub;
        return;
      }
      default:
        v.type = ir::VType::kField;
        v.node_name = tree_node(dm, K);
    }
  }
  // The node name of a type: `bit`, the subfield's, none for Field.
  static std::string type_node(const ValueRec &v) {
    if (v.type == ir::VType::kBit) return "bit";
    if (v.type == ir::VType::kSub) return v.sub;
    return "";
  }

  template <class F>
  void domain_values(const Domain<F> &dm) {
    const auto &N = cs_.nodes();
    for (size_t id = 0; id < N.size(); ++id) {
      if (cls_[id] != kValue || domain_of(id) != dm.index) continue;
      const Node &n = N[id];
      ValueRec v;
      v.key = id;
      v.node = id;
      v.name = n.name;
      v.domain = size_t(dm.index);
      v.phase = cs_.phase(id);
      v.size = n.n;
      v.shape = n.shape.empty() ? std::vector<size_t>{n.n} : n.shape;
      type_of(dm, n, v);
      v.bound = n.stmt_bound;
      // A member check's bound, where it lies within the field (Lean
      // `leafIvl` reads a bound N <= p).
      if (v.bound == 0) {
        const Bound cb = check_bound(n.name);
        if (cb != 0 && cb <= field_characteristic(dm.field())) v.bound = cb;
      }
      switch (n.kind) {
        case Kind::kPublicInput:
          v.kind = "input";
          break;
        case Kind::kConstant: {
          v.kind = "constant";
          const auto c =
              static_cast<const SystemCore *>(graph(dm).system)
                  ->template constant_values<F>(id);
          for (const auto &x : c) v.entries.push_back(enc(dm.field(), x));
          break;
        }
        case Kind::kChallenge:
          v.kind = "challenge";
          v.ref = id;
          break;
        case Kind::kPublicMessage:
          v.kind = "message";
          v.ref = n.deps.at(0);
          break;
        case Kind::kBitView: {
          v.kind = "bits";
          v.ref = n.deps.at(0);
          const auto &views = bit_views(dm);
          auto it = views.find(id);
          if (it == views.end())
            v.unmodeled = "bit view '" + n.name + "' has no words";
          else
            v.select = index_map(it->second);
          break;
        }
        case Kind::kPadCopy: {
          v.kind = "padCopy";
          auto it = late_of_pad_.find(n.deps.at(0));
          if (it == late_of_pad_.end())
            v.unmodeled = "pad copy '" + n.name + "' copies no late value's pad";
          else
            v.ref = it->second;
          break;
        }
        case Kind::kDerived:
          v.kind = "expr";
          break;
        case Kind::kPublicCompute:
          if (n.expression || powers_of_.count(id) || in_powers_.count(id) ||
              public_wiring_.count(id)) {
            v.kind = "expr";
          } else {
            v.kind = "opaque";
            v.opaque = n.name;
            // Its arguments are values, or the statement's bytes, which are
            // no value (an opaque value with no argument reads the
            // statement only).
            for (size_t a : n.deps) {
              if (cls_[a] == kValue) {
                v.args.push_back(a);
              } else if (!(N[a].kind == Kind::kPublicInput &&
                           N[a].type.base == Base::kBytes)) {
                v.unmodeled = "opaque public value '" + n.name + "' reads '" +
                              N[a].name + "', which is neither a value nor "
                              "the statement's bytes";
              }
            }
          }
          break;
        case Kind::kPrivateInput:
        case Kind::kAdvice:
          v.kind = bound_.count(id) ? "bound" : late(id) ? "late" : "priv";
          break;
        default:
          v.kind = "priv";
          v.unmodeled = "node '" + n.name + "' of an unexported kind";
      }
      vals_[id] = std::move(v);
    }
  }

  // The values of field DM no domain commits: a challenge, a public
  // expression of it (the MAC's chunk powers and their views), a late
  // value and its message. Their place is past the domains, their type
  // Field.
  template <class F>
  void bare_values(const Domain<F> &dm) {
    const auto &N = cs_.nodes();
    const size_t place = place_of(dm);
    for (size_t id = 0; id < N.size(); ++id) {
      if (cls_[id] != kValue || domain_of(id) != int(place)) continue;
      const Node &n = N[id];
      ValueRec v;
      v.key = id;
      v.node = id;
      v.name = n.name;
      v.domain = place;
      v.phase = cs_.phase(id);
      v.size = n.n;
      v.shape = n.shape.empty() ? std::vector<size_t>{n.n} : n.shape;
      v.type = ir::VType::kField;
      v.node_name = bare_field_name(place);
      if (n.kind == Kind::kChallenge) {
        v.kind = "challenge";
        v.ref = id;
      } else if (n.kind == Kind::kPublicMessage) {
        v.kind = "message";
        v.ref = n.deps.at(0);
      } else if (n.kind == Kind::kAdvice && late(id)) {
        v.kind = "late";
      } else if (n.kind == Kind::kPublicCompute &&
                 (powers_of_.count(id) || public_wiring_.count(id))) {
        v.kind = "expr";
      } else {
        v.kind = "priv";
        v.unmodeled = "value '" + n.name + "' of a field no domain commits is "
                      "not a challenge, a challenge's public expression, a "
                      "late value or its message";
      }
      vals_[id] = std::move(v);
    }
  }

  // The name of the field of place D past the domains: GF(2^w).
  std::string bare_field_name(size_t d) const {
    return S::dispatch(bare_.at(d - cs_.num_domains()).first, [](auto tag) {
      using F = typename decltype(tag)::type;
      if constexpr (F::kCharacteristicTwo) {
        return "GF(2^" + std::to_string(F::kBits) + ")";
      } else {
        export_fail("a field no domain commits that is not binary");
        return std::string();
      }
    });
  }

  // ---------------------------------------------------------- reads --

  // The closed reads of late value X's honest computation: the
  // challenges and pads reached through its dependencies, a late
  // dependency contributing its own closed reads (never itself).
  const std::set<ProgramRead> &late_reads(size_t x) {
    auto it = late_reads_.find(x);
    if (it != late_reads_.end()) return it->second;
    late_reads_[x] = {};
    std::set<ProgramRead> out;
    std::set<size_t> seen;
    std::function<void(size_t)> go = [&](size_t id) {
      if (!seen.insert(id).second) return;
      const Node &n = cs_.nodes()[id];
      if (n.kind == Kind::kChallenge) {
        out.insert({ProgramRead::kChal, chal_of_.at(id)});
        return;
      }
      if (n.kind == Kind::kPad) {
        auto l = late_of_pad_.find(id);
        // A pad masking no message (a key pad, Node::key_pad) is read by no
        // message's description.
        if (l == late_of_pad_.end()) {
          gap("pad '" + n.name + "' masks no late value");
          return;
        }
        out.insert({ProgramRead::kPad, l->second});
        return;
      }
      if (id != x && late(id)) {
        for (const auto &r : late_reads(id)) out.insert(r);
        return;
      }
      for (size_t d : n.deps) go(d);
    };
    go(x);
    out.erase({ProgramRead::kPad, x});
    late_reads_[x] = out;
    return late_reads_[x];
  }

  // What reading value KEY contributes: its reads and degrees.
  void leaf_info(size_t key, Ex &e) {
    e.values.insert(key);
    if (key >= cs_.nodes().size()) return;
    const ValueRec &v = vals_.at(key);
    if (v.kind == "bound") {
      const Ex &x = pub_expr(key);
      e.reads.insert(x.reads.begin(), x.reads.end());
      e.deg = deg_max(e.deg, x.deg);
    } else if (v.kind == "challenge") {
      e.reads.insert({ProgramRead::kChal, chal_of_.at(key)});
      e.deg[chal_of_.at(key)] = std::max<size_t>(e.deg[chal_of_.at(key)], 1);
    } else if (v.kind == "late") {
      e.reads.insert({ProgramRead::kLate, key});
    } else if (v.kind == "message") {
      e.reads.insert({ProgramRead::kLate, v.ref});
    } else if (v.kind == "padCopy") {
      e.reads.insert({ProgramRead::kPad, v.ref});
    } else if (v.kind == "expr") {
      const Ex &x = pub_expr(key);
      e.reads.insert(x.reads.begin(), x.reads.end());
      e.deg = deg_max(e.deg, x.deg);
    } else if (v.kind == "opaque") {
      for (size_t a : v.args) {
        Ex t;
        leaf_info(a, t);
        if (!t.deg.empty())
          export_fail("opaque public value '" + v.name + "' reads a challenge");
        e.reads.insert(t.reads.begin(), t.reads.end());
      }
    }
  }

  // ------------------------------------------------------ expressions --

  // The expression of public expression value KEY (its definition).
  const Ex &pub_expr(size_t key) {
    auto it = pub_ex_.find(key);
    if (it != pub_ex_.end()) return it->second;
    Ex out;
    const Node &n = cs_.nodes()[key];
    with_domain(size_t(vals_.at(key).domain), [&](const auto &d) {
      if (auto m = powers_of_.find(key); m != powers_of_.end()) {
        out = powers_expr(d, *m->second);
        return;
      }
      if (auto t = in_powers_.find(key); t != in_powers_.end()) {
        out = in_powers_expr(d, *t->second);
        return;
      }
      if (public_view_.count(key) || bound_.count(key)) {
        out = derived_def(d, key);
        vals_.at(key).sources = out.values;
        return;
      }
      if (auto w = public_wiring_.find(key); w != public_wiring_.end()) {
        out = wiring(d, w->second);
        vals_.at(key).sources = out.values;
        return;
      }
      const auto &pe = public_exprs(d);
      auto e = pe.find(key);
      if (e == pe.end())
        export_fail("public value '" + n.name + "' has no expression");
      out = convert(d, e->second);
    });
    vals_.at(key).expr = out.e;
    vals_.at(key).degree = out.deg;
    return pub_ex_[key] = out;
  }

  // r_c = beta^(c+1), c < nch: the product along nch of beta at the first
  // c + 1 positions and 1 at the others.
  template <class F>
  Ex powers_expr(const Domain<F> &d, const PlanRecords::Mac &m) {
    const size_t nch = m.nch;
    const size_t one = repeat_const(d, d.field().one(), 1);
    std::vector<size_t> idx;
    for (size_t c = 0; c < nch; ++c)
      for (size_t t = 0; t < nch; ++t) idx.push_back(t <= c ? 0 : 1);
    Ex e;
    e.n = nch;
    const Id cat = binary(ir::Expr::kConcat, leaf_node(m.key, cs_.nodes()[m.key].n),
                          leaf_node(one, 1), cs_.nodes()[m.key].n + 1);
    const Id rx = unary(ir::Expr::kReindex, index_map(idx), cat, nch * nch);
    e.e = unary(ir::Expr::kProd, nch, rx, nch);
    leaf_info(m.key, e);
    e.values.insert(one);
    e.deg[chal_of_.at(m.key)] = nch;
    return e;
  }

  // The leaf of node ID: a value, or a reference to a derived value.
  template <class F>
  Ex leaf(const Domain<F> &d, size_t id) {
    const Node &n = cs_.nodes()[id];
    if (cls_[id] == kValue) {
      Ex e;
      e.n = n.n;
      e.e = leaf_node(id, n.n);
      leaf_info(id, e);
      return e;
    }
    if (cls_[id] == kDerivedNode) return derived(d, id);
    export_fail("an expression reads '" + n.name + "', which the program "
                "does not export");
  }

  // Derived value ID as a shared expression.
  template <class F>
  Ex derived(const Domain<F> &d0, size_t id) {
    auto it = derived_.find(id);
    if (it != derived_.end()) return it->second;
    Ex r = share(derived_def(d0, id));
    derived_[id] = r;
    return r;
  }
  // The definition of derived value ID: its binding, affine view, wiring
  // view or expression.
  template <class F>
  Ex derived_def(const Domain<F> &d0, size_t id) {
    const Node &n = cs_.nodes()[id];
    Ex out;
    with_domain(size_t(domain_of(id)), [&](const auto &d) {
      using G = std::decay_t<decltype(d.field())>;
      if constexpr (std::is_same_v<G, F>) {
        if (auto b = bindings(d).find(id); b != bindings(d).end()) {
          out = lin(d, b->second);
        } else if (auto l = derived_views(d).find(id);
                   l != derived_views(d).end()) {
          out = lin(d, l->second);
        } else if (auto w = wiring_views(d).find(id);
                   w != wiring_views(d).end()) {
          out = wiring(d, w->second);
        } else if (auto x = expr_values(d).find(id); x != expr_values(d).end()) {
          out = convert(d, x->second);
        } else {
          export_fail("derived value '" + n.name + "' has no definition");
        }
      } else {
        export_fail("derived value '" + n.name + "' is read from another field");
      }
    });
    (void)d0;
    return out;
  }

  // E as a shared expression entry, read as kRef.
  Ex share(const Ex &e) {
    Ex r = e;
    r.e = unary(ir::Expr::kRef, P_.exprs.size(), kNone, e.n);
    P_.exprs.push_back(e.e);
    return r;
  }

  // A wiring view: coordinate i is (node, index), or zero.
  template <class F>
  Ex wiring(const Domain<F> &d,
            const std::vector<std::pair<size_t, size_t>> &src) {
    std::vector<size_t> nodes;
    std::map<size_t, size_t> base;
    bool zero = false;
    size_t at = 0;
    for (const auto &[nd, i] : src) {
      if (nd == kZeroCoordinate) {
        zero = true;
        continue;
      }
      if (!base.count(nd)) {
        base[nd] = at;
        at += cs_.nodes()[nd].n;
        nodes.push_back(nd);
      }
    }
    std::vector<size_t> idx;
    for (const auto &[nd, i] : src)
      idx.push_back(nd == kZeroCoordinate ? at : base.at(nd) + i);
    std::vector<Ex> parts;
    for (size_t nd : nodes) parts.push_back(leaf(d, nd));
    if (zero) parts.push_back(const_leaf(d, repeat_const(d, d.field().zero(), 1), 1));
    Ex c = concat(parts);
    Ex e;
    merge(e, c);
    e.deg = c.deg;
    e.n = idx.size();
    const size_t n = idx.size();
    e.e = unary(ir::Expr::kReindex, index_map(std::move(idx)), c.e, n);
    return e;
  }

  template <class F>
  Ex const_leaf(const Domain<F> &, size_t key, size_t n) {
    Ex e;
    e.n = n;
    e.e = leaf_node(key, n);
    e.values.insert(key);
    return e;
  }

  Ex concat(const std::vector<Ex> &parts) {
    if (parts.empty()) export_fail("an empty concatenation");
    Ex out = parts.back();
    for (size_t i = parts.size() - 1; i-- > 0;) {
      Ex c;
      merge(c, parts[i]);
      merge(c, out);
      c.deg = deg_max(parts[i].deg, out.deg);
      c.n = parts[i].n + out.n;
      c.e = binary(ir::Expr::kConcat, parts[i].e, out.e, c.n);
      out = c;
    }
    return out;
  }

  Ex add(const Ex &a, const Ex &b, bool sub = false) {
    if (a.n != b.n)
      export_fail(std::string(sub ? ".sub" : ".add") + " of lengths " +
                  std::to_string(a.n) + " and " + std::to_string(b.n));
    Ex e;
    merge(e, a);
    merge(e, b);
    e.deg = deg_max(a.deg, b.deg);
    e.n = a.n;
    e.e = binary(sub ? ir::Expr::kSub : ir::Expr::kAdd, a.e, b.e, a.n);
    return e;
  }
  Ex mul(const Ex &a, const Ex &b) {
    if (a.n != b.n)
      export_fail("a product of lengths " + std::to_string(a.n) + " and " +
                  std::to_string(b.n));
    Ex e;
    merge(e, a);
    merge(e, b);
    e.deg = deg_sum(a.deg, b.deg);
    e.n = a.n;
    e.e = binary(ir::Expr::kMul, a.e, b.e, a.n);
    return e;
  }
  template <class F>
  Ex scale(const Domain<F> &d, const typename F::Elt &k, const Ex &a) {
    if (k == d.field().one()) return a;
    Ex e = a;
    e.e = unary(ir::Expr::kScale, const_coef(enc(d.field(), k)), a.e, a.n);
    return e;
  }
  Ex reindex(Id map, size_t n, const Ex &a) {
    Ex e = a;
    e.n = n;
    e.e = unary(ir::Expr::kReindex, map, a.e, n);
    return e;
  }
  // The named operator OP on A, with public operand keys KEYS.
  Ex apply(Id op, size_t rows, const std::vector<size_t> &keys, const Ex &a) {
    Ex e = a;
    for (size_t k : keys) {
      Ex t;
      leaf_info(k, t);
      merge(e, t);
      e.deg = deg_sum(e.deg, t.deg);
    }
    e.n = rows;
    e.e = unary(ir::Expr::kApply, op, a.e, rows);
    return e;
  }
  Ex apply_sum(size_t w, size_t rows, const Ex &a) {
    ir::NamedOp op;
    op.kind = ir::NamedOp::kSum;
    op.nats = {w};
    return apply(op_of(std::move(op)), rows, {}, a);
  }

  // Affine leaf L: the sum of its terms, each a scale of an operator chain
  // applied to a node.
  template <class F>
  Ex lin(const Domain<F> &d, const Lin<F> &l) {
    if (l.terms.empty()) {
      return const_leaf(d, repeat_const(d, d.field().zero(), l.n), l.n);
    }
    std::optional<Ex> out;
    for (const auto &t : l.terms) {
      Ex x = leaf(d, t.node);
      for (const auto &op : t.chain) x = op_apply(d, *op, x);
      x = scale(d, t.scale, x);
      out = out ? add(*out, x) : x;
    }
    return *out;
  }

  template <class F>
  std::string elt_param(const Domain<F> &d, Params &p) {
    const auto b = p.bytes(F::kBytes);
    const auto x = d.field().of_bytes_field(b.data());
    if (!x) export_fail("an operator parameter is no field element");
    return enc(d.field(), *x);
  }
  // A negacyclic transform's root of length N (ntt.h): psi in the prime
  // field with psi^N = -1, or the build fails.
  template <class F>
  std::string root_param(const Domain<F> &d, Params &p, uint64_t n) {
    const F &f = d.field();
    const auto b = p.bytes(F::kBytes);
    const auto x = f.of_bytes_field(b.data());
    if (!x) export_fail("an operator's root is no field element");
    typename F::Elt y = f.one(), base = *x;
    for (uint64_t e = n; e != 0; e >>= 1) {
      if (e & 1) y = f.mulf(y, base);
      base = f.mulf(base, base);
    }
    if (!subfield_contains(f, *x) || y != f.mone())
      export_fail("an operator's root psi has psi^" + std::to_string(n) +
                  " != -1 or lies outside the prime field");
    return enc(f, *x);
  }

  // Operator OP on X: a view as a reindex, a named operator, or an unnamed
  // sparse matrix as sparse rows.
  template <class F>
  Ex op_apply(const Domain<F> &d, const OpSpec<F> &op, const Ex &x) {
    Params p{op.params};
    std::vector<size_t> keys;
    for (size_t k : op.deps) {
      if (cls_[k] != kValue)
        export_fail("operator '" + op.name + "' reads '" +
                    cs_.nodes()[k].name + "', which is no value");
      keys.push_back(k);
    }
    const std::string &nm = op.name;
    // A view, or a view batched over B blocks (`batched`, its inner
    // operator a gather or zero_extend): one reindex, block k's index j
    // read as k m + j, the zero coordinate after the B m inputs.
    std::string view = nm;
    size_t blocks = 1;
    std::vector<uint8_t> vparams = op.params;
    if (nm == "batched") {
      Params q{op.params};
      blocks = size_t(q.u64());
      view = q.str();
      vparams = q.bytes(size_t(q.u64()));
    }
    if (view == "gather" || view == "zero_extend") {
      Params q{vparams};
      std::vector<size_t> idx;
      size_t m = 0;
      if (view == "gather") {
        m = size_t(q.u64());
        const size_t c = size_t(q.u64());
        for (size_t i = 0; i < c; ++i) idx.push_back(size_t(q.u64()));
      } else {
        const size_t n = size_t(q.u64());
        m = n;
        const size_t mm = size_t(q.u64());
        for (size_t i = 0; i < mm; ++i) idx.push_back(i < n ? i : n);
      }
      if (blocks == 0 || x.n != blocks * m)
        export_fail("operator '" + nm + "' of " + std::to_string(blocks * m) +
                    " columns reads " + std::to_string(x.n));
      std::vector<size_t> all;
      all.reserve(blocks * idx.size());
      bool zero = false;
      for (size_t k = 0; k < blocks; ++k)
        for (size_t j : idx) {
          zero = zero || j == m;
          all.push_back(j == m ? blocks * m : k * m + j);
        }
      Ex in = x;
      if (zero)
        in = concat({x, const_leaf(d, repeat_const(d, d.field().zero(), 1), 1)});
      const size_t n = all.size();
      return reindex(index_map(std::move(all)), n, in);
    }
    const Id named = named_op(d, op, p, keys);
    if (named != kNone) {
      if (x.n % op.cols != 0)
        export_fail("operator '" + nm + "' of " + std::to_string(op.cols) +
                    " columns reads " + std::to_string(x.n));
      return apply(named, op.rows * (x.n / op.cols), keys, x);
    }
    if (op.emit && op.deps.empty() && op.staged == nullptr) {
      // An unnamed matrix: its sparse rows.
      const auto rows = op.emit();
      ir::LinearRows r(rows.size());
      for (size_t i = 0; i < rows.size(); ++i)
        for (size_t j = 0; j < rows[i].size(); ++j)
          r[i].push_back({rows[i][j].first,
                          const_coef(enc(d.field(), rows[i][j].second))});
      if (x.n != op.cols)
        export_fail("sparse operator '" + nm + "' reads " +
                    std::to_string(x.n) + " coordinates");
      P_.linears.push_back(std::move(r));
      Ex e = x;
      e.n = rows.size();
      e.e = unary(ir::Expr::kLinear, P_.linears.size() - 1, x.e, rows.size());
      return e;
    }
    if (op.dep_rows) {
      // A matrix the dependencies fix, described by its rows (constants and
      // coordinates of the public values it depends on).
      const auto rows = op.dep_rows();
      ir::LinearRows r(rows.size());
      for (size_t i = 0; i < rows.size(); ++i)
        for (const auto &[col, k] : rows[i]) {
          if (k.is_const) {
            r[i].push_back({col, const_coef(enc(d.field(), k.c))});
            continue;
          }
          if (k.dep >= keys.size())
            export_fail("operator '" + nm + "' reads a coefficient of no "
                        "dependency");
          ir::Coef c;
          c.is_const = false;
          c.v = Id(keys[k.dep]);
          c.i = k.at;
          P_.coefs.push_back(std::move(c));
          r[i].push_back({col, Id(P_.coefs.size() - 1)});
        }
      if (x.n != op.cols)
        export_fail("operator '" + nm + "' reads " + std::to_string(x.n) +
                    " coordinates, not " + std::to_string(op.cols));
      P_.linears.push_back(std::move(r));
      Ex e = x;
      for (size_t k : keys) {
        Ex t;
        leaf_info(k, t);
        merge(e, t);
        e.deg = deg_sum(e.deg, t.deg);
      }
      e.n = rows.size();
      e.e = unary(ir::Expr::kLinear, P_.linears.size() - 1, x.e, rows.size());
      return e;
    }
    if (const Id m = dense_op(d, op, 1); m != kNone) {
      if (x.n % op.cols != 0)
        export_fail("operator '" + nm + "' of " + std::to_string(op.cols) +
                    " columns reads " + std::to_string(x.n));
      return apply(m, op.rows * (x.n / op.cols), {}, x);
    }
    export_fail("operator '" + nm + "' has no export");
  }

  // A public operator with no name in the schema and no sparse rows (a
  // matrix the system gives as code, pq_mdoc.h's FipsNtt): `.rowDot M R W`
  // over its block of R rows and W columns, M a constant of R W entries in
  // row-major order, read off the instantiated operator (row r is
  // M^T e_r); kNone for an operator that reads values or is staged. BLOCKS
  // is the block count of a batched operator: its first block.
  template <class F>
  Id dense_op(const Domain<F> &d, const OpSpec<F> &op, size_t blocks) {
    if (!op.make || !op.deps.empty() || op.staged != nullptr || blocks == 0 ||
        op.rows % blocks != 0 || op.cols % blocks != 0)
      return kNone;
    const auto m = op.make(OpArgs{});
    if (m == nullptr || m->rows() != op.rows || m->cols() != op.cols)
      export_fail("operator '" + op.name + "' does not instantiate as declared");
    const F &f = d.field();
    const size_t R = op.rows / blocks, W = op.cols / blocks;
    std::vector<std::string> entries;
    entries.reserve(R * W);
    std::vector<typename F::Elt> y(op.rows, f.zero()), row(op.cols);
    for (size_t r = 0; r < R; ++r) {
      y[r] = f.one();
      m->transpose_apply(y.data(), row.data());
      y[r] = f.zero();
      for (size_t c = 0; c < W; ++c) entries.push_back(enc(f, row[c]));
    }
    ir::NamedOp o;
    o.kind = ir::NamedOp::kRowDot;
    o.value = Id(constant(place_of(d), std::move(entries)));
    o.nats = {R, W};
    return op_of(std::move(o));
  }

  // The named operator, or kNone for an operator with no name in the
  // schema.
  template <class F>
  Id named_op(const Domain<F> &d, const OpSpec<F> &op, Params &p,
              const std::vector<size_t> &keys) {
    const std::string &nm = op.name;
    using NO = ir::NamedOp;
    NO o;
    auto key0 = [&]() { return Id(keys.at(0)); };
    auto form = [&](bool ntt, uint64_t n) {
      o.ntt_form = ntt;
      if (ntt) o.elt = root_param(d, p, n);
    };
    if (nm == "negacyclic_conv") {
      // poly_mat_vec's parameter layout: the coefficient form has no
      // parameter, or only its entry bound (the string "entry_bound" and
      // the bound); the NTT form has its root alone.
      o.kind = NO::kNegacyclicConv;
      o.value = key0();
      if (p.done()) return op_of(std::move(o));
      if (p.b.size() - p.at != F::kBytes) {
        if (p.str() != "entry_bound")
          export_fail("operator '" + nm + "' has unknown parameters");
        return op_of(std::move(o));
      }
      form(true, op.cols);
      return op_of(std::move(o));
    }
    if (nm == "poly_mat_vec" || nm == "poly_broadcast") {
      const uint64_t K = p.u64(), L = p.u64(), n = p.u64(), f = p.u64();
      form(f == uint64_t(ops::Form::kNtt), n);
      o.value = key0();
      if (nm == "poly_mat_vec") {
        o.kind = NO::kPolyMatVec;
        o.nats = {size_t(K), size_t(L)};
      } else {
        o.kind = NO::kPolyBroadcast;
        o.nats = {size_t(K)};
      }
      return op_of(std::move(o));
    }
    if (nm == "ntt") {
      const uint64_t n = p.u64(), order = p.u64();
      p.u64();
      o.kind = NO::kNtt;
      o.nats = {size_t(n)};
      o.elt = root_param(d, p, n);
      o.natural_order = order != uint64_t(ops::NttOrder::kScheme);
      return op_of(std::move(o));
    }
    if (nm == "inverse_ntt" || nm == "ntt_transpose") {
      const uint64_t n = p.u64();
      o.kind = nm == "inverse_ntt" ? NO::kInverseNtt : NO::kNttTranspose;
      o.nats = {size_t(n)};
      o.elt = root_param(d, p, n);
      return op_of(std::move(o));
    }
    if (nm == "row_dot") {
      const uint64_t R = p.u64(), W = p.u64();
      o.kind = NO::kRowDot;
      o.value = key0();
      o.nats = {size_t(R), size_t(W)};
      return op_of(std::move(o));
    }
    if (nm == "mac_conv") {
      const uint64_t w = p.u64(), nch = p.u64();
      bool found = false;
      for (const auto &m : cs_.records().macs)
        if (m.width == w && !found) {
          // The first MAC of the width with taps names them.
          if (m.taps.empty()) continue;
          o.taps.assign(m.taps.begin(), m.taps.end());
          found = true;
        }
      o.kind = NO::kMacConv;
      o.value = key0();
      o.nats = {size_t(w), size_t(nch)};
      return op_of(std::move(o));
    }
    if (nm == "acyclic_conv") {
      const uint64_t lx = p.u64();
      o.kind = NO::kAcyclicConv;
      o.value = key0();
      o.nats = {size_t(lx)};
      return op_of(std::move(o));
    }
    if (nm == "diagonal") {
      o.kind = NO::kDiagonal;
      o.value = key0();
      return op_of(std::move(o));
    }
    if (nm == "scale") {
      o.kind = NO::kScale;
      o.value = key0();
      return op_of(std::move(o));
    }
    if (nm == "const_diagonal") {
      const size_t n = size_t(p.u64());
      std::vector<std::string> e;
      for (size_t i = 0; i < n; ++i) e.push_back(elt_param(d, p));
      o.kind = NO::kConstDiagonal;
      o.value = Id(constant(place_of(d), e));
      return op_of(std::move(o));
    }
    if (nm == "sum") {
      o.kind = NO::kSum;
      o.nats = {size_t(p.u64())};
      return op_of(std::move(o));
    }
    if (nm == "from_digits") {
      const uint64_t k = p.u64();
      o.kind = NO::kFromDigits;
      o.nats = {size_t(k)};
      o.elt = elt_param(d, p);
      return op_of(std::move(o));
    }
    if (nm == "batched") {
      const uint64_t b = p.u64();
      const std::string inner = p.str();
      const size_t len = size_t(p.u64());
      OpSpec<F> in;
      in.name = inner;
      in.params = p.bytes(len);
      in.rows = op.rows / b;
      in.cols = op.cols / b;
      in.deps = op.deps;
      Params q{in.params};
      if (inner == "gather" || inner == "zero_extend")
        export_fail("a batched view");
      Id t = named_op(d, in, q, keys);
      if (t == kNone) t = dense_op(d, op, size_t(b));
      if (t == kNone) export_fail("batched operator '" + inner + "' has no name");
      o.kind = NO::kBatched;
      o.nats = {size_t(b)};
      o.inner = t;
      return op_of(std::move(o));
    }
    return kNone;
  }

  // Expression node X, shared when read more than once.
  template <class F>
  Ex convert(const Domain<F> &d, const ExprPtr<F> &x) {
    return node(d, *x);
  }
  template <class F>
  void count_refs(const ExprNode<F> &x) {
    if (refs_[&x]++ > 0) return;
    for (const auto &k : x.kids) count_refs(*k);
  }
  template <class F>
  Ex node(const Domain<F> &d, const ExprNode<F> &x) {
    if (realized_ && has_spec(x)) {
      // The realized reading: each spectrally realized convolution read
      // through its realization, the rest as in the source form.
      auto it = memo_r_.find(&x);
      if (it != memo_r_.end()) return it->second;
      auto sp = spec_.find(&x);
      Ex e = sp != spec_.end() ? sp->second.read : node_once(d, x);
      memo_r_[&x] = e;
      return e;
    }
    auto it = memo_.find(&x);
    if (it != memo_.end()) return it->second;
    Ex e = node_once(d, x);
    // A node read twice is shared, unless it is a shared entry already.
    if (refs_[&x] > 1 && x.op != ExprOp::kLin && x.op != ExprOp::kConst &&
        P_.nodes[e.e].op != ir::Expr::kRef)
      e = share(e);
    memo_[&x] = e;
    return e;
  }
  // Whether X holds a spectrally realized convolution (spec_).
  template <class F>
  bool has_spec(const ExprNode<F> &x) {
    auto it = has_spec_.find(&x);
    if (it != has_spec_.end()) return it->second;
    bool any = spec_.count(&x) > 0;
    for (const auto &k : x.kids) any = has_spec(*k) || any;
    has_spec_[&x] = any;
    return any;
  }
  template <class F>
  Ex node_once(const Domain<F> &d, const ExprNode<F> &x) {
    const F &f = d.field();
    auto kid = [&](size_t i) { return node(d, *x.kids.at(i)); };
    auto ones = [&](size_t n) {
      return const_leaf(d, repeat_const(d, f.one(), n), n);
    };
    switch (x.op) {
      case ExprOp::kLin: {
        Ex e = lin(d, x.lin);
        if (e.n != x.n) export_fail("an affine leaf of the wrong length");
        return e;
      }
      case ExprOp::kConst: {
        if (x.c.size() == x.n) return const_leaf(d, constant_elts(d, x.c), x.n);
        if (x.c.size() == 1)
          return reindex(index_map(std::vector<size_t>(x.n, 0)), x.n,
                         const_leaf(d, constant_elts(d, x.c), 1));
        export_fail("a constant of " + std::to_string(x.c.size()) + " values");
      }
      case ExprOp::kAdd:
        return add(kid(0), kid(1));
      case ExprOp::kScale:
        return scale(d, x.c.at(0), kid(0));
      case ExprOp::kMul:
        return mul(kid(0), kid(1));
      case ExprOp::kSum: {
        const Ex a = kid(0);
        const size_t w = x.w == 0 ? a.n : x.w;
        return apply_sum(w, a.n / w, a);
      }
      case ExprOp::kBroadcast: {
        const Ex a = kid(0);
        std::vector<size_t> idx(x.n);
        for (size_t i = 0; i < x.n; ++i) idx[i] = i % a.n;
        return reindex(index_map(idx), x.n, a);
      }
      case ExprOp::kNot:
        return add(ones(x.n), kid(0), true);
      case ExprOp::kAnd:
        return mul(kid(0), kid(1));
      case ExprOp::kOr: {
        const Ex a = kid(0), b = kid(1);
        return add(add(a, b), mul(a, b), true);
      }
      case ExprOp::kXor: {
        const Ex a = kid(0), b = kid(1);
        if constexpr (F::kCharacteristicTwo) {
          return add(a, b);
        } else {
          return add(add(a, b), scale(d, f.addf(f.one(), f.one()), mul(a, b)),
                     true);
        }
      }
      case ExprOp::kMux: {
        const Ex c = kid(0), t = kid(1), e0 = kid(2);
        Ex e;
        merge(e, c);
        merge(e, t);
        merge(e, e0);
        e.deg = deg_sum(c.deg, deg_max(t.deg, e0.deg));
        e.n = t.n;
        ir::Expr m;
        m.op = ir::Expr::kMux;
        m.a = c.e;
        m.b = t.e;
        m.c = e0.e;
        m.n = t.n;
        e.e = node_of(std::move(m));
        return e;
      }
      case ExprOp::kLt:
      case ExprOp::kLeq:
      case ExprOp::kEq: {
        const Ex a = kid(0);
        Ex b;
        if (x.imm) {
          std::vector<typename F::Elt> bits(x.w);
          for (size_t i = 0; i < x.w; ++i)
            bits[i] = (x.value >> i) & 1 ? f.one() : f.zero();
          std::vector<size_t> idx(a.n);
          for (size_t i = 0; i < a.n; ++i) idx[i] = i % x.w;
          b = reindex(index_map(idx), a.n,
                      const_leaf(d, constant_elts(d, bits), x.w));
        } else {
          b = kid(1);
        }
        const ir::LogicOp op = x.op == ExprOp::kLt    ? ir::LogicOp::kLt
                               : x.op == ExprOp::kLeq ? ir::LogicOp::kLeq
                                                      : ir::LogicOp::kEq;
        return logic(op, x.w, {a, b}, x.n);
      }
      case ExprOp::kAny:
        return logic(ir::LogicOp::kAny, x.w, {kid(0)}, x.n);
      case ExprOp::kAll:
        return logic(ir::LogicOp::kAll, x.w, {kid(0)}, x.n);
      case ExprOp::kMaterialize:
        return kid(0);
      case ExprOp::kProd: {
        const Ex a = kid(0);
        Ex e = a;
        e.n = x.n;
        for (auto &[c, k] : e.deg) k *= x.w;
        e.e = unary(ir::Expr::kProd, x.w, a.e, x.n);
        return e;
      }
      case ExprOp::kGather: {
        std::vector<Ex> parts;
        for (size_t i = 0; i < x.kids.size(); ++i) parts.push_back(kid(i));
        return reindex(index_map(x.idx.vec()), x.n, concat(parts));
      }
      case ExprOp::kApply: {
        if (x.apply == nullptr) export_fail("an operator node with no operator");
        return op_apply(d, *x.apply, kid(0));
      }
      case ExprOp::kConv:
        return conv(d, x, kid(0), kid(1));
      default:
        export_fail(std::string("expression operation ") +
                    std::to_string(int(x.op)) + " has no export");
    }
  }

  // conv(a, b) (ExprOp::kConv), the acyclic convolutions of a [B][la] and
  // b [B][lb] along the last axis, as the source expression it is:
  // coordinate (blk, k, t) of two views of length B (la + lb - 1) la reads
  // a[blk][t] and b[blk][k - t] for 0 <= k - t < lb (the zero coordinate
  // otherwise), their product summed over t (`.sum la`) is
  // conv(a, b)[blk][k]. Its realization (compiler/conv.h) is exported
  // with the predicates the lowering declares.
  template <class F>
  Ex conv(const Domain<F> &d, const ExprNode<F> &x, const Ex &a, const Ex &b) {
    if (x.kids.size() != 2) export_fail("a conv of " +
                                        std::to_string(x.kids.size()) + " operands");
    const size_t la = x.kids[0]->dims().back();
    const size_t lb = x.kids[1]->dims().back();
    const size_t lc = la + lb - 1;
    if (la == 0 || lb == 0 || a.n % la != 0 || b.n % lb != 0 ||
        a.n / la != b.n / lb || x.n != (a.n / la) * lc)
      export_fail("a conv of " + std::to_string(a.n) + " and " +
                  std::to_string(b.n) + " coordinates to " +
                  std::to_string(x.n));
    const size_t B = a.n / la;
    std::vector<size_t> ia, ib;
    ia.reserve(B * lc * la);
    ib.reserve(B * lc * la);
    for (size_t blk = 0; blk < B; ++blk)
      for (size_t k = 0; k < lc; ++k)
        for (size_t t = 0; t < la; ++t) {
          const bool in = t <= k && k - t < lb;
          ia.push_back(in ? blk * la + t : a.n);
          ib.push_back(in ? blk * lb + (k - t) : b.n);
        }
    const Ex zero = const_leaf(d, repeat_const(d, d.field().zero(), 1), 1);
    const size_t na = ia.size(), nb = ib.size();
    const PlanRecords::SpectralConv *rec = nullptr;
    for (const auto &sc : cs_.records().spectral_convs)
      if (sc.conv == static_cast<const void *>(&x)) rec = &sc;
    if (rec == nullptr) {
      const Ex va = reindex(index_map(std::move(ia)), na, concat({a, zero}));
      const Ex vb = reindex(index_map(std::move(ib)), nb, concat({b, zero}));
      return apply_sum(la, B * lc, mul(va, vb));
    }
    // A spectrally realized convolution (compiler/conv.h, the batch form):
    // the source and its reading INTT_M(z)[0, lc) as shared expressions
    // (Lean `SpectralConv`), the views by their Lean names.
    const std::string dims =
        std::to_string(B) + " " + std::to_string(la) + " " + std::to_string(lb);
    if (rec->blocks != B || rec->left != la || rec->right != lb ||
        rec->length < lc)
      export_fail("the spectral realization of a conv of " + std::to_string(B) +
                  " rows does not match it");
    const Ex va = reindex(index_map_named(std::move(ia), "IndexMap.convLeft " + dims),
                          na, concat({a, zero}));
    const Ex vb = reindex(index_map_named(std::move(ib), "IndexMap.convRight " + dims),
                          nb, concat({b, zero}));
    SpecConv sp;
    sp.rec = rec;
    sp.a = a;
    sp.b = b;
    sp.zero = zero;
    sp.src = share(apply_sum(la, B * lc, mul(va, vb)));
    sp.ks = P_.exprs.size() - 1;
    const auto psi = d.field().of_bytes_field(rec->psi.data());
    if (!psi) export_fail("a spectral realization's root is no field element");
    sp.psi = enc(d.field(), *psi);
    const size_t M = rec->length;
    std::vector<size_t> pre;
    for (size_t blk = 0; blk < B; ++blk)
      for (size_t k = 0; k < lc; ++k) pre.push_back(blk * M + k);
    const Ex inv = apply(batched_transform(B, ir::NamedOp::kInverseNtt, M, sp.psi),
                         B * M, {}, leaf(d, rec->z));
    sp.read = share(reindex(
        index_map_named(std::move(pre), "IndexMap.blockPrefix " +
                                            std::to_string(B) + " " +
                                            std::to_string(M) + " " +
                                            std::to_string(lc)),
        B * lc, inv));
    sp.kr = P_.exprs.size() - 1;
    spec_[&x] = sp;
    return sp.src;
  }

  // `.batched B (T M psi)`: the transform KIND (ntt in scheme order, or
  // inverseNtt) of length M at PSI on each of B blocks.
  Id batched_transform(size_t B, ir::NamedOp::Kind kind, size_t M,
                       const std::string &psi) {
    ir::NamedOp t;
    t.kind = kind;
    t.nats = {M};
    t.elt = psi;
    ir::NamedOp o;
    o.kind = ir::NamedOp::kBatched;
    o.nats = {B};
    o.inner = op_of(std::move(t));
    return op_of(std::move(o));
  }

  // The spectral products predicate of SP (Lean `SpectralConv.products`):
  // NTT_M(a) . NTT_M(b) = z on the operands zero-extended to M, a part of
  // the batch the lowering proves it by, owned by OWNER.
  template <class F>
  void spectral_products(const Domain<F> &d, size_t di, const std::string &owner,
                         const SpecConv &sp) {
    const PlanRecords::SpectralConv &rec = *sp.rec;
    const size_t B = rec.blocks, la = rec.left, lb = rec.right, M = rec.length;
    auto extend = [&](const Ex &x, size_t l) {
      std::vector<size_t> idx;
      for (size_t blk = 0; blk < B; ++blk)
        for (size_t t = 0; t < M; ++t) idx.push_back(t < l ? blk * l + t : B * l);
      return reindex(index_map_named(std::move(idx),
                                     "IndexMap.zeroExtend " + std::to_string(B) +
                                         " " + std::to_string(l) + " " +
                                         std::to_string(M)),
                     B * M, concat({x, sp.zero}));
    };
    const Id ntt = batched_transform(B, ir::NamedOp::kNtt, M, sp.psi);
    const Ex l = mul(apply(ntt, B * M, {}, extend(sp.a, la)),
                     apply(ntt, B * M, {}, extend(sp.b, lb)));
    const Ex r = leaf(d, rec.z);
    PredRec p;
    p.name = rec.batch;
    p.domain = di;
    p.target = target_of(di, Placement::kBatch, rec.batch);
    p.role = "realization";
    p.owner_name = owner;
    p.p.body = ir::Predicate::kEqual;
    p.p.domain = Id(di);
    ir::SpectralConv c;
    c.source = Id(sp.ks);
    c.read = Id(sp.kr);
    c.products = Id(preds_.size());
    c.blocks = B;
    c.left = la;
    c.right = lb;
    c.length = M;
    c.root = sp.psi;
    P_.convs.push_back(std::move(c));
    add_pred(std::move(p), l, r);
  }

  Ex logic(ir::LogicOp op, size_t w, const std::vector<Ex> &args, size_t n) {
    Ex e;
    ir::Expr l;
    l.op = ir::Expr::kLogic;
    l.logic = op;
    l.x = w;
    l.n = n;
    for (size_t i = 0; i < args.size(); ++i) {
      merge(e, args[i]);
      if (!args[i].deg.empty())
        export_fail("a Logic builder reads a challenge");
      l.args.push_back(args[i].e);
    }
    e.n = n;
    e.e = node_of(std::move(l));
    return e;
  }

  // ------------------------------------------------------ predicates --

  void add_pred(PredRec p, const Ex &l, const Ex &r) {
    p.reads.insert(l.reads.begin(), l.reads.end());
    p.reads.insert(r.reads.begin(), r.reads.end());
    p.degree = deg_max(l.deg, r.deg);
    p.values.insert(l.values.begin(), l.values.end());
    p.values.insert(r.values.begin(), r.values.end());
    p.p.lhs = l.e;
    p.p.rhs = r.e;
    preds_.push_back(std::move(p));
  }
  // Predicate P with the sides SIDES(P) gives; a predicate the structure
  // cannot describe (an operator or operation with no form in the schema)
  // is kept, unmodeled, with why (its target and origin intact, so the
  // backend binds it; the printer refuses it).
  template <class Fn>
  void describe(PredRec p, Fn sides) {
    try {
      const auto [l, r] = sides(p);
      add_pred(std::move(p), l, r);
    } catch (const std::runtime_error &e) {
      p.p.unmodeled = e.what();
      p.p.lhs = p.p.rhs = kNone;
      preds_.push_back(std::move(p));
    }
  }

  static TargetRec target_of(size_t di, Placement where,
                             const std::string &batch) {
    TargetRec t;
    t.domain = di;
    switch (where) {
      case Placement::kAffine:
        t.kind = ir::Target::kAffine;
        break;
      case Placement::kQuadratic:
        t.kind = ir::Target::kQuadratic;
        break;
      case Placement::kBatch:
        t.kind = ir::Target::kBatch;
        t.batch = batch;
        break;
      default:
        t.kind = ir::Target::kGkr;
    }
    return t;
  }

  template <class F>
  void domain_predicates(const Domain<F> &d) {
    const auto &N = cs_.nodes();
    const DomainPlan &plan = plan_of(size_t(d.index));
    const F &f = d.field();
    const size_t di = size_t(d.index);
    std::map<std::string, std::string> h_owner;
    for (const auto &m : cs_.records().macs)
      if (!m.h_predicate.empty()) h_owner[m.h_predicate] = m.name + ".equal";
    // The integer equalities of D (assert_int_equal): their predicates are
    // mod_0, the sides and intervals from the lowering's record.
    std::map<std::string, const PlanRecords::ModEq *> integer;
    for (const auto &eq : cs_.records().mod_equalities)
      if (eq.integer && eq.domain == d.name) integer[eq.name] = &eq;
    // The predicates (assert_zero, assert_true), each with its target.
    const auto &preds = d.predicates();
    if (plan.pred_targets.size() != preds.size())
      export_fail("domain " + d.name + ": predicate targets");
    for (size_t k = 0; k < preds.size(); ++k) {
      const auto &pd = preds[k];
      const auto &tg = plan.pred_targets[k];
      dom_pred_[{di, k}] = preds_.size();
      PredRec p;
      p.name = pd.name;
      p.domain = di;
      p.target = target_of(di, tg.where, tg.batch);
      if (auto o = h_owner.find(pd.name); o != h_owner.end()) {
        p.role = "realization";
        p.owner_name = o->second;
      }
      // The direct conv realization's predicate <conv>.products
      // (compiler/conv.h), C = sum of products for its committed C
      // (<conv>.c): a part of the predicate that reads the conv (its owner
      // by name).
      if (conv_products(pd.name)) p.role = "realization";
      p.p.domain = Id(di);
      p.p.origin = {ir::Origin::kDecl, Id(di), k};
      if (auto it = integer.find(pd.name); it != integer.end()) {
        const PlanRecords::ModEq &eq = *it->second;
        mod_names_.insert(eq.name);
        p.p.body = ir::Predicate::kMod;
        p.p.q = "0";
        ir::ModRealization &m = p.p.mod;
        m.form = ir::ModForm::kInteger;
        m.has_interval = true;
        m.lhs_lo = int_str(eq.lhs_lo);
        m.lhs_hi = int_str(eq.lhs_hi);
        m.rhs_lo = int_str(eq.rhs_lo);
        m.rhs_hi = int_str(eq.rhs_hi);
        m.quotient_lo = "0";
        m.qmax = "0";
        m.radix = "0";
        // The integer form's target is the predicate's.
        m.target = ir::Target{};
        p.mod_target = true;
        m.span = bound_str(eq.span);
        const ExprPtr<F> &lhs = *static_cast<const ExprPtr<F> *>(eq.lhs.get());
        const ExprPtr<F> &rhs = *static_cast<const ExprPtr<F> *>(eq.rhs.get());
        try {
          Ex l = convert(d, lhs);
          Ex r = convert(d, rhs);
          // The convolutions the predicate reads through a spectral
          // realization: its field equation is the realized predicate's
          // (Lean `Target.realized`), the source's sides with each read
          // through its realization (`<name>.realized`, the affine rows the
          // C++ places), with each realization's products predicate.
          std::vector<const SpecConv *> specs;
          for (const auto &sc : cs_.records().spectral_convs) {
            auto sit = spec_.find(sc.conv);
            if (sc.pred == pd.name && sit != spec_.end())
              specs.push_back(&sit->second);
          }
          Ex lr, rr;
          if (!specs.empty()) {
            realized_ = true;
            lr = convert(d, lhs);
            rr = convert(d, rhs);
            realized_ = false;
            if (p.target.kind != ir::Target::kAffine)
              export_fail("predicate '" + pd.name + "' reads a spectral "
                          "realization off the affine rows");
            p.target.kind = ir::Target::kRealized;
            p.target.realized = preds_.size() + 1;
          }
          add_pred(std::move(p), l, r);
          if (!specs.empty()) {
            PredRec q;
            q.name = pd.name + ".realized";
            q.domain = di;
            q.target = target_of(di, Placement::kAffine, "");
            q.role = "realization";
            q.owner_name = pd.name;
            q.p.body = ir::Predicate::kEqual;
            q.p.domain = Id(di);
            add_pred(std::move(q), lr, rr);
            for (const SpecConv *sp : specs) spectral_products(d, di, pd.name, *sp);
          }
        } catch (const std::runtime_error &e) {
          realized_ = false;
          p.p.unmodeled = e.what();
          p.p.lhs = p.p.rhs = kNone;
          preds_.push_back(std::move(p));
        }
        continue;
      }
      p.p.body = ir::Predicate::kEqual;
      describe(std::move(p), [&](PredRec &) {
        if (tg.where == Placement::kQuadratic)
          return std::make_pair(mul(leaf(d, tg.a), leaf(d, tg.b)), leaf(d, tg.c));
        Ex l = convert(d, pd.e);
        Ex r = const_leaf(d, repeat_const(d, pd.truth ? f.one() : f.zero(), l.n), l.n);
        return std::make_pair(std::move(l), std::move(r));
      });
    }
    // The lowerings' affine rows.
    for (size_t ai = 0; ai < affine_decls(d).size(); ++ai) {
      const auto &a = affine_decls(d)[ai];
      if (a.pred >= 0) continue;
      PredRec p;
      p.name = a.name;
      p.domain = di;
      p.target = target_of(di, Placement::kAffine, "");
      p.role = "realization";
      p.row = true;
      p.p.body = ir::Predicate::kEqual;
      p.p.domain = Id(di);
      p.p.origin = {ir::Origin::kAffineRow, Id(di), ai};
      describe(std::move(p), [&](PredRec &) {
        Ex l = lin(d, a.e);
        Ex r = const_leaf(d, repeat_const(d, f.zero(), l.n), l.n);
        return std::make_pair(std::move(l), std::move(r));
      });
    }
    // Declared quadratic triples.
    size_t qk = 0;
    for (const auto &q : quad_decls(d)) {
      PredRec p;
      p.name = d.name + ".quad" + std::to_string(qk++);
      p.domain = di;
      p.target = target_of(di, Placement::kQuadratic, "");
      p.p.body = ir::Predicate::kEqual;
      p.p.domain = Id(di);
      p.p.origin = {ir::Origin::kQuad, Id(di), qk - 1};
      describe(std::move(p), [&](PredRec &) {
        return std::make_pair(mul(leaf(d, q.a), leaf(d, q.b)), leaf(d, q.c));
      });
    }
    // The Boolean checks v v = v.
    for (const auto &c : plan.type_checks) {
      PredRec p;
      p.name = N[c.id].name + ".boolean";
      p.domain = di;
      p.target = target_of(di, c.where, d.name + ".boolean");
      p.p.body = ir::Predicate::kEqual;
      p.p.domain = Id(di);
      p.p.origin = {ir::Origin::kTypeCheck, Id(di), c.id};
      if (cls_[c.id] == kValue) {
        p.role = "type";
        p.type_value = c.id;
        vals_.at(c.id).type_pred = p.name;
      } else if (core_lowered(c.id)) {
        // The check of a core realization's derived Bit value (an
        // assert_mod's residues): a part of that realization.
        p.role = "realization";
      }
      describe(std::move(p), [&](PredRec &) {
        Ex v = leaf(d, c.id);
        return std::make_pair(mul(v, v), v);
      });
    }
    // The range requests, as in predicates with their lookups.
    range_predicates(d);
    // The assert_in requests, as in predicates on their tables' rows.
    in_predicates(d);
    // The domain's batches and circuit.
    batches(d, plan);
    // The compiler's own circuits.
    for (const auto &c : circuit_decls(d))
      if (c.pred < 0) real_circuits_.push_back({c.name, di});
  }

  template <class F>
  void range_predicates(const Domain<F> &d) {
    const auto &N = cs_.nodes();
    const size_t di = size_t(d.index);
    std::map<std::string, size_t> by_name;
    for (size_t id = 0; id < N.size(); ++id)
      if (N[id].domain == d.index) by_name[N[id].name] = id;
    // Tables by size: each group's histograms.
    const auto &stats = table_stats(d);
    std::map<Bound, size_t> table_of;
    for (const auto &t : stats) {
      if (!table_of.count(t.table)) {
        table_of[t.table] = tables_.size();
        tables_.push_back({d.name + "." + bound_str(t.table), di, t.table,
                           chal_of_.at(t.alpha), {}, {}});
      }
      TableRec &tr = tables_[table_of[t.table]];
      // The group's members: each slice's request and the needle's index
      // among the request's needles.
      std::vector<std::tuple<std::string, size_t, size_t, size_t>> mem;
      for (const auto &m : t.members) {
        const RangeRequest<F> &rq = range_requests(d).at(m.req);
        const auto &ids = rq.realization.needle_ids;
        const auto at = std::find(ids.begin(), ids.end(), m.node);
        if (at == ids.end())
          export_fail("table " + tr.name + ": a member is no needle of '" +
                      rq.name + "'");
        mem.push_back({rq.name, size_t(at - ids.begin()), m.b, m.e - m.b});
      }
      logup_of_[t.circuit] = {table_of[t.table], tr.groups.size()};
      tr.groups.push_back(t);
      tr.members.push_back(std::move(mem));
      weights_of_["range.weights:" + tr.name] = table_of[t.table];
    }
    for (size_t ri = 0; ri < range_requests(d).size(); ++ri) {
      const auto &r = range_requests(d)[ri];
      const RangeRealization &R = r.realization;
      PredRec p;
      p.name = r.name;
      p.domain = di;
      p.mem = true;
      p.needles = r.realization.needle_ids.size();
      p.size = r.v.n;
      p.p.body = ir::Predicate::kMem;
      p.p.domain = Id(di);
      p.p.origin = {ir::Origin::kRange, Id(di), ri};
      p.p.range = bound_str(R.established);
      try {
      const Ex rec = lin(d, r.v);
      Ex needles;
      ir::InRealization &in = p.p.in;
      if (R.kind == RealizationKind::kImplied) {
        in.implied = true;
        in.lo = int_str(R.lo);
        in.hi = int_str(R.hi);
      } else {
        auto t = table_of.find(R.table);
        if (t == table_of.end())
          export_fail("range request '" + r.name + "': no table");
        ir::LookupRealization &lk = in.lookup;
        for (unsigned j = 0; j < R.k; ++j) {
          for (const char *s : {"d", "h"}) {
            auto it = by_name.find("range." + r.name + "." + s + std::to_string(j));
            if (it != by_name.end() && cls_[it->second] == kValue)
              (s[0] == 'd' ? lk.digit_values : lk.second).push_back(Id(it->second));
          }
        }
        // The needles of one request coordinate, in order (each over the
        // request's coordinates).
        const size_t per = R.needle_ids.size();
        for (size_t k = 0; k < per; ++k) {
          const Ex x = leaf(d, R.needle_ids[k]);
          merge(needles, x);
          lk.needles.push_back(x.e);
        }
        lk.table = Id(t->second);
        lk.group = Id(R.group);
        lk.kind = lookup_kind(R.kind);
        lk.digits = std::max(1u, R.k);
        lk.base = bound_str(R.table);
        lk.honest = bound_str(r.n);
        lk.max = bound_str(r.m);
      }
      req_bounds_[r.name] = {r.n, R.established, r.m};
      if (R.kind == RealizationKind::kTwoSided) {
        p.recon_row = R.recon_row;
        p.top_row = R.top_row;
      }
      if (R.bound_id != SIZE_MAX) bound_rec_[R.bound_id] = preds_.size();
      // The needles' reads are the predicate's; the values they read
      // belong to its realization, not to the records.
      needles.values.clear();
      PredRec q = p;
      add_pred(std::move(q), rec, needles);
      // The record is the predicate's expression; the needles are in its
      // realization.
      preds_.back().p.rhs = kNone;
      } catch (const std::runtime_error &e) {
        // A request the structure cannot describe: kept, unmodeled.
        p.p.unmodeled = e.what();
        p.p.lhs = p.p.rhs = kNone;
        preds_.push_back(std::move(p));
      }
    }
  }

  // r_c = gamma^c, c < amax (assert_in's in.powers:<D>, compiler/
  // assert_in.h): the product along amax - 1 of gamma at the first c
  // positions and 1 at the others.
  template <class F>
  Ex in_powers_expr(const Domain<F> &d, const PlanRecords::InLookup &t) {
    const size_t amax = cs_.nodes()[t.powers].n, w = amax - 1;
    const size_t one = repeat_const(d, d.field().one(), 1);
    std::vector<size_t> idx;
    for (size_t c = 0; c < amax; ++c)
      for (size_t i = 0; i < w; ++i) idx.push_back(i < c ? 0 : 1);
    Ex e;
    e.n = amax;
    const size_t ng = cs_.nodes()[t.gamma].n;
    const Id cat = binary(ir::Expr::kConcat, leaf_node(t.gamma, ng),
                          leaf_node(one, 1), ng + 1);
    const Id rx = unary(ir::Expr::kReindex, index_map(idx), cat, amax * w);
    e.e = unary(ir::Expr::kProd, w, rx, amax);
    leaf_info(t.gamma, e);
    e.values.insert(one);
    e.deg[chal_of_.at(t.gamma)] = w;
    return e;
  }

  // assert_in's packing of X, records of A coordinates, one entry each:
  // X itself at arity 1, otherwise the record's sum_c k_c x_c by sparse
  // rows, k_c the fixed packing's kappa^c or coordinate c of the powers of
  // gamma.
  template <class F>
  Ex in_pack(const Domain<F> &d, const PlanRecords::InLookup &t, const Ex &x) {
    const size_t A = t.arity;
    if (A == 1) return x;
    if (x.n % A != 0)
      export_fail("assert_in '" + t.table + "': records of " +
                  std::to_string(x.n) + " coordinates, not of arity " +
                  std::to_string(A));
    const size_t n = x.n / A;
    std::vector<Id> k(A);
    for (size_t c = 0; c < A; ++c) {
      if (t.fixed) {
        const auto e = d.field().of_bytes_field(t.kappa.at(c).data());
        if (!e) export_fail("assert_in '" + t.table + "': kappa is no field element");
        k[c] = const_coef(enc(d.field(), *e));
      } else {
        ir::Coef q;
        q.is_const = false;
        q.v = Id(t.powers);
        q.i = c;
        P_.coefs.push_back(std::move(q));
        k[c] = Id(P_.coefs.size() - 1);
      }
    }
    ir::LinearRows rows(n);
    for (size_t j = 0; j < n; ++j)
      for (size_t c = 0; c < A; ++c) rows[j].push_back({j * A + c, k[c]});
    P_.linears.push_back(std::move(rows));
    Ex e = x;
    if (!t.fixed) {
      Ex pw;
      leaf_info(t.powers, pw);
      merge(e, pw);
      e.deg = deg_sum(e.deg, pw.deg);
    }
    e.n = n;
    e.e = unary(ir::Expr::kLinear, P_.linears.size() - 1, x.e, n);
    return e;
  }

  // The assert_in requests of domain D (compiler/assert_in.h's records):
  // each an in predicate whose set is its table's packed rows, looked up
  // directly in the table's one group, its LogUp circuit the table's.
  template <class F>
  void in_predicates(const Domain<F> &d) {
    const size_t di = size_t(d.index);
    for (const auto &t : cs_.records().in_lookups) {
      if (t.domain != d.name) continue;
      try {
        Ex rows = t.rows ? convert(d, *static_cast<const ExprPtr<F> *>(t.rows.get()))
                         : leaf(d, t.rows_node);
        rows = in_pack(d, t, rows);
        const size_t ti = tables_.size();
        TableRec tr{t.table, di, Bound(t.nrows), chal_of_.at(t.alpha), {}, {},
                    rows.e};
        RangeTableStats g;
        g.alpha = t.alpha;
        g.circuit = t.circuit;
        for (size_t c : t.counts) g.capacity += c;
        (cs_.phase(t.mult) == 0 ? g.m0 : g.m1) = t.mult;
        std::vector<std::tuple<std::string, size_t, size_t, size_t>> mem;
        for (size_t k = 0; k < t.requests.size(); ++k)
          mem.push_back({t.requests[k], 0, 0, t.counts[k]});
        tr.groups.push_back(g);
        tr.members.push_back(std::move(mem));
        tables_.push_back(std::move(tr));
        logup_of_[t.circuit] = {ti, 0};
        for (size_t k = 0; k < t.requests.size(); ++k) {
          PredRec p;
          p.name = t.requests[k];
          p.domain = di;
          p.mem = true;
          p.needles = 1;
          p.size = t.counts[k];
          p.p.body = ir::Predicate::kMem;
          p.p.domain = Id(di);
          p.p.range = bound_str(Bound(t.nrows));
          p.p.set = rows.e;
          const Ex rec = in_pack(
              d, t, convert(d, *static_cast<const ExprPtr<F> *>(t.records[k].get())));
          ir::LookupRealization &lk = p.p.in.lookup;
          lk.table = Id(ti);
          lk.group = 0;
          lk.kind = ir::LookupKind::kDirect;
          lk.digits = 1;
          lk.base = bound_str(Bound(t.nrows));
          lk.needles = {rec.e};
          lk.honest = "0";
          lk.max = "0";
          Ex r = rows;
          r.values.clear();
          add_pred(std::move(p), rec, r);
          preds_.back().p.rhs = kNone;
        }
      } catch (const std::runtime_error &e) {
        gap("assert_in '" + t.table + "': " + e.what());
      }
    }
  }

  static ir::LookupKind lookup_kind(RealizationKind k) {
    const std::string n = realization_name(k);
    if (n == "direct") return ir::LookupKind::kDirect;
    if (n == "scaled") return ir::LookupKind::kScaled;
    if (n == "shifted") return ir::LookupKind::kShifted;
    if (n == "digits") return ir::LookupKind::kDigits;
    if (n == "two-sided") return ir::LookupKind::kTwoSided;
    if (n == "complement") return ir::LookupKind::kComplement;
    export_fail("a lookup realization named '" + n + "'");
  }

  struct TableRec {
    std::string name;
    size_t domain = 0;
    Bound size = 0;
    size_t alpha = 0;
    std::vector<RangeTableStats> groups;
    // Each group's LogUp members: (request name, needle index, first,
    // count), in sum order.
    std::vector<std::vector<std::tuple<std::string, size_t, size_t, size_t>>>
        members;
    // An assert_in table's rows (.expr), kNone for a range.
    Id rows_expr = kNone;
  };

  template <class F>
  void batches(const Domain<F> &d, const DomainPlan &plan) {
    const size_t di = size_t(d.index);
    for (const auto &b : plan.batches) {
      batch_id_[{di, b.name}] = batches_.size();
      batches_.push_back({b, di, F::kCharacteristicTwo});
    }
    if (plan.gkr) {
      circuit_id_[di] = circuits_.size();
      circuits_.push_back({di, plan});
    }
  }

  // The assert_mod predicates of domain D (the application's and the MAC
  // tails), from the lowerings' records.
  template <class F>
  void mod_predicates(const Domain<F> &d) {
    const size_t di = size_t(d.index);
    std::map<std::string, const PlanRecords::Mac *> tails;
    for (const auto &m : cs_.records().macs) tails[m.tail] = &m;
    const auto &eqs = cs_.records().mod_equalities;
    for (size_t ei = 0; ei < eqs.size(); ++ei) {
      const auto &eq = eqs[ei];
      if (eq.domain != d.name || eq.integer) continue;
      if (eq.lhs == nullptr || eq.rhs == nullptr)
        export_fail("assert_mod '" + eq.name + "' recorded no sides");
      PredRec p;
      p.name = eq.name;
      p.domain = di;
      mod_names_.insert(eq.name);
      if (auto t = tails.find(eq.name); t != tails.end()) {
        p.role = "realization";
        p.owner_name = t->second->name + ".equal";
      }
      p.p.body = ir::Predicate::kMod;
      p.p.domain = Id(di);
      p.p.origin = {ir::Origin::kMod, Id(di), ei};
      p.p.q = bound_str(eq.m);
      p.mod_ranges = eq.name;
      describe(std::move(p), [&](PredRec &q) {
        Ex l = lin(d, *static_cast<const Lin<F> *>(eq.lhs.get()));
        Ex r = lin(d, *static_cast<const Lin<F> *>(eq.rhs.get()));
        q.p.mod = mod_realization(d, eq);
        return std::make_pair(std::move(l), std::move(r));
      });
    }
  }

  // The record of the gadget NAME (not the grouped form's record), or
  // null.
  const PlanRecords::Mod *mod_record(const std::string &name, bool grouped) const {
    for (const auto &m : cs_.records().mods)
      if (m.name == name && (m.form == PlanRecords::Mod::kGrouped) == grouped)
        return &m;
    return nullptr;
  }

  // The realization of assert_mod EQ: its form, the sides' intervals, the
  // quotient or its digits, the in predicates that bound them (resolved
  // at the end), and the grouped form.
  template <class F>
  ir::ModRealization mod_realization(const Domain<F> &d,
                                     const PlanRecords::ModEq &eq) {
    const auto &N = cs_.nodes();
    const PlanRecords::Mod *g = mod_record(eq.name, true);
    const PlanRecords::Mod *q = mod_record(g ? g->final_quotient : eq.name, false);
    if (q == nullptr) export_fail("assert_mod '" + eq.name + "': no quotient record");
    using M = PlanRecords::Mod;
    ir::ModRealization out;
    out.form = q->form == M::kField           ? ir::ModForm::kField
               : q->form == M::kConstant      ? ir::ModForm::kConstant
               : q->form == M::kBitQuotient   ? ir::ModForm::kBit
               : q->form == M::kOneDigit      ? ir::ModForm::kOneDigit
               : q->form == M::kDigits        ? ir::ModForm::kDigits
                                              : ir::ModForm::kCommittedDigits;
    std::vector<std::string> ranges;
    if (q->quotient != SIZE_MAX) {
      out.quotient = leaf(d, q->quotient).e;
      if (q->form == M::kOneDigit) ranges.push_back(N[q->quotient].name);
    }
    for (size_t x : q->digits) {
      out.digits.push_back(leaf(d, x).e);
      ranges.push_back(N[x].name);
    }
    if (g != nullptr) {
      ir::GroupedMod gm;
      for (size_t i = 0; i < g->unit_ranges.size(); ++i)
        gm.groups.push_back({g->unit_ranges[i].first,
                             g->unit_ranges[i].second - g->unit_ranges[i].first});
      for (size_t id = 0; id < N.size(); ++id)
        if (N[id].domain == d.index && N[id].name == eq.name + ".acc")
          gm.accumulators = leaf(d, id).e;
      gm.base = bound_str(g->table);
      gm.digit_count = g->k;
      gm.group_bound = bound_str(g->group_bound);
      gm.group_digits = leaf(d, g->group_digits).e;
      gm.residues = leaf(d, g->residues).e;
      out.grouped = std::move(gm);
      ranges.push_back(N[g->group_digits].name);
    }
    for (const auto &rn : ranges) mod_ranges_[eq.name].push_back(rn);
    out.has_interval = eq.has_interval;
    if (eq.has_interval) {
      out.lhs_lo = int_str(eq.lhs_lo);
      out.lhs_hi = int_str(eq.lhs_hi);
      out.rhs_lo = int_str(eq.rhs_lo);
      out.rhs_hi = int_str(eq.rhs_hi);
    }
    out.quotient_lo = int_str(q->qlo);
    out.qmax = bound_str(q->qmax);
    out.radix = bound_str(q->radix);
    if (q->form == M::kField) out.target = ir::Target{ir::Target::kAffine, kNone};
    return out;
  }

  // The cross-field equalities: one per MAC. A binary MAC has one record
  // (X_H in H, X_A in A); a MAC between two odd domains has one record per
  // side (A's first), its tag in the field no domain commits, which is the
  // MAC field, and a blind in each side (blindX the x side's).
  void cross_predicates() {
    const auto &N = cs_.nodes();
    const auto &macs = cs_.records().macs;
    for (size_t i = 0; i < macs.size(); ++i) {
      const size_t first = i;
      const PlanRecords::Mac &m = macs[i];
      const bool odd = m.xh == SIZE_MAX;
      const PlanRecords::Mac *mb = nullptr;
      if (odd) {
        if (i + 1 >= macs.size() || macs[i + 1].name != m.name ||
            macs[i + 1].xh != SIZE_MAX) {
          gap("MAC '" + m.name + "' between two odd domains has one side");
          continue;
        }
        mb = &macs[++i];
      }
      if (m.tag == SIZE_MAX || m.xa == SIZE_MAX || m.key == SIZE_MAX ||
          (mb != nullptr && mb->xa == SIZE_MAX)) {
        gap("MAC '" + m.name + "' records no tag, key or sides");
        continue;
      }
      // The x side: X_H, or A's side; the y side: X_A, or B's side.
      const size_t xs = odd ? m.xa : m.xh, ys = odd ? mb->xa : m.xa;
      const size_t dx = size_t(domain_of(xs)), dy = size_t(domain_of(ys));
      // The accumulators and quotient digits: the tails' values.
      std::vector<Id> acc, quo;
      auto tail_values = [&](const PlanRecords::Mac &r, size_t dom) {
        for (size_t id = 0; id < N.size(); ++id) {
          if (cls_[id] != kValue || domain_of(id) != int(dom)) continue;
          const std::string &nm = N[id].name;
          if (nm.rfind(r.tail + ".acc", 0) == 0) acc.push_back(Id(id));
          if (nm.rfind(r.tail + ".gq", 0) == 0 ||
              nm.rfind(r.tail + ".final", 0) == 0 || nm == r.tail + ".low" ||
              nm == r.tail + ".high")
            quo.push_back(Id(id));
        }
      };
      if (odd) tail_values(m, dx);
      tail_values(odd ? *mb : m, dy);
      // The MAC field: H's field, or the tag's, which no domain commits.
      const size_t mac_place = odd ? size_t(domain_of(m.tag)) : dx;
      PredRec p;
      p.name = m.name + ".equal";
      p.domain = dx;
      p.p.body = ir::Predicate::kCross;
      p.p.domain = Id(dx);
      p.p.origin = {ir::Origin::kCross, Id(dx), first};
      p.p.dy = Id(dy);
      ir::MacRealization &mr = p.p.mac;
      mac_place_[preds_.size()] = mac_place;
      mr.key = chal_of_.count(m.key) ? Id(chal_of_.at(m.key)) : kNone;
      mr.blind_x = odd ? Id(m.blind) : kNone;
      mr.blind = Id(odd ? mb->blind : m.blind);
      mr.tag = Id(m.tag);
      mr.chunks = m.nch;
      mr.width = m.width;
      mr.accumulators = std::move(acc);
      mr.quotient_digits = std::move(quo);
      p.h_predicate = m.h_predicate;
      p.tails = {m.tail};
      if (odd) p.tails.push_back(mb->tail);
      describe(std::move(p), [&](PredRec &) {
        Ex x, y;
        with_domain(dx, [&](const auto &d) { x = leaf(d, xs); });
        with_domain(dy, [&](const auto &d) { y = leaf(d, ys); });
        return std::make_pair(std::move(x), std::move(y));
      });
    }
  }

  // ---------------------------------------------------------- finish --

  // The export's certificates (ir::Certificates), from the lowerings'
  // records: each rule's realized predicates, each predicate's MAC site,
  // a committed-digits mod_q's digit lookups and each bound value's lookup.
  void certificates() {
    const size_t np = preds_.size();
    certs_.roles.assign(np, 0);
    certs_.comm_digits.assign(np, {});
    // The committed-digits mod_q's quotient-digit lookups.
    for (size_t i = 0; i < np; ++i) {
      const ir::Predicate &q = P_.predicates[i];
      if (q.body == ir::Predicate::kMod && !preds_[i].mod_ranges.empty() &&
          q.mod.form == ir::ModForm::kCommittedDigits)
        certs_.comm_digits[i] = q.mod.ranges;
    }
    // The MAC sites: each predicate that realizes a cross-field equal (by
    // its chain of owners; never the equal itself, never a type check):
    // a hosted MAC's parts are its check over y's field (2 pid + 1); an
    // unhosted one's are the check of the tail they lie below, A's tail
    // over x's field (2 pid + 2) and B's over y's (2 pid + 1).
    for (size_t i = 0; i < np; ++i) {
      size_t o = i, below = i;
      for (size_t step = 0; step < np; ++step) {
        const ir::Predicate &q = P_.predicates[o];
        if (q.role != ir::Predicate::Role::kRealization || q.owner >= np) break;
        below = o;
        o = q.owner;
        const ir::Predicate &c = P_.predicates[o];
        if (c.body != ir::Predicate::kCross) continue;
        const bool hosted = c.mac.blind_x == kNone;
        const auto &tails = preds_[o].tails;
        const bool x_tail =
            !hosted && !tails.empty() && preds_[below].name == tails[0];
        certs_.roles[i] = x_tail ? 2 * o + 2 : 2 * o + 1;
        break;
      }
    }
    certs_.bound_recs.assign(P_.values.size(), kNone);
    for (const auto &[node, pi] : bound_rec_)
      if (auto it = id_of_.find(node); it != id_of_.end())
        certs_.bound_recs[it->second] = Id(pi);
    honest_tables();
  }

  // Per challenge, the degrees of the values and the shared entries
  // (Certificates::deg_vals, deg_refs; Lean `DegAnn`), Lean `Expr.deg`
  // node by node: a value of the challenge has degree 1, a public expression
  // its expression's (its values precede it), any other value 0.
  void challenge_degrees() {
    const size_t nc = P_.challenges.size(), nv = P_.values.size(), nn = P_.nodes.size();
    certs_.deg_vals.assign(nc, {});
    certs_.deg_refs.assign(nc, {});
    for (size_t c = 0; c < nc; ++c) {
      std::vector<uint64_t> vd(nv, 0), nd(nn, 0);
      std::vector<bool> done(nn, false);
      auto val = [&](Id v) -> uint64_t { return v < nv ? vd[v] : 0; };
      std::function<uint64_t(Id)> deg = [&](Id n) -> uint64_t {
        if (n == kNone) return 0;
        if (done[n]) return nd[n];
        const ir::Expr &e = P_.nodes[n];
        auto coef = [&](Id k) -> uint64_t {
          const ir::Coef &x = P_.coefs[k];
          return x.is_const ? 0 : val(x.v);
        };
        uint64_t d = 0;
        switch (e.op) {
          case ir::Expr::kLeaf: d = val(Id(e.x)); break;
          case ir::Expr::kAdd:
          case ir::Expr::kSub:
          case ir::Expr::kConcat: d = std::max(deg(e.a), deg(e.b)); break;
          case ir::Expr::kMul: d = deg(e.a) + deg(e.b); break;
          case ir::Expr::kScale: d = coef(Id(e.x)) + deg(e.a); break;
          case ir::Expr::kReindex: d = deg(e.a); break;
          case ir::Expr::kLinear: {
            uint64_t m = 0;
            for (const auto &row : P_.linears[e.x])
              for (const auto &t : row) m = std::max(m, coef(t.second));
            d = m + deg(e.a);
            break;
          }
          case ir::Expr::kProd: d = e.x * deg(e.a); break;
          case ir::Expr::kMux: d = deg(e.a) + std::max(deg(e.b), deg(e.c)); break;
          case ir::Expr::kApply: {
            uint64_t m = 0;
            Id o = Id(e.x);
            while (o != kNone) {
              const ir::NamedOp &op = P_.ops[o];
              if (op.value != kNone) m = std::max(m, val(op.value));
              o = op.kind == ir::NamedOp::kBatched ? op.inner : kNone;
            }
            d = m + deg(e.a);
            break;
          }
          case ir::Expr::kRef: d = deg(P_.exprs[e.x]); break;
          case ir::Expr::kLogic: {
            uint64_t m = 0;
            for (Id x : e.args) m = std::max(m, deg(x));
            d = 2 * e.x * m;
            break;
          }
        }
        nd[n] = d;
        done[n] = true;
        return d;
      };
      for (size_t v = 0; v < nv; ++v) {
        const ir::Value &x = P_.values[v];
        if (x.kind == ir::Value::kChallenge) vd[v] = x.ref == c ? 1 : 0;
        else if (x.kind == ir::Value::kPubExpr) {
          // The memo holds degrees at the values so far: a public
          // expression reads only earlier values.
          std::fill(done.begin(), done.end(), false);
          vd[v] = deg(x.expr);
        }
      }
      std::fill(done.begin(), done.end(), false);
      certs_.deg_vals[c] = vd;
      for (Id root : P_.exprs) certs_.deg_refs[c].push_back(deg(root));
    }
  }

  // The shared entries' structural annotations (Certificates::expr_max,
  // expr_fields, expr_pub, expr_len; Lean `ExprAnn`) from the entries'
  // closures: VALS gives each node's values (Lean `directNodes` through the
  // shared entries); the values read in the expression's field leave out a
  // MAC's powers (Lean `fieldNodes`), the coefficient values leave out the
  // leaves (Lean `coefNodes`).
  template <class Vals>
  void expr_annotations(Vals &vals) {
    const size_t ne = P_.exprs.size(), nn = P_.nodes.size();
    // Per node, its field values and coefficient values, memoised.
    std::vector<std::vector<Id>> fv(nn), cv(nn);
    std::vector<bool> done(nn, false);
    std::function<void(Id)> walk = [&](Id n) {
      if (done[n]) return;
      const ir::Expr &e = P_.nodes[n];
      std::vector<Id> f, c;
      auto take = [&](Id m) {
        if (m == kNone) return;
        walk(m);
        f.insert(f.end(), fv[m].begin(), fv[m].end());
        c.insert(c.end(), cv[m].begin(), cv[m].end());
      };
      auto coef = [&](Id k) {
        const ir::Coef &x = P_.coefs[k];
        if (!x.is_const) {
          f.push_back(x.v);
          c.push_back(x.v);
        }
      };
      switch (e.op) {
        case ir::Expr::kLeaf:
          f.push_back(Id(e.x));
          break;
        case ir::Expr::kScale:
          coef(Id(e.x));
          take(e.a);
          break;
        case ir::Expr::kLinear:
          for (const auto &row : P_.linears[e.x])
            for (const auto &t : row) coef(t.second);
          take(e.a);
          break;
        case ir::Expr::kApply: {
          Id o = Id(e.x);
          while (o != kNone) {
            const ir::NamedOp &op = P_.ops[o];
            if (op.value != kNone) {
              // A MAC's powers are a foreign operand: a coefficient value
              // read in its own field.
              if (op.kind != ir::NamedOp::kMacConv) f.push_back(op.value);
              c.push_back(op.value);
            }
            o = op.kind == ir::NamedOp::kBatched ? op.inner : kNone;
          }
          take(e.a);
          break;
        }
        case ir::Expr::kRef:
          take(P_.exprs[e.x]);
          break;
        case ir::Expr::kLogic:
          for (Id m : e.args) take(m);
          break;
        default:
          take(e.a);
          take(e.b);
          take(e.c);
          break;
      }
      for (auto *l : {&f, &c}) {
        std::sort(l->begin(), l->end());
        l->erase(std::unique(l->begin(), l->end()), l->end());
      }
      fv[n] = std::move(f);
      cv[n] = std::move(c);
      done[n] = true;
    };
    // Lean `fieldOfV`: a field-only value whose kind allows a field reads
    // its own, any other its domain's (a field-only value names domain 0).
    auto value_field = [&](Id v) -> uint64_t {
      const ir::Value &x = P_.values[v];
      const bool allows = x.kind == ir::Value::kChallenge || x.kind == ir::Value::kPubExpr ||
                          x.kind == ir::Value::kLate || x.kind == ir::Value::kMessage;
      if (x.domain == kNone && allows) return x.field;
      return field_of_domain_.at(x.domain == kNone ? 0 : x.domain);
    };
    // Lean `isPublicT`: neither committed (priv, bits, padCopy, bound) nor
    // late.
    auto is_public = [&](Id v) {
      const ir::Value::Kind k = P_.values[v].kind;
      return k != ir::Value::kPriv && k != ir::Value::kBits && k != ir::Value::kPadCopy &&
             k != ir::Value::kBound && k != ir::Value::kLate;
    };
    // Lean `cellNdT`: 1 for a committed (priv, bits, padCopy, bound) or
    // late value, 0 otherwise; `Expr.deg` and `Expr.zeroAtZero` per node.
    auto cell_nd = [&](Id v) -> uint64_t {
      if (v >= P_.values.size()) return 0;
      const ir::Value::Kind k = P_.values[v].kind;
      return (k == ir::Value::kPriv || k == ir::Value::kBits || k == ir::Value::kPadCopy ||
              k == ir::Value::kBound || k == ir::Value::kLate)
                 ? 1
                 : 0;
    };
    std::vector<uint64_t> ndeg(nn, 0);
    std::vector<bool> nzero(nn, false), dz_done(nn, false);
    std::function<void(Id)> dz = [&](Id n) {
      if (dz_done[n]) return;
      const ir::Expr &e = P_.nodes[n];
      auto sub = [&](Id m) {
        dz(m);
        return std::make_pair(ndeg[m], bool(nzero[m]));
      };
      auto coef_deg = [&](Id k) -> uint64_t {
        const ir::Coef &x = P_.coefs[k];
        return x.is_const ? 0 : cell_nd(x.v);
      };
      uint64_t d = 0;
      bool z = false;
      switch (e.op) {
        case ir::Expr::kLeaf:
          d = cell_nd(Id(e.x));
          z = true;
          break;
        case ir::Expr::kAdd:
        case ir::Expr::kSub:
        case ir::Expr::kConcat: {
          auto [da, za] = sub(e.a);
          auto [db, zb] = sub(e.b);
          d = std::max(da, db);
          z = za && zb;
          break;
        }
        case ir::Expr::kMul: {
          auto [da, za] = sub(e.a);
          auto [db, zb] = sub(e.b);
          d = da + db;
          z = za || zb;
          break;
        }
        case ir::Expr::kScale: {
          auto [da, za] = sub(e.a);
          d = coef_deg(Id(e.x)) + da;
          z = za;
          break;
        }
        case ir::Expr::kReindex: {
          auto [da, za] = sub(e.a);
          d = da;
          z = za;
          break;
        }
        case ir::Expr::kLinear: {
          auto [da, za] = sub(e.a);
          uint64_t m = 0;
          for (const auto &row : P_.linears[e.x])
            for (const auto &t : row) m = std::max(m, coef_deg(t.second));
          d = m + da;
          z = za;
          break;
        }
        case ir::Expr::kProd: {
          auto [da, za] = sub(e.a);
          d = e.x * da;
          z = e.x > 0 && za;
          break;
        }
        case ir::Expr::kMux: {
          auto [db, zb] = sub(e.a);
          auto [dt, zt] = sub(e.b);
          auto [de, ze] = sub(e.c);
          d = db + std::max(dt, de);
          z = ze && (zb || zt);
          break;
        }
        case ir::Expr::kApply: {
          auto [da, za] = sub(e.a);
          uint64_t m = 0;
          Id o = Id(e.x);
          while (o != kNone) {
            const ir::NamedOp &op = P_.ops[o];
            if (op.value != kNone) m = std::max(m, cell_nd(op.value));
            o = op.kind == ir::NamedOp::kBatched ? op.inner : kNone;
          }
          d = m + da;
          z = za;
          break;
        }
        case ir::Expr::kRef: {
          auto [dr, zr] = sub(P_.exprs[e.x]);
          d = dr;
          z = zr;
          break;
        }
        case ir::Expr::kLogic: {
          uint64_t m = 0;
          for (Id x : e.args) m = std::max(m, sub(x).first);
          d = 2 * e.x * m;
          z = false;
          break;
        }
      }
      ndeg[n] = d;
      nzero[n] = z;
      dz_done[n] = true;
    };
    certs_.expr_deg.assign(ne, 0);
    certs_.expr_zero.assign(ne, false);
    for (size_t k = 0; k < ne; ++k) {
      dz(P_.exprs[k]);
      certs_.expr_deg[k] = ndeg[P_.exprs[k]];
      certs_.expr_zero[k] = nzero[P_.exprs[k]];
    }
    certs_.expr_max.assign(ne, 0);
    certs_.expr_fields.assign(ne, 0);
    certs_.expr_len.assign(ne, 0);
    certs_.expr_pub.assign(ne, true);
    for (size_t k = 0; k < ne; ++k) {
      const Id root = P_.exprs[k];
      for (Id v : vals(root))
        certs_.expr_max[k] = std::max<uint64_t>(certs_.expr_max[k], uint64_t(v) + 1);
      walk(root);
      for (Id v : fv[root])
        if (v < P_.values.size()) certs_.expr_fields[k] |= uint64_t(1) << value_field(v);
      for (Id v : cv[root])
        if (v >= P_.values.size() || !is_public(v)) certs_.expr_pub[k] = false;
      certs_.expr_len[k] = P_.nodes[root].n;
    }
  }

  // The honest checks' shared tables (Certificates::pred_vals ...
  // comm_owners), from the finished program's records: each predicate's
  // values, the late values each value reads, the lookups' digits and the
  // committed-digits mod_q's quotient-digit lookups.
  void honest_tables() {
    const size_t nv = P_.values.size(), np = P_.predicates.size();
    // The values each expression node reads (Lean `Expr.directNodes`
    // through the shared entries: leaves, coefficients' values, named
    // operators' value operands), memoised per node.
    std::vector<std::vector<Id>> node_vals(P_.nodes.size());
    std::vector<bool> node_done(P_.nodes.size(), false);
    std::function<const std::vector<Id> &(Id)> vals = [&](Id n) -> const std::vector<Id> & {
      if (node_done[n]) return node_vals[n];
      const ir::Expr &e = P_.nodes[n];
      std::vector<Id> r;
      auto take = [&](Id m) {
        if (m == kNone) return;
        const std::vector<Id> &x = vals(m);
        r.insert(r.end(), x.begin(), x.end());
      };
      auto coef = [&](Id c) {
        const ir::Coef &k = P_.coefs[c];
        if (!k.is_const) r.push_back(k.v);
      };
      switch (e.op) {
        case ir::Expr::kLeaf:
          r.push_back(Id(e.x));
          break;
        case ir::Expr::kScale:
          coef(Id(e.x));
          take(e.a);
          break;
        case ir::Expr::kLinear:
          for (const auto &row : P_.linears[e.x])
            for (const auto &t : row) coef(t.second);
          take(e.a);
          break;
        case ir::Expr::kApply: {
          Id o = Id(e.x);
          while (o != kNone) {
            const ir::NamedOp &op = P_.ops[o];
            if (op.value != kNone) r.push_back(op.value);
            o = op.kind == ir::NamedOp::kBatched ? op.inner : kNone;
          }
          take(e.a);
          break;
        }
        case ir::Expr::kRef:
          take(P_.exprs[e.x]);
          break;
        case ir::Expr::kLogic:
          for (Id m : e.args) take(m);
          break;
        default:
          take(e.a);
          take(e.b);
          take(e.c);
          break;
      }
      std::sort(r.begin(), r.end());
      r.erase(std::unique(r.begin(), r.end()), r.end());
      node_vals[n] = std::move(r);
      node_done[n] = true;
      return node_vals[n];
    };
    // Per shared entry, the values it reads.
    certs_.expr_vals.clear();
    for (Id root : P_.exprs) certs_.expr_vals.push_back(vals(root));
    expr_annotations(vals);
    challenge_degrees();
    // Per value, what it reads (Lean `nodeReads`): a public expression the
    // reads of the values it reads, an opaque value its arguments', a bit
    // view its words', a challenge, a late value or a message itself; a
    // value reads only earlier values.
    certs_.val_reads.assign(P_.values.size(), {});
    for (size_t v = 0; v < P_.values.size(); ++v) {
      const ir::Value &x = P_.values[v];
      auto &out = certs_.val_reads[v];
      auto from = [&](Id u) {
        if (u < v) out.insert(out.end(), certs_.val_reads[u].begin(), certs_.val_reads[u].end());
      };
      switch (x.kind) {
        case ir::Value::kPubExpr:
          for (Id u : vals(x.expr)) from(u);
          break;
        case ir::Value::kOpaque:
          for (Id u : x.args) from(u);
          break;
        case ir::Value::kChallenge: out.push_back(3 * uint64_t(x.ref)); break;
        case ir::Value::kLate: out.push_back(3 * uint64_t(v) + 1); break;
        case ir::Value::kBits: from(x.ref); break;
        case ir::Value::kMessage: out.push_back(3 * uint64_t(x.ref) + 1); break;
        default: break;
      }
      std::sort(out.begin(), out.end());
      out.erase(std::unique(out.begin(), out.end()), out.end());
    }
    // Per predicate, the values its expressions read (Lean `predNodesM`):
    // both sides of an equal, a mod_q or a cross-field equal; an in's record
    // and its set's expression.
    certs_.pred_vals.clear();
    for (const ir::Predicate &q : P_.predicates) {
      std::vector<Id> vs;
      for (Id root : {q.lhs, q.body == ir::Predicate::kMem ? q.set : q.rhs})
        if (root != kNone) {
          const std::vector<Id> &x = vals(root);
          vs.insert(vs.end(), x.begin(), x.end());
        }
      std::sort(vs.begin(), vs.end());
      vs.erase(std::unique(vs.begin(), vs.end()), vs.end());
      certs_.pred_vals.push_back(std::move(vs));
    }
    // The late values each value reads (Lean `readsT`), in value order: a
    // late value reads itself, a message its late value, a bit view its
    // words, a public expression and an opaque function the values they
    // read; an entry reads only the entries before it, as the Lean table.
    std::vector<std::vector<Id>> late(nv);
    for (size_t v = 0; v < nv; ++v) {
      const ir::Value &x = P_.values[v];
      std::vector<Id> r;
      auto add = [&](Id w) {
        if (w < v) r.insert(r.end(), late[w].begin(), late[w].end());
      };
      switch (x.kind) {
        case ir::Value::kPubExpr:
          for (Id w : x.sources) add(w);
          break;
        case ir::Value::kOpaque:
          for (Id w : x.args) add(w);
          break;
        case ir::Value::kLate:
          r.push_back(Id(v));
          break;
        case ir::Value::kBits:
          add(x.ref);
          break;
        case ir::Value::kMessage:
          r.push_back(x.ref);
          break;
        default:
          break;
      }
      std::sort(r.begin(), r.end());
      r.erase(std::unique(r.begin(), r.end()), r.end());
      late[v] = std::move(r);
    }
    // Lean `IsLate`: a late value of a phase in [1, phases]; generated, a
    // realization's (no source value).
    auto is_late = [&](Id u) {
      return u < nv && P_.values[u].kind == ir::Value::kLate &&
             P_.values[u].phase >= 1 && P_.values[u].phase <= cs_.phases();
    };
    certs_.late_bad.assign(nv, false);
    certs_.gen_bad.assign(nv, false);
    for (size_t v = 0; v < nv; ++v)
      for (Id u : late[v])
        if (is_late(u)) {
          certs_.late_bad[v] = true;
          if (P_.values[u].owner != kNone) certs_.gen_bad[v] = true;
        }
    // The two-sided and digit lookups' digits, in predicate order.
    certs_.lookup_owners.clear();
    for (size_t pid = 0; pid < np; ++pid) {
      const ir::Predicate &q = P_.predicates[pid];
      if (q.body != ir::Predicate::kMem || q.in.implied ||
          (q.in.lookup.kind != ir::LookupKind::kTwoSided &&
           q.in.lookup.kind != ir::LookupKind::kDigits))
        continue;
      const ir::LookupRealization &r = q.in.lookup;
      for (size_t j = 0; j < r.digit_values.size(); ++j)
        certs_.lookup_owners.push_back({r.digit_values[j], Id(pid), false, j});
      for (size_t j = 0; j < r.second.size(); ++j)
        certs_.lookup_owners.push_back({r.second[j], Id(pid), true, j});
    }
    // The quotient digit each digit lookup bounds: digit j of the first
    // source committed-digits mod_q whose ranges (ModRow records) list it.
    std::map<Id, std::pair<Id, size_t>> rec_of;
    for (size_t m = 0; m < np; ++m) {
      const ir::Predicate &q = P_.predicates[m];
      if (q.body != ir::Predicate::kMod ||
          q.role != ir::Predicate::Role::kSource ||
          q.mod.form != ir::ModForm::kCommittedDigits)
        continue;
      for (size_t j = 0; j < q.mod.ranges.size(); ++j)
        rec_of.emplace(q.mod.ranges[j], std::make_pair(Id(m), j));
    }
    certs_.comm_owners.clear();
    for (size_t lk = 0; lk < np; ++lk) {
      const ir::Predicate &q = P_.predicates[lk];
      auto it = rec_of.find(Id(lk));
      if (it == rec_of.end() || q.body != ir::Predicate::kMem || q.in.implied ||
          q.in.lookup.kind != ir::LookupKind::kDigits)
        continue;
      const ir::LookupRealization &r = q.in.lookup;
      for (size_t k = 0; k < r.digit_values.size(); ++k)
        certs_.comm_owners.push_back(
            {r.digit_values[k], it->second.first, it->second.second, Id(lk), k});
    }
    completion_certs();
  }

  // The completeness certificate (Lean `Gens`, `CDerivations`): each
  // value's generator from the records the realizations left (a source
  // value, a group's static or late histogram, a lookup digit, a committed
  // digit, a convolution's transformed value); each source predicate derived
  // by `source`, each quotient range of a source one-digit mod_q by
  // `quotIn`, each quotient-digit lookup and field equation of a source
  // committed-digits mod_q by `commIn` and `commRow`, each convolution's
  // products predicate by `specProd`, each realized predicate by `specRow`,
  // each field-form mod_q's row by `fieldRow`; every other predicate without a derivation (the checker
  // refuses the certificate).
  void completion_certs() {
    using CG = ir::Certificates::Gen;
    using CS = ir::Certificates::CStep;
    const size_t nv = P_.values.size(), np = P_.predicates.size();
    // The first row of kind K of mod_q M (PlanRecords::ModRow), by the
    // lowerings' row names (kNone where none).
    std::map<std::string, Id> row_id;
    for (size_t i = 0; i < preds_.size(); ++i)
      if (preds_[i].row) row_id.emplace(preds_[i].name, Id(i));
    auto mod_row = [&](size_t m, PlanRecords::ModRow::Kind k) -> Id {
      if (m >= preds_.size() || preds_[m].mod_ranges.empty()) return kNone;
      for (const auto &r : cs_.records().mod_rows)
        if (r.mod == preds_[m].mod_ranges && r.kind == k) {
          auto it = row_id.find(r.row);
          return r.row.empty() || it == row_id.end() ? kNone : it->second;
        }
      return kNone;
    };
    certs_.gens.assign(nv, CG{});
    for (size_t v = 0; v < nv; ++v)
      if (P_.values[v].owner == kNone) certs_.gens[v].kind = CG::kSource;
    for (size_t t = 0; t < P_.tables.size(); ++t)
      for (size_t g = 0; g < P_.tables[t].groups.size(); ++g) {
        const auto &gr = P_.tables[t].groups[g];
        if (gr.static_mult != kNone && gr.static_mult < nv)
          certs_.gens[gr.static_mult] = CG{CG::kStaticHist, t, g, 0, 0, false};
        if (gr.late_mult != kNone && gr.late_mult < nv)
          certs_.gens[gr.late_mult] = CG{CG::kLateHist, t, g, 0, 0, false};
      }
    // A committed quotient digit is also a digit lookup's digit; its
    // generator is the quotient's (as the honest prover's commDigitOwner?
    // comes before lookupDigitOwner?).
    for (const auto &x : certs_.comm_owners)
      if (x.value < nv && certs_.gens[x.value].kind == CG::kNone)
        certs_.gens[x.value] = CG{CG::kCommDigit, x.mod, x.j, x.lk, x.k, false};
    for (const auto &x : certs_.lookup_owners)
      if (x.value < nv && certs_.gens[x.value].kind == CG::kNone)
        certs_.gens[x.value] = CG{CG::kLookupDigit, x.pid, x.idx, 0, 0, x.second};
    // The transformed value z of each spectrally realized convolution: the
    // right side of its products predicate NTT(a) NTT(b) = z.
    for (size_t k = 0; k < P_.convs.size(); ++k) {
      const Id p = P_.convs[k].products;
      if (p >= P_.predicates.size()) continue;
      const Id r = P_.predicates[p].rhs;
      if (r >= P_.nodes.size() || P_.nodes[r].op != ir::Expr::kLeaf) continue;
      const size_t z = size_t(P_.nodes[r].x);
      if (z < nv && certs_.gens[z].kind == CG::kNone)
        certs_.gens[z] = CG{CG::kSpec, k, 0, 0, 0, false};
    }
    certs_.comp_derivs.assign(np, {});
    certs_.comp_ranks.assign(np, 0);
    // A source predicate: of the source role, or the type check of a source
    // value (Lean `inSource`).
    for (size_t q = 0; q < np; ++q) {
      const ir::Predicate &pr = P_.predicates[q];
      if (pr.role == ir::Predicate::Role::kSource ||
          (pr.role == ir::Predicate::Role::kType && pr.owner < nv &&
           P_.values[pr.owner].owner == kNone))
        certs_.comp_derivs[q] = {CS{CS::kSource, q}};
    }
    for (size_t m = 0; m < np; ++m) {
      const ir::Predicate &q = P_.predicates[m];
      if (q.body != ir::Predicate::kMod || q.role != ir::Predicate::Role::kSource ||
          q.mod.form != ir::ModForm::kOneDigit)
        continue;
      for (Id rid : q.mod.ranges)
        if (rid < np && certs_.comp_derivs[rid].empty())
          certs_.comp_derivs[rid] = {CS{CS::kQuotIn, m}};
    }
    // A source committed-digits mod_q's quotient-digit lookups by `commIn`
    // (the first mod_q listing each, as comm_owners), and its field equation
    // (its realize record) by `commRow`, naming the lookup of each digit.
    for (size_t m = 0; m < np; ++m) {
      const ir::Predicate &q = P_.predicates[m];
      if (q.body != ir::Predicate::kMod || q.role != ir::Predicate::Role::kSource ||
          q.mod.form != ir::ModForm::kCommittedDigits)
        continue;
      std::vector<size_t> lks;
      for (size_t j = 0; j < q.mod.ranges.size(); ++j) {
        const Id lk = q.mod.ranges[j];
        lks.push_back(size_t(lk));
        if (lk >= np || !certs_.comp_derivs[lk].empty()) continue;
        const ir::Predicate &l = P_.predicates[lk];
        if (l.body != ir::Predicate::kMem || l.in.implied ||
            l.in.lookup.kind != ir::LookupKind::kDigits)
          continue;
        CS st{CS::kCommIn, m};
        st.j = j;
        certs_.comp_derivs[lk] = {st};
      }
      const Id row = mod_row(m, PlanRecords::ModRow::kCommitted);
      if (row < np && certs_.comp_derivs[row].empty()) {
        CS st{CS::kCommRow, m};
        st.lks = lks;
        certs_.comp_derivs[row] = {st};
      }
    }
    // The products predicate of each spectrally realized convolution, the
    // realized predicate of each source equal or mod_0 that reads one
    // (its target `realized q`), and the field row of each source
    // field-form mod_q (its realized predicates, Certificates::realize).
    for (size_t k = 0; k < P_.convs.size(); ++k) {
      const Id p = P_.convs[k].products;
      if (p < np && certs_.comp_derivs[p].empty())
        certs_.comp_derivs[p] = {CS{CS::kSpecProd, k}};
    }
    for (size_t m = 0; m < np; ++m) {
      const ir::Predicate &q = P_.predicates[m];
      if (q.role != ir::Predicate::Role::kSource) continue;
      Id r = kNone;
      if (q.body == ir::Predicate::kEqual && q.target.kind == ir::Target::kRealized)
        r = q.target.id;
      if (q.body == ir::Predicate::kMod && q.mod.target &&
          q.mod.target->kind == ir::Target::kRealized)
        r = q.mod.target->id;
      if (r < np && certs_.comp_derivs[r].empty())
        certs_.comp_derivs[r] = {CS{CS::kSpecRow, m}};
      if (q.body == ir::Predicate::kMod && q.mod.form == ir::ModForm::kField) {
        const Id f = mod_row(m, PlanRecords::ModRow::kField);
        if (f < np && certs_.comp_derivs[f].empty())
          certs_.comp_derivs[f] = {CS{CS::kFieldRow, 0}};
      }
    }
    // The MACs' late values: the tag of each cross-field equal, and its
    // tails' accumulators and quotient digits (a grouped tail's, an
    // ungrouped digit tail's accumulator and lower digits, or a one-digit
    // tail's accumulator). A MAC no domain hosts has a tail per field: each
    // tail's values are those of its domain.
    for (size_t p = 0; p < np; ++p) {
      const ir::Predicate &c = P_.predicates[p];
      if (c.body != ir::Predicate::kCross) continue;
      if (c.mac.tag < nv) certs_.gens[c.mac.tag] = CG{CG::kTag, p, 0, 0, 0, false};
      for (size_t tail = 0; tail < np; ++tail) {
        const ir::Predicate &tp = P_.predicates[tail];
        if (tp.body != ir::Predicate::kMod ||
            tp.role != ir::Predicate::Role::kRealization || tp.owner != Id(p))
          continue;
        const ir::ModRealization &tm = tp.mod;
        const bool grouped = tm.grouped.has_value();
        // A one-digit tail: its accumulator, the leaf of the quotient's
        // first summand a acc + b R through one shared entry (Lean
        // oneDigitAcc), is generated as the tail's accumulator (Lean
        // digitsAcc).
        if (!grouped && tm.form == ir::ModForm::kOneDigit &&
            tm.quotient < P_.nodes.size()) {
          const ir::Expr *e = &P_.nodes[tm.quotient];
          if (e->op == ir::Expr::kRef && e->x < P_.exprs.size() &&
              P_.exprs[e->x] < P_.nodes.size())
            e = &P_.nodes[P_.exprs[e->x]];
          if (e->op == ir::Expr::kAdd && e->a < P_.nodes.size()) {
            const ir::Expr &sc = P_.nodes[e->a];
            if (sc.op == ir::Expr::kScale && sc.a < P_.nodes.size() &&
                P_.nodes[sc.a].op == ir::Expr::kLeaf && P_.nodes[sc.a].x < nv)
              certs_.gens[P_.nodes[sc.a].x] =
                  CG{CG::kDigitsAcc, tail, 0, 0, 0, false};
          }
        }
        // A grouped tail's accumulators and quotient digits (Lean acc,
        // quotDigit); an ungrouped digit tail's accumulator and lower
        // digits (Lean digitsAcc, lowDigit), numbered within the tail.
        for (Id a : c.mac.accumulators)
          if (a < nv && P_.values[a].domain == tp.domain)
            certs_.gens[a] = CG{grouped ? CG::kAcc : CG::kDigitsAcc, tail, 0, 0, 0, false};
        size_t j = 0;
        for (Id q : c.mac.quotient_digits) {
          if (q >= nv || P_.values[q].domain != tp.domain) continue;
          certs_.gens[q] = grouped ? CG{CG::kQuotDigit, tail, 0, 0, 0, false}
                                   : CG{CG::kLowDigit, tail, j, 0, 0, false};
          ++j;
        }
      }
    }
    // The MACs' predicates (their sites, Certificates::roles) and the Boolean
    // checks of the pad copies.
    for (size_t q = 0; q < np; ++q) {
      if (!certs_.comp_derivs[q].empty()) continue;
      const size_t r = q < certs_.roles.size() ? certs_.roles[q] : 0;
      if (r != 0) {
        const size_t pid = (r - 1) / 2;
        const bool x_side = r % 2 == 0;
        // A check over a field of characteristic 2 (Lean isTwoSiteB): of a
        // MAC no domain hosts, in a domain of characteristic 2. Its one
        // predicate is its tail, the field equal b + macConv(r)(z) =
        // bits(T) (Lean twoTail).
        const ir::Predicate &c = P_.predicates[pid];
        const Id d = x_side ? c.domain : c.dy;
        const bool two = c.mac.blind_x != kNone && d < P_.domains.size() &&
                         P_.domains[d].field < P_.fields.size() &&
                         P_.fields[P_.domains[d].field].characteristic == "2";
        CS st{two ? CS::kTwoTail : CS::kMacRow, pid};
        st.x_side = x_side;
        certs_.comp_derivs[q] = {st};
        continue;
      }
      const ir::Predicate &pr = P_.predicates[q];
      if (pr.role == ir::Predicate::Role::kType && pr.owner < nv &&
          P_.values[pr.owner].kind == ir::Value::kPadCopy)
        certs_.comp_derivs[q] = {CS{CS::kPadBool, 0}};
    }
    // The reconstruction and top rows of a two-sided or digit lookup: the
    // realization predicates it owns.
    for (size_t q = 0; q < np; ++q) {
      const ir::Predicate &pr = P_.predicates[q];
      if (pr.role != ir::Predicate::Role::kRealization || pr.owner >= np ||
          !certs_.comp_derivs[q].empty())
        continue;
      const ir::Predicate &o = P_.predicates[pr.owner];
      if (o.body == ir::Predicate::kMem && !o.in.implied &&
          (o.in.lookup.kind == ir::LookupKind::kTwoSided ||
           o.in.lookup.kind == ir::LookupKind::kDigits))
        certs_.comp_derivs[q] = {CS{CS::kDigitRow, size_t(pr.owner)}};
    }
  }

  // A part of the program the structure cannot describe: the printer
  // refuses the program with the first (Program::unmodeled); the backend,
  // which reads the elements' origins and targets, is unaffected.
  void gap(const std::string &why) { P_.unmodeled.push_back(why); }
  // Predicate NAME's id, kNone (a gap) for a name no predicate has.
  Id pid(const std::string &name) {
    auto it = pred_id_.find(name);
    if (it == pred_id_.end()) {
      gap("no predicate is named '" + name + "'");
      return kNone;
    }
    return Id(it->second);
  }

  // The owner of a lowering's part named NAME: the predicate whose name
  // is the longest dotted prefix of it (a mod's rows, a MAC tail's ranges),
  // or the in predicate of request R for range.R.*.
  std::string owner_of(const std::string &name, bool value = false,
                       const PredRec *self = nullptr) const {
    std::string best, cand;
    auto consider = [&](const std::string &c, const std::string &owner) {
      if ((name == c || name.rfind(c + ".", 0) == 0) && c.size() > cand.size()) {
        cand = c;
        best = owner;
      }
    };
    for (const auto &p : preds_) {
      if (p.role == "type" || p.row || &p == self) continue;
      // A value named as its range request (an assert_mod's group digits,
      // mac.gq) is the assert_mod's: an in predicate owns only range.<r>.*.
      if (!(value && p.mem)) consider(p.name, p.name);
      if (p.mem) consider("range." + p.name, p.name);
    }
    return best;
  }

  ir::Space space_of(const std::string &pad_space, size_t place) const {
    ir::Space s;
    s.full = pad_space == dom_field_name(place);
    if (!s.full) s.node = pad_space;
    return s;
  }

  void finish() {
    const auto &N = cs_.nodes();
    // Field and domain tables.
    for (size_t d = 0; d < cs_.num_domains(); ++d) {
      with_domain(d, [&](const auto &dm) {
        ir::FieldDecl row{dm.field_name(),
                          plan_export_internal::characteristic_str(dm.field()),
                          plan_of(d).field_degree};
        auto it = std::find(P_.fields.begin(), P_.fields.end(), row);
        field_of_domain_[d] = size_t(it - P_.fields.begin());
        if (it == P_.fields.end()) P_.fields.push_back(row);
      });
    }
    // The fields no domain commits, after the domains' (their places past
    // the domains).
    for (size_t k = 0; k < bare_.size(); ++k) {
      const size_t d = cs_.num_domains() + k;
      S::dispatch(bare_[k].first, [&](auto tag) {
        using F = typename decltype(tag)::type;
        ir::FieldDecl row{bare_field_name(d),
                          plan_export_internal::characteristic_str(
                              *static_cast<const F *>(bare_[k].second)),
                          size_t(F::kBits)};
        auto it = std::find(P_.fields.begin(), P_.fields.end(), row);
        field_of_domain_[d] = size_t(it - P_.fields.begin());
        if (it == P_.fields.end()) P_.fields.push_back(row);
      });
    }
    // Roles: the lowerings' parts.
    for (auto &p : preds_) {
      if (p.role != "realization" || !p.owner_name.empty()) continue;
      p.owner_name = owner_of(p.name, false, &p);
      if (p.owner_name.empty())
        gap("the lowering's predicate '" + p.name + "' has no owner");
    }
    // Range requests a lowering declared: owned by a mod (its quotient
    // digits) or the MAC tail.
    for (auto &p : preds_) {
      if (p.role != "source" || !p.mem) continue;
      for (const auto &m : mod_names_)
        if (p.name.rfind(m + ".", 0) == 0 && p.name != m) {
          p.role = "realization";
          p.owner_name = m;
        }
    }
    // Names to ids; a lowering's row may share its predicate's name (the
    // field form of assert_mod), and names the predicate.
    for (size_t i = 0; i < preds_.size(); ++i) {
      if (preds_[i].row) continue;
      if (pred_id_.count(preds_[i].name)) {
        gap("two predicates named '" + preds_[i].name + "'");
        continue;
      }
      pred_id_[preds_[i].name] = i;
    }
    value_roles();
    // Late reads and type sources.
    for (auto &[id, v] : vals_) {
      if (v.kind == "late") {
        v.reads = late_reads(id);
        v.pad_space = pad_space(id);
      }
      if (v.kind == "expr" || v.kind == "bound") {
        try {
          pub_expr(id);
        } catch (const std::runtime_error &e) {
          v.unmodeled = e.what();
        }
      }
      const std::string want = type_node(v);
      if (want.empty()) {
        v.type_source = "none";
      } else if (v.kind == "priv" || v.kind == "bits" || v.kind == "padCopy") {
        v.type_source = v.node_name == want || v.kind == "bits" ? "node" : "pred";
      } else if (v.kind == "late") {
        v.type_source = v.pad_space == want ? "node" : "pred";
      }
      if (v.type_source == "pred" && v.type_pred.empty())
        gap("value '" + v.name + "' has no type source");
    }
    // Value ids: constants, then nodes in order.
    for (const auto &c : const_recs_) id_of_[c.key] = id_of_.size();
    for (size_t id = 0; id < N.size(); ++id)
      if (vals_.count(id)) id_of_[id] = id_of_.size();
    auto vid = [&](size_t key) -> Id {
      auto it = id_of_.find(key);
      if (it == id_of_.end()) {
        gap("a reference to node " + std::to_string(key) + ", which is no value");
        return kNone;
      }
      return Id(it->second);
    };
    auto read_of = [&](const ProgramRead &r) {
      ir::Read o;
      o.kind = r.kind == ProgramRead::kChal   ? ir::Read::kChal
               : r.kind == ProgramRead::kLate ? ir::Read::kLate
                                              : ir::Read::kPad;
      o.id = r.kind == ProgramRead::kChal ? Id(r.id) : vid(r.id);
      return o;
    };
    auto degree_of = [](const std::map<size_t, size_t> &m) {
      std::vector<std::pair<Id, size_t>> o;
      // Zero degrees are kept: a listed but zero degree prints as an empty
      // list where an unlisted one prints nothing (Value.degree).
      for (const auto &[c, k] : m) o.push_back({Id(c), k});
      return o;
    };
    // The values.
    auto value_of = [&](const ValueRec &v) {
      ir::Value o;
      o.name = v.name;
      if (bare_place(v.domain)) {
        o.domain = kNone;
        o.field = Id(field_of_domain_.at(v.domain));
      } else {
        o.domain = Id(v.domain);
      }
      o.shape = v.shape;
      o.type = v.type;
      o.sub = v.sub;
      o.phase = v.phase;
      o.cnode = v.node == SIZE_MAX ? kNone : Id(v.node);
      static const std::map<std::string, ir::Value::Kind> kinds = {
          {"priv", ir::Value::kPriv},       {"input", ir::Value::kInput},
          {"opaque", ir::Value::kOpaque},   {"expr", ir::Value::kPubExpr},
          {"constant", ir::Value::kConstant},
          {"challenge", ir::Value::kChallenge},
          {"late", ir::Value::kLate},       {"bits", ir::Value::kBits},
          {"padCopy", ir::Value::kPadCopy}, {"message", ir::Value::kMessage},
          {"bound", ir::Value::kBound}};
      o.kind = kinds.at(v.kind);
      if (o.kind == ir::Value::kPriv || o.kind == ir::Value::kBits ||
          o.kind == ir::Value::kPadCopy)
        o.node = v.node_name;
      o.type_source = v.type_source == "node"   ? ir::Value::TypeSource::kNode
                      : v.type_source == "pred" ? ir::Value::TypeSource::kPred
                                                : ir::Value::TypeSource::kNone;
      if (!v.type_pred.empty()) o.type_pred = pid(v.type_pred);
      if (o.kind == ir::Value::kLate) {
        for (const auto &r : v.reads) o.reads.push_back(read_of(r));
        o.pad_space = space_of(v.pad_space, v.domain);
      }
      if (o.kind == ir::Value::kPubExpr) o.degree = degree_of(v.degree);
      if (v.bound != 0) o.bound = bound_str(v.bound);
      if (!v.owner.empty()) o.owner = pid(v.owner);
      o.opaque = v.opaque;
      for (size_t a : v.args) o.args.push_back(vid(a));
      o.expr = v.expr;
      o.entries = v.entries;
      if (o.kind == ir::Value::kChallenge) o.ref = Id(chal_of_.at(v.ref));
      if ((o.kind == ir::Value::kBits || o.kind == ir::Value::kPadCopy ||
           o.kind == ir::Value::kMessage) &&
          v.ref != SIZE_MAX)
        o.ref = vid(v.ref);
      o.select = v.select;
      for (size_t k : v.sources) o.sources.push_back(vid(k));
      o.unmodeled = v.unmodeled;
      return o;
    };
    for (const auto &c : const_recs_) P_.values.push_back(value_of(c));
    for (const auto &[id, v] : vals_) P_.values.push_back(value_of(v));
    // The expressions' leaves and the operators' value parameters.
    for (auto &x : P_.nodes)
      if (x.op == ir::Expr::kLeaf) x.x = vid(size_t(x.x));
    for (auto &o : P_.ops)
      if (o.value != kNone) o.value = vid(o.value);
    for (auto &c : P_.coefs)
      if (!c.is_const) c.v = vid(c.v);
    // Batch and circuit numbers.
    auto target = [&](const TargetRec &t) {
      ir::Target o;
      o.kind = t.kind;
      if (t.kind == ir::Target::kBatch) {
        auto it = batch_id_.find({t.domain, t.batch});
        if (it == batch_id_.end())
          gap("a predicate in no batch: " + t.batch);
        else
          o.id = Id(it->second);
      } else if (t.kind == ir::Target::kRealized) {
        o.id = Id(t.realized);
      } else if (t.kind == ir::Target::kGkr) {
        auto it = circuit_id_.find(t.domain);
        if (it == circuit_id_.end())
          gap("a predicate placed in domain " + std::to_string(t.domain) +
              "'s circuit, which runs no GKR");
        else
          o.id = Id(it->second);
      }
      return o;
    };
    // The predicates.
    for (size_t i = 0; i < preds_.size(); ++i) {
      PredRec &r = preds_[i];
      ir::Predicate q = std::move(r.p);
      q.name = r.name;
      if (q.body == ir::Predicate::kEqual) q.target = target(r.target);
      if (r.mod_target) q.mod.target = target(r.target);
      if (!r.mod_ranges.empty()) {
        // An assert_mod's quotient ranges: their ids and (n, N, m).
        auto it = mod_ranges_.find(r.mod_ranges);
        if (it != mod_ranges_.end())
          for (const auto &nm : it->second) {
            auto pid = pred_id_.find(nm);
            auto b = req_bounds_.find(nm);
            if (pid == pred_id_.end() || b == req_bounds_.end()) {
              gap("assert_mod '" + r.mod_ranges + "': no range '" + nm + "'");
              continue;
            }
            const auto &[n, est, m] = b->second;
            q.mod.ranges.push_back(Id(pid->second));
            q.mod.bounds.push_back({bound_str(n), bound_str(est), bound_str(m)});
          }
      }
      if (q.body == ir::Predicate::kMem && !q.in.implied) {
        for (auto &v : q.in.lookup.digit_values) v = vid(v);
        for (auto &v : q.in.lookup.second) v = vid(v);
      }
      if (q.body == ir::Predicate::kCross) {
        ir::MacRealization &m = q.mac;
        m.mac_field = Id(field_of_domain_.at(mac_place_.at(i)));
        if (m.blind_x != kNone) m.blind_x = vid(m.blind_x);
        m.blind = vid(m.blind);
        m.tag = vid(m.tag);
        if (!r.h_predicate.empty()) m.h_predicate = pid(r.h_predicate);
        for (auto &v : m.accumulators) v = vid(v);
        for (auto &v : m.quotient_digits) v = vid(v);
      }
      for (const auto &x : r.reads) q.reads.push_back(read_of(x));
      q.degree = degree_of(r.degree);
      if (r.role == "realization") {
        q.role = ir::Predicate::Role::kRealization;
        q.owner = pid(r.owner_name);
      } else if (r.role == "type") {
        q.role = ir::Predicate::Role::kType;
        q.owner = vid(r.type_value);
      }
      for (size_t k : r.values) q.values.push_back(vid(k));
      q.needles = r.needles;
      q.size = r.size;
      P_.predicates.push_back(std::move(q));
    }
    // Tables.
    for (const auto &T : tables_) {
      ir::Table t;
      t.name = T.name;
      t.domain = Id(T.domain);
      t.size = bound_str(T.size);
      t.rows_expr = T.rows_expr;
      t.alpha = Id(T.alpha);
      for (size_t k = 0; k < T.groups.size(); ++k) {
        const auto &x = T.groups[k];
        ir::TableGroup g;
        g.capacity = x.capacity;
        g.static_mult = x.m0 == SIZE_MAX ? kNone : vid(x.m0);
        g.late_mult = x.m1 == SIZE_MAX ? kNone : vid(x.m1);
        g.merged = x.merged;
        for (const auto &[rn, needle, first, count] : T.members[k])
          g.members.push_back({pid(rn), needle, first, count});
        t.groups.push_back(std::move(g));
      }
      P_.tables.push_back(std::move(t));
    }
    // Challenges.
    for (size_t c = 0; c < chals_.size(); ++c) {
      const Node &n = N[chals_[c]];
      const int dd = domain_of(chals_[c]);
      if (dd < 0 || !field_of_domain_.count(size_t(dd))) {
        gap("challenge '" + n.name + "' lies in no field of the program");
        continue;
      }
      const size_t d = size_t(dd);
      ir::Challenge ch;
      ch.name = n.name;
      ch.field = Id(field_of_domain_.at(d));
      ch.phase = cs_.phase(chals_[c]);
      ch.size = n.n;
      if (bare_place(d) && n.sampler != "field")
        gap("challenge '" + n.name + "' of a field no domain commits is not "
            "drawn from the whole field");
      if (n.sampler == "subfield")
        with_domain(d, [&](const auto &dm) {
          using F = std::decay_t<decltype(dm.field())>;
          ch.sampler = ir::Challenge::Sampler::kNode;
          ch.node = tree_node(dm, designated_degree_of<F>());
        });
      if (n.sampler == "field-minus-tables") {
        ch.sampler = ir::Challenge::Sampler::kMinusRange;
        ch.tmax = excluded_range(n.name);
      }
      // assert_in's alpha with no range table of its domain: uniform in the
      // field minus the empty range [0, 0) (Lean's fieldMinusTables).
      for (const auto &t : cs_.records().in_lookups)
        if (t.alpha == chals_[c] && n.sampler == "field") {
          ch.sampler = ir::Challenge::Sampler::kMinusRange;
          ch.tmax = "0";
        }
      challenge_role(chals_[c], ch);
      P_.challenges.push_back(std::move(ch));
    }
    // Messages.
    for (size_t x : cs_.messages()) {
      if (!vals_.count(x)) {
        gap("the message of '" + N[x].name + "' is of no value");
        continue;
      }
      const auto &v = vals_.at(x);
      ir::Message m;
      m.value = vid(x);
      if (bare_place(v.domain)) {
        m.domain = kNone;
        m.field = Id(field_of_domain_.at(v.domain));
      } else {
        m.domain = Id(v.domain);
      }
      m.phase = v.phase;
      m.size = v.size;
      m.space = space_of(v.pad_space, v.domain);
      m.subfield_message = cs_.message_space(x) != Space::kField;
      if (auto pd = pad_of_late_.find(x); pd != pad_of_late_.end())
        m.pad = N[pd->second].name;
      P_.messages.push_back(std::move(m));
    }
    // Batches.
    for (size_t b = 0; b < batches_.size(); ++b) {
      const auto &[B, di, char2] = batches_[b];
      ir::Batch o;
      o.name = B.name;
      o.domain = Id(di);
      o.bit_operands = B.bit_operands;
      o.degree = B.degree;
      o.instances = B.instances;
      o.width = B.width;
      o.rounds = B.rounds;
      o.pads = B.pads;
      o.bit_sumcheck = B.bit_phase > 0;
      o.char2 = char2;
      const TargetRec want{ir::Target::kBatch, di, B.name};
      // Its parts: the predicates it is the target of (an equal's, or an
      // integer mod_0's realization's).
      for (size_t i = 0; i < preds_.size(); ++i)
        if (preds_[i].target == want) o.parts.push_back(Id(i));
      // A batch states its relation by its parts: a declared batch whose
      // relation no predicate states (a custom operand map the schema has
      // no form for) is an element with no description.
      if (o.parts.empty())
        gap("the batch '" + o.name + "' has no part: the program states no "
            "relation of it");
      P_.batches.push_back(std::move(o));
    }
    // Circuits: the predicates and entries in emission order, the input
    // layout as positioned blocks, the shape.
    for (size_t c = 0; c < circuits_.size(); ++c) {
      const auto &[di, Pl] = circuits_[c];
      ir::Circuit C;
      C.name = cs_.domain(di).name;
      C.domain = Id(di);
      C.public_inputs = Pl.npub;
      C.input_count = Pl.ninputs;
      C.layers = Pl.layers;
      C.wires = Pl.wires;
      C.terms = Pl.quad_terms;
      auto type_pred = [&](size_t id) {
        auto it = pred_id_.find(N[id].name + ".boolean");
        if (it == pred_id_.end()) {
          gap("the Boolean check of '" + N[id].name + "' is no predicate");
          return size_t(kNone);
        }
        return it->second;
      };
      for (const auto &e : Pl.circuit_entries) {
        using CE = DomainPlan::CircuitEntry;
        ir::CircuitEntry o;
        if (e.kind == CE::kTypeCheck) {
          o.kind = ir::CircuitEntry::kTypeCheck;
          o.id = type_pred(e.id);
          C.predicates.push_back(Id(o.id));
        } else if (e.kind == CE::kAlignment) {
          o.kind = ir::CircuitEntry::kAlignment;
          o.id = e.id;
        } else if (e.kind == CE::kPredicate) {
          o.kind = ir::CircuitEntry::kPred;
          o.id = dom_pred_.at({di, e.id});
          C.predicates.push_back(Id(o.id));
        } else {
          o.kind = ir::CircuitEntry::kRealization;
          o.real = real_circuit(e.name);
        }
        C.entries.push_back(std::move(o));
      }
      // The blocks: slots, cells and views, batch pads, filler runs.
      std::vector<ir::InputBlock> blocks;
      for (const auto &in : Pl.inputs) {
        const Node &n = N[in.id];
        using In = DomainPlan::Input;
        ir::InputBlock b;
        b.at = in.at;
        b.n = in.n;
        b.name = n.name;
        const bool pub = in.storage == In::kPublic || in.storage == In::kMessage;
        if (pub && cls_[in.id] != kValue) {
          b.kind = ir::InputBlock::kRealizationPub;
          b.real.name = n.name;
        } else if (pub) {
          b.kind = ir::InputBlock::kPub;
          b.value = vid(in.id);
        } else if (in.storage == In::kView) {
          b.kind = ir::InputBlock::kView;
          b.value = vid(in.id);
        } else if (n.kind == Kind::kPad) {
          b.kind = ir::InputBlock::kPad;
          // A key pad (Node::key_pad) masks no message.
          if (auto lp = late_of_pad_.find(in.id); lp != late_of_pad_.end())
            b.value = vid(lp->second);
          else
            gap("circuit input '" + n.name + "' is a pad that masks no message");
        } else if (vals_.count(in.id)) {
          b.kind = ir::InputBlock::kCommitted;
          b.value = vid(in.id);
        } else {
          gap("circuit input '" + n.name + "' is no value");
        }
        blocks.push_back(std::move(b));
      }
      for (const auto &b : Pl.batches)
        if (b.pads) {
          ir::InputBlock x;
          x.kind = ir::InputBlock::kBatchPads;
          x.value = Id(batch_id_.at({di, b.name}));
          x.at = b.pad_input;
          x.n = b.pads;
          x.name = b.name;
          blocks.push_back(std::move(x));
        }
      for (size_t i = 0; i < Pl.filler.size();) {
        size_t j = i + 1;
        while (j < Pl.filler.size() && Pl.filler[j] == Pl.filler[j - 1] + 1) ++j;
        ir::InputBlock x;
        x.kind = ir::InputBlock::kFiller;
        x.at = Pl.filler[i];
        x.n = j - i;
        blocks.push_back(std::move(x));
        i = j;
      }
      std::stable_sort(blocks.begin(), blocks.end(),
                       [](const ir::InputBlock &a, const ir::InputBlock &b) {
                         return a.at < b.at;
                       });
      size_t pos = 1;
      for (const auto &b : blocks) {
        if (b.at != pos)
          gap("domain " + cs_.domain(di).name + ": the circuit's inputs " +
              std::to_string(pos) + " to " + std::to_string(b.at) +
              " are in no block");
        pos = b.at + b.n;
      }
      if (pos > Pl.ninputs) gap("circuit blocks past the inputs");
      if (pos < Pl.ninputs) {
        ir::InputBlock x;
        x.kind = ir::InputBlock::kFiller;
        x.at = pos;
        x.n = Pl.ninputs - pos;
        blocks.push_back(std::move(x));
      }
      // The realization inputs, in block order (numbering the unmodeled
      // ones in order of appearance).
      for (auto &b : blocks)
        if (b.kind == ir::InputBlock::kRealizationPub) b.real = real_pub(b.real.name);
      C.inputs = std::move(blocks);
      P_.circuits.push_back(std::move(C));
    }
    for (const auto &[name, di] : real_circuits_)
      P_.realization_circuits.push_back({real_circuit(name), Id(di)});
    certificates();
    for (size_t d = 0; d < cs_.num_domains(); ++d)
      P_.domains.push_back({cs_.domain(d).name, Id(field_of_domain_.at(d))});
    P_.index_map_forms.resize(P_.index_maps.size());
    P_.phases = cs_.phases();
    for (const auto &c : cs_.records().member_checks)
      P_.checks.push_back({c.member, c.offset, c.bytes, c.check, c.args});
    if (want_derivations_) derivations();
  }

  // ------------------------------------------------------ derivations --

  // The derivations (ir::Certificates::derivations): each predicate's, as
  // its lowering recorded it (PlanRecords::derivations, the last record of
  // a name), with names and nodes resolved to the program's ids and each
  // request's derivation spliced where another one reads its range. A
  // field equal on a target of its own (affine rows, quadratic, batch,
  // circuit) is realized as written: realized p, conclude. Every
  // derivation is checked (derivation_check.h); a predicate without one
  // has its gap (Certificates::deriv_gaps).
  void derivations() {
    const size_t np = preds_.size();
    certs_.derivations.assign(np, {});
    certs_.deriv_gaps.assign(np, "");
    for (size_t i = 0; i < np; ++i)
      dpid_.emplace(std::make_pair(preds_[i].name, preds_[i].row), Id(i));
    for (const auto &d : cs_.records().derivations) {
      const Id i = dpid(d.pred, d.row);
      if (i != kNone) drec_[i] = &d;
    }
    for (size_t t = 0; t < P_.tables.size(); ++t)
      for (size_t g = 0; g < P_.tables[t].groups.size(); ++g) {
        const auto &ms = P_.tables[t].groups[g].members;
        for (size_t m = 0; m < ms.size(); ++m)
          dmembers_[{ms[m][0], ms[m][1]}].push_back({t, g, m});
      }
    for (size_t v = 0; v < P_.values.size(); ++v) {
      const auto &x = P_.values[v];
      const bool leaf = x.kind == ir::Value::kInput ||
                        (x.kind == ir::Value::kOpaque && x.args.empty());
      if (leaf && !x.bound.empty()) ddeclared_[Id(v)] = ddeclared_.size();
    }
    for (size_t i = 0; i < np; ++i) {
      const ir::Predicate &q = P_.predicates[i];
      auto &gap = certs_.deriv_gaps[i];
      if (!q.unmodeled.empty()) {
        gap = "the predicate is unmodeled";
        continue;
      }
      if (auto it = drec_.find(Id(i)); it != drec_.end()) {
        if (!it->second->gap.empty()) {
          gap = it->second->gap;
          continue;
        }
        try {
          certs_.derivations[i] = resolve_derivation(Id(i), 0);
        } catch (const std::exception &e) {
          gap = std::string("resolution: ") + e.what();
        }
        continue;
      }
      if (q.target.kind == ir::Target::kRealized) {
        // A predicate read through spectrally realized convolutions: each
        // convolution's source equals its reading once its products
        // predicate holds (linop spectral), so the realized predicate's
        // equation is the predicate's (an integer mod_0 needs its sides'
        // intervals too, which the conv lowering does not record).
        // A mod_0's own derivation (its lowering's: realized, the sides'
        // intervals, lift) with the realized step replaced by this chain.
        std::vector<ir::DStep> rest;
        if (q.body != ir::Predicate::kEqual) {
          auto it = drec_.find(Id(i));
          if (it == drec_.end() || !it->second->gap.empty()) {
            gap = it == drec_.end() ? "a spectrally realized mod_0 without its lowering's derivation"
                                    : it->second->gap;
            continue;
          }
          try {
            rest = resolve_derivation(Id(i), 0);
          } catch (const std::exception &e) {
            gap = std::string("resolution: ") + e.what();
            continue;
          }
          if (rest.empty() || rest[0].rule != ir::DStep::kRealized || rest[0].id != Id(i)) {
            gap = "a spectrally realized mod_0 whose derivation does not start at its field equation";
            continue;
          }
        }
        std::vector<ir::DStep> st;
        std::vector<size_t> ps;
        for (size_t c = 0; c < P_.convs.size(); ++c) {
          const Id prod = P_.convs[c].products;
          if (prod >= np || P_.predicates[prod].owner != Id(i)) continue;
          ir::DStep h, l;
          h.rule = ir::DStep::kHyp;
          h.id = prod;
          st.push_back(h);
          l.rule = ir::DStep::kLinop;
          l.src_arg = c;
          l.premises = {st.size() - 1};
          st.push_back(l);
          ps.push_back(st.size() - 1);
        }
        ir::DStep r, lin, c;
        r.rule = ir::DStep::kRealized;
        r.id = q.target.id;
        st.push_back(r);
        ps.push_back(st.size() - 1);
        lin.rule = ir::DStep::kLinear;
        lin.premises = ps;
        auto prog = [&](Id node) {
          ir::DExpr x;
          x.kind = ir::DExpr::kProgram;
          x.id = node;
          certs_.exprs.push_back(x);
          return Id(certs_.exprs.size() - 1);
        };
        lin.exprs = {prog(q.lhs), prog(q.rhs)};
        st.push_back(lin);
        if (q.body == ir::Predicate::kEqual) {
          c.rule = ir::DStep::kConclude;
          c.premises = {st.size() - 1};
          st.push_back(c);
        } else {
          // The rest, its step 0 now the chain's last.
          const size_t shift = st.size() - 1;
          for (size_t j = 1; j < rest.size(); ++j) {
            ir::DStep x = rest[j];
            for (size_t &pp : x.premises) pp += shift;
            st.push_back(std::move(x));
          }
        }
        certs_.derivations[i] = std::move(st);
        continue;
      }
      if (q.body == ir::Predicate::kEqual && q.target.kind != ir::Target::kRealized) {
        ir::DStep r, c;
        r.rule = ir::DStep::kRealized;
        r.id = Id(i);
        c.rule = ir::DStep::kConclude;
        c.premises = {0};
        certs_.derivations[i] = {r, c};
        continue;
      }
      gap = "its lowering records no derivation";
    }
    // Ranks: above every cited predicate (cycles fail the check), a cross
    // equal above every other predicate.
    certs_.deriv_ranks.assign(np, 0);
    {
      std::vector<int> state(np, 0);
      std::function<size_t(size_t)> rank = [&](size_t i) -> size_t {
        if (state[i] == 2) return certs_.deriv_ranks[i];
        if (state[i] == 1) return 0;
        state[i] = 1;
        size_t r = 0;
        for (const auto &st : certs_.derivations[i]) {
          if (st.rule == ir::DStep::kHyp && st.id < np) r = std::max(r, rank(st.id) + 1);
          if (st.rule == ir::DStep::kMac || st.rule == ir::DStep::kGroupedMod) {
            for (Id t : st.tails)
              if (t < np) r = std::max(r, rank(t) + 1);
            if (st.h < np) r = std::max(r, rank(st.h) + 1);
          }
        }
        state[i] = 2;
        return certs_.deriv_ranks[i] = r;
      };
      size_t top = 0;
      for (size_t i = 0; i < np; ++i)
        if (P_.predicates[i].body != ir::Predicate::kCross) top = std::max(top, rank(i));
      for (size_t i = 0; i < np; ++i)
        if (P_.predicates[i].body == ir::Predicate::kCross)
          certs_.deriv_ranks[i] = std::max(rank(i), top + 1);
    }
    DerivChecker check(P_, certs_);
    // Steps no later step reads (a source the walk did not consume) are
    // dropped, and the premises renumbered.
    auto prune = [&](std::vector<ir::DStep> &d) {
      if (d.empty()) return;
      std::vector<bool> used(d.size(), false);
      used.back() = true;
      for (size_t j = d.size(); j-- > 0;)
        if (used[j])
          for (size_t q : d[j].premises) used.at(q) = true;
      std::vector<size_t> at(d.size(), SIZE_MAX);
      std::vector<ir::DStep> out;
      for (size_t j = 0; j < d.size(); ++j) {
        if (!used[j]) continue;
        ir::DStep x = d[j];
        for (size_t &q : x.premises) q = at[q];
        at[j] = out.size();
        out.push_back(std::move(x));
      }
      d = std::move(out);
    };
    auto refuse = [&](size_t i, const std::string &e) {
      certs_.deriv_gaps[i] = "check: " + e;
      if (certs_.deriv_refused.size() < np) certs_.deriv_refused.resize(np);
      certs_.deriv_refused[i] = std::move(certs_.derivations[i]);
      certs_.derivations[i].clear();
    };
    for (size_t i = 0; i < np; ++i) {
      if (certs_.derivations[i].empty()) continue;
      std::string e = check.check(i);
      if (e.empty()) {
        // Pruned of unread steps, checked again (the walk's premise order
        // is already fixed).
        prune(certs_.derivations[i]);
        e = check.check(i);
      }
      if (!e.empty()) refuse(i, e);
    }
    // A mod_0 cites its sides' intervals as shared facts (the honest checks
    // read them): the steps each lift premise rests on, copied into an
    // entry, and `fact` of both entries first in the derivation.
    bool bumped = false;
    for (size_t i = 0; i < np; ++i) {
      const ir::Predicate &q = P_.predicates[i];
      auto &d = certs_.derivations[i];
      if (d.empty() || q.body != ir::Predicate::kMod || q.q != "0") continue;
      size_t lift = SIZE_MAX;
      for (size_t j = 0; j < d.size(); ++j)
        if (d[j].rule == ir::DStep::kLift) lift = j;
      if (lift == SIZE_MAX || d[lift].premises.size() != 3) {
        refuse(i, "a mod_0 without its sides' lift");
        continue;
      }
      std::vector<size_t> entries;
      bool ok = true;
      for (size_t side = 1; side <= 2 && ok; ++side) {
        const size_t top = d[lift].premises[side];
        // The steps TOP rests on, in order.
        std::vector<bool> need(d.size(), false);
        need[top] = true;
        for (size_t j = top + 1; j-- > 0;)
          if (need[j])
            for (size_t pp : d[j].premises) need[pp] = true;
        std::vector<size_t> at(d.size(), SIZE_MAX);
        ir::SharedFact e;
        e.dom = q.domain;
        size_t rk = 0;
        for (size_t j = 0; j <= top; ++j) {
          if (!need[j]) continue;
          ir::DStep x = d[j];
          for (size_t &pp : x.premises) pp = at[pp];
          if (x.rule == ir::DStep::kHyp) rk = std::max(rk, certs_.deriv_ranks.at(x.id) + 1);
          at[j] = e.steps.size();
          e.steps.push_back(std::move(x));
        }
        const ir::DStep &t = d[top];
        if (t.rule != ir::DStep::kIvlExpr || t.ints.size() != 2) {
          ok = false;
          break;
        }
        e.expr = t.exprs.at(0);
        e.lo = t.ints[0];
        e.hi = t.ints[1];
        e.rank = rk;
        entries.push_back(certs_.shared.size());
        certs_.shared.push_back(std::move(e));
      }
      if (!ok) {
        refuse(i, "a mod_0 whose side's interval is no ivlExpr");
        continue;
      }
      // fact k, fact k' first; the other steps' premises shift by two.
      for (auto &x : d)
        for (size_t &pp : x.premises) pp += 2;
      ir::DStep f0, f1;
      f0.rule = f1.rule = ir::DStep::kFact;
      f0.id = Id(entries[0]);
      f1.id = Id(entries[1]);
      d.insert(d.begin(), {f0, f1});
      size_t need_rank = 0;
      for (size_t k : entries) need_rank = std::max(need_rank, certs_.shared[k].rank + 1);
      certs_.deriv_ranks[i] = std::max(certs_.deriv_ranks[i], need_rank);
      bumped = true;
    }
    if (bumped) {
      // The cross equals above every other predicate again.
      size_t top = 0;
      for (size_t i = 0; i < np; ++i)
        if (P_.predicates[i].body != ir::Predicate::kCross)
          top = std::max(top, certs_.deriv_ranks[i]);
      for (size_t i = 0; i < np; ++i)
        if (P_.predicates[i].body == ir::Predicate::kCross)
          certs_.deriv_ranks[i] = std::max(certs_.deriv_ranks[i], top + 1);
    }
    for (size_t k = 0; k < certs_.shared.size(); ++k) {
      size_t owner = 0;
      for (size_t i = 0; i < np; ++i)
        for (const auto &x : certs_.derivations[i])
          if (x.rule == ir::DStep::kFact && x.id == k) owner = i;
      const std::string e = check.check_entry(k, owner);
      if (!e.empty()) refuse(owner, "shared fact " + std::to_string(k) + ": " + e);
    }
    for (size_t i = 0; i < np; ++i) {
      bool cites = false;
      for (const auto &x : certs_.derivations[i]) cites = cites || x.rule == ir::DStep::kFact;
      if (!cites) continue;
      const std::string e = check.check(i);
      if (!e.empty()) refuse(i, e);
    }
  }
  // The predicate NAME (a row when ROW, else the predicate, else the row).
  Id dpid(const std::string &name, bool row) const {
    auto it = dpid_.find({name, row});
    if (it == dpid_.end()) it = dpid_.find({name, !row});
    return it == dpid_.end() ? kNone : it->second;
  }
  [[noreturn]] static void dfail(const std::string &s) {
    throw std::runtime_error(s);
  }
  // The recorded derivation of predicate PID, resolved; DEPTH bounds the
  // splices.
  std::vector<ir::DStep> resolve_derivation(Id pid, size_t depth = 0) {
    using R = PlanRecords::DerivStep;
    auto it = drec_.find(pid);
    if (it == drec_.end()) dfail("'" + preds_.at(pid).name + "' has no derivation");
    const PlanRecords::Derivation &d = *it->second;
    if (!d.gap.empty()) dfail("'" + d.pred + "': " + d.gap);
    if (depth > 4) dfail("splices nest too deep");
    std::vector<ir::DStep> out;
    std::vector<size_t> at(d.steps.size(), SIZE_MAX);
    auto prem = [&](size_t k) {
      if (k >= at.size() || at[k] == SIZE_MAX) dfail("a premise is not an earlier step");
      return at[k];
    };
    auto dom_of = [&](const std::string &nm) -> Id {
      if (nm.empty()) return kNone;
      for (size_t i = 0; i < cs_.num_domains(); ++i)
        if (cs_.domain(i).name == nm) return Id(i);
      dfail("no domain '" + nm + "'");
    };
    for (size_t k = 0; k < d.steps.size(); ++k) {
      const R &s = d.steps[k];
      const size_t first = out.size();
      const Id in_dom = dom_of(s.in_dom);
      // Every step this record step becomes reads in its domain (a hyp
      // reads none).
      struct Wrap {
        std::vector<ir::DStep> &out;
        size_t first;
        Id dom;
        ~Wrap() {
          for (size_t i = first; i < out.size(); ++i)
            if (out[i].rule != ir::DStep::kHyp) out[i].in_dom = dom;
        }
      } wrap{out, first, in_dom};
      if (s.rule == R::kInline) {
        // The request's range, from its predicate (a lower rank): hyp,
        // holdsIn.
        const Id r = dpid(s.item, false);
        if (r == kNone) dfail("no request '" + s.item + "'");
        ir::DStep h, n;
        h.rule = ir::DStep::kHyp;
        h.id = r;
        out.push_back(h);
        n.rule = ir::DStep::kHoldsIn;
        n.premises = {out.size() - 1};
        out.push_back(n);
        at[k] = out.size() - 1;
        continue;
      }
      if (s.rule == R::kViewIvl) {
        // Each masked part of the view's definition by the interval walk
        // (its constants' entries as premises), then their disjoint sum.
        auto dv = derived_.find(s.node);
        if (dv == derived_.end()) dfail("a view the program does not hold");
        const Id root = P_.exprs.at(P_.nodes.at(dv->second.e).x);
        std::vector<Id> parts;
        for (Id x = root;;) {
          const ir::Expr &n = P_.nodes.at(x);
          if (n.op != ir::Expr::kAdd) {
            parts.push_back(x);
            break;
          }
          parts.push_back(n.b);
          x = n.a;
        }
        std::reverse(parts.begin(), parts.end());
        std::vector<size_t> src;
        for (size_t q : s.premises) src.push_back(prem(q));
        size_t acc = SIZE_MAX;
        for (Id part : parts) {
          std::vector<size_t> ps = src;
          for (Id v : constant_leaves(part)) {
            ir::DStep c;
            c.rule = ir::DStep::kSrc;
            c.id = v;
            c.src = ir::DStep::kConst;
            out.push_back(c);
            ps.push_back(out.size() - 1);
          }
          ir::DStep e;
          e.rule = ir::DStep::kIvlExpr;
          e.premises = std::move(ps);
          ir::DExpr d;
          d.kind = ir::DExpr::kProgram;
          d.id = part;
          certs_.exprs.push_back(d);
          e.exprs = {Id(certs_.exprs.size() - 1)};
          out.push_back(std::move(e));
          if (acc == SIZE_MAX) {
            acc = out.size() - 1;
          } else {
            ir::DStep j;
            j.rule = ir::DStep::kIvlDisjoint;
            j.premises = {acc, out.size() - 1};
            out.push_back(j);
            acc = out.size() - 1;
          }
        }
        at[k] = acc;
        continue;
      }
      ir::DStep x;
      x.rule = drule(s.rule);
      for (size_t q : s.premises) x.premises.push_back(prem(q));
      for (const auto &c : s.coeffs) x.coeffs.push_back(int_str(c));
      for (const auto &e : s.exprs) x.exprs.push_back(dexpr(e, pid));
      for (const auto &c : s.ints) x.ints.push_back(int_str(c));
      switch (s.rule) {
        case R::kRealized:
        case R::kNatBool:
          x.id = dpid(s.item, s.row);
          if (x.id == kNone) dfail("no predicate '" + s.item + "'");
          break;
        case R::kGroupedMod:
          for (const auto &t : s.names) {
            x.tails.push_back(dpid(t, true));
            if (x.tails.back() == kNone) dfail("no group row '" + t + "'");
          }
          break;
        case R::kMac:
          for (const auto &t : s.names) {
            x.tails.push_back(dpid(t, false));
            if (x.tails.back() == kNone) dfail("no tail '" + t + "'");
          }
          if (!s.h.empty()) {
            x.h = dpid(s.h, false);
            if (x.h == kNone) dfail("no H predicate '" + s.h + "'");
          }
          break;
        case R::kLookup: {
          const Id r = dpid(s.item, false);
          auto m = dmembers_.find({size_t(r), s.a});
          if (r == kNone || m == dmembers_.end())
            dfail("no members of needle " + std::to_string(s.a) + " of '" + s.item + "'");
          x.members = m->second;
          break;
        }
        case R::kSrc: {
          auto v = id_of_.find(s.node);
          if (v == id_of_.end())
            dfail("a source on '" + cs_.nodes().at(s.node).name +
                  "', which the program does not export");
          x.id = Id(v->second);
          using K = PlanRecords::DerivIvlSrc;
          switch (s.src.kind) {
            case K::kConst: x.src = ir::DStep::kConst; break;
            case K::kDeclared: {
              x.src = ir::DStep::kDeclared;
              auto e = ddeclared_.find(x.id);
              if (e == ddeclared_.end()) dfail("a value without a declared range");
              x.src_arg = e->second;
              break;
            }
            case K::kNat: x.src = ir::DStep::kNat; break;
            case K::kShift: x.src = ir::DStep::kShift; break;
            case K::kQuadRoot:
            case K::kRootSet:
              x.src = s.src.kind == K::kQuadRoot ? ir::DStep::kQuadRoot
                                                 : ir::DStep::kRootSet;
              for (const auto &q : s.names) {
                x.tails.push_back(dpid(q, false));
                if (x.tails.back() == kNone) dfail("no root predicate '" + q + "'");
              }
              break;
            case K::kPrime: {
              // A statement value with a declared range (a member check's
              // bound, which the export reads) takes that range.
              auto e = ddeclared_.find(x.id);
              if (e != ddeclared_.end()) {
                x.src = ir::DStep::kDeclared;
                x.src_arg = e->second;
              } else {
                x.src = ir::DStep::kPrime;
              }
              break;
            }
            case K::kOpaqueBit: {
              // A committed Bit's range is its Boolean check (natBool),
              // which the plan placed as the value's type source; an
              // opaque public Bit is opaqueBit.
              const ir::Value &v = P_.values.at(x.id);
              if (v.type_source == ir::Value::TypeSource::kPred) {
                ir::DStep b;
                b.rule = ir::DStep::kNatBool;
                b.id = v.type_pred;
                out.push_back(b);
                x.src = ir::DStep::kNat;
                x.premises = {out.size() - 1};
              } else {
                x.src = ir::DStep::kOpaqueBit;
              }
              break;
            }
          }
          break;
        }
        default:
          break;
      }
      out.push_back(std::move(x));
      at[k] = out.size() - 1;
    }
    return out;
  }
  // The constant values whose leaves expression X reads, in pre-order,
  // once each.
  std::vector<Id> constant_leaves(Id x) const {
    std::vector<Id> out, st{x};
    while (!st.empty()) {
      const Id y = st.back();
      st.pop_back();
      const ir::Expr &n = P_.nodes.at(y);
      if (n.op == ir::Expr::kLeaf) {
        const Id v = Id(n.x);
        if (P_.values.at(v).kind == ir::Value::kConstant &&
            std::find(out.begin(), out.end(), v) == out.end())
          out.push_back(v);
        continue;
      }
      if (n.op == ir::Expr::kRef) continue;
      for (Id k : {n.c, n.b, n.a})
        if (k != kNone) st.push_back(k);
      for (auto it = n.args.rbegin(); it != n.args.rend(); ++it) st.push_back(*it);
    }
    return out;
  }
  static ir::DStep::Rule drule(PlanRecords::DerivStep::Rule r) {
    using R = PlanRecords::DerivStep;
    using D = ir::DStep;
    switch (r) {
      case R::kRealized: return D::kRealized;
      case R::kSubst: return D::kSubst;
      case R::kLinear: return D::kLinear;
      case R::kLookup: return D::kLookup;
      case R::kRangeNat: return D::kRangeNat;
      case R::kIvlNat: return D::kIvlNat;
      case R::kSrc: return D::kSrc;
      case R::kIvlExpr: return D::kIvlExpr;
      case R::kIvlSolve: return D::kIvlSolve;
      case R::kIvlMeet: return D::kIvlMeet;
      case R::kNatIvl: return D::kNatIvl;
      case R::kNatComp: return D::kNatComp;
      case R::kNatBool: return D::kNatBool;
      case R::kNatLin: return D::kNatLin;
      case R::kLiftConst: return D::kLiftConst;
      case R::kFieldDvd: return D::kFieldDvd;
      case R::kGroupedMod: return D::kGroupedMod;
      case R::kTransport: return D::kTransport;
      case R::kLift: return D::kLift;
      case R::kDigits: return D::kDigits;
      case R::kCongr: return D::kCongr;
      case R::kMac: return D::kMac;
      case R::kLinop: return D::kLinop;
      case R::kConclude: return D::kConclude;
      case R::kInline:
      case R::kViewIvl:
        break;
    }
    dfail("a rule with no Lean step");
  }
  // Expression E of a step of predicate PID's derivation, as an entry of
  // Certificates::exprs.
  Id dexpr(const PlanRecords::DerivExpr &e, Id pid) {
    using K = PlanRecords::DerivExpr;
    ir::DExpr x;
    switch (e.kind) {
      case K::kSide: {
        const Id q = dpid(e.item, e.row);
        if (q == kNone) dfail("no predicate '" + e.item + "'");
        x.kind = ir::DExpr::kProgram;
        x.id = e.a == 0 ? P_.predicates[q].lhs : P_.predicates[q].rhs;
        if (x.id == kNone) dfail("'" + e.item + "' has no such side");
        break;
      }
      case K::kLeaf: {
        if (e.node < cls_.size() && cls_[e.node] == kValue) {
          x.kind = ir::DExpr::kLeaf;
          x.id = Id(id_of_.at(e.node));
        } else if (auto d = derived_.find(e.node); d != derived_.end()) {
          x.kind = ir::DExpr::kProgram;
          x.id = d->second.e;
        } else {
          dfail("the leaf of '" + cs_.nodes().at(e.node).name +
                "', which the program does not read");
        }
        break;
      }
      case K::kDef: {
        x.kind = ir::DExpr::kProgram;
        if (auto d = derived_.find(e.node); d != derived_.end()) {
          x.id = P_.exprs.at(P_.nodes.at(d->second.e).x);
        } else if (auto v = vals_.find(e.node);
                   v != vals_.end() && v->second.kind == "bound") {
          x.id = v->second.expr;
        } else {
          dfail("the definition of '" + cs_.nodes().at(e.node).name +
                "', which the program does not hold");
        }
        break;
      }
      case K::kAdd:
      case K::kSub:
      case K::kMul:
        x.kind = e.kind == K::kAdd   ? ir::DExpr::kAdd
                 : e.kind == K::kSub ? ir::DExpr::kSub
                                     : ir::DExpr::kMul;
        x.a = dexpr(e.args.at(0), pid);
        x.b = dexpr(e.args.at(1), pid);
        break;
      case K::kApplyIn: {
        const Id q = dpid(e.item, e.row);
        if (q == kNone) dfail("no predicate '" + e.item + "'");
        std::vector<Id> st{P_.predicates[q].lhs};
        Id found = kNone;
        while (!st.empty() && found == kNone) {
          const Id y = st.back();
          st.pop_back();
          const ir::Expr &n = P_.nodes.at(y);
          if (n.op == ir::Expr::kApply) {
            found = y;
            break;
          }
          if (n.op == ir::Expr::kRef) continue;
          for (Id k : {n.c, n.b, n.a})
            if (k != kNone) st.push_back(k);
        }
        if (found == kNone) dfail("'" + e.item + "' applies no operator");
        x.kind = ir::DExpr::kProgram;
        x.id = found;
        break;
      }
      case K::kScale: {
        x.kind = ir::DExpr::kScale;
        x.a = dexpr(e.args.at(0), pid);
        const SignedInt p = derivation_check_internal::parse_int(
            P_.fields.at(P_.domains.at(P_.predicates.at(pid).domain).field).characteristic);
        const SignedInt c = derivation_check_internal::modp(e.c, p);
        x.c = int_str(c);
        break;
      }
    }
    certs_.exprs.push_back(std::move(x));
    return Id(certs_.exprs.size() - 1);
  }

  std::string dom_field_name(size_t d) const {
    return bare_place(d) ? bare_field_name(d) : cs_.domain(d).field_name();
  }

  // The value roles: a value a core realization's lowering declared is a
  // realization value, owned by the MAC's cross-field equal (its key,
  // powers, tag, message, blind, target bits and joined sides), a table
  // group's first member (its histograms; the domain's alpha, the first
  // group's), or the predicate whose name is the longest dotted prefix of
  // the value's (a range request's digits, an assert_mod's quotient). Every
  // other value is a source value.
  void value_roles() {
    const auto &N = cs_.nodes();
    std::map<size_t, std::string> fixed;
    for (const auto &m : cs_.records().macs) {
      const std::string eq = m.name + ".equal";
      for (size_t id : {m.tag, m.key, m.powers, m.blind, m.xh, m.xa})
        if (id != SIZE_MAX) fixed[id] = eq;
      for (size_t id = 0; id < N.size(); ++id)
        if ((N[id].kind == Kind::kPublicMessage && N[id].deps.at(0) == m.tag) ||
            N[id].name.rfind(m.name + ".target_bits", 0) == 0)
          fixed[id] = eq;
    }
    std::map<size_t, bool> alpha_done;
    for (const auto &T : tables_)
      for (size_t k = 0; k < T.groups.size(); ++k) {
        if (T.members[k].empty()) continue;
        const std::string first = std::get<0>(T.members[k].front());
        for (size_t id : {T.groups[k].m0, T.groups[k].m1})
          if (id != SIZE_MAX) fixed[id] = first;
        const size_t a = T.groups[k].alpha;
        if (!alpha_done[a]) {
          fixed[a] = first;
          alpha_done[a] = true;
        }
      }
    // assert_in's multiplicities: its first request's. The powers of gamma
    // are a source value (the packed requests read them).
    std::set<size_t> source_values;
    for (const auto &t : cs_.records().in_lookups) {
      if (!t.requests.empty() && vals_.count(t.mult)) {
        fixed[t.mult] = t.requests.front();
        vals_.at(t.mult).owner = t.requests.front();
      }
      if (t.powers != SIZE_MAX) source_values.insert(t.powers);
    }
    for (auto &[id, v] : vals_) {
      const std::string pass = core_pass(id);
      if (pass.empty() || source_values.count(id)) continue;
      if (auto f = fixed.find(id); f != fixed.end()) {
        v.owner = f->second;
      } else {
        v.owner = owner_of(v.name, true);
      }
      if (v.owner.empty() || !pred_id_.count(v.owner))
        gap("the realization value '" + v.name + "' (declared by the "
            "lowering '" + pass + "') has no owner");
    }
  }

  // The role of challenge node C (the Lean's Challenge.role): a source
  // challenge; a core realization's (Lowering::realization), owned by the
  // domain's first member in (alpha:<D> when only range lookups read it)
  // or the MAC's cross-field equal (its key); or unmodeled (alpha:<D> when
  // an assert_in lookup reads it, and assert_in's gamma).
  void challenge_role(size_t c, ir::Challenge &ch) {
    const Node &n = cs_.nodes()[c];
    using R = ir::Challenge::Role;
    if (!n.realization) {
      ch.role = R::kSource;
      return;
    }
    for (const auto &m : cs_.records().macs)
      if (m.key == c) {
        ch.role = R::kRealization;
        ch.owner = pid(m.name + ".equal");
        return;
      }
    // assert_in's gamma: the packed in predicates are a randomized test of
    // the source program, which gamma's challenge belongs to.
    for (const auto &t : cs_.records().in_lookups)
      if (t.gamma == c) {
        ch.role = R::kSource;
        return;
      }
    if (n.name.rfind("in.gamma:", 0) == 0) {
      ch.role = R::kUnmodeled;
      return;
    }
    if (n.name.rfind("alpha:", 0) == 0) {
      // The first member of the domain's first table group (a range
      // table's, or an assert_in table's).
      for (const auto &T : tables_)
        for (size_t k = 0; k < T.groups.size(); ++k)
          if (T.groups[k].alpha == c && !T.members[k].empty()) {
            ch.role = R::kRealization;
            ch.owner = pid(std::get<0>(T.members[k].front()));
            return;
          }
    }
    gap("the realization challenge '" + n.name + "' has no owner");
  }

  // The structured realization circuit NAME (the Lean's RealCircuit): a
  // table group's LogUp sum, or a MAC's H part stated by the compiler's own
  // circuit, or unmodeled (an assert_in lookup), numbered in order of
  // appearance.
  ir::RealRef real_circuit(const std::string &name) {
    ir::RealRef r;
    r.name = name;
    if (auto it = logup_of_.find(name); it != logup_of_.end()) {
      r.kind = ir::RealRef::kLogup;
      r.a = Id(it->second.first);
      r.b = Id(it->second.second);
      return r;
    }
    for (const auto &m : cs_.records().macs)
      if (!m.h_circuit.empty() && m.h_circuit == name) {
        r.kind = ir::RealRef::kMacH;
        r.a = pid(m.name + ".equal");
        return r;
      }
    r.kind = ir::RealRef::kUnmodeled;
    r.a = Id(unmodeled_index(name));
    return r;
  }
  size_t unmodeled_index(const std::string &name) {
    auto it = unmodeled_.find(name);
    if (it == unmodeled_.end())
      it = unmodeled_.emplace(name, unmodeled_.size()).first;
    return it->second;
  }
  // The structured public input NAME only a realization circuit reads (the
  // Lean's RealPub): a table's weights.
  ir::RealRef real_pub(const std::string &name) {
    ir::RealRef r;
    r.name = name;
    auto it = weights_of_.find(name);
    if (it == weights_of_.end()) {
      r.kind = ir::RealRef::kUnmodeled;
      r.a = Id(unmodeled_index(name));
      return r;
    }
    r.kind = ir::RealRef::kWeights;
    r.a = Id(it->second);
    return r;
  }

  // The bound tmax of challenge NAME drawn outside [0, tmax) (the Lean's
  // fieldMinusTables), the union of the domain's range tables.
  std::string excluded_range(const std::string &name) {
    const PlanRecords::Excluded *x = nullptr;
    for (const auto &e : cs_.records().excluded)
      if (e.challenge == name) x = &e;
    if (x == nullptr || x->range == 0) {
      gap("challenge '" + name + "' is drawn outside a set the plan records "
          "do not name");
      return "0";
    }
    return bound_str(x->range);
  }

  // The packing-tree node of late value X's pad, or the field's name.
  std::string pad_space(size_t x) const {
    const Node &n = cs_.nodes().at(x);
    // A late value of a field no domain commits: its pad is uniform in the
    // field.
    if (n.domain < 0) return bare_field_name(size_t(domain_of(x)));
    const size_t di = size_t(n.domain);
    const DomainBase<S> &dm = cs_.domain(di);
    const DomainPlan &p = plan_of(di);
    const Space sp = cs_.message_space(x);
    const uint16_t dg = cs_.message_degree(x);
    return S::dispatch(dm.field_id, [&](auto tag) {
      using F = typename decltype(tag)::type;
      const size_t D = sp == Space::kField    ? p.field_degree
                       : sp == Space::kPrime ? 1
                                             : subfield_degree<F>(dg);
      const auto *fd = dynamic_cast<const Domain<F> *>(&dm);
      return tree_node(*fd, D);
    });
  }
  template <class F>
  static size_t designated_degree_of() {
    return domain_subfield<F>::kDegree;
  }

  enum Cls { kValue, kDerivedNode, kPadNode, kNoClass };
  const CS &cs_;
  ir::Program P_;
  ir::Certificates certs_;
  // The derivations' resolution: whether to build them (build_ir with
  // certificates), predicate ids by (name, row), each predicate's record,
  // LogUp members by (pred, needle), declared ranges' entries by value.
  bool want_derivations_ = false;
  std::map<std::pair<std::string, bool>, Id> dpid_;
  std::map<Id, const PlanRecords::Derivation *> drec_;
  std::map<std::pair<size_t, size_t>, std::vector<std::array<size_t, 3>>> dmembers_;
  std::map<Id, size_t> ddeclared_;
  // Each bound value's node -> the in predicate whose digits bind it.
  std::map<size_t, size_t> bound_rec_;
  // The fields no domain commits (field index, field object), each a place
  // past the domains; the system.
  std::vector<std::pair<size_t, const void *>> bare_;
  const SystemCore *sys_ = nullptr;
  std::vector<Cls> cls_;
  std::map<size_t, ValueRec> vals_;
  std::vector<ValueRec> const_recs_;
  std::map<std::pair<size_t, std::vector<std::string>>, size_t> consts_;
  std::map<std::vector<size_t>, Id> idx_;
  std::map<size_t, Ex> derived_, pub_ex_;
  std::map<const void *, size_t> refs_;
  std::map<const void *, Ex> memo_;
  // The spectrally realized convolutions by source conv node (SpecConv);
  // the realized reading's conversions (realized_).
  std::map<const void *, SpecConv> spec_;
  std::map<const void *, Ex> memo_r_;
  std::map<const void *, bool> has_spec_;
  bool realized_ = false;
  std::map<size_t, std::set<ProgramRead>> late_reads_;
  std::map<size_t, size_t> late_of_pad_, pad_of_late_, chal_of_, field_of_domain_;
  std::map<size_t, size_t> id_of_;
  std::vector<size_t> chals_;
  std::map<size_t, const PlanRecords::Mac *> powers_of_;
  std::map<size_t, const PlanRecords::InLookup *> in_powers_;
  std::vector<PredRec> preds_;
  std::map<size_t, size_t> mac_place_;
  std::map<std::string, size_t> pred_id_;
  std::set<std::string> mod_names_;
  std::set<size_t> public_view_;
  // The source values bound to their digits (kind bound).
  std::set<size_t> bound_;
  // Each domain predicate's (domain, index) -> its id.
  std::map<std::pair<size_t, size_t>, size_t> dom_pred_;
  // Each range request's (n, N, m), and each assert_mod's quotient
  // requests by name.
  std::map<std::string, std::tuple<Bound, Bound, Bound>> req_bounds_;
  std::map<std::string, std::vector<std::string>> mod_ranges_;
  std::map<size_t, std::vector<std::pair<size_t, size_t>>> public_wiring_;
  std::vector<TableRec> tables_;
  std::vector<std::tuple<DomainPlan::Batch, size_t, bool>> batches_;
  std::map<std::pair<size_t, std::string>, size_t> batch_id_;
  std::vector<std::pair<size_t, DomainPlan>> circuits_;
  std::map<size_t, size_t> circuit_id_;
  std::vector<std::pair<std::string, size_t>> real_circuits_;
  // The LogUp circuits by name -> (table, group); the weights by name ->
  // table.
  std::map<std::string, std::pair<size_t, size_t>> logup_of_;
  std::map<std::string, size_t> weights_of_;
  // The realization circuits and inputs the program does not model.
  std::map<std::string, size_t> unmodeled_;
  mutable std::map<size_t, DomainPlan> plans_;
};

}  // namespace program_builder_internal

// The realized program of CS (realized_program.h). Throws
// plan_export_internal's ExportError when an element has no description.
template <class S>
ir::Program build_ir(const BasicCompiledSystem<S> &cs) {
  return program_builder_internal::ProgramBuilder<S>(cs).run();
}
// The same with the export's certificates (ir::Certificates) in CERTS.
template <class S>
ir::Program build_ir(const BasicCompiledSystem<S> &cs, ir::Certificates &certs) {
  program_builder_internal::ProgramBuilder<S> b(cs);
  b.want_derivations();
  ir::Program p = b.run();
  certs = b.take_certificates();
  return p;
}

}  // namespace proofs::gordiehowe::compiler

#endif  // PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_COMPILER_PROGRAM_BUILDER_H_
