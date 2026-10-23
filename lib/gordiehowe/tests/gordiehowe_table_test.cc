// Copyright 2026 Chad Sharp and Paul Grubbs
// SPDX-License-Identifier: Apache-2.0

// GordieHowe tests: public tables (table.h).
//   - RowMap: the closed-form transposed powers against the definition and
//     against ops::NttTranspose (the digests' expression), and the row dot
//     kernels (ExtCoefTable's, the prescaled dot, field products) against
//     each other;
//   - select over rings of 64 and 100 (padded to 128) members, negacyclic
//     and block maps: honest proofs, a wrong index, a record off the table;
//   - lookup over a small public table: honest, a record off the table, a
//     wrong multiplicity; with a range check in the same domain, one alpha;
//   - compile errors for misuse.

#include <algorithm>
#include <cstddef>
#include <cstdint>
#include <random>
#include <string>
#include <vector>

#include "gordiehowe/compile_error_testing.h"
#include "algebra/fp24.h"
#include "algebra/fp24_6.h"
#include "algebra/fp_goldilocks4.h"
#include "algebra/reed_solomon_fp.h"
#include "gordiehowe/lib/ring_core.h"
#include "gf2k/gf2_256.h"
#include "gf2k/lch14_reed_solomon.h"
#include "gordiehowe/compiler/plan_program.h"
#include "gordiehowe/instances.h"
#include "gordiehowe/system.h"
#include "gordiehowe/lib/permutation.h"
#include "gordiehowe/lib/table.h"
#include "gtest/gtest.h"
#include "random/secure_random_engine.h"

namespace proofs::gordiehowe {
namespace {

using AF = Fp64G4;
using AElt = AF::Elt;
using AV = std::vector<AElt>;
using RSA = BasicFpReedSolomon<AF>;
using HF = GF2_256<>;
using RSH = LCH14ReedSolomonFactory<HF>;
using Sys = ConstraintSystem<SHA384, AF, HF>;
using SysValue = Sys::Value;
using Assignment = Sys::Assignment;
using ProveOptions = Sys::ProveOptions;
using CompiledSystem = Sys::Compiled;

struct Env {
  AF af;
  RSA rsa{af};
  HF hf;
  RSH rsh{hf};
  DomainProfile<AF, RSA::Factory, SHA384> a_profile() const {
    DomainProfile<AF, RSA::Factory, SHA384> p;
    p.f = &af;
    p.rsf = &rsa.factory();
    p.field_name = "Goldilocks^4";
    p.rate = 4;
    p.nreq = 64;
    const RSA *r = &rsa;
    p.block_enc = [r](const Circuit<AF> &, size_t nw, size_t nq) {
      return r->block_enc<SHA384>("gordiehowe", nw, nq, 4, 64);
    };
    p.has_subfield = true;
    p.prime = Space::kSubfield;
    return p;
  }
  DomainProfile<HF, RSH, SHA384> h_profile() const {
    DomainProfile<HF, RSH, SHA384> p;
    p.f = &hf;
    p.rsf = &rsh;
    p.field_name = "GF(2^256)";
    p.rate = 4;
    p.nreq = 64;
    p.has_subfield = true;
    p.prime = Space::kPrime;
    return p;
  }
};
const Env &env() {
  static const Env *e = new Env;
  return *e;
}
const AF &af() { return env().af; }

bool honest(const CompiledSystem &c, const Assignment &st, const Assignment &w) {
  auto prep = c.prepare(st);
  SecureRandomEngine rng;
  return prep.verify(prep.prove(w, rng));
}
// The cheating prover completes its proof under TAMPER and the verifier
// rejects it.
template <class Tamper>
bool verifier_rejects(const CompiledSystem &c, const Assignment &st,
                      const Assignment &w, Tamper tamper) {
  auto prep = c.prepare(st);
  ProveOptions opt;
  opt.tamper = tamper;
  opt.require_satisfied = false;
  SecureRandomEngine rng;
  std::vector<uint8_t> proof;
  try {
    proof = prep.prove(w, rng, opt);
  } catch (const std::runtime_error &e) {
    ADD_FAILURE() << "the cheating prover stopped: " << e.what();
    return false;
  }
  return !prep.verify(proof);
}
// A prover that skips its satisfaction check proves the bad witness W,
// and the verifier rejects the proof.
bool verifier_rejects_witness(const CompiledSystem &c, const Assignment &st,
                              const Assignment &w) {
  auto prep = c.prepare(st);
  ProveOptions opt;
  opt.require_satisfied = false;
  SecureRandomEngine rng;
  std::vector<uint8_t> proof;
  try {
    proof = prep.prove(w, rng, opt);
  } catch (const std::runtime_error &e) {
    ADD_FAILURE() << "the cheating prover stopped: " << e.what();
    return false;
  }
  return !prep.verify(proof);
}
// The honest prover's satisfaction check refuses the witness.
bool prover_refuses(const CompiledSystem &c, const Assignment &st,
                    const Assignment &w) {
  auto prep = c.prepare(st);
  SecureRandomEngine rng;
  try {
    prep.prove(w, rng);
  } catch (const std::runtime_error &) {
    return true;
  }
  return false;
}
std::vector<uint64_t> random_mod(size_t n, uint64_t q, uint64_t seed) {
  std::mt19937_64 g(seed);
  std::vector<uint64_t> v(n);
  for (auto &x : v) x = g() % q;
  return v;
}
template <class F>
std::vector<typename F::Elt> lift(const F &f, const std::vector<uint64_t> &v) {
  std::vector<typename F::Elt> out;
  for (uint64_t x : v) out.push_back(f.of_scalar(x));
  return out;
}
AV bits_of(size_t x, size_t k) {
  AV out;
  for (size_t b = 0; b < k; ++b) out.push_back((x >> b) & 1 ? af().one() : af().zero());
  return out;
}
AElt psi_of(size_t n) { return *ops::FieldNtt<AF>::root(af(), 2 * n); }

// ------------------------------------------------------------ row maps --

TEST(GordieHoweTable, TransposedPowersMatchTheDefinition) {
  const AF &f = af();
  const size_t n = 16;
  const auto map = lib::table::RowMap<AF>::blocks(
      {{lib::table::RowMap<AF>::negacyclic(f, n, psi_of(n)), 2},
       {lib::table::RowMap<AF>::identity(3), 1}});
  ASSERT_EQ(map.width(), 2 * n + 3);
  EXPECT_EQ(map.max_leaf(), n);
  EXPECT_EQ(map.multipliers(), 2u);
  SecureRandomEngine rng;
  const AElt gamma = rng.elt(f);
  const AV row = lift(f, random_mod(map.width(), 12289, 1));
  // digest(M(row)) by its definition against <row, G>.
  const AV rec = map.apply(f, row);
  AElt d = f.zero();
  for (const auto &l : map.leaves()) {
    for (size_t k = 0; k < l.n; ++k) {
      AElt p = f.one();
      for (size_t e = 0; e < l.offset + lib::table::RowMap<AF>::perm(l, k); ++e)
        p = f.mulf(p, gamma);
      f.add(d, f.mulf(rec[l.offset + k], p));
    }
  }
  const AV G = map.transposed(f, gamma);
  AElt e = f.zero();
  for (size_t i = 0; i < row.size(); ++i) f.add(e, f.mulf(row[i], G[i]));
  EXPECT_EQ(d, e);
  // The record agrees with the field's NegacyclicNtt (ntt.h's order).
  const ops::NegacyclicNtt<AF> ntt(f, n, psi_of(n));
  AV a(row.begin(), row.begin() + n);
  ntt.forward(a);
  for (size_t k = 0; k < n; ++k) EXPECT_EQ(a[k], rec[k]);
  // At a pole (gamma omega^i = 1) the closed form takes the limit.
  const AElt omega = f.mulf(psi_of(n), psi_of(n));
  AElt pole = f.one();
  for (size_t k = 0; k < 3; ++k) pole = f.mulf(pole, omega);
  const AElt gp = f.invertf(pole);
  const auto m1 = lib::table::RowMap<AF>::negacyclic(f, n, psi_of(n));
  const AV G1 = m1.transposed(f, gp);
  const AV r1(row.begin(), row.begin() + n);
  const AV c1 = m1.apply(f, r1);
  AElt d1 = f.zero(), e1 = f.zero(), p = f.one();
  std::vector<AElt> pw(n);
  for (size_t k = 0; k < n; ++k) {
    pw[k] = p;
    p = f.mulf(p, gp);
  }
  for (size_t k = 0; k < n; ++k) {
    f.add(d1,
          f.mulf(c1[k], pw[lib::table::RowMap<AF>::perm(m1.leaves()[0], k)]));
    f.add(e1, f.mulf(r1[k], G1[k]));
  }
  EXPECT_EQ(d1, e1);
  // The digests' expression: V^T (gamma^m)_m, by NttTranspose, equals the
  // closed form, at a pole too; and its transpose is the forward natural
  // transform.
  for (const AElt &x : {gamma, gp}) {
    std::vector<AElt> p(n), vt(n);
    AElt q = f.one();
    for (size_t k = 0; k < n; ++k) {
      p[k] = q;
      q = f.mulf(q, x);
    }
    const ops::NttTransposeOperator<AF> op(f, n, psi_of(n));
    op.apply(p.data(), vt.data());
    EXPECT_EQ(vt, m1.transposed(f, x));
    const AV a(row.begin(), row.begin() + n);
    AV fwd(n);
    op.transpose_apply(a.data(), fwd.data());
    const auto nat = lib::table::RowMap<AF>::negacyclic(
        f, n, psi_of(n), ops::NttOrder::kNatural);
    EXPECT_EQ(fwd, nat.apply(f, a));
  }
}

template <class F>
void kernels_agree(const F &f, uint64_t q) {
  const size_t R = 7, n = 256;
  const auto map = lib::table::RowMap<F>::negacyclic(f, n);
  SecureRandomEngine rng;
  const auto G = map.transposed(f, rng.elt(f));
  const auto rows = lift(f, random_mod(R * n, q, 2));
  const auto d =
      ops::row_dot_internal::row_dots(f, rows.data(), R, n, G.data());
  for (size_t j = 0; j < R; ++j) {
    typename F::Elt e = f.zero();
    for (size_t i = 0; i < n; ++i) f.add(e, f.mulf(rows[j * n + i], G[i]));
    EXPECT_EQ(d[j], e) << j;
  }
}
TEST(GordieHoweTable, DigestKernelsAgree) {
  static_assert(ops::row_dot_internal::PrescaledDot<AF>::value);
  static_assert(ops::row_dot_internal::ExtCoef<Fp24_6>::value);
  static_assert(!ops::row_dot_internal::ExtCoef<AF>::value);
  kernels_agree(af(), 12289);
  static const Fp24 *b = new Fp24(8380417);
  static const Fp24_6 *f6 = new Fp24_6(*b, Fp24_6::beta_);
  kernels_agree(*f6, 8380417);
  // FIPS 204's map over the ML-DSA field.
  EXPECT_EQ(lib::table::RowMap<Fp24_6>::fips204(*f6).leaves()[0].psi,
            f6->of_scalar(1753));
}

// -------------------------------------------------------------- select --

// A ring of R members, each a polynomial of n coefficients below 12289,
// and a committed spectrum of member SIGNER.
struct RingSys {
  Sys cs{"gh-table-ring"};
  Domain<AF> *A;
  Ref<AF, Subfield<>, Public> ring;
  Ref<AF, Subfield<>, Committed> spec;
  lib::table::PublicTable<AF> table;
  lib::table::Selected<AF> sel;
  size_t R, n;
  AV ring_v;
  RingSys(size_t R_, size_t n_) : R(R_), n(n_) {
    A = &cs.domain(env().a_profile(), "A");
    ring = A->pub(Subfield{}, "ring", Shape{R, n});
    spec = A->priv(Subfield{}, "spec", n);
    table = lib::table::public_table(
        cs, *A, "ring", ring,
        lib::table::RowMap<AF>::negacyclic(af(), n, psi_of(n)));
    sel = lib::table::select_row(cs, table, "signer", spec);
    ring_v = lift(af(), random_mod(R * n, 12289, 7));
  }
  AV member(size_t j) const {
    return table.map.apply(
        af(), AV(ring_v.begin() + long(j * n), ring_v.begin() + long((j + 1) * n)));
  }
  Assignment statement() const {
    Assignment st;
    st.set(ring, ring_v);
    return st;
  }
  Assignment witness(size_t index, size_t member_of) const {
    Assignment w;
    w.set(spec, member(member_of));
    w.set(sel.index, bits_of(index, sel.index.n));
    return w;
  }
};

// The degree recorded for challenge LABEL (the last charge, as the plan
// export reads it).
Bound charge_of(const Sys &cs, const std::string &label) {
  Bound d = 0;
  for (const auto &ch : cs.graph().records.charges)
    if (ch.label == label) d = ch.degree;
  return d;
}

// The degree bound compile() exports for challenge LABEL (computed from
// the predicates for a challenge of the source program).
template <class C>
Bound degree_bound(const C &c, const std::string &label) {
  Bound d = 0;
  for (const auto &ch : c.records().charges)
    if (ch.label == label) d = ch.degree;
  return d;
}

void ring_case(size_t R) {
  RingSys t(R, 32);
  auto c = compile(t.cs);
  EXPECT_EQ(t.table.padded_rows, size_t(1) << t.sel.index.n);
  EXPECT_EQ(c->phase(t.sel.gamma), 1u);
  // select_row compares the record with one row: gamma's charge is the
  // digest's degree, n - 1 for the negacyclic map.
  EXPECT_EQ(charge_of(t.cs, "ring.gamma"), Bound(31));
  // The computed degree bound agrees: one leaf at offset 0, so the
  // powers' degree is the digest's.
  EXPECT_EQ(degree_bound(*c, "ring.gamma"), Bound(31));
  // The powers and digests are expressions over gamma and the rows, lifted
  // into public values both parties evaluate: gamma^k for k < 32 (degree
  // 31), and the digests of the padded rows (degree 31).
  for (const char *nm : {"ring.powers", "ring.digests"}) {
    bool found = false;
    for (const auto &rec : t.cs.graph().records.gadgets)
      if (rec.kind == "public-expression" && rec.name == nm) {
        found = true;
        for (const auto &[k, v] : rec.params)
          if (k == "degree:ring.gamma") EXPECT_EQ(v, 31) << nm;
      }
    EXPECT_TRUE(found) << nm;
  }
  const size_t signer = R - 3;
  EXPECT_TRUE(honest(*c, t.statement(), t.witness(signer, signer)));
  // A wrong index.
  EXPECT_TRUE(prover_refuses(*c, t.statement(), t.witness(signer - 1, signer)));
  EXPECT_TRUE(verifier_rejects_witness(*c, t.statement(),
                                       t.witness(signer ^ 1, signer)));
  // A record off the table: a member's spectrum with one coefficient
  // changed.
  AV off = t.member(signer);
  af().add(off[5], af().one());
  Assignment w = t.witness(signer, signer);
  w.set(t.spec, off);
  EXPECT_TRUE(prover_refuses(*c, t.statement(), w));
  EXPECT_TRUE(verifier_rejects_witness(*c, t.statement(), w));
}
TEST(GordieHoweTable, SelectRingOf64) { ring_case(64); }
TEST(GordieHoweTable, SelectRingOf100Padded) {
  ring_case(100);
  // A padded index names a real member (index 100 + 3 repeats row 3).
  RingSys t(100, 32);
  auto c = compile(t.cs);
  EXPECT_EQ(t.table.padded_rows, 128u);
  EXPECT_TRUE(honest(*c, t.statement(), t.witness(103, 3)));
  EXPECT_TRUE(prover_refuses(*c, t.statement(), t.witness(103, 4)));
}

TEST(GordieHoweTable, SelectBlockRecord) {
  // Record: two polynomials in NTT form and three identity limbs, a
  // concatenation of cells; the digest's powers are factored (16 + 2
  // wires).
  const size_t n = 16, R = 8, W = 2 * n + 3;
  Sys cs("gh-table-blocks");
  auto &A = cs.domain(env().a_profile(), "A");
  auto rows = A.pub(Subfield{}, "rows", Shape{R, W});
  auto p = A.priv(Subfield{}, "polys", 2 * n);
  auto l = A.priv(Subfield{}, "limbs", 3);
  auto map = lib::table::RowMap<AF>::blocks(
      {{lib::table::RowMap<AF>::negacyclic(af(), n, psi_of(n)), 2},
       {lib::table::RowMap<AF>::identity(3), 1}});
  const auto table = lib::table::public_table(cs, A, "t", rows, map);
  auto sel = lib::table::select_row(cs, table, "pick", p.concat(l));
  EXPECT_EQ(sel.powers.size(), n + 2);
  auto c = compile(cs);
  // The declared charge is the digest's exact degree, 32 + 2. The computed
  // degree bound follows the challenge degrees coordinate by coordinate: the
  // leaves read t.powers = (gamma^0, ..., gamma^15, gamma^16, gamma^32) through
  // views, each coordinate of its own degree, so the limbs' leaf at offset 32
  // has degree 32 + 2 and select_row's predicate 34 in gamma.
  EXPECT_EQ(charge_of(cs, "t.gamma"), Bound(34));
  EXPECT_EQ(degree_bound(*c, "t.gamma"), Bound(34));
  const AV rv = lift(af(), random_mod(R * W, 1u << 20, 9));
  Assignment st;
  st.set(rows, rv);
  const AV rec = map.apply(af(), AV(rv.begin() + 5 * W, rv.begin() + 6 * W));
  Assignment w;
  w.set(p, AV(rec.begin(), rec.begin() + 2 * n));
  w.set(l, AV(rec.begin() + 2 * n, rec.end()));
  w.set(sel.index, bits_of(5, 3));
  EXPECT_TRUE(honest(*c, st, w));
  w.set(sel.index, bits_of(6, 3));
  EXPECT_TRUE(prover_refuses(*c, st, w));
}

// -------------------------------------------------------------- lookup --

size_t id_of(const Sys &cs, const std::string &name) {
  const auto &N = cs.graph().nodes;
  for (size_t i = 0; i < N.size(); ++i)
    if (N[i].name == name) return i;
  ADD_FAILURE() << "no node " << name;
  return SIZE_MAX;
}

TEST(GordieHoweTable, LookupSmallTable) {
  const size_t R = 10, W = 2, m = 5;
  Sys cs("gh-table-lookup");
  auto &A = cs.domain(env().a_profile(), "A");
  auto rows = A.pub(Subfield{}, "rows", Shape{R, W});
  auto recs = A.priv(Subfield{}, "recs", Shape{m, W});
  const auto table = lib::table::public_table(
      cs, A, "t", rows, lib::table::RowMap<AF>::identity(W));
  lib::table::lookup_rows(cs, table, "attrs", recs);
  auto c = compile(cs);
  // The lookup is assert_in over the rows: records of arity W = 2 <= [K :
  // E] = 4 in the subfield pack by the fixed kappa (exact, no gamma);
  // alpha: m + R - 1, the cleared identity. The table's own gamma is
  // select_row's, which this system does not call.
  EXPECT_EQ(charge_of(cs, "alpha:A"), Bound(m + R - 1));
  for (const auto &n : cs.graph().nodes) {
    EXPECT_NE(n.name, "in.gamma:A");
    EXPECT_NE(n.name, "t.gamma");
  }
  const AV rv = lift(af(), random_mod(R * W, 1000, 3));
  Assignment st;
  st.set(rows, rv);
  // Rows 2, 7, 2, 9, 0: row 2 twice.
  const size_t pick[m] = {2, 7, 2, 9, 0};
  AV rec;
  for (size_t t : pick)
    for (size_t k = 0; k < W; ++k) rec.push_back(rv[t * W + k]);
  Assignment w;
  w.set(recs, rec);
  EXPECT_TRUE(honest(*c, st, w));
  // A record off the table.
  AV off = rec;
  af().add(off[3], af().one());
  Assignment w2;
  w2.set(recs, off);
  EXPECT_TRUE(prover_refuses(*c, st, w2));
  EXPECT_TRUE(verifier_rejects_witness(*c, st, w2));
  // A wrong multiplicity.
  const auto mid = id_of(cs, "t.mult");
  EXPECT_TRUE(verifier_rejects(*c, st, w, [mid](size_t at, SysValue &x) {
    if (at == mid) af().add(std::get<AV>(x)[2], af().one());
  }));
}

// Stream bytes that serve fixed bytes, as a forced challenge stream does.
class FixedBytes : public RandomEngine {
 public:
  explicit FixedBytes(std::vector<uint8_t> b) : b_(std::move(b)) {}
  void bytes(uint8_t *buf, size_t n) override {
    for (size_t i = 0; i < n; ++i) buf[i] = b_.at(at_++);
  }

 private:
  std::vector<uint8_t> b_;
  size_t at_ = 0;
};
// The stream bytes on which rng.elt draws X, checked by drawing from them.
std::vector<uint8_t> draw_bytes(const AElt &x) {
  std::vector<uint8_t> b(AF::kBytes);
  af().to_bytes_field(b.data(), x);
  FixedBytes fb(b);
  EXPECT_EQ(fb.elt(af()), x);
  return b;
}
// pack(row_j) = sum_k row_j[k] P[k] for the R rows of RV.
AV packed(const AV &rv, size_t W, const AV &P) {
  AV d(rv.size() / W, af().zero());
  for (size_t j = 0; j < d.size(); ++j)
    for (size_t k = 0; k < W; ++k)
      af().add(d[j], af().mulf(rv[j * W + k], P[k]));
  return d;
}

// The sampler the program export writes for challenge NAME.
std::string sampler_of(const compiler::ProgramData &p, const std::string &name) {
  for (size_t i = 0; i < p.challenges.size(); ++i)
    if (p.challenges[i].first == name) return p.samplers.at(i);
  return "";
}

// A public table is checked by the identity after clearing denominators
// (lem:logup-point(3)), which has no weight and so no pole: alpha:A is
// uniform in K, a stream whose first draw is a packed row (the fixed kappa
// packing) is not redrawn, and the honest proof verifies at that alpha. A
// record whose value is missing from the table and a wrong multiplicity
// are rejected at the transcript's alpha: at a packed row the table side's
// cleared denominator vanishes, and with that row's multiplicity 0 (row 3
// here) the identity holds for any records, one of the at most n + R - 1
// roots that alpha's charge counts.
TEST(GordieHoweTable, PublicTableClearedAtPackedRow) {
  const size_t R = 10, W = 2, m = 5;
  Sys cs("gh-table-alpha-row");
  auto &A = cs.domain(env().a_profile(), "A");
  auto rows = A.pub(Subfield{}, "rows", Shape{R, W});
  auto recs = A.priv(Subfield{}, "recs", Shape{m, W});
  const auto table = lib::table::public_table(
      cs, A, "t", rows, lib::table::RowMap<AF>::identity(W));
  lib::table::lookup_rows(cs, table, "attrs", recs);
  auto c = compile(cs);
  EXPECT_EQ(cs.graph().nodes.at(id_of(cs, "alpha:A")).sampler, "field");
  // No weights: the circuit reads the rows.
  for (const auto &n : cs.graph().nodes) EXPECT_NE(n.name, "t.weights");
  EXPECT_EQ(c->report().find("packed rows"), std::string::npos)
      << c->report();
  const AV rv = lift(af(), random_mod(R * W, 1000, 3));
  Assignment st;
  st.set(rows, rv);
  AV rec;
  for (size_t j : {2u, 7u, 2u, 9u, 0u})
    for (size_t k = 0; k < W; ++k) rec.push_back(rv[j * W + k]);
  Assignment w;
  w.set(recs, rec);
  const AElt kappa = lib::permutation::selection_kappa(af());
  const AV d = packed(rv, W, {af().one(), kappa});
  c->set_challenge_prefix("alpha:A", draw_bytes(d[3]));
  EXPECT_TRUE(honest(*c, st, w));
  EXPECT_EQ(std::get<AV>(c->drawn_challenge("alpha:A")).at(0), d[3]);
  EXPECT_EQ(c->drawn_challenge_bytes("alpha:A"), 1 * AF::kBytes);
  // The program export draws alpha from the field minus [0, 0).
  {
    const auto p = compiler::build_program(
        *c, compiler::ExportMeta{"alpha-row", "wide", "test", "test", 0});
    EXPECT_EQ(sampler_of(p, "alpha:A"), "(.fieldMinusTables (.range 0))");
  }
  // A record whose value is missing from the table.
  c->set_challenge_prefix("alpha:A", {});
  AV off = rec;
  af().add(off[3], af().one());
  Assignment w2;
  w2.set(recs, off);
  EXPECT_TRUE(prover_refuses(*c, st, w2));
  EXPECT_TRUE(verifier_rejects_witness(*c, st, w2));
  // A wrong multiplicity.
  const auto mid = id_of(cs, "t.mult");
  EXPECT_TRUE(verifier_rejects(*c, st, w, [mid](size_t at, SysValue &x) {
    if (at == mid) af().add(std::get<AV>(x)[2], af().one());
  }));
}

// Under the challenge packing the same holds: with gamma forced, alpha
// drawn at a row packed by gamma is kept, and the proof verifies.
TEST(GordieHoweTable, PublicTableClearedAtGammaPackedRow) {
  const size_t R = 6, W = 5;
  Sys cs("gh-table-alpha-row-gamma");
  auto &A = cs.domain(env().a_profile(), "A");
  auto rows = A.pub(Subfield{}, "rows", Shape{R, W});
  auto recs = A.priv(Subfield{}, "recs", Shape{2, W});
  const auto table = lib::table::public_table(
      cs, A, "t", rows, lib::table::RowMap<AF>::identity(W));
  lib::table::lookup_rows(cs, table, "wide", recs);
  auto c = compile(cs);
  EXPECT_LE(c->phase(id_of(cs, "in.gamma:A")),
            c->phase(id_of(cs, "alpha:A")));
  EXPECT_EQ(cs.graph().nodes.at(id_of(cs, "alpha:A")).sampler, "field");
  const AV rv = lift(af(), random_mod(R * W, 1000, 11));
  Assignment st;
  st.set(rows, rv);
  AV rec;
  for (size_t j : {4u, 1u})
    for (size_t k = 0; k < W; ++k) rec.push_back(rv[j * W + k]);
  Assignment w;
  w.set(recs, rec);
  const AElt gamma = af().of_scalar(123456789);
  AV P(W, af().one());
  for (size_t k = 1; k < W; ++k) P[k] = af().mulf(P[k - 1], gamma);
  const AV d = packed(rv, W, P);
  c->set_challenge_prefix("in.gamma:A", draw_bytes(gamma));
  c->set_challenge_prefix("alpha:A", draw_bytes(d[4]));
  EXPECT_TRUE(honest(*c, st, w));
  EXPECT_EQ(std::get<AV>(c->drawn_challenge("in.gamma:A")).at(0), gamma);
  EXPECT_EQ(std::get<AV>(c->drawn_challenge("alpha:A")).at(0), d[4]);
  EXPECT_EQ(c->drawn_challenge_bytes("alpha:A"), 1 * AF::kBytes);
  const auto p = compiler::build_program(
      *c, compiler::ExportMeta{"alpha-row-gamma", "wide", "test", "test", 0});
  EXPECT_EQ(sampler_of(p, "alpha:A"), "(.fieldMinusTables (.range 0))");
}

// A domain with a range check and a public assert_in table draws one LogUp
// challenge, alpha:<D>: uniform outside [0, T_max), the range tables'
// rows (the table's packed rows are not excluded), at the later of the two
// lowerings' phases, charged the sum of their charges. A stream whose
// first draws are a range table point and a packed row is drawn a second
// time, the proof verifies at the packed row, and a record off the table
// or a value out of range is rejected.
TEST(GordieHoweTable, RangeAndTableShareOneAlpha) {
  const size_t R = 10, W = 2, m = 5, nx = 4;
  const Bound n = 200;
  // The charge, phase and program export of alpha:A in a system with the
  // range check, the lookup, or both.
  struct Alpha {
    Bound charge = 0;
    size_t phase = 0;
    std::string sampler, role;
  };
  auto alpha_of = [](const Sys &cs, const CompiledSystem &c) {
    Alpha a;
    a.charge = charge_of(cs, "alpha:A");
    a.phase = c.phase(id_of(cs, "alpha:A"));
    const auto p = compiler::build_program(
        c, compiler::ExportMeta{"alpha-joint", "wide", "test", "test", 0});
    for (size_t i = 0; i < p.challenges.size(); ++i)
      if (p.challenges[i].first == "alpha:A") {
        a.sampler = p.samplers.at(i);
        a.role = p.chal_roles.at(i);
      }
    return a;
  };
  Alpha range_only, table_only;
  {
    Sys cs("gh-table-alpha-range");
    auto &A = cs.domain(env().a_profile(), "A");
    auto x = A.priv(Subfield{}, "x", nx);
    assert_range(x, n, "x");
    auto c = compile(cs);
    range_only = alpha_of(cs, *c);
  }
  {
    Sys cs("gh-table-alpha-table");
    auto &A = cs.domain(env().a_profile(), "A");
    auto rows = A.pub(Subfield{}, "rows", Shape{R, W});
    auto recs = A.priv(Subfield{}, "recs", Shape{m, W});
    const auto table = lib::table::public_table(
        cs, A, "t", rows, lib::table::RowMap<AF>::identity(W));
    lib::table::lookup_rows(cs, table, "attrs", recs);
    auto c = compile(cs);
    table_only = alpha_of(cs, *c);
  }
  EXPECT_EQ(range_only.role, "realization");
  // assert_in exports its lookups as in predicates: alpha is owned by the
  // first one.
  EXPECT_EQ(table_only.role, "realization");
  EXPECT_EQ(table_only.charge, Bound(m + R - 1));

  Sys cs("gh-table-alpha-joint");
  auto &A = cs.domain(env().a_profile(), "A");
  auto x = A.priv(Subfield{}, "x", nx);
  assert_range(x, n, "x");
  auto rows = A.pub(Subfield{}, "rows", Shape{R, W});
  auto recs = A.priv(Subfield{}, "recs", Shape{m, W});
  const auto table = lib::table::public_table(
      cs, A, "t", rows, lib::table::RowMap<AF>::identity(W));
  lib::table::lookup_rows(cs, table, "attrs", recs);
  auto c = compile(cs);
  // One LogUp challenge, read by both lowerings' lookups.
  size_t alphas = 0;
  for (const auto &nd : cs.graph().nodes)
    if (nd.kind == Kind::kChallenge)
      alphas += nd.name.find("alpha") != std::string::npos;
  EXPECT_EQ(alphas, 1u);
  ASSERT_FALSE(A.range_tables().empty());
  Bound tmax = 0;
  for (const auto &t : A.range_tables()) {
    EXPECT_EQ(cs.graph().nodes.at(t.alpha).name, "alpha:A");
    tmax = std::max(tmax, t.table);
  }
  const Alpha joint = alpha_of(cs, *c);
  EXPECT_EQ(joint.charge, range_only.charge + table_only.charge);
  EXPECT_EQ(joint.phase, std::max(range_only.phase, table_only.phase));
  EXPECT_EQ(joint.role, "realization");
  EXPECT_EQ(cs.graph().nodes.at(id_of(cs, "alpha:A")).sampler,
            "field-minus-tables");
  const std::string want =
      "(.fieldMinusTables (.range " + bound_str(tmax) + "))";
  EXPECT_EQ(joint.sampler, want);
  EXPECT_EQ(range_only.sampler, want);
  // With no range table alpha avoids [0, 0).
  EXPECT_EQ(table_only.sampler, "(.fieldMinusTables (.range 0))");
  EXPECT_NE(c->report().find("alpha:A: drawn outside [0, " + bound_str(tmax) +
                             ")"),
            std::string::npos)
      << c->report();
  EXPECT_EQ(c->report().find("packed rows"), std::string::npos)
      << c->report();

  const AV rv = lift(af(), random_mod(R * W, 1000, 13));
  Assignment st;
  st.set(rows, rv);
  AV rec;
  for (size_t j : {2u, 7u, 2u, 9u, 0u})
    for (size_t k = 0; k < W; ++k) rec.push_back(rv[j * W + k]);
  const AV xv = lift(af(), {0, 17, 123, 199});
  Assignment w;
  w.set(recs, rec);
  w.set(x, xv);
  // The first draw is the range table's point 0, the second a packed row.
  const AElt kappa = lib::permutation::selection_kappa(af());
  const AV d = packed(rv, W, {af().one(), kappa});
  std::vector<uint8_t> prefix = draw_bytes(af().zero());
  const std::vector<uint8_t> second = draw_bytes(d[3]);
  prefix.insert(prefix.end(), second.begin(), second.end());
  c->set_challenge_prefix("alpha:A", prefix);
  EXPECT_TRUE(honest(*c, st, w));
  const AElt alpha = std::get<AV>(c->drawn_challenge("alpha:A")).at(0);
  EXPECT_EQ(alpha, d[3]);
  EXPECT_FALSE(compiler::range_internal::in_range_table(af(), alpha, tmax));
  EXPECT_EQ(c->drawn_challenge_bytes("alpha:A"), 2 * AF::kBytes);
  // The rejections run at the transcript's alpha: at a packed row of
  // multiplicity 0 the cleared identity holds for any records.
  c->set_challenge_prefix("alpha:A", {});
  // A record off the table.
  {
    AV off = rec;
    af().add(off[3], af().one());
    Assignment w2;
    w2.set(recs, off);
    w2.set(x, xv);
    EXPECT_TRUE(prover_refuses(*c, st, w2));
    EXPECT_TRUE(verifier_rejects_witness(*c, st, w2));
  }
  // A value out of range.
  {
    Assignment w2;
    w2.set(recs, rec);
    w2.set(x, lift(af(), {0, 17, 123, 4 * 199}));
    EXPECT_TRUE(prover_refuses(*c, st, w2));
    EXPECT_TRUE(verifier_rejects_witness(*c, st, w2));
  }
  // A wrong multiplicity of the table.
  const auto mid = id_of(cs, "t.mult");
  EXPECT_TRUE(verifier_rejects(*c, st, w, [mid](size_t at, SysValue &v) {
    if (at == mid) af().add(std::get<AV>(v)[2], af().one());
  }));
}

// Two lookups into one table are one argument: one multiplicity vector
// over both requests' records, one alpha and one circuit.
TEST(GordieHoweTable, LookupsShareOneArgument) {
  const size_t R = 10, W = 2;
  Sys cs("gh-table-lookups");
  auto &A = cs.domain(env().a_profile(), "A");
  auto rows = A.pub(Subfield{}, "rows", Shape{R, W});
  auto a = A.priv(Subfield{}, "a", Shape{3, W});
  auto b = A.priv(Subfield{}, "b", Shape{2, W});
  const auto table = lib::table::public_table(
      cs, A, "t", rows, lib::table::RowMap<AF>::identity(W));
  lib::table::lookup_rows(cs, table, "first", a);
  lib::table::lookup_rows(cs.scope("other"), table, "second", b);
  auto c = compile(cs);
  size_t mults = 0, alphas = 0;
  for (const auto &n : cs.graph().nodes) {
    mults += n.name == "t.mult";
    alphas += n.name == "alpha:A";
  }
  EXPECT_EQ(mults, 1u);
  EXPECT_EQ(alphas, 1u);
  EXPECT_NE(c->report().find("in t: 2 requests (first, other.second), "
                             "5 records, 10 rows of arity 2, fixed kappa "
                             "packing"),
            std::string::npos)
      << c->report();
  const AV rv = lift(af(), random_mod(R * W, 1000, 5));
  Assignment st;
  st.set(rows, rv);
  auto pick = [&](std::initializer_list<size_t> js) {
    AV out;
    for (size_t j : js)
      for (size_t k = 0; k < W; ++k) out.push_back(rv[j * W + k]);
    return out;
  };
  Assignment w;
  w.set(a, pick({1, 4, 1}));
  w.set(b, pick({4, 9}));
  EXPECT_TRUE(honest(*c, st, w));
  Assignment w2;
  w2.set(a, pick({1, 4, 1}));
  AV off = pick({4, 9});
  af().add(off[0], af().one());
  w2.set(b, off);
  EXPECT_TRUE(prover_refuses(*c, st, w2));
}

// Records wider than [K : E] = 4, and records of a block map (a negacyclic
// leaf and an identity limb): the rows become the public computation of
// M(row), and records of width W pack by the challenge in.gamma:A, charged
// R (W - 1).
TEST(GordieHoweTable, LookupWideAndMappedRecords) {
  const size_t R = 6, n = 4, W = n + 1;
  for (bool mapped : {false, true}) {
    Sys cs("gh-table-lookup-wide");
    auto &A = cs.domain(env().a_profile(), "A");
    auto rows = A.pub(Subfield{}, "rows", Shape{R, W});
    auto recs = A.priv(Subfield{}, "recs", Shape{2, W});
    const auto map =
        mapped ? lib::table::RowMap<AF>::blocks(
                     {{lib::table::RowMap<AF>::negacyclic(af(), n, psi_of(n)),
                       1},
                      {lib::table::RowMap<AF>::identity(1), 1}})
               : lib::table::RowMap<AF>::identity(W);
    const auto table = lib::table::public_table(cs, A, "t", rows, map);
    lib::table::lookup_rows(cs, table, "wide", recs);
    auto c = compile(cs);
    EXPECT_EQ(charge_of(cs, "in.gamma:A"), Bound(R * (W - 1))) << mapped;
    EXPECT_EQ(charge_of(cs, "alpha:A"), Bound(2 + R - 1)) << mapped;
    const AV rv = lift(af(), random_mod(R * W, 1000, 11));
    Assignment st;
    st.set(rows, rv);
    AV rec;
    for (size_t j : {4u, 1u}) {
      const AV r = map.apply(
          af(), AV(rv.begin() + long(j * W), rv.begin() + long((j + 1) * W)));
      rec.insert(rec.end(), r.begin(), r.end());
    }
    Assignment w;
    w.set(recs, rec);
    EXPECT_TRUE(honest(*c, st, w)) << mapped;
    AV off = rec;
    af().add(off[W + 1], af().one());
    Assignment w2;
    w2.set(recs, off);
    EXPECT_TRUE(verifier_rejects_witness(*c, st, w2)) << mapped;
  }
}

// ------------------------------------------------------- compile errors --

TEST(GordieHoweTable, MisuseIsACompileError) {
  // Rows computed from a challenge: the digests would not depend on the
  // statement alone.
  EXPECT_NE(error_of([] {
              Sys cs("e1");
              auto &A = cs.domain(env().a_profile(), "A");
              (void)A.priv(Subfield{}, "x", 4);
              auto ch = A.challenge("c");
              auto rows = A.pub(Field{}, "rows", Shape{4, 4}, depends_on(ch), computes("f"),
                  [](const AV &c) { return AV(16, c[0]); });
              (void)lib::table::public_table(
                  cs, A, "t", rows, lib::table::RowMap<AF>::identity(4));
            }).find("not a statement value"),
            std::string::npos);
  // A record of the wrong width.
  EXPECT_NE(error_of([] {
              Sys cs("e2");
              auto &A = cs.domain(env().a_profile(), "A");
              auto rows = A.pub(Subfield{}, "rows", Shape{4, 4});
              auto x = A.priv(Subfield{}, "x", 5);
              const auto t = lib::table::public_table(
                  cs, A, "t", rows, lib::table::RowMap<AF>::identity(4));
              (void)lib::table::select_row(cs, t, "s", x);
            }).find("has 5 coordinates"),
            std::string::npos);
  // A map wider than the rows.
  EXPECT_NE(error_of([] {
              Sys cs("e3");
              auto &A = cs.domain(env().a_profile(), "A");
              auto rows = A.pub(Subfield{}, "rows", Shape{4, 4});
              (void)lib::table::public_table(
                  cs, A, "t", rows, lib::table::RowMap<AF>::identity(5));
            }),
            "");
  // One row.
  EXPECT_NE(error_of([] {
              Sys cs("e4");
              auto &A = cs.domain(env().a_profile(), "A");
              auto rows = A.pub(Subfield{}, "rows", Shape{1, 4});
              (void)lib::table::public_table(
                  cs, A, "t", rows, lib::table::RowMap<AF>::identity(4));
            }),
            "");
  // A root of the wrong order.
  EXPECT_NE(error_of([] {
              (void)lib::table::RowMap<AF>::negacyclic(af(), 16, psi_of(32));
            }),
            "");
  EXPECT_NE(error_of([] { (void)lib::table::RowMap<AF>::fips204(af()); }),
            "");
  // A lookup in characteristic 2 is a C++ compile error.
}

}  // namespace
}  // namespace proofs::gordiehowe
