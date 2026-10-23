// Copyright 2026 Chad Sharp and Paul Grubbs
// SPDX-License-Identifier: Apache-2.0

// GordieHowe: assert_mod, the MAC lowering written through it (merged per
// domain pair, grouped when acc_max reaches p), and the range lowering's split
// groups, complements, type-implied intervals, table roots, table cap and the
// planner's cost model. Each lowering proves and verifies honestly and rejects
// a bad witness.

#include <algorithm>
#include <cstddef>
#include <cstdint>
#include <cstdio>
#include <functional>
#include <map>
#include <memory>
#include <optional>
#include <random>
#include <regex>
#include <string>
#include <type_traits>
#include <vector>

#include "gordiehowe/compile_error_testing.h"
#include "algebra/fp.h"
#include "algebra/fp14.h"
#include "algebra/fp14_n.h"
#include "algebra/fp_goldilocks4.h"
#include "algebra/reed_solomon_extension_n.h"
#include "algebra/reed_solomon_fp.h"
#include "gf2k/gf2_128.h"
#include "gf2k/gf2_256.h"
#include "gf2k/lch14_reed_solomon.h"
#include "gordiehowe/compiler/plan_export.h"
#include "gordiehowe/compiler/plan_program.h"
#include "gordiehowe/examples/shared/program_testing.h"
#include "gordiehowe/instances.h"
#include "gordiehowe/system.h"
#include "gtest/gtest.h"
#include "random/secure_random_engine.h"

namespace proofs::gordiehowe {
namespace {

using AF = Fp64G4;
using AElt = AF::Elt;
using AV = std::vector<AElt>;
using RSA = BasicFpReedSolomon<AF>;
using HF = GF2_256<>;
using HV = std::vector<HF::Elt>;
using RSH = LCH14ReedSolomonFactory<HF>;
using GF = GF2_128<>;
using GV = std::vector<GF::Elt>;
using RSG = LCH14ReedSolomonFactory<GF>;
using NF = Fp14_9;
using NElt = NF::Elt;
using NV = std::vector<NElt>;
using RSN = ReedSolomonExtensionNFactory<NF>;

using Sys = ConstraintSystem<SHA384, AF, HF, GF, NF>;
using SysValue = Sys::Value;
using Assignment = Sys::Assignment;
using ProveOptions = Sys::ProveOptions;
using CompiledSystem = Sys::Compiled;

constexpr uint64_t kQ = 12289;

struct Env {
  AF af;
  RSA rsa{af};
  HF hf;
  RSH rsh{hf};
  GF gf;
  RSG rsg{gf};
  Fp14 fq{kQ};
  NF nf{fq, NF::beta_};
  RSN rsn{fq};
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
    return p;
  }
  template <class F, class R>
  DomainProfile<F, R, SHA384> binary(const F *f, const R *r, const char *nm) const {
    DomainProfile<F, R, SHA384> p;
    p.f = f;
    p.rsf = r;
    p.field_name = nm;
    p.rate = 4;
    p.nreq = 64;
    return p;
  }
  DomainProfile<HF, RSH, SHA384> h_profile() const {
    return binary(&hf, &rsh, "GF(2^256)");
  }
  DomainProfile<GF, RSG, SHA384> g_profile() const {
    return binary(&gf, &rsg, "GF(2^128)");
  }
  DomainProfile<NF, RSN, SHA384> n_profile() const {
    DomainProfile<NF, RSN, SHA384> p;
    p.f = &nf;
    p.rsf = &rsn;
    p.field_name = "F_q^9";
    p.rate = 4;
    p.nreq = 64;
    return p;
  }
};
const Env &env() {
  static const Env *e = new Env;
  return *e;
}
const AF &af() { return env().af; }
const NF &nf() { return env().nf; }

// The native profile: Falcon native's MAC bases.
CompileProfile native_profile() {
  CompileProfile c;
  c.name = "native";
  c.mac_bases = {kMacBasisGF2_256, MacBasis{128, {7, 2, 1, 0}}};
  return c;
}

size_t id_of(const Sys &cs, const std::string &name) {
  const auto &N = cs.graph().nodes;
  for (size_t i = 0; i < N.size(); ++i)
    if (N[i].name == name) return i;
  ADD_FAILURE() << "no node " << name;
  return SIZE_MAX;
}
bool has(const std::string &report, const std::string &want) {
  if (report.find(want) != std::string::npos) return true;
  ADD_FAILURE() << "missing: " << want << "\n" << report;
  return false;
}

bool honest(const CompiledSystem &c, const Assignment &st,
            const Assignment &w) {
  auto prep = c.prepare(st);
  SecureRandomEngine rng;
  return prep.verify(prep.prove(w, rng));
}
// The cheating prover under TAMPER is refused by its own satisfaction
// check, or completes and the verifier rejects.
template <class Tamper>
bool rejected(const CompiledSystem &c, const Assignment &st,
              const Assignment &w, Tamper tamper) {
  // (A private input is not generated, so TAMPER does not reach it: a bad
  // private input is a bad assignment with no tamper.)
  auto prep = c.prepare(st);
  ProveOptions opt;
  opt.tamper = tamper;
  opt.require_satisfied = false;
  SecureRandomEngine rng;
  std::vector<uint8_t> proof;
  try {
    proof = prep.prove(w, rng, opt);
  } catch (const std::runtime_error &) {
    return true;
  }
  return !prep.verify(proof);
}
// Adds DELTA to coordinate I of node ID.
const auto kNoTamper = [](size_t, SysValue &) {};

template <class V, class E>
auto add_at(size_t id, size_t i, E delta) {
  return [id, i, delta](size_t at, SysValue &x) {
    if (at != id) return;
    auto &v = std::get<V>(x);
    if constexpr (std::is_same_v<V, AV>)
      af().add(v.at(i), delta);
    else
      nf().add(v.at(i), delta);
  };
}

// ------------------------------------------------------------ assert_mod --

// m = p: the field equality, whatever the sides' intervals.
TEST(GordieHoweMod, CharacteristicIsTheFieldEquality) {
  Sys cs("gh-mod-char");
  auto &N = cs.domain(env().n_profile(), "N");
  auto x = N.priv(Subfield{}, "x", 4);
  auto y = N.priv(Subfield{}, "y", 4);
  auto z = N.priv(Subfield{}, "z", 4, depends_on(x, y),
                    [](const NElt &a, const NElt &b) { return nf().addf(a, b); });
  assert_mod(x + y, z, kQ, "sum");
  // A Bit, whose Boolean check gives the domain its circuit.
  auto bit = N.priv(Bit{}, "bit", 1);
  auto c = compile(cs, native_profile());
  const std::string r = c->report();
  has(r, "assert_mod 'sum': m = p = 12289, the field equality (4 affine rows)");
  EXPECT_EQ(r.find("range."), std::string::npos) << r;
  Assignment w;
  w.set(x, NV{nf().of_scalar(12000), nf().of_scalar(1), nf().of_scalar(2),
              nf().of_scalar(3)});
  w.set(y, NV{nf().of_scalar(1000), nf().of_scalar(5), nf().of_scalar(6),
              nf().of_scalar(7)});
  w.set(bit, NV{nf().one()});
  EXPECT_TRUE(honest(*c, {}, w));
  EXPECT_TRUE(rejected(*c, {}, w, add_at<NV>(z.id, 1, nf().one())));
}

// The one-group forms over Goldilocks^4: a Bit quotient, one derived
// digit, and two digits in a balanced radix with a derived top digit.
struct OneGroupSys {
  Sys cs{"gh-mod-one"};
  Domain<AF> *A;
  Ref<AF> b, c, x, rx, z, rz;
  OneGroupSys() {
    A = &cs.domain(env().a_profile(), "A");
    // b < 8, c < 4: b - c in [-3, 7], m = 5: quotient in [0, 1].
    b = A->priv(Subfield{}, "b", 3);
    c = A->priv(Subfield{}, "c", 3, depends_on(b),
                  nat([](NatInt v) { return v % 5; }));
    assert_range(b, 8, "b");
    assert_range(c, 4, "c");
    assert_mod(b, c, 5, "bit");
    // x < 2048, m = 7: quotient below 293, one digit.
    x = A->priv(Subfield{}, "x", 3);
    rx = A->priv(Subfield{}, "rx", 3, depends_on(x), nat([](NatInt v) { return v % 7; }));
    assert_range(x, 2048, "x");
    assert_range(rx, 7, "rx");
    assert_mod(x, rx, 7, "one");
    // z < 2^22, m = 3: quotient below 1398102, two digits.
    z = A->priv(Subfield{}, "z", 3);
    rz = A->priv(Subfield{}, "rz", 3, depends_on(z), nat([](NatInt v) { return v % 3; }));
    assert_range(z, Bound(1) << 22, "z");
    assert_range(rz, 3, "rz");
    assert_mod(z, rz, 3, "two");
  }
  Assignment witness() const {
    Assignment w;
    w.set(b, AV{af().of_scalar(7), af().of_scalar(2), af().of_scalar(5)});
    w.set(x, AV{af().of_scalar(2047), af().of_scalar(0), af().of_scalar(1234)});
    w.set(z, AV{af().of_scalar((1 << 22) - 1), af().of_scalar(3),
                af().of_scalar(77777)});
    return w;
  }
};

TEST(GordieHoweMod, OneGroupForms) {
  OneGroupSys m;
  auto c = compile(m.cs);
  const std::string r = c->report();
  has(r, "assert_mod 'bit': lhs in [0, 7], rhs in [0, 3], m = 5, quotient in "
         "[0, 1]: a Bit quotient 'bit.q'");
  has(r, "assert_mod 'one': lhs in [0, 2047], rhs in [0, 6], m = 7, quotient "
         "in [0, 292]: one derived digit 'one.q' below 293");
  has(r, "assert_mod 'two': lhs in [0, 4194303], rhs in [0, 2], m = 3, "
         "quotient in [0, 1398101]: 2 digits, radix B = ");
  has(r, "two.nowrap: implied");
  const Assignment w = m.witness();
  EXPECT_TRUE(honest(*c, {}, w));
  // A wrong low digit (the derived top digit follows it out of range or
  // breaks the no-wrap identity).
  EXPECT_TRUE(rejected(*c, {}, w, add_at<AV>(id_of(m.cs, "two.low"), 0, af().one())));
  // A wrong residue: the one-digit quotient (rx + 1 - x) / 7 leaves the
  // table.
  EXPECT_TRUE(rejected(*c, {}, w, add_at<AV>(m.rx.id, 1, af().one())));
  // A wrong residue under the Bit quotient: its Boolean check fails.
  EXPECT_TRUE(rejected(*c, {}, w, add_at<AV>(m.c.id, 0, af().one())));
}

// The left side reaches p: units grouped below p, each group with its
// committed quotient digits in the table's base and its parity bit; the
// final sum of the parities against the right side.
struct GroupedSys {
  Sys cs{"gh-mod-grouped"};
  Domain<NF> *N;
  std::vector<Ref<NF>> xs;
  Ref<NF> par;
  GroupedSys() {
    N = &cs.domain(env().n_profile(), "N");
    Lin<NF> sum;
    for (size_t i = 0; i < 10; ++i) {
      xs.push_back(N->priv(Subfield{}, "x" + std::to_string(i), 2));
      assert_range(xs.back(), 2048, "x" + std::to_string(i));
      sum = i == 0 ? Lin<NF>(xs.back()) : sum + xs.back();
    }
    std::vector<Ref<NF>> deps(xs.begin(), xs.end());
    par = N->priv(Bit{}, "parity", 2, deps,
                    [](const std::vector<const NV *> &in) {
                      NV out(2, nf().zero());
                      for (size_t j = 0; j < 2; ++j) {
                        uint64_t t = 0;
                        for (const auto *v : in) t += uint64_t(nat_of(nf(), (*v)[j]));
                        out[j] = nf().of_scalar(t & 1);
                      }
                      return out;
                    });
    assert_mod(sum, par, 2, "par");
  }
  Assignment witness() const {
    Assignment w;
    for (size_t i = 0; i < xs.size(); ++i)
      w.set(xs[i], NV{nf().of_scalar(2047 - i), nf().of_scalar(3 * i + 1)});
    return w;
  }
};

TEST(GordieHoweMod, GroupedWhenTheLeftSideReachesP) {
  GroupedSys m;
  auto c = compile(m.cs, native_profile());
  const std::string r = c->report();
  std::printf("%s", r.c_str());
  // The base: the domain's candidate table 2048 (the units' checks), in
  // one digit.
  has(r, "assert_mod 'par': lhs in [0, 20470] reaches p = 12289; 5 groups of "
         "units (2, 2, 2, 2, 2), each sum at most 4095 < p, 1 committed "
         "quotient digits in base 2048, residues Bit; tail (m-1) + m(T^k - 1) "
         "= 4095 < p");
  has(r, "assert_mod 'par': lhs in [0, 5], rhs in [0, 1], m = 2, quotient in "
         "[0, 2]: one derived digit 'par.final.q' below 3");
  const Assignment w = m.witness();
  EXPECT_TRUE(honest(*c, {}, w));
  // A wrong quotient digit: the parity leaves {0, 1}.
  EXPECT_TRUE(rejected(*c, {}, w, add_at<NV>(id_of(m.cs, "par.gq"), 0, nf().one())));
  // A wrong parity bit.
  EXPECT_TRUE(rejected(*c, {}, w, [&](size_t at, SysValue &x) {
    if (at != m.par.id) return;
    auto &v = std::get<NV>(x);
    v[1] = v[1] == nf().one() ? nf().zero() : nf().one();
  }));
  // A wrapped group sum: a group quotient one step too large makes
  // S_g - 2 Q_g wrap mod q, outside {0, 1}.
  EXPECT_TRUE(rejected(*c, {}, w, add_at<NV>(id_of(m.cs, "par.gq"), 1,
                                              nf().one())));
}

// A side no circuit reads (a public polynomial's PolyMatVec with an entry
// bound) over a signed operand: x in [-50, 50] from its request on x + 50,
// a below 97, w = a * x mod 97 below 128. The rhs interval is
// +-8 * 96 * 50; the quotient's digits are committed and the relation is
// an affine row.
struct OperatorModSys {
  static constexpr size_t kN = 8;
  static constexpr uint64_t kM = 97;
  Sys cs{"gh-mod-operator"};
  Domain<AF> *A;
  Ref<AF, Subfield<>, Public> a;
  Ref<AF, Subfield<>, Committed> x, w;
  OperatorModSys() {
    A = &cs.domain(env().a_profile(), "A");
    a = A->pub(Subfield{}, "a", Shape{1, 1, kN});
    x = A->priv(Subfield{}, "x", kN);
    assert_range(x + 50, 101, "x");
    const NatInt p = nat_cast(field_characteristic(af()));
    w = A->priv(Subfield{}, "w", kN, depends_on(a, x),
                  [p](const std::vector<NatInt> &av, const std::vector<NatInt> &xv) {
                    std::vector<NatInt> out(kN);
                    for (size_t k = 0; k < kN; ++k) {
                      __int128 t = 0;
                      for (size_t u = 0; u < kN; ++u) {
                        const __int128 xu = xv[u] > p / 2 ? -__int128(p - xv[u])
                                                          : __int128(xv[u]);
                        const size_t j = (k + kN - u) % kN;
                        t += (u <= k ? 1 : -1) * __int128(av[j]) * xu;
                      }
                      out[k] = NatInt(((t % __int128(kM)) + kM) % kM);
                    }
                    return out;
                  });
    assert_range(w, 128, "w");
    assert_mod(w, ops::PolyMatVec(a, ops::EntryBound{kM})(x), kM, "conv");
  }
  Assignment statement(uint64_t first = 96) const {
    Assignment st;
    AV v;
    for (size_t k = 0; k < kN; ++k) v.push_back(af().of_scalar(k ? 13 * k : first));
    st.set(a, v);
    return st;
  }
  Assignment witness() const {
    Assignment w0;
    AV v;
    const int64_t xs[kN] = {50, -50, 3, -7, 0, 49, -1, 12};
    for (int64_t t : xs)
      v.push_back(t >= 0 ? af().of_scalar(uint64_t(t))
                         : af().negf(af().of_scalar(uint64_t(-t))));
    w0.set(x, v);
    return w0;
  }
};

TEST(GordieHoweMod, CommittedDigitsOverAnOperator) {
  OperatorModSys m;
  auto c = compile(m.cs);
  const std::string r = c->report();
  has(r, "assert_mod 'conv': lhs in [0, 127], rhs in [-38400, 38400], m = 97, "
         "quotient in [-395, 397]; no circuit reads a side: a committed "
         "quotient 'conv.q' below 793 (MaxBound ");
  has(r, "and the relation as 8 affine rows");
  const Assignment st = m.statement(), w = m.witness();
  EXPECT_TRUE(honest(*c, st, w));
  // A wrong quotient.
  EXPECT_TRUE(rejected(*c, st, w, add_at<AV>(id_of(m.cs, "conv.q"), 2, af().one())));
  // A wrong residue (the digit follows from the floor of the difference).
  EXPECT_TRUE(rejected(*c, st, w, add_at<AV>(m.w.id, 3, af().one())));
  // A public coefficient at the entry bound: the operator refuses it.
  EXPECT_THROW(
      {
        auto prep = c->prepare(m.statement(97));
        SecureRandomEngine rng;
        prep.prove(w, rng);
      },
      std::runtime_error);
}

// ------------------------------------------------------------------ MAC --

// Bits of H copied into A: the two sides of a crossing.
template <class HFld, class AFld, class S, class D1, class D2>
std::pair<Ref<HFld>, Ref<AFld>> crossing(S &cs, D1 &H, D2 &A,
                                         const std::string &nm, size_t n) {
  auto xh = H.priv(Bit{}, nm + "_h", n);
  const AFld *pa = &A.field();
  const HFld *ph = &H.field();
  auto xa = A.priv(Bit{}, nm + "_a", n, depends_on(xh),
                     [pa, ph](const std::vector<typename HFld::Elt> &b) {
                       std::vector<typename AFld::Elt> out;
                       for (const auto &e : b)
                         out.push_back(ct::bit_elt(*pa, ct::bit_of(*ph, e)));
                       return out;
                     });
  return {xh, xa};
}
template <class HFld>
std::vector<typename HFld::Elt> bits_of(const HFld &f, size_t n, size_t seed) {
  std::vector<typename HFld::Elt> v;
  for (size_t i = 0; i < n; ++i)
    v.push_back(((i * 37 + seed) * 2654435761u >> 7) % 3 == 0 ? f.one()
                                                               : f.zero());
  return v;
}
template <class V, class Fld>
auto flip_at(const Fld &f, size_t id, size_t i) {
  return [&f, id, i](size_t at, SysValue &x) {
    if (at != id) return;
    auto &v = std::get<V>(x);
    v.at(i) = v.at(i) == f.one() ? f.zero() : f.one();
  };
}

// Two equalities between H and A at one phase lower to one MAC over the
// concatenation of their sides: one beta, blind, value and tail.
TEST(GordieHoweMod, TwoEqualitiesOneMac) {
  Sys cs("gh-mac-merge");
  auto &H = cs.domain(env().h_profile(), "H");
  auto &A = cs.domain(env().a_profile(), "A");
  auto [x1h, x1a] = crossing<HF, AF>(cs, H, A, "x1", 300);
  auto [x2h, x2a] = crossing<HF, AF>(cs, H, A, "x2", 100);
  assert_same_bits(x1h, x1a);
  assert_same_bits(x2a, x2h);
  auto c = compile(cs);
  const std::string r = c->report();
  has(r, "MAC mac: 2 equalities, assert_same_bits(x1_h, x1_a), "
         "assert_same_bits(x2_a, x2_h); H = H, A = A, w = 256, nch = 2");
  for (const auto &n : cs.graph().nodes)
    EXPECT_EQ(n.name.rfind("mac1", 0), std::string::npos) << n.name;
  size_t betas = 0;
  for (const auto &n : cs.graph().nodes) betas += n.name == "mac.beta";
  EXPECT_EQ(betas, 1u);
  Assignment w;
  w.set(x1h, bits_of(env().hf, 300, 1));
  w.set(x2h, bits_of(env().hf, 100, 2));
  EXPECT_TRUE(honest(*c, {}, w));
  EXPECT_TRUE(rejected(*c, {}, w, flip_at<AV>(af(), x2a.id, 17)));
  EXPECT_TRUE(rejected(*c, {}, w, flip_at<AV>(af(), x1a.id, 299)));
}

// Two odd domains, Goldilocks^4 and F_q^9, with no binary domain: the
// MAC lies in GF(2^256), the system's first binary field with a MAC basis,
// which no domain hosts. Its pad, key and masked tag are values of that
// field; both domains copy the pad's bits and prove their tag against the
// tag message with the binary path's odd side. Two equalities at one phase
// merge into one MAC. An honest proof verifies; a flipped bit on either
// side is rejected.
TEST(GordieHoweMod, TwoOddDomainsOneMac) {
  Sys cs("gh-mac-odd");
  auto &A = cs.domain(env().a_profile(), "A");
  auto &N = cs.domain(env().n_profile(), "N");
  auto [x1a, x1n] = crossing<AF, NF>(cs, A, N, "x1", 300);
  auto [x2a, x2n] = crossing<AF, NF>(cs, A, N, "x2", 100);
  assert_equal(x1a, x1n);
  assert_same_bits(x2n, x2a);
  auto c = compile(cs, native_profile());
  const std::string r = c->report();
  has(r, "MAC mac: 2 equalities, assert_same_bits(x1_h, x1_a), "
         "assert_same_bits(x2_a, x2_h); two odd domains A = A, B = N, MAC "
         "field of w = 256 bits (no domain), nch = 2");
  // The key, the pad and the tag lie in no domain.
  for (const char *nm : {"mac.beta", "mac.value"})
    EXPECT_EQ(cs.graph().nodes.at(id_of(cs, nm)).domain, -1) << nm;
  EXPECT_FALSE(c->messages().empty());
  Assignment w;
  w.set(x1a, bits_of(af(), 300, 1));
  w.set(x2a, bits_of(af(), 100, 2));
  EXPECT_TRUE(honest(*c, {}, w));
  EXPECT_TRUE(rejected(*c, {}, w, flip_at<NV>(nf(), x2n.id, 17)));
  EXPECT_TRUE(rejected(*c, {}, w, flip_at<NV>(nf(), x1n.id, 299)));
}

// The MAC field between two odd domains comes from the compile profile,
// not the field set: a system of two odd fields lists no binary field.
// GF(2^256) when the profile is post-quantum (the default), GF(2^128) when
// classical; each proves honestly and rejects a flipped bit. A profile
// with no MAC basis of its width fails, naming the width.
TEST(GordieHoweMod, TwoOddDomainsMacFieldFromProfile) {
  using OddSys = ConstraintSystem<SHA384, AF, NF>;
  auto run = [](const CompileProfile &p, const std::string &want) {
    OddSys cs("gh-mac-odd-profile");
    auto &A = cs.domain(env().a_profile(), "A");
    auto &N = cs.domain(env().n_profile(), "N");
    auto [xa, xn] = crossing<AF, NF>(cs, A, N, "x", 300);
    assert_equal(xa, xn);
    auto c = compile(cs, p);
    has(c->report(), want);
    OddSys::Assignment w;
    w.set(xa, bits_of(af(), 300, 1));
    auto prep = c->prepare({});
    SecureRandomEngine rng;
    EXPECT_TRUE(prep.verify(prep.prove(w, rng)));
    OddSys::ProveOptions opt;
    opt.tamper = [id = xn.id](size_t at, OddSys::Value &x) {
      if (at != id) return;
      auto &v = std::get<NV>(x);
      v.at(17) = v.at(17) == nf().one() ? nf().zero() : nf().one();
    };
    opt.require_satisfied = false;
    bool rejected = false;
    try {
      rejected = !prep.verify(prep.prove(w, rng, opt));
    } catch (const std::runtime_error &) {
      rejected = true;
    }
    EXPECT_TRUE(rejected);
  };
  CompileProfile pq = native_profile();
  run(pq, "MAC field of w = 256 bits (no domain), nch = 2");
  CompileProfile classical = native_profile();
  classical.security = Security::kClassical;
  run(classical, "MAC field of w = 128 bits (no domain), nch = 3");

  OddSys cs("gh-mac-odd-nobasis");
  auto &A = cs.domain(env().a_profile(), "A");
  auto &N = cs.domain(env().n_profile(), "N");
  auto [xa, xn] = crossing<AF, NF>(cs, A, N, "x", 64);
  assert_equal(xa, xn);
  CompileProfile nobasis;
  nobasis.security = Security::kClassical;
  std::string err;
  try {
    compile(cs, nobasis);
  } catch (const CompileError &e) {
    err = e.what();
  }
  EXPECT_NE(err.find("takes its MAC field from the compile profile, "
                     "GF(2^128) for profile 'default', which names no MAC "
                     "basis of width 128"),
            std::string::npos)
      << err;
}

// The plan export of a MAC between two odd domains: the key is a
// challenge of the MAC field, which no domain commits; the chunk powers,
// the tag and its message are values of that field with no domain. The
// program has one cross-field equal, its realization naming both blinds;
// both tails are realization parts of it. The program passes
// check_program.
TEST(GordieHoweMod, TwoOddDomainsExport) {
  using OddSys = ConstraintSystem<SHA384, AF, NF>;
  OddSys cs("gh-mac-odd-export");
  auto &A = cs.domain(env().a_profile(), "A");
  auto &N = cs.domain(env().n_profile(), "N");
  auto [x1a, x1n] = crossing<AF, NF>(cs, A, N, "x1", 300);
  auto [x2a, x2n] = crossing<AF, NF>(cs, A, N, "x2", 100);
  assert_equal(x1a, x1n);
  assert_same_bits(x2n, x2a);
  auto c = compile(cs, native_profile());
  const compiler::ExportMeta meta{"odd-mac", "wide", "c0ffee", "run-0", 0};
  const auto p = compiler::build_program(*c, meta);
  examples::check_program(p);
  auto value = [&](const std::string &nm) -> const compiler::ProgramData::Value * {
    for (const auto &v : p.values)
      if (v.name == nm) return &v;
    ADD_FAILURE() << "no value " << nm;
    return nullptr;
  };
  // The key: a challenge of the MAC field, a realization of the equal.
  size_t beta = SIZE_MAX, equal = SIZE_MAX;
  for (size_t i = 0; i < p.challenges.size(); ++i)
    if (p.challenges[i].first == "mac.beta") beta = i;
  for (size_t i = 0; i < p.predicates.size(); ++i)
    if (p.predicates[i].name == "mac.equal") equal = i;
  ASSERT_NE(beta, SIZE_MAX);
  ASSERT_NE(equal, SIZE_MAX);
  EXPECT_EQ(p.chal_roles[beta], "realization");
  EXPECT_EQ(p.chal_owners[beta], equal);
  EXPECT_EQ(p.predicates[equal].kind, "cross");
  // The values of the MAC field: no domain, the field after both domains'.
  for (const char *nm : {"mac.beta", "mac.powers", "mac.value", "msg(mac.value)"}) {
    const auto *v = value(nm);
    ASSERT_NE(v, nullptr) << nm;
    EXPECT_EQ(v->domain, SIZE_MAX) << nm;
    EXPECT_EQ(v->field, 2u) << nm;
    EXPECT_EQ(v->role, "realization") << nm;
    EXPECT_EQ(v->owner, equal) << nm;
  }
  EXPECT_EQ(value("mac.value")->kind, "late");
  EXPECT_EQ(value("msg(mac.value)")->kind, "message");
  // The blinds are pad copies of the tag, one per odd domain.
  for (const char *nm : {"mac.blind:A", "mac.blind:N"})
    EXPECT_EQ(value(nm)->kind, "padCopy") << nm;
  const std::string &body = p.predicates[equal].body;
  EXPECT_NE(body.find("macField := 2"), std::string::npos) << body;
  EXPECT_NE(body.find("blindX := some"), std::string::npos) << body;
  EXPECT_NE(body.find("hPredicate := none"), std::string::npos) << body;
  // Both tails realize the equal.
  for (const char *nm : {"mac.A", "mac.N"}) {
    bool found = false;
    for (const auto &q : p.predicates)
      if (q.name == nm) {
        found = true;
        EXPECT_EQ(q.role, "realization") << nm;
        EXPECT_EQ(q.owner, equal) << nm;
      }
    EXPECT_TRUE(found) << nm;
  }
  // The MAC field is a field of the program and no domain's.
  EXPECT_NE(p.text.find("{ name := \"GF(2^256)\", characteristic := 2, "
                        "degree := 256 }"),
            std::string::npos);
  EXPECT_NE(p.text.find("field := some 2"), std::string::npos);
  // The plan module exports it too, the key with an empty domain.
  std::string plan;
  try {
    plan = compiler::export_lean_plan(*c, meta);
  } catch (const std::exception &e) {
    ADD_FAILURE() << e.what();
  }
  EXPECT_NE(plan.find("label := \"mac.beta\""), std::string::npos);
}

// A native-Falcon-shaped MAC: 8192 bits into F_q^9 at table 64, where
// acc_max = nch convMax + 1 exceeds q. At the QROM parameters (w = 256,
// convMax 1017) the groups have 8 chunks. At the ROM parameters (w = 128,
// convMax 504) they have 16.
template <class HFld, class RS>
void native_mac(const DomainProfile<HFld, RS, SHA384> &hp, const char *groups,
                size_t ngroups, Bound acc_max) {
  Sys cs("gh-mac-native");
  auto &H = cs.domain(hp, "H");
  auto &N = cs.domain(env().n_profile(), "N");
  auto [ch, ca] = crossing<HFld, NF>(cs, H, N, "c", 8192);
  assert_same_bits(ch, ca);
  // A check below 64, as Falcon native's norm and encoding checks: the
  // grouping draws its base from the domain's candidate tables.
  auto z = N.priv(Subfield{}, "z", 1);
  assert_range(z, 64, "z");
  auto c = compile(cs, native_profile());
  const std::string r = c->report();
  has(r, "acc_max = " + bound_str(acc_max) + " >= p (grouped)");
  has(r, std::string("assert_mod 'mac': lhs in [0, ") + bound_str(acc_max) +
             "] reaches p = 12289; " + groups);
  has(r, "2 committed quotient digits in base 64, residues Bit; tail (m-1) + "
         "m(T^k - 1) = 8191 < p; 1 units below m in the final sum, at most " +
         std::to_string(ngroups + 1));
  has(r, "one derived digit 'mac.final.q' below " +
             std::to_string((ngroups + 1) / 2 + 1));
  // Needles: two quotient digits per group and coordinate, the final
  // quotient (2816 at w = 256), and z's.
  const size_t w = HFld::kBits;
  size_t needles = 0;
  for (const auto &t : N.range_tables())
    needles += t.static_needles + t.dynamic_needles;
  EXPECT_EQ(needles, (2 * ngroups + 1) * w + 1);
  Assignment a;
  a.set(ch, bits_of(H.field(), 8192, 3));
  a.set(z, NV{nf().of_scalar(63)});
  EXPECT_TRUE(honest(*c, {}, a));
  // An unequal bit; a wrong quotient digit (its parity leaves {0, 1}).
  EXPECT_TRUE(rejected(*c, {}, a, flip_at<NV>(nf(), ca.id, 4095)));
  EXPECT_TRUE(rejected(*c, {}, a, add_at<NV>(id_of(cs, "mac.gq"), 2, nf().one())));
}
TEST(GordieHoweMod, NativeFalconShapedMacQROM) {
  native_mac(env().h_profile(), "4 groups of units (8, 8, 8, 8)", 4,
             32 * 1017 + 1);
}
TEST(GordieHoweMod, NativeFalconShapedMacROM) {
  native_mac(env().g_profile(), "4 groups of units (16, 16, 16, 16)", 4,
             64 * 504 + 1);
}

// The one-group MAC's radix from acc_max: ML-DSA's crossing (6656 bits)
// takes the balanced radix 114 at w = 128 (acc_max = 52 * 504 + 1) and 115
// at w = 256 (26 * 1017 + 1), where a fixed 2^8 would give a histogram of
// 128; Falcon's (8192 bits, w = 256) keeps the power of two 128.
template <class HFld, class RS>
std::string mac_report(const DomainProfile<HFld, RS, SHA384> &hp, size_t bits) {
  Sys cs("gh-mac-radix");
  auto &H = cs.domain(hp, "H");
  auto &A = cs.domain(env().a_profile(), "A");
  auto [xh, xa] = crossing<HFld, AF>(cs, H, A, "x", bits);
  assert_same_bits(xh, xa);
  CompileProfile p;
  p.name = "radix";
  p.mac_bases = {kMacBasisGF2_256, MacBasis{128, {7, 2, 1, 0}}};
  return compile(cs, p)->report();
}
TEST(GordieHoweMod, MacRadixFromAccMax) {
  has(mac_report(env().g_profile(), 6656),
      "lhs in [0, 26209], rhs in [0, 1], m = 2, quotient in [0, 13104]: 2 "
      "digits, radix B = 114, committed below 114, top 'mac.high' derived "
      "below 115");
  has(mac_report(env().h_profile(), 6656),
      "lhs in [0, 26443], rhs in [0, 1], m = 2, quotient in [0, 13221]: 2 "
      "digits, radix B = 115, committed below 115, top 'mac.high' derived "
      "below 115");
  has(mac_report(env().h_profile(), 8192),
      "radix B = 128, committed below 128, top 'mac.high' derived below 128");
}

// The MAC's odd side needs p > 2w (mac_require_centered), on both sides of
// each width's bound: 251 < 256 < 257 at w = 128, 509 < 512 < 521 at
// w = 256. F_q and Goldilocks^4 pass at both widths.
TEST(GordieHoweMod, MacOddCharacteristicAboveTwiceWidth) {
  auto error = [](const auto &f, size_t w) -> std::string {
    try {
      compiler::mac_require_centered(f, w, "assert_same_bits(x_h, x_a)", "A");
    } catch (const CompileError &e) {
      return e.what();
    }
    return "";
  };
  const Fp<1> f251("251"), f257("257"), f509("509"), f521("521");
  has(error(f251, 128),
      "assert_same_bits(x_h, x_a): the characteristic 251 of the odd domain A "
      "is not above 2w = 256; the MAC needs p > 2w");
  EXPECT_EQ(error(f257, 128), "");
  has(error(f257, 256), "the characteristic 257 of the odd domain A");
  has(error(f509, 256), "the characteristic 509 of the odd domain A is not "
                        "above 2w = 512");
  EXPECT_EQ(error(f521, 256), "");
  for (size_t w : {size_t{128}, size_t{256}}) {
    EXPECT_EQ(error(nf(), w), "");
    EXPECT_EQ(error(af(), w), "");
  }
}

// The MAC's mod-2 check at the bound acc_max = 1 + nch convMax of Conv
// (def:macconv), at its extremes in F_q (q = 12289): 12 chunks of
// GF(2^256) give acc_max = 1 + 12 * 1017 = 12205 < q, one quotient. The
// honest accumulators of all-ones chunks and blind at the all-ones chunk
// power reach acc_max; the check proves them and rejects a forged tag (one
// target bit flipped) and a flipped chunk bit.
TEST(GordieHoweMod, MacCheckAtTheBound) {
  constexpr size_t kW = HF::kBits, kNch = 12;
  const HF &hf = env().hf;
  Sys cs("gh-mac-bound");
  auto &H = cs.domain(env().h_profile(), "H");
  auto &N = cs.domain(env().n_profile(), "N");
  auto r = H.pub(Field{}, "r", kNch);
  auto t = N.pub(Bit{}, "t", kW);
  auto x = N.priv(Bit{}, "x", kNch * kW);
  auto bl = N.priv(Bit{}, "bl", kW);
  assert_mod(bl + ops::MACConv(nf(), r)(x), t, 2, "acc");
  auto c = compile(cs, native_profile());
  has(c->report(), "assert_mod 'acc': lhs in [0, 12205]");
  auto ones = hf.zero(), xb = hf.one();
  for (size_t b = 0; b < kW; ++b) {
    hf.add(ones, xb);
    xb = hf.mulf(xb, hf.of_scalar_field(0b10));
  }
  const HV rv(kNch, ones);
  const std::vector<uint8_t> xbits(kNch * kW, 1);
  auto acc = ops::mac_integer_accumulators<HF>(xbits, rv, ops::mac_taps(hf));
  for (auto &a : acc) a += 1;
  EXPECT_EQ(*std::max_element(acc.begin(), acc.end()), 12205u);
  NV tv;
  for (uint64_t a : acc) tv.push_back(a & 1 ? nf().one() : nf().zero());
  Assignment st, w;
  st.set(r, rv);
  st.set(t, tv);
  w.set(x, NV(kNch * kW, nf().one()));
  w.set(bl, NV(kW, nf().one()));
  EXPECT_TRUE(honest(*c, st, w));
  Assignment forged = st;
  NV tf = tv;
  tf[5] = tf[5] == nf().one() ? nf().zero() : nf().one();
  forged.set(t, tf);
  EXPECT_TRUE(rejected(*c, forged, w, kNoTamper));
  Assignment bad = w;
  NV xf(kNch * kW, nf().one());
  xf[1000] = nf().zero();
  bad.set(x, xf);
  EXPECT_TRUE(rejected(*c, st, bad, kNoTamper));

  // The MAC of 12 chunks into F_q: one group below q, its quotient below
  // 6103 one derived digit (a check below 8192 gives the domain a table
  // above it), under the cap (q - 1 - 1) / 2 + 1 = 6144.
  Sys ms("gh-mac-bound-mac");
  auto &MH = ms.domain(env().h_profile(), "H");
  auto &MN = ms.domain(env().n_profile(), "N");
  auto [xh, xn] = crossing<HF, NF>(ms, MH, MN, "x", kNch * kW);
  assert_same_bits(xh, xn);
  auto z = MN.priv(Subfield{}, "z", 1);
  assert_range(z, 8192, "z");
  auto mc = compile(ms, native_profile());
  has(mc->report(), "nch = 12, convMax = 1017, acc_max = 12205 < p");
  has(mc->report(), "quotient in [0, 6102]: one derived digit 'mac.q' below "
                    "6103 (MaxBound 6144)");
  Assignment mw;
  mw.set(xh, HV(kNch * kW, hf.one()));
  mw.set(z, NV{nf().of_scalar(8191)});
  EXPECT_TRUE(honest(*mc, {}, mw));
  EXPECT_TRUE(rejected(*mc, {}, mw, flip_at<NV>(nf(), xn.id, 3071)));
}

// The 12-chunk MAC into F_q with only a table of TABLE rows (a check below
// TABLE): acc_max = 12205, the quotient below 6103. At 64 rows the least
// key max(B, top) is radix 18 in 3 digits, whose top digit (below 19)
// exceeds its no-wrap cap (q - 1) / (2 * 18^2) = 18; the feasible radix 19
// (top below 17, cap 17) is chosen. At 9 rows no radix of at most 4
// digits has every digit below its cap, so the chunks are grouped. Either
// way the honest proof verifies, and a forged tag and a wrong quotient
// digit are rejected.
std::string mac_small_table(Bound table, const char *digit) {
  constexpr size_t kW = HF::kBits, kNch = 12;
  const HF &hf = env().hf;
  Sys ms("gh-mac-small-table");
  auto &MH = ms.domain(env().h_profile(), "H");
  auto &MN = ms.domain(env().n_profile(), "N");
  auto [xh, xn] = crossing<HF, NF>(ms, MH, MN, "x", kNch * kW);
  assert_same_bits(xh, xn);
  auto z = MN.priv(Subfield{}, "z", 1);
  assert_range(z, table, "z");
  auto mc = compile(ms, native_profile());
  Assignment mw;
  mw.set(xh, HV(kNch * kW, hf.one()));
  mw.set(z, NV{nf().of_scalar(uint64_t(table - 1))});
  EXPECT_TRUE(honest(*mc, {}, mw));
  const size_t tag = id_of(ms, "mac.value");
  EXPECT_TRUE(rejected(*mc, {}, mw, [&hf, tag](size_t at, SysValue &x) {
    if (at != tag) return;
    auto &v = std::get<HV>(x);
    hf.add(v.at(0), hf.one());
  }));
  EXPECT_TRUE(
      rejected(*mc, {}, mw, add_at<NV>(id_of(ms, digit), 0, nf().one())));
  return mc->report();
}
TEST(GordieHoweMod, MacQuotientDigitsBelowTheirCaps) {
  const std::string r = mac_small_table(64, "mac.d0");
  has(r, "quotient in [0, 6102]: 3 digits, radix B = 19, committed below "
         "19, top 'mac.high' derived below 17, Dmax = 17 (digits searched "
         "for the no-wrap condition)");
  const std::string g = mac_small_table(9, "mac.gq");
  has(g, "assert_mod 'mac': no radix with at most 4 digits fits the quotient "
         "below 6103 in the largest table 9 with every digit's bound at most "
         "its no-wrap cap (m = 2, W = 1, p = 12289); its units are grouped");
}

// ---------------------------------------------------------------- range --

// Needles past the group capacity split into groups that share alpha and
// the weights; a group with static and late needles takes one late
// histogram of T counts (T = 64 < 2 S_dyn = 128).
struct SplitSys {
  Sys cs{"gh-range-split"};
  Domain<NF> *N;
  Ref<NF> x, lt;
  explicit SplitSys(size_t nx) {
    N = &cs.domain(env().n_profile(), "N");
    x = N->priv(Subfield{}, "x", nx);
    auto g = N->challenge("g", depends_on(x));
    lt = N->priv(Subfield{}, "lt", 100, depends_on(x, g),
                   [](const NV &x, const NV &) {
                     NV out;
                     for (size_t i = 0; i < 100; ++i)
                       out.push_back(nf().of_scalar(uint64_t(nat_of(nf(), x[i])) ^ 21));
                     return out;
                   });
    assert_range(x, 64, "x");
    assert_range(lt, 64, "lt");
  }
  Assignment witness() const {
    Assignment w;
    NV v;
    for (size_t i = 0; i < x.n; ++i) v.push_back(nf().of_scalar((i * 7) % 64));
    w.set(x, v);
    return w;
  }
};

TEST(GordieHoweRange, SplitGroups) {
  SplitSys m(300);
  CompileProfile p = native_profile();
  p.name = "cap-128";
  p.range.group_capacity = 128;
  auto c = compile(m.cs, p);
  const std::string r = c->report();
  has(r, "table N.64: 4 groups of at most 128 needles (128, 128, 128, 16), "
         "one alpha and one weight table");
  has(r, "table N.64.g0: 128 static and 0 dynamic needles; m0 64, m1 none");
  has(r, "table N.64.g2: 44 static and 84 dynamic needles; one late "
         "histogram of 64");
  has(r, "table N.64.g3: 0 static and 16 dynamic needles; m0 none, m1 64");
  has(r, "the groups share alpha; the largest has 128 needles");
  ASSERT_EQ(m.N->range_tables().size(), 4u);
  EXPECT_EQ(m.N->range_tables()[2].group, 2u);
  Assignment w = m.witness();
  EXPECT_TRUE(honest(*c, {}, w));
  // An out-of-table needle in group 1, and one in the late group.
  {
    NV v;
    for (size_t i = 0; i < 300; ++i)
      v.push_back(nf().of_scalar(i == 200 ? 64 : (i * 7) % 64));
    w.set(m.x, v);
    EXPECT_TRUE(rejected(*c, {}, w, kNoTamper));
    w = m.witness();
  }
  EXPECT_TRUE(rejected(*c, {}, w, add_at<NV>(m.lt.id, 99, nf().of_scalar(64))));
}

// The capacity derived from p: Falcon native's 22467 needles (20163 static
// norm and encoding needles, 2304 late MAC needles) at table 64 of F_q
// fill one group of q - 1 = 12288 static needles and a second of 7875
// static and the 2304 late ones under one late histogram of 64.
TEST(GordieHoweRange, FalconNativeNeedlesInGroupsBelowQ) {
  Sys cs("gh-range-falcon-native");
  auto &H = cs.domain(env().h_profile(), "H");
  auto &N = cs.domain(env().n_profile(), "N");
  auto [ch, ca] = crossing<HF, NF>(cs, H, N, "c", 8192);
  assert_same_bits(ch, ca);
  auto x = N.priv(Subfield{}, "x", 20163);
  assert_range(x, 64, "x");
  auto c = compile(cs, native_profile());
  const std::string r = c->report();
  has(r, "table N.64: 2 groups of at most 12288 needles (12288, 10179), one "
         "alpha and one weight table");
  has(r, "table N.64.g0: 12288 static and 0 dynamic needles; m0 64, m1 none");
  has(r, "table N.64.g1: 7875 static and 2304 dynamic needles; one late "
         "histogram of 64");
  Assignment a;
  a.set(ch, bits_of(H.field(), 8192, 5));
  NV v;
  for (size_t i = 0; i < 20163; ++i) v.push_back(nf().of_scalar(i % 61));
  a.set(x, v);
  EXPECT_TRUE(honest(*c, {}, a));
  v[15000] = nf().of_scalar(64);
  a.set(x, v);
  EXPECT_TRUE(rejected(*c, {}, a, kNoTamper));
}

// The complement realization (one needle n - 1 - v) where Bit types bound
// v: ML-DSA's w1 below 44 from its six bits, and the hint weight
// Sum(h) <= omega.
TEST(GordieHoweRange, ComplementFromBitIntervals) {
  Sys cs("gh-range-complement");
  auto &A = cs.domain(env().a_profile(), "A");
  auto w1 = A.priv(Bit{}, "w1", Shape{8, 6});
  auto h = A.priv(Bit{}, "h", 16);
  assert_range(w1.from_digits(2), 44, "w1");
  assert_range(Sum(h), 7, "hint");
  CompileProfile p;
  p.name = "complement";
  // No direct realizations, which would read w1 itself in a table of 44
  // rows at the same cost.
  p.range.kinds = {RealizationKind::kComplement, RealizationKind::kDigits,
                   RealizationKind::kTwoSided};
  auto c = compile(cs, p);
  const std::string r = c->report();
  has(r, "w1: complement T=44 (n - 1 - v, v in [0, 63]) -> bound 44; 1 "
         "needles");
  has(r, "hint: complement T=44 (n - 1 - v, v in [0, 16]) -> bound 7; 1 "
         "needles");
  Assignment w;
  AV bits(48, af().zero()), hb(16, af().zero());
  for (size_t i = 0; i < 8; ++i)  // w1[i] = 5 i + 3 < 44
    for (size_t b = 0; b < 6; ++b)
      bits[i * 6 + b] = ((5 * i + 3) >> b) & 1 ? af().one() : af().zero();
  for (size_t i = 0; i < 6; ++i) hb[2 * i] = af().one();
  w.set(w1, bits);
  w.set(h, hb);
  EXPECT_TRUE(honest(*c, {}, w));
  // w1[0] = 3 + 48 = 51: bits 4 and 5 set; the needle wraps past the table.
  bits[4] = af().one();
  bits[5] = af().one();
  w.set(w1, bits);
  EXPECT_TRUE(rejected(*c, {}, w, kNoTamper));
  bits[4] = af().zero();
  bits[5] = af().zero();
  w.set(w1, bits);
  // Seven hints.
  hb[1] = af().one();
  w.set(h, hb);
  EXPECT_TRUE(rejected(*c, {}, w, kNoTamper));
}

// Requests that cost nothing: a Bit below 2 and a prime-field value below
// n >= p (by type), a duplicate, and a request a stricter one on the same
// value implies.
TEST(GordieHoweRange, TypeImpliedAndDuplicateRequests) {
  Sys cs("gh-range-free");
  auto &N = cs.domain(env().n_profile(), "N");
  auto b = N.priv(Bit{}, "b", 4);
  auto v = N.priv(Subfield{}, "v", 4);
  auto x = N.priv(Subfield{}, "x", 4);
  assert_range(b, 2, "b2");
  assert_range(v, kQ, "vq");
  assert_range(v, 20000, "vbig");
  assert_range(x, 64, "x64");
  assert_range(x, 64, "x64again");
  assert_range(x, 100, MaxBound{200}, "x100");
  // Direct tables only: two bound digits in 8 rows would make x a view
  // of them, and the witness x = 64 would not be rejected.
  CompileProfile p = native_profile();
  p.range.kinds = {RealizationKind::kDirect};
  auto c = compile(cs, p);
  const std::string r = c->report();
  has(r, "b2: implied (by the value's type), interval [0, 1] -> bound 2");
  has(r, "vq: implied (by the value's type), interval [0, 12288] -> bound 12289");
  has(r, "vbig: implied (by the value's type), interval [0, 12288] -> bound "
         "20000");
  has(r, "x64again: implied (a duplicate of 'x64'), interval [0, 63] -> bound 64");
  has(r, "x100: implied (by 'x64' on the same value), interval [0, 63] -> "
         "bound 100");
  ASSERT_EQ(N.range_tables().size(), 1u);
  EXPECT_EQ(N.range_tables()[0].static_needles, 4u);
  Assignment w;
  w.set(b, NV{nf().one(), nf().zero(), nf().one(), nf().one()});
  w.set(v, NV{nf().of_scalar(12288), nf().one(), nf().zero(), nf().of_scalar(7)});
  w.set(x, NV{nf().of_scalar(63), nf().one(), nf().zero(), nf().of_scalar(7)});
  EXPECT_TRUE(honest(*c, {}, w));
  w.set(x, NV{nf().of_scalar(64), nf().one(), nf().zero(), nf().of_scalar(7)});
  EXPECT_TRUE(rejected(*c, {}, w, kNoTamper));
}

// The range check of a sorted rearrangement: n = 64 values v of
// Goldilocks, each step v[i + 1] - v[i] below B = 2^16. RAISE sets the
// request's table cap to B (max_table).
struct SortedSteps {
  static constexpr size_t n = 64;
  static constexpr uint64_t B = 1 << 16;
  Sys cs{"gh-range-sorted"};
  Ref<AF, Subfield<>, Committed> v;
  explicit SortedSteps(bool raise = false) {
    auto &A = cs.domain(env().a_profile(), "A");
    v = A.priv(Subfield{}, "v", n);
    const auto steps =
        assert_range(v.slice(1, n) - v.slice(0, n - 1), B, "steps");
    if (raise) steps.max_table(B);
  }
  static CompileProfile profile() {
    CompileProfile p;
    p.name = "sorted";
    return p;
  }
  // Steps of 0 to B - 1; with DESCENT, one step of -1.
  Assignment witness(bool descent) const {
    AV x;
    uint64_t at = 5;
    for (size_t i = 0; i < n; ++i) {
      x.push_back(af().of_scalar(at));
      at += (i * 1021 + 7) % B;
    }
    if (descent) {
      x.back() = x[n - 2];
      af().sub(x.back(), af().one());
    }
    Assignment w;
    w.set(v, x);
    return w;
  }
};

// The planner weighs each table's rows against a direct table of 65536
// rows: digits in a small table. Two digits in 2^8 rows (a candidate, the
// square root of B) cost least; four digits in 2^4 rows are within the
// default margin (kDefaultMarginPercent) with fewer rows, so the default
// takes them.
TEST(GordieHoweRange, SortedStepsTakeRootDigits) {
  SortedSteps t;
  auto c = compile(t.cs, SortedSteps::profile());
  const std::string r = c->report();
  const auto &x = c->realization("steps");
  EXPECT_EQ(x.kind, RealizationKind::kDigits);
  EXPECT_EQ(x.table, Bound(1) << 4);
  EXPECT_EQ(x.k, 4u);
  EXPECT_EQ(r.find("warning: range table"), std::string::npos) << r;
  EXPECT_TRUE(honest(*c, {}, t.witness(false)));
  EXPECT_TRUE(rejected(*c, {}, t.witness(true), kNoTamper));
}

// The table cap: with direct realizations only, the 2^16-row table is
// above the policy's cap (2^14 rows) and the compile fails, naming the
// request and the table; the request's max_table admits it, and the report
// lists it as a warning.
TEST(GordieHoweRange, SortedStepsTableCap) {
  CompileProfile p = SortedSteps::profile();
  p.range.kinds = {RealizationKind::kDirect};
  {
    SortedSteps t;
    const std::string e = compile_error(t.cs, p);
    has(e, "range request 'steps'");
    has(e, "direct T=65536: T above the table cap 16384");
  }
  SortedSteps t(true);
  auto c = compile(t.cs, p);
  const std::string r = c->report();
  EXPECT_EQ(c->realization("steps").kind, RealizationKind::kDirect);
  EXPECT_EQ(c->realization("steps").table, Bound(SortedSteps::B));
  has(r, "warning: range table A.65536 has 65536 rows, above the cap 16384 "
         "(max_table: 'steps')");
  EXPECT_TRUE(honest(*c, {}, t.witness(false)));
  EXPECT_TRUE(rejected(*c, {}, t.witness(true), kNoTamper));
}

// One request's realization, for comparing plans.
std::string plan_entry(const RangeRealization &r) {
  return std::string(realization_name(r.kind)) + " T=" + bound_str(r.table) +
         " k=" + std::to_string(r.k) + " N=" + bound_str(r.established) +
         (r.bound ? " bound" : "");
}

// The plan does not depend on the order of the range checks: under 24
// orders of seven checks (two on one value, an interval request, an
// expression their bounds may imply, a check on x + c, and a duplicate),
// every check takes the same realization and the domain the same tables.
TEST(GordieHoweRange, PlanIndependentOfCheckOrder) {
  const std::vector<std::string> names = {"x64", "x1000", "y", "u", "w",
                                          "uw",  "z",     "y2"};
  std::vector<size_t> order = {0, 1, 2, 3, 4, 5, 6, 7};
  std::mt19937 rng(7);
  std::optional<std::map<std::string, std::string>> first;
  for (int trial = 0; trial < 24; ++trial) {
    Sys cs("gh-range-order");
    auto &A = cs.domain(env().a_profile(), "A");
    auto x = A.priv(Subfield{}, "x", 16);
    auto y = A.priv(Subfield{}, "y", 300);
    auto u = A.priv(Subfield{}, "u", 4);
    auto w = A.priv(Subfield{}, "w", 4);
    auto z = A.priv(Subfield{}, "z", 40);
    auto c5 = A.constant("c5", AV(40, af().of_scalar(5)));
    const std::vector<std::function<void()>> checks = {
        [&] { assert_range(x, 64, "x64"); },
        [&] { assert_range(x, 1000, MaxBound{4096}, "x1000"); },
        [&] { assert_range(y, 1 << 12, "y"); },
        [&] { assert_range(u, 128, "u"); },
        [&] { assert_range(w, 128, MaxBound{256}, "w"); },
        [&] { assert_range(u + af().of_scalar(128) * w, 1 << 14, "uw"); },
        [&] { assert_range(z + c5, 4096, "z"); },
        [&] { assert_range(y, 1 << 12, "y2"); },
    };
    for (size_t k : order) checks[k]();
    auto c = compile(cs, CompileProfile{});
    std::map<std::string, std::string> plan;
    for (const auto &nm : names) plan[nm] = plan_entry(c->realization(nm));
    std::string tables;
    for (const auto &tb : A.range_tables())
      tables += " " + bound_str(tb.table);
    plan["tables"] = tables;
    if (!first) {
      first = plan;
    } else {
      EXPECT_EQ(plan, *first) << "trial " << trial;
    }
    std::shuffle(order.begin(), order.end(), rng);
  }
  // Some realization other than the implied and duplicate ones.
  EXPECT_NE((*first)["x64"].find("T="), std::string::npos);
}

// Two checks below 2^16, of 2^10 and of 2^16 values, share one direct
// table of 2^16 rows (1 needle per value and 2^16 rows), in either order:
// two bound digits in 2^8 rows cost 3 per value, and the small check alone
// would take them.
TEST(GordieHoweRange, SmallAndLargeShareOneDirectTable) {
  for (bool small_first : {true, false}) {
    Sys cs("gh-range-share");
    auto &A = cs.domain(env().a_profile(), "A");
    A.max_table(Bound(1) << 16);
    auto a = A.priv(Subfield{}, "a", 1 << 10);
    auto b = A.priv(Subfield{}, "b", 1 << 16);
    if (small_first) assert_range(a, 1 << 16, "a");
    assert_range(b, 1 << 16, "b");
    if (!small_first) assert_range(a, 1 << 16, "a");
    auto c = compile(cs, CompileProfile{});
    for (const char *nm : {"a", "b"}) {
      const auto &r = c->realization(nm);
      EXPECT_EQ(r.kind, RealizationKind::kDirect) << nm;
      EXPECT_EQ(r.table, Bound(1) << 16) << nm;
    }
    ASSERT_EQ(A.range_tables().size(), 1u);
    has(c->report(), "range planning of domain A: |C| = 4 candidate tables "
                     "{16, 41, 256, 65536}, 16 subsets");
  }
}

// The quad terms of the compile report's circuit (one domain).
size_t quad_terms(const std::string &r) {
  std::smatch m;
  if (!std::regex_search(r, m, std::regex(R"(quad_terms=(\d+))"))) {
    ADD_FAILURE() << "no quad_terms\n" << r;
    return 0;
  }
  return std::stoul(m[1]);
}

// The terms of domain A's circuit with N values below B in a direct table
// of B rows, its only constraint.
size_t direct_terms(size_t n, Bound b) {
  Sys cs("gh-range-terms");
  auto &A = cs.domain(env().a_profile(), "A");
  auto v = A.priv(Subfield{}, "v", n);
  assert_range(v, b, "v");
  CompileProfile p;
  p.range.kinds = {RealizationKind::kDirect};
  auto c = compile(cs, p);
  EXPECT_EQ(c->realization("v").table, b);
  return quad_terms(c->report());
}

// The planner's quad terms per needle and per table row are the fraction
// tree's at the margin: 1024 more needles (6146 terms: 6 each, and 2 for
// the tree's added level), and 64 more rows (64 terms).
TEST(GordieHoweRange, FractionTreeTermsPerNeedleAndRow) {
  const size_t base = direct_terms(1024, 64);
  const size_t needles = direct_terms(2048, 64) - base;
  const size_t rows = direct_terms(1024, 128) - base;
  EXPECT_EQ(Bound((needles + 512) / 1024),
            compiler::range_internal::kNeedleTerms);
  EXPECT_EQ(Bound(rows), 64 * compiler::range_internal::kRowTerms);
}

// Domain A with N values below 2^12 under RATES (none: unmeasured): the
// realization of 'v' and the report.
RangeRealization weighted_choice(size_t n,
                                 const compiler::PlacementRates *rates,
                                 std::string &report) {
  Sys cs("gh-range-weighted");
  auto prof = env().a_profile();
  if (rates) prof.rates = *rates;
  auto &A = cs.domain(prof, "A");
  auto v = A.priv(Subfield{}, "v", n);
  assert_range(v, 1 << 12, "v");
  auto c = compile(cs, CompileProfile{});
  report = c->report();
  return c->realization("v");
}

// The planner weighs committed digits, needles and table rows by the
// domain's rates. Values below 2^12 take a direct table of 4096 rows (one
// needle each) or two bound digits in 64 rows (two needles and one net
// committed coordinate each). Unmeasured, each costs 1: 1700 values take
// the digits (5164 against 5796) and 3000 the direct table (7096 against
// 9064). Under rates where a quad term costs ten committed coordinates
// (gkr_term 1, commit_sub 0.1: needle 6, digit 0.1, row 1.1 us), 1700
// values take the direct table (14705.6 us against 20640.4 us); where a
// committed coordinate costs a hundred terms (commit_sub 1, gkr_term 0.01:
// needle 0.06, digit 1, row 1.01 us), 3000 values take the digits
// (3424.64 us against 4316.96 us).
TEST(GordieHoweRange, WeightsChangeTheTables) {
  std::string r;
  auto digits64 = [](const RangeRealization &x) {
    EXPECT_EQ(x.kind, RealizationKind::kDigits);
    EXPECT_EQ(x.table, Bound(64));
    EXPECT_EQ(x.k, 2u);
    EXPECT_TRUE(x.bound);
  };
  auto direct4096 = [](const RangeRealization &x) {
    EXPECT_EQ(x.kind, RealizationKind::kDirect);
    EXPECT_EQ(x.table, Bound(4096));
  };
  digits64(weighted_choice(1700, nullptr, r));
  has(r, "tables {64}, cost 5164");
  direct4096(weighted_choice(3000, nullptr, r));
  has(r, "tables {4096}, cost 7096");

  // Measured rates weigh A's packing chains: both at one cost.
  compiler::StageRates chains;
  chains.chains = {{{1, 4}, 1, 1, 1, 1, 1, 1}, {{1, 2, 4}, 1, 1, 1, 1, 1, 1}};
  compiler::PlacementRates terms;
  terms.commit_sub = 0.1;
  terms.gkr_term = 1;
  terms.stage = chains;
  direct4096(weighted_choice(1700, &terms, r));
  has(r, "tables {4096}, cost 14.706 ms (modeled)");

  compiler::PlacementRates commits;
  commits.commit_sub = 1;
  commits.gkr_term = 0.01;
  commits.stage = chains;
  digits64(weighted_choice(3000, &commits, r));
  has(r, "tables {64}, cost 3.425 ms (modeled)");
}

// The cost model's units: unmeasured, a committed coordinate, a needle and
// a row cost 1; measured, the commit rate of the domain's range values (the
// subfield's, or the field's when it is prime), kNeedleTerms terms and a
// row's count and kRowTerms terms, in 10^-6 us.
TEST(GordieHoweRange, CostModelUnits) {
  using compiler::range_internal::range_costs;
  compiler::PlacementRates none;
  const auto u = range_costs(none, true);
  EXPECT_FALSE(u.measured);
  EXPECT_EQ(u.coord, Bound(1));
  EXPECT_EQ(u.needle, Bound(1));
  EXPECT_EQ(u.row, Bound(1));
  compiler::PlacementRates r;
  r.commit_sub = 1.06;
  r.commit_full = 4.52;
  r.gkr_term = 0.380;
  const auto sub = range_costs(r, true);
  EXPECT_TRUE(sub.measured);
  EXPECT_EQ(sub.coord, Bound(1060000));
  EXPECT_EQ(sub.needle, Bound(2280000));
  EXPECT_EQ(sub.row, Bound(1440000));
  const auto full = range_costs(r, false);
  EXPECT_EQ(full.coord, Bound(4520000));
  EXPECT_EQ(full.needle, Bound(2280000));
  EXPECT_EQ(full.row, Bound(4900000));
}

TEST(GordieHoweMod, CompileErrors) {
  // assert_mod in characteristic 2 is a C++ compile error.
  {
    // A left side without a range request: x has [0, p - 1], which
    // no grouping of one unit fits.
    Sys cs("gh-mod-unbounded");
    auto &A = cs.domain(env().a_profile(), "A");
    auto x = A.priv(Subfield{}, "x", 2);
    auto y = A.priv(Bit{}, "y", 2);
    assert_mod(x, y, 3, "u");
    EXPECT_NE(compile_error(cs).find("assert_mod 'u': the left side's "
                                    "interval [0, 18446744069414584320] "
                                    "reaches p"),
              std::string::npos)
        << compile_error(cs);
  }
  {
    // A MAC whose chunks fit no group: at table 4 and four digits a group
    // holds sums below 512, under one chunk's convMax 1017.
    Sys cs("gh-mac-nogroup");
    auto &H = cs.domain(env().h_profile(), "H");
    auto &N = cs.domain(env().n_profile(), "N");
    auto [xh, xa] = crossing<HF, NF>(cs, H, N, "x", 8192);
    assert_same_bits(xh, xa);
    CompileProfile p = native_profile();
    p.name = "table-4";
    p.range.max_table = 4;
    EXPECT_NE(compile_error(cs, p).find("assert_mod 'mac': the left side's "
                                       "interval [0, 32545] reaches p = 12289, "
                                       "and no grouping of its units fits a "
                                       "candidate table"),
              std::string::npos)
        << compile_error(cs, p);
  }
  {
    // A modulus below 2.
    Sys cs("gh-mod-one");
    auto &A = cs.domain(env().a_profile(), "A");
    auto x = A.priv(Bit{}, "x", 2);
    assert_mod(x, x, 1, "m1");
    EXPECT_NE(compile_error(cs).find("the modulus is below 2"), std::string::npos);
  }
}

}  // namespace
}  // namespace proofs::gordiehowe
