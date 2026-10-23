// Copyright 2026 Chad Sharp and Paul Grubbs
// SPDX-License-Identifier: Apache-2.0

// GordieHowe tests (gordiehowe_test binary): the structural checks of
// compile(), pads and their copies, shapes, views and generator forms.

#include "gordiehowe/compile_error_testing.h"
#include "gordiehowe/tests/gordiehowe_test.h"

namespace proofs::gordiehowe {
namespace {

// --------------------------------------------------- structural rejects --

// A small system with one circuit and a challenge.
struct Small {
  Sys cs{"gordiehowe-m1-negative"};
  Domain<AF> *A;
  Ref<AF, Subfield<>, Committed> x, z;
  Ref<AF> gamma;
  Small() {
    const AF *pf = &env().af;
    A = &cs.domain(env().profile(), "A");
    x = A->priv(Subfield{}, "x", 2);
    z = A->priv(Subfield{}, "z", 2, depends_on(x), [pf](const Vec &x) {
      return Vec{pf->mulf(x[0], x[0]), pf->mulf(x[1], x[1])};
    });
    assert_equal(z, x * x, "z = x^2").pin(Placement::kCircuit);
    gamma = A->challenge("gamma", depends_on(x, z));
  }
  template <class T = Field>
  Ref<AF, T, Committed> late(const std::string &nm, Ref<AF> dep,
                             MaskedBy mb = {}) {
    const AF *pf = &env().af;
    return L::priv(*A, T{}, nm, 1, depends_on(dep, gamma),
                 [pf](const Vec &a, const Vec &g) { return Vec{pf->addf(a[0], g[0])}; },
                 mb);
  }
  // A generator that copies X.
  Ref<AF> copy(const std::string &nm, Ref<AF> x) {
    return A->priv(Field{}, nm, 1, depends_on(x), [](const Vec &v) { return v; });
  }
  // A pad copy of P, filled by the core.
  Ref<AF> pcopy(const std::string &nm, Ref<AF> p) {
    return L::pad_copy(*A, nm, p, Identity::identity());
  }
};

TEST(GordieHowe, SmallSystemCompiles) {
  // A pad copy feeding a later message is accepted.
  Small ok;
  auto P2 = L::pad(ok.cs, *ok.A, Field{});
  auto c2 = ok.pcopy("c", P2);
  ok.late("first", ok.x, L::masked_by(P2));
  ok.late("second", c2);
  EXPECT_EQ(core_error(ok.cs), "");
}

TEST(GordieHowe, RejectsMessageDependingOnItsOwnPad) {
  Small m;
  auto P = L::pad(m.cs, *m.A, Field{});
  auto c = m.pcopy("c", P);
  m.late("a", c, L::masked_by(P));
  const std::string err = core_error(m.cs);
  EXPECT_NE(err.find("message 'a' depends on its own pad"), std::string::npos)
      << err;
}

TEST(GordieHowe, RejectsMessageDependingOnALaterPad) {
  {
    // Same phase: a precedes b in declaration order and reads b's pad.
    Small m;
    auto Q = L::pad(m.cs, *m.A, Field{});
    auto c = m.pcopy("c", Q);
    m.late("a", c);
    m.late("b", m.x, L::masked_by(Q));
    const std::string err = core_error(m.cs);
    EXPECT_NE(err.find("message 'a' depends on the pad"), std::string::npos) << err;
    EXPECT_NE(err.find("of the later message 'b'"), std::string::npos) << err;
  }
  {
    // A phase-1 message reads the pad of a phase-2 message.
    Small m;
    auto Q = L::pad(m.cs, *m.A, Field{});
    auto c = m.pcopy("c", Q);
    auto a = m.late("a", c);
    auto d = m.A->challenge("delta", depends_on(a));
    L::priv(*m.A, Field{}, "b", 1, depends_on(d),
                [](const Vec &d) { return d; }, L::masked_by(Q));
    const std::string err = core_error(m.cs);
    EXPECT_NE(err.find("of the later message 'b'"), std::string::npos) << err;
  }
  {
    // Transitively: a1 reads a generator's copy of a pad copy of a2's pad.
    Small m;
    auto Q = L::pad(m.cs, *m.A, Field{});
    auto c = m.pcopy("c", Q);
    auto g = m.late("g", c);  // a phase-1 generator reading the pad copy
    auto a1 = m.late("a1", g);
    m.late("a2", m.x, L::masked_by(Q));
    const std::string err = core_error(m.cs);
    EXPECT_NE(err.find("message 'g' depends on the pad"), std::string::npos)
        << err;
    (void)a1;
  }
}

// A public message t1 = a1 + P1 depends on P1, the pad of the earlier
// message a1, so a message that reads t1 is accepted: a message reading a
// public message always follows it.
TEST(GordieHowe, MessageReadingAPublicMessageCompiles) {
  Small m;
  auto P1 = L::pad(m.cs, *m.A, Field{});
  auto a1 = m.late("a1", m.x, L::masked_by(P1));
  auto t1 = L::public_message(m.cs, a1);
  m.late("a2", t1);
  EXPECT_EQ(core_error(m.cs), "");
}

// No closure receives a pad: a pad listed as a generator's dependency is a
// compile error.
TEST(GordieHowe, RejectsPadAsGeneratorDependency) {
  Small m;
  auto P = L::pad(m.cs, *m.A, Field{});
  m.copy("c", P);
  m.late("a", m.x, L::masked_by(P));
  const std::string err = core_error(m.cs);
  EXPECT_NE(err.find("advice 'c' lists the pad '" + std::string("pad")),
            std::string::npos)
      << err;
  EXPECT_NE(err.find("a generator never reads a pad"), std::string::npos)
      << err;
}

// A generator that reads a pad copy runs before the pad's message is formed
// (here in phase 0): it could stash the pad for that message's generator.
TEST(GordieHowe, RejectsGeneratorReadingAPadBeforeItsMessage) {
  Small m;
  auto P = L::pad(m.cs, *m.A, Field{});
  auto c = m.pcopy("c", P);
  m.copy("g", c);  // phase 0
  m.late("a", m.x, L::masked_by(P));
  const std::string err = core_error(m.cs);
  EXPECT_NE(err.find("generator 'g' reads the pad"), std::string::npos) << err;
  EXPECT_NE(err.find("of the message 'a', which is formed after it"),
            std::string::npos)
      << err;
}

TEST(GordieHowe, RejectsBadPadCopies) {
  {
    // A copy of a value that is not a pad.
    Small m;
    L::pad_copy(*m.A, "c", m.z, Identity::identity());
    EXPECT_NE(core_error(m.cs).find("pad_copy 'c' copies 'z', which is not "
                                      "a pad"),
              std::string::npos)
        << core_error(m.cs);
  }
  // A one-field map across two field objects needs two domains of one
  // field, which a system does not have.
  {
    // An affine map of the wrong shape.
    const AF &af = env().af;
    EXPECT_THROW(Identity::affine(af, 2, 2, Vec(3, af.one()), Vec(2)),
                 CompileError);
    Small m;
    auto P = L::pad(m.cs, *m.A, Field{}, 3);
    EXPECT_THROW(L::pad_copy(*m.A, "c", P,
                             Identity::affine(af, 1, 2, Vec(2, af.one()),
                                              Vec(1, af.zero()))),
                 CompileError);
  }
}

// Two challenges whose phases form a cycle: a is computed from beta and
// read with alpha, b computed from alpha and read with beta, so alpha comes
// after beta and beta after alpha. The error names the cycle.
TEST(GordieHowe, NamesAPhaseCycle) {
  Small m;
  auto alpha = m.A->challenge("alpha");
  auto beta = m.A->challenge("beta");
  auto a = m.A->priv(Field{}, "a", 1, depends_on(m.x, beta),
                     [](const Vec &x, const Vec &) { return Vec{x[0]}; });
  auto b = m.A->priv(Field{}, "b", 1, depends_on(m.x, alpha),
                     [](const Vec &x, const Vec &) { return Vec{x[0]}; });
  assert_zero(alpha * a, "alpha a").pin(Placement::kCircuit);
  assert_zero(beta * b, "beta b").pin(Placement::kCircuit);
  const std::string err = core_error(m.cs);
  EXPECT_NE(err.find("the challenges' phases form a cycle"), std::string::npos)
      << err;
  EXPECT_NE(err.find("alpha tests a (computed from beta)"), std::string::npos)
      << err;
  EXPECT_NE(err.find("beta tests b (computed from alpha)"), std::string::npos)
      << err;
}

// Tests inference. alpha and beta are declared with the hint depends_on(x); y
// is computed from beta, independently of alpha, and a row reads alpha
// (through its powers) with y and x. alpha therefore tests y as well, and
// is drawn after y: phase 2, where the hint alone gave phase 1. With y
// computed from alpha, alpha stays in phase 1 and does not test y.
TEST(GordieHowe, InferredTestsOrderAChallengeAfterWhatItReads) {
  for (bool from_alpha : {false, true}) {
    Small m;
    const AF *pf = &env().af;
    auto alpha = m.A->challenge("alpha", depends_on(m.x));
    auto beta = m.A->challenge("beta", depends_on(m.x));
    // [alpha, alpha^2], a public expression the compiler lifts.
    const Expr<AF> a(alpha);
    const auto powers = a.concat(a * a).named("alpha.powers");
    auto src = from_alpha ? alpha : beta;
    auto y = m.A->priv(Field{}, "y", 2, depends_on(src),
                         [](const Vec &c) { return Vec{c[0], c[0]}; });
    assert_zero(powers * (y - m.x), "alpha^i (y_i - x_i)");
    auto c = compile(m.cs);
    EXPECT_EQ(c->phase(alpha), from_alpha ? 1u : 2u) << from_alpha;
    EXPECT_EQ(c->phase(beta), 1u);
    EXPECT_NE(c->report().find(from_alpha
                                   ? "challenge alpha n=1 phase=1"
                                   : "challenge alpha n=1 phase=2"),
              std::string::npos)
        << c->report();
  }
}

// (Pub-chal): a public value the application computes by a closure from a
// challenge fails compilation; the same value written as an expression is
// lifted into a public value both parties evaluate, with its degree in the
// challenge recorded, and placed on the linear test as a coefficient.
TEST(GordieHowe, PublicValuesFromChallengesAreExpressions) {
  {
    Small m;
    const AF *pf = &env().af;
    auto sq = m.A->pub(Field{}, "gamma.sq", 1, depends_on(m.gamma),
                       computes("square", {}), [pf](const Vec &g) {
                         return Vec{pf->mulf(g[0], g[0])};
                       });
    auto y = m.late("y", m.x);
    assert_zero(sq * m.x - y, "y = gamma^2 x");
    const std::string err = core_error(m.cs);
    EXPECT_NE(err.find("public value 'gamma.sq' is computed by a closure "
                       "from the challenge 'gamma'"),
              std::string::npos)
        << err;
  }
  Small m;
  const AF *pf = &env().af;
  const Expr<AF> g(m.gamma);
  const auto sq = (g * g).named("gamma.sq");
  auto y = L::priv(*m.A, Field{}, "y", 2, depends_on(m.x, m.gamma),
                   [pf](const Vec &x, const Vec &c) {
                     const AElt s = pf->mulf(c[0], c[0]);
                     return Vec{pf->mulf(s, x[0]), pf->mulf(s, x[1])};
                   });
  assert_zero(sq * m.x - y, "y = gamma^2 x");
  auto c = compile(m.cs);
  const std::string r = c->report();
  EXPECT_NE(r.find("gamma.sq"), std::string::npos) << r;
  bool found = false;
  for (const auto &rec : m.cs.graph().records.gadgets)
    if (rec.kind == "public-expression" && rec.name == "gamma.sq") {
      found = true;
      EXPECT_EQ(rec.domain, "A");
      bool degree = false;
      for (const auto &[k, v] : rec.params)
        if (k == "degree:gamma") degree = v == 2;
      EXPECT_TRUE(degree);
    }
  EXPECT_TRUE(found);
  Assignment w;
  w.set(m.x, Vec{env().af.of_scalar(3), env().af.of_scalar(5)});
  auto prep = c->prepare({});
  SecureRandomEngine rng;
  EXPECT_TRUE(prep.verify(prep.prove(w, rng)));
}

// A challenge of the source program has the degree bound the sum of the
// degrees in it of the predicates that read it. Here gamma^2 x (a lifted
// public expression of degree 2) and (gamma - x_0)(gamma - x_1) (a product
// over two coordinates, degree 2) give 4, from 2 predicates.
TEST(GordieHoweDegree, UserPredicatesReadingAChallengeAreCounted) {
  Small m;
  const AF *pf = &env().af;
  const Expr<AF> g(m.gamma);
  const auto sq = (g * g).named("gamma.sq");
  auto y = L::priv(*m.A, Field{}, "y", 2, depends_on(m.x, m.gamma),
                   [pf](const Vec &x, const Vec &c) {
                     const AElt s = pf->mulf(c[0], c[0]);
                     return Vec{pf->mulf(s, x[0]), pf->mulf(s, x[1])};
                   });
  assert_zero(sq * m.x - y, "y = gamma^2 x");
  auto w = L::priv(*m.A, Field{}, "w", 1, depends_on(m.x, m.gamma),
                   [pf](const Vec &x, const Vec &c) {
                     return Vec{pf->mulf(pf->subf(c[0], x[0]),
                                         pf->subf(c[0], x[1]))};
                   });
  assert_equal((g - m.x).prod(), w, "w = (gamma - x_0)(gamma - x_1)");
  auto c = compile(m.cs);
  Bound bound = 0;
  size_t records = 0;
  for (const auto &ch : c->records().charges)
    if (ch.label == "gamma") {
      bound = ch.degree;
      ++records;
    }
  EXPECT_EQ(records, 1u);
  EXPECT_EQ(bound, Bound(4));
  const std::string r = c->report();
  EXPECT_NE(r.find("degree bound gamma: 4 from 2 predicates"), std::string::npos)
      << r;
  Assignment wa;
  wa.set(m.x, Vec{env().af.of_scalar(3), env().af.of_scalar(5)});
  auto prep = c->prepare({});
  SecureRandomEngine rng;
  EXPECT_TRUE(prep.verify(prep.prove(wa, rng)));
}

// (Pub-chal): a closure over a challenge of the source program fails
// compilation even at the compiler tier, outside the core realizations,
// since its degree in the challenge is unknown.
TEST(GordieHoweDegree, ClosureOverASourceChallengeOutsideARealizationFails) {
  Small m;
  const AF *pf = &env().af;
  auto cube = L::pub(m.cs, env().af, Field{}, "gamma.cube", 1,
                     depends_on(m.gamma), computes("cube", {}),
                     [pf](const Vec &g) {
                       return Vec{pf->mulf(g[0], pf->mulf(g[0], g[0]))};
                     });
  auto y = m.late("y", m.x);
  assert_zero(cube * m.x[0] - y, "y = gamma^3 x_0");
  const std::string err = core_error(m.cs);
  EXPECT_NE(err.find("public value 'gamma.cube' is computed by a closure "
                     "from the challenge 'gamma', which no core realization "
                     "(the MAC, assert_in, the range lookups) draws"),
            std::string::npos)
      << err;
}

// Every challenge of the end-to-end system declared without depends_on(...):
// the inferred tests give the same phases and messages.
TEST(GordieHowe, InferredTestsMatchTheDeclaredOnes) {
  TestSystem t;
  auto c = compile(t.cs);
  // gamma: declared x, y, z, bits, blind, pcopy; the constraints that read
  // it read pcopy (v2 = pcopy + gamma, w = gamma), so the union keeps the
  // declaration. delta: declared u, v2, acc, lowbit; "e = delta * u"
  // reads u, whose pad P it adds.
  const auto &N = t.cs.graph().nodes;
  (void)N;
  EXPECT_EQ(c->phase(t.gamma), 1u);
  EXPECT_EQ(c->phase(t.delta), 2u);
  const std::string r = c->report();
  EXPECT_NE(r.find("challenge delta n=1 phase=2"), std::string::npos) << r;
}

// An operator over a private value inside a derived view: a compile error.
// (Values of one domain read by another domain's constraints need two
// domains of one field, which a system does not have.)
TEST(GordieHowe, RejectsCrossDomainReads) {
  {
    // Through an erased handle (a typed committed parameter is a C++
    // compile error).
    Small m;
    auto d = m.A->derive("d", ops::NegacyclicConv(Ref<AF>(m.z))(m.x));
    m.A->affine("d = 0", d);
    EXPECT_NE(core_error(m.cs).find("operator 'negacyclic_conv' applied to "
                                      "'x' reads private value 'z'"),
              std::string::npos)
        << core_error(m.cs);
  }
}

// An operator whose instantiation contradicts its declared shape is a clear
// runtime error when the rows are built.
TEST(GordieHowe, OperatorShapeMismatchIsAnError) {
  const AF &af = env().af;
  Small m;
  const Op<AF> liar = linear_operator<AF>({
      .name = "liar",
      .rows = 2,
      .cols = 2,
      .make =
          [](const AF &f) {
            return std::make_shared<DiagonalOperator<AF>>(f, Vec(3, f.one()));
          },
      .field = &af,
  });
  m.A->affine("liar(x) = liar(x)", liar(m.x) - liar(m.x));
  auto c = compile(m.cs);
  auto prep = c->prepare(Assignment{});
  Assignment w;
  w.set(m.x, Vec{af.of_scalar(3), af.of_scalar(5)});
  SecureRandomEngine rng;
  try {
    prep.prove(w, rng);
    ADD_FAILURE() << "the prover accepted a mis-shaped operator";
  } catch (const std::runtime_error &e) {
    EXPECT_NE(std::string(e.what()).find(
                  "operator 'liar' declares 2x2 but instantiates as 3x3"),
              std::string::npos)
        << e.what();
  }
}

// A challenge whose decoding stream runs past the Fiat-Shamir stream budget
// (fs_stream_budget) is refused by the prover.
TEST(GordieHowe, ChallengeStreamBudgetIsEnforced) {
  const AF &af = env().af;
  const size_t n = fs_stream_budget<SHA384>() / AF::kBytes + 1;
  Small m;
  m.A->challenge("huge", Field{}, n, depends_on(m.x));
  auto c = compile(m.cs);
  auto prep = c->prepare(Assignment{});
  Assignment w;
  w.set(m.x, Vec{af.of_scalar(3), af.of_scalar(5)});
  SecureRandomEngine rng;
  try {
    prep.prove(w, rng);
    ADD_FAILURE() << "the prover drew a challenge past its stream budget";
  } catch (const std::runtime_error &e) {
    EXPECT_NE(std::string(e.what()).find(
                  "challenge 'huge' read past its stream budget"),
              std::string::npos)
        << e.what();
  }
}

// The system digest identifies a public computation by its declared name
// and parameters, and a challenge by its field.
TEST(GordieHowe, DigestIdentifiesComputationsAndFields) {
  const AF *pf = &env().af;
  auto digest = [pf](const Computes &id, bool mac_field) {
    Small m;
    // A public computation of a statement value (a closure over a
    // challenge is a core realization's alone, (Pub-chal)).
    auto s = m.A->pub(Field{}, "s", 1);
    auto g = m.A->pub(Field{}, "g", 1, depends_on(s), id,
                                [](const Vec &g) { return g; });
    assert_zero((m.z[0] - m.x[0] * m.x[0]) * g[0], "(z - x^2) g = 0")
        .pin(Placement::kCircuit);
    if (mac_field)
      L::challenge(m.cs, env().mf, "beta", depends_on(m.x));
    else
      m.A->challenge("beta", depends_on(m.x));
    return compile(m.cs)->digest();
  };
  const auto base = digest(computes("copy", {1}), false);
  EXPECT_EQ(base, digest(computes("copy", {1}), false));
  EXPECT_NE(base, digest(computes("copy", {2}), false));
  EXPECT_NE(base, digest(computes("negate", {1}), false));
  EXPECT_NE(base, digest(computes("copy", {1}), true));
}

TEST(GordieHowe, RejectsLateVariableInQuadraticTriple) {
  Small m;
  auto a = m.late("a", m.x);
  m.A->quadratic(a, a, a);
  const std::string err = core_error(m.cs);
  EXPECT_NE(err.find("late variable 'a' (phase 1) in a quadratic triple"),
            std::string::npos)
      << err;
}

TEST(GordieHowe, RejectsSubfieldPadMaskingFieldValue) {
  Small m;
  auto P = L::pad(m.cs, *m.A, Subfield{});
  m.late<Field>("a", m.x, L::masked_by(P));
  const std::string err = core_error(m.cs);
  EXPECT_NE(err.find("a pad uniform over the subfield space cannot mask the "
                     "Field value 'a'"),
            std::string::npos)
      << err;
  // A Bit value in odd characteristic is masked by a prime-field pad, here
  // the Goldilocks source subfield: a Subfield pad is accepted for it.
  Small ok;
  auto P2 = L::pad(ok.cs, *ok.A, Subfield{});
  const AF *pf = &env().af;
  L::priv(*ok.A, Bit{}, "b", 1, depends_on(ok.gamma),
               [pf](const Vec &) { return Vec{pf->one()}; }, L::masked_by(P2));
  EXPECT_EQ(core_error(ok.cs), "");
}

// A value computed from a challenge is late by inference alone: it needs
// no annotation, and the core gives it a pad.
TEST(GordieHowe, InfersLateValueWithoutAnnotation) {
  Small m;
  auto beta = m.A->challenge("beta", depends_on(m.x));
  auto w = m.A->derive("w", beta);
  auto v = m.A->priv(Field{}, "v", 1, depends_on(w),
                    [](const Vec &w) { return w; });
  EXPECT_EQ(core_error(m.cs), "");
  const auto c = compile(m.cs);
  EXPECT_TRUE(c->late(v));
  EXPECT_EQ(c->phase(v), 1u);
}

TEST(GordieHowe, RejectsPadOwnershipViolations) {
  {
    Small m;
    auto P = L::pad(m.cs, *m.A, Field{});
    m.late("a", m.x, L::masked_by(P));
    m.late("b", m.z, L::masked_by(P));
    EXPECT_NE(core_error(m.cs).find("masks more than one message"),
              std::string::npos);
  }
  {
    Small m;
    L::pad(m.cs, *m.A, Field{});
    EXPECT_NE(core_error(m.cs).find("masks no message"), std::string::npos);
  }
  {
    Small m;
    auto P = L::pad(m.cs, *m.A, Field{});
    L::priv(*m.A, Field{}, "c", 1, depends_on(m.x),
                [](const Vec &x) { return Vec{x[0]}; }, L::masked_by(P));
    EXPECT_NE(core_error(m.cs).find("masked_by applies to late values only"),
              std::string::npos);
  }
}

TEST(GordieHowe, RejectsChallengeTestingNothing) {
  Small m;
  m.A->challenge("idle", depends_on());
  EXPECT_NE(core_error(m.cs).find("challenge 'idle' tests no value"),
            std::string::npos);
}

TEST(GordieHowe, RejectsDuplicateChallengeLabels) {
  Small m;
  m.A->challenge("gamma", depends_on(m.z));
  EXPECT_NE(core_error(m.cs).find("two challenges share the label 'gamma'"),
            std::string::npos);
}

// A pad that only a pad copy reads masks no message, and is unused.
TEST(GordieHowe, RejectsPadOnlyCopied) {
  Small m;
  auto P = L::pad(m.cs, *m.A, Field{});
  m.pcopy("c", P);
  EXPECT_NE(core_error(m.cs).find("masks no message"), std::string::npos);
}

// DomainProfile::prime against the field: Goldilocks^4 has odd
// characteristic, so a GF(2) prime field (and GF(2) pads on Bit values) is
// rejected.
TEST(GordieHowe, RejectsPrimeFieldMismatch) {
  auto p = env().profile();
  p.prime = Space::kPrime;
  Small m;  // a valid system, then the same with the wrong profile
  EXPECT_EQ(core_error(m.cs), "");
  Sys cs("gf2-in-odd-characteristic");
  auto &A = cs.domain(p, "A");
  auto x = A.priv(Field{}, "x", 2);
  assert_zero(x[0] * x[1], "x0 x1 = 0").pin(Placement::kCircuit);
  EXPECT_NE(core_error(cs).find("domain A has odd characteristic, so its "
                                  "prime field is not GF(2)"),
            std::string::npos)
      << core_error(cs);
}

TEST(GordieHowe, ReportChecksSubfield) {
  // Relative packing and the prefix subfield step establish Subfield
  // membership.
  Small m;
  auto c = compile(m.cs);
  EXPECT_NE(c->report().find("private_input x @A n=2 type=Subfield checked "
                             "(Subfield membership: relative packing) phase=0"),
            std::string::npos)
      << c->report();
  EXPECT_EQ(c->report().find("unchecked"), std::string::npos) << c->report();
  EXPECT_NE(c->report().find("prefix subfield test on"), std::string::npos)
      << c->report();
}

// Shapes and views: rows, slices, reversal, a dropped axis, stacking and
// interleaving read the right coordinates in generators, affine rows and
// circuits; an elementwise generator broadcasts a [3] value over [2][3];
// from_digits acts on the last axis; a scalar broadcasts in an affine
// expression; concat_public joins public values.
TEST(GordieHowe, ShapesAndViews) {
  const AF &af = env().af;
  Sys cs("gh-shapes");
  auto &A = cs.domain(env().profile(), "A");
  auto x = A.priv(Subfield{}, "x", Shape{2, 3});  // 1 2 3 / 4 5 6
  auto k = A.pub(Subfield{}, "k", 3);         // 10 20 30
  auto q = A.pub(Field{}, "q", 2);            // 5, 10
  auto d = A.priv(Bit{}, "d", Shape{2, 4});       // 5 = 1010, 10
  auto z = A.priv(Subfield{}, "z", 3);
  auto seven = A.constant("seven", Vec{af.of_scalar(7)});
  // y[i][j] = x[i][j] + k[j]: k broadcasts over the rows.
  auto y = A.priv(Subfield{}, "y", Shape{2, 3}, depends_on(x, k),
                                  nat([](NatInt a, NatInt b) { return a + b; }));
  auto r1 = x[1];              // 4 5 6
  auto sl = x.slice(1, 3, 1);      // 2 3 / 5 6
  auto rv = x.reverse(1);          // 3 2 1 / 6 5 4
  auto c0 = x.at(1, 0);            // 1 4
  auto st = stack(c0, c0);         // [2][2]: 1 1 / 4 4
  auto il = interleave(c0, x.at(1, 2));  // 1 3 4 6
  auto ze = c0.zero_extend(4);     // 1 4 0 0
  auto pk = concat_public(k, q);   // 10 20 30 5 10
  EXPECT_EQ(r1.dims(), (std::vector<size_t>{3}));
  EXPECT_EQ(sl.dims(), (std::vector<size_t>{2, 2}));
  EXPECT_EQ(st.dims(), (std::vector<size_t>{2, 2}));
  EXPECT_THROW(x.reshape({4, 2}), CompileError);
  A.affine("y - x - 10 = ...", y[0] - x[0] - k);
  A.affine("digits", d.from_digits(2) - q);
  A.affine("z = 7", z - seven);
  L::gkr(A, "views", depends_on(r1, sl, rv, st, il, ze, pk, x),
        [&af](const auto &lc, const auto &r1, const auto &sl,
              const auto &rv, const auto &st, const auto &il,
              const auto &ze, const auto &pk, const auto &x) {
          auto eq = [&](size_t w, uint64_t v) {
            lc.assert_eq(w, lc.konst(af.of_scalar(v)));
          };
          eq(r1[0], 4);
          eq(sl(1, 0), 5);
          eq(rv.row(1)[0], 6);
          eq(st(1, 1), 4);
          eq(il[3], 6);
          eq(ze[1], 4);
          eq(ze[3], 0);
          eq(pk[3], 5);
          lc.assert_eq(rv(0, 0), x(0, 2));
        });
  auto c = compile(cs);
  Assignment st0, w;
  auto vec = [&](std::initializer_list<uint64_t> v) {
    Vec o;
    for (uint64_t a : v) o.push_back(af.of_scalar(a));
    return o;
  };
  st0.set(k, vec({10, 20, 30})).set(q, vec({5, 10}));
  w.set(x, vec({1, 2, 3, 4, 5, 6}))
      .set(d, vec({1, 0, 1, 0, 0, 1, 0, 1}))
      .set(z, vec({7, 7, 7}));
  auto prep = c->prepare(st0);
  ProveOptions opt;
  Vec yv;
  opt.tamper = [&](size_t id, SysValue &v) {
    if (id == y.id) yv = std::get<Vec>(v);
  };
  SecureRandomEngine rng;
  EXPECT_TRUE(prep.verify(prep.prove(w, rng, opt)));
  EXPECT_EQ(yv, vec({11, 22, 33, 14, 25, 36}));
  // A wrong digit: from_digits(d) != q.
  w.set(d, vec({1, 1, 1, 0, 0, 1, 0, 1}));
  ProveOptions bad;
  bad.require_satisfied = false;
  EXPECT_FALSE(prep.verify(prep.prove(w, rng, bad)));
  // A dependency that does not broadcast: [2] to [2][3].
  Sys t("gh-shapes-broadcast");
  auto &B = t.domain(env().profile(), "B");
  auto u = B.priv(Subfield{}, "u", 2);
  EXPECT_THROW(B.priv(Subfield{}, "v", Shape{2, 3}, depends_on(u),
                                      nat([](NatInt a) { return a; })),
               CompileError);
}

// The one generator form: an elementwise field closure broadcasts its
// dependencies; a record fills two slots (one of canonical integers) from
// one closure call per proof, reading a host input; a cached public
// computation runs once per statement and is memoized across prepares.
TEST(GordieHowe, GeneratorForms) {
  const AF &af = env().af;
  Sys cs("gh-generators");
  auto &A = cs.domain(env().profile(), "A");
  auto x = A.priv(Subfield{}, "x", Shape{2, 2});  // 1 2 / 3 4
  auto k = A.pub(Subfield{}, "k", 2);         // 10 20
  auto h = cs.host_input("h", 2);                         // bytes 7, 9
  auto y = A.priv(Field{}, "y", Shape{2, 2}, depends_on(x, k),
                             [&af](const AElt &a, const AElt &b) {
                               return af.addf(a, b);
                             });
  int runs = 0;
  auto [w1, w2] = cs.advice_record(
      depends_on(x, h),
      [&af, &runs](const Tensor<AElt> &xv, const std::vector<uint8_t> &hb,
                   Vec &rows, std::vector<NatInt> &plus) {
        ++runs;
        for (size_t i = 0; i < 2; ++i) {
          rows[i] = af.addf(xv(i, 0), xv(i, 1));
          plus[i] = NatInt(hb[i]) + 1;
        }
      },
      A.slot(Subfield{}, "rows", 2), A.nat_slot(Subfield{}, "plus", 2));
  // A plain advice value reads a host input, in the field and the integer
  // forms.
  auto hf = A.priv(Subfield{}, "hf", 2, depends_on(h),
                     [&af](const std::vector<uint8_t> &hb) {
                       return Vec{af.of_scalar(hb[0]), af.of_scalar(hb[1])};
                     });
  auto hn = A.priv(Subfield{}, "hn", 2, depends_on(x, h),
                     [](const Tensor<uint64_t> &xv,
                        const std::vector<uint8_t> &hb) {
                       return std::vector<uint64_t>{xv[0] + hb[0],
                                                    xv[1] + hb[1]};
                     });
  int computed = 0;
  auto pc = A.pub(Field{}, "pc", 2, depends_on(k), computes("double"),
                             [&af, &computed](const Vec &kv) {
                               ++computed;
                               return Vec{af.addf(kv[0], kv[0]),
                                          af.addf(kv[1], kv[1])};
                             })
                .cache();
  A.constant("unused", Vec{af.one()});
  L::gkr(A, "checks", depends_on(y, x, k, w1, w2, pc, hf, hn),
        [&af](const auto &lc, const auto &y, const auto &x,
              const auto &k, const auto &w1, const auto &w2,
              const auto &pc, const auto &hf, const auto &hn) {
          auto c = [&](uint64_t v) { return lc.konst(af.of_scalar(v)); };
          for (size_t i = 0; i < 2; ++i)
            for (size_t j = 0; j < 2; ++j)
              lc.assert_eq(y(i, j), lc.add(x(i, j), k[j]));
          lc.assert_eq(w1[1], lc.add(x(1, 0), x(1, 1)));
          lc.assert_eq(w2[0], c(8));
          lc.assert_eq(w2[1], c(10));
          lc.assert_eq(pc[1], c(40));
          lc.assert_eq(hf[1], c(9));
          lc.assert_eq(hn[0], c(8));
          lc.assert_eq(hn[1], c(11));
        });
  auto c = compile(cs);
  EXPECT_NE(c->report().find("public_compute pc n=2 cached (setup)"),
            std::string::npos)
      << c->report();
  EXPECT_NE(c->report().find("host_input h n=2 phase=0"), std::string::npos)
      << c->report();
  auto vec = [&](std::initializer_list<uint64_t> v) {
    Vec o;
    for (uint64_t a : v) o.push_back(af.of_scalar(a));
    return o;
  };
  Assignment st, w;
  st.set(k, vec({10, 20}));
  w.set(x, vec({1, 2, 3, 4})).set(h, std::vector<uint8_t>{7, 9});
  auto prep = c->prepare(st);
  EXPECT_EQ(computed, 1);
  SecureRandomEngine rng;
  EXPECT_TRUE(prep.verify(prep.prove(w, rng)));
  EXPECT_EQ(runs, 1);  // one closure call for both slots
  EXPECT_EQ(computed, 1);  // neither prove nor verify recomputes it
  auto prep2 = c->prepare(st);
  EXPECT_EQ(computed, 1);  // memoized by the statement's digest
  Assignment st2;
  st2.set(k, vec({11, 20}));
  c->prepare(st2);
  EXPECT_EQ(computed, 2);
  // A missing host input.
  Assignment w0;
  w0.set(x, vec({1, 2, 3, 4}));
  EXPECT_THROW(prep.prove(w0, rng), std::runtime_error);
  // A cached computation that reads a challenge.
  Small m;
  m.A->pub(Field{}, "g2", 1, depends_on(m.gamma), computes("copy"),
                     [](const Vec &g) { return g; })
      .cache();
  EXPECT_NE(core_error(m.cs).find("public_compute 'g2' is cached but reads "
                                    "'gamma'"),
            std::string::npos)
      << core_error(m.cs);
}

// Byte packing: dense, injective, and canonical in each field.

}  // namespace
}  // namespace proofs::gordiehowe
