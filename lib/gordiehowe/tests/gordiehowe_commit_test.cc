// Copyright 2026 Chad Sharp and Paul Grubbs
// SPDX-License-Identifier: Apache-2.0

// GordieHowe: D.priv(e), a committed value equal to an expression whose
// honest witness the compiler computes by evaluating the expression
// (domain.h, predicates.h).
//
// The tests check that the witness equals the expression's value, that a
// tampered committed value is rejected, and where placement puts
// assert_equal(y, e). The DISABLED_ measurements compare the witness time
// of D.priv(e) with a host closure that fills the same values, over the
// same predicates: Keccak-f (a = H.priv(keccak_round(a, i)) per round)
// and SHA-256's compression function (every schedule word and the round
// values T1, E and A committed, each the expression add(...) of its
// operands).

#include <algorithm>
#include <array>
#include <chrono>
#include <cstddef>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <functional>
#include <map>
#include <memory>
#include <random>
#include <stdexcept>
#include <string>
#include <type_traits>
#include <utility>
#include <vector>

#include "algebra/fp_goldilocks4.h"
#include "gordiehowe/examples/shared/keccak_host.h"
#include "algebra/reed_solomon_fp.h"
#include "params/param_sets.h"
#include "params/param_sets_testing.h"
#include "gf2k/lch14_reed_solomon.h"
#include "gordiehowe/gordiehowe.h"
#include "gordiehowe/instances.h"
#include "gordiehowe/lib/arith.h"
#include "gordiehowe/lib/keccak.h"
#include "random/secure_random_engine.h"
#include "gtest/gtest.h"

namespace proofs::gordiehowe {
namespace {

using lib::keccak::keccak_round;

// ------------------------------------------------------------ helpers --

// The binary domain of profile P.
template <class P>
struct BinaryEnv {
  using HF = typename P::HashField;
  using PH = typename P::ProtocolHash;
  using RS = LCH14ReedSolomonFactory<HF>;
  using Sys = ConstraintSystem<PH, HF>;
  HF f;
  RS rs{f};
  DomainProfile<HF, RS, PH> profile() const {
    DomainProfile<HF, RS, PH> p;
    p.f = &f;
    p.rsf = &rs;
    p.field_name = "GF(2^" + std::to_string(HF::kBits) + ")";
    p.rate = 4;
    p.nreq = 64;
    p.has_subfield = true;
    p.prime = Space::kPrime;
    p.rates = param_sets::placement_rates<HF>();
    return p;
  }
};

// Bits of the 25 lanes A (lane (x, y) at A[5 x + y], KeccakTrace's
// order) in the state's flat order: coordinate 64 (5 y + x) + z is bit z
// of lane (x, y).
template <class F>
void append_state_bits(const F &f, const KeccakTrace::State &a,
                       std::vector<typename F::Elt> &out) {
  for (size_t y = 0; y < 5; ++y)
    for (size_t x = 0; x < 5; ++x)
      for (size_t z = 0; z < 64; ++z)
        out.push_back(ct::bit_elt(f, (a[5 * x + y] >> z) & 1));
}
// The same as GF(2^16) words, word q holding flat bits 16 q .. 16 q + 15
// (bit c the coefficient of beta_c).
template <class F>
void append_state_words(const F &f, const KeccakTrace::State &a,
                        std::vector<typename F::Elt> &out) {
  for (size_t q = 0; q < 100; ++q) {
    const size_t lane = q / 4, y = lane / 5, x = lane % 5;
    const uint64_t u = a[5 * x + y] >> (16 * (q % 4));
    auto v = f.zero();
    for (size_t c = 0; c < 16; ++c)
      f.add(v, ct::select(ct::mask(u >> c), f.beta(c), f.zero()));
    out.push_back(v);
  }
}
// The lanes of the state bits IN (flat order).
template <class F>
KeccakTrace::State state_lanes(const F &f,
                                   const std::vector<typename F::Elt> &in) {
  KeccakTrace::State a{};
  for (size_t y = 0; y < 5; ++y)
    for (size_t x = 0; x < 5; ++x)
      for (size_t z = 0; z < 64; ++z)
        a[5 * x + y] |= ct::bit_of(f, in[64 * (5 * y + x) + z]) << z;
  return a;
}
// The 24 round states of Keccak-f from IN (KeccakHost's trace).
inline std::vector<KeccakTrace::State> keccak_trace(
    const KeccakTrace::State &in) {
  KeccakHost keccak;
  (void)keccak.start(in);
  const KeccakTrace t = keccak.trace();
  return t.state;
}
template <class F>
std::vector<typename F::Elt> random_state_bits(const F &f, uint64_t seed) {
  std::mt19937_64 g(seed);
  KeccakTrace::State a{};
  for (auto &x : a) x = g();
  std::vector<typename F::Elt> out;
  append_state_bits(f, a, out);
  return out;
}

// Adds 1 to coordinate K of node ID (a cheating prover).
template <class Sys, class F>
std::function<void(size_t, typename Sys::Value &)> bump(const F &f, size_t id,
                                                        size_t k) {
  return [&f, id, k](size_t at, typename Sys::Value &v) {
    // The node is the test's choice, not a witness value.
    if (at != id) return;
    auto &x = Sys::Set::template get<F>(v);
    f.add(x.at(k), f.one());
  };
}
template <class C, class A, class T = std::nullptr_t>
bool proves(const C &c, const A &st, const A &w, T tamper = nullptr) {
  auto prep = c.prepare(st);
  typename C::ProveOptions opt;
  if constexpr (!std::is_same_v<T, std::nullptr_t>) {
    opt.require_satisfied = false;
    opt.tamper = tamper;
  }
  SecureRandomEngine rng;
  try {
    return prep.verify(prep.prove(w, rng, opt));
  } catch (const std::runtime_error &) {
    return false;
  }
}

// Flips coordinate K of the committed Bit value ID (a cheating prover). A
// value of whole words is committed as its words (ID is then their bit
// view, which has no storage and which the prover evaluates only when a
// circuit or an affine row reads it), so the flip is bit K % 16 of word
// K / 16 of the words. FIRED counts the changes, so that a test sees its
// tamper reach a committed value.
template <class Sys, class F>
std::function<void(size_t, typename Sys::Value &)> flip_bit(
    const Sys &cs, const F &f, size_t id, size_t k,
    std::shared_ptr<size_t> fired) {
  const auto &N = cs.graph().nodes;
  const bool view = N.at(id).kind == Kind::kBitView;
  const size_t at = view ? N.at(id).deps.at(0) : id;
  if (view && 16 * N.at(at).n != N.at(id).n)
    throw std::logic_error("flip_bit: a bit view of some of its words");
  return [&f, at, k, view, fired](size_t i, typename Sys::Value &v) {
    if (i != at) return;
    auto &x = Sys::Set::template get<F>(v);
    if (view)
      f.add(x.at(k / 16), f.beta(k % 16));
    else
      f.add(x.at(k), f.one());
    ++*fired;
  };
}
// Whether the proof with coordinate K of the committed Bit value ID flipped
// verifies; the flip must reach the prover once.
template <class C, class Sys, class F, class A>
bool flipped_proves(const C &c, const Sys &cs, const F &f, const A &st,
                    const A &w, size_t id, size_t k) {
  auto fired = std::make_shared<size_t>(0);
  const bool ok = proves(c, st, w, flip_bit<Sys>(cs, f, id, k, fired));
  EXPECT_EQ(*fired, 1u) << "the flip of node " << id << " at " << k
                        << " reached no committed value";
  return ok;
}

bool has(const std::string &r, const std::string &s) {
  return r.find(s) != std::string::npos;
}

// ---------------------------------------------------------- SHA-256 --
// Words are Bit [m, 32], least significant bit first, m independent
// compressions.

constexpr uint32_t kK[64] = {
    0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5, 0x3956c25b, 0x59f111f1,
    0x923f82a4, 0xab1c5ed5, 0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3,
    0x72be5d74, 0x80deb1fe, 0x9bdc06a7, 0xc19bf174, 0xe49b69c1, 0xefbe4786,
    0x0fc19dc6, 0x240ca1cc, 0x2de92c6f, 0x4a7484aa, 0x5cb0a9dc, 0x76f988da,
    0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7, 0xc6e00bf3, 0xd5a79147,
    0x06ca6351, 0x14292967, 0x27b70a85, 0x2e1b2138, 0x4d2c6dfc, 0x53380d13,
    0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85, 0xa2bfe8a1, 0xa81a664b,
    0xc24b8b70, 0xc76c51a3, 0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070,
    0x19a4c116, 0x1e376c08, 0x2748774c, 0x34b0bcb5, 0x391c0cb3, 0x4ed8aa4a,
    0x5b9cca4f, 0x682e6ff3, 0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208,
    0x90befffa, 0xa4506ceb, 0xbef9a3f7, 0xc67178f2};
constexpr uint32_t kIV[8] = {0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a,
                             0x510e527f, 0x9b05688c, 0x1f83d9ab, 0x5be0cd19};

template <class F>
struct ShaWords {
  using W = Expr<F, Bit>;
  const Domain<F> &H;
  size_t m;
  // The constant word C in each of the m compressions.
  W konst(uint32_t c) const {
    std::vector<uint64_t> b(32 * m);
    for (size_t i = 0; i < m; ++i)
      for (size_t p = 0; p < 32; ++p) b[32 * i + p] = (c >> p) & 1;
    return H.constant(Bit{}, b, Shape{m, 32});
  }
  W zeros(size_t d) const {
    return H.constant(Bit{}, std::vector<uint64_t>(m * d, 0), Shape{m, d});
  }
  W rotr(const W &x, long r) const { return x.rotate(-r, 1); }
  // x >> s: the high s bits zero.
  W shr(const W &x, size_t s) const {
    return x.slice(s, 32, 1).concat(zeros(s), 1);
  }
  // x << s: the low s bits zero.
  W shl(const W &x, size_t s) const {
    return zeros(s).concat(x.slice(0, 32 - s, 1), 1);
  }
  // x + y mod 2^32: generate and propagate bits, Kogge-Stone prefixes,
  // carries the prefixes shifted by one.
  W add2(const W &x, const W &y) const {
    const W p = x ^ y;
    W G = x & y;
    W P = p;
    for (size_t d = 1; d < 32; d <<= 1) {
      G = G ^ (P & shl(G, d));
      P = P & shl(P, d);
    }
    return p ^ shl(G, 1);
  }
  // The sum of WS mod 2^32.
  W add(const std::vector<W> &ws) const {
    W s = ws.at(0);
    for (size_t i = 1; i < ws.size(); ++i) s = add2(s, ws[i]);
    return s;
  }
  W big_sigma0(const W &x) const { return rotr(x, 2) ^ rotr(x, 13) ^ rotr(x, 22); }
  W big_sigma1(const W &x) const { return rotr(x, 6) ^ rotr(x, 11) ^ rotr(x, 25); }
  W small_sigma0(const W &x) const { return rotr(x, 7) ^ rotr(x, 18) ^ shr(x, 3); }
  W small_sigma1(const W &x) const {
    return rotr(x, 17) ^ rotr(x, 19) ^ shr(x, 10);
  }
};

// The committed values of one compression, in order: W_16..W_63, then per
// round T1, E, A, then H'_0..H'_7 (kShaValues words).
constexpr size_t kShaValues = 48 + 3 * 64 + 8;

// Their host values on block MSG (16 words): uint32 arithmetic.
inline std::vector<uint32_t> sha_values(const uint32_t *msg) {
  auto rotr = [](uint32_t x, int r) { return (x >> r) | (x << (32 - r)); };
  std::vector<uint32_t> out;
  out.reserve(kShaValues);
  uint32_t w[64];
  for (size_t t = 0; t < 16; ++t) w[t] = msg[t];
  for (size_t t = 16; t < 64; ++t) {
    const uint32_t s0 = rotr(w[t - 15], 7) ^ rotr(w[t - 15], 18) ^ (w[t - 15] >> 3);
    const uint32_t s1 = rotr(w[t - 2], 17) ^ rotr(w[t - 2], 19) ^ (w[t - 2] >> 10);
    w[t] = s1 + w[t - 7] + s0 + w[t - 16];
    out.push_back(w[t]);
  }
  uint32_t a = kIV[0], b = kIV[1], c = kIV[2], d = kIV[3], e = kIV[4],
           f = kIV[5], g = kIV[6], h = kIV[7];
  for (size_t t = 0; t < 64; ++t) {
    const uint32_t S1 = rotr(e, 6) ^ rotr(e, 11) ^ rotr(e, 25);
    const uint32_t ch = (e & f) ^ (~e & g);
    const uint32_t t1 = h + S1 + ch + kK[t] + w[t];
    const uint32_t S0 = rotr(a, 2) ^ rotr(a, 13) ^ rotr(a, 22);
    const uint32_t maj = (a & b) ^ (a & c) ^ (b & c);
    h = g;
    g = f;
    f = e;
    e = d + t1;
    d = c;
    c = b;
    b = a;
    a = t1 + S0 + maj;
    out.push_back(t1);
    out.push_back(e);
    out.push_back(a);
  }
  const uint32_t st[8] = {a, b, c, d, e, f, g, h};
  for (size_t k = 0; k < 8; ++k) out.push_back(kIV[k] + st[k]);
  return out;
}

// The predicates of m compressions on the message words MSG ([m, 16, 32])
// with the committed values VAL(k, e) for value k (in sha_values' order),
// whose expression is E: D.priv(e), or a slice of a closure's values
// with assert_equal(slice, e). Returns the digest words.
template <class F, class Val>
std::vector<Expr<F, Bit>> sha_compress(const ShaWords<F> &S,
                                       const Expr<F, Bit> &msg, Val val) {
  using W = Expr<F, Bit>;
  const size_t m = S.m;
  std::vector<W> w;
  for (size_t t = 0; t < 16; ++t)
    w.push_back(msg.slice(t, t + 1, 1).reshape(Shape{m, 32}));
  size_t k = 0;
  for (size_t t = 16; t < 64; ++t)
    w.push_back(val(k++, S.add({S.small_sigma1(w[t - 2]), w[t - 7],
                                S.small_sigma0(w[t - 15]), w[t - 16]})));
  std::vector<W> hin;
  for (size_t i = 0; i < 8; ++i) hin.push_back(S.konst(kIV[i]));
  // a..h, the IV broadcast to m rows by the first sums.
  std::vector<W> st = hin;
  for (size_t t = 0; t < 64; ++t) {
    const W &a = st[0], &b = st[1], &c = st[2], &d = st[3], &e = st[4],
            &f = st[5], &g = st[6], &h = st[7];
    const W ch = lib::arith::ch(e, f, g);
    const W maj = lib::arith::maj(a, b, c);
    const W t1 =
        val(k++, S.add({h, S.big_sigma1(e), ch, S.konst(kK[t]), w[t]}));
    const W en = val(k++, S.add({d, t1}));
    const W an = val(k++, S.add({t1, S.big_sigma0(a), maj}));
    st = {an, a, b, c, en, e, f, g};
  }
  std::vector<W> out;
  for (size_t i = 0; i < 8; ++i) out.push_back(val(k++, S.add({hin[i], st[i]})));
  return out;
}

// ------------------------------------------- overload resolution of priv --
// D.priv(e) takes an expression; the other priv forms keep their own
// arguments, and no call reaches the wrong one.

template <class D, class X, class = void>
struct CanPrivExpr : std::false_type {};
template <class D, class X>
struct CanPrivExpr<D, X,
                   std::void_t<decltype(std::declval<D &>().priv(
                       std::declval<const X &>()))>> : std::true_type {};
template <class D, class X, class = void>
struct CanPrivNamed : std::false_type {};
template <class D, class X>
struct CanPrivNamed<D, X,
                    std::void_t<decltype(std::declval<D &>().priv(
                        std::declval<const std::string &>(),
                        std::declval<const X &>()))>> : std::true_type {};
template <class D, class X>
using PrivOf = decltype(std::declval<D &>().priv(std::declval<const X &>()));

using CF = GF2_128<>;
using CElt = CF::Elt;
using CBits = Expr<CF, Bit>;
// A closure for the closure form.
struct CopyBits {
  std::vector<CElt> operator()(const std::vector<CElt> &v) const { return v; }
};

// An expression or an affine expression of the domain's field gives a
// committed value of its type, named or not, at the root and in a scope.
static_assert(CanPrivExpr<Domain<CF>, CBits>::value);
static_assert(CanPrivNamed<Domain<CF>, CBits>::value);
static_assert(CanPrivNamed<ScopedDomain<CF>, CBits>::value);
static_assert(std::is_same_v<PrivOf<Domain<CF>, CBits>, Ref<CF, Bit, Committed>>);
static_assert(
    std::is_same_v<PrivOf<Domain<CF>, Lin<CF>>, Ref<CF, Field, Committed>>);
// A handle is refused (its overload is deleted): it is a value already.
static_assert(!CanPrivExpr<Domain<CF>, Ref<CF, Bit, Committed>>::value);
static_assert(!CanPrivNamed<Domain<CF>, Ref<CF, Bit, Committed>>::value);
static_assert(!CanPrivExpr<Domain<CF>, Ref<CF, Bit, Public>>::value);
static_assert(!CanPrivNamed<ScopedDomain<CF>, Ref<CF, Bit, Committed>>::value);
// An expression of another field has no overload.
static_assert(!CanPrivExpr<Domain<CF>, Expr<Fp64G4, Field>>::value);
static_assert(!CanPrivNamed<ScopedDomain<CF>, Expr<Fp64G4, Field>>::value);
// A Witness member is not an expression, so priv(w.m) is the typed input.
static_assert(!Domain<CF>::kIsExprArg<In<std::array<bool, 8>>>);
static_assert(std::is_same_v<PrivOf<Domain<CF>, In<std::array<bool, 8>>>,
                             Ref<CF, Bit, Committed>>);
// The closure form and the named input still resolve to their own
// overloads, with an expression among the dependencies.
static_assert(std::is_same_v<
              decltype(std::declval<Domain<CF> &>().priv(
                  Bit{}, Shape{8}, depends_on(std::declval<CBits>()),
                  CopyBits{})),
              Ref<CF, Bit, Committed>>);
static_assert(std::is_same_v<decltype(std::declval<Domain<CF> &>().priv(
                                 Bit{}, std::string("x"), Shape{8})),
                             Ref<CF, Bit, Committed>>);

// --------------------------------------------------------------- tests --

template <class P>
class GordieHoweCommit : public ::testing::Test {};
TYPED_TEST_SUITE(GordieHoweCommit, param_sets::Profiles,
                 param_sets::ProfileName);

// 24 rounds, each a = H.priv(keccak_round(a, i)): the committed values
// are KeccakHost's round states, the 24 degree-2 equalities are one field
// batch, and a changed state is rejected.
TYPED_TEST(GordieHoweCommit, KeccakRounds) {
  using Env = BinaryEnv<TypeParam>;
  using HF = typename Env::HF;
  using Sys = typename Env::Sys;
  const Env env;
  const auto prof = env.profile();
  Sys cs("gh-commit-keccak");
  auto &H = cs.domain(prof, "H");
  auto in = H.pub(Bit{}, "in", Shape{5, 5, 64});
  Expr<HF, Bit> a = in;
  std::vector<Ref<HF, Bit, Committed>> S;
  for (size_t i = 0; i < 24; ++i) {
    S.push_back(H.priv("r" + std::to_string(i), keccak_round(a, i)));
    a = S.back();
  }
  auto c = compile(cs);
  const std::string r = c->report();
  // One batched zerocheck, no circuit.
  EXPECT_TRUE(has(r, "field batch")) << r;
  EXPECT_FALSE(has(r, ": circuit (")) << r;
  for (const auto &s : S) EXPECT_EQ(c->phase(s), 0u);

  const auto inv = random_state_bits(env.f, 20261008);
  typename Sys::Assignment st;
  st.set(in, inv);
  EXPECT_TRUE(proves(*c, st, typename Sys::Assignment{}));
  // The witness: KeccakHost's states, committed as GF(2^16) words (each
  // state's bit view reads them).
  const auto trace = keccak_trace(state_lanes(env.f, inv));
  size_t seen = 0;
  auto prep = c->prepare(st);
  typename Sys::ProveOptions opt;
  opt.tamper = [&](size_t id, typename Sys::Value &v) {
    for (size_t i = 0; i < S.size(); ++i) {
      if (cs.graph().nodes.at(S[i].id).deps.at(0) != id) continue;
      std::vector<typename HF::Elt> want;
      append_state_words(env.f, trace.at(i), want);
      EXPECT_EQ(Sys::Set::template get<HF>(v), want) << "round " << i;
      ++seen;
    }
  };
  SecureRandomEngine rng;
  EXPECT_TRUE(prep.verify(prep.prove(typename Sys::Assignment{}, rng, opt)));
  EXPECT_EQ(seen, 24u);
  // A tampered state is rejected: a word of the words state 9 is stored as
  // (its bit view is not committed).
  const size_t words9 = cs.graph().nodes.at(S[9].id).deps.at(0);
  EXPECT_FALSE(proves(*c, st, typename Sys::Assignment{},
                      bump<Sys>(env.f, words9, 48)));
  // The ends of the instance range: the first bit of the first state and
  // the last bit (bit 15 of the last word) of the last.
  EXPECT_FALSE(flipped_proves(*c, cs, env.f, st, typename Sys::Assignment{},
                              S.front().id, 0));
  EXPECT_FALSE(flipped_proves(*c, cs, env.f, st, typename Sys::Assignment{},
                              S.back().id, 1599));
}

// Placement treats assert_equal(y, e) as any predicate: an affine e (a sum
// of bits, XOR in characteristic 2) gives affine rows, a degree-2 e is
// placed by cost between the circuit and a field batch, and an AND of 64
// bits goes to the circuit. Under the rule's placement and with 'quad'
// forced to the circuit and to a batch, a flipped bit of each value is
// rejected at the first and last coordinates and inside.
TYPED_TEST(GordieHoweCommit, Placement) {
  using Env = BinaryEnv<TypeParam>;
  using HF = typename Env::HF;
  using Sys = typename Env::Sys;
  const Env env;
  const auto prof = env.profile();
  std::mt19937_64 g(7);
  std::vector<typename HF::Elt> xv(4096);
  for (auto &e : xv) e = ct::bit_elt(env.f, g() & 1);
  // A row of ones, so all() has a one.
  for (size_t j = 0; j < 64; ++j) xv[64 * 5 + j] = env.f.one();
  for (const std::string force : {"", "H/quad=circuit", "H/quad=batch"}) {
    SCOPED_TRACE(force.empty() ? "the rule's placement" : force);
    Sys cs("gh-commit-placement");
    auto &H = cs.domain(prof, "H");
    auto x = H.priv(Bit{}, "x", Shape{64, 64});
    auto lin = H.priv("lin", x + x.rotate(1, 1));
    auto quad = H.priv("quad", x & x.rotate(3, 1));
    auto deep = H.priv("deep", x.all(1));
    CompileOptions o;
    o.placement_force = force;
    auto c = compile(cs, CompileProfile{}, o);
    const std::string r = c->report();
    EXPECT_TRUE(has(r, "'lin' n=4096: affine rows")) << r;
    if (force.empty())
      EXPECT_TRUE(has(r, "'quad' n=4096: circuit (default") ||
                  has(r, "'quad' n=4096: field batch (cheapest"))
          << r;
    else if (force == "H/quad=batch")
      EXPECT_TRUE(has(r, "'quad' n=4096: field batch")) << r;
    else
      EXPECT_TRUE(has(r, "'quad' n=4096: circuit")) << r;
    EXPECT_TRUE(has(r, "'deep' n=64: circuit")) << r;
    typename Sys::Assignment w;
    w.set(x, xv);
    EXPECT_TRUE(proves(*c, typename Sys::Assignment{}, w));
    const std::vector<std::pair<size_t, size_t>> flips = {
        {lin.id, 0},  {lin.id, 3},     {lin.id, 4095}, {quad.id, 0},
        {quad.id, 4000}, {quad.id, 4095}, {deep.id, 0},  {deep.id, 5},
        {deep.id, 63}};
    for (const auto &[id, k] : flips)
      EXPECT_FALSE(flipped_proves(*c, cs, env.f, typename Sys::Assignment{},
                                  w, id, k))
          << cs.graph().nodes.at(id).name << " coordinate " << k;
  }
}

// SHA-256's compression on one block with D.priv(e) at every value: the
// digest equals the host's, and a changed round value is rejected.
TYPED_TEST(GordieHoweCommit, Sha256Compression) {
  using Env = BinaryEnv<TypeParam>;
  using HF = typename Env::HF;
  using Sys = typename Env::Sys;
  const Env env;
  const auto prof = env.profile();
  Sys cs("gh-commit-sha");
  auto &H = cs.domain(prof, "H");
  const size_t m = 2;
  auto msg = H.priv(Bit{}, "msg", Shape{m, 16, 32});
  const ShaWords<HF> S{H, m};
  std::vector<Ref<HF, Bit, Committed>> vals;
  const auto out = sha_compress<HF>(S, msg, [&](size_t k, const Expr<HF, Bit> &e) {
    vals.push_back(H.priv("v" + std::to_string(k), e));
    return Expr<HF, Bit>(vals.back());
  });
  ASSERT_EQ(vals.size(), kShaValues);
  auto c = compile(cs);
  std::mt19937 g(11);
  std::vector<uint32_t> words(16 * m);
  for (auto &x : words) x = g();
  std::vector<typename HF::Elt> mv;
  for (uint32_t x : words)
    for (size_t p = 0; p < 32; ++p) mv.push_back(ct::bit_elt(env.f, (x >> p) & 1));
  typename Sys::Assignment w;
  w.set(msg, mv);
  EXPECT_TRUE(proves(*c, typename Sys::Assignment{}, w));
  // The digest words against the host.
  auto prep = c->prepare(typename Sys::Assignment{});
  typename Sys::ProveOptions opt;
  size_t checked = 0;
  opt.tamper = [&](size_t id, typename Sys::Value &v) {
    for (size_t k = 0; k < kShaValues; ++k) {
      if (vals[k].id != id) continue;
      const auto &x = Sys::Set::template get<HF>(v);
      for (size_t i = 0; i < m; ++i) {
        const uint32_t want = sha_values(&words[16 * i])[k];
        uint32_t got = 0;
        for (size_t p = 0; p < 32; ++p)
          got |= uint32_t(ct::bit_of(env.f, x[32 * i + p])) << p;
        EXPECT_EQ(got, want) << "value " << k << " row " << i;
      }
      ++checked;
    }
  };
  SecureRandomEngine rng;
  EXPECT_TRUE(prep.verify(prep.prove(w, rng, opt)));
  EXPECT_EQ(checked, kShaValues);
  // A flipped bit of a round value, and of the first and the last value
  // at the ends of their rows.
  EXPECT_FALSE(flipped_proves(*c, cs, env.f, typename Sys::Assignment{}, w,
                              vals[100].id, 33));
  EXPECT_FALSE(flipped_proves(*c, cs, env.f, typename Sys::Assignment{}, w,
                              vals.front().id, 0));
  EXPECT_FALSE(flipped_proves(*c, cs, env.f, typename Sys::Assignment{}, w,
                              vals.back().id, 32 * m - 1));
}

// The word-level program of a Bit expression (bit_eval.h) computes
// eval_expr's values: views of views, sums, products, any and all along an
// axis, mux, NOT, scalar broadcasts and constants. A leaf of type Field
// and a coefficient outside {0, 1} have no program.
TYPED_TEST(GordieHoweCommit, BitProgramMatchesEvalExpr) {
  using Env = BinaryEnv<TypeParam>;
  using HF = typename Env::HF;
  using Sys = typename Env::Sys;
  const Env env;
  const auto prof = env.profile();
  Sys cs("gh-commit-bits");
  auto &H = cs.domain(prof, "H");
  auto hx = H.priv(Bit{}, "x", Shape{3, 7, 70});
  auto hy = H.priv(Bit{}, "y", Shape{7, 70});
  auto hs = H.priv(Bit{}, "s", Shape{1});
  auto z = H.priv(Field{}, "z", Shape{7, 70});
  std::vector<uint64_t> cb(70);
  for (size_t i = 0; i < 70; ++i) cb[i] = (i * 37 + 1) % 3 == 0;
  auto hc = H.priv(Bit{}, "c", Shape{70});
  // Expressions of the handles (a handle's own views are derived nodes,
  // which this test does not evaluate).
  const Expr<HF, Bit> x = hx, y = hy, s = hs, c = hc;
  const ShaWords<HF> S{H, 7};
  const std::vector<ExprPtr<HF>> ok = {
      as_expr(x.sum(0) + y.rotate(5, 1).rotate(-2, 0)).node,
      as_expr((x.rotate(3, 2) & ~x.rotate(-1, 0)).prod(0)).node,
      as_expr(x.any(2).concat(x.all(2), 0)).node,
      as_expr(y.mux(x.sum(0), ~y) ^ (y | x[1])).node,
      as_expr(Expr<HF, Bit>(y.slice(0, 32, 1)).mux(s, y.slice(32, 64, 1)))
          .node,
      as_expr(x[2] + c).node,
      as_expr(S.add({y.slice(3, 35, 1), y.slice(30, 62, 1),
                     y.slice(38, 70, 1)}))
          .node,
  };
  std::mt19937_64 g(3);
  auto bits = [&](size_t n) {
    std::vector<typename HF::Elt> v(n);
    for (auto &e : v) e = ct::bit_elt(env.f, g() & 1);
    return v;
  };
  const Graph &gr = *hx.g;
  ValueStore<typename Sys::Set> vs(gr.nodes.size());
  vs.v[hx.id] = Sys::Set::template wrap<HF>(bits(hx.n));
  vs.v[hy.id] = Sys::Set::template wrap<HF>(bits(hy.n));
  vs.v[hs.id] = Sys::Set::template wrap<HF>(bits(1));
  std::vector<typename HF::Elt> cv;
  for (uint64_t b : cb) cv.push_back(ct::bit_elt(env.f, b));
  vs.v[hc.id] = Sys::Set::template wrap<HF>(cv);
  for (size_t k = 0; k < ok.size(); ++k) {
    const auto p = BitProgram<HF>::compile(env.f, ok[k], gr);
    ASSERT_NE(p, nullptr) << k;
    EXPECT_EQ(p->run(vs), eval_expr(ok[k], vs)) << k;
  }
  EXPECT_EQ(BitProgram<HF>::compile(env.f, as_expr(z * y).node, gr), nullptr);
  EXPECT_EQ(BitProgram<HF>::compile(env.f, as_expr(env.f.beta(1) * y).node, gr),
            nullptr);
}

// In an odd field: y = A.priv(x * x + 3 x) is a Field value equal to its
// expression, and a changed y is rejected.
TEST(GordieHoweCommitOdd, FieldExpression) {
  using AF = Fp64G4;
  using RS = BasicFpReedSolomon<AF>;
  using Sys = ConstraintSystem<SHA384, AF>;
  const AF af;
  const RS rs(af);
  DomainProfile<AF, RS::Factory, SHA384> p;
  p.f = &af;
  p.rsf = &rs.factory();
  p.field_name = "Goldilocks^4";
  p.rate = 4;
  p.nreq = 64;
  p.block_enc = [&rs](const Circuit<AF> &, size_t nw, size_t nq) {
    return rs.block_enc<SHA384>("gordiehowe", nw, nq, 4, 64);
  };
  p.has_subfield = true;
  p.prime = Space::kSubfield;
  Sys cs("gh-commit-odd");
  auto &A = cs.domain(p, "A");
  auto x = A.priv(Field{}, "x", Shape{16});
  auto y = A.priv("y", x * x + 3 * x);
  auto c = compile(cs);
  std::vector<AF::Elt> xv(16);
  for (size_t i = 0; i < 16; ++i) xv[i] = af.of_scalar(uint64_t(1000 + 7 * i));
  typename Sys::Assignment w;
  w.set(x, xv);
  EXPECT_TRUE(proves(*c, typename Sys::Assignment{}, w));
  auto prep = c->prepare(typename Sys::Assignment{});
  typename Sys::ProveOptions opt;
  bool seen = false;
  opt.tamper = [&](size_t id, typename Sys::Value &v) {
    if (id != y.id) return;
    const auto &yv = Sys::Set::template get<AF>(v);
    for (size_t i = 0; i < 16; ++i) {
      const uint64_t xi = 1000 + 7 * i;
      EXPECT_EQ(yv[i], af.of_scalar(xi * xi + 3 * xi)) << i;
    }
    seen = true;
  };
  SecureRandomEngine rng;
  EXPECT_TRUE(prep.verify(prep.prove(w, rng, opt)));
  EXPECT_TRUE(seen);
  EXPECT_FALSE(
      proves(*c, typename Sys::Assignment{}, w, bump<Sys>(af, y.id, 9)));
}

// ------------------------------------------------------- measurements --

size_t env_size(const char *name, size_t dflt) {
  const char *e = std::getenv(name);
  return e != nullptr ? size_t(std::atoi(e)) : dflt;
}
// D.priv(e) with eval_expr's witness: a priv value whose closure copies
// E's values, which depends_on(e) evaluates by eval_expr (the generic
// path, for the measurements).
template <class F>
Expr<F, Bit> generic_commit(Domain<F> &H, const Expr<F, Bit> &e) {
  using Elt = typename F::Elt;
  const auto y = H.priv(Bit{}, Shape(e.dims()), depends_on(e),
                        [](const std::vector<Elt> &v) { return v; });
  assert_equal(y, e);
  return y;
}

// The median witness time of REPS proofs of C on ST, W.
template <class C, class A>
double witness_ms(const C &c, const A &st, const A &w, size_t reps) {
  auto prep = c.prepare(st);
  std::vector<double> ms;
  for (size_t k = 0; k < reps; ++k) {
    SecureRandomEngine rng;
    ProveTimes times;
    typename C::ProveOptions opt;
    opt.times = &times;
    const auto proof = prep.prove(w, rng, opt);
    EXPECT_TRUE(prep.verify(proof));
    ms.push_back(times.witness);
  }
  std::sort(ms.begin(), ms.end());
  return ms[reps / 2];
}

// GH_COMMIT_PERMS independent Keccak-f permutations (default 1), each with
// its 24 round states committed, four ways over the same predicates:
//   commit   a = H.priv(keccak_round(a, i))
//   generic  the same with eval_expr's witness (generic_commit)
//   bits     one H.priv(Bit{}) per permutation filled by KeccakHost's trace
//   words    one H.priv(Subfield{}) of GF(2^16) words per permutation filled
//            by KeccakHost's trace (keccak.h's layout), read through a
//            bit view
// Prints the medians of GH_COMMIT_REPS (default 9) witness times.
TYPED_TEST(GordieHoweCommit, DISABLED_MeasureKeccak) {
  using Env = BinaryEnv<TypeParam>;
  using HF = typename Env::HF;
  using Elt = typename HF::Elt;
  using Sys = typename Env::Sys;
  const size_t perms = env_size("GH_COMMIT_PERMS", 1);
  const size_t reps = env_size("GH_COMMIT_REPS", 9);
  const Env env;
  const HF *pf = &env.f;
  auto run = [&](int form) {
    const auto prof = env.profile();
    Sys cs("gh-commit-measure");
    auto &H = cs.domain(prof, "H");
    typename Sys::Assignment st;
    for (size_t p = 0; p < perms; ++p) {
      auto in = H.pub(Bit{}, "in" + std::to_string(p), Shape{5, 5, 64});
      st.set(in, random_state_bits(env.f, 100 + p));
      Expr<HF, Bit> a = in;
      if (form == 0) {
        for (size_t i = 0; i < 24; ++i) a = H.priv(keccak_round(a, i));
        continue;
      }
      if (form == 3) {
        for (size_t i = 0; i < 24; ++i)
          a = generic_commit(H, keccak_round(a, i));
        continue;
      }
      Expr<HF, Bit> T;
      if (form == 1) {
        T = H.priv(Bit{}, Shape{24, 5, 5, 64}, depends_on(in),
                   [pf](const std::vector<Elt> &v) {
                     std::vector<Elt> out;
                     out.reserve(24 * 1600);
                     for (const auto &s : keccak_trace(state_lanes(*pf, v)))
                       append_state_bits(*pf, s, out);
                     return out;
                   });
      } else {
        auto words = H.priv(Subfield<>{},
                            Shape{24 * 100}, depends_on(in),
                            [pf](const std::vector<Elt> &v) {
                              std::vector<Elt> out;
                              out.reserve(24 * 100);
                              for (const auto &s :
                                   keccak_trace(state_lanes(*pf, v)))
                                append_state_words(*pf, s, out);
                              return out;
                            });
        T = H.bits("bits" + std::to_string(p), words)
                .reshape(Shape{24, 5, 5, 64});
      }
      for (size_t i = 0; i < 24; ++i) {
        assert_equal(T[i], keccak_round(a, i));
        a = T[i];
      }
    }
    auto c = compile(cs);
    return witness_ms(*c, st, typename Sys::Assignment{}, reps);
  };
  const double commit = run(0), bits = run(1), words = run(2),
               generic = run(3);
  std::printf(
      "GH_COMMIT_KECCAK profile=%s perms=%zu reps=%zu witness_ms_median: "
      "commit=%.3f generic=%.3f closure_bits=%.3f closure_words=%.3f "
      "commit/bits=%.2f commit/words=%.2f generic/bits=%.1f\n",
      TypeParam::kId, perms, reps, commit, generic, bits, words, commit / bits,
      commit / words, generic / bits);
}

// GH_COMMIT_SHA_M SHA-256 compressions (default 1), vectorized over a
// leading axis, every value of sha_values committed, three ways over the
// same predicates: H.priv(add(...)) at each value, the same with
// eval_expr's witness (generic_commit), or one H.priv(Bit{}) filled by
// sha_values (uint32 arithmetic) with assert_equal(slice, e).
// Prints the medians of GH_COMMIT_REPS (default 9) witness times.
TYPED_TEST(GordieHoweCommit, DISABLED_MeasureSha256) {
  using Env = BinaryEnv<TypeParam>;
  using HF = typename Env::HF;
  using Elt = typename HF::Elt;
  using Sys = typename Env::Sys;
  const size_t m = env_size("GH_COMMIT_SHA_M", 1);
  const size_t reps = env_size("GH_COMMIT_REPS", 9);
  const Env env;
  const HF *pf = &env.f;
  std::mt19937 g(5);
  std::vector<Elt> mv;
  for (size_t i = 0; i < 16 * m; ++i) {
    const uint32_t x = g();
    for (size_t p = 0; p < 32; ++p) mv.push_back(ct::bit_elt(env.f, (x >> p) & 1));
  }
  auto run = [&](int form) {
    const auto prof = env.profile();
    Sys cs("gh-commit-measure-sha");
    auto &H = cs.domain(prof, "H");
    auto msg = H.priv(Bit{}, "msg", Shape{m, 16, 32});
    const ShaWords<HF> S{H, m};
    if (form == 0) {
      sha_compress<HF>(S, msg, [&](size_t, const Expr<HF, Bit> &e) {
        return Expr<HF, Bit>(H.priv(e));
      });
    } else if (form == 2) {
      sha_compress<HF>(S, msg, [&](size_t, const Expr<HF, Bit> &e) {
        return generic_commit(H, e);
      });
    } else {
      // [kShaValues, m, 32]: value k of compression i at (k, i).
      auto T = H.priv(Bit{}, Shape{kShaValues, m, 32}, depends_on(msg),
                      [pf, m](const std::vector<Elt> &v) {
                        std::vector<Elt> out(kShaValues * m * 32);
                        for (size_t i = 0; i < m; ++i) {
                          uint32_t w[16] = {};
                          for (size_t t = 0; t < 16; ++t)
                            for (size_t p = 0; p < 32; ++p)
                              w[t] |= uint32_t(ct::bit_of(
                                          *pf, v[(16 * i + t) * 32 + p]))
                                      << p;
                          const auto val = sha_values(w);
                          for (size_t k = 0; k < kShaValues; ++k)
                            for (size_t p = 0; p < 32; ++p)
                              out[(k * m + i) * 32 + p] =
                                  ct::bit_elt(*pf, (val[k] >> p) & 1);
                        }
                        return out;
                      });
      sha_compress<HF>(S, msg, [&](size_t k, const Expr<HF, Bit> &e) {
        const Expr<HF, Bit> y = T[k];
        assert_equal(y, e);
        return y;
      });
    }
    auto c = compile(cs);
    typename Sys::Assignment w;
    w.set(msg, mv);
    return witness_ms(*c, typename Sys::Assignment{}, w, reps);
  };
  const double commit = run(0), closure = run(1), generic = run(2);
  std::printf(
      "GH_COMMIT_SHA256 profile=%s m=%zu reps=%zu witness_ms_median: "
      "commit=%.3f generic=%.3f closure=%.3f commit/closure=%.2f "
      "generic/closure=%.1f\n",
      TypeParam::kId, m, reps, commit, generic, closure, commit / closure,
      generic / closure);
}

// A flat evaluator over field elements for the breakdown below: each node
// once, coordinatewise field operations, no Logic representation. It
// covers the operations of keccak_round.
template <class F>
struct FieldEval {
  using Elt = typename F::Elt;
  const F &f;
  const ValueReader &v;
  std::map<const ExprNode<F> *, std::vector<Elt>> memo;
  const std::vector<Elt> &operator()(const ExprNode<F> &x) {
    auto it = memo.find(&x);
    if (it != memo.end()) return it->second;
    return memo.emplace(&x, make(x)).first->second;
  }
  std::vector<Elt> make(const ExprNode<F> &x) {
    std::vector<Elt> out(x.n, f.zero());
    switch (x.op) {
      case ExprOp::kLin:
        for (const auto &t : x.lin.terms) {
          const auto &a = v.template get<F>(t.node);
          for (size_t i = 0; i < x.n; ++i)
            f.add(out[i], f.mulf(t.scale, a[i]));
        }
        break;
      case ExprOp::kConst:
        out = x.c;
        break;
      case ExprOp::kAdd: {
        const auto &a = (*this)(*x.kids[0]);
        const auto &b = (*this)(*x.kids[1]);
        for (size_t i = 0; i < x.n; ++i) out[i] = f.addf(a[i], b[i]);
        break;
      }
      case ExprOp::kAnd:
      case ExprOp::kMul: {
        const auto &a = (*this)(*x.kids[0]);
        const auto &b = (*this)(*x.kids[1]);
        for (size_t i = 0; i < x.n; ++i) out[i] = f.mulf(a[i], b[i]);
        break;
      }
      case ExprOp::kNot: {
        const auto &a = (*this)(*x.kids[0]);
        for (size_t i = 0; i < x.n; ++i) out[i] = f.subf(f.one(), a[i]);
        break;
      }
      case ExprOp::kSum: {
        const auto &a = (*this)(*x.kids[0]);
        const size_t w = x.w == 0 ? a.size() : x.w;
        for (size_t k = 0; k < x.n; ++k)
          for (size_t j = 0; j < w; ++j) f.add(out[k], a[k * w + j]);
        break;
      }
      case ExprOp::kBroadcast: {
        const auto &a = (*this)(*x.kids[0]);
        out.assign(x.n, a[0]);
        break;
      }
      case ExprOp::kGather: {
        std::vector<const Elt *> at;
        for (const auto &k : x.kids)
          for (const auto &e : (*this)(*k)) at.push_back(&e);
        for (size_t i = 0; i < x.n; ++i) out[i] = *at[x.idx[i]];
        break;
      }
      default:
        throw std::runtime_error("FieldEval: an operation it does not cover");
    }
    return out;
  }
};

// Where one round's witness time goes: GH_COMMIT_REPS (default 9) medians
// of 200 evaluations of keccak_round on one state, by eval_expr (the Logic
// emitter over the evaluation backend), by a flat evaluator over field
// elements (FieldEval), by the word-level program (bit_eval.h; its build
// separately), and by the host (lanes from bits, the 24-round trace, one
// state's bits).
TYPED_TEST(GordieHoweCommit, DISABLED_MeasureKeccakRoundBreakdown) {
  using Env = BinaryEnv<TypeParam>;
  using HF = typename Env::HF;
  using Elt = typename HF::Elt;
  using Sys = typename Env::Sys;
  using Clock = std::chrono::steady_clock;
  const size_t reps = env_size("GH_COMMIT_REPS", 9);
  constexpr size_t kIters = 200;
  const Env env;
  const auto prof = env.profile();
  Sys cs("gh-commit-breakdown");
  auto &H = cs.domain(prof, "H");
  auto in = H.pub(Bit{}, "in", Shape{5, 5, 64});
  const Expr<HF, Bit> e = keccak_round(Expr<HF, Bit>(in), 3);
  ValueStore<typename Sys::Set> vs(in.g->nodes.size());
  const auto inv = random_state_bits(env.f, 99);
  vs.v[in.id] = Sys::Set::template wrap<HF>(inv);
  auto median = [&](auto fn) {
    std::vector<double> us;
    for (size_t r = 0; r < reps; ++r) {
      const auto t0 = Clock::now();
      for (size_t k = 0; k < kIters; ++k) fn();
      us.push_back(
          std::chrono::duration<double, std::micro>(Clock::now() - t0).count() /
          kIters);
    }
    std::sort(us.begin(), us.end());
    return us[reps / 2];
  };
  const std::vector<Elt> want = eval_expr(e.node, vs);
  std::shared_ptr<const BitProgram<HF>> prog;
  const double build_us =
      median([&] { prog = BitProgram<HF>::compile(env.f, e.node, *in.g); });
  ASSERT_NE(prog, nullptr);
  EXPECT_EQ(prog->run(vs), want);
  FieldEval<HF> fe0{env.f, vs, {}};
  EXPECT_EQ(fe0(*e.node), want);
  size_t sink = 0;
  const double logic_us =
      median([&] { sink += eval_expr(e.node, vs).size(); });
  const double flat_us = median([&] {
    FieldEval<HF> fe{env.f, vs, {}};
    sink += fe(*e.node).size();
  });
  const double bits_us = median([&] { sink += prog->run(vs).size(); });
  const double host_us = median([&] {
    std::vector<Elt> out;
    out.reserve(1600);
    const KeccakTrace::State a = keccak_trace(state_lanes(env.f, inv))[3];
    append_state_bits(env.f, a, out);
    sink += out.size();
  });
  // The leaf read from packed bits (a program's output read by the next).
  vs.packed_bits[in.id] = std::vector<uint64_t>(25, 0);
  for (size_t i = 0; i < 1600; ++i)
    vs.packed_bits[in.id][i / 64] |= ct::bit_of(env.f, inv[i]) << (i % 64);
  EXPECT_EQ(prog->run(vs), want);
  const double cached_us = median([&] { sink += prog->run(vs).size(); });
  // 24 rounds chained as the prover's evaluation runs them: each program
  // reads the previous output's packed bits, and its elements are stored
  // as a node's value.
  std::vector<size_t> ids;
  std::vector<std::shared_ptr<const BitProgram<HF>>> chain;
  {
    Expr<HF, Bit> a = in;
    for (size_t i = 0; i < 24; ++i) {
      auto y = H.priv(Bit{}, Shape{5, 5, 64});
      chain.push_back(
          BitProgram<HF>::compile(env.f, keccak_round(a, i).node, *in.g));
      ids.push_back(y.id);
      a = y;
    }
  }
  const double chain_us = median([&] {
    ValueStore<typename Sys::Set> cv(in.g->nodes.size());
    cv.v[in.id] = vs.v[in.id];
    for (size_t i = 0; i < 24; ++i) {
      cv.v[ids[i]] = Sys::Set::template wrap<HF>(chain[i]->run(cv, ids[i]));
      sink += cv.v[ids[i]].index();
    }
  }) / 24;
  // SHA-256's T1 = h + Sigma1(e) + ch(e, f, g) + K + W on words [m, 32]
  // read from packed bits, for m = 1 and 16.
  for (size_t m : {size_t(1), size_t(16)}) {
    const ShaWords<HF> S{H, m};
    std::mt19937_64 g(m);
    std::vector<Expr<HF, Bit>> w;
    for (size_t k = 0; k < 5; ++k) {
      auto h = H.pub(Bit{}, Shape{m, 32});
      std::vector<Elt> hv(32 * m);
      for (auto &b : hv) b = ct::bit_elt(env.f, g() & 1);
      vs.v.resize(in.g->nodes.size());
      vs.msg.resize(in.g->nodes.size());
      vs.held.resize(in.g->nodes.size(), nullptr);
      vs.v[h.id] = Sys::Set::template wrap<HF>(hv);
      w.push_back(h);
    }
    const Expr<HF, Bit> t1 = S.add({w[0], S.big_sigma1(w[1]),
                                    lib::arith::ch(w[1], w[2], w[3]),
                                    S.konst(kK[0]), w[4]});
    const auto pt = BitProgram<HF>::compile(env.f, t1.node, *in.g);
    ASSERT_NE(pt, nullptr);
    EXPECT_EQ(pt->run(vs), eval_expr(t1.node, vs));
    const double t1_us = median([&] { sink += pt->run(vs).size(); });
    std::printf("GH_COMMIT_T1 profile=%s m=%zu ops=%zu us_per_run=%.3f\n",
                TypeParam::kId, m, pt->size(), t1_us);
  }
  std::printf(
      "GH_COMMIT_ROUND profile=%s reps=%zu us_per_round_median: "
      "eval_expr=%.2f flat_field=%.2f bit_program=%.2f (leaf from packed "
      "bits %.2f; build %.1f, %zu ops; chained 24 rounds %.2f per round) "
      "host_trace24_plus_io=%.2f (sink %zu)\n",
      TypeParam::kId, reps, logic_us, flat_us, bits_us, cached_us, build_us,
      prog->size(), chain_us, host_us, sink);
}

}  // namespace
}  // namespace proofs::gordiehowe
