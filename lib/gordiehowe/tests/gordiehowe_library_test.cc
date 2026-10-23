// Copyright 2026 Chad Sharp and Paul Grubbs
// SPDX-License-Identifier: Apache-2.0

// GordieHowe: the library functions over the core
// in a binary field, GF(2^128) with its GF(2^16) subfield, and an odd one,
// Goldilocks^4 with the prime subfield:
//   - windows at private offsets (windows.h): honest windows prove; a window
//     byte off the text and a window start off its offset are rejected;
//   - ordered selection (select.h, cutoff_select.h): the first n samples
//     below a cutoff, multiplicative labels in characteristic 2 and
//     additive ones in odd characteristic; a skipped sample is rejected;
//   - memory checking (permutation.h's assert_memory) of a write-and-read
//     trace with its time comparison: a wrong read value and a read time
//     that does not precede its step are rejected;
//   - multiset equality packed by the challenge gamma (records wider than
//     [K : E]);
//   - assert_sum_mod, ch, maj and xor3 (arith.h);
//   - add_words on a batch of words, and add_bit (arith.h).

#include <cstddef>
#include <cstdint>
#include <functional>
#include <map>
#include <random>
#include <string>
#include <vector>

#include "algebra/fp_goldilocks4.h"
#include "algebra/reed_solomon_fp.h"
#include "gf2k/gf2_128.h"
#include "gf2k/lch14_reed_solomon.h"
#include "gordiehowe/ct.h"
#include "gordiehowe/instances.h"
#include "gordiehowe/lib/arith.h"
#include "gordiehowe/lib/cutoff_select.h"
#include "gordiehowe/lib/interpolate.h"
#include "gordiehowe/lib/permutation.h"
#include "gordiehowe/lib/select.h"
#include "gordiehowe/lib/table.h"
#include "gordiehowe/lib/windows.h"
#include "gordiehowe/system.h"
#include "gtest/gtest.h"
#include "random/secure_random_engine.h"

namespace proofs::gordiehowe {
namespace {

using HF = GF2_128<>;
using RSH = LCH14ReedSolomonFactory<HF>;
using AF = Fp64G4;
using RSA = BasicFpReedSolomon<AF>;

struct Env {
  HF hf;
  RSH rsh{hf};
  AF af;
  RSA rsa{af};
};
const Env &env() {
  static const Env *e = new Env;
  return *e;
}

// The field F's system, field and domain profile.
template <class F>
struct Field;
template <>
struct Field<HF> {
  using Sys = ConstraintSystem<SHA384, HF>;
  static const HF &f() { return env().hf; }
  static DomainProfile<HF, RSH, SHA384> profile() {
    DomainProfile<HF, RSH, SHA384> p;
    p.f = &env().hf;
    p.rsf = &env().rsh;
    p.field_name = "GF(2^128)";
    p.rate = 4;
    p.nreq = 64;
    p.has_subfield = true;
    p.prime = Space::kPrime;
    return p;
  }
};
template <>
struct Field<AF> {
  using Sys = ConstraintSystem<SHA384, AF>;
  static const AF &f() { return env().af; }
  static DomainProfile<AF, RSA::Factory, SHA384> profile() {
    DomainProfile<AF, RSA::Factory, SHA384> p;
    p.f = &env().af;
    p.rsf = &env().rsa.factory();
    p.field_name = "Goldilocks^4";
    p.rate = 4;
    p.nreq = 64;
    const RSA *r = &env().rsa;
    p.block_enc = [r](const Circuit<AF> &, size_t nw, size_t nq) {
      return r->block_enc<SHA384>("gordiehowe", nw, nq, 4, 64);
    };
    p.has_subfield = true;
    p.prime = Space::kSubfield;
    return p;
  }
};

template <class F>
using Sys = typename Field<F>::Sys;
template <class F>
using V = std::vector<typename F::Elt>;

// Proves W (statement ST) and verifies; with CHEATING, the prover skips
// its satisfaction check and TAMPER edits its values.
template <class F>
bool proves(const typename Sys<F>::Compiled &c,
            const typename Sys<F>::Assignment &st,
            const typename Sys<F>::Assignment &w, bool cheating = false,
            std::function<void(size_t, typename Sys<F>::Value &)> tamper =
                nullptr) {
  auto prep = c.prepare(st);
  typename Sys<F>::ProveOptions opt;
  opt.require_satisfied = !cheating;
  if (tamper) opt.tamper = std::move(tamper);
  SecureRandomEngine rng;
  try {
    return prep.verify(prep.prove(w, rng, opt));
  } catch (const std::runtime_error &) {
    return false;
  }
}
// The bits of BYTES, bit 8 m + t of byte m.
template <class F>
V<F> byte_bits(const std::vector<uint8_t> &b) {
  return ct::byte_bits(Field<F>::f(), b);
}
// The W-bit words X, least significant bit first.
template <class F>
V<F> word_bits(const std::vector<uint64_t> &x, size_t w) {
  V<F> out;
  for (uint64_t v : x)
    for (size_t t = 0; t < w; ++t)
      out.push_back(ct::bit_elt(Field<F>::f(), v >> t));
  return out;
}
// Adds 1 to coordinate K of node ID.
template <class F>
std::function<void(size_t, typename Sys<F>::Value &)> bump(size_t id,
                                                           size_t k) {
  return [id, k](size_t at, typename Sys<F>::Value &v) {
    if (at != id) return;
    auto &x = std::get<V<F>>(v);
    Field<F>::f().add(x.at(k), Field<F>::f().one());
  };
}

template <class F>
class LibraryTest : public ::testing::Test {};
using Fields = ::testing::Types<HF, AF>;
class FieldName {
 public:
  template <class F>
  static std::string GetName(int) {
    return std::is_same_v<F, HF> ? "binary" : "odd";
  }
};
TYPED_TEST_SUITE(LibraryTest, Fields, FieldName);

// --------------------------------------------------------------- windows --

// A text of 64 bytes whose bytes [4, 60) windows may cover; window 0 is the
// key AA BB then 3 committed bytes, window 1 is 4 committed bytes.
TYPED_TEST(LibraryTest, Windows) {
  using F = TypeParam;
  constexpr size_t n = 64, first = 4, end = 60;
  const size_t k0 = 10, k1 = 30;
  std::mt19937_64 g(3);
  std::vector<uint8_t> text(n);
  for (auto &x : text) x = uint8_t(g());
  text[first + k0] = 0xAA;
  text[first + k0 + 1] = 0xBB;
  for (bool good : {true, false}) {
    Sys<F> cs("gh-library-windows");
    auto &D = cs.domain(Field<F>::profile(), "D");
    auto bytes = D.priv(Bit{}, "text", 8 * n);
    auto in_text = D.priv(Bit{}, "in_text", n);
    const HostInput offsets = cs.host_input("offsets", 4);
    const lib::windows::WindowText<F> wt{bytes, in_text, first, end};
    const auto w0 =
        lib::windows::window_bytes(cs, D, "w0", wt, offsets, 0, 2, 3);
    const auto w1 =
        lib::windows::window_bytes(cs, D, "w1", wt, offsets, 1, 0, 4);
    const std::vector<lib::windows::Window<F>> windows = {
        {{lib::windows::window_part<F>({0xAA, 0xBB}),
          lib::windows::window_part(w0)}},
        {{lib::windows::window_part(w1)}}};
    lib::windows::match_windows(cs, D, "m", wt, offsets, windows);
    auto c = compile(cs);
    typename Sys<F>::Assignment w;
    auto t = text;
    // Without the key at window 0's offset, the honest window does not
    // lie in the text.
    if (!good) t[first + k0 + 1] = 0xBC;
    w.set(bytes, byte_bits<F>(t));
    w.set(in_text, V<F>(n, Field<F>::f().one()));
    w.set(offsets, std::vector<uint8_t>{uint8_t(k0), 0, uint8_t(k1), 0});
    EXPECT_EQ(proves<F>(*c, {}, w, !good), good);
    if (good) {
      // A window byte off the text.
      EXPECT_FALSE(proves<F>(*c, {}, w, true, bump<F>(w1.id, 3)));
      // The start of window 1 off its offset.
      const size_t kid = cs.graph().nodes.size();
      size_t kappa = kid;
      for (size_t i = 0; i < cs.graph().nodes.size(); ++i)
        if (cs.graph().nodes[i].name == "m.kappa") kappa = i;
      ASSERT_LT(kappa, kid);
      EXPECT_FALSE(proves<F>(*c, {}, w, true, bump<F>(kappa, 1)));
    }
  }
}

// ------------------------------------------------------------- selection --

// The first 6 of 24 samples of 16 bits below 30000.
TYPED_TEST(LibraryTest, OrderedSelection) {
  using F = TypeParam;
  constexpr size_t S = 24, n = 6;
  constexpr uint32_t cutoff = 30000;
  std::mt19937_64 g(5);
  std::vector<uint64_t> v(S);
  for (auto &x : v) x = g() % 65536;
  Sys<F> cs("gh-library-select");
  auto &D = cs.domain(Field<F>::profile(), "D");
  auto stream = D.priv(Bit{}, "stream", Shape{S, 16});
  const auto sel = lib::select::select_first_n(
      cs, D, stream, lib::select::Cutoff{cutoff}, lib::select::Count{n});
  auto c = compile(cs);
  EXPECT_EQ(c->phase(sel.delta), 1u);
  typename Sys<F>::Assignment w;
  w.set(stream, word_bits<F>(v, 16));
  EXPECT_TRUE(proves<F>(*c, {}, w));
  // The output skips the first accepted sample.
  std::vector<uint64_t> acc;
  for (uint64_t x : v)
    if (x < cutoff) acc.push_back(x);
  ASSERT_GE(acc.size(), n + 1);
  const std::vector<uint64_t> skipped(acc.begin() + 1, acc.begin() + 1 + n);
  const auto bad = word_bits<F>(skipped, 16);
  EXPECT_FALSE(proves<F>(*c, {}, w, true,
                         [&bad, id = sel.raw.id](size_t at, auto &x) {
                           if (at == id) std::get<V<F>>(x) = bad;
                         }));
}

// ---------------------------------------------------------------- memory --

// N cells start at 0; step t reads cell a_t (value v_t written at time
// o_t) and writes u_t at time t + 1. Records (address, value, time):
// reads + final = initial + writes, and o_t < t + 1.
TYPED_TEST(LibraryTest, MemoryChecking) {
  using F = TypeParam;
  using Elt = typename F::Elt;
  constexpr size_t N = 8, T = 6, tb = 3;
  const F &f = Field<F>::f();
  const std::vector<uint64_t> addr = {3, 5, 3, 0, 5, 3};
  const std::vector<uint64_t> vals = {11, 12, 13, 14, 15, 16};
  Sys<F> cs("gh-library-memory");
  auto &D = cs.domain(Field<F>::profile(), "D");
  auto a = D.priv(Subfield{}, "addr", T);
  auto u = D.priv(Subfield{}, "write", T);
  const F *pf = &f;
  // The trace: read values and times, final cells and times.
  auto [rv, rt, fin, ft] = cs.advice_record(
      depends_on(a, u),
      [pf](const Tensor<Elt> &av, const Tensor<Elt> &uv, std::vector<Elt> &rv,
           std::vector<Elt> &rt, std::vector<Elt> &fin,
           std::vector<Elt> &ft) {
        const F &f = *pf;
        std::vector<Elt> mem(N, f.zero());
        std::vector<uint64_t> tm(N, 0);
        for (size_t t = 0; t < T; ++t) {
          Elt v = f.zero();
          uint64_t o = 0;
          for (size_t k = 0; k < N; ++k) {
            const uint64_t m = ct::mask(ct::equal(av[t], f.of_scalar(k)));
            v = ct::select(m, mem[k], v);
            o = ct::select(m, tm[k], o);
          }
          rv[t] = v;
          for (size_t b = 0; b < tb; ++b) rt[t * tb + b] = ct::bit_elt(f, o >> b);
          for (size_t k = 0; k < N; ++k) {
            const uint64_t m = ct::mask(ct::equal(av[t], f.of_scalar(k)));
            mem[k] = ct::select(m, uv[t], mem[k]);
            tm[k] = ct::select(m, uint64_t(t + 1), tm[k]);
          }
        }
        fin = mem;
        for (size_t k = 0; k < N; ++k) ft[k] = f.of_scalar(tm[k]);
      },
      D.slot(Subfield{}, "read", Shape(T)),
      D.slot(Bit{}, "read_time", Shape{T, tb}),
      D.slot(Subfield{}, "final", Shape(N)),
      D.slot(Subfield{}, "final_time", Shape(N)));
  std::vector<uint64_t> cells, steps, zeros(N, 0);
  for (size_t k = 0; k < N; ++k) cells.push_back(k);
  for (size_t t = 0; t < T; ++t) steps.push_back(t + 1);
  V<F> ce, se;
  for (uint64_t k : cells) ce.push_back(f.of_scalar(k));
  for (uint64_t t : steps) se.push_back(f.of_scalar(t));
  std::vector<Elt> basis;
  for (size_t b = 0; b < tb; ++b) basis.push_back(f.of_scalar(uint64_t(1) << b));
  const Expr<F> time =
      (Expr<F>(rt) * D.constant(basis)).sum(1);
  lib::permutation::Records<F, 3> initial(D), reads(D), writes(D), last(D);
  initial.push_constants({cells, zeros, zeros});
  reads.push(a, rv, time);
  writes.push(a, u, D.constant(se));
  last.push(D.constant(ce), fin, ft);
  lib::permutation::assert_memory(cs, D, "mem", initial, reads, writes, last);
  std::vector<uint64_t> sb;
  for (uint64_t t : steps)
    for (size_t b = 0; b < tb; ++b) sb.push_back((t >> b) & 1);
  assert_true(rt.from_bits() < D.constant(Bit{}, sb, Shape{T, tb}).from_bits(),
              "fresh");
  auto c = compile(cs);
  typename Sys<F>::Assignment w;
  V<F> av, uv;
  for (uint64_t x : addr) av.push_back(f.of_scalar(x));
  for (uint64_t x : vals) uv.push_back(f.of_scalar(x));
  w.set(a, av).set(u, uv);
  EXPECT_TRUE(proves<F>(*c, {}, w));
  // Step 2 reads cell 3, written at step 0: a wrong value.
  EXPECT_FALSE(proves<F>(*c, {}, w, true, bump<F>(rv.id, 2)));
  // A read time at its own step (o_2 = 3, not below 3), records consistent.
  EXPECT_FALSE(proves<F>(*c, {}, w, true, [&](size_t at, auto &x) {
    if (at != rt.id) return;
    auto &b = std::get<V<F>>(x);
    for (size_t k = 0; k < tb; ++k) b[2 * tb + k] = ct::bit_elt(f, 3 >> k);
  }));
}

// ----------------------------------------------- multiset, gamma packing --

// Records of arity 5: the fixed kappa packs at most [K : E] components (16
// over GF(2^16), 4 over Goldilocks), so the odd field packs these by gamma.
TYPED_TEST(LibraryTest, MultisetPacking) {
  using F = TypeParam;
  const F &f = Field<F>::f();
  for (bool equal : {true, false}) {
    Sys<F> cs("gh-library-multiset");
    auto &D = cs.domain(Field<F>::profile(), "D");
    auto x = D.priv(Subfield{}, "x", Shape{5, 4});
    auto y = D.priv(Subfield{}, "y", Shape{5, 4});
    lib::permutation::Records<F, 5> l(D), r(D);
    l.push(x.at(0), x.at(1), x.at(2), x.at(3), x.at(4));
    r.push(y.at(0), y.at(1), y.at(2), y.at(3), y.at(4));
    const auto m = lib::permutation::assert_multiset_equal(cs, D, "p", l, r);
    const bool odd = !std::is_same_v<F, HF>;
    EXPECT_EQ(m.packing.gamma.has_value(), odd);
    auto c = compile(cs);
    V<F> xv(20), yv(20);
    for (size_t k = 0; k < 5; ++k)
      for (size_t i = 0; i < 4; ++i) {
        xv[k * 4 + i] = f.of_scalar(10 * k + i);
        yv[k * 4 + i] = f.of_scalar(10 * k + (3 - i));
      }
    // A record whose components are another record's, but mixed.
    if (!equal) std::swap(yv[0], yv[1]);
    typename Sys<F>::Assignment w;
    w.set(x, xv).set(y, yv);
    EXPECT_EQ(proves<F>(*c, {}, w, !equal), equal);
  }
}

// ------------------------------------------------------------ arithmetic --

// Three words of 12 bits sum to r modulo 2^12; ch, maj and xor3 on 16 bits.
TYPED_TEST(LibraryTest, Arithmetic) {
  using F = TypeParam;
  constexpr size_t N = 12, m = 4;
  const std::vector<uint64_t> x1 = {4095, 17, 2048, 0}, x2 = {4095, 4000, 2048, 1},
                              x3 = {4095, 300, 0, 4095};
  std::vector<uint64_t> r;
  for (size_t i = 0; i < m; ++i) r.push_back((x1[i] + x2[i] + x3[i]) % 4096);
  const std::vector<uint64_t> a = {0xF0F0}, b = {0xCCCC}, z = {0xAAAA};
  const std::vector<uint64_t> ch = {(a[0] & b[0]) ^ (~a[0] & z[0] & 0xFFFF)};
  const std::vector<uint64_t> mj = {(a[0] & b[0]) ^ (a[0] & z[0]) ^ (b[0] & z[0])};
  const std::vector<uint64_t> xr = {a[0] ^ b[0] ^ z[0]};
  Sys<F> cs("gh-library-arith");
  auto &D = cs.domain(Field<F>::profile(), "D");
  auto w1 = D.priv(Bit{}, "x1", Shape{m, N});
  auto w2 = D.priv(Bit{}, "x2", Shape{m, N});
  auto w3 = D.priv(Bit{}, "x3", Shape{m, N});
  auto rr = D.priv(Bit{}, "r", Shape{m, N});
  lib::arith::assert_sum_mod(D, rr, {w1, w2, w3}, "sum");
  // Two-word sums in constant depth (assert_add) and by Sklansky's adder
  // (add_words): r12 = x1 + x2 for word 0.
  auto r12 = D.priv(Bit{}, "r12", N);
  const Expr<F, Bit> a1 = Expr<F, Bit>(w1).at(0), a2 = Expr<F, Bit>(w2).at(0);
  lib::arith::assert_add<F>(r12, a1, a2, "add");
  assert_equal(r12, lib::arith::add_words<F>(a1, a2), "add_words");
  auto pa = D.priv(Bit{}, "a", 16);
  auto pb = D.priv(Bit{}, "b", 16);
  auto pz = D.priv(Bit{}, "z", 16);
  auto pc = D.priv(Bit{}, "ch", 16);
  auto pm = D.priv(Bit{}, "maj", 16);
  auto px = D.priv(Bit{}, "xor", 16);
  assert_equal(pc, lib::arith::ch<F>(pa, pb, pz), "ch");
  assert_equal(pm, lib::arith::maj<F>(pa, pb, pz), "maj");
  assert_equal(px, lib::arith::xor3<F>(pa, pb, pz), "xor3");
  auto c = compile(cs);
  typename Sys<F>::Assignment w;
  w.set(w1, word_bits<F>(x1, N)).set(w2, word_bits<F>(x2, N));
  w.set(w3, word_bits<F>(x3, N)).set(rr, word_bits<F>(r, N));
  w.set(pa, word_bits<F>(a, 16)).set(pb, word_bits<F>(b, 16));
  w.set(pz, word_bits<F>(z, 16)).set(pc, word_bits<F>(ch, 16));
  w.set(pm, word_bits<F>(mj, 16)).set(px, word_bits<F>(xr, 16));
  w.set(r12, word_bits<F>({(x1[0] + x2[0]) % 4096}, N));
  EXPECT_TRUE(proves<F>(*c, {}, w));
  // A sum off by one, and one off by 2^12 is the same word.
  auto r1 = r;
  r1[1] = (r1[1] + 1) % 4096;
  auto w2v = w;
  w2v.set(rr, word_bits<F>(r1, N));
  EXPECT_FALSE(proves<F>(*c, {}, w2v, true));
  // A wrong two-word sum.
  auto wa = w;
  wa.set(r12, word_bits<F>({(x1[0] + x2[0] + 1) % 4096}, N));
  EXPECT_FALSE(proves<F>(*c, {}, wa, true));
  // A wrong bit of each function.
  for (auto [h, v] : {std::pair{pc, ch}, std::pair{pm, mj}, std::pair{px, xr}}) {
    auto bad = v;
    bad[0] ^= 1 << 5;
    auto wb = w;
    wb.set(h, word_bits<F>(bad, 16));
    EXPECT_FALSE(proves<F>(*c, {}, wb, true));
  }
}

// add_words on words [m, N], one sum per row (4095 + 4095 drops the carry
// out of the top bit); a wrong sum in one row is rejected.
TYPED_TEST(LibraryTest, AddWordsBatched) {
  using F = TypeParam;
  constexpr size_t N = 12, m = 4;
  const std::vector<uint64_t> x1 = {4095, 17, 2048, 0}, x2 = {4095, 4000, 2048, 1};
  std::vector<uint64_t> s;
  for (size_t i = 0; i < m; ++i) s.push_back((x1[i] + x2[i]) % 4096);
  Sys<F> cs("gh-library-add-words");
  auto &D = cs.domain(Field<F>::profile(), "D");
  auto a = D.priv(Bit{}, "a", Shape{m, N});
  auto b = D.priv(Bit{}, "b", Shape{m, N});
  auto r = D.priv(Bit{}, "r", Shape{m, N});
  assert_equal(r, lib::arith::add_words<F>(a, b), "add_words");
  auto c = compile(cs);
  typename Sys<F>::Assignment w;
  w.set(a, word_bits<F>(x1, N)).set(b, word_bits<F>(x2, N));
  w.set(r, word_bits<F>(s, N));
  EXPECT_TRUE(proves<F>(*c, {}, w));
  auto bad = s;
  bad[2] = (bad[2] + 1) % 4096;
  auto wb = w;
  wb.set(r, word_bits<F>(bad, N));
  EXPECT_FALSE(proves<F>(*c, {}, wb, true));
}

// add_bit: words [m, N] plus one bit each, mod 2^N (4095 + 1 is 0, the
// carry out of the top bit dropped), and one word [N] plus a bit; a wrong
// sum is rejected.
TYPED_TEST(LibraryTest, AddBit) {
  using F = TypeParam;
  constexpr size_t N = 12, m = 4;
  const std::vector<uint64_t> x = {4095, 17, 2047, 4095}, bits = {1, 1, 1, 0};
  std::vector<uint64_t> s;
  for (size_t i = 0; i < m; ++i) s.push_back((x[i] + bits[i]) % 4096);
  Sys<F> cs("gh-library-add-bit");
  auto &D = cs.domain(Field<F>::profile(), "D");
  auto t = D.priv(Bit{}, "t", Shape{m, N});
  auto b = D.priv(Bit{}, "b", m);
  auto r = D.priv(Bit{}, "r", Shape{m, N});
  assert_equal(r, lib::arith::add_bit<F>(t, b), "add_bit");
  auto t1 = D.priv(Bit{}, "t1", N);
  auto b1 = D.priv(Bit{}, "b1", 1);
  auto r1 = D.priv(Bit{}, "r1", N);
  assert_equal(r1, lib::arith::add_bit<F>(t1, b1), "add_bit1");
  auto c = compile(cs);
  typename Sys<F>::Assignment w;
  w.set(t, word_bits<F>(x, N)).set(b, word_bits<F>(bits, 1));
  w.set(r, word_bits<F>(s, N));
  w.set(t1, word_bits<F>({1023}, N)).set(b1, word_bits<F>({1}, 1));
  w.set(r1, word_bits<F>({1024}, N));
  EXPECT_TRUE(proves<F>(*c, {}, w));
  // Row 1 without its increment, and row 0's wrapped sum 0 given as 4095.
  for (auto [i, v] : {std::pair{size_t(1), uint64_t(17)},
                      std::pair{size_t(0), uint64_t(4095)}}) {
    auto bad = s;
    bad[i] = v;
    auto wb = w;
    wb.set(r, word_bits<F>(bad, N));
    EXPECT_FALSE(proves<F>(*c, {}, wb, true)) << i;
  }
  auto w1 = w;
  w1.set(r1, word_bits<F>({1023}, N));
  EXPECT_FALSE(proves<F>(*c, {}, w1, true));
}

// The small helpers: index_bits and big_endian_bit_order's values;
// below_constant against a constant of runs of both lengths, prefix_and
// and constant_word in a proof; in odd characteristic, the Lagrange basis
// of [0, 16) at a committed point.
TYPED_TEST(LibraryTest, SmallHelpers) {
  using F = TypeParam;
  EXPECT_EQ(lib::table::index_bits(1), 0u);
  EXPECT_EQ(lib::table::index_bits(2), 1u);
  EXPECT_EQ(lib::table::index_bits(100), 7u);
  EXPECT_EQ(lib::table::index_bits(128), 7u);
  EXPECT_EQ(lib::arith::big_endian_bit_order(2),
            (std::vector<size_t>{8, 9, 10, 11, 12, 13, 14, 15, 0, 1, 2, 3, 4,
                                 5, 6, 7}));
  EXPECT_EQ(lib::arith::big_endian_bit_order(3, 4),
            (std::vector<size_t>{16, 17, 18, 19}));
  // c: ones at 15..12, zeros at 11..9, a one at 8, zeros at 7..4, ones at
  // 3..0.
  constexpr uint64_t c = 0xF10F;
  Sys<F> cs("gh-library-small");
  auto &D = cs.domain(Field<F>::profile(), "D");
  auto x = D.priv(Bit{}, "x", 16);
  assert_true(lib::arith::below_constant(x, {c}), "below");
  auto cols = D.priv(Bit{}, "cols", 5);
  auto pre = D.priv(Bit{}, "prefix", 5);
  std::vector<Expr<F, Bit>> cv;
  for (size_t i = 0; i < 5; ++i) cv.push_back(Expr<F, Bit>(cols).slice(i, i + 1));
  const auto pv = lib::arith::prefix_and<F>(cv);
  for (size_t i = 0; i < 5; ++i)
    assert_equal(Expr<F, Bit>(pre).slice(i, i + 1), pv[i],
                 "prefix." + std::to_string(i));
  auto k = D.priv(Bit{}, "k", 8);
  assert_equal(k, lib::arith::constant_word(D, 0x5A, 8), "word");
  auto c2 = compile(cs);
  typename Sys<F>::Assignment w;
  w.set(cols, word_bits<F>({0b10111}, 5)).set(pre, word_bits<F>({0b00111}, 5));
  w.set(k, word_bits<F>({0x5A}, 8));
  for (uint64_t v : {uint64_t(0), c - 1, uint64_t(0xF0FF), uint64_t(0xE000)}) {
    w.set(x, word_bits<F>({v}, 16));
    EXPECT_TRUE(proves<F>(*c2, {}, w)) << v;
  }
  for (uint64_t v : {c, uint64_t(0xF110), uint64_t(0xF200), uint64_t(0xFFFF)}) {
    auto wb = w;
    wb.set(x, word_bits<F>({v}, 16));
    EXPECT_FALSE(proves<F>(*c2, {}, wb, true)) << v;
  }
  auto wp = w;
  wp.set(pre, word_bits<F>({0b10111}, 5));
  EXPECT_FALSE(proves<F>(*c2, {}, wp, true));
  auto wk = w;
  wk.set(k, word_bits<F>({0x5B}, 8));
  EXPECT_FALSE(proves<F>(*c2, {}, wk, true));
  if constexpr (!F::kCharacteristicTwo) {
    const F &f = Field<F>::f();
    Sys<F> ls("gh-library-lagrange");
    auto &L = ls.domain(Field<F>::profile(), "D");
    auto t = L.priv(gordiehowe::Field{}, "t", 1);
    auto y = L.priv(gordiehowe::Field{}, "y", 1);
    const auto bs = lib::interpolate::lagrange_basis(f, Expr<F>(t), 16);
    ASSERT_EQ(bs.l.size(), 16u);
    assert_zero(bs.z, "range");
    // y = sum_k (k^2 + 1) L_k(t), the table k^2 + 1 at t.
    Expr<F> sum = bs.l[0];
    for (size_t j = 1; j < 16; ++j) sum = sum + (j * j + 1) * bs.l[j];
    assert_zero(Expr<F>(y) - sum, "table");
    auto lc = compile(ls);
    for (uint64_t tv : {uint64_t(0), uint64_t(5), uint64_t(15)}) {
      typename Sys<F>::Assignment a;
      a.set(t, V<F>{f.of_scalar(tv)}).set(y, V<F>{f.of_scalar(tv * tv + 1)});
      EXPECT_TRUE(proves<F>(*lc, {}, a)) << tv;
      a.set(y, V<F>{f.of_scalar(tv * tv + 2)});
      EXPECT_FALSE(proves<F>(*lc, {}, a, true)) << tv;
    }
    typename Sys<F>::Assignment out;
    out.set(t, V<F>{f.of_scalar(16)}).set(y, V<F>{f.of_scalar(257)});
    EXPECT_FALSE(proves<F>(*lc, {}, out, true));
  }
}

// add(x1, x2, x3): the committed partial sum s.p2 = x1 + x2 and the sum
// s, each by its own closure and assert_add_majority, in both
// characteristics; a carry dropped from either is rejected.
TYPED_TEST(LibraryTest, Add) {
  using F = TypeParam;
  const F &f = Field<F>::f();
  constexpr size_t N = 12, m = 4;
  const std::vector<uint64_t> x1 = {4095, 17, 2048, 0}, x2 = {4095, 4000, 2048, 1},
                              x3 = {4095, 300, 0, 4095};
  Sys<F> cs("gh-library-add");
  auto &D = cs.domain(Field<F>::profile(), "D");
  auto w1 = D.priv(Bit{}, "x1", Shape{m, N});
  auto w2 = D.priv(Bit{}, "x2", Shape{m, N});
  auto w3 = D.priv(Bit{}, "x3", Shape{m, N});
  auto want = D.priv(Bit{}, "want", Shape{m, N});
  const auto s = lib::arith::add(w1, w2, w3, "s");
  assert_equal(s, want, "want");
  auto c = compile(cs);
  std::vector<uint64_t> r;
  for (size_t i = 0; i < m; ++i) r.push_back((x1[i] + x2[i] + x3[i]) % 4096);
  typename Sys<F>::Assignment w;
  w.set(w1, word_bits<F>(x1, N)).set(w2, word_bits<F>(x2, N));
  w.set(w3, word_bits<F>(x3, N)).set(want, word_bits<F>(r, N));
  EXPECT_TRUE(proves<F>(*c, {}, w));
  // The committed words without the carries: x1 ^ x2 for s.p2, and s
  // likewise from the honest p2. Where the compiler stores a Bit value as
  // GF(2^16) words (NAME.words, bit c of each the coefficient of beta_c),
  // the cheat replaces those.
  const auto &N_ = s.g->nodes;
  auto node = [&](const std::string &nm) {
    for (size_t id = 0; id < N_.size(); ++id)
      if (N_[id].name == nm) return id;
    return size_t(0);
  };
  std::vector<uint64_t> xr, sr;
  for (size_t i = 0; i < m; ++i) {
    xr.push_back(x1[i] ^ x2[i]);
    sr.push_back(((x1[i] + x2[i]) % 4096) ^ x3[i]);
  }
  for (auto [nm, v] : {std::pair{std::string("s.p2"), xr},
                       std::pair{std::string("s"), sr}}) {
    const auto bits = word_bits<F>(v, N);
    V<F> value = bits;
    size_t id = node(nm + ".words");
    if (id != 0) {
      if constexpr (F::kCharacteristicTwo) {
        value.assign(bits.size() / 16, f.zero());
        for (size_t i = 0; i < bits.size(); ++i)
          if (bits[i] == f.one()) f.add(value[i / 16], f.beta(i % 16));
      }
    } else {
      id = node(nm);
    }
    ASSERT_NE(id, 0u) << nm;
    auto wv = w;
    if (nm == "s") wv.set(want, bits);
    EXPECT_FALSE(proves<F>(*c, {}, wv, true, [&](size_t at, auto &x) {
      if (at == id) std::get<V<F>>(x) = value;
    })) << nm;
  }
}

}  // namespace
}  // namespace proofs::gordiehowe
