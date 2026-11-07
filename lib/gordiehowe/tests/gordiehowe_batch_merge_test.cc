// Copyright 2026 Chad Sharp and Paul Grubbs
// SPDX-License-Identifier: Apache-2.0

// GordieHowe tests (gordiehowe_batch_test binary): a merged bit batch
// (batch.h, MergedOperands), several relations on bit operands of the same
// lanes under one zerocheck of sum_i gamma^i Q_i. Its first round against
// the parts' and the field evaluation, its rows, its challenge points, and
// a system that proves and verifies with it and rejects a witness that
// violates one relation and tampered messages; a disabled timing of the
// merged batch against its relations in batches of their own.

#include "gordiehowe/tests/gordiehowe_batch_test.h"

namespace proofs::gordiehowe {
namespace {

using compiler::BatchKernel;
using compiler::BatchOperands;
using compiler::LaneOperandMap;
using compiler::MaskedFieldSkip;

// x y + z (chi's shape, as a relation tag of its own).
struct Chi : SkipLanes<3> {
  static constexpr unsigned kOperands = 3, kDegree = 2;
  static constexpr size_t kMonomials = 2;
  static constexpr int8_t kTerms[kMonomials][kDegree] = {{0, 1}, {2, -1}};
};
// x + y + z: the XOR of two operands is the third.
struct Xor3 : SkipLanes<3> {
  static constexpr unsigned kOperands = 3, kDegree = 1;
  static constexpr size_t kMonomials = 3;
  static constexpr int8_t kTerms[kMonomials][kDegree] = {{0}, {1}, {2}};
};
// a b + c d + e: an AND-XOR of degree 2 in five operands.
struct AndXor : SkipLanes<5> {
  static constexpr unsigned kOperands = 5, kDegree = 2;
  static constexpr size_t kMonomials = 3;
  static constexpr int8_t kTerms[kMonomials][kDegree] = {
      {0, 1}, {2, 3}, {4, -1}};
};
// a b c + d.
struct Cubic3 : SkipLanes<4> {
  static constexpr unsigned kOperands = 4, kDegree = 3;
  static constexpr size_t kMonomials = 2;
  static constexpr int8_t kTerms[kMonomials][kDegree] = {{0, 1, 2},
                                                         {3, -1, -1}};
};

uint64_t rotl64(uint64_t x, unsigned r) {
  return r ? (x << r) | (x >> (64 - r)) : x;
}

// The lanes of the tables X, Y, Z (random) and the outputs
//   C = X & Y   (chi:    X Y + C = 0),
//   S = X ^ Y   (xor:    X + Y + S = 0),
//   A = (X & Y) ^ (Y & Z)  (and-xor: X Y + Y Z + A = 0),
//   P = rotl(X, 3) & (X ^ Y) & ~Z  (cubic).
struct Lanes {
  std::vector<uint64_t> x, y, z, c, s, a, p;
  explicit Lanes(size_t n, uint64_t seed = 7) {
    std::mt19937_64 g(seed);
    for (size_t l = 0; l < n; ++l) {
      x.push_back(g());
      y.push_back(g());
      z.push_back(g());
      c.push_back(x[l] & y[l]);
      s.push_back(x[l] ^ y[l]);
      a.push_back((x[l] & y[l]) ^ (y[l] & z[l]));
      p.push_back(rotl64(x[l], 3) & (x[l] ^ y[l]) & ~z[l]);
    }
  }
};

Vec words_of_lanes(const std::vector<uint64_t> &lanes, const HF &f) {
  Vec out;
  for (uint64_t x : lanes)
    for (size_t c = 0; c < 4; ++c)
      out.push_back(f.of_scalar(uint16_t(x >> (16 * c))));
  return out;
}

// Operand j of a lane map reads table T[j] (each table N lanes, the
// tables concatenated in order) at lane l.
template <class R>
std::shared_ptr<const LaneOperandMap<HF, R>> lane_map(
    const HF &f, const std::string &name, size_t n, size_t tables,
    std::array<size_t, R::kOperands> t) {
  using M = LaneOperandMap<HF, R>;
  std::array<std::vector<typename M::Lane>, R::kOperands> ops;
  for (unsigned j = 0; j < R::kOperands; ++j)
    for (size_t l = 0; l < n; ++l) ops[j].push_back({0, {{t[j] * n + l, 0}}});
  return std::make_shared<const M>(f, name, 4 * n * tables, ops);
}

// The parts of the merged batch on N lanes, each reading its own tables:
//   chi     (X, Y, C),
//   xor     (X, Y, S),
//   and-xor (X, Y, Y, Z, A),
//   cubic   (X, Y, Z, P): rotl(X, 3), X ^ Y, ~Z, P.
std::shared_ptr<const BatchOperands<HF>> chi_part(const HF &f, size_t n,
                                                   unsigned w) {
  return compiler::bit_batch_operands<HF, Chi, 16>(
      f, lane_map<Chi>(f, "test.chi", n, 3, {0, 1, 2}), w);
}
std::shared_ptr<const BatchOperands<HF>> xor_part(const HF &f, size_t n,
                                                   unsigned w) {
  return compiler::bit_batch_operands<HF, Xor3, 16>(
      f, lane_map<Xor3>(f, "test.xor", n, 3, {0, 1, 2}), w);
}
std::shared_ptr<const BatchOperands<HF>> andxor_part(const HF &f, size_t n,
                                                      unsigned w) {
  return compiler::bit_batch_operands<HF, AndXor, 16>(
      f, lane_map<AndXor>(f, "test.and-xor", n, 4, {0, 1, 1, 2, 3}), w);
}
// Tables X, Y, Z, P: rotl(X, 3), X ^ Y, ~Z, P.
std::shared_ptr<const LaneOperandMap<HF, Cubic3>> cubic3_map(const HF &f,
                                                              size_t n) {
  using M = LaneOperandMap<HF, Cubic3>;
  std::array<std::vector<M::Lane>, 4> ops;
  for (size_t l = 0; l < n; ++l) {
    ops[0].push_back({0, {{l, 3}}});
    ops[1].push_back({0, {{l, 0}, {n + l, 0}}});
    ops[2].push_back({~uint64_t(0), {{2 * n + l, 0}}});
    ops[3].push_back({0, {{3 * n + l, 0}}});
  }
  return std::make_shared<const M>(f, "test.cubic", 16 * n, ops);
}
std::shared_ptr<const BatchOperands<HF>> cubic_part(const HF &f, size_t n,
                                                     unsigned w) {
  return compiler::bit_batch_operands<HF, Cubic3, 16>(f, cubic3_map(f, n), w);
}

// The words of the parts KINDS ("chi", "xor", "and-xor", "cubic") read, in
// order.
Vec part_words(const std::vector<std::string> &kinds, const Lanes &ln,
               const HF &f) {
  Vec out;
  auto put = [&](std::initializer_list<const std::vector<uint64_t> *> ts) {
    for (const auto *t : ts) {
      const Vec w = words_of_lanes(*t, f);
      out.insert(out.end(), w.begin(), w.end());
    }
  };
  for (const auto &k : kinds) {
    if (k == "chi") put({&ln.x, &ln.y, &ln.c});
    if (k == "xor") put({&ln.x, &ln.y, &ln.s});
    if (k == "and-xor") put({&ln.x, &ln.y, &ln.z, &ln.a});
    if (k == "cubic") put({&ln.x, &ln.y, &ln.z, &ln.p});
  }
  return out;
}
std::shared_ptr<const BatchOperands<HF>> part_of(const std::string &k,
                                                  size_t n, unsigned w) {
  const HF &f = env().hf;
  if (k == "chi") return chi_part(f, n, w);
  if (k == "xor") return xor_part(f, n, w);
  if (k == "and-xor") return andxor_part(f, n, w);
  return cubic_part(f, n, w);
}
std::shared_ptr<const BatchOperands<HF>> merged_of(
    const std::vector<std::string> &kinds, size_t n, unsigned w) {
  std::vector<std::shared_ptr<const BatchOperands<HF>>> parts;
  for (const auto &k : kinds) parts.push_back(part_of(k, n, w));
  if (parts.size() == 1) return parts[0];
  return std::make_shared<compiler::MergedOperands<HF>>(env().hf, parts, w);
}

BasicTranscript<SHA384> transcript(const char *label) {
  BasicProofSeed<SHA384> seed;
  std::memset(seed.bytes, 0, sizeof(seed.bytes));
  return BasicTranscript<SHA384>(reinterpret_cast<const uint8_t *>(label),
                                 std::strlen(label), seed);
}

// Instance t = 64 l + b of lane map M's operands: bit b of lane l, as a
// field element.
template <class R>
void field_operands(const LaneOperandMap<HF, R> &m, const Vec &words,
                    std::vector<std::vector<HElt>> &ops) {
  const HF &f = env().hf;
  std::vector<uint16_t> host;
  for (const auto &x : words) {
    uint8_t b[2];
    f.to_bytes_subfield(b, x);
    host.push_back(uint16_t(b[0] | (b[1] << 8)));
  }
  const auto lanes = m.apply(host);
  ops.resize(lanes.size() * 64);
  for (size_t l = 0; l < lanes.size(); ++l)
    for (size_t b = 0; b < 64; ++b)
      for (unsigned j = 0; j < R::kOperands; ++j)
        ops[64 * l + b].push_back(f.of_scalar((lanes[l][j] >> b) & 1));
}

// The merged first round equals the sum of gamma^i times the parts' own
// (bit-sliced) first rounds when the parts share the degree, and equals the
// field evaluation of sum_i gamma^i Q_i on the operand bits for parts of
// degrees 1, 2 and 3 (the lower ones interpolated to the batch's points);
// its bound operands are the field evaluation's.
TEST(GordieHoweBatchMerge, FirstRoundIsTheGammaSum) {
  const HF &f = env().hf;
  constexpr size_t n = 21;
  const Lanes ln(n);
  SecureRandomEngine rng;
  for (unsigned w : {1u, 4u, 16u}) {
    // Same degree: chi and and-xor.
    {
      const std::vector<std::string> kinds = {"chi", "and-xor"};
      const auto merged = merged_of(kinds, n, w);
      const HElt gamma = rng.elt(f);
      const MaskedFieldSkip<HF> sk(f, merged->relation(gamma), 64 * n, w);
      std::vector<HElt> e(size_t(1) << sk.layout.logs);
      for (auto &x : e) x = rng.elt(f);
      const Vec words = part_words(kinds, ln, f);
      const auto got = merged->first_round(sk, words, {}, nullptr)
                           ->skip_values(sk, e);
      std::vector<HElt> want(sk.extra(), f.zero());
      HElt g = f.one();
      size_t at = 0;
      for (const auto &k : kinds) {
        const auto p = part_of(k, n, w);
        const MaskedFieldSkip<HF> pk(f, p->relation(f.one()), 64 * n, w);
        const Vec pw(words.begin() + long(at),
                     words.begin() + long(at + p->words()));
        const auto v = p->first_round(pk, pw, {}, nullptr)->skip_values(pk, e);
        ASSERT_EQ(v.size(), want.size());
        for (size_t j = 0; j < v.size(); ++j)
          f.add(want[j], f.mulf(g, v[j]));
        f.mul(g, gamma);
        at += p->words();
      }
      EXPECT_EQ(got, want) << "width " << w;
    }
    // Degrees 2, 1 and 3: against the field evaluation.
    {
      const std::vector<std::string> kinds = {"chi", "xor", "cubic"};
      const auto merged = merged_of(kinds, n, w);
      const HElt gamma = rng.elt(f);
      const MaskedFieldSkip<HF> sk(f, merged->relation(gamma), 64 * n, w);
      EXPECT_EQ(sk.D, 3u);
      EXPECT_EQ(sk.K, 10u);
      std::vector<HElt> e(size_t(1) << sk.layout.logs);
      for (auto &x : e) x = rng.elt(f);
      const Vec words = part_words(kinds, ln, f);
      std::vector<std::vector<HElt>> ops(64 * n), po;
      const Vec wc(words.begin(), words.begin() + long(12 * n));
      const Vec wx(words.begin() + long(12 * n), words.begin() + long(24 * n));
      const Vec wq(words.begin() + long(24 * n), words.end());
      field_operands(*lane_map<Chi>(f, "c", n, 3, {0, 1, 2}), wc, po);
      for (size_t t = 0; t < ops.size(); ++t) ops[t] = po[t];
      po.clear();
      field_operands(*lane_map<Xor3>(f, "x", n, 3, {0, 1, 2}), wx, po);
      for (size_t t = 0; t < ops.size(); ++t)
        ops[t].insert(ops[t].end(), po[t].begin(), po[t].end());
      po.clear();
      field_operands(*cubic3_map(f, n), wq, po);
      for (size_t t = 0; t < ops.size(); ++t)
        ops[t].insert(ops[t].end(), po[t].begin(), po[t].end());
      const compiler::FieldSkipOperands<HF> ref(ops);
      const auto first = merged->first_round(sk, words, {}, nullptr);
      EXPECT_EQ(first->skip_values(sk, e), ref.skip_values(sk, e))
          << "width " << w;
      const HElt r = rng.elt(f);
      const auto a = first->bind(sk, r), b = ref.bind(sk, r);
      ASSERT_EQ(a.size(), b.size());
      for (size_t j = 0; j < a.size(); ++j)
        EXPECT_TRUE(std::equal(a[j].begin(), a[j].end(), b[j].begin()))
            << "width " << w << " operand " << j;
    }
  }
}

// The reduction of KERNEL on WORDS: its rows over the words and the pads
// (pads after the words), whether every row holds, and the challenge
// points the prover's and the verifier's transcripts open.
struct Reduced {
  bool holds = true, same_rows = true;
  size_t prover_points = 0, verifier_points = 0;
};
Reduced reduce(const BatchKernel<HF, SHA384> &kb, const Vec &words,
               std::function<void(std::vector<HElt> &)> tamper = nullptr) {
  const HF &f = env().hf;
  Reduced out;
  std::vector<HElt> pads(kb.pads());
  SecureRandomEngine rng;
  kb.fill_pads(pads.data(), rng);
  Vec w = words;
  w.insert(w.end(), pads.begin(), pads.end());
  auto tp = transcript("merged-bit-batch");
  const size_t p0 = tp.stats().points;
  std::vector<HElt> msgs;
  typename BatchKernel<HF, SHA384>::Tamper tm;
  tm.messages = tamper;
  const auto rows = kb.reduce(tp, msgs, words.size(), &words, pads.data(), tm);
  out.prover_points = tp.stats().points - p0;
  auto tv = transcript("merged-bit-batch");
  const size_t v0 = tv.stats().points;
  const auto vrows = kb.reduce(tv, msgs, words.size(), nullptr, nullptr, {});
  out.verifier_points = tv.stats().points - v0;
  out.same_rows = rows.b == vrows.b && rows.a.size() == vrows.a.size();
  // The verifier's rows on the prover's words and pads: the bit claim's
  // forms sum_k Frob^k(<a_k, W>).
  std::vector<HElt> lhs(vrows.b.size(), f.zero());
  for (const auto &t : vrows.a) f.add(lhs[t.c], f.mulf(t.k, w[t.w]));
  const auto &fm = *vrows.forms;
  for (size_t k = 0; k * fm.stride < fm.a.size(); ++k) {
    HElt ip = f.zero();
    for (size_t y = 0; y < fm.stride; ++y)
      f.add(ip, f.mulf(fm.a[k * fm.stride + y], words[y]));
    f.add(lhs[vrows.form_row], frobenius(ip, k, f));
  }
  for (size_t r = 0; r < vrows.b.size(); ++r)
    out.holds = out.holds && lhs[r] == vrows.b[r];
  return out;
}

// The merged batch's rows hold on an honest witness and the verifier
// replays them; a witness that violates one relation, or a tampered
// message, breaks them. Merged or not, the reduction opens the same
// challenge points (gamma shares the zerocheck's first).
TEST(GordieHoweBatchMerge, RowsHoldAndChallengePoints) {
  const HF &f = env().hf;
  constexpr size_t n = 37;
  const Lanes ln(n);
  for (unsigned w : {1u, 16u}) {
    const auto single = std::make_shared<BatchKernel<HF, SHA384>>(
        f, merged_of({"chi"}, n, w), w);
    const Reduced one = reduce(*single, part_words({"chi"}, ln, f));
    EXPECT_TRUE(one.holds && one.same_rows) << "width " << w;
    for (const auto &kinds : std::vector<std::vector<std::string>>{
             {"chi", "xor"}, {"chi", "xor", "cubic"}}) {
      const auto kb = std::make_shared<BatchKernel<HF, SHA384>>(
          f, merged_of(kinds, n, w), w);
      const Vec words = part_words(kinds, ln, f);
      const Reduced r = reduce(*kb, words);
      EXPECT_TRUE(r.holds) << "width " << w << " parts " << kinds.size();
      EXPECT_TRUE(r.same_rows);
      EXPECT_EQ(r.prover_points, one.prover_points) << "width " << w;
      EXPECT_EQ(r.verifier_points, one.verifier_points) << "width " << w;
      // One bit of S (xor's output, the second part's third table) flipped.
      Vec bad = words;
      const size_t at = 12 * n + 8 * n + 5;
      uint8_t b[2];
      f.to_bytes_subfield(b, bad[at]);
      bad[at] = f.of_scalar(uint16_t((b[0] | (b[1] << 8)) ^ 0x40));
      EXPECT_FALSE(reduce(*kb, bad).holds) << "width " << w;
      // A message changed before it is absorbed: the first and the last.
      for (bool last : {false, true})
        EXPECT_FALSE(reduce(*kb, words, [last](std::vector<HElt> &m) {
                       env().hf.add(last ? m.back() : m.front(),
                                    env().hf.one());
                     }).holds)
            << "width " << w << (last ? " last" : " first");
    }
  }
}

// ----------------------------------------------------- the system level --

// Tables X, Y, Z (random) and C, S, P, and the relations chi (X, Y, C),
// xor (X, Y, S) and cubic (X, Y, Z, P): merged in one batch, or each in a
// batch of its own.
struct MergedSystem {
  Sys cs{"gordiehowe-merged-bits"};
  Domain<HF> *H;
  Ref<HF> first;
  Ref<HF, Subfield<>, Committed> X, Y, Z, C, S, P;
  size_t n;
  MergedSystem(size_t lanes, unsigned width, bool merged) : n(lanes) {
    const HF *pf = &env().hf;
    H = &cs.domain(env().profile(), "H");
    first = H->pub(Field{}, "first", 1);
    X = H->priv(Subfield{}, "X", 4 * n);
    Y = H->priv(Subfield{}, "Y", 4 * n);
    Z = H->priv(Subfield{}, "Z", 4 * n);
    const size_t nn = n;
    auto out = [pf, nn](int k) {
      return [pf, nn, k](const Vec &x, const Vec &y, const Vec &z) {
        std::vector<uint64_t> v(nn);
        for (size_t l = 0; l < nn; ++l) {
          const uint64_t a = lane_of(x, l, *pf), b = lane_of(y, l, *pf),
                         c = lane_of(z, l, *pf);
          v[l] = k == 0 ? a & b : k == 1 ? a ^ b : rotl64(a, 3) & (a ^ b) & ~c;
        }
        return words_of_lanes(v, *pf);
      };
    };
    C = H->priv(Subfield{}, "C", 4 * n, depends_on(X, Y, Z), out(0));
    S = H->priv(Subfield{}, "S", 4 * n, depends_on(X, Y, Z), out(1));
    P = H->priv(Subfield{}, "P", 4 * n, depends_on(X, Y, Z), out(2));
    L::gkr(*H, "X[0] = first", depends_on(X, first),
           [](const auto &lc, const auto &x, const auto &f) {
             lc.assert_eq(x[0], f[0]);
           });
    auto chi = lane_map<Chi>(*pf, "test.chi", n, 3, {0, 1, 2});
    auto xr = lane_map<Xor3>(*pf, "test.xor", n, 3, {0, 1, 2});
    auto cu = cubic3_map(*pf, n);
    if (merged) {
      H->batch("merged", {X, Y, C, X, Y, S, X, Y, Z, P},
               {compiler::bit_batch_part<HF, Chi>(chi),
                compiler::bit_batch_part<HF, Xor3>(xr),
                compiler::bit_batch_part<HF, Cubic3>(cu)},
               width);
    } else {
      H->batch("chi", {X, Y, C}, Chi{}, chi, width);
      H->batch("xor", {X, Y, S}, Xor3{}, xr, width);
      H->batch("cubic", {X, Y, Z, P}, Cubic3{}, cu, width);
    }
  }
  static uint64_t lane_of(const Vec &w, size_t l, const HF &f) {
    uint64_t v = 0;
    for (size_t c = 0; c < 4; ++c) {
      uint8_t b[2];
      f.to_bytes_subfield(b, w[4 * l + c]);
      v |= uint64_t(b[0] | (b[1] << 8)) << (16 * c);
    }
    return v;
  }
  Vec lanes(uint64_t seed) const {
    std::mt19937_64 g(seed);
    std::vector<uint64_t> v(n);
    for (auto &x : v) x = g();
    return words_of_lanes(v, env().hf);
  }
  Assignment witness() const {
    Assignment w;
    w.set(X, lanes(1)).set(Y, lanes(2)).set(Z, lanes(3));
    return w;
  }
  Assignment statement() const {
    Assignment st;
    st.set(first, Vec{lanes(1)[0]});
    return st;
  }
};

// Flips bit 5 of word 9 of table ID in the prover's values.
ProveOptions flip(size_t id) {
  ProveOptions opt;
  opt.require_satisfied = false;
  opt.tamper = [id](size_t x, SysValue &v) {
    if (x != id) return;
    const HF &f = env().hf;
    auto &w = std::get<Vec>(v);
    uint8_t b[2];
    f.to_bytes_subfield(b, w[9]);
    w[9] = f.of_scalar(uint16_t((b[0] | (b[1] << 8)) ^ (1u << 5)));
  };
  return opt;
}

TEST(GordieHoweBatchMerge, ProveVerify) {
  for (unsigned width : {1u, 16u}) {
    MergedSystem t(37, width, true);
    auto c = compile(t.cs);
    std::printf("%s", c->report().c_str());
    auto prep = c->prepare(t.statement());
    SecureRandomEngine rng;
    const auto proof = prep.prove(t.witness(), rng);
    EXPECT_TRUE(prep.verify(proof)) << "width " << width;
    // A witness that violates one relation: C (chi), S (xor) or P (cubic).
    for (size_t id : {t.C.id, t.S.id, t.P.id})
      EXPECT_FALSE(prep.verify(prep.prove(t.witness(), rng, flip(id))))
          << "width " << width << " table " << id;
    // Changed batch message bytes.
    const auto sp = c->batch_message_span(0);
    for (size_t at : {sp.offset, sp.offset + sp.length / 2,
                      sp.offset + sp.length - 1}) {
      auto bad = proof;
      bad[at] ^= 1;
      EXPECT_FALSE(prep.verify(bad)) << "message byte " << at - sp.offset;
    }
    // Messages tampered before they are absorbed: the first, a round
    // coefficient and the last terminal value.
    // Width 16: (D - 1)(w - 1) = 30 skip values and 8 rounds of 3; width 1:
    // none and 12 rounds; then the 10 terminal values.
    const size_t skip = width == 16 ? 30 : 0, rounds = width == 16 ? 8 : 12;
    for (size_t i : {size_t(0), skip + 1, skip + 3 * rounds + 9})
      EXPECT_FALSE(tampered_message_accepted(prep, t.witness(), i))
          << "width " << width << " message " << i;
  }
}

// The merged batch against its relations in batches of their own, on
// GH_MERGE_LANES lanes (default 4096): prover and verifier times and proof
// bytes, GH_REPS repetitions.
TEST(GordieHoweBatchMerge, DISABLED_Timing) {
  using Clock = std::chrono::steady_clock;
  auto ms = [](Clock::time_point t0) {
    return std::chrono::duration<double, std::milli>(Clock::now() - t0).count();
  };
  const size_t lanes = std::getenv("GH_MERGE_LANES")
                           ? std::stoul(std::getenv("GH_MERGE_LANES"))
                           : 4096;
  const size_t reps =
      std::getenv("GH_REPS") ? std::stoul(std::getenv("GH_REPS")) : 5;
  for (bool merged : {false, true}) {
    MergedSystem t(lanes, 16, merged);
    auto c = compile(t.cs);
    auto prep = c->prepare(t.statement());
    SecureRandomEngine rng;
    for (size_t r = 0; r < reps; ++r) {
      ProveTimes pt;
      ProveOptions opt;
      opt.times = &pt;
      const auto proof = prep.prove(t.witness(), rng, opt);
      const auto t0 = Clock::now();
      const bool ok = prep.verify(proof);
      const double v = ms(t0);
      std::printf("GH_MERGE_RUN merged=%d lanes=%zu witness=%.3f "
                  "commit=%.3f prove=%.3f verify=%.3f bytes=%zu ok=%d\n",
                  int(merged), lanes, pt.witness, pt.commit, pt.prove, v,
                  proof.size(), int(ok));
      std::fflush(stdout);
      EXPECT_TRUE(ok);
    }
  }
}

}  // namespace
}  // namespace proofs::gordiehowe
