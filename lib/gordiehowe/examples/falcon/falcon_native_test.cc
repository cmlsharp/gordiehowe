// Copyright 2026 Chad Sharp and Paul Grubbs
// SPDX-License-Identifier: Apache-2.0

// GordieHowe: the Falcon-512 native proof of possession (falcon_native.h),
// checked against host values (falcon_hash_to_point.h, falcon_ntt.h,
// falcon_encoding.h) on the benchmark instance's key and message.
//
//   ProveVerifyMatchesHostWitness       honest proofs; c, s1 and the MAC's
//                                       quotient digits equal the host
//                                       values
//   MacAccumulatorsMatchReference       the MAC's grouped accumulators
//                                       against the schoolbook product and
//                                       the MAC field
//   PrivateLengths                      one relation, messages of several
//                                       private lengths up to its maximum
//   TamperRejected                      a cheating prover's proof fails, per
//                                       gadget
//   InvalidSignatureRejected            a budget overrun and an oversized
//                                       norm from the honest generators
//   MalformedKeyFailsVerification       the key codec
//   Layout                              cells, needles, groups, realizations
//   ProgramExport                       the realized program's invariants
//                                       (plan_program.h)
//   LigeroTarget                        both domains at list radius at the
//                                       profile's target
//
// The benches, the plan export and the compile report are
// falcon_native_bench's commands (falcon_native_bench.cc).

#include "gordiehowe/examples/falcon/falcon_native_fixture.h"
#include "gordiehowe/examples/shared/ligero_testing.h"

namespace proofs::gordiehowe::examples::falcon::native {
namespace {

template <class P>
class FalconNativeProfile : public ::testing::Test {};
TYPED_TEST_SUITE(FalconNativeProfile, param_sets::Profiles,
                 param_sets::ProfileName);

template <class F>
std::vector<uint64_t> ints(const F &f, const std::vector<typename F::Elt> &x) {
  std::vector<uint64_t> out(x.size());
  for (size_t i = 0; i < x.size(); ++i) out[i] = uint64_t(nat_of(f, x[i]));
  return out;
}
template <class F>
std::vector<uint64_t> words_of_bits(const F &f,
                                    const std::vector<typename F::Elt> &bits) {
  std::vector<uint64_t> b;
  for (const auto &x : bits) b.push_back(ct::bit_of(f, x));
  return host::words_of_bits(Tensor<uint64_t>(b, {b.size() / 16, 16}));
}

// An honest proof verifies; c and s1 equal the host values on the same key
// and message, and the MAC's group quotient digits are those of its
// accumulators.
TYPED_TEST(FalconNativeProfile, ProveVerifyMatchesHostWitness) {
  using P = TypeParam;
  using X = Fixture<P>;
  using HF = typename X::HF;
  X x;
  ASSERT_TRUE(falcon_encoding_advice(x.in.s2, kQ, kHighBudget).encodable);
  const auto &t = x.t;
  std::map<size_t, typename X::Value> cap;
  typename X::ProveOptions opt;
  opt.tamper = [&](size_t id, typename X::Value &v) { cap[id] = v; };
  ProveTimes pt;
  opt.times = &pt;
  auto prep = x.c->prepare(t.statement(x.in.hhat));
  SecureRandomEngine rng;
  const auto proof = prep.prove(x.witness(), rng, opt);
  std::printf("%s proof bytes %zu, witness %.1f commit %.1f prove %.1f ms\n",
              P::kId, proof.size(), pt.witness, pt.commit, pt.prove);
  EXPECT_TRUE(prep.verify(proof));

  const auto &hf = x.env.hf;
  const auto &af = x.env.af;
  auto hget = [&](const char *nm) {
    const auto it = cap.find(x.id(nm));
    if (it == cap.end()) ADD_FAILURE() << "not captured: " << nm;
    return it == cap.end() ? typename X::HV{}
                           : std::get<typename X::HV>(it->second);
  };
  auto aget = [&](const char *nm) {
    const auto it = cap.find(x.id(nm));
    if (it == cap.end()) ADD_FAILURE() << "not captured: " << nm;
    return it == cap.end() ? typename X::AV{}
                           : std::get<typename X::AV>(it->second);
  };
  auto aints = [&](const char *nm) { return ints(af, aget(nm)); };
  const std::vector<uint64_t> c_old(x.in.hw.c.begin(), x.in.hw.c.end());
  EXPECT_EQ(words_of_bits(hf, hget("h2p.select.raw")), c_old);
  EXPECT_EQ(words_of_bits(af, aget("crossing.c_A")), c_old);
  EXPECT_EQ(aints("signature.s1"), reference::s1(x.in));
  // The MAC's quotient digits: the base-64 digits of floor(acc / 2) at
  // this proof's group accumulators. The powers r are a public function of
  // the challenge, which the tamper hook does not see;
  // MacAccumulatorsMatchReference checks the accumulators themselves at
  // sampled powers.
  const auto acc = aints("mac.acc");
  std::vector<uint64_t> gq;
  for (uint64_t a : acc) {
    uint64_t v = (a - (a & 1)) / 2;
    for (size_t l = 0; l < param_sets::Derived<P>::kGroupQuotientLimbs; ++l) {
      gq.push_back(v % kTable);
      v /= kTable;
    }
  }
  EXPECT_EQ(aints("mac.gq"), gq);
  (void)sizeof(HF);
}

// The MAC's grouped accumulators (mac_grouped_accumulator_elements, the
// generator of mac.acc) at sampled powers, on the benchmark instance's c,
// equal the reference: for each group, the schoolbook integer coefficients
// sum_{i + j = k} X_c[i] R_c[j] summed over the group's chunks, each
// monomial x^k with k >= w then replaced once by the bits of x^k in the MAC
// field (def:macconv). Their parities are the coordinates of the MAC tag
// sum_c R_c X_c in the MAC field.
TYPED_TEST(FalconNativeProfile, MacAccumulatorsMatchReference) {
  using P = TypeParam;
  using MF = typename P::MacField;
  constexpr size_t kW = P::Mac::kBits;
  constexpr size_t G = param_sets::Derived<P>::kG;
  const Env<P> env;
  const auto in = reference::instance();
  const std::vector<uint64_t> c(in.hw.c.begin(), in.hw.c.end());
  const size_t nch = 16 * kN / kW;
  SecureRandomEngine rng;
  std::vector<typename MF::Elt> r(nch);
  for (size_t ch = 0; ch < nch; ++ch) r[ch] = rng.elt(env.mf);
  std::vector<uint8_t> x(16 * kN);
  for (size_t j = 0; j < kN; ++j)
    for (size_t b = 0; b < 16; ++b) x[16 * j + b] = uint8_t((c[j] >> b) & 1);
  std::vector<std::pair<size_t, size_t>> groups;
  for (size_t a = 0; a < nch; a += G) groups.push_back({a, std::min(a + G, nch)});
  const auto acc =
      ints(env.af, compiler::mac_grouped_accumulator_elements<MF>(
                       env.af, kQ, x, r, ops::mac_taps(env.mf), groups));
  const MF &mf = env.mf;
  // x^k in the MAC field for k = w..2w-2.
  std::vector<typename MF::Elt> xk(kW - 1);
  xk[0] = mf.one();
  for (size_t i = 0; i < kW; ++i) xk[0] = mf.mulf(xk[0], mf.of_scalar_field(0b10));
  for (size_t k = 1; k < kW - 1; ++k)
    xk[k] = mf.mulf(xk[k - 1], mf.of_scalar_field(0b10));
  std::vector<uint64_t> ref;
  for (const auto &[a, e] : groups) {
    std::vector<uint64_t> s(2 * kW - 1, 0);
    auto tag = mf.zero();
    for (size_t ch = a; ch < e; ++ch) {
      std::vector<uint8_t> bytes(MF::kBytes, 0);
      for (size_t i = 0; i < kW; ++i) {
        const uint8_t xi = x[ch * kW + i];
        bytes[i / 8] |= uint8_t(xi << (i % 8));
        for (size_t j = 0; j < kW; ++j) s[i + j] += xi & r[ch][j];
      }
      tag = mf.addf(tag, mf.mulf(r[ch], mf.of_bytes_field(bytes.data()).value()));
    }
    for (size_t k = kW; k <= 2 * kW - 2; ++k)
      for (size_t b = 0; b < kW; ++b)
        if (xk[k - kW][b]) s[b] += s[k];
    for (size_t b = 0; b < kW; ++b) {
      EXPECT_EQ(s[b] & 1, uint64_t(tag[b])) << "group " << a << " bit " << b;
      ref.push_back(s[b]);
    }
  }
  EXPECT_EQ(acc, ref);
}

// One relation over messages of at most 300 bytes. Messages of 0, 95, 96,
// 200 and 300 bytes prove and verify, each under its own key: nonce ||
// message of 40 to 340 bytes, so SHAKE256's suffix and 0x80 share byte
// 135, open block 1, and fill one to three blocks. A cheating prover's
// witness fails: the length member one more than the message's, and a
// nonzero buffer byte past the padding. A message over the maximum has no
// witness.
TYPED_TEST(FalconNativeProfile, PrivateLengths) {
  using P = TypeParam;
  using T = FalconNativeSystem<P>;
  using Sys = typename T::Sys;
  constexpr size_t kMax = 300;
  const Env<P> env;
  const T t(env, kMax);
  const auto c = t.compile();
  const auto &typed = t.rel.template typed<Sys>();
  for (size_t len : {0, 95, 96, 200, 300}) {
    const auto in = reference::instance(len);
    EXPECT_TRUE(message::testing::accepts<Sys>(
        *c, t.statement(in.hhat), t.witness(in.nonce, in.msg, in.s2)))
        << len;
  }
  const auto in = reference::instance(200);
  const auto st = t.statement(in.hhat);
  auto longer = falcon_witness(in.nonce, in.msg, in.s2, kMax);
  longer.msg_length = 201;
  EXPECT_FALSE(
      message::testing::accepts<Sys>(*c, st, typed.witness(longer), false));
  auto trailing = falcon_witness(in.nonce, in.msg, in.s2, kMax);
  trailing.message.back() = 1;
  EXPECT_FALSE(
      message::testing::accepts<Sys>(*c, st, typed.witness(trailing), false));
  EXPECT_ANY_THROW(falcon_witness(in.nonce, std::vector<uint8_t>(kMax + 1),
                                  in.s2, kMax));
}

// A cheating prover's proof fails verification, per gadget:
//   hash       a bit of h2p.select.raw (c_A copies it: the selection fails)
//   MAC        a bit of c_A (c_A != c_H; the algebra follows c_A)
//   signature  s1 + 1 (the norm's digits follow it: the affine row fails)
//   magnitude  a norm digit + 1 (the squares follow it: the centering fails)
//   square     a square digit + 1 (its column fails)
//   carry      a column carry + 1
//   running    a normalized running-sum digit + 1 (its row fails)
//   bound      a complement digit + 1 (S + D = beta^2 fails)
//   digit      d0 + 64, d1 - 1 of a magnitude: the same value, a digit
//              outside the table (the lookup fails)
//   encoding   the top digit slot h of s2's coefficient 5 + 1 (b = a1 - 2h
//              is not a bit)
//   MAC digit  a group quotient digit + 1 (the parity is not a bit)
TYPED_TEST(FalconNativeProfile, TamperRejected) {
  using P = TypeParam;
  using X = Fixture<P>;
  using Value = typename X::Value;
  using AV = typename X::AV;
  using HV = typename X::HV;
  X x;
  const auto &hf = x.env.hf;
  const auto &af = x.env.af;
  auto flip_h = [&](size_t target, size_t i) {
    return [&, target, i](size_t id, Value &v) {
      if (id != target) return;
      auto &b = std::get<HV>(v);
      b.at(i) = b[i] == hf.one() ? hf.zero() : hf.one();
    };
  };
  auto flip_a = [&](size_t target, size_t i) {
    return [&, target, i](size_t id, Value &v) {
      if (id != target) return;
      auto &b = std::get<AV>(v);
      b.at(i) = b[i] == af.one() ? af.zero() : af.one();
    };
  };
  auto add_a = [&](size_t target, size_t i, int64_t k) {
    return [&, target, i, k](size_t id, Value &v) {
      if (id != target) return;
      auto &a = std::get<AV>(v);
      const auto d = af.of_scalar(uint64_t(k < 0 ? -k : k));
      a.at(i) = k < 0 ? af.subf(a[i], d) : af.addf(a[i], d);
    };
  };
  // A magnitude whose second digit is nonzero (s1's coefficient 0..): the
  // centered |s1| in base B.
  const size_t a_id = x.id("norm.a");
  const auto s1 = reference::s1(x.in);
  const uint64_t B = P::kFalconNative.B;
  auto mag = [](uint64_t v) { return v <= kQ / 2 ? v : kQ - v; };
  size_t at = 0;
  while ((mag(s1[at]) / B) % B == 0) ++at;
  auto digit = [&, a_id, at](size_t id, Value &v) {
    if (id != a_id) return;
    add_a(a_id, 3 * at, 64)(id, v);
    add_a(a_id, 3 * at + 1, -1)(id, v);
  };
  const std::vector<std::pair<std::string, std::function<void(size_t, Value &)>>>
      cases = {
          {"c bit", flip_h(x.id("h2p.select.raw"), 16 * 7 + 3)},
          {"MAC (c_A != c_H)", flip_a(x.id("crossing.c_A"), 16 * 100 + 3)},
          {"signature s1", add_a(x.id("signature.s1"), 5, 1)},
          {"magnitude digit", add_a(a_id, 3 * 9, 1)},
          {"square digit", add_a(x.id("norm.sq"), 6 * 11, 1)},
          {"column carry", add_a(x.id("norm.cc"), 10 * 13 + 2, 1)},
          {"running sum", add_a(x.id("norm.nd"), 6 * 3 + 2, 1)},
          {"complement", add_a(x.id("norm.D"), 1, 1)},
          {"out-of-range digit", digit},
          {"encoding high part", add_a(a_id, 3 * (kN + 5) + 2, 1)},
          {"MAC quotient digit", add_a(x.id("mac.gq"), 7, 1)},
      };
  for (const auto &[name, tamper] : cases)
    EXPECT_FALSE(x.accepts(tamper)) << P::kId << ": " << name;
}

// Statements whose signature is invalid, from the honest generators; a
// prover that proceeds is rejected.
//   budget   400 coefficients of s2 with magnitude 200: sum high = 400 > J
//            = 392, with the norm in bound.
//   norm     every coefficient of s1 of magnitude 300: 512 * 300^2 > beta^2.
//            The complement is zero and its affine row, which only the
//            verifier checks, fails.
TYPED_TEST(FalconNativeProfile, InvalidSignatureRejected) {
  using P = TypeParam;
  std::mt19937 g(7);
  auto small = [&g](size_t) { return int64_t(g() % 61) - 30; };
  auto sign = [](size_t i) { return (i * 2654435761u >> 7) & 1 ? 1 : -1; };
  {
    auto s2c = [&](size_t i) {
      return i < 400 ? 200 * sign(i) : int64_t(i % 17) - 8;
    };
    Fixture<P> x(chosen_instance(small, s2c));
    EXPECT_TRUE(x.prover_refuses()) << "budget";
    EXPECT_FALSE(x.accepts({})) << "budget";
  }
  {
    auto s1c = [&](size_t i) { return int64_t(300) * sign(i); };
    Fixture<P> x(chosen_instance(s1c, small));
    EXPECT_FALSE(x.accepts({})) << "norm";
  }
}

// The key's codec: a coordinate at least q fails verification of an
// honest proof, before the key is decoded, and the prover refuses it;
// another canonical key fails too.
TYPED_TEST(FalconNativeProfile, MalformedKeyFailsVerification) {
  using P = TypeParam;
  Fixture<P> x;
  auto prep = x.c->prepare(x.t.statement(x.in.hhat));
  SecureRandomEngine rng;
  const auto proof = prep.prove(x.witness(), rng);
  ASSERT_TRUE(prep.verify(proof));
  auto bad = x.in.hhat;
  bad[17] += kQ;
  auto pb = x.c->prepare(x.t.statement(bad));
  EXPECT_EQ(pb.rejected_statement(), "statement");
  EXPECT_FALSE(pb.verify(proof));
  EXPECT_THROW(pb.prove(x.witness(), rng), std::runtime_error);
  bad = x.in.hhat;
  bad[17] = (bad[17] + 1) % kQ;
  EXPECT_FALSE(x.c->prepare(x.t.statement(bad)).verify(proof));
}



// A's layout: the norm's column carries in a table of 189 rows (one
// carry per column, below the honest 189), the
// other static needles and every late MAC needle in the table of 64 under
// one late histogram (one group of at most 12288 needles in both profiles),
// the field equality, and the MAC's grouping.
TYPED_TEST(FalconNativeProfile, Layout) {
  using P = TypeParam;
  const Env<P> env;
  FalconNativeSystem<P> t(env, 32);
  auto c = t.compile();
  const std::string r = c->report();
  const bool qrom = P::kPostQuantum;
  for (const std::string want : {
           std::string("assert_mod 'signature.equation': m = p = 12289, the "
                       "field equality (512 affine rows)"),
           std::string("norm.cc: direct T=189 -> bound 189"),
           std::string("encoding.high: complement T=64"),
           qrom ? std::string("table A.64: 9925 static and 2304 dynamic "
                              "needles; one late histogram of 64")
                : std::string("table A.64: 9925 static and 1152 dynamic "
                              "needles; one late histogram of 64"),
           std::string("table A.189: 5120 static and 0 dynamic needles"),
       })
    EXPECT_NE(r.find(want), std::string::npos) << want << "\n" << r;
  const auto &A = a_domain<P>(t.cs);
  // A commits no unused top batch carries, one carry per norm column, the
  // budget's four digits and the 189 rows' histogram, with one range group
  // in the table of 64.
  EXPECT_EQ(c->coordinates(A.index), qrom ? 27336u : 25672u);
}

// The realized program (plan_program.h) of the system the bench builds:
// every predicate's reads exist, every role is set, the late values' reads
// are closed (no late value, no own pad, pads of earlier messages); the
// MAC's H part is an affine realization part of the cross-field equality
// of degree nch in its key; the tail and its quotient ranges are parts of
// the realization; the norm's ranges are the source program's.
TYPED_TEST(FalconNativeProfile, ProgramExport) {
  using P = TypeParam;
  const Env<P> env;
  FalconNativeSystem<P> t(env, 32);
  const auto c = t.compile();
  const auto p = compiler::build_program(
      *c, compiler::ExportMeta{"falcon-native", P::kId, "test", "test", 32});
  for (const auto &e : compiler::program_errors(p)) ADD_FAILURE() << e;
  // Every index map, decoded from the runs the text writes, equals its
  // explicit entries; the maps with no run longer than one entry.
  for (const auto &e : compiler::index_map_errors(p)) ADD_FAILURE() << e;
  for (const auto &e : compiler::module_errors(p)) ADD_FAILURE() << e;
  for (size_t k : compiler::maps_without_runs(p))
    std::printf("GH_MAP_WITHOUT_RUNS idx%zu length %zu\n", k,
                p.index_maps[k].size());
  auto pred = [&](const std::string &nm) -> const compiler::ProgramData::Predicate * {
    for (const auto &q : p.predicates)
      if (q.name == nm) return &q;
    return nullptr;
  };
  const auto *h = pred("mac.H");
  ASSERT_NE(h, nullptr);
  EXPECT_EQ(h->role, "realization");
  EXPECT_EQ(p.predicates.at(h->owner).name, "mac.equal");
  EXPECT_EQ(h->target, ".affine");
  ASSERT_EQ(h->degree.size(), 1u);
  EXPECT_EQ(p.challenges.at(h->degree[0].first).first, "mac.beta");
  EXPECT_GT(h->degree[0].second, 1u);
  ASSERT_NE(pred("mac"), nullptr);
  EXPECT_EQ(p.predicates.at(pred("mac")->owner).name, "mac.equal");
  ASSERT_NE(pred("mac.final.q"), nullptr);
  EXPECT_EQ(pred("mac.final.q")->role, "realization");
  ASSERT_NE(pred("norm.a"), nullptr);
  EXPECT_EQ(pred("norm.a")->role, "source");
  // Value roles: the MAC's tag and blind belong to the cross-field equal,
  // the tail's group digits to the tail, the crossing's bits and s2 are
  // the source program's.
  auto value = [&](const std::string &nm) -> const compiler::ProgramData::Value * {
    for (const auto &v : p.values)
      if (v.name == nm) return &v;
    return nullptr;
  };
  for (const char *nm : {"mac.value", "mac.blind", "mac.beta"}) {
    ASSERT_NE(value(nm), nullptr) << nm;
    EXPECT_EQ(value(nm)->role, "realization") << nm;
    EXPECT_EQ(p.predicates.at(value(nm)->owner).name, "mac.equal") << nm;
  }
  ASSERT_NE(value("mac.gq"), nullptr);
  EXPECT_EQ(p.predicates.at(value("mac.gq")->owner).name, "mac");
  ASSERT_NE(value("s2"), nullptr);
  EXPECT_EQ(value("s2")->role, "source");
  ASSERT_NE(value("crossing.c_A"), nullptr);
  EXPECT_EQ(value("crossing.c_A")->role, "source");
  EXPECT_NE(p.text.find("role := .realization " +
                        std::to_string(value("mac.value")->owner) + " }"),
            std::string::npos);
  // Challenge roles: the MAC key belongs to the cross-field equal, the
  // range alpha to an in predicate, the selection's delta to the source.
  for (size_t c = 0; c < p.challenges.size(); ++c) {
    const std::string &nm = p.challenges[c].first;
    if (nm == "mac.beta") {
      EXPECT_EQ(p.chal_roles[c], "realization");
      EXPECT_EQ(p.predicates.at(p.chal_owners[c]).name, "mac.equal");
    } else if (nm == "alpha:A") {
      EXPECT_EQ(p.chal_roles[c], "realization");
      EXPECT_EQ(p.predicates.at(p.chal_owners[c]).kind, "mem");
    } else {
      EXPECT_EQ(p.chal_roles[c], "source") << nm;
    }
  }
  // The LogUp circuits are written as table groups, never by name.
  EXPECT_EQ(p.text.find("range.lookup:"), std::string::npos);
  EXPECT_NE(p.text.find(".realization (.logup 0 0)"), std::string::npos);
  size_t late = 0;
  for (const auto &v : p.values) late += v.kind == "late";
  EXPECT_EQ(late, p.messages.size());
  EXPECT_NE(p.text.find("def program : RealizedProgram"), std::string::npos);
  // The MAC tail is grouped, its final quotient bounded by an in
  // predicate; the signature's assert_mod at m = q is the field form.
  const std::string tail = pred("mac")->body;
  EXPECT_NE(tail.find("grouped := (some"), std::string::npos) << tail;
  EXPECT_EQ(tail.find("quotient := none"), std::string::npos) << tail;
  bool field = false;
  for (const auto &q : p.predicates)
    if (q.name == "signature.equation" && q.body.rfind(".mod", 0) == 0)
      field = q.body.find("form := .field") != std::string::npos;
  EXPECT_TRUE(field);
  // The circuit records agree with the compiled domains' plans: input
  // counts, shape, and each value block at its coordinate range.
  ASSERT_EQ(p.circuits.size(), 2u);
  for (const auto &C : p.circuits) {
    const DomainPlan plan = c->compiled_domain(C.domain).plan();
    EXPECT_EQ(C.inputs, plan.ninputs);
    EXPECT_EQ(C.public_inputs, plan.npub);
    EXPECT_EQ(C.layers, plan.layers);
    EXPECT_EQ(C.wires, plan.wires);
    EXPECT_EQ(C.terms, plan.quad_terms);
    for (const auto &b : C.blocks) {
      if (b.kind == "filler" || b.kind == "batchPads") continue;
      bool found = false;
      for (const auto &in : plan.inputs)
        found = found || (in.at == b.at && in.n == b.n);
      EXPECT_TRUE(found) << b.kind << " " << b.name << " at " << b.at;
    }
    EXPECT_FALSE(C.predicates.empty());
  }
}

// Both domains at list radius at the profile's target (the compiler's
// choice).
template <class P>
void check_ligero_target() {
  const Env<P> env;
  FalconNativeSystem<P> t(env, 32);
  expect_ligero_target<P>(*t.compile());
}
TEST(FalconNative, LigeroTarget) {
  check_ligero_target<param_sets::QROMParams>();
  check_ligero_target<param_sets::ROMParams>();
}

}  // namespace
}  // namespace proofs::gordiehowe::examples::falcon::native
