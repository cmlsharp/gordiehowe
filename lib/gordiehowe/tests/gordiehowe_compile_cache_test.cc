// Copyright 2026 Chad Sharp and Paul Grubbs
// SPDX-License-Identifier: Apache-2.0

// GordieHowe compile cache (compiler/compile_cache.h; gordiehowe_test
// binary): a system compiled from the cache has the digest, report,
// circuit ids and plan export of a fresh compile and proves and verifies
// against it, under the test profile and under measured rates with a
// Ligero target (a provisional pass, placement costs, the tableau search);
// a changed domain profile, placement rate, compile profile, relation or
// test hook on a stored decision misses the cache; an entry that fails its
// checks (its hash, its key, a record that does not fit) is discarded and
// replaced; a circuit closure without a key, or a rate request scan, is
// not stored.

#include <algorithm>
#include <cstdint>
#include <filesystem>
#include <memory>
#include <string>
#include <vector>

#include <unistd.h>

#include "gordiehowe/compiler/plan_export.h"
#include "gordiehowe/compiler/plan_program.h"
#include "gordiehowe/compiler/realized_program_io.h"
#include "gordiehowe/tests/gordiehowe_test.h"
#include "gordiehowe/membership.h"
#include "util/diagnostics.h"

namespace proofs::gordiehowe {
namespace {

using Kind = CacheOutcome::Kind;
using Profile = DomainProfile<AF, RSA, SHA384>;

// The test profile at Ligero rate RATE and NREQ opened columns, block_enc
// from the same parameters.
Profile profile_at(size_t rate, size_t nreq) {
  Profile p = env().profile();
  p.rate = rate;
  p.nreq = nreq;
  const RS *r = &env().rs;
  p.block_enc = [r, rate, nreq](const Circuit<AF> &, size_t nw, size_t nq) {
    return r->block_enc<SHA384>("gordiehowe", nw, nq, rate, nreq);
  };
  return p;
}

// The test profile under measured placement rates (so a provisional pass
// runs and placements are costed) and the classical Ligero target (so the
// tableau search runs).
Profile measured_profile() {
  Profile p = env().profile();
  p.rates.gkr_term = 0.25;
  p.rates.commit_full = 1.5;
  p.rates.stage.chains = {{{1, 4}, 1, 1, 1, 1, 1, 1},
                          {{1, 2, 4}, 1, 1, 1, 1, 1, 1}};
  p.target = compiler::LigeroTarget::kClassical;
  p.block_grid = compiler::BlockGrid::kPowerOfTwoBlock;
  return p;
}

// The plan export of C, or the message it fails with.
std::string plan_export(const Sys::Compiled &c) {
  try {
    return compiler::export_lean_plan(c, {"cache", "test", "x", "x"});
  } catch (const std::exception &e) {
    return std::string("failed: ") + e.what();
  }
}

// A fresh cache directory under the test's temporary directory, removed
// with the fixture.
struct CacheDir {
  std::string dir = ::testing::TempDir() + "/gh-compile-cache-" +
                    std::to_string(static_cast<long>(::getpid())) + "-" +
                    ::testing::UnitTest::GetInstance()
                        ->current_test_info()
                        ->name();
  CacheDir() { std::filesystem::remove_all(dir); }
  ~CacheDir() { std::filesystem::remove_all(dir); }
  CompileCache cache() const { return CompileCache{dir}; }
  size_t entries() const {
    if (!std::filesystem::exists(dir)) return 0;
    size_t n = 0;
    for (const auto &e : std::filesystem::directory_iterator(dir))
      n += e.path().extension() == ".ghcc";
    return n;
  }
};

// The cached relation: x, four Subfield values, rows of the public table
// rows and below 1000 (assert_in's keyed lookup closure and the range
// lowering's digits), and y = x * x + C in the circuit, z = x + 5 in
// affine rows.
struct CachedSystem {
  Sys cs{"gh-compile-cache"};
  Ref<AF> rows, x, y, z;
  explicit CachedSystem(const Profile &p, uint64_t c = 3) {
    auto &A = cs.domain(p, "A");
    const auto r = A.pub(Subfield{}, "rows", 8);
    const auto xs = A.priv(Subfield{}, "x", 4);
    const auto ys = A.priv(Field{}, "y", 4);
    const auto zs = A.priv(Field{}, "z", 4);
    assert_in(xs, in_table(cs, "t", r), "m");
    assert_range(xs, 1000, "r");
    assert_zero(xs * xs + c - ys, "square").pin(Placement::kCircuit);
    assert_zero(xs + 5 - zs, "shift");
    rows = r;
    x = xs;
    y = ys;
    z = zs;
  }
  std::unique_ptr<Sys::Compiled> compile(const CompileCache &cache,
                                         const CompileProfile &cp = {}) {
    return gordiehowe::compile(cs, cp, cache);
  }
  std::unique_ptr<Sys::Compiled> compile(const CompileOptions &options) {
    return gordiehowe::compile(cs, CompileProfile{}, options);
  }
  Assignment statement() const {
    const AF &af = env().af;
    Vec r;
    for (uint64_t v : {7, 11, 13, 17, 19, 23, 29, 31})
      r.push_back(af.of_scalar(v));
    Assignment st;
    st.set(rows, r);
    return st;
  }
  Assignment witness(uint64_t c = 3) const {
    const AF &af = env().af;
    Vec xv, yv, zv;
    for (uint64_t v : {11, 29, 7, 11}) {
      xv.push_back(af.of_scalar(v));
      yv.push_back(af.of_scalar(v * v + c));
      zv.push_back(af.of_scalar(v + 5));
    }
    Assignment w;
    w.set(x, xv).set(y, yv).set(z, zv);
    return w;
  }
};

// A proof by A's prover verifies under B (both compiled from one relation).
bool proves_across(const Sys::Compiled &a, const Sys::Compiled &b,
                   const CachedSystem &s) {
  SecureRandomEngine rng;
  const auto proof = a.prepare(s.statement()).prove(s.witness(), rng);
  return b.prepare(s.statement()).verify(proof);
}

// Under PROFILE: a fresh compile, a stored one and a hit, with one digest,
// report, circuit ids and plan export; proofs cross between the hit and
// the fresh system; a witness off the table fails under the hit.
void cached_matches_fresh(const CacheDir &d, const Profile &profile) {
  CachedSystem s0(profile);
  const auto fresh = s0.compile(CompileCache{});
  EXPECT_EQ(fresh->cache().kind, Kind::kOff);

  CachedSystem s1(profile);
  const auto stored = s1.compile(d.cache());
  EXPECT_EQ(stored->cache().kind, Kind::kStored) << stored->cache().reason;
  EXPECT_EQ(d.entries(), 1u);
  EXPECT_EQ(stored->digest(), fresh->digest());

  CachedSystem s2(profile);
  const auto hit = s2.compile(d.cache());
  ASSERT_EQ(hit->cache().kind, Kind::kHit) << hit->cache().reason;
  EXPECT_EQ(hit->cache().file, stored->cache().file);
  EXPECT_EQ(hit->digest(), fresh->digest());
  EXPECT_EQ(hit->report(), fresh->report());
  EXPECT_EQ(plan_export(*hit), plan_export(*fresh));
  // The hit's realized program is the fresh compile's, byte for byte, and
  // so is its Lean module.
  EXPECT_EQ(ir::write_program(hit->program()), ir::write_program(fresh->program()));
  const compiler::ExportMeta meta{"compile-cache", "test", "", "", 0, 0, ""};
  EXPECT_EQ(compiler::export_lean_program(*hit, meta),
            compiler::export_lean_program(*fresh, meta));
  EXPECT_EQ(plan_export(*hit).rfind("failed", 0), std::string::npos)
      << plan_export(*hit);
  for (size_t i = 0; i < hit->num_domains(); ++i)
    EXPECT_EQ(std::string(reinterpret_cast<const char *>(
                              hit->compiled_domain(i).circuit_id()),
                          Sys::Compiled::Hash::kDigestSize),
              std::string(reinterpret_cast<const char *>(
                              fresh->compiled_domain(i).circuit_id()),
                          Sys::Compiled::Hash::kDigestSize));
  EXPECT_TRUE(proves_across(*hit, *fresh, s2));
  EXPECT_TRUE(proves_across(*fresh, *hit, s2));
  // A witness off the table fails under the loaded circuit.
  const AF &af = env().af;
  Assignment bad = s2.witness();
  bad.set(s2.x, Vec{af.of_scalar(12), af.of_scalar(29), af.of_scalar(7),
                    af.of_scalar(11)});
  SecureRandomEngine rng;
  bool rejected = true;
  try {
    rejected = !hit->prepare(s2.statement())
                    .verify(hit->prepare(s2.statement()).prove(bad, rng));
  } catch (const std::exception &) {
  }
  EXPECT_TRUE(rejected);
}

TEST(GordieHoweCompileCache, CachedMatchesFresh) {
  const CacheDir d;
  cached_matches_fresh(d, env().profile());
}

// Measured rates and a Ligero target: the hit reads the provisional
// tableau, the placements and the Ligero choice from the entry.
TEST(GordieHoweCompileCache, CachedMatchesFreshMeasured) {
  const CacheDir d;
  ASSERT_TRUE(measured_profile().rates.measured());
  cached_matches_fresh(d, measured_profile());
}

// A compile option that changes a stored decision (the Ligero choice's
// forced repetitions or masking, a forced packing chain) is in the key: the
// system misses and stores its own entry.
TEST(GordieHoweCompileCache, TestHooksMiss) {
  const CacheDir d;
  CachedSystem s0(measured_profile());
  const auto base = s0.compile(d.cache());
  ASSERT_EQ(base->cache().kind, Kind::kStored) << base->cache().reason;
  auto misses = [&](const char *what, CompileOptions o) {
    SCOPED_TRACE(what);
    o.cache = d.cache();
    CachedSystem s(measured_profile());
    const auto c = s.compile(o);
    EXPECT_EQ(c->cache().kind, Kind::kStored) << c->cache().reason;
    EXPECT_NE(c->cache().file, base->cache().file);
  };
  CompileOptions o;
  o.ldt_reps = 2;
  misses("forced repetitions", o);
  o = {};
  o.domain_ldt_reps["A"] = 2;
  misses("forced repetitions of A", o);
  o = {};
  o.ligero_masking = LigeroMasking::kUntested;
  misses("forced masking", o);
  o = {};
  o.forced_chains = {{{1, 4}, {1, 2, 4}}};
  misses("forced chain", o);
  CachedSystem again(measured_profile());
  EXPECT_EQ(again.compile(d.cache())->cache().kind, Kind::kHit);
}

// The rate run's request scan (diagnostics::Options::rate_requests) needs
// the placement rule to run, so it compiles without the cache.
TEST(GordieHoweCompileCache, RateRequestsNotStored) {
  const CacheDir d;
  const diagnostics::Options before = diagnostics::options();
  ASSERT_TRUE(before.rate_requests.empty());
  const std::string scan = d.dir + "-requests.txt";
  diagnostics::Options scanning = before;
  scanning.rate_requests = scan;
  diagnostics::set(scanning);
  CachedSystem s(measured_profile());
  const auto c = s.compile(d.cache());
  diagnostics::set(before);
  std::filesystem::remove(scan);
  EXPECT_EQ(c->cache().kind, Kind::kNotStored);
  EXPECT_NE(c->cache().reason.find("rate request scan"), std::string::npos)
      << c->cache().reason;
  EXPECT_EQ(d.entries(), 0u);
}

TEST(GordieHoweCompileCache, ProfileChangeMisses) {
  const CacheDir d;
  CachedSystem s0(env().profile());
  const auto base = s0.compile(d.cache());
  ASSERT_EQ(base->cache().kind, Kind::kStored) << base->cache().reason;

  // Each change misses, compiles afresh and stores its own entry; the
  // system compiled from the cache next time is the changed one.
  auto misses = [&](const Profile &p, const CompileProfile &cp,
                    const char *what) {
    SCOPED_TRACE(what);
    CachedSystem s(p);
    const auto c = s.compile(d.cache(), cp);
    EXPECT_EQ(c->cache().kind, Kind::kStored) << c->cache().reason;
    EXPECT_NE(c->cache().file, base->cache().file);
    CachedSystem again(p);
    const auto h = again.compile(d.cache(), cp);
    EXPECT_EQ(h->cache().kind, Kind::kHit) << h->cache().reason;
    EXPECT_EQ(h->digest(), c->digest());
  };
  // The Ligero rate, and the opened columns.
  misses(profile_at(8, kNreq), {}, "rate");
  misses(profile_at(kRate, 80), {}, "nreq");
  // A placement rate: it decides placements but enters no description.
  Profile rates = env().profile();
  rates.rates.gkr_term = 0.25;
  rates.rates.commit_full = 1.5;
  // Measured rates weigh A's packing chains, so they state theirs.
  rates.rates.stage.chains = {{{1, 4}, 1, 1, 1, 1, 1, 1},
                              {{1, 2, 4}, 1, 1, 1, 1, 1, 1}};
  misses(rates, {}, "placement rates");
  // A packing chain's rate: with measured rates it decides the packing
  // tree's chains.
  Profile stage = env().profile();
  stage.rates.stage.chains.push_back({{1, 2, 4}, 1, 1, 1, 1, 1, 1});
  misses(stage, {}, "stage rates");
  // The packing tree's largest edge.
  Profile dmax = env().profile();
  dmax.d_max = 8;
  misses(dmax, {}, "d_max");
  // The Ligero target the compiler chooses the parameters from
  // (DomainProfile::target, ligero_choice.h), and its block grid's cap.
  Profile target = env().profile();
  target.target = compiler::LigeroTarget::kClassical;
  target.block_grid = compiler::BlockGrid::kPowerOfTwoBlock;
  misses(target, {}, "target");
  Profile capped = target;
  capped.max_block_enc = 4095;
  misses(capped, {}, "max_block_enc");
  // The compile profile.
  CompileProfile cp;
  cp.name = "gh-compile-cache-other";
  misses(env().profile(), cp, "compile profile");
  EXPECT_EQ(d.entries(), 9u);
}

TEST(GordieHoweCompileCache, RelationChangeMisses) {
  const CacheDir d;
  CachedSystem s0(env().profile(), 3);
  const auto base = s0.compile(d.cache());
  ASSERT_EQ(base->cache().kind, Kind::kStored);
  // Another constant in the circuit's predicate: its expression differs.
  CachedSystem s1(env().profile(), 4);
  const auto other = s1.compile(d.cache());
  EXPECT_EQ(other->cache().kind, Kind::kStored);
  EXPECT_NE(other->digest(), base->digest());
  SecureRandomEngine rng;
  EXPECT_TRUE(other->prepare(s1.statement())
                  .verify(other->prepare(s1.statement())
                              .prove(s1.witness(4), rng)));
}

TEST(GordieHoweCompileCache, BadEntryDiscarded) {
  const CacheDir d;
  CachedSystem s0(env().profile());
  const auto base = s0.compile(d.cache());
  ASSERT_EQ(base->cache().kind, Kind::kStored);
  // A flipped byte: the file's hash fails, the system compiles afresh and
  // its entry replaces the bad one.
  std::vector<uint8_t> b = *compiler::read_file(base->cache().file);
  b[b.size() / 2] ^= 1;
  ASSERT_EQ(compiler::write_file(d.dir, base->cache().file, b), "");
  CachedSystem s1(env().profile());
  const auto c = s1.compile(d.cache());
  EXPECT_EQ(c->cache().kind, Kind::kDiscarded);
  EXPECT_NE(c->cache().reason.find("hash"), std::string::npos)
      << c->cache().reason;
  EXPECT_EQ(c->digest(), base->digest());
  CachedSystem s2(env().profile());
  EXPECT_EQ(s2.compile(d.cache())->cache().kind, Kind::kHit);
}

// An entry whose hash holds but whose realized program does not build its
// domains (a truncated realization record, a delta index past its table, a
// declaration with no element, an element with no declaration) is
// discarded: the system compiles afresh, with the fresh digest, and
// replaces it.
TEST(GordieHoweCompileCache, MalformedRecordDiscarded) {
  for (const char *what : {"decisions", "circuit", "no element", "no entry"}) {
    SCOPED_TRACE(what);
    const CacheDir d;
    CachedSystem s0(measured_profile());
    const auto base = s0.compile(d.cache());
    ASSERT_EQ(base->cache().kind, Kind::kStored) << base->cache().reason;
    const std::vector<uint8_t> bytes = *compiler::read_file(base->cache().file);
    compiler::CacheKey key;
    std::copy(bytes.begin() + 12, bytes.begin() + 12 + key.size(), key.begin());
    std::string why;
    auto e = compiler::parse_entry(bytes, key, why);
    ASSERT_TRUE(e) << why;
    auto prog = ir::read_program(e->program);
    ASSERT_TRUE(prog);
    ir::DomainRealization &rec = prog->realizations.at(0);
    const std::string w = what;
    if (w == "decisions") {
      rec.decisions.resize(rec.decisions.size() / 2);
    } else if (w == "circuit") {
      ASSERT_GE(rec.circuit.size(), 4u);
      // The last term's delta index, past any delta table.
      for (size_t i = rec.circuit.size() - 4; i < rec.circuit.size(); ++i)
        rec.circuit[i] = 0xff;
    } else if (w == "no element") {
      // A declaration of domain 0 that names no element of the program.
      bool moved = false;
      for (auto &q : prog->predicates)
        if (!moved && q.origin.kind == ir::Origin::kDecl && q.origin.domain == 0) {
          q.origin.index = 1u << 30;
          moved = true;
        }
      ASSERT_TRUE(moved);
    } else {
      // An entry of the domain's circuit that the program does not list.
      ASSERT_FALSE(prog->circuits.empty());
      ASSERT_FALSE(prog->circuits[0].entries.empty());
      prog->circuits[0].entries.pop_back();
    }
    e->program = ir::write_program(*prog);
    ASSERT_EQ(compiler::write_file(d.dir, base->cache().file,
                                   compiler::entry_bytes(key, *e)),
              "");
    CachedSystem s1(measured_profile());
    const auto c = s1.compile(d.cache());
    EXPECT_EQ(c->cache().kind, Kind::kDiscarded);
    EXPECT_NE(c->cache().reason.find("does not build"), std::string::npos)
        << c->cache().reason;
    EXPECT_EQ(c->digest(), base->digest());
    CachedSystem s2(measured_profile());
    EXPECT_EQ(s2.compile(d.cache())->cache().kind, Kind::kHit);
  }
}

// The index maps' family form reads back every map (empty, constant,
// descending, periodic, nested periodic, irregular); a family whose head
// names itself, a family nested past the depth bound, or a map past the
// size bound is malformed.
TEST(GordieHoweCompileCache, IndexMapFamilies) {
  std::vector<std::vector<size_t>> maps(7);
  maps[1] = {5, 5, 5, 5};
  maps[2] = {9, 7, 5, 3, 1};
  for (size_t b = 0; b < 40; ++b)
    for (size_t i = 0; i < 32; ++i) maps[3].push_back(b * 256 + i);
  for (size_t b = 0; b < 16; ++b)
    for (size_t c = 0; c < 4; ++c)
      for (size_t i = 0; i < 8; ++i) maps[4].push_back(b * 32 + (3 - c) * 8 + i);
  for (size_t b = 0; b < 20; ++b)
    for (size_t i = 0; i < 32; ++i) maps[5].push_back(b * 32 + (i + 1) % 32);
  maps[6] = {3, 1, 4, 1, 5, 9, 2, 6, 5, 3, 5, 8, 9, 7, 9};
  ir::Program p;
  p.index_maps = maps;
  const auto q = ir::read_program(ir::write_program(p));
  ASSERT_TRUE(q);
  EXPECT_EQ(q->index_maps, maps);

  // Whether the varints XS read as index maps.
  auto reads = [](const std::vector<uint64_t> &xs) {
    ir::io_internal::W w;
    for (uint64_t x : xs) w.u(x);
    ir::io_internal::R r{w.b};
    std::vector<std::vector<size_t>> out;
    ir::io_internal::get_index_maps(r, out);
    return r.ok;
  };
  // Shapes: a count, then a run as (0, zigzag step, count) or a family as
  // (1, head count, (zigzag base, shape) per head item, times, zigzag
  // delta). Maps: a count, then per map an item count and (zigzag base,
  // shape) per item.
  EXPECT_TRUE(reads({1, 0, 2, 3, 1, 1, 0, 0}));
  // A family whose head names the family itself.
  EXPECT_FALSE(reads({1, 1, 1, 0, 0, 2, 0, 1, 1, 0, 0}));
  // 70 families, each one copy of the previous: nested past the bound.
  std::vector<uint64_t> deep = {71, 0, 2, 1};
  for (uint64_t k = 1; k <= 70; ++k)
    deep.insert(deep.end(), {1, 1, 0, k - 1, 1, 0});
  deep.insert(deep.end(), {1, 1, 0, 70});
  EXPECT_FALSE(reads(deep));
  // A run of 2^40 entries.
  EXPECT_FALSE(reads({1, 0, 2, uint64_t(1) << 40, 1, 1, 0, 0}));
}

// An entry of another key under this key's file name (a stale copy) is
// discarded and replaced.
TEST(GordieHoweCompileCache, OtherKeyDiscarded) {
  const CacheDir d;
  CachedSystem s0(env().profile());
  const auto a = s0.compile(d.cache());
  CachedSystem s1(profile_at(8, kNreq));
  const auto b = s1.compile(d.cache());
  ASSERT_EQ(a->cache().kind, Kind::kStored);
  ASSERT_EQ(b->cache().kind, Kind::kStored);
  ASSERT_EQ(compiler::write_file(d.dir, a->cache().file,
                                 *compiler::read_file(b->cache().file)),
            "");
  CachedSystem s2(env().profile());
  const auto c = s2.compile(d.cache());
  EXPECT_EQ(c->cache().kind, Kind::kDiscarded);
  EXPECT_NE(c->cache().reason.find("another key"), std::string::npos)
      << c->cache().reason;
  EXPECT_EQ(c->digest(), a->digest());
}

TEST(GordieHoweCompileCache, ClosureWithoutKeyNotStored) {
  const CacheDir d;
  TestSystem t;
  const auto c = gordiehowe::compile(t.cs, CompileProfile{}, d.cache());
  EXPECT_EQ(c->cache().kind, Kind::kNotStored);
  EXPECT_NE(c->cache().reason.find("closure without a key"), std::string::npos)
      << c->cache().reason;
  EXPECT_EQ(d.entries(), 0u);
}

// CompileOptions::cache names the directory of compile(System&, profile,
// options); by default the cache is off.
TEST(GordieHoweCompileCache, Environment) {
  const CacheDir d;
  CachedSystem s0(env().profile());
  EXPECT_EQ(compile(s0.cs, CompileProfile{})->cache().kind, Kind::kOff);
  CompileOptions o;
  o.cache.dir = d.dir;
  CachedSystem s1(env().profile());
  const auto c = compile(s1.cs, CompileProfile{}, o);
  CachedSystem s2(env().profile());
  const auto h = compile(s2.cs, CompileProfile{}, o);
  EXPECT_EQ(c->cache().kind, Kind::kStored);
  EXPECT_EQ(h->cache().kind, Kind::kHit);
  EXPECT_EQ(d.entries(), 1u);
}

}  // namespace
}  // namespace proofs::gordiehowe
