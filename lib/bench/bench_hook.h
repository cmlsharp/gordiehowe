// Copyright 2026 Chad Sharp and Paul Grubbs
// SPDX-License-Identifier: Apache-2.0

// The bench hook: a GordieHowe example system as a report_bench worker
// (serve(), the protocol of bench/harness.h) or timed alone (run()). Each
// application's bench executable (lib/gordiehowe/examples/*_bench.cc)
// calls one of them from its serve or bench command, with the hook's
// options (add_hook_flags: --params, --commit, --report).
//
// Once per statement, outside every timer, the worker prints
//   GH_SETUP config=C profile=P R=R build=MS compile=MS prepare=MS setup=MS
//            cache=KIND cache_bytes=N
// (build: the relation's graph; compile: its lowering and compile(), which
// the relation runs once as it is built; prepare: the statement's
// prepare, of which setup is the cached public computation, the ring's
// decode; cache: the compile cache's outcome, off unless GH_COMPILE_CACHE
// names its directory, and cache_bytes its entry's size), then the system's protocol hash (its field profile's)
//   PQ_HASH {"config":C,"profile":P,"ring":R,"hash":{"name":"SHA-256",
//            "digest_bytes":32,"proof_salt_bytes":32,"leaf_salt_bytes":64,
//            "fs_stream_extra_bytes":206848}}
// and, with --params, one line per domain
//   PQ_PARAMS {json}
// with the domain's field, Ligero tableau and circuit sizes (DomainPlan,
// domain.h) and the hash record. run_bench.sh checks every PQ_HASH line
// against its profile before timing (benchmarks/hash_check.py).
// After GH_SETUP, one line names each domain's field (DomainProfile's
// field_name), in domain order:
//   GH_DOMAINS <domain>=<field> ...        e.g. GH_DOMAINS A=Fp128 H=GF(2^128)
// Under the per-chunk MAC ablation (CompileProfile::unsound_per_chunk_mac),
// one line per per-chunk MAC follows (print_per_chunk_macs):
//   GH_PER_CHUNK_MAC config=C profile=P mac=NAME H=D A=D w=W nch=N
//                    product=gkr
// Each "run" is one proof:
//   GH_RUN witness=MS assemble=MS late=MS bytes=N setup_p=MS setup_v=MS
//          verify_parse=MS <domain>_bytes=N ... [split]
// precedes the protocol's PQ_RESULT. witness is the witness generation from
// the instance: assemble, the private inputs' assignment from the
// example's instance (its witness() call), plus the phase-0 generators
// (ProveTimes::witness). late is the later phases' generators (LogUp values
// and MAC tags, ProveTimes::late), inside prove. The prover time P is
// witness + PQ_RESULT's commit + prove. Per-statement work counts in the
// prover's and the verifier's times: each proof forgets the statement's
// memoized public computations (forget_setup) and prepares the statement
// twice, once for the prover and once for the verifier (fresh_prepare).
// setup_p and setup_v are those prepares (ML-DSA's ExpandA, tr and
// pkDecode, a ring's decode). PQ_RESULT's commit is setup_p plus
// ProveTimes::commit (with phase 0's public computations, which the
// verifier computes inside verify), its prove is ProveTimes::prove (with
// the later phases' generators), and its verify is setup_v plus the
// verify() call. verify_parse is the verify() call's proof parsing (VerifyTimes::
// parse: the seed, the phase messages and every domain's section decoded),
// inside verify.
//
// The per-domain split (domain_split): a single-threaded proof's GH_RUN
// ends with, per domain in domain order and then once,
//   <domain>_prover=MS <domain>_verify=MS ... shared_prover=MS shared_verify=MS
// <domain>_prover is the domain's commitment and low-degree test plus its
// reductions and opening after the transcript fork
// (ProveTimes::domain_commit + domain_prove); <domain>_verify is its
// commitment receipt and low-degree test plus its work after the fork
// (VerifyTimes::domain). shared_prover and shared_verify are the rest of
// PQ_RESULT's commit + prove and verify, less verify_parse: the statement,
// pads, phase challenges and messages and the fork, the verifier's domain
// verifiers' construction, and the prepares (setup_p, setup_v). So the
// domains' terms, verify_parse and the shared term are the totals. A
// multi-threaded proof (GH_THREADS=multi) prints no split: the domains run
// concurrently on the pool, their wall times add up to more than the
// proof's, and no remainder is the shared work. RSA's GH_RSA_RUN, the
// post-quantum mDL's PQMDOC_RUN and the composite's GH_COMPOSITE_RUN time
// the prepares the same way (fresh_prepare) and carry the same split and
// GH_DOMAINS lines.

#ifndef PRIVACY_PROOFS_ZK_LIB_BENCH_BENCH_HOOK_H_
#define PRIVACY_PROOFS_ZK_LIB_BENCH_BENCH_HOOK_H_

#include <algorithm>
#include <cmath>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <memory>
#include <regex>
#include <sstream>
#include <stdexcept>
#include <string>
#include <vector>

#include "bench/affinity.h"
#include "bench/cli.h"
#include "bench/harness.h"
#include "bench/hook_flags.h"
#include "bench/timing.h"
#include "params/param_sets.h"
#include "gordiehowe/system.h"
#include "merkle/merkle_commitment.h"
#include "random/transcript.h"
#include "random/secure_random_engine.h"
#include "util/optimization_options.h"

namespace proofs::gordiehowe::examples::bench_hook {

using bench::Clock;
using bench::ms_since;

// The implementation policy of every GordieHowe system: the optimized
// preset (the systems construct their Reed-Solomon factories and domains
// with OptimizationOptions::optimized()), as the PQ_OPTIMIZATIONS line and
// the PQ_PARAMS records state it.
inline constexpr OptimizationOptions kOptimizations =
    OptimizationOptions::optimized();

// The time (ms) the relation of the example system T took to lower and
// compile (RelationOf::compile_ms), inside its construction.
template <class T>
double relation_compile_ms(const T &t) {
  return t.rel.template typed<typename T::Sys>().compile_ms();
}

// The per-statement figures the worker reports once.
struct Setup {
  const char *config = "";
  const char *profile = "";
  size_t ring = 0;
  double build = 0, compile = 0;
};

// A JSON object of numbers, strings, booleans and nested objects, keys in
// insertion order. Every string here is an identifier, a commit, a profile
// name or a fixed reason, so nothing needs escaping.
class Obj {
 public:
  Obj &num(const char *k, uint64_t v) { return raw(k, std::to_string(v)); }
  // A number of bits in steps of 1/2 (108, 113.5).
  Obj &bits(const char *k, double v) {
    char buf[32];
    std::snprintf(buf, sizeof(buf), "%g", v);
    return raw(k, buf);
  }
  Obj &str(const char *k, const std::string &v) {
    return raw(k, "\"" + v + "\"");
  }
  Obj &boolean(const char *k, bool v) { return raw(k, v ? "true" : "false"); }
  Obj &null(const char *k) { return raw(k, "null"); }
  Obj &obj(const char *k, const Obj &v) { return raw(k, v.dump()); }
  std::string dump() const { return "{" + body_ + "}"; }

 private:
  Obj &raw(const char *k, const std::string &v) {
    body_ += (body_.empty() ? "\"" : ",\"") + std::string(k) + "\":" + v;
    return *this;
  }
  std::string body_;
};

// The protocol hash HASH as a run records it: its name, digest bytes, the
// proof's salt (its seed, random/transcript.h), each Merkle leaf's salt
// (merkle/merkle_commitment.h) and the stream bytes e a challenge point may
// read beyond the first k (kFSStreamExtraBytes, random/transcript.h).
template <class Hash>
Obj hash_record() {
  Obj h;
  h.str("name", Hash::kName)
      .num("digest_bytes", Hash::kDigestSize)
      .num("proof_salt_bytes", BasicProofSeed<Hash>::kLength)
      .num("leaf_salt_bytes", BasicMerkleNonce<Hash>::kLength)
      .num("fs_stream_extra_bytes", kFSStreamExtraBytes);
  return h;
}

// The PQ_HASH line of the system CONFIG (ring size RING, 0 outside a ring)
// in the field profile PROFILE, whose protocol hash is HASH.
template <class Hash>
void print_hash(const std::string &config, const char *profile,
                size_t ring = 0) {
  Obj e;
  e.str("config", config)
      .str("profile", profile)
      .num("ring", ring)
      .obj("hash", hash_record<Hash>());
  std::printf("PQ_HASH %s\n", e.dump().c_str());
  std::fflush(stdout);
}

// One domain's PQ_PARAMS entry, with the fields a DomainPlan carries.
// The schema's transcript, mac, application and skip objects are null, with
// their reasons. The options object records kOptimizations and the
// extension packing the records have always named, "both".
inline std::string params_entry(const DomainPlan &p, const std::string &half,
                                const Setup &su, const Obj &hash,
                                const Options &opts) {
  const OptimizationOptions o = kOptimizations;
  const bool qrom = std::string(su.profile) == param_sets::QROMParams::kId;
  Obj options, field, ligero, circuit, half_params, reasons, e;
  options.str("preset", o.preset_name())
      .boolean("unit_coefficients", o.unit_coefficients)
      .boolean("subfield_encoding", o.subfield_encoding)
      .boolean("native_ntt", o.native_ntt);
  if (p.characteristic != 0) {
    field.str("name", "GF(" + std::to_string(p.characteristic) + "^" +
                          std::to_string(p.protocol_degree) + ")")
        .num("characteristic", p.characteristic)
        .num("degree", p.protocol_degree);
  } else {
    field.null("name").null("characteristic").null("degree");
    reasons.str("half_params.field", "the field has no protocol field id");
  }
  field.num("bytes", p.field_bytes)
      .num("packing_degree", p.field_degree)
      .num("s0", p.s0);
  ligero.num("rate", p.rate)
      .num("block", p.k)
      .num("k", p.k)
      .num("block_enc", p.block_enc)
      .num("N", p.N)
      .num("nreq", p.t)
      .num("t", p.t)
      .num("r", p.r)
      .num("nrow", p.nrow)
      .num("nw", p.nw)
      .num("nq", p.nq)
      .boolean("list_radius", p.list_radius)
      .str("masking", p.split ? "split" : "standard")
      .num("ldt_reps", p.ldt_reps)
      .bits("target", p.target)
      .boolean("target_fallback", p.target_fallback)
      .num("target_num", p.target_num)
      .num("A", p.agreement)
      .num("exceptions", p.exceptions);
  circuit.num("ninputs", p.ninputs)
      .num("npub_in", p.npub)
      .num("committed", p.ninputs - p.npub)
      .num("layers", p.layers)
      .num("wires", p.wires)
      .num("nterms", p.quad_terms)
      .num("nquadratic", p.quad_triples)
      .num("batches", p.batches.size());
  half_params.obj("field", field).obj("ligero", ligero).obj("circuit", circuit);
  if (opts.commit.empty()) reasons.str("commit", "PQ_COMMIT unset");
  for (const char *k : {"transcript", "mac", "application", "skip"})
    reasons.str(k, "not dumped by the GordieHowe bench hook");
  if (!opts.commit.empty())
    e.str("commit", opts.commit);
  else
    e.null("commit");
  e.str("construction", "gordiehowe")
      .str("profile", su.profile)
      .str("profile_name",
           qrom ? param_sets::QROMParams::kName : param_sets::ROMParams::kName)
      .str("config", su.config)
      .str("half", half)
      .num("ring", su.ring)
      .obj("hash", hash)
      .obj("options", options)
      .obj("half_params", half_params)
      .null("transcript")
      .null("mac")
      .null("application")
      .null("skip")
      .obj("null_reasons", reasons);
  return e.dump();
}

// " <domain>=<field>" per domain of the compiled system CS, in domain
// order: the GH_DOMAINS fields (see the header).
template <class C>
std::string domain_fields(const C &cs) {
  std::string out;
  for (size_t d = 0; d < cs.num_domains(); ++d)
    out += " " + cs.domain(d).name + "=" + cs.domain(d).field_name();
  return out;
}

// The per-domain split of one single-threaded proof of CS (see the header):
// " <domain>_prover=MS <domain>_verify=MS" per domain, then
// " shared_prover=MS shared_verify=MS", the remainders of the bench's
// reported prover time PROVER (commit + prove) and verifier time VERIFY,
// the latter less the proof parsing (VerifyTimes::parse, its own
// verify_parse term).
template <class C>
std::string domain_split(const C &cs, const ProveTimes &pt,
                         const VerifyTimes &vt, double prover,
                         double verify) {
  std::string out;
  char buf[160];
  double dp = 0, dv = 0;
  for (size_t d = 0; d < cs.num_domains(); ++d) {
    const double p = pt.domain_commit.at(d) + pt.domain_prove.at(d);
    const double v = vt.domain.at(d);
    const std::string &nm = cs.domain(d).name;
    std::snprintf(buf, sizeof(buf), " %s_prover=%.3f %s_verify=%.3f",
                  nm.c_str(), p, nm.c_str(), v);
    out += buf;
    dp += p;
    dv += v;
  }
  std::snprintf(buf, sizeof(buf), " shared_prover=%.3f shared_verify=%.3f",
                prover - dp, verify - dv - vt.parse);
  return out + buf;
}

// The GH_PER_CHUNK_MAC line (see the header) of each per-chunk MAC in the
// compile report REPORT of the system CONFIG in profile PROFILE: its
// binary and odd domains, the chunk width w and the chunk count nch, from
// the MAC's report line (compiler/mac.h's per_chunk_mac). The odd domain's
// emulated GF(2^w) product, like the binary domain's field product, is a
// constraint of the domain's GKR circuit (product=gkr): per_chunk_mac
// declares both through gkr(). Prints nothing for a system without one.
inline void print_per_chunk_macs(const std::string &report,
                                 const std::string &config,
                                 const std::string &profile) {
  static const std::regex mac(
      R"(MAC (\S+) \(per-chunk ablation[^)]*\): .*; H = ([^,]+), A = ([^,]+), )"
      R"(w = (\d+), nch = (\d+);)");
  std::istringstream in(report);
  std::string line;
  std::smatch m;
  while (std::getline(in, line)) {
    if (line.find("per-chunk ablation") == std::string::npos) continue;
    if (!std::regex_search(line, m, mac)) continue;
    std::printf("GH_PER_CHUNK_MAC config=%s profile=%s mac=%s H=%s A=%s "
                "w=%s nch=%s product=gkr\n",
                config.c_str(), profile.c_str(), m[1].str().c_str(),
                m[2].str().c_str(), m[3].str().c_str(), m[4].str().c_str(),
                m[5].str().c_str());
  }
  std::fflush(stdout);
}

// One line per batch of every domain of CS, with the batch's shape and the
// soundness error of its masked zerocheck (the plan's per-batch masked-IP
// error):
//   GH_BATCH config=C domain=D batch=NAME degree=D arity=K instances=N
//            width=W rounds=M sum_num=X sum_bits=B worst_num=Y worst_bits=B'
//            field_bits=F
// sum_num/|K| = (M (D + 2) + D (W - 1) + 1)/|K| is the batch's summed
// error: M/|K| for the eq point, D (W - 1)/|K| for the skip polynomial,
// (D + 1)/|K| per round and 1/|K| for the terminal combination u.
// worst_num/|K| is its largest single term, max(M, D (W - 1), D + 1); the
// bits are -log2 of each. Width 1 (no skip) has no skip term.
template <class S>
void print_batches(const BasicCompiledSystem<S> &cs, const Setup &su) {
  for (size_t d = 0; d < cs.num_domains(); ++d) {
    const DomainPlan p = cs.compiled_domain(d).plan();
    const double fbits =
        p.characteristic > 1
            ? double(p.protocol_degree) * std::log2(double(p.characteristic))
            : double(8 * p.field_bytes);
    for (const auto &b : p.batches) {
      const uint64_t D = b.degree, M = b.rounds, W = b.width;
      const uint64_t sum = M * (D + 2) + D * (W - 1) + 1;
      const uint64_t worst = std::max({M, D * (W - 1), D + 1});
      std::printf("GH_BATCH config=%s domain=%s batch=%s degree=%llu "
                  "arity=%zu instances=%zu width=%llu rounds=%llu "
                  "sum_num=%llu sum_bits=%.3f worst_num=%llu "
                  "worst_bits=%.3f field_bits=%.0f\n",
                  su.config, cs.domain(d).name.c_str(), b.name.c_str(),
                  (unsigned long long)D, b.arity, b.instances,
                  (unsigned long long)W, (unsigned long long)M,
                  (unsigned long long)sum, fbits - std::log2(double(sum)),
                  (unsigned long long)worst, fbits - std::log2(double(worst)),
                  fbits);
    }
  }
}

template <class S>
void print_params(const BasicCompiledSystem<S> &cs, const Setup &su,
                  const Options &opts, double prepare, double setup) {
  // The compile cache's outcome (off, hit, stored, ...) and its entry's
  // bytes (0 without one): under GH_COMPILE_CACHE, a hit's build and
  // compile are the cache-hit setup.
  static const char *kinds[] = {"off", "hit", "stored", "not-stored",
                                "discarded"};
  size_t cache_bytes = 0;
  if (cs.cache().kind != CacheOutcome::Kind::kOff)
    if (const auto b = compiler::read_file(cs.cache().file)) cache_bytes = b->size();
  std::printf("GH_SETUP config=%s profile=%s R=%zu build=%.3f compile=%.3f "
              "prepare=%.3f setup=%.3f cache=%s cache_bytes=%zu\n",
              su.config, su.profile, su.ring, su.build, su.compile, prepare,
              setup, kinds[int(cs.cache().kind)], cache_bytes);
  if (opts.report) std::printf("%s\n", cs.report().c_str());
  std::printf("GH_DOMAINS%s\n", domain_fields(cs).c_str());
  print_per_chunk_macs(cs.report(), su.config, su.profile);
  print_hash<typename S::Hash>(su.config, su.profile, su.ring);
  if (opts.params) {
    for (size_t d = 0; d < cs.num_domains(); ++d) {
      const std::string entry =
          params_entry(cs.compiled_domain(d).plan(), cs.domain(d).name, su,
                       hash_record<typename S::Hash>(), opts);
      std::printf("PQ_PARAMS %s\n", entry.c_str());
    }
    print_batches(cs, su);
  }
  std::fflush(stdout);
}

// ------------------------------------------------- threading modes --
//
// The standalone benches (RSA, the post-quantum mDL, the composite) measure
// GordieHowe in both modes of the threading knob (threads.h):
// single-threaded, pinned to --cpu, and, when --par-cpus lists a core set
// (run_bench.sh --par-cores), multi-threaded, pinned to that set. Each
// round proves once per mode, both from the bench's SecureRandomEngine
// (OpenSSL's CSPRNG).

struct Mode {
  bool multi = false;
  std::vector<int> cpus;  // empty: no pinning
  const char *name() const { return multi ? "multi" : "single"; }
};

inline void add_mode_flags(bench::Flags &f) {
  f.flag("cpu", "", "pin the single-threaded proofs to this core")
      .flag("par-cpus", "", "also prove multi-threaded, pinned to these "
                            "cores (a-b or a,b,...)");
}
// The modes of this bench: single, then multi when --par-cpus is given.
inline std::vector<Mode> modes(const bench::Flags &f) {
  std::vector<Mode> out(1);
  out[0].cpus = bench::parse_cpus(f.str("cpu"));
  if (f.given("par-cpus"))
    out.push_back(Mode{true, bench::parse_cpus(f.str("par-cpus"))});
  return out;
}

// Pins the calling thread to MODE's cores (the pool's workers, created per
// proof, inherit them).
inline void enter(const Mode &mode) { bench::pin_self(mode.cpus); }

// STATEMENT prepared afresh on the compiled system CS, as every bench
// prepares it once for the prover and once for the verifier of each proof:
// CS forgets its memoized public computations (forget_setup), so the
// prepare runs the statement's setup again. MS is the prepare's time; the
// forgetting is outside it. Every Prepared of CS made earlier is invalid
// afterwards.
template <class C, class A>
auto fresh_prepare(const C &cs, const A &statement, double &ms) {
  cs.forget_setup();
  const auto t0 = Clock::now();
  auto prep = cs.prepare(statement);
  ms = ms_since(t0);
  return prep;
}

// One proof of WITNESS() on CS with its own prepares, its GH_RUN line
// printed (see the header).
template <class S, class Witness>
bench::RunResult prove_once(const BasicCompiledSystem<S> &cs,
                            const BasicAssignment<S> &statement,
                            Witness &witness, SecureRandomEngine &rng) {
  const auto ta = Clock::now();
  const auto w = witness();
  const double assemble = ms_since(ta);
  ProveTimes pt;
  VerifyTimes vt;
  std::vector<size_t> sections;
  BasicProveOptions<S> opt;
  opt.times = &pt;
  opt.domain_bytes = &sections;
  bench::RunResult r;
  double setup_p = 0, setup_v = 0;
  std::vector<uint8_t> proof;
  {
    const auto prep = fresh_prepare(cs, statement, setup_p);
    proof = prep.prove(w, rng, opt);
  }
  {
    const auto prep = fresh_prepare(cs, statement, setup_v);
    const auto t0 = Clock::now();
    r.ok = prep.verify(proof, &vt, opt.multithreaded);
    r.verify_ms = setup_v + ms_since(t0);
  }
  r.commit_ms = setup_p + pt.commit;
  r.prove_ms = pt.prove;
  r.proof_bytes = proof.size();
  std::printf("GH_RUN witness=%.3f assemble=%.3f late=%.3f bytes=%zu "
              "setup_p=%.3f setup_v=%.3f verify_parse=%.3f",
              assemble + pt.witness, assemble, pt.late, proof.size(),
              setup_p, setup_v, vt.parse);
  for (size_t d = 0; d < sections.size(); ++d)
    std::printf(" %s_bytes=%zu", cs.domain(d).name.c_str(), sections[d]);
  if (!opt.multithreaded)
    std::printf("%s", domain_split(cs, pt, vt, r.commit_ms + r.prove_ms,
                                   r.verify_ms)
                          .c_str());
  std::printf("\n");
  return r;
}

// Prepares STATEMENT on CS once for GH_SETUP and serves one proof of
// WITNESS() per "run" (the worker protocol, bench/harness.h).
template <class S, class Witness>
void serve(const BasicCompiledSystem<S> &cs,
           const BasicAssignment<S> &statement, Witness witness,
           const Setup &su, const Options &opts) {
  {
    const auto t0 = Clock::now();
    const auto prep = cs.prepare(statement);
    const double prepare = ms_since(t0);
    print_params(cs, su, opts, prepare, prep.setup_ms());
  }
  SecureRandomEngine rng;
  bench::serve(kOptimizations,
               [&]() { return prove_once(cs, statement, witness, rng); });
}

// The same records without report_bench: GH_SETUP, then REPS proofs, each
// printing its GH_RUN line and a PQ_RESULT line. Returns whether every
// proof verified.
template <class S, class Witness>
bool run(const BasicCompiledSystem<S> &cs,
         const BasicAssignment<S> &statement, Witness witness,
         const Setup &su, const Options &opts, size_t reps) {
  {
    const auto t0 = Clock::now();
    const auto prep = cs.prepare(statement);
    const double prepare = ms_since(t0);
    print_params(cs, su, opts, prepare, prep.setup_ms());
  }
  SecureRandomEngine rng;
  bool ok = true;
  for (size_t i = 0; i < reps; ++i) {
    const bench::RunResult r = prove_once(cs, statement, witness, rng);
    std::printf("PQ_RESULT %.17g %.17g %.17g %zu %d\n", r.commit_ms,
                r.prove_ms, r.verify_ms, r.proof_bytes, r.ok);
    std::fflush(stdout);
    ok = ok && r.ok;
  }
  return ok;
}

// The serve and bench commands of an application. WITH_SYSTEM(p, fn)
// builds the application's system in the profile p (a profile struct, as
// param_sets::with_profile passes it) and calls fn(compiled, statement,
// witness, setup).
template <class WithSystem>
int serve_command(const bench::Flags &f, WithSystem with_system) {
  const std::string profile = bench::apply_common_flags(f);
  const Options opts = hook_options(f);
  param_sets::with_profile(profile, [&](auto p) {
    with_system(p, [&](const auto &c, const auto &statement, auto witness,
                       const Setup &su) {
      serve(c, statement, witness, su, opts);
    });
  });
  return 0;
}
template <class WithSystem>
int bench_command(const bench::Flags &f, WithSystem with_system) {
  const std::string profile = bench::apply_common_flags(f);
  const Options opts = hook_options(f);
  bool ok = false;
  param_sets::with_profile(profile, [&](auto p) {
    with_system(p, [&](const auto &c, const auto &statement, auto witness,
                       const Setup &su) {
      ok = run(c, statement, witness, su, opts, f.num("reps"));
    });
  });
  return ok ? 0 : 1;
}

// The flags of an application's serve and bench commands: the common
// flags, the hook's, and bench's --reps.
inline void add_serve_flags(bench::Flags &f) {
  bench::add_common_flags(f);
  add_hook_flags(f);
}
inline void add_bench_flags(bench::Flags &f) {
  add_serve_flags(f);
  f.flag("reps", "3", "the proofs to time");
}

// The flags of an application's export command: the common flags, the
// output directory and the provenance the exports record.
inline void add_export_flags(bench::Flags &f) {
  bench::add_common_flags(f);
  f.flag("dir", "", "the directory the Lean modules go to (required)")
      .flag("commit", "unknown", "the C++ commit the exports record")
      .flag("run-id", "unknown", "the bench run the exports record");
}
inline std::string export_dir(const bench::Flags &f) {
  if (f.str("dir").empty()) throw bench::UsageError("--dir is required");
  return f.str("dir");
}

}  // namespace proofs::gordiehowe::examples::bench_hook

#endif  // PRIVACY_PROOFS_ZK_LIB_BENCH_BENCH_HOOK_H_
