// Copyright 2026 Chad Sharp and Paul Grubbs
// SPDX-License-Identifier: Apache-2.0

// The SHA-256 comparison's bench executable (sha256_compare_test.h):
// sha256_compare_bench COMMAND [FLAG...].
//   serve      a report_bench worker (bench_hook.h, bench/harness.h) of
//              the column --mode (longfellow, gkr or batched) at --blocks
//              blocks, or (gkr and batched) of an L-byte message in its
//              ceil((L + 9) / 64) blocks with --bytes L (config
//              sha256-<mode>-<L>B): the run's 64 B and 2048 B cases, and its
//              batched 1 KiB, 8 KiB and 32 KiB cases (17, 129 and 513
//              blocks). The reported time of a proof is commit + prove; the
//              witness is timed apart. The longfellow column serves the
//              harness's protocol itself.
//   bench      the same records and --reps proofs without report_bench
//   export     the plan export and realized program of the GordieHowe
//              column --mode (gkr or batched) at --blocks or --bytes, as
//              serve builds it, in --dir:
//              GordieHowe/Generated/SHA256/<Mode><Blocks>Blocks/ or
//              GordieHowe/Generated/SHA256/<Mode><size>/ (size 1KiB or
//              <L>B), then the parameter set, Plan.lean and Program.lean
//              (config sha256-<mode>-<blocks> or sha256-<mode>-<L>B, as the
//              serve command's PQ_HASH line)
//   tableaus   kListRadius's entries recomputed by the search
//   sweep      every column at each block count, medians
//   relpack    the relative-packing ablation
//   bitpack    the bit-packing comparison

#include <cstdio>
#include <cstring>
#include <string>
#include <vector>

#include "bench/bench_hook.h"
#include "bench/cli.h"
#include "bench/timing.h"
#include "gordiehowe/bench/hash_comparisons/sha256_compare_test.h"

namespace proofs::gordiehowe::examples::sha256_compare {
namespace {

namespace hook = examples::bench_hook;

// A flag's comma-separated sizes.
std::vector<size_t> sizes(const bench::Flags &f, const char *name) {
  std::vector<size_t> out;
  for (const std::string &s : f.list(name)) out.push_back(std::stoul(s));
  return out;
}

void add_size_flags(bench::Flags &f) {
  f.flag("mode", "batched", "the column: longfellow, gkr or batched")
      .flag("blocks", "8", "the message's blocks (64 B - 9 bytes per block)")
      .flag("bytes", "0", "the message's bytes in place of --blocks (gkr and "
                          "batched; 0: --blocks)");
}

Column column(const bench::Flags &f) {
  const std::string s = f.str("mode");
  if (s == "batched") return Column::kBatched;
  if (s == "gkr") return Column::kGkr;
  if (s == "longfellow") return Column::kLongfellow;
  throw bench::UsageError("unknown column " + s);
}

// The message size of the bench and the export: --bytes bytes (gkr and
// batched only) in its blocks, labelled <bytes>B, or else --blocks blocks of
// 64 B - 9 bytes, labelled by the block count.
struct MessageSize {
  size_t blocks = 8, bytes = 0;
  std::string label;
};
MessageSize message_size(const bench::Flags &f, Column col) {
  MessageSize ms;
  const size_t bytes = f.num("bytes");
  if (bytes != 0) {
    if (col == Column::kLongfellow)
      throw bench::UsageError(
          "--bytes: the longfellow column has block-count workloads only");
    ms.bytes = bytes;
    ms.blocks = lib::sha256::sha256_internal::blocks_of(bytes);
    ms.label = std::to_string(bytes) + "B";
    return ms;
  }
  ms.blocks = f.num("blocks");
  ms.label = std::to_string(ms.blocks);
  return ms;
}

// The longfellow column's proof as the harness records it, its GH_RUN line
// printed.
template <class P>
bench::RunResult longfellow_run(const LongfellowSha<P> &lf,
                                SecureRandomEngine &rng) {
  const ProofRun x = lf.run(rng);
  std::printf("GH_RUN witness=%.3f bytes=%zu\n", x.witness, x.bytes);
  bench::RunResult r;
  r.commit_ms = x.commit;
  r.prove_ms = x.prove;
  r.verify_ms = x.verify;
  r.proof_bytes = x.bytes;
  r.ok = x.ok;
  return r;
}

// The column the flags select, built, its records printed, then served
// (REPS 0) or proved REPS times. Returns whether every proof verified.
bool run_column(const bench::Flags &f, size_t reps) {
  const std::string profile = bench::apply_common_flags(f);
  const hook::Options opts = hook::hook_options(f);
  const Column col = column(f);
  const MessageSize ms = message_size(f, col);
  const size_t blocks = ms.blocks;
  bool ok = true;
  param_sets::with_profile(profile, [&](auto p) {
    using P = decltype(p);
    const std::string config = std::string("sha256-") + name(col) + "-" +
                               ms.label;
    if (col == Column::kLongfellow) {
      const auto t0 = Clock::now();
      const LongfellowSha<P> lf(blocks);
      std::printf("GH_SETUP config=%s profile=%s R=0 build=%.3f compile=0 "
                  "prepare=0 setup=0\n",
                  config.c_str(), P::kId, ms_since(t0));
      hook::print_hash<typename LongfellowSha<P>::Hash>(config, P::kId);
      std::printf("SHA_LIGERO profile=%s blocks=%zu mode=longfellow "
                  "model=unique-decoding t=%zu block_enc=%zu N=%zu k=%zu "
                  "bits=%.3f target=%g\n",
                  P::kId, blocks, lf.nreq(), lf.block_enc(), lf.tableau().N,
                  lf.tableau().k, lf.bits(), baseline_target<P>());
      SecureRandomEngine rng;
      if (reps == 0) {
        bench::serve(hook::kOptimizations,
                     [&]() { return longfellow_run(lf, rng); });
        return;
      }
      for (size_t i = 0; i < reps; ++i) {
        const bench::RunResult r = longfellow_run(lf, rng);
        std::printf("PQ_RESULT %.17g %.17g %.17g %zu %d\n", r.commit_ms,
                    r.prove_ms, r.verify_ms, r.proof_bytes, r.ok);
        std::fflush(stdout);
        ok = ok && r.ok;
      }
      return;
    }
    Env<P> env;
    // --no-skip: the batches without the univariate skip
    // (DomainProfile::no_skip, an ablation).
    const bool no_skip = f.on("no-skip");
    Prepared<P> x(env, blocks, col, /*unpacked=*/false, /*ud_rule=*/false,
                  no_skip, ms.bytes);
    std::printf("SHA_LIGERO profile=%s blocks=%zu bytes=%zu mode=%s model=%s "
                "t=%zu block_enc=%zu N=%zu k=%zu bits=%.3f target=%g\n",
                P::kId, blocks, x.t->message_bytes(), name(col), x.model(),
                x.opened(),
                x.ligero.block_enc, x.tableau.N, x.tableau.k, x.bits,
                gh_target<P>());
    const std::string cfg = no_skip ? config + "-noskip" : config;
    hook::Setup su{cfg.c_str(), P::kId};
    su.build = x.build_ms;
    su.compile = x.compile_ms;
    const auto witness = [&] { return x.t->witness(); };
    if (reps == 0)
      hook::serve(*x.c, x.t->statement(), witness, su, opts);
    else
      ok = hook::run(*x.c, x.t->statement(), witness, su, opts, reps);
  });
  return ok;
}

int serve(const bench::Flags &f) {
  run_column(f, 0);
  return 0;
}
int bench_column(const bench::Flags &f) {
  const size_t reps = f.num("reps");
  if (reps == 0) throw bench::UsageError("--reps must be positive");
  return run_column(f, reps) ? 0 : 1;
}

int export_plans(const bench::Flags &f) {
  const std::string profile = bench::apply_common_flags(f);
  const std::string dir = hook::export_dir(f);
  const Column col = column(f);
  if (col == Column::kLongfellow)
    throw bench::UsageError("longfellow is not a GordieHowe system");
  const MessageSize ms = message_size(f, col);
  param_sets::with_profile(profile, [&](auto p) {
    using P = decltype(p);
    Env<P> env;
    Prepared<P> x(env, ms.blocks, col, false, false, false, ms.bytes);
    // The message is private and the digest a public Bit input: msgLen 0.
    const compiler::ExportMeta meta{
        std::string("sha256-") + name(col) + "-" + ms.label, P::kId,
        f.str("commit"), f.str("run-id"), 0};
    const std::string path = write_plan(*x.c, dir, meta);
    std::printf("GH_EXPORT_PLAN profile=%s path=%s program=%s\n", P::kId,
                path.c_str(), compiler::lean_program_file(dir, meta).c_str());
  });
  return 0;
}

// kListRadius and kListRadiusUnpacked recomputed: at each block count of
// --blocks (default 1,2,8,17,32,33,64,129,513), the gkr and batched
// columns (--column gkr or batched: that column alone), and
// at 1, 8 and 32 blocks the unpacked batched column, built by Prepared's
// search (the table unread). Each prints its tableau and the planner's choice on it (SHA_TABLEAU), and an
// entry line of the table.
int tableaus(const bench::Flags &f) {
  const std::string profile = bench::apply_common_flags(f);
  const bool report = f.on("print-report");
  bool ok = true;
  param_sets::with_profile(profile, [&](auto p) {
    using P = decltype(p);
    for (size_t blocks :
         sizes(f, "blocks")) {
      for (Column col : {Column::kGkr, Column::kBatched})
        for (bool unpacked : {false, true}) {
          if (f.given("column") && f.str("column") != name(col)) continue;
          if (unpacked && (col != Column::kBatched ||
                           (blocks != 1 && blocks != 8 && blocks != 32)))
            continue;
          Env<P> env;
          const Prepared<P> x(env, blocks, col, unpacked, false, false, 0,
                              /*table=*/false, report);
          const DomainPlan dp = x.c->compiled_domain(0).plan();
          std::printf(
              "SHA_TABLEAU profile=%s column=%s blocks=%zu unpacked=%d "
              "rate=%zu block_enc=%zu N=%zu k=%zu t=%zu ldt_reps=%zu "
              "masking=%s bits=%.3f target=%g search_rounds=%zu "
              "grid_block_enc=%zu grid_t=%zu\n",
              P::kId, name(col), blocks, int(unpacked), dp.rate,
              x.ligero.block_enc, dp.N, dp.k, dp.t, dp.ldt_reps,
              dp.split ? "split" : "untested", x.bits, dp.target,
              x.search_rounds, x.grid_block_enc, x.grid_t);
          std::printf("SHA_ENTRY unpacked=%d     {\"%s\", Column::k%s, %zu, "
                      "%zu},  // (%zu, %zu)\n",
                      int(unpacked), P::kId,
                      col == Column::kGkr ? "Gkr" : "Batched", blocks,
                      x.ligero.block_enc, x.tableau.N, x.tableau.k);
          std::fflush(stdout);
        }
    }
  });
  return ok ? 0 : 1;
}

// Per block count, the columns built once, then --rounds rounds of
// --reps proofs per column, the first column rotating by round; medians
// over every proof. --plan prints the columns' Ligero and runs no proof.
int sweep(const bench::Flags &f) {
  const std::string profile = bench::apply_common_flags(f);
  const bool report = f.on("print-report");
  bool ok = true;
  param_sets::with_profile(profile, [&](auto p) {
    using P = decltype(p);
    const size_t rounds = f.num("rounds"),
                 reps = f.num("reps");
    const bool plan = f.on("plan");
    for (size_t blocks : sizes(f, "blocks")) {
      Env<P> env;
      const LongfellowSha<P> lf(blocks);
      Prepared<P> gkr(env, blocks, Column::kGkr, false, false, false, 0, true,
                      report),
          bat(env, blocks, Column::kBatched, false, false, false, 0, true,
              report);
      for (Column col : kColumns) {
        size_t t = 0, be = 0;
        Tableau tb;
        double bits = 0, target = baseline_target<P>();
        const char *model = "unique-decoding";
        if (col == Column::kLongfellow) {
          t = lf.nreq();
          be = lf.block_enc();
          tb = lf.tableau();
          bits = lf.bits();
        } else {
          target = gh_target<P>();
          const Prepared<P> &x = col == Column::kGkr ? gkr : bat;
          t = x.opened();
          be = x.ligero.block_enc;
          tb = x.tableau;
          bits = x.bits;
          model = x.model();
        }
        std::printf("SHA_LIGERO profile=%s blocks=%zu mode=%s model=%s t=%zu "
                    "block_enc=%zu N=%zu k=%zu bits=%.3f target=%g\n",
                    P::kId, blocks, name(col), model, t, be, tb.N, tb.k, bits,
                    target);
      }
      std::fflush(stdout);
      if (plan) continue;
      gkr.prepare();
      bat.prepare();
      std::vector<ProofRun> runs[3];
      SecureRandomEngine rng;
      auto run = [&](size_t c) {
        if (c == 0) return lf.run(rng);
        if (c == 1) return gkr.run(rng);
        return bat.run(rng);
      };
      for (size_t r = 0; r < rounds; ++r)
        for (size_t side = 0; side < 3; ++side) {
          const size_t c = (side + r) % 3;
          for (size_t k = 0; k < reps; ++k) {
            const ProofRun x = run(c);
            ok = ok && x.ok;
            runs[c].push_back(x);
            std::printf("SHA_RUN profile=%s blocks=%zu mode=%s round=%zu "
                        "witness=%.3f commit=%.3f prove=%.3f verify=%.3f "
                        "bytes=%zu ok=%d\n",
                        P::kId, blocks, name(kColumns[c]), r, x.witness,
                        x.commit, x.prove, x.verify, x.bytes, x.ok);
            std::fflush(stdout);
          }
        }
      for (size_t c = 0; c < 3; ++c) {
        auto med = [&](double ProofRun::*f) {
          std::vector<double> v;
          for (const auto &x : runs[c]) v.push_back(x.*f);
          return bench::median(v);
        };
        std::vector<double> b;
        for (const auto &x : runs[c]) b.push_back(double(x.bytes));
        Shape s;
        double compile_ms = 0;
        if (c == 0) {
          s.layers = lf.circuit().nl;
          s.committed = lf.circuit().ninputs - lf.circuit().npub_in;
          s.nw = lf.nw();
        } else {
          const Prepared<P> &x = c == 1 ? gkr : bat;
          s = x.shape;
          compile_ms = x.compile_ms;
        }
        std::printf(
            "SHA_MEDIAN profile=%s blocks=%zu mode=%s n=%zu bytes=%.0f "
            "witness=%.3f commit=%.3f prove=%.3f verify=%.3f compile=%.1f "
            "layers=%zu quad=%zu inputs=%zu nw=%zu tree=%zu lanes=%zu "
            "degree=%zu skip_rounds=%zu pads=%zu messages=%zu\n",
            P::kId, blocks, name(kColumns[c]), runs[c].size(), bench::median(b),
            med(&ProofRun::witness), med(&ProofRun::commit),
            med(&ProofRun::prove), med(&ProofRun::verify), compile_ms,
            s.layers, s.quad, s.committed, s.nw, s.ligero, s.lanes, s.degree,
            s.rounds, s.pads, s.messages);
        std::fflush(stdout);
      }
    }
  });
  return ok ? 0 : 1;
}

// The relative-packing ablation: the batched column with its GF(2^16) words
// packed into K cells (on) and committed one per subfield cell (off,
// DomainProfile::unpacked_s0), at --blocks (default 1,8,32). Both are
// built once, then --rounds (default 3) rounds of --reps (default
// 3) proofs per variant, the first variant alternating by round; medians
// over every proof. --plan prints the plans and runs no proof.
int relpack(const bench::Flags &f) {
  const std::string profile = bench::apply_common_flags(f);
  const bool report = f.on("print-report");
  bool ok = true;
  param_sets::with_profile(profile, [&](auto p) {
    using P = decltype(p);
    const size_t rounds = f.num("rounds"),
                 reps = f.num("reps");
    const bool plan = f.on("plan");
    const char *kName[2] = {"on", "off"};
    for (size_t blocks : sizes(f, "blocks")) {
      Env<P> env;
      Prepared<P> v[2] = {
          Prepared<P>(env, blocks, Column::kBatched, false, false, false, 0,
                      true, report),
          Prepared<P>(env, blocks, Column::kBatched, true, false, false, 0,
                      true, report)};
      for (size_t i = 0; i < 2; ++i) {
        const auto &x = v[i];
        const DomainPlan dp = x.c->compiled_domain(0).plan();
        std::printf("RELPACK_PLAN profile=%s blocks=%zu relpack=%s model=%s "
                    "t=%zu block_enc=%zu N=%zu k=%zu nrow=%zu nw=%zu "
                    "bits=%.3f compile=%.1f\n",
                    P::kId, blocks, kName[i], x.model(), x.opened(),
                    x.ligero.block_enc, x.tableau.N, x.tableau.k, dp.nrow,
                    dp.nw, x.bits, x.compile_ms);
        const std::string r = x.c->report();
        size_t at = 0;
        while (at < r.size()) {
          const size_t e = std::min(r.find('\n', at), r.size());
          const std::string line = r.substr(at, e - at);
          if (line.find("packing") != std::string::npos ||
              line.find("GF(2^16)") != std::string::npos ||
              line.find("GF(2^1)") != std::string::npos ||
              line.find("membership") != std::string::npos ||
              line.find("ligero") != std::string::npos)
            std::printf("RELPACK_REPORT relpack=%s blocks=%zu %s\n",
                        kName[i], blocks, line.c_str());
          at = e + 1;
        }
      }
      std::fflush(stdout);
      if (plan) continue;
      v[0].prepare();
      v[1].prepare();
      std::vector<ProofRun> runs[2];
      SecureRandomEngine rng;
      for (size_t r = 0; r < rounds; ++r)
        for (size_t side = 0; side < 2; ++side) {
          const size_t i = (side + r) % 2;
          for (size_t k = 0; k < reps; ++k) {
            const ProofRun x = v[i].run(rng);
            ok = ok && x.ok;
            runs[i].push_back(x);
            std::printf("RELPACK_RUN profile=%s blocks=%zu relpack=%s "
                        "round=%zu witness=%.3f commit=%.3f prove=%.3f "
                        "verify=%.3f bytes=%zu ok=%d\n",
                        P::kId, blocks, kName[i], r, x.witness, x.commit,
                        x.prove, x.verify, x.bytes, x.ok);
            std::fflush(stdout);
          }
        }
      for (size_t i = 0; i < 2; ++i) {
        auto med = [&](double ProofRun::*f) {
          std::vector<double> u;
          for (const auto &x : runs[i]) u.push_back(x.*f);
          return bench::median(u);
        };
        std::vector<double> b;
        for (const auto &x : runs[i]) b.push_back(double(x.bytes));
        std::printf("RELPACK_MEDIAN profile=%s blocks=%zu relpack=%s n=%zu "
                    "commit=%.3f prove=%.3f verify=%.3f bytes=%.0f\n",
                    P::kId, blocks, kName[i], runs[i].size(),
                    med(&ProofRun::commit), med(&ProofRun::prove),
                    med(&ProofRun::verify), bench::median(b));
      }
      std::fflush(stdout);
    }
  });
  return ok ? 0 : 1;
}

// The bit-packing comparison, at --blocks (default 1,8,32). Five rows:
//  - longfellow: the longfellow column;
//  - gkr-ud-on, gkr-ud-off: the gkr column at unique decoding by
//    Longfellow's column rule (LigeroChoice::ud_rule_t), with relative
//    packing on and off (DomainProfile::unpacked_s0);
//  - gkr-lr, batched-lr: the gkr and batched columns at list radius
//    (kListRadius).
// All are built once, then --rounds (default 3) rounds of --reps
// (default 3) proofs per row, the first row rotating by round; medians over
// every proof. --plan prints the plans and runs no proof.
int bitpack(const bench::Flags &f) {
  const std::string profile = bench::apply_common_flags(f);
  const bool report = f.on("print-report");
  bool ok = true;
  param_sets::with_profile(profile, [&](auto p) {
    using P = decltype(p);
    using HF = typename P::HashField;
    using LF = LongfellowSha<P>;
    const size_t rounds = f.num("rounds"),
                 reps = f.num("reps");
    const bool plan = f.on("plan");
    constexpr size_t kRows = 5;
    const char *kName[kRows] = {"longfellow", "gkr-ud-on", "gkr-ud-off",
                                "gkr-lr", "batched-lr"};
    for (size_t blocks : sizes(f, "blocks")) {
      Env<P> env;
      const LF lf(blocks);
      Prepared<P> v[kRows - 1] = {
          Prepared<P>(env, blocks, Column::kGkr, false, /*ud_rule=*/true,
                      false, 0, true, report),
          Prepared<P>(env, blocks, Column::kGkr, true, /*ud_rule=*/true,
                      false, 0, true, report),
          Prepared<P>(env, blocks, Column::kGkr, false, false, false, 0, true,
                      report),
          Prepared<P>(env, blocks, Column::kBatched, false, false, false, 0,
                      true, report)};
      const Circuit<HF> &lc = lf.circuit();
      const size_t plucked = lf.plucked_elements(), one = lf.bit_elements();
      const size_t pbits = plucked * LF::kPluckerBits;
      std::printf("BITPACK_PLAN profile=%s blocks=%zu row=longfellow "
                  "model=unique-decoding t=%zu block_enc=%zu N=%zu k=%zu "
                  "nrow=%zu nw=%zu bits=%.3f private=%zu plucked=%zu "
                  "plucked_bits=%zu one_bit=%zu bits_per_element=%.3f\n",
                  P::kId, blocks, lf.nreq(), lf.block_enc(), lf.tableau().N,
                  lf.tableau().k, lf.nrow(), lf.nw(), lf.bits(),
                  lc.ninputs - lc.npub_in, plucked, pbits, one,
                  double(pbits + one) / double(plucked + one));
      for (size_t i = 0; i + 1 < kRows; ++i) {
        const auto &x = v[i];
        const DomainPlan dp = x.c->compiled_domain(0).plan();
        std::printf("BITPACK_PLAN profile=%s blocks=%zu row=%s model=%s "
                    "t=%zu block_enc=%zu N=%zu k=%zu nrow=%zu nw=%zu "
                    "bits=%.3f committed=%zu compile=%.1f\n",
                    P::kId, blocks, kName[i + 1], x.model(), x.opened(),
                    x.ligero.block_enc, x.tableau.N, x.tableau.k, dp.nrow,
                    dp.nw, x.bits, x.shape.committed, x.compile_ms);
        const std::string r = x.c->report();
        size_t at = 0;
        while (at < r.size()) {
          const size_t e = std::min(r.find('\n', at), r.size());
          const std::string line = r.substr(at, e - at);
          if (line.find("packing") != std::string::npos ||
              line.find("GF(2^16)") != std::string::npos ||
              line.find("GF(2^1)") != std::string::npos ||
              line.find("ligero") != std::string::npos)
            std::printf("BITPACK_REPORT row=%s blocks=%zu %s\n", kName[i + 1],
                        blocks, line.c_str());
          at = e + 1;
        }
      }
      std::fflush(stdout);
      if (plan) continue;
      for (auto &x : v) x.prepare();
      std::vector<ProofRun> runs[kRows];
      SecureRandomEngine rng;
      for (size_t r = 0; r < rounds; ++r)
        for (size_t side = 0; side < kRows; ++side) {
          const size_t i = (side + r) % kRows;
          for (size_t k = 0; k < reps; ++k) {
            const ProofRun x = i == 0 ? lf.run(rng) : v[i - 1].run(rng);
            ok = ok && x.ok;
            runs[i].push_back(x);
            std::printf("BITPACK_RUN profile=%s blocks=%zu row=%s round=%zu "
                        "witness=%.3f commit=%.3f prove=%.3f verify=%.3f "
                        "bytes=%zu ok=%d\n",
                        P::kId, blocks, kName[i], r, x.witness, x.commit,
                        x.prove, x.verify, x.bytes, x.ok);
            std::fflush(stdout);
          }
        }
      for (size_t i = 0; i < kRows; ++i) {
        auto med = [&](double ProofRun::*f) {
          std::vector<double> u;
          for (const auto &x : runs[i]) u.push_back(x.*f);
          return bench::median(u);
        };
        std::vector<double> b;
        for (const auto &x : runs[i]) b.push_back(double(x.bytes));
        std::printf("BITPACK_MEDIAN profile=%s blocks=%zu row=%s n=%zu "
                    "commit=%.3f prove=%.3f verify=%.3f bytes=%.0f\n",
                    P::kId, blocks, kName[i], runs[i].size(),
                    med(&ProofRun::commit), med(&ProofRun::prove),
                    med(&ProofRun::verify), bench::median(b));
      }
      std::fflush(stdout);
    }
  });
  return ok ? 0 : 1;
}

}  // namespace
}  // namespace proofs::gordiehowe::examples::sha256_compare

int main(int argc, char **argv) {
  namespace app = proofs::gordiehowe::examples::sha256_compare;
  namespace hook = proofs::gordiehowe::examples::bench_hook;
  using proofs::bench::Flags;
  auto measurement = [](const char *blocks, const char *rounds) {
    return [=](Flags &f) {
      proofs::bench::add_common_flags(f);
      f.flag("blocks", blocks, "the block counts")
          .toggle("print-report", "print each compile report");
      if (rounds != nullptr) {
        f.flag("rounds", rounds, "the rounds")
            .flag("reps", rounds, "the proofs per round and row")
            .toggle("plan", "print the plans and run no proof");
      }
    };
  };
  return proofs::bench::run_commands(
      argc, argv, "The SHA-256 comparison's benches.",
      {{"serve", "a report_bench worker",
        [](Flags &f) {
          hook::add_serve_flags(f);
          app::add_size_flags(f);
          f.toggle("no-skip", "the batches without the univariate skip");
        },
        app::serve},
       {"bench", "the worker's records and --reps proofs, alone",
        [](Flags &f) {
          hook::add_bench_flags(f);
          app::add_size_flags(f);
          f.toggle("no-skip", "the batches without the univariate skip");
        },
        app::bench_column},
       {"export", "a GordieHowe column's plan export and realized program",
        [](Flags &f) {
          hook::add_export_flags(f);
          app::add_size_flags(f);
        },
        app::export_plans},
       {"tableaus", "kListRadius's entries recomputed by the search",
        [=](Flags &f) {
          measurement("1,2,8,17,32,33,64,129,513", nullptr)(f);
          f.flag("column", "", "gkr or batched alone (default: both)");
        },
        app::tableaus},
       {"sweep", "every column at each block count, medians",
        measurement("1,2,8,32,64", "5"), app::sweep},
       {"relpack", "the relative-packing ablation",
        measurement("1,8,32", "3"), app::relpack},
       {"bitpack", "the bit-packing comparison",
        measurement("1,8,32", "3"), app::bitpack}});
}
