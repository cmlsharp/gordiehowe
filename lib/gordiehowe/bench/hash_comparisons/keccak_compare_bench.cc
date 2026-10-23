// Copyright 2026 Chad Sharp and Paul Grubbs
// SPDX-License-Identifier: Apache-2.0

// The Keccak comparison's bench executable (keccak_compare_test.h):
// keccak_compare_bench COMMAND [FLAG...].
//   serve    a report_bench worker (bench_hook.h, bench/harness.h) of the
//            preset --preset in the mode --mode
//   bench    the same records and --reps proofs without report_bench
//   export   the plan exports and realized programs of the batched perms
//            and sha3 presets at N = --perms permutations, in --dir:
//            GordieHowe/Generated/KeccakPerms/Batched<N>/<parameter set>/
//            and GordieHowe/Generated/SHA3/Batched<N>Perms/<parameter set>/
//            (configs keccak-perms-batched-N and sha3-256-batched-N). With
//            --bytes L, the sha3 preset alone at an L-byte message:
//            GordieHowe/Generated/SHA3/Batched<size>/ (config
//            sha3-256-batched-<L>B, size 1KiB or <L>B; lean_config_name),
//            as the serve command builds it. The message is private and the
//            output words public: msgLen 0.

#include <cstdio>
#include <string>
#include <vector>

#include "bench/bench_hook.h"
#include "bench/cli.h"
#include "gordiehowe/bench/hash_comparisons/keccak_compare_test.h"

namespace proofs::gordiehowe::examples::keccak_compare {
namespace {

namespace hook = examples::bench_hook;

void add_size_flags(bench::Flags &f) {
  f.flag("bytes", "", "the sha3 preset's message bytes (default: 136 N - 1 "
                      "at N = --perms)")
      .flag("perms", "8", "the perms preset's permutations, N");
}
void add_case_flags(bench::Flags &f) {
  f.flag("preset", "falcon", "the workload: falcon, ml-dsa, perms or sha3")
      .flag("mode", "batched", "the Keccak implementation: gkr or batched")
      .toggle("no-skip", "the batches without the univariate skip "
                         "(DomainProfile::no_skip, an ablation)");
  add_size_flags(f);
}

Preset preset(const bench::Flags &f) {
  const std::string s = f.str("preset");
  if (s == "falcon") return Preset::kFalcon;
  if (s == "ml-dsa") return Preset::kMlDsa;
  if (s == "perms") return Preset::kPerms;
  if (s == "sha3") return Preset::kSha3;
  throw bench::UsageError("unknown preset " + s);
}
Mode mode(const bench::Flags &f) {
  const std::string s = f.str("mode");
  if (s == "batched") return Mode::kBatched;
  if (s == "gkr") return Mode::kGkr;
  throw bench::UsageError("unknown mode " + s);
}
size_t sha3_bytes(const bench::Flags &f) {
  if (!f.given("bytes")) return 0;
  const size_t n = f.num("bytes");
  if (n == 0) throw bench::UsageError("--bytes must be positive");
  return n;
}
size_t perms(const bench::Flags &f) {
  const size_t n = f.num("perms");
  if (n == 0) throw bench::UsageError("--perms must be positive");
  return n;
}

// The case the flags select, built and compiled, and handed to FN with its
// statement, witness and setup record.
template <class P, class Fn>
void with_system(const bench::Flags &f, Fn fn) {
  const Preset pr = preset(f);
  const Mode md = mode(f);
  const bool no_skip = f.on("no-skip");
  Env<P> env;
  const std::string config =
      std::string("keccak-") + name(pr) + "-" + name(md);
  const std::string cfg = no_skip ? config + "-noskip" : config;
  hook::Setup su{cfg.c_str(), P::kId};
  auto t0 = hook::Clock::now();
  KeccakSystem<P> t(env, pr, md, no_skip, sha3_bytes(f), perms(f));
  su.build = hook::ms_since(t0);
  t0 = hook::Clock::now();
  const auto c = t.compile();
  su.compile = hook::ms_since(t0);
  std::printf("KECCAK_COMPARE preset=%s mode=%s profile=%s perms=%zu "
              "bytes=%zu\n",
              name(pr), name(md), P::kId, t.permutations(), t.sha3_bytes());
  fn(*c, t.statement(), [&] { return t.witness(); }, su);
}
auto systems(const bench::Flags &f) {
  return [&f](auto p, auto fn) { with_system<decltype(p)>(f, fn); };
}

int export_plans(const bench::Flags &f) {
  const std::string profile = bench::apply_common_flags(f);
  const std::string dir = hook::export_dir(f);
  const std::string n = std::to_string(perms(f));
  const bool bytes = f.given("bytes");
  const std::string sha3_size =
      bytes ? std::to_string(sha3_bytes(f)) + "B" : n;
  std::vector<Preset> presets = {Preset::kSha3};
  if (!bytes) presets.insert(presets.begin(), Preset::kPerms);
  param_sets::with_profile(profile, [&](auto p) {
    using P = decltype(p);
    Env<P> env;
    for (const Preset pr : presets) {
      KeccakSystem<P> t(env, pr, Mode::kBatched, false, sha3_bytes(f),
                        perms(f));
      const auto c = t.compile();
      const std::string config =
          pr == Preset::kPerms ? "keccak-perms-batched-" + n
                               : "sha3-256-batched-" + sha3_size;
      const compiler::ExportMeta meta{config, P::kId, f.str("commit"),
                                      f.str("run-id"), 0};
      const std::string path = write_plan(*c, dir, meta);
      std::printf("GH_EXPORT_PLAN profile=%s path=%s program=%s\n", P::kId,
                  path.c_str(), compiler::lean_program_file(dir, meta).c_str());
    }
  });
  return 0;
}

}  // namespace
}  // namespace proofs::gordiehowe::examples::keccak_compare

int main(int argc, char **argv) {
  namespace app = proofs::gordiehowe::examples::keccak_compare;
  namespace hook = proofs::gordiehowe::examples::bench_hook;
  using proofs::bench::Flags;
  return proofs::bench::run_commands(
      argc, argv, "The Keccak comparison's benches.",
      {{"serve", "a report_bench worker",
        [](Flags &f) {
          hook::add_serve_flags(f);
          app::add_case_flags(f);
        },
        [](const Flags &f) { return hook::serve_command(f, app::systems(f)); }},
       {"bench", "the worker's records and --reps proofs, alone",
        [](Flags &f) {
          hook::add_bench_flags(f);
          app::add_case_flags(f);
        },
        [](const Flags &f) { return hook::bench_command(f, app::systems(f)); }},
       {"export", "the batched presets' plan exports and realized programs",
        [](Flags &f) {
          hook::add_export_flags(f);
          app::add_size_flags(f);
        },
        app::export_plans}});
}
