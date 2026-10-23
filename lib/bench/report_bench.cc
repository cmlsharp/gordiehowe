// Copyright 2026 Chad Sharp and Paul Grubbs
// SPDX-License-Identifier: Apache-2.0
// Build-once, round-robin report suite of the GordieHowe constructions
// (lib/gordiehowe/examples, bench_hook.h). Each case is a worker: the serve
// command of an application's bench executable (BUILD_ROOT/bench/
// <application>_bench serve --profile P ...). Workers retain their circuit
// and witness while idle; only one worker runs at a time. No process/IPC
// time is measured. The baselines are benchmarked from the
// longfellow-baselines repository (run_bench.sh --baselines).
//
// usage: report_bench BUILD_ROOT [wide|narrow] [FLAG...]
//   --only LIST          run only the named cases (comma-separated); the
//                        case outside the full report (gh-mdoc-1920) runs
//                        only when --only is given
//   --trials N           measured rounds after the warm-ups (default 9)
//   --warmups N          unreported proofs per case before the measured
//                        rounds (default 2)
//   --cpu C              once every worker is ready, pin all of its threads
//                        to core C (as longfellow-baselines'
//                        common/bench.py pins its workers)
//   --par-cpus LIST      the GordieHowe applications (gh-* cases), the
//                        batched SHA-256 (sha256-batched*) and SHA3-256
//                        (sha3-256-batched-*) also run multi-threaded
//                        (GH_THREADS=multi), one more worker per case
//                        labelled <case>@multi and pinned to the cores LIST
//                        ("a-b" or "a,b,..."); each round runs a case's two
//                        workers back to back. Every PQ_RESULT line ends
//                        with mode=single or mode=multi.
//   --par-scope S        the PQ_BENCH_PAR_CPUS line's scope: "all" when the
//                        set is every CPU of the run (default set)
//   --sha-blocks B       the block count of the SHA-256 cases
//                        sha256-longfellow, sha256-gkr and sha256-batched
//                        (default 8); sha256-{gkr,batched}-{64,2048}B are
//                        always 64- and 2048-byte messages, and
//                        sha256-batched-{1,8,32}KiB and
//                        sha3-256-batched-{1,8,32}KiB 1,024-, 8,192- and
//                        32,768-byte messages
//   --baseline-root DIR[,DIR...]  every case also runs from each build
//                        root DIR (its bench executables), labelled
//                        <case>@base for one root and <case>@<name> for
//                        several (NAME the directory above DIR/build), and
//                        @multi for the multi-threaded mode, interleaved
//                        with the case in every round: a comparison of
//                        builds in one run
//   --probe              build every worker, pass its setup lines (PQ_HASH
//                        among them) through, and stop before any proof
// and the workers' flags, which every worker gets: the common flags
// (bench/cli.h: --seed, --serial-commitments, --diagnostics,
// --rate-requests) and the bench hook's (bench/hook_flags.h: --params,
// --commit, --report).
#include <sys/wait.h>
#if defined(__linux__)
#include <sys/prctl.h>
#endif
#include <unistd.h>
#include <algorithm>
#include <csignal>
#include <cstdio>
#include <cstdlib>
#include <functional>
#include <memory>
#include <stdexcept>
#include <string>
#include <utility>
#include <vector>

#include "bench/affinity.h"
#include "bench/cli.h"
#include "bench/harness.h"
#include "bench/hook_flags.h"

namespace {

using Args = std::vector<std::string>;

struct Worker {
  pid_t pid = -1;
  FILE* input = nullptr;
  FILE* output = nullptr;
  std::string name;
  std::string optimization_policy;
  bool multi = false;
  // The worker ROOT/bench/BINARY serve --profile PROFILE ARGS, with
  // GH_THREADS set to its mode.
  Worker(const std::string& root, const std::string& profile,
         const char* binary, const std::string& label, const Args& args,
         bool multi_ = false)
      : name(label), multi(multi_) {
    const std::string path = root + "/bench/" + binary;
    Args argv_s = {path, "serve", "--profile", profile};
    argv_s.insert(argv_s.end(), args.begin(), args.end());
    std::vector<char*> argv_c;
    for (auto& a : argv_s) argv_c.push_back(a.data());
    argv_c.push_back(nullptr);
    int in[2], out[2];
    if (pipe(in) || pipe(out)) throw std::runtime_error("pipe failed");
    const pid_t parent = getpid();
    pid = fork();
    if (pid < 0) throw std::runtime_error("fork failed");
    if (pid == 0) {
#if defined(__linux__)
      // Do not leave a large idle worker behind if the driver is interrupted.
      prctl(PR_SET_PDEATHSIG, SIGTERM);
      if (getppid() != parent) _exit(1);
#else
      (void)parent;
#endif
      dup2(in[0], STDIN_FILENO);
      dup2(out[1], STDOUT_FILENO);
      close(in[0]); close(in[1]); close(out[0]); close(out[1]);
      // The threading knob (lib/gordiehowe/threads.h): the worker's mode.
      setenv("GH_THREADS", multi_ ? "multi" : "single", 1);
      execv(path.c_str(), argv_c.data());
      perror("exec worker");
      _exit(127);
    }
    close(in[0]); close(out[1]);
    input = fdopen(in[1], "w"); output = fdopen(out[0], "r");
    std::printf("BUILD %s\n", name.c_str()); std::fflush(stdout);
  }
  // Spawning and waiting are separate so every worker can build its circuit
  // and witness at the same time.  Only the MEASURED runs are serialized --
  // those still go one at a time, through run().
  void wait_ready() {
    read_until("PQ_READY");
    if (optimization_policy.empty())
      throw std::runtime_error(name + ": missing optimization policy");
    const std::string expected =
        "PQ_OPTIMIZATIONS preset=optimized unit_coefficients=1 "
        "subfield_encoding=1 native_ntt=1\n";
    if (optimization_policy != expected)
      throw std::runtime_error(name + ": unexpected optimization policy");
  }
  // One whole worker line, however long (a PQ_PARAMS line is several KB).
  bool next_line(std::string& line) {
    char* buf = nullptr;
    size_t cap = 0;
    const ssize_t n = getline(&buf, &cap, output);
    if (n >= 0) line.assign(buf, size_t(n));
    free(buf);
    return n >= 0;
  }
  std::string read_until(const char* prefix) {
    std::string line;
    while (next_line(line)) {
      if (line.rfind("PQ_OPTIMIZATIONS ", 0) == 0)
        optimization_policy = line;
      if (line.rfind(prefix, 0) == 0) return line;
      std::printf("[%s] %s", name.c_str(), line.c_str());
      std::fflush(stdout);
    }
    throw std::runtime_error(name + ": worker ended unexpectedly");
  }
  proofs::bench::RunResult run() {
    fputs("run\n", input); fflush(input);
    auto line = read_until("PQ_RESULT");
    if (!line.empty() && line.back() == '\n') line.pop_back();
    std::printf("[%s] %s mode=%s\n", name.c_str(), line.c_str(),
                multi ? "multi" : "single");
    proofs::bench::RunResult r;
    int ok;
    if (sscanf(line.c_str(), "PQ_RESULT %lf %lf %lf %zu %d", &r.commit_ms,
               &r.prove_ms, &r.verify_ms, &r.proof_bytes, &ok) != 5)
      throw std::runtime_error("invalid worker result");
    r.ok = ok;
    if (!r.ok) throw std::runtime_error(name + ": proof failed");
    return r;
  }
  void finish() {
    if (pid < 0) return;
    fputs("stop\n", input); fflush(input);
    fclose(input); input = nullptr;
    std::string line;
    while (next_line(line))
      std::printf("[%s] %s", name.c_str(), line.c_str());
    fclose(output); output = nullptr;
    int status; waitpid(pid, &status, 0); pid = -1;
    if (!WIFEXITED(status) || WEXITSTATUS(status) != 0)
      throw std::runtime_error(name + ": worker process failed");
  }
  ~Worker() {
    if (pid > 0) { kill(pid, SIGTERM); waitpid(pid, nullptr, 0); }
    if (input) fclose(input);
    if (output) fclose(output);
  }
};

void declare(proofs::bench::Flags& f) {
  proofs::bench::add_common_flags(f);
  proofs::gordiehowe::examples::bench_hook::add_hook_flags(f);
  f.flag("only", "", "run only the named cases (comma-separated)")
      .flag("trials", "9", "the measured rounds after the warm-ups")
      .flag("warmups", "2", "the unreported proofs per case first")
      .flag("cpu", "", "pin the single-threaded workers to this core")
      .flag("par-cpus", "", "also run the applications and batched hashes "
                            "multi-threaded, pinned to these cores")
      .flag("par-scope", "set", "the multi-threaded set's scope: set or all")
      .flag("sha-blocks", "8", "the SHA-256 cases' block count")
      .flag("baseline-root", "", "also run every case from these build "
                                 "roots (comma-separated), interleaved")
      .toggle("probe", "build every worker and stop before any proof");
}

}  // namespace

int main(int argc, char** argv) {
  const std::string usage =
      "usage: report_bench BUILD_ROOT [wide|narrow] [FLAG...]\n";
  std::vector<std::string> args(argv + 1, argv + argc);
  proofs::bench::Flags flags;
  declare(flags);
  for (const auto& a : args)
    if (a == "--help") {
      std::printf("%sflags:\n%s", usage.c_str(), flags.usage().c_str());
      return 0;
    }
  if (args.empty() || args[0].rfind("--", 0) == 0) {
    fprintf(stderr, "%s", usage.c_str());
    return 2;
  }
  const std::string root = args[0];
  args.erase(args.begin());
  std::string profile = "wide";
  if (!args.empty() && args[0].rfind("--", 0) != 0) {
    profile = args[0];
    args.erase(args.begin());
  }
  if (profile != "wide" && profile != "narrow") {
    fprintf(stderr, "%s", usage.c_str());
    return 2;
  }
  try {
    flags.parse(args);
  } catch (const proofs::bench::UsageError& e) {
    fprintf(stderr, "report_bench: %s\n%sflags:\n%s", e.what(), usage.c_str(),
            flags.usage().c_str());
    return 2;
  }
  printf("PQ_FIELD_PROFILE %s\n", profile.c_str());
  fflush(stdout);
  signal(SIGPIPE, SIG_IGN);
  try {
    // The flags every worker takes.
    Args pass = proofs::bench::common_args(flags);
    const Args hook =
        proofs::gordiehowe::examples::bench_hook::hook_args(flags);
    pass.insert(pass.end(), hook.begin(), hook.end());
    std::vector<std::unique_ptr<Worker>> workers;
    std::vector<proofs::bench::Case> cases;
    // --only restricts the run to the named cases.
    const bool only = flags.given("only");
    const std::string only_list = "," + flags.str("only") + ",";
    auto selected = [&](const std::string& name) {
      return !only || only_list.find("," + name + ",") != std::string::npos;
    };
    // The multi-threaded core set, when given; the hash probe builds the
    // single-threaded workers only.
    const bool probe = flags.on("probe");
    const std::vector<int> par_cpus =
        flags.given("par-cpus") && !probe
            ? proofs::bench::parse_cpus(flags.str("par-cpus"))
            : std::vector<int>{};
    if (flags.given("par-cpus") && !probe && par_cpus.empty())
      throw std::runtime_error("empty core list");
    // --baseline-root: each case also runs from those builds, labelled
    // <case>@base for one, <case>@<name> for several (NAME the directory
    // above the build root), after the case's own workers in every round.
    std::vector<std::pair<std::string, std::string>> roots = {{root, ""}};
    if (flags.given("baseline-root")) {
      std::vector<std::string> dirs;
      const std::string list = flags.str("baseline-root");
      for (size_t a = 0; a <= list.size();) {
        const size_t b = std::min(list.find(',', a), list.size());
        if (b > a) dirs.push_back(list.substr(a, b - a));
        a = b + 1;
      }
      for (const auto& d : dirs) {
        std::string nm = d;
        while (!nm.empty() && nm.back() == '/') nm.pop_back();
        if (nm.size() >= 6 && nm.compare(nm.size() - 6, 6, "/build") == 0)
          nm.resize(nm.size() - 6);
        nm = nm.substr(nm.find_last_of('/') + 1);
        roots.push_back({d, dirs.size() == 1 ? "@base" : "@" + nm});
      }
    }
    auto add = [&](const char* binary, const std::string& name,
                   const Args& case_args = {}) {
      if (!selected(name)) return;
      Args a = pass;
      a.insert(a.end(), case_args.begin(), case_args.end());
      for (const auto& [dir, tag] : roots) {
        const std::string label = name + tag;
        workers.emplace_back(new Worker(dir, profile, binary, label, a));
        Worker* w = workers.back().get();
        cases.push_back({label, [w]() { return w->run(); }});
        // The GordieHowe applications and the batched hashes also run
        // multi-threaded, back to back.
        const bool both = !par_cpus.empty() &&
                          (name.rfind("gh-", 0) == 0 ||
                           name.rfind("sha256-batched", 0) == 0 ||
                           name.rfind("sha3-256-batched-", 0) == 0);
        if (!both) continue;
        workers.emplace_back(
            new Worker(dir, profile, binary, label + "@multi", a, true));
        Worker* m = workers.back().get();
        cases.push_back({label + "@multi", [m]() { return m->run(); }});
      }
    };
    // The GordieHowe constructions (lib/gordiehowe/examples, bench_hook.h):
    // the four proofs of possession, and both rings' native and carrier arms
    // at each ring size.
    add("mldsa_native_bench", "gh-ml-native");
    // Its packing ablations (ROM parameters only; mldsa_native.h's
    // PackingAblation), interleaved with it round by round: no bit packing,
    // and no packing with the values in subfield rows.
    if (profile == "narrow")
      add("mldsa_native_bench", "gh-ml-native-nobitpack",
          {"--packing", "nobitpack"});
    if (profile == "narrow")
      add("mldsa_native_bench", "gh-ml-native-subfieldrows",
          {"--packing", "subfieldrows"});
    add("mldsa_emulated_bench", "gh-ml-emulated");
    // Its packing ablations, as ML-DSA native's (ROM parameters only;
    // setup.h's PackingAblation), interleaved with it round by round.
    if (profile == "narrow")
      add("mldsa_emulated_bench", "gh-ml-emulated-nobitpack",
          {"--packing", "nobitpack"});
    if (profile == "narrow")
      add("mldsa_emulated_bench", "gh-ml-emulated-subfieldrows",
          {"--packing", "subfieldrows"});
    add("falcon_native_bench", "gh-fn-native");
    add("falcon_emulated_bench", "gh-fn-emulated");
    for (size_t ring : {size_t{64}, size_t{256}, size_t{1024}}) {
      const std::string r = std::to_string(ring);
      for (const char* arm : {"native", "carrier"}) {
        add("mldsa_ring_bench", std::string("gh-ml-ring-") + arm + "-" + r,
            {"--ring-arm", arm, "--ring-size", r});
        add("falcon_ring_bench", std::string("gh-fn-ring-") + arm + "-" + r,
            {"--ring-arm", arm, "--ring-size", r});
      }
    }
    // The ECDSA mDL (examples/mdoc/mdoc.h, ROM parameters only): doc 3 at 1
    // attribute, the list-radius build, each proof's setup uncached and
    // timed.
    if (profile == "narrow") add("mdoc_bench", "gh-mdoc", {"--attrs", "1"});
    // Its device-signature ablation (mdoc.h, no device ECDSA verification
    // and no dpkx, dpky crossing), interleaved with it round by round.
    if (profile == "narrow")
      add("mdoc_bench", "gh-mdoc-nodevice", {"--attrs", "1", "--no-device"});
    // ---- The MAC and mask-test ablations (ROM parameters only;
    // examples/shared/ablation_testing.h, --ablation), each a worker of its
    // full system's executable interleaved with it round by round: the MAC
    // ablation (--ablation unsound-no-mac, cases -nomac: no MAC, unsound; a
    // measurement control as Longfellow's mdoc-v7-mac-ablation) of the four
    // proofs of possession and the ECDSA mDL; the per-chunk MAC ablation
    // (--ablation unsound-per-chunk-mac, cases -perchunk: Longfellow's
    // per-chunk MAC, not zero-knowledge, a measurement control) of ML-DSA-44
    // emulated and the ECDSA mDL; and the mask-test ablation (-untested:
    // Ligero without the mask test, each domain at the full system's
    // repetitions) of ML-DSA-44 native and emulated and the ECDSA mDL. The
    // post-quantum mDL's per-chunk MAC ablation runs in pq_mdoc_bench
    // (--unsound-per-chunk-mac-attrs).
    if (profile == "narrow") {
      struct Ablated {
        const char *binary, *name, *which;
      };
      static const Ablated kAblated[] = {
          {"mldsa_native_bench", "gh-ml-native-nomac", "unsound-no-mac"},
          {"mldsa_emulated_bench", "gh-ml-emulated-nomac", "unsound-no-mac"},
          {"falcon_native_bench", "gh-fn-native-nomac", "unsound-no-mac"},
          {"falcon_emulated_bench", "gh-fn-emulated-nomac", "unsound-no-mac"},
          {"mdoc_bench", "gh-mdoc-nomac", "unsound-no-mac"},
          {"mldsa_emulated_bench", "gh-ml-emulated-perchunk",
           "unsound-per-chunk-mac"},
          {"mdoc_bench", "gh-mdoc-perchunk", "unsound-per-chunk-mac"},
          {"mldsa_native_bench", "gh-ml-native-untested", "untested"},
          {"mldsa_emulated_bench", "gh-ml-emulated-untested", "untested"},
          {"mdoc_bench", "gh-mdoc-untested", "untested"},
      };
      for (const Ablated& a : kAblated) {
        Args case_args = {"--ablation", a.which};
        if (std::string(a.binary) == "mdoc_bench")
          case_args.insert(case_args.end(), {"--attrs", "1"});
        add(a.binary, a.name, case_args);
      }
    }
    // ---- end of the MAC and mask-test ablations.
    // The same at Vega's 1920-byte MSO bound (31 SHA-256 blocks in place of
    // v7's 40; mdoc_fixture.h, kVegaBlocks), for the comparison with Vega
    // only. It runs only when --only names it, so the full report leaves it
    // out.
    if (profile == "narrow" && only)
      add("mdoc_bench", "gh-mdoc-1920", {"--attrs", "1", "--blocks", "31"});
    // The SHAKE256 work of the Falcon and ML-DSA H domains alone, in a
    // GordieHowe system: in-GKR Keccak in a circuit constraint, and the
    // batched Keccak (gordiehowe/bench/hash_comparisons/keccak_compare_test.h).
    for (const char* preset : {"falcon", "ml-dsa"})
      for (const char* mode : {"gkr", "batched"})
        add("keccak_compare_bench",
            std::string("keccak-") + preset + "-" + mode,
            {"--preset", preset, "--mode", mode});
    // ---- The hash comparison with binius64 (benchmarks/binius.sh,
    // workloads sha3-256-private and sha256-private): SHA3-256 and SHA-256
    // of a private message of 1 KiB, 8 KiB and 32 KiB to a public digest,
    // batched (sha3-256-batched-<S> and sha256-batched-<S>, S = 1KiB, 8KiB,
    // 32KiB; keccak_compare_test.h's sha3 preset and
    // sha256_compare_test.h's batched column).
    struct HashSize {
      const char *label, *bytes;
    };
    static const HashSize kHashSizes[] = {
        {"1KiB", "1024"}, {"8KiB", "8192"}, {"32KiB", "32768"}};
    for (const HashSize& h : kHashSizes)
      add("keccak_compare_bench", std::string("sha3-256-batched-") + h.label,
          {"--preset", "sha3", "--mode", "batched", "--bytes", h.bytes});
    // The univariate-skip ablation (ROM parameters only):
    // sha3-256-batched-32KiB with every batch at skip width 1 (--no-skip,
    // DomainProfile::no_skip), interleaved with sha3-256-batched-32KiB round
    // by round.
    if (profile == "narrow")
      add("keccak_compare_bench", "sha3-256-batched-32KiB-noskip",
          {"--preset", "sha3", "--mode", "batched", "--bytes", "32768",
           "--no-skip"});
    for (const HashSize& h : kHashSizes)
      add("sha256_compare_bench", std::string("sha256-batched-") + h.label,
          {"--mode", "batched", "--bytes", h.bytes});
    // ---- end of the hash comparison with binius64.
    // The SHA-256 reference: an 8-block message (503 bytes) to a public
    // digest, by Longfellow's own pipeline at its unique-decoding minimum,
    // its flat circuit in a GordieHowe circuit constraint, and GordieHowe's
    // batched gadget (gordiehowe/bench/hash_comparisons/sha256_compare_test.h).
    const std::string sha_blocks = flags.str("sha-blocks");
    for (const char* mode : {"longfellow", "gkr", "batched"})
      add("sha256_compare_bench", std::string("sha256-") + mode,
          {"--mode", mode, "--blocks", sha_blocks});
    // The univariate-skip ablation (ROM parameters only): sha256-batched's
    // blocks with every batch at skip width 1 (--no-skip,
    // DomainProfile::no_skip), interleaved with sha256-batched round by
    // round.
    if (profile == "narrow")
      add("sha256_compare_bench", "sha256-batched-noskip",
          {"--mode", "batched", "--blocks", sha_blocks, "--no-skip"});
    // The flat circuit and the batched gadget on 64-byte and 2048-byte
    // messages (2 and 33 blocks): the two placements of SHA-256 at RSA's
    // message lengths, proved alone.
    for (const char* bytes : {"64", "2048"})
      for (const char* mode : {"gkr", "batched"})
        add("sha256_compare_bench",
            std::string("sha256-") + mode + "-" + bytes + "B",
            {"--mode", mode, "--bytes", bytes});
    if (workers.empty()) throw std::runtime_error("--only selects no case");
    for (auto& w : workers) w->wait_ready();
    if (probe) {
      for (auto& w : workers) w->finish();
      return 0;
    }
    // The single-threaded workers share one core and the multi-threaded
    // ones the core set, since only one worker runs at a time.
    if (flags.given("cpu")) {
      const std::string cpu = flags.str("cpu");
      for (auto& w : workers)
        if (!w->multi)
          proofs::bench::pin_process(w->pid, {std::atoi(cpu.c_str())});
      printf("PQ_BENCH_CPU %s\n", cpu.c_str());
      fflush(stdout);
    }
    // The multi-threaded workers on the core set (their pools take its size).
    if (!par_cpus.empty()) {
      for (auto& w : workers)
        if (w->multi) proofs::bench::pin_process(w->pid, par_cpus);
      printf("PQ_BENCH_PAR_CPUS %s K=%zu scope=%s\n",
             flags.str("par-cpus").c_str(), par_cpus.size(),
             flags.str("par-scope").c_str());
      fflush(stdout);
    }
    const int trials = int(flags.num("trials"));
    if (trials < 1) throw std::runtime_error("--trials must be positive");
    const int warmups = int(flags.num("warmups"));
    // Unreported warm-ups per case: fault retained circuits into memory and
    // exercise the complete proof path before collecting the report rounds.
    for (int i = 0; i < warmups; ++i)
      for (auto& c : cases) { printf("WARMUP %s\n", c.name.c_str()); c.run(); }
    proofs::bench::interleave(cases, trials);
    for (auto& w : workers) w->finish();
  } catch (const std::exception& e) {
    fprintf(stderr, "benchmark failed: %s\n", e.what()); return 1;
  }
}
