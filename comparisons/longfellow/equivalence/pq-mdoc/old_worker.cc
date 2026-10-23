// Copyright 2026 Chad Sharp and Paul Grubbs
// SPDX-License-Identifier: Apache-2.0

// The old side of the pq-mdoc equivalence run: the fork's Longfellow-style
// baseline of its post-quantum mdoc (lib/gordiehowe/examples/
// pq_mdoc_baseline_test.cc at b7dfdb34, its Baseline<P>::run unchanged),
// compiled in the fork's tree with that test's own compile command, with a
// main that serves it as a worker of common/bench_worker.h in place of the
// gtest main (equivalence/pq-mdoc/build_old_worker.sh).
//
// usage: old_worker narrow|wide NATTR
//
// The totals use baselines/pq-mdoc's definitions as far as the fork's
// timers allow: commit = H + A commit (the fork's H commit includes its
// statement absorption and the blinds' fill); prove = H + A prove (the
// MAC key and targets, untimed by the fork, are under 1 ms); verify = H + A
// verify (the fork's H verify includes its statement absorption, and
// excludes the two ZkVerifiers' construction, which takes microseconds);
// bytes as the fork counts them (seed, both proofs, targets).
#include "gordiehowe/examples/pq_mdoc_baseline_test.cc"

#include <string>

#include "bench_worker.h"

namespace proofs::pq_mdoc_baseline {
namespace {
template <class P>
int lfb_serve(size_t n) {
  set_log_level(ERROR);
  const auto x = data::present(document(), data::bench_request(n));
  const auto in = gpq::instance_of(x);
  Baseline<P> b(n, in.statement.device_tbs.size(), 16);
  lfb::info({{"profile", P::kId},
             {"attrs", std::to_string(n)},
             {"chunks", std::to_string(b.nch)},
             {"compile_ms", std::to_string(b.compile_ms)},
             {"H_ninputs", std::to_string(b.circH->ninputs)},
             {"A_ninputs", std::to_string(b.circA->ninputs)}});
  SecureRandomEngine rng;
  lfb::serve([&]() {
    const Times t = b.run(x, in, rng);
    lfb::Trial T;
    T.commit_ms = t.commit_h + t.commit_a;
    T.prove_ms = t.prove_h + t.prove_a;
    T.verify_ms = t.verify_h + t.verify_a;
    T.proof_bytes = t.bytes;
    T.ok = t.ok;
    T.add("witness", t.witness);
    T.add("H_commit", t.commit_h);
    T.add("H_prove", t.prove_h);
    T.add("H_verify", t.verify_h);
    T.add("H_bytes", double(t.bytes_h));
    T.add("A_commit", t.commit_a);
    T.add("A_prove", t.prove_a);
    T.add("A_verify", t.verify_a);
    T.add("A_bytes", double(t.bytes_a));
    T.add("verify_statement", t.verify_statement);
    return T;
  });
  return 0;
}
}  // namespace
}  // namespace proofs::pq_mdoc_baseline

int main(int argc, char **argv) {
  if (argc != 3) return 2;
  const std::string profile = argv[1];
  const size_t n = std::strtoull(argv[2], nullptr, 10);
  if (profile == "narrow")
    return proofs::pq_mdoc_baseline::lfb_serve<proofs::pq_profile::Narrow>(n);
  if (profile == "wide")
    return proofs::pq_mdoc_baseline::lfb_serve<proofs::pq_profile::Wide>(n);
  return 2;
}
