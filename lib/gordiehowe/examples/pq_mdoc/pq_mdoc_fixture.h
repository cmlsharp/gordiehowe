// Copyright 2026 Chad Sharp and Paul Grubbs
// SPDX-License-Identifier: Apache-2.0

// Post-quantum mdoc's tests and bench (pq_mdoc_test.cc, pq_mdoc_bench.cc):
// an arm's system built and compiled, the arms' environments, and a
// domain's plan as one line. Each file has its own copy (anonymous
// namespace).

#ifndef PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_EXAMPLES_PQ_MDOC_PQ_MDOC_FIXTURE_H_
#define PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_EXAMPLES_PQ_MDOC_PQ_MDOC_FIXTURE_H_

#include <cstddef>
#include <cstdio>
#include <memory>
#include <string>

#include "gordiehowe/examples/pq_mdoc/pq_mdoc_testing.h"

namespace proofs::gordiehowe::examples::pq_mdoc {
namespace {

template <class P, class Arm = FqArm>
struct Built {
  std::unique_ptr<PqMdocSystem<P, Arm>> sys;
  std::shared_ptr<const typename PqMdocSystem<P, Arm>::Compiled> c;
};
template <class P, class Arm = FqArm>
Built<P, Arm> build(const typename ArmProfiles<P, Arm>::E &env, size_t n,
                    size_t tbs_bytes, const PqMdocConfig &cfg = {}) {
  Built<P, Arm> b;
  b.sys = std::make_unique<PqMdocSystem<P, Arm>>(env, n, tbs_bytes, cfg);
  b.c = b.sys->compile();
  return b;
}
template <class P, class Arm = FqArm>
const typename ArmProfiles<P, Arm>::E &env() {
  using E = typename ArmProfiles<P, Arm>::E;
  static const E *e = new E;
  return *e;
}
template <class C>
std::string plan_line(const C &c, size_t d) {
  const DomainPlan p = c.compiled_domain(d).plan();
  char buf[512];
  // The Ligero choice's masking, repetitions, agreement threshold, line
  // certificate count and fallback target numerator (0: the profile's
  // target), which eval_params.py reads.
  std::snprintf(buf, sizeof(buf),
                "nw=%zu nq=%zu N=%zu k=%zu t=%zu nrow=%zu block_enc=%zu "
                "list_radius=%d layers=%zu wires=%zu quad_terms=%zu "
                "ninputs=%zu masking=%s ldt_reps=%zu A=%zu exceptions=%llu "
                "target_num=%llu",
                p.nw, p.nq, p.N, p.k, p.t, p.nrow, p.block_enc,
                int(p.list_radius), p.layers, p.wires, p.quad_terms,
                p.ninputs, p.split ? "split" : "untested", size_t(p.ldt_reps),
                p.agreement, (unsigned long long)p.exceptions,
                (unsigned long long)p.target_num);
  return buf;
}

template <class Arm>
constexpr const char *arm_name() {
  return Arm::kName;
}

}  // namespace
}  // namespace proofs::gordiehowe::examples::pq_mdoc

#endif  // PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_EXAMPLES_PQ_MDOC_PQ_MDOC_FIXTURE_H_
