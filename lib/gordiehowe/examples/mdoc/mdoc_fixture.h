// Copyright 2026 Chad Sharp and Paul Grubbs
// SPDX-License-Identifier: Apache-2.0

// Plain mdoc's tests and benches (mdoc_test.cc, mdoc_bench.cc): the system
// built at given profiles, the list-radius build the gh-mdoc bench case
// times, and Vega's MSO bound. Each file has its own copy (anonymous
// namespace).

#ifndef PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_EXAMPLES_MDOC_MDOC_FIXTURE_H_
#define PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_EXAMPLES_MDOC_MDOC_FIXTURE_H_

#include <cstddef>
#include <cstdio>
#include <memory>
#include <string>

#include "bench/timing.h"
#include "gordiehowe/examples/shared/setup.h"
#include "gordiehowe/examples/mdoc/mdoc_testing.h"

namespace proofs::gordiehowe::examples::mdoc::full {
namespace {

using bench::Clock;
using bench::ms_since;

struct Built {
  std::unique_ptr<MdocSystem> sys;
  const Compiled *c = nullptr;
};
Built build(const HProfile &hp, const AProfile &ap, size_t n,
            size_t blocks = examples::mdoc::kBlocks,
            bool device_signature = true,
            const examples::BuildOptions &options = {}) {
  Built b;
  b.sys = std::make_unique<MdocSystem>(hp, ap, n, blocks, device_signature,
                                       options);
  b.c = &b.sys->compiled();
  return b;
}
// The list-radius build: both domains at the compiler's choice for the
// classical target (domain_profile.h), the MSO buffer BLOCKS SHA-256 blocks;
// DEVICE_SIGNATURE false is the device-signature ablation.
Built build_list_radius(size_t n, size_t blocks = examples::mdoc::kBlocks,
                        bool device_signature = true,
                        const examples::BuildOptions &options = {}) {
  return build(list_h_profile(), list_a_profile(), n, blocks,
               device_signature, options);
}

// Domain D's plan as one line of the bench's records.
std::string plan_line(const Compiled &c, size_t d) {
  const DomainPlan p = c.compiled_domain(d).plan();
  char buf[320];
  std::snprintf(buf, sizeof(buf),
                "nw=%zu nq=%zu N=%zu k=%zu t=%zu nrow=%zu block_enc=%zu "
                "layers=%zu wires=%zu quad_terms=%zu ninputs=%zu",
                p.nw, p.nq, p.N, p.k, p.t, p.nrow, p.block_enc, p.layers,
                p.wires, p.quad_terms, p.ninputs);
  return buf;
}

// Vega's MSO bound (Kaviani and Setty, ePrint 2025/2094, Fig. 10): a
// 1920-byte tagged MSO. The message is kCose1Prefix (18 bytes, its last
// the bstr header 0x59), the MSO's 2-byte length and the MSO, so
// L = 18 + 2 + 1920 = 1940, and with SHA-256's 9 bytes of padding
// 1949 bytes: ceil(1949 / 64) = 31 blocks (30 hold 1920 bytes). 31 blocks
// hold a tagged MSO of up to 64 * 31 - 29 = 1955 bytes.
constexpr size_t kVegaBlocks = 31;
static_assert(64 * (kVegaBlocks - 1) < 18 + 2 + 1920 + 9 &&
              18 + 2 + 1920 + 9 <= 64 * kVegaBlocks);

}  // namespace
}  // namespace proofs::gordiehowe::examples::mdoc::full

#endif  // PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_EXAMPLES_MDOC_MDOC_FIXTURE_H_
