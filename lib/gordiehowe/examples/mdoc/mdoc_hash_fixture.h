// Copyright 2026 Chad Sharp and Paul Grubbs
// SPDX-License-Identifier: Apache-2.0

// The tests and bench of mdoc's domain H (mdoc_hash_test.cc,
// mdoc_hash_bench.cc): its system compiled once per attribute count. Each
// file has its own copy (anonymous namespace).

#ifndef PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_EXAMPLES_MDOC_MDOC_HASH_FIXTURE_H_
#define PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_EXAMPLES_MDOC_MDOC_HASH_FIXTURE_H_

#include <cstddef>
#include <memory>
#include <vector>

#include "gordiehowe/examples/mdoc/mdoc_hash_testing.h"

namespace proofs::gordiehowe::examples::mdoc::testing {
namespace {

// A compiled system for N attributes, built once per attribute count.
struct Compiled {
  std::unique_ptr<MdocHashSystem> sys;
  const Sys::Compiled *c = nullptr;
};
Compiled &compiled(size_t n) {
  static std::vector<std::unique_ptr<Compiled>> cache(5);
  if (!cache.at(n)) {
    auto x = std::make_unique<Compiled>();
    x->sys = std::make_unique<MdocHashSystem>(profile(), n);
    x->c = &x->sys->compiled();
    cache[n] = std::move(x);
  }
  return *cache[n];
}

}  // namespace
}  // namespace proofs::gordiehowe::examples::mdoc::testing

#endif  // PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_EXAMPLES_MDOC_MDOC_HASH_FIXTURE_H_
