// Copyright 2026 Chad Sharp and Paul Grubbs
// SPDX-License-Identifier: Apache-2.0

// The held-out programs' setup measurement (heldout_programs.h):
//   heldout_measure [--only CONFIG,...] [--reps N]
// builds and compiles each configuration N times (default 3) and prints,
// per compile,
//   GH_HELDOUT_SETUP config=<c> rep=<i> ms=<build and compile> cache=<outcome> cache_bytes=<n>
// Under GH_COMPILE_CACHE the first compile of a fresh cache stores the
// entry and the later ones hit it: their ms is the cache-hit setup.

#include <cstdio>
#include <cstdlib>
#include <set>
#include <sstream>
#include <string>

#include "gordiehowe/heldout/heldout_programs.h"

int main(int argc, char **argv) {
  using namespace proofs::gordiehowe::heldout;  // NOLINT
  std::set<std::string> only;
  int reps = 3;
  for (int i = 1; i < argc; ++i) {
    const std::string a = argv[i];
    if (a == "--only" && i + 1 < argc) {
      std::stringstream ss(argv[++i]);
      for (std::string c; std::getline(ss, c, ',');) only.insert(c);
    } else if (a == "--reps" && i + 1 < argc) {
      reps = std::atoi(argv[++i]);
    } else {
      std::fprintf(stderr, "usage: %s [--only A,B] [--reps N]\n", argv[0]);
      return 2;
    }
  }
  static const char *kinds[] = {"off", "hit", "stored", "not-stored",
                                "discarded"};
  for (const auto &e : exports()) {
    if (!only.empty() && !only.count(e.config)) continue;
    for (int r = 0; r < reps; ++r) {
      const HeldoutCompile c = e.compile();
      size_t bytes = 0;
      if (c.cache.kind != proofs::gordiehowe::CacheOutcome::Kind::kOff)
        if (const auto b = proofs::gordiehowe::compiler::read_file(c.cache.file))
          bytes = b->size();
      std::printf("GH_HELDOUT_SETUP config=%s rep=%d ms=%.3f cache=%s "
                  "cache_bytes=%zu\n",
                  e.config.c_str(), r, c.ms, kinds[int(c.cache.kind)], bytes);
      std::fflush(stdout);
    }
  }
  return 0;
}
