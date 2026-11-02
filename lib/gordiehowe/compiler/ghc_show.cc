// Copyright 2026 Chad Sharp and Paul Grubbs
// SPDX-License-Identifier: Apache-2.0

// ghc_show FILE.ghc: a GHC file as text (ghc.h's show): per section its
// index, name, type, flags and value, each value decoded by its section's
// type through the schema of the Lean types (ghc_gkr.h's gkr_schema, every
// type a GHC file holds), a reference to an earlier section as @<index>.
// Exits 1 with the reason on a file the schema does not read.
//
// ghc_show --schema: the schema's text (Schema::dump), which
// formal/scripts/ghc_schema.txt holds.

#include <cstdio>
#include <fstream>
#include <iterator>
#include <string>
#include <vector>

#include "gordiehowe/compiler/ghc.h"
#include "gordiehowe/compiler/ghc_gkr.h"

int main(int argc, char **argv) {
  namespace ghc = proofs::gordiehowe::ghc;
  if (argc != 2) {
    std::fprintf(stderr, "usage: ghc_show FILE.ghc | ghc_show --schema\n");
    return 2;
  }
  if (std::string(argv[1]) == "--schema") {
    std::fputs(ghc::gkr_schema().dump().c_str(), stdout);
    return 0;
  }
  std::ifstream in(argv[1], std::ios::binary);
  if (!in) {
    std::fprintf(stderr, "ghc_show: cannot read %s\n", argv[1]);
    return 1;
  }
  const std::vector<uint8_t> b((std::istreambuf_iterator<char>(in)), {});
  try {
    std::fputs(ghc::show(b, ghc::gkr_schema()).c_str(), stdout);
  } catch (const ghc::Error &e) {
    std::fprintf(stderr, "ghc_show: %s: %s\n", argv[1], e.what());
    return 1;
  }
  return 0;
}
