// Copyright 2026 Chad Sharp and Paul Grubbs
// SPDX-License-Identifier: Apache-2.0

// The held-out programs' plan export (heldout_programs.h):
//   heldout_export --dir DIR [--commit C] [--only CONFIG,...] [--list]
// writes each configuration's plan, realized program and proof modules
// under DIR (GordieHowe/Generated/Heldout/<lean>/ROMParams/), and prints
//   GH_EXPORT_PLAN config=<c> module=GordieHowe.Generated.Heldout.<lean>.ROMParams path=<plan>
// or, when the compiler or the exporter refuses the program,
//   GH_EXPORT_FAIL config=<c> what=<the error>
// It exits 0 when every selected configuration exported.

#include <cstdio>
#include <cstring>
#include <exception>
#include <set>
#include <sstream>
#include <string>

#include "gordiehowe/heldout/heldout_programs.h"

int main(int argc, char **argv) {
  using namespace proofs::gordiehowe::heldout;  // NOLINT
  std::string dir, commit = "unknown";
  std::set<std::string> only;
  bool list = false;
  for (int i = 1; i < argc; ++i) {
    const std::string a = argv[i];
    if (a == "--dir" && i + 1 < argc) {
      dir = argv[++i];
    } else if (a == "--commit" && i + 1 < argc) {
      commit = argv[++i];
    } else if (a == "--only" && i + 1 < argc) {
      std::stringstream ss(argv[++i]);
      for (std::string c; std::getline(ss, c, ',');) only.insert(c);
    } else if (a == "--list") {
      list = true;
    } else {
      std::fprintf(stderr,
                   "usage: %s --dir DIR [--commit C] [--only A,B] [--list]\n",
                   argv[0]);
      return 2;
    }
  }
  int failed = 0;
  for (const auto &e : exports()) {
    if (!only.empty() && !only.count(e.config)) continue;
    const std::string module = "GordieHowe.Generated.Heldout." + e.lean + "." +
                               proofs::gordiehowe::compiler::lean_param_set(
                                   P::kId);
    if (list) {
      std::printf("%s %s\n", e.config.c_str(), module.c_str());
      continue;
    }
    if (dir.empty()) {
      std::fprintf(stderr, "--dir is required\n");
      return 2;
    }
    try {
      const std::string path = e.run(dir, commit);
      std::printf("GH_EXPORT_PLAN config=%s module=%s path=%s\n",
                  e.config.c_str(), module.c_str(), path.c_str());
    } catch (const std::exception &ex) {
      std::string what = ex.what();
      for (char &c : what)
        if (c == '\n') c = ' ';
      std::printf("GH_EXPORT_FAIL config=%s what=%s\n", e.config.c_str(),
                  what.c_str());
      ++failed;
    }
    std::fflush(stdout);
  }
  return failed == 0 ? 0 : 1;
}
