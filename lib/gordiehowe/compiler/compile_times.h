// Copyright 2026 Chad Sharp and Paul Grubbs
// SPDX-License-Identifier: Apache-2.0

// GordieHowe compile-time regions (the compile_times switch,
// util/diagnostics.h): the wall time of each named phase of compile(), summed
// per region path over one outermost region and printed to stderr when it
// closes, one line each:
//   GH_CT system=NAME region=PATH ms=MS calls=N
// PATH joins the open regions' names with '/'. Off: a region costs one
// branch and builds no name.

#ifndef PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_COMPILER_COMPILE_TIMES_H_
#define PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_COMPILER_COMPILE_TIMES_H_

#include <chrono>
#include <cstdio>
#include <string>
#include <utility>
#include <vector>

#include "util/diagnostics.h"

namespace proofs::gordiehowe::compiler {

inline bool compile_times_on() { return diagnostics::options().compile_times; }

struct CompileTimesState {
  std::vector<std::string> stack;
  // Paths in first-use order, with their summed milliseconds and calls.
  std::vector<std::pair<std::string, std::pair<double, size_t>>> totals;
  std::string system;
};
inline CompileTimesState &compile_times_state() {
  thread_local CompileTimesState s;
  return s;
}

// The system name printed with the next outermost region's lines.
inline void compile_times_system(const std::string &name) {
  if (compile_times_on()) compile_times_state().system = name;
}

class CompileRegion {
 public:
  template <class Name>
  explicit CompileRegion(Name &&name) : on_(compile_times_on()) {
    if (!on_) return;
    auto &s = compile_times_state();
    std::string nm(std::forward<Name>(name));
    path_ = s.stack.empty() ? nm : s.stack.back() + "/" + nm;
    s.stack.push_back(path_);
    t0_ = std::chrono::steady_clock::now();
  }
  ~CompileRegion() {
    if (!on_) return;
    const double ms = std::chrono::duration<double, std::milli>(
                          std::chrono::steady_clock::now() - t0_)
                          .count();
    auto &s = compile_times_state();
    s.stack.pop_back();
    bool found = false;
    for (auto &[p, v] : s.totals)
      if (p == path_) {
        v.first += ms;
        ++v.second;
        found = true;
        break;
      }
    if (!found) s.totals.push_back({path_, {ms, 1}});
    if (!s.stack.empty()) return;
    for (const auto &[p, v] : s.totals)
      std::fprintf(stderr, "GH_CT system=%s region=%s ms=%.2f calls=%zu\n",
                   s.system.c_str(), p.c_str(), v.first, v.second);
    std::fflush(stderr);
    s.totals.clear();
  }
  CompileRegion(const CompileRegion &) = delete;
  CompileRegion &operator=(const CompileRegion &) = delete;

 private:
  bool on_;
  std::string path_;
  std::chrono::steady_clock::time_point t0_;
};

}  // namespace proofs::gordiehowe::compiler

// A region named by NAME (an expression evaluated only when timing is on)
// until the end of the enclosing scope.
#define GH_CT_CAT2(a, b) a##b
#define GH_CT_CAT(a, b) GH_CT_CAT2(a, b)
#define GH_COMPILE_REGION(NAME)                                   \
  ::proofs::gordiehowe::compiler::CompileRegion GH_CT_CAT(         \
      gh_ct_region_, __LINE__)(                                   \
      ::proofs::gordiehowe::compiler::compile_times_on()           \
          ? std::string(NAME)                                      \
          : std::string())

#endif  // PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_COMPILER_COMPILE_TIMES_H_
