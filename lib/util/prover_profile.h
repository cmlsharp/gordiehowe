// Copyright 2026 Chad Sharp and Paul Grubbs
// SPDX-License-Identifier: Apache-2.0
//
// The profiler: phase timers of proofs and verifications. A Session times
// one proof phase and prints one PQ_PHASE line when it ends; a Scope inside
// it adds its time under its key. The switches are diagnostics::Options'
// profile, profile_timeline and profile_generators (util/diagnostics.h);
// off, a session makes no clock calls and a scope costs one branch. Built
// with PROOFS_DIAGNOSTICS=0, every class here is empty.
#ifndef PRIVACY_PROOFS_ZK_LIB_UTIL_PROVER_PROFILE_H_
#define PRIVACY_PROOFS_ZK_LIB_UTIL_PROVER_PROFILE_H_
#include <algorithm>
#include <atomic>
#include <chrono>
#include <cstdio>
#include <map>
#include <string>
#include <typeinfo>
#include <utility>
#include <vector>

#include "util/diagnostics.h"

namespace proofs::profiling {
using Clock = std::chrono::steady_clock;
inline double elapsed(Clock::time_point start) {
  return std::chrono::duration<double, std::milli>(Clock::now() - start).count();
}

#if PROOFS_DIAGNOSTICS
inline bool enabled() { return diagnostics::options().profile; }
inline thread_local std::map<std::string, double>* active = nullptr;
// The active session's time under its outermost scopes and marks, and the
// number of its scopes open on this thread: a scope opened at depth 0 is
// outermost.
inline thread_local double* covered = nullptr;
inline thread_local int depth = 0;
// With the timeline switch, each PQ_PHASE line also gives its session's
// start, t0= (ms since the process's first session), and its thread, tid=
// (a small number per thread, in order of first use), so that the sessions
// of one proof can be laid on a timeline.
inline bool timeline() { return diagnostics::options().profile_timeline; }
inline Clock::time_point epoch() {
  static const Clock::time_point t = Clock::now();
  return t;
}
inline int thread_number() {
  static std::atomic<int> next{0};
  static thread_local const int id = next++;
  return id;
}

// Disabled sessions make no clock calls. Records contain timings and public
// circuit dimensions, never witness values. Profiling is not an optimization.
// Each line ends with other=, the session's total less the time under its
// outermost scopes and marks, so that those keys and other= add up to
// total= (nested scopes' keys are within their outer scope's).
class Session {
 public:
  Session(const char* kind, const char* field, size_t inputs, size_t depth)
      : kind_(kind), field_(field), inputs_(inputs), depth_(depth), on_(enabled()),
        previous_(active), previous_covered_(covered),
        previous_depth_(profiling::depth) {
    if (on_) {
      if (timeline()) epoch();
      start_ = lap_ = Clock::now();
      active = &values_;
      covered = &covered_;
      profiling::depth = 0;
    }
  }
  void mark(const char* stage) {
    if (!on_) return;
    auto now = Clock::now();
    const double lap = std::chrono::duration<double, std::milli>(now - lap_).count();
    values_[stage] += lap;
    covered_ += lap;
    lap_ = now;
  }
  ~Session() {
    if (!on_) return;
    const double total = elapsed(start_);
    active = previous_;
    covered = previous_covered_;
    profiling::depth = previous_depth_;
    // One write per line, so that sessions ending on several threads do not
    // interleave.
    char buf[256];
    std::snprintf(buf, sizeof(buf), "PQ_PHASE %s %s inputs=%zu depth=%zu total=%.9f",
                  kind_, field_, inputs_, depth_, total);
    std::string line = buf;
    if (timeline()) {
      std::snprintf(buf, sizeof(buf), " t0=%.6f tid=%d",
                    std::chrono::duration<double, std::milli>(start_ - epoch()).count(),
                    thread_number());
      line += buf;
    }
    for (const auto& [key, value] : values_) {
      std::snprintf(buf, sizeof(buf), " %s=%.9f", key.c_str(), value);
      line += buf;
    }
    std::snprintf(buf, sizeof(buf), " other=%.9f", total - covered_);
    line += buf;
    line += "\n";
    std::fputs(line.c_str(), stdout);
  }
 private:
  const char* kind_;
  const char* field_;
  size_t inputs_, depth_;
  bool on_;
  Clock::time_point start_, lap_;
  std::map<std::string, double> values_;
  std::map<std::string, double>* previous_;
  double covered_ = 0;
  double* previous_covered_;
  int previous_depth_;
};
class Scope {
 public:
  explicit Scope(const char* key) : key_(key), target_(active) {
    if (target_) {
      outer_ = depth == 0 ? covered : nullptr;
      ++depth;
      start_ = Clock::now();
    }
  }
  ~Scope() {
    if (!target_) return;
    const double e = elapsed(start_);
    (*target_)[key_] += e;
    --depth;
    if (outer_) *outer_ += e;
  }
 private:
  const char* key_;
  std::map<std::string, double>* target_;
  double* outer_ = nullptr;
  Clock::time_point start_;
};
template <class Fn>
decltype(auto) measure(const char* key, Fn fn) {
  Scope scope(key);
  return fn();
}

// The generators switch (with the profile switch): the witness
// generation's per-generator times. A GeneratorSession around a proof's
// phase-0 generators (gordiehowe/system.h) times each generator under its
// node's name with every run of digits replaced by '#', so that the
// generators of one gadget's rounds or limbs share a key, and prints one
// line per key, largest first, then the session's total:
//   PQ_WGEN <session> key=<name> kind=<kind> n=<generators> ms=<time>
//   PQ_WGEN_TOTAL <session> ms=<total> timed=<sum over keys>
// The values' type checks after their generators are one key, <type
// checks>. Off unless both are on: a clock pair per generator would move
// the witness time of the profiled bench runs. The session's total
// includes the profiler's own work, about 1 us per generator, so it
// exceeds the timed sum by that. Records contain timings and node names,
// never witness values.
inline bool generators_enabled() {
  return enabled() && diagnostics::options().profile_generators;
}
struct GeneratorTimes {
  struct Entry {
    std::string kind;
    size_t n = 0;
    double ms = 0;
  };
  std::map<std::string, Entry> by_key;
  void add(const std::string& name, const char* kind, double ms) {
    std::string key;
    key.reserve(name.size());
    bool digit = false;
    for (char c : name) {
      if (c >= '0' && c <= '9') {
        if (!digit) key += '#';
        digit = true;
        continue;
      }
      digit = false;
      key += (c == ' ' || c == '\t' || c == '=') ? '_' : c;
    }
    Entry& e = by_key[key];
    if (e.kind.empty()) e.kind = kind;
    ++e.n;
    e.ms += ms;
  }
};
inline thread_local GeneratorTimes* generator_times = nullptr;
class GeneratorSession {
 public:
  explicit GeneratorSession(const char* name)
      : name_(name), on_(generators_enabled()), previous_(generator_times) {
    if (on_) {
      start_ = Clock::now();
      generator_times = &times_;
    }
  }
  ~GeneratorSession() {
    if (!on_) return;
    const double total = elapsed(start_);
    generator_times = previous_;
    std::vector<std::pair<double, const std::string*>> order;
    double timed = 0;
    for (const auto& [key, e] : times_.by_key) {
      order.push_back({e.ms, &key});
      timed += e.ms;
    }
    std::sort(order.begin(), order.end(),
              [](const auto& a, const auto& b) { return a.first > b.first; });
    std::string out;
    char buf[160];
    for (const auto& [ms, key] : order) {
      const auto& e = times_.by_key.at(*key);
      std::snprintf(buf, sizeof(buf), " kind=%s n=%zu ms=%.6f\n",
                    e.kind.c_str(), e.n, e.ms);
      out += "PQ_WGEN " + std::string(name_) + " key=" + *key + buf;
    }
    std::snprintf(buf, sizeof(buf), "PQ_WGEN_TOTAL %s ms=%.6f timed=%.6f\n",
                  name_, total, timed);
    out += buf;
    std::fputs(out.c_str(), stdout);
  }
 private:
  const char* name_;
  bool on_;
  GeneratorTimes* previous_;
  GeneratorTimes times_;
  Clock::time_point start_;
};
#else
// Built without diagnostics: no session, scope or generator time exists.
inline constexpr bool enabled() { return false; }
inline constexpr bool timeline() { return false; }
inline constexpr bool generators_enabled() { return false; }
class Session {
 public:
  Session(const char*, const char*, size_t, size_t) {}
  void mark(const char*) {}
};
class Scope {
 public:
  explicit Scope(const char*) {}
};
template <class Fn>
decltype(auto) measure(const char*, Fn fn) {
  return fn();
}
struct GeneratorTimes {
  void add(const std::string&, const char*, double) {}
};
inline constexpr GeneratorTimes* generator_times = nullptr;
class GeneratorSession {
 public:
  explicit GeneratorSession(const char*) {}
};
#endif
}  // namespace proofs::profiling
#endif  // PRIVACY_PROOFS_ZK_LIB_UTIL_PROVER_PROFILE_H_
