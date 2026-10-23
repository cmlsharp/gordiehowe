// Copyright 2026 Chad Sharp and Paul Grubbs
// SPDX-License-Identifier: Apache-2.0
//
// Core lists and pinning: report_bench pins its workers' threads, the
// standalone benches pin themselves (Linux only).

#ifndef PRIVACY_PROOFS_ZK_LIB_BENCH_AFFINITY_H_
#define PRIVACY_PROOFS_ZK_LIB_BENCH_AFFINITY_H_

#include <cstdlib>
#include <stdexcept>
#include <string>
#include <vector>

#if defined(__linux__)
#include <dirent.h>
#include <sched.h>
#include <sys/types.h>
#endif

namespace proofs::bench {

// A core list "a-b" or "a,b,..." (or a mix), in order; empty for "".
inline std::vector<int> parse_cpus(const std::string &list) {
  std::vector<int> out;
  size_t at = 0;
  while (at < list.size()) {
    size_t end = list.find(',', at);
    if (end == std::string::npos) end = list.size();
    const std::string item = list.substr(at, end - at);
    const size_t dash = item.find('-');
    if (dash == std::string::npos) {
      out.push_back(std::stoi(item));
    } else {
      for (int c = std::stoi(item.substr(0, dash));
           c <= std::stoi(item.substr(dash + 1)); ++c)
        out.push_back(c);
    }
    at = end + 1;
  }
  return out;
}

#if defined(__linux__)
inline cpu_set_t cpu_set(const std::vector<int> &cpus) {
  cpu_set_t set;
  CPU_ZERO(&set);
  for (int c : cpus) CPU_SET(c, &set);
  return set;
}
#endif

// Pins the calling thread to CPUS (threads it creates later inherit them);
// an empty list pins nothing.
inline void pin_self(const std::vector<int> &cpus) {
  if (cpus.empty()) return;
#if defined(__linux__)
  const cpu_set_t set = cpu_set(cpus);
  if (sched_setaffinity(0, sizeof(set), &set) != 0)
    throw std::runtime_error("sched_setaffinity failed");
#else
  throw std::runtime_error("pinning needs Linux");
#endif
}

// Pins every thread of process PID to CPUS.
inline void pin_process(int pid, const std::vector<int> &cpus) {
#if defined(__linux__)
  const cpu_set_t set = cpu_set(cpus);
  const std::string dir = "/proc/" + std::to_string(pid) + "/task";
  DIR *d = opendir(dir.c_str());
  if (d == nullptr) throw std::runtime_error("cannot list " + dir);
  while (const dirent *e = readdir(d)) {
    if (e->d_name[0] == '.') continue;
    const pid_t tid = static_cast<pid_t>(std::atoi(e->d_name));
    if (sched_setaffinity(tid, sizeof(set), &set) != 0) {
      closedir(d);
      throw std::runtime_error("sched_setaffinity failed for " + dir);
    }
  }
  closedir(d);
#else
  (void)pid;
  (void)cpus;
  throw std::runtime_error("pinning needs Linux");
#endif
}

}  // namespace proofs::bench

#endif  // PRIVACY_PROOFS_ZK_LIB_BENCH_AFFINITY_H_
