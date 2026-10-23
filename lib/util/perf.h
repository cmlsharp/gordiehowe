// Copyright 2026 Chad Sharp and Paul Grubbs
// SPDX-License-Identifier: Apache-2.0

#ifndef PRIVACY_PROOFS_ZK_LIB_UTIL_PERF_H_
#define PRIVACY_PROOFS_ZK_LIB_UTIL_PERF_H_

// Measurement only: user-space cycles and instructions of the calling
// thread, under the eval_time switch (util/diagnostics.h). Counters that
// cannot be opened read as zero. Built with PROOFS_DIAGNOSTICS=0, a region
// does nothing.

#include <cstdint>
#include <cstdio>
#include <ctime>

#include "util/diagnostics.h"

#if defined(__linux__)
#include <linux/perf_event.h>
#include <sys/ioctl.h>
#include <sys/syscall.h>
#include <unistd.h>
#endif

namespace proofs {

#if PROOFS_DIAGNOSTICS
class PerfRegion {
 public:
  explicit PerfRegion(const char* label)
      : label_(label), on_(diagnostics::options().eval_time) {
    if (!on_) return;
#if defined(__linux__)
    fcy_ = open_counter(PERF_COUNT_HW_CPU_CYCLES);
    fin_ = open_counter(PERF_COUNT_HW_INSTRUCTIONS);
#endif
    clock_gettime(CLOCK_THREAD_CPUTIME_ID, &c0_);
#if defined(__linux__)
    if (fcy_ >= 0) ioctl(fcy_, PERF_EVENT_IOC_ENABLE, 0);
    if (fin_ >= 0) ioctl(fin_, PERF_EVENT_IOC_ENABLE, 0);
#endif
  }

  // Stop the counters and print one line tagged with LABEL and EXTRA.
  void report(const char* extra) {
    if (!on_) return;
    on_ = false;
    uint64_t cy = 0, ins = 0;
#if defined(__linux__)
    if (fcy_ >= 0) ioctl(fcy_, PERF_EVENT_IOC_DISABLE, 0);
    if (fin_ >= 0) ioctl(fin_, PERF_EVENT_IOC_DISABLE, 0);
    cy = read_counter(fcy_);
    ins = read_counter(fin_);
#endif
    timespec c1{};
    clock_gettime(CLOCK_THREAD_CPUTIME_ID, &c1);
    double us = (c1.tv_sec - c0_.tv_sec) * 1e6 + (c1.tv_nsec - c0_.tv_nsec) / 1e3;
    std::fprintf(stderr, "PQ_EVAL_TIME %s %s cpu_us=%.1f cycles=%llu instr=%llu\n",
                 label_, extra, us, (unsigned long long)cy,
                 (unsigned long long)ins);
  }

  ~PerfRegion() {
#if defined(__linux__)
    if (fcy_ >= 0) close(fcy_);
    if (fin_ >= 0) close(fin_);
#endif
  }

  PerfRegion(const PerfRegion&) = delete;
  PerfRegion& operator=(const PerfRegion&) = delete;

 private:
#if defined(__linux__)
  static int open_counter(uint64_t config) {
    perf_event_attr a{};
    a.type = PERF_TYPE_HARDWARE;
    a.size = sizeof(a);
    a.config = config;
    a.disabled = 1;
    a.exclude_kernel = 1;
    a.exclude_hv = 1;
    return int(syscall(SYS_perf_event_open, &a, 0, -1, -1, 0));
  }
  static uint64_t read_counter(int fd) {
    uint64_t v = 0;
    if (fd < 0 || read(fd, &v, sizeof(v)) != sizeof(v)) return 0;
    return v;
  }
#endif

  const char* label_;
  bool on_;
  int fcy_ = -1, fin_ = -1;
  timespec c0_{};
};
#else
class PerfRegion {
 public:
  explicit PerfRegion(const char*) {}
  void report(const char*) {}
  PerfRegion(const PerfRegion&) = delete;
  PerfRegion& operator=(const PerfRegion&) = delete;
};
#endif

}  // namespace proofs

#endif  // PRIVACY_PROOFS_ZK_LIB_UTIL_PERF_H_
