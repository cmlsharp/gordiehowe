// Copyright 2026 Chad Sharp and Paul Grubbs
// SPDX-License-Identifier: Apache-2.0

// The task pool (threads.h): nested groups complete with every task run
// once, and a caller waiting for its group helps only with the tasks nested
// inside it, never with an unrelated group's long task.

#include "gordiehowe/threads.h"

#include <atomic>
#include <chrono>
#include <cstddef>
#include <thread>
#include <vector>

#include "gtest/gtest.h"

namespace proofs::gordiehowe {
namespace {

using Clock = std::chrono::steady_clock;

void spin_until(const std::atomic<bool> &flag) {
  while (!flag.load(std::memory_order_acquire)) std::this_thread::yield();
}

TEST(TaskPool, NestedGroupsRunEveryTaskOnce) {
  internal::TaskPool pool(3);
  std::vector<std::atomic<int>> hits(8 * 16);
  pool.run(8, [&](size_t i) {
    pool.run(16, [&](size_t j) { hits[i * 16 + j].fetch_add(1); }, 0);
  }, 0);
  for (const auto &h : hits) EXPECT_EQ(h.load(), 1);
}

// One worker W. The caller C runs group OUTER, whose task 1 holds W until C
// has opened its INNER group and an unrelated thread E has opened group
// OTHER, whose task 1 is long (300 ms). W then takes INNER's task 1 (50 ms)
// and C, done with INNER's task 0, waits for it: C must not take OTHER's
// long task meanwhile, so INNER's run returns well before 300 ms.
TEST(TaskPool, WaitingCallerTakesNoUnrelatedTask) {
  internal::TaskPool pool(1);
  std::atomic<bool> inner_open{false}, other_open{false}, release_w{false},
      w_in_inner{false}, release_e{false};
  double inner_ms = 0;
  std::thread e;
  pool.run(2, [&](size_t i) {
    if (i == 1) {
      spin_until(release_w);
      return;
    }
    // Task 0, on C: E opens OTHER after C's INNER is open, so the worker
    // finds INNER first.
    const auto t0 = Clock::now();
    pool.run(2, [&](size_t j) {
      if (j == 1) {
        w_in_inner.store(true, std::memory_order_release);
        std::this_thread::sleep_for(std::chrono::milliseconds(50));
        return;
      }
      inner_open.store(true, std::memory_order_release);
      e = std::thread([&] {
        spin_until(inner_open);
        pool.run(2, [&](size_t k) {
          if (k == 1) {
            std::this_thread::sleep_for(std::chrono::milliseconds(300));
            return;
          }
          other_open.store(true, std::memory_order_release);
          spin_until(release_e);
        }, 0);
      });
      spin_until(other_open);
      release_w.store(true, std::memory_order_release);
      spin_until(w_in_inner);
    }, 0);
    inner_ms = std::chrono::duration<double, std::milli>(Clock::now() - t0)
                   .count();
    release_e.store(true, std::memory_order_release);
  }, 0);
  e.join();
  EXPECT_LT(inner_ms, 200.0);
}

}  // namespace
}  // namespace proofs::gordiehowe
