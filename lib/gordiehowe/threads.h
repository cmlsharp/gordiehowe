// Copyright 2026 Chad Sharp and Paul Grubbs
// SPDX-License-Identifier: Apache-2.0

// GordieHowe's threading (research branch parallel-domains): one knob,
// single-threaded or multi-threaded, for the prover and the verifier. The
// transcript schedule is the same in both modes; the knob decides only
// whether the per-domain commitments and the forked branches run on
// threads. ProveOptions::multithreaded and verify's argument default to
// the environment's GH_THREADS (multi: multi-threaded; anything else or
// unset: single-threaded).

#ifndef PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_THREADS_H_
#define PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_THREADS_H_

#include <atomic>
#include <cstddef>
#include <cstdint>
#include <cstdlib>
#include <cstring>
#include <exception>
#include <functional>
#include <mutex>
#include <string>
#include <thread>
#include <vector>

#if defined(__linux__)
#include <sched.h>
#endif

#include "random/random.h"
#include "random/secure_random_engine.h"
#include "util/panic.h"
#include "util/parallel.h"

namespace proofs::gordiehowe {

// The default of the threading knob: multi-threaded when GH_THREADS=multi.
inline bool default_multithreaded() {
  static const bool on = [] {
    const char *e = std::getenv("GH_THREADS");
    return e != nullptr && std::string(e) == "multi";
  }();
  return on;
}

namespace internal {

// The cores this process may run on (its affinity mask), at least 1.
inline size_t available_cores() {
#if defined(__linux__)
  cpu_set_t set;
  CPU_ZERO(&set);
  if (sched_getaffinity(0, sizeof(set), &set) == 0) {
    const int n = CPU_COUNT(&set);
    if (n > 0) return size_t(n);
  }
#endif
  const unsigned n = std::thread::hardware_concurrency();
  return n > 0 ? n : 1;
}

// A fork-join pool of worker threads that spin while idle. A proof or
// verification in multi-threaded mode starts one at its beginning, sized
// to min(available cores, the work's widest fan-out) - 1 workers (the
// calling thread is the last), so that the workers' cores are awake and
// at full clock when work arrives (an idle core's first milliseconds run
// at its lowest frequency), and stops it at its end. run() may be called
// from inside a task: the caller works on its own group's tasks, then on
// the tasks of groups nested inside them, until its group is done. It
// never takes an unrelated task (a sibling branch, another domain's GKR),
// which would hold it past its own group's end; an idle worker takes any.
// Nesting never deadlocks: a waiting caller's group has no unclaimed task
// it could take, and every claimed task runs on a thread whose stack ends
// in it or in the tasks nested inside it.
class TaskPool : public parallel::Runner {
 public:
  explicit TaskPool(size_t workers) {
    th_.reserve(workers);
    for (size_t k = 0; k < workers; ++k) th_.emplace_back([this] { loop(); });
  }
  ~TaskPool() {
    stop_.store(true, std::memory_order_release);
    for (auto &t : th_) t.join();
  }
  TaskPool(const TaskPool &) = delete;
  TaskPool &operator=(const TaskPool &) = delete;
  size_t size() const { return th_.size(); }

  // parallel::Runner: the kernels' data-parallel chunks (util/parallel.h),
  // the calling thread taking chunk 0.
  void run(size_t n, const std::function<void(size_t)> &fn) override {
    run(n, fn, 0);
  }

  // Runs FN(I) for I in [0, N), task FIRST on the calling thread first, the
  // others on whichever thread claims them. Returns when all have finished;
  // the first exception in index order is rethrown then.
  void run(size_t n, const std::function<void(size_t)> &fn, size_t first) {
    if (n == 0) return;
    Group g(n, fn, first, current_group());
    {
      std::lock_guard<std::mutex> lock(mu_);
      open_.push_back(&g);
      pending_.fetch_add(n - 1, std::memory_order_release);
    }
    g.exec(first);
    // This group's tasks, then anyone's, until this group is done. Idle
    // threads read only atomics; the lock is taken only to claim a task.
    while (g.done.load(std::memory_order_acquire) != n) {
      if (g.open() && claim(g)) continue;
      if (!help(&g)) relax();
    }
    {
      std::lock_guard<std::mutex> lock(mu_);
      for (size_t i = 0; i < open_.size(); ++i)
        if (open_[i] == &g) {
          open_.erase(open_.begin() + long(i));
          break;
        }
    }
    for (const auto &e : g.err)
      if (e) std::rethrow_exception(e);
  }

 private:
  struct Group {
    Group(size_t n_, const std::function<void(size_t)> &fn_, size_t first_,
          const Group *parent_)
        : n(n_), fn(fn_), first(first_), parent(parent_), err(n_) {}
    // Task index of the K-th claim: every index but FIRST, in order.
    size_t index(size_t k) const { return k < first ? k : k + 1; }
    void exec(size_t i) {
      const Group *outer = current_group();
      current_group() = this;
      try {
        fn(i);
      } catch (...) {
        err[i] = std::current_exception();
      }
      current_group() = outer;
      done.fetch_add(1, std::memory_order_acq_rel);
    }
    // Whether this group was opened inside a task of G, or inside a task
    // of a group nested so.
    bool nested_in(const Group *g) const {
      for (const Group *x = parent; x != nullptr; x = x->parent)
        if (x == g) return true;
      return false;
    }
    bool open() const { return next.load(std::memory_order_relaxed) + 1 < n; }
    const size_t n;
    const std::function<void(size_t)> &fn;
    const size_t first;
    // The group of the task that opened this one (null outside any task).
    // It outlives this group: its task returns only after this run().
    const Group *parent;
    std::vector<std::exception_ptr> err;
    alignas(64) std::atomic<size_t> next{0};
    alignas(64) std::atomic<size_t> done{0};
  };

  // Claims and runs one unclaimed task of G (its owner's call); false when
  // none is left.
  bool claim(Group &g) {
    const size_t k = g.next.fetch_add(1, std::memory_order_acq_rel);
    if (k + 1 >= g.n) return false;
    pending_.fetch_sub(1, std::memory_order_acq_rel);
    g.exec(g.index(k));
    return true;
  }

  static void relax() {
#if defined(__x86_64__) || defined(__i386__)
    __builtin_ia32_pause();
#else
    std::this_thread::yield();
#endif
  }
  // The group of the task this thread runs (null outside any task).
  static const Group *&current_group() {
    thread_local const Group *g = nullptr;
    return g;
  }
  // Runs one task of an open group, of any group (WAITING null: an idle
  // worker) or of one nested inside WAITING's tasks (a caller waiting for
  // WAITING); false when there was none. The claim is made under the lock,
  // and a group leaves the list (under the lock) only once its tasks are
  // done, so a claimed group outlives its task; an open group's ancestors
  // are open too, so the nesting walk reads live groups.
  bool help(const Group *waiting = nullptr) {
    if (pending_.load(std::memory_order_acquire) == 0) return false;
    Group *g = nullptr;
    size_t i = 0;
    {
      std::lock_guard<std::mutex> lock(mu_);
      for (Group *x : open_) {
        if (!x->open()) continue;
        if (waiting != nullptr && !x->nested_in(waiting)) continue;
        const size_t k = x->next.fetch_add(1, std::memory_order_acq_rel);
        if (k + 1 >= x->n) continue;
        pending_.fetch_sub(1, std::memory_order_acq_rel);
        g = x;
        i = x->index(k);
        break;
      }
    }
    if (g == nullptr) return false;
    g->exec(i);
    return true;
  }
  void loop() {
    // Tasks a worker runs split their kernels' chunks over this pool too.
    parallel::Scope scope(this);
    while (!stop_.load(std::memory_order_acquire))
      if (!help()) relax();
  }

  std::vector<std::thread> th_;
  std::mutex mu_;
  // Groups with unfinished tasks.
  std::vector<Group *> open_;
  // Unclaimed tasks over all groups: idle threads poll it, not the lock.
  alignas(64) std::atomic<size_t> pending_{0};
  alignas(64) std::atomic<bool> stop_{false};
};

// Runs FN(I) for I in [0, N): in order on this thread without POOL, on
// POOL otherwise, task FIRST (default the last) on this thread.
inline void run_tasks(TaskPool *pool, size_t n,
                      const std::function<void(size_t)> &fn,
                      size_t first = SIZE_MAX) {
  if (pool == nullptr || n < 2) {
    for (size_t i = 0; i < n; ++i) fn(i);
    return;
  }
  pool->run(n, fn, first >= n ? n - 1 : first);
}

}  // namespace internal

// The calling thread's prover randomness: one SecureRandomEngine per thread
// (random/secure_random_engine.h), which serves draws from a 4 KB buffer
// filled by OpenSSL's RAND_bytes, refilled when empty; a byte is served
// once. No OpenSSL context is created per task, draw or proof, and no
// engine is shared between threads.
inline SecureRandomEngine &thread_random() {
  thread_local SecureRandomEngine engine;
  return engine;
}

}  // namespace proofs::gordiehowe

#endif  // PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_THREADS_H_
