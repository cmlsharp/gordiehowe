// Copyright 2026 Chad Sharp and Paul Grubbs
// SPDX-License-Identifier: Apache-2.0

// Data parallelism inside the proof system's kernels (research branch
// intra-domain-par). A kernel splits its index range into chunks and runs
// them through the calling thread's runner when it has one (GordieHowe's
// multi-threaded mode installs its fork-join pool, gordiehowe/threads.h);
// the chunk boundaries depend only on the range and the grain, never on the
// thread count. Without a runner a kernel runs as one chunk on the calling
// thread. Each chunk writes only its own outputs; a reduction keeps one
// partial per chunk and combines them in chunk order. Field sums are exact,
// so a kernel's results are the same bytes in both modes and for any number
// of threads.

#ifndef PRIVACY_PROOFS_ZK_LIB_UTIL_PARALLEL_H_
#define PRIVACY_PROOFS_ZK_LIB_UTIL_PARALLEL_H_

#include <algorithm>
#include <cstddef>
#include <functional>
#include <memory>
#include <new>
#include <type_traits>
#include <utility>
#include <vector>

namespace proofs::parallel {

// Runs FN(I) for I in [0, N), possibly concurrently, returning when all
// have finished (rethrowing the first exception in index order).
class Runner {
 public:
  virtual ~Runner() = default;
  virtual void run(size_t n, const std::function<void(size_t)> &fn) = 0;
};

// The calling thread's runner, or null (sequential).
inline thread_local Runner *current = nullptr;

// Installs R as the calling thread's runner for the scope.
class Scope {
 public:
  explicit Scope(Runner *r) : prev_(current) { current = r; }
  ~Scope() { current = prev_; }
  Scope(const Scope &) = delete;
  Scope &operator=(const Scope &) = delete;

 private:
  Runner *prev_;
};

// The chunks of [0, N) of GRAIN indices each (the last may be shorter).
inline size_t chunks(size_t n, size_t grain) {
  return grain == 0 ? 0 : (n + grain - 1) / grain;
}

// FN(BEGIN, END) for each chunk of [0, N) of GRAIN indices.
template <class Fn>
void for_chunks(size_t n, size_t grain, Fn &&fn) {
  const size_t nc = chunks(n, grain);
  if (current == nullptr || nc < 2) {
    for (size_t c = 0; c < nc; ++c)
      fn(c * grain, std::min(n, (c + 1) * grain));
    return;
  }
  current->run(nc, [&](size_t c) {
    fn(c * grain, std::min(n, (c + 1) * grain));
  });
}

// FN(I) for each I in [0, N), in chunks of GRAIN indices.
template <class Fn>
void for_each(size_t n, size_t grain, Fn &&fn) {
  for_chunks(n, grain, [&](size_t b, size_t e) {
    for (size_t i = b; i < e; ++i) fn(i);
  });
}

// The grain that splits N indices into at most K chunks (at least 1), or
// one chunk when the calling thread has no runner: a chunk's fixed costs
// (an interpolator, a partial vector) are paid once per chunk, and a
// sequential kernel gains nothing from more. Field sums are exact, so the
// results do not depend on the chunking.
inline size_t grain_for(size_t n, size_t k) {
  if (current == nullptr) return std::max<size_t>(1, n);
  return std::max<size_t>(1, (n + k - 1) / k);
}

// The number of chunks the kernels aim for: enough to balance a few
// threads, few enough that a chunk's fixed costs stay small. A constant,
// so that chunk boundaries never depend on the thread count.
constexpr size_t kChunks = 16;

// An allocator whose value-initialization of an element writes nothing:
// a vector sized with it (resize, the count constructor) leaves its new
// elements as the allocation made them. Its element types are field
// elements, words and rows, trivially copyable and destructible, which
// the allocation creates. A kernel whose chunks write every element of
// such a vector touches each page first on the thread that fills it; a
// std::vector would write every element first on the calling thread, one
// page fault after another, before the chunks run.
template <class T>
struct ForOverwrite {
  using value_type = T;
  ForOverwrite() = default;
  template <class U>
  ForOverwrite(const ForOverwrite<U> &) {}  // NOLINT
  T *allocate(size_t n) { return std::allocator<T>().allocate(n); }
  void deallocate(T *p, size_t n) { std::allocator<T>().deallocate(p, n); }
  template <class U>
  void construct(U *) noexcept {
    static_assert(std::is_trivially_copyable_v<U> &&
                      std::is_trivially_destructible_v<U>,
                  "ForOverwrite: elements the allocation creates");
  }
  template <class U, class A0, class... A>
  void construct(U *p, A0 &&a0, A &&...a) {
    ::new (static_cast<void *>(p))
        U(std::forward<A0>(a0), std::forward<A>(a)...);
  }
  template <class U>
  bool operator==(const ForOverwrite<U> &) const {
    return true;
  }
};
// A vector whose elements the caller's chunks write (ForOverwrite).
template <class T>
using Buffer = std::vector<T, ForOverwrite<T>>;

// OUT resized to N copies of X, written in chunks under a runner. OUT
// keeps its capacity, so a buffer reused from proof to proof
// (gordiehowe/compiler/prover_scratch.h) writes pages it already holds.
template <class T>
void fill(Buffer<T> &out, size_t n, const T &x) {
  out.resize(n);
  T *p = out.data();
  for_chunks(n, grain_for(n, kChunks), [&](size_t b, size_t e) {
    std::fill(p + b, p + e, x);
  });
}
// A Buffer of N copies of X, written in chunks under a runner.
template <class T>
Buffer<T> filled(size_t n, const T &x) {
  Buffer<T> out;
  fill(out, n, x);
  return out;
}

}  // namespace proofs::parallel

#endif  // PRIVACY_PROOFS_ZK_LIB_UTIL_PARALLEL_H_
