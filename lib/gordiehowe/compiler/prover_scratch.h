// Copyright 2026 Chad Sharp and Paul Grubbs
// SPDX-License-Identifier: Apache-2.0

// GordieHowe: the prover's reusable working buffers.
//
// A domain's proof fills its large per-proof vectors into a scratch
// object's vectors, which keep their capacity when the proof ends: a
// batch's table words, its first round's tables, lanes and rows, its eq
// weights, its bound operand tables and their fold targets; the GKR input
// row's eq tables, the packing stages' and the root's combination buffers,
// the rows' term lists and the Ligero inner-product vector. The next proof that takes the same
// scratch writes pages the process already holds. A fresh vector of the
// same size would come, under glibc's default malloc, from a fresh mapping
// or from heap pages the allocator returned to the system, depending on
// the process's allocation history, and would fault on every page.
//
// A scratch serves one proof at a time. ScratchPool lends each proof in
// flight its own scratch (CompiledDomain owns the pool, DomainProver holds
// the lease for its proof), so concurrent proofs never share one; within a
// proof, each batch branch holds one of the scratch's BatchScratch while
// it runs, so batches that run at once on the pool never share one. Every
// buffer is resized and written before it is read: a proof reads nothing
// that an earlier proof left in it. A scratch's first proof keeps nothing
// (DomainScratch::keep), so a process's first proof allocates and frees
// as the per-proof vectors did.

#ifndef PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_COMPILER_PROVER_SCRATCH_H_
#define PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_COMPILER_PROVER_SCRATCH_H_

#include <cstddef>
#include <cstdint>
#include <memory>
#include <mutex>
#include <typeindex>
#include <unordered_map>
#include <utility>
#include <vector>

#include "util/parallel.h"

namespace proofs::gordiehowe::compiler {

// V's storage given back to the allocator: V empty, with no capacity.
template <class V>
void release(V &v) {
  V().swap(v);
}

// The working buffers of one batch's reduction in one proof.
template <class F>
struct BatchScratch {
  using Elt = typename F::Elt;
  using Table = parallel::Buffer<Elt>;
  // False in its domain scratch's first proof (DomainScratch::keep): each
  // buffer goes back to the allocator once it is used, where the
  // per-proof vectors were freed.
  bool keep = true;
  // The batch's table words (CompiledDomain::batch_words).
  std::vector<Elt> words;
  // The first round's host-word tables, one per table space, and the
  // operand map's lanes.
  std::vector<std::vector<uint64_t>> tables;
  std::vector<uint64_t> lanes;
  // The zerocheck's eq weights, its bound operand tables and the tables'
  // fold targets (MaskedFieldSkip::prove).
  std::vector<Elt> eq;
  std::vector<Table> bound, fold;
  // The first round's rows, whose type depends on the batch's relation
  // (BasicBooleanSkip's Rows, RuntimeBooleanSkip's Rows): one buffer per
  // type.
  template <class V>
  V &rows() {
    auto &slot = rows_[std::type_index(typeid(V))];
    if (!slot) slot = std::make_shared<V>();
    return *static_cast<V *>(slot.get());
  }
  // Every row buffer given back to the allocator.
  void release_rows() { rows_.clear(); }

 private:
  std::unordered_map<std::type_index, std::shared_ptr<void>> rows_;
};

// Lends one T to each user in flight (a proof, a batch branch). A lease
// returns its T to the pool when it ends; the pool keeps every T it lent,
// at most as many as the users that held one at once, and lends the one
// returned last first.
template <class T>
class ScratchPool {
  struct State {
    std::mutex mu;
    std::vector<std::unique_ptr<T>> free;
  };

 public:
  class Lease {
   public:
    Lease() = default;
    Lease(Lease &&) = default;
    Lease &operator=(Lease &&) = default;
    Lease(const Lease &) = delete;
    Lease &operator=(const Lease &) = delete;
    ~Lease() {
      if (state_ == nullptr || t_ == nullptr) return;
      std::lock_guard<std::mutex> lock(state_->mu);
      state_->free.push_back(std::move(t_));
    }
    T &operator*() const { return *t_; }
    T *operator->() const { return t_.get(); }

   private:
    friend class ScratchPool;
    Lease(State *state, std::unique_ptr<T> t)
        : state_(state), t_(std::move(t)) {}
    State *state_ = nullptr;
    std::unique_ptr<T> t_;
  };

  // A T no other user holds: one the pool kept, or a new one.
  Lease lease() const {
    std::unique_ptr<T> t;
    {
      std::lock_guard<std::mutex> lock(state_->mu);
      if (!state_->free.empty()) {
        t = std::move(state_->free.back());
        state_->free.pop_back();
      }
    }
    if (t == nullptr) t = std::make_unique<T>();
    return Lease(state_.get(), std::move(t));
  }

 private:
  std::unique_ptr<State> state_ = std::make_unique<State>();
};

// The working buffers of one domain's proof: the batches' BatchScratch,
// the GKR input row's eq tables (gkr_rows), the packing stages' and the
// root's combination buffers (TreeRows), the rows' term lists and the
// Ligero inner-product vector.
template <class F>
struct DomainScratch {
  using Elt = typename F::Elt;
  using Terms = std::vector<std::pair<size_t, Elt>>;
  // The proofs that held this scratch. In its first proof (none before)
  // each user gives its buffers back to the allocator once it is done with
  // them, as the per-proof vectors did, so that a process's first proof
  // reuses freed memory within the proof; from its second proof on (KEEP)
  // the buffers stay.
  size_t proofs = 0;
  bool keep() const { return proofs > 0; }
  // The batches' buffers, one lent to each batch branch while it runs:
  // batches that run one after another share one, and batches that run
  // at once on the pool hold their own.
  ScratchPool<BatchScratch<F>> batches;
  std::vector<Elt> input_eq[2];
  // The combination over L positions of each packing stage
  // (TreeRows::stage), the stages one at a time, and then of the root
  // (TreeRows::root).
  parallel::Buffer<Elt> combination;
  // Each stage's region coordinates, and then the Ligero inner-product
  // vector (LigeroProver::prove).
  parallel::Buffer<Elt> region;
  // The term lists of the rows a proof built (TreeRows::Row::terms), which
  // the rows return when the proof ends: the next proof's input row and
  // remainder rows take the largest. Empty, with their capacity.
  std::vector<Terms> spare_terms;
  Terms take_terms() {
    if (spare_terms.empty()) return {};
    auto best = spare_terms.begin();
    for (auto it = spare_terms.begin(); it != spare_terms.end(); ++it)
      if (it->capacity() > best->capacity()) best = it;
    Terms t = std::move(*best);
    spare_terms.erase(best);
    return t;
  }
  // Keeps T's capacity when it is large (kSpareTerms entries or more), at
  // most kSpares lists.
  static constexpr size_t kSpareTerms = 1 << 12, kSpares = 16;
  void give_terms(Terms &&t) {
    if (!keep() || t.capacity() < kSpareTerms) return;
    t.clear();
    if (spare_terms.size() < kSpares) {
      spare_terms.push_back(std::move(t));
      return;
    }
    auto least = spare_terms.begin();
    for (auto it = spare_terms.begin(); it != spare_terms.end(); ++it)
      if (it->capacity() < least->capacity()) least = it;
    if (least->capacity() < t.capacity()) *least = std::move(t);
  }
};

// Eqs' table EQ[Q, i], i < N <= 2^LOGN (arrays/eqs.h), into OUT, which
// keeps its capacity: the recurrence of Eqs' filleq, with the same field
// operations, in place of Eqs' own allocation.
template <class F>
void fill_eq(const F &f, size_t logn, size_t n, const typename F::Elt *q,
             std::vector<typename F::Elt> &out) {
  using Elt = typename F::Elt;
  out.resize(n);
  Elt *eq = out.data();
  eq[0] = f.one();
  for (size_t l = logn; l-- > 0;) {
    const size_t nl = 1 + ((n - 1) >> l);
    size_t i = 1 + ((nl - 1) >> 1);
    if (2 * i - 1 >= nl) {
      i--;
      Elt v = eq[i], qv = q[l];
      f.mul(qv, v);
      eq[2 * i] = v;
      f.sub(eq[2 * i], qv);
    }
    while (i-- > 0) {
      Elt v = eq[i], qv = q[l];
      f.mul(qv, v);
      eq[2 * i] = v;
      f.sub(eq[2 * i], qv);
      eq[2 * i + 1] = qv;
    }
  }
}

}  // namespace proofs::gordiehowe::compiler

#endif  // PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_COMPILER_PROVER_SCRATCH_H_
