// Copyright 2026 Chad Sharp and Paul Grubbs
// SPDX-License-Identifier: Apache-2.0

// Held-out program: offline memory checking (Blum, Evans, Gemmell, Kannan
// and Naor) of a read-write memory.
//
// The statement is a memory's initial and final contents (M words); the
// witness is a trace of T operations, each an address, a value and a
// write flag: a write stores the value, a read returns it. Operation t
// happens at time t + 1. The prover adds, for each operation, the value
// and time of the address's last access before it, and each address's
// time of last access at the end. The relation checks
//   - addresses below M, write flags 0 or 1, a read's value the stored one;
//   - each operation's previous access earlier than it (t - old_t in
//     [0, T));
//   - the multiset of tuples (address, value, time) written, the initial
//     memory at time 0 and every operation's new tuple, equals the
//     multiset read, every operation's old tuple and the final memory,
//     by the fingerprint prod (gamma - (a + beta v + beta^2 t)) of each
//     side, under two challenges beta and gamma.
// One Goldilocks^2 domain holds everything.

#ifndef PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_HELDOUT_MEMORY_CHECK_H_
#define PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_HELDOUT_MEMORY_CHECK_H_

#include <array>
#include <cstddef>
#include <cstdint>
#include <random>
#include <string>
#include <vector>

#include "gordiehowe/heldout/heldout_env.h"

namespace proofs::gordiehowe::heldout::memory_check {

constexpr size_t kM = 8;
constexpr size_t kT = 32;

template <template <class> class F>
struct Statement {
  F<std::array<uint32_t, kM>> initial;
  F<std::array<uint32_t, kM>> final_memory;
};
template <template <class> class F>
struct Witness {
  F<std::array<uint8_t, kT>> addr;
  F<std::array<uint32_t, kT>> value;
  F<std::array<uint8_t, kT>> is_write;
};

// The honest prover's view of a trace: each operation's old value and
// time, and each address's final time.
struct Trace {
  std::vector<uint64_t> old_value, old_time, final_time, final_value;
};
inline Trace run(const std::vector<uint64_t> &initial,
                 const std::vector<uint64_t> &addr,
                 const std::vector<uint64_t> &value,
                 const std::vector<uint64_t> &is_write) {
  Trace tr;
  std::vector<uint64_t> mem = initial, time(kM, 0);
  for (size_t t = 0; t < addr.size(); ++t) {
    const size_t a = size_t(addr[t] % kM);
    tr.old_value.push_back(mem[a]);
    tr.old_time.push_back(time[a]);
    if (is_write[t] != 0) mem[a] = value[t];
    time[a] = t + 1;
  }
  tr.final_time = time;
  tr.final_value = mem;
  return tr;
}

inline auto relation() {
  return compile<Statement, Witness>(
      compile_profile("memory-check"),
      [](GoldSys &cs, Statement<In> st, Witness<In> w) {
        auto &A = cs.domain(gold_profile(), "A");
        const GF &f = A.field();
        const auto initial = st.initial.values(A);
        const auto final_memory = st.final_memory.values(A);
        const auto addr = A.priv(Subfield<>{}, w.addr);
        const auto value = A.priv(Subfield<>{}, w.value);
        const auto is_write = A.priv(Subfield<>{}, w.is_write);
        // The old tuples and the final times, from the trace.
        using U = std::vector<uint64_t>;
        const auto deps = depends_on(initial, addr, value, is_write);
        const auto old_value = A.priv(
            Subfield<>{}, "old_value", Shape{kT}, deps,
            [](const U &i, const U &a, const U &v, const U &wr) {
              return run(i, a, v, wr).old_value;
            });
        const auto old_time = A.priv(
            Subfield<>{}, "old_time", Shape{kT}, deps,
            [](const U &i, const U &a, const U &v, const U &wr) {
              return run(i, a, v, wr).old_time;
            });
        const auto final_time = A.priv(
            Subfield<>{}, "final_time", Shape{kM}, deps,
            [](const U &i, const U &a, const U &v, const U &wr) {
              return run(i, a, v, wr).final_time;
            });
        assert_range(addr, kM, "addr");
        assert_range(is_write, 2, "is_write");
        // A read returns the stored value.
        assert_zero((1 - is_write) * (value - old_value), "read_value");
        std::vector<GF::Elt> times, cells;
        for (size_t t = 0; t < kT; ++t) times.push_back(f.of_scalar(t + 1));
        for (size_t m = 0; m < kM; ++m) cells.push_back(f.of_scalar(m));
        const auto now = A.constant("times", times);
        const auto cell = A.constant("cells", cells);
        // The previous access is earlier: now - 1 - old_time in [0, T).
        assert_range(now - 1 - old_time, kT, "old_before_now");
        assert_range(final_time, kT + 1, "final_time");
        const auto new_value = is_write * value + (1 - is_write) * old_value;
        const auto beta = A.challenge("beta");
        const auto gamma = A.challenge("gamma");
        auto fp = [&](const auto &a, const auto &v, const auto &t) {
          return gamma - (a + beta * v + beta * beta * t);
        };
        const auto written = as_expr(gamma - (cell + beta * initial))
                                 .concat(fp(addr, new_value, now));
        const auto read = as_expr(fp(addr, old_value, old_time))
                              .concat(fp(cell, final_memory, final_time));
        assert_equal(written.prod(), read.prod(), "multisets");
      },
      "heldout-memory-check");
}

struct Instance {
  Statement<Value> statement;
  Witness<Value> witness;
};
inline Instance instance(uint64_t seed) {
  std::mt19937_64 g(seed);
  Instance in;
  std::vector<uint64_t> init(kM), a(kT), v(kT), wr(kT);
  for (size_t m = 0; m < kM; ++m) {
    init[m] = uint32_t(g());
    in.statement.initial[m] = uint32_t(init[m]);
  }
  for (size_t t = 0; t < kT; ++t) {
    a[t] = g() % kM;
    wr[t] = g() % 2;
    v[t] = uint32_t(g());
  }
  // A read returns the stored value.
  const Trace pre = run(init, a, v, wr);
  for (size_t t = 0; t < kT; ++t)
    if (wr[t] == 0) v[t] = pre.old_value[t];
  const Trace tr = run(init, a, v, wr);
  for (size_t t = 0; t < kT; ++t) {
    in.witness.addr[t] = uint8_t(a[t]);
    in.witness.value[t] = uint32_t(v[t]);
    in.witness.is_write[t] = uint8_t(wr[t]);
  }
  for (size_t m = 0; m < kM; ++m)
    in.statement.final_memory[m] = uint32_t(tr.final_value[m]);
  return in;
}

}  // namespace proofs::gordiehowe::heldout::memory_check

#endif  // PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_HELDOUT_MEMORY_CHECK_H_
