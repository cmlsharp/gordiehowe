// Copyright 2026 Chad Sharp and Paul Grubbs
// SPDX-License-Identifier: Apache-2.0

// GordieHowe: test support for the Falcon-512 emulated system
// (falcon_emulated.h), which a standalone implementation does not need:
//   FalconEmulatedSystem   the relation with the assignments of example
//                          values
//   node_id, a_domain      lookups into a built system
//   a_inventory            A's phase-0 storage against the spec's inventory
//   export_plan            the compiled plan as a Lean data file
//                          (plan_export.h), the bench hook
//   compare::              the host encodings of c (words, bytes, MAC
//                          chunks) and canonical integers, for checking the
//                          generators against the host witness

#ifndef PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_EXAMPLES_FALCON_FALCON_EMULATED_TESTING_H_
#define PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_EXAMPLES_FALCON_FALCON_EMULATED_TESTING_H_

#include <cstddef>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <fstream>
#include <memory>
#include <sstream>
#include <stdexcept>
#include <string>
#include <vector>

#include "gordiehowe/compiler/plan_export.h"
#include "gordiehowe/examples/falcon/falcon_builders.h"
#include "gordiehowe/examples/falcon/falcon_emulated.h"
#include "gordiehowe/examples/shared/program_testing.h"
#include "gordiehowe/examples/shared/system_testing.h"

namespace proofs::gordiehowe::examples::falcon::emulated {

// The relation for messages of at most MAX_BYTES bytes, with the
// assignments of example values, for the tests and benchmarks that drive
// the prover directly.
template <class P>
struct FalconEmulatedSystem
    : RelationSystem<typename Env<P>::Sys, FalconStatement<Value>,
                     FalconWitness<Value>> {
  using E = Env<P>;
  using HF = typename E::HF;
  using AF = typename E::AF;
  using PH = typename E::PH;
  using Base = RelationSystem<typename E::Sys, FalconStatement<Value>,
                              FalconWitness<Value>>;
  using typename Base::Assignment;

  size_t max_bytes;

  FalconEmulatedSystem(const E &env, size_t max,
                       const BuildOptions &build = {})
      : Base(falcon_emulated<P>(env, max, build)), max_bytes(max) {}

  Assignment statement(const std::vector<uint64_t> &hhat) const {
    return Base::statement(falcon_statement(hhat));
  }
  Assignment witness(const std::vector<uint8_t> &nonce,
                     const std::vector<uint8_t> &msg,
                     const std::vector<uint64_t> &s2) const {
    return Base::witness(falcon_witness(nonce, msg, s2, max_bytes));
  }
};

// The node named NAME in system S.
template <class S>
size_t node_id(const S &s, const std::string &name) {
  const auto &N = s.graph().nodes;
  for (size_t i = 0; i < N.size(); ++i)
    if (N[i].name == name) return i;
  throw std::runtime_error("no node " + name);
}

// The plan export of profile P (plan_export.h): the system as the bench
// builds it for MSG_LEN-byte messages, compiled,
// written to DIR with its realized program (write_plan). Returns the plan's
// path.
template <class P>
std::string export_plan(const std::string &dir, const std::string &commit,
                        const std::string &run_id, size_t msg_len) {
  const Env<P> env;
  FalconEmulatedSystem<P> t(env, msg_len);
  const auto c = t.compile();
  const compiler::ExportMeta meta{"falcon-emulated", P::kId, commit, run_id,
                                  msg_len};
  return write_plan(*c, dir, meta);
}

// Domain A of system S (falcon_emulated declares H, then A).
template <class P>
auto &a_domain(const typename Env<P>::Sys &cs) {
  using Sys = typename Env<P>::Sys;
  using D = Domain<typename Env<P>::AF>;
  auto *d = dynamic_cast<const D *>(cs.domains().at(1).get());
  if (d == nullptr) throw std::runtime_error("domain 1 is not A");
  return *d;
}

// A's phase-0 storage by inventory category: the compiled coordinates and
// the specified ones (the spec column of a_inventory).
struct InventoryRow {
  std::string object;
  size_t now = 0, spec = 0;
  std::string note;
};

// A's committed phase-0 coordinates by spec category, from the compiled
// system: private inputs, unbound phase-0 advice and pad copies, then
// the pads compile() allocates, one per late value of A (its message's
// length). The rows add up to compiled.coordinates(A), or a last row shows
// the difference.
template <class P>
std::vector<InventoryRow> a_inventory(
    const typename Env<P>::Sys &cs,
    const typename Env<P>::Sys::Compiled &compiled) {
  const auto &A = a_domain<P>(cs);
  const auto &N = cs.graph().nodes;
  auto is_cell = [&](size_t id) {
    const Node &nd = N[id];
    if (nd.domain != A.index) return false;
    if (nd.kind == Kind::kPrivateInput || nd.kind == Kind::kPadCopy)
      return true;
    return nd.kind == Kind::kAdvice && compiled.phase(id) == 0 &&
           A.bindings().count(id) == 0;
  };
  auto starts = [](const std::string &x, const std::string &p) {
    return x.rfind(p, 0) == 0;
  };
  std::vector<InventoryRow> rows = {
      {"Sample bits c_A", 0, 8192, ""},
      {"s2", 0, 512, ""},
      {"s1 digits (range lowering)", 0, 1024, "s1 bound to them"},
      {"q - 1 - s1 digits (range lowering)", 0, 1024, ""},
      {"Quotient digits (range lowering)", 0, 1536,
       "the assert_mod's quotient bound to them"},
      {"s1 magnitude digits (range lowering)", 0, 1024, "mag1 bound to them"},
      {"mag2, low2", 0, 1024, ""},
      {"s1", 0, 0, "the shared magnitude form: a cell, no range of its own"},
      {"q / 2 - mag1 digits (range lowering)", 0, 0,
       "the shared magnitude form: mag1 below q / 2 + 1"},
      {"Norm digits (range lowering)", 0, 6, "norm bound to them"},
      {"Blind copy B_A", 0, 256, ""},
      {"Static histogram m0", 0, 2048, ""},
      {"Pads of s, l, m1", 0, 640,
       "the MAC's digits below 128 (n_high = 128) "
       "move m1 to the 128-row table's late histogram"},
      {"Budget digits (range lowering)", 0, 0,
       "128 J - sum (mag2 - low2) below 128 J + 1, two-sided"},
  };
  for (size_t id = 0; id < N.size(); ++id) {
    if (!is_cell(id)) continue;
    const std::string &nm = N[id].name;
    const size_t n = N[id].n;
    size_t k = SIZE_MAX;
    if (nm == "crossing.c_A") k = 0;
    else if (nm == "s2") k = 1;
    else if (starts(nm, "range.signature.s1.d")) k = 2;
    else if (starts(nm, "range.signature.s1.h")) k = 3;
    else if (starts(nm, "range.signature.equation.q.d")) k = 4;
    else if (starts(nm, "range.magnitudes.mag1.d")) k = 5;
    else if (nm == "magnitudes.mag2" || nm == "encoding.low2") k = 6;
    else if (starts(nm, "range.encoding.budget.")) k = 13;
    else if (starts(nm, "range.norm.bound.")) k = 9;
    else if (nm == "mac.blind") k = 10;
    else if (starts(nm, "range.static:")) k = 11;
    else if (nm == "signature.s1") k = 7;
    else if (starts(nm, "range.magnitudes.mag1.h")) k = 8;
    if (k == SIZE_MAX)
      rows.push_back({"(uncategorized) " + nm, n, 0, ""});
    else
      rows[k].now += n;
  }
  for (size_t x : compiled.messages())
    if (N[x].domain == A.index) rows[12].now += N[x].n;
  size_t listed = 0;
  for (const auto &r : rows) listed += r.now;
  const size_t all = compiled.coordinates(A.index);
  if (listed != all) rows.push_back({"(unaccounted)", all - listed, 0, ""});
  return rows;
}

inline std::string inventory_table(const std::vector<InventoryRow> &rows) {
  std::ostringstream o;
  size_t now = 0, spec = 0;
  o << "A phase-0 coordinates: compiled vs specified\n";
  char line[320];
  std::snprintf(line, sizeof(line), "  %-38s %7s %7s %7s  %s\n", "object",
                "compiled", "spec", "diff", "note");
  o << line;
  for (const auto &r : rows) {
    std::snprintf(line, sizeof(line), "  %-38s %7zu %7zu %+7lld  %s\n",
                  r.object.c_str(), r.now, r.spec,
                  (long long)r.now - (long long)r.spec, r.note.c_str());
    o << line;
    now += r.now;
    spec += r.spec;
  }
  std::snprintf(line, sizeof(line), "  %-38s %7zu %7zu %+7lld\n", "total",
                now, spec, (long long)now - (long long)spec);
  o << line;
  return o.str();
}

namespace compare {

// The integers of a bit matrix of field elements ([N][16]), least
// significant bit first.
template <class F>
std::vector<uint64_t> words_of_bits(const F &f,
                                    const Tensor<typename F::Elt> &bits) {
  std::vector<uint64_t> b;
  for (const auto &x : bits) b.push_back(ct::bit_of(f, x));
  return host::words_of_bits(Tensor<uint64_t>(b, bits.dims()));
}
// The output bytes of a bit vector (bit 8k + i is bit i of byte k).
template <class F>
std::vector<uint8_t> bytes_of_bits(const F &f,
                                   const std::vector<typename F::Elt> &bits) {
  std::vector<uint8_t> out(bits.size() / 8, 0);
  for (size_t i = 0; i < out.size() * 8; ++i)
    out[i / 8] |= uint8_t(ct::bit_of(f, bits[i]) << (i % 8));
  return out;
}
// Canonical integers of prime-field elements.
template <class F>
std::vector<uint64_t> integers(const F &f,
                               const std::vector<typename F::Elt> &x) {
  std::vector<uint64_t> out(x.size());
  for (size_t i = 0; i < x.size(); ++i) out[i] = uint64_t(nat_of(f, x[i]));
  return out;
}
// The MAC chunks of c (cref): the bits of c in sample
// order, least significant first, cut into chunks of w bits, each the
// polynomial-basis coefficients of a field element.
template <class MF>
std::vector<typename MF::Elt> mac_chunks(const MF &mf,
                                         const std::vector<uint64_t> &c) {
  std::vector<uint8_t> bits;
  for (uint64_t x : c)
    for (size_t b = 0; b < 16; ++b) bits.push_back(uint8_t((x >> b) & 1));
  bits.resize((bits.size() + MF::kBits - 1) / MF::kBits * MF::kBits, 0);
  std::vector<typename MF::Elt> out;
  for (size_t at = 0; at < bits.size(); at += MF::kBits) {
    uint8_t buf[MF::kBytes] = {};
    for (size_t i = 0; i < MF::kBits; ++i)
      buf[i / 8] |= uint8_t(bits[at + i] << (i % 8));
    out.push_back(mf.of_bytes_field(buf).value());
  }
  return out;
}

}  // namespace compare

}  // namespace proofs::gordiehowe::examples::falcon::emulated

#endif  // PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_EXAMPLES_FALCON_FALCON_EMULATED_TESTING_H_
