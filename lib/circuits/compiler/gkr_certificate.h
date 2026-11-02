// Copyright 2026 Chad Sharp and Paul Grubbs
// SPDX-License-Identifier: Apache-2.0

// The translation-validation certificate of one compiled GKR circuit
// (formal/GordieHowe/ProofSystem/GKR/Certificate.lean): the compiler's nodes
// as push_node created them (the DAG: the inputs, which are the first nodes,
// and every node the circuit computes or asserts), its constant table, the
// scheduler's provenance of every layered wire (ScheduleCert) and the
// last-layer assertions the compiler turned into outputs. The compiler
// records it at every compilation (QuadCircuit::take_certificate); the plan
// export writes it into the circuit's GHC file (gordiehowe/compiler/
// ghc_gkr.h, gkr_core) and as text (text()).

#ifndef PRIVACY_PROOFS_ZK_LIB_CIRCUITS_COMPILER_GKR_CERTIFICATE_H_
#define PRIVACY_PROOFS_ZK_LIB_CIRCUITS_COMPILER_GKR_CERTIFICATE_H_

#include <stddef.h>
#include <stdint.h>

#include <algorithm>
#include <set>
#include <string>
#include <tuple>
#include <utility>
#include <vector>

#include "circuits/compiler/schedule.h"
#include "sumcheck/circuit.h"

namespace proofs {

template <class Field>
struct GkrCertificate {
  using Elt = typename Field::Elt;

  // The number of nodes, of inputs, and whether the inputs are the first
  // nodes (node i the input i).
  size_t nnodes = 0;
  size_t ninput = 0;
  bool inputs_first = true;
  std::vector<Elt> constants;
  // The nodes the circuit computes or asserts (needed, or with an assertion
  // term), in id order: id, depth, needed, and their terms' first index into
  // node_terms (node_term_begin has one more entry, the end).
  std::vector<uint32_t> node_id, node_depth, node_term_begin;
  std::vector<uint8_t> node_needed;
  // Per term: constant index, operands.
  std::vector<uint32_t> node_terms;
  // The circuit's own outputs (output_wire): node and output wire.
  std::vector<std::pair<uint32_t, uint32_t>> outputs;
  ScheduleCert wires;
  // The last-layer assertions the compiler turned into outputs
  // (fixup_last_layer_assertions): the last-layer wire carrying the
  // operand, and the assertion node, in node order.
  std::vector<std::pair<uint32_t, uint32_t>> last_asserts;

  // Empty when the certificate describes the circuit C, else why not: the
  // inputs are the first nodes, and at every depth the exported layer is
  // C's, per gate the same multiset of terms (the certificate lists a gate's
  // terms in its node's order, the quad in Morton order), and each
  // last-layer assertion's wire is a last-layer wire carrying its operand.
  std::string mismatch(const Circuit<Field>& c, const Field& f) const {
    if (!inputs_first) return "the inputs are not the first nodes";
    if (wires.depths() != c.nl + 1) return "the depth differs";
    using Row = std::tuple<uint32_t, uint32_t, uint32_t, std::string>;
    std::vector<uint8_t> buf(Field::kBytes);
    auto bytes = [&](const Elt& v) {
      f.to_bytes_field(buf.data(), v);
      return std::string(buf.begin(), buf.end());
    };
    for (size_t i = 0; i < c.nl; ++i) {
      const size_t d = c.nl - i;
      std::vector<Row> a, b;
      for (size_t g = 0; g < wires.width(d); ++g) {
        const size_t w = wires.first_wire[d] + g;
        for (size_t t = wires.term_begin[w]; t < wires.term_begin[w + 1]; ++t) {
          const uint32_t x = wires.terms[3 * t + 1], y = wires.terms[3 * t + 2];
          a.emplace_back(uint32_t(g), std::min(x, y), std::max(x, y),
                         bytes(constants.at(wires.terms[3 * t])));
        }
      }
      for (const auto& ec : *c.l[i].quad)
        b.emplace_back(uint32_t(ec.g), uint32_t(ec.h[0]), uint32_t(ec.h[1]),
                       bytes(ec.v));
      std::sort(a.begin(), a.end());
      std::sort(b.begin(), b.end());
      if (a != b) return "layer " + std::to_string(d) + " differs";
    }
    std::vector<uint32_t> pos(nnodes, UINT32_MAX);
    for (size_t i = 0; i < node_id.size(); ++i) pos.at(node_id[i]) = uint32_t(i);
    const size_t last = wires.depths() - 1;
    for (const auto& [g, z] : last_asserts) {
      if (z >= nnodes || pos[z] == UINT32_MAX) return "a last-layer assertion is no node";
      const size_t b = node_term_begin[pos[z]], e = node_term_begin[pos[z] + 1];
      if (e != b + 1 || node_terms[3 * b] != 0 || node_terms[3 * b + 1] != 0)
        return "a last-layer assertion is no assertion";
      if (g >= wires.width(last) ||
          wires.op[wires.first_wire[last] + g] != node_terms[3 * b + 2])
        return "a last-layer assertion's wire does not carry its operand";
    }
    // Each asserted node is the single term 0 * 1 * U.
    for (size_t n = 0; n < node_id.size(); ++n) {
      const size_t b = node_term_begin[n], e = node_term_begin[n + 1];
      bool asserts = false;
      for (size_t t = b; t < e; ++t) asserts = asserts || node_terms[3 * t] == 0;
      if (asserts && (e != b + 1 || node_terms[3 * b + 1] != 0))
        return "asserted node " + std::to_string(node_id[n]) + " is not one term 0 * 1 * U";
    }
    // Every last-layer wire carries an output, a last-layer assertion's
    // operand, or an asserted node.
    if (wires.depths() > 0) {
      std::vector<uint8_t> ok(wires.width(last), 0);
      for (const auto& [n, g] : outputs)
        if (g < ok.size()) ok[g] = 1;
      for (const auto& [g, z] : last_asserts)
        if (g < ok.size()) ok[g] = 1;
      for (size_t g = 0; g < ok.size(); ++g) {
        const uint32_t n = wires.op[wires.first_wire[last] + g];
        if (ok[g] || (n < nnodes && pos[n] != UINT32_MAX &&
                      node_term_begin[pos[n] + 1] == node_term_begin[pos[n]] + 1 &&
                      node_terms[3 * node_term_begin[pos[n]]] == 0))
          continue;
        return "last-layer wire " + std::to_string(g) +
               " carries no output, assertion operand or asserted node";
      }
    }
    return "";
  }

  // The certificate as text (a readable dump, compared across compiler
  // changes; the Lean data is the GHC file, emit_export.h):
  //   gkrcert 3 / bytes B / consts N then N hex lines (to_bytes_field, most
  //   significant byte first) / nodes TOTAL INPUTS KEPT then per kept node,
  //   in id order, "P id depth needed nterms ki op0 op1 ..." (the nodes
  //   below INPUTS are the inputs) / outputs N then "O node wire" / depths D
  //   then per depth "depth d nw" and per wire, in wire order,
  //   "W op copy nterms ki a b ...".
  // The field width of the DAG's and the schedule's chunks: the bit
  // length of the largest field any chunk holds (node ids, constant
  // indices, wire indices and term-count headers).
  size_t term_width() const {
    size_t m = std::max<size_t>(nnodes, constants.size());
    for (size_t d = 0; d < wires.depths(); ++d) m = std::max<size_t>(m, wires.width(d));
    for (size_t w = 0; w + 1 < wires.term_begin.size(); ++w)
      m = std::max<size_t>(m, 2 * (wires.term_begin[w + 1] - wires.term_begin[w]) + 1);
    for (size_t n = 0; n + 1 < node_term_begin.size(); ++n)
      m = std::max<size_t>(m, 2 * (node_term_begin[n + 1] - node_term_begin[n]) + 1);
    size_t w = 0;
    while (m >> w) ++w;
    return w;
  }

  // The asserted nodes: every kept node with an assertion term (k = 0),
  // the last-layer assertions included, in increasing id.
  std::vector<uint32_t> asserted() const {
    std::vector<uint32_t> out;
    for (size_t n = 0; n < node_id.size(); ++n)
      for (size_t t = node_term_begin[n]; t < node_term_begin[n + 1]; ++t)
        if (node_terms[3 * t] == 0) {
          out.push_back(node_id[n]);
          break;
        }
    return out;
  }

  std::string text(const Field& f) const {
    std::string o;
    auto num = [&o](size_t x) { o += std::to_string(x); };
    auto sp = [&o, &num](size_t x) {
      o += ' ';
      num(x);
    };
    o += "gkrcert 3\nbytes ";
    num(Field::kBytes);
    o += "\nconsts ";
    num(constants.size());
    o += "\n";
    std::vector<uint8_t> buf(Field::kBytes);
    static const char kHex[] = "0123456789abcdef";
    for (const Elt& k : constants) {
      f.to_bytes_field(buf.data(), k);
      for (size_t i = buf.size(); i-- > 0;) {
        o += kHex[buf[i] >> 4];
        o += kHex[buf[i] & 15];
      }
      o += "\n";
    }
    o += "nodes";
    sp(nnodes);
    sp(ninput);
    sp(node_id.size());
    o += "\n";
    for (size_t n = 0; n < node_id.size(); ++n) {
      o += "P";
      sp(node_id[n]);
      sp(node_depth[n]);
      sp(node_needed[n]);
      sp(node_term_begin[n + 1] - node_term_begin[n]);
      for (size_t t = node_term_begin[n]; t < node_term_begin[n + 1]; ++t) {
        sp(node_terms[3 * t]);
        sp(node_terms[3 * t + 1]);
        sp(node_terms[3 * t + 2]);
      }
      o += "\n";
    }
    o += "outputs";
    sp(outputs.size());
    o += "\n";
    for (const auto& [n, g] : outputs) {
      o += "O";
      sp(n);
      sp(g);
      o += "\n";
    }
    o += "depths";
    sp(wires.depths());
    o += "\n";
    for (size_t d = 0; d < wires.depths(); ++d) {
      o += "depth";
      sp(d);
      sp(wires.width(d));
      o += "\n";
      for (size_t w = wires.first_wire[d]; w < wires.first_wire[d + 1]; ++w) {
        o += "W";
        sp(wires.op[w]);
        sp(wires.copy[w]);
        sp(wires.term_begin[w + 1] - wires.term_begin[w]);
        for (size_t t = wires.term_begin[w]; t < wires.term_begin[w + 1]; ++t) {
          sp(wires.terms[3 * t]);
          sp(wires.terms[3 * t + 1]);
          sp(wires.terms[3 * t + 2]);
        }
        o += "\n";
      }
    }
    return o;
  }
};

}  // namespace proofs

#endif  // PRIVACY_PROOFS_ZK_LIB_CIRCUITS_COMPILER_GKR_CERTIFICATE_H_
