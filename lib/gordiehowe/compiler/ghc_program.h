// Copyright 2026 Chad Sharp and Paul Grubbs
// SPDX-License-Identifier: Apache-2.0

// The realized program's expression annotations and completeness certificates as GHC v3
// sections. The reader reconstructs their original Lean literal expressions.

#ifndef PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_COMPILER_GHC_PROGRAM_H_
#define PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_COMPILER_GHC_PROGRAM_H_

#include <algorithm>
#include <cstddef>
#include <cstdint>
#include <string>
#include <utility>
#include <vector>

#include "gordiehowe/compiler/assignment_reads.h"
#include "gordiehowe/compiler/ghc_gkr.h"
#include "gordiehowe/compiler/program_printer.h"

namespace proofs::gordiehowe::ghc {

inline void write_expr_ann(File &f, const ir::Certificates &c, size_t nfields) {
  using compiler::program_printer_internal::width_below;
  auto width = [&](const std::vector<uint64_t> &xs) {
    uint64_t top = 1;
    for (uint64_t x : xs) {
      if (x == UINT64_MAX) return size_t(64);
      top = std::max(top, x + 1);
    }
    return width_below(top);
  };
  const size_t mw = width(c.expr_max), fw = std::max<size_t>(1, nfields),
               lw = width(c.expr_len), dw = width(c.expr_deg);
  Bytes out;
  auto packed = [&](const std::vector<uint64_t> &xs, size_t w) {
    BitPack p;
    for (size_t i = 0; i < xs.size(); ++i) {
      if (w < 64 && (xs[i] >> w) != 0) throw Error("ExprAnn entry exceeds its width");
      p.put(i * w, xs[i]);
    }
    p.write(out);
  };
  auto mask = [&](const std::vector<bool> &xs) {
    BitPack p;
    for (size_t i = 0; i < xs.size(); ++i)
      if (xs[i]) p.put(i, 1);
    p.write(out);
  };
  packed(c.expr_max, mw);
  packed(c.expr_fields, fw);
  mask(c.expr_pub);
  packed(c.expr_len, lw);
  packed(c.expr_deg, dw);
  mask(c.expr_zero);
  out.nat(mw);
  out.nat(fw);
  out.nat(lw);
  out.nat(dw);
  // The computable Hints record reads exprAnn, so preserve its compiled
  // code as well as registering the file-backed reader for explicit checks.
  f.section("exprAnn", ty("GordieHowe.RealizedProgram.ExprAnn"), kCompile | kReader, out);
}

inline std::vector<uint8_t> expr_ann_file(const ir::Certificates &c, size_t nfields) {
  File f(gkr_schema());
  write_expr_ann(f, c, nfields);
  return f.bytes();
}

// Constructor tags follow RealizedProgram.Gen's declaration order. Keep this
// explicit rather than depending on the unrelated C++ enum's representation.
inline void write_gen(Bytes &out, const ir::Certificates::Gen &g) {
  using G = ir::Certificates::Gen;
  switch (g.kind) {
    case G::kNone: out.nat(0); break;
    case G::kSource: out.nat(1); break;
    case G::kLookupDigit:
      out.nat(2); out.nat(g.a); out.nat(g.second ? 1 : 0); out.nat(g.b); break;
    case G::kCommDigit:
      out.nat(3); out.nat(g.a); out.nat(g.b); out.nat(g.c); out.nat(g.d); break;
    case G::kSpec: out.nat(4); out.nat(g.a); break;
    case G::kStaticHist: out.nat(5); out.nat(g.a); out.nat(g.b); break;
    case G::kTag: out.nat(6); out.nat(g.a); break;
    case G::kAcc: out.nat(7); out.nat(g.a); break;
    case G::kQuotDigit: out.nat(8); out.nat(g.a); break;
    case G::kDigitsAcc: out.nat(9); out.nat(g.a); break;
    case G::kLowDigit: out.nat(10); out.nat(g.a); out.nat(g.b); break;
    case G::kLateHist: out.nat(11); out.nat(g.a); out.nat(g.b); break;
    case G::kSpecC: out.nat(12); out.nat(g.a); break;
    default: throw Error("unknown program generator");
  }
}

// Tags follow the Lean constructors, independently of the C++ enum order.
inline void write_cstep(Bytes &out, const ir::Certificates::CStep &s) {
  using S = ir::Certificates::CStep;
  switch (s.kind) {
    case S::kSource: out.ctor(2); break;
    case S::kQuotIn: out.ctor(3); out.nat(s.id); break;
    case S::kDigitRow: out.ctor(4); out.nat(s.id); break;
    case S::kMacRow: {
      out.ctor(5); out.nat(s.id); out.nat(s.slot);
      switch (s.role) {
        case S::kTail: out.ctor(0); break;
        case S::kH: out.ctor(1); break;
        case S::kAccRow: out.ctor(2); break;
        case S::kGroupRow: out.ctor(3); out.nat(s.group); break;
        case S::kResidues: out.ctor(4); break;
        case S::kGqLookup: out.ctor(5); break;
        case S::kQuotLookup: out.ctor(6); break;
        case S::kLowLookup: out.ctor(7); break;
        case S::kTopLookup: out.ctor(8); break;
        case S::kWrap: out.ctor(9); break;
        default: throw Error("unknown completeness MAC role");
      }
      break;
    }
    case S::kPadBool: out.ctor(6); break;
    case S::kCommIn: out.ctor(7); out.nat(s.id); out.nat(s.j); break;
    case S::kCommRow:
      out.ctor(8); out.nat(s.id); out.nat(s.lks.size());
      for (size_t id : s.lks) out.nat(id);
      break;
    case S::kHyp: out.ctor(9); out.nat(s.id); break;
    case S::kSpecProd: out.ctor(10); out.nat(s.id); break;
    case S::kSpecRow: out.ctor(11); out.nat(s.id); break;
    case S::kFieldRow: out.ctor(12); break;
    case S::kTwoTail: out.ctor(13); out.nat(s.id); out.nat(s.slot); break;
    case S::kSpecC: out.ctor(14); out.nat(s.id); break;
    default: throw Error("unknown completeness step");
  }
}

// Aligned derivations and ranks, using the same 32-bit packing as the printer.
inline void write_cderivs(File &f, const ir::Certificates &c) {
  Bytes out;
  out.nat(c.comp_derivs.size());
  for (const auto &steps : c.comp_derivs) {
    out.nat(steps.size());
    for (const auto &step : steps) write_cstep(out, step);
  }
  BitPack ranks;
  for (size_t i = 0; i < c.comp_ranks.size(); ++i) {
    if (c.comp_ranks[i] > UINT32_MAX) throw Error("completeness rank exceeds its width");
    ranks.put(i * 32, c.comp_ranks[i]);
  }
  ranks.write(out);
  f.section("cderivs", ty("GordieHowe.RealizedProgram.CDerivations"), kCompile | kReader, out);
}

// The computational Hints/CompletionInputs records still read these values.
// Compile the literal definitions and also register their file-backed readers.
inline std::vector<uint8_t> program_cert_file(const ir::Certificates &c,
                                             const ir::Program &program) {
  File f(gkr_schema());
  write_expr_ann(f, c, program.fields.size());
  Bytes gens;
  gens.nat(c.gens.size());
  for (const auto &g : c.gens) write_gen(gens, g);
  f.section("gens", ty("List GordieHowe.RealizedProgram.Gen"), kCompile | kReader, gens);
  write_cderivs(f, c);
  Bytes reads;
  const auto rows = compiler::assignment_reads(program);
  reads.nat(rows.size());
  for (const auto &row : rows) {
    reads.nat(row.size());
    for (size_t v : row) reads.nat(v);
  }
  f.section("assignmentReads", ty("List (List Nat)"), kCompile | kReader, reads);
  return f.bytes();
}

// The nodes containing one, in the program's field and insertion order.
inline std::vector<uint8_t> honest_nodes_file(
    const std::vector<std::pair<size_t, std::string>> &nodes) {
  Bytes out;
  out.nat(nodes.size());
  for (const auto &node : nodes) {
    out.nat(node.first);
    out.string(node.second);
  }
  File file(gkr_schema());
  file.section("nodes", ty("List (Prod Nat String)"), kCompile | kReader, out);
  return file.bytes();
}

}  // namespace proofs::gordiehowe::ghc

#endif  // PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_COMPILER_GHC_PROGRAM_H_
