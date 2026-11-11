// Copyright 2026 Chad Sharp and Paul Grubbs
// SPDX-License-Identifier: Apache-2.0

// GordieHowe: the GKR export of a circuit's expression emission
// (compiler/emit_export.h), over Goldilocks^4 and GF(2^128).
//
//   GordieHoweEmitExport.Leb128        the GHC encoding's naturals (0,
//                                      127, 128, 2^64 - 1, 2^64, wide
//                                      field codes, high zero bytes),
//                                      zigzag integers, decimal codes and
//                                      the FNV-1a hash
//   GordieHoweEmitExport.RoundTrip     a circuit with an integer equality,
//                                      a shared product, a flattened chain,
//                                      a scaling and a sum: the GHC file
//                                      reads by its schema, and its data
//                                      is the certificate's DAG,
//                                      schedule and last-layer assertions
//                                      and to the table's entries and node
//                                      records and family records; the
//                                      Lean modules name it with its FNV-1a
//                                      hash; the mirrors accept it
//   GordieHoweEmitExport.MirrorRejects the mirrors refuse a mutated kind, a
//                                      scaling's code, a dropped and a
//                                      moved .ref, a wrong length, a kid
//                                      not below its node, a mutated wire,
//                                      aux wire, assertion pair and leaf
//                                      block, an atom operand marked uncut,
//                                      a wire on an uncut node, a LogUp
//                                      record's needle pointer moved, its
//                                      tree's spans not adjacent, its
//                                      weights block and its sum's wire
//                                      moved; and on a
//                                      hand-built DAG, the lazy difference
//                                      check accepts a cut whose operand is
//                                      cloned two levels deep and refuses a
//                                      wrong coefficient in that operand and
//                                      a cut leaving an input-only remainder
//   GordieHoweEmitExport.MacFamily     a MAC H half whose operand only the
//                                      circuit reads: its family record
//                                      decodes and checks; the mirror
//                                      refuses its powers and its tag
//                                      pointer moved and two chunks' wires
//                                      swapped; its packed bits' alignment
//                                      refuses its filler block moved
//   GordieHoweEmitExport.BooleanStepsChar2  derive<Bit> over GF(2^128): the
//                                      view check's steps ones - x and
//                                      x (ones - x) export and check
//   GordieHoweEmitExport.Walk          the walk numbers kids below their
//                                      node and flattened chain nodes
//                                      before their root, and gives a view
//                                      a new id when its wires differ; an
//                                      address reused with other contents,
//                                      and a node completed twice, are
//                                      recorded as problems
//   GordieHoweEmitExport.Plan          the check plan: a node's rebuild
//                                      follows its uncut cone, a node of
//                                      one-wire cuts that fits the leaf
//                                      budget is not sliced, small nodes
//                                      run together, a node or family whose
//                                      rebuild exceeds the budget is sliced
//                                      into the fewest slices under its
//                                      cap; an entry over the module
//                                      budget splits into contiguous leaf
//                                      ranges covering every leaf, under
//                                      budget it does not
//   GordieHoweEmitExport.WiringView    a circuit reading a view of two
//                                      sources with a zero coordinate
//                                      exports and checks
//   GordieHoweEmitExport.EmittedCircuit  a domain of two circuits has no
//                                      single emitted circuit

#include <algorithm>
#include <array>
#include <cstddef>
#include <cstdint>
#include <cstdio>
#include <functional>
#include <memory>
#include <set>
#include <stdexcept>
#include <string>
#include <utility>
#include <vector>

#include "algebra/fp14.h"
#include "algebra/fp14_n.h"
#include "algebra/fp_goldilocks4.h"
#include "algebra/reed_solomon_fp.h"
#include "circuits/compiler/compiler.h"
#include "gf2k/gf2_128.h"
#include "gf2k/gf2_256.h"
#include "gf2k/lch14_reed_solomon.h"
#include "gordiehowe/compiler/emit_export.h"
#include "gordiehowe/compiler/plan_export.h"
#include "gordiehowe/compiler/table_selections.h"
#include "gordiehowe/instances.h"
#include "gordiehowe/lib/table.h"
#include "gordiehowe/ops/spectral.h"
#include "gordiehowe/system.h"
#include "gtest/gtest.h"

namespace proofs::gordiehowe {
namespace {

using AF = Fp64G4;
using AElt = AF::Elt;
using RSA = BasicFpReedSolomon<AF>;
using HF = GF2_256<>;
using GF = GF2_128<>;
using NF = Fp14_9;
using RSG = LCH14ReedSolomonFactory<GF>;

// The field set of gordiehowe_mod_test (its instances, SETS mod).
using Sys = ConstraintSystem<SHA384, AF, HF, GF, NF>;
namespace ex = compiler::emit_export_internal;
using ENodeInfo = ex::ENodeInfo;
using ENode = ex::ENode;

struct Env {
  AF af;
  RSA rsa{af};
  GF gf;
  RSG rsg{gf};
  DomainProfile<AF, RSA::Factory, SHA384> a_profile() const {
    DomainProfile<AF, RSA::Factory, SHA384> p;
    p.f = &af;
    p.rsf = &rsa.factory();
    p.field_name = "Goldilocks^4";
    p.rate = 4;
    p.nreq = 64;
    const RSA *r = &rsa;
    p.block_enc = [r](const Circuit<AF> &, size_t nw, size_t nq) {
      return r->block_enc<SHA384>("gordiehowe", nw, nq, 4, 64);
    };
    return p;
  }
  DomainProfile<GF, RSG, SHA384> g_profile() const {
    DomainProfile<GF, RSG, SHA384> p;
    p.f = &gf;
    p.rsf = &rsg;
    p.field_name = "GF(2^128)";
    p.rate = 4;
    p.nreq = 64;
    return p;
  }
};
const Env &env() {
  static const Env *e = new Env;
  return *e;
}
const AF &af() { return env().af; }

CompileProfile table_profile() {
  CompileProfile c;
  c.name = "emit-export-1024";
  return c;
}

const compiler::ExportMeta kMeta{"emit-test", "wide", "c0ffee", "run-0", 0,
                                 0, "Test.EmitExport"};

// A system whose domain A's circuit holds an integer equality, a shared
// product read twice, a chain the emitter flattens, a scaling and a sum.
std::unique_ptr<Sys> system() {
  auto cs = std::make_unique<Sys>("gh-emit-export");
  auto &A = cs->domain(env().a_profile(), "A");
  auto a = A.priv(Subfield{}, "a", 4);
  auto b = A.priv(Subfield{}, "b", 4);
  auto c = A.priv(Subfield{}, "c", 4, depends_on(a, b),
                  [](const AElt &x, const AElt &y) { return af().mulf(x, y); });
  assert_range(a, 1024, "a");
  assert_range(b, 1024, "b");
  assert_range(c, Bound(1) << 20, "c");
  assert_int_equal(a * b, c, "product").pin(Placement::kCircuit);
  // AB is held by a C++ variable: shared, never flattened.
  const auto ab = a * b;
  A.assert_zero("chain", ab * ab * a * b - c * c).pin(Placement::kCircuit);
  A.assert_zero("total", (ab * 3 + a).sum() - c.sum()).pin(Placement::kCircuit);
  return cs;
}

// A system whose domain G's circuit holds a MAC H half: the operand d,
// an unchecked bit only the circuit reads (an expression), equals its bits
// copied into A (assert_same_bits); 256 bits, two chunks of 128.
std::unique_ptr<Sys> mac_system() {
  auto cs = std::make_unique<Sys>("gh-emit-mac");
  auto &G = cs->domain(env().g_profile(), "G");
  auto &A = cs->domain(env().a_profile(), "A");
  auto a = G.priv(Bit{}, "a", 256);
  auto b = G.priv(Bit{}, "b", 256);
  auto d = G.bit_from_unchecked("d", a * b);
  const GF *pg = &env().gf;
  const AF *pa = &af();
  auto da = A.priv(Bit{}, "d_a", 256, depends_on(a, b),
                   [pa, pg](const std::vector<GF::Elt> &x, const std::vector<GF::Elt> &y) {
                     std::vector<AElt> out;
                     for (size_t i = 0; i < x.size(); ++i)
                       out.push_back(ct::bit_elt(*pa, ct::bit_of(*pg, x[i]) &
                                                           ct::bit_of(*pg, y[i])));
                     return out;
                   });
  assert_same_bits(d, da);
  return cs;
}

std::vector<compiler::EmitExport> tables(const Sys::Compiled &c,
                                         const compiler::EmitOptions &o = {}) {
  return compiler::emit_tables(c, kMeta, o);
}

// ------------------------------- the certificate's records, read (test) --

struct Reader {
  const std::vector<uint8_t> &b;
  size_t at = 0, end = 0;
  bool ok = true;
  uint64_t nat() {
    uint64_t x = 0;
    for (unsigned s = 0;; s += 7) {
      if (at >= end || s > 63) {
        ok = false;
        return 0;
      }
      const uint8_t c = b[at++];
      x |= uint64_t(c & 0x7f) << s;
      if (!(c & 0x80)) return x;
    }
  }
  // A natural of any size (skipped).
  void big() {
    while (at < end && (b[at] & 0x80)) ++at;
    if (at >= end) ok = false;
    ++at;
  }
};

// The certificate's parts as the reader decodes them.
struct Decoded {
  uint64_t c = 0, w = 0, ninputs = 0, nnodes = 0, table = 0, nentries = 0;
  bool char2 = false;
  size_t nconsts = 0;
  std::vector<std::pair<uint64_t, std::vector<uint64_t>>> dag;  // id, terms
  std::vector<uint64_t> asserts, outputs;
  std::vector<std::vector<std::pair<uint64_t, std::vector<uint64_t>>>> sched;
  std::vector<std::pair<uint64_t, uint64_t>> last_asserts;
  std::vector<uint64_t> out_wires;
  struct Entry {
    uint64_t k = 0, lo = 0, hi = 0, root = 0;
    bool has_root = false;
    std::vector<std::pair<uint64_t, uint64_t>> zu;
    // The family record: -1 none, else its constructor (0 alignment,
    // 1 logup, 2 macH); its pointers, and its wires' nodes (leaf
    // denominators, inner nodes' (l, r, num, den), the sum, the chunks).
    int fam = -1;
    uint64_t block = 0, alpha = 0, bits = 0, powers = 0, tag = 0, sum = 0;
    std::vector<uint64_t> needles, hists, dens, chunks;
    std::vector<std::array<uint64_t, 4>> inner;
    std::vector<uint64_t> kinds, lens, wires, aux;
  };
  std::vector<Entry> entries;
};

void skip_named(Reader &r) {
  const uint64_t k = r.nat();
  auto form = [&]() {
    if (r.nat() != 0) r.big();
  };
  switch (k) {
    case 0: r.nat(); form(); break;
    case 1: r.nat(); r.nat(); r.nat(); form(); break;
    case 2: r.nat(); r.nat(); form(); break;
    case 3: r.nat(); r.big(); r.nat(); break;
    case 4: case 5: r.nat(); r.big(); break;
    case 6: r.nat(); r.nat(); r.nat(); break;
    case 7: {
      r.nat(); r.nat(); r.nat();
      const uint64_t n = r.nat();
      for (uint64_t i = 0; i < n; ++i) r.nat();
      break;
    }
    case 8: r.nat(); r.nat(); break;
    case 9: case 10: case 11: case 12: r.nat(); break;
    case 13: r.nat(); r.big(); break;
    case 14: r.nat(); skip_named(r); break;
    default: r.ok = false;
  }
}
void skip_eop(Reader &r) {
  switch (r.nat()) {
    case 0:
      r.nat();
      if (r.nat()) r.nat();
      break;
    case 1:
      skip_named(r);
      break;
    case 2: {
      const uint64_t rows = r.nat();
      for (uint64_t i = 0; i < rows; ++i) {
        const uint64_t n = r.nat();
        for (uint64_t j = 0; j < n; ++j) {
          r.nat();
          if (r.nat() == 0) {
            r.big();
          } else {
            r.nat();
            r.nat();
          }
        }
      }
      break;
    }
    case 3:
      skip_named(r);
      r.nat();
      break;
    default:
      r.ok = false;
  }
}
// A node record: its kind, length, wire and aux counts.
void read_node(Reader &r, Decoded::Entry &e) {
  const uint64_t kind = r.nat();
  switch (kind) {
    case 0: {
      const uint64_t n = r.nat();
      for (uint64_t i = 0; i < n; ++i) {
        r.big();
        r.nat();
        const uint64_t ops = r.nat();
        for (uint64_t j = 0; j < ops; ++j) skip_eop(r);
      }
      r.nat();
      break;
    }
    case 1: r.nat(); break;
    case 2: r.nat(); r.nat(); r.nat(); break;
    case 3: r.big(); r.nat(); break;
    case 4: case 5: case 6: case 7: r.nat(); r.nat(); break;
    case 8: r.nat(); r.nat(); r.nat(); r.nat(); break;
    case 9:
      r.nat(); r.nat(); r.nat();
      if (r.nat()) {
        r.nat();
        r.nat();
      } else {
        r.nat();
      }
      break;
    case 10: r.nat(); r.nat(); r.nat(); break;
    case 11: r.nat(); break;
    case 12: {
      r.nat();
      const uint64_t n = r.nat();
      for (uint64_t i = 0; i < n; ++i) r.nat();
      break;
    }
    case 13: skip_eop(r); r.nat(); break;
    case 14: {
      r.nat();
      const uint64_t p = r.nat();
      r.nat();
      if (p == 1) r.nat();
      break;
    }
    default: r.ok = false;  // 15, the retired raw leaf, among them
  }
  e.kinds.push_back(kind);
  e.lens.push_back(r.nat());
  r.nat();  // cut
  if (r.nat()) r.nat();  // ref
  const uint64_t nw = r.nat();
  for (uint64_t i = 0; i < nw; ++i) {
    r.big();
    r.big();
    r.nat();
  }
  const uint64_t na = r.nat();
  for (uint64_t i = 0; i < na; ++i) {
    r.big();
    r.big();
    r.nat();
  }
  e.wires.push_back(nw);
  e.aux.push_back(na);
}

// A wire 0 + 1 n of a family record: its node (a coefficient other than
// 0, 1 fails the read).
uint64_t read_node_wire(Reader &r) {
  if (r.nat() != 0 || r.nat() != 1) r.ok = false;
  return r.nat();
}
void read_fam(Reader &r, Decoded::Entry &e) {
  if (r.nat() == 0) return;
  e.fam = int(r.nat());
  auto nats = [&](std::vector<uint64_t> &v) {
    for (uint64_t i = 0, n = r.nat(); i < n && r.ok; ++i) v.push_back(r.nat());
  };
  switch (e.fam) {
    case 0:
      e.block = r.nat();
      break;
    case 1: {
      e.alpha = r.nat();
      nats(e.needles);
      nats(e.hists);
      e.block = r.nat();
      for (uint64_t i = 0, n = r.nat(); i < n && r.ok; ++i) e.dens.push_back(read_node_wire(r));
      for (uint64_t i = 0, n = r.nat(); i < n && r.ok; ++i) {
        const uint64_t l = r.nat(), rr = r.nat();
        const uint64_t num = read_node_wire(r), den = read_node_wire(r);
        e.inner.push_back({l, rr, num, den});
      }
      e.sum = read_node_wire(r);
      break;
    }
    case 2:
      e.bits = r.nat();
      e.powers = r.nat();
      e.tag = r.nat();
      for (uint64_t i = 0, n = r.nat(); i < n && r.ok; ++i) e.chunks.push_back(read_node_wire(r));
      break;
    default:
      r.ok = false;
  }
}

// The certificate's data as the export wrote it (EmitExport's core and
// table), each entry and node record read back from its bytes, after the
// file's sections are read and checked against the schema (ghc::read).
Decoded decode(const compiler::EmitExport &x) {
  Decoded d;
  std::vector<ghc::Section> secs;
  try {
    secs = ghc::read(x.ghc, ghc::gkr_schema());
  } catch (const ghc::Error &e) {
    ADD_FAILURE() << "the GHC file does not read: " << e.what();
    return d;
  }
  // consts first, the circuit's certificate last, in spine form.
  EXPECT_GE(secs.size(), 9u);
  if (secs.size() >= 9) {
    EXPECT_EQ(secs.front().name, "cert.consts");
    EXPECT_EQ(secs.back().name, "cert");
    EXPECT_EQ(secs.back().type.text(), "GordieHowe.RealizedProgram.CircuitData");
    EXPECT_EQ(secs.back().flags, ghc::kSpine | ghc::kReader);
  }
  const ghc::GkrCore &k = x.core;
  d.c = k.c;
  d.w = k.w;
  d.char2 = k.char2;
  d.ninputs = k.ninputs;
  d.nnodes = k.nnodes;
  d.table = x.table.size;
  d.nentries = x.table.entries.size();
  d.nconsts = k.consts.size();
  for (const auto &[id, ts] : k.dag) {
    std::vector<uint64_t> t;
    for (const auto &x3 : ts) t.insert(t.end(), x3.begin(), x3.end());
    d.dag.push_back({id, t});
  }
  d.asserts = k.asserts;
  d.outputs = k.outputs;
  for (const auto &ws : k.layers) {
    std::vector<std::pair<uint64_t, std::vector<uint64_t>>> v;
    for (const auto &g : ws) {
      std::vector<uint64_t> t;
      for (const auto &x3 : g.terms) t.insert(t.end(), x3.begin(), x3.end());
      v.push_back({g.node, t});
    }
    d.sched.push_back(v);
  }
  d.last_asserts = k.last_asserts;
  d.out_wires = k.out_wires;
  for (const ghc::Bytes &eb : x.table.entries) {
    Reader r{eb.out, 0, eb.out.size()};
    Decoded::Entry e;
    e.k = r.nat();
    e.lo = r.nat();
    e.hi = r.nat();
    e.has_root = r.nat() == 1;
    if (e.has_root) e.root = r.nat();
    for (uint64_t i = 0, n = r.nat(); i < n; ++i) {
      const uint64_t z = r.nat(), u = r.nat();
      e.zu.push_back({z, u});
    }
    read_fam(r, e);
    EXPECT_TRUE(r.ok) << "entry " << e.k;
    EXPECT_EQ(r.at, r.end) << "entry " << e.k << " not read to its end";
    for (uint64_t n = e.lo; n < e.hi && n < x.table.nodes.size(); ++n) {
      const auto &nb = x.table.nodes[n].out;
      Reader rn{nb, 0, nb.size()};
      read_node(rn, e);
      EXPECT_TRUE(rn.ok) << "node " << n;
      EXPECT_EQ(rn.at, rn.end) << "node " << n << " not read to its end";
    }
    d.entries.push_back(std::move(e));
  }
  return d;
}

TEST(GordieHoweEmitExport, Leb128) {
  auto enc = [](auto f) {
    ghc::Bytes o;
    f(o);
    return o.out;
  };
  using B = std::vector<uint8_t>;
  EXPECT_EQ(enc([](ghc::Bytes &o) { o.nat(0); }), (B{0x00}));
  EXPECT_EQ(enc([](ghc::Bytes &o) { o.nat(127); }), (B{0x7f}));
  EXPECT_EQ(enc([](ghc::Bytes &o) { o.nat(128); }), (B{0x80, 0x01}));
  EXPECT_EQ(enc([](ghc::Bytes &o) { o.nat(300); }), (B{0xac, 0x02}));
  EXPECT_EQ(enc([](ghc::Bytes &o) { o.nat(~uint64_t(0)); }),
            (B{0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0x01}));
  // Little-endian bytes: zero, high zero bytes dropped, 2^64, 2^127.
  EXPECT_EQ(enc([](ghc::Bytes &o) {
              const uint8_t z[4] = {0, 0, 0, 0};
              o.nat_le(z, 4);
            }),
            (B{0x00}));
  EXPECT_EQ(enc([](ghc::Bytes &o) {
              const uint8_t z[4] = {0x80, 0x00, 0, 0};
              o.nat_le(z, 4);
            }),
            (B{0x80, 0x01}));
  EXPECT_EQ(enc([](ghc::Bytes &o) {
              const uint8_t z[9] = {0, 0, 0, 0, 0, 0, 0, 0, 1};
              o.nat_le(z, 9);
            }),
            (B{0x80, 0x80, 0x80, 0x80, 0x80, 0x80, 0x80, 0x80, 0x80, 0x02}));
  {
    uint8_t z[16] = {};
    z[15] = 0x80;
    const B b = enc([&](ghc::Bytes &o) { o.nat_le(z, 16); });
    // 2^127: 19 groups, the last holding bit 127 at its position 1.
    ASSERT_EQ(b.size(), 19u);
    for (size_t i = 0; i + 1 < b.size(); ++i) EXPECT_EQ(b[i], 0x80);
    EXPECT_EQ(b.back(), 0x02);
  }
  // A 64-bit natural through both encoders.
  {
    const uint64_t x = 0x0123456789abcdefull;
    uint8_t le[8];
    for (int i = 0; i < 8; ++i) le[i] = uint8_t(x >> (8 * i));
    EXPECT_EQ(enc([&](ghc::Bytes &o) { o.nat(x); }),
              enc([&](ghc::Bytes &o) { o.nat_le(le, 8); }));
  }
  // Zigzag.
  EXPECT_EQ(enc([](ghc::Bytes &o) { o.integer(0); }), (B{0x00}));
  EXPECT_EQ(enc([](ghc::Bytes &o) { o.integer(-1); }), (B{0x01}));
  EXPECT_EQ(enc([](ghc::Bytes &o) { o.integer(1); }), (B{0x02}));
  EXPECT_EQ(enc([](ghc::Bytes &o) { o.integer(-64); }), (B{0x7f}));
  EXPECT_EQ(enc([](ghc::Bytes &o) { o.integer(64); }), (B{0x80, 0x01}));
  // A decimal code.
  EXPECT_EQ(enc([](ghc::Bytes &o) { ex::dec_nat(o, "0"); }), (B{0x00}));
  EXPECT_EQ(enc([](ghc::Bytes &o) { ex::dec_nat(o, "18446744073709551616"); }),
            (B{0x80, 0x80, 0x80, 0x80, 0x80, 0x80, 0x80, 0x80, 0x80, 0x02}));
  // FNV-1a 64 of "" and "a".
  EXPECT_EQ(ghc::fnv1a({}), 0xcbf29ce484222325ull);
  EXPECT_EQ(ghc::fnv1a({'a'}), 0xaf63dc4c8601ec8cull);
}

TEST(GordieHoweEmitExport, Plan) {
  using PN = ex::PlanNode;
  // Blocks of COUNT cuts, each one wire (FREE) or reading LEAVES wires and
  // SCALES scales.
  auto cuts = [](size_t count, bool free, size_t leaves, size_t scales) {
    std::vector<ex::CutBlock> v;
    for (size_t left = count; left > 0;) {
      const size_t b = std::min(left, ex::kCutBlock);
      v.push_back({b, free ? b : 0, free ? 0 : b * leaves, free ? 0 : b * scales});
      left -= b;
    }
    return v;
  };
  // 0: a value leaf of length 4; 1, 2: uncut nodes of length 4 over it; 3: a
  // cut node of length 4 over both, two wires per cut, its rebuild its own
  // coordinates and its cone's and their kids' reads; 4: a value leaf of
  // 94,208 one-wire cuts; 5: a lin node of 4,096 cuts through an operator
  // over 4, each 23 wires and 22 scales; 6: a gather of 117,760 one-wire
  // cuts over 4.
  std::vector<PN> info(7);
  info[0] = {4, true, 0, PN::kPlace, {}, cuts(4, true, 0, 0)};
  info[1] = {4, false, 0, PN::kOwn, {0}, {}};
  info[2] = {4, false, 0, PN::kOwn, {0}, {}};
  info[3] = {4, true, 0, PN::kOwn, {1, 2}, cuts(4, false, 2, 0)};
  info[4] = {94208, true, 0, PN::kPlace, {}, cuts(94208, true, 0, 0)};
  info[5] = {4096, true, 0, PN::kOperator, {4}, cuts(4096, false, 23, 22)};
  info[6] = {117760, true, 0, PN::kIndex, {4}, cuts(117760, true, 0, 0)};
  const auto o = ex::plan_node_objects(info);
  ASSERT_EQ(o.size(), 7u);
  EXPECT_EQ(o[1].cuts(), 0u);
  EXPECT_NEAR(o[3].F, ex::kOwnMs * (4 + 8 + 2 * 8), 1e-9);
  EXPECT_EQ(o[3].cuts(), 4u);
  EXPECT_NEAR(o[3].total(), 4 * (ex::kCutMs + 2 * ex::kTermMs), 1e-9);
  EXPECT_NEAR(o[5].F, ex::kOwnMs * 4096 + (ex::kOperatorMs + ex::kRampMs) * 94208, 1e-6);
  // the value leaf fits one leaf; the lin node and the gather do not
  const auto whole = ex::plan_slices(o[4]);
  EXPECT_EQ(whole.m, 1u);
  EXPECT_LE(whole.leaves[0], ex::kLeafBudgetMs);
  const auto lin = ex::plan_slices(o[5]);
  const auto gather = ex::plan_slices(o[6]);
  for (const auto *sp : {&lin, &gather}) {
    EXPECT_GT(sp->m, 1u);
    EXPECT_EQ(sp->leaves.size(), sp->m);
    EXPECT_LE((sp->m - 1) * sp->S, sp == &lin ? 4096u : 117760u);
    EXPECT_GT(sp->m * sp->S, sp == &lin ? 4095u : 117759u);
  }
  // the lin node's rebuild alone exceeds the budget: its leaves stay under
  // twice it, and one slice fewer would not
  for (double x : lin.leaves) EXPECT_LE(x, 2 * ex::kLeafBudgetMs);
  {
    const size_t S = (4096 + lin.m - 2) / (lin.m - 1);
    double worst = 0;
    for (double x : ex::slice_costs(o[5], S)) worst = std::max(worst, x);
    EXPECT_GT(worst, 2 * ex::kLeafBudgetMs);
  }
  // the gather's drop to its end exceeds the budget: a few slices of
  // thousands of cuts, not one per thousand cuts
  EXPECT_LE(gather.m, 16u);
  EXPECT_GE(gather.S, 4096u);
  // A LogUp family of 600 two-wire cuts, under the budget: one slice.
  const auto fam = ex::plan_family_object(ex::kLogupBuildMs * 600, {}, 600, 2 * ex::kTermMs);
  const std::vector<ex::PlanObject> entry(o.begin(), o.begin() + 5);
  const auto e = ex::plan_entry(entry, fam);
  // nodes 0 to 4 run together, then the family
  EXPECT_EQ(e.parts, (std::vector<size_t>{0, 0, 5, 2, 600, 1}));
  ASSERT_EQ(e.leaves.size(), 3u);
  EXPECT_EQ(e.leaves[0], size_t(ex::kHeadMs));
  EXPECT_TRUE(e.modules.empty());
  // A MAC H family of 920 chunks of 128 bits: sliced under its cap.
  const auto mac = ex::plan_family_object(ex::kMacBuildMs * 117760, cuts(920, false, 128, 127),
                                          0, 0);
  const auto ms = ex::plan_slices(mac);
  EXPECT_GT(ms.m, 1u);
  for (double x : ms.leaves) EXPECT_LE(x, 2 * ex::kLeafBudgetMs);
  // An entry with the lin node: a budget below the cost gives contiguous
  // ranges covering every leaf, at most ceil(cost / budget) of them, none
  // empty.
  const std::vector<ex::PlanObject> big(o.begin(), o.begin() + 6);
  for (double budget : {300000.0, 600000.0, 1200000.0}) {
    const auto s = ex::plan_entry(big, fam, budget);
    ASSERT_GE(s.modules.size(), 2u) << budget;
    EXPECT_LE(s.modules.size(), (s.cost + size_t(budget) - 1) / size_t(budget));
    size_t at = 0;
    for (const auto &[lo, hi] : s.modules) {
      EXPECT_EQ(lo, at);
      EXPECT_LT(lo, hi);
      at = hi;
    }
    EXPECT_EQ(at, s.leaves.size());
  }
  EXPECT_EQ(ex::plan_text({0, 0, 4, 2, 256, 1}), "[0, 0, 4, 2, 256, 1]");
  // A node of 8,192 cuts that are not one wire, cheap enough for one leaf
  // by its price, is checked in slices of at most kMaxSliceHard cuts; the
  // gather's one-wire cuts (node 6) are not limited. A LogUp family's cut
  // pays its base, and 106,752 of them are checked in slices under the cap.
  std::vector<PN> ap(2);
  ap[0] = {1024, true, 0, PN::kPlace, {}, cuts(1024, true, 0, 0)};
  ap[1] = {1024, true, 7168, PN::kOwn, {0}, cuts(8192, false, 1, 0)};
  const auto ao = ex::plan_node_objects(ap);
  EXPECT_EQ(ao[1].hard, 8192u);
  EXPECT_LE(ex::kLeafMs + ao[1].F + ao[1].total(), ex::kLeafBudgetMs);
  const auto as = ex::plan_slices(ao[1]);
  EXPECT_EQ(as.m, 8u);
  EXPECT_EQ(as.S, ex::kMaxSliceHard);
  EXPECT_EQ(o[6].hard, 0u);
  const auto lf = ex::plan_family_object(ex::kLogupBuildMs * 106752, {}, 106752, 2 * ex::kTermMs,
                                         ex::kLogupCutMs);
  EXPECT_NEAR(lf.total(), 106752 * (2 * ex::kTermMs + ex::kLogupCutMs), 1e-3);
  const auto ls = ex::plan_slices(lf);
  EXPECT_GT(ls.m, 9u);
  for (double x : ls.leaves) EXPECT_LE(x, 2 * ex::kLeafBudgetMs + 0.25 * ex::kLeafBudgetMs);
}

TEST(GordieHoweEmitExport, HeaderPlan) {
  // Leaves in Load.lean's order: six header parts; a layer of 100,000 gates in 49 slices (each its
  // check and counts, all but the last its next tail's equation); a layer of 60,000 gates in 30
  // slices after its previous layer's length; a small layer's check and counts; the last suffix
  // and the shape; 49 slices of asserted nodes twice; part 6 and four small checks.
  const auto h = ex::plan_header({100000, 60000, 1000}, 25000, 2743);
  EXPECT_EQ(h.leaves.size(), 6u + (49 * 3 - 1) + (1 + 30 * 3 - 1) + 2 + 2 + 2 * 49 + 1 + 4);
  size_t sum = 0;
  for (size_t x : h.leaves) sum += x;
  EXPECT_EQ(h.cost, sum);
  // Part modules under the module budget, contiguous and covering every leaf.
  ASSERT_GT(h.modules.size(), 1u);
  EXPECT_EQ(h.modules.front().first, 0u);
  EXPECT_EQ(h.modules.back().second, h.leaves.size());
  for (size_t j = 1; j < h.modules.size(); ++j)
    EXPECT_EQ(h.modules[j].first, h.modules[j - 1].second);
  // A small circuit's header is one module.
  EXPECT_TRUE(ex::plan_header({10, 5}, 3, 20).modules.empty());
}

TEST(GordieHoweEmitExport, RoundTrip) {
  auto cs = system();
  auto c = compile(*cs, table_profile());
  const auto out = tables(*c);
  ASSERT_EQ(out.size(), 1u);
  const auto &x = out[0];
  EXPECT_EQ(x.domain, "A");
  EXPECT_GT(x.cuts, 0u);
  // The Lean modules: the data module, one per entry, the header's, the circuit's.
  ASSERT_EQ(x.modules.size(), 1u);
  ASSERT_EQ(x.check_modules.size(), x.entries + 2);
  const std::string &t = x.modules[0].second;
  EXPECT_EQ(x.modules[0].first, "GKR/A.lean");
  char hash[17];
  std::snprintf(hash, sizeof(hash), "%016llx",
                static_cast<unsigned long long>(ghc::fnv1a(x.ghc)));
  for (const std::string &want :
       {std::string("namespace GordieHowe.Generated.Test.EmitExport.GKR.A"),
        std::string("public import GordieHoweCerts.Generated.Test.EmitExport.Program"),
        std::string("public import GordieHowe.Language.Realizations.Circuit.RelEntry"),
        std::string("def ar : CodeArith := (RealizedProgram.gold4Code.arith).withPrime "
                    "18446744069414584321"),
        "load_ghc \"A.ghc\" \"" + std::string(hash) + "\""})
    EXPECT_NE(t.find(want), std::string::npos) << want << "\n" << t;
  const std::string root = "Check/Kernel/GordieHoweCheck/Test/EmitExport/GKR/A/";
  const auto &entry = x.check_modules.front();
  EXPECT_EQ(entry.first, root + "E0.lean");
  EXPECT_NE(entry.second.find("check_entry cert ar 0 ["), std::string::npos);
  EXPECT_NE(entry.second.find("\nmeta import GordieHoweCerts.Generated.Test.EmitExport.GKR.A\n"),
            std::string::npos);
  // The header imports no entry; the circuit's module composes the header's and the entries'.
  const auto &header = x.check_modules[x.check_modules.size() - 2];
  EXPECT_EQ(header.first, root + "Header.lean");
  EXPECT_NE(header.second.find("check_header_leaves cert ar 0 "), std::string::npos);
  EXPECT_NE(header.second.find("compose_header cert ar\n"), std::string::npos);
  EXPECT_EQ(header.second.find("GKR.A.E0"), std::string::npos);
  const auto &circuit = x.check_modules.back();
  EXPECT_EQ(circuit.first, root + "Circuit.lean");
  EXPECT_NE(circuit.second.find("compose_circuit cert ar\n"), std::string::npos);
  EXPECT_NE(circuit.second.find("public import GordieHoweCheck.Test.EmitExport.GKR.A.E0"),
            std::string::npos);
  EXPECT_NE(circuit.second.find("public import GordieHoweCheck.Test.EmitExport.GKR.A.Header\n"),
            std::string::npos);
  for (const auto &[path, source] : x.check_modules) {
    EXPECT_EQ(path.find("Check/Kernel/"), 0u);
    EXPECT_EQ(source.find(" native\n"), std::string::npos);
    EXPECT_EQ(source.find("CertCheck"), std::string::npos);
  }
  // The GHC file reads by its schema, and holds the certificate and the table.
  const Decoded d = decode(x);
  const auto &C = *static_cast<const GkrCertificate<AF> *>(
      c->compiled_domain(0).gkr_cert_data());
  EXPECT_EQ(d.ninputs, C.ninput);
  EXPECT_EQ(d.nnodes, C.nnodes);
  EXPECT_EQ(d.w, C.term_width());
  EXPECT_EQ(d.nconsts, C.constants.size());
  EXPECT_FALSE(d.char2);
  ASSERT_EQ(d.dag.size(), C.node_id.size());
  for (size_t n = 0; n < d.dag.size(); ++n) {
    EXPECT_EQ(d.dag[n].first, C.node_id[n]);
    EXPECT_EQ(d.dag[n].second,
              (std::vector<uint64_t>(C.node_terms.begin() + 3 * C.node_term_begin[n],
                                     C.node_terms.begin() + 3 * C.node_term_begin[n + 1])));
  }
  std::vector<uint64_t> as;
  for (uint32_t z : C.asserted()) as.push_back(z);
  EXPECT_EQ(d.asserts, as);
  ASSERT_EQ(d.sched.size() + 1, C.wires.depths());
  for (size_t i = 0; i < d.sched.size(); ++i) {
    const size_t dep = i + 1;
    ASSERT_EQ(d.sched[i].size(), C.wires.width(dep));
    for (size_t g = 0; g < d.sched[i].size(); ++g) {
      const size_t w = C.wires.first_wire[dep] + g;
      EXPECT_EQ(d.sched[i][g].first, C.wires.op[w]);
      EXPECT_EQ(d.sched[i][g].second,
                (std::vector<uint64_t>(C.wires.terms.begin() + 3 * C.wires.term_begin[w],
                                       C.wires.terms.begin() + 3 * C.wires.term_begin[w + 1])));
    }
  }
  ASSERT_EQ(d.last_asserts.size(), C.last_asserts.size());
  for (size_t i = 0; i < d.last_asserts.size(); ++i) {
    EXPECT_EQ(d.last_asserts[i].first, C.last_asserts[i].first);
    EXPECT_EQ(d.last_asserts[i].second, C.last_asserts[i].second);
  }
  EXPECT_EQ(d.out_wires.size(), d.outputs.size());
  // The entries: one per printed entry, partitioning the table; each
  // asserted node is one of the DAG's.
  ASSERT_EQ(d.nentries, x.entries);
  ASSERT_EQ(d.entries.size(), x.entries);
  EXPECT_EQ(d.table, x.nodes);
  uint64_t at = 0, wires = 0, aux = 0;
  size_t rooted = 0;
  for (size_t k = 0; k < d.entries.size(); ++k) {
    const auto &e = d.entries[k];
    EXPECT_EQ(e.k, k);
    EXPECT_EQ(e.lo, at);
    at = e.hi;
    for (size_t i = 0; i < e.kinds.size(); ++i) {
      wires += e.wires[i];
      aux += e.aux[i];
    }
    if (!e.has_root) continue;
    ++rooted;
    for (const auto &[z, u] : e.zu) {
      if (z == 0) {
        EXPECT_EQ(u, 0u);
        continue;
      }
      EXPECT_TRUE(std::binary_search(d.asserts.begin(), d.asserts.end(), z)) << z;
    }
  }
  EXPECT_EQ(at, d.table);
  EXPECT_EQ(wires, x.wires);
  EXPECT_EQ(aux, x.aux);
  // The three placed predicates (the two assert_zero, the integer
  // equality) have roots; the chain's products have aux wires.
  EXPECT_GE(rooted, 3u);
  EXPECT_GT(aux, 0u);
  // The family records decode to the table's.
  using T = ex::EmitTable<AF>;
  using Fam = T::Fam;
  T tab;
  {
    compiler::EmitOptions o;
    o.mutate = [&](void *tp, const std::string &) { tab = *static_cast<T *>(tp); };
    tables(*c, o);
  }
  ASSERT_EQ(tab.blocks.size(), d.entries.size());
  auto u64 = [](const std::vector<size_t> &v) {
    return std::vector<uint64_t>(v.begin(), v.end());
  };
  size_t logups = 0;
  for (size_t k = 0; k < d.entries.size(); ++k) {
    const auto &b = tab.blocks[k];
    const auto &e = d.entries[k];
    EXPECT_EQ(e.fam, b.fam.kind == Fam::kNone ? -1 : int(b.fam.kind) - 1) << k;
    if (b.fam.kind == Fam::kAlignment) EXPECT_EQ(e.block, b.fam.block);
    if (b.fam.kind != Fam::kLogup) continue;
    ++logups;
    EXPECT_EQ(e.alpha, b.fam.alpha);
    EXPECT_EQ(e.needles, u64(b.fam.needles));
    EXPECT_EQ(e.hists, u64(b.fam.hists));
    EXPECT_EQ(e.block, b.fam.block);
    EXPECT_EQ(e.dens, u64(b.log.dens));
    ASSERT_EQ(e.inner.size(), b.log.inner.size());
    for (size_t i = 0; i < e.inner.size(); ++i)
      EXPECT_EQ(e.inner[i], (std::array<uint64_t, 4>{b.log.inner[i].l, b.log.inner[i].r,
                                                     b.log.inner[i].num,
                                                     b.log.inner[i].den}));
    EXPECT_EQ(e.inner.size() + 1, e.dens.size());
    EXPECT_EQ(e.sum, b.log.sum);
    EXPECT_EQ(e.zu.size(), 1u);
  }
  EXPECT_GT(logups, 0u);
}

// The mirrors refuse each mutation.
TEST(GordieHoweEmitExport, MirrorRejects) {
  auto cs = system();
  auto c = compile(*cs, table_profile());
  using T = ex::EmitTable<AF>;
  auto refused = [&](std::function<void(T &)> edit) {
    std::vector<std::string> err;
    compiler::EmitOptions o;
    o.errors = &err;
    o.mutate = [&](void *t, const std::string &) { edit(*static_cast<T *>(t)); };
    tables(*c, o);
    return !err.empty();
  };
  EXPECT_FALSE(refused([](T &) {}));
  auto first = [](T &t, auto pred) -> size_t {
    for (size_t k = 0; k < t.nodes.size(); ++k)
      if (pred(t.nodes[k], k)) return k;
    return SIZE_MAX;
  };
  // A sum made a product.
  EXPECT_TRUE(refused([&](T &t) {
    const size_t k = first(t, [](const ENodeInfo &x, size_t) {
      return x.node.kind == ENode::kBin && x.node.op == ENode::kAdd;
    });
    ASSERT_NE(k, SIZE_MAX);
    t.nodes[k].node.op = ENode::kMul;
  }));
  // A scaling's code changed.
  EXPECT_TRUE(refused([&](T &t) {
    const size_t k = first(t, [](const ENodeInfo &x, size_t) {
      return x.node.kind == ENode::kScale && x.node.code != "1";
    });
    ASSERT_NE(k, SIZE_MAX);
    t.nodes[k].node.code = "5";
  }));
  // A shared node's .ref dropped, and moved.
  EXPECT_TRUE(refused([&](T &t) {
    const size_t k = first(t, [](const ENodeInfo &x, size_t) { return x.has_ref; });
    ASSERT_NE(k, SIZE_MAX);
    t.nodes[k].has_ref = false;
  }));
  EXPECT_TRUE(refused([&](T &t) {
    const size_t k = first(t, [](const ENodeInfo &x, size_t) { return x.has_ref; });
    ASSERT_NE(k, SIZE_MAX);
    t.nodes[k].ref += 1;
  }));
  // A wrong length, and a kid not below its node.
  EXPECT_TRUE(refused([&](T &t) { t.nodes.back().len += 1; }));
  EXPECT_TRUE(refused([&](T &t) {
    const size_t k = first(t, [](const ENodeInfo &x, size_t) {
      return x.node.kind == ENode::kBin;
    });
    ASSERT_NE(k, SIZE_MAX);
    t.nodes[k].node.kids[0] = k;
  }));
  // A product node's wire moved to another DAG node.
  EXPECT_TRUE(refused([&](T &t) {
    const size_t k = first(t, [](const ENodeInfo &x, size_t) {
      return x.node.kind == ENode::kBin && x.node.op == ENode::kMul && !x.flat;
    });
    ASSERT_NE(k, SIZE_MAX);
    t.W[k][0].x += 1;
  }));
  // A wire's coefficient changed.
  EXPECT_TRUE(refused([&](T &t) {
    const size_t k = first(t, [](const ENodeInfo &x, size_t) {
      return x.node.kind == ENode::kBin && !x.flat;
    });
    ASSERT_NE(k, SIZE_MAX);
    t.W[k][0].c1 = af().addf(t.W[k][0].c1, af().one());
  }));
  // An aux wire moved, and one dropped.
  EXPECT_TRUE(refused([&](T &t) {
    const size_t k =
        first(t, [&](const ENodeInfo &, size_t j) { return !t.aux[j].empty(); });
    ASSERT_NE(k, SIZE_MAX);
    t.aux[k][0].x += 1;
  }));
  EXPECT_TRUE(refused([&](T &t) {
    const size_t k =
        first(t, [&](const ENodeInfo &, size_t j) { return !t.aux[j].empty(); });
    ASSERT_NE(k, SIZE_MAX);
    t.aux[k].pop_back();
  }));
  // An assertion pair's node moved to another node, and two swapped.
  EXPECT_TRUE(refused([&](T &t) {
    for (auto &b : t.blocks)
      if (b.has_root && !b.Z.empty()) {
        b.Z[0] = b.Z.back() + 1;
        return;
      }
    FAIL() << "no rooted entry";
  }));
  EXPECT_TRUE(refused([&](T &t) {
    for (auto &b : t.blocks)
      if (b.has_root && b.Z.size() > 1) {
        std::swap(b.Z[0], b.Z[1]);
        return;
      }
    FAIL() << "no entry of two assertions";
  }));
  // A product operand (the shared a b, a leaf of the chain's products)
  // marked uncut: its parent's cut expands it, and a product of a product is
  // no product of atoms.
  EXPECT_TRUE(refused([&](T &t) {
    std::vector<uint8_t> root(t.nodes.size(), 0);
    for (const auto &b : t.blocks)
      if (b.has_root) root[b.root] = 1;
    const size_t k = first(t, [&](const ENodeInfo &x, size_t j) {
      return t.cut[j] && !root[j] && x.node.kind == ENode::kBin &&
             x.node.op == ENode::kMul && !x.flat;
    });
    ASSERT_NE(k, SIZE_MAX);
    t.cut[k] = 0;
    t.W[k].clear();
  }));
  // A wire on an uncut node.
  EXPECT_TRUE(refused([&](T &t) {
    const size_t k = first(t, [&](const ENodeInfo &x, size_t j) {
      return !t.cut[j] && x.len > 0;
    });
    ASSERT_NE(k, SIZE_MAX);
    for (const auto &b : t.blocks)
      if (b.has_root) {
        t.W[k].push_back(t.W[b.root].at(0));
        return;
      }
    FAIL() << "no rooted entry";
  }));
  // A value leaf's block moved.
  EXPECT_TRUE(refused([&](T &t) {
    const size_t k = first(t, [](const ENodeInfo &x, size_t) {
      return x.node.kind == ENode::kValue && x.node.pl.kind == ex::Place::kBlock;
    });
    ASSERT_NE(k, SIZE_MAX);
    t.nodes[k].node.pl.b += 1;
  }));

  // A LogUp record: a needle pointer moved to alpha's node, its tree's
  // last inner node's kids swapped (the spans no longer adjacent), its
  // weights block moved, its sum's wire moved.
  auto logup = [](T &t) -> T::Block * {
    for (auto &b : t.blocks)
      if (b.fam.kind == T::Fam::kLogup && !b.log.inner.empty()) return &b;
    return nullptr;
  };
  EXPECT_TRUE(refused([&](T &t) {
    auto *b = logup(t);
    ASSERT_NE(b, nullptr);
    b->fam.needles[0] = b->fam.alpha;
  }));
  EXPECT_TRUE(refused([&](T &t) {
    auto *b = logup(t);
    ASSERT_NE(b, nullptr);
    std::swap(b->log.inner.back().l, b->log.inner.back().r);
  }));
  EXPECT_TRUE(refused([&](T &t) {
    auto *b = logup(t);
    ASSERT_NE(b, nullptr);
    b->fam.block += 1;
  }));
  EXPECT_TRUE(refused([&](T &t) {
    auto *b = logup(t);
    ASSERT_NE(b, nullptr);
    b->log.sum = b->log.dens[0];
  }));

  // The lazy difference check (A14) on a hand-built DAG. s = x1 + x2 is
  // cloned into t = s + x3, t into u = 3 t, and u into w = u + x4 x5 (the
  // builder clones an operand of equal or greater depth), so w's own terms
  // are 3 x1 + 3 x2 + 3 x3 + x4 x5 and never name s.
  {
    QuadCircuit<AF> q(af());
    size_t x[6];
    for (size_t i = 1; i < 6; ++i) x[i] = q.input_wire();
    const AElt three = af().of_scalar(3);
    const size_t s = q.add(x[1], x[2]);
    const size_t t3 = q.add(s, x[3]);
    const size_t u = q.mul(three, t3);
    const size_t m = q.mul(x[4], x[5]);
    const size_t w = q.add(u, m);
    auto cert = q.take_certificate({w, s, m});
    ASSERT_EQ(cert->node_term_begin.size(), cert->node_id.size() + 1);
    using RM = ex::RelMirror<AF>;
    using W = RM::Wire;
    auto wire = [&](size_t n) {
      RM::TE e;
      e.k = RM::TE::kWire;
      e.w = W{af().zero(), af().one(), n};
      return e;
    };
    auto node = [](typename RM::TE::K k, std::vector<RM::TE> kids, AElt c) {
      RM::TE e;
      e.k = k;
      e.c = c;
      e.kids = std::move(kids);
      return e;
    };
    // w = 3 (s + x3) + m, and the same tree without x3.
    const RM::TE good = node(
        RM::TE::kSum,
        {node(RM::TE::kScale, {node(RM::TE::kSum, {wire(s), wire(x[3])}, af().zero())},
              three),
         wire(m)},
        af().zero());
    const RM::TE short_x3 = node(
        RM::TE::kSum, {node(RM::TE::kScale, {wire(s)}, three), wire(m)}, af().zero());
    const ir::Program prog;
    const std::vector<ir::InputBlock> inputs;
    const ex::EmitTable<AF> table;
    const W ww{af().zero(), af().one(), w};
    {
      RM rm(af(), *cert, prog, inputs, table);
      EXPECT_EQ(rm.cut_error(ww, good), "");
      // An input-only remainder: 3 x3 is left once s and m are unfolded.
      const std::string why = rm.cut_error(ww, short_x3);
      EXPECT_NE(why.find("does not vanish"), std::string::npos) << why;
    }
    // A wrong coefficient deep in the cloned operand: s's term x2 read as 7.
    {
      size_t at = SIZE_MAX;
      for (size_t i = 0; i < cert->node_id.size(); ++i)
        if (cert->node_id[i] == s)
          for (size_t k = cert->node_term_begin[i]; k < cert->node_term_begin[i + 1]; ++k)
            if (cert->node_terms[3 * k + 2] == x[2]) at = k;
      ASSERT_NE(at, SIZE_MAX);
      cert->constants.push_back(af().of_scalar(7));
      cert->node_terms[3 * at] = uint32_t(cert->constants.size() - 1);
      RM rm(af(), *cert, prog, inputs, table);
      EXPECT_NE(rm.cut_error(ww, good), "");
    }
  }
}

// A MAC H half whose operand only the circuit reads: its record decodes
// and checks, and the mirror refuses its pointers moved and a wrong
// generator power.
TEST(GordieHoweEmitExport, MacFamily) {
  auto cs = mac_system();
  CompileProfile prof = table_profile();
  prof.mac_bases = {MacBasis{128, {7, 2, 1, 0}}};
  auto c = compile(*cs, prof);
  const auto out = tables(*c);
  const compiler::EmitExport *g = nullptr;
  for (const auto &x : out)
    if (x.domain == "G") g = &x;
  ASSERT_NE(g, nullptr);
  const Decoded d = decode(*g);
  const Decoded::Entry *mac = nullptr;
  for (const auto &e : d.entries)
    if (e.fam == 2) mac = &e;
  ASSERT_NE(mac, nullptr);
  EXPECT_FALSE(mac->chunks.empty());
  EXPECT_EQ(mac->zu.size(), 1u);
  using T = ex::EmitTable<GF>;
  auto refused = [&](std::function<void(T &)> edit) {
    std::vector<std::string> err;
    compiler::EmitOptions o;
    o.errors = &err;
    o.mutate = [&](void *t, const std::string &dn) {
      if (dn == "G") edit(*static_cast<T *>(t));
    };
    tables(*c, o);
    return !err.empty();
  };
  auto first = [](T &t) -> T::Block * {
    for (auto &b : t.blocks)
      if (b.fam.kind == T::Fam::kMacH) return &b;
    return nullptr;
  };
  EXPECT_FALSE(refused([](T &) {}));
  EXPECT_TRUE(refused([&](T &t) {
    auto *b = first(t);
    ASSERT_NE(b, nullptr);
    b->fam.powers = b->fam.tag;
  }));
  EXPECT_TRUE(refused([&](T &t) {
    auto *b = first(t);
    ASSERT_NE(b, nullptr);
    b->fam.tag = b->fam.powers;
  }));
  // Two chunks' wires swapped: each chunk's cut reads the other's bits.
  EXPECT_TRUE(refused([&](T &t) {
    auto *b = first(t);
    ASSERT_NE(b, nullptr);
    ASSERT_GT(b->log.chunks.size(), 1u);
    std::swap(b->log.chunks[0], b->log.chunks[1]);
  }));
  // An alignment's filler block moved.
  bool aligned = false;
  for (const auto &e : d.entries) aligned = aligned || e.fam == 0;
  EXPECT_TRUE(aligned) << "domain G has no alignment entry";
  EXPECT_TRUE(refused([&](T &t) {
    for (auto &b : t.blocks)
      if (b.fam.kind == T::Fam::kAlignment) {
        b.fam.block += 1;
        return;
      }
    FAIL() << "no alignment entry";
  }));
}

// derive<Bit> over GF(2^128): the view check x (x - 1) = 0 as the steps
// ones - x and x (ones - x), in characteristic two. The step reads the
// domain's constant of ones of the view's length: printed for a negation
// of that length (with NOT), else added by the printer after every other
// value (without NOT), so the circuit exports either way.
TEST(GordieHoweEmitExport, BooleanStepsChar2) {
  for (const bool with_not : {false, true}) {
  auto cs = std::make_unique<Sys>("gh-emit-char2");
  auto &G = cs->domain(env().g_profile(), "G");
  auto a = G.priv(Subfield{}, "a", 4);
  auto b = G.priv(Subfield{}, "b", 4);
  auto d = G.derive(Bit{}, "d", a + b);
  if (with_not)
    G.assert_zero("prod", (!d) * a - b * d).pin(Placement::kCircuit);
  else
    G.assert_zero("prod", d * a - b * d).pin(Placement::kCircuit);
  auto c = compile(*cs, table_profile());
  const auto *W =
      static_cast<const EmitWalk<GF> *>(c->compiled_domain(0).gkr_emit_walk());
  ASSERT_NE(W, nullptr);
  size_t steps = 0;
  for (const auto &en : W->nodes) steps += en.step == EmitWalk<GF>::kViewMul;
  EXPECT_GE(steps, 1u);
  const auto out = tables(*c);
  ASSERT_EQ(out.size(), 1u);
  if (!with_not) {
    // The added constant is the last value.
    const ir::Program &p = c->program();
    ASSERT_FALSE(p.values.empty());
    EXPECT_EQ(p.values.back().kind, ir::Value::kConstant);
    EXPECT_EQ(p.values.back().entries.size(), 4u);
  }
  const Decoded dd = decode(out[0]);
  EXPECT_TRUE(dd.char2);
  // Some entry's root is its last node, the step x (ones - x) (bin).
  bool found = false;
  for (const auto &e : dd.entries)
    if (e.has_root && !e.kinds.empty() && e.root + 1 == e.hi && e.kinds.back() == 2)
      found = true;
  EXPECT_TRUE(found);
  }
}

// A system whose domain A's circuit holds a spectral product
// (ops::assert_spectral): Ntt(w) = h_hat * Ntt(s) for the selected row
// h_hat of a public ring of spectra under a negacyclic NTT of 16
// coefficients.
std::unique_ptr<Sys> spectral_system() {
  const size_t n = 16, R = 8;
  const uint64_t q = 12289;
  auto cs = std::make_unique<Sys>("gh-emit-export-product");
  auto &A = cs->domain(env().a_profile(), "A");
  auto keys = A.pub(Subfield{}, "keys", Shape{R, n}).bounded(q);
  auto spec = A.priv(Subfield{}, "spec", n);
  auto sv = A.priv(Subfield{}, "s", n);
  auto w = A.priv(Subfield{}, "w", n);
  assert_range(sv, 50, "s");
  assert_range(w, q, "w");
  const AElt psi = *ops::FieldNtt<AF>::root(af(), 2 * n);
  const auto ntt = ops::Ntt(af(), n, psi, ops::Stages::every(2),
                            ops::NttOrder::kNatural);
  const auto map =
      lib::table::RowMap<AF>::negacyclic(af(), n, psi, ops::NttOrder::kNatural);
  const auto ring = lib::table::public_table(*cs, A, "ring", keys, map);
  lib::table::select_row(*cs, ring, "signer", spec);
  ops::assert_spectral(*cs, "rel", w, ops::SpectralProduct(spec, sv, ntt));
  return cs;
}

// A12: a product operand whose one-level form is no atom (here an operator
// or affine node under a product), left uncut, is refused; the honest
// marking is accepted.
// The selection certificate (compiler/table_selections.h) of the spectral
// system's select_row: the predicate `signer`, the table's values, the record
// `spec` and the row map's one natural leaf; a record naming no predicate is
// refused.
TEST(GordieHoweEmitExport, TableSelectionCert) {
  auto cs = spectral_system();
  auto c = compile(*cs, table_profile());
  const ir::Program &p = c->program();
  const auto &recs = c->records().table_selections;
  ASSERT_EQ(recs.size(), 1u);
  EXPECT_EQ(recs[0].pred, "signer");
  EXPECT_EQ(recs[0].rows, 8u);
  EXPECT_EQ(recs[0].bits, 3u);
  ASSERT_EQ(recs[0].leaves.size(), 1u);
  EXPECT_TRUE(recs[0].leaves[0].ntt);
  EXPECT_TRUE(recs[0].leaves[0].natural);
  const auto certs = compiler::table_selection_certs(p, recs);
  ASSERT_EQ(certs.size(), 1u);
  auto id = [&](const std::string &name) {
    for (size_t v = 0; v < p.values.size(); ++v)
      if (p.values[v].name == name) return std::to_string(v);
    return std::string("?");
  };
  size_t q = p.predicates.size();
  for (size_t i = 0; i < p.predicates.size(); ++i)
    if (p.predicates[i].name == "signer") q = i;
  ASSERT_LT(q, p.predicates.size());
  const std::string &x = certs[0];
  EXPECT_EQ(x.rfind("⟨" + std::to_string(q) + ", { dom := 0,", 0), 0u) << x;
  EXPECT_NE(x.find("gamma := " + id("ring.gamma") + ","), std::string::npos) << x;
  EXPECT_NE(x.find("pow := " + id("ring.powers") + ","), std::string::npos) << x;
  EXPECT_NE(x.find("dig := " + id("ring.digests") + ","), std::string::npos) << x;
  EXPECT_NE(x.find("idx := " + id("signer.index") + ","), std::string::npos) << x;
  EXPECT_NE(x.find("record := .leaf " + id("spec") + ","), std::string::npos) << x;
  EXPECT_NE(x.find("parts := [(" + id("keys") + ", 16)], rows := 8, bits := 3 }⟩"),
            std::string::npos)
      << x;
  EXPECT_NE(x.find("map := [⟨true, true, 16, 0, "), std::string::npos) << x;
  auto bad = recs;
  bad[0].pred = "missing";
  EXPECT_THROW(compiler::table_selection_certs(p, bad), std::runtime_error);
}

TEST(GordieHoweEmitExport, UncutOperandRejected) {
  auto cs = spectral_system();
  auto c = compile(*cs, table_profile());
  using T = ex::EmitTable<AF>;
  auto refused = [&](std::function<void(T &)> edit) {
    std::vector<std::string> err;
    compiler::EmitOptions o;
    o.errors = &err;
    o.mutate = [&](void *t, const std::string &) { edit(*static_cast<T *>(t)); };
    tables(*c, o);
    return !err.empty();
  };
  EXPECT_FALSE(refused([](T &) {}));
  // The honest marking cuts a node of one parent only for an atom: so a
  // cut, non-root, once-read operator, affine or chain node is one.
  EXPECT_TRUE(refused([&](T &t) {
    std::vector<size_t> parents(t.nodes.size(), 0);
    for (const auto &n : t.nodes) {
      std::set<size_t> seen(n.node.kids.begin(), n.node.kids.end());
      for (const auto &term : n.node.terms) seen.insert(term.view);
      for (size_t a : seen) ++parents[a];
    }
    std::vector<uint8_t> root(t.nodes.size(), 0);
    for (const auto &b : t.blocks)
      if (b.has_root) root[b.root] = 1;
    // A product's or mux's operand, read through uncut views.
    std::function<bool(size_t)> try_kid = [&](size_t a) {
      const auto k = t.nodes[a].node.kind;
      if (!t.cut[a] && (k == ENode::kGather || k == ENode::kBroadcast ||
                        k == ENode::kMaterialize)) {
        for (size_t b : t.nodes[a].node.kids)
          if (try_kid(b)) return true;
        return false;
      }
      // A node whose one-level form is no wire: an operator, a sum, a
      // chain, an affine node of several terms.
      const bool form = k == ENode::kApply || k == ENode::kSum || k == ENode::kBin ||
                        (k == ENode::kLin && t.nodes[a].node.terms.size() > 1);
      if (t.cut[a] && !root[a] && parents[a] == 1 && form) {
        t.cut[a] = 0;
        t.W[a].clear();
        return true;
      }
      return false;
    };
    for (size_t m = 0; m < t.nodes.size(); ++m) {
      const ENode &x = t.nodes[m].node;
      // A product's factors, and a mux's control (its other operands enter
      // linearly).
      if ((x.kind == ENode::kBin && x.op == ENode::kMul) || x.kind == ENode::kProd) {
        for (size_t a : x.kids)
          if (try_kid(a)) return;
      } else if (x.kind == ENode::kMux && try_kid(x.kids[0])) {
        return;
      }
    }
    FAIL() << "no non-atom product operand";
  }));
}

TEST(GordieHoweEmitExport, Walk) {
  auto cs = system();
  auto c = compile(*cs, table_profile());
  const auto *W =
      static_cast<const EmitWalk<AF> *>(c->compiled_domain(0).gkr_emit_walk());
  ASSERT_NE(W, nullptr);
  EXPECT_TRUE(W->problem.empty()) << W->problem;
  size_t flat = 0;
  for (size_t k = 0; k < W->nodes.size(); ++k) {
    const auto &en = W->nodes[k];
    flat += en.flat;
    if (en.e == nullptr) continue;
    if (!en.flat) EXPECT_EQ(en.W.size(), en.len) << k;
    for (const auto &kid : en.e->kids) {
      auto it = W->expr_id.find(kid.get());
      ASSERT_NE(it, W->expr_id.end());
      EXPECT_LT(it->second, k);
    }
  }
  // ab * ab * a * b flattens two of its three products.
  EXPECT_GE(flat, 2u);

  // A view's id: the same wires keep it, others give a new one, and a
  // reader below the new one reads the old.
  using Wire = EmitWalk<AF>::Wire;
  EmitWalk<AF> v;
  const size_t v0 = v.view(3, {Wire{af().zero(), af().one(), 7}});
  EXPECT_EQ(v.view(3, {Wire{af().zero(), af().one(), 7}}), v0);
  const size_t v1 = v.view(3, {Wire{af().zero(), af().one(), 8}});
  EXPECT_NE(v1, v0);
  EXPECT_EQ(v.view_before(3, v1), v0);
  EXPECT_EQ(v.view_before(3, v1 + 1), v1);

  // An address reused with other contents, and a node completed twice.
  auto x = std::make_shared<ExprNode<AF>>();
  x->op = ExprOp::kConst;
  x->n = 1;
  x->c = {af().one()};
  EmitWalk<AF> w;
  w.complete(x.get(), false);
  w.hit(x.get());
  EXPECT_TRUE(w.problem.empty());
  x->n = 2;
  w.hit(x.get());
  EXPECT_NE(w.problem.find("reused"), std::string::npos) << w.problem;
  EmitWalk<AF> w2;
  w2.complete(x.get(), false);
  w2.complete(x.get(), false);
  EXPECT_NE(w2.problem.find("twice"), std::string::npos) << w2.problem;
}

// A circuit reads a wiring view of two values with a zero coordinate
// (gather): the program prints the view as its wiring, the form the
// circuit reads, so the export covers and checks the circuit.
TEST(GordieHoweEmitExport, WiringView) {
  auto cs = std::make_unique<Sys>("gh-emit-wiring");
  auto &A = cs->domain(env().a_profile(), "A");
  auto a = A.priv(Subfield{}, "a", 4);
  auto b = A.priv(Subfield{}, "b", 4);
  const auto v = gather(std::vector{a, b},
                        {{1, 0}, {0, 1}, Coord::zero(), {0, 3}, {1, 2}, {0, 0},
                         {1, 1}, {1, 3}});
  A.assert_zero("wired", v * v - v).pin(Placement::kCircuit);
  auto c = compile(*cs, table_profile());
  const auto out = tables(*c);
  ASSERT_EQ(out.size(), 1u);
  EXPECT_EQ(out[0].domain, "A");
  decode(out[0]);
}

// A domain with two circuits has no single emitted circuit.
TEST(GordieHoweEmitExport, EmittedCircuit) {
  ir::Program p;
  p.circuits.resize(2);
  p.circuits[0].domain = 0;
  p.circuits[1].domain = 0;
  EXPECT_THROW(ex::emitted_circuit(p, 0), std::runtime_error);
  p.circuits[0].domain = 1;
  EXPECT_EQ(ex::emitted_circuit(p, 0), 1u);
  EXPECT_EQ(ex::emitted_circuit(p, 1), 0u);
}

}  // namespace
}  // namespace proofs::gordiehowe
