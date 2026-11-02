// Copyright 2026 Chad Sharp and Paul Grubbs
// SPDX-License-Identifier: Apache-2.0

// The GHC writer (compiler/ghc.h, ghc_gkr.h).
//
//   GordieHoweGhc.Types       type text parsed, printed and encoded curried
//   GordieHoweGhc.RoundTrip   a file of plain and spine-form sections (a
//                             structure, an inductive, lists, options,
//                             pairs, integers, strings, index maps, a
//                             trie split into a section, references) reads
//                             back to its sections and renders as text
//   GordieHoweGhc.Malformed   the reader refuses a wrong magic or version,
//                             a truncated file, a length past the end,
//                             trailing bytes after the end marker, a value
//                             shorter or longer than its length, a bad
//                             constructor index and Bool, a reference to a
//                             later section or of another type, a spine tag
//                             on a type with no constructor form, and a
//                             second section of one name; the writer
//                             refuses the same values
//   GordieHoweGhc.UnknownType the writer and the reader refuse a section of
//                             a type the schema does not know, at a wrong
//                             arity, or naming an unknown argument
//   GordieHoweGhc.Gkr         a small certificate's sections: their names,
//                             types, flags and order, the packed constant
//                             table and a DAG chunk, as Lean reads them
//   GordieHoweGhc.SchemaText  a schema's text (Schema::dump): structures
//                             with their named or unnamed fields,
//                             inductives with their constructors; the GKR
//                             schema's text is formal/scripts/ghc_schema.txt,
//                             the Lean types' text (scripts/GhcSchema.lean)

#include <cstdint>
#include <fstream>
#include <iterator>
#include <string>
#include <vector>

#include "gordiehowe/compiler/ghc.h"
#include "gordiehowe/compiler/ghc_gkr.h"
#include "gtest/gtest.h"

namespace proofs::gordiehowe::ghc {
namespace {

// A schema: a structure and an inductive over the primitives.
Schema test_schema() {
  Schema s;
  s.structure("T.Point", 0, {"Nat", "Int", "Bool"});
  s.inductive("T.Shape", 0,
              {{"dot", {}},
               {"line", {"T.Point", "T.Point"}},
               {"poly", {"List T.Point", "Option String"}},
               {"pair", {"Prod Nat GordieHowe.RealizedProgram.IndexMap"}}});
  s.inductive("T.Tree", 1, {{"nil", {}}, {"leaf", {"#0"}}, {"node", {"T.Tree #0", "T.Tree #0"}}});
  return s;
}

void point(Bytes &o, uint64_t x, int64_t y, bool b) {
  o.nat(x);
  o.integer(y);
  o.boolean(b);
}

TEST(GordieHoweGhc, Types) {
  const Ty t = ty("Prod (List Nat) (T.Tree (Option Bool))");
  EXPECT_EQ(t.name, "Prod");
  ASSERT_EQ(t.args.size(), 2u);
  EXPECT_EQ(t.args[1].args[0].text(), "Option Bool");
  EXPECT_EQ(t.text(), "Prod (List Nat) (T.Tree (Option Bool))");
  // List Nat: app (const List) (const Nat).
  Bytes o;
  ty("List Nat").encode(o);
  EXPECT_EQ(o.out, (std::vector<uint8_t>{1, 0, 4, 'L', 'i', 's', 't', 0, 3, 'N', 'a', 't'}));
  EXPECT_THROW(ty("List (Nat"), Error);
  EXPECT_THROW(ty(""), Error);
}

// A file of every kind of value; returns it and its expected rendering.
std::vector<uint8_t> sample(const Schema &s, std::string *text) {
  File f(s);
  Bytes p;
  point(p, 300, -5, true);
  f.section("p", ty("T.Point"), 0, p);
  Bytes sh;
  sh.ctor(2);
  sh.nat(2);
  point(sh, 1, 2, false);
  point(sh, 3, -64, true);
  sh.ctor(1);
  sh.string("ok");
  f.section("q.shape", ty("T.Shape"), kCompile, sh);
  Bytes pr;
  pr.ctor(3);
  pr.nat(7);
  pr.nat(4);
  f.section("pair", ty("T.Shape"), 0, pr);
  // A trie of naturals keyed 0..4, its subtrees at depth 1 sections.
  std::vector<Bytes> leaves(5);
  TrieWriter::Items items;
  for (uint64_t k = 0; k < 5; ++k) {
    leaves[k].nat(10 + k);
    items.emplace_back(k, &leaves[k]);
  }
  Bytes tr;
  TrieWriter::split(f, tr, items, "tree.part", ty("T.Tree Nat"), 1);
  f.section("tree", ty("T.Tree Nat"), kSpine | kReader, tr);
  // A spine-form list referring to sections 0 and 1, with a plain item.
  Bytes l;
  l.inline_();
  l.nat(2);
  l.ref(1);
  l.plain();
  l.ctor(0);
  f.section("shapes", ty("List T.Shape"), kSpine, l);
  *text =
      "@0 p : T.Point :=\n  ⟨300, -5, true⟩\n"
      "@1 q.shape : T.Shape [compile] :=\n  (.poly [⟨1, 2, false⟩, ⟨3, -64, true⟩] (some \"ok\"))\n"
      "@2 pair : T.Shape :=\n  (.pair ⟨7, idx4⟩)\n"
      "@3 tree.part0 : T.Tree Nat :=\n  (.node (.node (.leaf 10) (.leaf 14)) (.leaf 12))\n"
      "@4 tree.part1 : T.Tree Nat :=\n  (.node (.leaf 11) (.leaf 13))\n"
      "@5 tree : T.Tree Nat [spine] [reader] :=\n  (.node @3 @4)\n"
      "@6 shapes : List T.Shape [spine] :=\n  [@1, .dot]\n";
  return f.bytes();
}

TEST(GordieHoweGhc, RoundTrip) {
  const Schema s = test_schema();
  std::string want;
  const std::vector<uint8_t> b = sample(s, &want);
  EXPECT_EQ(std::vector<uint8_t>(b.begin(), b.begin() + 4),
            (std::vector<uint8_t>{0x47, 0x48, 0x43, 0x03}));
  const std::vector<Section> secs = read(b, s);
  ASSERT_EQ(secs.size(), 7u);
  EXPECT_EQ(secs[1].name, "q.shape");
  EXPECT_EQ(secs[1].type, ty("T.Shape"));
  EXPECT_EQ(secs[1].flags, uint64_t(kCompile));
  EXPECT_EQ(secs[0].value, (std::vector<uint8_t>{0xac, 0x02, 0x09, 0x01}));
  EXPECT_EQ(show(b, s), want);
  // Written again from the sections read, the same bytes.
  File g(s);
  for (const Section &x : secs) {
    Bytes v;
    v.bytes(x.value);
    g.section(x.name, x.type, x.flags, v);
  }
  EXPECT_EQ(g.bytes(), b);
  // Naturals of any size.
  File h(s);
  BitPack c;
  c.put(200, 1);
  Bytes big;
  c.write(big);
  h.section("n", ty("Nat"), 0, big);
  EXPECT_EQ(show(h.bytes(), s), "@0 n : Nat :=\n  0x100000000000000000000000000000000000000000000000000\n");
}

// The bytes of a one-section file: name, type, flags, length, value.
std::vector<uint8_t> one(const std::string &name, const Ty &t, uint64_t flags,
                         const std::vector<uint8_t> &value, size_t len) {
  Bytes o;
  o.out = {0x47, 0x48, 0x43, 0x03};
  o.string(name);
  t.encode(o);
  o.nat(flags);
  o.nat(len);
  o.bytes(value);
  o.string("");
  return o.out;
}

TEST(GordieHoweGhc, Malformed) {
  const Schema s = test_schema();
  std::string want;
  const std::vector<uint8_t> b = sample(s, &want);
  auto bad = [&](std::vector<uint8_t> x) { EXPECT_THROW(read(x, s), Error); };
  // Magic and version.
  {
    auto x = b;
    x[0] = 'X';
    bad(x);
    x = b;
    x[3] = 2;
    bad(x);
  }
  // Truncated anywhere; a byte after the end marker.
  for (size_t n : {size_t(3), size_t(5), b.size() / 2, b.size() - 1})
    bad(std::vector<uint8_t>(b.begin(), b.begin() + n));
  {
    auto x = b;
    x.push_back(0);
    bad(x);
  }
  const std::vector<uint8_t> pt = {0x05, 0x02, 0x01};  // ⟨5, 1, true⟩
  EXPECT_NO_THROW(read(one("p", ty("T.Point"), 0, pt, 3), s));
  // A length past the end, a value shorter or longer than its length.
  bad(one("p", ty("T.Point"), 0, pt, 4));
  bad(one("p", ty("T.Point"), 0, {0x05, 0x02}, 2));
  bad(one("p", ty("T.Point"), 0, {0x05, 0x02, 0x01, 0x00}, 4));
  // A Bool of 2; a constructor index of 4 of T.Shape's 4.
  bad(one("p", ty("T.Point"), 0, {0x05, 0x02, 0x02}, 3));
  bad(one("s", ty("T.Shape"), 0, {0x04}, 1));
  // Spine form: a reference to itself, a spine tag 3, a constructor form of
  // a natural.
  bad(one("s", ty("T.Shape"), kSpine, {0x01, 0x00}, 2));
  bad(one("s", ty("T.Shape"), kSpine, {0x03}, 1));
  bad(one("n", ty("Nat"), kSpine, {0x02, 0x05}, 2));
  EXPECT_NO_THROW(read(one("n", ty("Nat"), kSpine, {0x00, 0x05}, 2), s));
  // The writer refuses the same.
  File f(s);
  Bytes v;
  v.bytes({0x05, 0x02});
  EXPECT_THROW(f.section("p", ty("T.Point"), 0, v), Error);
  Bytes r;
  r.ref(0);
  EXPECT_THROW(f.section("s", ty("T.Shape"), kSpine, r), Error);
  Bytes ok;
  ok.bytes(pt);
  f.section("p", ty("T.Point"), 0, ok);
  // A reference to a section of another type; a second section "p".
  EXPECT_THROW(f.section("s", ty("T.Shape"), kSpine, r), Error);
  EXPECT_THROW(f.section("p", ty("T.Point"), 0, ok), Error);
  EXPECT_THROW(f.section("", ty("T.Point"), 0, ok), Error);
  Bytes rr;
  rr.ref(0);
  EXPECT_NO_THROW(f.section("p2", ty("T.Point"), kSpine, rr));
}

TEST(GordieHoweGhc, UnknownType) {
  const Schema s = test_schema();
  const std::vector<uint8_t> pt = {0x05, 0x02, 0x01};
  for (const char *t : {"T.Nope", "T.Point Nat", "List", "List T.Nope", "T.Tree"}) {
    EXPECT_THROW(read(one("p", ty(t), 0, pt, 3), s), Error) << t;
    File f(s);
    Bytes v;
    v.bytes(pt);
    EXPECT_THROW(f.section("p", ty(t), 0, v), Error) << t;
  }
  // The GKR schema knows its section types, and nothing else.
  const Schema &g = gkr_schema();
  for (const char *t : {"GordieHowe.RealizedProgram.CircuitData", "GordieHowe.GKR.Fold.Consts",
                        "List GordieHowe.GKR.Rel.EntryCert",
                        "GordieHowe.RealizedProgram.Trie GordieHowe.RealizedProgram.ENodeInfo"})
    EXPECT_TRUE(g.knows(ty(t))) << t;
  EXPECT_FALSE(g.knows(ty("GordieHowe.RealizedProgram.CircuitDatum")));
}

TEST(GordieHoweGhc, Gkr) {
  GkrCore k;
  k.c = 2;
  k.w = 4;
  k.chr = {17};
  k.neg1 = {16};
  k.half = {9};
  k.ninputs = 2;
  k.nnodes = 4;
  k.consts = {{0}, {1}, {16}};
  k.dag = {{2, {{1, 0, 1}}}, {3, {{0, 1, 2}}}};
  k.asserts = {3};
  k.outputs = {};
  k.layers = {{{2, false, {{1, 0, 1}}}}};
  k.last_asserts = {{0, 3}};
  GkrTable t;
  File f(gkr_schema());
  write_gkr(f, "cert", k, t);
  const std::vector<uint8_t> b = f.bytes();
  const std::vector<Section> secs = read(b, gkr_schema());
  std::vector<std::string> names;
  for (const Section &x : secs) names.push_back(x.name);
  EXPECT_EQ(names, (std::vector<std::string>{"cert.consts", "cert.dagPart0", "cert.dag",
                                             "certlayer0", "certwtab0", "cert.layered",
                                             "cert.width", "cert.sched", "cert.table",
                                             "cert.entries", "cert"}));
  EXPECT_EQ(secs[0].flags, uint64_t(kCompile));
  EXPECT_EQ(secs[3].flags, uint64_t(kCompile | kReader));
  EXPECT_EQ(secs.back().flags, uint64_t(kSpine | kReader));
  const std::string text = show(b, gkr_schema());
  // The constants 0, 1, 16 at width 5 (16's bit length), 16 to a chunk:
  // 0 | 1 << 5 | 16 << 10 = 16416. The DAG's node 2: 2 * 1 | (1 | 0 << 4 |
  // 1 << 8) << 4 = 4114; node 3: 2 | (0 | 1 << 4 | 2 << 8) << 4 = 8450, the
  // trie of keys 2, 3 split at depth 0. The gate: 2 | 0 << 4 | 2 << 8 |
  // (1 | 0 << 4 | 1 << 8) << 12 = 1053186.
  for (const char *want :
       {"@0 cert.consts : GordieHowe.GKR.Fold.Consts [compile] :=\n  ⟨5, (.packed 4 (.leaf "
        "16416))⟩\n",
        "@1 cert.dagPart0 : GordieHowe.GKR.Certificate.NTree :=\n  (.node (.leaf 4114) (.leaf "
        "8450))\n",
        "@2 cert.dag : GordieHowe.GKR.Certificate.Dag [spine] :=\n  ⟨@1, 2, 4, [3], []⟩\n",
        "@3 certlayer0 : List Nat [compile] [reader] :=\n  [1053186]\n",
        "@5 cert.layered : GordieHowe.GKR.Certificate.Layered [compile] [spine] :=\n  ⟨2, [@3]⟩\n",
        "@10 cert : GordieHowe.RealizedProgram.CircuitData [spine] [reader] :=\n  ⟨2, 4, 17, 0, "
        "false, 16, 9, @0, @2, @5, @7, @8, @9⟩\n"})
    EXPECT_NE(text.find(want), std::string::npos) << want << "\n" << text;
}

TEST(GordieHoweGhc, SchemaText) {
  EXPECT_EQ(test_schema().dump(),
            "structure T.Point (params 0)\n"
            "  _ : Nat\n"
            "  _ : Int\n"
            "  _ : Bool\n"
            "inductive T.Shape (params 0)\n"
            "  | dot\n"
            "  | line T.Point T.Point\n"
            "  | poly (List T.Point) (Option String)\n"
            "  | pair (Prod Nat GordieHowe.RealizedProgram.IndexMap)\n"
            "inductive T.Tree (params 1)\n"
            "  | nil\n"
            "  | leaf #0\n"
            "  | node (T.Tree #0) (T.Tree #0)\n");
  Schema s;
  s.structure("T.Named", 1, {"x : Nat", "ys : List (Prod Nat #0)"});
  EXPECT_EQ(s.dump(),
            "structure T.Named (params 1)\n"
            "  x : Nat\n"
            "  ys : List (Prod Nat #0)\n");
  // The GKR schema is the Lean types of formal/GordieHoweNative/Data.lean:
  // a field renamed or moved, or a constructor added, on either side changes
  // the text.
  std::ifstream in(GH_GHC_SCHEMA_FILE);
  ASSERT_TRUE(in) << GH_GHC_SCHEMA_FILE;
  const std::string lean((std::istreambuf_iterator<char>(in)), {});
  EXPECT_EQ(gkr_schema().dump(), lean)
      << "the C++ schema (ghc_gkr.h) differs from " << GH_GHC_SCHEMA_FILE
      << ", the Lean types' text (formal/scripts/GhcSchema.lean)";
}

}  // namespace
}  // namespace proofs::gordiehowe::ghc
