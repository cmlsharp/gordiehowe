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
//   GordieHoweGhc.UnknownTags the writer and the reader refuse a section
//                             flag outside kKnownFlags; the reader refuses
//                             a natural not minimally encoded (a tag, a
//                             count, a value, a flag) and a tag of more
//                             than 64 bits, which it read truncated before
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
#include <cstdlib>
#include <fstream>
#include <initializer_list>
#include <iterator>
#include <string>
#include <vector>

#include "gordiehowe/compiler/ghc.h"
#include "gordiehowe/compiler/ghc_gkr.h"
#include "gordiehowe/compiler/ghc_program.h"
#include "gordiehowe/compiler/ghc_derivs.h"
#include "gordiehowe/compiler/ghc_structure.h"
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

TEST(GordieHoweGhc, UnknownTags) {
  const Schema s = test_schema();
  const std::vector<uint8_t> pt = {0x05, 0x02, 0x01};  // ⟨5, 1, true⟩
  auto bad = [&](const std::vector<uint8_t> &x) { EXPECT_THROW(read(x, s), Error); };
  // Flags: each known combination reads, any other bit is refused by the
  // reader and the writer.
  for (uint64_t f : std::initializer_list<uint64_t>{0, 1, 4, 5}) EXPECT_NO_THROW(read(one("p", ty("T.Point"), f, pt, 3), s)) << f;
  for (uint64_t f : std::initializer_list<uint64_t>{8, 9, 64, uint64_t(1) << 20}) {
    bad(one("p", ty("T.Point"), f, pt, 3));
    File w(s);
    Bytes v;
    v.bytes(pt);
    EXPECT_THROW(w.section("p", ty("T.Point"), f, v), Error) << f;
  }
  // A flag byte 0x80 0x00 (zero, not minimal).
  {
    std::vector<uint8_t> x = {0x47, 0x48, 0x43, 0x03, 0x01, 'p', 0x00, 0x07};
    for (char ch : std::string("T.Point")) x.push_back(uint8_t(ch));
    x.insert(x.end(), {0x80, 0x00, 0x03});
    x.insert(x.end(), pt.begin(), pt.end());
    x.push_back(0x00);
    bad(x);
    x.erase(x.end() - 7);
    EXPECT_NO_THROW(read(x, s));
  }
  // Values: a Bool tag 1 as 0x81 0x00, a natural 5 as 0x85 0x00, an
  // integer 1 as 0x82 0x00, a constructor index 1 as 0x81 0x00, a spine tag
  // 0 as 0x80 0x00.
  bad(one("p", ty("T.Point"), 0, {0x05, 0x02, 0x81, 0x00}, 4));
  bad(one("p", ty("T.Point"), 0, {0x85, 0x00, 0x02, 0x01}, 4));
  bad(one("p", ty("T.Point"), 0, {0x05, 0x82, 0x00, 0x01}, 4));
  bad(one("s", ty("T.Shape"), 0, {0x81, 0x00, 0x05, 0x02, 0x01, 0x05, 0x02, 0x01}, 8));
  EXPECT_NO_THROW(read(one("s", ty("T.Shape"), 0, {0x01, 0x05, 0x02, 0x01, 0x05, 0x02, 0x01}, 7), s));
  bad(one("n", ty("Nat"), kSpine, {0x80, 0x00, 0x05}, 3));
  // A Bool tag 2^64 + 1 (ten groups): refused, not read as 1.
  std::vector<uint8_t> wide = {0x05, 0x02, 0x81};
  wide.insert(wide.end(), 8, 0x80);
  wide.push_back(0x02);
  bad(one("p", ty("T.Point"), 0, wide, wide.size()));
  // A natural value of more than 64 bits still reads.
  std::vector<uint8_t> big = {0x81};
  big.insert(big.end(), 8, 0x80);
  big.insert(big.end(), {0x02, 0x02, 0x01});
  EXPECT_NO_THROW(read(one("p", ty("T.Point"), 0, big, big.size()), s));
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

TEST(GordieHoweGhc, ExprAnn) {
  ir::Certificates c;
  c.expr_max = {0, 3, 1};
  c.expr_fields = {1, 2, 3};
  c.expr_pub = {true, false, true};
  c.expr_len = {4, 1, 0};
  c.expr_deg = {1, 0, 2};
  c.expr_zero = {false, true, false};
  const auto bytes = expr_ann_file(c, 2);
  // The kept Lean loader regression uses exactly this compiler-produced file.
  if (const char *dir = std::getenv("GH_PROGRAM_CERT_TEST_DIR")) {
    std::ofstream file(std::string(dir) + "/ExprAnn.ghc", std::ios::binary);
    file.write(reinterpret_cast<const char *>(bytes.data()), std::streamsize(bytes.size()));
    ASSERT_TRUE(file.good());
  }
  const auto sections = read(bytes, gkr_schema());
  ASSERT_EQ(sections.size(), 1u);
  EXPECT_EQ(sections[0].name, "exprAnn");
  EXPECT_EQ(sections[0].flags, uint64_t(kCompile | kReader));
  EXPECT_EQ(show(bytes, gkr_schema()),
            "@0 exprAnn : GordieHowe.RealizedProgram.ExprAnn [compile] [reader] :=\n"
            "  ⟨28, 57, 5, 12, 33, 2, 2, 2, 3, 2⟩\n");
  // A packed natural crossing a machine word: a set bit at position 80.
  c.expr_max.assign(81, 0);
  c.expr_max.back() = 1;
  EXPECT_NE(show(expr_ann_file(c, 2), gkr_schema()).find("0x100000000000000000000"),
            std::string::npos);
  // The field mask does not fit.
  EXPECT_THROW(expr_ann_file(c, 1), Error);
  // This ten-Nat structure refuses both a missing and an extra field.
  auto value = sections[0].value;
  value.pop_back();
  EXPECT_THROW(read(one("exprAnn", sections[0].type, kReader, value, value.size()),
                    gkr_schema()), Error);
  value = sections[0].value;
  value.push_back(0);
  EXPECT_THROW(read(one("exprAnn", sections[0].type, kReader, value, value.size()),
                    gkr_schema()), Error);
}

TEST(GordieHoweGhc, ProgramGenerators) {
  ir::Program p;
  p.fields.resize(1);
  using G = ir::Certificates::Gen;
  ir::Certificates c;
  c.gens = {{G::kNone}, {G::kSource}, {G::kLookupDigit, 1, 2, 0, 0, true},
            {G::kCommDigit, 3, 4, 5, 6}, {G::kSpec, 7}, {G::kStaticHist, 8, 9},
            {G::kTag, 10}, {G::kAcc, 11}, {G::kQuotDigit, 12}, {G::kDigitsAcc, 13},
            {G::kLowDigit, 14, 15}, {G::kLateHist, 16, 17}};
  // Cross the loader's old 128-element list-chaining boundary. The Lean
  // regression compares the entire emitted declaration with a literal.
  c.gens.insert(c.gens.end(), 130, G{G::kSource});
  const auto bytes = program_cert_file(c, p);
  if (const char *dir = std::getenv("GH_PROGRAM_CERT_TEST_DIR")) {
    std::ofstream file(std::string(dir) + "/Gens.ghc", std::ios::binary);
    file.write(reinterpret_cast<const char *>(bytes.data()), std::streamsize(bytes.size()));
    ASSERT_TRUE(file.good());
  }
  const auto sections = read(bytes, gkr_schema());
  ASSERT_EQ(sections.size(), 4u);
  EXPECT_EQ(sections[1].name, "gens");
  EXPECT_EQ(sections[1].flags, uint64_t(kCompile | kReader));
  const auto text = show(bytes, gkr_schema());
  EXPECT_NE(text.find("lookupDigit 1 true 2"), std::string::npos);
  EXPECT_NE(text.find("commDigit 3 4 5 6"), std::string::npos);
  EXPECT_NE(text.find("lateHist 16 17"), std::string::npos);
  // Reject an unknown constructor, a missing constructor argument, an
  // invalid Boolean and trailing data in a typed generator-list section.
  for (const std::vector<uint8_t> value : {
           std::vector<uint8_t>{1, 12}, {1, 3, 0}, {1, 2, 0, 2, 0}, {0, 1}})
    EXPECT_THROW(read(one("gens", sections[1].type, kReader, value, value.size()),
                      gkr_schema()), Error);
  c.gens = {{static_cast<G::Kind>(255)}};
  EXPECT_THROW(program_cert_file(c, p), Error);
}

TEST(GordieHoweGhc, AssignmentReadRows) {
  ir::Program p;
  p.fields.resize(1);
  p.values.resize(2);
  ir::Expr a, b, sum, ref, twice;
  a.x = 1;
  b.x = 0;
  sum.op = ir::Expr::kAdd; sum.a = 0; sum.b = 1;
  ref.op = ir::Expr::kRef; ref.x = 0;
  twice.op = ir::Expr::kAdd; twice.a = 3; twice.b = 3;
  p.nodes = {a, b, sum, ref, twice};
  p.exprs = {2};
  ir::Value bound;
  bound.kind = ir::Value::kBound; bound.expr = 4;
  p.values.push_back(bound);
  const auto bytes = program_cert_file({}, p);
  const auto sections = read(bytes, gkr_schema());
  ASSERT_EQ(sections.size(), 4u);
  EXPECT_EQ(sections[3].name, "assignmentReads");
  EXPECT_EQ(sections[3].flags, uint64_t(kCompile | kReader));
  EXPECT_NE(show(bytes, gkr_schema()).find("[[0], [1], [1, 0, 1, 0]]"),
            std::string::npos);
  for (const std::vector<uint8_t> value : {
           std::vector<uint8_t>{1}, {1, 1}, {0, 0}})
    EXPECT_THROW(read(one("assignmentReads", sections[3].type, kReader,
                          value, value.size()), gkr_schema()), Error);
}

TEST(GordieHoweGhc, CompletenessDerivations) {
  ir::Program p;
  p.fields.resize(1);
  using S = ir::Certificates::CStep;
  ir::Certificates c;
  // All compiler step constructors, including every MAC role and a long row.
  for (auto kind : {S::kSource, S::kQuotIn, S::kDigitRow, S::kPadBool, S::kHyp,
                    S::kCommIn, S::kCommRow, S::kSpecProd, S::kSpecRow,
                    S::kFieldRow, S::kTwoTail}) {
    S step;
    step.kind = kind; step.id = 7; step.slot = 2; step.j = 3;
    step.lks = {1, 2, 3};
    c.comp_derivs.push_back({step});
  }
  for (auto role : {S::kTail, S::kH, S::kAccRow, S::kGroupRow, S::kResidues,
                    S::kGqLookup, S::kQuotLookup, S::kLowLookup, S::kTopLookup, S::kWrap}) {
    S step;
    step.kind = S::kMacRow; step.id = 7; step.slot = 2;
    step.role = role; step.group = 4;
    c.comp_derivs.push_back({step});
  }
  c.comp_derivs.push_back(std::vector<S>(40));
  c.comp_derivs.resize(140);
  c.comp_ranks = {1, 2, 3};
  File file(gkr_schema());
  write_cderivs(file, c);
  const auto bytes = file.bytes();
  if (const char *dir = std::getenv("GH_PROGRAM_CERT_TEST_DIR")) {
    std::ofstream fixture(std::string(dir) + "/CDerivations.ghc", std::ios::binary);
    fixture.write(reinterpret_cast<const char *>(bytes.data()), std::streamsize(bytes.size()));
    ASSERT_TRUE(fixture.good());
  }
  const auto sections = read(bytes, gkr_schema());
  ASSERT_EQ(sections.size(), 1u);
  EXPECT_EQ(sections[0].name, "cderivs");
  EXPECT_EQ(sections[0].flags, uint64_t(kCompile | kReader));
  const auto text = show(bytes, gkr_schema());
  EXPECT_NE(text.find("(.macRow 7 2 (.groupRow 4))"), std::string::npos);
  EXPECT_NE(text.find("(.commRow 7 [1, 2, 3])"), std::string::npos);
  EXPECT_NE(text.find("0x30000000200000001"), std::string::npos);
  for (const std::vector<uint8_t> value : {
           std::vector<uint8_t>{1, 1, 14}, {1, 1, 5, 0, 0, 10}, {1, 1, 3}, {0, 0, 0}})
    EXPECT_THROW(read(one("cderivs", sections[0].type, kReader, value, value.size()),
                      gkr_schema()), Error);
  S bad;
  bad.kind = static_cast<S::Kind>(255);
  c.comp_derivs = {{bad}};
  EXPECT_THROW(program_cert_file(c, p), Error);
  bad.kind = S::kMacRow; bad.role = static_cast<S::MacRole>(255);
  c.comp_derivs = {{bad}};
  EXPECT_THROW(program_cert_file(c, p), Error);
  c.comp_derivs.clear(); c.comp_ranks = {uint64_t(UINT32_MAX) + 1};
  EXPECT_THROW(program_cert_file(c, p), Error);
}

TEST(GordieHoweGhc, RealizationDerivations) {
  ir::Program p;
  ir::Certificates c;
  p.index_maps.push_back({});
  p.coefs.push_back({true, "18446744073709551617"});
  p.coefs.push_back({false, "", 2, 3});
  p.linears.push_back({{{0, 0}, {1, 1}}});
  using O = ir::NamedOp;
  for (auto kind : {O::kNegacyclicConv, O::kPolyMatVec, O::kPolyBroadcast, O::kNtt,
                    O::kInverseNtt, O::kNttTranspose, O::kRowDot, O::kMacConv,
                    O::kAcyclicConv, O::kDiagonal, O::kScale, O::kConstDiagonal,
                    O::kSum, O::kFromDigits, O::kBatched}) {
    O op; op.kind = kind; op.value = 7; op.nats = {2, 3}; op.elt = "65537";
    op.ntt_form = true; op.natural_order = true; op.taps = {0, 2, 5}; op.inner = 0;
    p.ops.push_back(op);
  }
  using E = ir::Expr;
  E leaf; leaf.op = E::kLeaf; leaf.x = 1; p.nodes.push_back(leaf);
  for (auto op : {E::kAdd, E::kSub, E::kScale, E::kMul, E::kReindex, E::kConcat,
                  E::kLinear, E::kProd, E::kMux, E::kApply, E::kRef, E::kLogic}) {
    E e; e.op = op; e.x = 0; e.a = 0; e.b = 0; e.c = 0;
    e.logic = ir::LogicOp::kEq; e.args = {0, 0};
    p.nodes.push_back(e);
  }
  for (size_t i = 0; i < p.ops.size(); ++i) {
    E e; e.op = E::kApply; e.x = i; e.a = 0; p.nodes.push_back(e);
  }
  for (size_t i = 0; i < p.nodes.size(); ++i) {
    ir::DExpr e; e.kind = ir::DExpr::kProgram; e.id = i; c.exprs.push_back(e);
  }
  using S = ir::DStep;
  std::vector<S> steps;
  for (auto rule : {S::kRealized, S::kSubst, S::kLinear, S::kLookup, S::kRangeNat,
                    S::kHoldsIn, S::kSrc, S::kIvlNat, S::kIvlExpr, S::kIvlMeet,
                    S::kNatIvl, S::kNatComp, S::kNatBool, S::kNatLin, S::kLiftConst,
                    S::kFieldDvd, S::kGroupedMod, S::kIvlApply, S::kIvlLogic,
                    S::kFact, S::kTransport, S::kLift, S::kDigits, S::kCongr,
                    S::kMac, S::kLinop, S::kConclude, S::kHyp, S::kIvlDisjoint,
                    S::kCircuitAssert, S::kInputPremise}) {
    S s; s.rule = rule; s.id = 7; s.premises = {0, 1, 2}; s.coeffs = {"-4", "0", "7"};
    s.exprs = {0, 1}; s.ints = {"5", "12", "2"}; s.members = {{{1, 2, 3}}};
    s.tails = {1, 2}; s.h = 3; s.src_arg = 2; s.in_dom = 1;
    steps.push_back(s);
  }
  for (auto src : {S::kConst, S::kDeclared, S::kNat, S::kPrime, S::kOpaqueBit,
                   S::kQuadRoot, S::kRootSet, S::kShift, S::kTableHull}) {
    S s; s.rule = S::kSrc; s.id = 3; s.src = src; s.src_arg = 2; s.premises = {0};
    s.tails = {1, 2}; s.ints = {"-18446744073709551617", "9", "2"}; steps.push_back(s);
  }
  for (size_t i = 0; i < c.exprs.size(); ++i) {
    S s; s.rule = S::kIvlExpr; s.exprs = {ir::Id(i)}; s.ints = {"-1", "65537"};
    steps.push_back(s);
  }
  c.derivations = {steps};
  for (size_t i = 0; i < 140; ++i) c.deriv_ranks.push_back(i);
  c.shared.push_back({0, 0, "-5", "9", 2, {steps[0]}});
  c.circuit_derivs.push_back({2, {{3, {steps.back()}}}});
  const auto bytes = derivations_file(p, c);
  const auto sections = read(bytes, gkr_schema());
  ASSERT_EQ(sections.size(), 4u);
  for (const auto &s : sections) EXPECT_EQ(s.flags, uint64_t(kCompile | kReader));
  EXPECT_EQ(sections[0].name, "derivs");
  EXPECT_EQ(sections[1].name, "ranks");
  EXPECT_EQ(sections[2].name, "shared");
  EXPECT_EQ(sections[3].name, "circuitDerivs");
  const auto text = show(bytes, gkr_schema());
  EXPECT_NE(text.find("(.inDom 1 (.fact 7))"), std::string::npos);
  EXPECT_NE(text.find("(.reindex idx0 (.leaf 1))"), std::string::npos);
  if (const char *dir = std::getenv("GH_PROGRAM_CERT_TEST_DIR")) {
    std::ofstream fixture(std::string(dir) + "/Derivations.ghc", std::ios::binary);
    fixture.write(reinterpret_cast<const char *>(bytes.data()), std::streamsize(bytes.size()));
    ASSERT_TRUE(fixture.good());
    std::ofstream literal(std::string(dir) + "/DerivationsLiteral.txt");
    literal << compiler::print_derivations(p, c);
    ASSERT_TRUE(literal.good());
  }
  auto truncated = sections[0].value; truncated.pop_back();
  EXPECT_THROW(read(one("derivs", sections[0].type, kReader, truncated, truncated.size()),
                    gkr_schema()), Error);
  const std::vector<uint8_t> bad_tag{1, 0, 1, 34};
  EXPECT_THROW(read(one("derivs", sections[0].type, kReader, bad_tag, bad_tag.size()),
                    gkr_schema()), Error);
  S bad; bad.rule = S::kIvlSolve; c.derivations = {{bad}};
  EXPECT_THROW(derivations_file(p, c), Error);
  bad.rule = static_cast<S::Rule>(255); c.derivations = {{bad}};
  EXPECT_THROW(derivations_file(p, c), Error);
  Bytes decimal;
  for (const std::string invalid : {"", "-", "+1", "1x", "-1"})
    EXPECT_THROW(write_decimal(decimal, invalid), Error);
}

TEST(GordieHoweGhc, StructureRecords) {
  using R = compiler::StructureRecords;
  using K = R::GadgetKind;
  using P = R::GadgetPart::Kind;
  using T = R::Route::Kind;
  using I = R::IvlSource::Kind;
  ir::Program program;
  program.index_maps.push_back({});
  ir::Expr leaf; leaf.op = ir::Expr::kLeaf; leaf.x = 3;
  program.nodes.push_back(leaf);
  ir::Expr reindex; reindex.op = ir::Expr::kReindex; reindex.x = 0; reindex.a = 0;
  program.nodes.push_back(reindex);
  R r;
  for (auto k : {K::selectRow, K::selectFirst, K::keccak,
                 K::macSite, K::modField, K::modCommitted, K::modGrouped,
                 K::modDigits, K::modOneDigit, K::lookupTwoSided, K::lookupDigits,
                 K::packedTable})
    r.gadgets.push_back({k, {0, 1}, {2, 3}, {4, 5}, {}});
  r.gadgets[0].parts = {{P::expr, {1}, {}}, {P::stream, {2}, {}},
                        {P::stream, {2}, 3}};
  r.origins = {{0, {1, 2}}, {3, {4, 5}}};
  for (size_t n = 0; n < 140; ++n) r.messages.push_back({n, n + 1});
  r.bound_recs = {{1, 2}};
  r.member_values = {{3, 4}};
  r.routes = {{0, {T::affine, {}, false}}, {1, {T::affine, {}, true}},
              {2, {T::quadratic, {}}}, {3, {T::batch, {1, 2}}},
              {4, {T::gkr, {3, 4}}}, {5, {T::realized, {5, 6, 7}}},
              {6, {T::realized, {8}}}};
  r.logup_hosts = {{{1, 2}, {3, 4}}};
  r.mac_hosts = {{5, {6, 7}}};
  r.chal_values = {{8, 9}};
  r.ivl_sources = {{0, {I::constant, {}}}, {1, {I::opaqueBit, {}}},
                   {2, {I::declared, {0}}}, {3, {I::shiftRange, {1}}},
                   {4, {I::range, {2}}}, {5, {I::quadRoot, {3, 4}}},
                   {6, {I::rootSet, {5, 6}}}, {7, {I::rootSet, {}}},
                   {8, {I::prime, {}}}};
  r.table_gadgets = {{1, 2}};
  r.mac_requests = {{3, {4, 5, 6}}};
  r.mod_requests = {{7, {8, 9}}};
  const auto bytes = structure_file(program, r);
  const auto sections = read(bytes, gkr_schema());
  ASSERT_EQ(sections.size(), 1u);
  EXPECT_EQ(sections[0].name, "records");
  EXPECT_EQ(sections[0].flags, uint64_t(kCompile | kReader));
  EXPECT_EQ(sections[0].type.text(), "GordieHowe.RealizedProgram.Structure");
  EXPECT_NE(show(bytes, gkr_schema()).find("(.reindex idx0 (.leaf 3))"), std::string::npos);
  if (const char *dir = std::getenv("GH_PROGRAM_CERT_TEST_DIR")) {
    std::ofstream fixture(std::string(dir) + "/Structure.ghc", std::ios::binary);
    fixture.write(reinterpret_cast<const char *>(bytes.data()), std::streamsize(bytes.size()));
    ASSERT_TRUE(fixture.good());
    std::ofstream literal(std::string(dir) + "/StructureLiteral.txt");
    literal << "def records : RealizedProgram.Structure where\n" << compiler::print_structure(r, program);
    ASSERT_TRUE(literal.good());
  }
  auto truncated = sections[0].value; truncated.pop_back();
  EXPECT_THROW(read(one("records", sections[0].type, kReader, truncated, truncated.size()),
                    gkr_schema()), Error);
  auto bad_tag = sections[0].value; bad_tag[1] = 127;
  EXPECT_THROW(read(one("records", sections[0].type, kReader, bad_tag, bad_tag.size()),
                    gkr_schema()), Error);
  auto rejects = [&](const R &bad) {
    EXPECT_THROW(structure_file(program, bad), Error);
    EXPECT_THROW(compiler::print_structure(bad, program), std::runtime_error);
  };
  R bad = r; bad.gadgets[0].kind = static_cast<K>(255); rejects(bad);
  bad = r; bad.gadgets[0].parts[0].kind = static_cast<P>(255); rejects(bad);
  bad = r; bad.gadgets[0].parts[1].args.pop_back(); rejects(bad);
  bad = r; bad.gadgets[0].parts[0].zero_slot = 1; rejects(bad);
  bad = r; bad.gadgets[0].parts[0].args = {size_t(UINT32_MAX) + 1}; rejects(bad);
  bad = r; bad.routes[0].second.kind = static_cast<T>(255); rejects(bad);
  bad = r; bad.routes[2].second.on_views = true; rejects(bad);
  bad = r; bad.routes[3].second.args.pop_back(); rejects(bad);
  bad = r; bad.routes[5].second.args.clear(); rejects(bad);
  bad = r; bad.ivl_sources[0].second.kind = static_cast<I>(255); rejects(bad);
  bad = r; bad.ivl_sources[5].second.args.pop_back(); rejects(bad);
  bad = r; bad.origins[1].first = 0; rejects(bad);
  bad = r; std::swap(bad.routes[0], bad.routes[1]); rejects(bad);
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

TEST(GordieHoweGhc, HonestNodes) {
  const std::vector<std::pair<size_t, std::string>> nodes = {
      {0, "GF(p^1)"}, {1, "bit"}, {12, "quote\"slash\\line\nλ"}};
  const auto bytes = honest_nodes_file(nodes);
  if (const char *dir = std::getenv("GH_PROGRAM_CERT_TEST_DIR")) {
    std::ofstream file(std::string(dir) + "/Nodes.ghc", std::ios::binary);
    file.write(reinterpret_cast<const char *>(bytes.data()), std::streamsize(bytes.size()));
    ASSERT_TRUE(file.good());
  }
  const auto sections = read(bytes, gkr_schema());
  ASSERT_EQ(sections.size(), 1u);
  EXPECT_EQ(sections[0].name, "nodes");
  EXPECT_EQ(sections[0].flags, uint64_t(kCompile | kReader));
  EXPECT_EQ(sections[0].type, ty("List (Prod Nat String)"));
  EXPECT_EQ(read(honest_nodes_file({}), gkr_schema()).size(), 1u);
  auto value = sections[0].value;
  value.pop_back();
  EXPECT_THROW(read(one("nodes", sections[0].type, kReader, value, value.size()),
                    gkr_schema()), Error);
  value = sections[0].value;
  value.push_back(0);
  EXPECT_THROW(read(one("nodes", sections[0].type, kReader, value, value.size()),
                    gkr_schema()), Error);
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
