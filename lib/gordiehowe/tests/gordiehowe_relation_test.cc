// Copyright 2026 Chad Sharp and Paul Grubbs
// SPDX-License-Identifier: Apache-2.0

// GordieHowe relations over Statement and Witness templates (relation.h;
// gordiehowe_test binary): members as handles of Statement<In>, the
// statement's views (bits, values, a public computation of its bytes),
// committed witness members (bytes and bools as Bit, integers mod p,
// negatives included), a witness member a generator reads as bytes, the
// statement node, proofs on struct values, record members (dotted names)
// and structs of more than 12 members.

#include <array>
#include <cstdint>
#include <string>
#include <vector>

#include "gordiehowe/compiler/plan_export.h"
#include "gordiehowe/compiler/plan_program.h"
#include "gordiehowe/tests/gordiehowe_test.h"
#include "gordiehowe/relation.h"

namespace proofs::gordiehowe {
namespace {

template <template <class> class F>
struct ToyStatement {
  F<std::array<uint8_t, 4>> tag;
  F<std::array<std::array<uint32_t, 3>, 2>> t;
};
template <template <class> class F>
struct ToyWitness {
  F<std::array<std::array<int16_t, 3>, 2>> s;
  F<std::array<bool, 5>> flags;
  F<std::array<uint8_t, 2>> key;
  F<std::array<uint8_t, 8>> nonce;
};

// The toy relation: t = s + 3 as integers mod p (s may be negative), the
// committed key's bits are the tag's first two bytes, the flags are bits,
// and the tag's byte sum (a public computation of the statement) is the
// sum of the key bytes and of the tag's last two bytes. A generator reads
// the nonce's bytes; nothing constrains its output.
struct Toy {
  Ref<AF> sv, flags, key, tag_sum, noise;
  std::string t_name;
  Relation<ToyStatement<Value>, ToyWitness<Value>> rel;
  Toy()
      : rel(compile<ToyStatement, ToyWitness>(
            CompileProfile{},
            [this](Sys &cs, ToyStatement<In> st, ToyWitness<In> w) {
              auto &A = cs.domain(env().profile(), "A");
              const auto &tag = st.tag;
              const auto &t = st.t;
              const auto &s = w.s;
              const auto &f = w.flags;
              const auto &k = w.key;
              const auto &nonce = w.nonce;
              t_name = st.t.name();
              const auto s_val = A.priv(Subfield<>{}, s);
              sv = s_val;
              assert_equal(s_val + 3, t.values(A), "t");
              flags = A.priv(f);
              const auto key_bits = A.priv(k);
              key = key_bits;
              const auto tag_bits = tag.bits(A);
              assert_equal(key_bits, tag_bits.slice(0, 2), "key");
              const AF *pf = &env().af;
              const auto sum = A.pub(
                  Field{}, "tag.sum", 1, depends_on(tag),
                  computes("byte-sum"), [pf](const std::vector<uint8_t> &b) {
                    uint64_t x = 0;
                    for (uint8_t c : b) x += c;
                    return Vec{pf->of_scalar(x)};
                  });
              tag_sum = sum;
              assert_equal(key_bits.from_digits(2).sum() +
                               tag_bits.slice(2, 4).from_digits(2).sum(),
                           sum, "tag.sum");
              noise = A.priv(Field{}, "noise", 1, depends_on(nonce),
                             [pf](const std::vector<uint8_t> &b) {
                               return Vec{pf->of_scalar(b.at(7))};
                             });
            },
            "gh-relation-toy")) {}
};

ToyStatement<Value> toy_statement() {
  ToyStatement<Value> st;
  st.tag = {0x5a, 0xc3, 0x01, 0x80};
  for (size_t i = 0; i < 2; ++i)
    for (size_t j = 0; j < 3; ++j) st.t[i][j] = uint32_t(10 * i + j + 1);
  return st;
}
ToyWitness<Value> toy_witness() {
  ToyWitness<Value> w;
  for (size_t i = 0; i < 2; ++i)
    for (size_t j = 0; j < 3; ++j) w.s[i][j] = int16_t(int(10 * i + j) - 2);
  w.flags = {true, false, true, true, false};
  w.key = {0x5a, 0xc3};
  for (size_t i = 0; i < 8; ++i) w.nonce[i] = uint8_t(i * 29);
  return w;
}

TEST(GordieHoweRelation, ProvesOnStructs) {
  Toy toy;
  const ToyStatement<Value> st = toy_statement();
  const ToyWitness<Value> w = toy_witness();
  SecureRandomEngine rng;
  const auto proof = toy.rel.prove(st, w, rng);
  EXPECT_TRUE(toy.rel.verify(st, proof));
  // Another statement: a value of t, or a tag byte.
  ToyStatement<Value> other = st;
  other.t[1][2] += 1;
  EXPECT_FALSE(toy.rel.verify(other, proof));
  other = st;
  other.tag[3] ^= 1;
  EXPECT_FALSE(toy.rel.verify(other, proof));
  // A witness that does not satisfy the relation has no proof that
  // verifies (the prover may refuse it).
  auto rejected = [&](const ToyWitness<Value> &bad) {
    try {
      return !toy.rel.verify(st, toy.rel.prove(st, bad, rng));
    } catch (const std::exception &) {
      return true;
    }
  };
  ToyWitness<Value> bad = w;
  bad.s[0][1] += 1;
  EXPECT_TRUE(rejected(bad));
  bad = w;
  bad.key[1] ^= 4;
  EXPECT_TRUE(rejected(bad));
  EXPECT_FALSE(rejected(w));
}

// The members' names, shapes and nodes: the statement is one Bytes node of
// its canonical bytes, declared at the first read of the statement; each
// committed witness member is a private input named after it; the views
// are public computations of the statement.
TEST(GordieHoweRelation, NamesShapesAndNodes) {
  Toy toy;
  auto &sys = toy.rel.typed<Sys>().system();
  const auto &N = sys.graph().nodes;
  EXPECT_EQ(toy.t_name, "t");
  const size_t sid = sys.statement_node();
  EXPECT_EQ(N[sid].name, "statement");
  EXPECT_EQ(N[sid].kind, Kind::kPublicInput);
  // 4 tag bytes, then 2 x 3 four-byte integers.
  EXPECT_EQ(N[sid].n, 4u + 24u);
  EXPECT_EQ(N[toy.sv.id].name, "s");
  EXPECT_EQ(N[toy.sv.id].kind, Kind::kPrivateInput);
  EXPECT_EQ(N[toy.sv.id].shape, (std::vector<size_t>{2, 3}));
  EXPECT_EQ(N[toy.flags.id].name, "flags");
  EXPECT_EQ(N[toy.flags.id].type.base, Base::kBit);
  EXPECT_EQ(N[toy.flags.id].shape, (std::vector<size_t>{5}));
  EXPECT_EQ(N[toy.key.id].shape, (std::vector<size_t>{2, 8}));
  bool bits_view = false, values_view = false, host = false;
  for (const Node &n : N) {
    bits_view |= n.name == "statement.tag.bits" &&
                 n.kind == Kind::kPublicCompute && n.cached;
    values_view |= n.name == "statement.t" && n.kind == Kind::kPublicCompute;
    host |= n.name == "nonce" && n.kind == Kind::kHostInput && n.n == 8;
  }
  EXPECT_TRUE(bits_view);
  EXPECT_TRUE(values_view);
  EXPECT_TRUE(host);
  // The statement's canonical bytes: the tag, then t little-endian.
  const auto bytes = toy.rel.typed<Sys>().bytes(toy_statement());
  ASSERT_EQ(bytes.size(), 28u);
  EXPECT_EQ(bytes[0], 0x5a);
  EXPECT_EQ(bytes[4], 1);
  EXPECT_EQ(bytes[7], 0);
}

// A member read where its role forbids it: priv of a statement member, a
// view of a witness member.
TEST(GordieHoweRelation, RolesAreChecked) {
  const auto priv_of_statement = [](Sys &cs, ToyStatement<In> st,
                                    ToyWitness<In>) {
    auto &A = cs.domain(env().profile(), "A");
    (void)A.priv(st.tag);
  };
  const auto bits_of_witness = [](Sys &cs, ToyStatement<In>,
                                  ToyWitness<In> w) {
    auto &A = cs.domain(env().profile(), "A");
    (void)w.key.bits(A);
  };
  EXPECT_THROW((void)(compile<ToyStatement, ToyWitness>(
                   {}, priv_of_statement, "gh-roles-1")),
               CompileError);
  EXPECT_THROW((void)(compile<ToyStatement, ToyWitness>(
                   {}, bits_of_witness, "gh-roles-2")),
               CompileError);
}

// A ring of any size: std::vector members whose lengths the shape values
// fix per relation, and a member check (each key below 1000).
template <template <class> class F>
struct RingStatement {
  F<std::vector<std::array<uint16_t, 3>>> keys;
};
template <template <class> class F>
struct RingWitness {
  F<std::vector<bool>> select;
  F<std::array<uint16_t, 3>> key;
};
Relation<RingStatement<Value>, RingWitness<Value>> ring_relation(size_t R) {
  RingStatement<Value> st_shape;
  st_shape.keys.resize(R);
  RingWitness<Value> w_shape;
  w_shape.select.resize(R);
  return compile<RingStatement, RingWitness>(
      CompileProfile{},
      [R](Sys &cs, RingStatement<In> st, RingWitness<In> w) {
        auto &A = cs.domain(env().profile(), "A");
        const auto &keys = st.keys;
        st.keys.check(computes("below", {1000}),
                   [](const std::vector<uint16_t> &k) {
                     for (uint16_t x : k)
                       if (x >= 1000) return false;
                     return true;
                   });
        const auto table = keys.values(A);
        const auto sel = A.priv(w.select);
        const auto k = A.priv(Subfield<>{}, w.key);
        assert_zero(sel.sum() - 1, "one");
        // The selected row: the sum over the rows of select times the row.
        for (size_t j = 0; j < 3; ++j)
          assert_equal((sel * table.at(1, j)).sum(), k[j],
                       "row" + std::to_string(j));
        EXPECT_EQ(table.dims(), (std::vector<size_t>{R, 3}));
      },
      "gh-relation-ring", st_shape, w_shape);
}

TEST(GordieHoweRelation, VectorMembersAndChecks) {
  for (size_t R : {3, 5}) {
    const auto rel = ring_relation(R);
    RingStatement<Value> st;
    for (size_t i = 0; i < R; ++i)
      st.keys.push_back({uint16_t(7 * i), uint16_t(11 * i + 1), uint16_t(i)});
    RingWitness<Value> w;
    w.select.assign(R, false);
    w.select[1] = true;
    w.key = st.keys[1];
    SecureRandomEngine rng;
    const auto proof = rel.prove(st, w, rng);
    EXPECT_TRUE(rel.verify(st, proof)) << R;
    // Another ring member's key.
    RingStatement<Value> other = st;
    other.keys[1][2] += 1;
    EXPECT_FALSE(rel.verify(other, proof)) << R;
    // A key the check refuses: the statement is rejected.
    other = st;
    other.keys[0][0] = 1000;
    EXPECT_FALSE(rel.verify(other, proof)) << R;
    EXPECT_THROW((void)rel.prove(other, w, rng), std::runtime_error) << R;
    // A ring of another size than the relation's.
    other = st;
    other.keys.push_back({1, 2, 3});
    EXPECT_THROW((void)rel.verify(other, proof), std::runtime_error) << R;
  }
}

// Record members: an attribute record (a struct of parallel vectors, whose
// length a shape value fixes) and a nested record in the statement, a
// signature record in the witness. Their members are named record.member,
// serialized in place of the record, and read as st.attr.id.
template <template <class> class F>
struct Lengths {
  F<std::vector<uint8_t>> id;
  F<std::vector<uint8_t>> value;
};
template <template <class> class F>
struct Attributes {
  F<std::vector<std::array<uint8_t, 2>>> id;
  F<std::vector<uint16_t>> value;
  Lengths<F> len;
};
template <template <class> class F>
struct RecordStatement {
  F<uint8_t> version;
  Attributes<F> attr;
};
template <template <class> class F>
struct Signature {
  F<std::array<int16_t, 3>> z;
  F<std::array<bool, 2>> h;
};
template <template <class> class F>
struct RecordWitness {
  Signature<F> issuer;
  F<uint8_t> pad;
  Signature<F> device;
};

struct Records {
  size_t n;
  std::vector<std::string> names;
  Ref<AF> issuer_z, device_h;
  Relation<RecordStatement<Value>, RecordWitness<Value>> rel;
  explicit Records(size_t attrs) : n(attrs), rel(make(attrs)) {}
  Relation<RecordStatement<Value>, RecordWitness<Value>> make(size_t attrs) {
    RecordStatement<Value> st_shape;
    st_shape.attr.id.resize(attrs);
    st_shape.attr.value.resize(attrs);
    st_shape.attr.len.id.resize(attrs);
    st_shape.attr.len.value.resize(attrs);
    return compile<RecordStatement, RecordWitness>(
        CompileProfile{},
        [this](Sys &cs, RecordStatement<In> st, RecordWitness<In> w) {
          auto &A = cs.domain(env().profile(), "A");
          names = {st.version.name(),     st.attr.id.name(),
                   st.attr.value.name(),  st.attr.len.id.name(),
                   st.attr.len.value.name(), w.issuer.z.name(),
                   w.issuer.h.name(),     w.pad.name(),
                   w.device.z.name(),     w.device.h.name()};
          st.attr.len.id.check(computes("below", {3}),
                               [](const std::vector<uint8_t> &l) {
                                 for (uint8_t x : l)
                                   if (x > 2) return false;
                                 return true;
                               });
          const auto zi = A.priv(Subfield<>{}, w.issuer.z);
          const auto zd = A.priv(Subfield<>{}, w.device.z);
          issuer_z = zi;
          device_h = A.priv(w.device.h);
          const auto hi = A.priv(w.issuer.h);
          // The attribute values are the issuer's z plus the device's.
          const auto value = st.attr.value.values(A);
          for (size_t a = 0; a < n; ++a)
            assert_equal(value[a], zi[a] + zd[a], "value" + std::to_string(a));
          assert_equal(hi, device_h, "h");
          EXPECT_EQ(st.attr.id.bits(A).dims(),
                    (std::vector<size_t>{n, 2, 8}));
          EXPECT_EQ(st.attr.len.value.dims(), (std::vector<size_t>{n}));
        },
        "gh-relation-records", st_shape, RecordWitness<Value>{});
  }
};

RecordStatement<Value> record_statement(size_t n) {
  RecordStatement<Value> st;
  st.version = 1;
  for (size_t a = 0; a < n; ++a) {
    st.attr.id.push_back({uint8_t(a), uint8_t(0xa0 + a)});
    st.attr.value.push_back(uint16_t(10 * a + 7));
    st.attr.len.id.push_back(2);
    st.attr.len.value.push_back(uint8_t(a));
  }
  return st;
}
RecordWitness<Value> record_witness(size_t n) {
  RecordWitness<Value> w;
  for (size_t a = 0; a < n; ++a) {
    w.issuer.z[a] = int16_t(10 * a + 9);
    w.device.z[a] = -2;
  }
  w.issuer.h = {true, false};
  w.device.h = {true, false};
  w.pad = 0x5c;
  return w;
}

TEST(GordieHoweRelation, RecordMembers) {
  constexpr size_t n = 3;
  Records r(n);
  EXPECT_EQ(r.names,
            (std::vector<std::string>{"version", "attr.id", "attr.value",
                                      "attr.len.id", "attr.len.value",
                                      "issuer.z", "issuer.h", "pad",
                                      "device.z", "device.h"}));
  const auto &typed = r.rel.typed<Sys>();
  const auto &N = typed.system().graph().nodes;
  EXPECT_EQ(N[r.issuer_z.id].name, "issuer.z");
  EXPECT_EQ(N[r.device_h.id].name, "device.h");
  bool id_bits = false;
  for (const Node &nd : N)
    id_bits |= nd.name == "statement.attr.id.bits";
  EXPECT_TRUE(id_bits);
  // The canonical bytes: version, then the record's members in order
  // (ids, values little-endian, the nested lengths), as plain members.
  const RecordStatement<Value> st = record_statement(n);
  const auto bytes = typed.bytes(st);
  ASSERT_EQ(bytes.size(), 1 + 2 * n + 2 * n + n + n);
  EXPECT_EQ(bytes[0], 1);
  EXPECT_EQ(bytes[1 + 2], 1);
  EXPECT_EQ(bytes[1 + 3], 0xa1);
  EXPECT_EQ(bytes[1 + 2 * n + 2], 17);
  EXPECT_EQ(bytes[1 + 4 * n], 2);
  EXPECT_EQ(bytes[1 + 5 * n + 2], 2);
  const RecordWitness<Value> w = record_witness(n);
  SecureRandomEngine rng;
  const auto proof = r.rel.prove(st, w, rng);
  EXPECT_TRUE(r.rel.verify(st, proof));
  // A value inside the record, and a nested member.
  RecordStatement<Value> other = st;
  other.attr.value[1] += 1;
  EXPECT_FALSE(r.rel.verify(other, proof));
  // The nested member's check refuses a length of 3.
  other = st;
  other.attr.len.id[2] = 3;
  EXPECT_FALSE(r.rel.verify(other, proof));
  // A record's vector of another length than the relation's.
  other = st;
  other.attr.len.value.push_back(0);
  EXPECT_THROW((void)r.rel.verify(other, proof), std::runtime_error);
  // A witness record's member is committed from its own place: a device z
  // that breaks a value has no proof that verifies.
  const auto rejected = [&](const RecordWitness<Value> &bad) {
    try {
      return !r.rel.verify(st, r.rel.prove(st, bad, rng));
    } catch (const std::exception &) {
      return true;
    }
  };
  RecordWitness<Value> bad = w;
  bad.device.z[0] = 0;
  EXPECT_TRUE(rejected(bad));
  bad = w;
  bad.issuer.h[1] = true;
  EXPECT_TRUE(rejected(bad));
}

// The plan records each member check: the program's statement lists it
// (the member's dotted name, its bytes in the statement, the check's id),
// and the statement's bytes-codec record has codec 3 and the count.
TEST(GordieHoweRelation, MemberChecksExport) {
  Records r(3);
  const auto &c = r.rel.typed<Sys>().compiled();
  const compiler::ExportMeta meta{"records", "wide", "c0ffee", "run-0", 0};
  const std::string program = compiler::export_lean_program(c, meta);
  EXPECT_NE(program.find("statement := { msgLen := 0, ctxLen := 0, checks := "
                         "[{ member := \"attr.len.id\", offset := 13, bytes "
                         ":= 3, check := \"below\", args := [3] }] }"),
            std::string::npos);
  const std::string plan = compiler::export_lean_plan(c, meta);
  EXPECT_NE(plan.find("(\"codec\", 3)"), std::string::npos);
  EXPECT_NE(plan.find("(\"checks\", 1)"), std::string::npos);
}

// More members than structured bindings of fixed arity once allowed (12):
// a Witness of 14 members, each committed and constrained.
template <template <class> class F>
struct WideStatement {
  F<std::array<uint16_t, 14>> sum;
};
template <template <class> class F>
struct WideWitness {
  F<uint16_t> m0;
  F<uint16_t> m1;
  F<uint16_t> m2;
  F<uint16_t> m3;
  F<uint16_t> m4;
  F<uint16_t> m5;
  F<uint16_t> m6;
  F<uint16_t> m7;
  F<uint16_t> m8;
  F<uint16_t> m9;
  F<uint16_t> m10;
  F<uint16_t> m11;
  F<uint16_t> m12;
  F<uint16_t> m13;
};

TEST(GordieHoweRelation, MoreThanTwelveMembers) {
  static_assert(internal::reflect::count<WideWitness<Value>>() == 14);
  std::vector<std::string> names;
  const auto rel = compile<WideStatement, WideWitness>(
      CompileProfile{},
      [&names](Sys &cs, WideStatement<In> st, WideWitness<In> w) {
        auto &A = cs.domain(env().profile(), "A");
        const auto sum = st.sum.values(A);
        const auto m = std::apply(
            [&](const auto &...x) {
              return std::vector<Ref<AF, Subfield<>, Committed>>{
                  A.priv(Subfield<>{}, x)...};
            },
            std::tie(w.m0, w.m1, w.m2, w.m3, w.m4, w.m5, w.m6, w.m7, w.m8,
                     w.m9, w.m10, w.m11, w.m12, w.m13));
        names.push_back(w.m0.name());
        names.push_back(w.m13.name());
        // Member k plus member k + 1 (mod 14) is sum[k].
        for (size_t k = 0; k < 14; ++k)
          assert_equal(m[k] + m[(k + 1) % 14], sum.slice(k, k + 1),
                       "sum" + std::to_string(k));
      },
      "gh-relation-wide");
  EXPECT_EQ(names, (std::vector<std::string>{"m0", "m13"}));
  WideWitness<Value> w;
  const std::array<uint16_t *, 14> m = {&w.m0, &w.m1, &w.m2,  &w.m3,  &w.m4,
                                        &w.m5, &w.m6, &w.m7,  &w.m8,  &w.m9,
                                        &w.m10, &w.m11, &w.m12, &w.m13};
  for (size_t k = 0; k < 14; ++k) *m[k] = uint16_t(100 + 3 * k);
  WideStatement<Value> st;
  for (size_t k = 0; k < 14; ++k)
    st.sum[k] = uint16_t(*m[k] + *m[(k + 1) % 14]);
  SecureRandomEngine rng;
  const auto proof = rel.prove(st, w, rng);
  EXPECT_TRUE(rel.verify(st, proof));
  // The last member is read from its own place.
  WideStatement<Value> other = st;
  other.sum[13] += 1;
  EXPECT_FALSE(rel.verify(other, proof));
  EXPECT_EQ(rel.typed<Sys>().witness_bytes(w).size(), 28u);
  EXPECT_EQ(rel.typed<Sys>().witness_bytes(w)[26], uint8_t(100 + 39));
}

}  // namespace
}  // namespace proofs::gordiehowe
