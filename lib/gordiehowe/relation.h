// Copyright 2026 Chad Sharp and Paul Grubbs
// SPDX-License-Identifier: Apache-2.0

// GordieHowe: a relation over a Statement and a Witness struct.
//
// A Statement and a Witness are aggregate templates over a member
// wrapper F, each member F<T> with T std::arrays and std::vectors (nested
// to any depth) of integers, bytes, bools or field elements; the member
// types give the shapes. Statement<Value> (Value<T> is T) is the plain
// data a proof is made and checked on; Statement<In> holds the relation's
// handles on its members, each an In<T> named after its member.
// compile<Statement, Witness>(profile, fn[, name]) builds the system FN
// declares, fn(ConstraintSystem &cs, Statement<In> st, Witness<In> w),
// lowers and compiles it, and returns a relation that proves and verifies
// on Statement<Value> and Witness<Value>:
//
//   template <template <class> class F>
//   struct Statement {
//     F<std::array<uint8_t, 32>> h;
//   };
//   template <template <class> class F>
//   struct Witness {
//     F<std::array<uint8_t, 512>> enc;
//     F<std::array<std::array<int32_t, 256>, 4>> s2;
//   };
//   auto r = compile<Statement, Witness>(
//       profile, [&](ConstraintSystem<Hash, HF, AF> &cs,
//                    Statement<In> st, Witness<In> w) {
//         auto &H = cs.domain(h_profile, "H");
//         auto &A = cs.domain(a_profile, "A");
//         // Bit [512, 8]: each byte's bits, least significant first
//         auto bits = H.priv(w.enc);
//         // integers mod q, a negative v as q - |v|
//         auto s = A.priv(Subfield<>{}, w.s2);
//         assert_equal(digest_of(bits), st.h.bits(H).flat());
//       });
//   const auto proof = r.prove(statement, witness, rng);
//   const bool ok = r.verify(statement, proof);
//
// A member may be a record: R<F> m for a template R of the same form,
// whose members may be records in turn. Its members are members of the
// struct named m.a, m.b, ... (the dotted name is the member's node name),
// serialized in place of m, and the relation reads them as st.m.a. A
// record groups members that belong together, as an mDL's attribute
// identifiers, values and their lengths:
//
//   template <template <class> class F>
//   struct Attributes {
//     F<std::vector<std::array<uint8_t, 32>>> id;
//     F<std::vector<uint8_t>> id_len;
//   };
//   template <template <class> class F>
//   struct Statement {
//     // the members attr.id and attr.id_len
//     Attributes<F> attr;
//   };
//
// The members of both instantiations are enumerated alike (initializer
// counting and structured bindings), so each handle reads the value at its
// own index; a struct has any number of members. A std::vector member's
// length is fixed per relation by shape
// values that compile() takes, compile<Statement, Witness>(profile, fn,
// name, st_shape, w_shape), so one relation serves rings or messages of
// any length chosen at run time.
//
// Statement. The whole statement is serialized canonically and absorbed
// into the transcript before any commitment, as Bytes statements are: the
// members in declaration order, each integer little-endian in its width,
// each bool one byte (0 or 1), each field element by its field's
// to_bytes_field. It is one Bytes statement named "statement", which the
// system declares where the relation first reads the statement (after the
// relation when it never does), in the field of its first binary domain,
// else its first domain. A member is read through explicit views, each a
// cached public computation of the statement:
//   m.bits(D)     Ref<F, Bit, Public>: each integer's bits, least
//                 significant first, shape [dims..., 8 * width]; a bool's
//                 one bit, shape [dims...]; named statement.<m>.bits
//   m.values(D)   Ref<F, Subfield<>, Public>: the integers mod p (odd
//                 characteristic; a negative v is p - |v|), or for field
//                 elements Ref<F, Field, Public>; shape [dims...]; named
//                 statement.<m>
//   depends_on(m) a public computation's closure receives the member's
//                 canonical bytes (decode(m) as D.pub(..., depends_on(m),
//                 id, fn))
//   m.check(id, pred), m.check(D, id, pred)
//                 the member's codec: pred reads its integers (or its
//                 elements of D's field) and is true when the member is
//                 well formed; a statement it refuses is rejected
//   m.check_value(v, id, pred)
//                 the same codec, recorded against the public value named
//                 v that the program computes from the member
// Witness. A member is committed explicitly, as a private input named
// after it:
//   D.priv(m)     bytes and bools as Bit (bytes [dims..., 8], least
//                 significant bit first; bools [dims...]), field elements
//                 as Field
//   D.priv(T{}, m)  as type T: Bit (any integer's bits, as bits() reads
//                 them), Subfield<E> or Field (integers mod p, odd
//                 characteristic; field elements of D's field as they
//                 are)
//   depends_on(m) a generator's closure receives the member's canonical
//                 bytes, through a host input named after the member
//                 (generators only: no constraint reads it)
// The integer conversions run without a branch on a witness value (ct.h);
// an integer whose magnitude is not below p is an error after the whole
// conversion. Computed values keep the value forms (D.priv with depends_on
// and a closure), as do challenges.

#ifndef PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_RELATION_H_
#define PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_RELATION_H_

#include <array>
#include <chrono>
#include <cstddef>
#include <cstdint>
#include <functional>
#include <map>
#include <memory>
#include <stdexcept>
#include <string>
#include <string_view>
#include <tuple>
#include <type_traits>
#include <utility>
#include <vector>

#include "gordiehowe/core.h"
#include "gordiehowe/ct.h"
#include "gordiehowe/domain.h"
#include "gordiehowe/system.h"
#include "gordiehowe/system_core.h"
#include "random/random.h"

namespace proofs::gordiehowe {

// The instantiations of a Statement or Witness template S: S<Value> holds
// the data (Value<T> is T), S<In> the relation's handles on its members.
template <class T>
using Value = T;

namespace internal {

// ------------------------------------------------------------ reflection
// An aggregate's members without macros: its member count by the number of
// initializers it accepts, its members by structured bindings, and their
// names from the signature of a function templated on a member's address.
namespace reflect {

struct Any {
  template <class T>
  operator T() const;  // NOLINT
};
template <class T, size_t... I>
constexpr bool init_with(std::index_sequence<I...>) {
  return requires { T{(void(I), Any{})...}; };
}
// The number of members of the aggregate T.
template <class T, size_t N = 0>
constexpr size_t count() {
  if constexpr (init_with<T>(std::make_index_sequence<N + 1>{}))
    return count<T, N + 1>();
  else
    return N;
}
// The members of T, as a tuple of references (a structured binding pack,
// a C++26 feature clang accepts in C++23 as an extension).
#if defined(__clang__)
#pragma clang diagnostic push
#pragma clang diagnostic ignored "-Wc++26-extensions"
#endif
template <class T>
constexpr auto tie(T &t) {
  if constexpr (count<std::remove_cv_t<T>>() == 0) {
    return std::tuple<>();
  } else {
    auto &[... m] = t;
    return std::tie(m...);
  }
}
#if defined(__clang__)
#pragma clang diagnostic pop
#endif
// The type of member I of T.
template <class T, size_t I>
using member_t = std::remove_cvref_t<
    std::tuple_element_t<I, decltype(tie(std::declval<T &>()))>>;
template <class T>
struct Wrap {
  T value;
};
// An object whose members' addresses name them; never defined.
#if defined(__clang__)
#pragma clang diagnostic push
#pragma clang diagnostic ignored "-Wundefined-var-template"
#endif
template <class T>
extern const Wrap<T> fake;
template <auto P>
consteval std::string_view pretty() {
  return __PRETTY_FUNCTION__;
}
// The name of member I of T: the last identifier of the address in
// pretty's signature ("... [P = &fake<T>.value.h]").
template <class T, size_t I>
consteval std::string_view name() {
  constexpr std::string_view s = pretty<&std::get<I>(tie(fake<T>.value))>();
  constexpr size_t end = s.rfind(']');
  constexpr size_t dot = s.rfind('.', end);
  return s.substr(dot + 1, end - dot - 1);
}
#if defined(__clang__)
#pragma clang diagnostic pop
#endif

}  // namespace reflect

// ------------------------------------------------------------ records
// A record member: R<Value> for a template R of the Statement's form
// (template <template <class> class F> struct R { F<...> a; ... };),
// declared in a Statement or Witness as R<F> m. Its members are members of
// the struct, named m.a, ..., to any depth.
template <class M>
struct RecordOf {
  static constexpr bool kRecord = false;
};
template <template <template <class> class> class R>
struct RecordOf<R<Value>> {
  static constexpr bool kRecord = true;
  template <template <class> class G>
  using With = R<G>;
};
template <class M>
constexpr bool kRecordMember = RecordOf<M>::kRecord;
// The number of plain members of T, a record's counted through its own.
template <class T>
constexpr size_t plain_count();
template <class M>
constexpr size_t plain_count_of() {
  if constexpr (kRecordMember<M>)
    return plain_count<M>();
  else
    return 1;
}
template <class T>
constexpr size_t plain_count() {
  return []<size_t... I>(std::index_sequence<I...>) {
    return (plain_count_of<reflect::member_t<T, I>>() + ... + size_t{0});
  }(std::make_index_sequence<reflect::count<T>()>{});
}
// The index among T's plain members of the first plain member of member I.
template <class T, size_t I>
constexpr size_t plain_index() {
  return []<size_t... J>(std::index_sequence<J...>) {
    return (plain_count_of<reflect::member_t<T, J>>() + ... + size_t{0});
  }(std::make_index_sequence<I>{});
}
// The member of T at PATH (member indices, outermost first).
template <class T, size_t I, size_t... Rest>
const auto &member_at(const T &t) {
  const auto &m = std::get<I>(reflect::tie(t));
  if constexpr (sizeof...(Rest) == 0)
    return m;
  else
    return member_at<std::remove_cvref_t<decltype(m)>, Rest...>(m);
}
// FN(m) for each plain member m of the value T, in declaration order, a
// record's members in place of the record.
template <class T, class Fn>
void for_each_plain(T &t, Fn &&fn) {
  std::apply(
      [&](auto &...m) {
        (
            [&](auto &x) {
              if constexpr (kRecordMember<std::remove_cvref_t<decltype(x)>>)
                for_each_plain(x, fn);
              else
                fn(x);
            }(m),
            ...);
      },
      reflect::tie(t));
}

// ------------------------------------------------------- member types
// A member of type M: nested std::arrays and std::vectors of a leaf
// type. An array's length is part of its type; a vector's is fixed per
// relation by the shape value compile() takes.
template <class M>
struct ArrayOf {
  using Leaf = M;
  static constexpr bool kSized = true;
  static void dims(const M *, std::vector<size_t> &) {}
};
template <class T, size_t N>
struct ArrayOf<std::array<T, N>> {
  using Leaf = typename ArrayOf<T>::Leaf;
  static constexpr bool kSized = ArrayOf<T>::kSized;
  static void dims(const std::array<T, N> *m, std::vector<size_t> &d) {
    d.push_back(N);
    ArrayOf<T>::dims(m == nullptr || N == 0 ? nullptr : &(*m)[0], d);
  }
};
template <class T, class A>
struct ArrayOf<std::vector<T, A>> {
  using Leaf = typename ArrayOf<T>::Leaf;
  static constexpr bool kSized = false;
  static void dims(const std::vector<T, A> *m, std::vector<size_t> &d) {
    if (m == nullptr)
      fail("a Statement or Witness member is a std::vector: compile() "
           "takes a shape value that fixes its length");
    d.push_back(m->size());
    if constexpr (!ArrayOf<T>::kSized) {
      if (m->empty())
        fail("a Statement or Witness member's shape holds an empty "
             "std::vector of std::vectors");
      // Every entry has the first one's shape (the conversions check the
      // number of leaves).
      ArrayOf<T>::dims(&(*m)[0], d);
    } else {
      ArrayOf<T>::dims(nullptr, d);
    }
  }
};
template <class M>
using LeafOf = typename ArrayOf<M>::Leaf;
// The member's axes (a lone value is [1]), the vectors' lengths read from
// SHAPE (none is needed when every length is in the type).
template <class M>
std::vector<size_t> dims_of(const M *shape = nullptr) {
  std::vector<size_t> d;
  ArrayOf<M>::dims(shape, d);
  if (d.empty()) d.push_back(1);
  return d;
}
// FN(leaf) for each leaf of M, in row-major order.
template <class M, class Fn>
void for_each_leaf(const M &m, Fn &&fn) {
  if constexpr (std::is_same_v<M, LeafOf<M>>) {
    fn(m);
  } else {
    for (const auto &x : m) for_each_leaf(x, fn);
  }
}
// The number of coordinates of axes DIMS.
inline size_t count_of_dims(const std::vector<size_t> &dims) {
  size_t n = 1;
  for (size_t d : dims) n *= d;
  return n;
}
// The number of leaves of the value M.
template <class M>
size_t leaves_in(const M &m) {
  size_t n = 0;
  for_each_leaf(m, [&n](const auto &) { ++n; });
  return n;
}
template <class L>
constexpr bool kIntegerLeaf = std::is_integral_v<L>;
// An integer leaf's canonical width in bytes (a bool's is 1).
template <class L>
constexpr size_t integer_width() {
  return std::is_same_v<L, bool> ? 1 : sizeof(L);
}
// The field of the system whose elements L is: the one F of FS with
// F::Elt = L.
template <class L, class... Fs>
struct FieldOfElt {
  static constexpr size_t kMatches =
      (size_t(std::is_same_v<typename Fs::Elt, L>) + ... + 0);
  static_assert(kMatches == 1,
                "a Statement or Witness member's leaves are integers, bools "
                "or the elements of exactly one of the system's fields");
  template <class G>
  using Match = std::conditional_t<std::is_same_v<typename G::Elt, L>,
                                   std::tuple<G>, std::tuple<>>;
  using type = std::tuple_element_t<
      0, decltype(std::tuple_cat(std::declval<Match<Fs>>()...))>;
};

// The field of the system of field set S whose elements L is.
template <class L, class S>
struct ElementField;
template <class L, class H, class... Fs>
struct ElementField<L, FieldSet<H, Fs...>> : FieldOfElt<L, Fs...> {};
// An integer leaf's unsigned type (a bool's is one byte).
template <class L>
struct UnsignedOf {
  using type = std::make_unsigned_t<L>;
};
template <>
struct UnsignedOf<bool> {
  using type = uint8_t;
};

// A member's canonical bytes: integers little-endian in their width, bools
// one byte, field elements by FIELD's to_bytes_field (FIELD the system's
// field of that element type; unused for integers).
template <class M, class Field>
void put_member(std::vector<uint8_t> &out, const M &m, const Field *field) {
  using L = LeafOf<M>;
  for_each_leaf(m, [&](const L &x) {
    if constexpr (std::is_same_v<L, bool>) {
      out.push_back(uint8_t(x ? 1 : 0));
    } else if constexpr (kIntegerLeaf<L>) {
      using U = std::make_unsigned_t<L>;
      const U u = U(x);
      for (size_t b = 0; b < sizeof(L); ++b)
        out.push_back(uint8_t(uint64_t(u) >> (8 * b)));
    } else {
      uint8_t buf[Field::kBytes];
      field->to_bytes_field(buf, x);
      out.insert(out.end(), buf, buf + Field::kBytes);
    }
  });
}

// The integer leaf X as an element of F: X mod p, a negative X as p - |X|,
// with OK cleared when |X| is not below p (no branch on X).
template <class F, class L>
typename F::Elt integer_elt(const F &f, L x, uint64_t &ok) {
  static_assert(sizeof(L) <= 8, "integers of at most 64 bits");
  uint64_t mag = uint64_t(x), neg = 0;
  if constexpr (std::is_signed_v<L>) {
    const uint64_t s = uint64_t(int64_t(x) >> 63);
    mag = (uint64_t(int64_t(x)) ^ s) - s;
    neg = s & 1;
  }
  // MAG is below 2^64; p beyond 128 bits exceeds it (a public choice).
  const Bound pb = field_characteristic(f);
  const uint64_t below =
      pb.fits128() ? ct::lt128(NatInt(mag), static_cast<NatInt>(pb)) : 1;
  ok &= below;
  const auto e = elt_of_nat(f, NatInt(mag) & ct::mask128(below));
  // e, or -e when negative: e + neg (-e - e).
  return f.addf(e, f.mulf(ct::bit_elt(f, neg), f.subf(f.negf(e), e)));
}

// A member converted to the elements of F a committed value of type T
// holds (Domain::priv(T{}, m)), NAME naming it in errors.
template <class F, class T, class M>
std::vector<typename F::Elt> member_elements(const F &f, const M &m,
                                             const std::string &name) {
  using L = LeafOf<M>;
  std::vector<typename F::Elt> out;
  if constexpr (is_bit_v<T>) {
    static_assert(kIntegerLeaf<L>,
                  "priv(Bit{}, m): the member's leaves are integers, bytes "
                  "or bools");
    for_each_leaf(m, [&](const L &x) {
      if constexpr (std::is_same_v<L, bool>) {
        out.push_back(ct::bit_elt(f, uint64_t(x)));
      } else {
        using U = std::make_unsigned_t<L>;
        const uint64_t u = uint64_t(U(x));
        for (size_t j = 0; j < 8 * sizeof(L); ++j)
          out.push_back(ct::bit_elt(f, (u >> j) & 1));
      }
    });
  } else if constexpr (kIntegerLeaf<L>) {
    static_assert(!F::kCharacteristicTwo,
                  "priv(Subfield/Field, m) of integers: integers mod p exist "
                  "in odd characteristic; commit a binary field's bits with "
                  "Bit{}");
    uint64_t ok = 1;
    for_each_leaf(m, [&](const L &x) { out.push_back(integer_elt(f, x, ok)); });
    if (!ok)
      throw std::runtime_error("witness member '" + name +
                               "': an integer's magnitude is not below p");
  } else {
    static_assert(std::is_same_v<L, typename F::Elt>,
                  "priv(T{}, m): the member's leaves are integers, bools or "
                  "elements of the domain's field");
    for_each_leaf(m, [&](const L &x) { out.push_back(x); });
  }
  return out;
}
// The shape of a member of axes D committed as type T.
template <class T, class M>
Shape member_shape(std::vector<size_t> d) {
  using L = LeafOf<M>;
  if constexpr (is_bit_v<T> && kIntegerLeaf<L> && !std::is_same_v<L, bool>)
    d.push_back(8 * sizeof(L));
  return Shape(d);
}

// What the members of one input struct share: the system, which struct it
// is (statement or witness), each member's name and canonical byte range,
// and what proving fills from a witness value.
struct InputState {
  SystemCore *sys = nullptr;
  bool witness = false;
  std::vector<std::string> names;
  std::vector<std::vector<size_t>> dims;
  std::vector<size_t> offset, len;
  // A committed witness member: its node and its elements from the struct
  // value (a std::vector of its field's elements).
  struct Fill {
    size_t node;
    std::function<std::shared_ptr<void>(const void *)> elements;
  };
  std::vector<Fill> fills;
  // Witness members read as bytes: each member's host input.
  std::map<size_t, HostInput> hosts;
  // The struct value's canonical bytes.
  std::function<std::vector<uint8_t>(const void *)> bytes;
};

// The members' system-side access (SystemCore's statement node).
struct RelationAccess {
  static void request_statement(SystemCore &s, size_t n) {
    s.statement_bytes_ = n;
  }
  static HostInput host_input(SystemCore &s, const std::string &nm, size_t n) {
    return s.root().host_input(nm, n);
  }
  // A check of the statement's bytes [OFFSET, OFFSET + LEN), member
  // MEMBER's: ID enters the statement node's description, and PRED runs on
  // the range whenever a statement is prepared; a range PRED refuses
  // rejects the statement. The plan records the check, and the statement's
  // bytes-codec record has codec 3 (member checks) and their count.
  static void check(SystemCore &s, const std::string &member, size_t offset,
                    size_t len, const Computes &id,
                    std::function<bool(const std::vector<uint8_t> &)> pred) {
    const size_t node = s.statement_node();
    PlanRecords &rec = s.mutable_graph().records;
    PlanRecords::MemberCheck mc{member, id.name, offset, len, {}};
    for (size_t k = 0; k + 8 <= id.params.size(); k += 8) {
      uint64_t v = 0;
      for (size_t b = 0; b < 8; ++b)
        v |= uint64_t(id.params[k + b]) << (8 * b);
      mc.args.push_back(v);
    }
    rec.member_checks.push_back(std::move(mc));
    for (auto &g : rec.gadgets) {
      if (g.kind != "bytes-codec" ||
          g.name != s.mutable_graph().nodes.at(node).name)
        continue;
      std::erase_if(g.params,
                    [](const auto &p) { return p.first == "checks"; });
      for (auto &p : g.params)
        if (p.first == "codec") p.second = 3;
      g.params.push_back({"checks", SignedInt(rec.member_checks.size())});
    }
    std::vector<uint8_t> &d = s.mutable_graph().nodes.at(node).descr;
    put_str(d, "check");
    put_u64(d, offset);
    put_u64(d, len);
    put_str(d, id.name);
    put_u64(d, id.params.size());
    d.insert(d.end(), id.params.begin(), id.params.end());
    s.statement_checks_->push_back({offset, len, std::move(pred)});
    s.statement_codec(
        node, [checks = s.statement_checks_](const std::vector<uint8_t> &b) {
          for (const auto &c : *checks) {
            const std::vector<uint8_t> r(b.begin() + long(c.offset),
                                         b.begin() + long(c.offset + c.len));
            if (!c.pred(r)) return kRejected;
          }
          return kAccepted;
        });
  }
};

}  // namespace internal

// ---------------------------------------------------------------- In --

// A member of type M of a Statement or Witness struct (the header comment
// lists its uses).
template <class M>
class In {
 public:
  using Leaf = internal::LeafOf<M>;

  const std::string &name() const { return st_->names.at(index_); }
  std::vector<size_t> dims() const { return st_->dims.at(index_); }
  bool witness() const { return st_->witness; }

  // A statement member's codec: PRED(leaves) is true when the member is
  // well formed, its leaves in row-major order (a std::vector of its
  // integers or bools). A statement whose member PRED refuses fails
  // verification (Prepared::rejected_statement() names "statement"), and
  // the prover refuses it. ID names the check in the system digest.
  template <class Pred>
  void check(const Computes &id, Pred pred) const {
    check_as(name(), id, pred);
  }
  // The same codec, recorded against the public value VALUE (its name) the
  // program computes from the member (D.pub(..., depends_on(m), ...)): the
  // verifier still runs PRED on the member's integers, and the plan's
  // check names VALUE, the statement value the check constrains.
  template <class Pred>
  void check_value(const std::string &value, const Computes &id,
                   Pred pred) const {
    check_as(value, id, pred);
  }
  // check and check_value's shared body: the plan records the check
  // against RECORDED.
  template <class Pred>
  void check_as(const std::string &recorded, const Computes &id,
                Pred pred) const {
    static_assert(internal::kIntegerLeaf<Leaf>,
                  "check(id, pred): a member of integers or bools; a member "
                  "of field elements is check(D, id, pred)");
    static_assert(
        std::is_invocable_r_v<bool, const Pred &, const std::vector<Leaf> &>,
        "check: the predicate takes a const std::vector<Leaf>& and returns "
        "bool");
    require(false, "check");
    constexpr size_t w = internal::integer_width<Leaf>();
    internal::RelationAccess::check(
        *st_->sys, recorded, st_->offset.at(index_), st_->len.at(index_), id,
        [pred](const std::vector<uint8_t> &b) {
          using U = typename internal::UnsignedOf<Leaf>::type;
          std::vector<Leaf> v;
          v.reserve(b.size() / w);
          for (size_t k = 0; k < b.size(); k += w) {
            uint64_t u = 0;
            for (size_t j = 0; j < w; ++j) u |= uint64_t(b[k + j]) << (8 * j);
            v.push_back(Leaf(U(u)));
          }
          return pred(v);
        });
  }
  // The same for a member of elements of D's field: PRED reads them
  // decoded (a std::vector of elements); a non-canonical encoding is
  // refused before PRED runs.
  template <class F, class Pred>
  void check(Domain<F> &D, const Computes &id, Pred pred) const {
    using Elt = typename F::Elt;
    static_assert(std::is_same_v<Leaf, Elt>,
                  "check(D, id, pred): a member of elements of D's field");
    static_assert(
        std::is_invocable_r_v<bool, const Pred &, const std::vector<Elt> &>,
        "check: the predicate takes a const std::vector<Elt>& and returns "
        "bool");
    require(false, "check");
    const F *pf = &D.field();
    internal::RelationAccess::check(
        *st_->sys, name(), st_->offset.at(index_), st_->len.at(index_), id,
        [pf, pred](const std::vector<uint8_t> &b) {
          std::vector<Elt> v;
          v.reserve(b.size() / F::kBytes);
          for (size_t k = 0; k < b.size(); k += F::kBytes) {
            const auto e = pf->of_bytes_field(&b[k]);
            if (!e) return false;
            v.push_back(*e);
          }
          return pred(v);
        });
  }

  // A statement member's bits in D's field: each integer's bits, least
  // significant first, [dims..., 8 * width]; a bool's one bit, [dims...].
  template <class F>
  Ref<F, Bit, Public> bits(Domain<F> &D) const {
    static_assert(internal::kIntegerLeaf<Leaf>,
                  "bits(): the member's leaves are integers, bytes or bools");
    require(false, "bits");
    constexpr bool kBool = std::is_same_v<Leaf, bool>;
    constexpr size_t w = internal::integer_width<Leaf>();
    const F *pf = &D.field();
    std::vector<size_t> d = dims();
    if (!kBool) d.push_back(8 * w);
    return D.pub(Bit{}, "statement." + name() + ".bits", Shape(d),
                 depends_on(slice()),
                 computes("statement.bits", {st_->offset.at(index_),
                                             st_->len.at(index_), w}),
                 [pf](const std::vector<uint8_t> &b) {
                   std::vector<typename F::Elt> out;
                   for (size_t k = 0; k < b.size(); k += w) {
                     for (size_t j = 0; j < (kBool ? 1 : 8 * w); ++j)
                       out.push_back(ct::bit_elt(
                           *pf, uint64_t(b[k + j / 8] >> (j % 8)) & 1));
                   }
                   return out;
                 })
        .cache();
  }
  // A statement member's values in D's field: integers mod p (a negative v
  // as p - |v|) as Subfield values, field elements as Field values;
  // [dims...].
  template <class F>
  auto values(Domain<F> &D) const {
    require(false, "values");
    const F *pf = &D.field();
    const std::string nm = "statement." + name();
    const Computes id = computes(
        "statement.values", {st_->offset.at(index_), st_->len.at(index_)});
    if constexpr (internal::kIntegerLeaf<Leaf>) {
      static_assert(!F::kCharacteristicTwo,
                    "values(): integers mod p exist in odd characteristic; "
                    "read a binary field's statement through bits()");
      constexpr size_t w = internal::integer_width<Leaf>();
      return D.pub(Subfield<>{}, nm, Shape(dims()), depends_on(slice()), id,
                   [pf, nm](const std::vector<uint8_t> &b) {
                     // The integers in chunks on the calling thread's
                     // runner (util/parallel.h), each with its own flag.
                     const size_t n = b.size() / w;
                     auto out = parallel::presized<typename F::Elt>(n);
                     const size_t grain =
                         parallel::grain_for(n, parallel::kChunks);
                     std::vector<uint64_t> oks(parallel::chunks(n, grain), 1);
                     parallel::for_chunks(n, grain, [&](size_t lo, size_t hi) {
                       uint64_t ok = 1;
                       for (size_t m = lo; m < hi; ++m) {
                         using U = typename internal::UnsignedOf<Leaf>::type;
                         uint64_t u = 0;
                         for (size_t j = 0; j < w; ++j)
                           u |= uint64_t(b[m * w + j]) << (8 * j);
                         out[m] = internal::integer_elt(*pf, Leaf(U(u)), ok);
                       }
                       oks[lo / grain] = ok;
                     });
                     uint64_t ok = 1;
                     for (uint64_t x : oks) ok &= x;
                     if (!ok)
                       throw std::runtime_error(
                           nm + ": an integer's magnitude is not below p");
                     return out;
                   })
          .cache();
    } else {
      static_assert(std::is_same_v<Leaf, typename F::Elt>,
                    "values(): the member's leaves are integers or elements "
                    "of the domain's field");
      return D.pub(Field{}, nm, Shape(dims()), depends_on(slice()), id,
                   [pf, nm](const std::vector<uint8_t> &b) {
                     std::vector<typename F::Elt> out;
                     for (size_t k = 0; k < b.size(); k += F::kBytes) {
                       const auto e = pf->of_bytes_field(&b[k]);
                       if (!e)
                         throw std::runtime_error(
                             nm + ": a field element is not canonical");
                       out.push_back(*e);
                     }
                     return out;
                   })
          .cache();
    }
  }

  // The member's canonical bytes as a depends_on entry: a slice of the
  // statement, or the witness member's host input.
  BytesSlice slice() const {
    const size_t n = st_->len.at(index_);
    if (!st_->witness)
      return BytesSlice{st_->sys->statement_node(), st_->offset.at(index_), n};
    auto it = st_->hosts.find(index_);
    if (it == st_->hosts.end())
      it = st_->hosts
               .emplace(index_, internal::RelationAccess::host_input(
                                    *st_->sys, name(), n))
               .first;
    return BytesSlice{it->second.id, 0, n};
  }

  // The struct value's member (Relation fills the witness with it).
  const M &of(const void *whole) const { return get_(whole); }
  internal::InputState &state() const { return *st_; }
  // A CompileError naming WHAT unless this is a witness member (WITNESS)
  // or a statement member.
  void require(bool witness, const char *what) const {
    if (st_->witness != witness)
      fail(std::string(what) + "(" + name() + "): a " +
           (st_->witness ? "witness" : "statement") + " member; " +
           (witness ? "priv commits witness members"
                    : "the views read statement members"));
  }

  In(std::shared_ptr<internal::InputState> st, size_t index,
     const M &(*get)(const void *))
      : st_(std::move(st)), index_(index), get_(get) {}

 private:
  std::shared_ptr<internal::InputState> st_;
  size_t index_;
  const M &(*get_)(const void *);
};

// A depends_on entry: the member's canonical bytes.
template <class M>
struct DepEntry<In<M>> {
  using type = BytesSlice;
  static type of(const In<M> &m) { return m.slice(); }
};

namespace internal {
template <class Root, template <template <class> class> class S,
          size_t... Path>
S<In> handles_at(const std::shared_ptr<InputState> &st, size_t first);
// The handle on member I of V, the member of the struct value Root at
// PATH (V itself when PATH is empty): an In<M> at the plain index INDEX,
// or for a record member the record's handles.
template <class Root, class V, size_t I, size_t... Path>
auto member_handle(const std::shared_ptr<InputState> &st, size_t index) {
  using M = reflect::member_t<V, I>;
  if constexpr (kRecordMember<M>) {
    return handles_at<Root, RecordOf<M>::template With, Path..., I>(st,
                                                                    index);
  } else {
    return In<M>(st, index, [](const void *v) -> const M & {
      return member_at<Root, Path..., I>(*static_cast<const Root *>(v));
    });
  }
}
// S<In>: the handles on S<Value>'s members, enumerated as S<Value>'s
// members are (initializer counting and structured bindings), so the
// handle at each index reads the value at the same index. S<Value> is the
// member of Root at PATH, its first plain member at index FIRST.
template <class Root, template <template <class> class> class S,
          size_t... Path>
S<In> handles_at(const std::shared_ptr<InputState> &st, size_t first) {
  using V = S<Value>;
  static_assert(std::is_aggregate_v<V> && std::is_aggregate_v<S<In>>,
                "a Statement, Witness or record template is a plain "
                "aggregate");
  constexpr size_t n = reflect::count<V>();
  return [&]<size_t... I>(std::index_sequence<I...>) {
    return S<In>{
        member_handle<Root, V, I, Path...>(st, first + plain_index<V, I>())...};
  }(std::make_index_sequence<n>{});
}
template <template <template <class> class> class S>
S<In> handles(const std::shared_ptr<InputState> &st) {
  return handles_at<S<Value>, S>(st, 0);
}
}  // namespace internal

// ------------------------------------------------- Domain::priv(member)

template <class F>
template <class T, class M>
Ref<F, T, Committed> Domain<F>::priv(T, const In<M> &m) {
  static_assert(is_value_type_v<T>,
                "priv(T{}, m): the type is Bit, Subfield or Field");
  m.require(true, "priv");
  auto r = priv(T{}, m.name(), internal::member_shape<T, M>(m.dims()));
  const F *pf = f_;
  const In<M> mm = m;
  const std::string nm = m.name();
  m.state().fills.push_back(
      {r.id, [pf, mm, nm](const void *w) -> std::shared_ptr<void> {
         return std::make_shared<std::vector<Elt>>(
             internal::member_elements<F, T>(*pf, mm.of(w), nm));
       }});
  return r;
}
template <class F>
template <class M>
auto Domain<F>::priv(const In<M> &m) {
  using L = internal::LeafOf<M>;
  if constexpr (std::is_same_v<L, uint8_t> || std::is_same_v<L, bool>) {
    return priv(Bit{}, m);
  } else {
    static_assert(std::is_same_v<L, Elt>,
                  "priv(m): a member of integers names its type, "
                  "priv(Subfield<E>{}, m) or priv(Bit{}, m)");
    return priv(Field{}, m);
  }
}

// ----------------------------------------------------------- Relation --

// A compiled relation over Statement ST and Witness W: it proves and
// verifies on struct values. The system's field set lives behind it.
template <class St, class W>
class Relation {
 public:
  struct Impl {
    virtual ~Impl() = default;
    virtual std::vector<uint8_t> prove(const St &st, const W &w,
                                       RandomEngine &rng) const = 0;
    virtual bool verify(const St &st,
                        const std::vector<uint8_t> &proof) const = 0;
  };
  explicit Relation(std::unique_ptr<Impl> impl) : impl_(std::move(impl)) {}

  // A proof that W satisfies the relation on ST.
  std::vector<uint8_t> prove(const St &st, const W &w,
                             RandomEngine &rng) const {
    return impl_->prove(st, w, rng);
  }
  // Whether PROOF proves the relation on ST.
  bool verify(const St &st, const std::vector<uint8_t> &proof) const {
    return impl_->verify(st, proof);
  }
  // The system's side (Sys the ConstraintSystem the relation declared):
  // the system, its compilation and the assignments of a statement and a
  // witness, for tests and benchmarks.
  template <class Sys>
  const auto &typed() const;

 private:
  std::unique_ptr<Impl> impl_;
};

namespace internal {

// The ConstraintSystem type a relation function declares into: its first
// parameter's.
template <class Fn>
struct FirstParam : FirstParam<decltype(&Fn::operator())> {};
template <class R, class C, class A, class... B>
struct FirstParam<R (C::*)(A, B...) const> {
  using type = std::remove_cvref_t<A>;
};
template <class R, class C, class A, class... B>
struct FirstParam<R (C::*)(A, B...)> {
  using type = std::remove_cvref_t<A>;
};
template <class R, class A, class... B>
struct FirstParam<R (*)(A, B...)> {
  using type = std::remove_cvref_t<A>;
};

// The plain members of struct T added to the input state ST: names under
// PREFIX, axes and byte ranges from AT on (field elements sized by their
// field in FS), the std::vector members' lengths from SHAPE.
template <class T, class... Fs>
void add_members(InputState &st, const T *shape, const std::string &prefix,
                 size_t &at) {
  [&]<size_t... I>(std::index_sequence<I...>) {
    (
        [&] {
          using M = reflect::member_t<T, I>;
          const M *ms = shape == nullptr
                            ? nullptr
                            : &std::get<I>(reflect::tie(*shape));
          const std::string nm = prefix + std::string(reflect::name<T, I>());
          if constexpr (kRecordMember<M>) {
            add_members<M, Fs...>(st, ms, nm + ".", at);
          } else {
            using L = LeafOf<M>;
            size_t w;
            if constexpr (kIntegerLeaf<L>)
              w = integer_width<L>();
            else
              w = FieldOfElt<L, Fs...>::type::kBytes;
            st.names.push_back(nm);
            st.dims.push_back(dims_of<M>(ms));
            st.offset.push_back(at);
            st.len.push_back(w * count_of_dims(st.dims.back()));
            at += st.len.back();
          }
        }(),
        ...);
  }(std::make_index_sequence<reflect::count<T>()>{});
}
// The input state of struct T in system SYS: its plain members' names
// (a record's members named record.member), axes and byte ranges, the
// std::vector members' lengths from SHAPE.
template <class T, class... Fs>
std::shared_ptr<InputState> input_state(SystemCore *sys, bool witness,
                                        const T *shape) {
  auto st = std::make_shared<InputState>();
  st->sys = sys;
  st->witness = witness;
  size_t at = 0;
  add_members<T, Fs...>(*st, shape, "", at);
  return st;
}

}  // namespace internal

// The relation of system type SYS (relation.h's Relation::Impl).
template <class St, class W, class Sys>
class RelationOf final : public Relation<St, W>::Impl {
 public:
  using Compiled = typename Sys::Compiled;
  using Assignment = typename Sys::Assignment;
  using Set = typename Sys::Set;

  RelationOf(std::unique_ptr<Sys> sys,
             std::shared_ptr<internal::InputState> st,
             std::shared_ptr<internal::InputState> w)
      : sys_(std::move(sys)), st_(std::move(st)), w_(std::move(w)) {}
  void compile(const CompileProfile &p, const CompileOptions &options) {
    const auto t0 = std::chrono::steady_clock::now();
    compiled_ = gordiehowe::compile(*sys_, p, options);
    compile_ms_ = std::chrono::duration<double, std::milli>(
                      std::chrono::steady_clock::now() - t0)
                      .count();
  }

  Sys &system() const { return *sys_; }
  const Compiled &compiled() const { return *compiled_; }
  // The compiled system, shared with the relation (the tests' and
  // benchmarks' handle on it).
  std::shared_ptr<const Compiled> compiled_ptr() const { return compiled_; }
  // The time (ms) the relation's lowering and compile() took.
  double compile_ms() const { return compile_ms_; }
  // The statement's assignment: its canonical bytes.
  Assignment statement(const St &st) const {
    Assignment a;
    const size_t id = sys_->statement_node();
    const Node &n = sys_->graph().nodes.at(id);
    lengths(*st_, &st, "statement");
    with_field<Set>(n, [&](const auto &f) {
      using F = std::decay_t<decltype(f)>;
      a.set(Ref<F, Bytes, Public>(id, n.n, &f, nullptr, {}), bytes(st));
    });
    return a;
  }
  // The witness's assignment: each committed member's elements and each
  // host input's bytes.
  Assignment witness(const W &w) const {
    Assignment a;
    const auto &N = sys_->graph().nodes;
    lengths(*w_, &w, "witness");
    for (const auto &fill : w_->fills) {
      const Node &n = N.at(fill.node);
      const auto v = fill.elements(&w);
      with_field<Set>(n, [&](const auto &f) {
        using F = std::decay_t<decltype(f)>;
        a.set(Ref<F>(fill.node, n.n, &f, nullptr, {}),
              *std::static_pointer_cast<std::vector<typename F::Elt>>(v));
      });
    }
    if (!w_->hosts.empty()) {
      const std::vector<uint8_t> all = witness_bytes(w);
      for (const auto &[k, h] : w_->hosts)
        a.set(h, std::vector<uint8_t>(
                     all.begin() + long(w_->offset.at(k)),
                     all.begin() + long(w_->offset.at(k) + w_->len.at(k))));
    }
    return a;
  }

  std::vector<uint8_t> prove(const St &st, const W &w,
                             RandomEngine &rng) const override {
    return compiled_->prepare(statement(st)).prove(witness(w), rng);
  }
  bool verify(const St &st,
              const std::vector<uint8_t> &proof) const override {
    const auto prep = compiled_->prepare(statement(st));
    if (!prep.rejected_statement().empty()) return false;
    return prep.verify(proof);
  }

  // The canonical bytes of a statement and a witness value.
  std::vector<uint8_t> bytes(const St &st) const { return serialize(st); }
  std::vector<uint8_t> witness_bytes(const W &w) const { return serialize(w); }

 private:
  // Each member of the value V of an input struct has the axes the
  // relation was compiled with (a std::vector's length is fixed per
  // relation).
  template <class T>
  static void lengths(const internal::InputState &s, const T *v,
                      const char *what) {
    size_t i = 0;
    internal::for_each_plain(*v, [&](const auto &m) {
      if (internal::leaves_in(m) != internal::count_of_dims(s.dims.at(i)))
        throw std::runtime_error(std::string(what) + " member '" +
                                 s.names.at(i) +
                                 "' has another length than the relation's");
      ++i;
    });
  }
  template <class T>
  std::vector<uint8_t> serialize(const T &t) const {
    std::vector<uint8_t> out;
    internal::for_each_plain(t, [&](const auto &m) { put(out, m); });
    return out;
  }
  template <class M>
  void put(std::vector<uint8_t> &out, const M &m) const {
    using L = internal::LeafOf<M>;
    if constexpr (internal::kIntegerLeaf<L>) {
      internal::put_member<M, Set>(out, m, nullptr);
    } else {
      using F = typename internal::ElementField<L, Set>::type;
      const Domain<F> *d = sys_->template domain_of<F>();
      if (d == nullptr)
        fail("a member's field elements lie in a field with no domain");
      internal::put_member<M, F>(out, m, &d->field());
    }
  }

  std::unique_ptr<Sys> sys_;
  std::shared_ptr<internal::InputState> st_, w_;
  std::shared_ptr<const Compiled> compiled_;
  double compile_ms_ = 0;
};

template <class St, class W>
template <class Sys>
const auto &Relation<St, W>::typed() const {
  const auto *r = dynamic_cast<const RelationOf<St, W, Sys> *>(impl_.get());
  if (r == nullptr) throw std::logic_error("Relation::typed: another system");
  return *r;
}

// Builds the system RELATION declares, fn(cs, Statement<In>,
// Witness<In>), lowers and compiles it under PROFILE with OPTIONS, and
// returns the relation. NAME names the system (the transcript label;
// PROFILE's name by default).
//
// With ST_SHAPE and W_SHAPE, a Statement and a Witness of the relation's
// shape, the lengths of their std::vector members are those of the shape
// values (whose other contents are not read): every statement and witness
// of the relation has them.
template <template <template <class> class> class Statement,
          template <template <class> class> class Witness, class Fn>
Relation<Statement<Value>, Witness<Value>> compile(
    const CompileProfile &profile, Fn relation, std::string name,
    const Statement<Value> *st_shape, const Witness<Value> *w_shape,
    const CompileOptions &options = {}) {
  using St = Statement<Value>;
  using W = Witness<Value>;
  using Sys = typename internal::FirstParam<Fn>::type;
  auto sys = std::make_unique<Sys>(name.empty() ? profile.name : name);
  auto make = [&]<class H, class... Fs>(TypeTag<FieldSet<H, Fs...>>) {
    return std::make_pair(
        internal::input_state<St, Fs...>(sys.get(), false, st_shape),
        internal::input_state<W, Fs...>(sys.get(), true, w_shape));
  };
  auto [st, w] = make(TypeTag<typename Sys::Set>{});
  const size_t n = st->len.empty() ? 0 : st->offset.back() + st->len.back();
  internal::RelationAccess::request_statement(*sys, n);
  relation(*sys, internal::handles<Statement>(st),
           internal::handles<Witness>(w));
  // A statement the relation never read is declared now: it is absorbed
  // all the same.
  (void)sys->statement_node();
  auto impl = std::make_unique<RelationOf<St, W, Sys>>(std::move(sys), st, w);
  impl->compile(profile, options);
  return Relation<St, W>(std::move(impl));
}
template <template <template <class> class> class Statement,
          template <template <class> class> class Witness, class Fn>
Relation<Statement<Value>, Witness<Value>> compile(
    const CompileProfile &profile, Fn relation, std::string name = "") {
  return compile<Statement, Witness>(
      profile, std::move(relation), std::move(name),
      static_cast<const Statement<Value> *>(nullptr),
      static_cast<const Witness<Value> *>(nullptr));
}
template <template <template <class> class> class Statement,
          template <template <class> class> class Witness, class Fn>
Relation<Statement<Value>, Witness<Value>> compile(
    const CompileProfile &profile, Fn relation, std::string name,
    const Statement<Value> &st_shape, const Witness<Value> &w_shape,
    const CompileOptions &options = {}) {
  return compile<Statement, Witness>(profile, std::move(relation),
                                     std::move(name), &st_shape, &w_shape,
                                     options);
}

}  // namespace proofs::gordiehowe

#endif  // PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_RELATION_H_
