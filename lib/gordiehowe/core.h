// Copyright 2026 Chad Sharp and Paul Grubbs
// SPDX-License-Identifier: Apache-2.0

// GordieHowe: the logical graph shared by the system builder, the
// compiler and the runtime.
//
// A system is a graph of typed nodes over a closed set of fields
// (FieldSet). Every node carries the index of the field it lives in, its
// length, and its declared dependencies; a value is a std::variant over the
// fields' element vectors. Phases are not stored on nodes; compile() infers
// them.

#ifndef PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_CORE_H_
#define PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_CORE_H_

#include <algorithm>
#include <array>
#include <atomic>
#include <cstddef>
#include <cstdint>
#include <cstring>
#include <functional>
#include <initializer_list>
#include <iterator>
#include <map>
#include <memory>
#include <optional>
#include <stdexcept>
#include <string>
#include <tuple>
#include <type_traits>
#include <typeinfo>
#include <utility>
#include <variant>
#include <vector>

#include "gf2k/gf2_128.h"
#include "gf2k/gf2_256.h"
#include "gordiehowe/subfield.h"
#include "gordiehowe/wide_int.h"
#include "random/random.h"
#include "random/transcript.h"
#include "util/crypto.h"
#include "util/parallel.h"
#include "util/readbuffer.h"

namespace proofs::gordiehowe {

// Every structural rejection (types, phases, pads, capabilities) is a
// CompileError thrown by compile().
struct CompileError : std::runtime_error {
  using std::runtime_error::runtime_error;
};
[[noreturn]] inline void fail(const std::string &why) {
  throw CompileError(why);
}

// An honest prover that cannot produce a witness for a reason the
// completeness analysis names (the selection's sample budget, whose
// probability Selection::log2_budget_failure gives).
struct CompletenessFailure : std::runtime_error {
  using std::runtime_error::runtime_error;
};

// A cached public computation's refusal of a malformed statement (an
// ML-DSA key whose bounded ExpandA has too few acceptances): the setup
// records it as a rejected statement, which the verifier rejects and the
// prover refuses (Prepared::rejected_statement() names the computation).
struct StatementRefused : std::runtime_error {
  using std::runtime_error::runtime_error;
};

// --------------------------------------------------------------- bounds --

// Exclusive bounds on canonical integers, certificates and characteristics,
// and the signed integers of intervals and certificates: fixed-width
// integers of WideUint::kBits = 640 bits (wide_int.h), so that a
// characteristic up to 2^256 (F_p256), its square, and sums of such
// products are exact. The checked operations below fail on an overflow
// (a CompileError).
using Bound = WideUint;
using SignedInt = WideInt;
// The canonical integers of witness values (nat slots, nat closures and
// the generators of the lowerings): native 128-bit integers, which the
// prover's witness generation converts and divides with ct.h's 128-bit
// operations. A value of a prime field wider than 128 bits (F_p256) whose
// integer exceeds 2^128 has none (nat_of_ct clears OK). Bound stays
// compile-time, with the generators that need wider integers
// (p256_ecdsa's bind_mod_n) using WideUint themselves.
using NatInt = unsigned __int128;
// X as a NatInt, for a public bound or parameter that a generator captures;
// a CompileError when X does not fit 128 bits.
inline NatInt nat_cast(const Bound &x) {
  if (!x.fits128()) fail("a bound beyond 128 bits where a generator reads it");
  return static_cast<NatInt>(x);
}
// The modulus of a generator's NatInt arithmetic for a field of
// characteristic P: P when it fits 128 bits, and 0 otherwise (F_p256), when
// the NatInt operations wrap modulo 2^128 instead. An honest value there is
// a NatInt below its request's bound, which the lowerings check fits 128
// bits, and never wraps; a dishonest one gives a value the verifier
// rejects.
inline NatInt nat_modulus(const Bound &p) {
  return p.fits128() ? static_cast<NatInt>(p) : NatInt(0);
}
// The cap on the integers that bounds and intervals carry (row sums,
// interval ends, coefficients): beyond 2^kBoundCapBits a bound is "none".
// A product of two capped values and the sums of such products fit 640
// bits, and every characteristic in use (below 2^256) lies under it.
inline constexpr unsigned kBoundCapBits = 300;
inline const Bound kBoundMax = ~Bound(0);
inline Bound bound_add(Bound a, Bound b) {
  if (a > kBoundMax - b) fail("bound arithmetic overflows 640 bits");
  return a + b;
}
inline Bound bound_mul(Bound a, Bound b) {
  if (a != 0 && b > kBoundMax / a) fail("bound arithmetic overflows 640 bits");
  return a * b;
}
inline Bound bound_pow(Bound a, unsigned k) {
  Bound r = 1;
  for (unsigned i = 0; i < k; ++i) r = bound_mul(r, a);
  return r;
}
inline std::string bound_str(const Bound &x) { return x.str(); }

// Description bytes, for the system digest.
inline void put_u64(std::vector<uint8_t> &out, uint64_t x) {
  const size_t at = out.size();
  out.resize(at + 8);
  uint8_t *b = out.data() + at;
  for (size_t i = 0; i < 8; ++i) b[i] = (x >> (8 * i)) & 0xff;
}
inline void put_str(std::vector<uint8_t> &out, const std::string &s) {
  put_u64(out, s.size());
  out.insert(out.end(), s.begin(), s.end());
}
// X's low 128 bits, then, only when X is not the 128-bit image of a value
// in (-2^127, 2^128) (its high limbs neither all zero nor, with bit 127
// set, all one), the remaining limbs: the bytes of every bound below 2^128
// and of every signed value of 128 bits are those of the 128-bit encoding.
inline void put_bound(std::vector<uint8_t> &out, const Bound &x) {
  put_u64(out, x.limb(0));
  put_u64(out, x.limb(1));
  bool zero = true, ones = (x.limb(1) >> 63) != 0;
  for (size_t i = 2; i < Bound::kLimbs; ++i) {
    zero = zero && x.limb(i) == 0;
    ones = ones && x.limb(i) == ~uint64_t(0);
  }
  if (zero || ones) return;
  for (size_t i = 2; i < Bound::kLimbs; ++i) put_u64(out, x.limb(i));
}

// ------------------------------------------------------------------ types --

// Variable types.
enum class Base : uint8_t { kBit = 0, kSubfield = 1, kField = 2, kBytes = 3 };
// DEGREE names the subfield of a Subfield value by its degree over the prime
// field; 0 is the domain's designated subfield (domain_subfield<F>). A
// domain stores its designated subfield's degree as 0, so a type has one
// representation per domain.
struct Type {
  Base base = Base::kField;
  uint16_t degree = 0;
};
// Bit is the semantic type "a value in {0, 1}". It is defined by the prime
// subfield GF<1>: in characteristic 2 it is Subfield<GF<1>>, GF(2) itself
// (type_in stores a Subfield<GF<1>> value as a Bit); in odd characteristic
// it is Subfield<GF<1>>, the prime field, plus the Boolean check
// x (x - 1) = 0 the core adds (has_boolean_check). Storage reads only that
// definition: a Bit cell lies in the packing tree's degree-1 node, which
// bit-packs in characteristic 2. Cross-domain equality, the Logic builders,
// SHAKE messages, bit views and bit_from_unchecked key on Bit.
struct Bit {
  operator Type() const { return Type{Base::kBit}; }
};
// Subfields of a domain's field, by degree over the prime field: GF<16> is
// GF(2^16) in characteristic 2, GF<1> the prime field of an odd extension,
// GF<2> its quadratic subfield. Designated is the field's own subfield
// (domain_subfield<F>: Field::kSubFieldBits in characteristic 2, the prime
// field otherwise), whatever its degree.
template <size_t Degree>
struct GF {
  static_assert(Degree >= 1, "a subfield has degree at least 1");
  static constexpr size_t kDegree = Degree;
};
struct Designated {
  static constexpr size_t kDegree = 0;
};
// The named subfields: Fq, the prime field F_q of an odd field
// F_{q^k}, and GF2_16, GF(2^16) in a binary field.
using Fq = GF<1>;
using GF2_16 = GF<16>;
// A value of the subfield S of the domain's field (subfield.h); Subfield<>
// is the designated subfield.
template <class S = Designated>
struct Subfield {
  using subfield = S;
  operator Type() const {
    return Type{Base::kSubfield, static_cast<uint16_t>(S::kDegree)};
  }
};
struct Field {
  operator Type() const { return Type{Base::kField}; }
};
// A statement of bytes (pub(X, Bytes{}, ...)): absorbed packed densely
// into field elements, read by generators and public computations as bytes,
// never by a constraint.
struct Bytes {
  operator Type() const { return Type{Base::kBytes}; }
};
// The type of a handle whose type is not tracked by C++ (Ref<F>): the
// checks that need a type stay compile-time CompileErrors for it.
struct AnyType {};

// Type traits. A value's type is a C++ type, and every rule that depends on
// it reads these traits, never the tag itself, so that Subfield can gain a
// parameter (the subfield it names) by changing only these definitions.
template <class T>
struct is_bit : std::is_same<T, Bit> {};
template <class T>
struct is_subfield : std::false_type {};
template <class S>
struct is_subfield<Subfield<S>> : std::true_type {};
template <class T>
struct is_field : std::is_same<T, Field> {};
template <class T>
struct is_any_type : std::is_same<T, AnyType> {};
template <class T>
struct is_bytes : std::is_same<T, Bytes> {};
template <class T>
constexpr bool is_bytes_v = is_bytes<T>::value;
template <class T>
constexpr bool is_bit_v = is_bit<T>::value;
template <class T>
constexpr bool is_subfield_v = is_subfield<T>::value;
template <class T>
constexpr bool is_field_v = is_field<T>::value;
template <class T>
constexpr bool is_any_type_v = is_any_type<T>::value;
// A committed value's type tag: Bit, Subfield<S> or Field.
template <class T>
constexpr bool is_value_type_v =
    is_bit<T>::value || is_subfield<T>::value || is_field<T>::value;
// A statement's type tag: a value type or Bytes.
template <class T>
constexpr bool is_statement_type_v = is_value_type_v<T> || is_bytes<T>::value;
// The subfield a Subfield type names: GF<d>, or Designated for Subfield<>.
// A Bit lies in the prime subfield GF<1>.
template <class T>
struct subfield_of {
  static_assert(is_subfield<T>::value, "subfield_of: not a Subfield type");
  using type = typename T::subfield;
};
template <>
struct subfield_of<Bit> {
  using type = GF<1>;
};
// Whether a value of type T in field F is a prime-field value, which a
// statement bound may restrict (Ref::bounded): odd characteristic, and T is
// the prime subfield (Subfield<> or Subfield<GF<1>>), or Field of a prime
// field. A Bit is bounded by its type.
template <class F, class T>
constexpr bool prime_field_value() {
  if constexpr (F::kCharacteristicTwo) {
    return false;
  } else if constexpr (is_subfield_v<T>) {
    return subfield_of<T>::type::kDegree <= 1;
  } else if constexpr (is_field_v<T>) {
    return F::kBytes == F::kSubFieldBytes;
  } else {
    return false;
  }
}
// Whether a Bit value of field F carries the core's Boolean check: in odd
// characteristic, where the prime subfield is larger than {0, 1}.
template <class F>
constexpr bool has_boolean_check() {
  return !F::kCharacteristicTwo;
}

// false, dependent on X: the message of a catch-all overload that a typed
// handle of the wrong type or placement selects.
template <class... X>
constexpr bool kTypeError = false;

// The type tag T as a runtime Type.
template <class T>
constexpr Type type_of() {
  static_assert(is_bit_v<T> || is_subfield_v<T> || is_field_v<T> ||
                    is_bytes_v<T>,
                "a value's type is Bit, Subfield, Field or Bytes");
  if constexpr (is_bytes_v<T>) {
    return Type{Base::kBytes};
  } else if constexpr (is_bit_v<T>) {
    return Type{Base::kBit};
  } else if constexpr (is_subfield_v<T>) {
    return Type{Base::kSubfield,
                static_cast<uint16_t>(subfield_of<T>::type::kDegree)};
  } else {
    return Type{Base::kField};
  }
}
// The type tag T of a value of field F: a Subfield's degree is checked
// against F's subfields and stored normalized (designated = 0). In
// characteristic 2, Subfield<GF<1>> is GF(2), so it is stored as a Bit.
template <class F, class T>
Type type_in() {
  Type t = type_of<T>();
  if (t.base == Base::kSubfield && t.degree != 0) {
    if (F::kCharacteristicTwo && t.degree == 1) return Type{Base::kBit};
    const std::string why = SubfieldInfo<F>::unsupported(t.degree);
    if (!why.empty())
      fail("Subfield<GF<" + std::to_string(t.degree) + ">>: " + why);
    t.degree = normalize_degree<F>(t.degree);
  }
  return t;
}

// Where a value lives, the second axis of a handle's type:
//   Public       the statement, constants, public computations, challenges
//                and public messages; both parties hold it;
//   Committed    private inputs, advice, derived views over them, pads and
//                pad copies; every coordinate is a committed coordinate or
//                an affine view of committed coordinates;
//   CircuitOnly  bit views and the wiring views that read one: they have no
//                committed coordinate, so only circuits read them.
struct Public {};
struct Committed {};
struct CircuitOnly {};
// The placement of a handle whose placement is not tracked (Ref<F>).
struct AnyPlace {};

// Masking spaces. kPrime is the prime subfield; a domain resolves it to the
// source subfield or the ambient field when one of them is the prime field.
// After resolution kPrime remains only for GF(2) in characteristic 2.
enum class Space : uint8_t { kPrime = 0, kSubfield = 1, kField = 2 };

// The smallest additive subgroup containing the type.
inline Space masking_space(Type t) {
  switch (t.base) {
    case Base::kBit:
      return Space::kPrime;
    case Base::kSubfield:
      return Space::kSubfield;
    default:
      return Space::kField;
  }
}
// The subfield a pad of the subfield space lies in, as a type's stored
// degree: a Subfield<GF<d>> value's own (0 for the designated subfield),
// so a late value of any packed subfield E has its pad uniform in E.
inline uint16_t masking_degree(Type t) {
  return t.base == Base::kSubfield ? t.degree : 0;
}

inline std::string type_name(Type t) {
  switch (t.base) {
    case Base::kBit:
      return "Bit";
    case Base::kSubfield:
      if (t.degree)
        return "Subfield<GF<" + std::to_string(t.degree) + ">>";
      return "Subfield";
    case Base::kBytes:
      return "Bytes";
    default:
      return "Field";
  }
}
inline const char *space_name(Space s) {
  switch (s) {
    case Space::kPrime:
      return "prime";
    case Space::kSubfield:
      return "subfield";
    default:
      return "field";
  }
}

// ------------------------------------------------------------ field ops --

// The canonical integer of an element of an odd-characteristic field's prime
// subfield (the source subfield of Goldilocks extensions, the whole field of
// a prime field): its little-endian subfield bytes.
template <class F>
Bound nat_of(const F &f, const typename F::Elt &x) {
  if constexpr (F::kCharacteristicTwo) {
    fail("canonical integers exist in odd characteristic only");
  } else {
    if (!subfield_contains(f, x)) fail("canonical integer of a non-prime-field element");
    uint8_t b[domain_subfield<F>::kBytes];
    subfield_to_bytes(f, b, x);
    static_assert(domain_subfield<F>::kBytes * 8 < Bound::kBits,
                  "a canonical integer wider than a Bound");
    Bound r = 0;
    for (size_t i = domain_subfield<F>::kBytes; i-- > 0;) r = (r << 8) | b[i];
    return r;
  }
}
// The canonical integer of X with no branch on X, for witness values: OK
// is cleared when X lies outside the prime field or its integer exceeds
// 128 bits (X then reads as 0). The caller checks OK once, after its loop.
template <class F>
NatInt nat_of_ct(const F &f, const typename F::Elt &x, uint64_t &ok) {
  if constexpr (F::kCharacteristicTwo) {
    fail("canonical integers exist in odd characteristic only");
  } else {
    const uint64_t in = uint64_t(subfield_contains(f, x));
    ok &= in;
    const auto y = ct::select(ct::mask(in), x, f.zero());
    uint8_t b[domain_subfield<F>::kBytes];
    subfield_to_bytes(f, b, y);
    NatInt r = 0;
    uint64_t high = 0;
    for (size_t i = domain_subfield<F>::kBytes; i-- > 0;) {
      if (i >= 16)
        high |= b[i];
      else
        r = (r << 8) | b[i];
    }
    ok &= ct::is_zero(high);
    return r;
  }
}
// The element of the prime field with canonical integer X (< p). The high
// word enters whenever the prime field is wider than 64 bits, whatever X.
template <class F>
typename F::Elt elt_of_nat(const F &f, NatInt x) {
  const uint64_t lo = static_cast<uint64_t>(x);
  const uint64_t hi = static_cast<uint64_t>(x >> 64);
  auto r = f.of_scalar(lo);
  auto high = [&] {
    auto t32 = f.of_scalar(uint64_t(1) << 32);
    f.add(r, f.mulf(f.of_scalar(hi), f.mulf(t32, t32)));
  };
  if constexpr (F::kCharacteristicTwo) {
    if (hi != 0) high();  // public values only
  } else if constexpr (domain_subfield<F>::kBytes > 8) {
    high();
  }
  return r;
}
// The same for a compile-time Bound (public), which may exceed 128 bits in
// a wider prime field (F_p256): its limbs above 128 bits enter too.
template <class F>
typename F::Elt elt_of_nat(const F &f, const Bound &x) {
  auto r = elt_of_nat(f, static_cast<NatInt>(x));
  if constexpr (!F::kCharacteristicTwo && domain_subfield<F>::kBytes > 16) {
    auto t32 = f.of_scalar(uint64_t(1) << 32);
    const auto t64 = f.mulf(t32, t32);
    auto w = f.mulf(t64, t64);
    for (size_t i = 2; 8 * i < domain_subfield<F>::kBytes; ++i) {
      f.add(r, f.mulf(f.of_scalar(x.limb(i)), w));
      w = f.mulf(w, t64);
    }
  }
  return r;
}
template <class F>
Bound field_characteristic(const F &f) {
  if constexpr (F::kCharacteristicTwo) {
    return 2;
  } else {
    return bound_add(nat_of(f, f.mone()), 1);
  }
}
// Whether the characteristic exceeds X.
template <class F>
bool characteristic_above(const F &f, Bound x) {
  if constexpr (F::kCharacteristicTwo) {
    return x < 2;
  } else {
    return field_characteristic(f) > x;
  }
}
// Whether the characteristic exceeds 2^128 (F_p256).
template <class F>
bool characteristic_wide(const F &f) {
  if constexpr (F::kCharacteristicTwo) {
    return false;
  } else {
    return field_characteristic(f) > Bound::pow2(128);
  }
}
// Operations on vectors of one field's elements: what the graph and the
// runtime do with a node's value, given the node's field object F.
template <class F>
struct FieldValues {
  using Elt = typename F::Elt;
  using V = std::vector<Elt>;

  // The field's identity in the system digest: its type, sizes, and the
  // bytes of -1 (which fix the characteristic of a runtime modulus).
  static std::vector<uint8_t> identity(const F &f) {
    std::vector<uint8_t> out;
    put_str(out, typeid(F).name());
    put_u64(out, F::kBytes);
    put_u64(out, domain_subfield<F>::kBytes);
    put_u64(out, F::kCharacteristicTwo ? 1 : 0);
    uint8_t b[F::kBytes];
    f.to_bytes_field(b, f.mone());
    out.insert(out.end(), b, b + F::kBytes);
    return out;
  }
  static V add(const F &f, const V &a, const V &b) {
    V r = a;
    for (size_t i = 0; i < r.size(); ++i) f.add(r[i], b[i]);
    return r;
  }
  // A uniform vector of N elements of the resolved space S; in the
  // subfield space, of the subfield of stored degree D (0: designated).
  static V sample(const F &f, Space s, size_t n, RandomEngine &rng,
                  uint16_t d = 0) {
    V r(n);
    if (s == Space::kSubfield && d != 0) {
      const auto &e = SubfieldInfo<F>::get(f, d);
      for (auto &x : r) x = e.sample(f, rng);
      return r;
    }
    for (auto &x : r) {
      if (s == Space::kField) {
        x = rng.elt(f);
      } else if (s == Space::kSubfield) {
        x = subfield_sample(f, rng);
      } else {
        uint8_t b;
        rng.bytes(&b, 1);
        x = (b & 1) ? f.one() : f.zero();
      }
    }
    return r;
  }
  // Bit: every element 0 or 1. Subfield membership is not checked here: the
  // prover's commitment checks it on every subfield coordinate (relative
  // packing, or Ligero's subfield rows).
  // The elements run in chunks of at least kMinGrain under a runner
  // (util/parallel.h), each chunk's flag combined after them.
  static bool has_type(const F &f, const V &v, Type t) {
    if (t.base != Base::kBit) return true;
    const Elt zero = f.zero(), one = f.one();
    const size_t n = v.size();
    // A value of fewer than kMinGrain elements in one chunk.
    constexpr size_t kMinGrain = 4096;
    const size_t grain =
        std::max(parallel::grain_for(n, parallel::kChunks), kMinGrain);
    std::vector<uint64_t> ok(parallel::chunks(n, grain), 1);
    parallel::for_chunks(n, grain, [&](size_t b, size_t e) {
      uint64_t c = 1;
      for (size_t i = b; i < e; ++i)
        c &= ct::equal(v[i], zero) | ct::equal(v[i], one);
      ok[b / grain] = c;
    });
    uint64_t all = 1;
    for (uint64_t c : ok) all &= c;
    return all != 0;
  }
  // Every element lies in the type: 0 or 1 for Bit, the subfield for
  // Subfield (a statement value's check).
  static bool in_type(const F &f, const V &v, Type t) {
    if (t.base == Base::kField) return true;
    if (t.base == Base::kBit) return has_type(f, v, t);
    if (t.degree != 0) {
      const auto &s = SubfieldInfo<F>::get(f, t.degree);
      for (const Elt &x : v)
        if (!s.contains(f, x)) return false;
      return true;
    }
    for (const Elt &x : v)
      if (!subfield_contains(f, x)) return false;
    return true;
  }
  // Whether every element lies in the prime field with its canonical
  // integer in [0, N - 1] (a statement bound, Ref::bounded). In
  // characteristic 2 no value has a bound.
  static bool below(const F &f, const V &v, Bound n) {
    if constexpr (F::kCharacteristicTwo) {
      return false;
    } else {
      for (const Elt &x : v) {
        uint64_t ok = 1;
        const NatInt y = nat_of_ct(f, x, ok);
        if (!ok || Bound(y) >= n) return false;
      }
      return true;
    }
  }
  // Full-width canonical bytes, for the statement and system description.
  static std::vector<uint8_t> bytes(const F &f, const V &x) {
    std::vector<uint8_t> out(x.size() * F::kBytes);
    for (size_t i = 0; i < x.size(); ++i)
      f.to_bytes_field(&out[i * F::kBytes], x[i]);
    return out;
  }
  // Absorb into a transcript of the protocol hash.
  template <class H>
  static void absorb(const F &f, BasicTranscript<H> &t, const V &x) {
    t.write(x.data(), 1, x.size(), f);
  }
  // Message codec in the resolved space S; in the subfield space, of the
  // subfield of stored degree D (0: designated): its coordinates over the
  // prime field, D bits in characteristic 2 and D prime-field elements
  // otherwise (SubfieldInfo's codec).
  static size_t codec_bytes(Space s, uint16_t d = 0) {
    if (s == Space::kField) return F::kBytes;
    if (s == Space::kSubfield && d != 0)
      return F::kCharacteristicTwo ? (size_t(d) + 7) / 8
                                   : size_t(d) * F::kSubFieldBytes;
    if (s == Space::kSubfield) return domain_subfield<F>::kBytes;
    return 1;
  }
  static void encode(const F &f, std::vector<uint8_t> &out, const V &v,
                     Space s, uint16_t d = 0) {
    if (s == Space::kSubfield && d != 0) {
      const auto &e = SubfieldInfo<F>::get(f, d);
      for (const Elt &x : v) {
        const size_t at = out.size();
        out.resize(at + codec_bytes(s, d));
        e.to_bytes(f, &out[at], x);
      }
      return;
    }
    for (const Elt &x : v) {
      const size_t at = out.size();
      out.resize(at + codec_bytes(s));
      if (s == Space::kField) {
        f.to_bytes_field(&out[at], x);
      } else if (s == Space::kSubfield) {
        subfield_to_bytes(f, &out[at], x);
      } else {
        out[at] = (x == f.one()) ? 1 : 0;
      }
    }
  }
  // A message in the subfield of stored degree D decodes to an element of
  // that subfield by construction, and a non-canonical encoding (a
  // coordinate at or above p, or a bit above the degree in characteristic
  // 2) is refused: no message outside the subfield is accepted.
  static std::optional<V> decode(const F &f, ReadBuffer &rb, size_t n,
                                 Space s, uint16_t d = 0) {
    V r(n);
    std::vector<uint8_t> buf(codec_bytes(s, d));
    if (s == Space::kSubfield && d != 0) {
      const auto &e = SubfieldInfo<F>::get(f, d);
      for (auto &x : r) {
        if (!rb.have(buf.size())) return std::nullopt;
        rb.next(buf.size(), buf.data());
        if (F::kCharacteristicTwo && d % 8 != 0 &&
            (buf.back() >> (d % 8)) != 0)
          return std::nullopt;
        auto y = e.of_bytes(f, buf.data());
        if (!y || !e.contains(f, *y)) return std::nullopt;
        x = *y;
      }
      return r;
    }
    for (auto &x : r) {
      if (!rb.have(buf.size())) return std::nullopt;
      rb.next(buf.size(), buf.data());
      if (s == Space::kField) {
        auto e = f.of_bytes_field(buf.data());
        if (!e) return std::nullopt;
        x = *e;
      } else if (s == Space::kSubfield) {
        auto e = subfield_of_bytes(f, buf.data());
        if (!e) return std::nullopt;
        x = *e;
      } else {
        if (buf[0] > 1) return std::nullopt;
        x = buf[0] ? f.one() : f.zero();
      }
    }
    return r;
  }
};

// ------------------------------------------------------------ field set --

template <class T>
struct TypeTag {
  using type = T;
};
// T in a parameter that does not take part in deduction, so that a handle
// converts to the expression type there (C++20's std::type_identity_t).
template <class T>
using NonDeduced = typename TypeTag<T>::type;

namespace internal {
template <class F, class... Fs>
struct IndexOf;
template <class F, class... Fs>
struct IndexOf<F, F, Fs...> : std::integral_constant<size_t, 0> {};
template <class F, class G, class... Fs>
struct IndexOf<F, G, Fs...>
    : std::integral_constant<size_t, 1 + IndexOf<F, Fs...>::value> {};
template <class... Fs>
struct Distinct : std::true_type {};
template <class F, class... Fs>
struct Distinct<F, Fs...>
    : std::bool_constant<(!std::is_same_v<F, Fs> && ...) &&
                         Distinct<Fs...>::value> {};
}  // namespace internal

template <class Hash, class... Fs>
class BasicConstraintSystem;

namespace internal {
template <class... Fs>
struct FieldList {};
template <class L, class F, bool B>
struct AppendIf {
  using type = L;
};
template <class... Fs, class F>
struct AppendIf<FieldList<Fs...>, F, true> {
  using type = FieldList<Fs..., F>;
};
// The fields of a system with fields FS...: FS..., then, when two or more
// of them are odd, the fields the compile profile may take for a MAC
// between two odd domains (GF(2^128) and GF(2^256), CompileProfile::
// security) that FS... does not list. The program does not list a MAC
// field, and no domain commits one.
template <class... Fs>
struct WithMacFields {
  static constexpr bool kOdd =
      ((Fs::kCharacteristicTwo ? 0 : 1) + ... + 0) >= 2;
  using A = typename AppendIf<FieldList<Fs...>, GF2_128<>,
                              kOdd && !(std::is_same_v<GF2_128<>, Fs> ||
                                        ...)>::type;
  using type = typename AppendIf<A, GF2_256<>,
                                 kOdd && !(std::is_same_v<GF2_256<>, Fs> ||
                                           ...)>::type;
};

// The value forms of a field set over the fields of field list L.
template <class L>
struct FieldSetOver;
template <class... Fs>
struct FieldSetOver<FieldList<Fs...>> {
  using Value = std::variant<std::vector<typename Fs::Elt>...>;
  static constexpr size_t kFields = sizeof...(Fs);

  // Whether F is one of the fields, a MAC field the program does not list
  // included.
  template <class F>
  static constexpr bool kContains = (std::is_same_v<F, Fs> || ...);

  // The index of F in the field set. F must be one of the system's fields.
  template <class F>
  static constexpr size_t index() {
    static_assert(kContains<F>,
                  "this field is not one of the system's fields: list its "
                  "type in System<Fields...>");
    if constexpr (kContains<F>) {
      return internal::IndexOf<F, Fs...>::value;
    } else {
      return 0;
    }
  }
  template <class F>
  static Value wrap(std::vector<typename F::Elt> v) {
    return Value(std::in_place_index<index<F>()>, std::move(v));
  }
  template <class F>
  static const std::vector<typename F::Elt> &get(const Value &v) {
    return std::get<index<F>()>(v);
  }
  template <class F>
  static std::vector<typename F::Elt> &get(Value &v) {
    return std::get<index<F>()>(v);
  }

  // FN(TypeTag<F>{}) for the field F of index I.
  template <class Fn>
  static decltype(auto) dispatch(size_t i, Fn &&fn) {
    return dispatch_from<0, Fs...>(i, fn);
  }

 private:
  template <size_t I, class G, class... Gs, class Fn>
  static decltype(auto) dispatch_from(size_t i, Fn &fn) {
    if constexpr (sizeof...(Gs) == 0) {
      if (i != I) throw std::logic_error("field index out of range");
      return fn(TypeTag<G>{});
    } else {
      if (i == I) return fn(TypeTag<G>{});
      return dispatch_from<I + 1, Gs...>(i, fn);
    }
  }
};
}  // namespace internal

// The closed field set of a system and its protocol hash. A value is a
// vector of elements of one of the fields, a std::variant whose alternative
// I is the field of index I; each node records its field's index, and a
// handle Ref<F> resolves F's index at compile time (index<F>()). The fields
// are FS..., in order, then the MAC fields of internal::WithMacFields.
template <class Hash_, class... Fs>
struct FieldSet
    : internal::FieldSetOver<typename internal::WithMacFields<Fs...>::type> {
  static_assert(sizeof...(Fs) >= 1, "a system lists at least one field");
  static_assert(internal::Distinct<Fs...>::value,
                "a field type is listed twice in the system's field set");
  using Hash = Hash_;
  using System = BasicConstraintSystem<Hash_, Fs...>;

  // Whether the program lists F (a domain's field is one).
  template <class F>
  static constexpr bool kListed = (std::is_same_v<F, Fs> || ...);
};

// An address unique to the field type F, which marks a value's field where
// the field set is not known (OpArgs).
template <class F>
const void *field_tag() {
  static const char tag = 0;
  return &tag;
}

// ------------------------------------------------------------- values --

// The host values of one run as the generators of a domain read them,
// without the system's field set: a node's elements by its field type, the
// bytes of host inputs and Bytes statements, and the run's caches. A
// ValueStore is one.
// The prover's current witness run on this thread, 0 outside one
// (BasicPrepared::prove numbers each phase-0 evaluation, WitnessRun). A
// generator may memoize a host computation within one run under a key of
// public data alone: the run, its argument's address and size, its own
// parameters (lib/sha256.h's families, which share one trace).
inline thread_local uint64_t witness_run = 0;
class WitnessRun {
 public:
  WitnessRun() : previous_(witness_run) {
    static std::atomic<uint64_t> next{0};
    witness_run = ++next;
  }
  ~WitnessRun() { witness_run = previous_; }
  WitnessRun(const WitnessRun &) = delete;
  WitnessRun &operator=(const WitnessRun &) = delete;

 private:
  uint64_t previous_;
};

// Packed bits by node id (ValueReader::packed_bits): a slot per node, so a
// lookup is an index. find() returns the node's bits or null; operator[]
// makes the slot present. A slot's buffer stays where it is while others
// are added.
class PackedBitsMap {
 public:
  const std::vector<uint64_t> *find(size_t id) const {
    return id < has_.size() && has_[id] ? &v_[id] : nullptr;
  }
  std::vector<uint64_t> &operator[](size_t id) {
    if (id >= has_.size()) {
      has_.resize(id + 1, 0);
      v_.resize(id + 1);
    }
    has_[id] = 1;
    return v_[id];
  }
  void erase(size_t id) {
    if (id >= has_.size()) return;
    has_[id] = 0;
    v_[id].clear();
  }
  void clear() {
    has_.clear();
    v_.clear();
  }
  // Slots for nodes 0 .. N - 1 up front.
  void reserve(size_t n) {
    if (n > has_.size()) {
      has_.resize(n, 0);
      v_.resize(n);
    }
  }

 private:
  std::vector<uint8_t> has_;
  std::vector<std::vector<uint64_t>> v_;
};

class ValueReader {
 public:
  virtual ~ValueReader() = default;
  // Structured operators instantiated in this run, by operator spec, so that
  // each party builds an operator (and its kernel spectra) once per proof.
  mutable std::map<const void *, std::shared_ptr<const void>> operators;
  // Host inputs (prover only) and byte statements, by node id.
  std::map<size_t, std::vector<uint8_t>> bytes;
  // The outputs of each record generator (advice_record) in this run, so
  // that its closure runs once for all its slots.
  mutable std::map<const void *, std::shared_ptr<void>> records;
  // The values word-level programs (bit_eval.h) computed in this run, as
  // packed bits, by node id. A value changed after its generator ran (a
  // test's tamper) is dropped, so a program reads it from its elements.
  mutable PackedBitsMap packed_bits;

  // The elements of node ID, which lies in field F.
  template <class F>
  const std::vector<typename F::Elt> &get(size_t id) const {
    const auto [tag, p] = elements(id);
    if (tag != field_tag<F>())
      throw std::logic_error("node " + std::to_string(id) +
                             " is read in another field");
    return *static_cast<const std::vector<typename F::Elt> *>(p);
  }
  // The elements of node ID: its field's tag (field_tag) and a pointer to
  // its std::vector<Elt>.
  virtual std::pair<const void *, const void *> elements(size_t id) const = 0;
};

// Host values of the nodes of one run, indexed by node id. MSG holds the
// masked message t = x + P of each late variable.
template <class S>
struct ValueStore : ValueReader {
  using Value = typename S::Value;
  std::vector<Value> v, msg;
  // Values held elsewhere, by node id: a prepared statement's cached public
  // computations (a ring's decoded keys), read in place by every proof.
  std::vector<const Value *> held;
  explicit ValueStore(size_t n = 0) : v(n), msg(n), held(n, nullptr) {
    packed_bits.reserve(n);
  }
  // The value of node ID, held or stored.
  const Value &value(size_t id) const {
    const Value *h = id < held.size() ? held[id] : nullptr;
    return h != nullptr ? *h : v.at(id);
  }
  // A Ref<F> names a node of field F, so the alternative is F's.
  template <class F>
  const std::vector<typename F::Elt> &get(size_t id) const {
    return S::template get<F>(value(id));
  }
  std::pair<const void *, const void *> elements(size_t id) const override {
    const Value &x = value(id);
    return S::dispatch(x.index(), [&](auto tag) {
      using G = typename decltype(tag)::type;
      return std::pair<const void *, const void *>(
          field_tag<G>(), &S::template get<G>(x));
    });
  }
  template <class F>
  const std::vector<typename F::Elt> &message(size_t id) const {
    return S::template get<F>(msg.at(id));
  }
};

// The values of an operator's declared dependencies, in declaration order
// (OpSpec::make). Each carries its field's tag; reading one as another field
// is a library error.
class OpArgs {
 public:
  void push(const void *tag, const void *value) { args_.push_back({tag, value}); }
  size_t size() const { return args_.size(); }
  template <class F>
  const std::vector<typename F::Elt> &get(size_t k) const {
    const Arg &a = args_.at(k);
    if (a.tag != field_tag<F>())
      throw std::logic_error("OpArgs: dependency " + std::to_string(k) +
                             " is read in another field");
    return *static_cast<const std::vector<typename F::Elt> *>(a.value);
  }

 private:
  struct Arg {
    const void *tag, *value;
  };
  std::vector<Arg> args_;
};

// --------------------------------------------------------------- nodes --

enum class Kind : uint8_t {
  kPublicInput = 0,   // statement
  kConstant = 1,      // public, fixed by the system
  kPrivateInput = 2,  // supplied by the prover, phase 0
  kAdvice = 3,        // host closure; late when its phase is >= 1
  kDerived = 4,       // affine view; relation is part of the system
  kPublicCompute = 5, // computed by both parties
  kChallenge = 6,
  kPad = 7,           // core-owned uniform pad, committed in phase 0
  kPublicMessage = 8, // t = x + P of a late variable
  kBitView = 9,       // canonical bits of phase-0 Subfield words; no storage
  kPadCopy = 10,      // a pad through a declared map, filled by the core
  kHostInput = 11,    // per-proof bytes for generators; never committed
};

inline bool is_public(Kind k) {
  return k == Kind::kPublicInput || k == Kind::kConstant ||
         k == Kind::kPublicCompute || k == Kind::kChallenge ||
         k == Kind::kPublicMessage;
}

// A value's degree in one challenge, coordinate by coordinate: U at each of its
// N coordinates when V is empty, V[i] at coordinate i otherwise.
struct CoordDegrees {
  size_t n = 0, u = 0;
  std::vector<size_t> v;
  static CoordDegrees uniform(size_t n, size_t d) { return {n, d, {}}; }
  // V as degrees, kept uniform when every coordinate has the same.
  static CoordDegrees of(std::vector<size_t> v) {
    CoordDegrees out{v.size(), v.empty() ? 0 : v[0], {}};
    for (size_t d : v)
      if (d != out.u) {
        out.v = std::move(v);
        break;
      }
    return out;
  }
  size_t at(size_t i) const { return v.empty() ? u : v[i]; }
  // The largest degree among the coordinates.
  size_t max() const {
    if (v.empty()) return n == 0 ? 0 : u;
    return *std::max_element(v.begin(), v.end());
  }
};

struct Node {
  Kind kind;
  std::string name;
  int domain = -1;  // -1: belongs to the system (public values)
  // The node's field: its index in the system's field set, and the field
  // object (of that type).
  size_t field = 0;
  const void *fobj = nullptr;
  size_t n = 0;
  Type type{Base::kField};
  std::vector<size_t> deps;   // dataflow dependencies
  std::vector<size_t> tests;  // challenges only
  long masked_by = -1;        // advice: the declared pad
  Space pad_space = Space::kField;  // pads: declared masking space
  // Pads of the subfield space: the subfield's stored degree (a type's
  // degree; 0 is the designated subfield).
  uint16_t pad_degree = 0;
  bool auto_pad = false;              // pads allocated by compile()
  // A pad of an unmasked message (Lowering::zero_pad; only the per-chunk
  // MAC ablation, CompileProfile::unsound_per_chunk_mac, declares one): the
  // core sets it to zero, so the message t = x + P is x itself.
  bool zero_pad = false;
  // A key pad (Lowering::key_pad; only the per-chunk MAC ablation declares
  // one): uniform prover randomness that masks no message, which
  // constraints and generators read directly (the MAC's key shares). The
  // core draws it with the other pads, from the prover's random engine.
  bool key_pad = false;
  // Pad copies: the map keeps the pad's masking space as the copy's type
  // (compile() resolves it), and the map acts within one field.
  bool copy_keeps_space = false, copy_same_field = false;
  // Challenges: "field", "subfield", or "field-minus-tables" (uniform in
  // the field minus a set U of public values, Domain::challenge_outside).
  std::string sampler;
  // Challenges of "field-minus-tables": the public values U is built from,
  // each drawn or computed before the challenge (compile() checks it).
  std::vector<size_t> excludes;
  // Challenges: the lowering or library function that declared it
  // ("application" for the application's own).
  std::string origin;
  // Extra description bytes (constants' values, derived expressions).
  std::vector<uint8_t> descr;
  // The value's shape (product n): how handles and closures index it. It
  // does not enter the description; the relation is the same flat one.
  std::vector<size_t> shape;
  // A view a view operation made, not yet named (Ref::named).
  bool auto_view = false;
  // A public computation computed once per statement (Ref::cache).
  bool cached = false;
  // A statement value's declared bound N (Ref::bounded): the statement is
  // well formed only when every coordinate's canonical integer lies in
  // [0, N - 1]. 0: no bound.
  Bound stmt_bound = 0;
  // A public computation defined by an expression over public values,
  // which both parties evaluate with the host emitter
  // (compiler/public_expr.h), with no closure of its own.
  bool expression = false;
  // A public expression's or public view's degree in each challenge it
  // reads, directly or through public expressions, coordinate by
  // coordinate (challenge_coord_degrees in expr.h): (challenge id,
  // degrees), in increasing id order.
  std::vector<std::pair<size_t, CoordDegrees>> challenge_degrees;
  // A challenge a core realization draws (realization_challenge).
  bool realization = false;
};

// Whether a challenge is drawn by a core realization: the cross-field MAC's
// key, assert_in's alpha and its tuple-packing gamma, and the range lookups'
// alpha, which their lowerings mark (Lowering::realization). Their degree
// bounds come from the errors of the realizations' identities, which the
// lowerings declare; every other challenge is the source program's, and
// compile() bounds it by the sum of the degrees in it of the predicates that
// read it.
inline bool realization_challenge(const Node &n) {
  return n.kind == Kind::kChallenge && n.realization;
}

// Whether N is a public view (the system's wiring of public coordinates,
// a reindex or slice of a public value): no closure of its own.
inline bool public_view(const Node &n) {
  return n.kind == Kind::kPublicCompute && n.origin == "view";
}

// The challenges the nodes IDS read, directly or through public
// computations and derived views, in increasing order.
inline std::vector<size_t> challenges_read(const std::vector<Node> &N,
                                           const std::vector<size_t> &ids) {
  std::vector<bool> seen(N.size(), false);
  std::vector<size_t> stack(ids.begin(), ids.end()), out;
  while (!stack.empty()) {
    const size_t x = stack.back();
    stack.pop_back();
    if (seen.at(x)) continue;
    seen[x] = true;
    const Node &n = N[x];
    if (n.kind == Kind::kChallenge) out.push_back(x);
    if (n.kind == Kind::kPublicCompute || n.kind == Kind::kDerived)
      stack.insert(stack.end(), n.deps.begin(), n.deps.end());
  }
  std::sort(out.begin(), out.end());
  return out;
}

// FN(f) with the field object f of node N, typed by the field set S.
template <class S, class Fn>
decltype(auto) with_field(const Node &n, Fn &&fn) {
  return S::dispatch(n.field, [&](auto tag) -> decltype(auto) {
    using F = typename decltype(tag)::type;
    return fn(*static_cast<const F *>(n.fobj));
  });
}

// The closures of a node: advice, derived, public compute and constants
// evaluate; challenges decode from a label-separated stream.
template <class S>
struct Generator {
  std::function<typename S::Value(const ValueStore<S> &)> eval;
  // A challenge's sampler, on its stream and the values of earlier phases
  // (which a sampler outside a set U reads).
  std::function<typename S::Value(RandomEngine &, const ValueStore<S> &)>
      sample;
  // A public input's statement codec: kAccepted, kRejected (the whole
  // value), or the index of the first row a per-row codec refuses; over the
  // bytes of a Bytes statement.
  std::function<long(const typename S::Value &)> accepts;
  std::function<long(const std::vector<uint8_t> &)> accepts_bytes;
};
constexpr long kAccepted = -1, kRejected = -2;

// A challenge's excluded set U (Domain::challenge_outside): from the values
// U is built from, the membership test of U.
template <class F>
using ExcludedSet = std::function<std::function<bool(const typename F::Elt &)>(
    const ValueReader &)>;

// The nodes, which handles reach.
// A view coordinate: (node, coordinate), or kZeroCoordinate for a zero.
constexpr size_t kZeroCoordinate = SIZE_MAX;
using ViewSource = std::vector<std::pair<size_t, size_t>>;

// The choices of the lowerings and library gadgets, as plain data for the
// plan export (plan_export.h). They restate what the system description
// already fixes, so they do not enter the digest.
struct PlanRecords {
  // An affine expression over the integers (range_internal::plan_affine):
  // its terms (kind 'n' a node, 's' the sum operator on a node, 'o' another
  // operator chain written o(...(node))), one signed coefficient each, and
  // the constants per coordinate; ERROR when it has no integer form.
  struct Affine {
    std::vector<std::pair<char, std::string>> terms;
    // Per term, the interval bounds of its operators ('o' terms): each
    // operator's named bound terms, or its rowSum / absRowSum.
    std::vector<std::vector<std::pair<std::string, Bound>>> op_bounds;
    std::vector<SignedInt> coeffs, consts;
    size_t n = 0;
    std::string error;
  };
  // A MAC equality (mac.h): its label, domains, shape and challenge.
  struct Mac {
    std::string name, tag_domain, acc_domain, challenge;
    // The nodes of the MAC: the two sides X_H and X_A (a concatenation
    // view when several equalities merge), the tag U, its pad, the blind
    // (the pad's bits copied into the odd domain), the key and the chunk
    // powers; the name of the H predicate (empty when the compiler's own
    // circuit states it). SIZE_MAX where the form has none. The odd/odd
    // MAC has no X_H and records one Mac per odd side: X_A that side, the
    // blind that side's copy of the pad; its tag, pad, key and powers lie
    // in no domain.
    size_t xh = SIZE_MAX, xa = SIZE_MAX, tag = SIZE_MAX, pad = SIZE_MAX,
           blind = SIZE_MAX, key = SIZE_MAX, powers = SIZE_MAX;
    std::string h_predicate, h_circuit;
    size_t width = 0, nch = 0;
    std::vector<size_t> taps;  // the support of x^w, ascending
    std::vector<std::string> members;  // the merged equalities (2 or more)
    uint64_t conv_max = 0;
    Bound acc_max = 0;
    // The assert_mod its tail is (a Mod of that name), and in the grouped
    // form each group's chunks [first, first + count) and the bound on its
    // accumulator, as the lowering declared them.
    std::string tail;
    struct Group {
      size_t first = 0, count = 0;
      Bound bound = 0;
    };
    std::vector<Group> groups;
  };
  // One assert_mod gadget (mod.h). FORM: the field equality, a constant,
  // a Bit, one derived digit or K digits in radix B (top derived below
  // TOP), the grouped form (GROUPS groups of K quotient digits in base
  // TABLE; its final sum is the quotient NAME.final), or the committed
  // quotient (K = 1 digit in radix Qmax + 1, its request sound below
  // DMAX) with the relation as affine rows (sides no circuit reads).
  struct Mod {
    enum Form {
      kField,
      kConstant,
      kBitQuotient,
      kOneDigit,
      kDigits,
      kGrouped,
      kCommittedDigits
    };
    std::string name;
    Form form = kField;
    Bound m = 0, qmax = 0, radix = 0, top = 0, dmax = 0, table = 0;
    unsigned k = 0;
    size_t groups = 0;
    // The grouped form: each group's units [first, end) and the bound on
    // a group's sum.
    std::vector<std::pair<size_t, size_t>> unit_ranges;
    Bound group_bound = 0;
    // The grouped form's final quotient (a Mod of that name).
    std::string final_quotient;
    // The quotient for the plan export: q = qlo + the quotient node
    // (QUOTIENT: a Bit or a one-digit quotient, derived), or its digits
    // DIGITS, least significant first (the top digit derived in kDigits),
    // in radix RADIX; in the grouped form, the groups' quotient digits
    // GROUP_DIGITS and residues RESIDUES. SIZE_MAX where the form has
    // none.
    SignedInt qlo = 0;
    size_t quotient = SIZE_MAX, group_digits = SIZE_MAX,
           residues = SIZE_MAX;
    std::vector<size_t> digits;
  };
  // An assert_mod (mod.h): lhs - rhs = 0 (mod M) in DOMAIN, the integer
  // interval [lo, hi] of lhs - rhs the lowering relies on (none for the
  // field equality); its gadget is the Mod of the same name (NAME.final
  // for the grouped form's quotient).
  struct ModEq {
    std::string name, domain;
    Bound m = 0;
    Affine expr;
    bool has_interval = false;
    SignedInt lo = 0, hi = 0;
    // The two sides' intervals [lhs_lo, lhs_hi] and [rhs_lo, rhs_hi]
    // (has_interval).
    SignedInt lhs_lo = 0, lhs_hi = 0, rhs_lo = 0, rhs_hi = 0;
    // The two sides as the lowering read them (Lin<F> of the domain's
    // field F, type-erased): the left side's units summed, and the right
    // side. For M = 0 (INTEGER, assert_int_equal) they are ExprPtr<F>s,
    // EXPR is empty, and SPAN = max(lhs_hi, rhs_hi) - min(lhs_lo, rhs_lo) < p
    // is the no-wrap certificate; its field equation lhs - rhs = 0 is the
    // domain's predicate of the same name.
    std::shared_ptr<const void> lhs, rhs;
    bool integer = false;
    Bound span = 0;
  };
  // The excluded set U of a challenge drawn uniform in K minus U
  // (Domain::challenge_outside): [0, RANGE), the union of the domain's range
  // tables. CHALLENGE is the domain's alpha:<D>.
  struct Excluded {
    std::string challenge;
    Bound range = 0;
  };
  std::vector<Excluded> excluded;
  // The nodes each lowering pass of compile() declared: [first, end) of
  // the pass NAME (the core realizations' values, for the plan export's
  // value roles).
  struct Lowered {
    std::string name;
    size_t first = 0, end = 0;
  };
  std::vector<Lowered> lowered;
  // A gadget's parameters or a certify condition (KIND "certify": lhs,
  // rhs and op, 0 for <, 1 for <=, 2 for ==).
  struct Gadget {
    std::string name, kind, domain;
    std::vector<std::pair<std::string, SignedInt>> params;
  };
  // An ordered selection (select.h): S candidates of WIDTH bits, N
  // outputs; KIND and BOUND come from the scan (kNone: the scan names
  // neither).
  struct Selection {
    enum Kind { kNone, kFixedCutoff, kRisingThreshold };
    std::string name, domain, challenge;
    Kind kind = kNone;
    size_t candidates = 0, outputs = 0, width = 0;
    uint64_t bound = 0;
  };
  // A SampleInBall shuffle (examples/mldsa/sample_in_ball.h): its record
  // permutation's name, domain and challenge, and tau; the permutation is
  // the Permutation of that challenge.
  struct SampleInBall {
    std::string name, domain, challenge;
    size_t tau = 0;
  };
  // A record permutation (assert_permutation, permutation.h): its arity,
  // the records of each side and those whose every field is a constant.
  struct Permutation {
    std::string name, domain, challenge;
    size_t arity = 0, left = 0, right = 0, const_records = 0;
  };
  // A filtered permutation of byte windows (match_windows, windows.h):
  // the message node and its length in bytes, each window's offset node
  // (kappa_w), length and allowed start bytes [first, last], the field the
  // offsets' powers lie in and the position encoding's bits, the records of
  // each side and the challenge.
  struct FilteredPermutation {
    struct Window {
      std::string name;
      size_t len = 0, first = 0, last = 0;
    };
    std::string name, domain, message, offset_field, challenge;
    size_t message_len = 0, position_bits = 0;
    size_t message_records = 0, window_records = 0;
    std::vector<Window> windows;
  };
  // The degree a gadget charges for its challenge's event: the
  // fingerprint's S, the MAC's nch, the lookup's sum over its tables of T
  // plus, per range group, N + T - 1. After compile() (CompiledSystem's
  // records), one per bounded challenge: the declared bound of a core
  // realization's challenge, the computed degree bound of the source
  // program's.
  // EXACT, when set, is the event's numerator over |K| - |U| for a
  // challenge drawn outside a set U (the lookup's sum over its groups of
  // N + T - 1, without the tables' T that DEGREE adds to read it over
  // |K|); unset, the event's numerator is DEGREE over |K|. EXACT / |K|
  // never exceeds the Lean's error of the challenge.
  struct Charge {
    std::string label;
    Bound degree = 0;
    std::optional<Bound> exact = std::nullopt;
  };
  // A statement member's check (relation.h's In::check): the member's name
  // (a record's member dotted), its canonical bytes [offset, offset +
  // bytes) in the statement's bytes, and the check's id (computes(): its
  // name and its integer parameters).
  struct MemberCheck {
    std::string member, check;
    size_t offset = 0, bytes = 0;
    std::vector<uint64_t> args;
  };
  std::vector<Mac> macs;
  std::vector<Mod> mods;
  std::vector<ModEq> mod_equalities;
  std::vector<Gadget> gadgets;
  std::vector<Selection> selections;
  std::vector<SampleInBall> sample_in_balls;
  std::vector<Permutation> permutations;
  std::vector<FilteredPermutation> filtered_permutations;
  std::vector<Charge> charges;
  std::vector<MemberCheck> member_checks;
  // A convolution the conv lowering (compiler/conv.h) realizes by the
  // spectral batch BATCH in an affine context: the source conv node CONV
  // (an ExprNode of the domain's field, type-erased, owned by the
  // predicate's expression) of BLOCKS rows of operands of LEFT and RIGHT
  // coefficients, read by the predicate PRED as the first LEFT + RIGHT - 1
  // coordinates of each block of INTT_LENGTH(z) at the root PSI (its field
  // bytes), z the committed node Z. The plan export states the
  // realization (plan_program.h).
  struct SpectralConv {
    std::string pred, batch;
    const void *conv = nullptr;
    size_t z = 0, blocks = 0, left = 0, right = 0, length = 0;
    std::vector<uint8_t> psi;
  };
  std::vector<SpectralConv> spectral_convs;
  // An assert_in table of a domain (compiler/assert_in.h), as the realized
  // program states it: its requests (names, records as ExprPtr<F> of the
  // domain's field F, type-erased, each COUNTS records of ARITY
  // coordinates), its rows (a committed table's expression ROWS, or a
  // public table's rows value ROWS_NODE), its NROWS rows, the packing
  // (fixed: the constants KAPPA, kappa^c in field bytes; gamma: the public
  // powers of gamma, POWERS), its multiplicities MULT, the domain's ALPHA
  // and GAMMA, and its LogUp circuit's name.
  struct InLookup {
    std::string table, domain, circuit;
    std::vector<std::string> requests;
    std::vector<std::shared_ptr<const void>> records;
    std::vector<size_t> counts;
    std::shared_ptr<const void> rows;
    size_t rows_node = SIZE_MAX;
    size_t arity = 1, nrows = 0;
    bool fixed = true;
    std::vector<std::vector<uint8_t>> kappa;
    size_t powers = SIZE_MAX, gamma = SIZE_MAX, alpha = SIZE_MAX,
           mult = SIZE_MAX;
  };
  std::vector<InLookup> in_lookups;
  // An affine row an assert_mod's lowering (mod.h) declares for the
  // equation MOD: the field equation (kField), a constant quotient's row
  // (kConstant), the committed digits' equation (kCommitted), the left
  // side's accumulator row (kAcc) or a group's accumulator row (kGroupAcc).
  struct ModRow {
    enum Kind { kField, kConstant, kCommitted, kAcc, kGroupAcc };
    std::string mod, row;
    Kind kind = kField;
  };
  std::vector<ModRow> mod_rows;
  // The derivations (Lean `Derivation`; compiler/derivation.h): for a
  // predicate, the steps by which the predicates its lowering realized it
  // by imply it, recorded by the lowering when it emits the realization.
  // Steps name program items by C++ names and node ids; the export
  // resolves them to the program's ids (program_builder.h). Export-only:
  // neither the digest nor the compile cache reads them.
  struct DerivExpr {
    // A side of the predicate or row ITEM (kSide: A = 0 the left side, 1
    // the right; ROW: ITEM names a lowering's row), the leaf of node NODE
    // (kLeaf: a value's leaf, a derived value's shared entry), the
    // definition of derived node NODE (kDef: its shared entry's root), the
    // sum, difference or product of ARGS (kAdd, kSub, kMul), ARGS[0] scaled
    // by the integer C (kScale).
    // kApplyIn: the first operator application (pre-order) of the left side
    // of predicate or row ITEM (a group row's convolution term).
    enum Kind : uint8_t { kSide, kLeaf, kDef, kAdd, kSub, kMul, kScale, kApplyIn };
    Kind kind = kLeaf;
    std::string item;
    bool row = false;
    size_t a = 0, node = SIZE_MAX;
    SignedInt c = 0;
    std::vector<DerivExpr> args;
  };
  // A value's interval source (Lean `IvlSrc`): its constant entries, its
  // statement bound (kDeclared), a nat premise (kNat), the prime field, a
  // Bit.
  struct DerivIvlSrc {
    enum Kind : uint8_t {
      kConst,
      kDeclared,
      kNat,
      kPrime,
      kOpaqueBit,
      kQuadRoot,
      kRootSet,
      kShift
    };
    Kind kind = kConst;
  };
  struct DerivStep {
    // The rule (Lean `Step`'s constructor); kInline splices the derivation
    // of request ITEM up to its last step (its range fact), which becomes
    // this step.
    enum Rule : uint8_t {
      kRealized,
      kSubst,
      kLinear,
      kLookup,
      kRangeNat,
      kIvlNat,
      kSrc,
      kIvlExpr,
      kIvlSolve,
      kIvlMeet,
      kNatIvl,
      kNatComp,
      kNatBool,
      kNatLin,
      kLiftConst,
      kFieldDvd,
      kGroupedMod,
      kTransport,
      kLift,
      kDigits,
      kCongr,
      kMac,
      kLinop,
      kConclude,
      kInline,
      kViewIvl
    };
    Rule rule = kConclude;
    // Earlier steps of the derivation, by index; kLinear's coefficients.
    std::vector<size_t> premises;
    std::vector<SignedInt> coeffs;
    // kViewIvl: ivl of the view NODE from its sources' ivl PREMISES, by its
    // masked parts (ivlExpr each, ivlDisjoint their sum; the export
    // expands it).
    // kRealized: the predicate or row ITEM; kLookup: needle A of range
    // request ITEM (its members, resolved by the export); kSrc: the value
    // of node NODE from SRC (kNat: from PREMISES[0]); kInline: the request
    // ITEM.
    std::string item;
    bool row = false;
    size_t a = 0, node = SIZE_MAX;
    DerivIvlSrc src;
    // The domain the step reads in, when not the derivation's (Lean
    // inDom): the other side of a cross equal; "" for its own.
    std::string in_dom;
    // kMac: the tails' and the H predicate's names (H "" for none).
    std::vector<std::string> names;
    std::string h;
    // kSubst, kLinear: e1, e2; kIvlExpr: e; kIvlSolve: the atom a.
    std::vector<DerivExpr> exprs;
    // kIvlExpr, kIvlSolve: lo, hi; kDigits: T.
    std::vector<SignedInt> ints;
  };
  struct Derivation {
    // The predicate (a row's name when ROW), in domain DOMAIN.
    std::string pred, domain;
    bool row = false;
    std::vector<DerivStep> steps;
    // Why the lowering records no derivation ("" when it does): a step of
    // its argument that the rules do not state.
    std::string gap;
  };
  std::vector<Derivation> derivations;
};

class SystemCore;
struct Graph {
  std::vector<Node> nodes;
  // The system the nodes belong to (system_core.h), which a predicate
  // finds through the handles it reads.
  SystemCore *system = nullptr;
  // Declares a view node over SRC (ConstraintSystem sets it): a wiring view of
  // a domain, or a public computation that gathers public values.
  std::function<size_t(const ViewSource &)> wire;
  // The scopes declared (Scope::scope): full prefix and parameter
  // bytes, in declaration order.
  std::vector<std::pair<std::string, std::vector<uint8_t>>> scopes;
  PlanRecords records;
};
// The nodes and their closures, which only the system and its domains add.
template <class S>
struct BasicGraph : Graph {
  std::vector<Generator<S>> gens;
  size_t add(Node n, Generator<S> g = {}) {
    nodes.push_back(std::move(n));
    gens.push_back(std::move(g));
    return nodes.size() - 1;
  }
};

// A value's shape: its axes' sizes, row-major (the last axis varies
// fastest). A length converts to the rank-1 shape.
struct Shape {
  std::vector<size_t> dims;
  Shape() = default;
  Shape(size_t n) : dims{n} {}  // NOLINT
  Shape(std::initializer_list<size_t> d) : dims(d) {}
  explicit Shape(std::vector<size_t> d) : dims(std::move(d)) {}
  size_t size() const {
    size_t k = 1;
    for (size_t x : dims) k *= x;
    return k;
  }
};

// The flat strides of DIMS.
inline std::vector<size_t> strides_of(const std::vector<size_t> &dims) {
  std::vector<size_t> st(dims.size(), 1);
  for (size_t a = dims.size(); a-- > 1;) st[a - 1] = st[a] * dims[a];
  return st;
}

// Broadcasting (the rules of NumPy): FROM, aligned on the trailing axes,
// has each axis equal to TO's or 1, and no more axes. The flat coordinate
// of FROM that coordinate i of TO reads; empty when FROM equals TO (the
// identity). A shape that does not broadcast is a CompileError naming WHAT.
inline std::vector<size_t> broadcast_map(const std::vector<size_t> &to,
                                         const std::vector<size_t> &from,
                                         const std::string &what) {
  if (from == to) return {};
  auto str = [](const std::vector<size_t> &d) {
    std::string s = "[";
    for (size_t a = 0; a < d.size(); ++a)
      s += (a ? ", " : "") + std::to_string(d[a]);
    return s + "]";
  };
  if (from.size() > to.size())
    fail(what + ": shape " + str(from) + " does not broadcast to " + str(to));
  const size_t off = to.size() - from.size();
  for (size_t a = 0; a < from.size(); ++a)
    if (from[a] != to[off + a] && from[a] != 1)
      fail(what + ": shape " + str(from) + " does not broadcast to " +
           str(to));
  const auto fst = strides_of(from);
  size_t total = 1;
  for (size_t x : to) total *= x;
  std::vector<size_t> map(total);
  std::vector<size_t> ix(to.size(), 0);
  for (size_t i = 0; i < total; ++i) {
    size_t at = 0;
    for (size_t a = 0; a < from.size(); ++a)
      if (from[a] != 1) at += ix[off + a] * fst[a];
    map[i] = at;
    for (size_t a = to.size(); a-- > 0;) {
      if (++ix[a] < to[a]) break;
      ix[a] = 0;
    }
  }
  return map;
}

// The index maps of the views that handles, affine expressions and
// expressions share (Ref, Lin, Expr): the view's dims and, for each of its
// coordinates, the flat coordinate it reads. A bad axis or bound is a
// CompileError naming WHAT.
struct ViewMap {
  std::vector<size_t> dims;
  std::vector<size_t> idx;
};
namespace view_maps {
inline void check_axis(const std::vector<size_t> &d, size_t axis,
                       const char *what) {
  if (axis >= d.size())
    throw CompileError(std::string(what) + ": no axis " + std::to_string(axis) +
                       " in a value of rank " + std::to_string(d.size()));
}
// The view of dims OUT whose coordinate at index ix reads D at SRC(ix), an
// index of D.
template <class Src>
ViewMap select(const std::vector<size_t> &d, std::vector<size_t> out,
               Src src) {
  const auto st = strides_of(d);
  size_t total = 1;
  for (size_t x : out) total *= x;
  ViewMap v;
  v.idx.reserve(total);
  std::vector<size_t> ix(out.size(), 0);
  for (size_t k = 0; k < total; ++k) {
    const std::vector<size_t> jx = src(ix);
    size_t at = 0;
    for (size_t a = 0; a < d.size(); ++a) at += jx[a] * st[a];
    v.idx.push_back(at);
    for (size_t a = out.size(); a-- > 0;) {
      if (++ix[a] < out[a]) break;
      ix[a] = 0;
    }
  }
  v.dims = std::move(out);
  return v;
}
// out[i] = x[i - k] along AXIS, cyclically (K may be negative).
inline ViewMap rotate(const std::vector<size_t> &d, long k, size_t axis) {
  check_axis(d, axis, "rotate");
  const size_t m = d[axis];
  if (m == 0) throw CompileError("rotate: an empty axis");
  const long lm = static_cast<long>(m);
  const size_t s = static_cast<size_t>(((k % lm) + lm) % lm);
  return select(d, d, [&](std::vector<size_t> ix) {
    ix[axis] = (ix[axis] + m - s) % m;
    return ix;
  });
}
// The indices IDX of AXIS, in order.
inline ViewMap reindex(const std::vector<size_t> &d,
                    const std::vector<size_t> &idx, size_t axis) {
  check_axis(d, axis, "reindex");
  for (size_t j : idx)
    if (j >= d[axis])
      throw CompileError("reindex: index " + std::to_string(j) + " past the " +
                         std::to_string(d[axis]) + " entries of axis " +
                         std::to_string(axis));
  auto out = d;
  out[axis] = idx.size();
  return select(d, out, [&](std::vector<size_t> ix) {
    ix[axis] = idx[ix[axis]];
    return ix;
  });
}
// Indices [B, E) of AXIS.
inline ViewMap slice(const std::vector<size_t> &d, size_t axis, size_t b,
                     size_t e) {
  if (axis >= d.size() || b > e || e > d[axis])
    throw CompileError("slice: [" + std::to_string(b) + ", " +
                       std::to_string(e) + ") of axis " +
                       std::to_string(axis) + " is out of range");
  auto out = d;
  out[axis] = e - b;
  return select(d, out, [&](std::vector<size_t> ix) {
    ix[axis] += b;
    return ix;
  });
}
// Index I of AXIS; the axis is dropped (a scalar keeps rank 1).
inline ViewMap at(const std::vector<size_t> &d, size_t axis, size_t i) {
  if (axis >= d.size() || i >= d[axis])
    throw CompileError("at: index " + std::to_string(i) + " of axis " +
                       std::to_string(axis) + " is out of range");
  auto out = d;
  out[axis] = 1;
  ViewMap v = select(d, out, [&](std::vector<size_t> ix) {
    ix[axis] = i;
    return ix;
  });
  v.dims.erase(v.dims.begin() + long(axis));
  if (v.dims.empty()) v.dims = {1};
  return v;
}
// AXIS moved to the last position, the other axes in order.
inline ViewMap axis_last(const std::vector<size_t> &d, size_t axis) {
  std::vector<size_t> out;
  for (size_t a = 0; a < d.size(); ++a)
    if (a != axis) out.push_back(d[a]);
  out.push_back(d.at(axis));
  return select(d, out, [&](const std::vector<size_t> &ix) {
    std::vector<size_t> jx(d.size());
    for (size_t a = 0, o = 0; a < d.size(); ++a)
      if (a != axis) jx[a] = ix[o++];
    jx[axis] = ix.back();
    return jx;
  });
}
// A of dims DA and B of dims DB along AXIS: the index is into A's
// coordinates followed by B's.
inline ViewMap concat(const std::vector<size_t> &da,
                      const std::vector<size_t> &db, size_t axis) {
  if (da.size() != db.size())
    throw CompileError("concat: the parts' ranks differ");
  check_axis(da, axis, "concat");
  for (size_t a = 0; a < da.size(); ++a)
    if (a != axis && da[a] != db[a])
      throw CompileError("concat: the parts differ on axis " +
                         std::to_string(a));
  auto out = da;
  out[axis] += db[axis];
  const auto sa = strides_of(da), sb = strides_of(db);
  size_t na = 1;
  for (size_t x : da) na *= x;
  ViewMap v;
  v.dims = out;
  std::vector<size_t> ix(out.size(), 0);
  size_t total = 1;
  for (size_t x : out) total *= x;
  for (size_t k = 0; k < total; ++k) {
    const bool first = ix[axis] < da[axis];
    size_t at = first ? 0 : na;
    for (size_t a = 0; a < out.size(); ++a) {
      const size_t j = a == axis && !first ? ix[a] - da[axis] : ix[a];
      at += j * (first ? sa[a] : sb[a]);
    }
    v.idx.push_back(at);
    for (size_t a = out.size(); a-- > 0;) {
      if (++ix[a] < out[a]) break;
      ix[a] = 0;
    }
  }
  return v;
}
}  // namespace view_maps

// The shape A and B broadcast to (NumPy's rule): aligned on the trailing
// axes, each axis pair equal or one of them 1, a missing axis read as 1.
// Shapes that do not broadcast are a CompileError naming WHAT.
inline std::vector<size_t> broadcast_shape(const std::vector<size_t> &a,
                                           const std::vector<size_t> &b,
                                           const std::string &what) {
  const size_t r = std::max(a.size(), b.size());
  std::vector<size_t> out(r);
  for (size_t k = 0; k < r; ++k) {
    const size_t x = k < r - a.size() ? 1 : a[k - (r - a.size())];
    const size_t y = k < r - b.size() ? 1 : b[k - (r - b.size())];
    if (x != y && x != 1 && y != 1) {
      auto str = [](const std::vector<size_t> &d) {
        std::string s = "[";
        for (size_t i = 0; i < d.size(); ++i)
          s += (i ? ", " : "") + std::to_string(d[i]);
        return s + "]";
      };
      fail(what + ": shapes " + str(a) + " and " + str(b) +
           " do not broadcast");
    }
    out[k] = x == 1 ? y : x;
  }
  return out;
}

// A shaped read-only view of a value's elements, as closures and circuits
// receive them: x[i] is flat coordinate i, x.row(i) the slice at index i of
// the leading axis, x(i, j, ...) one element. A view of a whole value
// converts to its std::vector, so closures that take a vector keep working.
template <class E>
class Tensor {
 public:
  Tensor(const std::vector<E> &v, std::vector<size_t> dims)
      : p_(v.data()), n_(v.size()), dims_(std::move(dims)), whole_(&v) {
    if (dims_.empty()) dims_ = {n_};
    size_t k = 1;
    for (size_t d : dims_) k *= d;
    if (k != n_) throw std::logic_error("Tensor: the shape's size differs");
  }
  size_t size() const { return n_; }
  bool empty() const { return n_ == 0; }
  const std::vector<size_t> &dims() const { return dims_; }
  const E &operator[](size_t i) const { return p_[i]; }
  const E *begin() const { return p_; }
  const E *end() const { return p_ + n_; }
  const E *data() const { return p_; }
  // The slice at index I of the leading axis.
  Tensor row(size_t i) const {
    if (dims_.empty() || i >= dims_[0])
      throw std::logic_error("Tensor::row: index past the leading axis");
    std::vector<size_t> d(dims_.begin() + 1, dims_.end());
    if (d.empty()) d = {1};
    const size_t k = n_ / dims_[0];
    return Tensor(p_ + i * k, k, std::move(d));
  }
  size_t rows() const { return dims_.empty() ? 0 : dims_[0]; }
  template <class... I>
  const E &operator()(I... idx) const {
    static_assert(sizeof...(I) >= 1, "Tensor: an element needs its indices");
    const size_t ix[] = {size_t(idx)...};
    if (sizeof...(I) != dims_.size())
      throw std::logic_error("Tensor: wrong number of indices");
    size_t at = 0;
    for (size_t a = 0; a < dims_.size(); ++a) at = at * dims_[a] + ix[a];
    return p_[at];
  }
  std::vector<E> vec() const { return std::vector<E>(p_, p_ + n_); }
  operator const std::vector<E> &() const {  // NOLINT
    if (whole_ == nullptr)
      throw std::logic_error("Tensor: a row is not a whole vector; use vec()");
    return *whole_;
  }

 private:
  Tensor(const E *p, size_t n, std::vector<size_t> dims)
      : p_(p), n_(n), dims_(std::move(dims)) {}
  const E *p_;
  size_t n_;
  std::vector<size_t> dims_;
  const std::vector<E> *whole_ = nullptr;
};

// Plain C++ arrays of integers or bits: std::vector of integers, and
// std::array and C arrays of integers or of such arrays (a C++ constant of
// rank k, its shape their extents, as kRoundConstant[i] of shape
// [5][5][64]). An operand of +, -, *, the gates, the comparisons and mux
// lifts one to a constant of the other operand's field, broadcast like any
// operand; Domain::constant lifts one that stands alone. The same
// arrays index a value (x[idx], x.reindex(idx)).
template <class K, class = void>
struct ConstArray : std::false_type {};
template <class I, class A>
struct ConstArray<std::vector<I, A>, std::enable_if_t<std::is_integral_v<I>>>
    : std::true_type {};
template <class E, size_t N>
struct ConstArray<std::array<E, N>,
                  std::enable_if_t<std::is_integral_v<E> ||
                                   ConstArray<E>::value>> : std::true_type {};
template <class E, size_t N>
struct ConstArray<E[N], std::enable_if_t<std::is_integral_v<E> ||
                                         ConstArray<E>::value>>
    : std::true_type {};
template <class K>
constexpr bool kIsConstArray = ConstArray<std::remove_cvref_t<K>>::value;

namespace const_internal {
// The integers of a C++ constant K (an integer, or an array of them, of
// any rank) in row-major order, and the extents of its axes in DIMS (none
// for an integer). A ragged array is a CompileError.
template <class K, class L>
void const_flatten(const K &k, size_t depth, std::vector<size_t> &dims,
                   std::vector<L> &out) {
  if constexpr (std::is_integral_v<K>) {
    out.push_back(L(k));
  } else {
    const size_t n = std::size(k);
    if (dims.size() == depth) {
      dims.push_back(n);
    } else if (dims.at(depth) != n) {
      fail("constant: a ragged array (" + std::to_string(n) + " and " +
           std::to_string(dims[depth]) + " entries on axis " +
           std::to_string(depth) + ")");
    }
    for (const auto &x : k) const_flatten(x, depth + 1, dims, out);
  }
}
// The innermost integer type of a C++ constant.
template <class K>
struct ConstLeaf {
  using type = K;
};
template <class I, class A>
struct ConstLeaf<std::vector<I, A>> {
  using type = I;
};
template <class E, size_t N>
struct ConstLeaf<std::array<E, N>> {
  using type = typename ConstLeaf<E>::type;
};
template <class E, size_t N>
struct ConstLeaf<E[N]> {
  using type = typename ConstLeaf<E>::type;
};
template <class K>
using ConstLeafType = typename ConstLeaf<std::remove_cvref_t<K>>::type;
// The flat indices of an index array K and its shape (rank 1 for a
// std::vector).
template <class K>
std::pair<std::vector<size_t>, std::vector<size_t>> index_array(const K &k) {
  static_assert(kIsConstArray<K>,
                "an index array is a std::vector, std::array or C array of "
                "integers");
  std::vector<ConstLeafType<K>> v;
  std::vector<size_t> dims;
  const_flatten(k, 0, dims, v);
  std::vector<size_t> idx;
  idx.reserve(v.size());
  for (const auto &x : v) {
    if constexpr (std::is_signed_v<ConstLeafType<K>>)
      if (x < 0) fail("an index array holds the negative index " +
                      std::to_string(x));
    idx.push_back(size_t(x));
  }
  return {std::move(idx), std::move(dims)};
}
}  // namespace const_internal

// An expression of field F whose values have type T (expr.h).
template <class F, class T>
struct Expr;

// A handle on a node of field F, of type T (Bit, Subfield, Field) and
// placement P (Public, Committed, CircuitOnly). The declarations return
// typed handles, and the operations whose rule the type expresses take
// them, so breaking the rule is a C++ compile error (a quadratic triple on a
// Subfield cell, an affine row reading a bit view). A typed handle converts
// to one that tracks less (Ref<F, T> or Ref<F>): an erased handle is
// accepted where any value is, and the rule is then the compile-time
// CompileError it always was.
//
// A handle is an expression of its type: its base Expr<F, T> holds the
// leaf that reads the node, so a function template taking Expr<F, Bit>
// accepts a Bit handle with F deduced. sync() rebuilds the leaf after a
// member changes.
template <class F, class T = AnyType, class P = AnyPlace>
struct Ref : Expr<F, T> {
  using field_type = F;
  using type_tag = T;
  using place_tag = P;
  size_t id = SIZE_MAX;
  size_t n = 0;
  const F *f = nullptr;
  Graph *g = nullptr;
  // The handle's shape (empty: rank 1, [n]). reshape changes it without a
  // node; the other views declare a view node.
  std::vector<size_t> shape = {};

  Ref() = default;
  Ref(size_t id_, size_t n_, const F *f_, Graph *g_ = nullptr,
      std::vector<size_t> shape_ = {})
      : id(id_), n(n_), f(f_), g(g_), shape(std::move(shape_)) {
    sync();
  }
  // The base expression's leaf for the current members (none for a Bytes
  // statement or a handle on no node).
  void sync() {
    if constexpr (!is_bytes_v<T>) {
      if (f != nullptr && id != SIZE_MAX)
        this->node = Expr<F, T>::handle_node(*this);
      else
        this->node = nullptr;
    }
  }

  std::vector<size_t> dims() const {
    return shape.empty() ? std::vector<size_t>{n} : shape;
  }
  size_t rank() const { return dims().size(); }

  // The same coordinates in another shape of the same size: no node.
  Ref reshape(Shape s) const {
    if (s.size() != n)
      throw CompileError("reshape: " + std::to_string(s.size()) +
                         " coordinates, the value has " + std::to_string(n));
    Ref r = *this;
    r.shape = s.dims;
    r.sync();
    return r;
  }
  Ref flat() const { return reshape(Shape(n)); }
  // Indices [B, E) of axis AXIS.
  Ref slice(size_t b, size_t e, size_t axis = 0) const {
    auto d = dims();
    if (axis >= d.size() || b > e || e > d[axis])
      throw CompileError("slice: [" + std::to_string(b) + ", " +
                         std::to_string(e) + ") of axis " +
                         std::to_string(axis) + " is out of range");
    auto out = d;
    out[axis] = e - b;
    return select(out, [&](std::vector<size_t> &ix) { ix[axis] += b; });
  }
  // Index I of axis AXIS; the axis is dropped.
  Ref at(size_t axis, size_t i) const {
    auto d = dims();
    if (axis >= d.size() || i >= d[axis])
      throw CompileError("at: index " + std::to_string(i) + " of axis " +
                         std::to_string(axis) + " is out of range");
    auto out = d;
    out[axis] = 1;
    Ref r = select(out, [&](std::vector<size_t> &ix) { ix[axis] = i; });
    out.erase(out.begin() + long(axis));
    if (out.empty()) out = {1};
    r.shape = out;
    r.sync();
    return r;
  }
  // Index I of the leading axis, which is dropped.
  Ref operator[](size_t i) const { return at(0, i); }
  Ref at(size_t i) const { return at(0, i); }
  // Axis AXIS in reverse order.
  Ref reverse(size_t axis) const {
    auto d = dims();
    if (axis >= d.size()) throw CompileError("reverse: no such axis");
    return select(d, [&](std::vector<size_t> &ix) {
      ix[axis] = d[axis] - 1 - ix[axis];
    });
  }
  // The coordinates, then zeros up to M (rank 1).
  Ref zero_extend(size_t m) const {
    if (m < n) throw CompileError("zero_extend: shorter than the value");
    ViewSource src;
    for (size_t i = 0; i < m; ++i)
      src.push_back(i < n ? std::make_pair(id, i)
                          : std::make_pair(kZeroCoordinate, size_t(0)));
    return view_of(src, {m});
  }
  // A general index map (NumPy's fancy indexing of the flattened value):
  // entry i is flat coordinate IDX[i]; x[idx] is the same view.
  Ref reindex(const std::vector<size_t> &idx) const {
    return flat().reindex(idx, 0);
  }
  // The indices IDX of axis AXIS, in order: the axis has IDX.size()
  // entries.
  Ref reindex(const std::vector<size_t> &idx, size_t axis) const {
    const auto d = dims();
    if (axis >= d.size()) throw CompileError("reindex: no such axis");
    for (size_t j : idx)
      if (j >= d[axis])
        throw CompileError("reindex: index " + std::to_string(j) +
                           " past the " + std::to_string(d[axis]) +
                           " entries of axis " + std::to_string(axis) +
                           " of '" + g->nodes.at(id).name + "'");
    auto out = d;
    out[axis] = idx.size();
    return select(out, [&](std::vector<size_t> &ix) { ix[axis] = idx[ix[axis]]; });
  }
  // The same with a public index array of any rank (a std::vector, or a
  // std::array or C array of integers): the view has IDX's shape.
  template <class K, class = std::enable_if_t<kIsConstArray<K>>>
  Ref reindex(const K &idx) const {
    const auto [flat_idx, d] = const_internal::index_array(idx);
    Ref r = reindex(flat_idx);
    return d.size() == 1 ? r : r.reshape(Shape(d));
  }
  // The indices IDX (rank 1) of axis AXIS.
  template <class K, class = std::enable_if_t<kIsConstArray<K>>>
  Ref reindex(const K &idx, size_t axis) const {
    const auto [flat_idx, d] = const_internal::index_array(idx);
    if (d.size() != 1)
      throw CompileError("reindex along an axis: the index array has rank " +
                         std::to_string(d.size()) + ", not 1");
    return reindex(flat_idx, axis);
  }
  // x[idx] is x.reindex(idx).
  template <class K, class = std::enable_if_t<kIsConstArray<K>>>
  Ref operator[](const K &idx) const {
    return reindex(idx);
  }
  // A cyclic shift along AXIS, out[i] = x[i - k]: a positive K moves the
  // entries toward higher indices (NumPy's roll, Keccak's ROT). A view.
  Ref rotate(long k, size_t axis) const {
    const ViewMap v = view_maps::rotate(dims(), k, axis);
    ViewSource src;
    src.reserve(v.idx.size());
    for (size_t j : v.idx) src.push_back({id, j});
    return view_of(src, v.dims);
  }
  // This value followed by Y along AXIS (the other axes agree): a view of
  // both (concat_along).
  template <class T2, class P2>
  auto concat(const Ref<F, T2, P2> &y, size_t axis = 0) const {
    return concat_along(*this, y, axis);
  }
  // The same with an expression Y (expr.h): an expression.
  template <class Y>
  auto concat(const Y &y, size_t axis = 0) const {
    return as_expr(*this).concat(y, axis);
  }

  // The expression methods (expr.h) on the handle read as an expression:
  // sums and products of the coordinates, of all of them (a scalar) or
  // along AXIS; on Bit values, c.mux(t, e) and the OR and AND along AXIS.
  auto sum() const { return as_expr(*this).sum(); }
  auto sum(size_t axis) const { return as_expr(*this).sum(axis); }
  auto prod() const { return as_expr(*this).prod(); }
  auto prod(size_t axis) const { return as_expr(*this).prod(axis); }
  template <class X, class Y>
  auto mux(const X &t, const Y &e) const {
    return as_expr(*this).mux(t, e);
  }
  auto any(size_t axis) const { return as_expr(*this).any(axis); }
  auto all(size_t axis) const { return as_expr(*this).all(axis); }
  // The integers of the digit vectors on the last axis in BASE (an integer
  // or a field element), least significant first: [..., k] -> [...], an
  // affine expression (operators.h).
  template <class B>
  auto from_digits(const B &base) const {
    return as_lin(*this).from_digits(base);
  }
  // Bit words [..., w] as integers of width w (expr.h's Word): their value
  // is from_digits(2), and the comparisons read their bits.
  auto from_bits() const { return word_of(*this); }
  // A public computation whose every dependency is a statement value or
  // constant, computed once per statement in prepare() (the setup), and
  // memoized across statements by the digest of those values.
  Ref cache() const {
    static_assert(std::is_same_v<P, Public> || std::is_same_v<P, AnyPlace>,
                  "cache() applies to public computations");
    if (g == nullptr || g->nodes.at(id).kind != Kind::kPublicCompute)
      throw CompileError("cache() applies to public computations only");
    g->nodes.at(id).cached = true;
    return *this;
  }
  // v := stmt(N): declares that every coordinate of this statement value
  // (a statement input, or a cached public computation of the statement)
  // lies in [0, N - 1]. A statement outside the bound is malformed: the
  // verifier rejects it before reading the proof and the prover refuses
  // it; interval propagation gives the value [0, N - 1]. For prime-field
  // values only (prime_field_value): a bound on another type is a C++
  // compile error. 1 <= N <= p; compile() checks that the value is a
  // statement input or a cached public computation.
  template <class TT = T,
            class = std::enable_if_t<prime_field_value<F, TT>() &&
                                     std::is_same_v<P, Public>>>
  Ref bounded(Bound bound) const {
    if (g == nullptr || f == nullptr)
      throw CompileError("bounded: a detached handle");
    Node &nd = g->nodes.at(id);
    if (nd.kind != Kind::kPublicInput && nd.kind != Kind::kPublicCompute)
      throw CompileError("bounded: '" + nd.name +
                         "' is not a statement value");
    if (bound == 0 || !characteristic_above(*f, bound - 1))
      throw CompileError("bounded: the bound of '" + nd.name +
                         "' is not in [1, p]");
    if (nd.stmt_bound != 0)
      throw CompileError("bounded: '" + nd.name + "' already has a bound");
    nd.stmt_bound = bound;
    return *this;
  }
  // The node's name (a plan record names the values it reads).
  const std::string &name() const { return g->nodes.at(id).name; }
  // This value carried to domain D (a Domain or a ScopedDomain of another
  // field; across two odd fields the MAC lies in the compile profile's
  // binary field): a priv Bit copy of this value's shape,
  // filled by copying the bits, and the cross-field assert_equal of the two
  // (predicates.h). NM names the copy (unnamed: priv<k>).
  template <class D>
  auto to(D &&d) const;
  template <class D>
  auto to(D &&d, const std::string &nm) const;
  // Names a view node a view operation made (the name enters the digest).
  Ref named(const std::string &nm) const {
    Node &nd = g->nodes.at(id);
    if (!nd.auto_view)
      throw CompileError("named: '" + nd.name + "' is not an unnamed view");
    nd.name = nm;
    nd.auto_view = false;
    return *this;
  }
  // A view node of SRC with shape DIMS, through the system's wiring.
  Ref view_of(const ViewSource &src, std::vector<size_t> dims) const {
    if (g == nullptr || !g->wire) throw CompileError("a view of a detached handle");
    Ref r = *this;
    r.id = g->wire(src);
    r.n = src.size();
    r.shape = std::move(dims);
    g->nodes.at(r.id).shape = r.shape;
    r.sync();
    return r;
  }

 private:
  // A view of shape OUT whose coordinate at index ix reads this value at
  // MAP(ix).
  template <class Map>
  Ref select(const std::vector<size_t> &out, Map map) const {
    const auto d = dims();
    const auto st = strides_of(d);
    size_t total = 1;
    for (size_t x : out) total *= x;
    ViewSource src;
    src.reserve(total);
    std::vector<size_t> ix(out.size(), 0);
    for (size_t k = 0; k < total; ++k) {
      std::vector<size_t> jx = ix;
      map(jx);
      size_t at = 0;
      for (size_t a = 0; a < d.size(); ++a) at += jx[a] * st[a];
      src.push_back({id, at});
      for (size_t a = out.size(); a-- > 0;) {
        if (++ix[a] < out[a]) break;
        ix[a] = 0;
      }
    }
    return view_of(src, out);
  }

 public:
  // The same node through a handle that tracks less.
  template <class T2, class P2,
            class = std::enable_if_t<
                (std::is_same_v<T2, T> || is_any_type_v<T2>) &&
                (std::is_same_v<P2, P> || std::is_same_v<P2, AnyPlace>) &&
                !(std::is_same_v<T2, T> && std::is_same_v<P2, P>)>>
  operator Ref<F, T2, P2>() const {  // NOLINT
    return Ref<F, T2, P2>{id, n, f, g, shape};
  }
};

// The type of a view over values of types T...: Bit when every part is
// Bit, the parts' Subfield type when every part has the same one, Field
// otherwise (AnyType when a part's type is not tracked). Its placement:
// CircuitOnly when a part is, so that no affine row reads a bit view
// through it; Public when every part is.
template <class T, class... U>
struct FirstType {
  using type = T;
};
template <class... T>
using WiredType = std::conditional_t<
    (is_any_type_v<T> || ...), AnyType,
    std::conditional_t<
        (is_bit_v<T> && ...), Bit,
        std::conditional_t<
            ((is_subfield_v<T> &&
              std::is_same_v<T, typename FirstType<T...>::type>) &&
             ...),
            typename FirstType<T...>::type, Field>>>;
template <class... P>
using WiredPlace = std::conditional_t<
    (std::is_same_v<P, CircuitOnly> || ...), CircuitOnly,
    std::conditional_t<
        (std::is_same_v<P, AnyPlace> || ...), AnyPlace,
        std::conditional_t<(std::is_same_v<P, Public> && ...), Public,
                           Committed>>>;

namespace internal {
template <class F, class... T, class... P>
Ref<F, WiredType<T...>, WiredPlace<P...>> wired(
    const ViewSource &src, std::vector<size_t> dims, Ref<F, T, P>... parts) {
  const Ref<F> first[] = {Ref<F>(parts)...};
  const Ref<F> r = first[0].view_of(src, std::move(dims));
  return Ref<F, WiredType<T...>, WiredPlace<P...>>{r.id, r.n, r.f, r.g,
                                                   r.shape};
}
}  // namespace internal

namespace internal {
// PARTS along axis 0 as one view (concat_public): their trailing axes
// agree.
template <class F, class... T, class... P>
Ref<F, WiredType<T...>, WiredPlace<P...>> concat_parts(Ref<F, T, P>... parts) {
  static_assert(sizeof...(T) >= 1, "concat of nothing");
  const Ref<F> ps[] = {Ref<F>(parts)...};
  std::vector<size_t> dims = ps[0].dims();
  ViewSource src;
  size_t lead = 0;
  for (const auto &p : ps) {
    auto d = p.dims();
    if (d.size() != dims.size() ||
        !std::equal(d.begin() + 1, d.end(), dims.begin() + 1))
      throw CompileError("concat: the parts' trailing axes differ");
    lead += d[0];
    for (size_t i = 0; i < p.n; ++i) src.push_back({p.id, i});
  }
  dims[0] = lead;
  return internal::wired(src, dims, parts...);
}
}  // namespace internal
// PARTS, of one shape, along a new last axis: [..., k].
template <class F, class... T, class... P>
Ref<F, WiredType<T...>, WiredPlace<P...>> stack(Ref<F, T, P>... parts) {
  const Ref<F> ps[] = {Ref<F>(parts)...};
  const size_t k = sizeof...(T), n = ps[0].n;
  for (const auto &p : ps)
    if (p.dims() != ps[0].dims()) throw CompileError("stack: shapes differ");
  ViewSource src;
  for (size_t i = 0; i < n; ++i)
    for (size_t j = 0; j < k; ++j) src.push_back({ps[j].id, i});
  auto dims = ps[0].dims();
  dims.push_back(k);
  return internal::wired(src, dims, parts...);
}
// PARTS coordinate by coordinate: a0, b0, ..., a1, b1, ... (rank 1).
template <class F, class... T, class... P>
Ref<F, WiredType<T...>, WiredPlace<P...>> interleave(Ref<F, T, P>... parts) {
  return stack(parts...).flat();
}
// Public values (statement values, public computations) along axis 0, as
// one public value both parties compute (a table's rows).
template <class F, class... T, class... P>
Ref<F, WiredType<T...>, Public> concat_public(Ref<F, T, P>... parts) {
  static_assert(((std::is_same_v<P, Public> || std::is_same_v<P, AnyPlace>) &&
                 ...),
                "concat_public: every part is a public value");
  const auto r = internal::concat_parts(parts...);
  return Ref<F, WiredType<T...>, Public>{r.id, r.n, r.f, r.g, r.shape};
}
// X followed by Y along AXIS (x.concat(y, axis)): their other axes agree.
template <class F, class T1, class P1, class T2, class P2>
Ref<F, WiredType<T1, T2>, WiredPlace<P1, P2>> concat_along(
    const Ref<F, T1, P1> &x, const Ref<F, T2, P2> &y, size_t axis) {
  const ViewMap v = view_maps::concat(x.dims(), y.dims(), axis);
  ViewSource src;
  src.reserve(v.idx.size());
  for (size_t j : v.idx)
    src.push_back(j < x.n ? std::make_pair(x.id, j)
                          : std::make_pair(y.id, j - x.n));
  return internal::wired(src, v.dims, x, y);
}

// A coordinate that gather() reads: flat coordinate AT of part PART, or a
// zero (Coord::zero()).
struct Coord {
  size_t part = kZeroCoordinate;
  size_t at = 0;
  static constexpr Coord zero() { return {}; }
};
// The coordinates IDX of PARTS, values of one field, type and placement,
// as one view of shape SHAPE (rank 1 when SHAPE is empty): coordinate k
// reads coordinate IDX[k].at of PARTS[IDX[k].part], or is zero. NumPy's
// fancy indexing over several arrays at once; one view node.
template <class F, class T, class P>
Ref<F, T, P> gather(const std::vector<Ref<F, T, P>> &parts,
                    const std::vector<Coord> &idx, Shape shape = {}) {
  if (parts.empty()) throw CompileError("gather: no parts");
  ViewSource src;
  src.reserve(idx.size());
  for (const Coord &c : idx) {
    if (c.part == kZeroCoordinate) {
      src.push_back({kZeroCoordinate, 0});
      continue;
    }
    if (c.part >= parts.size() || c.at >= parts[c.part].n)
      throw CompileError("gather: coordinate " + std::to_string(c.at) +
                         " of part " + std::to_string(c.part) +
                         " is out of range");
    src.push_back({parts[c.part].id, c.at});
  }
  if (shape.dims.empty()) shape = Shape(idx.size());
  if (shape.size() != idx.size())
    throw CompileError("gather: " + std::to_string(idx.size()) +
                       " coordinates for a shape of " +
                       std::to_string(shape.size()));
  return parts[0].view_of(src, shape.dims);
}
// PARTS, values of one field, type and placement, one after another along
// AXIS (their other axes agree): NumPy's concatenate, one view node.
template <class F, class T, class P>
Ref<F, T, P> concat(const std::vector<Ref<F, T, P>> &parts,
                    size_t axis = 0) {
  if (parts.empty()) throw CompileError("concat: no parts");
  std::vector<size_t> out = parts[0].dims();
  if (axis >= out.size())
    throw CompileError("concat: no axis " + std::to_string(axis));
  // The part and the offset along AXIS of each index of the output axis.
  std::vector<std::pair<size_t, size_t>> along;
  for (size_t p = 0; p < parts.size(); ++p) {
    const auto d = parts[p].dims();
    if (d.size() != out.size())
      throw CompileError("concat: the parts' ranks differ");
    for (size_t a = 0; a < d.size(); ++a)
      if (a != axis && d[a] != out[a])
        throw CompileError("concat: the parts differ on axis " +
                           std::to_string(a));
    for (size_t i = 0; i < d[axis]; ++i) along.push_back({p, i});
  }
  out[axis] = along.size();
  std::vector<Coord> idx;
  std::vector<size_t> ix(out.size(), 0);
  const size_t total = Shape(out).size();
  idx.reserve(total);
  for (size_t k = 0; k < total; ++k) {
    const auto [p, i] = along[ix[axis]];
    auto jx = ix;
    jx[axis] = i;
    const auto st = strides_of(parts[p].dims());
    size_t at = 0;
    for (size_t a = 0; a < jx.size(); ++a) at += jx[a] * st[a];
    idx.push_back({p, at});
    for (size_t a = out.size(); a-- > 0;) {
      if (++ix[a] < out[a]) break;
      ix[a] = 0;
    }
  }
  return gather(parts, idx, Shape(out));
}

template <class X>
struct IsRef : std::false_type {};
template <class F, class T, class P>
struct IsRef<Ref<F, T, P>> : std::true_type {};

// A per-proof input of N_BYTES bytes that only generators read
// (System::host_input): the uncommitted counterpart of a private input,
// filled through the Assignment. It is not a value handle, so no
// constraint, view, test or public computation can name it: reading it in
// a constraint is a C++ compile error.
struct HostInput {
  size_t id = SIZE_MAX;
  size_t n = 0;
};
template <class X>
struct IsHost : std::false_type {};
template <>
struct IsHost<HostInput> : std::true_type {};

// The bytes [OFFSET, OFFSET + LEN) of the byte node ID (a Bytes statement
// or a host input), as a depends_on entry: the closure receives them. A
// member of a Statement or Witness struct is one (relation.h).
struct BytesSlice {
  // No field: the closure reads bytes.
  struct NoField {
    static constexpr bool kCharacteristicTwo = false;
  };
  using field_type = NoField;
  using type_tag = Bytes;
  using place_tag = AnyPlace;
  size_t id = SIZE_MAX;
  size_t offset = 0, len = 0;
};
template <class X>
struct IsBytesSlice : std::false_type {};
template <>
struct IsBytesSlice<BytesSlice> : std::true_type {};
// The argument a closure receives for a depends_on entry (vector form): a Tensor
// of a value's elements, or a host input's bytes.
// A depends_on entry that is an expression (expr.h's ExprDep): it reads
// the nodes of its leaves, and a closure receives its values.
template <class R>
struct IsExprDep : std::false_type {};
// A depends_on entry with values in a field: a handle or an expression.
template <class R>
constexpr bool kIsValueDep = IsRef<R>::value || IsExprDep<R>::value;
template <class R, class = void>
struct DepArg {
  using type = std::vector<uint8_t>;
};
template <class R>
struct DepArg<R, std::enable_if_t<kIsValueDep<R> &&
                                  !is_bytes_v<typename R::type_tag>>> {
  using type = Tensor<typename R::field_type::Elt>;
};
// Whether a depends_on entry arrives as bytes: a host input or a Bytes statement.
template <class R, class = void>
struct IsBytesArg : std::true_type {};
template <class R>
struct IsBytesArg<R, std::enable_if_t<kIsValueDep<R>>>
    : std::bool_constant<is_bytes_v<typename R::type_tag>> {};
// The bytes a depends_on entry R that arrives as bytes reads: a host
// input's or a Bytes statement's, or the slice of one a BytesSlice names
// (a copy).
template <class R>
decltype(auto) dep_bytes(const ValueReader &v, const R &r) {
  const std::vector<uint8_t> &all = v.bytes.at(r.id);
  if constexpr (IsBytesSlice<R>::value) {
    if (r.offset + r.len > all.size())
      throw std::runtime_error("depends_on: a byte slice past its node");
    return std::vector<uint8_t>(all.begin() + long(r.offset),
                                all.begin() + long(r.offset + r.len));
  } else {
    return all;
  }
}

// What depends_on stores for an argument R: R itself (a handle or a host
// input), or for an expression its ExprDep (the specialization in expr.h).
template <class R, class = void>
struct DepEntry {
  using type = R;
  static const R &of(const R &r) { return r; }
};

// depends_on(...): the typed handles and expressions a declaration depends
// on. It lists an advice value's or a public computation's inputs (host
// inputs included), what a raw circuit reads, and the optional ordering
// hint of a challenge (the values it tests besides the inferred ones). An
// expression depends on the nodes of its leaves.
template <class... R>
struct Deps {
  std::tuple<R...> refs;
  std::vector<size_t> ids() const {
    std::vector<size_t> out;
    std::apply(
        [&](const auto &...r) {
          (
              [&](const auto &x) {
                if constexpr (IsExprDep<std::decay_t<decltype(x)>>::value) {
                  const auto d = x.ids();
                  out.insert(out.end(), d.begin(), d.end());
                } else {
                  out.push_back(x.id);
                }
              }(r),
              ...);
        },
        refs);
    return out;
  }
};
template <class... R>
Deps<typename DepEntry<R>::type...> depends_on(R... r) {
  static_assert(((IsRef<R>::value || IsHost<R>::value ||
                  IsBytesSlice<typename DepEntry<R>::type>::value ||
                  IsExprDep<typename DepEntry<R>::type>::value) &&
                 ...),
                "depends_on takes value handles, expressions, host inputs "
                "and the members of a Statement or Witness");
  return Deps<typename DepEntry<R>::type...>{
      std::make_tuple(typename DepEntry<R>::type(DepEntry<R>::of(r))...)};
}

// nat(fn): a generator closure over canonical integers (NatInt or uint64_t)
// in place of field elements; priv and pub closures convert both ways. A closure whose parameters are integers is read this way without
// the wrapper; one over field elements is not.
template <class Fn>
struct NatFn {
  Fn fn;
};
template <class Fn>
NatFn<Fn> nat(Fn fn) {
  return NatFn<Fn>{std::move(fn)};
}
template <class X>
struct IsNat : std::false_type {};
template <class Fn>
struct IsNat<NatFn<Fn>> : std::true_type {};

namespace nat_internal {
// The vector-form argument of a depends_on entry R over integers I: a
// Tensor of its canonical integers, or a host input's (Bytes statement's)
// bytes.
template <class I, class R>
using VecArg =
    std::conditional_t<IsBytesArg<R>::value, std::vector<uint8_t>, Tensor<I>>;
// FN(I, ...) -> I, one integer per entry (no host input).
template <class I, class Fn, class... R>
inline constexpr bool kElementwise =
    !(IsBytesArg<R>::value || ...) &&
    std::is_invocable_r_v<I, const Fn &, std::conditional_t<true, I, R>...>;
// FN(Tensor<I>, ...) -> std::vector<I>.
template <class I, class Fn, class... R>
inline constexpr bool kVector =
    std::is_invocable_r_v<std::vector<I>, const Fn &, const VecArg<I, R> &...>;
template <class I, class Fn, class... R>
inline constexpr bool kReads = kElementwise<I, Fn, R...> || kVector<I, Fn, R...>;
// The integer type FN reads: NatInt, else uint64_t, else void (FN reads no
// integers).
template <class Fn, class... R>
using Integer = std::conditional_t<
    kReads<NatInt, Fn, R...>, NatInt,
    std::conditional_t<kReads<uint64_t, Fn, R...>, uint64_t, void>>;
}  // namespace nat_internal

// ---------------------------------------------------------- lowerings --

// assert_range(v, n, MaxBound{m}): the compiler establishes v < N for a selected
// N with n <= N <= m.
struct MaxBound {
  Bound m;
};
// assert_range(v, n, Slack{}): v lies below n honestly, and soundly below
// some N >= n that the compiler selects up to the largest bound for which
// the integer equalities reading v (assert_int_equal) cannot wrap around
// p; the program relies on v >= 0 and those equalities only.
struct Slack {};
// A range request of domain DOMAIN (its index), number REQUEST there.
// max_table(T) raises the request's table cap to T (RangePolicy::
// max_table): the planner may then pick a table of up to T rows, and the
// compile report lists each table above the policy's cap as a warning.
template <class F>
struct RangeHandle {
  int domain = -1;
  size_t request = SIZE_MAX;
  // The request's table cap, shared with the request; 0 means the
  // domain's or the policy's.
  std::shared_ptr<Bound> cap;
  const RangeHandle &max_table(Bound T) const {
    if (!cap) fail("max_table: a range handle without its request");
    *cap = T;
    return *this;
  }
};

enum class RealizationKind : uint8_t {
  kDirect = 0,
  kDigits = 3,
  kTwoSided = 4,
  kImplied = 5,  // interval propagation: no needles, cells or rows
  // One needle n - 1 - v, for v with a known interval [lo, hi], lo >= 0
  // and hi + T < p (a v of n or more wraps to at least p + n - 1 - hi >= T).
  kComplement = 6,
};
inline const char *realization_name(RealizationKind k) {
  switch (k) {
    case RealizationKind::kDirect:
      return "direct";
    case RealizationKind::kDigits:
      return "digits";
    case RealizationKind::kTwoSided:
      return "two-sided";
    case RealizationKind::kComplement:
      return "complement";
    default:
      return "implied";
  }
}

// The range lowering's policy: its realizations and limits. The planner
// derives the domain's candidate tables from its range requests' bounds
// (range.h).
struct RangePolicy {
  std::string name = "candidates";
  uint32_t version = 2;
  // K: the most digits of a digit or two-sided realization.
  unsigned max_digits = 4;
  std::vector<RealizationKind> kinds = {
      RealizationKind::kDirect, RealizationKind::kComplement,
      RealizationKind::kDigits, RealizationKind::kTwoSided};
  bool bind_digit_views = true;
  size_t max_joint_candidates = 4096;
  // The most nodes the planner's branch and bound over the subsets of a
  // domain's candidate tables may visit; a domain that needs more fails the
  // compile, naming its candidates.
  size_t max_search_nodes = size_t(1) << 22;
  // Needles per range group: a table whose needles exceed the capacity is
  // split into groups that share alpha and the weights, each with its own
  // histograms and fraction tree. The capacity is the least of p - 1 (the
  // honest counts stay below p), the screen's (the largest group n with
  // (n + 2T - 1) / |K| <= 2^-group_error_bits) and GROUP_CAPACITY when it
  // is set (a profile override).
  size_t group_capacity = 0;
  double group_error_bits = 100;
  // The largest lookup table, in rows, the planner may pick for a range
  // request or a public table may have (lookup_rows): a larger table fails
  // the compile. A domain's max_table or a request's max_table raises it.
  // A table of T rows costs T committed multiplicities, T public weights
  // and T products in the fraction tree's circuit, which the planner weighs
  // at c_T per row (range.h's RangeCosts); the cap guards against a table
  // no realization should need.
  Bound max_table = Bound(1) << 14;
};

// The realization the planner selected for one request.
struct RangeRealization {
  RealizationKind kind = RealizationKind::kDirect;
  Bound table = 0;      // T
  unsigned k = 0;       // digits (kDigits, kTwoSided)
  Bound established = 0;  // the proven exclusive bound N
  size_t needles = 0;     // needles per request coordinate
  size_t coords = 0;      // new committed coordinates per coordinate
  bool bound = false;     // digits bind the request's node (no cell)
  // kImplied: the propagated integer interval [lo, hi] of the expression.
  SignedInt lo = 0, hi = 0;
  // kImplied of a plain request (by its value's type, a duplicate, or
  // another request on the same value): the interval is [0, plain_n - 1],
  // plain_n the bound that implies it.
  bool plain = false;
  Bound plain_n = 0;
  // Set by the emitter: whether the needles are late (an operand of
  // phase >= 1), and the node the digits bind (BOUND), x of an x + c
  // request when BOUND_OFFSET.
  bool late = false;
  size_t group = 0;  // the range group of its first needle coordinate
  size_t bound_id = SIZE_MAX;
  bool bound_offset = false;
  // The affine rows the emitter declares (their names, "" for none): the
  // reconstruction v - sum T^j d_j (digits, two-sided, unless the digits
  // bind v) and the top row (n - 1) - v - sum T^j h_j (two-sided).
  std::string recon_row, top_row;
  // The nodes looked up, per request coordinate one needle of each, in
  // order (the plan export's lookup realization).
  std::vector<size_t> needle_ids;
};

// A signed integer in decimal.
inline std::string int_str(const SignedInt &x) { return x.str(); }

// The MAC's polynomial basis: x^w = sum of x^tap in the MAC field.
struct MacBasis {
  size_t w;
  std::vector<unsigned> taps;
};
inline const MacBasis kMacBasisGF2_256{256, {10, 5, 2, 0}};

// The security a compile profile targets. It sets the field of a MAC
// between two odd domains, which the program does not list and no domain
// commits: GF(2^128) when classical, GF(2^256) when post-quantum.
enum class Security { kClassical, kPostQuantum };

// The compile profile: the policies of the lowering passes.
struct CompileProfile {
  std::string name = "default";
  uint32_t version = 1;
  RangePolicy range;
  std::vector<MacBasis> mac_bases = {kMacBasisGF2_256};
  Security security = Security::kPostQuantum;
  // The MAC ablation, a measurement control (benchmarks: gh-*-nomac), as
  // Longfellow's MAC ablation removes its MACs (longfellow-baselines
  // mdoc-v7-mac-ablation): the equalities across two domains lower to
  // nothing (compiler/lowering.h's MacEqualityLowering): no MAC, no pad,
  // challenge, tag or A tail. Every value either domain declares and every
  // other constraint stay. The system is unsound.
  bool unsound_no_mac = false;
  // The per-chunk MAC ablation, a measurement control as unsound_no_mac
  // is: the equalities between a binary and an odd domain lower to
  // Longfellow's per-chunk MAC (longfellow-baselines lib/circuits/mac) in
  // place of the polynomial MAC (compiler/mac.h's per_chunk_mac). The
  // shared bits split into chunks x_i of the binary field's width, the
  // prover commits a key share a_i per chunk in both domains and sends the
  // tag (beta + a_i) x_i in the clear after the key beta, and each domain
  // checks the tag of its own copy, the odd one by Longfellow's emulated
  // product (Karatsuba on bits, then reduction). Sound, but a zero chunk
  // has the tag zero, so the system is not zero-knowledge (the ML-DSA
  // challenge polynomial has zero chunks). Not combined with
  // unsound_no_mac.
  bool unsound_per_chunk_mac = false;
  // The width in bits of the MAC field between two odd domains.
  size_t odd_mac_bits() const {
    return security == Security::kClassical ? 128 : 256;
  }
};

namespace compiler {
class Lowering;
}  // namespace compiler

// Lowering::priv(..., masked_by(P)): only a Lowering makes one
// (Lowering::masked_by).
class MaskedBy {
 public:
  MaskedBy() = default;
  long pad() const { return pad_; }

 private:
  friend class compiler::Lowering;
  explicit MaskedBy(long p) : pad_(p) {}
  long pad_ = -1;
};

// A declared public map from a pad's value (N elements of FS) to the value
// of a pad copy (elements of FD). Only the factories below make one, and the
// core evaluates it, so no closure ever receives a pad. Its name and
// parameters enter the system digest.
template <class FS, class FD>
class PadMap {
 public:
  using In = std::vector<typename FS::Elt>;
  using Out = std::vector<typename FD::Elt>;

  // The pad itself, typed by its masking space (a pad of the Bit masking
  // space in characteristic 2 is a Bit).
  static PadMap identity() {
    static_assert(std::is_same_v<FS, FD>, "identity: one field");
    PadMap m("identity");
    m.keeps_space_ = m.same_field_ = true;
    m.out_n_ = [](size_t n) { return n; };
    m.apply_ = [](const In &x) { return x; };
    return m;
  }

  // The polynomial-basis coefficients of each element of the binary field
  // FS (Elt::operator[], coefficient of x^i), FS::kBits per element, as 0/1
  // elements of FD: a Bit vector. The MAC's blind copy B_A is this map of
  // the blind B.
  static PadMap polynomial_bits(const FD &fd) {
    static_assert(FS::kCharacteristicTwo, "polynomial_bits: a binary field");
    PadMap m("polynomial_bits");
    put_u64(m.params_, FS::kBits);
    m.type_ = Type{Base::kBit};
    m.out_n_ = [](size_t n) { return n * FS::kBits; };
    const FD *pf = &fd;
    m.apply_ = [pf](const In &x) {
      Out y;
      y.reserve(x.size() * FS::kBits);
      for (const auto &e : x)
        for (size_t i = 0; i < FS::kBits; ++i)
          y.push_back(ct::bit_elt(*pf, uint64_t(e[i])));
      return y;
    };
    return m;
  }

  // y = M x + c over one field, M of ROWS x COLS (row-major), c of ROWS: a
  // Field vector.
  static PadMap affine(const FD &f, size_t rows, size_t cols, Out mat,
                       Out c) {
    static_assert(std::is_same_v<FS, FD>, "affine: one field");
    if (mat.size() != rows * cols || c.size() != rows)
      throw CompileError("PadMap::affine: matrix or offset of the wrong size");
    PadMap m("affine");
    m.same_field_ = true;
    put_u64(m.params_, rows);
    put_u64(m.params_, cols);
    for (const auto &x : mat) put_elt(m.params_, f, x);
    for (const auto &x : c) put_elt(m.params_, f, x);
    m.out_n_ = [rows, cols](size_t n) {
      if (n != cols)
        throw CompileError("PadMap::affine: a pad of " + std::to_string(n) +
                           " elements, the matrix has " +
                           std::to_string(cols) + " columns");
      return rows;
    };
    const FD *pf = &f;
    m.apply_ = [pf, rows, cols, mat, c](const In &x) {
      Out y = c;
      for (size_t i = 0; i < rows; ++i)
        for (size_t j = 0; j < cols; ++j)
          pf->add(y[i], pf->mulf(mat[i * cols + j], x[j]));
      return y;
    };
    return m;
  }

  const std::string &name() const { return name_; }
  const std::vector<uint8_t> &params() const { return params_; }
  size_t out_n(size_t in_n) const { return out_n_(in_n); }
  bool keeps_space() const { return keeps_space_; }
  bool same_field() const { return same_field_; }
  Type type() const { return type_; }
  Out operator()(const In &x) const { return apply_(x); }

 private:
  explicit PadMap(std::string name) : name_(std::move(name)) {}
  static void put_elt(std::vector<uint8_t> &out, const FD &f,
                      const typename FD::Elt &x) {
    uint8_t b[FD::kBytes];
    f.to_bytes_field(b, x);
    out.insert(out.end(), b, b + FD::kBytes);
  }
  std::string name_;
  std::vector<uint8_t> params_;
  bool keeps_space_ = false, same_field_ = false;
  Type type_{Base::kField};
  std::function<size_t(size_t)> out_n_;
  std::function<Out(const In &)> apply_;
};

// The identity of a public computation's function, for the system digest:
// a declared name and its parameters (pub with a closure).
struct Computes {
  std::string name;
  std::vector<uint8_t> params = {};
};
// A Computes whose parameters are integers.
inline Computes computes(std::string name,
                         std::initializer_list<uint64_t> params = {}) {
  Computes c{std::move(name), {}};
  for (uint64_t x : params) put_u64(c.params, x);
  return c;
}

// A statement codec applied to each row (the leading axis) of a shaped
// statement value: PRED takes a row (a Tensor of elements, or the row's
// bytes for a Bytes statement). One malformed row rejects the statement.
template <class Pred>
struct PerRow {
  Computes id;
  Pred pred;
};
template <class Pred>
PerRow<Pred> per_row(Computes id, Pred pred) {
  return PerRow<Pred>{std::move(id), std::move(pred)};
}

// Bytes packed densely into elements of F, for absorption: each subfield
// coordinate of an element holds the most bytes below its characteristic
// (every byte of a binary subfield; 7 bytes of a Goldilocks coordinate; 1
// byte of an F_q coordinate with q < 2^16), little-endian, the rest zero.
// For a fixed length the packing is injective.
template <class F>
size_t pack_bytes_per_coordinate(const F &f) {
  if constexpr (F::kCharacteristicTwo) {
    return domain_subfield<F>::kBytes;
  } else {
    // p >= 2^(8 (k + 1)); at most 15 bytes, below 2^128 (F_p256 packs 15
    // bytes per element, as the shipped plans do).
    size_t k = 0;
    while (k < domain_subfield<F>::kBytes && k + 1 < 16 &&
           characteristic_above(f, (Bound(1) << (8 * (k + 1))) - 1))
      ++k;
    if (k == 0) fail("pack_bytes: the prime field holds no byte");
    return k;
  }
}
// A field whose serialization is its subfield coordinates side by side,
// each in kSubFieldBytes bytes; the native fields F_q^k pack their
// coordinates in kIntegerBits + 1 bits instead (F_{q^11}: 23-bit
// coordinates in 32 bytes).
template <class F>
constexpr bool kCoordinateAligned =
    F::kCharacteristicTwo || !ExtensionTraits<F>::supported ||
    F::kBytes == ExtensionTraits<F>::degree * F::kSubFieldBytes;
template <class F>
std::vector<typename F::Elt> pack_bytes(const F &f,
                                        const std::vector<uint8_t> &b) {
  const size_t k = pack_bytes_per_coordinate(f);
  std::vector<typename F::Elt> out;
  if constexpr (!kCoordinateAligned<F>) {
    // Each coordinate's value over the extension basis of F over its
    // prime field (zk_extension_packed.h): an injective packing whatever
    // the serialization.
    constexpr size_t D = ExtensionTraits<F>::degree;
    const auto &basis = ExtensionBasis<F>::get(f).beta;
    for (size_t at = 0; at < b.size(); at += k * D) {
      typename F::Elt e = f.zero();
      for (size_t j = 0; j < D; ++j) {
        uint64_t v = 0;
        for (size_t i = 0; i < k && at + j * k + i < b.size(); ++i)
          v |= uint64_t(b[at + j * k + i]) << (8 * i);
        f.add(e, f.mulf(f.of_scalar(v), basis[j]));
      }
      out.push_back(e);
    }
    return out;
  }
  const size_t coords = F::kBytes / domain_subfield<F>::kBytes;
  const size_t per = k * coords;
  for (size_t at = 0; at < b.size(); at += per) {
    uint8_t buf[F::kBytes] = {};
    for (size_t j = 0; j < coords; ++j)
      for (size_t i = 0; i < k && at + j * k + i < b.size(); ++i)
        buf[j * domain_subfield<F>::kBytes + i] = b[at + j * k + i];
    auto e = f.of_bytes_field(buf);
    if (!e) fail("pack_bytes: a packed element is not canonical");
    out.push_back(*e);
  }
  return out;
}



}  // namespace proofs::gordiehowe

#endif  // PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_CORE_H_
