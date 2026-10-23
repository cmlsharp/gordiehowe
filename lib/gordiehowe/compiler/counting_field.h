// Copyright 2026 Chad Sharp and Paul Grubbs
// SPDX-License-Identifier: Apache-2.0

// GordieHowe: a field that counts its operations, for the batch kernels'
// operation counts (op_counts.h).
//
// CountingField<F> wraps a field F (fields cannot be copied) and forwards
// the field interface the batch kernels use, tallying multiplications,
// additions (and subtractions and negations), multiply-accumulates,
// reductions and inversions in its counts. The batch kernels are templates
// on their field, so a kernel over CountingField<F> runs F's arithmetic and
// reports the work it did; the placement cost prices those counts
// (op_counts.h). The production kernels are instantiated over F alone, so
// they count nothing.

#ifndef PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_COMPILER_COUNTING_FIELD_H_
#define PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_COMPILER_COUNTING_FIELD_H_

#include <cstddef>
#include <cstdint>
#include <type_traits>
#include <utility>

#include "gordiehowe/compiler/op_count_types.h"
#include "sumcheck/boolean_skip.h"
#include "zk/zk_extension_packed.h"

namespace proofs::gordiehowe::compiler {
template <class F>
class CountingField;

namespace counting_internal {
// The constants only some fields have.
template <class F, class = void>
struct Optional {};
template <class F>
struct Optional<F, std::void_t<decltype(F::kSubFieldLogBits)>> {
  static constexpr size_t kSubFieldLogBits = F::kSubFieldLogBits;
};
template <class F, class = void>
struct OptionalN {};
template <class F>
struct OptionalN<F, std::void_t<typename F::N>> {
  using N = typename F::N;
};
}  // namespace counting_internal
}  // namespace proofs::gordiehowe::compiler

namespace proofs {
// CountingField<F> has F's structure.
template <class F>
struct ExtensionTraits<gordiehowe::compiler::CountingField<F>>
    : ExtensionTraits<F> {};
template <class F>
struct SkipByteField<gordiehowe::compiler::CountingField<F>>
    : SkipByteField<F> {};
}  // namespace proofs

namespace proofs::gordiehowe::compiler {

template <class F>
class CountingField : public counting_internal::Optional<F>,
                      public counting_internal::OptionalN<F> {
 public:
  using Field = F;
  using Elt = typename F::Elt;
  using Accum = typename F::Accum;
  static constexpr bool kCharacteristicTwo = F::kCharacteristicTwo;
  static constexpr size_t kBits = F::kBits;
  static constexpr size_t kBytes = F::kBytes;
  static constexpr size_t kSubFieldBits = F::kSubFieldBits;
  static constexpr size_t kSubFieldBytes = F::kSubFieldBytes;

  explicit CountingField(const F &f) : f_(f) {}
  CountingField(const CountingField &) = delete;
  CountingField &operator=(const CountingField &) = delete;

  // The field counted, and the tallies so far.
  const F &field() const { return f_; }
  OpCounts &counts() const { return counts_; }

  // Counted.
  void add(Elt &a, const Elt &y) const {
    ++counts_.add;
    f_.add(a, y);
  }
  void sub(Elt &a, const Elt &y) const {
    ++counts_.add;
    f_.sub(a, y);
  }
  void mul(Elt &a, const Elt &y) const {
    ++counts_.mul;
    f_.mul(a, y);
  }
  void neg(Elt &a) const {
    ++counts_.add;
    f_.neg(a);
  }
  Elt addf(const Elt &a, const Elt &y) const {
    ++counts_.add;
    return f_.addf(a, y);
  }
  Elt subf(const Elt &a, const Elt &y) const {
    ++counts_.add;
    return f_.subf(a, y);
  }
  Elt mulf(const Elt &a, const Elt &y) const {
    ++counts_.mul;
    return f_.mulf(a, y);
  }
  Elt negf(const Elt &a) const {
    ++counts_.add;
    return f_.negf(a);
  }
  Elt invertf(const Elt &a) const {
    ++counts_.inv;
    return f_.invertf(a);
  }
  void mac(Accum &acc, const Elt &x, const Elt &y) const {
    ++counts_.mac;
    f_.mac(acc, x, y);
  }
  Elt reduce(const Accum &acc) const {
    ++counts_.reduce;
    return f_.reduce(acc);
  }

  // Forwarded, not counted: constants, embeddings and codecs.
  // F's own return types (a reference for some fields, a value for
  // others).
  decltype(auto) zero() const { return f_.zero(); }
  decltype(auto) one() const { return f_.one(); }
  decltype(auto) mone() const { return f_.mone(); }
  Elt of_scalar(uint64_t a) const { return f_.of_scalar(a); }
  template <class... A>
  auto of_scalar_field(A &&...a) const {
    return f_.of_scalar_field(std::forward<A>(a)...);
  }
  template <class... A>
  auto of_string(A &&...a) const {
    return f_.of_string(std::forward<A>(a)...);
  }
  template <class... A>
  auto beta(A &&...a) const {
    return f_.beta(std::forward<A>(a)...);
  }
  bool in_subfield(const Elt &x) const { return f_.in_subfield(x); }
  template <class... A>
  void to_bytes_field(A &&...a) const {
    f_.to_bytes_field(std::forward<A>(a)...);
  }
  template <class... A>
  void to_bytes_subfield(A &&...a) const {
    f_.to_bytes_subfield(std::forward<A>(a)...);
  }
  template <class... A>
  auto of_bytes_field(A &&...a) const {
    return f_.of_bytes_field(std::forward<A>(a)...);
  }
  template <class... A>
  auto of_bytes_subfield(A &&...a) const {
    return f_.of_bytes_subfield(std::forward<A>(a)...);
  }
  template <class G>
  Elt sample(G &&g) const {
    return f_.sample(std::forward<G>(g));
  }
  template <class G>
  Elt sample_subfield(G &&g) const {
    return f_.sample_subfield(std::forward<G>(g));
  }

 private:
  const F &f_;
  mutable OpCounts counts_;
};

}  // namespace proofs::gordiehowe::compiler

#endif  // PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_COMPILER_COUNTING_FIELD_H_
