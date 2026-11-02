-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Language.RealizedProgram
public import GordieHoweNative.Language.RealizedProgram.IvlSource

@[expose] public section

/-!
# The sources of the values' intervals

The rule, with the predicates or the entry it reads, that justifies a value's interval
(`GordieHowe.RealizedProgram.IvlSource`), and the sources each kind of value takes
(`GordieHowe.RealizedProgram.IvlSource.allows`). The rules themselves are checked by
`GordieHowe.RealizedProgram.ivlAt` (`GordieHowe/Language/RealizedProgram/RealizationValid.lean`).
A leaf module, so that the structure records (`GordieHowe.RealizedProgram.Structure`,
`GordieHoweNative/Language/RealizedProgram/Structure.lean`) can name a value's source.

The definitions are in `GordieHoweNative/Language/RealizedProgram/IvlSource.lean`
(the compiled library `GordieHoweNative`); this module has their lemmas.
-/

namespace GordieHowe.RealizedProgram

/-- **A constant takes only its entries**, and only a constant does. -/
theorem IvlSource.allows_const {k : Kind} (h : IvlSource.allows k .const = true) :
    ∃ es, k = .constant es := by
  rcases k with _ | ⟨_ | ⟨n, _ | ⟨a, as⟩⟩ | x⟩ | es | c | _ | ⟨w, sel⟩ | ⟨u, mp⟩ | u | x <;>
    simp_all [IvlSource.allows]

/-- **Only an opaque value computed from arguments takes its `Bit` type.** -/
theorem IvlSource.allows_opaqueBit {k : Kind} (h : IvlSource.allows k .opaqueBit = true) :
    ∃ name a args, k = .pub (.opaque name (a :: args)) := by
  rcases k with _ | ⟨_ | ⟨n, _ | ⟨a, as⟩⟩ | x⟩ | es | c | _ | ⟨w, sel⟩ | ⟨u, mp⟩ | u | x <;>
    simp_all [IvlSource.allows]

/-- **Only a bound value takes an `in` read centred.** -/
theorem IvlSource.allows_shiftRange {k : Kind} {q : Nat}
    (h : IvlSource.allows k (.shiftRange q) = true) : ∃ x, k = .bound x := by
  rcases k with _ | ⟨_ | ⟨n, _ | ⟨a, as⟩⟩ | x⟩ | es | c | _ | ⟨w, sel⟩ | ⟨u, mp⟩ | u | x <;>
    simp_all [IvlSource.allows]

/-- **A value taking a source other than its entries or an `in` read centred is neither a constant
nor bound.** -/
theorem IvlSource.allows_other {k : Kind} {s : IvlSource} (h : s.allows k = true)
    (hc : s ≠ .const) (hb : ∀ q, s ≠ .shiftRange q) :
    (∀ es, k ≠ .constant es) ∧ ∀ x, k ≠ .bound x := by
  constructor
  · rintro es rfl
    cases s <;> simp_all [IvlSource.allows]
  · rintro x rfl
    cases s <;> simp_all [IvlSource.allows]

end GordieHowe.RealizedProgram
