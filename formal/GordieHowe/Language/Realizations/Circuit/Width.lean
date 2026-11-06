-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Language.Assumptions
public import GordieHoweNative.ProofSystem.Program.ForkNums

/-! # The numeric circuit width

These logarithm lemmas are shared by the GKR checker and the program figure reader without
importing either soundness graph into the other.
-/

public section

namespace GordieHowe.RealizedProgram
variable (ir : RealizedProgram)

/-- Doubling from a power of two computes the ceiling logarithm within its fuel bound. -/
theorem clog2_go_eq (n p k f : ℕ) (hp : p = 2 ^ k) (hk : k ≤ Nat.clog 2 n)
    (hf : n ≤ 2 ^ (k + f)) : clog2.go n p k f = Nat.clog 2 n := by
  induction f generalizing p k with
  | zero =>
    have := (Nat.clog_le_iff_le_pow (by norm_num : 1 < 2)).2 hf
    simp only [clog2.go]
    omega
  | succ f ih =>
    simp only [clog2.go]
    split
    · rename_i h
      have := (Nat.clog_le_iff_le_pow (by norm_num : 1 < 2)).2 (hp ▸ h)
      omega
    · rename_i h
      have hlt : k < Nat.clog 2 n := by
        by_contra hc
        exact h (hp ▸ (Nat.clog_le_iff_le_pow (by norm_num : 1 < 2)).1 (by omega))
      have hf' : n ≤ 2 ^ (k + 1 + f) := by rw [show k + 1 + f = k + (f + 1) by omega]; exact hf
      exact ih (2 * p) (k + 1) (by rw [hp, pow_succ]; ring) hlt hf'

/-- The numeric ceiling logarithm equals the semantic logarithm, including zero and one. -/
theorem clog2_eq (n : ℕ) : clog2 n = Nat.clog 2 n :=
  clog2_go_eq n 1 0 n rfl (Nat.zero_le _) (by rw [zero_add]; exact (Nat.lt_two_pow_self).le)

/-- The semantic circuit width equals the existing numeric reader width. -/
theorem circuitWidth_eq (c : ℕ) : ir.circuitWidth c = ForkReader.circW ir c := by
  rw [circuitWidth, ForkReader.circW, clog2_eq]

end GordieHowe.RealizedProgram
