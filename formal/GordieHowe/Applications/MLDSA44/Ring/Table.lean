-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Language.Library.TableSelect
public import GordieHowe.Language.RealizedProgram.Check

@[expose] public section

/-!
# The ML-DSA-44 rings' public table

The row maps of the ML-DSA-44 rings' public table (`lib/gordiehowe/examples/rings/mldsa_ring.h`,
`member.table`): a row is a member's key record `â ‖ t₁` (`20` blocks of `256` coefficients) and
the `24` limbs of its message representative `μ`, the column blocks `ring.keys` (`[64, 5120]`) and
`ring.mu` (`[64, 24]`).

* `nativeMap`: the native rings' map, `21` identity leaves (`20` of `256` cells, then `24`).
* `carrierMap`: the carriers' map, the `20` key leaves the scheme-order negacyclic transform of
  length `256` at the Goldilocks root `carrierPsi` (a key's `â` and `t₁` are committed as their
  FIPS 204 spectra over the carrier field), then the identity leaf of `24`.
-/

namespace GordieHowe.MLDSA44.Ring

open RealizedProgram

/-- **The native rings' row map**: `20` identity leaves of `256` cells, then one of `24`. -/
def nativeMap : List RowLeaf :=
  (List.range 20).map (fun i => ⟨false, false, 256, 256 * i, 0⟩) ++ [⟨false, false, 24, 5120, 0⟩]

/-- **The carriers' transform root** (`ψ` of length `256` over Goldilocks, the natural of the
C++ encoding). -/
abbrev carrierPsi : ℕ := 1803076106186727246

/-- **The carriers' row map**: `20` scheme-order transforms of length `256` at `carrierPsi`, then
an identity leaf of `24` cells. -/
def carrierMap : List RowLeaf :=
  (List.range 20).map (fun i => ⟨true, false, 256, 256 * i, carrierPsi⟩) ++
    [⟨false, false, 24, 5120, 0⟩]

end GordieHowe.MLDSA44.Ring

namespace GordieHowe.MLDSA44.Ring.Native

open RealizedProgram

/-! ## The values a shared expression reads, through a closed set of entries -/

section Closure

variable {ir : RealizedProgram} {S R : List ℕ}

/-- **The values an entry reads, through its entries**, lie in `S` where every entry of a set `R`
closed under reading reads directly only values of `S`. -/
theorem refClosure_sub
    (hR : ∀ k ∈ R, (∀ u ∈ (ir.expr k).directNodes, u ∈ S) ∧ ∀ k' ∈ (ir.expr k).refs, k' ∈ R) :
    ∀ n k, k ∈ R → ∀ u ∈ ir.refClosure Expr.directNodes n k, u ∈ S
  | 0, _, _, u, hu => by simp [RealizedProgram.refClosure] at hu
  | n + 1, k, hk, u, hu => by
    rw [RealizedProgram.refClosure, List.mem_append, List.mem_flatMap] at hu
    rcases hu with hu | ⟨k', hk', hu⟩
    · exact (hR k hk).1 u hu
    · exact refClosure_sub hR n k' ((hR k hk).2 k' hk') u hu

/-- **The values an expression reads** (`exprNodes`) lie in `S` where it reads directly only values
of `S` and entries of a closed set `R` reading directly only values of `S`. -/
theorem exprNodes_sub {e : Expr} (he : ∀ u ∈ e.directNodes, u ∈ S) (hr : ∀ k ∈ e.refs, k ∈ R)
    (hR : ∀ k ∈ R, (∀ u ∈ (ir.expr k).directNodes, u ∈ S) ∧ ∀ k' ∈ (ir.expr k).refs, k' ∈ R) :
    ∀ u ∈ ir.exprNodes e, u ∈ S := by
  intro u hu
  unfold RealizedProgram.exprNodes RealizedProgram.closure at hu
  rw [List.mem_append, List.mem_flatMap] at hu
  rcases hu with hu | ⟨k, hk, hu⟩
  · exact he u hu
  · exact refClosure_sub hR _ k (hr k hk) u hu

/-- **A public expression's dependencies lie in `S`** (`exprNodes_sub`). -/
theorem valueDeps_sub {v : ℕ} {e : Expr} (hk : (ir.value v).kind = .pub (.expr e))
    (he : ∀ u ∈ e.directNodes, u ∈ S) (hr : ∀ k ∈ e.refs, k ∈ R)
    (hR : ∀ k ∈ R, (∀ u ∈ (ir.expr k).directNodes, u ∈ S) ∧ ∀ k' ∈ (ir.expr k).refs, k' ∈ R) :
    ∀ u ∈ ir.valueDeps v, u ∈ S := by
  unfold RealizedProgram.valueDeps
  rw [hk]
  exact exprNodes_sub he hr hR

/-- **A public expression's reads** are those of the values of `S` (`exprNodes_sub`). -/
theorem nodeReads_sub {v n : ℕ} {e : Expr} (hk : (ir.value v).kind = .pub (.expr e))
    (he : ∀ u ∈ e.directNodes, u ∈ S) (hr : ∀ k ∈ e.refs, k ∈ R)
    (hR : ∀ k ∈ R, (∀ u ∈ (ir.expr k).directNodes, u ∈ S) ∧ ∀ k' ∈ (ir.expr k).refs, k' ∈ R)
    {P : Read → Prop} (hS : ∀ u ∈ S, ∀ rd ∈ ir.nodeReads n u, P rd) :
    ∀ rd ∈ ir.nodeReads (n + 1) v, P rd := by
  intro rd hrd
  rw [RealizedProgram.nodeReads] at hrd
  rw [hk] at hrd
  simp only [List.mem_flatMap] at hrd
  obtain ⟨u, hu, hrd⟩ := hrd
  exact hS u (exprNodes_sub he hr hR u hu) rd hrd

end Closure


end GordieHowe.MLDSA44.Ring.Native
