-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.ProofSystem.Ligero.Completeness
public import GordieHowe.ProofSystem.Ligero.Preparation
public import GordieHowe.ProofSystem.Ligero.Layout

@[expose] public section

/-!
# The fixed Shape layout for prepared Ligero rows

`Shape` is the concrete block layout: source witnesses occupy the witness-row
suffix, product copies occupy the three product-row groups, and every unused
product slot is zero.  This file records the layout compatibility needed by
the generic prepared encoding.  In particular, source and copy locations are
injective for the canonical `Shape.placement`; arbitrary placements do not
inherit this fact.
-/

namespace GordieHowe.Ligero.ShapeEncoding
open IOP

open Polynomial
open MvPolynomial
open scoped Classical
section

variable {F : Type} [Field F] {N : ℕ}
  (S : Layout.Shape) (C : GordieHowe.RSCode F N)
  (hk : C.k = S.r + S.w)
  (nodes : Fin C.k → F) (hnodes : Function.Injective nodes)

/-- The canonical Shape location map has no aliases. -/
theorem placement_location_injective :
    Function.Injective (Preparation.Placement.location
      (S.placement C hk nodes hnodes) : Routing.Prepared (Fin S.nw) (Fin S.nq) →
      Fin (S.dataRows + 1) × Fin C.k) := by
  intro x y hxy
  cases x with
  | inl i =>
      cases y with
      | inl j =>
          have hr := congrArg (fun z => z.1.val) hxy
          have hc := congrArg (fun z => z.2.val) hxy
          simp [Layout.Shape.placement, Preparation.Placement.location,
            Layout.Shape.source, Layout.Shape.column] at hr hc
          have hdiv : i.val / S.w = j.val / S.w := by omega
          have hmod : i.val % S.w = j.val % S.w := by omega
          apply congrArg Sum.inl
          apply Fin.ext
          calc
            i.val = i.val / S.w * S.w + i.val % S.w :=
              by simpa [Nat.mul_comm] using (Nat.div_add_mod i.val S.w).symm
            _ = j.val / S.w * S.w + j.val % S.w := by rw [hdiv, hmod]
            _ = j.val := by simpa [Nat.mul_comm] using Nat.div_add_mod j.val S.w
      | inr js =>
          have hr := congrArg (fun z => z.1.val) hxy
          have hi := i.isLt
          have hg := S.block_lt hi
          have hs := js.2.isLt
          have hq := js.1.isLt
          have hsource : i.val / S.w < S.witnessRows := by
            simpa [Layout.Shape.witnessRows] using hg
          have hproduct : S.witnessRows <
              1 + S.witnessRows + js.2.val * S.productGroups + js.1.val / S.w := by
            exact Nat.lt_of_lt_of_le (Nat.lt_add_of_pos_left (n := S.witnessRows)
              (k := 1) (by decide)) (by
                simpa [Nat.add_assoc] using
                  (Nat.le_add_right (1 + S.witnessRows)
                    (js.2.val * S.productGroups + js.1.val / S.w)))
          simp [Layout.Shape.placement, Preparation.Placement.location,
            Layout.Shape.source, Layout.Shape.products,
            Layout.Shape.column] at hr
          dsimp [Layout.Shape.parameters, Layout.Shape.products] at hr
          change 1 + i.val / S.w =
            1 + S.witnessRows + js.2.val * S.productGroups + js.1.val / S.w at hr
          omega
  | inr i =>
      cases y with
      | inl j =>
          have hr := congrArg (fun z => z.1.val) hxy
          have hi := i.2.isLt
          have hq := i.1.isLt
          have hs := j.isLt
          have hsource : j.val / S.w < S.witnessRows := by
            simpa [Layout.Shape.witnessRows] using (S.block_lt hs)
          have hproduct : S.witnessRows <
              1 + S.witnessRows + i.2.val * S.productGroups + i.1.val / S.w := by
            exact Nat.lt_of_lt_of_le (Nat.lt_add_of_pos_left (n := S.witnessRows)
              (k := 1) (by decide)) (by
                simpa [Nat.add_assoc] using
                  (Nat.le_add_right (1 + S.witnessRows)
                    (i.2.val * S.productGroups + i.1.val / S.w)))
          simp [Layout.Shape.placement, Preparation.Placement.location,
            Layout.Shape.source, Layout.Shape.products,
            Layout.Shape.column] at hr
          dsimp [Layout.Shape.parameters, Layout.Shape.products] at hr
          change 1 + S.witnessRows + i.2.val * S.productGroups + i.1.val / S.w =
            1 + j.val / S.w at hr
          omega
      | inr js =>
          have hr := congrArg (fun z => z.1.val) hxy
          have hc := congrArg (fun z => z.2.val) hxy
          have hsi := js.2.isLt
          have hsj := i.2.isLt
          have hqi := i.1.isLt
          have hqj := js.1.isLt
          simp [Layout.Shape.placement, Preparation.Placement.location,
            Layout.Shape.products, Layout.Shape.column] at hr hc
          dsimp [Layout.Shape.parameters, Layout.Shape.products] at hr hc
          rcases i with ⟨iq, si⟩
          rcases js with ⟨jq, sj⟩
          change 1 + S.witnessRows + si.val * S.productGroups + iq.val / S.w =
            1 + S.witnessRows + sj.val * S.productGroups + jq.val / S.w at hr
          change iq.val % S.w = jq.val % S.w at hc
          have hgi : iq.val / S.w < S.productGroups := by
            change iq.val / S.w < S.blocks S.nq
            exact S.block_lt iq.isLt
          have hgj : jq.val / S.w < S.productGroups := by
            change jq.val / S.w < S.blocks S.nq
            exact S.block_lt jq.isLt
          have hqdiv_nonneg : 0 ≤ jq.val / S.w := Nat.zero_le _
          have hqdiv_i_nonneg : 0 ≤ iq.val / S.w := Nat.zero_le _
          have hqi_lt : iq.val < S.productGroups * S.w :=
            (Nat.div_lt_iff_lt_mul S.width_pos).mp hgi
          have hqj_lt : jq.val < S.productGroups * S.w :=
            (Nat.div_lt_iff_lt_mul S.width_pos).mp hgj
          have hslot : si.val = sj.val := by
            fin_cases si <;> fin_cases sj
            all_goals
              have hnonneg : 0 ≤ jq.val / S.w := Nat.zero_le _
              norm_num [Nat.succ_mul] at hr hgi hgj hqi_lt hqj_lt ⊢ <;>
                (try simp) <;> omega
          have hdiv : iq.val / S.w = jq.val / S.w := by
            rw [hslot] at hr
            omega
          have hmod : iq.val % S.w = jq.val % S.w := by omega
          have hq : iq.val = jq.val := by
            calc
              iq.val = iq.val / S.w * S.w + iq.val % S.w :=
                by simpa [Nat.mul_comm] using (Nat.div_add_mod iq.val S.w).symm
              _ = jq.val / S.w * S.w + jq.val % S.w := by rw [hdiv, hmod]
              _ = jq.val := by simpa [Nat.mul_comm] using Nat.div_add_mod jq.val S.w
          exact congrArg Sum.inr (Prod.ext (Fin.ext hq) (Fin.ext hslot))

variable {Lin : Type} [Fintype Lin]
  {hrate : 2 * C.k - 1 ≤ N}

theorem product_location_at (S : Layout.Shape) (C : GordieHowe.RSCode F N)
    (hk : C.k = S.r + S.w) (nodes : Fin C.k → F) (hnodes : Function.Injective nodes)
    (q : Fin S.productGroups) (slot : Fin 3) (j : Fin C.k)
    (hj : S.r ≤ j.val) (hm : q.val * S.w + (j.val - S.r) < S.nq) :
    (Preparation.Placement.location (S.placement C hk nodes hnodes)
      (.inr (⟨q.val * S.w + (j.val - S.r), hm⟩, slot))) =
      (S.products q slot, j) := by
  have hcol : j.val - S.r < S.w := by
    have := j.isLt
    omega
  have hdiv : (q.val * S.w + (j.val - S.r)) / S.w = q.val := by
    apply Nat.div_eq_of_lt_le
    · omega
    · simp [Nat.succ_mul]
      omega
  have hrem : (q.val * S.w + (j.val - S.r)) % S.w = j.val - S.r := by
    have h := Nat.div_add_mod (q.val * S.w + (j.val - S.r)) S.w
    rw [hdiv] at h
    simpa [Nat.mul_comm] using h
  apply Prod.ext
  · apply Fin.ext
    simp [Layout.Shape.placement, Preparation.Placement.location,
      Layout.Shape.parameters, Layout.Shape.products, hdiv]
  · apply Fin.ext
    simp [Layout.Shape.placement, Preparation.Placement.location,
      Layout.Shape.parameters, Layout.Shape.column, hrem]
    omega

theorem product_location_iff (S : Layout.Shape) (C : GordieHowe.RSCode F N)
    (hk : C.k = S.r + S.w) (nodes : Fin C.k → F) (hnodes : Function.Injective nodes)
    (q : Fin S.productGroups) (slot : Fin 3) (j : Fin C.k) (hj : S.r ≤ j.val) :
    (∃ z : Routing.Prepared (Fin S.nw) (Fin S.nq),
      (Preparation.Placement.location (S.placement C hk nodes hnodes)) z =
        (S.products q slot, j)) ↔
      q.val * S.w + (j.val - S.r) < S.nq := by
  constructor
  · rintro ⟨z, hz⟩
    cases z with
    | inl i =>
        have hr := congrArg (fun x => x.1.val) hz
        have hi := i.isLt
        have hsource : i.val / S.w < S.witnessRows := by
          simpa [Layout.Shape.witnessRows] using S.block_lt hi
        have hprod : S.witnessRows <
            1 + S.witnessRows + slot.val * S.productGroups + q.val := by
          exact Nat.lt_of_lt_of_le (Nat.lt_add_of_pos_left (n := S.witnessRows)
            (k := 1) (by decide)) (by
              simpa [Nat.add_assoc] using
                Nat.le_add_right (1 + S.witnessRows)
                  (slot.val * S.productGroups + q.val))
        simp [Layout.Shape.placement, Preparation.Placement.location,
          Layout.Shape.source, Layout.Shape.products] at hr
        omega
    | inr qs =>
        rcases qs with ⟨q', s'⟩
        have hr := congrArg (fun x => x.1.val) hz
        have hc := congrArg (fun x => x.2.val) hz
        simp [Layout.Shape.placement, Preparation.Placement.location,
          Layout.Shape.products, Layout.Shape.column] at hr hc
        dsimp [Layout.Shape.parameters, Layout.Shape.products] at hr hc
        have hgroup : q'.val / S.w = q.val := by
          have hgi : q'.val / S.w < S.productGroups := by
            change q'.val / S.w < S.blocks S.nq
            exact S.block_lt q'.isLt
          have hq : q.val < S.productGroups := q.isLt
          have hqdiv : 0 ≤ q'.val / S.w := Nat.zero_le _
          have hqval : 0 ≤ q.val := Nat.zero_le _
          fin_cases s' <;> fin_cases slot
          all_goals
            norm_num [Nat.succ_mul] at hr ⊢ <;> omega
        have hrem : q'.val % S.w = j.val - S.r := by
          have hcol : j.val - S.r < S.w := by omega
          omega
        have hdecomp := Nat.div_add_mod q'.val S.w
        rw [hgroup, hrem] at hdecomp
        have heq : q.val * S.w + (j.val - S.r) = q'.val := by
          simpa [Nat.mul_comm] using hdecomp
        omega
  · intro hm
    exact ⟨.inr (⟨q.val * S.w + (j.val - S.r), hm⟩, slot),
      product_location_at S C hk nodes hnodes q slot j hj hm⟩

end
end GordieHowe.Ligero.ShapeEncoding
