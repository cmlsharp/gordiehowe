-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Language.Realizations.Derivation.ProductMod
public import GordieHowe.Language.Realizations.Derivation.Events
public import GordieHoweNative.Language.Realizations.Derivation.TableKernel

@[expose] public section

/-!
# GordieHowe: the kernel of a product form from a public-table selection

The interval source `tableKernel` (`lib/gordiehowe/compiler/derivation_check.h`, `src tableKernel`)
bounds the coefficients of the polynomial whose spectrum a product form's kernel holds, when that
spectrum is selected from a public table (`lib/gordiehowe/lib/table.h`, `select_row`): the
selection's record is, block by block, the leaf transform of a row's blocks of the table (one block
for a single-leaf record). The C++ checks the
bounds' fit and trusts the hull; the rule here recomputes it (`tableKernelFact`): the table's value
has a declared range `[0, B)` (`sr`), so a row's entries lie in `[0, B − 1]`, within `[lo, hi]`.

The selection holds only up to its fingerprint (`SelEvent`): where every field `equal` of rank below
the derivation's holds and the selection event does not occur, every block of the record is the
transform of a block of one row (`SelExact`), and the inverse transform returns that block
(`tableKernelFact_sound`).

The definitions are in `GordieHoweNative/Language/Realizations/Derivation/TableKernel.lean`
(the compiled library `GordieHoweNative`); this module has their lemmas.
-/

namespace GordieHowe.RealizedProgram

open Export Range IOP

section

variable {ir : RealizedProgram} {I : Interp} {primeNodes : ℕ → List String}

/-- **`readsFixedB` decides that a value reads only what is fixed when `j` is drawn.** -/
theorem readsFixedB_iff (hwf : ir.WellFormed) {j v : ℕ} :
    ir.readsFixedB j v = true ↔ ∀ rd ∈ ir.nodeReads ir.fuel v, ir.ReadFixedAt j rd := by
  simp only [readsFixedB, List.all_eq_true, decide_eq_true_eq]
  exact forall_congr' fun rd => imp_congr_left (mem_readsT hwf v rd).symm

/-- **A predicate whose values are fixed when challenge `j` is drawn** (`readsFixedB`, through
the reads table) reads only what is fixed then. -/
theorem predReads_fixed_of_readsFixedB (hwf : ir.WellFormed) {j : ℕ} {b : PredBody}
    (h : (ir.predNodes b).all (ir.readsFixedB j) = true) :
    ∀ rd ∈ ir.predReads b, ir.ReadFixedAt j rd := by
  intro rd hrd
  obtain ⟨v, hv, hrv⟩ := List.mem_flatMap.1 hrd
  exact (readsFixedB_iff hwf).1 (List.all_eq_true.1 h v hv) rd hrv

/-- **`tableKernelFact_sound`**: the kernel fact holds, or the selection event occurs. Without the
event, the fields' `equal`s (of rank below `self`, `CitesHold`) give each block of the record as
the transform of a block of a row of the table (`SelExact`); the inverse transform returns that block
(`inverseNttNatural_nttNatural`, `inverseNtt_nttScheme`),
whose entries are naturals below the table's declared bound (`hS`), read centred as themselves. -/
theorem tableKernelFact_sound (hwf : ir.WellFormed) (hI : I.Registered ir)
    (hL : I.Lawful ir primeNodes) {sr : List (ℕ × ℕ)} {e : ir.Env I}
    (hS : ∀ vN ∈ sr, ∀ i < (ir.value vN.1).size,
      ∃ n < vN.2, ir.reader e vN.1 i = ((n : ℕ) : (I (ir.valueField vN.1)).K))
    {ctx : DerivCtx} {self : ℕ} (hc : CitesHold e ctx self) {d v : ℕ} {s : IvlSrc} {f : Fact}
    (hf : ir.tableKernelFact sr ctx self d v s = some f) :
    f.Holds e ∨ ∃ j, ir.RealEvent j e := by
  unfold tableKernelFact at hf
  split at hf
  swap
  · cases hf
  rename_i b q _ lo hi
  split at hf
  swap
  · cases hf
  rename_i sh hk
  split_ifs at hf with hok
  cases hf
  simp only [tableKernelOkB, Bool.and_eq_true, decide_eq_true_eq, List.any_eq_true,
    List.all_eq_true, List.mem_range, Bool.or_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true,
    beq_iff_eq] at hok
  obtain ⟨⟨⟨⟨⟨⟨hv, hb, rfl, hd, hq, hfr, hft, hrows, hlo0, hlo, hhi⟩, hrr⟩, hrt⟩,
    ⟨⟨T, B⟩, hTB, rfl, hB⟩⟩, hroot⟩, hrank⟩ := hok
  simp only at hTB hB
  by_cases hev : ir.SelEvent sh.chal e
  · exact .inr ⟨_, .inr (.inr hev)⟩
  refine .inl ?_
  have hx : ir.SelExact (ir.reader e) sh := by
    by_contra hx
    refine hev ⟨q, hq, sh, hk, rfl, fun rd hrd => ?_, fun p hp heq _ => ?_, hx⟩
    · rcases List.mem_append.1 hrd with hrd | hrd
      · obtain ⟨u, hu, hrd⟩ := List.mem_flatMap.1 hrd
        exact (readsFixedB_iff hwf).1 (hrr u hu) rd hrd
      · exact (readsFixedB_iff hwf).1 hrt rd hrd
    · refine hc.1 p hp ?_
      rcases hrank p hp with h | h
      · rw [h] at heq
        cases heq
      · exact h
  obtain ⟨r, hr, hrec⟩ := hx
  obtain ⟨k, hkl, hkeq⟩ := List.getElem_of_mem hv
  have hkv : sh.records.getD k 0 = v := by rw [List.getD_eq_getElem _ _ hkl, hkeq]
  have htile : ir.tilesB sh = true := by
    unfold kernelSel? at hk
    obtain ⟨-, hp⟩ := Option.filter_eq_some_iff.1 hk
    simp only [Bool.and_eq_true] at hp
    exact hp.1.2
  have hfit := blockStart_add_le ir htile hkl
  rw [hkv] at hfit
  set o := ir.blockStart sh k
  have hrow : ∀ b' < ir.recBlocks sh v, ∀ m < sh.n,
      (castElt (ir.reader e v (b' * sh.n + m)) : (I (ir.domainField sh.domain)).K) =
        Ops.nttOf sh.natural sh.n ((I (ir.domainField sh.domain)).decode sh.psi)
          (fun c => castElt (ir.reader e sh.table (r * sh.width + (o + b') * sh.n + c))) m :=
    fun b' hb' => by
      have := hrec k hkl b' (by rwa [hkv])
      rwa [hkv] at this
  have hdF := domainField_lt hwf hd
  have hchar := charP_field hI hdF
  have hp := hI.characteristic _ hdF
  have htn := hL.toNat_natCast _ hdF
  have hR := rootFacts_of_rootOkB hwf hI hL hd hroot
  intro i hin
  -- coefficient `i` of block `b`'s polynomial is entry `r W + (o + b) n + i` of the table
  have hpoly : ir.kernelPoly (ir.reader e) sh.domain v b sh.n sh.psi sh.natural i =
      castElt (ir.reader e sh.table (r * sh.width + (o + b) * sh.n + i)) := by
    unfold kernelPoly
    have hrb := hrow b hb
    cases hnat : sh.natural <;> simp only [hnat, Ops.nttOf, Bool.false_eq_true, ite_true,
      ite_false, NamedOp.formPoly] at hrb ⊢
    · rw [Ops.inverseNtt_congr hrb, Ops.inverseNtt_nttScheme hR.pow2 hR.prim hR.ne _ hin]
    · rw [Ops.inverseNttNatural_congr hrb, Ops.inverseNttNatural_nttNatural hR.prim hR.ne _ hin]
  have hidx : r * sh.width + (o + b) * sh.n + i < (ir.value sh.table).size := by
    have h1 : (o + b) * sh.n + i < sh.width := by
      have hbK : b < ir.recBlocks sh v := hb
      have : (o + b + 1) * sh.n ≤ (o + ir.recBlocks sh v) * sh.n :=
        Nat.mul_le_mul_right _ (by omega)
      rw [Nat.add_mul _ 1, Nat.one_mul] at this
      omega
    have : (r + 1) * sh.width ≤ sh.rows * sh.width := Nat.mul_le_mul_right _ hr
    rw [Nat.succ_mul] at this
    omega
  obtain ⟨c, hcB, hcv⟩ := hS (sh.table, B) hTB _ hidx
  rw [hpoly, hcv, castElt_natCast hft]
  have hcz : 2 * |(c : ℤ)| < (ir.charOf (ir.domainField sh.domain) : ℤ) := by
    rw [abs_of_nonneg (Int.natCast_nonneg c)]
    have : (c : ℤ) ≤ hi := by omega
    have : hi ≤ |hi| := le_abs_self hi
    omega
  have hcast : ((c : ℕ) : (I (ir.domainField sh.domain)).K) =
      ((c : ℤ) : (I (ir.domainField sh.domain)).K) := (Int.cast_natCast c).symm
  rw [hcast, FieldInterp.coefInt_intCast hp hchar htn hcz]
  exact ⟨by omega, by omega, rfl⟩

end

end GordieHowe.RealizedProgram
