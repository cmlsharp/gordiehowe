-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Language.Realizations.Circuit.RelSound

@[expose] public section

/-!
# GordieHowe: the node table's read premises at the honest prover's input

The completeness direction (`CircuitsAccept`) reads a circuit's node table at the honest input
vector (`GordieHowe.RealizedProgram.circuitInput`) and the honest reader (the reader of the
layout's environment at the realized assignment, `bindAsg a`):

* **Placement leaves** (`GordieHowe.RealizedProgram.leafReads_circuitInput`): a value leaf's wires
  read the honest reader's coordinates, where every private block lies at private positions and the
  honest pads are zero off the late values' coordinates.
* **Definitions** (`GordieHowe.RealizedProgram.defReads_reader`): every bound value and public
  expression reads its definition at a reader of a realized assignment.
-/

namespace GordieHowe.RealizedProgram

open Export
open GordieHowe.GKR.Rel (Wire TE Place)

variable {ir : RealizedProgram} {I : Interp} {c : ℕ} {x : ir.Valuation I}
  {r : (ir.layout I).Run} {d : ℕ}

/-- **The honest input at a public position** is the verifier's public input. -/
theorem vecRead_circuitInput_pub (hL : ir.InputLayoutOk c)
    (hfit : (ir.circuit c).inputCount ≤ 2 ^ d)
    {a : ir.Assignment I} {q : ℕ} (hq : q < (ir.circuit c).publicInputs) :
    vecRead (ir.circuitInput I c x r a (d := d)) q = ir.publicInput I c x r q := by
  have := hL.pubLe
  rw [vecRead, dite_eq_left (by omega)]
  unfold circuitInput
  rw [ite_eq_left (show (ir.circuit c).IsPublicPos q from hq)]

/-- **The honest input at a private position held by a block** is the block's private value. -/
theorem vecRead_circuitInput_priv (hL : ir.InputLayoutOk c)
    (hfit : (ir.circuit c).inputCount ≤ 2 ^ d) {a : ir.Assignment I} {blk : InputBlock}
    (hmem : blk ∈ (ir.circuit c).inputs) {q : ℕ} (hq : (ir.circuit c).publicInputs ≤ q)
    {y : (I (ir.circField c)).K}
    (hy : blk.privValue? (fun u i => castElt (a.val u i)) (fun u i => castElt (a.pad u i))
      (fun u i => castElt (ir.reader (ir.layoutEnv I x (ir.bindAsg a) r) u i)) q = some y) :
    vecRead (ir.circuitInput I c x r a (d := d)) q = y := by
  have hh := InputBlock.holds_of_privValue? (by rw [hy]; simp)
  have hend := InputBlock.layoutEnd_end_le hL.layout blk hmem
  unfold InputBlock.Holds at hh
  rw [vecRead, dite_eq_left (by omega)]
  unfold circuitInput
  rw [ite_eq_right (show ¬ (ir.circuit c).IsPublicPos q from fun h => absurd h (by
    unfold Circuit.IsPublicPos; omega))]
  rw [InputBlock.findSome?_eq_of_holds hL.layout hmem (q := q) (by unfold InputBlock.Holds; omega)
    fun b' h => InputBlock.holds_of_privValue? h, hy, Option.getD_some]

/-- **The honest reader meets the placement-leaf premise** (`LeafReads`) at node values reading the
honest input vector (`circuitInput`). -/
theorem leafReads_circuitInput (hL : ir.InputLayoutOk c)
    (hpriv : ∀ b ∈ (ir.circuit c).inputs, b.isPublic = false →
      (ir.circuit c).publicInputs ≤ b.first)
    {a : ir.Assignment I} (ha0 : ir.PadsAgreeOff I ⟨0, 0⟩ a)
    (hfit : (ir.circuit c).inputCount ≤ 2 ^ d)
    {val : ℕ → (I (ir.circField c)).K}
    (hval : ∀ q < (ir.circuit c).inputCount,
      val q = vecRead (ir.circuitInput I c x r a (d := d)) q)
    {env : TEnv} (hAr : env.ArithOk (I (ir.circField c)).decode) {E : ETable} :
    LeafReads (ir := ir) (c := c) (env := env) (E := E)
      (rd := ir.reader (ir.layoutEnv I x (ir.bindAsg a) r)) (V := val) := by
  intro k u pl hk hpl cs h hcs i hi
  have hA := hAr.hom
  have h' := toOption_eq_some h
  have hw := placeCutsE_wires h'
  unfold placeCutsE at h'
  simp only [hk, hw, Nat.beq_refl, Bool.not_true, Bool.cond_false] at h'
  cases pl with
  | defined y => exact absurd rfl (hpl y)
  | block b =>
    simp only at h'
    obtain ⟨hb, rfl⟩ := cond_ok_eq_ok h'
    simp only [Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq, Nat.ble_eq, List.all_eq_true,
      Bool.not_eq_true'] at hb
    obtain ⟨⟨⟨⟨⟨hbl, hkind⟩, -⟩, hfu⟩, hlen⟩, -⟩ := hb
    have hmem := getD_mem_lt hbl
    generalize hblk : (ir.circuit c).inputs.getD b default = blk at hmem hkind hlen hcs
    have hend := InputBlock.layoutEnd_end_le hL.layout blk hmem
    have hq : blk.first + i < (ir.circuit c).inputCount := by omega
    have hm := mem_zip_getD (xs := (E.get k).wires)
      (ys := (List.range (E.get k).len).map fun i => TE.wire 0 1 (blk.first + i)) (i := i)
      (by omega) (by simp only [List.length_map, List.length_range]; omega)
    have hc := hcs _ hm
    simp only at hc
    rw [hc, getD_map_lt' _ (by simp only [List.length_range]; omega), List.getD_eq_getElem _ _
      (by simp only [List.length_range]; omega), List.getElem_range]
    simp only [TE.eval, hA.zero, hA.one, zero_add, one_mul]
    rw [hval _ hq]
    unfold kindBlockB at hkind
    rcases hku : (ir.value u).kind with _ | _ | _ | _ | _ | ⟨w, sel⟩ | ⟨s, mm⟩ | _ | _ <;>
      simp only [hku] at hkind
    case priv | padCopy =>
      cases blk <;> simp only [InputBlock.isCommittedOf, beq_iff_eq,
        Bool.false_eq_true] at hkind
      rename_i u0 a0 n0
      subst u0
      have hp := hpriv _ hmem rfl
      simp only [InputBlock.first, InputBlock.len] at hp hlen ⊢
      rw [vecRead_circuitInput_priv hL hfit hmem (by omega) (by
        simp only [InputBlock.privValue?]
        rw [ite_eq_left ⟨by omega, by omega⟩, Nat.add_sub_cancel_left])]
      first
        | rw [reader_of_priv _ hku]
        | rw [reader_of_padCopy _ hku]
      simp only [layoutEnv]
      rw [ir.bindAsg_val_of_isBound (v := u) _ (by rw [hku]; rfl)]
    case bits =>
      cases blk <;> simp only [InputBlock.isViewOf, beq_iff_eq,
        Bool.false_eq_true] at hkind
      rename_i u0 a0 n0
      subst u0
      have hp := hpriv _ hmem rfl
      simp only [InputBlock.first, InputBlock.len] at hp hlen ⊢
      rw [vecRead_circuitInput_priv hL hfit hmem (by omega) (by
        simp only [InputBlock.privValue?]
        rw [ite_eq_left ⟨by omega, by omega⟩, Nat.add_sub_cancel_left])]
    case late => cases hkind
    all_goals
      cases blk <;> simp only [InputBlock.isPubOf, beq_iff_eq,
        Bool.false_eq_true] at hkind
      rename_i u0 a0 n0
      subst u0
      obtain ⟨-, hpb, ha1, han⟩ := hL.pub _ a0 n0 hmem
      have hnl : ¬ ir.IsLate u := fun hl => by simp [IsLate, hku, Kind.isLate] at hl
      have hpb : ir.pubB ir.fuel u = true := hpb.resolve_left hnl
      simp only [InputBlock.first, InputBlock.len] at hlen ⊢
      have hv : ((InputBlock.pub u a0 n0).pubValue?
          (fun u i => (castElt (ir.reader (ir.layoutEnv I x ⟨0, 0⟩ r) u i) :
            (I (ir.circField c)).K))
          (ir.realPubValue I c r) (a0 + i)) =
            some (castElt (ir.reader (ir.layoutEnv I x ⟨0, 0⟩ r) u i)) := by
        simp only [InputBlock.pubValue?]
        rw [ite_eq_left ⟨by omega, by omega⟩, Nat.add_sub_cancel_left]
      rw [vecRead_circuitInput_pub hL hfit (by omega), publicInput, ite_eq_right (by omega),
        InputBlock.findSome_pubValue? hL.layout _ hmem hv, Option.getD_some,
        reader_eq_of_pubB (a' := ir.bindAsg a) ha0 hpb]
  | late pb pd =>
    simp only at h'
    split at h'
    · rename_i m a1 n u' a' n' hgpb hgpd
      obtain ⟨hb, rfl⟩ := cond_ok_eq_ok h'
      simp only [Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq, Nat.ble_eq, List.all_eq_true,
        Bool.not_eq_true', Bool.or_eq_true] at hb
      obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hpbl, hpdl⟩, -⟩, hmsg⟩, huu⟩, -⟩, -⟩, hfu⟩, hn⟩, hn'⟩, -⟩, -⟩ := hb
      subst u'
      have hmemb : InputBlock.pub m a1 n ∈ (ir.circuit c).inputs := hgpb ▸ getD_mem_lt hpbl
      have hmemd : InputBlock.pad u a' n' ∈ (ir.circuit c).inputs := hgpd ▸ getD_mem_lt hpdl
      have hendb := InputBlock.layoutEnd_end_le hL.layout _ hmemb
      have hendd := InputBlock.layoutEnd_end_le hL.layout _ hmemd
      simp only [InputBlock.first, InputBlock.len] at hendb hendd
      have hm := mem_zip_getD (xs := (E.get k).wires)
        (ys := (List.range (E.get k).len).map fun i =>
          TE.add (.wire 0 1 (a1 + i)) (.scale env.neg1 (.wire 0 1 (a' + i)))) (i := i)
        (by omega) (by simp only [List.length_map, List.length_range]; omega)
      have hc := hcs _ hm
      simp only at hc
      rw [hc, getD_map_lt' _ (by simp only [List.length_range]; omega), List.getD_eq_getElem _ _
        (by simp only [List.length_range]; omega), List.getElem_range]
      simp only [TE.eval, hA.zero, hA.one, zero_add, one_mul, hAr.neg1]
      rw [hval _ (by omega), hval _ (by omega)]
      obtain ⟨hu, hlate, hnp⟩ := hL.pad u a' n' hmemd
      have hku : (ir.value u).kind = .late := by
        have h := hlate.1
        revert h
        cases (ir.value u).kind <;> simp [Kind.isLate]
      obtain ⟨hfm, -, ham, hamn⟩ := hL.pub m a1 n hmemb
      have hpp := hpriv _ hmemd rfl
      simp only [InputBlock.first] at hpp
      have hvm : ((InputBlock.pub m a1 n).pubValue?
          (fun u i => (castElt (ir.reader (ir.layoutEnv I x ⟨0, 0⟩ r) u i) :
            (I (ir.circField c)).K))
          (ir.realPubValue I c r) (a1 + i)) =
            some (castElt (ir.reader (ir.layoutEnv I x ⟨0, 0⟩ r) m i)) := by
        simp only [InputBlock.pubValue?]
        rw [ite_eq_left ⟨by omega, by omega⟩, Nat.add_sub_cancel_left]
      have hcond : u < ir.values.length ∧ ir.IsLate u ∧ i < (ir.value u).size :=
        ⟨hu, hlate, by omega⟩
      rw [vecRead_circuitInput_pub hL hfit (by omega), publicInput, ite_eq_right (by omega),
        InputBlock.findSome_pubValue? hL.layout _ hmemb hvm, Option.getD_some,
        vecRead_circuitInput_priv hL hfit hmemd (by omega) (by
          simp only [InputBlock.privValue?]
          rw [ite_eq_left ⟨by omega, by omega⟩, Nat.add_sub_cancel_left])]
      have hMsg : m = u ∨ (ir.value m).kind = .message u := by
        rcases hmsg with hmu | hmk
        · exact .inl hmu
        · right
          split at hmk
          · rename_i u'' hk''
            simp only [Nat.beq_eq] at hmk
            rw [hk'', hmk]
          · cases hmk
      rw [reader_of_late _ hku]
      simp only [layoutEnv, ite_eq_left hcond, bindAsg]
      rcases hMsg with rfl | hkm
      · rw [reader_of_late _ hku]
        simp only [ite_eq_left hcond]
        rw [castElt_sub, castElt_sub]
        simp [sub_eq_add_neg]
      · rw [reader, fuel, read]
        simp only [hkm]
        rw [ite_eq_left hcond, castElt_castElt_eq, ite_eq_left (hfu.trans hfm.symm), castElt_add,
          castElt_sub]
        simp [sub_eq_add_neg]
    · exact absurd h' (by simp)

/-- **The honest reader reads every definition** (`DefReads`) at an environment whose assignment
is a realized one (`bindAsg`), where every value bound to its digits reads committed values and
constants (`BoundOk`): a bound value by `reader_bindAsg_of_boundOk'`, a public expression one level
down (`read`) at values of smaller identifier, whose readings the extra level does not change
(`read_stable`). -/
theorem defReads_reader (hwf : ir.WellFormed) (hbd : ∀ w < ir.values.length, ir.BoundOk w)
    {e : ir.Env I} {a : ir.Assignment I} (he : e.asg = ir.bindAsg a) :
    ir.DefReads (ir.reader e) := by
  intro u hu e' hd
  unfold valueDef at hd
  rcases hk : (ir.value u).kind with
      _ | ⟨_ | ⟨_, _⟩ | e''⟩ | _ | _ | _ | ⟨_, _⟩ | ⟨_, _⟩ | _ | e'' <;>
    simp only [hk, reduceCtorEq, Option.some.injEq] at hd
  · subst hd
    funext i
    have hdep := (hwf.values u hu).2
    rw [hk] at hdep
    conv_lhs => rw [reader, fuel, read]
    simp only [hk]
    refine congrFun (evalE_congr fun w hw => ?_) i
    have hw' : w < u := hdep.2 w hw
    show ir.read _ ir.values.length w = ir.read _ ir.fuel w
    exact (read_stable hwf.valuesOrdered _ (by omega) (by omega) (by simp [fuel])).symm
  · subst hd
    exact reader_bindAsg_of_boundOk' hbd he hu hk

end GordieHowe.RealizedProgram
