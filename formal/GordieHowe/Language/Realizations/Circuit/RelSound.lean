-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Language.Realizations.Circuit.RelTable
public import GordieHowe.Language.Realizations.Circuit.NttPure

@[expose] public section

/-!
# GordieHowe: the soundness of a circuit's node table

The relational check (`GKR.Rel.relOk`) gives, at the DAG's node values `V`, every cut of the node
table (`GordieHowe.RealizedProgram.nodeCutsE`): a wire's value is its tree expression's value. This
file turns the cuts into the node table's meaning: every cut node has one wire per coordinate, and
coordinate `i`'s wire has the value of the node's meaning (`GordieHowe.RealizedProgram.nodeSem`) at
`i`; an uncut node's expansion has the same values (`expansion_sound`).

* **Leaves** (`GordieHowe.RealizedProgram.DefReads`, `defRead_sound`, `placementRead_sound`,
  `defReads_inputValuation`, `leafReads_inputValuation`): a value read through its definition
  has its definition node's wires; a value read from its input blocks has the inputs' values.
* **Kinds**: one lemma per node kind on its one-level form (`linConsStep_sound`,
  `constStep_sound`, `chainStep_sound`, `prodStep_sound`, `treeStep_sound`, `cmpStep_sound`, …),
  over the operators (`opTE_binds`), the chain trees (`chainTree_sound`, `chainRoot_sound`), the
  balanced products and Logic trees (`prodTree_sound`, `balTree_sound`, `eqTree_sound`,
  `ltTree_sound`).
* **Expansions** (`GordieHowe.RealizedProgram.nodeEF_sound`): by induction on the fuel.
* **The table** (`GordieHowe.RealizedProgram.nodeTable_sound`): by strong induction on the node id.
-/

namespace GordieHowe.RealizedProgram

open GordieHowe.GKR.Rel (Wire TE Place)
open GordieHowe.GKR.Fold

/-! ## Except and list helpers -/

theorem except_bind_eq_ok {ε α β : Type} {x : Except ε α} {f : α → Except ε β} {b : β} :
    x >>= f = .ok b ↔ ∃ a, x = .ok a ∧ f a = .ok b := by
  cases x <;> simp [bind, Except.bind]

theorem chk_eq_ok {b : Bool} {r : TReason} {u : Unit} : chk b r = .ok u ↔ b = true := by
  cases b <;> simp [chk]

theorem cond_ok_eq_ok {α : Type} {b : Bool} {x y : α} {r : TReason}
    (h : cond b (Except.ok x) (Except.error r) = Except.ok y) : b = true ∧ x = y := by
  cases b <;> simp_all

theorem toOption_eq_some {ε α : Type} {x : Except ε α} {a : α} (h : x.toOption = some a) :
    x = .ok a := by
  cases x <;> simp_all [Except.toOption]

theorem mem_zip_getD {α β : Type} [Inhabited α] [Inhabited β] {xs : List α} {ys : List β} {i : ℕ}
    (hx : i < xs.length) (hy : i < ys.length) :
    (xs.getD i default, ys.getD i default) ∈ xs.zip ys := by
  rw [List.getD_eq_getElem _ _ hx, List.getD_eq_getElem _ _ hy]
  have hz : i < (xs.zip ys).length := by simp [hx, hy]
  have hm := List.getElem_mem hz
  rwa [List.getElem_zip] at hm

theorem getD_map_lt' {α β : Type} [Inhabited α] [Inhabited β] (f : α → β) {l : List α} {i : ℕ}
    (hi : i < l.length) : (l.map f).getD i default = f (l.getD i default) := by
  rw [List.getD_eq_getElem _ _ (by simpa using hi), List.getElem_map, List.getD_eq_getElem _ _ hi]

theorem getD_take_lt {α : Type} [Inhabited α] {l : List α} {n i : ℕ} (hi : i < n) :
    (l.take n).getD i default = l.getD i default := by
  simp [List.getD_eq_getElem?_getD, hi]

theorem teW_eval {F : Type*} [CommRing F] (κc v : ℕ → F) (W : Wire) :
    (teW W).eval κc v = W.val κc v := rfl

/-- A value with a definition is one of the program's values. -/
theorem lt_of_valueDef {ir : RealizedProgram} {u : ℕ} {e : Expr} (h : ir.valueDef u = some e) :
    u < ir.values.length := by
  by_contra hu
  have hd : ir.value u = default :=
    (ir.value_eq_getD u).trans (List.getD_eq_default _ _ (by omega))
  unfold valueDef at h
  rw [hd] at h
  cases h

/-! ## Definition reads -/

section Reads

variable (ir : RealizedProgram) {I : Interp}

/-- **The one definition premise**: `.bound e` and `.pub (.expr e)` read their expression. -/
def DefReads (rd : ir.Valuation I) : Prop :=
  ∀ u < ir.values.length, ∀ e, ir.valueDef u = some e → rd u = ir.evalE rd (ir.valueField u) e

end Reads

variable {ir : RealizedProgram} {I : Interp}

/-- **A value leaf's cuts check its wire count** (`placeCutsE`'s first test). -/
theorem placeCutsE_wires {c : ℕ} {env : TEnv} {E : ETable} {k : ℕ} {cs : List (Wire × TE)}
    (h : ir.placeCutsE c env E k = .ok cs) : (E.get k).wires.length = (E.get k).len := by
  unfold placeCutsE at h
  cases hwb : Nat.beq (E.get k).wires.length (E.get k).len
  · simp [hwb] at h
  · simpa using hwb

/-- **`defRead_sound`**: a value read through its definition has its definition node's wires. -/
theorem defRead_sound {c : ℕ} {env : TEnv} {E : ETable} (ho : ir.RefsOrdered)
    (hE : ir.EmitTableOk env E) {rd : ir.Valuation I} (hR : ir.DefReads rd)
    {val : ℕ → (I (ir.circField c)).K} {k u y : ℕ} (hk : (E.get k).node = .value u (.defined y))
    {cs : List (Wire × TE)} (h : ir.placeCuts c env E k = some cs)
    (hcs : ∀ q ∈ cs,
      q.1.val (I (ir.circField c)).decode val = q.2.eval (I (ir.circField c)).decode val)
    (hy : ∀ i < (E.get y).len, ir.nodeSem env E rd (ir.circuit c).domain y i =
      ((E.get y).wires.getD i default).val (I (ir.circField c)).decode val) :
    ∀ i < (E.get k).len, (castElt (rd u i) : (I (ir.circField c)).K) =
      ((E.get k).wires.getD i default).val (I (ir.circField c)).decode val := by
  intro i hi
  have h' := toOption_eq_some h
  have hw := placeCutsE_wires h'
  unfold placeCutsE at h'
  simp only [hk, hw, Nat.beq_refl, Bool.not_true, Bool.cond_false] at h'
  cases hd : ir.valueDef u with
  | none => simp [hd] at h'
  | some e =>
    simp only [hd] at h'
    obtain ⟨hb, rfl⟩ := cond_ok_eq_ok h'
    simp only [Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq] at hb
    obtain ⟨⟨⟨⟨⟨-, -⟩, heq⟩, hwy⟩, hlen⟩, hfu⟩ := hb
    have hiy : i < (E.get y).len := by omega
    have hm := mem_zip_getD (xs := (E.get k).wires)
      (ys := ((E.get y).wires.take (E.get k).len).map teW) (i := i) (by omega)
      (by simp only [List.length_map, List.length_take]; omega)
    have hc := hcs _ hm
    simp only at hc
    rw [hc, getD_map_lt' _ (by simp only [List.length_take]; omega), getD_take_lt hi, teW_eval,
      ← hy i hiy]
    obtain ⟨-, hsem⟩ := eqB_sound ho hE rd (ir.circuit c).domain heq
    rw [← hsem, hR u (lt_of_valueDef hd) e hd]
    exact castElt_evalE hfu rd e i

/-! ## Placement reads -/

/-- **The first entry of a list some function reads**: every entry before index `b` reads
nothing and entry `b` reads `y`. -/
theorem findSome?_at {α β : Type} [Inhabited α] {f : α → Option β} {l : List α} {b : ℕ} {y : β}
    (hb : b < l.length) (hpre : ∀ x ∈ l.take b, f x = none) (hx : f (l.getD b default) = some y) :
    l.findSome? f = some y := by
  rw [← List.take_append_drop b l, List.findSome?_append, List.findSome?_eq_none_iff.2 hpre,
    Option.none_or, List.drop_eq_getElem_cons hb, List.findSome?_cons]
  rw [List.getD_eq_getElem _ _ hb] at hx
  rw [hx]

theorem getD_mem_lt {α : Type} [Inhabited α] {l : List α} {b : ℕ} (hb : b < l.length) :
    l.getD b default ∈ l := by
  rw [List.getD_eq_getElem _ _ hb]
  exact List.getElem_mem hb

namespace InputBlock

theorem committedPos_of_isCommittedOf {u i : ℕ} {b : InputBlock} (h : b.isCommittedOf u = true)
    (hi : i < b.len) : b.committedPos u i = some (b.first + i) := by
  cases b <;> simp_all [isCommittedOf, committedPos, first, len]

theorem committedPos_of_not {u i : ℕ} {b : InputBlock} (h : b.isCommittedOf u = false) :
    b.committedPos u i = none := by
  cases b <;> simp_all [isCommittedOf, committedPos]

theorem viewPos_of_isViewOf {u i : ℕ} {b : InputBlock} (h : b.isViewOf u = true)
    (hi : i < b.len) : b.viewPos u i = some (b.first + i) := by
  cases b <;> simp_all [isViewOf, viewPos, first, len]

theorem viewPos_of_not {u i : ℕ} {b : InputBlock} (h : b.isViewOf u = false) :
    b.viewPos u i = none := by
  cases b <;> simp_all [isViewOf, viewPos]

theorem pubPos_of_isPubOf {u i : ℕ} {b : InputBlock} (h : b.isPubOf u = true)
    (hi : i < b.len) : b.pubPos u i = some (b.first + i) := by
  cases b <;> simp_all [isPubOf, pubPos, first, len]

theorem pubPos_of_not {u i : ℕ} {b : InputBlock} (h : b.isPubOf u = false) :
    b.pubPos u i = none := by
  cases b <;> simp_all [isPubOf, pubPos]

theorem padPos_of_not {u i : ℕ} {b : InputBlock} (h : b.isPadOf u = false) :
    b.padPos u i = none := by
  cases b <;> simp_all [isPadOf, padPos]

end InputBlock

variable {c : ℕ} {x : ir.Valuation I} {r : (ir.layout I).Run} {d : ℕ}
  {v : Fin (2 ^ d) → (I (ir.circField c)).K}

/-- **A value read from an input block or as a late value** has the inputs' values
(`placementRead_sound` with the environment's codes decoding as named, `TEnv.ArithOk`, as a
hypothesis). -/
theorem placementRead_sound (hL : ir.InputLayoutOk c) (hfit : (ir.circuit c).inputCount ≤ 2 ^ d)
    (hpub : ∀ j : Fin (2 ^ d), (ir.circuit c).IsPublicPos j → v j = ir.publicInput I c x r j)
    (_hP : ir.InputPremises I c x r v)
    {val : ℕ → (I (ir.circField c)).K} (hval : ∀ q < (ir.circuit c).inputCount, val q = vecRead v q)
    {env : TEnv} (hAr : env.ArithOk (I (ir.circField c)).decode)
    {E : ETable} {k u : ℕ} {pl : Place} (hk : (E.get k).node = .value u pl)
    (hpl : ∀ y, pl ≠ .defined y) {cs : List (Wire × TE)} (h : ir.placeCuts c env E k = some cs)
    (hcs : ∀ q ∈ cs,
      q.1.val (I (ir.circField c)).decode val = q.2.eval (I (ir.circField c)).decode val) :
    ∀ i < (E.get k).len, (castElt (ir.inputValuation I c x r v u i) : (I (ir.circField c)).K) =
      ((E.get k).wires.getD i default).val (I (ir.circField c)).decode val := by
  intro i hi
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
    obtain ⟨⟨⟨⟨⟨hbl, hkind⟩, hpre⟩, hfu⟩, hlen⟩, -⟩ := hb
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
    have hpos : ∀ (isX : InputBlock → Bool) (P : InputBlock → Option ℕ),
        (∀ b', isX b' = false → P b' = none) → P blk = some (blk.first + i) →
        (∀ b' ∈ (ir.circuit c).inputs.take b, isX b' = false) →
        (ir.circuit c).inputs.findSome? P = some (blk.first + i) := fun isX P hn hs hpre' =>
      findSome?_at hbl (fun b' hb' => hn b' (hpre' b' hb')) (by rw [hblk]; exact hs)
    have hback : ∀ q, (castElt (castElt (vecRead v q) : (I (ir.valueField u)).K) :
        (I (ir.circField c)).K) = vecRead v q := fun q => castElt_castElt_of_eq hfu.symm _
    unfold kindBlockB at hkind hpre
    rcases hku : (ir.value u).kind with _ | _ | _ | _ | _ | ⟨w, sel⟩ | ⟨s, mm⟩ | _ | _ <;>
      simp only [hku] at hkind hpre
    case priv | padCopy =>
      have hcp : (ir.circuit c).committedPos u i = some (blk.first + i) := by
        refine hpos (InputBlock.isCommittedOf u) (InputBlock.committedPos u i)
          (fun _ => InputBlock.committedPos_of_not)
          (InputBlock.committedPos_of_isCommittedOf hkind (by omega))
          (fun b' hb' => by simpa using hpre b' hb')
      first
        | rw [inputValuation_committed (.inl hku) hcp, hback]
        | rw [inputValuation_committed (.inr ⟨_, _, hku⟩) hcp, hback]
    case bits =>
      have hcp : (ir.circuit c).viewPos u i = some (blk.first + i) := by
        refine hpos (InputBlock.isViewOf u) (InputBlock.viewPos u i)
          (fun _ => InputBlock.viewPos_of_not)
          (InputBlock.viewPos_of_isViewOf hkind (by omega))
          (fun b' hb' => by simpa using hpre b' hb')
      rw [inputValuation_view hku hcp, hback]
    case late => cases hkind
    all_goals
      have hcp : (ir.circuit c).pubPos u i = some (blk.first + i) := by
        refine hpos (InputBlock.isPubOf u) (InputBlock.pubPos u i)
          (fun _ => InputBlock.pubPos_of_not)
          (InputBlock.pubPos_of_isPubOf hkind (by omega))
          (fun b' hb' => by simpa using hpre b' hb')
      rw [inputValuation_pub (by simp [Kind.readsPubBlock, hku]) hcp, hback]
  | late pb pd =>
    simp only at h'
    split at h'
    · rename_i m a n u' a' n' hgpb hgpd
      obtain ⟨hb, rfl⟩ := cond_ok_eq_ok h'
      simp only [Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq, Nat.ble_eq, List.all_eq_true,
        Bool.not_eq_true', Bool.or_eq_true] at hb
      obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hpbl, hpdl⟩, -⟩, hmsg⟩, rfl⟩, hpreb⟩, hpred⟩, hfu⟩, hn⟩, hn'⟩, -⟩, -⟩ := hb
      have hmemb : InputBlock.pub m a n ∈ (ir.circuit c).inputs := hgpb ▸ getD_mem_lt hpbl
      have hmemd : InputBlock.pad u' a' n' ∈ (ir.circuit c).inputs := hgpd ▸ getD_mem_lt hpdl
      have hendb := InputBlock.layoutEnd_end_le hL.layout _ hmemb
      have hendd := InputBlock.layoutEnd_end_le hL.layout _ hmemd
      simp only [InputBlock.first, InputBlock.len] at hendb hendd
      have hqm : (ir.circuit c).pubPos m i = some (a + i) := by
        refine findSome?_at hpbl (fun b' hb' => ?_) (by
          rw [hgpb]
          simp [InputBlock.pubPos]
          omega)
        exact InputBlock.pubPos_of_not (by simpa using hpreb b' hb')
      have hqp : (ir.circuit c).padPos u' i = some (a' + i) := by
        refine findSome?_at hpdl (fun b' hb' => ?_) (by
          rw [hgpd]
          simp [InputBlock.padPos]
          omega)
        exact InputBlock.padPos_of_not (by simpa using hpred b' hb')
      have hMsg : ir.MessageOf m u' := by
        rcases hmsg with hmu | hmk
        · exact .inl hmu
        · right
          split at hmk
          · rename_i u'' hk''
            simp only [Nat.beq_eq] at hmk
            rw [hk'', hmk]
          · cases hmk
      have hm := mem_zip_getD (xs := (E.get k).wires)
        (ys := (List.range (E.get k).len).map fun i =>
          TE.add (.wire 0 1 (a + i)) (.scale env.neg1 (.wire 0 1 (a' + i)))) (i := i)
        (by omega) (by simp only [List.length_map, List.length_range]; omega)
      have hc := hcs _ hm
      simp only at hc
      rw [hc, getD_map_lt' _ (by simp only [List.length_range]; omega), List.getD_eq_getElem _ _
        (by simp only [List.length_range]; omega), List.getElem_range]
      simp only [TE.eval, hA.zero, hA.one, zero_add, one_mul, hAr.neg1]
      rw [lateModel_inputValuation hL hfit hpub (inputs := (ir.circuit c).inputCount) hval u' m i
        (a + i) (a' + i) hMsg hfu hqm hqp (by omega) (by omega)]
      ring
    · exact absurd h' (by simp)

/-- **The realized assignment reads a bound value through its digits** (`BoundOk`; a copy of
`reader_bindAsg_of_boundOk`, `Realizations/Realize.lean`, which this file does not import). -/
theorem reader_bindAsg_of_boundOk' (hbd : ∀ v < ir.values.length, ir.BoundOk v) {e : ir.Env I}
    {a : ir.Assignment I} (he : e.asg = ir.bindAsg a) {v : ℕ} (hvl : v < ir.values.length)
    {x : Expr} (hk : (ir.value v).kind = .bound x) :
    ir.reader e v = ir.evalE (ir.reader e) (ir.valueField v) x := by
  have hb := hbd v hvl
  rw [BoundOk, hk] at hb
  funext i
  have hrd : ir.reader e v i = (ir.bindAsg a).val v i := by
    simp only [reader, fuel, read, hk, he]
  rw [hrd]
  simp only [bindAsg, hk]
  refine congrFun (evalE_congr fun u hu => ?_) i
  funext j
  have hu' := hb.2 u hu
  unfold isPrivOrConst at hu'
  unfold committedRead
  split at hu'
  · rename_i hku
    rw [hku, reader_of_priv e hku, he, ir.bindAsg_val_of_isBound (v := u) _ (by rw [hku]; rfl)]
  · rename_i es hku
    rw [hku, reader_of_constant e hku]
  · cases hu'

/-- **The decoded valuation reads every definition** (`defReads_inputValuation` with the premise
that every value bound to its digits reads committed values and constants, `BoundOk`): a bound
value by the realized assignment (`reader_bindAsg_of_boundOk`), a public expression by
`exprReads_inputValuation`. -/
theorem defReads_inputValuation (hwf : ir.WellFormed)
    (hbd : ∀ w < ir.values.length, ir.BoundOk w) (hL : ir.InputLayoutOk c)
    (hfit : (ir.circuit c).inputCount ≤ 2 ^ d)
    (hpub : ∀ j : Fin (2 ^ d), (ir.circuit c).IsPublicPos j → v j = ir.publicInput I c x r j)
    (hP : ir.InputPremises I c x r v) : ir.DefReads (ir.inputValuation I c x r v) := by
  intro u hu e hd
  unfold valueDef at hd
  rcases hk : (ir.value u).kind with
      _ | ⟨_ | ⟨_, _⟩ | e'⟩ | _ | _ | _ | ⟨_, _⟩ | ⟨_, _⟩ | _ | e' <;>
    simp only [hk, reduceCtorEq, Option.some.injEq] at hd
  · subst hd
    exact exprReads_inputValuation hwf hL hfit hpub hP u hu e' hk
  · subst hd
    rw [inputValuation_eq_inputBase hL hfit hpub hP]
    exact reader_bindAsg_of_boundOk' hbd rfl hu hk

/-! ## The node kinds -/

section Kinds

variable (ir) (c : ℕ) (env : TEnv) (E : ETable) (rd : ir.Valuation I)
  (V : ℕ → (I (ir.circField c)).K)

/-- **Node `k`'s wires bind its meaning** at the node values `V`: one wire per coordinate, each of
the node's meaning there. -/
def WiresOk (k : ℕ) : Prop :=
  (E.get k).wires.length = (E.get k).len ∧ ∀ i < (E.get k).len,
    ((E.get k).wires.getD i default).val (I (ir.circField c)).decode V =
      ir.nodeSem env E rd (ir.circuit c).domain k i

/-- **Tree expressions bind an expression** over the node table (kids read as their meanings, of
their lengths): as many as its coordinates, each of its value there. -/
def TEBinds (e : Expr) (ts : List TE) : Prop :=
  Expr.len ir (fun a => (E.get a).len) e = ts.length ∧ ∀ j < ts.length,
    Expr.eval ir (ir.circField c) rd (fun a => ir.nodeSem env E rd (ir.circuit c).domain a)
      (fun a => (E.get a).len) e j = (ts.getD j default).eval (I (ir.circField c)).decode V

variable {ir c env E rd V}

/-! ### Generic list facts -/

theorem forall₂_getD' {α β : Type} {Q : α → β → Prop} {dx : α} {dy : β} :
    ∀ {xs : List α} {ys : List β}, List.Forall₂ Q xs ys →
      ys.length = xs.length ∧ ∀ i < xs.length, Q (xs.getD i dx) (ys.getD i dy)
  | [], [], .nil => ⟨rfl, fun i hi => absurd hi (Nat.not_lt_zero _)⟩
  | _ :: _, _ :: _, .cons h hs => by
    obtain ⟨hl, hi⟩ := forall₂_getD' (dx := dx) (dy := dy) hs
    refine ⟨by simp [hl], fun i hi' => ?_⟩
    cases i with
    | zero => simpa using h
    | succ i => simpa using hi i (by simpa using hi')

theorem option_mapM_forall₂ {α β : Type} {f : α → Option β} :
    ∀ {l : List α} {l' : List β}, l.mapM f = some l' → List.Forall₂ (fun a b => f a = some b) l l'
  | [], l', h => by
    simp only [List.mapM_nil, Option.pure_def, Option.some.injEq] at h
    subst h
    exact .nil
  | a :: l, l', h => by
    simp only [List.mapM_cons, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at h
    obtain ⟨b, hb, bs, hbs, rfl⟩ := h
    exact .cons hb (option_mapM_forall₂ hbs)

theorem except_mapM_forall₂ {ε α β : Type} {f : α → Except ε β} :
    ∀ {l : List α} {l' : List β}, l.mapM f = .ok l' → List.Forall₂ (fun a b => f a = .ok b) l l'
  | [], l', h => by
    simp only [List.mapM_nil] at h
    cases h
    exact .nil
  | a :: l, l', h => by
    simp only [List.mapM_cons, except_bind_eq_ok] at h
    obtain ⟨b, hb, bs, hbs, h⟩ := h
    cases h
    exact .cons hb (except_mapM_forall₂ hbs)

/-! ### Tree expressions -/

section TEval

variable {F : Type*} [CommRing F] {κc v : ℕ → F}

theorem foldl_add_eval : ∀ (es : List TE) (e : TE),
    (es.foldl .add e).eval κc v = e.eval κc v + (es.map (TE.eval κc v)).sum
  | [], e => by simp
  | e' :: es, e => by
    rw [List.foldl_cons, foldl_add_eval es, List.map_cons, List.sum_cons]
    simp only [TE.eval]
    ring

theorem sumB_eval (h0 : κc 0 = 0) :
    ∀ (f : ℕ) (es : List TE), es.length ≤ f →
      (TE.sumB f es).eval κc v = (es.map (TE.eval κc v)).sum
  | _, [], _ => by simp [TE.sumB, TE.eval, h0]
  | _, [e], _ => by simp [TE.sumB]
  | 0, _ :: _ :: _, h => by simp at h
  | f + 1, e :: e' :: es, h => by
    have hl : (e :: e' :: es).length = es.length + 2 := rfl
    rw [TE.sumB, TE.eval, sumB_eval h0 f _ (by simp; omega), sumB_eval h0 f _ (by simp; omega),
      ← List.sum_append, ← List.map_append, List.take_append_drop]

theorem sumL_eval (h0 : κc 0 = 0) (es : List TE) :
    (TE.sumL es).eval κc v = (es.map (TE.eval κc v)).sum :=
  sumB_eval h0 _ es le_rfl

theorem rowTE_eval (h0 : κc 0 = 0) (h1 : κc 1 = 1) (x : ℕ → TE) (row : List (ℕ × ℕ)) :
    (rowTE x row).eval κc v = rowEval κc row (fun col => (x col).eval κc v) := by
  rw [rowTE, sumL_eval h0, List.map_map, rowEval]
  congr 1
  refine List.map_congr_left fun t _ => ?_
  by_cases ht : t.2 = 1
  · simp [ht, h1]
  · simp [ht, TE.eval]

theorem rowEval_congr {row : List (ℕ × ℕ)} {g g' : ℕ → F} (h : ∀ t ∈ row, g t.1 = g' t.1) :
    rowEval κc row g = rowEval κc row g' := by
  rw [rowEval, rowEval]
  congr 1
  exact List.map_congr_left fun t ht => by rw [h t ht]

end TEval

/-! ### Kids and binds -/

/-- **The cuts hold** at the node values `V`. -/
def CutsHold (cs : Cuts) : Prop :=
  ∀ q ∈ cs, q.1.val (I (ir.circField c)).decode V = q.2.eval (I (ir.circField c)).decode V

theorem cutsHold_append {cs ds : Cuts} :
    CutsHold (ir := ir) (c := c) (V := V) (cs ++ ds) ↔
      CutsHold (ir := ir) (c := c) (V := V) cs ∧ CutsHold (ir := ir) (c := c) (V := V) ds := by
  simp only [CutsHold, List.mem_append]
  exact ⟨fun h => ⟨fun q hq => h q (.inl hq), fun q hq => h q (.inr hq)⟩,
    fun h q hq => hq.elim (h.1 q) (h.2 q)⟩

theorem cutsHold_flatten {css : List Cuts} :
    CutsHold (ir := ir) (c := c) (V := V) css.flatten ↔
      ∀ cs ∈ css, CutsHold (ir := ir) (c := c) (V := V) cs := by
  simp only [CutsHold, List.mem_flatten]
  exact ⟨fun h cs hcs q hq => h q ⟨cs, hcs, hq⟩, fun h q ⟨cs, hcs, hq⟩ => h cs hcs q hq⟩

/-- **The cut nodes below `k` carry their meaning** (the induction hypothesis). -/
def KidsOk (k : ℕ) : Prop := ∀ a < k, (E.get a).cut = true → ir.WiresOk c env E rd V a

/-- **Tree expressions carry node `k`'s meaning** at every coordinate below its length. -/
def NodeOk (k : ℕ) (ts : List TE) : Prop :=
  ∀ j < (E.get k).len, (ts.getD j default).eval (I (ir.circField c)).decode V =
    ir.nodeSem env E rd (ir.circuit c).domain k j

/-- **An expansion of node `k` is sound**: one tree expression per coordinate, each of the node's
meaning. -/
def ExpOk (k : ℕ) (ts : List TE) : Prop :=
  ts.length = (E.get k).len ∧ NodeOk (ir := ir) (c := c) (env := env) (E := E) (rd := rd) (V := V)
    k ts

/-- **A kid reader is sound below `k`**: where the cuts it returns hold, it reads a kid below `k`,
at most the kid's length, one tree expression per coordinate asked, each of the kid's meaning. -/
def KidSpec (kid : ℕ → ℕ → Except TReason (List TE × Cuts)) (k : ℕ) : Prop :=
  ∀ a n r, kid a n = .ok r → CutsHold (ir := ir) (c := c) (V := V) r.2 →
    a < k ∧ n ≤ (E.get a).len ∧ r.1.length = n ∧ ∀ j < n,
      (r.1.getD j default).eval (I (ir.circField c)).decode V =
        ir.nodeSem env E rd (ir.circuit c).domain a j

/-- **The table's kid reader is sound** where the cut nodes below `k` carry their meaning and the
expansions `rec` of the nodes below `k` are sound. -/
theorem kidSpec_kidTEF {rec : ℕ → Except TReason (List TE × Cuts)} {k : ℕ}
    (IH : KidsOk (ir := ir) (c := c) (env := env) (E := E) (rd := rd) (V := V) k)
    (hrec : ∀ a < k, ∀ r, rec a = .ok r → CutsHold (ir := ir) (c := c) (V := V) r.2 →
      ExpOk (ir := ir) (c := c) (env := env) (E := E) (rd := rd) (V := V) a r.1) :
    KidSpec (ir := ir) (c := c) (env := env) (E := E) (rd := rd) (V := V) (kidTEF E rec k) k := by
  intro a n r h hcs
  unfold kidTEF at h
  cases hb : (Nat.blt a k && Nat.ble n (E.get a).len)
  · simp [hb] at h
  · simp only [hb, Bool.cond_true] at h
    simp only [Bool.and_eq_true, Nat.blt_eq, Nat.ble_eq] at hb
    obtain ⟨hak, hn⟩ := hb
    cases hcut : (E.get a).cut
    · simp only [hcut, Bool.cond_false, except_bind_eq_ok, Except.ok.injEq] at h
      obtain ⟨r', hr', rfl⟩ := h
      obtain ⟨hl, hv⟩ := hrec a hak r' hr' hcs
      rw [takeL_eq hl]
      refine ⟨hak, hn, by simp [hl]; omega, fun j hj => ?_⟩
      rw [getD_take_lt hj]
      exact hv j (by omega)
    · simp only [hcut, Bool.cond_true, Except.ok.injEq] at h
      subst h
      obtain ⟨hw, hv⟩ := IH a hak hcut
      rw [takeL_eq (by simp [hw]), ← List.map_take]
      refine ⟨hak, hn, by simp [hw]; omega, fun j hj => ?_⟩
      rw [getD_map_lt' _ (by simp [hw]; omega), getD_take_lt hj, teW_eval]
      exact hv j (by omega)

theorem kidAll_binds {kid : ℕ → ℕ → Except TReason (List TE × Cuts)} {k a : ℕ}
    {r : List TE × Cuts}
    (hkid : KidSpec (ir := ir) (c := c) (env := env) (E := E) (rd := rd) (V := V) kid k)
    (h : kid a (E.get a).len = .ok r) (hcs : CutsHold (ir := ir) (c := c) (V := V) r.2) :
    a < k ∧ ir.TEBinds c env E rd V (.ref a) r.1 := by
  obtain ⟨hak, -, hl, hv⟩ := hkid a _ r h hcs
  exact ⟨hak, ⟨by rw [hl]; rfl, fun j hj => by rw [hv j (by omega)]; rfl⟩⟩

/-- **A row's values give a node's meaning**: where the node's row evaluates to the tree
expressions. -/
theorem nodeOk_of_row (hE : ir.EmitTableOk env E) {k : ℕ} {ts : List TE}
    (hv : ∀ j < (E.get k).len, Expr.eval ir (ir.circField c) rd
      (fun a => ir.nodeSem env E rd (ir.circuit c).domain a) (fun a => (E.get a).len)
      ((E.get k).node.row env) j = (ts.getD j default).eval (I (ir.circField c)).decode V) :
    NodeOk (ir := ir) (c := c) (env := env) (E := E) (rd := rd) (V := V) k ts := fun j hj => by
  rw [← hv j hj, congrFun (nodeSem_eq hE rd _ k) j]

/-! ### Operators -/

/-- **A zero constant of the circuit's field reads `0`.** -/
theorem zeroConst_read (hA : env.ar.Hom (I (ir.circField c)).decode)
    (hK : ∀ v es, (ir.value v).kind = .constant es → ∀ i,
      rd v i = (I (ir.valueField v)).decode (es.getD i 0))
    {z : ℕ} (hz : ir.zeroConstB z = true) (hf : ir.valueField z = ir.circField c) (i : ℕ) :
    (castElt (rd z i) : (I (ir.circField c)).K) = 0 := by
  unfold zeroConstB at hz
  split at hz
  · rename_i es hk
    rw [hK z es hk i]
    have h00 : es.getD i 0 = 0 := by
      rw [List.getD_eq_getElem?_getD]
      cases hes : es[i]? with
      | none => rfl
      | some c' =>
        have := List.all_eq_true.1 hz c' (List.mem_of_getElem? hes)
        simpa using this
    rw [h00, castElt_decode hf, hA.zero]
  · cases hz

theorem opTE_binds (hA : env.ar.Hom (I (ir.circField c)).decode)
    (hK : ∀ v es, (ir.value v).kind = .constant es → ∀ i,
      rd v i = (I (ir.valueField v)).decode (es.getD i 0))
    {x : Expr} {xs ys : List TE} (op : EOp) (h : opTE ir c env op xs = .ok ys)
    (hx : ir.TEBinds c env E rd V x xs) : ir.TEBinds c env E rd V (op.wrap x) ys := by
  obtain ⟨hxl, hxv⟩ := hx
  rcases op with ⟨idx, _ | z⟩ | nop | rows | ⟨nop, mask⟩
  · simp only [opTE] at h
    obtain ⟨hr, rfl⟩ := cond_ok_eq_ok h
    rw [pickL_eq hr]
    refine ⟨by simp [EOp.wrap, Expr.len, IndexMap.length_toList], fun j hj => ?_⟩
    simp only [List.length_map, IndexMap.length_toList] at hj
    have he := IndexMap.entry_lt_of_inRange hr hj
    simp only [EOp.wrap, Expr.eval]
    rw [getD_map_lt' _ (by rw [IndexMap.length_toList]; exact hj)]
    rw [show idx.toList.getD j default = idx.entry j from
        (IndexMap.entry_eq_getD_toList idx j).symm,
      PTree.get_ofList _ he, hxv _ he]
  · simp only [opTE] at h
    obtain ⟨hr, rfl⟩ := cond_ok_eq_ok h
    simp only [Bool.and_eq_true, Nat.beq_eq] at hr
    obtain ⟨⟨hr, hz⟩, hzf⟩ := hr
    refine ⟨by simp [EOp.wrap, Expr.len, IndexMap.length_toList], fun j hj => ?_⟩
    simp only [List.length_map, IndexMap.length_toList] at hj
    have he := IndexMap.entry_lt_of_inRange hr hj
    simp only [EOp.wrap, Expr.eval]
    rw [getD_map_lt' _ (by rw [IndexMap.length_toList]; exact hj)]
    rw [show idx.toList.getD j default = idx.entry j from
        (IndexMap.entry_eq_getD_toList idx j).symm,
      hxl]
    by_cases hlt : idx.entry j < xs.length
    · have hb : Nat.blt (idx.entry j) xs.length = true := by simpa using hlt
      simp only [hlt, ↓reduceIte, hb, Bool.cond_true]
      rw [PTree.get_ofList _ hlt, hxv _ hlt]
    · have hb : Nat.blt (idx.entry j) xs.length = false :=
        Bool.eq_false_iff.2 fun h' => hlt (by simpa using h')
      simp only [hlt, ↓reduceIte, hb, Bool.cond_false, TE.eval, hA.zero]
      exact zeroConst_read hA hK hz hzf _
  · simp only [opTE] at h
    split at h
    · cases h
    · rename_i rows' hrw
      obtain ⟨hr, rfl⟩ := cond_ok_eq_ok h
      simp only [Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq] at hr
      obtain ⟨⟨hC, -⟩, hin⟩ := hr
      obtain ⟨hRl, hRv⟩ := emitRows_sound rd hA hK rfl nop hrw
      have hlen : (shiftRows (NamedOp.cols ir nop) (xs.length / NamedOp.cols ir nop) rows').length =
          xs.length / NamedOp.cols ir nop * NamedOp.rows ir nop := by
        rw [length_shiftRows, hRl]
      refine ⟨by simp [EOp.wrap, Expr.len, hxl, hlen], fun j hj => ?_⟩
      simp only [List.length_map, hlen] at hj
      have hR0 : 0 < NamedOp.rows ir nop := Nat.pos_of_ne_zero fun h0 => by simp [h0] at hj
      have hjr :
          j < (shiftRows (NamedOp.cols ir nop) (xs.length / NamedOp.cols ir nop) rows').length := by
        rw [hlen]; exact hj
      rw [getD_map_lt' _ hjr, rowTE_eval hA.zero hA.one]
      have hrow : (shiftRows (NamedOp.cols ir nop) (xs.length / NamedOp.cols ir nop) rows').getD j
          default = _ := getD_shiftRows hRl hR0 hj
      have hmem := getD_mem_lt hjr
      have hcols := List.all_eq_true.1 hin _ hmem
      rw [rowEval_congr (g' := Expr.eval ir (ir.circField c) rd
        (fun a => ir.nodeSem env E rd (ir.circuit c).domain a) (fun a => (E.get a).len) x)
        fun t ht => by
          have htl : t.1 < xs.length := by simpa using List.all_eq_true.1 hcols t ht
          rw [PTree.get_ofList _ htl, hxv _ htl]]
      rw [hrow, rowEval_shift, hRv _ _ (Nat.mod_lt _ hR0)]
      simp only [EOp.wrap, Expr.eval, NamedOp.apply]
  · simp only [opTE] at h
    split at h
    · cases h
    · rename_i rs hrs
      obtain ⟨hin, rfl⟩ := cond_ok_eq_ok h
      have hF := forall₂_getD' (dx := []) (dy := []) (option_mapM_forall₂ hrs)
      refine ⟨by simp [EOp.wrap, Expr.len, hF.1], fun j hj => ?_⟩
      simp only [List.length_map] at hj
      have hjr : j < rows.length := by rw [← hF.1]; exact hj
      rw [getD_map_lt' _ hj, rowTE_eval hA.zero hA.one]
      have hmem := getD_mem_lt hj
      have hcols := List.all_eq_true.1 hin _ hmem
      rw [rowEval_congr (g' := Expr.eval ir (ir.circField c) rd
        (fun a => ir.nodeSem env E rd (ir.circuit c).domain a) (fun a => (E.get a).len) x)
        fun t ht => by
          have htl : t.1 < xs.length := by simpa using List.all_eq_true.1 hcols t ht
          rw [PTree.get_ofList _ htl, hxv _ htl]]
      have hrow := hF.2 j hjr
      have hF2 : List.Forall₂ (fun t p => p.1 = t.1 ∧
          (I (ir.circField c)).decode p.2 = Coef.eval ir (ir.circField c) rd t.2)
          (rows.getD j []) (rs.getD j []) := (option_mapM_forall₂ hrow).imp fun t p hp => by
        simp only [Option.map_eq_some_iff] at hp
        obtain ⟨a, ha, rfl⟩ := hp
        exact ⟨rfl, coefCode_sound hK rfl ha⟩
      rw [show rs.getD j default = rs.getD j [] from rfl, rowEval_of_forall₂ rd _ hF2]
      simp only [EOp.wrap, Expr.eval]
  · simp [opTE] at h

theorem opsTE_binds (hA : env.ar.Hom (I (ir.circField c)).decode)
    (hK : ∀ v es, (ir.value v).kind = .constant es → ∀ i,
      rd v i = (I (ir.valueField v)).decode (es.getD i 0)) :
    ∀ (ops : List EOp) {x : Expr} {xs ys : List TE}, opsTE ir c env ops xs = .ok ys →
      ir.TEBinds c env E rd V x xs →
      ir.TEBinds c env E rd V (ops.foldl (fun x op => op.wrap x) x) ys
  | [], x, xs, ys, h, hx => by
    simp only [opsTE] at h
    cases h
    exact hx
  | op :: ops, x, xs, ys, h, hx => by
    simp only [opsTE, except_bind_eq_ok] at h
    obtain ⟨zs, h1, h2⟩ := h
    exact opsTE_binds hA hK ops h2 (opTE_binds hA hK op h1 hx)

/-! ### List positions -/

theorem getD_range_map {α : Type} [Inhabited α] (f : ℕ → α) {n j : ℕ} (hj : j < n) :
    ((List.range n).map f).getD j default = f j := by
  rw [getD_map_lt' _ (by simpa using hj), List.getD_eq_getElem _ _ (by simpa using hj),
    List.getElem_range]

theorem getD_range_lt {n j : ℕ} (hj : j < n) : (List.range n).getD j default = j := by
  rw [List.getD_eq_getElem _ _ (by simpa using hj), List.getElem_range]

theorem getD_range_lt' {n j : ℕ} (hj : j < n) : (List.range n).getD j 0 = j := by
  rw [List.getD_eq_getElem _ _ (by simpa using hj), List.getElem_range]

theorem getD_zipWith' {α β γ : Type} [Inhabited α] [Inhabited β] [Inhabited γ] (f : α → β → γ)
    {l₁ : List α} {l₂ : List β} {j : ℕ} (h₁ : j < l₁.length) (h₂ : j < l₂.length) :
    (List.zipWith f l₁ l₂).getD j default = f (l₁.getD j default) (l₂.getD j default) := by
  rw [List.getD_eq_getElem _ _ (by simp [h₁, h₂]), List.getElem_zipWith,
    List.getD_eq_getElem _ _ h₁, List.getD_eq_getElem _ _ h₂]

theorem getD_zip' {α β : Type} [Inhabited α] [Inhabited β] {l₁ : List α} {l₂ : List β} {j : ℕ}
    (h₁ : j < l₁.length) (h₂ : j < l₂.length) :
    (l₁.zip l₂).getD j default = (l₁.getD j default, l₂.getD j default) := by
  rw [List.getD_eq_getElem _ _ (by simp [h₁, h₂]), List.getElem_zip,
    List.getD_eq_getElem _ _ h₁, List.getD_eq_getElem _ _ h₂]

theorem length_slices {α : Type} (w : ℕ) : ∀ (n : ℕ) (l : List α), (slices w n l).length = n
  | 0, _ => rfl
  | n + 1, l => by simp [slices, length_slices w n]

theorem getD_slices {α : Type} (w : ℕ) : ∀ (n : ℕ) (l : List α) {j : ℕ}, j < n →
    (slices w n l).getD j [] = (l.drop (j * w)).take w
  | 0, _, _, hj => absurd hj (Nat.not_lt_zero _)
  | n + 1, l, j, hj => by
    cases j with
    | zero => simp [slices]
    | succ j =>
      simp only [slices, List.getD_cons_succ]
      rw [getD_slices w n (l.drop w) (by omega), List.drop_drop]
      congr 2
      ring

/-! ### The kinds -/

theorem nodeOk_of_binds (hE : ir.EmitTableOk env E) {k : ℕ} {ts : List TE}
    (hb : ir.TEBinds c env E rd V ((E.get k).node.row env) ts) :
    NodeOk (ir := ir) (c := c) (env := env) (E := E) (rd := rd) (V := V) k ts :=
  nodeOk_of_row hE fun j hj => hb.2 j (by rw [← hb.1, ← hE.len_eq k]; exact hj)

theorem forall₂_and_right {α β : Type} {R : α → β → Prop} {P : β → Prop} :
    ∀ {l₁ : List α} {l₂ : List β}, List.Forall₂ R l₁ l₂ → (∀ b ∈ l₂, P b) →
      List.Forall₂ (fun a b => R a b ∧ P b) l₁ l₂
  | [], [], .nil, _ => .nil
  | _ :: _, b :: _, .cons h hs, hP =>
    .cons ⟨h, hP b (by simp)⟩ (forall₂_and_right hs fun b' hb' => hP b' (by simp [hb']))

theorem lnotT_eval (hAr : env.ArithOk (I (ir.circField c)).decode) (x : TE) :
    (lnotT env x).eval (I (ir.circField c)).decode V =
      1 - x.eval (I (ir.circField c)).decode V := by
  have hA := hAr.hom
  cases x with
  | wire c0 c1 n =>
    simp only [lnotT, teW_eval, lnotW, Wire.val, TE.eval, hA.add, cmul_hom hA, hA.one, hAr.neg1]
    ring
  | const k =>
    simp only [lnotT, TE.eval, hA.add, cmul_hom hA, hA.one, hAr.neg1]
    ring
  | _ =>
    simp only [lnotT, TE.eval, hA.one, hAr.neg1]
    ring

section Steps

variable {kid : ℕ → ℕ → Except TReason (List TE × Cuts)} {k : ℕ} {r : List TE × Cuts}

theorem constStep_sound (hE : ir.EmitTableOk env E)
    (hK : ∀ v es, (ir.value v).kind = .constant es → ∀ i,
      rd v i = (I (ir.valueField v)).decode (es.getD i 0))
    {v : ℕ} (hk : (E.get k).node = .const v) (h : ir.nodeStep c env E kid k = .ok r) :
    NodeOk (ir := ir) (c := c) (env := env) (E := E) (rd := rd) (V := V) k r.1 := by
  unfold nodeStep at h
  simp only [hk, except_bind_eq_ok, chk_eq_ok, Except.ok.injEq] at h
  obtain ⟨_, -, es, hes, rfl⟩ := h
  have hes' : constCodes? ir c v = some es := by
    unfold constE at hes
    split at hes
    · cases hes
      assumption
    · cases hes
  refine nodeOk_of_row hE fun j hj => ?_
  rw [getD_map_lt' _ (by rw [length_padTo]; exact hj), hk]
  simp only [show (default : ℕ) = 0 from rfl, getD_padTo es hj]
  simp only [ENode.row, Expr.eval, TE.eval]
  exact constCodes?_read hK rfl hes' j

theorem linNilStep_sound (hAr : env.ArithOk (I (ir.circField c)).decode)
    (hE : ir.EmitTableOk env E)
    (hK : ∀ v es, (ir.value v).kind = .constant es → ∀ i,
      rd v i = (I (ir.valueField v)).decode (es.getD i 0))
    {z : ℕ} (hk : (E.get k).node = .lin [] z) (h : ir.nodeStep c env E kid k = .ok r) :
    NodeOk (ir := ir) (c := c) (env := env) (E := E) (rd := rd) (V := V) k r.1 := by
  unfold nodeStep at h
  simp only [hk, except_bind_eq_ok, chk_eq_ok, Nat.beq_eq, Except.ok.injEq, Bool.and_eq_true] at h
  obtain ⟨_, -, _, ⟨hz, hzf⟩, rfl⟩ := h
  refine nodeOk_of_row hE fun j hj => ?_
  rw [List.getD_eq_getElem _ _ (by simpa using hj), List.getElem_replicate, hk]
  simp only [ENode.row, linRow, Expr.eval, TE.eval, hAr.hom.zero]
  exact zeroConst_read hAr.hom hK hz hzf j

theorem scaleStep_sound (hAr : env.ArithOk (I (ir.circField c)).decode)
    (hE : ir.EmitTableOk env E)
    (hkid : KidSpec (ir := ir) (c := c) (env := env) (E := E) (rd := rd) (V := V) kid k)
    {s a : ℕ} (hk : (E.get k).node = .scale s a) (h : ir.nodeStep c env E kid k = .ok r)
    (hcs : CutsHold (ir := ir) (c := c) (V := V) r.2) :
    NodeOk (ir := ir) (c := c) (env := env) (E := E) (rd := rd) (V := V) k r.1 := by
  unfold nodeStep at h
  simp only [hk, except_bind_eq_ok, chk_eq_ok, Except.ok.injEq] at h
  obtain ⟨_, -, r', hr', rfl⟩ := h
  obtain ⟨-, -, hxl, hxv⟩ := hkid a _ r' hr' hcs
  refine nodeOk_of_row hE fun j hj => ?_
  rw [getD_map_lt' _ (by omega), hk]
  simp only [TE.eval, ENode.row]
  rw [hxv j hj]
  cases hs : Nat.beq s 1
  · simp only [Bool.cond_false, Expr.eval, Coef.eval]
  · simp only [Nat.beq_eq] at hs
    simp only [Bool.cond_true, Expr.eval, hs, hAr.hom.one, one_mul]

theorem materializeStep_sound (hE : ir.EmitTableOk env E)
    (hkid : KidSpec (ir := ir) (c := c) (env := env) (E := E) (rd := rd) (V := V) kid k)
    {a : ℕ} (hk : (E.get k).node = .materialize a) (h : ir.nodeStep c env E kid k = .ok r)
    (hcs : CutsHold (ir := ir) (c := c) (V := V) r.2) :
    NodeOk (ir := ir) (c := c) (env := env) (E := E) (rd := rd) (V := V) k r.1 := by
  unfold nodeStep at h
  simp only [hk, except_bind_eq_ok, chk_eq_ok] at h
  obtain ⟨_, -, h⟩ := h
  obtain ⟨-, -, -, hxv⟩ := hkid a _ r h hcs
  refine nodeOk_of_row hE fun j hj => ?_
  rw [hxv j hj, hk]
  rfl

theorem lnotStep_sound (hAr : env.ArithOk (I (ir.circField c)).decode)
    (hE : ir.EmitTableOk env E)
    (hK : ∀ v es, (ir.value v).kind = .constant es → ∀ i,
      rd v i = (I (ir.valueField v)).decode (es.getD i 0))
    (hkid : KidSpec (ir := ir) (c := c) (env := env) (E := E) (rd := rd) (V := V) kid k)
    {o a : ℕ} (hk : (E.get k).node = .lnot o a) (h : ir.nodeStep c env E kid k = .ok r)
    (hcs : CutsHold (ir := ir) (c := c) (V := V) r.2) :
    NodeOk (ir := ir) (c := c) (env := env) (E := E) (rd := rd) (V := V) k r.1 := by
  unfold nodeStep at h
  simp only [hk, except_bind_eq_ok, chk_eq_ok, Except.ok.injEq] at h
  obtain ⟨_, -, es, hes, r', hr', rfl⟩ := h
  have hes' : constCodes? ir c o = some es := by
    unfold constE at hes
    split at hes
    · cases hes
      assumption
    · cases hes
  obtain ⟨-, -, hxl, hxv⟩ := hkid a _ r' hr' hcs
  refine nodeOk_of_row hE fun j hj => ?_
  rw [getD_zipWith' _ (by rw [length_padTo]; exact hj) (by omega), hk]
  simp only [show (default : ℕ) = 0 from rfl, getD_padTo es hj]
  simp only [TE.eval, hxv j hj, ENode.row, Expr.eval, hAr.neg1]
  rw [constCodes?_read hK rfl hes' j]
  ring

theorem muxBitStep_sound (hAr : env.ArithOk (I (ir.circField c)).decode)
    (hE : ir.EmitTableOk env E)
    (hkid : KidSpec (ir := ir) (c := c) (env := env) (E := E) (rd := rd) (V := V) kid k)
    {cc t e : ℕ} (hk : (E.get k).node = .mux true cc t e) (h : ir.nodeStep c env E kid k = .ok r)
    (hcs : CutsHold (ir := ir) (c := c) (V := V) r.2) :
    NodeOk (ir := ir) (c := c) (env := env) (E := E) (rd := rd) (V := V) k r.1 := by
  unfold nodeStep at h
  simp only [hk, except_bind_eq_ok, chk_eq_ok, Except.ok.injEq] at h
  obtain ⟨_, -, rc, hc, rt, ht, re, he, rfl⟩ := h
  simp only [cutsHold_append] at hcs
  obtain ⟨⟨hcc, hct⟩, hce⟩ := hcs
  obtain ⟨-, -, hcl, hcv⟩ := hkid cc _ rc hc hcc
  obtain ⟨-, -, htl, htv⟩ := hkid t _ rt ht hct
  obtain ⟨-, -, hel, hev⟩ := hkid e _ re he hce
  refine nodeOk_of_row hE fun j hj => ?_
  rw [getD_zipWith' _ (by omega) (by simp; omega), getD_zip' (by omega) (by omega), hk]
  simp only [TE.eval, lnotT_eval hAr]
  rw [hcv j hj, htv j hj, hev j hj]
  simp only [ENode.row, Expr.eval]

theorem muxFieldStep_sound (hAr : env.ArithOk (I (ir.circField c)).decode)
    (hE : ir.EmitTableOk env E)
    (hkid : KidSpec (ir := ir) (c := c) (env := env) (E := E) (rd := rd) (V := V) kid k)
    {cc t e : ℕ} (hk : (E.get k).node = .mux false cc t e) (h : ir.nodeStep c env E kid k = .ok r)
    (hcs : CutsHold (ir := ir) (c := c) (V := V) r.2) :
    NodeOk (ir := ir) (c := c) (env := env) (E := E) (rd := rd) (V := V) k r.1 := by
  unfold nodeStep at h
  simp only [hk, except_bind_eq_ok, chk_eq_ok, Nat.beq_eq, Except.ok.injEq] at h
  obtain ⟨rc, hc, rt, ht, re, he, _, hal, rfl⟩ := h
  simp only [cutsHold_append] at hcs
  obtain ⟨⟨⟨hd, hcc⟩, hct⟩, hce⟩ := hcs
  obtain ⟨-, -, hcl, hcv⟩ := hkid cc _ rc hc hcc
  obtain ⟨-, -, htl, htv⟩ := hkid t _ rt ht hct
  obtain ⟨-, -, hel, hev⟩ := hkid e _ re he hce
  refine nodeOk_of_row hE fun j hj => ?_
  have hjA : j < (List.zipWith (fun d (p : TE × TE) =>
      (d, TE.add p.1 (.scale env.neg1 p.2))) (E.get k).aux (rt.1.zip re.1)).length := by
    simp; omega
  have hdj := hd _ (getD_mem_lt hjA)
  rw [getD_zipWith' _ (by omega) (by simp; omega), getD_zip' (by omega) (by omega)] at hdj
  simp only [TE.eval, htv j hj, hev j hj, hAr.neg1] at hdj
  rw [getD_zipWith' _ (by omega) (by simp; omega), getD_zip' (by omega) (by omega), hk]
  simp only [TE.eval, teW_eval, hcv j hj, hev j hj, hdj, ENode.row, Expr.eval]
  ring

theorem applyStep_sound (hAr : env.ArithOk (I (ir.circField c)).decode)
    (hE : ir.EmitTableOk env E)
    (hK : ∀ v es, (ir.value v).kind = .constant es → ∀ i,
      rd v i = (I (ir.valueField v)).decode (es.getD i 0))
    (hkid : KidSpec (ir := ir) (c := c) (env := env) (E := E) (rd := rd) (V := V) kid k)
    {op : EOp} {a : ℕ} (hk : (E.get k).node = .apply op a) (hs : staged? op = none)
    (h : ir.nodeStep c env E kid k = .ok r)
    (hcs : CutsHold (ir := ir) (c := c) (V := V) r.2) :
    NodeOk (ir := ir) (c := c) (env := env) (E := E) (rd := rd) (V := V) k r.1 := by
  unfold nodeStep at h
  simp only [hk, hs, except_bind_eq_ok, chk_eq_ok, Except.ok.injEq] at h
  obtain ⟨_, -, r', hr', ys, hy, rfl⟩ := h
  obtain ⟨-, hb⟩ := kidAll_binds hkid hr' hcs
  exact nodeOk_of_binds hE (by rw [hk]; exact opTE_binds hAr.hom hK op hy hb)

theorem broadcastStep_sound (hAr : env.ArithOk (I (ir.circField c)).decode)
    (hE : ir.EmitTableOk env E)
    (hK : ∀ v es, (ir.value v).kind = .constant es → ∀ i,
      rd v i = (I (ir.valueField v)).decode (es.getD i 0))
    (hkid : KidSpec (ir := ir) (c := c) (env := env) (E := E) (rd := rd) (V := V) kid k)
    {idx : IndexMap} {a : ℕ} (hk : (E.get k).node = .broadcast idx a)
    (h : ir.nodeStep c env E kid k = .ok r) (hcs : CutsHold (ir := ir) (c := c) (V := V) r.2) :
    NodeOk (ir := ir) (c := c) (env := env) (E := E) (rd := rd) (V := V) k r.1 := by
  unfold nodeStep at h
  simp only [hk, except_bind_eq_ok, chk_eq_ok, Except.ok.injEq] at h
  obtain ⟨_, -, r', hr', _, hr, rfl⟩ := h
  obtain ⟨-, hb⟩ := kidAll_binds hkid hr' hcs
  have hop : opTE ir c env (.view idx none) r'.1 = .ok (pickL r'.1 idx) := by
    simp [opTE, hr]
  exact nodeOk_of_binds hE (by rw [hk]; exact opTE_binds hAr.hom hK (.view idx none) hop hb)

theorem teBinds_concatRow :
    ∀ {es : List Expr} {tss : List (List TE)}, es ≠ [] →
      List.Forall₂ (fun e ts => ir.TEBinds c env E rd V e ts) es tss →
      ir.TEBinds c env E rd V (concatRow es) tss.flatten
  | [], _, hne, _ => absurd rfl hne
  | [e], [ts], _, .cons h .nil => by simpa [concatRow] using h
  | e :: e' :: es, ts :: ts' :: tss, _, .cons h hs => by
    obtain ⟨hl, hv⟩ := teBinds_concatRow (es := e' :: es) (by simp) hs
    obtain ⟨hl0, hv0⟩ := h
    refine ⟨?_, fun j hj => ?_⟩
    · simp only [concatRow, Expr.len, hl0, hl, List.flatten_cons, List.length_append]
    · simp only [concatRow, Expr.eval, List.flatten_cons] at hj ⊢
      rw [hl0]
      simp only [List.length_append] at hj
      split_ifs with hj0
      · rw [hv0 j hj0, List.getD_append _ _ _ _ hj0]
      · rw [hv (j - ts.length) (by simp only [List.flatten_cons, List.length_append]; omega),
          List.getD_append_right _ _ _ _ (by omega), List.flatten_cons]

theorem gatherStep_sound (hAr : env.ArithOk (I (ir.circField c)).decode)
    (hE : ir.EmitTableOk env E)
    (hK : ∀ v es, (ir.value v).kind = .constant es → ∀ i,
      rd v i = (I (ir.valueField v)).decode (es.getD i 0))
    (hkid : KidSpec (ir := ir) (c := c) (env := env) (E := E) (rd := rd) (V := V) kid k)
    {idx : IndexMap} {ps : List ℕ} (hk : (E.get k).node = .gather idx ps)
    (h : ir.nodeStep c env E kid k = .ok r) (hcs : CutsHold (ir := ir) (c := c) (V := V) r.2) :
    NodeOk (ir := ir) (c := c) (env := env) (E := E) (rd := rd) (V := V) k r.1 := by
  unfold nodeStep at h
  simp only [hk, except_bind_eq_ok, chk_eq_ok, Except.ok.injEq, flattenL_eq] at h
  obtain ⟨_, -, _, hne, rs, hrs, _, hr, rfl⟩ := h
  have hcs' : ∀ q ∈ rs, CutsHold (ir := ir) (c := c) (V := V) q.2 := fun q hq =>
    cutsHold_flatten.1 hcs _ (List.mem_map_of_mem hq)
  have hF := forall₂_and_right (except_mapM_forall₂ hrs) hcs'
  have hF' : List.Forall₂ (fun e ts => ir.TEBinds c env E rd V e ts) (ps.map Expr.ref)
      (rs.map Prod.fst) := by
    rw [List.forall₂_map_left_iff, List.forall₂_map_right_iff]
    exact hF.imp fun p q hpq => (kidAll_binds hkid hpq.1 hpq.2).2
  have hC := teBinds_concatRow (by simpa using hne) hF'
  have hop : opTE ir c env (.view idx none) (rs.map Prod.fst).flatten =
      .ok (pickL (rs.map Prod.fst).flatten idx) := by
    simp only [opTE, hr, Bool.cond_true]
  exact nodeOk_of_binds hE (by rw [hk]; exact opTE_binds hAr.hom hK (.view idx none) hop hC)

theorem sumStep_sound (hAr : env.ArithOk (I (ir.circField c)).decode) (hE : ir.EmitTableOk env E)
    (hkid : KidSpec (ir := ir) (c := c) (env := env) (E := E) (rd := rd) (V := V) kid k)
    {w a : ℕ} (hk : (E.get k).node = .sum w a) (h : ir.nodeStep c env E kid k = .ok r)
    (hcs : CutsHold (ir := ir) (c := c) (V := V) r.2) :
    NodeOk (ir := ir) (c := c) (env := env) (E := E) (rd := rd) (V := V) k r.1 := by
  unfold nodeStep at h
  simp only [hk, except_bind_eq_ok, chk_eq_ok, Except.ok.injEq] at h
  obtain ⟨_, -, r', hr', rfl⟩ := h
  obtain ⟨-, -, hxl, hxv⟩ := hkid a _ r' hr' hcs
  refine nodeOk_of_row hE fun j hj => ?_
  have hjw : ∀ t < w, j * w + t < (E.get k).len * w := fun t ht => by
    have : (j + 1) * w ≤ (E.get k).len * w := Nat.mul_le_mul_right _ hj
    rw [add_mul, one_mul] at this
    omega
  have hsl : (r'.1.drop (j * w)).take w =
      (List.range w).map fun t => r'.1.getD (j * w + t) default := by
    refine List.ext_getElem ?_ fun t h1 h2 => ?_
    · simp only [List.length_take, List.length_drop, List.length_map, List.length_range, hxl]
      rcases Nat.eq_zero_or_pos w with hw0 | hw0
      · simp [hw0]
      · have := hjw (w - 1) (by omega)
        omega
    · simp only [List.getElem_take, List.getElem_drop, List.getElem_map, List.getElem_range]
      rw [List.getD_eq_getElem]
  rw [getD_map_lt' _ (by rw [length_slices]; exact hj), show (slices w (E.get k).len r'.1).getD j
    default = _ from getD_slices w _ r'.1 hj, hsl, hk, sumL_eval (κc := (I (ir.circField c)).decode)
    (v := V) hAr.hom.zero]
  simp only [ENode.row, Expr.eval, NamedOp.apply, NamedOp.block, NamedOp.rows, NamedOp.cols,
    Ops.sum, Nat.mod_one, Nat.div_one, ↓reduceIte, List.map_map]
  rw [sum_map_range, Fin.sum_univ_eq_sum_range (fun t => ir.nodeSem env E rd (ir.circuit c).domain a
    (j * w + t)) w]
  refine Finset.sum_congr rfl fun t ht => ?_
  rw [Finset.mem_range] at ht
  simp only [Function.comp]
  rw [hxv _ (hjw t ht)]

theorem termTE_binds (hAr : env.ArithOk (I (ir.circField c)).decode)
    (hK : ∀ v es, (ir.value v).kind = .constant es → ∀ i,
      rd v i = (I (ir.valueField v)).decode (es.getD i 0))
    (hkid : KidSpec (ir := ir) (c := c) (env := env) (E := E) (rd := rd) (V := V) kid k)
    {n : ℕ} {t : ETerm} (h : termTE ir c env E kid n t = .ok r)
    (hcs : CutsHold (ir := ir) (c := c) (V := V) r.2) :
    r.1.length = n ∧ ir.TEBinds c env E rd V t.row r.1 := by
  unfold termTE at h
  simp only [except_bind_eq_ok, chk_eq_ok, Nat.beq_eq, Except.ok.injEq] at h
  obtain ⟨r', hr', ys, hy, _, hyl, rfl⟩ := h
  obtain ⟨-, hb⟩ := kidAll_binds hkid hr' hcs
  obtain ⟨hbl, hbv⟩ := opsTE_binds hAr.hom hK t.ops hy hb
  unfold ETerm.row
  cases hs : Nat.beq t.scale 1
  · simp only [Bool.cond_false]
    refine ⟨by simp [hyl], ?_, fun j hj => ?_⟩
    · simp [Expr.len, hbl]
    · simp only [List.length_map] at hj
      rw [getD_map_lt' _ hj]
      simp only [Expr.eval, Coef.eval, TE.eval, hbv j hj]
  · simp only [Nat.beq_eq] at hs
    exact ⟨by simpa using hyl, by simpa using hbl, fun j hj => by simpa using hbv j hj⟩

theorem termsTE_binds (hAr : env.ArithOk (I (ir.circField c)).decode)
    (hK : ∀ v es, (ir.value v).kind = .constant es → ∀ i,
      rd v i = (I (ir.valueField v)).decode (es.getD i 0))
    (hkid : KidSpec (ir := ir) (c := c) (env := env) (E := E) (rd := rd) (V := V) kid k)
    {n : ℕ} :
    ∀ (ts : List ETerm) {A : Expr} {acc : List TE} {q : List TE × Cuts}, acc.length = n →
      ir.TEBinds c env E rd V A acc → termsTE ir c env E kid n ts acc = .ok q →
      CutsHold (ir := ir) (c := c) (V := V) q.2 →
      ir.TEBinds c env E rd V (ts.foldl (fun acc t' => .add acc t'.row) A) q.1
  | [], A, acc, q, _, hA, h, _ => by
    simp only [termsTE, Except.ok.injEq] at h
    subst h
    exact hA
  | t :: ts, A, acc, q, hl, hA, h, hcs => by
    simp only [termsTE, except_bind_eq_ok, Except.ok.injEq] at h
    obtain ⟨r', hr', q', hq', rfl⟩ := h
    dsimp only at hcs
    rw [cutsHold_append] at hcs
    obtain ⟨hyl, hyb⟩ := termTE_binds hAr hK hkid hr' hcs.1
    refine termsTE_binds hAr hK hkid ts (q := q') (by simp [hl, hyl]) ⟨?_, fun j hj => ?_⟩ hq' hcs.2
    · simp [Expr.len, hA.1, hl, hyl]
    · simp only [List.length_zipWith] at hj
      rw [getD_zipWith' _ (by omega) (by omega)]
      simp only [Expr.eval, TE.eval]
      rw [hA.2 j (by omega), hyb.2 j (by omega)]

theorem linConsStep_sound (hAr : env.ArithOk (I (ir.circField c)).decode)
    (hE : ir.EmitTableOk env E)
    (hK : ∀ v es, (ir.value v).kind = .constant es → ∀ i,
      rd v i = (I (ir.valueField v)).decode (es.getD i 0))
    (hkid : KidSpec (ir := ir) (c := c) (env := env) (E := E) (rd := rd) (V := V) kid k)
    {t : ETerm} {ts : List ETerm} {z : ℕ} (hk : (E.get k).node = .lin (t :: ts) z)
    (h : ir.nodeStep c env E kid k = .ok r) (hcs : CutsHold (ir := ir) (c := c) (V := V) r.2) :
    NodeOk (ir := ir) (c := c) (env := env) (E := E) (rd := rd) (V := V) k r.1 := by
  unfold nodeStep at h
  simp only [hk, except_bind_eq_ok, chk_eq_ok, Except.ok.injEq] at h
  obtain ⟨_, -, r', hr', q, hq, rfl⟩ := h
  rw [cutsHold_append] at hcs
  obtain ⟨hyl, hyb⟩ := termTE_binds hAr hK hkid hr' hcs.1
  have hb := termsTE_binds hAr hK hkid ts hyl hyb hq hcs.2
  exact nodeOk_of_binds hE (by rw [hk]; exact hb)

end Steps

/-! ### Chains -/

section Fold

variable {F : Type*}

/-- **A non-empty list folded by `g`** from its head; `e0` for the empty list. -/
def fold1 (g : F → F → F) (e0 : F) : List F → F
  | [] => e0
  | x :: xs => xs.foldl g x

theorem foldl_assoc_cons {g : F → F → F} (hg : ∀ x y z, g (g x y) z = g x (g y z)) :
    ∀ (ys : List F) (a y : F), ys.foldl g (g a y) = g a (ys.foldl g y)
  | [], _, _ => rfl
  | z :: zs, a, y => by
    simp only [List.foldl_cons]
    rw [hg, foldl_assoc_cons hg zs a (g y z)]

/-- **Folding a concatenation** of two non-empty lists by an associative `g`. -/
theorem fold1_append {g : F → F → F} (hg : ∀ x y z, g (g x y) z = g x (g y z))
    (e0 : F) {xs ys : List F} (hx : xs ≠ []) (hy : ys ≠ []) :
    fold1 g e0 (xs ++ ys) = g (fold1 g e0 xs) (fold1 g e0 ys) := by
  obtain ⟨x, xs, rfl⟩ := List.exists_cons_of_ne_nil hx
  obtain ⟨y, ys, rfl⟩ := List.exists_cons_of_ne_nil hy
  simp only [fold1, List.cons_append, List.foldl_append, List.foldl_cons]
  exact foldl_assoc_cons hg ys _ y

theorem fold1_add [CommRing F] : ∀ l : List F, fold1 (· + ·) 0 l = l.sum
  | [] => rfl
  | x :: xs => by
    simp only [fold1, List.sum_cons]
    induction xs generalizing x with
    | nil => simp
    | cons y ys ih => simp only [List.foldl_cons, List.sum_cons, ih (x + y)]; ring

end Fold

theorem leavesOf_ne_nil (op : BinOp) : ∀ (fuel a : ℕ), leavesOf E op fuel a ≠ []
  | 0, a => by simp [leavesOf]
  | fuel + 1, a => by
    unfold leavesOf
    split
    · cases (!(E.get a).cut && decide (_ = op))
      · simp
      · simp [leavesOf_ne_nil op fuel]
    · simp

/-- **A chain node's meaning is the fold of its leaves'** (through uncut kids of the same
combine). -/
theorem leavesOf_sem (hA : env.ar.Hom (I (ir.circField c)).decode) (hE : ir.EmitTableOk env E)
    (op : BinOp) (i : ℕ) : ∀ (fuel a : ℕ),
      ir.nodeSem env E rd (ir.circuit c).domain a i =
        fold1 (op.sem env.char2) 0 ((leavesOf E op fuel a).map
          fun l => ir.nodeSem env E rd (ir.circuit c).domain l i)
  | 0, a => by simp [leavesOf, fold1]
  | fuel + 1, a => by
    unfold leavesOf
    split
    · rename_i op' a1 a2 hn
      cases hb : (!(E.get a).cut && decide (op' = op))
      · simp [fold1]
      · simp only [Bool.and_eq_true, decide_eq_true_eq] at hb
        obtain ⟨-, rfl⟩ := hb
        simp only [Bool.cond_true, List.map_append]
        rw [fold1_append (BinOp.sem_assoc env.char2 op') 0
          (by simpa using leavesOf_ne_nil op' fuel a1)
          (by simpa using leavesOf_ne_nil op' fuel a2), ← leavesOf_sem hA hE op' i fuel a1,
          ← leavesOf_sem hA hE op' i fuel a2]
        exact nodeSem_bin hA hE rd hn i
    · simp [fold1]

theorem combTE_eval (hAr : env.ArithOk (I (ir.circField c)).decode) (op : BinOp) (x y : TE) :
    (combTE env op x y).eval (I (ir.circField c)).decode V =
      op.sem env.char2 (x.eval (I (ir.circField c)).decode V)
        (y.eval (I (ir.circField c)).decode V) := by
  have hA := hAr.hom
  cases op <;> simp only [combTE, TE.eval, BinOp.sem, hAr.neg1]
  · ring
  · cases env.char2 <;> simp only [Bool.cond_true, Bool.cond_false, TE.eval, hAr.neg1,
      hA.add, hA.one]
    ring

theorem chainTree_sound (hAr : env.ArithOk (I (ir.circField c)).decode) (op : BinOp) :
    ∀ (f : ℕ) (ls : List TE) (aux : List Wire) {w : TE} {aux' : List Wire} {cs : Cuts},
      chainTree env op f ls aux = some (w, aux', cs) →
      CutsHold (ir := ir) (c := c) (V := V) cs → ls ≠ [] →
      w.eval (I (ir.circField c)).decode V =
        fold1 (op.sem env.char2) 0 (ls.map (TE.eval (I (ir.circField c)).decode V))
  | _, [], _, _, _, _, _, _, hne => absurd rfl hne
  | f, [x], aux, w, aux', cs, h, _, _ => by
    cases f <;> simp only [chainTree, Option.some.injEq, Prod.mk.injEq] at h <;>
      obtain ⟨rfl, -, -⟩ := h <;> rfl
  | 0, _ :: _ :: _, _, _, _, _, h, _, _ => by simp [chainTree] at h
  | f + 1, x :: y :: zs, aux, w, aux', cs, h, hcs, _ => by
    have hLR : (x :: (y :: zs).take (zs.length / 2)) ++ (y :: zs).drop (zs.length / 2) =
        x :: y :: zs := by
      rw [List.cons_append, List.take_append_drop]
    have hne2 : (y :: zs).drop (zs.length / 2) ≠ [] := by
      simp only [ne_eq, List.drop_eq_nil_iff, List.length_cons]
      omega
    simp only [chainTree] at h
    cases h1 : chainTree env op f (x :: (y :: zs).take (zs.length / 2)) aux with
    | none => simp [h1] at h
    | some r1 =>
      obtain ⟨wl, aux1, c1⟩ := r1
      cases h2 : chainTree env op f ((y :: zs).drop (zs.length / 2)) aux1 with
      | none => simp [h1, h2] at h
      | some r2 =>
        obtain ⟨wr, aux2, c2⟩ := r2
        cases aux2 with
        | nil => simp [h1, h2] at h
        | cons w' aux3 =>
          simp [h1, h2] at h
          obtain ⟨rfl, -, rfl⟩ := h
          have hl := chainTree_sound hAr op f _ _ h1
            (fun q hq => hcs q (by simp [hq])) (List.cons_ne_nil _ _)
          have hr := chainTree_sound hAr op f _ _ h2
            (fun q hq => hcs q (by simp [hq])) hne2
          have hc := hcs (w', combTE env op wl wr) (by simp)
          simp only at hc
          rw [teW_eval, hc, combTE_eval hAr, hl, hr, ← fold1_append (BinOp.sem_assoc env.char2 op) 0
            (by simp) (by simpa using hne2), ← List.map_append, hLR]

theorem chainRoot_sound (hAr : env.ArithOk (I (ir.circField c)).decode) (op : BinOp)
    {ls : List TE} {aux : List Wire} {t : TE} {cs : Cuts}
    (h : chainRoot env op ls aux = some (t, cs))
    (hcs : CutsHold (ir := ir) (c := c) (V := V) cs) :
    t.eval (I (ir.circField c)).decode V =
      fold1 (op.sem env.char2) 0 (ls.map (TE.eval (I (ir.circField c)).decode V)) := by
  match ls, h with
  | [], h => simp [chainRoot] at h
  | [_], h => simp [chainRoot] at h
  | x :: y :: zs, h =>
    have hLR : (x :: (y :: zs).take (zs.length / 2)) ++ (y :: zs).drop (zs.length / 2) =
        x :: y :: zs := by
      rw [List.cons_append, List.take_append_drop]
    have hne2 : (y :: zs).drop (zs.length / 2) ≠ [] := by
      simp only [ne_eq, List.drop_eq_nil_iff, List.length_cons]
      omega
    simp only [chainRoot] at h
    cases h1 : chainTree env op (zs.length + 1 + 1) (x :: (y :: zs).take (zs.length / 2)) aux with
    | none => simp [h1] at h
    | some r1 =>
      obtain ⟨wl, aux1, c1⟩ := r1
      cases h2 : chainTree env op (zs.length + 1 + 1) ((y :: zs).drop (zs.length / 2)) aux1 with
      | none => simp [h1, h2] at h
      | some r2 =>
        obtain ⟨wr, aux2, c2⟩ := r2
        cases aux2 with
        | cons _ _ => simp [h1, h2] at h
        | nil =>
          simp [h1, h2] at h
          obtain ⟨rfl, rfl⟩ := h
          have hl := chainTree_sound hAr op _ _ _ h1 (fun q hq => hcs q (by simp [hq]))
            (List.cons_ne_nil _ _)
          have hr := chainTree_sound hAr op _ _ _ h2 (fun q hq => hcs q (by simp [hq])) hne2
          rw [combTE_eval hAr, hl, hr, ← fold1_append (BinOp.sem_assoc env.char2 op) 0
            (by simp) (by simpa using hne2), ← List.map_append, hLR]

theorem columnsW_spec {α : Type} [Inhabited α] (n : ℕ) :
    ∀ (bss : List (List α)), (∀ bs ∈ bss, bs.length = n) →
      (columnsW n bss).length = n ∧ ∀ i < n,
        (columnsW n bss).getD i default = bss.map fun bs => bs.getD i default
  | [], _ => ⟨by simp [columnsW], fun i hi => by
      simp [columnsW, List.getD_eq_getElem?_getD, hi]⟩
  | bs :: bss, h => by
    obtain ⟨hl, hv⟩ := columnsW_spec n bss fun b hb => h b (by simp [hb])
    have hbs := h bs (by simp)
    refine ⟨by simp [columnsW, hl, hbs], fun i hi => ?_⟩
    simp only [columnsW]
    rw [getD_zipWith' _ (by omega) (by omega), hv i hi, List.map_cons]

/-- **A chain root's expansion** (`chainE`) carries its meaning. -/
theorem chainStep_sound (hAr : env.ArithOk (I (ir.circField c)).decode)
    (hE : ir.EmitTableOk env E) {kid : ℕ → ℕ → Except TReason (List TE × Cuts)} {k : ℕ}
    {r : List TE × Cuts}
    (hkid : KidSpec (ir := ir) (c := c) (env := env) (E := E) (rd := rd) (V := V) kid k)
    {op : BinOp} {a b : ℕ} (hk : (E.get k).node = .bin op a b)
    (h : ir.nodeStep c env E kid k = .ok r) (hcs : CutsHold (ir := ir) (c := c) (V := V) r.2) :
    NodeOk (ir := ir) (c := c) (env := env) (E := E) (rd := rd) (V := V) k r.1 := by
  unfold nodeStep at h
  simp only [hk] at h
  unfold chainE at h
  simp only [except_bind_eq_ok] at h
  obtain ⟨rs, hrs, h⟩ := h
  have hF := except_mapM_forall₂ hrs
  have hsem₀ : ∀ j, ir.nodeSem env E rd (ir.circuit c).domain k j =
      fold1 (op.sem env.char2) 0 ((leavesOf E op k a ++ leavesOf E op k b).map
        fun l => ir.nodeSem env E rd (ir.circuit c).domain l j) := fun j => by
    rw [nodeSem_bin hAr.hom hE rd hk j, leavesOf_sem hAr.hom hE op j k a,
      leavesOf_sem hAr.hom hE op j k b, List.map_append,
      fold1_append (BinOp.sem_assoc env.char2 op) 0 (by simpa using leavesOf_ne_nil op k a)
        (by simpa using leavesOf_ne_nil op k b)]
  split at h
  · -- two leaves: one combine per coordinate
    rename_i r₁ r₂
    simp only [except_bind_eq_ok, chk_eq_ok, Except.ok.injEq] at h
    obtain ⟨_, -, rfl⟩ := h
    generalize hls : leavesOf E op k a ++ leavesOf E op k b = ls at hF
    obtain ⟨l₁, l₂, rfl, hk1, hk2⟩ : ∃ l₁ l₂, ls = [l₁, l₂] ∧ kid l₁ (E.get k).len = .ok r₁ ∧
        kid l₂ (E.get k).len = .ok r₂ := by
      cases hF with
      | cons h1 hF' =>
        cases hF' with
        | cons h2 hF'' =>
          cases hF''
          exact ⟨_, _, rfl, h1, h2⟩
    have hc1 : CutsHold (ir := ir) (c := c) (V := V) r₁.2 :=
      cutsHold_flatten.1 hcs _ (by simp)
    have hc2 : CutsHold (ir := ir) (c := c) (V := V) r₂.2 :=
      cutsHold_flatten.1 hcs _ (by simp)
    obtain ⟨-, -, hl1, hv1⟩ := hkid _ _ _ hk1 hc1
    obtain ⟨-, -, hl2, hv2⟩ := hkid _ _ _ hk2 hc2
    intro j hj
    rw [getD_zipWith' _ (by omega) (by omega), combTE_eval hAr, hv1 j hj, hv2 j hj, hsem₀ j, hls]
    simp [fold1]
  -- the leaves' cuts are a suffix of the node's in both forms
  have hkax : CutsHold (ir := ir) (c := c) (V := V) (rs.map Prod.snd).flatten →
      ∀ j < (E.get k).len, ((columnsW (E.get k).len (rs.map Prod.fst)).getD j default).map
        (TE.eval (I (ir.circField c)).decode V) =
        (leavesOf E op k a ++ leavesOf E op k b).map
          (fun l => ir.nodeSem env E rd (ir.circuit c).domain l j) ∧
        (columnsW (E.get k).len (rs.map Prod.fst)).length = (E.get k).len := fun hk' j hj => by
    have hcs' : ∀ q ∈ rs, CutsHold (ir := ir) (c := c) (V := V) q.2 := fun q hq =>
      cutsHold_flatten.1 hk' _ (List.mem_map_of_mem hq)
    have hF2 := forall₂_and_right hF hcs'
    have hlen : ∀ ts ∈ rs.map Prod.fst, ts.length = (E.get k).len := fun ts hts => by
      obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hts
      obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hq
      have hl := hF.length_eq
      have := (forall₂_getD' (dx := 0) (dy := default) hF2).2 i (by omega)
      rw [List.getD_eq_getElem _ _ hi] at this
      exact (hkid _ _ _ this.1 this.2).2.2.1
    obtain ⟨hcl, hcv⟩ := columnsW_spec (E.get k).len _ hlen
    refine ⟨?_, hcl⟩
    rw [hcv j hj, List.map_map, List.map_map]
    exact (OpList.map_eq_map_of_forall₂ (fun l => ir.nodeSem env E rd (ir.circuit c).domain l j)
      ((TE.eval (I (ir.circField c)).decode V ∘ fun bs => bs.getD j default) ∘ Prod.fst)
      (fun l q hlq => ((hkid _ _ _ hlq.1 hlq.2).2.2.2 j hj).symm) hF2).symm
  have hsem : ∀ j, ir.nodeSem env E rd (ir.circuit c).domain k j =
      fold1 (op.sem env.char2) 0 ((leavesOf E op k a ++ leavesOf E op k b).map
        fun l => ir.nodeSem env E rd (ir.circuit c).domain l j) := fun j => by
    rw [nodeSem_bin hAr.hom hE rd hk j, leavesOf_sem hAr.hom hE op j k a,
      leavesOf_sem hAr.hom hE op j k b, List.map_append,
      fold1_append (BinOp.sem_assoc env.char2 op) 0 (by simpa using leavesOf_ne_nil op k a)
        (by simpa using leavesOf_ne_nil op k b)]
  have hsplit : ∀ {sm : Bool}, (sm = true → (op.sem env.char2 : (I (ir.circField c)).K → _ → _) =
      (· + ·)) →
      (cond sm (do
        chk (E.get k).aux.isEmpty .length
        .ok ((columnsW (E.get k).len (rs.map Prod.fst)).map TE.sumL, (rs.map Prod.snd).flatten))
      (do
        chk (Nat.blt 1 (leavesOf E op k a ++ leavesOf E op k b).length &&
          Nat.beq (E.get k).aux.length ((E.get k).len *
            ((leavesOf E op k a ++ leavesOf E op k b).length - 2))) .length
        match (List.zipWith (chainRoot env op) (columnsW (E.get k).len (rs.map Prod.fst))
            (slices ((leavesOf E op k a ++ leavesOf E op k b).length - 2) (E.get k).len
              (E.get k).aux)).mapM id with
        | some l => .ok (l.map Prod.fst, (l.map Prod.snd).flatten ++ (rs.map Prod.snd).flatten)
        | none => .error .chain) : Except TReason (List TE × Cuts)) = .ok r →
      NodeOk (ir := ir) (c := c) (env := env) (E := E) (rd := rd) (V := V) k r.1 := by
    intro sm hg h j hj
    cases sm
    · simp only [Bool.cond_false, except_bind_eq_ok, chk_eq_ok] at h
      obtain ⟨_, -, h⟩ := h
      split at h
      · rename_i l hl
        cases h
        rw [cutsHold_append] at hcs
        obtain ⟨hcol, hcl⟩ := hkax hcs.2 j hj
        have hF2 := forall₂_getD' (dx := default) (dy := default) (option_mapM_forall₂ hl)
        have hcsl := hF2.1
        simp only [List.length_zipWith, length_slices, hcl, Nat.min_self] at hcsl
        have hlj := hF2.2 j (by simp [hcl, length_slices]; omega)
        rw [getD_zipWith' _ (by omega) (by simp [length_slices]; omega)] at hlj
        have hcj : CutsHold (ir := ir) (c := c) (V := V) (l.getD j default).2 :=
          cutsHold_flatten.1 hcs.1 _ (List.mem_map_of_mem (getD_mem_lt (by omega)))
        have hroot := chainRoot_sound hAr op (t := (l.getD j default).1)
          (cs := (l.getD j default).2) hlj hcj
        rw [getD_map_lt' _ (by omega), hroot, hcol, hsem j]
      · cases h
    · simp only [Bool.cond_true, except_bind_eq_ok, chk_eq_ok, Except.ok.injEq] at h
      obtain ⟨_, -, rfl⟩ := h
      obtain ⟨hcol, hcl⟩ := hkax hcs j hj
      rw [getD_map_lt' _ (by omega), sumL_eval hAr.hom.zero, hcol, hsem j, hg rfl, fold1_add]
  rcases op with _ | _ | _ | _ | _
  · exact hsplit (fun _ => rfl) h
  · exact hsplit (fun h => by simp at h) h
  · exact hsplit (fun h => by simp at h) h
  · exact hsplit (fun h => by simp at h) h
  · exact hsplit (fun hc => by
      funext x y
      simp [BinOp.sem, hc]) h

/-! ### Products, trees and comparisons -/

theorem keepT_sound {b : Bool} {e : TE} {aux : List Wire} {t : TE} {aux' : List Wire} {cs : Cuts}
    (h : keepT b e aux = some (t, aux', cs)) (hcs : CutsHold (ir := ir) (c := c) (V := V) cs) :
    t.eval (I (ir.circField c)).decode V = e.eval (I (ir.circField c)).decode V := by
  cases b
  · simp only [keepT, Bool.cond_false, Option.some.injEq, Prod.mk.injEq] at h
    rw [h.1]
  · cases aux with
    | nil => simp [keepT] at h
    | cons w aux =>
      simp only [keepT, Bool.cond_true, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, -, rfl⟩ := h
      have := hcs (w, e) (by simp)
      simpa [teW_eval] using this

theorem prodLevel_sound :
    ∀ (l : List TE) (aux : List Wire) {l' : List TE} {aux' : List Wire} {cs : Cuts},
      prodLevel l aux = some (l', aux', cs) → CutsHold (ir := ir) (c := c) (V := V) cs →
      (l'.map (TE.eval (I (ir.circField c)).decode V)).prod =
        (l.map (TE.eval (I (ir.circField c)).decode V)).prod
  | [], aux, l', aux', cs, h, _ => by
    simp only [prodLevel, Option.some.injEq, Prod.mk.injEq] at h
    rw [← h.1]
  | [x], aux, l', aux', cs, h, _ => by
    simp only [prodLevel, Option.some.injEq, Prod.mk.injEq] at h
    rw [← h.1]
  | _ :: _ :: _, [], _, _, _, h, _ => by simp [prodLevel] at h
  | x :: y :: rest, w :: aux, l', aux', cs, h, hcs => by
    simp only [prodLevel] at h
    cases h1 : prodLevel rest aux with
    | none => simp [h1] at h
    | some q =>
      obtain ⟨l1, aux1, c1⟩ := q
      simp only [h1, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, -, rfl⟩ := h
      have hw := hcs (w, .mul x y) (by simp)
      have ih := prodLevel_sound rest aux h1 fun q hq => hcs q (by simp [hq])
      simp only at hw
      simp only [List.map_cons, List.prod_cons, teW_eval, hw, TE.eval, ih]
      ring

theorem prodTree_sound (hAr : env.ArithOk (I (ir.circField c)).decode) :
    ∀ (f : ℕ) (l : List TE) (aux : List Wire) {r : TE} {aux' : List Wire} {cs : Cuts},
      prodTree f l aux = some (r, aux', cs) → CutsHold (ir := ir) (c := c) (V := V) cs →
      r.eval (I (ir.circField c)).decode V = (l.map (TE.eval (I (ir.circField c)).decode V)).prod
  | f, [], aux, r, aux', cs, h, _ => by
    cases f <;> simp only [prodTree, Option.some.injEq, Prod.mk.injEq] at h <;>
      obtain ⟨rfl, -, -⟩ := h <;> simp [TE.eval, hAr.hom.one]
  | f, [x], aux, r, aux', cs, h, _ => by
    cases f <;> simp only [prodTree, Option.some.injEq, Prod.mk.injEq] at h <;>
      obtain ⟨rfl, -, -⟩ := h <;> simp
  | f, [x, y], aux, r, aux', cs, h, _ => by
    cases f <;> simp only [prodTree, Option.some.injEq, Prod.mk.injEq] at h <;>
      obtain ⟨rfl, -, -⟩ := h <;> simp [TE.eval]
  | 0, _ :: _ :: _ :: _, _, _, _, _, h, _ => by simp [prodTree] at h
  | f + 1, x :: y :: z :: l, aux, r, aux', cs, h, hcs => by
    simp only [prodTree] at h
    cases h1 : prodLevel (x :: y :: z :: l) aux with
    | none => simp [h1] at h
    | some q =>
      obtain ⟨l1, aux1, c1⟩ := q
      cases h2 : prodTree f l1 aux1 with
      | none => simp [h1, h2] at h
      | some q2 =>
        obtain ⟨r2, aux2, c2⟩ := q2
        simp only [h1, h2, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, -, rfl⟩ := h
        rw [cutsHold_append] at hcs
        rw [prodTree_sound hAr f l1 aux1 h2 hcs.2, prodLevel_sound _ _ h1 hcs.1]

theorem balTree_sound {comb : TE → TE → TE} {unit : TE} {a : ℕ → TE}
    {g : (I (ir.circField c)).K → (I (ir.circField c)).K → (I (ir.circField c)).K}
    (hc : ∀ x y, (comb x y).eval (I (ir.circField c)).decode V =
      g (x.eval (I (ir.circField c)).decode V) (y.eval (I (ir.circField c)).decode V))
    {T : ℕ → ℕ → (I (ir.circField c)).K}
    (h0 : ∀ i0, T 0 i0 = unit.eval (I (ir.circField c)).decode V)
    (h1 : ∀ i0, T 1 i0 = (a i0).eval (I (ir.circField c)).decode V)
    (h2 : ∀ n i0, T (n + 2) i0 =
      g (T ((n + 2) / 2) i0) (T (n + 2 - (n + 2) / 2) (i0 + (n + 2) / 2))) :
    ∀ (f n i0 : ℕ) (root : Bool) (aux : List Wire) {r : TE} {aux' : List Wire} {cs : Cuts},
      balTree comb unit a f n i0 root aux = some (r, aux', cs) →
      CutsHold (ir := ir) (c := c) (V := V) cs → r.eval (I (ir.circField c)).decode V = T n i0
  | 0, _, _, _, _, _, _, _, h, _ => by simp [balTree] at h
  | _ + 1, 0, i0, _, _, r, _, _, h, _ => by
    simp only [balTree, Option.some.injEq, Prod.mk.injEq] at h
    rw [← h.1, h0]
  | _ + 1, 1, i0, _, _, r, _, _, h, _ => by
    simp only [balTree, Option.some.injEq, Prod.mk.injEq] at h
    rw [← h.1, h1]
  | f + 1, n + 2, i0, root, aux, r, aux', cs, h, hcs => by
    simp only [balTree] at h
    cases hl : balTree comb unit a f (n / 2 + 1) i0 false aux with
    | none => simp [hl] at h
    | some ql =>
      obtain ⟨lo, aux1, c1⟩ := ql
      cases hh : balTree comb unit a f (n + 1 - n / 2) (i0 + (n / 2 + 1)) false aux1 with
      | none => simp [hl, hh] at h
      | some qh =>
        obtain ⟨hi, aux2, c2⟩ := qh
        cases hk : keepT (!root) (comb lo hi) aux2 with
        | none => simp [hl, hh, hk] at h
        | some qk =>
          obtain ⟨r3, aux3, c3⟩ := qk
          simp [hl, hh, hk] at h
          obtain ⟨rfl, -, rfl⟩ := h
          simp only [cutsHold_append] at hcs
          have e1 : (n + 2) / 2 = n / 2 + 1 := by omega
          have e2 : n + 2 - (n + 2) / 2 = n + 1 - n / 2 := by omega
          rw [keepT_sound hk hcs.2.2, hc, balTree_sound hc h0 h1 h2 f _ _ _ _ hl hcs.1,
            balTree_sound hc h0 h1 h2 f _ _ _ _ hh hcs.2.1, h2, e2, e1]

theorem lxorT_eval (hAr : env.ArithOk (I (ir.circField c)).decode) (x y : TE) :
    (lxorT env x y).eval (I (ir.circField c)).decode V =
      Ops.lxor (x.eval (I (ir.circField c)).decode V) (y.eval (I (ir.circField c)).decode V) := by
  rw [lxorT, combTE_eval hAr, Ops.lxor]
  cases h2 : env.char2
  · simp [BinOp.sem]
  · have h11 := hAr.char2 h2
    simp only [BinOp.sem, Bool.cond_true]
    have : (2 : (I (ir.circField c)).K) = 0 := by rw [← h11]; norm_num
    rw [this]
    ring

theorem eqTree_sound (hAr : env.ArithOk (I (ir.circField c)).decode) {a b : ℕ → TE} :
    ∀ (f n i0 : ℕ) (root : Bool) (aux : List Wire) {r : TE} {aux' : List Wire} {cs : Cuts},
      eqTree env a b f n i0 root aux = some (r, aux', cs) →
      CutsHold (ir := ir) (c := c) (V := V) cs →
      r.eval (I (ir.circField c)).decode V =
        Ops.eqReduce (fun t => (a t).eval (I (ir.circField c)).decode V)
          (fun t => (b t).eval (I (ir.circField c)).decode V) n i0
  | 0, _, _, _, _, _, _, _, h, _ => by simp [eqTree] at h
  | _ + 1, 0, i0, _, _, r, _, _, h, _ => by
    simp only [eqTree, Option.some.injEq, Prod.mk.injEq] at h
    rw [← h.1, Ops.eqReduce.eq_1]
    simp [TE.eval, hAr.hom.one]
  | _ + 1, 1, i0, root, aux, r, aux', cs, h, hcs => by
    simp only [eqTree] at h
    rw [keepT_sound h hcs, Ops.eqReduce.eq_2, lnotT_eval hAr, lxorT_eval hAr]
  | f + 1, n + 2, i0, root, aux, r, aux', cs, h, hcs => by
    simp only [eqTree] at h
    cases hl : eqTree env a b f (n / 2 + 1) i0 false aux with
    | none => simp [hl] at h
    | some ql =>
      obtain ⟨lo, aux1, c1⟩ := ql
      cases hh : eqTree env a b f (n + 1 - n / 2) (i0 + (n / 2 + 1)) false aux1 with
      | none => simp [hl, hh] at h
      | some qh =>
        obtain ⟨hi, aux2, c2⟩ := qh
        cases hk : keepT (!root) (.mul lo hi) aux2 with
        | none => simp [hl, hh, hk] at h
        | some qk =>
          obtain ⟨r3, aux3, c3⟩ := qk
          simp [hl, hh, hk] at h
          obtain ⟨rfl, -, rfl⟩ := h
          simp only [cutsHold_append] at hcs
          have e1 : (n + 2) / 2 = n / 2 + 1 := by omega
          have e2 : n + 2 - (n + 2) / 2 = n + 1 - n / 2 := by omega
          rw [keepT_sound hk hcs.2.2, TE.eval, eqTree_sound hAr f _ _ _ _ hl hcs.1,
            eqTree_sound hAr f _ _ _ _ hh hcs.2.1, Ops.eqReduce.eq_3, e2, e1]

theorem ltTree_sound (hAr : env.ArithOk (I (ir.circField c)).decode) {a b : ℕ → TE} :
    ∀ (f n i0 : ℕ) (root lower : Bool) (aux : List Wire) {r : TE × TE} {aux' : List Wire}
      {cs : Cuts}, ltTree env a b f n i0 root lower aux = some (r, aux', cs) →
      CutsHold (ir := ir) (c := c) (V := V) cs →
      (r.1.eval (I (ir.circField c)).decode V, r.2.eval (I (ir.circField c)).decode V) =
        Ops.ltReduce (fun t => (a t).eval (I (ir.circField c)).decode V)
          (fun t => (b t).eval (I (ir.circField c)).decode V) n i0
  | 0, _, _, _, _, _, _, _, _, h, _ => by simp [ltTree] at h
  | _ + 1, 0, i0, _, _, _, r, _, _, h, _ => by
    simp only [ltTree, Option.some.injEq, Prod.mk.injEq] at h
    rw [← h.1, Ops.ltReduce.eq_1]
    simp [TE.eval, hAr.hom.one, hAr.hom.zero]
  | _ + 1, 1, i0, root, lower, aux, r, aux', cs, h, hcs => by
    simp only [ltTree] at h
    cases h1 : keepT (!root) (lnotT env (lxorT env (a i0) (b i0))) aux with
    | none => simp [h1] at h
    | some q1 =>
      obtain ⟨eq, aux1, c1⟩ := q1
      cases h2 : keepT (!root && lower) (.mul (lnotT env (a i0)) (b i0)) aux1 with
      | none => simp [h1, h2] at h
      | some q2 =>
        obtain ⟨lt, aux2, c2⟩ := q2
        simp only [h1, h2, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, -, rfl⟩ := h
        rw [cutsHold_append] at hcs
        rw [keepT_sound h1 hcs.1, keepT_sound h2 hcs.2, Ops.ltReduce.eq_2, lnotT_eval hAr,
          lxorT_eval hAr, TE.eval, lnotT_eval hAr]
  | f + 1, n + 2, i0, root, lower, aux, r, aux', cs, h, hcs => by
    simp only [ltTree] at h
    cases hl : ltTree env a b f (n / 2 + 1) i0 false true aux with
    | none => simp [hl] at h
    | some ql =>
      obtain ⟨lo, aux1, c1⟩ := ql
      cases hh : ltTree env a b f (n + 1 - n / 2) (i0 + (n / 2 + 1)) false false aux1 with
      | none => simp [hl, hh] at h
      | some qh =>
        obtain ⟨hi, aux2, c2⟩ := qh
        cases h3 : keepT (!root) (.mul hi.1 lo.1) aux2 with
        | none => simp [hl, hh, h3] at h
        | some q3 =>
          obtain ⟨eq, aux3, c3⟩ := q3
          cases h4 : keepT (!root && lower) (.add hi.2 (.mul hi.1 lo.2)) aux3 with
          | none => simp [hl, hh, h3, h4] at h
          | some q4 =>
            obtain ⟨lt, aux4, c4⟩ := q4
            simp [hl, hh, h3, h4] at h
            obtain ⟨rfl, -, rfl⟩ := h
            simp only [cutsHold_append] at hcs
            have elo := ltTree_sound hAr f _ _ _ _ _ hl hcs.1
            have ehi := ltTree_sound hAr f _ _ _ _ _ hh hcs.2.1
            have e1 : (n + 2) / 2 = n / 2 + 1 := by omega
            have e2 : n + 2 - (n + 2) / 2 = n + 1 - n / 2 := by omega
            rw [keepT_sound h3 hcs.2.2.1, keepT_sound h4 hcs.2.2.2, Ops.ltReduce.eq_3, e2, e1,
              ← elo, ← ehi]
            simp only [TE.eval]

/-- **The polynomial of a comparison** of words `a`, `b` of `w` bits (`Ops.ltWord`,
`Ops.leqWord`, `Ops.eqWord`). -/
def cmpWord {R : Type*} [CommRing R] : CmpOp → ℕ → (ℕ → R) → (ℕ → R) → R
  | .lt, w, a, b => Ops.ltWord w a b
  | .leq, w, a, b => Ops.leqWord w a b
  | .eq, w, a, b => Ops.eqWord w a b

theorem logicEval_cmp {R : Type*} [CommRing R] (op : CmpOp) (w : ℕ) (x y : ℕ → R) (j : ℕ) :
    op.logic.eval w [x, y] j = cmpWord op w (fun t => x (j * w + t)) (fun t => y (j * w + t)) := by
  cases op <;> rfl

theorem cmpWord_congr {R : Type*} [CommRing R] (op : CmpOp) (w : ℕ) {a b a' b' : ℕ → R}
    (ha : ∀ t < w, a t = a' t) (hb : ∀ t < w, b t = b' t) :
    cmpWord op w a b = cmpWord op w a' b' := by
  have ha' : ∀ t < w, a (0 + t) = a' (0 + t) := fun t ht => by simpa using ha t ht
  have hb' : ∀ t < w, b (0 + t) = b' (0 + t) := fun t ht => by simpa using hb t ht
  cases op
  · simp only [cmpWord, Ops.ltWord, Ops.ltReduce_congr w 0 ha' hb']
  · simp only [cmpWord, Ops.leqWord, Ops.ltWord, Ops.ltReduce_congr w 0 hb' ha']
  · simp only [cmpWord, Ops.eqWord, Ops.eqReduce_congr w 0 ha' hb']

theorem cmpTree_sound (hAr : env.ArithOk (I (ir.circField c)).decode) {op : CmpOp} {w : ℕ}
    {a b : ℕ → TE} {aux : List Wire} {r : TE} {aux' : List Wire} {cs : Cuts}
    (h : cmpTree env op w a b aux = some (r, aux', cs))
    (hcs : CutsHold (ir := ir) (c := c) (V := V) cs) :
    r.eval (I (ir.circField c)).decode V =
      cmpWord op w (fun t => (a t).eval (I (ir.circField c)).decode V)
        (fun t => (b t).eval (I (ir.circField c)).decode V) := by
  cases op
  · simp only [cmpTree, Option.map_eq_some_iff] at h
    obtain ⟨q, hq, hqe⟩ := h
    simp only [Prod.mk.injEq] at hqe
    obtain ⟨rfl, -, rfl⟩ := hqe
    have := ltTree_sound hAr _ _ _ _ _ _ hq hcs
    simp only [cmpWord, Ops.ltWord, ← this]
  · simp only [cmpTree, Option.map_eq_some_iff] at h
    obtain ⟨q, hq, hqe⟩ := h
    simp only [Prod.mk.injEq] at hqe
    obtain ⟨rfl, -, rfl⟩ := hqe
    have := ltTree_sound hAr _ _ _ _ _ _ hq hcs
    simp only [cmpWord, Ops.leqWord, Ops.ltWord, ← this, lnotT_eval hAr]
  · simp only [cmpTree] at h
    rw [eqTree_sound hAr _ _ _ _ _ h hcs]
    rfl

theorem auxCoords_sound {f : ℕ → List Wire → Option (TE × List Wire × Cuts)} :
    ∀ (js : List ℕ) (aux : List Wire) {ts : List TE} {aux' : List Wire} {cs : Cuts},
      auxCoords f js aux = some (ts, aux', cs) → CutsHold (ir := ir) (c := c) (V := V) cs →
      ts.length = js.length ∧ ∀ i < js.length, ∃ a0 a1 c0, f (js.getD i 0) a0 =
        some (ts.getD i default, a1, c0) ∧ CutsHold (ir := ir) (c := c) (V := V) c0
  | [], aux, ts, aux', cs, h, _ => by
    simp only [auxCoords, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -, -⟩ := h
    exact ⟨rfl, fun i hi => absurd hi (Nat.not_lt_zero _)⟩
  | j :: js, aux, ts, aux', cs, h, hcs => by
    simp only [auxCoords] at h
    cases h1 : f j aux with
    | none => simp [h1] at h
    | some q =>
      obtain ⟨t, aux1, c1⟩ := q
      cases h2 : auxCoords f js aux1 with
      | none => simp [h1, h2] at h
      | some q2 =>
        obtain ⟨ts', aux2, c2⟩ := q2
        simp only [h1, h2, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, -, rfl⟩ := h
        rw [cutsHold_append] at hcs
        obtain ⟨hl, hv⟩ := auxCoords_sound js aux1 h2 hcs.2
        refine ⟨by simp [hl], fun i hi => ?_⟩
        cases i with
        | zero => exact ⟨aux, aux1, c1, by simpa using h1, hcs.1⟩
        | succ i => simpa using hv i (by simpa using hi)

theorem auxAll_sound {f : ℕ → List Wire → Option (TE × List Wire × Cuts)} {n : ℕ}
    {aux : List Wire} {r : List TE × Cuts} (h : auxAll f n aux = .ok r)
    (hcs : CutsHold (ir := ir) (c := c) (V := V) r.2) :
    r.1.length = n ∧ ∀ j < n, ∃ a0 a1 c0, f j a0 = some (r.1.getD j default, a1, c0) ∧
      CutsHold (ir := ir) (c := c) (V := V) c0 := by
  unfold auxAll at h
  split at h
  · rename_i ts cs hq
    cases h
    obtain ⟨hl, hv⟩ := auxCoords_sound _ _ hq hcs
    refine ⟨by simpa using hl, fun j hj => ?_⟩
    have := hv j (by simpa using hj)
    rwa [getD_range_lt' hj] at this
  · cases h

section Steps2

variable {kid : ℕ → ℕ → Except TReason (List TE × Cuts)} {k : ℕ} {r : List TE × Cuts}

/-- The tree expression of word `j`'s bit `t` of a kid read at `n · w` coordinates. -/
theorem wordBit_eval {xs : List TE} {n w j t : ℕ} {f : ℕ → (I (ir.circField c)).K}
    (hl : xs.length = n * w)
    (hv : ∀ i < n * w, (xs.getD i default).eval (I (ir.circField c)).decode V = f i)
    (hj : j < n) (ht : t < w) :
    ((PTree.ofList xs).get (j * w + t)).eval (I (ir.circField c)).decode V = f (j * w + t) := by
  have hlt : j * w + t < n * w := by
    have : (j + 1) * w ≤ n * w := Nat.mul_le_mul_right _ hj
    rw [add_mul, one_mul] at this
    omega
  rw [PTree.get_ofList _ (by omega), hv _ hlt]

theorem prodStep_sound (hAr : env.ArithOk (I (ir.circField c)).decode)
    (hE : ir.EmitTableOk env E)
    (hkid : KidSpec (ir := ir) (c := c) (env := env) (E := E) (rd := rd) (V := V) kid k)
    {w a : ℕ} (hk : (E.get k).node = .prod w a) (h : ir.nodeStep c env E kid k = .ok r)
    (hcs : CutsHold (ir := ir) (c := c) (V := V) r.2) :
    NodeOk (ir := ir) (c := c) (env := env) (E := E) (rd := rd) (V := V) k r.1 := by
  unfold nodeStep at h
  simp only [hk, except_bind_eq_ok, Except.ok.injEq] at h
  obtain ⟨r', hr', q, hq, rfl⟩ := h
  dsimp only at hcs
  rw [cutsHold_append] at hcs
  obtain ⟨-, -, hxl, hxv⟩ := hkid a _ r' hr' hcs.2
  obtain ⟨-, hqv⟩ := auxAll_sound hq hcs.1
  refine nodeOk_of_row hE fun j hj => ?_
  obtain ⟨a0, a1, c0, hp, hc0⟩ := hqv j hj
  rw [prodTree_sound hAr _ _ _ hp hc0, hk, List.map_map]
  simp only [ENode.row, Expr.eval]
  congr 1
  refine List.map_congr_left fun t ht => ?_
  rw [List.mem_range] at ht
  exact (wordBit_eval hxl hxv hj ht).symm

theorem treeStep_sound (hAr : env.ArithOk (I (ir.circField c)).decode)
    (hE : ir.EmitTableOk env E)
    (hkid : KidSpec (ir := ir) (c := c) (env := env) (E := E) (rd := rd) (V := V) kid k)
    {any : Bool} {w a : ℕ} (hk : (E.get k).node = .tree any w a)
    (h : ir.nodeStep c env E kid k = .ok r) (hcs : CutsHold (ir := ir) (c := c) (V := V) r.2) :
    NodeOk (ir := ir) (c := c) (env := env) (E := E) (rd := rd) (V := V) k r.1 := by
  unfold nodeStep at h
  simp only [hk, except_bind_eq_ok, Except.ok.injEq] at h
  obtain ⟨r', hr', q, hq, rfl⟩ := h
  dsimp only at hcs
  rw [cutsHold_append] at hcs
  obtain ⟨-, -, hxl, hxv⟩ := hkid a _ r' hr' hcs.2
  obtain ⟨-, hqv⟩ := auxAll_sound hq hcs.1
  refine nodeOk_of_row hE fun j hj => ?_
  obtain ⟨a0, a1, c0, hp, hc0⟩ := hqv j hj
  have hA := hAr.hom
  rw [hk]
  cases any
  · have := balTree_sound (g := (· * ·)) (fun x y => rfl)
      (T := Ops.andTree fun t => ((PTree.ofList r'.1).get (j * w + t)).eval
        (I (ir.circField c)).decode V)
      (fun i0 => by simp [Ops.andTree.eq_1, TE.eval, hA.one])
      (fun i0 => by simp [Ops.andTree.eq_2]) (fun n i0 => by rw [Ops.andTree.eq_3])
      _ _ _ _ _ hp hc0
    rw [this]
    simp only [ENode.row, Bool.cond_false, Expr.eval, Expr.evalList, LogicOp.eval,
      List.headD_cons]
    exact Ops.andTree_congr w 0 fun t ht => by
      simp only [Nat.zero_add]
      exact (wordBit_eval hxl hxv hj ht).symm
  · have := balTree_sound (g := Ops.lor) (fun x y => by
        simp only [Bool.cond_true, lorT, lnotT_eval hAr, TE.eval, Ops.lor])
      (T := Ops.orTree fun t => ((PTree.ofList r'.1).get (j * w + t)).eval
        (I (ir.circField c)).decode V)
      (fun i0 => by simp [Ops.orTree.eq_1, TE.eval, hA.zero])
      (fun i0 => by simp [Ops.orTree.eq_2]) (fun n i0 => by rw [Ops.orTree.eq_3])
      _ _ _ _ _ hp hc0
    rw [this]
    simp only [ENode.row, Bool.cond_true, Expr.eval, Expr.evalList, LogicOp.eval, List.headD_cons]
    exact Ops.orTree_congr w 0 fun t ht => by
      simp only [Nat.zero_add]
      exact (wordBit_eval hxl hxv hj ht).symm

theorem cmpStep_sound (hAr : env.ArithOk (I (ir.circField c)).decode)
    (hE : ir.EmitTableOk env E)
    (hK : ∀ v es, (ir.value v).kind = .constant es → ∀ i,
      rd v i = (I (ir.valueField v)).decode (es.getD i 0))
    (hkid : KidSpec (ir := ir) (c := c) (env := env) (E := E) (rd := rd) (V := V) kid k)
    {op : CmpOp} {w a : ℕ} {b : CmpArg} (hk : (E.get k).node = .cmp op w a b)
    (h : ir.nodeStep c env E kid k = .ok r) (hcs : CutsHold (ir := ir) (c := c) (V := V) r.2) :
    NodeOk (ir := ir) (c := c) (env := env) (E := E) (rd := rd) (V := V) k r.1 := by
  unfold nodeStep at h
  simp only [hk, except_bind_eq_ok, Except.ok.injEq] at h
  obtain ⟨r', hr', rb, hrb, q, hq, rfl⟩ := h
  dsimp only at hcs
  simp only [cutsHold_append] at hcs
  obtain ⟨⟨hcq, hcr⟩, hcb⟩ := hcs
  obtain ⟨-, -, hxl, hxv⟩ := hkid a _ r' hr' hcr
  obtain ⟨-, hqv⟩ := auxAll_sound hq hcq
  -- the second operand's bits and their values
  obtain ⟨B, hbl, hbv, hrow⟩ : ∃ B : ℕ → (I (ir.circField c)).K,
      rb.1.length = (E.get k).len * w ∧
      (∀ i < (E.get k).len * w, (rb.1.getD i default).eval (I (ir.circField c)).decode V = B i) ∧
      ∀ j, Expr.eval ir (ir.circField c) rd (fun a => ir.nodeSem env E rd (ir.circuit c).domain a)
          (fun a => (E.get a).len) ((E.get k).node.row env) j =
        cmpWord op w (fun t => ir.nodeSem env E rd (ir.circuit c).domain a (j * w + t))
          (fun t => B (j * w + t)) := by
    cases b with
    | node b' =>
      obtain ⟨-, -, hbl, hbv⟩ := hkid b' _ rb hrb hcb
      refine ⟨ir.nodeSem env E rd (ir.circuit c).domain b', hbl, hbv, fun j => ?_⟩
      rw [hk]
      simp only [ENode.row, Expr.eval, Expr.evalList]
      exact logicEval_cmp op w _ _ j
    | imm v idx =>
      simp only [except_bind_eq_ok, Except.ok.injEq] at hrb
      obtain ⟨es, hes, rfl⟩ := hrb
      have hes' : constCodes? ir c v = some es := by
        unfold constE at hes
        split at hes
        · cases hes
          assumption
        · cases hes
      refine ⟨fun i => castElt (rd v (idx.entry i)), by simp [length_padTo], fun i hi => ?_,
        fun j => ?_⟩
      · rw [getD_map_lt' _ (by rw [length_padTo]; exact hi)]
        simp only [show (default : ℕ) = 0 from rfl, getD_padTo _ hi,
          ← IndexMap.entry_eq_getD_toList, TE.eval]
        exact (constCodes?_read hK rfl hes' _).symm
      · rw [hk]
        simp only [ENode.row, Expr.eval, Expr.evalList]
        exact logicEval_cmp op w _ _ j
  refine nodeOk_of_row hE fun j hj => ?_
  obtain ⟨a0, a1, c0, hp, hc0⟩ := hqv j hj
  rw [cmpTree_sound hAr hp hc0, hrow j]
  exact cmpWord_congr op w (fun t ht => (wordBit_eval hxl hxv hj ht).symm)
    (fun t ht => (wordBit_eval hbl hbv hj ht).symm)

end Steps2

/-! ### Staged transforms -/

theorem staged?_eq {op : EOp} {q : ℕ × ℕ × NttOrder × ℕ} (h : staged? op = some q) :
    ∃ nop mask, op = .staged nop mask ∧ stagedCore? nop = some q := by
  unfold staged? at h
  split at h
  · exact ⟨_, _, rfl, h⟩
  · cases h

/-- **A staged operator's widths**: its rows and columns are its block width `w`, a positive
multiple of its transform's length. -/
theorem stagedCore?_dims :
    ∀ {op : NamedOp} {n psi : ℕ} {o : NttOrder} {w : ℕ}, stagedCore? op = some (n, psi, o, w) →
      NamedOp.rows ir op = w ∧ NamedOp.cols ir op = w ∧ ∃ c, w = n * c ∧ 0 < c
  | .ntt _ _ _, n, psi, o, w, h => by
    simp only [stagedCore?, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl, rfl⟩ := h
    exact ⟨rfl, rfl, 1, by ring, one_pos⟩
  | .batched (b + 1) op', n, psi, o, w, h => by
    simp only [stagedCore?] at h
    cases h' : stagedCore? op' with
    | none => simp [h'] at h
    | some q =>
      obtain ⟨n', psi', o', w'⟩ := q
      simp only [h', Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl, rfl⟩ := h
      obtain ⟨hr, hc, c, hcw, hc0⟩ := stagedCore?_dims h'
      exact ⟨by simp [NamedOp.rows, hr], by simp [NamedOp.cols, hc], (b + 1) * c,
        by rw [hcw]; ring, by positivity⟩
  | .batched 0 _, _, _, _, _, h | .negacyclicConv _ _, _, _, _, _, h
  | .polyMatVec _ _ _ _, _, _, _, _, h | .polyBroadcast _ _ _, _, _, _, _, h
  | .inverseNtt _ _, _, _, _, _, h | .nttTranspose _ _, _, _, _, _, h
  | .rowDot _ _ _, _, _, _, _, h | .macConv _ _ _ _, _, _, _, _, h
  | .acyclicConv _ _, _, _, _, _, h | .diagonal _, _, _, _, _, h | .scale _, _, _, _, _, h
  | .constDiagonal _, _, _, _, _, h | .sum _, _, _, _, _, h | .fromDigits _ _, _, _, _, _, h => by
    simp [stagedCore?] at h

theorem div_mul_add_mod_div {j n c : ℕ} :
    j / (n * c) * (n * c) + j % (n * c) / n * n = j / n * n := by
  rw [Nat.mod_mul_right_div_self, ← Nat.div_div_eq_div_mul]
  have := Nat.div_add_mod' (j / n) c
  calc j / n / c * (n * c) + j / n % c * n = (j / n / c * c + j / n % c) * n := by ring
    _ = j / n * n := by rw [this]

/-- **A staged operator on one block** is its transform on each block of `n` (`batched` reads its
blocks of `n` in order). -/
theorem stagedCore?_block {f : ℕ} {leaf : ∀ v : ℕ, ℕ → (I (ir.valueField v)).K} :
    ∀ {op : NamedOp} {n psi : ℕ} {o : NttOrder} {w : ℕ}, stagedCore? op = some (n, psi, o, w) →
      ∀ (y : ℕ → (I f).K) {j : ℕ}, j < w →
        NamedOp.block ir f leaf op y j =
          nttBy o n ((I f).decode psi) (fun t => y (j / n * n + t)) (j % n)
  | .ntt n' psi' o', n, psi, o, w, h, y, j, hj => by
    simp only [stagedCore?, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨h1, h2, h3, h4⟩ := h
    subst n' psi' o' w
    rw [Nat.div_eq_of_lt hj, Nat.mod_eq_of_lt hj]
    cases o <;> simp [NamedOp.block, nttBy]
  | .batched (b + 1) op', n, psi, o, w, h, y, j, hj => by
    simp only [stagedCore?] at h
    cases h' : stagedCore? op' with
    | none => simp [h'] at h
    | some q =>
      obtain ⟨n', psi', o', w'⟩ := q
      simp only [h', Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨h1, h2, h3, h4⟩ := h
      subst n' psi' o' w
      obtain ⟨hr, hc, c, hcw, hc0⟩ := stagedCore?_dims (ir := ir) h'
      subst hcw
      have hw0 : 0 < n * c := by
        rcases Nat.eq_zero_or_pos (n * c) with h0 | h0
        · rw [h0, mul_zero] at hj
          omega
        · exact h0
      simp only [NamedOp.block, hr, hc, hj, ↓reduceIte]
      rw [stagedCore?_block h' _ (Nat.mod_lt _ hw0), Nat.mod_mod_of_dvd _ ⟨c, rfl⟩]
      congr 1
      funext t
      rw [← add_assoc, div_mul_add_mod_div]
  | .batched 0 _, _, _, _, _, h, _, _, _ | .negacyclicConv _ _, _, _, _, _, h, _, _, _
  | .polyMatVec _ _ _ _, _, _, _, _, h, _, _, _ | .polyBroadcast _ _ _, _, _, _, _, h, _, _, _
  | .inverseNtt _ _, _, _, _, _, h, _, _, _ | .nttTranspose _ _, _, _, _, _, h, _, _, _
  | .rowDot _ _ _, _, _, _, _, h, _, _, _ | .macConv _ _ _ _, _, _, _, _, h, _, _, _
  | .acyclicConv _ _, _, _, _, _, h, _, _, _ | .diagonal _, _, _, _, _, h, _, _, _
  | .scale _, _, _, _, _, h, _, _, _ | .constDiagonal _, _, _, _, _, h, _, _, _
  | .sum _, _, _, _, _, h, _, _, _ | .fromDigits _ _, _, _, _, _, h, _, _, _ => by
    simp [stagedCore?] at h

/-- **A staged operator along the last axis** is its transform on each block of `n` of the
operand. -/
theorem stagedCore?_apply {f : ℕ} {leaf : ∀ v : ℕ, ℕ → (I (ir.valueField v)).K} {op : NamedOp}
    {n psi : ℕ} {o : NttOrder} {w : ℕ} (h : stagedCore? op = some (n, psi, o, w)) (hn0 : 0 < n)
    (x : ℕ → (I f).K) (j : ℕ) :
    NamedOp.apply ir f leaf op x j =
      nttBy o n ((I f).decode psi) (fun t => x (j / n * n + t)) (j % n) := by
  obtain ⟨hr, hc, c, rfl, hc0⟩ := stagedCore?_dims (ir := ir) h
  unfold NamedOp.apply
  rw [hr, hc, stagedCore?_block h _ (Nat.mod_lt _ (Nat.mul_pos hn0 hc0)),
    Nat.mod_mod_of_dvd _ ⟨c, rfl⟩]
  congr 1
  funext t
  rw [← add_assoc, div_mul_add_mod_div]

theorem powList_getD (hAr : env.ArithOk (I (ir.circField c)).decode) (cc L w : ℕ) {j : ℕ}
    (hj : j < L) : (I (ir.circField c)).decode ((powList env.ar cc L w).getD j default) =
      (I (ir.circField c)).decode w * (I (ir.circField c)).decode cc ^ j := by
  have h := map_powList hAr.hom cc L w
  have hl : (powList env.ar cc L w).length = L := by simpa using congrArg List.length h
  have := congrArg (fun l => l[j]?) h
  simp only [List.getElem?_map, List.getElem?_range hj, Option.map_some] at this
  rw [List.getElem?_eq_getElem (by omega)] at this
  rw [List.getD_eq_getElem _ _ (by omega)]
  simpa using this

theorem bflyT_eval (hAr : env.ArithOk (I (ir.circField c)).decode) {n h : ℕ} {tw : ℕ → ℕ}
    {arr : List TE} {A τ : ℕ → (I (ir.circField c)).K}
    (hdvd : 2 * h ∣ n) (hl : arr.length = n)
    (hA : ∀ q < n, (arr.getD q default).eval (I (ir.circField c)).decode V = A q)
    (hw : ∀ q < n, q % (2 * h) < h → (I (ir.circField c)).decode (tw q) = τ q) :
    (bflyT env n h tw arr).length = n ∧ ∀ p < n,
      ((bflyT env n h tw arr).getD p default).eval (I (ir.circField c)).decode V =
        bflyF h τ A p := by
  refine ⟨by simp [bflyT], fun p hp => ?_⟩
  have hh : 0 < h := by
    rcases Nat.eq_zero_or_pos h with h0 | h0
    · subst h0
      simp at hdvd
      omega
    · exact h0
  have hmod : p % (2 * h) < 2 * h := Nat.mod_lt _ (by omega)
  obtain ⟨q, hq⟩ := hdvd
  -- the block of `p` lies below `n`
  have hblk : p - p % (2 * h) + 2 * h ≤ n := by
    have h1 : p - p % (2 * h) = 2 * h * (p / (2 * h)) := by
      have := Nat.div_add_mod p (2 * h)
      omega
    have h2 : p / (2 * h) < q := by
      rw [hq] at hp
      exact Nat.div_lt_of_lt_mul hp
    rw [h1, hq]
    have : 2 * h * (p / (2 * h)) + 2 * h = 2 * h * (p / (2 * h) + 1) := by ring
    rw [this]
    exact Nat.mul_le_mul_left _ h2
  simp only [bflyT]
  rw [getD_range_map _ hp]
  unfold bflyF
  by_cases hlt : p % (2 * h) < h
  · have hb : Nat.blt (p % (2 * h)) h = true := by simpa using hlt
    simp only [hb, Bool.cond_true, hlt, ↓reduceIte, TE.eval]
    rw [PTree.get_ofList _ (by omega), PTree.get_ofList _ (by omega), hA p hp, hA (p + h) (by omega),
      hw p hp hlt]
  · have hb : Nat.blt (p % (2 * h)) h = false :=
      Bool.eq_false_iff.2 fun h' => hlt (by simpa using h')
    simp only [hb, Bool.cond_false, hlt, ↓reduceIte, TE.eval, hAr.neg1]
    have hlo : (p - h) % (2 * h) < h := by
      rw [mod_two_mul_sub (by omega)]
      omega
    rw [PTree.get_ofList _ (by omega), PTree.get_ofList _ (by omega), hA (p - h) (by omega),
      hA p hp, hw (p - h) (by omega) hlo]
    ring

theorem stagesT_sound (hAr : env.ArithOk (I (ir.circField c)).decode) {n S : ℕ}
    {sched : ℕ → ℕ × (ℕ → ℕ)} {τ : ℕ → ℕ → (I (ir.circField c)).K}
    (hdvd : ∀ s < S, 2 * (sched s).1 ∣ n)
    (hw : ∀ s < S, ∀ q < n, q % (2 * (sched s).1) < (sched s).1 →
      (I (ir.circField c)).decode ((sched s).2 q) = τ s q) :
    ∀ (r s : ℕ) (arr : List TE) (aux : List Wire) {A : ℕ → (I (ir.circField c)).K}
      {out : List TE} {aux' : List Wire} {cs : Cuts}, s + r ≤ S →
      arr.length = n → (∀ q < n, (arr.getD q default).eval (I (ir.circField c)).decode V = A q) →
      stagesT env n sched r s arr aux = some (out, aux', cs) →
      CutsHold (ir := ir) (c := c) (V := V) cs →
      out.length = n ∧ ∀ p < n, (out.getD p default).eval (I (ir.circField c)).decode V =
        stagesF (fun s => ((sched s).1, τ s)) r s A p
  | 0, s, arr, aux, A, out, aux', cs, _, hl, hA, h0, _ => by
    simp only [stagesT, Option.some.injEq, Prod.mk.injEq] at h0
    obtain ⟨rfl, -, -⟩ := h0
    exact ⟨hl, fun p hp => by rw [hA p hp]; rfl⟩
  | r + 1, s, arr, aux, A, out, aux', cs, hS, hl, hA, h0, hcs => by
    obtain ⟨hl', hv'⟩ := bflyT_eval hAr (hdvd s (by omega)) hl hA (hw s (by omega))
    cases r with
    | zero =>
      simp only [stagesT, Option.some.injEq, Prod.mk.injEq] at h0
      obtain ⟨rfl, -, -⟩ := h0
      refine ⟨hl', fun p hp => ?_⟩
      rw [hv' p hp]
      rfl
    | succ r' =>
      simp only [stagesT] at h0
      cases hb : Nat.ble n aux.length
      · simp [hb] at h0
      · simp only [hb, Bool.cond_true] at h0
        have hbl : n ≤ aux.length := by simpa using hb
        cases hrec : stagesT env n sched (r' + 1) (s + 1) ((aux.map teW).take n) (aux.drop n) with
        | none => simp [hrec] at h0
        | some q =>
          obtain ⟨o, a1, c1⟩ := q
          simp [hrec] at h0
          obtain ⟨rfl, -, rfl⟩ := h0
          rw [cutsHold_append] at hcs
          have hA' : ∀ q < n, (((aux.map teW).take n).getD q default).eval
              (I (ir.circField c)).decode V = bflyF (sched s).1 (τ s) A q := fun q hq => by
            have hc := hcs.1 _ (mem_zip_getD (xs := aux.take n)
              (ys := bflyT env n (sched s).1 (sched s).2 arr) (i := q) (by simp; omega) (by omega))
            simp only at hc
            rw [getD_take_lt hq, getD_map_lt' _ (by omega), ← getD_take_lt (n := n) hq, teW_eval,
              hc, hv' q hq]
          obtain ⟨hl2, hv2⟩ := stagesT_sound hAr hdvd hw (r' + 1) (s + 1) _ _ (by omega)
            (by simp; omega) hA' hrec hcs.2
          exact ⟨hl2, fun p hp => by rw [hv2 p hp]; rfl⟩

theorem nttBlockT_sound (hAr : env.ArithOk (I (ir.circField c)).decode) {n L psi : ℕ}
    {o : NttOrder} (hn : 2 ^ L = n) (hψ : (I (ir.circField c)).decode psi ^ n = -1)
    {xs : List TE} (hxl : n ≤ xs.length) {aux : List Wire} {out : List TE} {aux' : List Wire}
    {cs : Cuts} (h : nttBlockT env n L psi o xs aux = some (out, aux', cs))
    (hcs : CutsHold (ir := ir) (c := c) (V := V) cs) :
    out.length = n ∧ ∀ m < n, (out.getD m default).eval (I (ir.circField c)).decode V =
      nttBy o n ((I (ir.circField c)).decode psi)
        (fun t => (xs.getD t default).eval (I (ir.circField c)).decode V) m := by
  have hA := hAr.hom
  set ψ := (I (ir.circField c)).decode psi
  set x : ℕ → (I (ir.circField c)).K := fun t => (xs.getD t default).eval
    (I (ir.circField c)).decode V
  set Tw := PTree.ofList (powList env.ar psi n 1)
  have hpl : (powList env.ar psi n 1).length = n := by
    have := congrArg List.length (map_powList hA psi n 1)
    simpa using this
  have hTw : ∀ e < n, (I (ir.circField c)).decode (Tw.get e) = ψ ^ e := fun e he => by
    rw [PTree.get_ofList _ (by rw [hpl]; exact he), powList_getD hAr _ _ _ he, hA.one, one_mul]
  have hn0 : 0 < n := hn ▸ Nat.two_pow_pos L
  have h0 : ∀ q < n, ((nttInT n L Tw (PTree.ofList xs) o).getD q default).eval
      (I (ir.circField c)).decode V = nttInF L ψ x o q := fun q hq => by
    cases o with
    | scheme =>
      simp only [nttInT, nttInF]
      rw [getD_range_map _ hq, PTree.get_ofList _ (by omega)]
    | natural =>
      have hb : bitRevNat L q < n := hn ▸ bitRevNat_lt L q
      simp only [nttInT, nttInF]
      rw [getD_range_map _ hq]
      simp only [TE.eval]
      rw [hTw _ hb, PTree.get_ofList _ (by omega)]
  have hl0 : (nttInT n L Tw (PTree.ofList xs) o).length = n := by
    cases o <;> simp [nttInT]
  have hdvd : ∀ s < L, 2 * (nttSchedT n L Tw o s).1 ∣ n := fun s hs => by
    rw [← hn]
    cases o with
    | scheme =>
      simp only [nttSchedT, nttHalf]
      rw [← pow_succ']
      exact pow_dvd_pow 2 (by omega)
    | natural =>
      simp only [nttSchedT, nttHalf]
      rw [← pow_succ']
      exact pow_dvd_pow 2 (by omega)
  have hw : ∀ s < L, ∀ q < n, q % (2 * (nttSchedT n L Tw o s).1) < (nttSchedT n L Tw o s).1 →
      (I (ir.circField c)).decode ((nttSchedT n L Tw o s).2 q) = ψ ^ nttTwIdx n L o s q :=
    fun s hs q _ hq => by
    simp only [nttSchedT] at hq ⊢
    refine hTw _ ?_
    cases o with
    | scheme =>
      simp only [nttTwIdx]
      exact hn ▸ bitRevNat_lt L _
    | natural =>
      simp only [nttHalf] at hq
      simp only [nttTwIdx]
      have hd : 2 ^ s ∣ n := hn ▸ pow_dvd_pow 2 (by omega)
      have hpos : 0 < n / 2 ^ s := Nat.div_pos (Nat.le_of_dvd hn0 hd) (Nat.two_pow_pos s)
      calc n / 2 ^ s * (q % (2 * 2 ^ s)) < n / 2 ^ s * 2 ^ s := Nat.mul_lt_mul_of_pos_left hq hpos
        _ = n := Nat.div_mul_cancel hd
  obtain ⟨hl, hv⟩ := stagesT_sound hAr hdvd hw L 0 _ aux (by omega) hl0 h0 h hcs
  refine ⟨hl, fun m hm => ?_⟩
  rw [hv m hm]
  exact nttBy_of_stagesF o hn hψ x hm

theorem nttBlocksT_sound (hAr : env.ArithOk (I (ir.circField c)).decode) {n L psi : ℕ}
    {o : NttOrder} (hn : 2 ^ L = n) (hψ : (I (ir.circField c)).decode psi ^ n = -1) :
    ∀ (k : ℕ) (xs : List TE) (aux : List Wire) {out : List TE} {aux' : List Wire} {cs : Cuts},
      xs.length = k * n → nttBlocksT env n L psi o k xs aux = some (out, aux', cs) →
      CutsHold (ir := ir) (c := c) (V := V) cs →
      out.length = k * n ∧ ∀ j < k * n, (out.getD j default).eval (I (ir.circField c)).decode V =
        nttBy o n ((I (ir.circField c)).decode psi)
          (fun t => (xs.getD (j / n * n + t) default).eval (I (ir.circField c)).decode V) (j % n)
  | 0, xs, aux, out, aux', cs, _, h, _ => by
    simp only [nttBlocksT, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -, -⟩ := h
    exact ⟨by simp, fun j hj => by simp at hj⟩
  | k + 1, xs, aux, out, aux', cs, hl, h, hcs => by
    have hn0 : 0 < n := hn ▸ Nat.two_pow_pos L
    simp only [nttBlocksT] at h
    cases h1 : nttBlockT env n L psi o (xs.take n) aux with
    | none => simp [h1] at h
    | some q =>
      obtain ⟨o', aux1, c1⟩ := q
      cases h2 : nttBlocksT env n L psi o k (xs.drop n) aux1 with
      | none => simp [h1, h2] at h
      | some q2 =>
        obtain ⟨os, aux2, c2⟩ := q2
        simp only [h1, h2, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, -, rfl⟩ := h
        rw [cutsHold_append] at hcs
        obtain ⟨hol, hov⟩ := nttBlockT_sound hAr hn hψ (by simp; rw [hl]; nlinarith) h1 hcs.1
        obtain ⟨hosl, hosv⟩ := nttBlocksT_sound hAr hn hψ k (xs.drop n) aux1
          (by simp [hl]; ring_nf; omega) h2 hcs.2
        refine ⟨by simp [hol, hosl]; ring, fun j hj => ?_⟩
        by_cases hjn : j < n
        · rw [List.getD_append _ _ _ _ (by omega), hov j hjn, Nat.div_eq_of_lt hjn,
            Nat.mod_eq_of_lt hjn]
          refine congrFun (nttBy_congr o fun t ht => ?_) _
          simp only [zero_mul, zero_add]
          rw [getD_take_lt ht]
        · have hge : n ≤ j := by omega
          obtain ⟨j', rfl⟩ : ∃ j', j = n + j' := ⟨j - n, by omega⟩
          have hj' : j' < k * n := by rw [Nat.succ_mul] at hj; omega
          rw [List.getD_append_right _ _ _ _ (by omega), show n + j' - o'.length = j' by omega,
            hosv j' hj']
          have hdiv : (n + j') / n = j' / n + 1 := by
            rw [Nat.add_comm, Nat.add_div_right _ hn0]
          have hmod : (n + j') % n = j' % n := by simp
          rw [hmod]
          refine congrFun (nttBy_congr o fun t _ => ?_) _
          rw [OpList.getD_drop', hdiv]
          congr 2
          ring

theorem stagedStep_sound (hAr : env.ArithOk (I (ir.circField c)).decode)
    (hE : ir.EmitTableOk env E) {kid : ℕ → ℕ → Except TReason (List TE × Cuts)} {k : ℕ}
    {r : List TE × Cuts}
    (hkid : KidSpec (ir := ir) (c := c) (env := env) (E := E) (rd := rd) (V := V) kid k)
    {op : EOp} {a nn psi w : ℕ} {o : NttOrder} (hk : (E.get k).node = .apply op a)
    (hs : staged? op = some (nn, psi, o, w)) (h : ir.nodeStep c env E kid k = .ok r)
    (hcs : CutsHold (ir := ir) (c := c) (V := V) r.2) :
    NodeOk (ir := ir) (c := c) (env := env) (E := E) (rd := rd) (V := V) k r.1 := by
  have hA := hAr.hom
  unfold nodeStep at h
  simp only [hk, hs, except_bind_eq_ok, chk_eq_ok, Bool.and_eq_true, Nat.ble_eq, Nat.beq_eq] at h
  obtain ⟨r', hr', _, ⟨⟨⟨h2, hpow⟩, hdiv⟩, hpsi⟩, h⟩ := h
  split at h
  · rename_i out cs hb
    cases h
    dsimp only at hcs
    rw [cutsHold_append] at hcs
    obtain ⟨-, -, hxl, hxv⟩ := hkid a _ r' hr' hcs.2
    obtain ⟨nop, mask, rfl, hcore⟩ := staged?_eq hs
    obtain ⟨hrows, hcols, cc, hwc, hc0⟩ := stagedCore?_dims (ir := ir) hcore
    have hψ : (I (ir.circField c)).decode psi ^ nn = -1 := by
      rw [← codePow_hom hA]
      exact hA.neg_one hpsi
    have hn0 : 0 < nn := by omega
    have hkw : r'.1.length = r'.1.length / w * w :=
      (Nat.div_mul_cancel (Nat.dvd_of_mod_eq_zero hdiv)).symm
    have hkl : r'.1.length = r'.1.length / nn * nn :=
      (Nat.div_mul_cancel (Nat.dvd_trans ⟨cc, hwc⟩ (Nat.dvd_of_mod_eq_zero hdiv))).symm
    obtain ⟨hol, hov⟩ := nttBlocksT_sound hAr hpow hψ _ r'.1 _ hkl hb hcs.1
    have hlenk : (E.get k).len = (E.get a).len := by
      rw [hE.len_eq k, hk]
      simp only [ENode.row, EOp.wrap, Expr.len, hrows, hcols]
      rw [← hxl, ← hkw]
    refine nodeOk_of_row hE fun j hj => ?_
    have hj' : j < r'.1.length / nn * nn := by rw [← hkl, hxl, ← hlenk]; exact hj
    rw [hov j hj', hk]
    simp only [ENode.row, EOp.wrap, Expr.eval]
    rw [stagedCore?_apply hcore hn0]
    refine congrFun (nttBy_congr o fun t ht => ?_) _
    have hlt : j / nn * nn + t < (E.get a).len := by
      have h1 : j / nn < r'.1.length / nn := Nat.div_lt_of_lt_mul (by
        rw [Nat.mul_comm]; exact hj')
      have h2 : (j / nn + 1) * nn ≤ r'.1.length / nn * nn := Nat.mul_le_mul_right _ h1
      rw [add_mul, one_mul] at h2
      rw [← hxl, hkl]
      omega
    exact (hxv _ hlt).symm
  · cases h

/-! ### Expansions -/

/-- **A node's one-level form carries its meaning** where its kid reader is sound and its cuts
hold, by its kind. -/
theorem nodeStep_sound (hAr : env.ArithOk (I (ir.circField c)).decode)
    (hE : ir.EmitTableOk env E)
    (hK : ∀ v es, (ir.value v).kind = .constant es → ∀ i,
      rd v i = (I (ir.valueField v)).decode (es.getD i 0))
    {kid : ℕ → ℕ → Except TReason (List TE × Cuts)} {k : ℕ} {r : List TE × Cuts}
    (hkid : KidSpec (ir := ir) (c := c) (env := env) (E := E) (rd := rd) (V := V) kid k)
    (h : ir.nodeStep c env E kid k = .ok r) (hcs : CutsHold (ir := ir) (c := c) (V := V) r.2) :
    NodeOk (ir := ir) (c := c) (env := env) (E := E) (rd := rd) (V := V) k r.1 := by
  cases hn : (E.get k).node with
  | lin ts z =>
    cases ts with
    | nil => exact linNilStep_sound hAr hE hK hn h
    | cons t ts => exact linConsStep_sound hAr hE hK hkid hn h hcs
  | const v => exact constStep_sound hE hK hn h
  | bin op a b => exact chainStep_sound hAr hE hkid hn h hcs
  | scale s a => exact scaleStep_sound hAr hE hkid hn h hcs
  | sum w a => exact sumStep_sound hAr hE hkid hn h hcs
  | broadcast idx a => exact broadcastStep_sound hAr hE hK hkid hn h hcs
  | lnot o a => exact lnotStep_sound hAr hE hK hkid hn h hcs
  | mux bit cc t e =>
    cases bit with
    | false => exact muxFieldStep_sound hAr hE hkid hn h hcs
    | true => exact muxBitStep_sound hAr hE hkid hn h hcs
  | materialize a => exact materializeStep_sound hE hkid hn h hcs
  | gather idx ps => exact gatherStep_sound hAr hE hK hkid hn h hcs
  | apply op a =>
    cases hs : staged? op with
    | none => exact applyStep_sound hAr hE hK hkid hn hs h hcs
    | some q =>
      obtain ⟨nn, psi, o, w⟩ := q
      exact stagedStep_sound hAr hE hkid hn hs h hcs
  | value u pl =>
    unfold nodeStep at h
    simp [hn] at h
  | prod w a => exact prodStep_sound hAr hE hkid hn h hcs
  | cmp op w a b => exact cmpStep_sound hAr hE hK hkid hn h hcs
  | tree any w a => exact treeStep_sound hAr hE hkid hn h hcs

/-- **An expansion carries its node's meaning** (`nodeEF`): where the cut nodes below carry
theirs and the expansion's cuts hold, it has one tree expression per coordinate, each of the node's
meaning. -/
theorem nodeEF_sound (hAr : env.ArithOk (I (ir.circField c)).decode)
    (hE : ir.EmitTableOk env E)
    (hK : ∀ v es, (ir.value v).kind = .constant es → ∀ i,
      rd v i = (I (ir.valueField v)).decode (es.getD i 0)) :
    ∀ (f k : ℕ) {r : List TE × Cuts},
      KidsOk (ir := ir) (c := c) (env := env) (E := E) (rd := rd) (V := V) k →
      ir.nodeEF c env E f k = .ok r → CutsHold (ir := ir) (c := c) (V := V) r.2 →
      ExpOk (ir := ir) (c := c) (env := env) (E := E) (rd := rd) (V := V) k r.1
  | 0, k, r, _, h, _ => by simp [nodeEF] at h
  | f + 1, k, r, IH, h, hcs => by
    simp only [nodeEF, except_bind_eq_ok, chk_eq_ok, Nat.beq_eq, Except.ok.injEq] at h
    obtain ⟨r', hr', _, hl, rfl⟩ := h
    have hkid := kidSpec_kidTEF (rec := ir.nodeEF c env E f) IH fun a hak q hq hcq =>
      nodeEF_sound hAr hE hK f a (fun b hb hcb => IH b (by omega) hcb) hq hcq
    exact ⟨hl, nodeStep_sound hAr hE hK hkid hr' hcs⟩

/-! ### Value leaves -/

/-- **The premise on placement leaves**: the conclusion of `placementRead_sound` at the reader
`rd` and the node values `V`. -/
def LeafReads : Prop :=
  ∀ k u pl, (E.get k).node = .value u pl → (∀ y, pl ≠ .defined y) → ∀ cs,
    ir.placeCuts c env E k = some cs →
      CutsHold (ir := ir) (c := c) (V := V) cs → ∀ i < (E.get k).len,
        (castElt (rd u i) : (I (ir.circField c)).K) =
          ((E.get k).wires.getD i default).val (I (ir.circField c)).decode V

theorem valueCuts_sound (hE : ir.EmitTableOk env E) (ho : ir.RefsOrdered) (hR : ir.DefReads rd)
    (hL : LeafReads (ir := ir) (c := c) (env := env) (E := E) (rd := rd) (V := V))
    {k : ℕ} {cs : List (Wire × TE)}
    (IH : KidsOk (ir := ir) (c := c) (env := env) (E := E) (rd := rd) (V := V) k)
    {u : ℕ} {pl : Place} (hk : (E.get k).node = .value u pl)
    (h : ir.nodeCutsE c env E k = .ok cs) (hcs : CutsHold (ir := ir) (c := c) (V := V) cs) :
    ir.WiresOk c env E rd V k := by
  unfold nodeCutsE at h
  simp only [hk, except_bind_eq_ok, chk_eq_ok, Bool.and_eq_true, Nat.beq_eq] at h
  obtain ⟨_, ⟨⟨-, hw⟩, -⟩, hp⟩ := h
  have hsem : ∀ i, ir.nodeSem env E rd (ir.circuit c).domain k i =
      (castElt (rd u i) : (I (ir.circField c)).K) := fun i => by
    rw [congrFun (nodeSem_eq hE rd _ k) i, hk]
    rfl
  refine ⟨hw, fun i hi => ?_⟩
  rw [hsem i]
  have hpc : ir.placeCuts c env E k = some cs := by
    simp [placeCuts, hp, Except.toOption]
  cases pl with
  | defined y =>
    have hy : y < k ∧ (E.get y).cut = true := by
      unfold placeCutsE at hp
      simp only [hk, hw, Nat.beq_refl, Bool.not_true, Bool.cond_false] at hp
      split at hp
      · obtain ⟨hb, -⟩ := cond_ok_eq_ok hp
        simp only [Bool.and_eq_true, Nat.blt_eq] at hb
        exact ⟨hb.1.1.1.1.1, hb.1.1.1.1.2⟩
      · cases hp
    obtain ⟨-, hvy⟩ := IH y hy.1 hy.2
    exact ((defRead_sound ho hE hR hk hpc hcs fun i hi => (hvy i hi).symm) i hi).symm
  | block b => exact (hL k u _ hk (fun _ h => by cases h) cs hpc hcs i hi).symm
  | late pb pd => exact (hL k u _ hk (fun _ h => by cases h) cs hpc hcs i hi).symm

/-- **A cut node other than a leaf** carries its meaning: its wires against its expansion. -/
theorem cutCuts_sound (hAr : env.ArithOk (I (ir.circField c)).decode)
    (hE : ir.EmitTableOk env E)
    (hK : ∀ v es, (ir.value v).kind = .constant es → ∀ i,
      rd v i = (I (ir.valueField v)).decode (es.getD i 0))
    {k : ℕ} {cs : List (Wire × TE)}
    (IH : KidsOk (ir := ir) (c := c) (env := env) (E := E) (rd := rd) (V := V) k)
    (hnv : ∀ u pl, (E.get k).node ≠ .value u pl) (hcut : (E.get k).cut = true)
    (h : ir.nodeCutsE c env E k = .ok cs) (hcs : CutsHold (ir := ir) (c := c) (V := V) cs) :
    ir.WiresOk c env E rd V k := by
  unfold nodeCutsE at h
  dsimp only at h
  split at h
  · rename_i u pl hv
    exact absurd hv (hnv u pl)
  · simp only [hcut, Bool.cond_true, except_bind_eq_ok, chk_eq_ok, Nat.beq_eq,
      Except.ok.injEq] at h
    obtain ⟨_, hw, r, hr, rfl⟩ := h
    rw [cutsHold_append] at hcs
    obtain ⟨hl, hv⟩ := nodeEF_sound hAr hE hK (k + 1) k IH hr hcs.2
    refine ⟨hw, fun i hi => ?_⟩
    have hc := hcs.1 _ (mem_zip_getD (xs := (E.get k).wires) (ys := r.1) (i := i) (by omega)
      (by omega))
    simp only at hc
    rw [hc, hv i hi]

/-! ### The table -/

/-- **The node table is sound** (the table invariant): at node values `V` where every node's cuts
hold, every cut node has one wire per coordinate, each of the node's meaning there. Hypotheses:
the environment's codes decode as named (`TEnv.ArithOk`), the table checks (`EmitTableOk`), the
shared expressions read only earlier ones, constants read their entries, definitions read their
expressions (`DefReads`), placement leaves read their inputs (`LeafReads`, given by
`placementRead_sound`), and every node below the node count passes `nodeCutsE` with its cuts
holding (`relOk_sound`). -/
theorem nodeTable_sound (hAr : env.ArithOk (I (ir.circField c)).decode)
    (hE : ir.EmitTableOk env E) (ho : ir.RefsOrdered)
    (hK : ∀ v es, (ir.value v).kind = .constant es → ∀ i,
      rd v i = (I (ir.valueField v)).decode (es.getD i 0))
    (hR : ir.DefReads rd)
    (hL : LeafReads (ir := ir) (c := c) (env := env) (E := E) (rd := rd) (V := V))
    (hcuts : ∀ k < E.size, ∃ cs, ir.nodeCutsE c env E k = .ok cs ∧
      CutsHold (ir := ir) (c := c) (V := V) cs) :
    ∀ k < E.size, (E.get k).cut = true → ir.WiresOk c env E rd V k := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hks hcut
    have IH : KidsOk (ir := ir) (c := c) (env := env) (E := E) (rd := rd) (V := V) k :=
      fun a hak hca => ih a hak (by omega) hca
    obtain ⟨cs, h, hcs⟩ := hcuts k hks
    cases hn : (E.get k).node with
    | value u pl => exact valueCuts_sound hE ho hR hL IH hn h hcs
    | _ => exact cutCuts_sound hAr hE hK IH (fun u pl hv => by rw [hn] at hv; cases hv) hcut h hcs

/-- **An uncut node's expansion carries its meaning** below a sound table: where every cut node
below it carries its meaning (`nodeTable_sound`) and the expansion's cuts hold. -/
theorem expansion_sound (hAr : env.ArithOk (I (ir.circField c)).decode)
    (hE : ir.EmitTableOk env E)
    (hK : ∀ v es, (ir.value v).kind = .constant es → ∀ i,
      rd v i = (I (ir.valueField v)).decode (es.getD i 0))
    {k f : ℕ} {r : List TE × Cuts}
    (hT : ∀ a < k, (E.get a).cut = true → ir.WiresOk c env E rd V a)
    (h : ir.nodeEF c env E f k = .ok r) (hcs : CutsHold (ir := ir) (c := c) (V := V) r.2) :
    r.1.length = (E.get k).len ∧ ∀ j < (E.get k).len,
      (r.1.getD j default).eval (I (ir.circField c)).decode V =
        ir.nodeSem env E rd (ir.circuit c).domain k j :=
  nodeEF_sound hAr hE hK f k hT h hcs

end Kinds

/-- **The decoded valuation meets the placement-leaf premise** (`LeafReads`) at node values reading
the input vector, where the environment's codes decode as named (`placementRead_sound`). -/
theorem leafReads_inputValuation (hL : ir.InputLayoutOk c)
    (hfit : (ir.circuit c).inputCount ≤ 2 ^ d)
    (hpub : ∀ j : Fin (2 ^ d), (ir.circuit c).IsPublicPos j → v j = ir.publicInput I c x r j)
    (hP : ir.InputPremises I c x r v)
    {val : ℕ → (I (ir.circField c)).K} (hval : ∀ q < (ir.circuit c).inputCount, val q = vecRead v q)
    {env : TEnv} (hAr : env.ArithOk (I (ir.circField c)).decode) {E : ETable} :
    LeafReads (ir := ir) (c := c) (env := env) (E := E) (rd := ir.inputValuation I c x r v)
      (V := val) :=
  fun _ _ _ hk hpl _ h hcs => placementRead_sound hL hfit hpub hP hval hAr hk hpl h hcs

end GordieHowe.RealizedProgram
