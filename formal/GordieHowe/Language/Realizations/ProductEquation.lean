-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Language.Realizations.Derivation.Basic
public import GordieHowe.Language.Realizations.RealizeInteger
public import GordieHowe.Language.Library.Eval
public import GordieHoweNative.Language.Realizations.ProductEquation

@[expose] public section

/-!
# GordieHowe: the normal form of an expression

The normal form an entry's asserted root is compared in (`GordieHowe.RealizedProgram.nf`,
`GordieHowe/Language/Realizations/SharedNorm.lean`, `GordieHowe.RealizedProgram.nfUnitEqB`): a
sum of signed, scaled products. A monomial (`Mono`) is a code `c` times a product of factors, a
factor an atom expression read at one coordinate per output coordinate (its path). Normalizing an
expression read at the coordinates `ps`:

* sums, differences and constant multiples become sums of monomials, `e − e'` as `e + (−1)·e'`,
  the codes multiplied modulo the characteristic;
* a product multiplies out;
* a view composes its index map into the path (`IndexMap.entriesAt`, which is `ps.map idx.entry`
  read in one pass along the runs), so nested views read through
  one path, and a concatenation read wholly in one part is that part;
* a reference is its shared expression;
* a constant reading one code `c` at every coordinate of the path is the scalar `c`;
* a block of a batched transform is the transform of the operand's block;
* any other expression is an atom.

The normal form is sound (`GordieHowe.RealizedProgram.nf_sound`): at every coordinate below the
path's length, an expression's value is its normal form's.

The definitions are in `GordieHoweNative/Language/Realizations/ProductEquation.lean`
(the compiled library `GordieHoweNative`); this module has their lemmas.
-/

namespace GordieHowe.RealizedProgram

open Export

/-! ## Codes, index maps and transforms -/

/-- **The code of `z` casts to `z`** in a ring of characteristic `p > 0`. -/
theorem natCast_intCode {K : Type*} [Ring K] {p : ℕ} [CharP K p] (hp : 0 < p) (z : ℤ) :
    ((intCode p z : ℕ) : K) = (z : K) := by
  have hnn : 0 ≤ z % (p : ℤ) := Int.emod_nonneg _ (by exact_mod_cast hp.ne')
  have hc : ((intCode p z : ℕ) : ℤ) = z % (p : ℤ) := by
    simp only [intCode]
    exact Int.toNat_of_nonneg hnn
  have hd : (p : ℤ) ∣ z - z % (p : ℤ) := ⟨z / (p : ℤ), by rw [Int.emod_def]; ring⟩
  have h0 : ((z - z % (p : ℤ) : ℤ) : K) = 0 := (CharP.intCast_eq_zero_iff K p _).2 hd
  rw [← Int.cast_natCast, hc]
  push_cast at h0
  exact (sub_eq_zero.1 h0).symm

/-- **A natural's cast is its residue's** in a ring of characteristic `p`. -/
theorem natCast_mod_char {K : Type*} [Ring K] {p : ℕ} [CharP K p] (a : ℕ) :
    ((a % p : ℕ) : K) = (a : K) := (CharP.cast_eq_mod K p a).symm

/-- **Entry `k < n` of the single run `[(s, 1, n)]`** is `s + k`. -/
theorem IndexMap.entry_slice {s n k : ℕ} (hk : k < n) :
    IndexMap.entry [((s : ℕ), (1 : ℤ), n)] k = s + k := by
  simp only [IndexMap.entry, hk, ↓reduceIte, one_mul]
  omega

/-- **The transform's block reads its operand below `n` only.** -/
theorem NamedOp.block_ntt_congr (ir : RealizedProgram) {I : Interp} (f : ℕ)
    (leaf : ∀ v : ℕ, ℕ → (I (ir.valueField v)).K) {n psi : ℕ} (o : NttOrder) {x y : ℕ → (I f).K}
    (h : ∀ t < n, x t = y t) (k : ℕ) :
    NamedOp.block ir f leaf (.ntt n psi o) x k = NamedOp.block ir f leaf (.ntt n psi o) y k := by
  have hf : Ops.toFin n x = Ops.toFin n y := funext fun t => h t t.isLt
  cases o <;> simp [NamedOp.block, Ops.nttScheme, Ops.nttNatural, hf]

/-! ## Index maps read along a path -/

namespace IndexMap

theorem entriesGo_eq (m : IndexMap) :
    ∀ (f : ℕ) (r : IndexMap) (o : ℕ) (ps : List ℕ),
      (∀ j, o ≤ j → m.entry j = r.entry (j - o)) → entriesGo m f r o ps = ps.map m.entry
  | _, _, _, [], _ => by simp [entriesGo]
  | 0, r, o, i :: ps, _ => by simp [entriesGo]
  | f + 1, [], o, i :: ps, h => by
    simp only [entriesGo, List.map_cons, entriesGo_eq m f [] o ps h]
  | f + 1, (s, d, c) :: rest, o, i :: ps, h => by
    simp only [entriesGo]
    by_cases h1 : i < o
    · rw [if_pos h1, entriesGo_eq m f _ o ps h, List.map_cons]
    · rw [if_neg h1]
      by_cases h2 : i < o + c
      · rw [if_pos h2, entriesGo_eq m f _ o ps h, List.map_cons, h i (by omega), entry,
          if_pos (by omega)]
      · rw [if_neg h2, entriesGo_eq m f rest (o + c) (i :: ps)]
        intro j hj
        rw [h j (by omega), entry, if_neg (by omega)]
        congr 1
        omega

/-- **The entries along a path are the entries.** -/
theorem entriesAt_eq (m : IndexMap) (ps : List ℕ) : entriesAt m ps = ps.map m.entry :=
  entriesGo_eq m _ m 0 ps fun j _ => by simp

end IndexMap

/-! ## Soundness of the normal form -/

section Sound

variable {ir : RealizedProgram} {I : Interp}

/-- **A factor's value at coordinate `i`**: its atom at its path's entry `i`. -/
def facVal (rd : ir.Valuation I) (f i : ℕ) (x : List ℕ × Expr) : (I f).K :=
  ir.evalE rd f x.2 (x.1.getD i 0)

/-- **A monomial's value at coordinate `i`**: its code's cast times its factors' values. -/
def Mono.val (rd : ir.Valuation I) (f i : ℕ) (m : Mono) : (I f).K :=
  (m.coef : (I f).K) * (m.facs.map (facVal rd f i)).prod

/-- **A monomial list's value at coordinate `i`**: the sum of the monomials' values. -/
def monosVal (rd : ir.Valuation I) (f i : ℕ) (ms : List Mono) : (I f).K :=
  (ms.map (Mono.val rd f i)).sum

/-- **What the normal form needs of the field `f` of characteristic `p`**: the shared expressions
read only smaller ones, `p > 0`, codes below `p` decode to their casts, and constants read their
entries. -/
structure NormModel (rd : ir.Valuation I) (f p : ℕ) : Prop where
  /-- The shared expressions are ordered. -/
  ordered : ir.RefsOrdered
  /-- The characteristic is positive. -/
  pos : 0 < p
  /-- A code below `p` decodes to its cast. -/
  dec : ∀ c < p, (I f).decode c = (c : (I f).K)
  /-- A constant reads its entries. -/
  consts : ∀ v es, (ir.value v).kind = .constant es → ∀ i,
    rd v i = (I (ir.valueField v)).decode (es.getD i 0)

variable {rd : ir.Valuation I} {f p : ℕ}

theorem monosVal_append (i : ℕ) (ms ms' : List Mono) :
    monosVal rd f i (ms ++ ms') = monosVal rd f i ms + monosVal rd f i ms' := by
  simp [monosVal, List.map_append, List.sum_append]

theorem monosVal_nil (i : ℕ) : monosVal rd f i [] = 0 := rfl

theorem Mono.val_scale [CharP (I f).K p] (c i : ℕ) (m : Mono) :
    (m.scale p c).val rd f i = (c : (I f).K) * m.val rd f i := by
  simp only [Mono.val, Mono.scale, natCast_mod_char, Nat.cast_mul, mul_assoc]

theorem monosVal_map_scale [CharP (I f).K p] (c i : ℕ) (ms : List Mono) :
    monosVal rd f i (ms.map (Mono.scale p c)) = (c : (I f).K) * monosVal rd f i ms := by
  simp only [monosVal, List.map_map, Function.comp_def, Mono.val_scale, List.sum_map_mul_left]

theorem Mono.val_mul [CharP (I f).K p] (i : ℕ) (m m' : Mono) :
    (Mono.mul p m m').val rd f i = m.val rd f i * m'.val rd f i := by
  simp only [Mono.val, Mono.mul, natCast_mod_char, Nat.cast_mul, List.map_append, List.prod_append]
  ring

theorem monosVal_flatMap_mul [CharP (I f).K p] (i : ℕ) (ms ms' : List Mono) :
    monosVal rd f i (ms.flatMap fun m => ms'.map (Mono.mul p m)) =
      monosVal rd f i ms * monosVal rd f i ms' := by
  induction ms with
  | nil => simp [monosVal]
  | cons m ms ih =>
    rw [List.flatMap_cons, monosVal_append, ih]
    simp only [monosVal, List.map_cons, List.sum_cons, List.map_map, Function.comp_def,
      Mono.val_mul, List.sum_map_mul_left]
    ring

theorem Mono.val_atom (i : ℕ) (ps : List ℕ) (e : Expr) :
    (Mono.atom ps e).val rd f i = ir.evalE rd f e (ps.getD i 0) := by
  simp [Mono.val, Mono.atom, facVal]

theorem monosVal_atom (i : ℕ) (ps : List ℕ) (e : Expr) :
    monosVal rd f i [Mono.atom ps e] = ir.evalE rd f e (ps.getD i 0) := by
  simp [monosVal, Mono.val_atom]

/-- **Entry `i` below the length of a mapped list.** -/
theorem getD_map_of_lt {α β : Type*} (g : α → β) (l : List α) (d : α) (d' : β) {i : ℕ}
    (hi : i < l.length) : (l.map g).getD i d' = g (l.getD i d) := by
  rw [List.getD_eq_getElem _ _ (by simpa using hi), List.getD_eq_getElem _ _ hi,
    List.getElem_map]

/-- **Entry `i` below the length is a member.** -/
theorem getD_mem_of_lt {α : Type*} (l : List α) (d : α) {i : ℕ} (hi : i < l.length) :
    l.getD i d ∈ l := by
  rw [List.getD_eq_getElem _ _ hi]
  exact List.getElem_mem hi

/-- **Entry `i` of a list is a member or the default.** -/
theorem getD_mem_or {α : Type*} (l : List α) (d : α) (i : ℕ) : l.getD i d ∈ l ∨ l.getD i d = d := by
  by_cases hi : i < l.length
  · exact .inl (getD_mem_of_lt l d hi)
  · right
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega), Option.getD_none]

theorem nfLeaf_sound [CharP (I f).K p] (hN : NormModel rd f p) (u : ℕ) (ps : List ℕ) {i : ℕ}
    (hi : i < ps.length) : ir.evalE rd f (.leaf u) (ps.getD i 0) = monosVal rd f i (ir.nfLeaf f p u ps) := by
  unfold nfLeaf
  split
  · rename_i c hc
    unfold constCode? at hc
    split at hc
    · rename_i es hk
      split at hc
      · rename_i hall
        simp only [Option.some.injEq] at hc
        subst hc
        simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, beq_iff_eq] at hall
        obtain ⟨⟨⟨hvf, hlt⟩, hes⟩, hps⟩ := hall
        have hmem := getD_mem_of_lt ps 0 hi
        have hin := hps _ hmem
        have hent : es.getD (ps.getD i 0) 0 = es.headD 0 := by
          rw [List.getD_eq_getElem _ _ hin]
          exact hes _ (List.getElem_mem hin)
        simp only [monosVal, Mono.val, List.map_cons, List.map_nil, List.prod_nil, mul_one,
          List.sum_cons, List.sum_nil, add_zero]
        rw [evalE_leaf, hN.consts u es hk, hent]
        subst hvf
        rw [hN.dec _ hlt, castElt_self]
      · cases hc
    · cases hc
  · rw [monosVal_atom]

/-- **A block of a batched transform is the transform of the operand's block.** -/
theorem evalE_batched_ntt_block (rd : ir.Valuation I) (f : ℕ) {B n psi b i : ℕ} (o : NttOrder)
    (x : Expr) (hb : b < B) (hi : i < n) :
    ir.evalE rd f (.apply (.batched B (.ntt n psi o)) x) (b * n + i) =
      ir.evalE rd f (.apply (.ntt n psi o) (.reindex [(b * n, 1, n)] x)) i := by
  have hn : 0 < n := by omega
  have hlt : b * n + i < B * n := by nlinarith
  rw [evalE_apply, evalE_apply]
  simp only [NamedOp.apply, NamedOp.rows, NamedOp.cols]
  rw [Nat.div_eq_of_lt hlt, Nat.mod_eq_of_lt hlt, Nat.div_eq_of_lt hi, Nat.mod_eq_of_lt hi]
  simp only [NamedOp.block, NamedOp.rows, NamedOp.cols, Nat.zero_mul, Nat.zero_add, if_pos hlt]
  have hd : (b * n + i) / n = b := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ hn, Nat.div_eq_of_lt hi, Nat.zero_add]
  have hm : (b * n + i) % n = i := by
    rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hi]
  rw [hd, hm]
  refine NamedOp.block_ntt_congr ir f rd o (fun t ht => ?_) i
  rw [evalE_reindex, IndexMap.entry_slice ht]

theorem nfApply_sound (op : NamedOp) (x : Expr) (ps : List ℕ) {i : ℕ} (hi : i < ps.length) :
    ir.evalE rd f (.apply op x) (ps.getD i 0) = monosVal rd f i (nfApply ps op x) := by
  unfold nfApply
  split
  · rename_i B n psi o
    split
    · rename_i b hb
      unfold blockOfPath? at hb
      split at hb
      · rename_i hc
        simp only [Option.some.injEq] at hb
        subst hb
        simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hc
        obtain ⟨⟨hn, hB⟩, hps⟩ := hc
        have hlen : ps.length = n := by rw [hps]; simp
        have hin : i < n := hlen ▸ hi
        have hget : ps.getD i 0 = ps.headD 0 / n * n + i := by
          generalize ps.headD 0 / n = b at hps
          rw [hps, getD_map_of_lt _ _ 0 _ (by simpa using hin)]
          simp [List.getD_eq_getElem?_getD, hin]
        rw [hget, evalE_batched_ntt_block rd f o x hB hin, monosVal_atom]
        simp [List.getD_eq_getElem?_getD, hin]
      · cases hb
    · rw [monosVal_atom]
  · rw [monosVal_atom]

/-- **The normal form is sound**: an expression read at `ps` is, at every coordinate below the
path's length, the value of its normal form. -/
theorem nf_sound [CharP (I f).K p] (hN : NormModel rd f p) :
    ∀ (k : ℕ) (ps : List ℕ) (e : Expr) (ms : List Mono), ir.nf f p k ps e = some ms →
      ∀ i < ps.length, ir.evalE rd f e (ps.getD i 0) = monosVal rd f i ms
  | 0, _, _, _, h => by simp [nf] at h
  | k + 1, ps, e, ms, h => by
    intro i hi
    have ih := nf_sound hN k
    cases e with
    | add a b =>
      simp only [nf, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
        Option.some.injEq] at h
      obtain ⟨x, hx, y, hy, rfl⟩ := h
      rw [evalE_add, monosVal_append, ih ps a x hx i hi, ih ps b y hy i hi]
    | sub a b =>
      simp only [nf, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
        Option.some.injEq] at h
      obtain ⟨x, hx, y, hy, rfl⟩ := h
      rw [evalE_sub, monosVal_append, monosVal_map_scale, ih ps a x hx i hi, ih ps b y hy i hi,
        natCast_intCode hN.pos]
      push_cast
      ring
    | scale c a =>
      cases c with
      | const c =>
        simp only [nf] at h
        split at h
        · rename_i hc
          obtain ⟨x, hx, rfl⟩ := Option.map_eq_some_iff.1 h
          rw [evalE_scale_const, monosVal_map_scale, ih ps a x hx i hi, hN.dec c hc]
        · simp only [Option.some.injEq] at h
          subst h
          rw [monosVal_atom]
      | node v j =>
        simp only [nf, Option.some.injEq] at h
        subst h
        rw [monosVal_atom]
    | mul a b =>
      simp only [nf, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
        Option.some.injEq] at h
      obtain ⟨x, hx, y, hy, rfl⟩ := h
      rw [evalE_mul, monosVal_flatMap_mul, ih ps a x hx i hi, ih ps b y hy i hi]
    | reindex idx a =>
      simp only [nf, IndexMap.entriesAt_eq] at h
      have := ih _ a ms h i (by simpa using hi)
      rw [evalE_reindex, ← this, getD_map_of_lt _ _ 0 _ hi]
    | concat a b =>
      simp only [nf] at h
      have hmem := getD_mem_of_lt ps 0 hi
      split at h
      · rename_i ha
        simp only [List.all_eq_true, decide_eq_true_eq] at ha
        rw [evalE_concat, if_pos (ha _ hmem), ih ps a ms h i hi]
      · split at h
        · rename_i _ hb
          simp only [List.all_eq_true, decide_eq_true_eq] at hb
          have := ih _ b ms h i (by simpa using hi)
          rw [evalE_concat, if_neg (by have := hb _ hmem; omega), ← this,
            getD_map_of_lt _ _ 0 _ hi]
        · simp only [Option.some.injEq] at h
          subst h
          rw [monosVal_atom]
    | ref j =>
      simp only [nf] at h
      split at h
      · rename_i hj
        rw [evalE_ref hN.ordered rd f hj, ih ps _ ms h i hi]
      · simp only [Option.some.injEq] at h
        subst h
        rw [monosVal_atom]
    | leaf u =>
      simp only [nf, Option.some.injEq] at h
      subst h
      exact nfLeaf_sound hN u ps hi
    | apply op x =>
      simp only [nf, Option.some.injEq] at h
      subst h
      exact nfApply_sound (ir := ir) op x ps hi
    | linear rows a | prod w a | mux b t a | logic op w args =>
      simp only [nf, Option.some.injEq] at h
      subst h
      rw [monosVal_atom]

end Sound

end GordieHowe.RealizedProgram
