-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Language.Realizations.ProductForm
public import GordieHowe.Language.Realizations.Derivation.Basic
public import GordieHowe.Language.Realizations.RealizeInteger
public import GordieHowe.Language.Library.Eval
public import GordieHoweNative.Language.Realizations.ProductEquation

@[expose] public section

/-!
# GordieHowe: the asserted equation of a product form placed in a circuit

A spectral product form `mod_m P N` placed in a circuit asserts zero, coordinatewise, on the C++
node `Congruence::equation` (`lib/gordiehowe/ops/integer_congruence.h`, built by `product_sides`
in `lib/gordiehowe/compiler/mod.h` and `spectral_sides` in `lib/gordiehowe/ops/spectral_sum.h`).
The circuit's template concludes that the printed form `X` of that node is zero. This file
recognizes `X` (`GordieHowe.RealizedProgram.productEquationB`) and proves that a zero `X` gives the
placed equation (`GordieHowe.RealizedProgram.productPlaced_of_productEquationB`).

**The normal form.** Both `X` and the expected equation are compared as sums of signed, scaled
products (`GordieHowe.RealizedProgram.nf`): a monomial (`Mono`) is a code `c` times a product of
factors, a factor an atom expression read at one coordinate per output coordinate (its path).
Normalizing an expression read at the coordinates `ps`:

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

Two monomial lists agree (`matchAll`) when every monomial matches a distinct one of equal code
whose factors match one to one: equal paths and structurally equal atoms, or, for two transforms
`.apply (.ntt n ψ o)` read below `n`, operands whose normal forms agree below `n`.

**The accepted form of `X`**, for the shape `sh` of the sides (`productShape?`), `n = sh.n`, `T`
the transform `.apply (.ntt n sh.psi o)` (`o` natural or scheme as `sh.natural`), `R` the rows: for
every row `r < R`, `X` read at `r n, …, r n + n − 1` normalizes to one monomial `T L` (code `1`, path
`0, …, n − 1`) and the rest, where

* `L` read below `n` agrees with the row's expression parts of `P` minus those of `N`, minus `m`
  times the quotient's coordinates `r n, …, r n + n − 1`, minus the constant `m qlo`;
* the rest agrees with `−s · h_b ⊙ T(x)` for each kernel part of `N` and `s · h_b ⊙ T(x)` for each
  kernel part of `P` (`h_b` block `b` of the kernel's value, `x` its operand, `s` its scale).

The definitions are in `GordieHoweNative/Language/Realizations/ProductEquation.lean`
(the compiled library `GordieHoweNative`); this module has their lemmas.
-/

namespace GordieHowe.RealizedProgram

open Export

/-! ## Matching list elements -/

/-- **Removing the element `takeSome` finds splits the sum** of any weights `w`. -/
theorem takeSome_sum {σ β M : Type*} [AddCommMonoid M] (w : σ → M) {g : σ → Option β} :
    ∀ {ss : List σ} {b : β} {ss' : List σ}, takeSome g ss = some (b, ss') →
      ∃ s, g s = some b ∧ (ss.map w).sum = w s + (ss'.map w).sum
  | [], _, _, h => by simp [takeSome] at h
  | s :: ss, b, ss', h => by
    unfold takeSome at h
    split at h
    · rename_i b' hs
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨s, hs, by simp⟩
    · obtain ⟨⟨b'', ss''⟩, h', he⟩ := Option.map_eq_some_iff.1 h
      simp only [Prod.mk.injEq] at he
      obtain ⟨rfl, rfl⟩ := he
      obtain ⟨t, ht, hsum⟩ := takeSome_sum w h'
      refine ⟨t, ht, ?_⟩
      simp only [List.map_cons, List.sum_cons, hsum]
      abel

/-- **Removing the element `takeSome` finds splits the product** of any weights `w`. -/
theorem takeSome_prod {σ β M : Type*} [CommMonoid M] (w : σ → M) {g : σ → Option β} :
    ∀ {ss : List σ} {b : β} {ss' : List σ}, takeSome g ss = some (b, ss') →
      ∃ s, g s = some b ∧ (ss.map w).prod = w s * (ss'.map w).prod
  | [], _, _, h => by simp [takeSome] at h
  | s :: ss, b, ss', h => by
    unfold takeSome at h
    split at h
    · rename_i b' hs
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨s, hs, by simp⟩
    · obtain ⟨⟨b'', ss''⟩, h', he⟩ := Option.map_eq_some_iff.1 h
      simp only [Prod.mk.injEq] at he
      obtain ⟨rfl, rfl⟩ := he
      obtain ⟨t, ht, hprod⟩ := takeSome_prod w h'
      refine ⟨t, ht, ?_⟩
      simp only [List.map_cons, List.prod_cons, hprod]
      exact mul_left_comm _ _ _

/-- **Matched lists have equal sums**, when a match `m s e` gives `e` the slot's weight. -/
theorem matchAll_sum {σ τ M : Type*} [AddCommMonoid M] {m : σ → τ → Bool} (fe : τ → M)
    (g : σ → M) (hm : ∀ s e, m s e = true → fe e = g s) :
    ∀ {es : List τ} {ss : List σ}, matchAll m es ss = true → (es.map fe).sum = (ss.map g).sum
  | [], ss, h => by
    simp only [matchAll, List.isEmpty_iff] at h
    simp [h]
  | e :: es, ss, h => by
    unfold matchAll at h
    split at h
    · rename_i u ss' hss
      obtain ⟨s, hs, hsum⟩ := takeSome_sum g hss
      have hse : m s e = true := by
        by_contra hc
        simp [hc] at hs
      rw [List.map_cons, List.sum_cons, hsum, hm s e hse, matchAll_sum fe g hm h]
    · cases h

/-- **Matched lists have equal products**, when a match `m s e` gives `e` the slot's weight. -/
theorem matchAll_prod {σ τ M : Type*} [CommMonoid M] {m : σ → τ → Bool} (fe : τ → M)
    (g : σ → M) (hm : ∀ s e, m s e = true → fe e = g s) :
    ∀ {es : List τ} {ss : List σ}, matchAll m es ss = true → (es.map fe).prod = (ss.map g).prod
  | [], ss, h => by
    simp only [matchAll, List.isEmpty_iff] at h
    simp [h]
  | e :: es, ss, h => by
    unfold matchAll at h
    split at h
    · rename_i u ss' hss
      obtain ⟨s, hs, hprod⟩ := takeSome_prod g hss
      have hse : m s e = true := by
        by_contra hc
        simp [hc] at hs
      rw [List.map_cons, List.prod_cons, hprod, hm s e hse, matchAll_prod fe g hm h]
    · cases h

/-- **A sum of negated terms is the negated sum.** -/
theorem List.sum_map_neg_fun {α M : Type*} [AddCommGroup M] (g : α → M) :
    ∀ l : List α, (l.map fun x => -g x).sum = -(l.map g).sum
  | [] => by simp
  | a :: l => by
    simp only [List.map_cons, List.sum_cons, List.sum_map_neg_fun g l]
    abel

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

/-- **The transform `ntt n ψ` of order `natural` at a frequency below `n`** is `Ops.nttOf`. -/
theorem nttOf_congr {K : Type*} [Field K] (natural : Bool) {n : ℕ} (ψ : K) {x y : ℕ → K}
    (h : ∀ t < n, x t = y t) (k : ℕ) : Ops.nttOf natural n ψ x k = Ops.nttOf natural n ψ y k := by
  have hf : Ops.toFin n x = Ops.toFin n y := funext fun t => h t t.isLt
  cases natural <;> simp [Ops.nttOf, Ops.nttScheme, Ops.nttNatural, hf]

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

theorem nfSum_sound [CharP (I f).K p] (hN : NormModel rd f p) (k : ℕ) (ps : List ℕ) :
    ∀ (es : List Expr) (ms : List Mono), ir.nfSum f p k ps es = some ms →
      ∀ i < ps.length, (es.map fun e => ir.evalE rd f e (ps.getD i 0)).sum = monosVal rd f i ms
  | [], ms, h, i, _ => by
    simp only [nfSum, Option.some.injEq] at h
    subst h
    rfl
  | e :: es, ms, h, i, hi => by
    simp only [nfSum, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at h
    obtain ⟨x, hx, y, hy, rfl⟩ := h
    rw [List.map_cons, List.sum_cons, monosVal_append, nf_sound hN k ps e x hx i hi,
      nfSum_sound hN k ps es y hy i hi]

/-- **The transform at a frequency below `n`** is `Ops.nttOf` of the operand. -/
theorem evalE_apply_ntt (rd : ir.Valuation I) (f : ℕ) {n psi : ℕ} (natural : Bool) (x : Expr)
    {k : ℕ} (hk : k < n) :
    ir.evalE rd f (.apply (.ntt n psi (nttOrderOf natural)) x) k =
      Ops.nttOf natural n ((I f).decode psi) (ir.evalE rd f x) k := by
  rw [evalE_apply]
  simp only [NamedOp.apply, NamedOp.rows, NamedOp.cols, Nat.div_eq_of_lt hk, Nat.mod_eq_of_lt hk,
    Nat.zero_mul, Nat.zero_add]
  cases natural <;> rfl

/-- **Transforms of operands agreeing below `n` agree below `n`.** -/
theorem evalE_apply_ntt_congr (rd : ir.Valuation I) (f : ℕ) {n psi : ℕ} (o : NttOrder)
    {x x' : Expr} (h : ∀ t < n, ir.evalE rd f x t = ir.evalE rd f x' t) {j : ℕ} (hj : j < n) :
    ir.evalE rd f (.apply (.ntt n psi o) x) j = ir.evalE rd f (.apply (.ntt n psi o) x') j := by
  rw [evalE_apply, evalE_apply]
  simp only [NamedOp.apply, NamedOp.rows, NamedOp.cols, Nat.div_eq_of_lt hj, Nat.mod_eq_of_lt hj,
    Nat.zero_mul, Nat.zero_add]
  exact NamedOp.block_ntt_congr ir f rd o h j

/-- **Agreeing monomials have equal values**, given that agreeing factors do. -/
theorem monoVal_of_match [CharP (I f).K p] {k : ℕ}
    (hfac : ∀ x y, ir.facEqB f p k x y = true → ∀ i, facVal rd f i x = facVal rd f i y)
    {m' m : Mono} (h : ir.monoEqB f p k m' m = true) (i : ℕ) : m.val rd f i = m'.val rd f i := by
  simp only [monoEqB, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨hc, hm⟩ := h
  simp only [Mono.val, hc]
  rw [matchAll_prod (facVal rd f i) (facVal rd f i) (fun s e he => (hfac s e he i).symm) hm]

/-- **Agreeing factors have equal values** at every coordinate. -/
theorem facEqB_sound [CharP (I f).K p] (hN : NormModel rd f p) :
    ∀ (k : ℕ) (x y : List ℕ × Expr), ir.facEqB f p k x y = true →
      ∀ i, facVal rd f i x = facVal rd f i y
  | 0, _, _, h, _ => by simp [facEqB] at h
  | k + 1, (ps, a), (ps', a'), h, i => by
    simp only [facEqB, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at h
    obtain ⟨rfl, h⟩ := h
    rcases h with h | h
    · simp only [facVal, Expr.eq_of_beq h]
    · split at h
      · rename_i n psi o x op' x'
        simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
        obtain ⟨⟨⟨rfl, hn⟩, hps⟩, h⟩ := h
        split at h
        · rename_i ms ms' hx hx'
          have hmono : ∀ t, monosVal rd f t ms = monosVal rd f t ms' := fun t =>
            matchAll_sum (Mono.val rd f t) (Mono.val rd f t)
              (fun _ _ he => monoVal_of_match (facEqB_sound hN k) he t) h
          have hop : ∀ t < n, ir.evalE rd f x t = ir.evalE rd f x' t := by
            intro t ht
            have hl : t < (List.range n).length := by simpa using ht
            have e1 := nf_sound hN k _ x ms hx t hl
            have e2 := nf_sound hN k _ x' ms' hx' t hl
            simp only [List.getD_eq_getElem?_getD, List.getElem?_range ht, Option.getD_some] at e1 e2
            rw [e1, e2, hmono]
          have hlt : ps.getD i 0 < n := by
            rcases getD_mem_or ps 0 i with hm | hm
            · exact hps _ hm
            · rw [hm]
              exact hn
          exact evalE_apply_ntt_congr rd f o hop hlt
        · cases h
      · cases h

/-- **Agreeing monomial lists have equal values.** -/
theorem monosVal_of_matchAll [CharP (I f).K p] (hN : NormModel rd f p) {k : ℕ}
    {ms ms' : List Mono} (h : matchAll (ir.monoEqB f p k) ms ms' = true) (i : ℕ) :
    monosVal rd f i ms = monosVal rd f i ms' :=
  matchAll_sum (Mono.val rd f i) (Mono.val rd f i)
    (fun _ _ he => monoVal_of_match (facEqB_sound hN k) he i) h

end Sound

/-! ## Soundness of the row check -/

section RowSound

variable {ir : RealizedProgram} {I : Interp} {rd : ir.Valuation I}

/-- **The values of kernel parts' expected monomials**: each term's kernel term, negated with
`neg`. -/
theorem kernelMonos_sound {d k : ℕ} [CharP (I (ir.domainField d)).K (ir.charOf (ir.domainField d))]
    (hN : NormModel rd (ir.domainField d) (ir.charOf (ir.domainField d))) (sh : ProductShape)
    (neg : Bool) :
    ∀ (κs : List KernelPart) (ms : List Mono),
      ir.kernelMonos (ir.domainField d) (ir.charOf (ir.domainField d)) k sh neg κs = some ms →
      ∀ t < sh.n, monosVal rd (ir.domainField d) t ms =
        (κs.map fun κ =>
          let v := ir.kernelTerm rd d sh.natural sh.n ((I (ir.domainField d)).decode sh.psi) κ t
          if neg then -v else v).sum
  | [], ms, h, t, _ => by
    simp only [kernelMonos, Option.some.injEq] at h
    subst h
    rfl
  | κ :: κs, ms, h, t, ht => by
    simp only [kernelMonos, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
    obtain ⟨x, hx, y, hy, h⟩ := h
    split at h
    · rename_i hs
      simp only [Option.pure_def, Option.some.injEq] at h
      subst h
      have hl : t < (List.range sh.n).length := by simpa using ht
      have ex := nf_sound hN k _ _ x hx t hl
      simp only [List.getD_eq_getElem?_getD, List.getElem?_range ht, Option.getD_some] at ex
      rw [monosVal_append, monosVal_map_scale, ← ex, kernelMonos_sound hN sh neg κs y hy t ht,
        natCast_intCode hN.pos, List.map_cons, List.sum_cons]
      congr 1
      simp only [kernelExpr, evalE_mul, evalE_reindex, IndexMap.entry_slice ht,
        evalE_apply_ntt rd _ sh.natural _ ht, evalE_leaf, kernelTerm, hN.dec _ hs]
      rw [show ir.evalWith rd d κ.operand = ir.evalE rd (ir.domainField d) κ.operand from rfl]
      split_ifs <;> push_cast <;> ring
    · cases h

/-- **The value of a row's expected transformed operand** below `n`: the row's expression parts
of `P` minus those of `N` minus the quotient term. -/
theorem lhsMonos_sound {d k m : ℕ}
    [CharP (I (ir.domainField d)).K (ir.charOf (ir.domainField d))]
    (hN : NormModel rd (ir.domainField d) (ir.charOf (ir.domainField d))) {real : ModRealization}
    {sh : ProductShape} {r : ℕ} {PR NR : Expr} {ms : List Mono}
    (h : ir.lhsMonos (ir.domainField d) (ir.charOf (ir.domainField d)) k m real sh r PR NR =
      some ms) {t : ℕ} (ht : t < sh.n) :
    monosVal rd (ir.domainField d) t ms =
      ((ir.rowExprs PR).map fun e => ir.evalWith rd d e t).sum -
        ((ir.rowExprs NR).map fun e => ir.evalWith rd d e t).sum -
          ir.quotTerm rd d m real (r * sh.n + t) := by
  have hl : t < (List.range sh.n).length := by simpa using ht
  have hg : (List.range sh.n).getD t 0 = t := by
    simp [List.getD_eq_getElem?_getD, List.getElem?_range ht]
  simp only [lhsMonos, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
    Option.some.injEq] at h
  obtain ⟨a, ha, b, hb, q, hq, rfl⟩ := h
  have ea := nfSum_sound hN k _ _ a ha t hl
  have eb := nfSum_sound hN k _ _ b hb t hl
  simp only [hg] at ea eb
  unfold quotMonos at hq
  unfold quotTerm
  have hc : ∀ x : (I (ir.domainField d)).K,
      monosVal rd (ir.domainField d) t (if real.quotientLo = 0 then [] else
        [⟨intCode (ir.charOf (ir.domainField d)) (-((m : ℤ) * real.quotientLo)), []⟩]) - x =
        -(((m : ℤ) * real.quotientLo : ℤ) : (I (ir.domainField d)).K) - x := by
    intro x
    split_ifs with hz
    · simp [monosVal_nil, hz]
    · simp only [monosVal, Mono.val, List.map_cons, List.map_nil, List.prod_nil, mul_one,
        List.sum_cons, List.sum_nil, add_zero, natCast_intCode hN.pos]
      push_cast
      ring
  cases hQ : real.quotient with
  | some Q =>
    rw [hQ] at hq
    obtain ⟨x, hx, rfl⟩ := Option.map_eq_some_iff.1 hq
    have ex := nf_sound hN k _ Q x hx t (by simpa using ht)
    rw [getD_map_of_lt _ _ 0 _ hl, hg] at ex
    have := hc 0
    rw [sub_zero, sub_zero] at this
    rw [monosVal_append, monosVal_append, monosVal_append, monosVal_map_scale, monosVal_map_scale,
      this, ← ea, ← eb, ← ex, natCast_intCode hN.pos, natCast_intCode hN.pos]
    simp only [evalWith]
    push_cast
    ring
  | none =>
    rw [hQ] at hq
    simp only [Option.some.injEq] at hq
    subst hq
    have := hc 0
    rw [sub_zero, sub_zero] at this
    rw [monosVal_append, monosVal_append, monosVal_append, monosVal_map_scale, monosVal_nil,
      this, ← ea, ← eb, natCast_intCode hN.pos]
    simp only [evalWith]
    push_cast
    ring

variable {primeNodes : ℕ → List String}

/-- **The asserted equation of a product form gives its placed equation**: if `X` is the printed
equation (`productEquationB`) and every coordinate of `X` is zero, the product form's placed
equation holds (`ProductPlaced`). -/
theorem productPlaced_of_productEquationB {primeNodes : ℕ → List String}
    (hM : ir.DerivModel I primeNodes) {rd : ir.Valuation I}
    (hK : ∀ v es, (ir.value v).kind = .constant es → ∀ i,
      rd v i = (I (ir.valueField v)).decode (es.getD i 0))
    (hB : ir.BoundReads rd) {d q : ℕ} {«X» P N : Expr} {real : ModRealization}
    (h : ir.productEquationB d q «X» P N real = true)
    (hX : ∀ i < ir.exprLen «X», ir.evalWith rd d «X» i = 0) : ir.ProductPlaced rd d q P N real := by
  have _hB := hB
  unfold productEquationB at h
  split at h
  · rename_i sh hform hsh
    simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, List.all_eq_true,
      List.mem_range] at h
    obtain ⟨⟨⟨⟨⟨hd, hp⟩, hn⟩, hlen⟩, hXlen⟩, hrows⟩ := h
    have hf := domainField_lt hM.wf hd
    have := charP_field hM.registered hf
    have hN : NormModel rd (ir.domainField d) (ir.charOf (ir.domainField d)) :=
      ⟨hM.wf.refsOrdered, hp, hM.lawful.decode_natCast _ hf, hK⟩
    unfold ProductPlaced
    rw [hform]
    simp only [hsh]
    refine ⟨hlen, fun r hr k hk => ?_⟩
    have hrow := hrows r hr
    unfold spectralRowB at hrow
    split at hrow
    · rename_i ms hms
      split at hrow
      · rename_i L rest htake
        split at hrow
        · rename_i ls el er hls hel her
          simp only [Bool.and_eq_true] at hrow
          obtain ⟨hmL, hmR⟩ := hrow
          -- the row of `X` at frequency `k`
          have hpl : k < ((List.range sh.n).map (r * sh.n + ·)).length := by simpa using hk
          have e0 := nf_sound hN _ _ _ ms hms k hpl
          rw [getD_map_of_lt _ _ 0 _ (by simpa using hk)] at e0
          simp only [List.getD_eq_getElem?_getD, List.getElem?_range hk, Option.getD_some] at e0
          have hz : ir.evalWith rd d «X» (r * sh.n + k) = 0 :=
            hX _ (by nlinarith)
          obtain ⟨s, hs, hsplit⟩ := takeSome_sum (Mono.val rd (ir.domainField d) k) htake
          -- the transform monomial
          unfold transformArg? at hs
          split at hs
          · rename_i ps op L' hfacs
            split at hs
            · rename_i hc
              obtain ⟨hc1, hop, hps⟩ := hc
              simp only [Option.some.injEq] at hs
              subst hs
              have hT : Mono.val rd (ir.domainField d) k s =
                  Ops.nttOf sh.natural sh.n ((I (ir.domainField d)).decode sh.psi)
                    (ir.evalE rd (ir.domainField d) L') k := by
                simp only [Mono.val, hfacs, hc1, hop, hps, List.map_cons, List.map_nil,
                  List.prod_cons, List.prod_nil, mul_one, Nat.cast_one, one_mul, facVal]
                simp only [List.getD_eq_getElem?_getD, List.getElem?_range hk, Option.getD_some]
                exact evalE_apply_ntt rd _ sh.natural L' hk
              -- the transformed operand agrees with the expected one below `n`
              have hLt : ∀ t < sh.n, ir.evalE rd (ir.domainField d) L' t =
                  ((ir.rowExprs (sh.rowsP.getD r default)).map fun e => ir.evalWith rd d e t).sum -
                    ((ir.rowExprs (sh.rowsN.getD r default)).map fun e =>
                      ir.evalWith rd d e t).sum -
                    ir.quotTerm rd d q real (r * sh.n + t) := by
                intro t ht
                have eL := nf_sound hN _ _ L' ls hls t (by simpa using ht)
                simp only [List.getD_eq_getElem?_getD, List.getElem?_range ht,
                  Option.getD_some] at eL
                rw [eL, monosVal_of_matchAll hN hmL t]
                exact lhsMonos_sound hN hel ht
              -- the rest agrees with the kernel terms
              have hR : monosVal rd (ir.domainField d) k rest =
                  -(((ir.rowKernels (sh.rowsN.getD r default)).map fun κ =>
                      ir.kernelTerm rd d sh.natural sh.n
                        ((I (ir.domainField d)).decode sh.psi) κ k).sum -
                    ((ir.rowKernels (sh.rowsP.getD r default)).map fun κ =>
                      ir.kernelTerm rd d sh.natural sh.n
                        ((I (ir.domainField d)).decode sh.psi) κ k).sum) := by
                rw [monosVal_of_matchAll hN hmR k]
                simp only [rhsMonos, Option.bind_eq_bind, Option.bind_eq_some_iff,
                  Option.pure_def, Option.some.injEq] at her
                obtain ⟨a, ha, b, hb, rfl⟩ := her
                rw [monosVal_append, kernelMonos_sound hN sh true _ a ha k hk,
                  kernelMonos_sound hN sh false _ b hb k hk]
                simp only [Bool.false_eq_true, ↓reduceIte, List.sum_map_neg_fun]
                ring
              unfold SpectralRowHolds
              rw [← nttOf_congr sh.natural _ hLt, ← hT]
              have hsum : Mono.val rd (ir.domainField d) k s +
                  monosVal rd (ir.domainField d) k rest = 0 := by
                rw [← hz]
                simp only [evalWith, e0, monosVal, hsplit]
              rw [hR] at hsum
              linear_combination hsum
            · cases hs
          · cases hs
        · cases hrow
      · cases hrow
    · cases hrow
  · cases h

end RowSound

end GordieHowe.RealizedProgram
