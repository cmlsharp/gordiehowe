-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Language.Realizations.ProductEquation
public import GordieHoweNative.Language.Realizations.SharedNorm

@[expose] public section

/-!
# GordieHowe: the normal form of the meaning check, with shared atoms and merged terms

A circuit entry's meaning check (`GordieHowe.RealizedProgram.nfUnitEqB`) compares the print `X` of
the entry's root with the predicate's `l − r`. Both read the program's shared expressions through
`.ref j`. This file normalizes such an expression as a sum of monomials over atoms
(`GordieHowe.RealizedProgram.nfS`) and decides whether a difference of normal forms is zero
(`GordieHowe.RealizedProgram.zeroLoop`).

* **Factors and monomials** (`SFac`, `SMono`): a factor is an atom expression read along a path,
  with a key computed once from the atom and the path (`SFac.of`: `4j + 1` for `.ref j`, `4u` for
  `.leaf u`, a structural hash `Expr.hashN` for any other atom). A monomial is a code times its
  factors, sorted by key; a normal form is a list of monomials sorted by their keys.
* **Arithmetic** (`sAdd`, `sScale`, `sMul`): a sum merges two sorted lists, combining two monomials
  whose factors are equal (`sameFacs`) and dropping a zero code; a product is the sum of the
  monomial products. Every merge has fuel and falls back to concatenation. A key that does not
  separate two atoms only leaves equal monomials unmerged.
* **The normal form** (`nfS`): as `GordieHowe.RealizedProgram.nf`, with merging after every sum and
  product, and `.ref j` an atom.
* **The zero check** (`zeroLoop`): while the difference `D` is not zero, the largest shared
  expression `j` read in `D` along a long enough path is unfolded: every factor `.ref j` is replaced
  by the normal form of `expr j` along the factor's path (`unfoldAll`).

**Soundness** (`nfS_sound`, `zeroLoop_sound`): an atom `.ref j` reads the shared expression's value
(`evalE_ref`), so the value of every normal form at coordinate `i` is the expression's at the path's
entry `i`, and an unfold keeps the difference's value.

The definitions are in `GordieHoweNative/Language/Realizations/SharedNorm.lean`
(the compiled library `GordieHoweNative`); this module has their lemmas.
-/

namespace GordieHowe.RealizedProgram

open Export

/-! ## Soundness -/

section Sound

variable {ir : RealizedProgram} {I : Interp} {rd : ir.Valuation I} {f p : ℕ}

/-- **A factor's value at coordinate `i`**: its atom at its path's entry `i`. -/
def SFac.val (rd : ir.Valuation I) (f i : ℕ) (x : SFac) : (I f).K :=
  ir.evalE rd f x.atom (x.path.getD i 0)

/-- **A monomial's value at coordinate `i`**: its code's cast times its factors' values. -/
def SMono.val (rd : ir.Valuation I) (f i : ℕ) (m : SMono) : (I f).K :=
  (m.coef : (I f).K) * (m.facs.map (SFac.val rd f i)).prod

/-- **A normal form's value at coordinate `i`**: the sum of its monomials' values. -/
def sVal (rd : ir.Valuation I) (f i : ℕ) (q : List SMono) : (I f).K :=
  (q.map (SMono.val rd f i)).sum

theorem sVal_nil (i : ℕ) : sVal rd f i [] = 0 := rfl

theorem sVal_cons (i : ℕ) (m : SMono) (q : List SMono) :
    sVal rd f i (m :: q) = m.val rd f i + sVal rd f i q := by
  simp [sVal]

theorem sVal_append (i : ℕ) (q q' : List SMono) :
    sVal rd f i (q ++ q') = sVal rd f i q + sVal rd f i q' := by
  simp [sVal, List.map_append, List.sum_append]

theorem SFac.val_of (i : ℕ) (ps : List ℕ) (e : Expr) :
    (SFac.of ps e).val rd f i = ir.evalE rd f e (ps.getD i 0) := rfl

/-- **Equal factors have equal values.** -/
theorem SFac.val_of_same {x y : SFac} (h : x.same y = true) (i : ℕ) :
    x.val rd f i = y.val rd f i := by
  simp only [SFac.same, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨-, hp⟩, he⟩ := h
  simp only [SFac.val, hp, Expr.eq_of_beq he]

/-- **Equal factor lists have equal products.** -/
theorem prod_of_sameFacs (i : ℕ) : ∀ {xs ys : List SFac}, sameFacs xs ys = true →
    (xs.map (SFac.val rd f i)).prod = (ys.map (SFac.val rd f i)).prod
  | [], [], _ => rfl
  | x :: xs, y :: ys, h => by
    simp only [sameFacs, Bool.and_eq_true] at h
    simp only [List.map_cons, List.prod_cons, SFac.val_of_same h.1 i, prod_of_sameFacs i h.2]
  | [], _ :: _, h => by simp [sameFacs] at h
  | _ :: _, [], h => by simp [sameFacs] at h

theorem sVal_push (i : ℕ) (m : SMono) (q : List SMono) :
    sVal rd f i (SMono.push m q) = m.val rd f i + sVal rd f i q := by
  unfold SMono.push
  cases h : Nat.beq m.coef 0
  · simp only [Bool.cond_false, sVal_cons]
  · have h0 : m.coef = 0 := Nat.eq_of_beq_eq_true h
    simp [SMono.val, h0]

/-- **The merged sum is the sum.** -/
theorem sVal_sAddF [CharP (I f).K p] (i : ℕ) : ∀ (n : ℕ) (x y : List SMono),
    sVal rd f i (sAddF p n x y) = sVal rd f i x + sVal rd f i y
  | 0, x, y => by simp only [sAddF, sVal_append]
  | _ + 1, [], y => by simp [sAddF, sVal_nil]
  | _ + 1, m :: x, [] => by simp [sAddF, sVal_nil]
  | n + 1, m :: x, m' :: y => by
    have ih := sVal_sAddF i n
    simp only [sAddF]
    split
    · rw [sVal_cons, ih, sVal_cons, sVal_cons]
      ring
    · rw [sVal_cons, ih, sVal_cons, sVal_cons]
      ring
    · cases hs : sameFacs m.facs m'.facs
      · simp only [Bool.cond_false, sVal_cons, ih]
        ring
      · simp only [Bool.cond_true, sVal_push, ih, sVal_cons, SMono.val, natCast_mod_char,
          Nat.cast_add, prod_of_sameFacs i hs]
        ring

theorem sVal_sAdd [CharP (I f).K p] (i : ℕ) (x y : List SMono) :
    sVal rd f i (sAdd p x y) = sVal rd f i x + sVal rd f i y := sVal_sAddF i _ x y

theorem sVal_sScale [CharP (I f).K p] (c i : ℕ) : ∀ q : List SMono,
    sVal rd f i (sScale p c q) = (c : (I f).K) * sVal rd f i q
  | [] => by simp [sScale, sVal_nil]
  | m :: q => by
    rw [sScale, sVal_push, sVal_sScale c i q, sVal_cons]
    simp only [SMono.val, natCast_mod_char, Nat.cast_mul]
    ring

/-- **The merged factor list has the product of both.** -/
theorem prod_mergeFacs (i : ℕ) : ∀ (n : ℕ) (a b : List SFac),
    ((mergeFacs n a b).map (SFac.val rd f i)).prod =
      (a.map (SFac.val rd f i)).prod * (b.map (SFac.val rd f i)).prod
  | 0, a, b => by simp [mergeFacs, List.prod_append]
  | _ + 1, [], b => by simp [mergeFacs]
  | _ + 1, x :: a, [] => by simp [mergeFacs]
  | n + 1, x :: a, y :: b => by
    have ih := prod_mergeFacs i n
    simp only [mergeFacs]
    cases Nat.ble x.key y.key
    · simp only [Bool.cond_false, List.map_cons, List.prod_cons, ih]
      ring
    · simp only [Bool.cond_true, List.map_cons, List.prod_cons, ih]
      ring

theorem SMono.val_mul [CharP (I f).K p] (i : ℕ) (m m' : SMono) :
    (m.mul p m').val rd f i = m.val rd f i * m'.val rd f i := by
  simp only [SMono.val, SMono.mul, natCast_mod_char, Nat.cast_mul, prod_mergeFacs]
  ring

theorem sVal_sPairs [CharP (I f).K p] (i : ℕ) : ∀ xs : List (List SMono),
    ((sPairs p xs).map (sVal rd f i)).sum = (xs.map (sVal rd f i)).sum
  | [] => by simp [sPairs]
  | [x] => by simp [sPairs]
  | x :: y :: r => by
    simp only [sPairs, List.map_cons, List.sum_cons, sVal_sAdd, sVal_sPairs i r]
    ring

theorem sVal_flatten (i : ℕ) : ∀ xs : List (List SMono),
    sVal rd f i xs.flatten = (xs.map (sVal rd f i)).sum
  | [] => rfl
  | x :: xs => by
    rw [List.flatten_cons, sVal_append, sVal_flatten i xs, List.map_cons, List.sum_cons]

theorem sVal_sSumAll [CharP (I f).K p] (i : ℕ) : ∀ (n : ℕ) (xs : List (List SMono)),
    sVal rd f i (sSumAll p n xs) = (xs.map (sVal rd f i)).sum
  | _, [] => by simp [sSumAll, sVal_nil]
  | _, [x] => by simp [sSumAll]
  | 0, x :: y :: r => by simp only [sSumAll, sVal_flatten]
  | n + 1, x :: y :: r => by
    simp only [sSumAll]
    rw [sVal_sSumAll i n, sVal_sPairs]

theorem sVal_sSum [CharP (I f).K p] (i : ℕ) (xs : List (List SMono)) :
    sVal rd f i (sSum p xs) = (xs.map (sVal rd f i)).sum := sVal_sSumAll i _ xs

/-- **The product of normal forms is the product.** -/
theorem sVal_sMul [CharP (I f).K p] (i : ℕ) (x y : List SMono) :
    sVal rd f i (sMul p x y) = sVal rd f i x * sVal rd f i y := by
  have hrow : ∀ m : SMono, ((y.map fun m' => SMono.push (m.mul p m') []).map (sVal rd f i)).sum =
      m.val rd f i * sVal rd f i y := by
    intro m
    induction y with
    | nil => simp [sVal_nil]
    | cons m' y ih =>
      simp only [List.map_cons, List.sum_cons, ih, sVal_push, sVal_nil, SMono.val_mul, sVal_cons]
      ring
  unfold sMul
  rw [sVal_sSum]
  induction x with
  | nil => simp [sVal_nil]
  | cons m x ih =>
    rw [List.flatMap_cons, List.map_append, List.sum_append, ih, hrow, sVal_cons]
    ring

theorem prod_sortFacs (i : ℕ) : ∀ fs : List (List ℕ × Expr),
    ((sortFacs fs).map (SFac.val rd f i)).prod = (fs.map (facVal rd f i)).prod
  | [] => rfl
  | x :: xs => by
    rw [sortFacs, prod_mergeFacs, prod_sortFacs i xs]
    simp [SFac.val_of, facVal]

theorem sVal_ofMonos [CharP (I f).K p] (i : ℕ) (ms : List Mono) :
    sVal rd f i (ofMonos p ms) = monosVal rd f i ms := by
  unfold ofMonos
  rw [sVal_sSum]
  induction ms with
  | nil => rfl
  | cons m ms ih =>
    simp only [List.map_cons, List.sum_cons, ih, sVal_push, sVal_nil, add_zero, monosVal]
    simp [SMono.val, SMono.ofMono, Mono.val, prod_sortFacs]

theorem sVal_sAtom (i : ℕ) (ps : List ℕ) (e : Expr) :
    sVal rd f i (sAtom ps e) = ir.evalE rd f e (ps.getD i 0) := by
  simp [sAtom, sVal, SMono.val, SFac.val_of]

/-- **The normal form is sound**: an expression read at `ps` is, at every coordinate below the
path's length, the value of its normal form. -/
theorem nfS_sound [CharP (I f).K p] (hN : NormModel rd f p) :
    ∀ (k : ℕ) (ps : List ℕ) (e : Expr) (q : List SMono), ir.nfS f p k ps e = some q →
      ∀ i < ps.length, ir.evalE rd f e (ps.getD i 0) = sVal rd f i q
  | 0, _, _, _, h => by simp [nfS] at h
  | k + 1, ps, e, q, h => by
    intro i hi
    have ih := nfS_sound hN k
    cases e with
    | add a b =>
      simp only [nfS, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
        Option.some.injEq] at h
      obtain ⟨x, hx, y, hy, rfl⟩ := h
      rw [evalE_add, sVal_sAdd, ih ps a x hx i hi, ih ps b y hy i hi]
    | sub a b =>
      simp only [nfS, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
        Option.some.injEq] at h
      obtain ⟨x, hx, y, hy, rfl⟩ := h
      rw [evalE_sub, sVal_sAdd, sVal_sScale, ih ps a x hx i hi, ih ps b y hy i hi,
        natCast_intCode hN.pos]
      push_cast
      ring
    | scale c a =>
      cases c with
      | const c =>
        simp only [nfS] at h
        split at h
        · rename_i hc
          obtain ⟨x, hx, rfl⟩ := Option.map_eq_some_iff.1 h
          rw [evalE_scale_const, sVal_sScale, ih ps a x hx i hi, hN.dec c hc]
        · simp only [Option.some.injEq] at h
          subst h
          rw [sVal_sAtom]
      | node v j =>
        simp only [nfS, Option.some.injEq] at h
        subst h
        rw [sVal_sAtom]
    | mul a b =>
      simp only [nfS, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
        Option.some.injEq] at h
      obtain ⟨x, hx, y, hy, rfl⟩ := h
      rw [evalE_mul, sVal_sMul, ih ps a x hx i hi, ih ps b y hy i hi]
    | reindex idx a =>
      simp only [nfS, IndexMap.entriesAt_eq] at h
      have := ih _ a q h i (by simpa using hi)
      rw [evalE_reindex, ← this, getD_map_of_lt _ _ 0 _ hi]
    | concat a b =>
      simp only [nfS] at h
      have hmem := getD_mem_of_lt ps 0 hi
      split at h
      · rename_i ha
        simp only [List.all_eq_true, decide_eq_true_eq] at ha
        rw [evalE_concat]
        simp only [ha _ hmem, ↓reduceIte]
        exact ih ps a q h i hi
      · split at h
        · rename_i _ hb
          simp only [List.all_eq_true, decide_eq_true_eq] at hb
          have := ih _ b q h i (by simpa using hi)
          have hn : ¬ps.getD i 0 < ir.exprLen a := by
            have := hb _ hmem
            omega
          rw [evalE_concat]
          simp only [hn, ↓reduceIte]
          rw [← this, getD_map_of_lt _ _ 0 _ hi]
        · simp only [Option.some.injEq] at h
          subst h
          rw [sVal_sAtom]
    | ref j =>
      simp only [nfS, Option.some.injEq] at h
      subst h
      rw [sVal_sAtom]
    | leaf u =>
      simp only [nfS, Option.some.injEq] at h
      subst h
      rw [sVal_ofMonos]
      exact nfLeaf_sound hN u ps hi
    | apply op x =>
      simp only [nfS, Option.some.injEq] at h
      subst h
      rw [sVal_ofMonos]
      exact nfApply_sound (ir := ir) op x ps hi
    | linear rows a | prod w a | mux b t a | logic op w args =>
      simp only [nfS, Option.some.injEq] at h
      subst h
      rw [sVal_sAtom]

theorem SFac.of_isRefAt {L j : ℕ} {x : SFac} (h : x.isRefAt L j = true) :
    x.atom = .ref j ∧ L ≤ x.path.length := by
  unfold SFac.isRefAt at h
  split at h
  · rename_i j' hj'
    simp only [Bool.and_eq_true, Nat.beq_eq, Nat.ble_eq] at h
    exact ⟨h.1 ▸ hj', h.2⟩
  · cases h

/-- **An unfolded factor list has the factors' product**, at every coordinate below `L`. -/
theorem unfoldFacs_sound [CharP (I f).K p] (hN : NormModel rd f p) {k L j : ℕ}
    (hj : j < ir.exprs.length) {i : ℕ} (hi : i < L) : ∀ (xs : List SFac) (r : List SMono),
      ir.unfoldFacs f p k L j xs = some r → sVal rd f i r = (xs.map (SFac.val rd f i)).prod
  | [], r, h => by
    simp only [unfoldFacs, Option.some.injEq] at h
    subst h
    simp [sVal, SMono.val, natCast_mod_char]
  | x :: xs, r, h => by
    simp only [unfoldFacs] at h
    split at h
    · cases h
    · rename_i r₀ h₀
      have ih := unfoldFacs_sound hN hj hi xs r₀ h₀
      rw [List.map_cons, List.prod_cons, ← ih]
      cases hx : x.isRefAt L j
      · simp only [hx, Bool.cond_false, Option.some.injEq] at h
        subst h
        rw [sVal_sMul]
        simp [sVal, SMono.val, natCast_mod_char]
      · simp only [hx, Bool.cond_true] at h
        obtain ⟨e, he, rfl⟩ := Option.map_eq_some_iff.1 h
        obtain ⟨hxa, hxl⟩ := SFac.of_isRefAt hx
        rw [sVal_sMul, ← nfS_sound hN k x.path (ir.expr j) e he i (by omega)]
        simp only [SFac.val, hxa, evalE_ref hN.ordered rd f hj]

theorem unfoldMono_sound [CharP (I f).K p] (hN : NormModel rd f p) {k L j : ℕ}
    (hj : j < ir.exprs.length) {i : ℕ} (hi : i < L) (m : SMono) {r : List SMono}
    (h : ir.unfoldMono f p k L j m = some r) : sVal rd f i r = m.val rd f i := by
  unfold unfoldMono at h
  cases hm : m.facs.any (SFac.isRefAt L j)
  · simp only [hm, Bool.cond_false, Option.some.injEq] at h
    subst h
    simp [sVal]
  · simp only [hm, Bool.cond_true] at h
    obtain ⟨r₀, h₀, rfl⟩ := Option.map_eq_some_iff.1 h
    rw [sVal_sScale, unfoldFacs_sound hN hj hi _ r₀ h₀]
    rfl

theorem unfoldAll_sound [CharP (I f).K p] (hN : NormModel rd f p) {k L j : ℕ}
    (hj : j < ir.exprs.length) {i : ℕ} (hi : i < L) : ∀ (D : List SMono) (rs : List (List SMono)),
      ir.unfoldAll f p k L j D = some rs → (rs.map (sVal rd f i)).sum = sVal rd f i D
  | [], rs, h => by
    simp only [unfoldAll, Option.some.injEq] at h
    subst h
    rfl
  | m :: D, rs, h => by
    simp only [unfoldAll] at h
    split at h
    · rename_i a b ha hb
      simp only [Option.some.injEq] at h
      subst h
      rw [List.map_cons, List.sum_cons, unfoldMono_sound hN hj hi m ha,
        unfoldAll_sound hN hj hi D b hb, sVal_cons]
    · cases h

/-- **The zero check is sound**: a normal form it accepts is zero at every coordinate below `L`. -/
theorem zeroLoop_sound [CharP (I f).K p] (hN : NormModel rd f p) {k L : ℕ} :
    ∀ (n : ℕ) (D : List SMono), ir.zeroLoop f p k L n D = true →
      ∀ i < L, sVal rd f i D = 0
  | 0, D, h, i, _ => by
    simp only [zeroLoop, List.isEmpty_iff] at h
    subst h
    rfl
  | n + 1, D, h, i, hi => by
    simp only [zeroLoop, Bool.or_eq_true, List.isEmpty_iff, Bool.and_eq_true, Nat.blt_eq,
      Nat.ble_eq] at h
    rcases h with h | ⟨⟨h0, hle⟩, h⟩
    · subst h
      rfl
    · split at h
      · rename_i rs hrs
        rw [← unfoldAll_sound hN (by omega) hi D rs hrs, ← sVal_sSum]
        exact zeroLoop_sound hN n _ h i hi
      · cases h

end Sound

end GordieHowe.RealizedProgram
