-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Language.Honest.Digits
public import GordieHowe.Foundations.Probability.PackingCollision

@[expose] public section

/-!
# Tables packed at a challenge

`assert_in` (`lib/gordiehowe/compiler/assert_in.h`) packs a table of records of `A ≥ 2` columns at
the powers `in.powers:<D> = (1, γ, …, γ^(A−1))` of a challenge `in.gamma:<D>`: the table's rows and
its requests' needles are `linear rows b` with row `j` of `rows` the pairs `(A j + c, node P c)`,
`c < A`, `P` the powers' value (`packRows`, `packOf?`, `gammaPack?`): coordinate `j` is
`Σ_c P_c · b_{A j + c}`, the record `(b_{A j}, …, b_{A j + A − 1})` (`tupleOf`) packed at the
powers (`packWith`, `evalE_packRows`). A table packed at a constant `κ` has constant coefficients
and is no such table.

The honest prover counts the records (`lib::table::table_internal::first_match_counts`). Its
counts are the honest counts of the packed rows wherever the packing is injective on the table's
records (`rowHistogram_map_of_injOn`), which the source execution ensures off its completeness
events (`PackFreeAt`, `GordieHowe.RealizedProgram.SourceExecutionCore.packFree`): a program with
no such table ensures it always (`packFreeAt_of_noGamma`), and an application with one charges the
collision event to its completeness error (`GordieHowe.prob_packCollision_le`).
-/

namespace GordieHowe.RealizedProgram

open Range

section

variable {ir : RealizedProgram} {I : Interp}

/-- **The rows of a packed expression** of `n` records of `A` columns, packed at the coordinates
of value `P`: row `j` is `[(A j + c, node P c) | c < A]`. -/
def packRows (A P n : ℕ) : List (List (ℕ × Coef)) :=
  (List.range n).map fun j => (List.range A).map fun c => (A * j + c, Coef.node P c)

/-- **An expression packed at the coordinates of a value** (`packRows`): `linear rows b` with
records of `A ≥ 2` columns at the value `P`, read off its first coefficient; the powers' value
`P`, the arity `A` and the records' expression `b`. -/
def packOf? : Expr → Option (ℕ × ℕ × Expr)
  | .linear rows b =>
    match rows with
    | ((_, .node P _) :: r0) :: _ =>
      if 2 ≤ r0.length + 1 ∧ rows = packRows (r0.length + 1) P rows.length then
        some (P, r0.length + 1, b)
      else none
    | _ => none
  | _ => none

/-- **A packed expression is `linear (packRows A P n) b`** for some `n`, with `2 ≤ A`. -/
theorem eq_of_packOf? {e : Expr} {P A : ℕ} {b : Expr} (h : packOf? e = some (P, A, b)) :
    2 ≤ A ∧ ∃ n, e = .linear (packRows A P n) b := by
  unfold packOf? at h
  split at h
  · rename_i rows b'
    split at h
    · rename_i x P' y r0 rest
      split_ifs at h with hc
      · simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl, rfl⟩ := h
        exact ⟨hc.1, _, by rw [← hc.2]⟩
    · cases h
  · cases h

variable (ir) in
/-- **Table `t` is packed at a value**: its rows are a packed expression (`packOf?`). -/
def gammaPack? (t : ℕ) : Option (ℕ × ℕ × Expr) :=
  match (ir.table t).rows with
  | .expr e' => packOf? e'
  | _ => none

variable (ir) in
/-- **The records' expression of member `m`'s needle** packed at the value `P` with `A` columns,
when its needle is one. -/
def memberBase? (P A : ℕ) (m : Member) : Option Expr :=
  match packOf? (ir.needleExpr m.pred m.needle) with
  | some (P', A', b) => if P' = P ∧ A' = A then some b else none
  | none => none

variable (ir) in
/-- **The record at coordinate `i`** of `A` columns of the expression `b`, read by `rd` in field
`f`: `(b_{A i}, …, b_{A i + A − 1})`. -/
def tupleOf (rd : ir.Valuation I) (f A : ℕ) (b : Expr) (i : ℕ) : List (I f).K :=
  (List.range A).map fun c => ir.evalE rd f b (A * i + c)

theorem length_tupleOf (rd : ir.Valuation I) (f A : ℕ) (b : Expr) (i : ℕ) :
    (ir.tupleOf rd f A b i).length = A := by
  simp [tupleOf]

/-- **A coordinate of a packed expression is its record packed at the powers' value**, read in the
field `f`. -/
theorem evalE_packRows (rd : ir.Valuation I) (f A P n : ℕ) (b : Expr) {j : ℕ} (hj : j < n) :
    ir.evalE rd f (.linear (packRows A P n) b) j =
      packWith (fun c => (castElt (rd P c) : (I f).K)) (ir.tupleOf rd f A b j) := by
  simp only [evalE, Expr.eval, packRows, packWith, length_tupleOf]
  rw [List.getD_eq_getElem _ _ (by simpa using hj), List.getElem_map, List.getElem_range,
    List.map_map]
  refine congrArg List.sum (List.map_congr_left fun c hc => ?_)
  simp only [Function.comp, Coef.eval]
  congr 1
  rw [List.mem_range] at hc
  simp [tupleOf, List.getD_eq_getElem?_getD, List.getElem?_range hc, evalE]

theorem length_packRows (A P n : ℕ) : (packRows A P n).length = n := by
  simp [packRows]

/-- **A row of a packed table is its record packed at the powers' value.** -/
theorem tableRow_of_gammaPack {t P A : ℕ} {b : Expr} (h : ir.gammaPack? t = some (P, A, b))
    (rd : ir.Valuation I) (f : ℕ) (j : Fin (ir.tableSize t)) :
    ir.tableRow rd f t j =
      packWith (fun c => (castElt (rd P c) : (I f).K)) (ir.tupleOf rd f A b j) := by
  have hj := j.isLt
  unfold gammaPack? at h
  unfold tableRow
  unfold tableSize at hj
  split at h
  · rename_i e' hr
    obtain ⟨-, n, rfl⟩ := eq_of_packOf? h
    simp only [hr] at hj ⊢
    simp only [exprLen, Expr.len, length_packRows] at hj
    exact evalE_packRows rd f A P n b hj
  · cases h

/-- **The records of the rows of table `t`**, packed with `A` columns of `b`, read by `rd`. -/
def rowTuples (rd : ir.Valuation I) (t A : ℕ) (b : Expr) : List (List (I (ir.chalField (ir.alphaOf t))).K) :=
  (List.range (ir.tableSize t)).map (ir.tupleOf rd (ir.chalField (ir.alphaOf t)) A b)

/-- **The records of member `m`'s needle** packed at `P` with `A` columns, read by `rd` in field
`f`: one per coordinate of the member; none for a needle not so packed. -/
def memberTuples (rd : ir.Valuation I) (f P A : ℕ) (m : Member) : List (List (I f).K) :=
  match ir.memberBase? P A m with
  | some b => (List.range m.count).map fun c => ir.tupleOf rd f A b (m.first + c)
  | none => []

/-- **The records of table `t` packed at a value**: its rows' and its groups' members' records;
none for a table not so packed. -/
def packTuples (rd : ir.Valuation I) (t : ℕ) : List (List (I (ir.chalField (ir.alphaOf t))).K) :=
  match ir.gammaPack? t with
  | some (P, A, b) => ir.rowTuples rd t A b ++
      (List.range (ir.groupCountOf t)).flatMap fun g =>
        (ir.members t g).flatMap (ir.memberTuples rd (ir.chalField (ir.alphaOf t)) P A)
  | none => []

/-- **A packed member's needles are its records packed at the powers' value**, its coordinates
within its needle's length. -/
theorem memberVals_of_memberBase {P A : ℕ} {m : Member} {b : Expr}
    (h : ir.memberBase? P A m = some b)
    (hfit : m.first + m.count ≤ ir.exprLen (ir.needleExpr m.pred m.needle))
    (rd : ir.Valuation I) (f : ℕ) :
    ir.memberVals rd f m =
      (ir.memberTuples rd f P A m).map (packWith fun c => (castElt (rd P c) : (I f).K)) := by
  have hb := h
  unfold memberBase? at h
  split at h
  · rename_i P' A' b' hp
    split_ifs at h with hPA
    obtain ⟨rfl, rfl⟩ := hPA
    simp only [Option.some.injEq] at h
    subst h
    obtain ⟨-, n, hn⟩ := eq_of_packOf? hp
    simp only [memberTuples, hb, memberVals, List.map_map]
    refine List.map_congr_left fun c hc => ?_
    rw [List.mem_range] at hc
    rw [hn] at hfit ⊢
    simp only [exprLen, Expr.len, length_packRows] at hfit
    exact evalE_packRows rd f _ _ n b' (by omega)
  · cases h

variable (ir I) in
/-- **The packing of every packed table is injective on its records** in the environment `e`:
two of its records with equal packings at its powers' value are equal. The completeness
obligation of the source execution for a program with tables packed at a challenge
(`SourceExecutionCore.packFree`). -/
def PackFreeAt (e : ir.Env I) : Prop :=
  ∀ t < ir.tables.length, ∀ P A b, ir.gammaPack? t = some (P, A, b) →
    ∀ a ∈ ir.packTuples (ir.reader e) t, ∀ a' ∈ ir.packTuples (ir.reader e) t,
      packWith (fun c => (castElt (ir.reader e P c) : (I (ir.chalField (ir.alphaOf t))).K)) a =
        packWith (fun c => castElt (ir.reader e P c)) a' → a = a'

variable (ir) in
/-- **No table is packed at a value.** -/
def NoGammaTables : Prop := ∀ t < ir.tables.length, ir.gammaPack? t = none

instance : Decidable ir.NoGammaTables := by
  unfold NoGammaTables
  infer_instance

/-- **A program with no table packed at a value has injective packings** in every environment. -/
theorem packFreeAt_of_noGamma (h : ir.NoGammaTables) (e : ir.Env I) : ir.PackFreeAt I e := by
  intro t ht P A b hp
  rw [h t ht] at hp
  cases hp

/-! ## A challenge coordinate at a uniform phase challenge -/

open IOP in
open IOP in
/-! ## The honest counts of packed records -/

variable {K : Type*} [Field K] [DecidableEq K] {L : Type*} [DecidableEq L] [BEq L] [LawfulBEq L]

omit [Field K] in
/-- **A list's count through a map injective on it and the counted element.** -/
theorem count_map_of_injOn (f : L → K) {x : L} : ∀ {l : List L},
    (∀ a ∈ x :: l, ∀ a' ∈ x :: l, f a = f a' → a = a') → (l.map f).count (f x) = l.count x
  | [], _ => rfl
  | a :: l, h => by
    rw [List.map_cons, List.count_cons, List.count_cons,
      count_map_of_injOn f fun u hu u' hu' => h u (by
        rcases List.mem_cons.1 hu with rfl | hu
        · exact List.mem_cons_self
        · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hu)) u' (by
        rcases List.mem_cons.1 hu' with rfl | hu'
        · exact List.mem_cons_self
        · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hu'))]
    congr 1
    by_cases hax : a = x
    · subst hax
      simp
    · have : f a ≠ f x := fun he => hax (h a (List.mem_cons_of_mem _ List.mem_cons_self) x
        List.mem_cons_self he)
      simp [hax, this]

/-- **The honest counts of packed rows are the records' counts** (`rowHistogram`, the C++
`first_match_counts` on the records) when the packing `f` is injective on the rows' records `r`
and the needles' records `ns`: at a first occurrence of a record among the rows, the number of
needles equal to it, `0` at a repeat. -/
theorem rowHistogram_map_of_injOn {T : ℕ} (f : L → K) (r : Fin T → L) (ns : List L)
    (h : ∀ a, (a ∈ ns ∨ ∃ k, r k = a) → ∀ a', (a' ∈ ns ∨ ∃ k, r k = a') → f a = f a' → a = a')
    (j : Fin T) :
    rowHistogram (fun k => f (r k)) (ns.map f) j =
      (((if ∀ k : Fin T, k < j → r k ≠ r j then ns.count (r j) else 0 : ℕ)) : K) := by
  unfold rowHistogram
  have hfo : (∀ k : Fin T, k < j → f (r k) ≠ f (r j)) ↔ ∀ k : Fin T, k < j → r k ≠ r j :=
    ⟨fun hk k hkj he => hk k hkj (congrArg f he), fun hk k hkj he =>
      hk k hkj (h _ (.inr ⟨k, rfl⟩) _ (.inr ⟨j, rfl⟩) he)⟩
  by_cases hf : ∀ k : Fin T, k < j → r k ≠ r j
  · rw [if_pos (hfo.2 hf), if_pos hf, count_map_of_injOn f fun a ha a' ha' => h a (by
      rcases List.mem_cons.1 ha with rfl | ha
      · exact .inr ⟨j, rfl⟩
      · exact .inl ha) a' (by
      rcases List.mem_cons.1 ha' with rfl | ha'
      · exact .inr ⟨j, rfl⟩
      · exact .inl ha')]
  · rw [if_neg (fun h' => hf (hfo.1 h')), if_neg hf, Nat.cast_zero]

end

end GordieHowe.RealizedProgram
