-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import LatticeCrypto.MLDSA.Concrete.NTT
import all LatticeCrypto.MLDSA.Concrete.NTT
import all GordieHowe.Applications.MLDSA44.Spec.NTT
import Init.Internal.Order.While

/-!
# The vendored ML-DSA NTT loop kernels equal the structural definitions

`MLDSA.Concrete.ntt`, `invNTT` and `multiplyNTTs` (vendored in
`Vendor/LatticeCrypto/MLDSA/Concrete/NTT.lean`) are defined from eight certified butterfly
stages and run through `@[implemented_by]` as the loop kernels `loopNTT`, `loopInvNTT` and
`loopMultiplyNTTs` (FIPS 204 Algorithms 41, 42 and 47). This file proves each pair equal
(`ntt_eq_loopNTT`, `invNTT_eq_loopInvNTT`, `multiplyNTTs_eq_loopMultiplyNTTs`), so compiled
code and proofs compute the same functions.

Proof: a `while` loop in `Id` unfolds one step at a time (`Lean.Loop.forIn_eq_of_monadTail`) and
a `for` loop is a `List.foldl`. One block of butterflies changes exactly the two halves of the
block (`block_fold`); the inner `while` over blocks then computes one stage pointwise
(`inner_run`), and that stage is `nttStage s` read through the array (`fwd_stageT`,
`inv_stageT`). The outer `while` runs the stages in order. Pointwise multiplication follows from
`ntt_get`: evaluation at a root of `x^256 + 1` sends the negacyclic product to the product of
evaluations.
-/

namespace GordieHowe.MLDSA44.NTTLoop

open _root_.MLDSA _root_.MLDSA.Concrete

/-! ## Arrays and loops -/

theorem getZ_set (a : Array Coeff) (p i : ℕ) (x : Coeff) :
    getZ (a.set! p x) i = if p = i ∧ p < a.size then x else getZ a i := by
  unfold getZ
  rw [Array.getD_eq_getD_getElem?, Array.getD_eq_getD_getElem?, Array.set!,
    Array.getElem?_setIfInBounds]
  by_cases h1 : p = i
  · subst h1
    by_cases h2 : p < a.size
    · simp [h2]
    · simp [h2]
  · simp [h1]

theorem size_set (a : Array Coeff) (p : ℕ) (x : Coeff) : (a.set! p x).size = a.size := by
  simp

/-- One step of a `while` loop in `Id`. -/
theorem loop_unfold {β : Type} (b : β) (f : Unit → β → Id (ForInStep β)) :
    (forIn Lean.Loop.mk b f : Id β) = match (f () b).run with
      | .done v => pure v
      | .yield v => forIn Lean.Loop.mk v f := by
  rw [show (forIn Lean.Loop.mk b f : Id β) = Lean.Loop.forIn Lean.Loop.mk b f from rfl,
    Lean.Loop.forIn_eq_of_monadTail]
  rfl

theorem iterate_succ_eq (n m : ℕ) : (fun k : ℕ => k + 1)^[n] m = m + n := by
  induction n generalizing m with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply, ih]; omega

theorem iterate_pred_eq (n m : ℕ) : (fun k : ℕ => k - 1)^[n] m = m - n := by
  induction n generalizing m with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply, ih]; omega

/-! ## One block of butterflies -/

/-- The forward butterfly at `j` (Algorithm 41, inner body). -/
def fwdJ (z : Coeff) (len : ℕ) (b : Array Coeff) (j : ℕ) : Array Coeff :=
  (b.set! (j + len) (getZ b j - z * getZ b (j + len))).set! j (getZ b j + z * getZ b (j + len))

/-- The inverse butterfly at `j` (Algorithm 42, inner body). -/
def invJ (z : Coeff) (len : ℕ) (b : Array Coeff) (j : ℕ) : Array Coeff :=
  (b.set! j (getZ b j + getZ b (j + len))).set! (j + len) (z * (getZ b j - getZ b (j + len)))

/-- A butterfly `bf z L b j` writes `F z u v` at `j` and `G z u v` at `j + L`, where
`u, v` are the entries at `j` and `j + L`, and keeps every other entry. -/
def BflySpec (bf : Coeff → ℕ → Array Coeff → ℕ → Array Coeff)
    (F G : Coeff → Coeff → Coeff → Coeff) : Prop :=
  ∀ z L b j i, 0 < L → j + L < b.size →
    (bf z L b j).size = b.size ∧
    getZ (bf z L b j) i = if i = j then F z (getZ b j) (getZ b (j + L))
      else if i = j + L then G z (getZ b j) (getZ b (j + L)) else getZ b i

theorem fwdJ_spec : BflySpec fwdJ (fun z u v => u + z * v) (fun z u v => u - z * v) := by
  intro z L b j i hL hj
  refine ⟨by simp [fwdJ], ?_⟩
  have hj' : j < b.size := by omega
  simp only [fwdJ, getZ_set, size_set]
  by_cases h1 : i = j
  · subst h1; simp [hj']
  · by_cases h2 : i = j + L
    · subst h2; simp [hj, hL.ne']
    · simp [h1, h2, Ne.symm h1, Ne.symm h2]

theorem invJ_spec : BflySpec invJ (fun _ u v => u + v) (fun z u v => z * (u - v)) := by
  intro z L b j i hL hj
  refine ⟨by simp [invJ], ?_⟩
  have hj' : j < b.size := by omega
  simp only [invJ, getZ_set, size_set]
  by_cases h1 : i = j
  · subst h1; simp [hj', hL.ne']
  · by_cases h2 : i = j + L
    · subst h2; simp [hj, hL.ne']
    · simp [h1, h2, Ne.symm h1, Ne.symm h2]

/-- Running the butterflies at `start, …, start + m - 1` rewrites `[start, start + m)` and
`[start + L, start + L + m)` from the input and keeps the rest. -/
theorem block_fold {bf : Coeff → ℕ → Array Coeff → ℕ → Array Coeff}
    {F G : Coeff → Coeff → Coeff → Coeff} (hs : BflySpec bf F G) (z : Coeff) {L start : ℕ}
    (hL : 0 < L) (b : Array Coeff) (hb : start + 2 * L ≤ b.size) :
    ∀ m ≤ L, (List.foldl (fun c j => bf z L c j) b (List.range' start m)).size = b.size ∧
      ∀ i, getZ (List.foldl (fun c j => bf z L c j) b (List.range' start m)) i =
        if start ≤ i ∧ i < start + m then F z (getZ b i) (getZ b (i + L))
        else if start + L ≤ i ∧ i < start + L + m then G z (getZ b (i - L)) (getZ b i)
        else getZ b i
  | 0, _ => by
    refine ⟨rfl, fun i => ?_⟩
    rw [ite_eq_right (by omega), ite_eq_right (by omega)]
    rfl
  | m + 1, hm => by
    obtain ⟨ih1, ih2⟩ := block_fold hs z hL b hb m (by omega)
    rw [List.range'_concat, List.foldl_append]
    simp only [List.foldl_cons, List.foldl_nil, Nat.one_mul]
    have hsz : start + m + L <
        (List.foldl (fun c j => bf z L c j) b (List.range' start m)).size := by
      rw [ih1]; omega
    refine ⟨by rw [(hs z L _ (start + m) 0 hL hsz).1, ih1], fun i => ?_⟩
    rw [(hs z L _ (start + m) i hL hsz).2, ih2, ih2, ih2]
    have hX : (if start ≤ start + m ∧ start + m < start + m then
        F z (getZ b (start + m)) (getZ b (start + m + L))
      else if start + L ≤ start + m ∧ start + m < start + L + m then
        G z (getZ b (start + m - L)) (getZ b (start + m))
      else getZ b (start + m)) = getZ b (start + m) := by
      rw [ite_eq_right (by omega), ite_eq_right (by omega)]
    have hY : (if start ≤ start + m + L ∧ start + m + L < start + m then
        F z (getZ b (start + m + L)) (getZ b (start + m + L + L))
      else if start + L ≤ start + m + L ∧ start + m + L < start + L + m then
        G z (getZ b (start + m + L - L)) (getZ b (start + m + L))
      else getZ b (start + m + L)) = getZ b (start + m + L) := by
      rw [ite_eq_right (by omega), ite_eq_right (by omega)]
    rw [hX, hY]
    by_cases h1 : i = start + m
    · subst h1
      rw [ite_eq_left rfl, ite_eq_left (by omega)]
    · by_cases h2 : i = start + m + L
      · subst h2
        rw [ite_eq_right h1, ite_eq_left rfl, ite_eq_right (by omega), ite_eq_left (by omega),
          Nat.add_sub_cancel]
      · rw [ite_eq_right h1, ite_eq_right h2]
        split_ifs <;> first | rfl | omega

/-! ## One stage: the `while` loop over blocks -/

/-- The body of the inner `while` loop of Algorithms 41 and 42: one block of butterflies with
the twiddle `zOf k`, then `k := kNext k` and `start := start + 2·len`. -/
def innerBody (zOf : ℕ → Coeff) (kNext : ℕ → ℕ)
    (bf : Coeff → ℕ → Array Coeff → ℕ → Array Coeff) (len : ℕ) :
    Unit → Array Coeff × ℕ × ℕ → Id (ForInStep (Array Coeff × ℕ × ℕ)) := fun _ s =>
  if s.2.2 < ringDegree then
    pure (.yield (List.foldl (fun c j => bf (zOf s.2.1) len c j) s.1 (List.range' s.2.2 len),
      kNext s.2.1, s.2.2 + 2 * len))
  else pure (.done s)

/-- The entry at `i` after one stage with block length `2·L`, read from the input `a0`. -/
def stageT (F G : Coeff → Coeff → Coeff → Coeff) (zOf : ℕ → Coeff) (kNext : ℕ → ℕ)
    (k0 L : ℕ) (a0 : Array Coeff) (i : ℕ) : Coeff :=
  if i % (2 * L) < L then F (zOf (kNext^[i / (2 * L)] k0)) (getZ a0 i) (getZ a0 (i + L))
  else G (zOf (kNext^[i / (2 * L)] k0)) (getZ a0 (i - L)) (getZ a0 i)

theorem div_mod_of_block {i g D : ℕ} (hlo : g * D ≤ i) (hhi : i < g * D + D) :
    i / D = g ∧ i % D = i - g * D := by
  have hD : 0 < D := by omega
  have hdiv : i / D = g := Nat.div_eq_of_lt_le
    hlo (by rw [Nat.succ_mul]; omega)
  refine ⟨hdiv, ?_⟩
  have := Nat.div_add_mod i D
  rw [hdiv] at this
  rw [Nat.mul_comm] at this
  omega

/-- The inner `while` loop of Algorithms 41 and 42 computes one stage. -/
theorem inner_run {bf : Coeff → ℕ → Array Coeff → ℕ → Array Coeff}
    {F G : Coeff → Coeff → Coeff → Coeff} (hs : BflySpec bf F G) (zOf : ℕ → Coeff)
    (kNext : ℕ → ℕ) (k0 : ℕ) {L N : ℕ} (hL : 0 < L) (hN : N * (2 * L) = 256)
    (a0 : Array Coeff) :
    ∀ r g (b : Array Coeff), g + r = N → b.size = 256 →
      (∀ i < 256, getZ b i = if i < g * (2 * L) then stageT F G zOf kNext k0 L a0 i
        else getZ a0 i) →
      (Id.run (forIn Lean.Loop.mk (b, kNext^[g] k0, g * (2 * L))
          (innerBody zOf kNext bf L))).1.size = 256 ∧
      (∀ i < 256, getZ (Id.run (forIn Lean.Loop.mk (b, kNext^[g] k0, g * (2 * L))
          (innerBody zOf kNext bf L))).1 i = stageT F G zOf kNext k0 L a0 i) ∧
      (Id.run (forIn Lean.Loop.mk (b, kNext^[g] k0, g * (2 * L))
          (innerBody zOf kNext bf L))).2.1 = kNext^[N] k0
  | 0, g, b, hg, hb, hrep => by
    rw [loop_unfold]
    have hstop : ¬ g * (2 * L) < ringDegree := by
      rw [show ringDegree = 256 from rfl, ← hN, Nat.add_zero] at *
      rw [hg]; omega
    simp only [innerBody, ite_eq_right hstop, Id.run_pure]
    refine ⟨hb, fun i hi => ?_, by rw [Nat.add_zero] at hg; rw [hg]⟩
    rw [hrep i hi, ite_eq_left]
    rw [Nat.add_zero] at hg
    rw [hg, hN]; exact hi
  | r + 1, g, b, hg, hb, hrep => by
    rw [loop_unfold]
    have hM : g * (2 * L) + 2 * L ≤ 256 := by
      rw [← hN, ← hg, show (g + (r + 1)) * (2 * L) = g * (2 * L) + 2 * L + r * (2 * L) by ring]
      omega
    have hgo : g * (2 * L) < ringDegree := by
      show g * (2 * L) < 256; omega
    simp only [innerBody, ite_eq_left hgo, Id.run_pure]
    have hstep : kNext (kNext^[g] k0) = kNext^[g + 1] k0 := by
      rw [Function.iterate_succ_apply']
    have hstart : g * (2 * L) + 2 * L = (g + 1) * (2 * L) := by ring
    change (Id.run (forIn Lean.Loop.mk (List.foldl (fun c j => bf (zOf (kNext^[g] k0)) L c j) b
        (List.range' (g * (2 * L)) L), kNext (kNext^[g] k0), g * (2 * L) + 2 * L)
        (innerBody zOf kNext bf L))).1.size = 256 ∧ _ ∧ _
    rw [hstep, hstart]
    obtain ⟨hsz, hget⟩ := block_fold hs (zOf (kNext^[g] k0)) hL b
      (start := g * (2 * L)) (by omega) L le_rfl
    refine inner_run hs zOf kNext k0 hL hN a0 r (g + 1) _ (by omega) (by rw [hsz, hb])
      (fun i hi => ?_)
    rw [hget i]
    by_cases hlow : i < g * (2 * L)
    · rw [ite_eq_right (by omega), ite_eq_right (by omega), hrep i hi, ite_eq_left hlow,
        ite_eq_left (by rw [← hstart]; omega)]
    · by_cases hin : i < (g + 1) * (2 * L)
      · rw [ite_eq_left hin]
        rw [← hstart] at hin
        obtain ⟨hdiv, hmod⟩ := div_mod_of_block (not_lt.mp hlow) hin
        unfold stageT
        rw [hdiv, hmod]
        by_cases hleft : i < g * (2 * L) + L
        · rw [ite_eq_left ⟨not_lt.mp hlow, hleft⟩, ite_eq_left (by omega), hrep i hi,
            ite_eq_right hlow,
            hrep (i + L) (by omega), ite_eq_right (by omega)]
        · rw [ite_eq_right (by omega), ite_eq_left ⟨by omega, by omega⟩, ite_eq_right (by omega),
            hrep (i - L) (by omega), ite_eq_right (by omega), hrep i hi, ite_eq_right hlow]
      · rw [ite_eq_right hin, ite_eq_right (by omega), ite_eq_right (by omega), hrep i hi,
          ite_eq_right hlow]

/-! ## The forward NTT -/

/-- `a` has length 256 and holds the coefficient function `v`. -/
def Rep (a : Array Coeff) (v : Fin polyBackend.degree → Coeff) : Prop :=
  a.size = 256 ∧ ∀ i : Fin polyBackend.degree, getZ a i = v i

theorem len_pos (s : Fin 8) : 0 < 128 / 2 ^ s.val := by
  revert s; decide

theorem len_half (s : Fin 8) : 128 / 2 ^ s.val / 2 = 128 / 2 ^ (s.val + 1) := by
  revert s; decide

theorem len_double (s : Fin 7) : 128 / 2 ^ (s.val + 1) * 2 = 128 / 2 ^ s.val := by
  revert s; decide

theorem groups_shape (s : Fin 8) : 2 ^ s.val * (2 * (128 / 2 ^ s.val)) = 256 := by
  revert s; decide

theorem drop_nttStages (s : Fin 8) :
    nttStages.drop s.val = nttStage s :: nttStages.drop (s.val + 1) := by
  fin_cases s <;> rfl

/-- In stage `s` a coordinate lies in one of the `2^s` blocks. -/
theorem block_lt (s : Fin 8) (i : Fin polyBackend.degree) :
    i.val / (2 * (128 / 2 ^ s.val)) < 2 ^ s.val := by
  apply Nat.div_lt_of_lt_mul
  rw [Nat.mul_comm, groups_shape s]
  exact i.isLt

theorem fwd_stageT (s : Fin 8) {a : Array Coeff} {v : Fin polyBackend.degree → Coeff}
    (h : Rep a v) (i : Fin polyBackend.degree) :
    stageT (fun z u v => u + z * v) (fun z u v => u - z * v) (getZ zetaTable) (fun k => k + 1)
      (2 ^ s.val) (128 / 2 ^ s.val) a i = (nttStage s).forward v i := by
  set L := 128 / 2 ^ s.val with hL
  let g : Fin (2 ^ s.val) := ⟨i.val / (2 * L), block_lt s i⟩
  have hdm := Nat.div_add_mod' i.val (2 * L)
  have hmod := Nat.mod_lt i.val (show 0 < 2 * L by have := len_pos s; omega)
  have hz : getZ zetaTable ((fun k => k + 1)^[i.val / (2 * L)] (2 ^ s.val)) =
      zeta ^ bitRev8 (2 ^ s.val + g.val) := by
    rw [iterate_succ_eq]
    exact getZ_zetaTable _ (layer_twiddle_index_bounds s g).1
  unfold stageT
  rw [hz]
  by_cases ho : i.val % (2 * L) < L
  · let o : Fin L := ⟨i.val % (2 * L), ho⟩
    have hl : (layerLayout s).equiv ((g, o), false) = i := Fin.ext (by
      rw [NTTEval.layerLayout_left_val]; exact hdm)
    have hr : ((layerLayout s).equiv ((g, o), true)).val = i.val + L := by
      rw [NTTEval.layerLayout_right_val]
      change i.val / (2 * L) * (2 * L) + L + i.val % (2 * L) = _; omega
    rw [ite_eq_left ho]
    conv_rhs => rw [← hl, NTTEval.stage_left s v g o, hl]
    rw [h.2 i, ← hr, h.2]
  · have ho' : i.val % (2 * L) - L < L := by omega
    let o : Fin L := ⟨i.val % (2 * L) - L, ho'⟩
    have hr : (layerLayout s).equiv ((g, o), true) = i := Fin.ext (by
      rw [NTTEval.layerLayout_right_val]; change g.val * (2 * L) + L + o.val = _
      change i.val / (2 * L) * (2 * L) + L + (i.val % (2 * L) - L) = _; omega)
    have hl : ((layerLayout s).equiv ((g, o), false)).val = i.val - L := by
      rw [NTTEval.layerLayout_left_val]
      change i.val / (2 * L) * (2 * L) + (i.val % (2 * L) - L) = _; omega
    rw [ite_eq_right ho]
    conv_rhs => rw [← hr, NTTEval.stage_right s v g o, hr]
    rw [h.2 i, ← hl, h.2]

/-- The body of the outer `while` loop of Algorithm 41. -/
def fwdOuter : Unit → Array Coeff × ℕ × ℕ → Id (ForInStep (Array Coeff × ℕ × ℕ)) := fun _ s =>
  if s.2.2 ≥ 1 then do
    let t ← forIn Lean.Loop.mk (s.1, s.2.1, 0)
      (innerBody (getZ zetaTable) (fun k => k + 1) fwdJ s.2.2)
    pure (.yield (t.1, t.2.1, s.2.2 / 2))
  else pure (.done s)

theorem loopNTT_eq (f : Rq) : loopNTT f =
    ⟨Vector.ofFn fun i => getZ (Id.run (forIn Lean.Loop.mk (f.toArray, 1, 128) fwdOuter)).1 i⟩ := by
  unfold loopNTT
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', List.forIn_pure_yield_eq_foldl,
    Std.Legacy.Range.size, Nat.add_sub_cancel_left, Nat.add_sub_cancel, Nat.div_one]
  rfl

/-- The outer `while` loop of Algorithm 41 from stage `s` runs the remaining stages. -/
theorem fwd_outer : ∀ r s, s + r = 8 → ∀ a v, Rep a v →
    Rep (Id.run (forIn Lean.Loop.mk (a, 2 ^ s, 128 / 2 ^ s) fwdOuter)).1
      (LatticeCrypto.NTTCert.forwardStages (nttStages.drop s) v)
  | 0, s, hs, a, v, h => by
    obtain rfl : s = 8 := by omega
    rw [loop_unfold]
    simp only [fwdOuter, show ¬ (128 / 2 ^ 8 ≥ 1) by decide, ite_false, Id.run_pure]
    exact h
  | r + 1, s, hs, a, v, h => by
    have hs8 : s < 8 := by omega
    let S : Fin 8 := ⟨s, hs8⟩
    have hlen : 128 / 2 ^ s ≥ 1 := len_pos S
    rw [loop_unfold]
    simp only [fwdOuter]
    rw [ite_eq_left hlen]
    obtain ⟨h1, h2, h3⟩ := inner_run fwdJ_spec (getZ zetaTable) (fun k => k + 1) (2 ^ s)
      (len_pos S) (groups_shape S) a (2 ^ s) 0 a (Nat.zero_add _) h.1
      (fun i _ => by rw [ite_eq_right (by omega)])
    simp only [Function.iterate_zero, id, Nat.zero_mul] at h1 h2 h3
    change Rep (Id.run (forIn Lean.Loop.mk ((Id.run (forIn Lean.Loop.mk (a, 2 ^ s, 0)
      (innerBody (getZ zetaTable) (fun k => k + 1) fwdJ (128 / 2 ^ s)))).1,
      (Id.run (forIn Lean.Loop.mk (a, 2 ^ s, 0)
      (innerBody (getZ zetaTable) (fun k => k + 1) fwdJ (128 / 2 ^ s)))).2.1,
      128 / 2 ^ s / 2) fwdOuter)).1 _
    rw [h3, iterate_succ_eq, len_half S, show 2 ^ s + 2 ^ s = 2 ^ (s + 1) by ring,
      drop_nttStages S]
    exact fwd_outer r (s + 1) (by omega) _ _
      ⟨h1, fun i => by rw [h2 i i.isLt]; exact fwd_stageT S h i⟩

/-- **The forward NTT loop kernel is the structural forward NTT.** -/
public theorem ntt_eq_loopNTT : ntt = loopNTT := by
  funext f
  rw [loopNTT_eq]
  have h := fwd_outer 8 0 rfl f.toArray (fun i => f.get i)
    ⟨Vector.size_toArray (self := f), fun i => by
      unfold getZ
      rw [Array.getD_eq_getD_getElem?,
        Array.getElem?_eq_getElem (by rw [Vector.size_toArray (self := f)]; exact i.isLt)]
      rfl⟩
  simp only [pow_zero, Nat.div_one, List.drop_zero] at h
  apply LatticeCrypto.TransformPoly.ext
  apply Vector.ext
  intro i hi
  change (Vector.ofFn (nttCoeffs fun i => f.get i))[i] =
    (Vector.ofFn fun i => getZ (Id.run (forIn Lean.Loop.mk (f.toArray, 1, 128) fwdOuter)).1 i)[i]
  rw [Vector.getElem_ofFn, Vector.getElem_ofFn]
  exact (h.2 ⟨i, hi⟩).symm

/-! ## The inverse NTT -/

theorem inv_stage_left (s : Fin 8) (v : Fin polyBackend.degree → Coeff) (g : Fin (2 ^ s.val))
    (o : Fin (128 / 2 ^ s.val)) :
    (nttStage s).inverse v ((layerLayout s).equiv ((g, o), false)) =
      v ((layerLayout s).equiv ((g, o), false)) + v ((layerLayout s).equiv ((g, o), true)) := by
  simp [nttStage, LatticeCrypto.NTTCert.butterflyStage, LatticeCrypto.NTTCert.inverseStage,
    LatticeCrypto.NTTCert.inverseButterfly]

theorem inv_stage_right (s : Fin 8) (v : Fin polyBackend.degree → Coeff) (g : Fin (2 ^ s.val))
    (o : Fin (128 / 2 ^ s.val)) :
    (nttStage s).inverse v ((layerLayout s).equiv ((g, o), true)) =
      -getZ zetaTable (2 ^ (s.val + 1) - 1 - g.val) *
        (v ((layerLayout s).equiv ((g, o), false)) - v ((layerLayout s).equiv ((g, o), true))) := by
  simp [nttStage, LatticeCrypto.NTTCert.butterflyStage, LatticeCrypto.NTTCert.inverseStage,
    LatticeCrypto.NTTCert.inverseButterfly]

theorem inv_stageT (s : Fin 8) {a : Array Coeff} {v : Fin polyBackend.degree → Coeff}
    (h : Rep a v) (i : Fin polyBackend.degree) :
    stageT (fun _ u v => u + v) (fun z u v => z * (u - v)) (fun k => -getZ zetaTable k)
      (fun k => k - 1) (2 ^ (s.val + 1) - 1) (128 / 2 ^ s.val) a i =
      (nttStage s).inverse v i := by
  set L := 128 / 2 ^ s.val with hL
  let g : Fin (2 ^ s.val) := ⟨i.val / (2 * L), block_lt s i⟩
  have hdm := Nat.div_add_mod' i.val (2 * L)
  have hmod := Nat.mod_lt i.val (show 0 < 2 * L by have := len_pos s; omega)
  have hz : (fun k => k - 1)^[i.val / (2 * L)] (2 ^ (s.val + 1) - 1) =
      2 ^ (s.val + 1) - 1 - g.val := iterate_pred_eq _ _
  unfold stageT
  rw [hz]
  by_cases ho : i.val % (2 * L) < L
  · let o : Fin L := ⟨i.val % (2 * L), ho⟩
    have hl : (layerLayout s).equiv ((g, o), false) = i := Fin.ext (by
      rw [NTTEval.layerLayout_left_val]; exact hdm)
    have hr : ((layerLayout s).equiv ((g, o), true)).val = i.val + L := by
      rw [NTTEval.layerLayout_right_val]
      change i.val / (2 * L) * (2 * L) + L + i.val % (2 * L) = _; omega
    rw [ite_eq_left ho]
    conv_rhs => rw [← hl, inv_stage_left s v g o, hl]
    rw [h.2 i, ← hr, h.2]
  · have ho' : i.val % (2 * L) - L < L := by omega
    let o : Fin L := ⟨i.val % (2 * L) - L, ho'⟩
    have hr : (layerLayout s).equiv ((g, o), true) = i := Fin.ext (by
      rw [NTTEval.layerLayout_right_val]
      change i.val / (2 * L) * (2 * L) + L + (i.val % (2 * L) - L) = _; omega)
    have hl : ((layerLayout s).equiv ((g, o), false)).val = i.val - L := by
      rw [NTTEval.layerLayout_left_val]
      change i.val / (2 * L) * (2 * L) + (i.val % (2 * L) - L) = _; omega
    rw [ite_eq_right ho]
    conv_rhs => rw [← hr, inv_stage_right s v g o, hr]
    rw [h.2 i, ← hl, h.2]

theorem take_nttStages (s : Fin 8) (v : Fin polyBackend.degree → Coeff) :
    LatticeCrypto.NTTCert.inverseStages (nttStages.take (s.val + 1)) v =
      LatticeCrypto.NTTCert.inverseStages (nttStages.take s.val) ((nttStage s).inverse v) := by
  fin_cases s <;> rfl

/-- The body of the outer `while` loop of Algorithm 42. -/
def invOuter : Unit → Array Coeff × ℕ × ℕ → Id (ForInStep (Array Coeff × ℕ × ℕ)) := fun _ s =>
  if s.2.2 ≤ 128 then do
    let t ← forIn Lean.Loop.mk (s.1, s.2.1, 0)
      (innerBody (fun k => -getZ zetaTable k) (fun k => k - 1) invJ s.2.2)
    pure (.yield (t.1, t.2.1, s.2.2 * 2))
  else pure (.done s)

/-- The final `for` loop of Algorithm 42: multiply every entry by `256⁻¹`. -/
def scaleFold (a : Array Coeff) : Array Coeff :=
  List.foldl (fun b j => b.set! j (nInv * getZ b j)) a (List.range' 0 ringDegree)

theorem scale_fold (b : Array Coeff) (hb : b.size = 256) :
    ∀ m ≤ 256, (List.foldl (fun b j => b.set! j (nInv * getZ b j)) b (List.range' 0 m)).size =
        256 ∧
      ∀ i, getZ (List.foldl (fun b j => b.set! j (nInv * getZ b j)) b (List.range' 0 m)) i =
        if i < m then nInv * getZ b i else getZ b i
  | 0, _ => ⟨hb, fun i => by rw [ite_eq_right (by omega)]; rfl⟩
  | m + 1, hm => by
    obtain ⟨ih1, ih2⟩ := scale_fold b hb m (by omega)
    rw [List.range'_concat, List.foldl_append]
    simp only [List.foldl_cons, List.foldl_nil, Nat.one_mul, Nat.zero_add]
    refine ⟨by rw [size_set, ih1], fun i => ?_⟩
    rw [getZ_set, ih1, ih2, ih2, ite_eq_right (show ¬ m < m by omega)]
    by_cases him : m = i
    · subst him; rw [ite_eq_left ⟨rfl, by omega⟩, ite_eq_left (by omega)]
    · rw [ite_eq_right (fun h => him h.1)]
      split_ifs <;> first | rfl | omega

theorem loopInvNTT_eq (fHat : Tq) : loopInvNTT fHat =
    Vector.ofFn fun i =>
      getZ (scaleFold (Id.run (forIn Lean.Loop.mk (fHat.toArray, 255, 1) invOuter)).1) i := by
  unfold loopInvNTT
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', List.forIn_pure_yield_eq_foldl,
    Std.Legacy.Range.size, Nat.add_sub_cancel_left, Nat.add_sub_cancel, Nat.div_one,
    Nat.sub_zero]
  rfl

/-- The outer `while` loop of Algorithm 42 from stage `s` runs stages `s, s - 1, …, 0`. -/
theorem inv_outer : ∀ s, (hs : s < 8) → ∀ a v, Rep a v →
    Rep (Id.run (forIn Lean.Loop.mk (a, 2 ^ (s + 1) - 1, 128 / 2 ^ s) invOuter)).1
      (LatticeCrypto.NTTCert.inverseStages (nttStages.take (s + 1)) v)
  | s, hs, a, v, h => by
    have hlen : 128 / 2 ^ s ≤ 128 := Nat.div_le_self _ _
    rw [loop_unfold]
    simp only [invOuter]
    rw [ite_eq_left hlen]
    obtain ⟨h1, h2, h3⟩ := inner_run invJ_spec (fun k => -getZ zetaTable k) (fun k => k - 1)
      (2 ^ (s + 1) - 1) (len_pos ⟨s, hs⟩) (groups_shape ⟨s, hs⟩) a (2 ^ s) 0 a
      (Nat.zero_add _) h.1 (fun i _ => by rw [ite_eq_right (by omega)])
    simp only [Function.iterate_zero, id, Nat.zero_mul] at h1 h2 h3
    have hrep : Rep (Id.run (forIn Lean.Loop.mk (a, 2 ^ (s + 1) - 1, 0)
        (innerBody (fun k => -getZ zetaTable k) (fun k => k - 1) invJ (128 / 2 ^ s)))).1
        ((nttStage ⟨s, hs⟩).inverse v) :=
      ⟨h1, fun i => by rw [h2 i i.isLt]; exact inv_stageT ⟨s, hs⟩ h i⟩
    rw [take_nttStages ⟨s, hs⟩]
    change Rep (Id.run (forIn Lean.Loop.mk ((Id.run (forIn Lean.Loop.mk (a, 2 ^ (s + 1) - 1, 0)
      (innerBody (fun k => -getZ zetaTable k) (fun k => k - 1) invJ (128 / 2 ^ s)))).1,
      (Id.run (forIn Lean.Loop.mk (a, 2 ^ (s + 1) - 1, 0)
      (innerBody (fun k => -getZ zetaTable k) (fun k => k - 1) invJ (128 / 2 ^ s)))).2.1,
      128 / 2 ^ s * 2) invOuter)).1 _
    rw [h3, iterate_pred_eq]
    generalize (Id.run (forIn Lean.Loop.mk (a, 2 ^ (s + 1) - 1, 0)
      (innerBody (fun k => -getZ zetaTable k) (fun k => k - 1) invJ (128 / 2 ^ s)))).1 = b at hrep ⊢
    cases s with
    | zero =>
      rw [loop_unfold]
      simp only [invOuter, show ¬ (128 / 2 ^ 0 * 2 ≤ 128) by decide, ite_false, Id.run_pure]
      exact hrep
    | succ t =>
      have hk : 2 ^ (t + 1 + 1) - 1 - 2 ^ (t + 1) = 2 ^ (t + 1) - 1 := by
        rw [pow_succ 2 (t + 1)]; omega
      rw [hk, len_double ⟨t, by omega⟩]
      exact inv_outer t (by omega) _ _ hrep

theorem invNTT_eq_ofFn (fHat : Tq) : invNTT fHat =
    Vector.ofFn (LatticeCrypto.NTTCert.scaleCoeffs nInv
      (LatticeCrypto.NTTCert.inverseStages nttStages fun i => fHat.coeffs.get i)) := rfl

theorem toArray_rep (fHat : Tq) : Rep fHat.toArray (fun i => fHat.coeffs.get i) := by
  refine ⟨Vector.size_toArray (self := fHat.coeffs), fun i => ?_⟩
  unfold getZ
  change fHat.coeffs.toArray.getD i 0 = _
  rw [Array.getD_eq_getD_getElem?,
    Array.getElem?_eq_getElem (by rw [Vector.size_toArray (self := fHat.coeffs)]; exact i.isLt)]
  rfl

/-- **The inverse NTT loop kernel is the structural inverse NTT.** -/
public theorem invNTT_eq_loopInvNTT : invNTT = loopInvNTT := by
  funext fHat
  rw [loopInvNTT_eq, invNTT_eq_ofFn]
  have h := inv_outer 7 (by omega) fHat.toArray _ (toArray_rep fHat)
  rw [show 2 ^ (7 + 1) - 1 = 255 by norm_num, show 128 / 2 ^ 7 = 1 by norm_num,
    show nttStages.take (7 + 1) = nttStages from rfl] at h
  have hs := scale_fold _ h.1 ringDegree le_rfl
  apply Vector.ext
  intro i hi
  rw [Vector.getElem_ofFn, Vector.getElem_ofFn]
  unfold scaleFold
  rw [hs.2, ite_eq_left (show i < ringDegree from hi), h.2 ⟨i, hi⟩]
  rfl

/-! ## Pointwise multiplication -/

/-- Evaluation at a root `x` of `X^256 + 1`, as a ring hom on the negacyclic quotient. -/
noncomputable def evalQ (x : Coeff) (hx : x ^ 256 = -1) :
    LatticeCrypto.NegacyclicQuotient Coeff polyBackend.degree →+* Coeff :=
  Ideal.Quotient.lift _ (Polynomial.evalRingHom x) (by
    intro p hp
    obtain ⟨q, rfl⟩ := Ideal.mem_span_singleton'.mp hp
    change Polynomial.eval x (q * (Polynomial.X ^ 256 + 1)) = 0
    simp [hx])

theorem evalQ_ofBackend (x : Coeff) (hx : x ^ 256 = -1) (p : Rq) :
    evalQ x hx (LatticeCrypto.NegacyclicQuotient.ofBackend polyBackend p) =
      ∑ j : Fin ringDegree, p.get j * x ^ j.val := by
  simp only [evalQ, LatticeCrypto.NegacyclicQuotient.ofBackend,
    LatticeCrypto.NegacyclicQuotient.ofPolynomial, Ideal.Quotient.lift_mk,
    Polynomial.coe_evalRingHom, LatticeCrypto.PolyBackend.toPolynomial, Polynomial.eval_finsetSum,
    Polynomial.eval_monomial]
  rfl

/-- At a root of `X^256 + 1`, the value of a negacyclic product is the product of the values. -/
theorem eval_negacyclicMul (x : Coeff) (hx : x ^ 256 = -1) (a b : Rq) :
    ∑ j : Fin ringDegree, (negacyclicMul a b).get j * x ^ j.val =
      (∑ j : Fin ringDegree, a.get j * x ^ j.val) * ∑ j : Fin ringDegree, b.get j * x ^ j.val := by
  rw [← evalQ_ofBackend x hx, ← evalQ_ofBackend x hx, ← evalQ_ofBackend x hx, ← map_mul]
  exact congrArg (evalQ x hx) (LatticeCrypto.negacyclicMulPure_sound polyBackend polyKernel a b)

theorem ntt_point_pow (k : Fin ringDegree) :
    ((zeta : Coeff) ^ (2 * bitRev8 k + 1)) ^ 256 = -1 := by
  rw [← pow_mul, show (2 * bitRev8 k + 1) * 256 = 256 * (2 * bitRev8 k + 1) by ring, pow_mul,
    NTTEval.zeta_pow_256, pow_succ, pow_mul]
  simp

theorem ntt_get_pow (f : Rq) (k : Fin ringDegree) :
    (ntt f).coeffs.get k =
      ∑ j : Fin ringDegree, f.get j * ((zeta : Coeff) ^ (2 * bitRev8 k + 1)) ^ j.val := by
  rw [NTTEval.ntt_get]
  simp only [← pow_mul]

/-- **The pointwise multiplication kernel is the structural `multiplyNTTs`.** -/
public theorem multiplyNTTs_eq_loopMultiplyNTTs : multiplyNTTs = loopMultiplyNTTs := by
  funext fHat gHat
  apply LatticeCrypto.TransformPoly.ext
  apply Vector.ext
  intro i hi
  have hx := ntt_point_pow ⟨i, hi⟩
  change (ntt (negacyclicMul (invNTT fHat) (invNTT gHat))).coeffs.get ⟨i, hi⟩ =
    (Vector.ofFn fun i : Fin ringDegree => fHat[i.val] * gHat[i.val])[i]
  rw [Vector.getElem_ofFn, ntt_get_pow, eval_negacyclicMul _ hx, ← ntt_get_pow, ← ntt_get_pow,
    ntt_invNTT, ntt_invNTT]
  rfl

end GordieHowe.MLDSA44.NTTLoop
