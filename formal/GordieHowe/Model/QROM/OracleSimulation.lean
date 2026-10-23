-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Model.QROM.FourierCompression
public import Mathlib.Algebra.Order.Chebyshev

@[expose] public section

/-!
# Zhandry's Lemma 5: CMS19 Lemma 4.9, first inequality

Zhandry, "How to Record Quantum Queries" (Zha19, ePrint 2018/276), Lemma 5, p. 16, proof in
App. B.3, pp. 33–35; restated as CMS19 Lemma 4.9 (p. 20):

    Lemma 5. Consider a quantum algorithm A making queries to a random oracle H and outputting
    tuples (x1, …, xk, y1, …, yk, z). Let R be a collection of such tuples. Suppose with
    probability p, A outputs a tuple such that (1) the tuple is in R and (2) H(xi) = yi for all
    i. Now consider running A with the oracle CStO, and suppose the database D is measured after
    A produces its output. Let p′ be the probability that (1) the tuple is in R, and (2)
    D(xi) = yi for all i (and in particular D(xi) ≠ ⊥). Then √p ≤ √p′ + √(k/2^n).

`oracle_sim_sets` proves it for `t`-query algorithms `A : QueryAlg (Bits m) (BitStr I J) t _`,
`p` the probability under `A.realLaw e` and `p′` under `simLaw e A`, the outcome of CMS19's
`Sim*(A)` with the fixed-bound compressed phase oracle.

## Proof

Write `α = fourStage A t` for the final state of the Fourier-basis run. By Zha19 Lemmas 2 and 4
(`realLaw_eq_bornWeight`, `fourier_fourStage`, `simState_eq_compress`):
- `p = ‖mask GoodO (fourier α)‖²`, the truth table `h` satisfying `h(a_i) = b_i`;
- `p′ = ‖mask GoodD (dbFun α)‖²` (`simLaw_win_eq`, `norm_goodSim_compress`), where `dbFun` applies
  the entry kernel `fk` of `GordieHowe/Model/QROM/FourierCompression.lean` to every input (the database written as
  a function `Bits m → Option B`) and `GoodD` asks `D(a_i) = b_i`.

As in App. B.3, the two differ only in the terms whose Fourier index vanishes at some `a_i`:
- an isometry `Gop` (the embedding `y ↦ some y` at the queried inputs `A_r = {a_i}`, the
  compression `fk ∘ H^n` elsewhere) carries `mask GoodO ∘ fourier` to `mask GoodD ∘ Wop`, where
  `Wop` has the entry `gk` at the queried inputs and `fk` elsewhere (`norm_goodO_eq`);
- `mask GoodD ∘ dbFun = mask GoodD ∘ Wop ∘ P_Z`, `P_Z` the projection onto the Fourier indices
  that are nonzero at every `a_i` (`goodD_dbFun_eq`);
- the rest, `α − P_Z α`, splits into the orthogonal pieces `Q_j α` whose index vanishes first at
  `a_j` (`Zs`), and `‖mask GoodD (Wop (Q_j α))‖ ≤ (1/√2^n) ‖Q_j α‖` (`norm_goodD_wOp_le`); by
  Cauchy–Schwarz their sum has norm at most `√(k/2^n) ‖α‖`.

Zha19's proof assumes distinct `x_i` and starts at `k = 1` (App. B.3, pp. 33–35). Here
repeated `a_i` and `k = 0` need no separate case: the queried inputs form a set, a piece `Q_j`
whose `a_j` repeats an earlier one is empty, and for `k = 0` there are no pieces.
-/

open Finset GordieHowe.Quantum
open scoped BigOperators ENNReal

namespace GordieHowe.QROM

variable {I J : Type} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J] {m : ℕ}
  {B : Type} [Fintype B] [DecidableEq B] (e : BitStr I J ≃ B) {t : ℕ}

/-! ### Databases as functions -/

namespace DB

variable {X Y : Type*} [Fintype X] [DecidableEq X]

/-- The database with `D(x) = d x`. -/
def ofFun (d : X → Option Y) : DB X Y :=
  Finmap.keysLookupEquiv.symm ⟨(univ.filter fun x => (d x).isSome, d), fun x => by simp⟩

@[simp] theorem lookup_ofFun (d : X → Option Y) (x : X) : (ofFun d).lookup x = d x :=
  Finmap.keysLookupEquiv_symm_apply_lookup _ x

theorem size_ofFun (d : X → Option Y) :
    (ofFun d).size = (univ.filter fun x => (d x).isSome).card := by
  rw [size, ofFun, Finmap.keysLookupEquiv_symm_apply_keys]

end DB

/-! ### Entries -/

section Entries

omit [DecidableEq B] in
theorem sum_option_equiv {M : Type*} [AddCommMonoid M] (f : Option B → M) :
    ∑ o, f o = f none + ∑ y : BitStr I J, f (some (e y)) := by
  rw [Fintype.sum_option]
  exact congrArg _ (Fintype.sum_equiv e.symm _ _ fun b => by simp)

omit [DecidableEq B] in
/-- The entries `fk r` are orthonormal. -/
theorem fk_orthonormal (r r' : BitStr I J) :
    ∑ o, star (fk e r o) * fk e r' o = if r = r' then 1 else 0 := by
  rw [sum_option_equiv e]
  simp only [fk, Equiv.symm_apply_apply]
  by_cases h : r = 0 <;> by_cases h' : r' = 0
  · simp [h, h']
  · simp [h, h', Ne.symm h']
  · simp [h, h']
  · simp only [h, h', if_false, star_zero, zero_mul, zero_add]
    exact hk_orthonormal r r'

omit [DecidableEq B] in
/-- The entries `gk r` are orthonormal. -/
theorem gk_orthonormal (r r' : BitStr I J) :
    ∑ o, star (gk e r o) * gk e r' o = if r = r' then 1 else 0 := by
  rw [sum_option_equiv e]
  simp only [gk, Equiv.symm_apply_apply, star_zero, zero_mul, zero_add]
  exact hk_orthonormal r r'

end Entries

/-! ### The outcome of `Sim*(A)` as a function of the Fourier-basis run -/

section Sim

variable (W : Type) [Fintype W] [DecidableEq W]

/-- The registers with the database written as a function `Bits m → Option B`. -/
abbrev FunReg (W I J : Type) (m : ℕ) (B : Type) :=
  QueryReg W 1 (Bits m) (BitStr I J) × (Bits m → Option B)

/-- The entry kernel `fk` on every input: `|F⟩ ↦ ∑_d ∏_x fk (F x) (d x) |d⟩`. -/
noncomputable def dbFun : QState (PurReg W I J m) →L[ℂ] QState (FunReg W I J m B) :=
  kernelMap (idLeft fun _ => piKernel fun _ o r => fk e r o)

variable {W}

omit [DecidableEq B] in
theorem compress_apply (v : QState (PurReg W I J m)) (r : QueryReg W 1 (Bits m) (BitStr I J))
    (s : Slots I J m t) :
    compress e t W v (r, s) =
      if IsDBState e s then dbFun e W v (r, fun x => (slotsDB e s).lookup x) else 0 := by
  rw [compress, kernelMap_idLeft_apply, dbFun, kernelMap_idLeft_apply]
  by_cases hs : IsDBState e s
  · simp only [if_pos hs, fdb, dbVec, PiLp.toLp_apply, dbAmp]
    rfl
  · simp [hs, fdb, dbVec]

omit [DecidableEq B] in
/-- Where `dbFun v` is nonzero, the database records at most as many inputs as some Fourier index
in the support of `v`. -/
theorem card_isSome_le_of_dbFun {v : QState (PurReg W I J m)}
    (hv : Supported {b | b.2 ∈ {F : Bits m → BitStr I J | fourierSize F ≤ t}} v)
    {r : QueryReg W 1 (Bits m) (BitStr I J)} {d : Bits m → Option B} (h : dbFun e W v (r, d) ≠ 0) :
    (univ.filter fun x => (d x).isSome).card ≤ t := by
  rw [dbFun, kernelMap_idLeft_apply] at h
  obtain ⟨F, -, hF⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
  have hα : v (r, F) ≠ 0 := right_ne_zero_of_mul hF
  have hK := (Finset.prod_ne_zero_iff.1 (left_ne_zero_of_mul hF))
  refine (Finset.card_le_card fun x hx => ?_).trans (not_not.1 fun hn => hα (hv _ hn))
  refine Finset.mem_filter.2 ⟨Finset.mem_univ _, fun h0 => ?_⟩
  have hx' := (Finset.mem_filter.1 hx).2
  have := hK x (Finset.mem_univ _)
  obtain ⟨b, hb⟩ := Option.isSome_iff_exists.1 hx'
  simp [hb, fk] at this
  exact this.1 h0

variable (C : Type) {k : ℕ}

/-- The winning set of the simulated game on the basis of `Sim*`: `(a, b, c) ∈ G` and
`D(a_i) = b_i` for the database `D` the slots hold. -/
def goodSim (out : W → BaseGame.Tuple (Bits m) B C k)
    (G : Set (BaseGame.Tuple (Bits m) B C k)) : Set (SimRegister W I J m t) :=
  {b | out b.1.1 ∈ G ∧ (out b.1.1).InDB (slotsDB e b.2)}

/-- The winning set of the simulated game with the database written as a function. -/
def goodD (out : W → BaseGame.Tuple (Bits m) B C k)
    (G : Set (BaseGame.Tuple (Bits m) B C k)) : Set (FunReg W I J m B) :=
  {b | out b.1.1 ∈ G ∧ ∀ i, b.2 ((out b.1.1).queries i) = some ((out b.1.1).answers i)}

variable {C}

omit [DecidableEq B] in
/-- **The norm of the simulated win, with the database written as a function**: for `v` whose
Fourier-basis truth tables have at most `t` nonzero entries,
`‖mask goodSim (compress v)‖ = ‖mask goodD (dbFun v)‖`. -/
theorem norm_goodSim_compress (out : W → BaseGame.Tuple (Bits m) B C k)
    (G : Set (BaseGame.Tuple (Bits m) B C k)) {v : QState (PurReg W I J m)}
    (hv : Supported {b | b.2 ∈ {F : Bits m → BitStr I J | fourierSize F ≤ t}} v) :
    ‖mask (goodSim e C out G) (compress e t W v)‖ = ‖mask (goodD C out G) (dbFun e W v)‖ := by
  have key : ∀ (r : QueryReg W 1 (Bits m) (BitStr I J)) (s : Slots I J m t),
      mask (goodSim e C out G) (compress e t W v) (r, s) = if IsDBState e s then
        mask (goodD C out G) (dbFun e W v) (r, fun x => (slotsDB e s).lookup x) else 0 := by
    intro r s
    rw [mask_apply, mask_apply]
    by_cases hs : IsDBState e s
    · rw [if_pos hs]
      by_cases hg : (r, s) ∈ goodSim e C out G
      · rw [Set.indicator_of_mem hg, Set.indicator_of_mem (show (r, fun x =>
          (slotsDB e s).lookup x) ∈ goodD C out G from hg), compress_apply, if_pos hs]
      · rw [Set.indicator_of_notMem hg, Set.indicator_of_notMem (show (r, fun x =>
          (slotsDB e s).lookup x) ∉ goodD C out G from hg)]
    · rw [if_neg hs]
      by_cases hg : (r, s) ∈ goodSim e C out G
      · rw [Set.indicator_of_mem hg, compress_apply, if_neg hs]
      · rw [Set.indicator_of_notMem hg]
  refine (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 ?_
  rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq]
  have hdb : ∀ b : SimRegister W I J m t, ‖mask (goodSim e C out G) (compress e t W v) b‖ ^ 2 ≠ 0 →
      IsDBState e b.2 := fun b h => by
    by_contra hn
    exact h (by rw [key, if_neg hn]; simp)
  refine Finset.sum_bij_ne_zero (fun b _ _ => (b.1, fun x => (slotsDB e b.2).lookup x))
    (fun _ _ _ => Finset.mem_univ _) ?_ ?_ ?_
  · rintro ⟨r, s⟩ - h1 ⟨r', s'⟩ - h2 heq
    have hs : IsDBState e s := hdb (r, s) h1
    have hs' : IsDBState e s' := hdb (r', s') h2
    simp only [Prod.mk.injEq] at heq
    obtain ⟨rfl, hl⟩ := heq
    have hD : slotsDB e s = slotsDB e s' := Finmap.ext_lookup fun x => congrFun hl x
    rw [← (IsDBState.dbSlots_slotsDB e hs).2, ← (IsDBState.dbSlots_slotsDB e hs').2, hD]
  · rintro ⟨r, d⟩ - h
    have hd : dbFun e W v (r, d) ≠ 0 := by
      intro h0
      exact h (by simp [mask_apply, h0])
    have hsz : (DB.ofFun d).size ≤ t := by
      rw [DB.size_ofFun]
      exact card_isSome_le_of_dbFun e hv hd
    have hl : (fun x => (slotsDB e (dbSlots e t (DB.ofFun d))).lookup x) = d := by
      funext x
      rw [slotsDB_dbSlots e hsz, DB.lookup_ofFun]
    refine ⟨(r, dbSlots e t (DB.ofFun d)), Finset.mem_univ _, ?_, ?_⟩
    · rwa [key, if_pos (isDBState_dbSlots e hsz), hl]
    · simp only [hl]
  · rintro ⟨r, s⟩ - h
    rw [key, if_pos (hdb _ h)]

end Sim

/-! ### The comparison of the real and the simulated win -/

section Core


variable {W : Type} [Fintype W] [DecidableEq W] {C : Type} {k : ℕ}
  (out : W → BaseGame.Tuple (Bits m) B C k) (G : Set (BaseGame.Tuple (Bits m) B C k))

/-- The winning set of the real game on the basis of the purified run: `(a, b, c) ∈ G` and
`h(a_i) = b_i` for the truth table `h`. -/
def goodO : Set (PurReg W I J m) :=
  {b | out b.1.1 ∈ G ∧ (out b.1.1).AnsweredBy (e ∘ b.2)}

/-- The entry kernel of `wOp`: `gk` at the queried inputs `a_i` of the output, `fk` elsewhere. -/
noncomputable def wK (r : QueryReg W 1 (Bits m) (BitStr I J)) (x : Bits m) (o : Option B)
    (y : BitStr I J) : ℂ :=
  if ∃ i, (out r.1).queries i = x then gk e y o else fk e y o

/-- `fk` elsewhere and `gk` at the queried inputs, on every input. -/
noncomputable def wOp : QState (PurReg W I J m) →L[ℂ] QState (FunReg W I J m B) :=
  kernelMap (idLeft fun r => piKernel (wK e out r))

/-- The entry kernel of `gOp`: `y ↦ some y` at the queried inputs, `fk ∘ H^n` elsewhere. -/
noncomputable def gK (r : QueryReg W 1 (Bits m) (BitStr I J)) (x : Bits m) (o : Option B)
    (y : BitStr I J) : ℂ :=
  if ∃ i, (out r.1).queries i = x then (if o = some (e y) then 1 else 0) else ∑ r', fk e r' o * hk y r'

/-- The isometry that carries the real win to the simulated win. -/
noncomputable def gOp : QState (PurReg W I J m) →L[ℂ] QState (FunReg W I J m B) :=
  kernelMap (idLeft fun r => piKernel (gK e out r))

omit [Fintype W] [DecidableEq W] in
theorem gK_orthonormal (r : QueryReg W 1 (Bits m) (BitStr I J)) (x : Bits m) (y y' : BitStr I J) :
    ∑ o, star (gK e out r x o y) * gK e out r x o y' = if y = y' then 1 else 0 := by
  by_cases hx : ∃ i, (out r.1).queries i = x
  · simp only [gK, if_pos hx]
    rw [sum_option_equiv e]
    simp [e.injective.eq_iff, eq_comm]
  · simp only [gK, if_neg hx, star_sum, star_mul', star_hk, Finset.sum_mul, Finset.mul_sum]
    calc ∑ o, ∑ r', ∑ r, star (fk e r o) * hk y r * (fk e r' o * hk y' r')
        = ∑ r', ∑ r, hk y r * hk y' r' * ∑ o, star (fk e r o) * fk e r' o := by
          rw [Finset.sum_comm]
          refine sum_congr rfl fun r' _ => ?_
          rw [Finset.sum_comm]
          refine sum_congr rfl fun r _ => ?_
          rw [Finset.mul_sum]
          exact sum_congr rfl fun o _ => by ring
      _ = ∑ r, hk y r * hk r y' := by
          rw [Finset.sum_comm]
          refine sum_congr rfl fun r _ => ?_
          simp only [fk_orthonormal, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq,
            Finset.mem_univ, if_true, hk_comm r y']
      _ = _ := sum_hk_mul y y'

omit [Fintype W] [DecidableEq W] [DecidableEq B] in
theorem wK_orthonormal (r : QueryReg W 1 (Bits m) (BitStr I J)) (x : Bits m) (y y' : BitStr I J) :
    ∑ o, star (wK e out r x o y) * wK e out r x o y' = if y = y' then 1 else 0 := by
  by_cases hx : ∃ i, (out r.1).queries i = x
  · simp only [wK, if_pos hx]
    exact gk_orthonormal e y y'
  · simp only [wK, if_neg hx]
    exact fk_orthonormal e y y'

/-- `gOp` is an isometry. -/
theorem norm_gOp (v : QState (PurReg W I J m)) : ‖gOp e out v‖ = ‖v‖ :=
  norm_kernelMap (idLeft_orthonormal (S := fun _ => Set.univ) fun r F _ F' _ =>
    piKernel_orthonormal (fun x y y' => gK_orthonormal e out r x y y') F F')
    fun _ hb => absurd (Set.mem_univ _) hb

omit [Fintype B] [Fintype W] [DecidableEq W] in
theorem sum_gK_mul_hk (r : QueryReg W 1 (Bits m) (BitStr I J)) (x : Bits m) (o : Option B)
    (z : BitStr I J) : ∑ y, gK e out r x o y * hk y z = wK e out r x o z := by
  by_cases hx : ∃ i, (out r.1).queries i = x
  · simp only [gK, wK, if_pos hx, ite_mul, one_mul, zero_mul]
    rcases o with _ | b
    · simp [gk]
    · rw [Finset.sum_eq_single (e.symm b) (fun y _ hy => if_neg fun h => hy (by
        rw [Option.some_inj] at h; rw [h, Equiv.symm_apply_apply])) (by simp)]
      simp [gk]
  · simp only [gK, wK, if_neg hx, Finset.sum_mul]
    rw [Finset.sum_comm]
    have h1 : ∀ r' : BitStr I J, ∑ y, fk e r' o * hk y r' * hk y z =
        fk e r' o * (if r' = z then 1 else 0) := fun r' => by
      rw [← sum_hk_mul r' z, Finset.mul_sum]
      exact sum_congr rfl fun y _ => by rw [hk_comm y r']; ring
    simp_rw [h1]
    simp

/-- `gOp ∘ fourier = wOp`. -/
theorem gOp_fourier (v : QState (PurReg W I J m)) : gOp e out (fourier _ v) = wOp e out v := by
  ext ⟨r, d⟩
  rw [gOp, wOp, kernelMap_idLeft_apply, kernelMap_idLeft_apply]
  simp_rw [fourier_apply, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine sum_congr rfl fun F _ => ?_
  simp_rw [← mul_assoc]
  rw [← Finset.sum_mul]
  congr 1
  simp only [fourierK]
  rw [sum_piKernel_mul]
  simp only [sum_gK_mul_hk]

/-- `gOp` carries the real winning set to the simulated one. -/
theorem goodD_gOp (v : QState (PurReg W I J m)) :
    mask (goodD C out G) (gOp e out v) = gOp e out (mask (goodO e out G) v) := by
  refine (kernelMap_mask (fun a j h => ?_) v).symm
  obtain ⟨r, d⟩ := a
  obtain ⟨r', h'⟩ := j
  simp only [idLeft] at h
  split_ifs at h with hr
  · subst hr
    have hq : ∀ i, d ((out r.1).queries i) = some (e (h' ((out r.1).queries i))) := fun i => by
      have := (Finset.prod_ne_zero_iff.1 h) ((out r.1).queries i) (mem_univ _)
      simp only [gK, if_pos (⟨i, rfl⟩ : ∃ i', (out r.1).queries i' = (out r.1).queries i)] at this
      by_contra hne
      exact this (if_neg hne)
    simp only [goodD, goodO, Set.mem_setOf_eq, hq, Option.some_inj, BaseGame.Tuple.AnsweredBy,
      Function.comp_apply]
  · exact absurd rfl h

/-- **The real win as a simulated win with the entries `gk` at the queried inputs**:
`‖mask goodO (fourier v)‖ = ‖mask goodD (wOp v)‖`. -/
theorem norm_goodO_eq (v : QState (PurReg W I J m)) :
    ‖mask (goodO e out G) (fourier _ v)‖ = ‖mask (goodD C out G) (wOp e out v)‖ := by
  rw [← gOp_fourier, goodD_gOp, norm_gOp]

/-- The Fourier indices that are nonzero at the queried inputs `a_i` with `i < j`. -/
def Zs (j : ℕ) : Set (PurReg W I J m) :=
  {b | ∀ i : Fin k, (i : ℕ) < j → b.2 ((out b.1.1).queries i) ≠ 0}

omit [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J] [Fintype B] [DecidableEq B] [Fintype W] [DecidableEq W] in
theorem Zs_succ_subset (j : ℕ) : Zs out (j + 1) ⊆ (Zs out j : Set (PurReg W I J m)) :=
  fun _ hb i hi => hb i (Nat.lt_succ_of_lt hi)

omit [Fintype B] [DecidableEq B] [DecidableEq W] in
theorem mask_Zs_zero (v : QState (PurReg W I J m)) : mask (Zs out 0) v = v := by
  ext b
  exact mask_apply_of_mem _ fun i hi => absurd hi (Nat.not_lt_zero _)

omit [DecidableEq B] in
/-- **Away from the queried inputs `dbFun` and `wOp` agree, and at a queried input recorded with
its claimed answer the entry `fk` is `gk` restricted to nonzero Fourier values** (Zha19 App. B.3:
`p′` is the norm of the terms with `r` nonzero in every position). -/
theorem goodD_dbFun_eq (v : QState (PurReg W I J m)) :
    mask (goodD C out G) (dbFun e W v) = mask (goodD C out G) (wOp e out (mask (Zs out k) v)) := by
  ext ⟨r, d⟩
  rw [mask_apply, mask_apply]
  by_cases hg : (r, d) ∈ goodD C out G
  · rw [Set.indicator_of_mem hg, Set.indicator_of_mem hg, dbFun, wOp, kernelMap_idLeft_apply,
      kernelMap_idLeft_apply]
    refine sum_congr rfl fun F _ => ?_
    by_cases hZ : (r, F) ∈ (Zs out k : Set (PurReg W I J m))
    · rw [mask_apply_of_mem _ hZ]
      congr 1
      refine prod_congr rfl fun x _ => ?_
      by_cases hx : ∃ i, (out r.1).queries i = x
      · obtain ⟨i, rfl⟩ := hx
        have hz : F ((out r.1).queries i) ≠ 0 := hZ i i.2
        have hd : d ((out r.1).queries i) = some ((out r.1).answers i) := hg.2 i
        show fk e (F ((out r.1).queries i)) (d ((out r.1).queries i)) =
          wK e out r ((out r.1).queries i) (d ((out r.1).queries i)) (F ((out r.1).queries i))
        rw [wK, if_pos ⟨i, rfl⟩, hd]
        simp [fk, gk, hz]
      · show fk e (F x) (d x) = wK e out r x (d x) (F x)
        rw [wK, if_neg hx]
    · rw [mask_apply_of_notMem _ hZ, mul_zero]
      simp only [Zs, Set.mem_setOf_eq, not_forall, not_not] at hZ
      obtain ⟨i, -, hi⟩ := hZ
      refine mul_eq_zero_of_left (Finset.prod_eq_zero (Finset.mem_univ ((out r.1).queries i)) ?_) _
      have hd : d ((out r.1).queries i) = some ((out r.1).answers i) := hg.2 i
      show fk e (F ((out r.1).queries i)) (d ((out r.1).queries i)) = 0
      rw [hd]
      simp [fk, hi]
  · rw [Set.indicator_of_notMem hg, Set.indicator_of_notMem hg]

omit [Fintype B] [DecidableEq B] [DecidableEq W] in
open Classical in
/-- The pieces `Q_j = Zs j \ Zs (j + 1)`: the Fourier index vanishes first at `a_j`. -/
theorem sub_eq_sum_Q (v : QState (PurReg W I J m)) :
    v - mask (Zs out k) v = ∑ j ∈ range k, mask (Zs out j \ Zs out (j + 1)) v := by
  have h : ∀ j, mask (Zs out j) v - mask (Zs out (j + 1)) v =
      mask (Zs out j \ Zs out (j + 1) : Set (PurReg W I J m)) v := fun j => by
    ext b
    simp only [PiLp.sub_apply, mask_apply, Set.indicator_apply, Set.mem_diff]
    by_cases h1 : b ∈ (Zs out (j + 1) : Set (PurReg W I J m))
    · simp [h1, Zs_succ_subset out j h1]
    · simp [h1]
  simp_rw [← h]
  rw [Finset.sum_range_sub', mask_Zs_zero]

omit [Fintype B] [DecidableEq B] [DecidableEq W] in
theorem sum_norm_Q_sq_le (v : QState (PurReg W I J m)) :
    ∑ j ∈ range k, ‖mask (Zs out j \ Zs out (j + 1) : Set (PurReg W I J m)) v‖ ^ 2 ≤ ‖v‖ ^ 2 := by
  have h : ∀ j, ‖mask (Zs out j \ Zs out (j + 1) : Set (PurReg W I J m)) v‖ ^ 2 =
      ‖mask (Zs out j) v‖ ^ 2 - ‖mask (Zs out (j + 1)) v‖ ^ 2 := fun j => by
    have := norm_sq_eq_norm_mask_sq_add (Zs out (j + 1)) (mask (Zs out j) v)
    rw [(mask_mask_of_subset (Zs_succ_subset out j) v).1] at this
    have h2 : mask (Zs out (j + 1))ᶜ (mask (Zs out j) v) =
        mask (Zs out j \ Zs out (j + 1) : Set (PurReg W I J m)) v := by
      ext b
      simp only [mask_apply, Set.indicator_apply, Set.mem_compl_iff, Set.mem_diff]
      by_cases h1 : b ∈ (Zs out (j + 1) : Set (PurReg W I J m)) <;>
        by_cases h0 : b ∈ (Zs out j : Set (PurReg W I J m)) <;> simp [h1, h0]
    rw [h2] at this
    linarith
  simp_rw [h]
  rw [Finset.sum_range_sub', mask_Zs_zero]
  linarith [sq_nonneg ‖mask (Zs out k) v‖]

/-- **A piece whose Fourier index vanishes at a queried input contributes at most `1/√2^n` of its
norm** (Zha19 App. B.3): at `x₀ = a_j` the entry `gk 0` is `1/√2^n` on every recorded answer,
and the simulated win asks for one of them. -/
theorem norm_goodD_wOp_le (j : Fin k) {γ : QState (PurReg W I J m)}
    (hγ : Supported {b | b.2 ((out b.1.1).queries j) = 0} γ) :
    ‖mask (goodD C out G) (wOp e out γ)‖ ≤ invSqrtCardR I J * ‖γ‖ := by
  set x₀ : QueryReg W 1 (Bits m) (BitStr I J) → Bits m := fun r => (out r.1).queries j
  set b₀ : QueryReg W 1 (Bits m) (BitStr I J) → B := fun r => (out r.1).answers j
  set K' : QueryReg W 1 (Bits m) (BitStr I J) → Bits m → Option B → BitStr I J → ℂ :=
    fun r x o y => if x = x₀ r then (if o = some (b₀ r) ∧ y = 0 then 1 else 0) else wK e out r x o y
  have hsub : goodD C out G ⊆ {b : FunReg W I J m B | b.2 (x₀ b.1) = some (b₀ b.1)} :=
    fun b hb => hb.2 j
  have heq : mask {b : FunReg W I J m B | b.2 (x₀ b.1) = some (b₀ b.1)} (wOp e out γ) =
      invSqrtCard I J • kernelMap (idLeft fun r => piKernel (K' r)) γ := by
    ext ⟨r, d⟩
    rw [mask_apply, Set.indicator_apply, PiLp.smul_apply, wOp, kernelMap_idLeft_apply,
      kernelMap_idLeft_apply, smul_eq_mul, Finset.mul_sum]
    split_ifs with hd
    · refine sum_congr rfl fun F _ => ?_
      by_cases hF : F (x₀ r) = 0
      · simp only [piKernel]
        rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ (x₀ r)),
          ← Finset.mul_prod_erase _ (fun x => K' r x (d x) (F x)) (Finset.mem_univ (x₀ r))]
        have hrest : ∏ x ∈ univ.erase (x₀ r), K' r x (d x) (F x) =
            ∏ x ∈ univ.erase (x₀ r), wK e out r x (d x) (F x) :=
          prod_congr rfl fun x hx => by simp [K', Finset.ne_of_mem_erase hx]
        have hd' : d (x₀ r) = some (b₀ r) := hd
        rw [hrest]
        simp only [K', if_pos rfl, hd', hF, and_self, if_true, wK,
          if_pos (⟨j, rfl⟩ : ∃ i, (out r.1).queries i = x₀ r), gk, hk_zero]
        ring
      · rw [hγ (r, F) hF, mul_zero, mul_zero, mul_zero]
    · refine (Finset.sum_eq_zero fun F _ => ?_).symm
      by_cases hF : F (x₀ r) = 0
      · have hd' : ¬ d (x₀ r) = some (b₀ r) := hd
        rw [show piKernel (K' r) d F = 0 from Finset.prod_eq_zero (Finset.mem_univ (x₀ r))
          (by simp [K', hd']), zero_mul, mul_zero]
      · rw [hγ (r, F) hF, mul_zero, mul_zero]
  have hiso : ‖kernelMap (idLeft fun r => piKernel (K' r)) γ‖ = ‖γ‖ := by
    refine norm_kernelMap (S := {b : PurReg W I J m | b.2 ∈
        (fun r => {F : Bits m → BitStr I J | F (x₀ r) = 0}) b.1})
      (idLeft_orthonormal (S := fun r => {F : Bits m → BitStr I J | F (x₀ r) = 0})
        fun r F hF F' hF' => ?_)
      (fun b hb => hγ b hb)
    rw [sum_star_piKernel_mul]
    have hcol : ∀ x, ∑ o, star (K' r x o (F x)) * K' r x o (F' x) =
        if F x = F' x then 1 else 0 := fun x => by
      by_cases hx : x = x₀ r
      · subst hx
        have h1 : F (x₀ r) = 0 := hF
        have h2 : F' (x₀ r) = 0 := hF'
        simp only [K', if_pos rfl, h1, h2, and_true, if_true]
        rw [Finset.sum_eq_single (some (b₀ r)) (fun o _ ho => by simp [ho]) (by simp)]
        simp
      · simp only [K', if_neg hx]
        exact wK_orthonormal e out r x _ _
    simp only [hcol]
    by_cases hFF : F = F'
    · subst hFF
      simp
    · obtain ⟨x, hx⟩ := Function.ne_iff.1 hFF
      rw [if_neg hFF]
      exact Finset.prod_eq_zero (Finset.mem_univ x) (if_neg hx)
  calc ‖mask (goodD C out G) (wOp e out γ)‖
      ≤ ‖mask {b : FunReg W I J m B | b.2 (x₀ b.1) = some (b₀ b.1)} (wOp e out γ)‖ :=
        norm_mask_le_norm_mask hsub _
    _ = invSqrtCardR I J * ‖γ‖ := by
        have hnn : 0 ≤ invSqrtCardR I J := inv_nonneg.2 (Real.sqrt_nonneg _)
        rw [heq, norm_smul, hiso, invSqrtCard_eq, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg hnn]

/-- **The core inequality of Zha19 Lemma 5** (App. B.3, "By the triangle inequality, √p = |v| ≤
|u| + |w| ≤ √p′ + √(k/2^n)"):
`‖mask goodO (fourier v)‖ ≤ ‖mask goodD (dbFun v)‖ + √(k/2^n) ‖v‖`. -/
theorem norm_goodO_le (v : QState (PurReg W I J m)) :
    ‖mask (goodO e out G) (fourier _ v)‖ ≤ ‖mask (goodD C out G) (dbFun e W v)‖ +
      Real.sqrt (k / Fintype.card (BitStr I J)) * ‖v‖ := by
  set Q : ℕ → Set (PurReg W I J m) := fun j => Zs out j \ Zs out (j + 1)
  have hsplit : v = mask (Zs out k) v + ∑ j ∈ range k, mask (Q j) v := by
    rw [← sub_eq_sum_Q, add_sub_cancel]
  have hQ : ∀ j ∈ range k, ‖mask (goodD C out G) (wOp e out (mask (Q j) v))‖ ≤
      invSqrtCardR I J * ‖mask (Q j) v‖ := fun j hj => by
    refine norm_goodD_wOp_le e out G ⟨j, Finset.mem_range.1 hj⟩ fun b hb => ?_
    rw [mask_apply_of_notMem]
    rintro ⟨h1, h2⟩
    refine h2 fun i hi => ?_
    rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | hi
    · exact h1 i hi
    · have : i = ⟨j, Finset.mem_range.1 hj⟩ := Fin.ext hi
      subst this
      exact hb
  have hCS : ∑ j ∈ range k, ‖mask (Q j) v‖ ≤ Real.sqrt k * ‖v‖ := by
    have h := sq_sum_le_card_mul_sum_sq (s := range k) (f := fun j => ‖mask (Q j) v‖)
    rw [Finset.card_range] at h
    have h2 := sum_norm_Q_sq_le out v
    rw [← Real.sqrt_sq (norm_nonneg v), ← Real.sqrt_mul (Nat.cast_nonneg _)]
    refine Real.le_sqrt_of_sq_le ?_
    calc (∑ j ∈ range k, ‖mask (Q j) v‖) ^ 2 ≤ k * ∑ j ∈ range k, ‖mask (Q j) v‖ ^ 2 := h
      _ ≤ k * ‖v‖ ^ 2 := by gcongr
  have hc : invSqrtCardR I J * Real.sqrt k = Real.sqrt (k / Fintype.card (BitStr I J)) := by
    rw [invSqrtCardR, Real.sqrt_div' _ (Nat.cast_nonneg _), div_eq_inv_mul]
  calc ‖mask (goodO e out G) (fourier _ v)‖ = ‖mask (goodD C out G) (wOp e out v)‖ :=
        norm_goodO_eq e out G v
    _ = ‖mask (goodD C out G) (dbFun e W v) + ∑ j ∈ range k,
          mask (goodD C out G) (wOp e out (mask (Q j) v))‖ := by
        rw [goodD_dbFun_eq e out G, ← map_sum, ← map_sum, ← map_add, ← map_add, ← hsplit]
    _ ≤ ‖mask (goodD C out G) (dbFun e W v)‖ + ∑ j ∈ range k,
          ‖mask (goodD C out G) (wOp e out (mask (Q j) v))‖ :=
        (norm_add_le _ _).trans (add_le_add le_rfl (norm_sum_le _ _))
    _ ≤ ‖mask (goodD C out G) (dbFun e W v)‖ + invSqrtCardR I J * (Real.sqrt k * ‖v‖) := by
        gcongr
        have hnn : 0 ≤ invSqrtCardR I J := inv_nonneg.2 (Real.sqrt_nonneg _)
        calc ∑ j ∈ range k, ‖mask (goodD C out G) (wOp e out (mask (Q j) v))‖
            ≤ ∑ j ∈ range k, invSqrtCardR I J * ‖mask (Q j) v‖ := Finset.sum_le_sum hQ
          _ = invSqrtCardR I J * ∑ j ∈ range k, ‖mask (Q j) v‖ := (Finset.mul_sum _ _ _).symm
          _ ≤ invSqrtCardR I J * (Real.sqrt k * ‖v‖) := mul_le_mul_of_nonneg_left hCS hnn
    _ = _ := by rw [← mul_assoc, hc]

end Core

/-! ### Zhandry's Lemma 5 -/

section Lemma5

variable {C : Type} {k : ℕ}
  (A : QueryAlg (Bits m) (BitStr I J) t (BaseGame.Tuple (Bits m) B C k))
  (G : Set (BaseGame.Tuple (Bits m) B C k))

omit [Fintype B] [DecidableEq B] in
/-- The real win is the norm of the real winning set in the purified final state. -/
theorem realLaw_win_eq :
    (A.realLaw e).toOuterMeasure {p | p.out ∈ G ∧ p.out.AnsweredBy p.oracle} =
      ‖mask (goodO e A.out G) (fourier _ (fourStage A t))‖ₑ ^ 2 := by
  rw [realLaw_eq_bornWeight, fourier_fourStage, bornWeight_apply]
  rfl

omit [Fintype B] [DecidableEq B] in
/-- The simulated win is the norm of the simulated winning set in `|Sim*(A)⟩`. -/
theorem simLaw_win_eq :
    simLaw e A {p | p.1 ∈ G ∧ p.1.InDB p.2} =
      ‖mask (goodSim e C A.out G) (simState e A)‖ₑ ^ 2 := by
  rw [simLaw, MeasureTheory.OuterMeasure.map_apply, bornWeight_apply]
  rfl

omit [Fintype B] [DecidableEq B] in
/-- The final state of the Fourier-basis run is a unit vector. -/
theorem norm_fourStage : ‖fourStage A t‖ = 1 := by
  have h := realLaw_eq_bornWeight A (Equiv.refl (BitStr I J)) Set.univ
  rw [(PMF.toOuterMeasure_apply_eq_one_iff _ _).2 (Set.subset_univ _), bornWeight_apply] at h
  have hm : mask {b : PurReg A.W I J m |
      (⟨A.out b.1.1, Equiv.refl (BitStr I J) ∘ b.2⟩ : Outcome _ (Bits m) _) ∈ (Set.univ : Set _)}
      (purStage A t) = purStage A t := by
    ext b
    exact mask_apply_of_mem _ (Set.mem_univ _)
  rw [hm, ← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _)] at h
  have h1 : ‖purStage A t‖ ^ 2 = 1 := by
    have := (ENNReal.ofReal_eq_one.1 h.symm)
    exact this
  rw [← norm_fourier, fourier_fourStage]
  nlinarith [norm_nonneg (purStage A t), sq_nonneg (‖purStage A t‖ - 1)]

include e in
omit [DecidableEq B] in
theorem sqrt_div_card_eq :
    ((k : ℝ≥0∞) / Fintype.card B) ^ (1 / 2 : ℝ) =
      ENNReal.ofReal (Real.sqrt (k / Fintype.card (BitStr I J))) := by
  have hN : (0 : ℝ) < Fintype.card (BitStr I J) := by exact_mod_cast Fintype.card_pos
  rw [← Fintype.card_congr e, ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_natCast (Fintype.card _),
    ← ENNReal.ofReal_div_of_pos hN, ENNReal.ofReal_rpow_of_nonneg (by positivity) (by norm_num),
    Real.sqrt_eq_rpow]

/-- **Zha19 Lemma 5** (p. 16, proof App. B.3; CMS19 Lemma 4.9, first inequality, p. 20): for a
`t`-query algorithm `A` whose output is `(a, b, c)`,
`√Pr[(a, b, c) ∈ G ∧ h(a_i) = b_i] ≤ √Pr[(a, b, c) ∈ G ∧ D(a_i) = b_i] + √(k/|B|)`, the first
probability for a uniformly random oracle `h` (`QueryAlg.realLaw`), the second for the output and
the measured database of `Sim*(A)` (`simLaw`). Repeated `a_i` and `k = 0` are included. -/
theorem oracle_sim_sets :
    (A.realLaw e).toOuterMeasure {p | p.out ∈ G ∧ p.out.AnsweredBy p.oracle} ^ (1 / 2 : ℝ) ≤
      simLaw e A {p | p.1 ∈ G ∧ p.1.InDB p.2} ^ (1 / 2 : ℝ) +
        ((k : ℝ≥0∞) / Fintype.card B) ^ (1 / 2 : ℝ) := by
  have h2 : ∀ x : ℝ≥0∞, (x ^ 2) ^ (1 / 2 : ℝ) = x := fun x => by
    rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
    norm_num
  have hcore := norm_goodO_le e A.out G (fourStage A t)
  rw [norm_fourStage, mul_one] at hcore
  rw [realLaw_win_eq, simLaw_win_eq, simState_eq_compress, h2, h2, sqrt_div_card_eq e,
    ← ofReal_norm, ← ofReal_norm, norm_goodSim_compress e A.out G (supported_fourStage A t),
    ← ENNReal.ofReal_add (norm_nonneg _) (Real.sqrt_nonneg _)]
  exact ENNReal.ofReal_le_ofReal hcore

end Lemma5

end GordieHowe.QROM
