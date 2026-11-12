-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Applications.Ring.PublicW1.MLDSAPublicW1

@[expose] public section

/-!
# Completeness of the refusal rule

The signer of `MLDSAPublicW1.lean` refuses a ring when two members share a message
representative `µ_j` or when more than `tol` of the `reps · |R|` check samples fail
(`RingAdmissible`). This file bounds the probability that it refuses a ring it should sign on.

- `refuseError`, `expect_not_ringCheck_le_prod`, `expect_not_ringCheck_le`: over a uniform check
  oracle, a ring fails the check with probability at most
  `x^-(tol+1) · ∏_j (1 + (x - 1) δ_j)^reps ≤ refuseError reps tol d x =
  x^-(tol+1) · exp((x - 1) · reps · d)` for every `x ≥ 1`, with `δ_j` the members' check defects
  and `d` a bound on their sum (the Chernoff upper tail of the number of failed samples).
- `honestRing`, `expect_not_ringCheck_honestRing_le`: for a ring of `N'` honestly generated keys
  (independent uniform seeds), the probability is at most
  `x^-(tol+1) · (𝔼_seed (1 + (x - 1) δ(seed))^reps)^N'`, with `δ(seed)` the check defect of the
  key of `seed`: the samples of different members are independent, and those of one member are
  independent given its key.
- `expect_not_muDistinct_le`, `expect_not_ringAdmissible_le`: the members' `µ_j` of a ring of
  distinct keys collide with probability at most `|R|² / 2^512` over the message-representative
  oracle, so a ring of distinct keys of defect at most `d` is refused with probability at most
  `|R|² / 2^512 + refuseError reps tol d x`.

The numerical value of these bounds needs the law of an honest key's check defect `δ`, which is
not formalized; the README gives estimates of it and the resulting parameters.
-/

namespace GordieHowe.Ring.MLDSAW1

open _root_.MLDSA GordieHowe.MLDSA PMF Finset
open scoped ENNReal BigOperators

variable {p : Params} (prims : Primitives p) [NeZero (bucketCount p)] [nttOps : NTTRingOps]
  [Nonempty (MaskBox p)] {Msg : Type} [Fintype Msg] [DecidableEq Msg]
  [Inhabited prims.Hint] [Fintype prims.Hint] [DecidableEq prims.Hint]
  [Fintype prims.Power2High] [DecidableEq prims.Power2High]

/-- **The refusal error** at `reps` samples per member, tolerance `tol`, ring defect `d` and
Chernoff parameter `x`: `x^-(tol+1) · exp((x - 1) · reps · d)`, the bound of
`expect_not_ringCheck_le` for `x ≥ 1`. -/
noncomputable def refuseError (reps tol : ℕ) (d x : ℝ) : ℝ :=
  (x ^ (tol + 1))⁻¹ * Real.exp ((x - 1) * (reps * d))

omit [NeZero (bucketCount p)] [Nonempty (MaskBox p)] [Fintype Msg] [DecidableEq Msg]
  [Inhabited prims.Hint] [Fintype prims.Hint] [DecidableEq prims.Hint] in
/-- **A ring fails the check with probability at most the Chernoff product**: over a uniform
check oracle, more than `tol` of the `reps · |R|` samples fail with probability at most
`x^-(tol+1) · ∏_j (1 + (x - 1) δ_j)^reps` for every `x ≥ 1`, with `δ_j` the members' check
defects: `1[F > tol] ≤ x^(F - (tol + 1))` for the number `F` of failed samples, and the samples are
independent (`PMF.expect_comp_embedding`, `PMF.expect_prod_apply`). -/
theorem expect_not_ringCheck_le_prod (βmin : ℚ≥0) (tol : ℕ) {N reps : ℕ}
    (l : RingOf (PubKey p prims) N) {x : ℝ} (hx : 1 ≤ x) :
    𝔼 G : CheckOrc p prims N reps, (if sampledRingCheck prims βmin tol G l then 0 else 1 : ℝ) ≤
      (x ^ (tol + 1))⁻¹ *
        ∏ j, (1 + (x - 1) * checkDefect prims (Cutoff.const βmin) (ringT0s prims l.1 j)) ^ reps :=
            by
  have hx0 : 0 < x := zero_lt_one.trans_le hx
  set ψ : Fin l.1.length × Fin reps → CommitHashBytes p → ℝ := fun jr c =>
    if checkWeight prims (ringT0s prims l.1 jr.1) c < βmin then x else 1
  let e : Fin l.1.length × Fin reps ↪ RingOf (PubKey p prims) N × Fin N × Fin reps :=
    ⟨fun jr => (l, Fin.castLE l.2 jr.1, jr.2), fun a b h => by
      simp only [Prod.mk.injEq, Fin.castLE_inj] at h
      exact Prod.ext h.2.1 h.2.2⟩
  have h1 : ∀ G : CheckOrc p prims N reps, (if sampledRingCheck prims βmin tol G l then 0 else 1 :
      ℝ) ≤
      (x ^ (tol + 1))⁻¹ * ∏ jr, ψ jr (G (e jr)) := fun G => by
    have hprod : ∏ jr, ψ jr (G (e jr)) = x ^ checkFails prims βmin G l := by
      simp only [ψ]
      rw [Finset.prod_ite, Finset.prod_const_one, mul_one, Finset.prod_const]
      rfl
    rw [hprod]
    split_ifs with h
    · positivity
    · unfold sampledRingCheck at h
      push Not at h
      rw [inv_mul_eq_div, le_div_iff₀ (pow_pos hx0 _), one_mul]
      exact pow_le_pow_right₀ hx h
  have hψ : ∀ jr, 𝔼 c, ψ jr c =
      1 + (x - 1) * checkDefect prims (Cutoff.const βmin) (ringT0s prims l.1 jr.1) := fun jr => by
    have h : ∀ c, ψ jr c = 1 + (x - 1) *
        (if checkWeight prims (ringT0s prims l.1 jr.1) c < βmin then 1 else 0) := fun c => by
      simp only [ψ]
      split_ifs <;> ring
    rw [Finset.expect_congr rfl fun c _ => h c, Finset.expect_add_distrib,
      Finset.expect_const univ_nonempty, ← Finset.mul_expect, checkDefect]
  calc 𝔼 G : CheckOrc p prims N reps, (if sampledRingCheck prims βmin tol G l then 0 else 1 : ℝ)
      ≤ 𝔼 G : CheckOrc p prims N reps, (x ^ (tol + 1))⁻¹ * ∏ jr, ψ jr (G (e jr)) :=
        Finset.expect_le_expect fun G _ => h1 G
    _ = (x ^ (tol + 1))⁻¹ * ∏ jr, 𝔼 c, ψ jr c := by
        rw [← Finset.mul_expect, PMF.expect_comp_embedding e (fun g => ∏ jr, ψ jr (g jr)),
          PMF.expect_prod_apply]
    _ = (x ^ (tol + 1))⁻¹ *
        ∏ j, (1 + (x - 1) * checkDefect prims (Cutoff.const βmin) (ringT0s prims l.1 j)) ^ reps :=
            by
        simp only [hψ]
        rw [Fintype.prod_prod_type]
        simp

omit [NeZero (bucketCount p)] [Nonempty (MaskBox p)] [Fintype Msg] [DecidableEq Msg]
  [Inhabited prims.Hint] [Fintype prims.Hint] [DecidableEq prims.Hint] in
/-- **A ring of defect at most `d` fails the check with probability at most
`refuseError reps tol d x`** over a uniform check oracle, for every `x ≥ 1`
(`expect_not_ringCheck_le_prod`, `1 + y ≤ exp y`). -/
theorem expect_not_ringCheck_le (βmin : ℚ≥0) (tol : ℕ) {N reps : ℕ}
    (l : RingOf (PubKey p prims) N) {d x : ℝ} (hd : ringDefect prims βmin l.1 ≤ d) (hx : 1 ≤ x) :
    𝔼 G : CheckOrc p prims N reps, (if sampledRingCheck prims βmin tol G l then 0 else 1 : ℝ) ≤
      refuseError reps tol d x := by
  have hx1 : 0 ≤ x - 1 := sub_nonneg.2 hx
  refine (expect_not_ringCheck_le_prod prims βmin tol l hx).trans ?_
  unfold refuseError
  refine mul_le_mul_of_nonneg_left ?_ (inv_nonneg.2 (pow_nonneg (zero_le_one.trans hx) _))
  calc ∏ j, (1 + (x - 1) * checkDefect prims (Cutoff.const βmin) (ringT0s prims l.1 j)) ^ reps
      ≤ ∏ j : Fin l.1.length,
          Real.exp ((x - 1) * checkDefect prims (Cutoff.const βmin) (ringT0s prims l.1 j)) ^ reps :=
        Finset.prod_le_prod₀ (fun j _ => pow_nonneg (by
          nlinarith [checkDefect_nonneg prims (Cutoff.const βmin) (ringT0s prims l.1 j)]) _) fun j
              _ =>
          pow_le_pow_left₀ (by nlinarith [checkDefect_nonneg prims (Cutoff.const βmin) (ringT0s
              prims l.1 j)])
            (by linarith [Real.add_one_le_exp ((x - 1) *
              checkDefect prims (Cutoff.const βmin) (ringT0s prims l.1 j))]) _
    _ = Real.exp ((x - 1) * (reps * ringDefect prims βmin l.1)) := by
        simp only [← Real.exp_nat_mul, ← Real.exp_sum, ringDefect, ringDefectOf, ringCuts_constCut]
        congr 1
        rw [Finset.mul_sum, Finset.mul_sum]
        exact Finset.sum_congr rfl fun j _ => by ring
    _ ≤ Real.exp ((x - 1) * (reps * d)) :=
        Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hd (Nat.cast_nonneg _)) hx1)

/-- **The ring of `N'` honestly generated keys** from the seeds `seeds`, for `N' ≤ N`. -/
def honestRing {N N' : ℕ} (seeds : Fin N' → Bytes 32) (hN : N' ≤ N) :
    RingOf (PubKey p prims) N :=
  ⟨List.ofFn fun j => (keyGen prims (seeds j)).1, by simpa using hN⟩

omit [NeZero (bucketCount p)] [Nonempty (MaskBox p)] [Fintype Msg] [DecidableEq Msg]
  [Inhabited prims.Hint] [Fintype prims.Hint] [DecidableEq prims.Hint] in
/-- **A rejection bound of the ring check `chk`**: a function `r` of the ring that bounds the
probability, over a uniform check oracle, that the ring fails the test (`reject_le`). The refusal
theorems read it; the soundness side of `chk` (`s`, `e`, `shortfall_le`) does not. -/
structure RingCheck.RejectBound {cutOf : CutoffFamily prims} {N reps : ℕ}
    (chk : RingCheck prims cutOf N reps) where
  /-- The rejection bound of the ring `l`: an analysis quantity, read only by theorems, never by
  the signer or the verifier. -/
  r : RingOf (PubKey p prims) N → ℝ
  /-- The ring `l` fails the test with probability at most `r l`, an expectation over a uniform
  check oracle. At the sampled check (`RingCheck.sampledRejectBound`) it is a proved fact for
  every ring. -/
  reject_le : ∀ l : RingOf (PubKey p prims) N,
    𝔼 G : CheckOrc p prims N reps, (if chk.adm l (fun j t => G (l, j, t)) = true then 0 else 1 : ℝ)
      ≤ r l

omit [NeZero (bucketCount p)] [Nonempty (MaskBox p)] [Fintype Msg] [DecidableEq Msg]
  [Inhabited prims.Hint] [Fintype prims.Hint] [DecidableEq prims.Hint] in
/-- **Honest rings are rejected within `ρ`**: over `n` independent uniform key seeds, the average
of the rejection bound `rb.r` on the ring of their keys (`honestRing`) is at most `ρ`. A hypothesis
of the generic refusal lemmas (`RingCheck.RejectBound.expect_not_admits_honestRing_le`); at the
sampled check it is proved from the check-defect conjecture `W1CheckDefectMgf`
(`sampledRejectBound_honestRejectWithin`). -/
def RingCheck.RejectBound.HonestRejectWithin {cutOf : CutoffFamily prims} {N reps : ℕ}
    {chk : RingCheck prims cutOf N reps} (rb : chk.RejectBound prims) {n : ℕ} (hn : n ≤ N)
    (ρ : ℝ) : Prop :=
  𝔼 seeds : Fin n → Bytes 32, rb.r (honestRing prims seeds hn) ≤ ρ

omit [NeZero (bucketCount p)] [Nonempty (MaskBox p)] [Fintype Msg] [DecidableEq Msg]
  [Inhabited prims.Hint] [Fintype prims.Hint] [DecidableEq prims.Hint] in
/-- **An honest ring fails the ring check `chk` with probability at most `ρ`** over the seeds and a
uniform check oracle, when honest rings are rejected within `ρ` (`reject_le` at each value of the
seeds). -/
theorem RingCheck.RejectBound.expect_not_admits_honestRing_le {cutOf : CutoffFamily prims}
    {N reps : ℕ} {chk : RingCheck prims cutOf N reps} (rb : chk.RejectBound prims) {n : ℕ}
    (hn : n ≤ N) {ρ : ℝ} (h : rb.HonestRejectWithin prims hn ρ) :
    𝔼 seeds : Fin n → Bytes 32, 𝔼 G : CheckOrc p prims N reps,
        (if chk.Admits prims G (honestRing prims seeds hn) then 0 else 1 : ℝ) ≤ ρ :=
  (Finset.expect_le_expect fun _ _ => rb.reject_le _).trans h

omit [NeZero (bucketCount p)] [Nonempty (MaskBox p)] [Fintype Msg] [DecidableEq Msg]
  [Inhabited prims.Hint] [Fintype prims.Hint] [DecidableEq prims.Hint] in
/-- **The rejection bound of the sampled ring check** at the constant cut-off `β_min`: the Chernoff
product `y^-(tol+1) · ∏_j (1 + (y - 1) δ_j)^reps` of `expect_not_ringCheck_le_prod`, for every
`y ≥ 1`, with `δ_j` the members' check defects. The check's own parameter `x` belongs to the lower
tail of the failed samples, which bounds the soundness error; `y` belongs to their upper tail,
which bounds the rejection of a ring. The two bounds are smallest at different values, so the
rejection bound has its own parameter. -/
noncomputable def RingCheck.sampledRejectBound (βmin : ℚ≥0) (tol N reps : ℕ) (s x : ℝ)
    (hx : 1 ≤ x) {y : ℝ} (hy : 1 ≤ y) :
    (RingCheck.sampled prims (constCut prims βmin) tol N reps s x hx).RejectBound prims where
  r l := (y ^ (tol + 1))⁻¹ *
    ∏ j, (1 + (y - 1) * checkDefect prims (Cutoff.const βmin) (ringT0s prims l.1 j)) ^ reps
  reject_le l := by
    refine le_of_eq_of_le (Finset.expect_congr rfl fun G _ => ?_)
      (expect_not_ringCheck_le_prod prims βmin tol l hy)
    have h := RingCheck.sampled_admits_constCut_iff prims βmin tol N reps s x hx G l
    unfold RingCheck.Admits at h
    simp only [h]

omit [NeZero (bucketCount p)] [Nonempty (MaskBox p)] [Fintype Msg] [DecidableEq Msg]
  [Inhabited prims.Hint] [Fintype prims.Hint] [DecidableEq prims.Hint] [Fintype prims.Power2High]
  [DecidableEq prims.Power2High] in
/-- **The product-to-moment step**: averaged over `n` independent uniform seeds, the Chernoff
product `y^-(tol+1) · ∏_j (1 + (y - 1) δ_j)^reps` of the ring of their keys (the rejection bound
of `RingCheck.sampledRejectBound`) is `y^-(tol+1)` times the `n`-th power of
`𝔼_seed (1 + (y - 1) δ(seed))^reps`, with `δ(seed)` the check defect of the key of `seed`
(`PMF.expect_prod_apply`). -/
theorem expect_sampledReject_honestRing_eq (βmin : ℚ≥0) (tol reps : ℕ) (y : ℝ) {N n : ℕ}
    (hn : n ≤ N) :
    𝔼 seeds : Fin n → Bytes 32, (y ^ (tol + 1))⁻¹ * ∏ j, (1 + (y - 1) *
        checkDefect prims (Cutoff.const βmin) (ringT0s prims (honestRing prims seeds hn).1 j)) ^
          reps =
      (y ^ (tol + 1))⁻¹ * (𝔼 seed : Bytes 32,
        (1 + (y - 1) * checkDefect prims (Cutoff.const βmin) (keyGen prims seed).1.2.2) ^ reps) ^
          n := by
  have hpt : ∀ seeds : Fin n → Bytes 32,
      ∏ j, (1 + (y - 1) * checkDefect prims (Cutoff.const βmin)
          (ringT0s prims (honestRing prims seeds hn).1 j)) ^ reps =
        ∏ j : Fin n, (1 + (y - 1) * checkDefect prims (Cutoff.const βmin)
          (keyGen prims (seeds j)).1.2.2) ^ reps := fun seeds => by
    refine Fintype.prod_equiv (finCongr (List.length_ofFn)) _ _ fun j => ?_
    simp only [ringT0s, honestRing, List.get_eq_getElem, List.getElem_ofFn]
    rfl
  simp only [hpt]
  rw [← Finset.mul_expect, PMF.expect_prod_apply (fun _ seed =>
    (1 + (y - 1) * checkDefect prims (Cutoff.const βmin) (keyGen prims seed).1.2.2) ^ reps),
    Finset.prod_const, Finset.card_univ, Fintype.card_fin]

omit [NeZero (bucketCount p)] [Nonempty (MaskBox p)] [Fintype Msg] [DecidableEq Msg]
  [Inhabited prims.Hint] [Fintype prims.Hint] [DecidableEq prims.Hint] in
/-- **A ring of honestly generated keys fails the check with probability at most
`x^-(tol+1) · (𝔼_seed (1 + (x - 1) δ(seed))^reps)^N'`** over `N'` independent uniform seeds and a
uniform check oracle, for every `x ≥ 1`, with `δ(seed)` the check defect of the key of `seed`
(`RingCheck.RejectBound.expect_not_admits_honestRing_le` at `RingCheck.sampledRejectBound`, and
`expect_sampledReject_honestRing_eq`). -/
theorem expect_not_ringCheck_honestRing_le (βmin : ℚ≥0) (tol : ℕ) {N N' reps : ℕ}
    (hN : N' ≤ N) {x : ℝ} (hx : 1 ≤ x) :
    𝔼 seeds : Fin N' → Bytes 32, 𝔼 G : CheckOrc p prims N reps,
        (if sampledRingCheck prims βmin tol G (honestRing prims seeds hN) then 0 else 1 : ℝ) ≤
      (x ^ (tol + 1))⁻¹ * (𝔼 seed : Bytes 32,
        (1 + (x - 1) * checkDefect prims (Cutoff.const βmin) (keyGen prims seed).1.2.2) ^ reps) ^
            N' := by
  have h := (RingCheck.sampledRejectBound prims βmin tol N reps 0 x hx hx
    ).expect_not_admits_honestRing_le prims hN
    (le_of_eq (expect_sampledReject_honestRing_eq prims βmin tol reps x hN))
  simp only [RingCheck.sampled_admits_constCut_iff] at h
  exact h

omit [NeZero (bucketCount p)] nttOps [Nonempty (MaskBox p)] [DecidableEq Msg]
  [Inhabited prims.Hint] [Fintype prims.Hint] [DecidableEq prims.Hint] in
/-- **Two distinct points of a uniform oracle collide with probability `1 / |B|`.** -/
theorem expect_apply_eq_apply {K B : Type*} [Fintype K] [DecidableEq K] [Fintype B] [Nonempty B]
    [DecidableEq B] {a b : K} (hab : a ≠ b) :
    𝔼 H : K → B, (if H a = H b then 1 else 0 : ℝ) = 1 / Fintype.card B := by
  let f : Fin 2 ↪ K := ⟨![a, b], fun i j h => by
    fin_cases i <;> fin_cases j <;> simp_all [eq_comm]⟩
  have h : 𝔼 H : K → B, (if H a = H b then 1 else 0 : ℝ) =
      𝔼 g : Fin 2 → B, (if g 0 = g 1 then 1 else 0 : ℝ) :=
    PMF.expect_comp_embedding f (fun g : Fin 2 → B => (if g 0 = g 1 then 1 else 0 : ℝ))
  rw [h, ← Fintype.expect_equiv (piFinTwoEquiv fun _ => B).symm
    (fun y : B × B => (if y.1 = y.2 then 1 else 0 : ℝ)) _ fun y => rfl,
    ← Finset.univ_product_univ, Finset.expect_product]
  have hin : ∀ y : B, 𝔼 z : B, (if y = z then 1 else 0 : ℝ) = 1 / Fintype.card B := fun y => by
    rw [Fintype.expect_eq_sum_div_card, Finset.sum_ite_eq]
    simp
  simp only [hin, Fintype.expect_const]

omit [NeZero (bucketCount p)] [Nonempty (MaskBox p)] [Inhabited prims.Hint] [Fintype prims.Hint]
  [DecidableEq prims.Hint] in
/-- **The message representatives of a ring of distinct keys collide with probability at most
`|R|² / 2^512`**: over a uniform message-representative oracle `H_µ`, for a ring whose members'
`tr` are distinct, two members share `µ_j` with probability at most `|R|² / |Bytes 64|`
(a union over the pairs of the members' points, `expect_apply_eq_apply`). -/
theorem expect_not_muDistinct_le {N : ℕ} (l : RingOf (PubKey p prims) N) (m : Msg)
    (htr : (l.1.map (pubTr prims)).Nodup) :
    𝔼 Hmu : MuOrc Msg, (if MuDistinct prims Hmu l m then 0 else 1 : ℝ) ≤
      l.1.length ^ 2 / Fintype.card (Bytes 64) := by
  set S := (l.1.map fun x => (pubTr prims x, m)).toFinset
  have hS : S.card ≤ l.1.length :=
    (List.toFinset_card_le _).trans_eq (List.length_map _)
  have hcover : ∀ Hmu : MuOrc Msg, (if MuDistinct prims Hmu l m then 0 else 1 : ℝ) ≤
      ∑ ab ∈ S ×ˢ S, (if ab.1 ≠ ab.2 ∧ Hmu ab.1 = Hmu ab.2 then 1 else 0 : ℝ) := fun Hmu => by
    split_ifs with hd
    · exact Finset.sum_nonneg fun _ _ => by split_ifs <;> norm_num
    · have hcoll : ∃ ab ∈ S ×ˢ S, ab.1 ≠ ab.2 ∧ Hmu ab.1 = Hmu ab.2 := by
        by_contra hno
        push Not at hno
        refine hd (List.Nodup.map_on (fun x hx y hy hxy => ?_) (List.Nodup.of_map _ htr))
        have hxS : (pubTr prims x, m) ∈ S := List.mem_toFinset.2 (List.mem_map.2 ⟨x, hx, rfl⟩)
        have hyS : (pubTr prims y, m) ∈ S := List.mem_toFinset.2 (List.mem_map.2 ⟨y, hy, rfl⟩)
        have hpt : (pubTr prims x, m) = (pubTr prims y, m) := by
          by_contra hne
          exact hno ((pubTr prims x, m), (pubTr prims y, m)) (Finset.mem_product.2 ⟨hxS, hyS⟩)
            hne hxy
        exact List.inj_on_of_nodup_map htr hx hy (congrArg Prod.fst hpt)
      obtain ⟨ab, hab, h⟩ := hcoll
      refine le_of_eq_of_le ?_ (Finset.single_le_sum (f := fun ab : (Bytes 64 × Msg) ×
        (Bytes 64 × Msg) => (if ab.1 ≠ ab.2 ∧ Hmu ab.1 = Hmu ab.2 then 1 else 0 : ℝ))
        (fun _ _ => by split_ifs <;> norm_num) hab)
      exact (if_pos h).symm
  refine (Finset.expect_le_expect fun Hmu _ => hcover Hmu).trans ?_
  rw [Finset.expect_sum_comm]
  calc ∑ ab ∈ S ×ˢ S, 𝔼 Hmu : MuOrc Msg,
        (if ab.1 ≠ ab.2 ∧ Hmu ab.1 = Hmu ab.2 then 1 else 0 : ℝ)
      ≤ ∑ _ab ∈ S ×ˢ S, 1 / (Fintype.card (Bytes 64) : ℝ) := Finset.sum_le_sum fun ab _ => by
        by_cases hab : ab.1 ≠ ab.2
        · simp only [ne_eq, hab, not_false_eq_true, true_and]
          exact (expect_apply_eq_apply hab).le
        · simp only [hab, false_and, if_false, Finset.expect_const_zero]
          positivity
    _ = S.card ^ 2 / Fintype.card (Bytes 64) := by
        rw [Finset.sum_const, Finset.card_product, nsmul_eq_mul]
        push_cast
        ring
    _ ≤ l.1.length ^ 2 / Fintype.card (Bytes 64) := by
        gcongr

omit [NeZero (bucketCount p)] [Nonempty (MaskBox p)] [Inhabited prims.Hint] [Fintype prims.Hint]
  [DecidableEq prims.Hint] in
/-- **A ring of distinct keys of defect at most `d` is refused with probability at most
`|R|² / |Bytes 64| + refuseError reps tol d x`** over the game's oracles, for every `x ≥ 1`
(`expect_not_muDistinct_le`, `expect_not_ringCheck_le`). `|Bytes 64| = 2^512`. -/
theorem expect_not_ringAdmissible_le (βmin : ℚ≥0) (tol : ℕ) {N reps : ℕ}
    (l : RingOf (PubKey p prims) N) (m : Msg) (htr : (l.1.map (pubTr prims)).Nodup) {d x : ℝ}
    (hd : ringDefect prims βmin l.1 ≤ d) (hx : 1 ≤ x) :
    𝔼 HG : GameOrc prims Msg N reps,
        (if RingAdmissible prims βmin tol HG l m then 0 else 1 : ℝ) ≤
      l.1.length ^ 2 / Fintype.card (Bytes 64) + refuseError reps tol d x := by
  classical
  have hpt : ∀ HG : GameOrc prims Msg N reps,
      (if RingAdmissible prims βmin tol HG l m then 0 else 1 : ℝ) ≤
        (if MuDistinct prims HG.1.1 l m then 0 else 1) +
          (if sampledRingCheck prims βmin tol HG.2 l then 0 else 1) := fun HG => by
    unfold RingAdmissible
    by_cases h1 : MuDistinct prims HG.1.1 l m <;>
      by_cases h2 : sampledRingCheck prims βmin tol HG.2 l <;>
      simp [h1, h2]
  refine (Finset.expect_le_expect fun HG _ => hpt HG).trans ?_
  rw [Finset.expect_add_distrib]
  refine add_le_add ?_ ?_
  · rw [Finset.expect_comp_fst (fun H : SchOrc p Msg => (if MuDistinct prims H.1 l m then 0 else 1 : ℝ)),
      Finset.expect_comp_fst (fun Hmu : MuOrc Msg => (if MuDistinct prims Hmu l m then 0 else 1 : ℝ))]
    exact expect_not_muDistinct_le prims l m htr
  · rw [Finset.expect_comp_snd (fun G : CheckOrc p prims N reps =>
      (if sampledRingCheck prims βmin tol G l then 0 else 1 : ℝ))]
    exact expect_not_ringCheck_le prims βmin tol l hd hx

end GordieHowe.Ring.MLDSAW1
