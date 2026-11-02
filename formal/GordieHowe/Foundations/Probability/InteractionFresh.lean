-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Foundations.Probability.InteractionGuess

@[expose] public section

/-!
# Fresh coins: lazy sampling for classical interactions

A classical interaction (`GordieHowe/Foundations/Probability/Interaction.lean`) whose challenger
draws uniform coins `a : Fin N → C` and answers the coin-reading move `m` (`w m ≠ 0`) after the
history `h` reading only the coin `a j`, `j = readCount w h` (the number of coin-reading moves of
`h`, weighted by `w`), through a kernel `K h m : C → PMF R`, while it answers the other moves, and
every move once `N` coins are read, without reading a coin. Since the move at a coin's read is chosen
before the coin is read and every later read is of a later coin, the experiment is the **lazy**
one, in which each read draws its reply from the averaged kernel `(uniform C).bind (K h m)`
(lazy sampling). Two challengers with the same averaged kernels,
whatever their coin types, have the same experiment.

- `cont_congr_of_support`: continuations against two challengers agree from a history of a set
  closed under the supported replies, when the inputs and the replies there agree.
- `mem_support_cont_inv`: the final history of a continuation lies in such a set and has `k` more
  rounds.
- `FreshCoins χ w i₀ K L`: the hypotheses (uniform coins, the input `i₀`, the reads through `K`,
  the other replies `L`). `Challenger.ofFresh`: the challenger built from `K` and `L`
  (`freshCoins_ofFresh`).
- `lazy w N i₀ Kbar L`: the challenger without coins answering the reads from `Kbar`;
  `lazy_congr`: it reads `Kbar` only at the reads.
- `cont_update_of_lt`: the continuation from a history past the read of coin `j` does not read it.
- `tsum_uniform_cont`, `exper_eq_lazy`: **the lazy sampling**: the coin average of the
  continuations is the lazy continuation, and the experiment is the lazy one.
- `exper_eq_of_freshCoins`: two such challengers with the same averaged kernels at the reads have
  the same experiment.
-/

open scoped ENNReal BigOperators

namespace GordieHowe.Interaction

variable {I M R O : Type*}

/-! ### Continuations on a set closed under the replies -/

section Support

variable {Ω Ω' : Type*}

/-- **Continuations against two challengers agree on a set closed under the supported replies**:
from a history of `P`, with the same input at the coins `ω`, `ω'`, when the replies agree at the
histories of `P` and every supported reply keeps the history in `P`. -/
theorem cont_congr_of_support (σ : Strategy I M R O) (χ : Challenger Ω I M R)
    (χ' : Challenger Ω' I M R) {ω : Ω} {ω' : Ω'} (P : Hist M R → Prop)
    (hP : ∀ h m r, P h → r ∈ (χ.reply ω h m).support → P (h ++ [(m, r)]))
    (hin : χ.input ω = χ'.input ω') (hr : ∀ h m, P h → χ.reply ω h m = χ'.reply ω' h m) :
    ∀ (k : ℕ) (h : Hist M R), P h → cont σ χ ω h k = cont σ χ' ω' h k
  | 0, h, _ => by simp only [cont, hin]
  | k + 1, h, hh => by
    simp only [cont, hin]
    refine congrArg _ (funext fun m => ?_)
    rw [← hr h m hh]
    ext x
    simp only [PMF.bind_apply]
    refine tsum_congr fun r => ?_
    by_cases hs : r ∈ (χ.reply ω h m).support
    · rw [cont_congr_of_support σ χ χ' P hP hin hr k _ (hP h m r hh hs)]
    · rw [(PMF.apply_eq_zero_iff _ _).2 hs, zero_mul, zero_mul]

/-- **The final history of a continuation stays in a set closed under the supported replies**,
and has `k` more rounds than its start. -/
theorem mem_support_cont_inv (σ : Strategy I M R O) (χ : Challenger Ω I M R) (ω : Ω)
    (P : Hist M R → Prop) (hP : ∀ h m r, P h → r ∈ (χ.reply ω h m).support → P (h ++ [(m, r)])) :
    ∀ (k : ℕ) (h : Hist M R) (p : Hist M R × O), P h → p ∈ (cont σ χ ω h k).support →
      P p.1 ∧ p.1.length = h.length + k
  | 0, h, p, hh, hp => by
    simp only [cont, PMF.support_map, Set.mem_image] at hp
    obtain ⟨o, -, rfl⟩ := hp
    exact ⟨hh, rfl⟩
  | k + 1, h, p, hh, hp => by
    simp only [cont, PMF.support_bind, Set.mem_iUnion] at hp
    obtain ⟨m, -, r, hr, hp⟩ := hp
    obtain ⟨h1, h2⟩ := mem_support_cont_inv σ χ ω P hP k _ p (hP h m r hh hr) hp
    refine ⟨h1, ?_⟩
    rw [h2, List.length_append, List.length_singleton]
    omega

end Support

/-! ### Fresh coins -/

section Fresh

variable {C : Type*} [Fintype C] [Nonempty C] {N : ℕ}

/-- **A challenger reading a fresh coin at each read**: its coins `a : Fin N → C` are uniform, its
input is `i₀`, a coin-reading move `m` (`w m ≠ 0`) after a history `h` with fewer than `N` reads
(`readCount w h`) is answered by `K h m` at the coin `a (readCount w h)`, and every other move by
`L h m`, reading no coin. -/
structure FreshCoins (χ : Challenger (Fin N → C) I M R) (w : M → ℕ) (i₀ : I)
    (K : Hist M R → M → C → PMF R) (L : Hist M R → M → PMF R) : Prop where
  /-- The coins are uniform. -/
  coins : χ.coins = PMF.uniformOfFintype (Fin N → C)
  /-- The input reads no coin. -/
  input : ∀ a, χ.input a = i₀
  /-- A read reads its coin only. -/
  read : ∀ a h m (hj : readCount w h < N), w m ≠ 0 →
    χ.reply a h m = K h m (a ⟨readCount w h, hj⟩)
  /-- The other replies read no coin. -/
  noRead : ∀ a h m, (w m = 0 ∨ N ≤ readCount w h) → χ.reply a h m = L h m

/-- **The challenger built from the read kernels `K` and the other replies `L`**, with uniform
coins and the input `i₀`. -/
noncomputable def Challenger.ofFresh (N : ℕ) (w : M → ℕ) (i₀ : I) (K : Hist M R → M → C → PMF R)
    (L : Hist M R → M → PMF R) : Challenger (Fin N → C) I M R where
  coins := PMF.uniformOfFintype (Fin N → C)
  input _ := i₀
  reply a h m := if hj : w m ≠ 0 ∧ readCount w h < N then K h m (a ⟨readCount w h, hj.2⟩)
    else L h m

/-- **The challenger built from `K` and `L` reads fresh coins.** -/
theorem freshCoins_ofFresh (w : M → ℕ) (i₀ : I) (K : Hist M R → M → C → PMF R)
    (L : Hist M R → M → PMF R) : FreshCoins (Challenger.ofFresh N w i₀ K L) w i₀ K L where
  coins := rfl
  input _ := rfl
  read a h m hj hw := by simp only [Challenger.ofFresh, dite_eq_left_of_eq_true (eq_true (And.intro hw hj))]
  noRead a h m hm := by
    have : ¬ (w m ≠ 0 ∧ readCount w h < N) := by omega
    simp only [Challenger.ofFresh, dite_eq_right_of_eq_false (eq_false this)]

omit [Fintype C] [Nonempty C] in
variable (N) in
/-- **The lazy challenger**: no coins, the input `i₀`, a read (a move with `w m ≠ 0` after fewer
than `N` reads) answered from `Kbar h m`, every other move from `L h m`. -/
noncomputable def lazy (w : M → ℕ) (i₀ : I) (Kbar L : Hist M R → M → PMF R) :
    Challenger Unit I M R where
  coins := PMF.pure ()
  input _ := i₀
  reply _ h m := if w m ≠ 0 ∧ readCount w h < N then Kbar h m else L h m

omit [Fintype C] [Nonempty C] in
/-- **The lazy challenger reads its kernels only at the reads.** -/
theorem lazy_congr (w : M → ℕ) (i₀ : I) {Kbar Kbar' : Hist M R → M → PMF R}
    (L : Hist M R → M → PMF R)
    (hK : ∀ h m, w m ≠ 0 → readCount w h < N → Kbar h m = Kbar' h m) :
    lazy N w i₀ Kbar L = lazy N w i₀ Kbar' L := by
  simp only [lazy]
  congr 1
  funext _ h m
  split_ifs with h1
  · exact hK h m h1.1 h1.2
  · rfl

variable {χ : Challenger (Fin N → C) I M R} {w : M → ℕ} {i₀ : I} {K : Hist M R → M → C → PMF R}
  {L : Hist M R → M → PMF R}

/-- **The continuation past the read of coin `j` does not read it.** -/
theorem cont_update_of_lt (σ : Strategy I M R O) (hχ : FreshCoins χ w i₀ K L) (a : Fin N → C)
    (j : Fin N) (y : C) (k : ℕ) (h : Hist M R) (hj : (j : ℕ) < readCount w h) :
    cont σ χ (Function.update a j y) h k = cont σ χ a h k := by
  classical
  refine cont_congr_coins σ χ (fun h' => (j : ℕ) < readCount w h')
    (fun h' m r hh => by rw [readCount_append]; omega) (by rw [hχ.input, hχ.input])
    (fun h' m hh => ?_) k h hj
  by_cases hm : w m ≠ 0 ∧ readCount w h' < N
  · rw [hχ.read _ _ _ hm.2 hm.1, hχ.read _ _ _ hm.2 hm.1, Function.update_of_ne]
    intro he
    rw [← he] at hh
    exact lt_irrefl _ hh
  · rw [hχ.noRead _ _ _ (by omega), hχ.noRead _ _ _ (by omega)]

/-- **The lazy sampling, from a history**: the uniform average over the coins of the continuation
from `h` is the lazy continuation from `h`. -/
theorem tsum_uniform_cont (σ : Strategy I M R O) (hχ : FreshCoins χ w i₀ K L) (x : Hist M R × O) :
    ∀ (k : ℕ) (h : Hist M R),
      ∑' a, PMF.uniformOfFintype (Fin N → C) a * cont σ χ a h k x =
        cont σ (lazy N w i₀ (fun h m => (PMF.uniformOfFintype C).bind (K h m)) L) () h k x
  | 0, h => by
    simp only [cont, hχ.input, lazy]
    rw [ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]
  | k + 1, h => by
    classical
    have ih := tsum_uniform_cont σ hχ x k
    simp only [cont, hχ.input, PMF.bind_apply]
    rw [tsum_mul_tsum_mul_comm]
    refine tsum_congr fun m => ?_
    congr 1
    simp only [lazy] at ih ⊢
    by_cases hm : w m ≠ 0 ∧ readCount w h < N
    · rw [ite_eq_left_of_eq_true _ _ (eq_true hm)]
      have hF := sum_uniform_update ⟨readCount w h, hm.2⟩
        (fun a => ∑' r, χ.reply a h m r * cont σ χ a (h ++ [(m, r)]) k x)
      rw [← tsum_fintype (L := SummationFilter.unconditional _),
        ← tsum_fintype (L := SummationFilter.unconditional _)] at hF
      have hupd : ∀ (a : Fin N → C) (y : C), (∑' r, χ.reply (Function.update a
          ⟨readCount w h, hm.2⟩ y) h m r * cont σ χ (Function.update a ⟨readCount w h, hm.2⟩ y)
            (h ++ [(m, r)]) k x) =
          ∑' r, K h m y r * cont σ χ a (h ++ [(m, r)]) k x := fun a y => by
        refine tsum_congr fun r => ?_
        rw [hχ.read _ _ _ hm.2 hm.1, cont_update_of_lt σ hχ a _ y k _
          (by simp only [readCount_append, readCount_singleton]; omega), Function.update_self]
      simp only [hupd] at hF
      rw [hF]
      have hin : ∀ a : Fin N → C, ∑ y, PMF.uniformOfFintype C y *
          ∑' r, K h m y r * cont σ χ a (h ++ [(m, r)]) k x =
          ∑' r, ((PMF.uniformOfFintype C).bind (K h m)) r * cont σ χ a (h ++ [(m, r)]) k x :=
        fun a => by
          rw [← tsum_fintype (L := SummationFilter.unconditional _)]
          simp_rw [PMF.bind_apply, ← ENNReal.tsum_mul_left, ← ENNReal.tsum_mul_right]
          rw [ENNReal.tsum_comm]
          exact tsum_congr fun r => tsum_congr fun y => by ring
      simp only [hin]
      rw [tsum_mul_tsum_mul_comm]
      exact tsum_congr fun r => by rw [ih]
    · rw [ite_eq_right_of_eq_false _ _ (eq_false hm)]
      have hn : ∀ a, χ.reply a h m = L h m := fun a => hχ.noRead _ _ _ (by omega)
      simp only [hn]
      rw [tsum_mul_tsum_mul_comm]
      exact tsum_congr fun r => by rw [ih]

/-- **The lazy sampling**: the experiment against a challenger reading fresh coins is the lazy
experiment, each read answered from the averaged kernel `(uniform C).bind (K h m)`. -/
theorem exper_eq_lazy (σ : Strategy I M R O) (hχ : FreshCoins χ w i₀ K L) (Q : ℕ) :
    exper σ χ Q = exper σ (lazy N w i₀ (fun h m => (PMF.uniformOfFintype C).bind (K h m)) L) Q := by
  ext x
  simp only [exper, PMF.bind_apply, hχ.coins]
  rw [tsum_uniform_cont σ hχ x Q []]
  simp [lazy]

/-- **Two challengers reading fresh coins with the same averaged kernels have the same
experiment**, whatever their coin types `C` and `C'`: the averages agree at every read (a move with
`w m ≠ 0` after fewer than `N` reads). -/
theorem exper_eq_of_freshCoins {C' : Type*} [Fintype C'] [Nonempty C'] (σ : Strategy I M R O)
    {χ' : Challenger (Fin N → C') I M R} {K' : Hist M R → M → C' → PMF R}
    (hχ : FreshCoins χ w i₀ K L) (hχ' : FreshCoins χ' w i₀ K' L)
    (hK : ∀ h m, w m ≠ 0 → readCount w h < N →
      (PMF.uniformOfFintype C).bind (K h m) = (PMF.uniformOfFintype C').bind (K' h m))
    (Q : ℕ) : exper σ χ Q = exper σ χ' Q := by
  rw [exper_eq_lazy σ hχ, exper_eq_lazy σ hχ', lazy_congr w i₀ L hK]

end Fresh

end GordieHowe.Interaction
