-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Fin.Tuple.Basic
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.Order.Fin.Basic
public import Mathlib.Tactic.Ring
public import Mathlib.Data.List.OfFn
public import Mathlib.Data.Fintype.Inv

@[expose] public section

/-!
# Counting functions `Fin S → Fin M` by a threshold on their values

General `Finset`/`Fintype` cardinality facts, kept here as candidates for
upstreaming. The main result, `Finset.card_filter_lt_fin_lt_choose_sum`, counts
the fraction of functions `Fin S → Fin M` for which fewer than `n` coordinates
fall below a threshold `a ≤ M`: a binomial tail. It is used for Falcon's
`HashToPoint` rejection-sampling completeness error (`GordieHowe.Falcon512.unsupportedFraction_le`).
-/

/-- Reindexing a filtered `Finset.univ` along an equivalence of the ambient
types does not change its cardinality. -/
theorem Finset.card_filter_congr {α β : Type*} [Fintype α] [Fintype β]
    (e : α ≃ β) (P : β → Prop) [DecidablePred P] [DecidablePred fun a => P (e a)] :
    (Finset.univ.filter fun a => P (e a)).card = (Finset.univ.filter P).card :=
  Finset.card_equiv e fun i => by simp

/-- The number of `p : A × B` satisfying `Q`, as a sum over the first
coordinate of the number of second coordinates satisfying `Q`. -/
theorem Finset.card_filter_prod_eq_sum {A B : Type*} [Fintype A] [Fintype B]
    (Q : A × B → Prop) [DecidablePred Q] :
    (Finset.univ.filter Q).card = ∑ a : A, (Finset.univ.filter fun b => Q (a, b)).card := by
  classical
  rw [← Fintype.card_subtype Q,
    Fintype.card_congr (Equiv.subtypeProdEquivSigmaSubtype fun a b => Q (a, b)),
    Fintype.card_sigma]
  exact Finset.sum_congr rfl fun a _ => Fintype.card_subtype fun b => Q (a, b)

/-- Splitting off the last coordinate: the number of accepted coordinates of
`Fin.snoc front last` is the number accepted among `front` plus one more if
`last` is itself accepted. -/
theorem Finset.card_filter_snoc {M : Type*} (P : M → Prop) [DecidablePred P]
    {S : ℕ} (front : Fin S → M) (last : M) :
    (Finset.univ.filter fun i : Fin (S + 1) => P ((Fin.snoc front last : Fin (S + 1) → M) i)).card
      = (Finset.univ.filter fun i => P (front i)).card + (if P last then 1 else 0) := by
  simp only [Finset.card_filter, Fin.sum_univ_castSucc, Fin.snoc_castSucc, Fin.snoc_last]

/-- The number of entries of `List.ofFn f` accepted by `p` is the number of
indices `i` with `p (f i)`. -/
theorem List.countP_ofFn {α : Type*} (p : α → Bool) : ∀ {n : ℕ} (f : Fin n → α),
    (List.ofFn f).countP p = (Finset.univ.filter fun i => p (f i) = true).card := by
  intro n f
  induction f using Fin.snocInduction with
  | elim0 => simp
  | snoc x x0 ih =>
      rw [Finset.card_filter_snoc (fun a => p a = true) x x0, ← ih, List.ofFn_succ',
        List.concat_eq_append, List.countP_append]
      simp [Fin.snoc_castSucc, Fin.snoc_last]

/-- The number of `m : Fin M` with `(m : ℕ) < a`, for `a ≤ M`, is `a`. -/
theorem Finset.card_filter_val_lt_fin (M a : ℕ) (ha : a ≤ M) :
    (Finset.univ.filter fun m : Fin M => (m : ℕ) < a).card = a := by
  have hset : Finset.univ.filter (fun m : Fin M => (m : ℕ) < a)
      = Finset.univ.map (Fin.castLEOrderEmb ha).toEmbedding := by
    ext m
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map,
      RelEmbedding.coe_toEmbedding, Fin.castLEOrderEmb_apply]
    constructor
    · intro hm
      exact ⟨⟨(m : ℕ), hm⟩, Fin.ext rfl⟩
    · rintro ⟨i, rfl⟩
      simpa using i.2
  rw [hset, Finset.card_map, Finset.card_univ, Fintype.card_fin]

/-- The number of `v : Fin S → Fin M` with exactly `k` coordinates below `a`
(a natural number cast, `a ≤ M`) is `S.choose k * a ^ k * (M - a) ^ (S - k)`:
choose the `k` accepted positions, then an accepted value (`a` choices) for
each and a rejected value (`M - a` choices) for the rest. -/
theorem Finset.card_filter_lt_fin_eq_choose {M a : ℕ} (ha : a ≤ M) :
    ∀ S k : ℕ,
      (Finset.univ.filter fun v : Fin S → Fin M =>
        (Finset.univ.filter fun i => (v i : ℕ) < a).card = k).card
        = S.choose k * a ^ k * (M - a) ^ (S - k) := by
  intro S
  induction S with
  | zero =>
    intro k
    have hempty : ∀ v : Fin 0 → Fin M,
        (Finset.univ.filter fun i : Fin 0 => (v i : ℕ) < a).card = 0 := fun v => by simp
    rcases Nat.eq_zero_or_pos k with hk | hk
    · subst hk
      simp
    · have hemp : (Finset.univ.filter fun v : Fin 0 → Fin M =>
          (Finset.univ.filter fun i => (v i : ℕ) < a).card = k) = ∅ :=
        Finset.filter_false_of_mem fun v _ => by rw [hempty v]; omega
      rw [hemp, Finset.card_empty, Nat.choose_eq_zero_of_lt hk]
      ring
  | succ S ih =>
    intro k
    classical
    set e : Fin M × (Fin S → Fin M) ≃ (Fin (S + 1) → Fin M) :=
      Fin.snocEquiv (fun _ : Fin (S + 1) => Fin M) with he
    set Pred : (Fin (S + 1) → Fin M) → Prop :=
      fun v => (Finset.univ.filter fun i => (v i : ℕ) < a).card = k with hPred
    have hstep := Finset.card_filter_congr e Pred
    have hpt : ∀ p : Fin M × (Fin S → Fin M),
        Pred (e p) ↔ (Finset.univ.filter fun i => (p.2 i : ℕ) < a).card
            + (if (p.1 : ℕ) < a then 1 else 0) = k := by
      intro p
      have heq := Finset.card_filter_snoc (fun x : Fin M => (x : ℕ) < a) p.2 p.1
      have hep : e p = Fin.snoc p.2 p.1 := rfl
      show (Finset.univ.filter fun i => (e p i : ℕ) < a).card = k ↔ _
      rw [hep, heq]
    have hfilter_eq : (Finset.univ.filter fun p : Fin M × (Fin S → Fin M) => Pred (e p))
        = Finset.univ.filter fun p : Fin M × (Fin S → Fin M) =>
            (Finset.univ.filter fun i => (p.2 i : ℕ) < a).card
              + (if (p.1 : ℕ) < a then 1 else 0) = k :=
      Finset.filter_congr fun p _ => hpt p
    have hkey : (Finset.univ.filter Pred).card
        = a * (Finset.univ.filter fun front : Fin S → Fin M =>
              (Finset.univ.filter fun i => (front i : ℕ) < a).card + 1 = k).card
          + (M - a) * (Finset.univ.filter fun front : Fin S → Fin M =>
              (Finset.univ.filter fun i => (front i : ℕ) < a).card = k).card := by
      rw [← hstep, hfilter_eq, Finset.card_filter_prod_eq_sum]
      have hterm : ∀ m : Fin M,
          (Finset.univ.filter fun front : Fin S → Fin M =>
              (Finset.univ.filter fun i => (front i : ℕ) < a).card
                + (if (m : ℕ) < a then 1 else 0) = k).card
            = if (m : ℕ) < a then
                (Finset.univ.filter fun front : Fin S → Fin M =>
                  (Finset.univ.filter fun i => (front i : ℕ) < a).card + 1 = k).card
              else
                (Finset.univ.filter fun front : Fin S → Fin M =>
                  (Finset.univ.filter fun i => (front i : ℕ) < a).card = k).card := by
        intro m
        split_ifs <;> simp
      rw [Finset.sum_congr rfl fun m _ => hterm m,
        Finset.sum_ite
          (fun _ : Fin M => (Finset.univ.filter fun front : Fin S → Fin M =>
              (Finset.univ.filter fun i => (front i : ℕ) < a).card + 1 = k).card)
          (fun _ : Fin M => (Finset.univ.filter fun front : Fin S → Fin M =>
              (Finset.univ.filter fun i => (front i : ℕ) < a).card = k).card),
        Finset.sum_const, Finset.sum_const, smul_eq_mul, smul_eq_mul,
        Finset.card_filter_val_lt_fin M a ha]
      have hcompl : (Finset.univ.filter fun m : Fin M => ¬ (m : ℕ) < a).card = M - a := by
        have htot := Finset.card_filter_add_card_filter_not
          (s := (Finset.univ : Finset (Fin M))) (fun m : Fin M => (m : ℕ) < a)
        rw [Finset.card_filter_val_lt_fin M a ha, Finset.card_univ, Fintype.card_fin] at htot
        omega
      rw [hcompl]
    rw [hkey]
    by_cases hk : k = 0
    · subst hk
      have hz : (Finset.univ.filter fun front : Fin S → Fin M =>
          (Finset.univ.filter fun i => (front i : ℕ) < a).card + 1 = 0).card = 0 := by
        apply Finset.card_eq_zero.mpr
        apply Finset.filter_eq_empty_iff.mpr
        intro front _
        omega
      rw [hz, ih 0]
      simp only [Nat.choose_zero_right, pow_zero, Nat.sub_zero, one_mul]
      ring
    · obtain ⟨k', rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk
      simp only [Nat.succ_eq_add_one]
      have e1 : (Finset.univ.filter fun front : Fin S → Fin M =>
          (Finset.univ.filter fun i => (front i : ℕ) < a).card + 1 = k' + 1).card
          = (Finset.univ.filter fun front : Fin S → Fin M =>
              (Finset.univ.filter fun i => (front i : ℕ) < a).card = k').card := by
        congr 1
        apply Finset.filter_congr
        intro front _
        omega
      rw [e1, ih k', ih (k' + 1)]
      have hpascal : (S + 1).choose (k' + 1) = S.choose k' + S.choose (k' + 1) :=
        Nat.choose_succ_succ' S k'
      have hexp1 : S + 1 - (k' + 1) = S - k' := by omega
      by_cases hkS : k' < S
      · have hexp2 : S - (k' + 1) + 1 = S - k' := by omega
        have hpow : (M - a) * (M - a) ^ (S - (k' + 1)) = (M - a) ^ (S - k') := by
          rw [← pow_succ', hexp2]
        have hterm2 : (M - a) * (S.choose (k' + 1) * a ^ (k' + 1) * (M - a) ^ (S - (k' + 1)))
            = S.choose (k' + 1) * a ^ (k' + 1) * (M - a) ^ (S - k') := by
          rw [← hpow]; ring
        rw [hexp1, hpascal, hterm2]
        ring
      · simp only [not_lt] at hkS
        have hz2 : S.choose (k' + 1) = 0 := Nat.choose_eq_zero_of_lt (by omega)
        rw [hexp1, hpascal, hz2]
        ring

/-- The number of `v : Fin S → Fin M` for which fewer than `n` coordinates are
below `a` (`a ≤ M`) is the binomial tail `∑_{k<n} C(S,k) a^k (M-a)^(S-k)`. -/
theorem Finset.card_filter_lt_fin_lt_choose_sum {M a : ℕ} (ha : a ≤ M) (S n : ℕ) :
    (Finset.univ.filter fun v : Fin S → Fin M =>
      (Finset.univ.filter fun i => (v i : ℕ) < a).card < n).card
      = ∑ k ∈ Finset.range n, S.choose k * a ^ k * (M - a) ^ (S - k) := by
  classical
  rw [Finset.card_eq_sum_card_fiberwise
    (f := fun v : Fin S → Fin M => (Finset.univ.filter fun i => (v i : ℕ) < a).card)
    (t := Finset.range n) (by
      intro v hv
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hv
      exact Finset.mem_range.mpr hv)]
  refine Finset.sum_congr rfl fun k hk => ?_
  rw [Finset.mem_range] at hk
  rw [← Finset.card_filter_lt_fin_eq_choose ha S k]
  congr 1
  rw [Finset.filter_filter]
  apply Finset.filter_congr
  intro v _
  constructor
  · rintro ⟨_, h2⟩; exact h2
  · intro h2; exact ⟨by omega, h2⟩

/-! ### Evaluating the binomial tail sum without Pascal's rule

`Nat.choose`'s own equation `choose (n+1) (k+1) = choose n k + choose n (k+1)` is a Pascal
recursion: evaluating it from scratch for each `k` up to some `n` revisits the same sub-values
exponentially many times. `binomialTail` instead carries the coefficient `S.choose k` alongside the
partial sum, updating it by one exact multiplication and division per step
(`S.choose (k+1) = S.choose k * (S - k) / (k + 1)`), so evaluating the whole tail sum up to `n`
costs `O(n)` arithmetic operations. -/

/-- The partial binomial tail sum `∑_{k<n} C(S,k) a^k (M-a)^(S-k)` together
with the coefficient `C(S,n)`, computed by structural recursion on `n` without
calling `Nat.choose`. -/
def binomialTailAux (S a M : ℕ) : ℕ → ℕ × ℕ
  | 0 => (0, 1)
  | k + 1 =>
    let p := binomialTailAux S a M k
    (p.1 + p.2 * a ^ k * (M - a) ^ (S - k), p.2 * (S - k) / (k + 1))

theorem binomialTailAux_snd (S a M : ℕ) : ∀ n, (binomialTailAux S a M n).2 = S.choose n
  | 0 => (Nat.choose_zero_right S).symm
  | n + 1 => by
      show (binomialTailAux S a M n).2 * (S - n) / (n + 1) = S.choose (n + 1)
      rw [binomialTailAux_snd S a M n, ← Nat.choose_succ_right_eq S n,
        Nat.mul_div_cancel _ (Nat.succ_pos n)]

theorem binomialTailAux_fst (S a M : ℕ) :
    ∀ n, (binomialTailAux S a M n).1 = ∑ k ∈ Finset.range n, S.choose k * a ^ k * (M - a) ^ (S - k)
  | 0 => rfl
  | n + 1 => by
      show (binomialTailAux S a M n).1 + (binomialTailAux S a M n).2 * a ^ n * (M - a) ^ (S - n)
        = ∑ k ∈ Finset.range (n + 1), S.choose k * a ^ k * (M - a) ^ (S - k)
      rw [binomialTailAux_fst S a M n, binomialTailAux_snd S a M n, Finset.sum_range_succ]

/-- The binomial tail sum `∑_{k<n} C(S,k) a^k (M-a)^(S-k)`, evaluated in `O(n)`
arithmetic operations. -/
def binomialTail (S a M n : ℕ) : ℕ := (binomialTailAux S a M n).1

theorem binomialTail_eq (S a M n : ℕ) :
    binomialTail S a M n = ∑ k ∈ Finset.range n, S.choose k * a ^ k * (M - a) ^ (S - k) :=
  binomialTailAux_fst S a M n

/-- **Extension along an injective map from a finite type**, computably: `g a` at `f a`, the
default `e` off the range of `f`. It is `Function.extend f g e` (`Function.extendFin_eq`). -/
def Function.extendFin {α β γ : Type*} [Fintype α] [DecidableEq β] (f : α → β)
    (hf : Function.Injective f) (g : α → γ) (e : β → γ) (b : β) : γ :=
  if h : ∃ a, f a = b then
    g (Fintype.choose (fun a => f a = b) (h.elim fun a ha => ⟨a, ha, fun _ h' => hf (h'.trans ha.symm)⟩))
  else e b

theorem Function.extendFin_apply {α β γ : Type*} [Fintype α] [DecidableEq β] {f : α → β}
    (hf : Function.Injective f) (g : α → γ) (e : β → γ) (a : α) :
    Function.extendFin f hf g e (f a) = g a := by
  unfold Function.extendFin
  split
  · exact congrArg g (hf (Fintype.choose_spec (fun a' => f a' = f a) _))
  · rename_i h
    exact absurd ⟨a, rfl⟩ h

theorem Function.extendFin_apply' {α β γ : Type*} [Fintype α] [DecidableEq β] {f : α → β}
    (hf : Function.Injective f) (g : α → γ) (e : β → γ) {b : β} (hb : ¬ ∃ a, f a = b) :
    Function.extendFin f hf g e b = e b := by
  unfold Function.extendFin
  split
  · exact absurd ‹_› hb
  · rfl

theorem Function.extendFin_eq {α β γ : Type*} [Fintype α] [DecidableEq β] {f : α → β}
    (hf : Function.Injective f) (g : α → γ) (e : β → γ) :
    Function.extendFin f hf g e = Function.extend f g e := by
  funext b
  by_cases hb : ∃ a, f a = b
  · obtain ⟨a, rfl⟩ := hb
    rw [Function.extendFin_apply, hf.extend_apply]
  · rw [Function.extendFin_apply' hf g e hb, Function.extend_apply' _ _ _ hb]
