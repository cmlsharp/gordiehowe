-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Model.Quantum.O2H.SaltReprogram
public import GordieHowe.Model.Quantum.Interactive.QueryBoundedZK
public import GordieHowe.Foundations.ToMathlib.PMFUniform

@[expose] public section

/-!
# Reprogramming at hidden fresh salts against interactive adversaries

`GordieHowe/Model/Quantum/O2H/SaltReprogram.lean` bounds, for distinguishers of the pure game with
a query budget, the change when a challenger's reads of the random oracle at hidden fresh salts
are replaced by fresh functions. This file carries the bound to the interactive adversaries of
`GordieHowe/Model/Quantum/Interactive` (`AdaptiveIAlg`) against challengers (`Challenger`).

- `Challenger.AnswersBy C resp`: the challenger answers request number `j` (below `C.Q`), after
  any history of length `j`, by `resp c H j req`, from its coins `c`, the oracle `H` and the
  request, and reprograms nothing. `AnswersBy.oracleIn`, `AnswersBy.answerAfter`,
  `AnswersBy.oracle`: its environment of the pure game (`Challenger.toPureEnv`) answers and keeps
  the oracle accordingly.
- `Challenger.SaltFreshPair emb ν C₀ C₁`: `C₀` answers request by request with `ans c j req g H`
  from a part `c ← ζ` of its coins, the values `g` of `H` on the slices `emb (ρ i, ·)` of `K` salts
  `ρ ← ν` drawn independently of `c` from the rest of its coins, and `H` read only outside the
  range of `emb`; `C₁` answers with the same `ans`, with `K` independent uniform functions from its
  coins in place of `g`. The replies of `C₀` depend on the salts only through `g`.
  `SaltFreshPair.acceptProbAt_salt`, `SaltFreshPair.acceptProbAt_fresh`: in the pure game they are
  the salted and the fresh environments of `O2H/SaltReprogram.lean` (`saltEnv`, `freshEnv`) at
  the decoded coins; `SaltFreshPair.sum_salt`, `SaltFreshPair.sum_fresh`: averaged over an oracle
  law and their coins, their acceptance probabilities are those of the two environments.
- `AdaptiveIAlg.pureDil o`: the dilation of the adversary for the output `o`
  (`KindAlg.dilate`) with its post phase moved into query slots (`Distinguisher.withPostSlots`),
  a distinguisher with a budget of `budget + post` query slots (`AdaptiveIAlg.pureDilBudget`).
  `AdaptiveIAlg.toReal_outLaw_compose_eq`: at every oracle `H`, the composition with a challenger
  outputs `o` with the coin average of its acceptance probabilities at `H` (deferred
  measurement).
- `AdaptiveIAlg.advantage_salt_fresh_le`: for an injective `emb` and an oracle law uniform on the
  range of `emb` given the rest (`IsUniformOnRange`), the probabilities, averaged over that law,
  that the adversary outputs `o` against `C₀` and against `C₁` differ by at most
  `Pr[two salts collide] + 2 (budget + post) √(width ε)`, for `ε` bounding the probability that a
  given point of `S` is a salt.
  `AdaptiveIAlg.advantage_salt_fresh_le_of_queries_le`: at most
  `Pr[two salts collide] + 2 t √ε` when `width (budget + post) ≤ t`
  (`AdaptiveIAlg.two_mul_sqrt_le_of_mul_le`).
- For a split `e : Y ≃ Y₁ × Y₂` of the oracle's values (`O2H/SaltReprogram.lean`):
  `Challenger.SaltFreshPairOn emb e ν C₀ C₁`, where `C₀` reads the first components on the slices
  (`slicesOn`) and the oracle's first components only outside the range (`ReadsOffRangeOn`), and
  `C₁` reads fresh functions `U → Y₁`; `SaltFreshPairOn.ansFin`,
  `SaltFreshPairOn.readsOffRange_ansFin`, `SaltFreshPairOn.acceptProbAt_salt`,
  `SaltFreshPairOn.acceptProbAt_fresh`, `SaltFreshPairOn.sum_salt`, `SaltFreshPairOn.sum_fresh`
  (with `saltEnvOn`); `SaltFreshPair.toOn`: a `SaltFreshPair` is a `SaltFreshPairOn` at
  `wholeSplit Y`, and the statements about `SaltFreshPair` are derived through it.
  `AdaptiveIAlg.advantage_saltOn_fresh_le`, `AdaptiveIAlg.advantage_saltOn_fresh_le_of_queries_le`:
  the bounds for an oracle law uniform in the first components (`IsUniformOnRangeOn`), from which
  `advantage_salt_fresh_le` and `advantage_salt_fresh_le_of_queries_le` are derived.
-/

open Finset
open scoped BigOperators ENNReal

namespace GordieHowe.Quantum

/-! ### Challengers that answer request by request -/

namespace Challenger

variable {X Y Req Resp : Type} [Fintype X] [DecidableEq X] [Fintype Y] [Nonempty Y]
  (C : Challenger X Y Req Resp)

/-- **A challenger that answers request by request and reprograms nothing**: the reply program
of request number `j < Q` returns the response `resp c H j req` at the coins `c` and the oracle `H`,
after any history of length `j`, and no assignments. -/
def AnswersBy (resp : C.Coins → (X → Y) → ℕ → Req → Option Resp) : Prop :=
  ∀ c hist req H, hist.length < C.Q →
    (C.respond c hist req).run H = ⟨resp c H hist.length req, []⟩

variable {C} {resp : C.Coins → (X → Y) → ℕ → Req → Option Resp}

/-- **The state of the pure game's challenger** answering request by request: the base oracle of
the tape, no assignments, and a history of the requests answered so far. -/
theorem AnswersBy.oracleIn (h : C.AnswersBy resp) (ω : (X → Y) × C.Coins) (rs : List Req) :
    (C.toPureEnv.oracleIn ω rs).base = ω.1 ∧ (C.toPureEnv.oracleIn ω rs).ass = [] ∧
      (C.toPureEnv.oracleIn ω rs).hist.length = min rs.length C.Q := by
  induction rs using List.reverseRecOn with
  | nil => exact ⟨rfl, rfl, by simp [Env.oracleIn_nil, toPureEnv]⟩
  | append_singleton rs req ih =>
    obtain ⟨hb, ha, hl⟩ := ih
    rw [Env.oracleIn_append_singleton, Env.update]
    split_ifs with hq
    · set s := C.toPureEnv.oracleIn ω rs
      have hl' : s.hist.length < C.Q := by
        rw [hl]
        exact lt_of_le_of_lt (min_le_left _ _) hq
      have hrun : (C.respond ω.2 s.hist req).run (s.base.reprogram s.ass) =
          ⟨resp ω.2 ω.1 s.hist.length req, []⟩ := by
        rw [hb, ha]
        exact h _ _ _ _ hl'
      simp only [toPureEnv, hrun, List.append_nil, List.length_append, List.length_singleton]
      refine ⟨hb, ha, ?_⟩
      rw [hl]
      simp only at hq
      omega
    · simp only at hq
      refine ⟨hb, ha, ?_⟩
      rw [hl, List.length_append, List.length_singleton]
      omega

/-- **A challenger answering request by request answers request number `j < Q` by `resp`**, and
later requests by `none`, in the pure game. -/
theorem AnswersBy.answerAfter (h : C.AnswersBy resp) (ω : (X → Y) × C.Coins) (rs : List Req)
    (req : Req) :
    C.toPureEnv.answerAfter ω rs req =
      if rs.length < C.Q then resp ω.2 ω.1 rs.length req else none := by
  rw [Env.answerAfter]
  split_ifs with hq
  · obtain ⟨hb, ha, hl⟩ := h.oracleIn ω rs
    have hl' : (C.toPureEnv.oracleIn ω rs).hist.length = rs.length := by
      rw [hl]
      exact min_eq_left hq.le
    change ((C.respond ω.2 (C.toPureEnv.oracleIn ω rs).hist req).run
      ((C.toPureEnv.oracleIn ω rs).base.reprogram (C.toPureEnv.oracleIn ω rs).ass)).response = _
    rw [hb, ha]
    change ((C.respond ω.2 (C.toPureEnv.oracleIn ω rs).hist req).run ω.1).response = _
    rw [h _ _ _ _ (hl'.trans_lt hq), hl']
  · rfl

/-- **A challenger answering request by request keeps the oracle of the tape** in the pure
game. -/
theorem AnswersBy.oracle (h : C.AnswersBy resp) (ω : (X → Y) × C.Coins) {m : ℕ}
    (lg : LogReg Req m) : C.toPureEnv.oracle ω lg = ω.1 := by
  obtain ⟨hb, ha, -⟩ := h.oracleIn ω (requests lg)
  change (C.toPureEnv.oracleIn ω (requests lg)).base.reprogram
    (C.toPureEnv.oracleIn ω (requests lg)).ass = ω.1
  rw [hb, ha]
  rfl

end Challenger

/-! ### A salted challenger and its fresh counterpart -/

namespace Challenger

variable {X Y Req Resp S U : Type} [Fintype X] [DecidableEq X] [Fintype Y] [Nonempty Y]
  [Fintype U] [DecidableEq U] {K : ℕ}

/-- **A challenger reading the oracle at hidden fresh salts, and its fresh counterpart.** The
challenger `C₀` answers request by request (`AnswersBy`) with `ans c j req g H`: from a part
`c ← ζ` of its coins, the request number and the request, the values `g = slices emb H ρ` of the
oracle on the slices `emb (ρ i, ·)` of `K` salts `ρ ← ν` drawn from the rest of its coins
independently of `c` (`map_dec₀`), and the oracle `H` read only outside the range of the
embedding `emb` (`readsOffRange`). Its replies depend on the salts only through the values on
the slices. The challenger `C₁` answers with the same
`ans`, with `K` uniform functions `Z` drawn independently of `c` (`map_dec₁`) in place of `g`.
Both answer the same number of requests. -/
structure SaltFreshPair (emb : S × U → X) (ν : PMF (Fin K → S))
    (C₀ C₁ : Challenger X Y Req Resp) where
  /-- The other coins. -/
  Coins' : Type
  [instFintype : Fintype Coins']
  /-- The law of the other coins. -/
  ζ : PMF Coins'
  /-- The answer to request number `j` with request `req`, from the other coins, the values on
  the slices and the oracle. -/
  ans : Coins' → ℕ → Req → (Fin K → U → Y) → (X → Y) → Option Resp
  /-- The answers read the oracle only outside the range of the embedding. -/
  readsOffRange : ReadsOffRange emb ans
  /-- The other coins and the salts of `C₀`'s coins. -/
  dec₀ : C₀.Coins → Coins' × (Fin K → S)
  /-- The salts are drawn from `ν` independently of the other coins. -/
  map_dec₀ : C₀.coins.map dec₀ = prodLaw ζ ν
  /-- `C₀` answers with the values of the oracle on the slices of its salts. -/
  salted : C₀.AnswersBy fun c H j req => ans (dec₀ c).1 j req (slices emb H (dec₀ c).2) H
  /-- The fresh functions and the other coins of `C₁`'s coins. -/
  dec₁ : C₁.Coins → (Fin K → U → Y) × Coins'
  /-- The fresh functions are uniform and independent of the other coins. -/
  map_dec₁ : C₁.coins.map dec₁ = prodLaw (PMF.uniformOfFintype (Fin K → U → Y)) ζ
  /-- `C₁` answers with the fresh functions. -/
  fresh : C₁.AnswersBy fun c H j req => ans (dec₁ c).2 j req (dec₁ c).1 H
  /-- Both answer the same number of requests. -/
  Q_eq : C₁.Q = C₀.Q

attribute [instance] SaltFreshPair.instFintype

namespace SaltFreshPair

/-- An average over a product law is an iterated average. -/
theorem sum_prodLaw {α β : Type*} [Fintype α] [Fintype β] (p : PMF α) (q : PMF β)
    (f : α × β → ℝ) :
    ∑ x, (prodLaw p q x).toReal * f x = ∑ a, (p a).toReal * ∑ b, (q b).toReal * f (a, b) := by
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [prodLaw_apply, ENNReal.toReal_mul, mul_assoc]

/-- An average of a constant is the constant. -/
theorem sum_toReal_mul_const {β : Type*} [Fintype β] (q : PMF β) (r : ℝ) :
    ∑ b, (q b).toReal * r = r := by
  rw [← Finset.sum_mul, PMF.sum_toReal, one_mul]

end SaltFreshPair

variable {Y₁ Y₂ : Type} [Fintype Y₁] [Nonempty Y₁]

/-- **A challenger reading the first components of the oracle at hidden fresh salts, and its
fresh counterpart**, for a split `e : Y ≃ Y₁ × Y₂` of the oracle's values. The challenger `C₀`
answers request by request (`AnswersBy`) with `ans c j req g H`: from a part `c ← ζ` of its
coins, the request number and the request, the first components `g = slicesOn emb e H ρ` of the
oracle on the slices `emb (ρ i, ·)` of `K` salts `ρ ← ν` drawn from the rest of its coins
independently of `c` (`map_dec₀`), and the oracle `H` read in its first components only outside
the range of the embedding `emb` (`readsOffRange`: its second components may be read
everywhere). The challenger `C₁` answers with the same `ans`, with `K` uniform functions
`Z : Fin K → U → Y₁` drawn independently of `c` (`map_dec₁`) in place of `g`. Both answer the
same number of requests. `SaltFreshPair` is the case of the split with a trivial second component
(`SaltFreshPair.toOn`). -/
structure SaltFreshPairOn (emb : S × U → X) (e : Y ≃ Y₁ × Y₂) (ν : PMF (Fin K → S))
    (C₀ C₁ : Challenger X Y Req Resp) where
  /-- The other coins. -/
  Coins' : Type
  [instFintype : Fintype Coins']
  /-- The law of the other coins. -/
  ζ : PMF Coins'
  /-- The answer to request number `j` with request `req`, from the other coins, the first
  components on the slices and the oracle. -/
  ans : Coins' → ℕ → Req → (Fin K → U → Y₁) → (X → Y) → Option Resp
  /-- The answers read the oracle's first components only outside the range of the embedding. -/
  readsOffRange : ReadsOffRangeOn emb e ans
  /-- The other coins and the salts of `C₀`'s coins. -/
  dec₀ : C₀.Coins → Coins' × (Fin K → S)
  /-- The salts are drawn from `ν` independently of the other coins. -/
  map_dec₀ : C₀.coins.map dec₀ = prodLaw ζ ν
  /-- `C₀` answers with the first components of the oracle on the slices of its salts. -/
  salted : C₀.AnswersBy fun c H j req => ans (dec₀ c).1 j req (slicesOn emb e H (dec₀ c).2) H
  /-- The fresh functions and the other coins of `C₁`'s coins. -/
  dec₁ : C₁.Coins → (Fin K → U → Y₁) × Coins'
  /-- The fresh functions are uniform and independent of the other coins. -/
  map_dec₁ : C₁.coins.map dec₁ = prodLaw (PMF.uniformOfFintype (Fin K → U → Y₁)) ζ
  /-- `C₁` answers with the fresh functions. -/
  fresh : C₁.AnswersBy fun c H j req => ans (dec₁ c).2 j req (dec₁ c).1 H
  /-- Both answer the same number of requests. -/
  Q_eq : C₁.Q = C₀.Q

attribute [instance] SaltFreshPairOn.instFintype

namespace SaltFreshPairOn

variable {emb : S × U → X} {e : Y ≃ Y₁ × Y₂} {ν : PMF (Fin K → S)}
  {C₀ C₁ : Challenger X Y Req Resp} (P : SaltFreshPairOn emb e ν C₀ C₁)

/-- The answer function indexed by the request numbers below `Q`. -/
def ansFin (Q : ℕ) : P.Coins' → Fin Q → Req → (Fin K → U → Y₁) → (X → Y) → Option Resp :=
  fun c j => P.ans c j

omit [Fintype X] [DecidableEq X] [Fintype Y] [Nonempty Y] in
/-- The indexed answer function reads the oracle's first components only outside the range of
the embedding. -/
theorem readsOffRange_ansFin (Q : ℕ) : ReadsOffRangeOn emb e (P.ansFin Q) :=
  fun c j => P.readsOffRange c j

variable [Fintype Req] [Fintype Resp] [DecidableEq Req] [DecidableEq Resp] [AddGroup Y]
  {W : Type} [Fintype W] {n m : ℕ} (D : Distinguisher W X Y Req Resp n m)
  (post : (X → Y) → QState (DReg W n X Y Req Resp) ≃ₗᵢ[ℂ] QState (DReg W n X Y Req Resp))
  (μH : PMF (X → Y))

/-- **`C₀` in the pure game is the salted challenger reading first components** at its other
coins and salts, for any fresh functions on the tape. -/
theorem acceptProbAt_salt (H : X → Y) (c : C₀.Coins) (Z : Fin K → U → Y₁) :
    D.acceptProbAt C₀.toPureEnv post (H, c) =
      D.acceptProbAt (saltEnvOn emb e (P.ansFin C₀.Q) μH P.ζ ν) post
        ((H, Z, (P.dec₀ c).1), (P.dec₀ c).2) := by
  refine D.acceptProbAt_congr _ _ (fun lg k => ?_) (fun lg => ?_) post
  · unfold Env.answer
    refine congrArg ((lg k).elim none) (funext fun req => ?_)
    rw [P.salted.answerAfter]
    simp only [Env.answerAfter, saltEnvOn, ansFin]
    split_ifs <;> rfl
  · rw [P.salted.oracle]
    simp only [Env.oracle, Env.oracleIn_of_keepsState (keepsState_saltEnvOn emb e _ μH P.ζ ν)]
    rfl

/-- **`C₁` in the pure game is the fresh challenger** at its fresh functions and other coins,
for any salts on the tape. -/
theorem acceptProbAt_fresh (H : X → Y) (c : C₁.Coins) (ρ : Fin K → S) :
    D.acceptProbAt C₁.toPureEnv post (H, c) =
      D.acceptProbAt (freshEnv (P.ansFin C₀.Q) μH P.ζ ν) post
        ((H, (P.dec₁ c).1, (P.dec₁ c).2), ρ) := by
  refine D.acceptProbAt_congr _ _ (fun lg k => ?_) (fun lg => ?_) post
  · unfold Env.answer
    refine congrArg ((lg k).elim none) (funext fun req => ?_)
    rw [P.fresh.answerAfter, P.Q_eq]
    simp only [Env.answerAfter, freshEnv, ansFin]
    split_ifs <;> rfl
  · rw [P.fresh.oracle]
    simp only [Env.oracle, Env.oracleIn_of_keepsState (keepsState_freshEnv _ μH P.ζ ν)]
    rfl

/-- **The pure game against `C₀`, averaged over the oracle law, is the salted game reading
first components.** -/
theorem sum_salt [Fintype S] [DecidableEq S] :
    ∑ H, (μH H).toReal * ∑ c, (C₀.coins c).toReal * D.acceptProbAt C₀.toPureEnv noPost (H, c) =
      D.acceptProb (saltEnvOn emb e (P.ansFin C₀.Q) μH P.ζ ν) noPost := by
  set E := saltEnvOn emb e (P.ansFin C₀.Q) μH P.ζ ν
  let Z₀ : Fin K → U → Y₁ := fun _ _ => Classical.arbitrary Y₁
  have hZ : ∀ H Z c' ρ, D.acceptProbAt E noPost ((H, Z, c'), ρ) =
      D.acceptProbAt E noPost ((H, Z₀, c'), ρ) := fun H Z c' ρ => by
    rw [D.acceptProbAt_saltEnvOn, D.acceptProbAt_saltEnvOn]
  have hc : ∀ H, ∑ c, (C₀.coins c).toReal * D.acceptProbAt C₀.toPureEnv noPost (H, c) =
      ∑ x, (prodLaw P.ζ ν x).toReal * D.acceptProbAt E noPost ((H, Z₀, x.1), x.2) := fun H => by
    simp only [P.acceptProbAt_salt D noPost μH H _ Z₀]
    rw [← P.map_dec₀, PMF.sum_toReal_map_mul]
  simp only [hc]
  change _ = ∑ ω, (saltLaw μH P.ζ ν ω).toReal * D.acceptProbAt E noPost ω
  rw [saltLaw, SaltFreshPair.sum_prodLaw]
  simp only [vLaw]
  rw [SaltFreshPair.sum_prodLaw]
  refine Finset.sum_congr rfl fun H _ => ?_
  congr 1
  rw [SaltFreshPair.sum_prodLaw, SaltFreshPair.sum_prodLaw]
  simp only [hZ H _]
  rw [SaltFreshPair.sum_toReal_mul_const]

/-- **The pure game against `C₁`, averaged over the oracle law, is the fresh game.** -/
theorem sum_fresh [Fintype S] [DecidableEq S] :
    ∑ H, (μH H).toReal * ∑ c, (C₁.coins c).toReal * D.acceptProbAt C₁.toPureEnv noPost (H, c) =
      D.acceptProb (freshEnv (P.ansFin C₀.Q) μH P.ζ ν) noPost := by
  set E := freshEnv (P.ansFin C₀.Q) μH P.ζ ν
  obtain ⟨ρ₀, -⟩ := ν.support_nonempty
  have hρ : ∀ H Z c' ρ, D.acceptProbAt E noPost ((H, Z, c'), ρ) =
      D.acceptProbAt E noPost ((H, Z, c'), ρ₀) := fun H Z c' ρ =>
    D.acceptProbAt_congr _ _ (fun _ _ => rfl) (fun _ => rfl) noPost
  have hc : ∀ H, ∑ c, (C₁.coins c).toReal * D.acceptProbAt C₁.toPureEnv noPost (H, c) =
      ∑ x, (prodLaw (PMF.uniformOfFintype (Fin K → U → Y₁)) P.ζ x).toReal *
        D.acceptProbAt E noPost ((H, x.1, x.2), ρ₀) := fun H => by
    simp only [P.acceptProbAt_fresh D noPost μH H _ ρ₀]
    rw [← P.map_dec₁, PMF.sum_toReal_map_mul]
  simp only [hc]
  change _ = ∑ ω, (saltLaw μH P.ζ ν ω).toReal * D.acceptProbAt E noPost ω
  rw [saltLaw, SaltFreshPair.sum_prodLaw]
  simp only [vLaw]
  rw [SaltFreshPair.sum_prodLaw]
  refine Finset.sum_congr rfl fun H _ => ?_
  congr 1
  refine Finset.sum_congr rfl fun x _ => ?_
  obtain ⟨Z, c'⟩ := x
  congr 1
  simp only [hρ H Z c']
  rw [SaltFreshPair.sum_toReal_mul_const]

end SaltFreshPairOn

namespace SaltFreshPair

variable {emb : S × U → X} {ν : PMF (Fin K → S)} {C₀ C₁ : Challenger X Y Req Resp}
  (P : SaltFreshPair emb ν C₀ C₁)

/-- **A salted pair is a pair reading first components at the split with a trivial second
component.** -/
def toOn : SaltFreshPairOn emb (wholeSplit Y) ν C₀ C₁ where
  Coins' := P.Coins'
  ζ := P.ζ
  ans := P.ans
  readsOffRange := P.readsOffRange.readsOffRangeOn
  dec₀ := P.dec₀
  map_dec₀ := P.map_dec₀
  salted := P.salted
  dec₁ := P.dec₁
  map_dec₁ := P.map_dec₁
  fresh := P.fresh
  Q_eq := P.Q_eq

/-- The answer function indexed by the request numbers below `Q`. -/
def ansFin (Q : ℕ) : P.Coins' → Fin Q → Req → (Fin K → U → Y) → (X → Y) → Option Resp :=
  fun c j => P.ans c j

omit [Fintype X] [DecidableEq X] in
/-- The indexed answer function reads the oracle only outside the range of the embedding. -/
theorem readsOffRange_ansFin (Q : ℕ) : ReadsOffRange emb (P.ansFin Q) :=
  fun c j => P.readsOffRange c j

variable [Fintype Req] [Fintype Resp] [DecidableEq Req] [DecidableEq Resp] [AddGroup Y]
  {W : Type} [Fintype W] {n m : ℕ} (D : Distinguisher W X Y Req Resp n m)
  (post : (X → Y) → QState (DReg W n X Y Req Resp) ≃ₗᵢ[ℂ] QState (DReg W n X Y Req Resp))
  (μH : PMF (X → Y))

/-- **`C₀` in the pure game is the salted challenger** at its other coins and salts, for any
fresh functions on the tape (`SaltFreshPairOn.acceptProbAt_salt` through `toOn`). -/
theorem acceptProbAt_salt (H : X → Y) (c : C₀.Coins) (Z : Fin K → U → Y) :
    D.acceptProbAt C₀.toPureEnv post (H, c) =
      D.acceptProbAt (saltEnv emb (P.ansFin C₀.Q) μH P.ζ ν) post
        ((H, Z, (P.dec₀ c).1), (P.dec₀ c).2) :=
  P.toOn.acceptProbAt_salt D post μH H c Z

/-- **`C₁` in the pure game is the fresh challenger** at its fresh functions and other coins,
for any salts on the tape (`SaltFreshPairOn.acceptProbAt_fresh` through `toOn`). -/
theorem acceptProbAt_fresh (H : X → Y) (c : C₁.Coins) (ρ : Fin K → S) :
    D.acceptProbAt C₁.toPureEnv post (H, c) =
      D.acceptProbAt (freshEnv (P.ansFin C₀.Q) μH P.ζ ν) post
        ((H, (P.dec₁ c).1, (P.dec₁ c).2), ρ) :=
  P.toOn.acceptProbAt_fresh D post μH H c ρ

/-- **The pure game against `C₀`, averaged over the oracle law, is the salted game.** -/
theorem sum_salt [Fintype S] [DecidableEq S] :
    ∑ H, (μH H).toReal * ∑ c, (C₀.coins c).toReal * D.acceptProbAt C₀.toPureEnv noPost (H, c) =
      D.acceptProb (saltEnv emb (P.ansFin C₀.Q) μH P.ζ ν) noPost :=
  P.toOn.sum_salt D μH

/-- **The pure game against `C₁`, averaged over the oracle law, is the fresh game.** -/
theorem sum_fresh [Fintype S] [DecidableEq S] :
    ∑ H, (μH H).toReal * ∑ c, (C₁.coins c).toReal * D.acceptProbAt C₁.toPureEnv noPost (H, c) =
      D.acceptProb (freshEnv (P.ansFin C₀.Q) μH P.ζ ν) noPost :=
  P.toOn.sum_fresh D μH

end SaltFreshPair

end Challenger

/-! ### Deferred measurement at a fixed oracle -/

namespace AdaptiveIAlg

variable {X Y Req Resp O : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
  [Fintype Req] [DecidableEq Req] [Fintype Resp] [DecidableEq Resp] [Nonempty X] [AddGroup Y]
  [Nonempty Y] [DecidableEq O] {shA : AlgShape X Y Req Resp} (A : AdaptiveIAlg shA O)

/-- **The dilated adversary as a distinguisher without a final unitary**: the dilation for the
output `o` (`KindAlg.dilate`) with its post phase of query batches moved into `post` further query
slots (`Distinguisher.withPostSlots`). -/
noncomputable def pureDil (o : O) :=
  (A.toKindAlg.dilate o).withPostSlots
    (fun j => A.toKindAlg.uStepD (A.toKindAlg.slots + 1 + j)) A.toKindAlg.post

/-- **The dilated adversary has a budget of `budget + post` query slots.** -/
noncomputable def pureDilBudget (o : O) : (A.pureDil o).Budget (A.budget + A.post) :=
  Distinguisher.Budget.withPostSlots _ _ _ (A.dilBudget o)

/-- **Deferred measurement at a fixed oracle**: the composition with a challenger outputs `o` at
the oracle `H` with the coin average of the dilated adversary's acceptance probabilities at the
tapes `(H, c)`. -/
theorem toReal_outLaw_compose_eq (C : Challenger X Y Req Resp) (H : X → Y) (o : O) :
    ((A.compose C).outLaw H (some o)).toReal =
      ∑ c, (C.coins c).toReal * (A.pureDil o).acceptProbAt C.toPureEnv noPost (H, c) := by
  have hpost : A.toKindAlg.postOp = fun H => Distinguisher.postN
      (fun j => A.toKindAlg.uStepD (A.toKindAlg.slots + 1 + j)) H A.toKindAlg.post :=
    funext fun H => A.toKindAlg.postOpN_eq_postN H _
  have hacc : ∀ c : C.Coins, A.toKindAlg.mgAccept C.toPureEnv o (H, c) true =
      (A.pureDil o).acceptProbAt C.toPureEnv noPost (H, c) := fun c => by
    rw [KindAlg.mgAccept_deph, ← KindAlg.acceptProbAt_dilate, pureDil,
      Distinguisher.acceptProbAt_withPostSlots, hpost]
  rw [compose, KindAlg.outLaw_composeBoth_some]
  simp only [hacc]
  exact ENNReal.toReal_ofReal (Finset.sum_nonneg fun c _ =>
    mul_nonneg ENNReal.toReal_nonneg (prob_nonneg _ _))

/-- **`2 q √(n ε)` in terms of the query bound**: for `n q ≤ t`, at most `2 t √ε`. -/
theorem two_mul_sqrt_le_of_mul_le {n q t : ℕ} (h : n * q ≤ t) (ε : ℝ) :
    2 * (q : ℝ) * √(n * ε) ≤ 2 * t * √ε := by
  rcases le_or_gt ε 0 with hε | hε
  · rw [Real.sqrt_eq_zero'.2 hε, Real.sqrt_eq_zero'.2
      (mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg n) hε)]
    simp
  · rw [Real.sqrt_mul (Nat.cast_nonneg n)]
    have hn : √(n : ℝ) ≤ n := by
      have h1 : (n : ℝ) ≤ (n : ℝ) ^ 2 := by exact_mod_cast Nat.le_self_pow two_ne_zero n
      exact (Real.sqrt_le_sqrt h1).trans_eq (Real.sqrt_sq (Nat.cast_nonneg n))
    have ht : (n : ℝ) * q ≤ t := by exact_mod_cast h
    have hs := Real.sqrt_nonneg ε
    calc 2 * (q : ℝ) * (√(n : ℝ) * √ε) = 2 * ((q : ℝ) * √(n : ℝ)) * √ε := by ring
      _ ≤ 2 * ((q : ℝ) * n) * √ε := by gcongr
      _ ≤ 2 * t * √ε := by rw [mul_comm (q : ℝ)]; gcongr

variable {S U : Type} [Fintype S] [DecidableEq S] [Fintype U] [DecidableEq U] {K : ℕ}
  {emb : S × U → X} {ν : PMF (Fin K → S)} {C₀ C₁ : Challenger X Y Req Resp}
  {Y₁ Y₂ : Type} [Fintype Y₁] [Nonempty Y₁] {e : Y ≃ Y₁ × Y₂}

/-- **Reprogramming the first components at hidden fresh salts against an interactive
adversary** (`Distinguisher.advantage_saltOn_fresh_le` through the dilation): for a challenger
`C₀` reading the first components, under a split `e : Y ≃ Y₁ × Y₂`, of the oracle at `K` hidden
fresh salts `ρ ← ν` and its fresh counterpart `C₁` (`Challenger.SaltFreshPairOn`), an injective
embedding `emb`, and an oracle law `μH` uniform in the first components on the range of `emb`
given the rest (`IsUniformOnRangeOn`), the probabilities, averaged over `μH`, that the adversary
outputs `o` against `C₀` and against `C₁` differ by at most
`Pr[two salts collide] + 2 (budget + post) √(width ε)`, for `ε` bounding the probability that a
given point of `S` is a salt. -/
theorem advantage_saltOn_fresh_le (P : C₀.SaltFreshPairOn emb e ν C₁)
    (hemb : Function.Injective emb) {μH : PMF (X → Y)} (hμH : IsUniformOnRangeOn emb e μH)
    {ε : ℝ} (hε : ∀ s, (ν.toOuterMeasure {ρ | ∃ i, ρ i = s}).toReal ≤ ε) (o : O) :
    GordieHowe.advantage (∑ H, (μH H).toReal * ((A.compose C₀).outLaw H (some o)).toReal)
      (∑ H, (μH H).toReal * ((A.compose C₁).outLaw H (some o)).toReal) ≤
        (ν.toOuterMeasure {ρ | ¬ Function.Injective ρ}).toReal +
          2 * (A.budget + A.post : ℕ) * √(A.width * ε) := by
  simp only [toReal_outLaw_compose_eq]
  rw [P.sum_salt (A.pureDil o) μH, P.sum_fresh (A.pureDil o) μH]
  exact (A.pureDil o).advantage_saltOn_fresh_le e (P.ansFin C₀.Q) μH P.ζ ν hemb hμH
    (P.readsOffRange_ansFin C₀.Q) (A.pureDilBudget o) hε

/-- **`advantage_saltOn_fresh_le` in terms of the query bound**: for an adversary with
`width (budget + post) ≤ t`, at most `Pr[two salts collide] + 2 t √ε`. -/
theorem advantage_saltOn_fresh_le_of_queries_le (P : C₀.SaltFreshPairOn emb e ν C₁)
    (hemb : Function.Injective emb) {μH : PMF (X → Y)} (hμH : IsUniformOnRangeOn emb e μH)
    {ε : ℝ} (hε : ∀ s, (ν.toOuterMeasure {ρ | ∃ i, ρ i = s}).toReal ≤ ε) (o : O) {t : ℕ}
    (ht : A.width * (A.budget + A.post) ≤ t) :
    GordieHowe.advantage (∑ H, (μH H).toReal * ((A.compose C₀).outLaw H (some o)).toReal)
      (∑ H, (μH H).toReal * ((A.compose C₁).outLaw H (some o)).toReal) ≤
        (ν.toOuterMeasure {ρ | ¬ Function.Injective ρ}).toReal + 2 * t * √ε :=
  (A.advantage_saltOn_fresh_le P hemb hμH hε o).trans
    (add_le_add le_rfl (two_mul_sqrt_le_of_mul_le ht ε))

/-- **Reprogramming at hidden fresh salts against an interactive adversary**
(`Distinguisher.advantage_salt_fresh_le` through the dilation): for a challenger `C₀` reading
the oracle at `K` hidden fresh salts `ρ ← ν` and its fresh counterpart `C₁`
(`Challenger.SaltFreshPair`), an
injective embedding `emb`, and an oracle law `μH` uniform on the range of `emb` given the rest,
the probabilities, averaged over `μH`, that the adversary outputs `o` against `C₀` and against
`C₁` differ by at most `Pr[two salts collide] + 2 (budget + post) √(width ε)`, for `ε` bounding
the probability that a given point of `S` is a salt. -/
theorem advantage_salt_fresh_le (P : C₀.SaltFreshPair emb ν C₁) (hemb : Function.Injective emb)
    {μH : PMF (X → Y)} (hμH : IsUniformOnRange emb μH) {ε : ℝ}
    (hε : ∀ s, (ν.toOuterMeasure {ρ | ∃ i, ρ i = s}).toReal ≤ ε) (o : O) :
    GordieHowe.advantage (∑ H, (μH H).toReal * ((A.compose C₀).outLaw H (some o)).toReal)
      (∑ H, (μH H).toReal * ((A.compose C₁).outLaw H (some o)).toReal) ≤
        (ν.toOuterMeasure {ρ | ¬ Function.Injective ρ}).toReal +
          2 * (A.budget + A.post : ℕ) * √(A.width * ε) :=
  A.advantage_saltOn_fresh_le P.toOn hemb hμH.isUniformOnRangeOn hε o

/-- **`advantage_salt_fresh_le` in terms of the query bound**: for an adversary with
`width (budget + post) ≤ t`, at most `Pr[two salts collide] + 2 t √ε`. -/
theorem advantage_salt_fresh_le_of_queries_le (P : C₀.SaltFreshPair emb ν C₁)
    (hemb : Function.Injective emb) {μH : PMF (X → Y)} (hμH : IsUniformOnRange emb μH) {ε : ℝ}
    (hε : ∀ s, (ν.toOuterMeasure {ρ | ∃ i, ρ i = s}).toReal ≤ ε) (o : O) {t : ℕ}
    (ht : A.width * (A.budget + A.post) ≤ t) :
    GordieHowe.advantage (∑ H, (μH H).toReal * ((A.compose C₀).outLaw H (some o)).toReal)
      (∑ H, (μH H).toReal * ((A.compose C₁).outLaw H (some o)).toReal) ≤
        (ν.toOuterMeasure {ρ | ¬ Function.Injective ρ}).toReal + 2 * t * √ε :=
  A.advantage_saltOn_fresh_le_of_queries_le P.toOn hemb hμH.isUniformOnRangeOn hε o ht

end AdaptiveIAlg

end GordieHowe.Quantum
