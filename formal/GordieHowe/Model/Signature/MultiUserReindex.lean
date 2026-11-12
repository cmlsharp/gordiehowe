-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Model.Signature.MultiUserSim
public import GordieHowe.Model.Quantum.Interactive.CompressedSimReindex
public import GordieHowe.Model.Quantum.Interactive.ReqBridge

@[expose] public section

/-!
# Reindexing the coins of the multi-user challenger

The multi-user challenger (`Signature.muChallenger`) signs request number `j` with its coins `c j`.
A query algorithm with request points (`Quantum.ReqQueryAlg`) sends one request at every step,
a dummy `d₂` at the steps where the run it simulates makes no request, so the challenger signs the
request of step `k` with `c k`, while the run it simulates signs its `j`-th request with coin `j`:
the number of earlier requests other than the dummy (`ReqQueryAlg.countND`). The two give the same
coin average of `simLaw` (`sum_simLaw_countND_muReply`), by `ReqQueryAlg.sum_simLaw_instLog_eq`:
on every request pattern the coins read at the non-dummy steps are distinct in both, so a
permutation of the coins (`Equiv.extendSubtype`) carries one family of replies to the other, and
the uniform coins are invariant under it.

- `exists_perm_comp_eq`: two injective maps of a finite type into a finite type differ by a
  permutation of the target.
- `PMF.map_uniformOfFintype_comp_perm`: uniform coins are invariant under a permutation of the
  coordinates.
- `countND_requestsBefore_lt`: along a full request pattern, the number of earlier non-dummy
  requests is at most the step and strictly increases past a non-dummy request.
- `sum_simLaw_countND_muReply` (**the reindexing**).
-/

namespace GordieHowe

open Quantum QROM RingSignature

/-- **Two injective maps differ by a permutation of the target**: for injective `f₁ f₂ : T → α`
of finite types, some permutation `σ` of `α` has `σ (f₁ k) = f₂ k`. -/
theorem exists_perm_comp_eq {T α : Type} [Fintype T] [Fintype α] [DecidableEq α] {f₁ f₂ : T → α}
    (h₁ : Function.Injective f₁) (h₂ : Function.Injective f₂) :
    ∃ σ : Equiv.Perm α, ∀ k, σ (f₁ k) = f₂ k := by
  classical
  let e : {x // x ∈ Set.range f₁} ≃ {x // x ∈ Set.range f₂} :=
    (Equiv.ofInjective f₁ h₁).symm.trans (Equiv.ofInjective f₂ h₂)
  refine ⟨e.extendSubtype, fun k => ?_⟩
  rw [Equiv.extendSubtype_apply_of_mem e (f₁ k) ⟨k, rfl⟩]
  change ((Equiv.ofInjective f₂ h₂) ((Equiv.ofInjective f₁ h₁).symm ⟨f₁ k, ⟨k, rfl⟩⟩) : α) = f₂ k
  rw [Equiv.ofInjective_symm_apply]
  rfl

/-- **Uniform coins are invariant under a permutation of the coordinates.** -/
theorem PMF.map_uniformOfFintype_comp_perm {α C : Type} [Fintype α] [DecidableEq α] [Fintype C]
    [DecidableEq C] [Nonempty C] (σ : Equiv.Perm α) :
    (PMF.uniformOfFintype (α → C)).map (fun ω => ω ∘ σ) = PMF.uniformOfFintype (α → C) := by
  ext u
  rw [PMF.map_apply, tsum_eq_single (u ∘ σ.symm) fun ω hω => by
    rw [if_neg]
    rintro rfl
    exact hω (by funext x; simp)]
  rw [if_pos (by funext x; simp), PMF.uniformOfFintype_apply, PMF.uniformOfFintype_apply]

/-- The number of earlier non-dummy requests after one more full log. -/
theorem countND_requestsBefore_succ {Req : Type} [DecidableEq Req] {m : ℕ} (d : Req)
    (L : Fin m → Req) {k : ℕ} (hk : k < m) :
    ReqQueryAlg.countND d (requestsBefore (fun j => some (L j)) (k + 1)) =
      ReqQueryAlg.countND d (requestsBefore (fun j => some (L j)) k) +
        if L ⟨k, hk⟩ ≠ d then 1 else 0 := by
  rw [requestsBefore_succ_of_lt _ hk]
  simp only [ReqQueryAlg.countND, Option.toList_some, List.filter_append, List.length_append]
  split_ifs with h <;> simp [h]

/-- **The number of earlier non-dummy requests is at most the step.** -/
theorem countND_requestsBefore_le {Req : Type} [DecidableEq Req] {m : ℕ} (d : Req)
    (L : Fin m → Req) (k : ℕ) :
    ReqQueryAlg.countND d (requestsBefore (fun j => some (L j)) k) ≤ k :=
  (List.length_filter_le _ _).trans (length_requestsBefore_le _ k)

/-- The number of earlier non-dummy requests does not decrease. -/
theorem countND_requestsBefore_mono {Req : Type} [DecidableEq Req] {m : ℕ} (d : Req)
    (L : Fin m → Req) (k : ℕ) : ∀ j, k + j ≤ m →
    ReqQueryAlg.countND d (requestsBefore (fun j => some (L j)) k) ≤
      ReqQueryAlg.countND d (requestsBefore (fun j => some (L j)) (k + j))
  | 0, _ => le_rfl
  | j + 1, h => by
    rw [← Nat.add_assoc, countND_requestsBefore_succ d L (by omega)]
    exact (countND_requestsBefore_mono d L k j (by omega)).trans (Nat.le_add_right _ _)

/-- **Past a non-dummy request, the number of earlier non-dummy requests increases.** -/
theorem countND_requestsBefore_lt {Req : Type} [DecidableEq Req] {m : ℕ} (d : Req)
    (L : Fin m → Req) {k k' : Fin m} (hkk : k < k') (hL : L k ≠ d) :
    ReqQueryAlg.countND d (requestsBefore (fun j => some (L j)) k) <
      ReqQueryAlg.countND d (requestsBefore (fun j => some (L j)) k') := by
  have h1 := countND_requestsBefore_succ d L k.2
  rw [if_pos hL] at h1
  have h2 := countND_requestsBefore_mono d L ((k : ℕ) + 1) ((k' : ℕ) - ((k : ℕ) + 1))
    (by have := k'.2; omega)
  rw [show (k : ℕ) + 1 + ((k' : ℕ) - ((k : ℕ) + 1)) = k' by have : (k : ℕ) < k' := hkk; omega] at h2
  omega

namespace Signature

variable {N n : ℕ} {m : ℕ} {I J Bd : Type} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
  {T : Signature.SchemeTypes} {RMsg : Type}
  {B : BaseSigner (Bits m) (BitStr I J) N T RMsg} (O : SignOracle B.core) (e : BitStr I J ≃ Bd)
  {t : ℕ}
  {Ot : Type}

variable [Fintype O.SMsg] [DecidableEq O.SMsg] [Fintype O.Coins] [DecidableEq O.Coins]

variable [Fintype T.PK] [DecidableEq T.PK] [Fintype T.BSig] [DecidableEq T.BSig]
  [Fintype T.KeyCoins] [DecidableEq T.KeyCoins] [Nonempty O.Coins]

open Classical in
/-- **The reindexing of the multi-user challenger's coins** (module docstring): for a dummy request
`d₂` that is not a signing request (`hd₂`) and at least `t + 1` answered requests (`hQ`), the coin
average of `simLaw` of the instance whose request point `k` is answered with the coins at the number
of earlier non-dummy requests is that of the instance answered as the challenger answers, with the
coins at the step. -/
theorem sum_simLaw_countND_muReply [Inhabited (MURequest O n)] (keys : Fin n → B.KeyCoins)
    {Q' : ℕ} (hQ : t + 1 ≤ Q') (d₂ : MURequest O n) (hd₂ : ∀ i sm, d₂ ≠ .sign i sm)
    (G : ReqQueryAlg (Bits m) (BitStr I J) (MURequest O n) (MUResponse B.core) t Ot)
    (S : Set (Ot × DB (Bits m) Bd)) :
    ∑ ω, PMF.uniformOfFintype (Fin Q' → O.Coins) ω *
        simLaw e (G.instLog fun _ prev r =>
          muReplyAfter O keys Q' ω (ReqQueryAlg.countND d₂ prev) r) S =
      ∑ c, PMF.uniformOfFintype (Fin Q' → O.Coins) c *
        simLaw e (G.inst (muReplyAfter O keys Q' c)) S := by
  rw [show (fun c => PMF.uniformOfFintype (Fin Q' → O.Coins) c *
      simLaw e (G.inst (muReplyAfter O keys Q' c)) S) =
      fun c => PMF.uniformOfFintype (Fin Q' → O.Coins) c *
      simLaw e (G.instLog fun k _ r => muReplyAfter O keys Q' c k r) S from rfl]
  refine ReqQueryAlg.sum_simLaw_instLog_eq e G _ _ _ _ (fun L _ => ?_) S
  -- the steps with a non-dummy request, sent to the step and to the request count
  have hcntQ : ∀ k : Fin (t + 1),
      ReqQueryAlg.countND d₂ (requestsBefore (fun j => some (L j)) k) < Q' := fun k =>
    lt_of_le_of_lt (countND_requestsBefore_le d₂ L k) (lt_of_lt_of_le k.2 hQ)
  let T := {k : Fin (t + 1) // L k ≠ d₂}
  let f₁ : T → Fin Q' := fun k => ⟨k.1, lt_of_lt_of_le k.1.2 hQ⟩
  let f₂ : T → Fin Q' := fun k =>
    ⟨ReqQueryAlg.countND d₂ (requestsBefore (fun j => some (L j)) k.1), hcntQ k.1⟩
  have h₁ : Function.Injective f₁ := fun k k' h => Subtype.ext (Fin.ext (by
    simpa [f₁] using congrArg Fin.val h))
  have h₂ : Function.Injective f₂ := by
    intro k k' h
    have hv : ReqQueryAlg.countND d₂ (requestsBefore (fun j => some (L j)) k.1) =
        ReqQueryAlg.countND d₂ (requestsBefore (fun j => some (L j)) k'.1) := by
      simpa [f₂] using congrArg Fin.val h
    rcases lt_trichotomy k.1 k'.1 with hl | hl | hl
    · exact absurd hv (countND_requestsBefore_lt d₂ L hl k.2).ne
    · exact Subtype.ext hl
    · exact absurd hv.symm (countND_requestsBefore_lt d₂ L hl k'.2).ne
  obtain ⟨σ, hσ⟩ := exists_perm_comp_eq h₁ h₂
  -- the count-indexed replies are the step-indexed ones at the permuted coins
  have hpt : ∀ ω : Fin Q' → O.Coins,
      ReqQueryAlg.repliesAt
        (fun _ prev r => muReplyAfter O keys Q' ω (ReqQueryAlg.countND d₂ prev) r) L =
        ReqQueryAlg.repliesAt (fun k _ r => muReplyAfter O keys Q' (ω ∘ σ) k r) L := by
    intro ω
    funext k
    simp only [ReqQueryAlg.repliesAt, muReplyAfter, dif_pos (hcntQ k),
      dif_pos (lt_of_lt_of_le k.2 hQ)]
    rcases hL : L k with i | ⟨i, sm⟩ | i
    · rfl
    · have hk : L k ≠ d₂ := fun h => hd₂ i sm (h.symm.trans hL)
      have := hσ ⟨k, hk⟩
      simp only [f₁, f₂] at this
      simp only [Function.comp_apply, this]
    · rfl
  rw [show (fun c => ReqQueryAlg.repliesAt
      (fun _ prev r => muReplyAfter O keys Q' c (ReqQueryAlg.countND d₂ prev) r) L) =
      (fun c => ReqQueryAlg.repliesAt (fun k _ r => muReplyAfter O keys Q' c k r) L) ∘
        fun ω => ω ∘ σ
      from funext hpt, ← PMF.map_comp, PMF.map_uniformOfFintype_comp_perm]

end Signature

end GordieHowe
