-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Model.Signature.MultiUserBridge
public import GordieHowe.Model.Signature.MultiUserSim

@[expose] public section

/-!
# Extraction runs at tables of the multi-user challenger's replies, as a multi-user forger

For a family of extraction runs (`Quantum.extRun`) whose outer requests are requests of the
multi-user game, each holding a table that agrees with the multi-user challenger's replies at the
users' key coins (on the dummy and the outer requests, below the number of slots), by the bridge
statement (`Quantum.extBridge`): the average, over the users' key coins and
an auxiliary value drawn from the public keys, of the probability of an event `W` of each run is
at most the success probability in MU-EUF-CMA^corr of the forger holding the compressed-oracle
simulation of the bridge algorithms (`Signature.coSimMU`), when on every basis state of nonzero
amplitude of the bridge's simulation the event makes its readout a forgery for the logged
multi-user requests (`hwin`).

- `bornWeight_mono_of_support`: the Born weight is monotone on the support.
- `Signature.tableForger`: the multi-user forger of the bridge algorithms.
- `Signature.sum_simLaw_extRun_le_muEufProb_tableForger`: the bound.
-/

namespace GordieHowe

open Quantum QROM RingSignature
open scoped ENNReal

/-- **The Born weight is monotone on the support**: `S ⊆ S'` on the basis states of nonzero
amplitude suffices. -/
theorem bornWeight_mono_of_support {ι : Type*} [Fintype ι] (v : QState ι) {S S' : Set ι}
    (h : ∀ i, v i ≠ 0 → i ∈ S → i ∈ S') : bornWeight v S ≤ bornWeight v S' := by
  rw [bornWeight_apply_eq_sum, bornWeight_apply_eq_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  by_cases hi : i ∈ S
  · by_cases hv : v i = 0
    · simp [Set.indicator, hv]
    · rw [Set.indicator_of_mem hi, Set.indicator_of_mem (h i hv hi)]
  · rw [Set.indicator_of_notMem hi]
    exact bot_le

namespace Signature

variable {N n : ℕ} {m : ℕ} {I J Bd : Type} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
  {T : Signature.SchemeTypes} {RMsg : Type} [Fintype T.PK] [DecidableEq T.PK]
  [Fintype T.BSig] [DecidableEq T.BSig]
  [Fintype T.KeyCoins] [DecidableEq T.KeyCoins]
  {B : BaseSigner (Bits m) (BitStr I J) N T RMsg} (O : SignOracle B.core) [NeZero n]
  (e : BitStr I J ≃ Bd)
  {Req Resp Req₁ Resp₁ Ot : Type} [Fintype Req] [DecidableEq Req] [Fintype Resp]
  [DecidableEq Resp] [Fintype Req₁] [DecidableEq Req₁] [Fintype Resp₁] [DecidableEq Resp₁]
  [Inhabited Req₁]
  (Aux : (Fin n → B.PK) → Type) (aux : ∀ pks, PMF (Aux pks))
  {shA : ∀ pks, Aux pks → AlgShape (Bits m) (BitStr I J) Req Resp} (A : ∀ pks (aux : Aux pks), AdaptiveIAlg (shA pks aux) Ot)
  (C₁ : ∀ pks, Aux pks → Challenger (Bits m) (BitStr I J) Req₁ Resp₁)
  (F : ∀ pks, Aux pks → TwoRelay Req Resp Req₁ Resp₁ (MURequest O n) (MUResponse B.core))
  (d₂ : MURequest O n)
  (E : ∀ pks p, Expansion (Bits m) Bd
    (ExtReg (A pks p) (C₁ pks p) (MURequest O n) (MUResponse B.core)))
  (kq : ℕ) (d₀ : ∀ pks p, ExtReg (A pks p) (C₁ pks p) (MURequest O n) (MUResponse B.core))
  (g : ∀ pks p, BaseGame.Tuple (Bits m) Bd
    (ExtReg (A pks p) (C₁ pks p) (MURequest O n) (MUResponse B.core)) kq × DB (Bits m) Bd →
      B.PK × B.BMsg × B.BSig)

variable [Fintype O.SMsg] [DecidableEq O.SMsg]

/-- **The multi-user forger of a family of bridge algorithms** (`coSimMU`): on the public keys
`pks` it draws `p` from `aux pks`, runs the compressed-oracle simulation of the bridge algorithm
of the extraction run at `(pks, p)` with its request points sent to the multi-user challenger, and
outputs `g pks p` of the output and the measured database. -/
noncomputable def tableForger : MUAdversary O n (OracleView.queriesOnly (Bits m) (BitStr I J)) 0 :=
  coSimMU O e Aux aux
    (fun pks p => ((((A pks p).absorbTab (F pks p) (tab₀ (A pks p))).toTPKindAlg.composeBothOut
      (C₁ pks p) id).depth) + kq)
    (fun pks p => BaseGame.Tuple (Bits m) Bd
      (ExtReg (A pks p) (C₁ pks p) (MURequest O n) (MUResponse B.core)) kq)
    (fun pks p => bridgeAlg e (A pks p) (C₁ pks p) (F pks p) d₂ (E pks p) kq (d₀ pks p)) g

variable [Fintype O.Coins] [DecidableEq O.Coins] [Nonempty O.Coins]

variable [Nonempty T.KeyCoins]

/-- **Extraction runs at tables of the multi-user challenger's replies are bounded by the multi-user
forger of their bridge algorithms** (module docstring): for a signing oracle without queries (`hO`),
for trace-preserving adversaries (`hTP`), outer requests never
the dummy (`hout`), a dummy that is not a signing request (`hd₂`), `Q'` at least the number of
request points (`hQ`), tables `tab keys p` agreeing with the multi-user challenger's replies at
every coins (`htab`), and events `W keys p` that make the readout `g` a forgery for the logged
multi-user requests on every basis state of nonzero amplitude of the bridge's simulation (`hwin`),
the average of the events' probabilities is at most `muEufProb` of `tableForger`. -/
theorem sum_simLaw_extRun_le_muEufProb_tableForger (hO : O.NoQuery)
    (hTP : ∀ pks p, (A pks p).TracePreserving)
    (hout : ∀ pks p c r q, (F pks p).outer c r = some q → q ≠ d₂) (hd₂ : ∀ i sm, d₂ ≠ .sign i sm)
    {Q' : ℕ}
    (hQ : ∀ pks p, ((((A pks p).absorbTab (F pks p) (tab₀ (A pks p))).toTPKindAlg.composeBothOut
      (C₁ pks p) id).depth) + kq + 1 ≤ Q')
    (tab : ∀ (keys : Fin n → B.KeyCoins) (p : Aux fun i => B.pk (keys i)),
      (A (fun i => B.pk (keys i)) p).OuterTab (MURequest O n) (MUResponse B.core))
    (htab : ∀ keys p ω j q, (q = d₂ ∨ ∃ c r, (F (fun i => B.pk (keys i)) p).outer c r = some q) →
      tab keys p j q = muReplyAfter O keys Q' ω j q)
    (W : ∀ (keys : Fin n → B.KeyCoins) (p : Aux fun i => B.pk (keys i)),
      Set (BaseGame.Tuple (Bits m) Bd (ExtReg (A (fun i => B.pk (keys i)) p)
        (C₁ (fun i => B.pk (keys i)) p) (MURequest O n) (MUResponse B.core)) kq × DB (Bits m) Bd))
    (hwin : ∀ keys p H c b, simState e ((bridgeAlg e (A (fun i => B.pk (keys i)) p)
        (C₁ (fun i => B.pk (keys i)) p) (F (fun i => B.pk (keys i)) p) d₂
        (E (fun i => B.pk (keys i)) p) kq (d₀ (fun i => B.pk (keys i)) p)).inst
          (muReplyAfter O keys Q' c)) b ≠ 0 →
      ((bridgeAlg e (A (fun i => B.pk (keys i)) p) (C₁ (fun i => B.pk (keys i)) p)
        (F (fun i => B.pk (keys i)) p) d₂ (E (fun i => B.pk (keys i)) p) kq
        (d₀ (fun i => B.pk (keys i)) p)).out b.1.1.1, slotsDB e b.2) ∈ W keys p →
      ForgesReq keys H (g (fun i => B.pk (keys i)) p
        ((bridgeAlg e (A (fun i => B.pk (keys i)) p) (C₁ (fun i => B.pk (keys i)) p)
          (F (fun i => B.pk (keys i)) p) d₂ (E (fun i => B.pk (keys i)) p) kq
          (d₀ (fun i => B.pk (keys i)) p)).out b.1.1.1, slotsDB e b.2)) (requests b.1.1.2)) :
    ∑' keys, PMF.uniformOfFintype (Fin n → B.KeyCoins) keys *
      ∑' p, aux (fun i => B.pk (keys i)) p *
        simLaw e (extRun e (A (fun i => B.pk (keys i)) p) (C₁ (fun i => B.pk (keys i)) p)
          (F (fun i => B.pk (keys i)) p) (E (fun i => B.pk (keys i)) p) kq
          (d₀ (fun i => B.pk (keys i)) p) (tab keys p)) (W keys p) ≤
      muEufProb (tableForger O e Aux aux A C₁ F d₂ E kq d₀ g) Q' := by
  rw [tableForger, muEufProb_coSimMU _ _ hO _ _ _ _ _ _ _ hQ]
  refine ENNReal.tsum_le_tsum fun keys => mul_le_mul' le_rfl ?_
  rw [← one_mul (∑' p, _), ← PMF.tsum_coe (PMF.uniformOfFintype (Bits m → BitStr I J)),
    ← ENNReal.tsum_mul_right]
  refine ENNReal.tsum_le_tsum fun H => mul_le_mul' le_rfl ?_
  refine ENNReal.tsum_le_tsum fun p => mul_le_mul' le_rfl ?_
  rw [simLaw_extRun_tab_eq_sum (O := O) (A (fun i => B.pk (keys i)) p)
    (C₁ (fun i => B.pk (keys i)) p) (F (fun i => B.pk (keys i)) p) e d₂
    (E (fun i => B.pk (keys i)) p) kq (d₀ (fun i => B.pk (keys i)) p)
    (hTP _ p) (hout _ p) hd₂ keys (hQ _ p) (tab keys p) (htab keys p) (W keys p)]
  refine Finset.sum_le_sum fun c _ => mul_le_mul' le_rfl ?_
  rw [simLaw, MeasureTheory.OuterMeasure.map_apply]
  exact bornWeight_mono_of_support _ fun b hb hS => hwin keys p H c b hb hS

end Signature

end GordieHowe
