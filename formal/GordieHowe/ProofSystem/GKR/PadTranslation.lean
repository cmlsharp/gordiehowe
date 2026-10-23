-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.ProofSystem.GKR.CircuitProtocol

@[expose] public section

/-!
# Committed-pad translation of the GKR transcript

Pads are fixed with the committed witness before GKR challenges. Only prover
messages are translated; all verifier challenges retain their source order
and values. No distribution or honesty condition is imposed on the pads.
-/
namespace GordieHowe.GKR.PadTranslation
open IOP
open GKR.Circuit CircuitProtocol LayerProtocol LayerSumcheck
variable {F : Type} [Field F]

structure LayerPads (F : Type) (d : ℕ) (Tail : Type) where
  polynomial : Fin (schedule d).length → Fin 2 → F
  claim : Fin 3 → F
  tail : Tail

def Pads {d : ℕ} (C : Circuit F d) : Type :=
  match C with
  | .input _ => Unit
  | .layer (inDim := i) _ tail => LayerPads F i (Pads tail)

def unmaskMessage (pad : Fin 2 → F) (msg : Message F) : Message F :=
  ⟨msg.p0 + pad 0, msg.p2 + pad 1, msg.challenge⟩

def unmask {d : ℕ} (C : Circuit F d) (pads : Pads C) (tr : Trace C) : Trace C :=
  match C with
  | .input _ => tr
  | .layer _ tail =>
    { alpha := tr.alpha, beta := tr.beta
      rounds := fun r => unmaskMessage (pads.polynomial r) (tr.rounds r)
      wc := fun h => tr.wc h + pads.claim ⟨h.val, by omega⟩
      tail := unmask tail pads.tail tr.tail }

/-- The third claim pad is checked separately by the quadratic pad equation. -/
def ProductsHold {d : ℕ} (C : Circuit F d) (pads : Pads C) : Prop :=
  match C with
  | .input _ => True
  | .layer _ tail => pads.claim 0 * pads.claim 1 = pads.claim 2 ∧
      ProductsHold tail pads.tail

/-- Subtract a pad pair from the two revealed values of a round message; the
challenge is not translated. -/
def maskMessage (pad : Fin 2 → F) (msg : Message F) : Message F :=
  ⟨msg.p0 - pad 0, msg.p2 - pad 1, msg.challenge⟩

@[simp] theorem unmaskMessage_maskMessage (pad : Fin 2 → F) (msg : Message F) :
    unmaskMessage pad (maskMessage pad msg) = msg := by
  simp only [unmaskMessage, maskMessage, sub_add_cancel]

@[simp] theorem maskMessage_unmaskMessage (pad : Fin 2 → F) (msg : Message F) :
    maskMessage pad (unmaskMessage pad msg) = msg := by
  simp only [unmaskMessage, maskMessage, add_sub_cancel_right]

@[simp] theorem maskMessage_challenge (pad : Fin 2 → F) (msg : Message F) :
    (maskMessage pad msg).challenge = msg.challenge := rfl

@[simp] theorem maskMessage_zero (msg : Message F) : maskMessage 0 msg = msg := by
  simp only [maskMessage, Pi.zero_apply, sub_zero]

/-- Subtract the fixed committed pads from the revealed values of a trace: the
two coefficients of every round and the two wire claims of every layer. This is
the trace the prover sends. -/
def mask {d : ℕ} (C : Circuit F d) (pads : Pads C) (tr : Trace C) : Trace C :=
  match C with
  | .input _ => tr
  | .layer _ tail =>
    { alpha := tr.alpha, beta := tr.beta
      rounds := fun r => maskMessage (pads.polynomial r) (tr.rounds r)
      wc := fun h => tr.wc h - pads.claim ⟨h.val, by omega⟩
      tail := mask tail pads.tail tr.tail }

@[simp] theorem unmask_mask {d : ℕ} (C : Circuit F d) (pads : Pads C) (tr : Trace C) :
    unmask C pads (mask C pads tr) = tr := by
  induction C with
  | input d => rfl
  | layer Q tail ih =>
    cases tr
    simp only [unmask, mask, unmaskMessage_maskMessage, sub_add_cancel, ih]
    rfl

@[simp] theorem mask_unmask {d : ℕ} (C : Circuit F d) (pads : Pads C) (tr : Trace C) :
    mask C pads (unmask C pads tr) = tr := by
  induction C with
  | input d => rfl
  | layer Q tail ih =>
    cases tr
    simp only [unmask, mask, maskMessage_unmaskMessage, add_sub_cancel_right, ih]
    rfl

/-- The pads the honest prover draws: both round-coefficient pads of every
sumcheck round and the two revealed wire-claim pads of every layer. The product
pad `claim 2` is not drawn; `FreePads.pads` sets it to `claim 0 * claim 1`. -/
def FreePads {d : ℕ} (C : Circuit F d) : Type :=
  match C with
  | .input _ => Unit
  | .layer (inDim := i) _ tail => (Fin (schedule i).length → Fin 2 → F) × (Fin 2 → F) × FreePads tail

instance FreePads.instAddCommGroup {d : ℕ} : (C : Circuit F d) → AddCommGroup (FreePads C)
  | .input _ => inferInstanceAs (AddCommGroup Unit)
  | .layer (inDim := i) _ tail =>
    letI := FreePads.instAddCommGroup tail
    inferInstanceAs (AddCommGroup ((Fin (schedule i).length → Fin 2 → F) × (Fin 2 → F) × FreePads tail))

instance FreePads.instFintype [Fintype F] {d : ℕ} : (C : Circuit F d) → Fintype (FreePads C)
  | .input _ => inferInstanceAs (Fintype Unit)
  | .layer (inDim := i) _ tail =>
    letI := FreePads.instFintype tail
    inferInstanceAs (Fintype ((Fin (schedule i).length → Fin 2 → F) × (Fin 2 → F) × FreePads tail))

/-- The committed pads: the free pads, and the product pad `claim 2 := claim 0 * claim 1`. -/
def FreePads.pads {d : ℕ} {C : Circuit F d} (π : FreePads C) : Pads C :=
  match C, π with
  | .input _, _ => ()
  | .layer _ tail, π =>
    ⟨π.1, ![π.2.1 0, π.2.1 1, π.2.1 0 * π.2.1 1], FreePads.pads (C := tail) π.2.2⟩

theorem FreePads.productsHold {d : ℕ} {C : Circuit F d} (π : FreePads C) :
    ProductsHold C π.pads := by
  induction C with
  | input d => trivial
  | layer Q tail ih => exact ⟨rfl, ih π.2.2⟩

/-- The revealed values of a trace, in the shape of the free pads. -/
def revealed {d : ℕ} (C : Circuit F d) (tr : Trace C) : FreePads C :=
  match C with
  | .input _ => ()
  | .layer _ tail => (fun r => ![(tr.rounds r).p0, (tr.rounds r).p2], tr.wc, revealed tail tr.tail)

/-- Arbitrary message translations leave the final challenge point unchanged. -/
theorem run_env_unmask {σ : Type} [DecidableEq σ] (nodes : Sumcheck.Nodes F)
    (env : σ → F) (incoming incoming' : F) (todo : List σ)
    (tr : Fin todo.length → Message F) (pads : Fin todo.length → Fin 2 → F) :
    (run nodes env incoming todo (fun r => unmaskMessage (pads r) (tr r))).1 =
      (run nodes env incoming' todo tr).1 := by
  rw [run_env, run_env]
  rfl

theorem layerRun_env_unmask {d : ℕ} {Tail : Type} (nodes : Sumcheck.Nodes F)
    (c0 c1 c0' c1' : F) (tr : LayerTrace F d Tail)
    (pads : Fin (schedule d).length → Fin 2 → F) :
    (layerRun nodes c0 c1 { tr with rounds := fun r => unmaskMessage (pads r) (tr.rounds r) }).1 =
      (layerRun nodes c0' c1' tr).1 :=
  run_env_unmask nodes _ _ _ _ _ _

/-- Translating an arbitrary pair does not alter the fresh scalar challenge. -/
theorem unmaskMessage_challenge (pads : Fin 2 → F) (msg : Message F) :
    (unmaskMessage pads msg).challenge = msg.challenge := rfl

end GordieHowe.GKR.PadTranslation
