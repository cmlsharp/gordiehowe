-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Model.Quantum.Interactive.Adaptive

@[expose] public section

/-!
# The shape of an adversary

A register type shared between algorithms is written as the register type of a shape term, never
through an algorithm.

The shape of an adversary with run-time kinds (`AlgShape`) is its workspace, width, slots, post
batches, budget and Kraus index; that of an algorithm with run-time kinds (`KindShape`) is the same
without the budget. Every constructor of adversaries has a shape function, which takes only the
input shape and numbers or types, never steps, kinds, initial states, outputs or whole relays,
and a `toShape` lemma, closed by `rfl`: the shape of the constructed adversary is the shape
function at the input shape. Two adversaries that differ only in their steps (say, in the coins of
a relay) then have the same register types, which `rfl` checks against the shape term without
comparing the two adversaries. Comparing an adversary's projection with a shape term reduces only
the adversary's side; comparing the projections of two adversaries first compares the two
adversaries, deep down to where they differ.

## Declarations

- `AlgShape`: the shape of an adversary; `AdaptiveIAlg.toShape`. `KindShape`, the type index of
  `KindAlg` (`KindAlg.toShape`), is declared with `KindAlg` (`Basic.lean`).
- `AlgShape.toKindS` (`AdaptiveIAlg.toKindAlg_toShape`), `AlgShape.tpKindS` (the
  trace-preserving form, `toTPKindAlg`), `AlgShape.abortS` (`abortAlg`), `AlgShape.restrictAtS`
  (`restrictAt`), `AlgShape.withConstS` (`withConst`). The constructors that keep the shape
  (`unitOut`, `mapOut`, `withStep`) have the identity as shape function; their lemmas sit next to
  them.
- `AlgShape.toAdaptiveS` (`Distinguisher.toAdaptive`).
- `KindShape.DW` (`KindAlg.DW_eq_shape`): the workspace of the dilation (`KindAlg.dilate`).
- `KindShape.CW`: the composed work register of a shape with a challenger (`KindAlg.CW`).
- `PMF.map_cast_congr`: the transport of a family of laws along an equality of indices, with
  casts to one outcome type.

The shape functions of the later constructors sit next to them: `AlgShape.absorbS`
(`Absorb.lean`), `patchTagS` (`AssignPatch.lean`), `relayAdvS` (`MultiRelay.lean`),
`absorbAssignS` (`AbsorbAssign.lean`), `absorbTabS` (`ReqBridge.lean`), `seAlgKFS`
(`GordieHowe/Applications/Ring/KeyFreeSE.lean`).
-/

namespace GordieHowe.Quantum

variable {X Y Req Resp O : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
  [Fintype Req] [DecidableEq Req] [Fintype Resp] [DecidableEq Resp]

namespace AlgShape

variable (s : AlgShape X Y Req Resp)

/-- The shape of the trace-preserving form `toTPKindAlg`: the workspace with the query counter,
the Kraus index with the completion's and the end's operators. -/
@[reducible] def tpKindS : KindShape X Y Req Resp where
  W := s.CntW
  width := s.width
  width_pos := s.width_pos
  slots := s.slots
  post := s.post
  R := s.R ⊕ (s.R ⊕ Fin (s.budget + 2))

/-- The shape of the aborting completion `abortAlg`. -/
@[reducible] def abortS : AlgShape X Y Req Resp where
  W := s.CntW
  width := s.width
  width_pos := s.width_pos
  slots := s.slots
  post := s.post
  budget := s.budget
  R := s.R ⊕ (s.R ⊕ Fin (s.budget + 2))

/-- The shape of `restrictAt` at the split `Y ≃+ Y₁ × Y₂`: the workspace with the `Y₁`-parts of
the query answers. -/
@[reducible] def restrictAtS (Y₁ Y₂ : Type) [Fintype Y₁] [DecidableEq Y₁] : AlgShape X Y₂ Req Resp where
  W := s.W × (Fin s.width → Y₁)
  width := s.width
  width_pos := s.width_pos
  slots := s.slots
  post := s.post
  budget := s.budget
  R := s.R

/-- The shape of `withConst` with the constant register `T`. -/
@[reducible] def withConstS (T : Type) [Fintype T] [DecidableEq T] : AlgShape X Y Req Resp where
  W := s.W × T
  width := s.width
  width_pos := s.width_pos
  slots := s.slots
  post := s.post
  budget := s.budget
  R := s.R

/-- The shape of `Distinguisher.toAdaptive`: the distinguisher's workspace, width and slots, no
post batches, the budget `q`, one Kraus operator. -/
@[reducible] def toAdaptiveS (W : Type) [Fintype W] [DecidableEq W] (n m : ℕ) (hn : 0 < n) (q : ℕ) :
    AlgShape X Y Req Resp where
  W := W
  width := n
  width_pos := hn
  slots := m
  post := 0
  budget := q
  R := Unit

end AlgShape

namespace KindShape

variable (s : KindShape X Y Req Resp)

/-- **The composed work register** of an algorithm of shape `s` with the challenger `C`
(`KindAlg.CW`). -/
abbrev CW (C : Challenger X Y Req Resp) : Type :=
  CWork s.W s.width X Y Req Resp s.slots C.q C.Coins

end KindShape

namespace AlgShape

/-- **Decidable equality of the composed work register of the adversary with its counter at a
shape** (`AdaptiveIAlg.toKindAlg`, `toTPKindAlg`), as one instance over the named counter
workspace: one instance search over the registers built from it stays within the default size
limit of instance search. -/
instance instDecidableEqCntCW (s : AlgShape X Y Req Resp) (C : Challenger X Y Req Resp) :
    DecidableEq (CWork s.CntW s.width X Y Req Resp s.slots C.q C.Coins) :=
  inferInstance

end AlgShape

namespace AdaptiveIAlg

variable {sh : AlgShape X Y Req Resp} (A : AdaptiveIAlg sh O)

theorem toKindAlg_toShape : A.toKindAlg.toShape = A.toShape.toKindS :=
  rfl

end AdaptiveIAlg

namespace KindAlg

variable {ksA : KindShape X Y Req Resp} (A : KindAlg ksA O)

theorem DW_eq_shape : A.DW = A.toShape.DW :=
  rfl

theorem CW_eq_shape (C : Challenger X Y Req Resp) : A.CW C = A.toShape.CW C :=
  rfl

end KindAlg

end GordieHowe.Quantum

/-- **The transport of a family of laws along an equality of indices**: at equal indices
`a₁ = a₂`, the laws `f a₁` and `f a₂`, cast to one outcome type `Ω`, are equal. With `Ω` a shape
term's type, this compares two adversaries' laws without comparing their outcome types with each
other. -/
theorem PMF.map_cast_congr.{u, v} {T : Sort u} {α : T → Type v} (f : (a : T) → PMF (α a))
    {a₁ a₂ : T} (h : a₁ = a₂) {Ω : Type v} (h₁ : α a₁ = Ω) (h₂ : α a₂ = Ω) :
    (f a₁).map (cast h₁) = (f a₂).map (cast h₂) := by
  subst h
  rfl
