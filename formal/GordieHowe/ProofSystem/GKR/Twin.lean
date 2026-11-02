-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.ProofSystem.GKR.Rel
public import GordieHoweNative.ProofSystem.GKR.Twin

@[expose] public section

/-!
# Failure-reporting twins of `Bool` checkers

A checker `checkB : … → Bool` has a twin `checkE : … → Except ε Unit` that runs the same checks
and, on rejection, returns the first failing item's position and a reason code (constructors, no
strings, so the kernel path builds none). The twin is proved equal to the checker once
(`checkB x = okB (checkE x)`) from one lemma per combinator:

| shape | combinator | lemma |
|---|---|---|
| test `b` | `guardE b e` | `okB_guardE : okB (guardE b e) = b` |
| `b₁ && b₂` | `seqE x y` | `okB_seqE : okB (seqE x y) = (okB x && okB y)` |
| `l.all p` (index `i`) | `allE f i l` | `okB_allE : (∀ i x, okB (f i x) = p x) → okB (allE f i l) = l.all p` |
| `Option` fold stopping at `none` | `foldOptE step fail i b l` | `toOption_foldOptE : (foldOptE …).toOption = l.foldlM step b` |
| test on a fold's result | `thenE x q` | `okB_thenE : okB (thenE x q) = x.toOption.elim false (okB ∘ q)` |
| relabel the failure | `mapE g x` | `okB_mapE : okB (mapE g x) = okB x` |

A new checker may be written as its twin only, with `checkB := okB ∘ checkE`; its soundness proofs
then go through these lemmas. The relational check (`GKR.Rel.relOk`) keeps its `Bool` form, for
the kernel, and has the twin `GKR.Rel.relOkE` (`GKR.Rel.relOk_eq_okB`).

The definitions are in `GordieHoweNative/ProofSystem/GKR/Twin.lean`
(the compiled library `GordieHoweNative`); this module has their lemmas.
-/

namespace GordieHowe.Twin

/-! ## The combinators -/

theorem okB_guardE {ε : Type} (b : Bool) (e : ε) : okB (guardE b e) = b := by
  cases b <;> rfl

theorem okB_seqE {ε : Type} (x y : Except ε Unit) : okB (seqE x y) = (okB x && okB y) := by
  cases x <;> rfl

theorem okB_allE {ε α : Type} {f : ℕ → α → Except ε Unit} {p : α → Bool}
    (h : ∀ i x, okB (f i x) = p x) : ∀ (i : ℕ) (l : List α), okB (allE f i l) = l.all p
  | _, [] => rfl
  | i, x :: xs => by rw [allE, okB_seqE, h, okB_allE h (i + 1) xs, List.all_cons]

/-- **An `Option`-valued fold with indices**: `step` on every element from the state `b`; at the
first `none`, the failure of its index. -/
def foldOptE {ε α β : Type} (step : β → α → Option β) (fail : ℕ → ε) : ℕ → β → List α → Except ε β
  | _, b, [] => .ok b
  | i, b, x :: xs =>
    match step b x with
    | some b' => foldOptE step fail (i + 1) b' xs
    | none => .error (fail i)

theorem toOption_foldOptE {ε α β : Type} (step : β → α → Option β) (fail : ℕ → ε) :
    ∀ (i : ℕ) (b : β) (l : List α), (foldOptE step fail i b l).toOption = l.foldlM step b
  | _, b, [] => rfl
  | i, b, x :: xs => by
    simp only [foldOptE, List.foldlM_cons]
    cases step b x with
    | some b' => exact toOption_foldOptE step fail (i + 1) b' xs
    | none => rfl

theorem okB_thenE {ε β : Type} (x : Except ε β) (q : β → Except ε Unit) :
    okB (thenE x q) = x.toOption.elim false fun b => okB (q b) := by
  cases x <;> rfl

theorem okB_mapE {ε ε' α : Type} (g : ε → ε') (x : Except ε α) : okB (mapE g x) = okB x := by
  cases x <;> rfl

end GordieHowe.Twin

namespace GordieHowe.GKR.Rel

open GordieHowe.GKR.Certificate GordieHowe.GKR.Fold GordieHowe.Twin

/-! ## The twin of the relational check -/

theorem okB_verdictE (pt : Part) (i : ℕ) (r : Option Reason) : okB (verdictE pt i r) = r.isNone := by
  cases r <;> rfl

section

variable (w : ℕ) (D : Dag) (Kc : Consts) (ar : CodeArith)

theorem cutOk_eq_okB (i : ℕ) (W : Wire) (e : TE) :
    okB (cutE w D Kc ar i W e) = cutOk w D Kc ar W e :=
  okB_verdictE _ _ _

theorem zeroOk_eq_okB (i Z U : ℕ) (e : TE) :
    okB (zeroE w D Kc ar i Z U e) = zeroOk w D Kc ar Z U e :=
  okB_verdictE _ _ _

/-- **The twin agrees with the relational check.** -/
theorem relOk_eq_okB (cuts : List (Wire × TE)) (zs : List (ℕ × ℕ × TE)) :
    relOk w D Kc ar cuts zs = okB (relOkE w D Kc ar cuts zs) := by
  rw [relOkE, okB_seqE, okB_seqE, okB_guardE,
    okB_allE (p := fun c => cutOk w D Kc ar c.1 c.2)
      (fun i c => cutOk_eq_okB w D Kc ar i c.1 c.2),
    okB_allE (p := fun z => zeroOk w D Kc ar z.1 z.2.1 z.2.2)
      (fun i z => zeroOk_eq_okB w D Kc ar i z.1 z.2.1 z.2.2), relOk, Bool.and_assoc]

end

end GordieHowe.GKR.Rel
