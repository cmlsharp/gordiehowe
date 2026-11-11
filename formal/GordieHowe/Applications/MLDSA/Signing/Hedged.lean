-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Applications.MLDSA.Signing.Oracles
public import GordieHowe.Model.NARG.OracleProg

@[expose] public section

/-!
# FIPS 204 hedged signing with the mask derivation a random oracle

FIPS 204 Algorithm 7 derives the masks of a signature from a 32-byte nonce `rnd`:
`y = ExpandMask(H(K ‖ rnd ‖ µ), κ)` (lines 7 and 11). Here the derivation is a part of the one
random oracle `X → Y`.

- `MaskPt T Msg`: the points of the mask oracle at one nonce, `(κ, (K, (tr, m)))`.
- `MaskOracle X Y p T Msg`: the mask oracle inside the one random oracle: its points
  `(rnd, (κ, (K, (tr, m))))` embedded in `X`, its values decoded from `Y` onto the mask box.
- `MaskSource`: where the masks of a call come from. `MaskSource.hedged M`: from the mask oracle at
  a 32-byte nonce `rnd` (one query per mask); `MaskSource.fresh M`: from a mask function
  `MaskFn T Msg Y` (the named function type `MaskPt T Msg → Y`) drawn with the signing coins (no
  query). `run_read_hedged`, `run_read_fresh`: the masks the two sources read.
- `stdProg`, `stdProg_queries`, `exists_index_of_run_stdProg_eq_some`: the ordinary hedged FIPS 204
  signer at the first nonce as a classical oracle program (`µ`, then `T` attempts), its query
  bound, and every signature it outputs is the attempt output of one of the masks read.
-/

namespace GordieHowe.MLDSA

open _root_.MLDSA

/-- **The points of the mask oracle at one nonce**: the attempt counter, the secret seed `K` and
the message point `(tr, m)`, the input of `µ`. -/
abbrev MaskPt (T : ℕ) (Msg : Type) : Type := Fin T × (Bytes 32 × (Bytes 64 × Msg))

open scoped ENNReal

variable {X Y : Type}

/-! ### The mask oracle and the sources of masks -/

/-- **The mask oracle of FIPS 204 hedged signing inside the one random oracle `X → Y`**: the points
`(rnd, (κ, (K, (tr, m))))` of `ExpandMask(H(K ‖ rnd ‖ µ), κ)` (Algorithm 7, lines 7 and 11)
embedded in `X`, the masks decoded from `Y`. -/
structure MaskOracle (X Y : Type) (p : Params) (T : ℕ) (Msg : Type) where
  /-- The points of the mask oracle. -/
  pt : Bytes 32 × MaskPt T Msg → X
  /-- The masks decoded from the oracle's values. -/
  ans : Y → MaskBox p

/-- **A source of masks**: a type `Rnd` of per-call randomness, and the mask at a point of
`MaskPt T Msg` read from it by a program with at most `qr` queries. -/
structure MaskSource (X Y : Type) (p : Params) (T : ℕ) (Msg : Type) where
  /-- The per-call randomness. -/
  Rnd : Type
  /-- The bound on the queries of one mask. -/
  qr : ℕ
  /-- The mask at a point, read from the randomness. -/
  read : Rnd → MaskPt T Msg → OracleProg X Y (MaskBox p)
  /-- It makes at most `qr` queries. -/
  read_queries : ∀ r u, (read r u).QueriesLE qr

variable {p : Params} {T : ℕ} {Msg : Type}

/-- **The hedged source**: the mask at the point `u` of the nonce `rnd` is the mask oracle's value
at `(rnd, u)`, one query. -/
@[reducible]
def MaskSource.hedged (M : MaskOracle X Y p T Msg) : MaskSource X Y p T Msg where
  Rnd := Bytes 32
  qr := 1
  read r u := .query (M.pt (r, u)) fun y => .pure (M.ans y)
  read_queries _ _ _ := by simp [OracleProg.trace_query, OracleProg.trace_pure]

/-- **The mask functions of the fresh source**: a value in `Y` at each mask point. A named type, so
instance search stops at the name instead of rebuilding the instances of the function type inside
the coins of the fresh ring loop. -/
def MaskFn (T : ℕ) (Msg Y : Type) : Type := MaskPt T Msg → Y

instance instFintypeMaskFn [Fintype Msg] [DecidableEq Msg] [Fintype Y] :
    Fintype (MaskFn T Msg Y) :=
  inferInstanceAs (Fintype (MaskPt T Msg → Y))

instance instDecidableEqMaskFn [Fintype Msg] [DecidableEq Y] : DecidableEq (MaskFn T Msg Y) :=
  inferInstanceAs (DecidableEq (MaskPt T Msg → Y))

instance instNonemptyMaskFn [Nonempty Y] : Nonempty (MaskFn T Msg Y) :=
  inferInstanceAs (Nonempty (MaskPt T Msg → Y))

/-- **The fresh source**: the mask at the point `u` is the decoding of `g u` for a mask function
`g : MaskFn T Msg Y` drawn with the signing coins, no query. -/
@[reducible]
def MaskSource.fresh (M : MaskOracle X Y p T Msg) : MaskSource X Y p T Msg where
  Rnd := MaskFn T Msg Y
  qr := 0
  read g u := .pure (M.ans (g u))
  read_queries _ _ := OracleProg.QueriesLE.pure _ _

/-- The hedged source reads the mask oracle. -/
theorem run_read_hedged (M : MaskOracle X Y p T Msg) (r : Bytes 32) (u : MaskPt T Msg)
    (H : X → Y) : ((MaskSource.hedged M).read r u).run H = M.ans (H (M.pt (r, u))) :=
  rfl

/-- The fresh source decodes its function. -/
theorem run_read_fresh (M : MaskOracle X Y p T Msg) (g : MaskFn T Msg Y) (u : MaskPt T Msg)
    (H : X → Y) : ((MaskSource.fresh M).read g u).run H = M.ans (g u) :=
  rfl

/-! ### The ordinary signer -/

section Loop

variable (prims : Primitives p) [NeZero (bucketCount p)] [nttOps : NTTRingOps] {N reps : ℕ}

variable [Fintype prims.Power2High] [DecidableEq prims.Power2High] [Fintype prims.Hint]
  [DecidableEq prims.Hint] [Inhabited prims.Hint] [Nonempty (MaskBox p)]

/-- **The ordinary hedged FIPS 204 signer** (Algorithm 7) at the randomness of the first call:
`µ = H_µ(tr, m)` (one query), the `T` masks, the commitment hash `H(µ, w₁)` at each mask's
commitment, and the signature of the first mask whose attempt passes the checks (`none` when none
does, or when `k = 0`). -/
def stdProg (src : MaskSource X Y p T Msg) (O : MLDSAOracles X Y p Msg)
    (k : ℕ) (sk : SecretKey p) (m : Msg) (r : Fin k → src.Rnd) :
    OracleProg X Y (Option (FIPSSignature p prims)) :=
  if hk : 0 < k then
    .query (O.muPt (sk.tr, m)) fun yMu =>
      (OracleProg.tabulate (fun _ => maskBoxPoint p) (List.finRange T) fun t =>
          src.read (r ⟨0, hk⟩) (t, (sk.key, (sk.tr, m)))).bind fun ys =>
        (OracleProg.tabulate (fun _ => default) (List.finRange T) fun t =>
            .query (O.chPt (O.muAns yMu, realBuckets (prims.expandA sk.rho) (ys t))) fun y =>
              .pure (O.chAns y)).mapOutput fun cs =>
          match (List.finRange T).find? (fun t =>
              attemptAccept prims sk (prims.expandA sk.rho) (ys t) (cs t)) with
          | some t => some (attemptOutput prims sk (prims.expandA sk.rho) (ys t, cs t))
          | none => none
  else .pure none

omit [Fintype prims.Power2High] [DecidableEq prims.Power2High] [Fintype prims.Hint]
  [DecidableEq prims.Hint] [Inhabited prims.Hint] in
/-- The ordinary signer makes at most `1 + T · qr + T` queries. -/
theorem stdProg_queries (src : MaskSource X Y p T Msg) (O : MLDSAOracles X Y p Msg)
    (k : ℕ) (sk : SecretKey p) (m : Msg) (r : Fin k → src.Rnd) :
    (stdProg prims src O k sk m r).QueriesLE (1 + T * src.qr + T) := by
  unfold stdProg
  split_ifs with hk
  · refine OracleProg.QueriesLE.mono (q := T * src.qr + T + 1)
      (OracleProg.QueriesLE.query _ fun yMu => ?_) (by omega)
    have h₁ : (OracleProg.tabulate (fun _ => maskBoxPoint p) (List.finRange T)
        fun t => src.read (r ⟨0, hk⟩) (t, (sk.key, (sk.tr, m)))).QueriesLE (T * src.qr) := by
      simpa using OracleProg.QueriesLE.tabulate (fun _ => maskBoxPoint p)
        (List.finRange T) fun t => src.read_queries (r ⟨0, hk⟩) (t, (sk.key, (sk.tr, m)))
    refine h₁.bind fun ys => ?_
    have h₂ := OracleProg.QueriesLE.tabulate (fun _ => (default : CommitHashBytes p))
      (List.finRange T) (q := 1)
      (P := fun t => .query (O.chPt (O.muAns yMu, realBuckets (prims.expandA sk.rho) (ys t)))
        fun y => .pure (O.chAns y))
      fun t h => by simp [OracleProg.trace_query, OracleProg.trace_pure]
    simpa using h₂.mapOutput _
  · exact OracleProg.QueriesLE.pure _ _

omit [Fintype prims.Power2High] [DecidableEq prims.Power2High] [Fintype prims.Hint]
  [DecidableEq prims.Hint] [Inhabited prims.Hint] in
/-- **Every signature of the ordinary signer is the output of one of its masks**: at the oracle
`H`, `stdProg` outputs `σ` only for `k > 0` and as `attemptOutput (y, c̃)` with `y` the mask read
from the first call's randomness at a point `(t, (K, (tr, m)))`. -/
theorem exists_index_of_run_stdProg_eq_some (src : MaskSource X Y p T Msg)
    (O : MLDSAOracles X Y p Msg) (k : ℕ) (sk : SecretKey p) (m : Msg)
    (r : Fin k → src.Rnd) (H : X → Y) {σ : FIPSSignature p prims}
    (h : (stdProg prims src O k sk m r).run H = some σ) :
    ∃ (hk : 0 < k) (t : Fin T) (cTilde : CommitHashBytes p),
      σ = attemptOutput prims sk (prims.expandA sk.rho)
        ((src.read (r ⟨0, hk⟩) (t, (sk.key, (sk.tr, m)))).run H, cTilde) := by
  unfold stdProg at h
  split_ifs at h with hk
  · simp only [OracleProg.run_query, OracleProg.run_bind, OracleProg.run_mapOutput,
      OracleProg.run_tabulate, OracleProg.run_pure, List.mem_finRange, ite_true] at h
    split at h
    · rename_i t _
      exact ⟨hk, t, _, (Option.some.inj h).symm⟩
    · exact absurd h (by simp)
  · exact absurd h (by simp [OracleProg.run_pure])

end Loop

end GordieHowe.MLDSA
