-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Applications.MLDSA.Flattened.Signer
public import GordieHowe.Applications.MLDSA.Flattened.Core.Oracle
public import GordieHowe.Model.ROM.ProgEnv
public import GordieHowe.Foundations.ToMathlib.PMFUniformPullback

public section

/-!
# Presentations of the single-key flattened ML-DSA signer

A presentation answers a context `ctx` chosen by the verifier: it draws a fresh `R`, computes
`µ = H_µ(tr ‖ R ‖ ctx)` (FIPS 204 Algorithm 7 line 6 with `M = R ‖ ctx`), runs the flattened
signer with `c̃ = H(µ ‖ w1Encode(w₁))` read from the random oracle, and publishes `(µ, w₁, c̃)`.
The game is zero knowledge in the quantum random-oracle model (`GordieHowe.QROM.ZeroKnowledge`,
query-bounded quantum adversaries all of whose queries are counted) with one random function on the
points of both oracles (`PresIn`, `PresOut`), the presenter given as an oracle program
(`honestPresenterProg`): the adversary chooses `ctx` for each presentation and sees exactly
`(µ, w₁, c̃)` per presentation, besides the oracles and whatever it holds (the public key, so
`tr`). `R` and the rest of the signature are not published.
-/

namespace GordieHowe.MLDSA

open _root_.MLDSA _root_.MLDSA.Concrete Finset PMF GordieHowe.ROM.NIZK GordieHowe.QROM
open scoped ENNReal BigOperators

variable {p : Params} [NeZero (bucketCount p)] {Rnd Ctx : Type}

/-- **The points of the presentation oracles**: `H_µ` at `(tr, R, ctx)` (`µ = H_µ(tr ‖ R ‖ ctx)`)
and `H` at `(µ, w₁)` (`c̃ = H(µ ‖ w1Encode(w₁))`). -/
inductive PresIn (p : Params) (Rnd Ctx : Type) where
  /-- The message-representative oracle at `tr ‖ R ‖ ctx`. -/
  | mu (tr : _root_.MLDSA.Bytes 64) (R : Rnd) (ctx : Ctx)
  /-- The commitment-hash oracle at `µ ‖ w1Encode(w₁)`. -/
  | commit (mu : _root_.MLDSA.Bytes 64) (w1 : BucketVec p)
  deriving DecidableEq

/-- **The values of the presentation oracle**: a message representative and a commitment hash.
`H_µ` reads the first component and `H` the second. A uniform function into this type has
uniform, independent components, which is the form the presentation game draws its oracle
in. -/
structure PresOut (p : Params) where
  /-- The value read as `H_µ`. -/
  mu : _root_.MLDSA.Bytes 64
  /-- The value read as `H`. -/
  cTilde : CommitHashBytes p
  deriving DecidableEq, Fintype

/-- **One presentation**: `(µ, w₁, c̃)`. -/
structure Presentation (p : Params) where
  /-- The message representative. -/
  mu : _root_.MLDSA.Bytes 64
  /-- The commitment. -/
  w1 : BucketVec p
  /-- The commitment hash. -/
  cTilde : CommitHashBytes p
  deriving DecidableEq, Fintype

/-- `PresIn` as a sum. -/
def PresIn.equivSum (p : Params) (Rnd Ctx : Type) :
    PresIn p Rnd Ctx ≃
      (_root_.MLDSA.Bytes 64 × Rnd × Ctx) ⊕ (_root_.MLDSA.Bytes 64 × BucketVec p) where
  toFun x := match x with
    | PresIn.mu tr r c => .inl (tr, r, c)
    | PresIn.commit m w1 => .inr (m, w1)
  invFun x := match x with
    | .inl (tr, r, c) => PresIn.mu tr r c
    | .inr (m, w1) => PresIn.commit m w1
  left_inv x := by cases x <;> rfl
  right_inv x := by rcases x with ⟨_, _, _⟩ | ⟨_, _⟩ <;> rfl

instance instFintypePresIn [Fintype Rnd] [Fintype Ctx] : Fintype (PresIn p Rnd Ctx) :=
  Fintype.ofEquiv _ (PresIn.equivSum p Rnd Ctx).symm

instance instNonemptyPresOut : Nonempty (PresOut p) :=
  ⟨⟨default, default⟩⟩

/-- The points of the presentation oracles are nonempty: a commitment-hash point at the zero bucket
vector. -/
instance instNonemptyPresIn : Nonempty (PresIn p Rnd Ctx) :=
  ⟨.commit default fun _ => 0⟩

/-- **A group structure on the values of the presentation oracle**: the cyclic group on
`Fin |PresOut p|` carried over by an enumeration. The quantum oracle adds its answer into a
register, so its value type needs some group structure; the quantum statements take the group as
an instance argument and hold for every one, and this definition witnesses that one exists. It is
not an instance. -/
@[instance_reducible]
noncomputable def presOutAddCommGroup : AddCommGroup (PresOut p) :=
  haveI : NeZero (Fintype.card (PresOut p)) := ⟨Fintype.card_ne_zero⟩
  (Fintype.equivFin (PresOut p)).addCommGroup

variable (prims : Primitives p) [nttOps : NTTRingOps] [Nonempty (MaskBox p)] (sk : SecretKey p)
  (aHat : TqMatrix p.k p.l) (cut : Cutoff p)

/-- **The loop tape**, a proof device: a kept commitment for every function of commitment hashes,
drawn independently (`loopTapeLaw`, an independent loop per `H`-slice); a presentation reads it at
the function `H(µ ‖ ·)`. On every fixed oracle the presentation then has the law of the signer's
loop (`map_prove_honestPresenter`). -/
abbrev LoopTape (p : Params) : Type := (BucketVec p → CommitHashBytes p) → Option (BucketVec p)

/-- The law of the loop tape: independent loops against every function of commitment hashes. -/
@[expose] noncomputable def loopTapeLaw : PMF (LoopTape p) :=
  PMF.pi fun f => flatSliceLoop prims sk aHat cut f

/-- **Publishing from the loop tape**: at `µ`, read the tape at the function `H(µ ‖ ·)` and
publish `(µ, w₁, H(µ ‖ w₁))` for the kept `w₁`, or `none`. It reads the oracle only at the points
`(µ, ·)`. -/
def presentAt (O : PresIn p Rnd Ctx → PresOut p) (mu : _root_.MLDSA.Bytes 64) (τ : LoopTape p) :
    Option (Presentation p) :=
  (τ fun v => (O (.commit mu v)).cTilde).map fun w1 => ⟨mu, w1, (O (.commit mu w1)).cTilde⟩

omit [NeZero (bucketCount p)] nttOps [Nonempty (MaskBox p)] in
theorem presentAt_eq (O : PresIn p Rnd Ctx → PresOut p) (mu : _root_.MLDSA.Bytes 64)
    (τ : LoopTape p) :
    presentAt O mu τ =
      (τ fun v => (O (.commit mu v)).cTilde).map fun w1 =>
        ⟨mu, w1, (O (.commit mu w1)).cTilde⟩ := by
  unfold presentAt; rfl

omit [NeZero (bucketCount p)] nttOps [Nonempty (MaskBox p)] in
/-- Publishing reads the oracle only at the points `(µ, ·)`. -/
theorem presentAt_congr {O O' : PresIn p Rnd Ctx → PresOut p} {mu : _root_.MLDSA.Bytes 64}
    (h : ∀ v, O (.commit mu v) = O' (.commit mu v)) (τ : LoopTape p) :
    presentAt O mu τ = presentAt O' mu τ := by
  simp only [presentAt, h]

variable [Fintype Rnd] [Nonempty Rnd] [DecidableEq Rnd] [Fintype Ctx] [DecidableEq Ctx]

/-- **The honest presenter** for the public key with `tr = H(pk)`: on `ctx`, with coins a fresh
`R` and the loop tape, `µ = H_µ(tr ‖ R ‖ ctx)` and the signer's loop against `H(µ ‖ ·)`
(`flatSliceLoop`, read from the tape); it publishes `(µ, w₁, c̃)`, or `none` if the loop never
keeps. Its coins are drawn from `honestPresenterLaw`.
Its reply on every oracle has the law of fresh `R` and the loop (`map_prove_honestPresenter`). -/
def honestPresenter (tr : _root_.MLDSA.Bytes 64) :
    NARG.ProverFn (PresIn p Rnd Ctx) (PresOut p) Ctx Unit (Option (Presentation p))
      (Rnd × LoopTape p) where
  prove O ctx _ c := presentAt O (O (.mu tr c.1 ctx)).mu c.2

/-- **The honest presenter's coin law**: a uniform `R` and an independent loop tape drawn from
`loopTapeLaw`. -/
@[expose] noncomputable def honestPresenterLaw : PMF (Rnd × LoopTape p) :=
  (uniformOfFintype Rnd).bind fun R => (loopTapeLaw prims sk aHat cut).map (R, ·)

omit [NeZero (bucketCount p)] nttOps [Nonempty (MaskBox p)] [Fintype Rnd] [Nonempty Rnd]
  [DecidableEq Rnd] [Fintype Ctx] [DecidableEq Ctx] in
theorem honestPresenter_prove (tr : _root_.MLDSA.Bytes 64) (O : PresIn p Rnd Ctx → PresOut p)
    (ctx : Ctx) (w : Unit) (c : Rnd × LoopTape p) :
    (honestPresenter tr).prove O ctx w c = presentAt O (O (.mu tr c.1 ctx)).mu c.2 := by
  unfold honestPresenter; rfl

/-- **An enumeration of the bucket vectors**, from `FinEnum` of the function type. Sealed, so that
no proof unfolds the enumeration. -/
@[irreducible] def bucketVecList (p : Params) : List (BucketVec p) :=
  FinEnum.toList (CoeffIndex p → Fin (bucketCount p))

omit [NeZero (bucketCount p)] nttOps [Nonempty (MaskBox p)] in
/-- Every bucket vector is in `bucketVecList`. -/
theorem mem_bucketVecList (v : BucketVec p) : v ∈ bucketVecList p := by
  unfold bucketVecList
  exact FinEnum.mem_toList (α := CoeffIndex p → Fin (bucketCount p)) v

omit [NeZero (bucketCount p)] nttOps [Nonempty (MaskBox p)] in
/-- `bucketVecList` has one entry per bucket vector. -/
theorem length_bucketVecList : (bucketVecList p).length = Fintype.card (BucketVec p) := by
  unfold bucketVecList
  change (FinEnum.toList (CoeffIndex p → Fin (bucketCount p))).length =
    Fintype.card (CoeffIndex p → Fin (bucketCount p))
  rw [FinEnum.toList, List.length_map, List.length_finRange]
  exact FinEnum.card_eq_fintypeCard.trans (Fintype.card_congr (Equiv.refl _))

omit nttOps [Nonempty (MaskBox p)] in
/-- **The honest presenter as an oracle program**: it queries `H_µ` at `(tr, R, ctx)`, then `H` at
every point `(µ, v)`, and reads the loop tape at the function `H(µ ‖ ·)` so tabulated. Reading the
loop tape, a device of the proof, needs the whole function `H(µ ‖ ·)`, so the program queries
`1 + |BucketVec p|` points; the signer's loop itself queries `H(µ ‖ ·)` only at the commitments it
tries. Its semantics is `honestPresenter tr` (`honestPresenterProg_toFn`). -/
def honestPresenterProg (tr : _root_.MLDSA.Bytes 64) :
    NARG.Prover (PresIn p Rnd Ctx) (PresOut p) Ctx Unit (Option (Presentation p))
      (Rnd × LoopTape p) where
  prog ctx _ c := .query (.mu tr c.1 ctx) fun y =>
    (OracleProg.tabulate (fun _ => default) (bucketVecList p)
        fun v => .query (.commit y.mu v) fun z => .pure z.cTilde).bind fun g =>
      .pure ((c.2 g).map fun w1 => ⟨y.mu, w1, g w1⟩)
  q := Fintype.card (BucketVec p) + 1
  prog_queries ctx w c := by
    refine OracleProg.QueriesLE.query _ fun y => ?_
    have h := OracleProg.QueriesLE.tabulate (fun _ => (default : CommitHashBytes p))
      (bucketVecList p) (q := 1) fun v =>
        OracleProg.QueriesLE.query (PresIn.commit (Rnd := Rnd) (Ctx := Ctx) y.mu v)
          (k := fun z : PresOut p => OracleProg.pure z.cTilde) fun _ =>
          OracleProg.QueriesLE.pure _ 0
    rw [length_bucketVecList, mul_one] at h
    exact (h.bind (q₂ := 0) fun _ => OracleProg.QueriesLE.pure _ 0).mono (Nat.add_zero _).le

omit [NeZero (bucketCount p)] nttOps [Nonempty (MaskBox p)] [Fintype Rnd] [Nonempty Rnd]
  [DecidableEq Rnd] [Fintype Ctx] [DecidableEq Ctx] in
/-- The honest presenter's program computes the honest presenter. -/
theorem honestPresenterProg_toFn (tr : _root_.MLDSA.Bytes 64) :
    (honestPresenterProg (Rnd := Rnd) (Ctx := Ctx) tr).toFn = honestPresenter (p := p) tr := by
  rw [honestPresenter, NARG.Prover.toFn]
  congr 1
  funext O ctx w c
  simp only [honestPresenterProg, OracleProg.run_query, OracleProg.run_bind,
    OracleProg.run_tabulate, OracleProg.run_pure, mem_bucketVecList, ite_true,
    presentAt]

omit [DecidableEq Rnd] in
theorem honestPresenterLaw_eq :
    honestPresenterLaw (Rnd := Rnd) prims sk aHat cut =
      (uniformOfFintype Rnd).bind fun R => (loopTapeLaw prims sk aHat cut).map (R, ·) := by
  unfold honestPresenterLaw; rfl

omit [DecidableEq Rnd] [Fintype Ctx] [DecidableEq Ctx] in
/-- **The honest reply on a fixed oracle** is a fresh `R`, `µ = H_µ(tr ‖ R ‖ ctx)` and the
signer's loop against `H(µ ‖ ·)` (`pi_map_eval`). -/
theorem map_prove_honestPresenter (tr : _root_.MLDSA.Bytes 64) (O : PresIn p Rnd Ctx → PresOut p)
    (ctx : Ctx) :
    (honestPresenterLaw (Rnd := Rnd) prims sk aHat cut).map
        (fun c => (honestPresenter (Ctx := Ctx) tr).prove O ctx () c) =
      (uniformOfFintype Rnd).bind fun R =>
        (flatSliceLoop prims sk aHat cut fun v => (O (.commit (O (.mu tr R ctx)).mu v)).cTilde).map
          (Option.map fun w1 =>
            ⟨(O (.mu tr R ctx)).mu, w1, (O (.commit (O (.mu tr R ctx)).mu w1)).cTilde⟩) := by
  simp only [honestPresenter, honestPresenterLaw, PMF.map_bind]
  congr 1
  funext R
  rw [PMF.map_comp, loopTapeLaw]
  rw [show ((fun c : Rnd × LoopTape p => presentAt O (O (.mu tr c.1 ctx)).mu c.2) ∘
      fun x => (R, x)) = Option.map (fun w1 => (⟨(O (.mu tr R ctx)).mu, w1,
        (O (.commit (O (.mu tr R ctx)).mu w1)).cTilde⟩ : Presentation p)) ∘
      fun τ : LoopTape p => τ fun v => (O (.commit (O (.mu tr R ctx)).mu v)).cTilde from rfl,
    ← PMF.map_comp, PMF.pi_map_eval]

/-- **The simulator of the flattened presentations with a sampler** `f`: on `ctx`, with coins
`(µ, u)` for a uniform `u`, it publishes `(µ, w₁, c̃) = (µ, f u)` and programs `H(µ ‖ w₁) := c̃`.
It reads neither the key nor `tr`, and does not program `H_µ`.

Its output on the oracle `O`, a statement and coins `s` is the presentation
`(s.salt, f s.coins)` with the assignment list of one entry that sets the point
`commit s.salt (f s.coins).1` to the commitment hash `(f s.coins).2`, keeping the
`H_µ`-component of `O` at that point (`flatPresentSimOf_run`).

Running time: it evaluates `f` once on its coins, reads the oracle at one point `(µ, w₁)` to keep
its `H_µ`-component, and returns an assignment list of length one; the coins are `512` bits and
the sampler's coins. This running time is argued here, not proved in Lean. -/
def flatPresentSimOf {C : Type} [Fintype C] [Nonempty C]
    (f : C → BucketVec p × CommitHashBytes p) :
    NARG.SimulatorFn (PresIn p Rnd Ctx) (PresOut p) Ctx (Option (Presentation p))
      (SaltedCoins (_root_.MLDSA.Bytes 64) C) where
  run O _ s :=
    ⟨some ⟨s.salt, (f s.coins).1, (f s.coins).2⟩,
      [⟨.commit s.salt (f s.coins).1, ⟨(O (.commit s.salt (f s.coins).1)).mu, (f s.coins).2⟩⟩]⟩
  coins_nonempty := inferInstance

omit [NeZero (bucketCount p)] nttOps [Nonempty (MaskBox p)] [Fintype Rnd] [Nonempty Rnd]
  [DecidableEq Rnd] [Fintype Ctx] [DecidableEq Ctx] in
theorem flatPresentSimOf_run {C : Type} [Fintype C] [Nonempty C]
    (f : C → BucketVec p × CommitHashBytes p) (O : PresIn p Rnd Ctx → PresOut p) (x : Ctx)
    (s : SaltedCoins (_root_.MLDSA.Bytes 64) C) :
    (flatPresentSimOf f).run O x s =
      ⟨some ⟨s.salt, (f s.coins).1, (f s.coins).2⟩,
        [⟨.commit s.salt (f s.coins).1,
          ⟨(O (.commit s.salt (f s.coins).1)).mu, (f s.coins).2⟩⟩]⟩ := by
  unfold flatPresentSimOf; rfl

/-- **The presentation simulator**: on `ctx`, with uniform coins `(µ, (w₁, c̃))` (`flatTarget`
with a uniform `µ`), it publishes `(µ, w₁, c̃)` and programs `H(µ ‖ w₁) := c̃`
(`flatPresentSimOf` with the identity sampler). It reads neither the key nor `tr`, and does not
program `H_µ`.

Its output on the oracle `O`, a statement and coins `s` is the presentation
`(s.salt, s.coins)` with the assignment list of one entry that sets the point
`commit s.salt s.coins.1` to the commitment hash `s.coins.2`, keeping the `H_µ`-component of `O`
at that point (`flatPresentSim_run`).

Running time: it copies its coins, reads the oracle at one point `(µ, w₁)` to keep its
`H_µ`-component, and returns an assignment list of length one; the coins are `512` bits, a bucket
vector and a commitment hash. This running time is argued here, not proved in Lean. -/
def flatPresentSim :
    NARG.SimulatorFn (PresIn p Rnd Ctx) (PresOut p) Ctx (Option (Presentation p))
      (SaltedCoins (_root_.MLDSA.Bytes 64) (BucketVec p × CommitHashBytes p)) :=
  flatPresentSimOf id

omit nttOps [Nonempty (MaskBox p)] [Fintype Rnd] [Nonempty Rnd] [DecidableEq Rnd] [Fintype Ctx]
  [DecidableEq Ctx] in
/-- The presentation simulator is the simulator with the identity sampler. -/
theorem flatPresentSim_eq_flatPresentSimOf :
    (flatPresentSim : NARG.SimulatorFn (PresIn p Rnd Ctx) (PresOut p) Ctx _ _) =
      flatPresentSimOf id := by
  unfold flatPresentSim
  rfl

omit nttOps [Nonempty (MaskBox p)] [Fintype Rnd] [Nonempty Rnd] [DecidableEq Rnd] [Fintype Ctx]
  [DecidableEq Ctx] in
theorem flatPresentSim_run (O : PresIn p Rnd Ctx → PresOut p) (x : Ctx)
    (s : SaltedCoins (_root_.MLDSA.Bytes 64) (BucketVec p × CommitHashBytes p)) :
    flatPresentSim.run O x s =
      ⟨some ⟨s.salt, s.coins.1, s.coins.2⟩,
        [⟨.commit s.salt s.coins.1, ⟨(O (.commit s.salt s.coins.1)).mu, s.coins.2⟩⟩]⟩ := by
  rw [flatPresentSim_eq_flatPresentSimOf, flatPresentSimOf_run]
  rfl

/-- **The simulator of the flattened presentations with a sampler, as an oracle program**: with
coins `(µ, u)` it queries the point `(µ, w₁)` for `(w₁, c̃) = f u`, publishes `(µ, w₁, c̃)` and
programs `H(µ ‖ w₁) := c̃`, keeping the `H_µ`-component it read. Its semantics is
`flatPresentSimOf f` (`flatPresentSimProgOf_toFn`).

Running time: it evaluates `f` once on its coins, makes one query at `(µ, w₁)`, and returns an
assignment list of length one; the coins are `512` bits and the sampler's coins. This running
time is argued here, not proved in Lean. -/
def flatPresentSimProgOf {C : Type} [Fintype C] [Nonempty C]
    (f : C → BucketVec p × CommitHashBytes p) :
    NARG.Simulator (PresIn p Rnd Ctx) (PresOut p) Ctx (Option (Presentation p))
      (SaltedCoins (_root_.MLDSA.Bytes 64) C) where
  prog _ s := .query (.commit s.salt (f s.coins).1) fun y =>
    .pure ⟨some ⟨s.salt, (f s.coins).1, (f s.coins).2⟩,
      [⟨.commit s.salt (f s.coins).1, ⟨y.mu, (f s.coins).2⟩⟩]⟩
  coins_nonempty := inferInstance
  q := 1
  prog_queries _ _ := OracleProg.QueriesLE.query _ fun _ => OracleProg.QueriesLE.pure _ 0

omit [NeZero (bucketCount p)] nttOps [Nonempty (MaskBox p)] [Fintype Rnd] [Nonempty Rnd]
  [DecidableEq Rnd] [Fintype Ctx] [DecidableEq Ctx] in
/-- The simulator program with a sampler computes the simulator with that sampler. -/
theorem flatPresentSimProgOf_toFn {C : Type} [Fintype C] [Nonempty C]
    (f : C → BucketVec p × CommitHashBytes p) :
    (flatPresentSimProgOf (Rnd := Rnd) (Ctx := Ctx) f).toFn = flatPresentSimOf f := by
  rw [flatPresentSimOf]
  rfl

/-- **The presentation simulator as an oracle program**: `flatPresentSimProgOf` with the identity
sampler. Its semantics is `flatPresentSim` (`flatPresentSimProg_toFn`).

Running time: it copies its coins, makes one query at `(µ, w₁)`, and returns an assignment list of
length one; the coins are `512` bits, a bucket vector and a commitment hash. This running time is
argued here, not proved in Lean. -/
def flatPresentSimProg :
    NARG.Simulator (PresIn p Rnd Ctx) (PresOut p) Ctx (Option (Presentation p))
      (SaltedCoins (_root_.MLDSA.Bytes 64) (BucketVec p × CommitHashBytes p)) :=
  flatPresentSimProgOf id

omit nttOps [Nonempty (MaskBox p)] [Fintype Rnd] [Nonempty Rnd] [DecidableEq Rnd] [Fintype Ctx]
  [DecidableEq Ctx] in
/-- The presentation simulator program is the simulator program with the identity sampler. -/
theorem flatPresentSimProg_eq_flatPresentSimProgOf :
    (flatPresentSimProg : NARG.Simulator (PresIn p Rnd Ctx) (PresOut p) Ctx _ _) =
      flatPresentSimProgOf id := by
  unfold flatPresentSimProg
  rfl

omit nttOps [Nonempty (MaskBox p)] [Fintype Rnd] [Nonempty Rnd] [DecidableEq Rnd] [Fintype Ctx]
  [DecidableEq Ctx] in
/-- The presentation simulator program computes the presentation simulator. -/
theorem flatPresentSimProg_toFn :
    (flatPresentSimProg (Rnd := Rnd) (Ctx := Ctx) (p := p)).toFn = flatPresentSim := by
  rw [flatPresentSim_eq_flatPresentSimOf]
  rfl

end GordieHowe.MLDSA
