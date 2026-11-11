-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Applications.MLDSA.Flattened.Presentation
public import GordieHowe.Applications.MLDSA.Flattened.KeepProb
public import GordieHowe.Model.ROM.HiddenProgramming
public import GordieHowe.Model.ROM.ProverCoins
public import GordieHowe.Foundations.ToMathlib.PMFUniformApprox
public import GordieHowe.Model.ROM.InteractiveNIZKLastProofQuery

public section

/-!
# Simulating the presentations of the flattened signer

The bound `presentations_advantage_le_of_keyFloorAt`, at a cut-off under `KeyFloorAt` with the
simulator `flatPresentSimOf f` for a sampler `f` within `δ` of the shaped target, through hybrids
with the loop tape drawn as `g u` for a uniform `u : Fin D` (`honestPresenterAt`;
`exists_map_uniformOfFintype_tvDist_le` puts it within `|LoopTape| / D` of the tape's law, and `D`
is then taken large):

* step A (`advantage_freshMuSim_le`, salt `R`, `zeroKnowledge_of_sliceCloseAt`): the honest
  presenter against `freshMuSim`, which draws `µ` fresh and programs `H_µ(tr, R, ctx) := µ`; the
  two slice laws are equal (`realSliceAt_eq_simSliceAt_freshMu`);
* step C (`abs_acceptProb_simEnv_dropAssignments_le`, salt `R`): dropping that programming;
* step B (`advantage_freshMuPresenter_le_of_keyFloorAt`, salt `µ`,
  `zeroKnowledge_of_sliceCloseAt`): the presenter with a fresh `µ` against `flatPresentSimOf f`.
  Both slice laws are lifts of hash laws by uniform message representatives (`sliceLift`, which
  does not increase the distance): the simulator's of the sampled target followed by the
  reprogramming kernel (`simSliceAt_flatPresentSimOf_eq_sliceLift`). The one-presentation term is
  `stepBError + δ`: the loop against a uniform commitment-hash function against the shaped target
  (`tvDist_oracleProver_le`, `tvDist_flatSigner_shapedTarget_le_of_keyFloorAt`), the distance of
  the tape drawn as `g u` from the tape's law, and `δ`.

Moving the honest coins to the tape drawn as `g u` costs `Q` times that distance
(`abs_acceptProb_realEnv_law_sub_le`). `zeroKnowledge_presentations_of_keyFloorAt` states the bound
as `GordieHowe.ROM.ZeroKnowledge`. `presentations_advantage_le_of_keyFloor` and
`zeroKnowledge_presentations` are the constant cut-off under `KeyFloor` with `flatPresentSim`, the
identity sampler (`δ = 0`).
-/

namespace GordieHowe.MLDSA

open _root_.MLDSA _root_.MLDSA.Concrete Finset PMF GordieHowe.ROM.NIZK GordieHowe.QROM
open scoped ENNReal BigOperators

variable {p : Params} [NeZero (bucketCount p)] {Rnd Ctx : Type}

/-- **The salt of a point of `H_µ`**: its `R`; the points of `H` carry none. -/
def saltR : PresIn p Rnd Ctx → Option Rnd
  | .mu _ R _ => some R
  | .commit _ _ => none

/-- **The salt of a point of `H`**: its `µ`; the points of `H_µ` carry none. -/
def saltMu : PresIn p Rnd Ctx → Option (_root_.MLDSA.Bytes 64)
  | .mu .. => none
  | .commit mu _ => some mu

section Slice

variable {X Y Sd C : Type} [DecidableEq X] [DecidableEq Sd]

/-- Replacing a slice by a function updated at a point of the slice updates the result there. -/
theorem replaceSlice_update (saltOf : X → Option Sd) {σ : Sd} {x : X} (hx : saltOf x = some σ)
    (H F : X → Y) (y : Y) :
    replaceSlice saltOf σ H (Function.update F x y) =
      Function.update (replaceSlice saltOf σ H F) x y := by
  funext z
  by_cases hz : z = x
  · subst hz; simp [replaceSlice, hx]
  · simp [replaceSlice, Function.update_of_ne hz]

/-- **Splitting off the value at `x`** of a fresh slice whose coins carry a value. -/
def sliceSplit (x : X) : FreshSlice X Y (Y × C) ≃ FreshSlice X Y C × Y where
  toFun a := (⟨a.coins.2, Function.update a.slice x a.coins.1⟩, a.slice x)
  invFun b := ⟨(b.1.slice x, b.1.coins), Function.update b.1.slice x b.2⟩
  left_inv a := by
    ext
    · simp
    · simp
    · simp
  right_inv b := by
    ext
    · simp
    · simp
    · simp

end Slice

variable [Fintype Rnd] [Nonempty Rnd] [DecidableEq Rnd] [Fintype Ctx] [DecidableEq Ctx]
  (tr : _root_.MLDSA.Bytes 64) {D : ℕ} [NeZero D] (f : Fin D → LoopTape p)

/-- **The honest presenter with the tape drawn as `f u`** for a uniform `u : Fin D`, its coins
`(R, u)` drawn uniformly. -/
def honestPresenterAt :
    NARG.ProverFn (PresIn p Rnd Ctx) (PresOut p) Ctx Unit (Option (Presentation p))
      (SaltedCoins Rnd (Fin D)) where
  prove O ctx _ c := presentAt O (O (.mu tr c.salt ctx)).mu (f c.coins)

/-- **A fresh `µ`, programmed into `H_µ`**: with coins `(R, (y, u))` it publishes from the tape
`f u` at `µ = y.mu` and programs `H_µ(tr, R, ctx) := y`.

Running time: one read of the tape and the oracle at the points `(µ, ·)` it reads (`presentAt`),
and an assignment list of length one; the coins are those of `R`, one oracle value and `u`. This
running time is argued here, not proved in Lean. -/
def freshMuSim :
    NARG.SimulatorFn (PresIn p Rnd Ctx) (PresOut p) Ctx (Option (Presentation p))
      (SaltedCoins Rnd (PresOut p × Fin D)) where
  run O ctx c := ⟨presentAt O c.coins.1.mu (f c.coins.2), [⟨.mu tr c.salt ctx, c.coins.1⟩]⟩
  coins_nonempty := inferInstance

/-- **The presenter with a fresh `µ`** as its salt: it publishes from the tape `f u` at `µ`, its
coins drawn uniformly. -/
def freshMuPresenter :
    NARG.ProverFn (PresIn p Rnd Ctx) (PresOut p) Ctx Unit (Option (Presentation p))
      (SaltedCoins (_root_.MLDSA.Bytes 64) (Rnd × CommitHashBytes p × Fin D)) where
  prove O _ _ c := presentAt O c.salt (f c.coins.2.2)

/-! ### Step A: the message representative -/

omit [NeZero (bucketCount p)] [DecidableEq Rnd] [Fintype Ctx] [DecidableEq Ctx] in
/-- The honest presenter and `freshMuSim` are local in the salt `R`. -/
theorem saltedLocal_freshMuSim :
    SaltedLocal (saltR : PresIn p Rnd Ctx → Option Rnd) (honestPresenterAt tr f)
      (uniformOfFintype (SaltedCoins Rnd (Fin D))) (freshMuSim tr f) where
  prove_congr H H' x w c h := by
    have h1 : H (.mu tr c.salt x) = H' (.mu tr c.salt x) := h _ (Or.inr rfl)
    change presentAt H (H (.mu tr c.salt x)).mu (f c.coins) =
      presentAt H' (H' (.mu tr c.salt x)).mu (f c.coins)
    rw [h1]
    exact presentAt_congr (fun v => h _ (Or.inl rfl)) _
  run_congr H H' x s h := by
    change (⟨presentAt H _ _, _⟩ : NARG.SimOutput _ _ _) = ⟨presentAt H' _ _, _⟩
    rw [presentAt_congr (fun v => h _ (Or.inl rfl))]
  run_salt H x s a ha := by
    change a ∈ [_] at ha
    rw [List.mem_singleton] at ha
    subst ha
    rfl
  coins_eq := rfl

omit [NeZero (bucketCount p)] in
/-- **The two slice laws of step A are equal**: drawing `µ` fresh and programming
`H_µ(tr, R, ctx) := µ` on a fresh slice is the same as reading `µ` from the fresh slice. -/
theorem realSliceAt_eq_simSliceAt_freshMu (σ : Rnd) (H : PresIn p Rnd Ctx → PresOut p)
    (x : Ctx) (w : Unit) :
    realSliceAt saltR (honestPresenterAt tr f) σ H x w =
      simSliceAt saltR (freshMuSim tr f) σ H x := by
  classical
  rw [realSliceAt, simSliceAt, ← map_fst_uniformOfFintype (β := PresOut p),
    ← map_uniformOfFintype_equiv (sliceSplit (.mu tr σ x)), map_comp, map_comp]
  congr 1
  funext a
  have hx : saltR (.mu tr σ x : PresIn p Rnd Ctx) = some σ := rfl
  change (⟨some (presentAt (replaceSlice saltR σ H (Function.update a.slice (.mu tr σ x) a.coins.1))
      ((replaceSlice saltR σ H (Function.update a.slice (.mu tr σ x) a.coins.1)) (.mu tr σ x)).mu
      (f a.coins.2)), replaceSlice saltR σ H (Function.update a.slice (.mu tr σ x) a.coins.1)⟩ :
      Quantum.EnvReply _ _) =
    ⟨some (presentAt (replaceSlice saltR σ H a.slice) a.coins.1.mu (f a.coins.2)),
      Function.update (replaceSlice saltR σ H a.slice) (.mu tr σ x) a.coins.1⟩
  rw [replaceSlice_update saltR hx, Function.update_self,
    presentAt_congr (O' := replaceSlice saltR σ H a.slice) fun v =>
      Function.update_of_ne (by simp) _ _]

omit [NeZero (bucketCount p)] in
/-- The slice laws of step A are within `0`. -/
theorem sliceCloseAt_freshMuSim :
    SliceCloseAt (saltR : PresIn p Rnd Ctx → Option Rnd) (fun _ _ => True) (honestPresenterAt tr f)
      (freshMuSim tr f) fun _ => 0 where
  close σ H x w _ := by
    rw [realSliceAt_eq_simSliceAt_freshMu, tvDist_self]
  nonneg _ := le_rfl
  congr _ _ _ := rfl

omit [NeZero (bucketCount p)] in
/-- **Step A**: the honest presenter and `freshMuSim` are within
`Q t / |Rnd| + Q (Q - 1) / (2 |Rnd|)` (`zeroKnowledge_of_sliceCloseAt`, salt `R`). -/
theorem advantage_freshMuSim_le {m t Q : ℕ}
    (𝒜 : Adversary (PresIn p Rnd Ctx) (PresOut p) Ctx Unit (Option (Presentation p)) m t) :
    𝒜.advantage (fun _ _ => True) (honestPresenterAt tr f)
        (uniformOfFintype (SaltedCoins Rnd (Fin D))) (freshMuSim tr f) Q ≤
      Q * t / Fintype.card Rnd + Q * (Q - 1) / (2 * Fintype.card Rnd) := by
  have h := zeroKnowledge_of_sliceCloseAt (hloc := saltedLocal_freshMuSim tr f)
    (hcl := sliceCloseAt_freshMuSim tr f) m t Q 𝒜
  simpa using h

/-! ### Step C: the programming of the message representative -/

omit [NeZero (bucketCount p)] [Fintype Rnd] [DecidableEq Rnd] [Fintype Ctx] [DecidableEq Ctx] in
/-- `freshMuSim` programs at the hidden salt `R`. -/
theorem hiddenProgramming_freshMuSim :
    HiddenProgramming (saltR : PresIn p Rnd Ctx → Option Rnd) (freshMuSim tr f) where
  run_congr H H' x s h := by
    change (⟨presentAt H _ _, _⟩ : NARG.SimOutput _ _ _) = ⟨presentAt H' _ _, _⟩
    rw [presentAt_congr fun v => h _ rfl]
  proof_salt _ _ _ _ _ := rfl
  run_salt H x s a ha := by
    change a ∈ [_] at ha
    rw [List.mem_singleton] at ha
    subst ha
    rfl

/-- The coins of `freshMuSim` as those of `freshMuPresenter`: the fresh value's `µ` is the salt. -/
def freshMuCoinsEquiv :
    SaltedCoins Rnd (PresOut p × Fin D) ≃
      SaltedCoins (_root_.MLDSA.Bytes 64) (Rnd × CommitHashBytes p × Fin D) where
  toFun c := ⟨c.coins.1.mu, (c.salt, c.coins.1.cTilde, c.coins.2)⟩
  invFun c := ⟨c.coins.1, (⟨c.salt, c.coins.2.1⟩, c.coins.2.2)⟩
  left_inv _ := rfl
  right_inv _ := rfl

omit [NeZero (bucketCount p)] in
/-- **Without its programming, `freshMuSim` is the presenter with a fresh `µ`.** -/
theorem acceptProb_simEnv_dropAssignments_freshMuSim {m t Q : ℕ}
    (𝒜 : Adversary (PresIn p Rnd Ctx) (PresOut p) Ctx Unit (Option (Presentation p)) m t) :
    𝒜.acceptProb (simEnv (fun _ _ => True) (freshMuSim tr f).dropAssignments Q) =
      𝒜.acceptProb (realEnv (fun _ _ => True) (freshMuPresenter f)
        (uniformOfFintype (SaltedCoins (_root_.MLDSA.Bytes 64) (Rnd × CommitHashBytes p × Fin D)))
        Q) := by
  have h : ∀ r,
      (𝒜.alg r).acceptProb (simEnv (fun _ _ => True) (freshMuSim tr f).dropAssignments Q) =
        (𝒜.alg r).acceptProb (realEnv (fun _ _ => True) (freshMuPresenter f)
          (uniformOfFintype
            (SaltedCoins (_root_.MLDSA.Bytes 64) (Rnd × CommitHashBytes p × Fin D))) Q) :=
      fun r => by
    rw [IAlg.acceptProb_simEnv_dropAssignments]
    exact (IAlg.acceptProb_realEnv_eq_of_map _ _ _ _ _ _ freshMuCoinsEquiv (fun _ _ _ _ => rfl)
      (map_uniformOfFintype_equiv _).symm).symm
  simp only [Adversary.acceptProb, h]

/-! ### Step B: the commitment hash -/

section StepB

variable (σ : _root_.MLDSA.Bytes 64) (H : PresIn p Rnd Ctx → PresOut p)

/-- **`H` with its points `(σ, ·)` answered by `G`.** -/
def sliceOracle (G : BucketVec p → PresOut p) : PresIn p Rnd Ctx → PresOut p
  | .mu tr' R ctx => H (.mu tr' R ctx)
  | .commit mu v => if mu = σ then G v else H (.commit mu v)

omit [NeZero (bucketCount p)] [Fintype Rnd] [Nonempty Rnd] [DecidableEq Rnd] [Fintype Ctx]
  [DecidableEq Ctx] in
/-- The fresh slice of `σ` answers the points `(σ, ·)`. -/
theorem replaceSlice_saltMu (F : PresIn p Rnd Ctx → PresOut p) :
    replaceSlice saltMu σ H F = sliceOracle σ H fun v => F (.commit σ v) := by
  funext z
  cases z with
  | mu tr' R ctx => simp [replaceSlice, saltMu, sliceOracle]
  | commit mu v =>
    by_cases h : mu = σ
    · subst h; simp [replaceSlice, saltMu, sliceOracle]
    · simp [replaceSlice, saltMu, sliceOracle, h]

omit [NeZero (bucketCount p)] [Fintype Rnd] [Nonempty Rnd] [DecidableEq Rnd] [Fintype Ctx]
  [DecidableEq Ctx] in
theorem sliceOracle_commit (G : BucketVec p → PresOut p) (v : BucketVec p) :
    sliceOracle σ H G (.commit σ v) = G v := by
  simp [sliceOracle]

omit [NeZero (bucketCount p)] [Fintype Rnd] [Nonempty Rnd] [Fintype Ctx] in
/-- Updating the slice function at `w` updates the oracle at `(σ, w)`. -/
theorem sliceOracle_update (G : BucketVec p → PresOut p) (w : BucketVec p) (z : PresOut p) :
    sliceOracle σ H (Function.update G w z) =
      Function.update (sliceOracle σ H G) (.commit σ w) z := by
  funext y
  cases y with
  | mu tr' R ctx => simp [sliceOracle]
  | commit mu v =>
    by_cases h : mu = σ
    · subst h
      by_cases hv : v = w
      · subst hv; simp [sliceOracle]
      · simp [sliceOracle, hv]
    · simp [sliceOracle, h]

/-- **The reply from a slice function and a kept commitment**: publish `(σ, w₁, G(w₁))`, and the
oracle `H` with its points `(σ, ·)` answered by `G`. -/
def sliceReply (G : BucketVec p → PresOut p) (ow : Option (BucketVec p)) :
    Quantum.EnvReply (Option (Presentation p)) (PresIn p Rnd Ctx → PresOut p) :=
  ⟨some (ow.map fun w1 => ⟨σ, w1, (G w1).cTilde⟩), sliceOracle σ H G⟩

/-- The points `(σ, ·)` of the oracle. -/
def commitAt : BucketVec p ↪ PresIn p Rnd Ctx :=
  ⟨fun v => .commit σ v, fun _ _ h => by cases h; rfl⟩

omit [NeZero (bucketCount p)] [Nonempty Rnd] in
/-- **A fresh slice restricted to the points `(σ, ·)`**, with coins pushed to a uniform law, is
uniform. -/
theorem map_freshSlice_commitAt {C C' : Type} [Fintype C] [Nonempty C] [Fintype C']
    [Nonempty C'] [NeZero (bucketCount p)] {π : C → C'}
    (hπ : (uniformOfFintype C).map π = uniformOfFintype C') :
    (uniformOfFintype (FreshSlice (PresIn p Rnd Ctx) (PresOut p) C)).map
        (fun a => (fun v => a.slice (commitAt (Rnd := Rnd) (Ctx := Ctx) σ v), π a.coins)) =
      uniformOfFintype ((BucketVec p → PresOut p) × C') := by
  rw [← map_uniformOfFintype_equiv (FreshSlice.equivProd _ _ C).symm, map_comp,
    ← map_uniformOfFintype_equiv (Equiv.prodComm C' (BucketVec p → PresOut p)),
    ← map_prodMap_uniformOfFintype hπ
      (map_uniformOfFintype_comp_embedding (commitAt (Rnd := Rnd) (Ctx := Ctx) σ)),
    map_comp]
  rfl

omit [NeZero (bucketCount p)] in
/-- **The real slice law of step B**: a uniform slice function `G` on the points `(σ, ·)` and a
uniform `u`, published from the tape `f u` read at `G`'s commitment hashes. -/
theorem realSliceAt_freshMuPresenter [NeZero (bucketCount p)] (x : Ctx) (w : Unit) :
    realSliceAt (saltMu : PresIn p Rnd Ctx → Option (_root_.MLDSA.Bytes 64)) (freshMuPresenter f) σ
        H x w =
      (uniformOfFintype ((BucketVec p → PresOut p) × Fin D)).map fun q =>
        sliceReply σ H q.1 (f q.2 fun v => (q.1 v).cTilde) := by
  have hπ : (uniformOfFintype (Rnd × CommitHashBytes p × Fin D)).map (fun c => c.2.2) =
      uniformOfFintype (Fin D) := by
    rw [show (fun c : Rnd × CommitHashBytes p × Fin D => c.2.2) = Prod.snd ∘ Prod.snd from rfl,
      ← PMF.map_comp, map_snd_uniformOfFintype, map_snd_uniformOfFintype]
  rw [realSliceAt, ← map_freshSlice_commitAt (Rnd := Rnd) (Ctx := Ctx) σ hπ, PMF.map_comp]
  congr 1
  funext a
  change (⟨some (presentAt (replaceSlice saltMu σ H a.slice) σ (f a.coins.2.2)),
    replaceSlice saltMu σ H a.slice⟩ : Quantum.EnvReply _ _) = sliceReply σ H _ _
  rw [replaceSlice_saltMu, presentAt_eq]
  simp only [sliceOracle_commit]
  rfl

/-- **Programming one point of a slice function** with a fresh commitment hash: the updated
function and the point are uniform. -/
theorem map_update_uniformOfFintype :
    (uniformOfFintype ((BucketVec p → PresOut p) × (BucketVec p × CommitHashBytes p))).map
        (fun q => (Function.update q.1 q.2.1 ⟨(q.1 q.2.1).mu, q.2.2⟩, q.2.1)) =
      uniformOfFintype ((BucketVec p → PresOut p) × BucketVec p) := by
  let e : (BucketVec p → PresOut p) × (BucketVec p × CommitHashBytes p) ≃
      ((BucketVec p → PresOut p) × BucketVec p) × CommitHashBytes p :=
    { toFun := fun q => ((Function.update q.1 q.2.1 ⟨(q.1 q.2.1).mu, q.2.2⟩, q.2.1),
        (q.1 q.2.1).cTilde)
      invFun := fun r => (Function.update r.1.1 r.1.2 ⟨(r.1.1 r.1.2).mu, r.2⟩,
        (r.1.2, (r.1.1 r.1.2).cTilde))
      left_inv := fun q => by
        rcases q with ⟨G, w, c⟩
        simp only [Function.update_self, Function.update_idem]
        ext v
        · by_cases hv : v = w
          · subst hv; simp
          · simp [Function.update_of_ne hv]
        · rfl
        · simp
      right_inv := fun r => by
        rcases r with ⟨⟨G, w⟩, c⟩
        simp only [Function.update_self, Function.update_idem]
        ext v
        · by_cases hv : v = w
          · subst hv; simp
          · simp [Function.update_of_ne hv]
        · rfl
        · rfl }
  rw [show (fun q : (BucketVec p → PresOut p) × (BucketVec p × CommitHashBytes p) =>
      (Function.update q.1 q.2.1 ⟨(q.1 q.2.1).mu, q.2.2⟩, q.2.1)) = Prod.fst ∘ e from rfl,
    ← PMF.map_comp, map_uniformOfFintype_equiv, map_fst_uniformOfFintype]

omit [NeZero (bucketCount p)] [Nonempty Rnd] in
/-- **The simulated slice law of step B**: a uniform slice function and a uniform commitment
`w₁`. -/
theorem simSliceAt_flatPresentSim [NeZero (bucketCount p)] (x : Ctx) :
    simSliceAt (saltMu : PresIn p Rnd Ctx → Option (_root_.MLDSA.Bytes 64)) flatPresentSim σ H x =
      (uniformOfFintype ((BucketVec p → PresOut p) × BucketVec p)).map fun q =>
        sliceReply σ H q.1 (some q.2) := by
  rw [simSliceAt, ← map_update_uniformOfFintype,
    ← map_freshSlice_commitAt (Rnd := Rnd) (Ctx := Ctx) σ (π := id) (PMF.map_id _), PMF.map_comp,
    PMF.map_comp]
  congr 1
  funext a
  rw [flatPresentSim_run]
  change (⟨some (some ⟨σ, a.coins.1, a.coins.2⟩), Function.update (replaceSlice saltMu σ H a.slice)
    (.commit σ a.coins.1) ⟨(replaceSlice saltMu σ H a.slice (.commit σ a.coins.1)).mu, a.coins.2⟩⟩ :
      Quantum.EnvReply _ _) = sliceReply σ H _ _
  rw [replaceSlice_saltMu, sliceOracle_commit, ← sliceOracle_update]
  simp only [sliceReply, Function.update_self, Option.map_some]
  rfl

/-! #### The law of a slice function with a kept commitment -/

/-- **A uniform slice function with a kept commitment drawn from `K` at its commitment hashes.** -/
noncomputable def sliceLaw (K : (BucketVec p → CommitHashBytes p) → PMF (Option (BucketVec p))) :
    PMF ((BucketVec p → PresOut p) × Option (BucketVec p)) :=
  (uniformOfFintype (BucketVec p → PresOut p)).bind fun G =>
    (K fun v => (G v).cTilde).map (G, ·)

/-- **Uniform commitment hashes with a kept commitment drawn from `K`.** -/
noncomputable def hashLaw (K : (BucketVec p → CommitHashBytes p) → PMF (Option (BucketVec p))) :
    PMF ((BucketVec p → CommitHashBytes p) × Option (BucketVec p)) :=
  (uniformOfFintype (BucketVec p → CommitHashBytes p)).bind fun h => (K h).map (h, ·)

/-- Slice functions as their commitment hashes and their message representatives. -/
def sliceFunEquiv :
    (BucketVec p → PresOut p) ≃
      (BucketVec p → CommitHashBytes p) × (BucketVec p → _root_.MLDSA.Bytes 64) where
  toFun G := (fun v => (G v).cTilde, fun v => (G v).mu)
  invFun q v := ⟨q.2 v, q.1 v⟩
  left_inv _ := rfl
  right_inv _ := rfl

omit [NeZero (bucketCount p)] in
/-- **The slice law is the hash law with uniform message representatives added.** -/
theorem sliceLaw_eq_bind (K : (BucketVec p → CommitHashBytes p) → PMF (Option (BucketVec p))) :
    sliceLaw K = (hashLaw K).bind fun q =>
      (uniformOfFintype (BucketVec p → _root_.MLDSA.Bytes 64)).map fun gm =>
        (sliceFunEquiv.symm (q.1, gm), q.2) := by
  rw [sliceLaw, hashLaw, ← map_uniformOfFintype_equiv sliceFunEquiv.symm, PMF.bind_map,
    uniformOfFintype_prod_eq_bind, PMF.bind_bind, PMF.bind_bind]
  congr 1
  funext h
  rw [PMF.bind_map, PMF.bind_map]
  exact PMF.bind_comm (uniformOfFintype _) (K h) fun gm o =>
    PMF.pure (sliceFunEquiv.symm (h, gm), o)

/-- **Adding independent uniform message representatives** to commitment hashes with a kept
commitment: the slice function with those commitment hashes and uniform message representatives. -/
noncomputable def sliceLift
    (μ : PMF ((BucketVec p → CommitHashBytes p) × Option (BucketVec p))) :
    PMF ((BucketVec p → PresOut p) × Option (BucketVec p)) :=
  μ.bind fun q => (uniformOfFintype (BucketVec p → _root_.MLDSA.Bytes 64)).map fun gm =>
    (sliceFunEquiv.symm (q.1, gm), q.2)

omit [NeZero (bucketCount p)] in
/-- **The slice law is the lift of the hash law** (`sliceLaw_eq_bind`). -/
theorem sliceLaw_eq_sliceLift
    (K : (BucketVec p → CommitHashBytes p) → PMF (Option (BucketVec p))) :
    sliceLaw K = sliceLift (hashLaw K) :=
  sliceLaw_eq_bind K

omit [NeZero (bucketCount p)] in
/-- **Adding independent uniform message representatives** does not increase the distance. -/
theorem tvDist_sliceLift_le
    (μ₁ μ₂ : PMF ((BucketVec p → CommitHashBytes p) × Option (BucketVec p))) :
    tvDist (sliceLift μ₁) (sliceLift μ₂) ≤ tvDist μ₁ μ₂ :=
  tvDist_bind_right_le _ _ _

omit [NeZero (bucketCount p)] in
/-- **Adding independent uniform message representatives** to two hash laws does not increase
their distance. -/
theorem tvDist_sliceLaw_le
    (K₁ K₂ : (BucketVec p → CommitHashBytes p) → PMF (Option (BucketVec p))) :
    tvDist (sliceLaw K₁) (sliceLaw K₂) ≤ tvDist (hashLaw K₁) (hashLaw K₂) := by
  rw [sliceLaw_eq_sliceLift, sliceLaw_eq_sliceLift]
  exact tvDist_sliceLift_le _ _

omit [NeZero (bucketCount p)] in
/-- **The lift of the reprogramming kernel**: a uniform slice function with its commitment hash at
`w₁` set to `c̃`, and `w₁`. -/
theorem sliceLift_oracleKernel (vc : BucketVec p × CommitHashBytes p) :
    sliceLift (oracleKernel vc) =
      (uniformOfFintype (BucketVec p → PresOut p)).map fun G =>
        (Function.update G vc.1 ⟨(G vc.1).mu, vc.2⟩, some vc.1) := by
  rw [sliceLift, oracleKernel, PMF.bind_map, ← map_uniformOfFintype_equiv sliceFunEquiv.symm,
    PMF.map_comp]
  refine (uniformOfFintype_bind_map_eq (α := BucketVec p → CommitHashBytes p)
    (β := BucketVec p → _root_.MLDSA.Bytes 64)
    fun H gm => (sliceFunEquiv.symm (Function.update H vc.1 vc.2, gm), some vc.1)).trans ?_
  congr 1
  funext q
  refine Prod.ext ?_ rfl
  funext w
  by_cases hw : w = vc.1
  · subst hw
    simp [sliceFunEquiv]
  · simp [sliceFunEquiv, Function.update_of_ne hw]

omit [NeZero (bucketCount p)] in
/-- **A tape drawn as `f u`** against the tape's law: at most their distance. -/
theorem tvDist_hashLaw_tape_le (ν : PMF (LoopTape p)) :
    tvDist (hashLaw fun h => (uniformOfFintype (Fin D)).map fun u => f u h)
        (hashLaw fun h => ν.map fun τ => τ h) ≤
      tvDist ((uniformOfFintype (Fin D)).map f) ν := by
  rw [hashLaw, hashLaw]
  refine (tvDist_uniformOfFintype_bind_le _ _).trans ?_
  refine (Finset.expect_le_expect fun h _ => ?_).trans_eq (Fintype.expect_const _)
  rw [PMF.map_comp, PMF.map_comp, show ((fun x => (h, x)) ∘ fun u => f u h) =
    (fun τ : LoopTape p => (h, τ h)) ∘ f from rfl, ← PMF.map_comp]
  exact tvDist_map_le _ _ _

/-! #### The loop against the commitment hashes, and the target -/

omit [NeZero (bucketCount p)] in
/-- **Updating a uniform function at a point with a uniform value** gives a uniform function. -/
theorem map_update_pair_uniformOfFintype (v : BucketVec p) :
    (uniformOfFintype ((BucketVec p → CommitHashBytes p) × CommitHashBytes p)).map
        (fun q => Function.update q.1 v q.2) =
      uniformOfFintype (BucketVec p → CommitHashBytes p) := by
  let e : (BucketVec p → CommitHashBytes p) × CommitHashBytes p ≃
      (BucketVec p → CommitHashBytes p) × CommitHashBytes p :=
    { toFun := fun q => (Function.update q.1 v q.2, q.1 v)
      invFun := fun r => (Function.update r.1 v r.2, r.1 v)
      left_inv := fun q => by
        rcases q with ⟨H, c⟩
        simp only [Function.update_self, Function.update_idem, Function.update_eq_self]
      right_inv := fun r => by
        rcases r with ⟨H, c⟩
        simp only [Function.update_self, Function.update_idem, Function.update_eq_self] }
  rw [show (fun q : (BucketVec p → CommitHashBytes p) × CommitHashBytes p =>
      Function.update q.1 v q.2) = Prod.fst ∘ e from rfl, ← PMF.map_comp,
    map_uniformOfFintype_equiv, map_fst_uniformOfFintype]

variable (prims : Primitives p) [nttOps : NTTRingOps] [Nonempty (MaskBox p)] (sk : SecretKey p)
  (aHat : TqMatrix p.k p.l) (cut : Cutoff p)

omit [Fintype Rnd] [Nonempty Rnd] [DecidableEq Rnd] [Fintype Ctx] [DecidableEq Ctx] in
/-- **The hash law of the flattened signer's loop** is the prover against a random function. -/
theorem hashLaw_flatSliceLoop :
    hashLaw (flatSliceLoop prims sk aHat cut) =
      oracleProver (maskUniform p) (realBuckets aHat) (attemptAccept prims sk aHat)
        (fun a => (flattenCoin prims sk cut a : ℝ≥0∞)) (coe_flattenCoin_le_one prims sk cut) := by
  rw [hashLaw, oracleProver, loopForever]
  rfl

omit nttOps [Nonempty (MaskBox p)] in
/-- **Reprogramming a uniform function at a uniform point with a uniform value**: the function and
the point are uniform and independent. -/
theorem map_update_uniformOfFintype_triple :
    (uniformOfFintype ((BucketVec p × CommitHashBytes p) × (BucketVec p → CommitHashBytes p))).map
        (fun q => (Function.update q.2 q.1.1 q.1.2, q.1.1)) =
      uniformOfFintype ((BucketVec p → CommitHashBytes p) × BucketVec p) := by
  let e : (BucketVec p × CommitHashBytes p) × (BucketVec p → CommitHashBytes p) ≃
      ((BucketVec p → CommitHashBytes p) × BucketVec p) × CommitHashBytes p :=
    { toFun := fun q => ((Function.update q.2 q.1.1 q.1.2, q.1.1), q.2 q.1.1)
      invFun := fun r => ((r.1.2, r.1.1 r.1.2), Function.update r.1.1 r.1.2 r.2)
      left_inv := fun q => by
        rcases q with ⟨⟨v, c⟩, H⟩
        simp only [Function.update_self, Function.update_idem, Function.update_eq_self]
      right_inv := fun r => by
        rcases r with ⟨⟨H, v⟩, c⟩
        simp only [Function.update_self, Function.update_idem, Function.update_eq_self] }
  rw [show (fun q : (BucketVec p × CommitHashBytes p) × (BucketVec p → CommitHashBytes p) =>
      (Function.update q.2 q.1.1 q.1.2, q.1.1)) = Prod.fst ∘ e from rfl, ← PMF.map_comp,
    map_uniformOfFintype_equiv, map_fst_uniformOfFintype]

omit [Fintype Rnd] [Nonempty Rnd] [DecidableEq Rnd] [Fintype Ctx] [DecidableEq Ctx] nttOps
  [Nonempty (MaskBox p)] in
/-- **The hash law of a uniform commitment** is the uniform target followed by the reprogramming
kernel. -/
theorem hashLaw_uniform :
    hashLaw (fun _ => (uniformOfFintype (BucketVec p)).map some) =
      (flatTarget p).bind oracleKernel := by
  have hL : hashLaw (fun _ => (uniformOfFintype (BucketVec p)).map some) =
      (uniformOfFintype ((BucketVec p → CommitHashBytes p) × BucketVec p)).map
        fun q => (q.1, some q.2) := by
    calc hashLaw (fun _ => (uniformOfFintype (BucketVec p)).map some)
        = (uniformOfFintype (BucketVec p → CommitHashBytes p)).bind
            (fun h => (uniformOfFintype (BucketVec p)).map fun v => (h, some v)) := by
          rw [hashLaw]
          congr 1
          funext h
          rw [PMF.map_comp]
          rfl
      _ = _ := uniformOfFintype_bind_map_eq fun h v => (h, some v)
  have hR : (flatTarget p).bind oracleKernel =
      (uniformOfFintype ((BucketVec p → CommitHashBytes p) × BucketVec p)).map
        fun q => (q.1, some q.2) := by
    calc (flatTarget p).bind oracleKernel
        = (uniformOfFintype (BucketVec p × CommitHashBytes p)).bind
            (fun vc => (uniformOfFintype (BucketVec p → CommitHashBytes p)).map
              fun H => (Function.update H vc.1 vc.2, some vc.1)) := by
          rw [flatTarget_eq_uniformOfFintype]
          rfl
      _ = (uniformOfFintype ((BucketVec p × CommitHashBytes p) ×
            (BucketVec p → CommitHashBytes p))).map
              (fun q => (Function.update q.2 q.1.1 q.1.2, some q.1.1)) :=
          uniformOfFintype_bind_map_eq (α := BucketVec p × CommitHashBytes p)
            (β := BucketVec p → CommitHashBytes p)
            fun vc H => (Function.update H vc.1 vc.2, some vc.1)
      _ = ((uniformOfFintype ((BucketVec p × CommitHashBytes p) ×
            (BucketVec p → CommitHashBytes p))).map
              (fun q => (Function.update q.2 q.1.1 q.1.2, q.1.1))).map
            (fun q => (q.1, some q.2)) := by
          rw [PMF.map_comp]
          rfl
      _ = _ := by rw [map_update_uniformOfFintype_triple]
  rw [hL, hR]

/-- **One presentation's law against its target at a cut-off**: under the floor at the cut-off,
the loop against a uniform commitment-hash function is within the oracle concentration term, `ε`
and `signerRegGap / (1 - ε)` of the shaped target followed by the reprogramming kernel
(`tvDist_oracleProver_le`, `tvDist_flatSigner_shapedTarget_le_of_keyFloorAt`). If the signer never
keeps, `signerRegGap / (1 - ε) ≥ 1` (`one_sub_le_signerRegGap_of_keyFloorAt`). -/
theorem tvDist_hashLaw_flatSliceLoop_le_of_keyFloorAt (hp : SigningParams p)
    (h_laws : SigningLaws prims) (hs2 : polyVecBounded sk.s2 p.eta) {ε : ℝ}
    (hf : KeyFloorAt prims cut ε sk.t0) :
    tvDist (hashLaw (flatSliceLoop prims sk aHat cut)) ((shapedTarget cut).bind oracleKernel) ≤
      flatOracleConcError prims sk aHat cut + (ε + signerRegGap prims sk aHat cut / (1 - ε)) := by
  by_cases hkeep : SignerKeeps prims sk aHat cut
  · rw [hashLaw_flatSliceLoop]
    have hkeep' := hkeep
    rw [SignerKeeps] at hkeep'
    refine (tvDist_oracleProver_le _ _ _ _ _ (shapedTarget cut) hkeep').trans
      (add_le_add le_rfl ?_)
    have hlaw : condSome _ hkeep' = realKeptLaw prims sk aHat cut := by
      rw [realKeptLaw, condSomeOr_of_ne _ hkeep']
    rw [hlaw]
    exact tvDist_flatSigner_shapedTarget_le_of_keyFloorAt prims sk aHat hp h_laws hs2 hf
  · have hg := one_sub_le_signerRegGap_of_keyFloorAt prims sk aHat hp h_laws hs2 hf hkeep
    have h1 : 0 < 1 - ε := by linarith [hf.lt_one]
    have h2 : 1 ≤ signerRegGap prims sk aHat cut / (1 - ε) := by
      rw [le_div_iff₀ h1]; linarith
    linarith [tvDist_le_one (hashLaw (flatSliceLoop prims sk aHat cut))
      ((shapedTarget cut).bind oracleKernel), flatOracleConcError_nonneg prims sk aHat cut,
      hf.nonneg]

/-- **One presentation's law against its target**: under the floor, the loop against a uniform
commitment-hash function is within the oracle concentration term, `ε` and
`signerRegGap / (1 - ε)` of a uniform function and a uniform commitment
(`tvDist_hashLaw_flatSliceLoop_le_of_keyFloorAt` at the constant cut-off, `hashLaw_uniform`). -/
theorem tvDist_hashLaw_flatSliceLoop_le (βmin : ℚ≥0) (hp : SigningParams p)
    (h_laws : SigningLaws prims) (hs2 : polyVecBounded sk.s2 p.eta) {ε : ℝ}
    (hf : KeyFloor prims βmin ε sk.t0) :
    tvDist (hashLaw (flatSliceLoop prims sk aHat (Cutoff.const βmin)))
        (hashLaw fun _ => (uniformOfFintype (BucketVec p)).map some) ≤
      flatOracleConcError prims sk aHat (Cutoff.const βmin) + (ε + signerRegGap prims sk aHat
          (Cutoff.const βmin) / (1 - ε)) := by
  rw [hashLaw_uniform, ← shapedTarget_const βmin]
  exact tvDist_hashLaw_flatSliceLoop_le_of_keyFloorAt prims sk aHat (Cutoff.const βmin) hp h_laws
    hs2 (keyFloorAt_const_iff.2 hf)

omit [Fintype Rnd] [Nonempty Rnd] [DecidableEq Rnd] [Fintype Ctx] [DecidableEq Ctx]
  [NeZero (bucketCount p)] nttOps [Nonempty (MaskBox p)] in
/-- The slice law of the tape drawn as `f u`, read at the slice function's commitment hashes. -/
theorem map_uniformOfFintype_tape_eq_sliceLaw :
    (uniformOfFintype ((BucketVec p → PresOut p) × Fin D)).map
        (fun q => (q.1, f q.2 fun v => (q.1 v).cTilde)) =
      sliceLaw fun h => (uniformOfFintype (Fin D)).map fun u => f u h := by
  rw [sliceLaw]
  refine (uniformOfFintype_bind_map_eq (α := BucketVec p → PresOut p) (β := Fin D)
    fun G u => (G, f u fun v => (G v).cTilde)).symm.trans ?_
  congr 1
  funext G
  rw [PMF.map_comp]
  rfl

omit [Fintype Rnd] [Nonempty Rnd] [DecidableEq Rnd] [Fintype Ctx] [DecidableEq Ctx] nttOps
  [Nonempty (MaskBox p)] in
/-- The slice law of a uniform commitment. -/
theorem map_uniformOfFintype_eq_sliceLaw :
    (uniformOfFintype ((BucketVec p → PresOut p) × BucketVec p)).map (fun q => (q.1, some q.2)) =
      sliceLaw fun _ => (uniformOfFintype (BucketVec p)).map some := by
  rw [sliceLaw]
  refine (uniformOfFintype_bind_map_eq (α := BucketVec p → PresOut p) (β := BucketVec p)
    fun G v => (G, some v)).symm.trans ?_
  congr 1
  funext G
  rw [PMF.map_comp]
  rfl

omit [Fintype Rnd] [Nonempty Rnd] [DecidableEq Rnd] [Fintype Ctx] [DecidableEq Ctx] in
/-- **The hash law of the loop** is that of its tape (`pi_map_eval`). -/
theorem hashLaw_flatSliceLoop_eq_tape :
    hashLaw (flatSliceLoop prims sk aHat cut) =
      hashLaw fun h => (loopTapeLaw prims sk aHat cut).map fun τ => τ h := by
  classical
  rw [hashLaw, hashLaw]
  congr 1
  funext h
  rw [loopTapeLaw, PMF.pi_map_eval]

/-- **The one-presentation error of step B**: the oracle concentration term, the floor `ε`, the
regularity term `signerRegGap / (1 - ε)`, and the distance of the tape drawn as `f u` from the
tape's law. -/
noncomputable def stepBError (ε : ℝ) : ℝ :=
  flatOracleConcError prims sk aHat cut + (ε + signerRegGap prims sk aHat cut / (1 - ε)) +
    tvDist ((uniformOfFintype (Fin D)).map f) (loopTapeLaw prims sk aHat cut)

omit [NeZero (bucketCount p)] [Nonempty Rnd] nttOps [Nonempty (MaskBox p)] in
/-- **The simulated slice law of step B with a sampler**: a uniform slice function and uniform
sampler coins `u`, with the slice function's commitment hash at `w₁` set to `c̃` for
`(w₁, c̃) = samp u`. -/
theorem simSliceAt_flatPresentSimOf [NeZero (bucketCount p)] {C : Type} [Fintype C] [Nonempty C]
    (samp : C → BucketVec p × CommitHashBytes p) (x : Ctx) :
    simSliceAt (saltMu : PresIn p Rnd Ctx → Option (_root_.MLDSA.Bytes 64)) (flatPresentSimOf samp)
        σ H x =
      (uniformOfFintype ((BucketVec p → PresOut p) × C)).map fun q =>
        sliceReply σ H (Function.update q.1 (samp q.2).1 ⟨(q.1 (samp q.2).1).mu, (samp q.2).2⟩)
          (some (samp q.2).1) := by
  rw [simSliceAt, ← map_freshSlice_commitAt (Rnd := Rnd) (Ctx := Ctx) σ (π := id) (PMF.map_id _),
    PMF.map_comp]
  congr 1
  funext a
  rw [flatPresentSimOf_run]
  change (⟨some (some ⟨σ, (samp a.coins).1, (samp a.coins).2⟩),
    Function.update (replaceSlice saltMu σ H a.slice) (.commit σ (samp a.coins).1)
      ⟨(replaceSlice saltMu σ H a.slice (.commit σ (samp a.coins).1)).mu, (samp a.coins).2⟩⟩ :
      Quantum.EnvReply _ _) = sliceReply σ H _ _
  rw [replaceSlice_saltMu, sliceOracle_commit, ← sliceOracle_update]
  simp only [sliceReply, Function.update_self, Option.map_some]
  rfl

omit [NeZero (bucketCount p)] [Nonempty Rnd] nttOps [Nonempty (MaskBox p)] in
/-- **The simulated slice law of step B is the lift of the sampled target followed by the
reprogramming kernel** (`sliceLift_oracleKernel`). -/
theorem simSliceAt_flatPresentSimOf_eq_sliceLift [NeZero (bucketCount p)] {C : Type} [Fintype C]
    [Nonempty C] (samp : C → BucketVec p × CommitHashBytes p) (x : Ctx) :
    simSliceAt (saltMu : PresIn p Rnd Ctx → Option (_root_.MLDSA.Bytes 64)) (flatPresentSimOf samp)
        σ H x =
      (sliceLift (((uniformOfFintype C).map samp).bind oracleKernel)).map fun q =>
        sliceReply σ H q.1 q.2 := by
  rw [simSliceAt_flatPresentSimOf, sliceLift, PMF.bind_bind, PMF.bind_map,
    ← map_uniformOfFintype_equiv (Equiv.prodComm C (BucketVec p → PresOut p)), PMF.map_comp]
  have hl : ∀ c : C, ((oracleKernel (samp c)).bind fun q =>
      (uniformOfFintype (BucketVec p → _root_.MLDSA.Bytes 64)).map fun gm =>
        (sliceFunEquiv.symm (q.1, gm), q.2)) =
      (uniformOfFintype (BucketVec p → PresOut p)).map fun G =>
        (Function.update G (samp c).1 ⟨(G (samp c).1).mu, (samp c).2⟩, some (samp c).1) :=
    fun c => sliceLift_oracleKernel (samp c)
  simp only [Function.comp_def, hl]
  rw [uniformOfFintype_bind_map_eq, PMF.map_comp]
  rfl

omit [NeZero (bucketCount p)] nttOps [Nonempty (MaskBox p)] in
/-- The slice law of the tape drawn as `f u` is the lift of its hash law. -/
theorem map_tape_eq_sliceLift :
    (uniformOfFintype ((BucketVec p → PresOut p) × Fin D)).map
        (fun q => (q.1, f q.2 fun v => (q.1 v).cTilde)) =
      sliceLift (hashLaw fun h => (uniformOfFintype (Fin D)).map fun u => f u h) := by
  rw [map_uniformOfFintype_tape_eq_sliceLaw, sliceLaw_eq_sliceLift]

/-- **The slice laws of step B with a sampler are within `stepBError + δ`** at every `µ`, oracle
and context, for a sampler within `δ` of the shaped target. -/
theorem sliceCloseAt_flatPresentSimOf (hp : SigningParams p) (h_laws : SigningLaws prims)
    (hs2 : polyVecBounded sk.s2 p.eta) {ε : ℝ} (hf : KeyFloorAt prims cut ε sk.t0) {C : Type}
    [Fintype C] [Nonempty C] (samp : C → BucketVec p × CommitHashBytes p) {δ : ℝ}
    (hδ : tvDist ((uniformOfFintype C).map samp) (shapedTarget cut) ≤ δ) :
    SliceCloseAt (saltMu : PresIn p Rnd Ctx → Option (_root_.MLDSA.Bytes 64)) (fun _ _ => True)
      (freshMuPresenter f) (flatPresentSimOf samp)
        fun _ => stepBError f prims sk aHat cut ε + δ where
  close σ H x w _ := by
    rw [realSliceAt_freshMuPresenter, simSliceAt_flatPresentSimOf_eq_sliceLift,
      show (fun q : (BucketVec p → PresOut p) × Fin D =>
          sliceReply σ H q.1 (f q.2 fun v => (q.1 v).cTilde)) =
        (fun q => sliceReply σ H q.1 q.2) ∘ fun q => (q.1, f q.2 fun v => (q.1 v).cTilde) from rfl,
      ← PMF.map_comp, map_tape_eq_sliceLift]
    refine (tvDist_map_le _ _ _).trans ((tvDist_sliceLift_le _ _).trans ?_)
    have h1 := tvDist_triangle (hashLaw fun h => (uniformOfFintype (Fin D)).map fun u => f u h)
      (hashLaw (flatSliceLoop prims sk aHat cut))
      (((uniformOfFintype C).map samp).bind oracleKernel)
    have h2 := tvDist_triangle (hashLaw (flatSliceLoop prims sk aHat cut))
      ((shapedTarget cut).bind oracleKernel) (((uniformOfFintype C).map samp).bind oracleKernel)
    have h3 := tvDist_hashLaw_flatSliceLoop_le_of_keyFloorAt prims sk aHat cut hp h_laws hs2 hf
    have h4 := (tvDist_bind_right_le (shapedTarget cut) ((uniformOfFintype C).map samp)
      oracleKernel).trans ((tvDist_comm _ _).trans_le hδ)
    have h5 := tvDist_hashLaw_tape_le f (loopTapeLaw prims sk aHat cut)
    rw [← hashLaw_flatSliceLoop_eq_tape] at h5
    rw [stepBError]
    linarith
  nonneg _ := by
    have h1 : 0 ≤ 1 - ε := sub_nonneg.2 hf.lt_one.le
    have := oracleConc_nonneg (maskUniform p) (realBuckets aHat) (attemptAccept prims sk aHat)
      (fun a => (flattenCoin prims sk cut a : ℝ≥0∞)) (coe_flattenCoin_le_one prims sk cut)
    exact add_nonneg (add_nonneg (add_nonneg this (add_nonneg hf.nonneg
      (div_nonneg (signerRegGap_nonneg prims sk aHat cut) h1))) (tvDist_nonneg _ _))
      ((tvDist_nonneg _ _).trans hδ)
  congr _ _ _ := rfl

omit nttOps [Nonempty (MaskBox p)] in
/-- The identity sampler is the shaped target at a constant cut-off. -/
theorem tvDist_map_id_shapedTarget_const (β : ℚ≥0) :
    tvDist ((uniformOfFintype (BucketVec p × CommitHashBytes p)).map id)
      (shapedTarget (Cutoff.const β)) ≤ 0 := by
  rw [PMF.map_id, shapedTarget_const, flatTarget_eq_uniformOfFintype, tvDist_self]

/-- **The slice laws of step B are within `stepBError`** at every `µ`, oracle and context
(`sliceCloseAt_flatPresentSimOf` with the identity sampler). -/
theorem sliceCloseAt_flatPresentSim (βmin : ℚ≥0) (hp : SigningParams p)
    (h_laws : SigningLaws prims) (hs2 : polyVecBounded sk.s2 p.eta) {ε : ℝ}
    (hf : KeyFloor prims βmin ε sk.t0) :
    SliceCloseAt (saltMu : PresIn p Rnd Ctx → Option (_root_.MLDSA.Bytes 64)) (fun _ _ => True)
      (freshMuPresenter f) flatPresentSim
        fun _ => stepBError f prims sk aHat (Cutoff.const βmin) ε := by
  have h := sliceCloseAt_flatPresentSimOf (Rnd := Rnd) (Ctx := Ctx) f prims sk aHat
    (Cutoff.const βmin) hp h_laws hs2 (keyFloorAt_const_iff.2 hf) id
    (tvDist_map_id_shapedTarget_const βmin)
  rw [flatPresentSim_eq_flatPresentSimOf]
  simpa only [add_zero] using h

omit [NeZero (bucketCount p)] [DecidableEq Rnd] [Fintype Ctx] [DecidableEq Ctx] nttOps
  [Nonempty (MaskBox p)] in
/-- The presenter with a fresh `µ` and `flatPresentSimOf samp` are local in the salt `µ`. -/
theorem saltedLocal_flatPresentSimOf {C : Type} [Fintype C] [Nonempty C]
    (samp : C → BucketVec p × CommitHashBytes p) :
    SaltedLocal (saltMu : PresIn p Rnd Ctx → Option (_root_.MLDSA.Bytes 64)) (freshMuPresenter f)
      (uniformOfFintype (SaltedCoins (_root_.MLDSA.Bytes 64) (Rnd × CommitHashBytes p × Fin D)))
      (flatPresentSimOf samp) where
  prove_congr H H' x w c h := by
    change presentAt H c.salt (f c.coins.2.2) = presentAt H' c.salt (f c.coins.2.2)
    exact presentAt_congr (fun v => h _ (Or.inr rfl)) _
  run_congr H H' x s h := by
    rw [flatPresentSimOf_run, flatPresentSimOf_run, h _ (Or.inr rfl)]
  run_salt H x s a ha := by
    rw [flatPresentSimOf_run] at ha
    change a ∈ [_] at ha
    rw [List.mem_singleton] at ha
    subst ha
    rfl
  coins_eq := rfl

omit [DecidableEq Rnd] [Fintype Ctx] [DecidableEq Ctx] nttOps [Nonempty (MaskBox p)] in
/-- The presenter with a fresh `µ` and `flatPresentSim` are local in the salt `µ`. -/
theorem saltedLocal_flatPresentSim :
    SaltedLocal (saltMu : PresIn p Rnd Ctx → Option (_root_.MLDSA.Bytes 64)) (freshMuPresenter f)
      (uniformOfFintype (SaltedCoins (_root_.MLDSA.Bytes 64) (Rnd × CommitHashBytes p × Fin D)))
      flatPresentSim := by
  rw [flatPresentSim_eq_flatPresentSimOf]
  exact saltedLocal_flatPresentSimOf f id

/-- **Step B with a sampler**: the presenter with a fresh `µ` and `flatPresentSimOf samp` are
within `Q t / 2^512 + Q (Q - 1) / 2^513 + Q · (stepBError + δ)` (`zeroKnowledge_of_sliceCloseAt`,
salt `µ`). -/
theorem advantage_freshMuPresenter_le_of_keyFloorAt (hp : SigningParams p)
    (h_laws : SigningLaws prims) (hs2 : polyVecBounded sk.s2 p.eta) {ε : ℝ}
    (hf : KeyFloorAt prims cut ε sk.t0) {C : Type} [Fintype C] [Nonempty C]
    (samp : C → BucketVec p × CommitHashBytes p) {δ : ℝ}
    (hδ : tvDist ((uniformOfFintype C).map samp) (shapedTarget cut) ≤ δ) {m t Q : ℕ}
    (𝒜 : Adversary (PresIn p Rnd Ctx) (PresOut p) Ctx Unit (Option (Presentation p)) m t) :
    𝒜.advantage (fun _ _ => True) (freshMuPresenter f)
        (uniformOfFintype (SaltedCoins (_root_.MLDSA.Bytes 64) (Rnd × CommitHashBytes p × Fin D)))
        (flatPresentSimOf samp) Q ≤
      Q * t / Fintype.card (_root_.MLDSA.Bytes 64) +
        Q * (Q - 1) / (2 * Fintype.card (_root_.MLDSA.Bytes 64)) +
        Q * (stepBError f prims sk aHat cut ε + δ) := by
  have h := zeroKnowledge_of_sliceCloseAt (hloc := saltedLocal_flatPresentSimOf f samp)
    (hcl := sliceCloseAt_flatPresentSimOf f prims sk aHat cut hp h_laws hs2 hf samp hδ) m t Q 𝒜
  exact h.trans_eq (by rw [Fintype.expect_const])

/-- **Step B**: the presenter with a fresh `µ` and `flatPresentSim` are within
`Q t / 2^512 + Q (Q - 1) / 2^513 + Q · stepBError` (`advantage_freshMuPresenter_le_of_keyFloorAt`
with the identity sampler). -/
theorem advantage_freshMuPresenter_le (βmin : ℚ≥0) (hp : SigningParams p)
    (h_laws : SigningLaws prims) (hs2 : polyVecBounded sk.s2 p.eta) {ε : ℝ}
    (hf : KeyFloor prims βmin ε sk.t0) {m t Q : ℕ}
    (𝒜 : Adversary (PresIn p Rnd Ctx) (PresOut p) Ctx Unit (Option (Presentation p)) m t) :
    𝒜.advantage (fun _ _ => True) (freshMuPresenter f)
        (uniformOfFintype (SaltedCoins (_root_.MLDSA.Bytes 64) (Rnd × CommitHashBytes p × Fin D)))
        flatPresentSim Q ≤
      Q * t / Fintype.card (_root_.MLDSA.Bytes 64) +
        Q * (Q - 1) / (2 * Fintype.card (_root_.MLDSA.Bytes 64)) +
        Q * stepBError f prims sk aHat (Cutoff.const βmin) ε := by
  have h := advantage_freshMuPresenter_le_of_keyFloorAt f prims sk aHat (Cutoff.const βmin) hp
    h_laws hs2 (keyFloorAt_const_iff.2 hf) id (tvDist_map_id_shapedTarget_const βmin) (Q := Q) 𝒜
  rw [flatPresentSim_eq_flatPresentSimOf]
  simpa only [add_zero] using h

end StepB

/-! ### The presentations -/

section Assembly

variable (prims : Primitives p) [nttOps : NTTRingOps] [Nonempty (MaskBox p)] (sk : SecretKey p)
  (aHat : TqMatrix p.k p.l) (cut : Cutoff p)

omit nttOps in
/-- `Bytes 64` has `2^512` values (`GordieHowe.Lattice.card_bytes`). -/
theorem card_bytes64 : (Fintype.card (_root_.MLDSA.Bytes 64) : ℝ) = 2 ^ 512 := by
  rw [GordieHowe.Lattice.card_bytes, Nat.cast_pow, show ((256 : ℕ) : ℝ) = 2 ^ 8 by norm_num,
    ← pow_mul]

/-- **The coins of the honest presenter with the tape drawn as `f u`**: a uniform `R` and the
tape `f u` for a uniform `u`. -/
noncomputable def tapeCoinsAt : PMF (Rnd × LoopTape p) :=
  (uniformOfFintype Rnd).bind fun R => ((uniformOfFintype (Fin D)).map f).map (R, ·)

omit [NeZero (bucketCount p)] [DecidableEq Rnd] [Fintype Ctx] [DecidableEq Ctx] nttOps
  [Nonempty (MaskBox p)] in
/-- The coins of `honestPresenterAt`, read as `(R, f u)`, have the law `tapeCoinsAt f`. -/
theorem map_uniform_eq_tapeCoinsAt :
    (uniformOfFintype (SaltedCoins Rnd (Fin D))).map (fun c => (c.salt, f c.coins)) =
      tapeCoinsAt f := by
  rw [← map_uniformOfFintype_equiv (SaltedCoins.equivProd Rnd (Fin D)).symm, PMF.map_comp,
    uniformOfFintype_prod_eq_bind, PMF.map_bind, tapeCoinsAt]
  congr 1
  funext R
  simp only [PMF.map_comp]
  rfl

omit [DecidableEq Rnd] [Fintype Ctx] [DecidableEq Ctx] in
/-- **The tape drawn as `f u`** moves the honest coins by at most the distance of the tapes. -/
theorem tvDist_honestPresenterLaw_le :
    tvDist (honestPresenterLaw (Rnd := Rnd) prims sk aHat cut) (tapeCoinsAt f) ≤
      tvDist ((uniformOfFintype (Fin D)).map f) (loopTapeLaw prims sk aHat cut) := by
  rw [honestPresenterLaw_eq, tapeCoinsAt]
  refine (tvDist_uniformOfFintype_bind_le _ _).trans ?_
  refine (Finset.expect_le_expect fun R _ => ?_).trans_eq (Fintype.expect_const _)
  rw [tvDist_comm]
  exact tvDist_map_le _ _ _

omit [NeZero (bucketCount p)] nttOps [Nonempty (MaskBox p)] in
/-- **The honest presenter with the coins `tapeCoinsAt f`** is `honestPresenterAt f` with uniform
coins. -/
theorem acceptProb_realEnv_tapeCoinsAt {m t Q : ℕ}
    (𝒜 : Adversary (PresIn p Rnd Ctx) (PresOut p) Ctx Unit (Option (Presentation p)) m t) :
    𝒜.acceptProb (realEnv (fun _ _ => True) (honestPresenter tr) (tapeCoinsAt f) Q) =
      𝒜.acceptProb (realEnv (fun _ _ => True) (honestPresenterAt tr f)
        (uniformOfFintype (SaltedCoins Rnd (Fin D))) Q) := by
  have h : ∀ r, (𝒜.alg r).acceptProb (realEnv (fun _ _ => True) (honestPresenter tr)
      (tapeCoinsAt f) Q) =
      (𝒜.alg r).acceptProb (realEnv (fun _ _ => True) (honestPresenterAt tr f)
        (uniformOfFintype (SaltedCoins Rnd (Fin D))) Q) := fun r =>
    IAlg.acceptProb_realEnv_eq_of_map _ _ _ _ _ _ (fun c => (c.salt, f c.coins))
      (fun H x w c => honestPresenter_prove tr H x w (c.salt, f c.coins))
      (map_uniform_eq_tapeCoinsAt f).symm
  simp only [Adversary.acceptProb, h]

/-- **The presentations at a fixed tape approximation with a sampler**: steps A, C and B, and the
move of the honest coins to `tapeCoinsAt f`. -/
theorem advantage_honestPresenter_le_tape_of_keyFloorAt (hp : SigningParams p)
    (h_laws : SigningLaws prims) (hs2 : polyVecBounded sk.s2 p.eta) {ε : ℝ}
    (hf : KeyFloorAt prims cut ε sk.t0) {C : Type} [Fintype C] [Nonempty C]
    (samp : C → BucketVec p × CommitHashBytes p) {δ : ℝ}
    (hδ : tvDist ((uniformOfFintype C).map samp) (shapedTarget cut) ≤ δ) {m t Q : ℕ}
    (𝒜 : Adversary (PresIn p Rnd Ctx) (PresOut p) Ctx Unit (Option (Presentation p)) m t)
    (hpost : ∀ r, (𝒜.alg r).PostOracleFree) :
    𝒜.advantage (fun _ _ => True) (honestPresenter tr) (honestPresenterLaw prims sk aHat cut)
        (flatPresentSimOf samp) Q ≤
      Q * tvDist ((uniformOfFintype (Fin D)).map f) (loopTapeLaw prims sk aHat cut) +
        (Q * t / Fintype.card Rnd + Q * (Q - 1) / (2 * Fintype.card Rnd)) +
        Q * t / Fintype.card Rnd +
        (Q * t / Fintype.card (_root_.MLDSA.Bytes 64) +
          Q * (Q - 1) / (2 * Fintype.card (_root_.MLDSA.Bytes 64)) +
          Q * (stepBError f prims sk aHat cut ε + δ)) := by
  have h0 := 𝒜.abs_acceptProb_realEnv_law_sub_le (fun _ _ => True) (Q := Q)
    (honestPresenter tr) (honestPresenterLaw prims sk aHat cut) (tapeCoinsAt f)
  rw [acceptProb_realEnv_tapeCoinsAt] at h0
  have hA := advantage_freshMuSim_le tr f (Q := Q) 𝒜
  have hC := abs_acceptProb_simEnv_dropAssignments_le (rel := fun _ _ => True)
    (Q := Q) (hS := hiddenProgramming_freshMuSim tr f) (𝒜 := 𝒜) (hpost := hpost)
  rw [acceptProb_simEnv_dropAssignments_freshMuSim] at hC
  have hB := advantage_freshMuPresenter_le_of_keyFloorAt f prims sk aHat cut hp h_laws hs2 hf samp
    hδ (Q := Q) 𝒜
  rw [Adversary.advantage] at hA hB ⊢
  rw [GordieHowe.advantage] at hA hB ⊢
  have hcoins := mul_le_mul_of_nonneg_left
    (tvDist_honestPresenterLaw_le (Rnd := Rnd) f prims sk aHat cut)
    (Nat.cast_nonneg (α := ℝ) Q)
  have := abs_sub_le
    (𝒜.acceptProb (realEnv (fun _ _ => True) (honestPresenter tr)
      (honestPresenterLaw prims sk aHat cut) Q))
    (𝒜.acceptProb (realEnv (fun _ _ => True) (honestPresenterAt tr f)
      (uniformOfFintype (SaltedCoins Rnd (Fin D))) Q))
    (𝒜.acceptProb (simEnv (fun _ _ => True) (flatPresentSimOf samp) Q))
  have := abs_sub_le (𝒜.acceptProb (realEnv (fun _ _ => True) (honestPresenterAt tr f)
      (uniformOfFintype (SaltedCoins Rnd (Fin D))) Q))
    (𝒜.acceptProb (simEnv (fun _ _ => True) (freshMuSim tr f) Q))
    (𝒜.acceptProb (simEnv (fun _ _ => True) (flatPresentSimOf samp) Q))
  have := abs_sub_le (𝒜.acceptProb (simEnv (fun _ _ => True) (freshMuSim tr f) Q))
    (𝒜.acceptProb (realEnv (fun _ _ => True) (freshMuPresenter f)
      (uniformOfFintype (SaltedCoins (_root_.MLDSA.Bytes 64) (Rnd × CommitHashBytes p × Fin D))) Q))
    (𝒜.acceptProb (simEnv (fun _ _ => True) (flatPresentSimOf samp) Q))
  linarith

/-- **The presentations at a fixed tape approximation**: steps A, C and B, and the move of the
honest coins to `tapeCoinsAt f` (`advantage_honestPresenter_le_tape_of_keyFloorAt` with the
identity sampler). -/
theorem advantage_honestPresenter_le_tape (βmin : ℚ≥0) (hp : SigningParams p)
    (h_laws : SigningLaws prims) (hs2 : polyVecBounded sk.s2 p.eta) {ε : ℝ}
    (hf : KeyFloor prims βmin ε sk.t0) {m t Q : ℕ}
    (𝒜 : Adversary (PresIn p Rnd Ctx) (PresOut p) Ctx Unit (Option (Presentation p)) m t)
    (hpost : ∀ r, (𝒜.alg r).PostOracleFree) :
    𝒜.advantage (fun _ _ => True) (honestPresenter tr)
        (honestPresenterLaw prims sk aHat (Cutoff.const βmin)) flatPresentSim Q ≤
      Q * tvDist ((uniformOfFintype (Fin D)).map f)
          (loopTapeLaw prims sk aHat (Cutoff.const βmin)) +
        (Q * t / Fintype.card Rnd + Q * (Q - 1) / (2 * Fintype.card Rnd)) +
        Q * t / Fintype.card Rnd +
        (Q * t / Fintype.card (_root_.MLDSA.Bytes 64) +
          Q * (Q - 1) / (2 * Fintype.card (_root_.MLDSA.Bytes 64)) +
          Q * stepBError f prims sk aHat (Cutoff.const βmin) ε) := by
  have h := advantage_honestPresenter_le_tape_of_keyFloorAt tr f prims sk aHat (Cutoff.const βmin)
    hp h_laws hs2 (keyFloorAt_const_iff.2 hf) id (tvDist_map_id_shapedTarget_const βmin) (Q := Q)
    𝒜 hpost
  rw [flatPresentSim_eq_flatPresentSimOf]
  simpa only [add_zero] using h

/-- **The presentations of the flattened signer are simulated by `flatPresentSimOf f`**: under the
floor at the cut-off, for a sampler `f` whose output on uniform coins is within `δ` of the shaped
target, every adversary with a budget of `t` queries whose output does not read the final oracle
(`IAlg.PostOracleFree`), with `Q` presentations answered, has advantage at most

    Q · (flatOracleConcError + ε + signerRegGap / (1 - ε) + δ)
      + (2 Q t + Q (Q - 1) / 2) / |Rnd| + (Q t + Q (Q - 1) / 2) / 2^512

between the honest presenter and the simulator. The adversary chooses each context and sees
`(µ, w₁, c̃)` per presentation and the oracles; `R` is never published.

The proof draws the loop tape as `g u` for a uniform `u : Fin D`, within `|LoopTape| / D` of its
law (`exists_map_uniformOfFintype_tvDist_le`); that costs `2 Q |LoopTape| / D` at every `D`
(`advantage_honestPresenter_le_tape_of_keyFloorAt`), and `D` is taken large. -/
theorem presentations_advantage_le_of_keyFloorAt (hp : SigningParams p)
    (h_laws : SigningLaws prims) (hs2 : polyVecBounded sk.s2 p.eta) {ε : ℝ}
    (hf : KeyFloorAt prims cut ε sk.t0) {C : Type} [Fintype C] [Nonempty C]
    (f : C → BucketVec p × CommitHashBytes p) {δ : ℝ}
    (hδ : tvDist ((uniformOfFintype C).map f) (shapedTarget cut) ≤ δ) {m t Q : ℕ}
    (𝒜 : Adversary (PresIn p Rnd Ctx) (PresOut p) Ctx Unit (Option (Presentation p)) m t)
    (hpost : ∀ r, (𝒜.alg r).PostOracleFree) :
    𝒜.advantage (fun _ _ => True) (honestPresenter tr) (honestPresenterLaw prims sk aHat cut)
        (flatPresentSimOf f) Q ≤
      Q * (flatOracleConcError prims sk aHat cut + ε + signerRegGap prims sk aHat cut / (1 - ε) +
          δ) +
        (2 * Q * t + Q * (Q - 1) / 2) / Fintype.card Rnd + (Q * t + Q * (Q - 1) / 2) / 2 ^ 512 := by
  refine le_of_forall_pos_le_add fun e he => ?_
  set L : ℝ := (Fintype.card (LoopTape p) : ℝ)
  obtain ⟨n, hn⟩ := exists_nat_gt (2 * Q * L / e)
  have : NeZero (n + 1) := ⟨n.succ_ne_zero⟩
  obtain ⟨g, hg⟩ := exists_map_uniformOfFintype_tvDist_le (loopTapeLaw prims sk aHat cut) (n + 1)
  have h := advantage_honestPresenter_le_tape_of_keyFloorAt tr g prims sk aHat cut hp h_laws hs2
    hf f hδ (Q := Q) 𝒜 hpost
  rw [stepBError, card_bytes64] at h
  have hD : (0 : ℝ) < (n + 1 : ℕ) := Nat.cast_pos.2 n.succ_pos
  have hδ' : (Q : ℝ) *
      tvDist ((uniformOfFintype (Fin (n + 1))).map g) (loopTapeLaw prims sk aHat cut)
      ≤ Q * L / (n + 1 : ℕ) := by
    rw [mul_div_assoc]
    exact mul_le_mul_of_nonneg_left hg (Nat.cast_nonneg Q)
  have hsmall : 2 * (Q * L / (n + 1 : ℕ)) ≤ e := by
    rw [← mul_div_assoc, div_le_iff₀ hD]
    have : 2 * Q * L / e < (n + 1 : ℕ) := by push_cast; linarith
    rw [div_lt_iff₀ he] at this
    linarith
  have hR : (0 : ℝ) < Fintype.card Rnd := Nat.cast_pos.2 Fintype.card_pos
  have hsplit : (2 * Q * t + Q * (Q - 1) / 2) / (Fintype.card Rnd : ℝ) =
      Q * t / Fintype.card Rnd + Q * (Q - 1) / (2 * Fintype.card Rnd) +
        Q * t / Fintype.card Rnd := by
    field_simp
    ring
  set N : ℝ := 2 ^ 512
  have hN0 : (0 : ℝ) < N := by positivity
  clear_value N
  have hsplit' : (Q * t + Q * (Q - 1) / 2) / N = Q * t / N + Q * (Q - 1) / (2 * N) := by
    field_simp
  set η := tvDist ((uniformOfFintype (Fin (n + 1))).map g) (loopTapeLaw prims sk aHat cut)
  have hmul : (Q : ℝ) * (flatOracleConcError prims sk aHat cut +
      (ε + signerRegGap prims sk aHat cut / (1 - ε)) + η + δ) =
      Q * (flatOracleConcError prims sk aHat cut + ε + signerRegGap prims sk aHat cut / (1 - ε) +
          δ) +
        Q * η := by ring
  rw [hmul] at h
  rw [hsplit, hsplit']
  linarith

/-- **The presentations of the flattened signer are simulated by `flatPresentSim`**: under the
floor, every adversary with a budget of `t` queries whose
output does not read the final oracle (`IAlg.PostOracleFree`), with `Q` presentations answered,
has advantage at most

    Q · (flatOracleConcError + ε + signerRegGap / (1 - ε))
      + (2 Q t + Q (Q - 1) / 2) / |Rnd| + (Q t + Q (Q - 1) / 2) / 2^512

between the honest presenter and the simulator. The adversary chooses each context and sees
`(µ, w₁, c̃)` per presentation and the oracles; `R` is never published. It is
`presentations_advantage_le_of_keyFloorAt` at the constant cut-off with the identity sampler
(`δ = 0`). -/
theorem presentations_advantage_le_of_keyFloor (βmin : ℚ≥0) (hp : SigningParams p)
    (h_laws : SigningLaws prims) (hs2 : polyVecBounded sk.s2 p.eta) {ε : ℝ}
    (hf : KeyFloor prims βmin ε sk.t0) {m t Q : ℕ}
    (𝒜 : Adversary (PresIn p Rnd Ctx) (PresOut p) Ctx Unit (Option (Presentation p)) m t)
    (hpost : ∀ r, (𝒜.alg r).PostOracleFree) :
    𝒜.advantage (fun _ _ => True) (honestPresenter tr)
        (honestPresenterLaw prims sk aHat (Cutoff.const βmin)) flatPresentSim Q ≤
      Q * (flatOracleConcError prims sk aHat (Cutoff.const βmin) + ε + signerRegGap prims sk aHat
          (Cutoff.const βmin) / (1 - ε)) +
        (2 * Q * t + Q * (Q - 1) / 2) / Fintype.card Rnd + (Q * t + Q * (Q - 1) / 2) / 2 ^ 512 := by
  have h := presentations_advantage_le_of_keyFloorAt tr prims sk aHat (Cutoff.const βmin) hp
    h_laws hs2 (keyFloorAt_const_iff.2 hf) id (tvDist_map_id_shapedTarget_const βmin) (Q := Q)
    𝒜 hpost
  rw [flatPresentSim_eq_flatPresentSimOf]
  simpa only [add_zero] using h

/-- **The presentations are zero knowledge** in the classical random-oracle model against
query-bounded adversaries (`GordieHowe.ROM.ZeroKnowledge`, through
`ROM.NIZK.ZeroKnowledgeQueryBounded` and `zeroKnowledge_of_queryBounded`), at the error of
`presentations_advantage_le_of_keyFloorAt`: under the floor at the cut-off, with the simulator
`flatPresentSimOf f` for a sampler `f` within `δ` of the shaped target. -/
theorem zeroKnowledge_presentations_of_keyFloorAt (hp : SigningParams p)
    (h_laws : SigningLaws prims) (hs2 : polyVecBounded sk.s2 p.eta) {ε : ℝ}
    (hf : KeyFloorAt prims cut ε sk.t0) {C : Type} [Fintype C] [Nonempty C]
    (f : C → BucketVec p × CommitHashBytes p) {δ : ℝ}
    (hδ : tvDist ((uniformOfFintype C).map f) (shapedTarget cut) ≤ δ) :
    GordieHowe.ROM.ZeroKnowledge (fun (_ : Ctx) (_ : Unit) => True)
      (honestPresenter (Rnd := Rnd) tr) (honestPresenterLaw prims sk aHat cut)
      (flatPresentSimOf f)
      fun t Q =>
        Q * (flatOracleConcError prims sk aHat cut + ε +
          signerRegGap prims sk aHat cut / (1 - ε) + δ) +
          (2 * Q * t + Q * (Q - 1) / 2) / Fintype.card Rnd + (Q * t + Q * (Q - 1) / 2) / 2 ^ 512 :=
  GordieHowe.ROM.QueryBoundedAdversary.zeroKnowledge_of_queryBounded fun _ _ _ 𝒜 hpost =>
    presentations_advantage_le_of_keyFloorAt tr prims sk aHat cut hp h_laws hs2 hf f hδ 𝒜 hpost

/-- **The presentations are zero knowledge** in the classical random-oracle model against
query-bounded adversaries (`GordieHowe.ROM.ZeroKnowledge`, through
`ROM.NIZK.ZeroKnowledgeQueryBounded` and `zeroKnowledge_of_queryBounded`), at the error of
`presentations_advantage_le_of_keyFloor`.

The everlasting form fails: an adversary unbounded after its steps can search `H_µ(tr, ·, ctx)`
for the published `µ`, which the simulator draws without programming `H_µ`. -/
theorem zeroKnowledge_presentations (βmin : ℚ≥0) (hp : SigningParams p)
    (h_laws : SigningLaws prims) (hs2 : polyVecBounded sk.s2 p.eta) {ε : ℝ}
    (hf : KeyFloor prims βmin ε sk.t0) :
    GordieHowe.ROM.ZeroKnowledge (fun (_ : Ctx) (_ : Unit) => True)
      (honestPresenter (Rnd := Rnd) tr) (honestPresenterLaw prims sk aHat (Cutoff.const βmin))
      flatPresentSim
      fun t Q =>
        Q * (flatOracleConcError prims sk aHat (Cutoff.const βmin) + ε +
          signerRegGap prims sk aHat (Cutoff.const βmin) / (1 - ε)) +
          (2 * Q * t + Q * (Q - 1) / 2) / Fintype.card Rnd + (Q * t + Q * (Q - 1) / 2) / 2 ^ 512 :=
  GordieHowe.ROM.QueryBoundedAdversary.zeroKnowledge_of_queryBounded fun _ _ _ 𝒜 hpost =>
    presentations_advantage_le_of_keyFloor tr prims sk aHat βmin hp h_laws hs2 hf 𝒜 hpost

end Assembly

end GordieHowe.MLDSA
