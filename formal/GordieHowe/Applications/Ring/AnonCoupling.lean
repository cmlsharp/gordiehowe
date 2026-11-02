-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Applications.Ring.Anonymity
public import GordieHowe.Foundations.Probability.Convexity
public import GordieHowe.Foundations.ToMathlib.PMFUniform

@[expose] public section

/-!
# The coupling bound for rounds with public outputs and refusals

The anonymity argument of `GordieHowe/Applications/Ring/Anonymity.lean`
(`PubAnonAdversary.abs_condProb_sub_le`), restated for any proof system with a witness
indistinguishability hypothesis, for entries that may be refusals, and with the signing coins of a
round shared by all challenges (as a challenger draws them).

- `PMF.bind_pi_bind_coord`: **resampling one coordinate of a product law** at the level of laws: if
  `f T` does not read coordinate `j` of `T`, binding `f T` and then a kernel reading `T j` is binding
  `f T` and then the kernel averaged over `ν j`.
- `histRun init step`: rounds whose outputs are appended to a history, the first state drawn from
  `init`, round `j`'s output drawn from `step j` of the state and the history; `pubRun_eq_histRun`:
  the rounds with public outputs of `Anonymity.lean` are such rounds. `histRun_congr`: two step
  families that agree before round `j` give the same rounds up to `j`.
- `bind_pi_histRun`: **lazy sampling**: rounds that read row `j` of a table in round `j`, averaged
  over a table with independent rows, are the rounds that draw the row afresh in each round. So the
  rounds read only the law of each row.
- `wiSelector`, `PubWI law pubOf rel wi`: **witness indistinguishability with public outputs** of a
  proof law at error `wi`: deterministic adversaries choosing, from the whole oracle and the history,
  a statement with two witnesses in `rel` from a set of at most `c` choices, distinguish the rounds
  answered with the first and with the second witnesses with advantage at most `Q · wi c`
  (`GordieHowe/Applications/Ring/SPBCSAnon.lean` proves it for the spBCS proof law at error
  `wiError δ` from honest-verifier zero knowledge at error `δ`).
  `PubWI.wi_nonneg`: its error is nonnegative. `PubWI.mono`: it holds on every smaller relation.
- `ETable`, `entryLaw L b`, `entrySel`: rounds whose round `j` reads, from a table with an
  independent entry per round and challenge, the entry of its challenge `choice j`: a refusal
  `none`, or a public value with a base signature, proved with the witness of user `b`.
- `ecoupling`, `ecoupledLaw`, `eside`, `ehybChoice`, `ehybrid`, `ehybridSet`, `bad₀`, `bad₁`,
  `ebadProb`: the coupled table of the two users' entries, the hybrid two-witness choices and the
  bad events, with refusals. `entryLaw_eq_map_eside`: the entry table of each user is a side of
  the coupled table. `abs_erun_sub_hybrid_le`: an experiment and its hybrid differ by at most the
  sum over the rounds of the bad events' probabilities. `sum_ecoupledLaw_mul_badProb_le`: over the
  coupled table, the bad event of a round has probability at most `ε` when the coupling of every
  challenge gives it probability at most `ε`.
- `abs_entryRounds_sub_le`: **the coupling bound**: with witness indistinguishability at error `wi`
  and every challenge outside the active set `act` refused by both users, the experiments of the
  two users are within `Q · (ε + 2η) + Q · wi (Q · C)` for `C ≥ |act|`, `ε` bounding the distance
  of the two users' laws of the refusal-or-public value of an active challenge, `η` bounding the
  probability of an invalid entry of an active challenge. A refusal by one user only is a
  difference of the refusal-or-public values, so it is counted in `ε`.
- `relabelHist`, `pubRun_map_proof`, `PubWI.map_proof`: witness indistinguishability survives
  relabelling the proofs by a function. `pubRun_split`, `PubWI.of_split`: it survives an oracle that
  splits as a product whose first part the proofs do not read. `pubRun_congr_law`,
  `PubWI.congr_rel`: it transfers between proof laws that agree on the relation.
  `PubWI.of_forall_not_mem`: it holds for the empty relation at every nonnegative error.
-/

namespace PMF

open scoped ENNReal

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {δ : ι → Type*} [∀ i, Fintype (δ i)]
  [∀ i, DecidableEq (δ i)] {α β : Type*}

/-- **Resampling one coordinate of a product law, for laws**: if `f T` does not depend on
coordinate `j` of `T`, then drawing `T ← pi ν`, `a ← f T` and a value of `k a (T j)` is drawing
`T ← pi ν`, `a ← f T`, a fresh `b ← ν j` and a value of `k a b`. -/
theorem bind_pi_bind_coord (ν : ∀ i, PMF (δ i)) (j : ι) (f : (∀ i, δ i) → PMF α)
    (hf : ∀ T b, f (Function.update T j b) = f T) (k : α → δ j → PMF β) :
    (pi ν).bind (fun T => (f T).bind fun a => k a (T j)) =
      ((pi ν).bind f).bind fun a => (ν j).bind (k a) := by
  ext z
  simp only [bind_apply]
  have hL : ∑' T, pi ν T * ∑' a, f T a * k a (T j) z =
      ∑ T, pi ν T * (fun T b => ∑' a, f T a * k a b z) T (T j) :=
    tsum_fintype (L := SummationFilter.unconditional _) _
  rw [hL, sum_pi_mul_apply_eq ν j (fun T b => ∑' a, f T a * k a b z) fun T b => by simp only [hf]]
  have e1 : ∀ T, pi ν T * ∑ b, ν j b * ∑' a, f T a * k a b z =
      ∑' b, ∑' a, pi ν T * (ν j b * (f T a * k a b z)) := fun T => by
    rw [← tsum_fintype (L := SummationFilter.unconditional (δ j)), ← ENNReal.tsum_mul_left]
    refine tsum_congr fun b => ?_
    rw [← ENNReal.tsum_mul_left, ← ENNReal.tsum_mul_left]
  have e2 : ∀ a, (∑' T, pi ν T * f T a) * ∑' b, ν j b * k a b z =
      ∑' T, ∑' b, pi ν T * (ν j b * (f T a * k a b z)) := fun a => by
    rw [← ENNReal.tsum_mul_right]
    refine tsum_congr fun T => ?_
    rw [← ENNReal.tsum_mul_left]
    refine tsum_congr fun b => ?_
    ring
  simp_rw [e1, e2]
  rw [← tsum_fintype (L := SummationFilter.unconditional (∀ i, δ i))]
  calc _ = ∑' (T : ∀ i, δ i) (a : α) (b : δ j), pi ν T * (ν j b * (f T a * k a b z)) := by
        congr 1
        funext T
        exact ENNReal.tsum_comm
    _ = _ := ENNReal.tsum_comm

end PMF

namespace GordieHowe.Ring

open scoped ENNReal BigOperators

/-! ### Rounds appended to a history -/

section HistRun

variable {Ω A : Type} {Q : ℕ}

/-- **Rounds appended to a history**: the first state `h ← init`, then in round `j` an output drawn
from `step j h hist`, given the state and the outputs `hist` of the earlier rounds, appended to the
history. -/
noncomputable def histRun (init : PMF Ω) (step : (j : Fin Q) → Ω → (Fin j → A) → PMF A) :
    (j : ℕ) → j ≤ Q → PMF (Ω × (Fin j → A))
  | 0, _ => init.map fun h => (h, Fin.elim0)
  | j + 1, hj => (histRun init step j (by omega)).bind fun s =>
      (step ⟨j, by omega⟩ s.1 s.2).map fun r => (s.1, Fin.snoc (α := fun _ => A) s.2 r)

/-- **Two step families that agree before round `j` give the same rounds up to `j`.** -/
theorem histRun_congr {init : PMF Ω} {step step' : (j : Fin Q) → Ω → (Fin j → A) → PMF A} :
    ∀ j (hj : j ≤ Q), (∀ i : Fin Q, i.1 < j → step i = step' i) →
      histRun init step j hj = histRun init step' j hj
  | 0, _, _ => rfl
  | j + 1, hj, h => by
    rw [histRun, histRun, histRun_congr j (by omega) fun i hi => h i (by omega),
      h ⟨j, by omega⟩ (by simp)]

/-- **The rounds with public outputs** of `GordieHowe/Applications/Ring/Anonymity.lean` are rounds
appended to a history, the oracle uniform and round `j`'s output `roundLaw` of the selection. -/
theorem pubRun_eq_histRun {X W Pub Pf : Type} [Fintype Ω] [Nonempty Ω]
    (law : Ω → X → W → PMF Pf) (pubOf : X → Pub) (sel : Selector Ω X W Pub Pf Q) :
    ∀ j (hj : j ≤ Q), pubRun law pubOf sel j hj =
      histRun (PMF.uniformOfFintype Ω) (fun j h hist => roundLaw law pubOf h (sel j h hist)) j hj
  | 0, _ => rfl
  | j + 1, hj => by
    rw [pubRun, histRun, pubRun_eq_histRun law pubOf sel j (by omega)]
    rfl

variable {Rw : Type} [Fintype Rw] [DecidableEq Rw]

/-- **Lazy sampling**: rounds whose round `j` reads row `j` of a table `T` (through the kernel
`K j h hist (T j)`), averaged over a table with independent rows `T ← pi ρ`, are the rounds that
draw the row `b ← ρ j` afresh in round `j`. -/
theorem bind_pi_histRun (init : PMF Ω) (ρ : Fin Q → PMF Rw)
    (K : (j : Fin Q) → Ω → (Fin j → A) → Rw → PMF A) :
    ∀ j (hj : j ≤ Q),
      (PMF.pi ρ).bind (fun T => histRun init (fun j h hist => K j h hist (T j)) j hj) =
        histRun init (fun j h hist => (ρ j).bind (K j h hist)) j hj
  | 0, _ => PMF.bind_const _ _
  | j + 1, hj => by
    refine (PMF.bind_pi_bind_coord ρ ⟨j, by omega⟩
      (fun T => histRun init (fun j h hist => K j h hist (T j)) j (by omega))
      (fun (T : Fin Q → Rw) (b : Rw) => histRun_congr j (by omega) fun i hi => by
        funext h hist
        rw [Function.update_of_ne (fun he => by rw [he] at hi; exact lt_irrefl _ hi)])
      (fun s b => (K ⟨j, by omega⟩ s.1 s.2 b).map fun r =>
        (s.1, Fin.snoc (α := fun _ => A) s.2 r))).trans ?_
    rw [bind_pi_histRun init ρ K j (by omega), histRun]
    congr 1
    funext s
    rw [PMF.map_bind]

end HistRun

/-! ### Witness indistinguishability with public outputs -/

section WI

variable {Ω Stmt Wit Pub Pf : Type} [Fintype Ω] [Nonempty Ω]

/-- **The selector of two-witness choices** answering round `j` with the second witness when `bs j`
and refusing the rounds whose choice is `none`. -/
def wiSelector {Q : ℕ} (F : (j : Fin Q) → Ω → PubHist Pub Pf j → Option (SPBCS.WIChoice Stmt Wit))
    (bs : ℕ → Bool) : Selector Ω Stmt Wit Pub Pf Q :=
  fun j h hist => (F j h hist).map fun c => (c.stmt, if bs j then c.wit₁ else c.wit₀)

/-- **Witness indistinguishability with public outputs at error `wi`** of the proof law `law` (the
law of an honest proof at an oracle, a statement and a witness) for the relation `rel`: for every
`Q`, every deterministic adversary choosing in each round, from the whole oracle and the history of
public values and proofs, a statement with two witnesses (or refusing the round), all from a finite
set of at most `c` choices whose witnesses are both in `rel`, the rounds answered with the first and
with the second witnesses are distinguished by any event of the oracle and the history with
advantage at most `Q · wi c`. The spBCS compilation has it at `wi = wiError δ` when its honest
prover has honest-verifier zero knowledge at error `δ` (`pubWI_proofLaw_comap`,
`pubWI_spbcsProofSystem` of `GordieHowe/Applications/Ring/SPBCSAnon.lean`, from
`gameAdvantage_pubRun_le`). -/
def PubWI (law : Ω → Stmt → Wit → PMF Pf) (pubOf : Stmt → Pub) (rel : Set (Stmt × Wit))
    (wi : ℕ → ℝ) : Prop :=
  ∀ (Q c : ℕ) (F : (j : Fin Q) → Ω → PubHist Pub Pf j → Option (SPBCS.WIChoice Stmt Wit))
    (S : Finset (SPBCS.WIChoice Stmt Wit)), S.card ≤ c →
    (∀ x ∈ S, (x.stmt, x.wit₀) ∈ rel ∧ (x.stmt, x.wit₁) ∈ rel) →
    (∀ j h hist x, F j h hist = some x → x ∈ S) →
    ∀ U : Ω → PubHist Pub Pf Q → Prop,
      gameAdvantage (pubRun law pubOf (wiSelector F fun _ => false) Q le_rfl)
        (pubRun law pubOf (wiSelector F fun _ => true) Q le_rfl) {s | U s.1 s.2} ≤ Q * wi c

/-- **Witness indistinguishability on a smaller relation**: a proof law with witness
indistinguishability at error `wi` for `rel` has it for every `rel' ⊆ rel`. -/
theorem PubWI.mono {law : Ω → Stmt → Wit → PMF Pf} {pubOf : Stmt → Pub}
    {rel rel' : Set (Stmt × Wit)} {wi : ℕ → ℝ} (h : PubWI law pubOf rel wi) (hsub : rel' ⊆ rel) :
    PubWI law pubOf rel' wi :=
  fun Q c F S hS hrel hF U => h Q c F S hS (fun x hx => ⟨hsub (hrel x hx).1, hsub (hrel x hx).2⟩)
    hF U

/-- **The error of witness indistinguishability is nonnegative**: one round refused by both
experiments has advantage `0`. -/
theorem PubWI.wi_nonneg {law : Ω → Stmt → Wit → PMF Pf} {pubOf : Stmt → Pub}
    {rel : Set (Stmt × Wit)} {wi : ℕ → ℝ} (h : PubWI law pubOf rel wi) (c : ℕ) : 0 ≤ wi c := by
  have hadv := h 1 c (fun _ _ _ => none) ∅ (by simp) (by simp) (by simp) fun _ _ => True
  have hsel : wiSelector (Q := 1) (Ω := Ω) (Stmt := Stmt) (Wit := Wit) (Pub := Pub) (Pf := Pf)
      (fun _ _ _ => none)
      (fun _ => false) = wiSelector (fun _ _ _ => none) fun _ => true := rfl
  rw [hsel] at hadv
  simpa [gameAdvantage, advantage] using hadv

end WI

/-! ### Rounds with entries -/

section Entries

variable {Ω Stmt Wit Pub Pf Ch BSig : Type} [Fintype Ω] [Nonempty Ω] [Fintype Ch] [DecidableEq Ch]
  [Fintype Pub] [DecidableEq Pub] [Fintype BSig] [DecidableEq BSig] {Q : ℕ}

/-- **A table of entries**: for each round and each challenge, a public value with a base signature,
or a refusal (`none`). -/
abbrev ETable (Ch Pub BSig : Type) (Q : ℕ) : Type := Fin Q → Ch → Option (Pub × BSig)

/-- **The law of the entry table of experiment `b`**: every entry independent, the entry of the
challenge `ch` drawn from `L b ch`. -/
noncomputable def entryLaw (L : Bool → Ch → PMF (Option (Pub × BSig))) (b : Bool) :
    PMF (ETable Ch Pub BSig Q) :=
  PMF.pi fun _ => PMF.pi fun ch => L b ch

variable (choice : (j : Fin Q) → Ω → PubHist Pub Pf j → Ch) (stmtOf : Ch → Pub → Stmt)
  (witOf : Bool → Ch → BSig → Wit)

/-- **The selector of experiment `b` at the entry table `T`**: round `j` reads the entry of its
challenge `choice j`; a refusal refuses the round, and an entry `(y, σ)` selects the statement of
the challenge with the public value `y` and the witness of user `b` with `σ`. -/
def entrySel (b : Bool) (T : ETable Ch Pub BSig Q) : Selector Ω Stmt Wit Pub Pf Q :=
  fun j h hist => (T j (choice j h hist)).map fun e =>
    (stmtOf (choice j h hist) e.1, witOf b (choice j h hist) e.2)

end Entries

/-! ### The coupled table and the hybrid -/

section Coupled

variable {Ω Stmt Wit Pub Pf Ch BSig : Type} [Fintype Ω] [Nonempty Ω] [Fintype Ch] [DecidableEq Ch]
  [Fintype Pub] [DecidableEq Pub] [Fintype BSig] [DecidableEq BSig] {Q : ℕ}
  (L : Bool → Ch → PMF (Option (Pub × BSig)))

/-- An entry pair: the entries of user `0` and of user `1`. -/
abbrev EPair (Pub BSig : Type) : Type := Option (Pub × BSig) × Option (Pub × BSig)

/-- **The coupling of the two users' entries of a challenge**: a joint law with marginals `L false ch`
and `L true ch` whose refusal-or-public values differ with probability at most the distance of their
laws (`PMF.exists_coupling_map_le_tvDist`). -/
noncomputable def ecoupling (ch : Ch) : PMF (EPair Pub BSig) :=
  Classical.choose (PMF.exists_coupling_map_le_tvDist (L false ch) (L true ch) (Option.map Prod.fst))

omit [Fintype Ch] [DecidableEq Ch] in
/-- The first marginal of the coupling is user `0`'s entry law. -/
theorem map_fst_ecoupling (ch : Ch) : (ecoupling L ch).map Prod.fst = L false ch :=
  (Classical.choose_spec (PMF.exists_coupling_map_le_tvDist (L false ch) (L true ch)
    (Option.map Prod.fst))).1

omit [Fintype Ch] [DecidableEq Ch] in
/-- The second marginal of the coupling is user `1`'s entry law. -/
theorem map_snd_ecoupling (ch : Ch) : (ecoupling L ch).map Prod.snd = L true ch :=
  (Classical.choose_spec (PMF.exists_coupling_map_le_tvDist (L false ch) (L true ch)
    (Option.map Prod.fst))).2.1

omit [Fintype Ch] [DecidableEq Ch] in
/-- **The coupled refusal-or-public values differ with probability at most the distance of their
laws.** -/
theorem toReal_ecoupling_ne_le (ch : Ch) :
    ((ecoupling L ch).toOuterMeasure {x | x.1.map Prod.fst ≠ x.2.map Prod.fst}).toReal ≤
      PMF.tvDist ((L false ch).map (Option.map Prod.fst)) ((L true ch).map (Option.map Prod.fst)) :=
  (Classical.choose_spec (PMF.exists_coupling_map_le_tvDist (L false ch) (L true ch)
    (Option.map Prod.fst))).2.2

omit [Fintype Ch] [DecidableEq Ch] in
/-- An event of user `0`'s coupled entry has its probability under user `0`'s entry law. -/
theorem ecoupling_fst_eq (ch : Ch) (U : Set (Option (Pub × BSig))) :
    (ecoupling L ch).toOuterMeasure {x | x.1 ∈ U} = (L false ch).toOuterMeasure U := by
  rw [← map_fst_ecoupling L ch, PMF.toOuterMeasure_map_apply]
  rfl

omit [Fintype Ch] [DecidableEq Ch] in
/-- An event of user `1`'s coupled entry has its probability under user `1`'s entry law. -/
theorem ecoupling_snd_eq (ch : Ch) (U : Set (Option (Pub × BSig))) :
    (ecoupling L ch).toOuterMeasure {x | x.2 ∈ U} = (L true ch).toOuterMeasure U := by
  rw [← map_snd_ecoupling L ch, PMF.toOuterMeasure_map_apply]
  rfl

/-- A table of coupled entries. -/
abbrev CETable (Ch Pub BSig : Type) (Q : ℕ) : Type := Fin Q → Ch → EPair Pub BSig

/-- The law of the coupled table: every entry independent, from the coupling of its challenge. -/
noncomputable def ecoupledLaw : PMF (CETable Ch Pub BSig Q) :=
  PMF.pi fun _ => PMF.pi fun ch => ecoupling L ch

/-- The entries of user `b` of a coupled table. -/
def eside (b : Bool) (T : CETable Ch Pub BSig Q) : ETable Ch Pub BSig Q :=
  fun j ch => if b then (T j ch).2 else (T j ch).1

/-- **The entry table is a side of the coupled table.** -/
theorem entryLaw_eq_map_eside (b : Bool) :
    entryLaw (Q := Q) L b = (ecoupledLaw L).map (eside b) := by
  have h1 : (ecoupledLaw (Q := Q) L).map (eside b) =
      PMF.pi fun _ => ((PMF.pi fun ch => ecoupling L ch).map fun row ch =>
        if b then (row ch).2 else (row ch).1) :=
    PMF.pi_map (fun _ => PMF.pi fun ch => ecoupling L ch)
      (fun _ row ch => if b then (row ch).2 else (row ch).1)
  rw [h1, entryLaw]
  congr 1
  funext j
  rw [PMF.pi_map (fun ch => ecoupling L ch) (fun _ x => if b then x.2 else x.1)]
  congr 1
  funext ch
  cases b
  · exact (map_fst_ecoupling L ch).symm
  · exact (map_snd_ecoupling L ch).symm

variable (stmtOf : Ch → Pub → Stmt) (witOf : Bool → Ch → BSig → Wit) (rel : Set (Stmt × Wit))

open Classical in
/-- The witness of user `1` in the hybrid choice, given user `0`'s valid entry `p₀`: user `1`'s
when its entry is valid with the same public value, user `0`'s otherwise. -/
noncomputable def hybWit₁ (ch : Ch) (p₀ : Pub × BSig) : Option (Pub × BSig) → Wit
  | some p₁ =>
    if p₁.1 = p₀.1 ∧ (stmtOf ch p₁.1, witOf true ch p₁.2) ∈ rel then witOf true ch p₁.2
    else witOf false ch p₀.2
  | none => witOf false ch p₀.2

open Classical in
/-- **The hybrid choice of a challenge at a coupled entry**: when user `0`'s entry is valid, its
statement and witness, with user `1`'s witness when that is valid with the same public value; when
user `0`'s entry is invalid and user `1`'s valid, user `1`'s statement and witness twice; otherwise
(user `0` refuses, or neither is valid) `none`. -/
noncomputable def ehybChoice (ch : Ch) : EPair Pub BSig → Option (SPBCS.WIChoice Stmt Wit)
  | (none, _) => none
  | (some p₀, x₁) =>
    if (stmtOf ch p₀.1, witOf false ch p₀.2) ∈ rel then
      some ⟨stmtOf ch p₀.1, witOf false ch p₀.2, hybWit₁ stmtOf witOf rel ch p₀ x₁⟩
    else
      match x₁ with
      | some p₁ =>
        if (stmtOf ch p₁.1, witOf true ch p₁.2) ∈ rel then
          some ⟨stmtOf ch p₁.1, witOf true ch p₁.2, witOf true ch p₁.2⟩
        else none
      | none => none

omit [Fintype Ch] [DecidableEq Ch] [Fintype Pub] [Fintype BSig] [DecidableEq BSig] in
/-- **Every hybrid choice is admissible.** -/
theorem ehybChoice_admissible {ch : Ch} {x : EPair Pub BSig} {w : SPBCS.WIChoice Stmt Wit}
    (hw : ehybChoice stmtOf witOf rel ch x = some w) :
    (w.stmt, w.wit₀) ∈ rel ∧ (w.stmt, w.wit₁) ∈ rel := by
  classical
  obtain ⟨_ | p₀, x₁⟩ := x
  · simp [ehybChoice] at hw
  simp only [ehybChoice] at hw
  split_ifs at hw with h0
  · cases hw
    refine ⟨h0, ?_⟩
    rcases x₁ with _ | p₁
    · exact h0
    · simp only [hybWit₁]
      split_ifs with h1
      · rw [← h1.1]
        exact h1.2
      · exact h0
  · rcases x₁ with _ | p₁
    · simp at hw
    · simp only at hw
      split_ifs at hw with h1
      cases hw
      exact ⟨h1, h1⟩

variable {stmtOf witOf rel}
variable (choice : (j : Fin Q) → Ω → PubHist Pub Pf j → Ch) (act : Finset Ch)

/-- **The hybrid two-witness choices** at the coupled table `T`: in round `j`, the hybrid choice of
the round's challenge at its coupled entry when the challenge is active, `none` otherwise. -/
noncomputable def ehybrid (T : CETable Ch Pub BSig Q) :
    (j : Fin Q) → Ω → PubHist Pub Pf j → Option (SPBCS.WIChoice Stmt Wit) :=
  fun j h hist => if choice j h hist ∈ act then
    ehybChoice stmtOf witOf rel (choice j h hist) (T j (choice j h hist)) else none

open Classical in
/-- **The hybrid choice set** at the coupled table `T`: the hybrid choices of the active challenges at
every round. -/
noncomputable def ehybridSet (T : CETable Ch Pub BSig Q) : Finset (SPBCS.WIChoice Stmt Wit) :=
  ((Finset.univ : Finset (Fin Q)) ×ˢ act).biUnion fun p =>
    (ehybChoice stmtOf witOf rel p.2 (T p.1 p.2)).toFinset

omit [Fintype Ch] [DecidableEq Ch] [Fintype Pub] [Fintype BSig] [DecidableEq BSig] in
/-- **The hybrid choice set has at most `Q · |act|` choices.** -/
theorem card_ehybridSet_le (T : CETable Ch Pub BSig Q) :
    (ehybridSet (stmtOf := stmtOf) (witOf := witOf) (rel := rel) act T).card ≤ Q * act.card := by
  classical
  refine Finset.card_biUnion_le.trans ?_
  refine (Finset.sum_le_sum (g := fun _ => 1) fun p _ => Finset.card_le_one.2
    fun a ha b hb => by
      rw [Option.mem_toFinset] at ha hb
      exact Option.mem_unique ha hb).trans ?_
  rw [Finset.sum_const, Finset.card_product, Finset.card_univ, Fintype.card_fin, smul_eq_mul,
    mul_one]

omit [Fintype Ω] [Nonempty Ω] [Fintype Ch] [Fintype Pub] [Fintype BSig] [DecidableEq BSig] in
open Classical in
/-- **Every hybrid choice of a round is in the hybrid choice set.** -/
theorem ehybrid_mem (T : CETable Ch Pub BSig Q) (j : Fin Q) (h : Ω) (hist : PubHist Pub Pf j)
    (x : SPBCS.WIChoice Stmt Wit)
    (hx : ehybrid (stmtOf := stmtOf) (witOf := witOf) (rel := rel) choice act T j h hist = some x) :
    x ∈ ehybridSet (stmtOf := stmtOf) (witOf := witOf) (rel := rel) act T := by
  unfold ehybrid at hx
  split_ifs at hx with hA
  exact Finset.mem_biUnion.2 ⟨(j, choice j h hist), Finset.mem_product.2 ⟨Finset.mem_univ _, hA⟩,
    by rw [Option.mem_toFinset]; exact hx⟩

omit [Fintype Ch] [DecidableEq Ch] [Fintype Pub] [Fintype BSig] [DecidableEq BSig] in
open Classical in
/-- **Every choice of the hybrid choice set is admissible.** -/
theorem ehybridSet_admissible (T : CETable Ch Pub BSig Q) :
    ∀ c ∈ ehybridSet (stmtOf := stmtOf) (witOf := witOf) (rel := rel) act T,
      (c.stmt, c.wit₀) ∈ rel ∧ (c.stmt, c.wit₁) ∈ rel := by
  intro x hx
  obtain ⟨p, -, hp⟩ := Finset.mem_biUnion.1 hx
  rw [Option.mem_toFinset] at hp
  exact ehybChoice_admissible stmtOf witOf rel hp

variable (stmtOf witOf rel) in
/-- **The bad event of experiment `0`** at a coupled entry: an inactive challenge with an entry of
user `0`, or an invalid entry of user `0`. -/
def bad₀ (ch : Ch) (x : EPair Pub BSig) : Prop :=
  (ch ∉ act ∧ x.1 ≠ none) ∨ ∃ p ∈ x.1, (stmtOf ch p.1, witOf false ch p.2) ∉ rel

variable (stmtOf witOf rel) in
/-- **The bad event of experiment `1`** at a coupled entry: an inactive challenge with an entry of
user `1`, an invalid entry of user `1`, or refusal-or-public values that differ. -/
def bad₁ (ch : Ch) (x : EPair Pub BSig) : Prop :=
  (ch ∉ act ∧ x.2 ≠ none) ∨ (∃ p ∈ x.2, (stmtOf ch p.1, witOf true ch p.2) ∉ rel) ∨
    x.1.map Prod.fst ≠ x.2.map Prod.fst

omit [Fintype Ω] [Nonempty Ω] [Fintype Ch] [Fintype Pub] [Fintype BSig] [DecidableEq BSig] in
/-- **In experiment `0` the game selects as the hybrid with the first witnesses** unless the round's
coupled entry is bad for experiment `0`. -/
theorem entrySel_false_ne (T : CETable Ch Pub BSig Q) (j : Fin Q) (h : Ω)
    (hist : PubHist Pub Pf j)
    (hne : entrySel choice stmtOf witOf false (eside false T) j h hist ≠
      wiSelector (ehybrid (stmtOf := stmtOf) (witOf := witOf) (rel := rel) choice act T)
        (fun _ => false) j h hist) :
    bad₀ stmtOf witOf rel act (choice j h hist) (T j (choice j h hist)) := by
  classical
  set ch := choice j h hist with hch
  apply Classical.byContradiction
  intro hb
  apply hne
  simp only [bad₀, not_or, not_and, not_exists, not_not] at hb
  simp only [entrySel, wiSelector, ehybrid, eside, ← hch, Bool.false_eq_true, ite_false]
  generalize T j ch = x at hb ⊢
  obtain ⟨_ | p₀, x₁⟩ := x
  · simp only [Option.map_none]
    split_ifs <;> simp [ehybChoice]
  · by_cases hA : ch ∈ act
    · have h0 := hb.2 p₀ rfl
      simp [hA, ehybChoice, h0]
    · exact absurd (hb.1 hA) (by simp)

omit [Fintype Ω] [Nonempty Ω] [Fintype Ch] [Fintype Pub] [Fintype BSig] [DecidableEq BSig] in
/-- **In experiment `1` the game selects as the hybrid with the second witnesses** unless the round's
coupled entry is bad for experiment `1`. -/
theorem entrySel_true_ne (T : CETable Ch Pub BSig Q) (j : Fin Q) (h : Ω)
    (hist : PubHist Pub Pf j)
    (hne : entrySel choice stmtOf witOf true (eside true T) j h hist ≠
      wiSelector (ehybrid (stmtOf := stmtOf) (witOf := witOf) (rel := rel) choice act T)
        (fun _ => true) j h hist) :
    bad₁ stmtOf witOf rel act (choice j h hist) (T j (choice j h hist)) := by
  classical
  set ch := choice j h hist with hch
  apply Classical.byContradiction
  intro hb
  apply hne
  simp only [bad₁, not_or, not_and, not_exists, not_not] at hb
  obtain ⟨hb1, hb2, hb3⟩ := hb
  simp only [entrySel, wiSelector, ehybrid, eside, ← hch, ite_true]
  generalize T j ch = x at hb1 hb2 hb3 ⊢
  obtain ⟨x₀, x₁⟩ := x
  simp only at hb1 hb2 hb3 ⊢
  by_cases hA : ch ∈ act
  · simp only [hA, ite_true]
    rcases x₀ with _ | p₀ <;> rcases x₁ with _ | p₁
    · simp [ehybChoice]
    · simp at hb3
    · simp at hb3
    · simp only [Option.map_some, Option.some.injEq] at hb3
      have h1 := hb2 p₁ rfl
      by_cases h0 : (stmtOf ch p₀.1, witOf false ch p₀.2) ∈ rel
      · have h0' : (stmtOf ch p₁.1, witOf false ch p₀.2) ∈ rel := hb3 ▸ h0
        simp [ehybChoice, h0', hybWit₁, hb3, h1]
      · simp [ehybChoice, h0, h1]
  · simp only [hA, ite_false, Option.map_none]
    rw [hb1 hA]
    rfl

end Coupled

/-! ### The bad events and the bound -/

section Bound

variable {Ω Stmt Wit Pub Pf Ch BSig : Type} [Fintype Ω] [Nonempty Ω] [Fintype Ch] [DecidableEq Ch]
  [Fintype Pub] [DecidableEq Pub] [Fintype BSig] [DecidableEq BSig] {Q : ℕ}
  (L : Bool → Ch → PMF (Option (Pub × BSig))) (law : Ω → Stmt → Wit → PMF Pf) (pubOf : Stmt → Pub)
  (choice : (j : Fin Q) → Ω → PubHist Pub Pf j → Ch) (stmtOf : Ch → Pub → Stmt)
  (witOf : Bool → Ch → BSig → Wit)

/-- **The probability of the bad event `bad` of round `i`** at the coupled table `T`: in experiment
`b` before round `i`, the coupled entry of round `i`'s challenge is bad. -/
noncomputable def ebadProb (b : Bool) (bad : Ch → EPair Pub BSig → Prop)
    (T : CETable Ch Pub BSig Q) (i : Fin Q) : ℝ≥0∞ :=
  (pubRun law pubOf (entrySel choice stmtOf witOf b (eside b T)) i i.2.le).toOuterMeasure
    {s | bad (choice i s.1 s.2) (T i (choice i s.1 s.2))}

omit [Fintype Ch] [DecidableEq Ch] [Fintype Pub] [DecidableEq Pub] [Fintype BSig]
  [DecidableEq BSig] in
/-- The rounds before round `i` do not read row `i` of the table. -/
theorem pubRun_eside_update (b : Bool) (T : CETable Ch Pub BSig Q) (i : Fin Q)
    (r : Ch → EPair Pub BSig) :
    pubRun law pubOf (entrySel choice stmtOf witOf b (eside b (Function.update T i r))) i i.2.le =
      pubRun law pubOf (entrySel choice stmtOf witOf b (eside b T)) i i.2.le := by
  refine pubRun_congr _ _ fun i' hi' => ?_
  have hne : i' ≠ i := fun h => by rw [h] at hi'; exact lt_irrefl _ hi'
  funext h hist
  simp only [entrySel, eside, Function.update_of_ne hne]

/-- **The bad event of each round has probability at most `ε`** over the coupled table, when the
coupling of every challenge gives the bad event probability at most `ε`. -/
theorem sum_ecoupledLaw_mul_badProb_le (b : Bool) (bad : Ch → EPair Pub BSig → Prop) {ε : ℝ}
    (hε : ∀ ch, (ecoupling L ch).toOuterMeasure {x | bad ch x} ≤ ENNReal.ofReal ε) (i : Fin Q) :
    ∑ T, ecoupledLaw L T * ebadProb law pubOf choice stmtOf witOf b bad T i ≤
      ENNReal.ofReal ε := by
  classical
  let G : CETable Ch Pub BSig Q → (Ch → EPair Pub BSig) → ℝ≥0∞ := fun T row =>
    (pubRun law pubOf (entrySel choice stmtOf witOf b (eside b T)) i i.2.le).toOuterMeasure
      {s | bad (choice i s.1 s.2) (row (choice i s.1 s.2))}
  have hG : ∀ T r, G (Function.update T i r) = G T := fun T r => by
    funext row
    simp only [G, pubRun_eside_update]
  refine PMF.sum_pi_mul_apply_le _ i G hG fun T => ?_
  set μ := pubRun law pubOf (entrySel choice stmtOf witOf b (eside b T)) i i.2.le
  simp only [G, PMF.toOuterMeasure_apply]
  calc ∑ row, (PMF.pi fun ch => ecoupling L ch) row *
        ∑' s, {s : Ω × PubHist Pub Pf i | bad (choice i s.1 s.2) (row (choice i s.1 s.2))}.indicator
          μ s
      = ∑' s, μ s * ∑ row, (PMF.pi fun ch => ecoupling L ch) row *
            (if bad (choice i s.1 s.2) (row (choice i s.1 s.2)) then 1 else 0) := by
        rw [← tsum_fintype (L := SummationFilter.unconditional _)]
        simp_rw [← ENNReal.tsum_mul_left]
        rw [ENNReal.tsum_comm]
        refine tsum_congr fun s => ?_
        rw [tsum_fintype, Finset.mul_sum]
        refine Finset.sum_congr rfl fun row _ => ?_
        simp only [Set.indicator_apply, Set.mem_ofPred_eq]
        split_ifs <;> ring
    _ ≤ ∑' s, μ s * ENNReal.ofReal ε := by
        refine ENNReal.tsum_le_tsum fun s => mul_le_mul_right ?_ _
        rw [PMF.sum_pi_mul_apply_coord (fun ch => ecoupling L ch) (choice i s.1 s.2)
          (fun x => if bad (choice i s.1 s.2) x then 1 else 0)]
        have hm : ∑ x, ecoupling L (choice i s.1 s.2) x *
            (if bad (choice i s.1 s.2) x then 1 else 0) =
            (ecoupling L (choice i s.1 s.2)).toOuterMeasure {x | bad (choice i s.1 s.2) x} := by
          rw [PMF.toOuterMeasure_apply, tsum_fintype]
          refine Finset.sum_congr rfl fun x _ => ?_
          simp only [Set.indicator_apply, Set.mem_ofPred_eq]
          split_ifs <;> simp
        rw [hm]
        exact hε _
    _ = ENNReal.ofReal ε := by rw [ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]

omit [Fintype Ch] [DecidableEq Ch] [Fintype Pub] [DecidableEq Pub] [Fintype BSig]
  [DecidableEq BSig] in
/-- **An experiment and its hybrid at a coupled table are within the bad events of the rounds**:
if the selectors of experiment `b` and of the hybrid choices `F` with the witnesses of user `b` differ
only where the round's bad event holds, every event has probabilities within the sum over the rounds
of the bad events' probabilities. -/
theorem abs_erun_sub_hybrid_le (b : Bool) (T : CETable Ch Pub BSig Q)
    (F : (j : Fin Q) → Ω → PubHist Pub Pf j → Option (SPBCS.WIChoice Stmt Wit))
    (bad : Ch → EPair Pub BSig → Prop)
    (hsel : ∀ j h hist, entrySel choice stmtOf witOf b (eside b T) j h hist ≠
      wiSelector F (fun _ => b) j h hist → bad (choice j h hist) (T j (choice j h hist)))
    (U : Set (Ω × PubHist Pub Pf Q)) :
    |((pubRun law pubOf (entrySel choice stmtOf witOf b (eside b T)) Q le_rfl).toOuterMeasure
        U).toReal -
      ((pubRun law pubOf (wiSelector F fun _ => b) Q le_rfl).toOuterMeasure U).toReal| ≤
      ∑ i : Fin Q, (ebadProb law pubOf choice stmtOf witOf b bad T i).toReal := by
  refine (PMF.abs_toOuterMeasure_sub_le_tvDist _ _ _).trans ?_
  refine (tvDist_pubRun_le _ _ Q le_rfl).trans (Finset.sum_le_sum fun i _ => ?_)
  refine ENNReal.toReal_mono (ne_top_of_le_ne_top ENNReal.one_ne_top
    (PMF.toOuterMeasure_apply_le_one _ _)) (PMF.toOuterMeasure_mono _ ?_)
  intro s hs
  exact hsel _ s.1 s.2 hs.1

omit [DecidableEq Pub] [DecidableEq BSig] in
/-- The point mass at `none` gives the entries other than `none` probability `0`. -/
theorem toOuterMeasure_pure_none_ne :
    (PMF.pure (none : Option (Pub × BSig))).toOuterMeasure {e | e ≠ none} = 0 := by
  simp

/-- **The coupling bound for rounds with entries** (the anonymity argument of
`GordieHowe/Applications/Ring/Anonymity.lean`, `PubAnonAdversary.abs_condProb_sub_le`, for entries
that may be refusals): for a proof law with witness indistinguishability at error `wi` for `rel`
(`hwi`), the active challenges `act` (every other challenge is refused by both users, `hact`), an
`ε` bounding the distance of the two users' laws of the refusal-or-public value of every active
challenge (`hε`), and an `η` bounding the probability that a user's entry of an active challenge is
an invalid witness (`hη`), the experiments answering each round from user `0`'s and from user `1`'s
entries give every event of the oracle and the history probabilities within
`Q · (ε + 2η) + Q · wi (Q · C)` for any `C ≥ |act|`. -/
theorem abs_entryRounds_sub_le {rel : Set (Stmt × Wit)} {wi : ℕ → ℝ}
    (hwi : PubWI law pubOf rel wi) (act : Finset Ch) {C : ℕ} (hC : act.card ≤ C)
    (hact : ∀ ch ∉ act, ∀ b, L b ch = PMF.pure none) {ε η : ℝ} (hε0 : 0 ≤ ε) (hη0 : 0 ≤ η)
    (hε : ∀ ch ∈ act, PMF.tvDist ((L false ch).map (Option.map Prod.fst))
      ((L true ch).map (Option.map Prod.fst)) ≤ ε)
    (hη : ∀ ch ∈ act, ∀ b, (L b ch).toOuterMeasure
      {e | ∃ p ∈ e, (stmtOf ch p.1, witOf b ch p.2) ∉ rel} ≤ ENNReal.ofReal η)
    (U : Ω → PubHist Pub Pf Q → Prop) :
    |(((entryLaw L false).bind fun T =>
        pubRun law pubOf (entrySel choice stmtOf witOf false T) Q le_rfl).toOuterMeasure
          {s | U s.1 s.2}).toReal -
      (((entryLaw L true).bind fun T =>
        pubRun law pubOf (entrySel choice stmtOf witOf true T) Q le_rfl).toOuterMeasure
          {s | U s.1 s.2}).toReal| ≤ Q * (ε + 2 * η) + Q * wi (Q * C) := by
  classical
  set μ := ecoupledLaw (Q := Q) L
  let U' : Set (Ω × PubHist Pub Pf Q) := {s | U s.1 s.2}
  let f : Bool → CETable Ch Pub BSig Q → ℝ≥0∞ := fun b T =>
    (pubRun law pubOf (entrySel choice stmtOf witOf b (eside b T)) Q le_rfl).toOuterMeasure U'
  let F : CETable Ch Pub BSig Q → (j : Fin Q) → Ω → PubHist Pub Pf j →
      Option (SPBCS.WIChoice Stmt Wit) := fun T =>
    ehybrid (stmtOf := stmtOf) (witOf := witOf) (rel := rel) choice act T
  let g : Bool → CETable Ch Pub BSig Q → ℝ≥0∞ := fun b T =>
    (pubRun law pubOf (wiSelector (F T) fun _ => b) Q le_rfl).toOuterMeasure U'
  have hcond : ∀ b, ((entryLaw L b).bind fun T =>
      pubRun law pubOf (entrySel choice stmtOf witOf b T) Q le_rfl).toOuterMeasure U' =
        ∑ T, μ T * f b T := fun b => by
    rw [entryLaw_eq_map_eside L b, PMF.bind_map, PMF.toOuterMeasure_bind_apply, tsum_fintype]
    rfl
  change |(((entryLaw L false).bind fun T =>
    pubRun law pubOf (entrySel choice stmtOf witOf false T) Q le_rfl).toOuterMeasure U').toReal -
      (((entryLaw L true).bind fun T =>
    pubRun law pubOf (entrySel choice stmtOf witOf true T) Q le_rfl).toOuterMeasure U').toReal| ≤ _
  rw [hcond false, hcond true]
  have hle1 : ∀ p : PMF (Ω × PubHist Pub Pf Q), p.toOuterMeasure U' ≤ 1 := fun p =>
    PMF.toOuterMeasure_apply_le_one _ _
  have hz : ∀ ch ∉ act, ∀ b : Bool, (ecoupling L ch).toOuterMeasure
      {x | (if b then x.2 else x.1) ≠ none} = 0 := fun ch hch b => by
    cases b
    · rw [show {x : EPair Pub BSig | (if false = true then x.2 else x.1) ≠ none} =
        {x | x.1 ∈ {e | e ≠ none}} from rfl, ecoupling_fst_eq, hact ch hch false]
      exact toOuterMeasure_pure_none_ne
    · rw [show {x : EPair Pub BSig | (if true = true then x.2 else x.1) ≠ none} =
        {x | x.2 ∈ {e | e ≠ none}} from rfl, ecoupling_snd_eq, hact ch hch true]
      exact toOuterMeasure_pure_none_ne
  have hb₀ : ∀ ch, (ecoupling L ch).toOuterMeasure {x | bad₀ stmtOf witOf rel act ch x} ≤
      ENNReal.ofReal η := fun ch => by
    by_cases hch : ch ∈ act
    · have hs : {x | bad₀ stmtOf witOf rel act ch x} =
          {x : EPair Pub BSig | x.1 ∈ {e | ∃ p ∈ e, (stmtOf ch p.1, witOf false ch p.2) ∉ rel}} := by
        ext x
        simp [bad₀, hch]
      rw [hs, ecoupling_fst_eq]
      exact hη ch hch false
    · refine (PMF.toOuterMeasure_mono _ fun x hx => ?_).trans ((hz ch hch false).trans_le bot_le)
      rcases hx.1 with ⟨-, hx⟩ | ⟨p, hp, -⟩
      · exact hx
      · simp only [Bool.false_eq_true, ite_false, Set.mem_ofPred_eq]
        rw [hp]
        simp
  have hb₁ : ∀ ch, (ecoupling L ch).toOuterMeasure {x | bad₁ stmtOf witOf rel act ch x} ≤
      ENNReal.ofReal (η + ε) := fun ch => by
    by_cases hch : ch ∈ act
    · have hu : {x | bad₁ stmtOf witOf rel act ch x} =
          {x : EPair Pub BSig | x.2 ∈ {e | ∃ p ∈ e, (stmtOf ch p.1, witOf true ch p.2) ∉ rel}} ∪
            {x | x.1.map Prod.fst ≠ x.2.map Prod.fst} := by
        ext x
        simp [bad₁, hch]
      rw [hu, ENNReal.ofReal_add hη0 hε0]
      refine (MeasureTheory.measure_union_le _ _).trans (add_le_add ?_ ?_)
      · rw [ecoupling_snd_eq]
        exact hη ch hch true
      · rw [← ENNReal.ofReal_toReal (ne_top_of_le_ne_top ENNReal.one_ne_top
          (PMF.toOuterMeasure_apply_le_one _ _))]
        exact ENNReal.ofReal_le_ofReal ((toReal_ecoupling_ne_le L ch).trans (hε ch hch))
    · have hsub : {x | bad₁ stmtOf witOf rel act ch x} ⊆
          {x : EPair Pub BSig | (if false = true then x.2 else x.1) ≠ none} ∪
            {x | (if true = true then x.2 else x.1) ≠ none} := fun x hx => by
        simp only [Bool.false_eq_true, ite_false, ite_true, Set.mem_union, Set.mem_ofPred_eq]
        rcases hx with ⟨-, hx⟩ | ⟨p, hp, -⟩ | hx
        · exact Or.inr hx
        · right
          rw [hp]
          simp
        · by_contra hc
          push Not at hc
          exact hx (by rw [hc.1, hc.2])
      calc (ecoupling L ch).toOuterMeasure {x | bad₁ stmtOf witOf rel act ch x}
          ≤ (ecoupling L ch).toOuterMeasure
              ({x : EPair Pub BSig | (if false = true then x.2 else x.1) ≠ none} ∪
                {x | (if true = true then x.2 else x.1) ≠ none}) :=
            PMF.toOuterMeasure_mono _ fun x hx => hsub hx.1
        _ ≤ _ := MeasureTheory.measure_union_le _ _
        _ = 0 := by rw [hz ch hch false, hz ch hch true, add_zero]
        _ ≤ _ := bot_le
  have hwi' : ∀ T, (μ T).toReal * |(g false T).toReal - (g true T).toReal| ≤
      (μ T).toReal * (Q * wi (Q * C)) := fun T => by
    refine mul_le_mul_of_nonneg_left ?_ ENNReal.toReal_nonneg
    exact hwi Q (Q * C) (F T) (ehybridSet act T)
      ((card_ehybridSet_le act T).trans (Nat.mul_le_mul_left Q hC))
      (ehybridSet_admissible act T) (ehybrid_mem choice act T) U
  have hsum : ∀ (b : Bool) (bad : Ch → EPair Pub BSig → Prop) {ε' : ℝ}, 0 ≤ ε' →
      (∀ ch, (ecoupling L ch).toOuterMeasure {x | bad ch x} ≤ ENNReal.ofReal ε') →
      ∑ T, (μ T).toReal * ∑ i : Fin Q,
        (ebadProb law pubOf choice stmtOf witOf b bad T i).toReal ≤ Q * ε' :=
    fun b bad ε' hε' hb => by
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
      calc ∑ i : Fin Q, ∑ T, (μ T).toReal *
            (ebadProb law pubOf choice stmtOf witOf b bad T i).toReal
          ≤ ∑ _i : Fin Q, ε' := Finset.sum_le_sum fun i _ => by
            have h := sum_ecoupledLaw_mul_badProb_le L law pubOf choice stmtOf witOf b bad hb i
            have hne : ∀ T, μ T * ebadProb law pubOf choice stmtOf witOf b bad T i ≠ ⊤ :=
              fun T => ENNReal.mul_ne_top (μ.apply_ne_top T) (ne_top_of_le_ne_top
                ENNReal.one_ne_top (PMF.toOuterMeasure_apply_le_one _ _))
            simp_rw [← ENNReal.toReal_mul]
            rw [← ENNReal.toReal_sum fun T _ => hne T]
            exact ENNReal.toReal_le_of_le_ofReal hε' h
        _ = Q * ε' := by simp
  have hbad : ∀ b (bad : Ch → EPair Pub BSig → Prop), (∀ T j h hist,
      entrySel choice stmtOf witOf b (eside b T) j h hist ≠ wiSelector (F T) (fun _ => b) j h hist →
        bad (choice j h hist) (T j (choice j h hist))) →
      ∀ T, (μ T).toReal * |(f b T).toReal - (g b T).toReal| ≤
        (μ T).toReal * ∑ i : Fin Q, (ebadProb law pubOf choice stmtOf witOf b bad T i).toReal :=
    fun b bad hsel T => mul_le_mul_of_nonneg_left
      (abs_erun_sub_hybrid_le law pubOf choice stmtOf witOf b T (F T) bad (hsel T) U')
      ENNReal.toReal_nonneg
  have h0 := hbad false (bad₀ stmtOf witOf rel act) fun T j h hist hne =>
    entrySel_false_ne choice act T j h hist hne
  have h1 := hbad true (bad₁ stmtOf witOf rel act) fun T j h hist hne =>
    entrySel_true_ne choice act T j h hist hne
  calc |(∑ T, μ T * f false T).toReal - (∑ T, μ T * f true T).toReal|
      ≤ |(∑ T, μ T * f false T).toReal - (∑ T, μ T * g false T).toReal| +
          |(∑ T, μ T * g false T).toReal - (∑ T, μ T * g true T).toReal| +
          |(∑ T, μ T * g true T).toReal - (∑ T, μ T * f true T).toReal| := by
        have e1 := abs_sub_le (∑ T, μ T * f false T).toReal (∑ T, μ T * g false T).toReal
          (∑ T, μ T * f true T).toReal
        have e2 := abs_sub_le (∑ T, μ T * g false T).toReal (∑ T, μ T * g true T).toReal
          (∑ T, μ T * f true T).toReal
        linarith
    _ ≤ Q * η + Q * wi (Q * C) + Q * (η + ε) := by
        refine add_le_add (add_le_add ?_ ?_) ?_
        · refine ((PMF.abs_sum_mul_sub_sum_mul_le μ (fun _ => hle1 _) fun _ => hle1 _).trans
            (Finset.sum_le_sum fun T _ => h0 T)).trans ?_
          exact hsum false _ hη0 hb₀
        · refine ((PMF.abs_sum_mul_sub_sum_mul_le μ (fun _ => hle1 _) fun _ => hle1 _).trans
            (Finset.sum_le_sum fun T _ => hwi' T)).trans_eq ?_
          rw [← Finset.sum_mul, ← ENNReal.toReal_sum fun T _ => μ.apply_ne_top T, PMF.sum_coe,
            ENNReal.toReal_one, one_mul]
        · refine ((PMF.abs_sum_mul_sub_sum_mul_le μ (fun _ => hle1 _) fun _ => hle1 _).trans
            (Finset.sum_le_sum fun T _ => ?_)).trans (hsum true _ (add_nonneg hη0 hε0) hb₁)
          rw [abs_sub_comm]
          exact h1 T
    _ = Q * (ε + 2 * η) + Q * wi (Q * C) := by ring

end Bound

/-! ### Transfers of witness indistinguishability -/

section Transfer

variable {Ω Stmt Wit Pub Pf Pf' : Type} [Fintype Ω] [Nonempty Ω] {Q : ℕ}

/-- **A history with its proofs relabelled by `g`.** -/
def relabelHist (g : Pf → Pf') {j : ℕ} (hist : PubHist Pub Pf j) : PubHist Pub Pf' j :=
  fun i => (hist i).map (Prod.map id g)

/-- **Relabelling a history extended by one round** relabels the history and the round. -/
theorem relabelHist_snoc (g : Pf → Pf') {j : ℕ} (hist : PubHist Pub Pf j) (r : Option (Pub × Pf)) :
    relabelHist g (Fin.snoc (α := fun _ => Option (Pub × Pf)) hist r) =
      Fin.snoc (α := fun _ => Option (Pub × Pf')) (relabelHist g hist) (r.map (Prod.map id g)) := by
  funext i
  refine Fin.lastCases ?_ (fun i => ?_) i
  · simp [relabelHist]
  · simp [relabelHist]

omit [Fintype Ω] [Nonempty Ω] in
/-- **A round of a proof law relabelled by `g`** is the round of the proof law, its proof relabelled
by `g`. -/
theorem roundLaw_map_proof (law : Ω → Stmt → Wit → PMF Pf) (pubOf : Stmt → Pub) (g : Pf → Pf')
    (h : Ω) (o : Option (Stmt × Wit)) :
    roundLaw (fun h x w => (law h x w).map g) pubOf h o =
      (roundLaw law pubOf h o).map (Option.map (Prod.map id g)) := by
  cases o with
  | none => rw [roundLaw, roundLaw, PMF.pure_map]; rfl
  | some xw => simp only [roundLaw, PMF.map_comp]; rfl

/-- **Rounds whose proofs are relabelled by `g`** are the rounds of the original proofs, the selector
reading the relabelled history, with the history relabelled. -/
theorem pubRun_map_proof (law : Ω → Stmt → Wit → PMF Pf) (pubOf : Stmt → Pub) (g : Pf → Pf')
    (sel : Selector Ω Stmt Wit Pub Pf' Q) :
    ∀ j (hj : j ≤ Q), pubRun (fun h x w => (law h x w).map g) pubOf sel j hj =
      (pubRun law pubOf (fun j h hist => sel j h (relabelHist g hist)) j hj).map
        fun s => (s.1, relabelHist g s.2)
  | 0, _ => by
    simp only [pubRun, PMF.map_comp]
    congr 1
    funext h
    simp only [Function.comp_apply, Prod.mk.injEq, true_and]
    funext i
    exact i.elim0
  | j + 1, hj => by
    rw [pubRun, pubRun, pubRun_map_proof law pubOf g sel j (by omega), PMF.bind_map, PMF.map_bind]
    congr 1
    funext s
    simp only [Function.comp_apply, pubStep, roundLaw_map_proof, PMF.map_comp]
    congr 1
    funext r
    simp only [Function.comp_apply, relabelHist_snoc]

/-- **Witness indistinguishability survives relabelling the proofs.** -/
theorem PubWI.map_proof {law : Ω → Stmt → Wit → PMF Pf} {pubOf : Stmt → Pub}
    {rel : Set (Stmt × Wit)} {wi : ℕ → ℝ} (hwi : PubWI law pubOf rel wi) (g : Pf → Pf') :
    PubWI (fun h x w => (law h x w).map g) pubOf rel wi := by
  intro Q c F S hc hS hF U
  rw [pubRun_map_proof, pubRun_map_proof]
  simp only [gameAdvantage, PMF.toOuterMeasure_map_apply]
  exact hwi Q c (fun j h hist => F j h (relabelHist g hist)) S hc hS
    (fun j h hist x hx => hF _ _ _ x hx) fun h hist => U h (relabelHist g hist)

variable {Ω₁ Ω₂ : Type} [Fintype Ω₁] [Nonempty Ω₁] [Fintype Ω₂] [Nonempty Ω₂]

/-- **Rounds at an oracle that splits as a product**, the proofs reading only the second part: the
first part drawn uniformly, then the rounds at the second part with the selector at the first. -/
theorem pubRun_split (e : Ω ≃ Ω₂ × Ω₁) (law : Ω → Stmt → Wit → PMF Pf)
    (law₁ : Ω₁ → Stmt → Wit → PMF Pf) (hlaw : ∀ ω₂ h₁, law (e.symm (ω₂, h₁)) = law₁ h₁)
    (pubOf : Stmt → Pub) (sel : Selector Ω Stmt Wit Pub Pf Q) :
    ∀ j (hj : j ≤ Q), pubRun law pubOf sel j hj =
      (PMF.uniformOfFintype Ω₂).bind fun ω₂ =>
        (pubRun law₁ pubOf (fun j h₁ hist => sel j (e.symm (ω₂, h₁)) hist) j hj).map
          fun s => (e.symm (ω₂, s.1), s.2)
  | 0, _ => by
    simp only [pubRun]
    rw [← PMF.map_uniformOfFintype_equiv e.symm, PMF.uniformOfFintype_prod_eq_bind, PMF.map_bind,
      PMF.map_bind]
    congr 1
    funext ω₂
    simp only [PMF.map_comp]
    rfl
  | j + 1, hj => by
    rw [pubRun, pubRun_split e law law₁ hlaw pubOf sel j (by omega), PMF.bind_bind]
    congr 1
    funext ω₂
    simp only [pubRun]
    rw [PMF.bind_map, PMF.map_bind]
    congr 1
    funext s
    simp only [Function.comp_apply, pubStep, PMF.map_comp]
    have hr : roundLaw law pubOf (e.symm (ω₂, s.1)) = roundLaw law₁ pubOf s.1 := by
      funext o
      cases o with
      | none => rfl
      | some xw => simp only [roundLaw, hlaw]
    rw [hr]
    rfl

/-- **Witness indistinguishability survives an independent part of the oracle**: if the proofs read
only the second part of an oracle that splits as a product, witness indistinguishability at the
second part gives it at the whole oracle (the first part is independent randomness of the
adversary, fixed at its best value, `gameAdvantage_bind_le`). -/
theorem PubWI.of_split (e : Ω ≃ Ω₂ × Ω₁) {law : Ω → Stmt → Wit → PMF Pf}
    {law₁ : Ω₁ → Stmt → Wit → PMF Pf} (hlaw : ∀ ω₂ h₁, law (e.symm (ω₂, h₁)) = law₁ h₁)
    {pubOf : Stmt → Pub} {rel : Set (Stmt × Wit)} {wi : ℕ → ℝ} (hwi : PubWI law₁ pubOf rel wi) :
    PubWI law pubOf rel wi := by
  intro Q c F S hc hS hF U
  rw [pubRun_split e law law₁ hlaw, pubRun_split e law law₁ hlaw]
  refine gameAdvantage_bind_le _ _ _ _ fun ω₂ _ => ?_
  simp only [gameAdvantage, PMF.toOuterMeasure_map_apply]
  exact hwi Q c (fun j h₁ hist => F j (e.symm (ω₂, h₁)) hist) S hc hS
    (fun j h hist x hx => hF _ _ _ x hx) fun h₁ hist => U (e.symm (ω₂, h₁)) hist

end Transfer

/-! ### Laws that agree on the relation -/

section Congr

variable {Ω Stmt Wit Pub Pf : Type} [Fintype Ω] [Nonempty Ω] {Q : ℕ}

/-- **Rounds read the proof law only at the selected pairs**: two laws agreeing at every pair a
selector can select give the same rounds. -/
theorem pubRun_congr_law {law law' : Ω → Stmt → Wit → PMF Pf} (pubOf : Stmt → Pub)
    (sel : Selector Ω Stmt Wit Pub Pf Q)
    (h : ∀ j h₀ hist xw, sel j h₀ hist = some xw → ∀ h', law h' xw.1 xw.2 = law' h' xw.1 xw.2) :
    ∀ j (hj : j ≤ Q), pubRun law pubOf sel j hj = pubRun law' pubOf sel j hj
  | 0, _ => rfl
  | j + 1, hj => by
    rw [pubRun, pubRun, pubRun_congr_law pubOf sel h j (by omega)]
    congr 1
    funext s
    simp only [pubStep]
    congr 1
    cases hs : sel ⟨j, by omega⟩ s.1 s.2 with
    | none => rfl
    | some xw => simp only [roundLaw, h _ _ _ xw hs s.1]

/-- **Witness indistinguishability transfers between proof laws that agree on the relation.** -/
theorem PubWI.congr_rel {law law' : Ω → Stmt → Wit → PMF Pf} {pubOf : Stmt → Pub}
    {rel : Set (Stmt × Wit)} {wi : ℕ → ℝ} (hwi : PubWI law' pubOf rel wi)
    (h : ∀ h₀ x w, (x, w) ∈ rel → law h₀ x w = law' h₀ x w) : PubWI law pubOf rel wi := by
  intro Q c F S hc hS hF U
  have hcongr : ∀ bs : ℕ → Bool, pubRun law pubOf (wiSelector F bs) Q le_rfl =
      pubRun law' pubOf (wiSelector F bs) Q le_rfl := fun bs =>
    pubRun_congr_law pubOf _ (fun j h₀ hist xw hxw h' => by
      simp only [wiSelector, Option.map_eq_some_iff] at hxw
      obtain ⟨x, hx, rfl⟩ := hxw
      have hm := hS x (hF _ _ _ x hx)
      split_ifs
      · exact h h' _ _ hm.2
      · exact h h' _ _ hm.1) Q le_rfl
  rw [hcongr, hcongr]
  exact hwi Q c F S hc hS hF U

/-- **Witness indistinguishability for the empty relation** at every nonnegative error: no
admissible choice exists, so every round is refused in both experiments. -/
theorem PubWI.of_forall_not_mem {law : Ω → Stmt → Wit → PMF Pf} {pubOf : Stmt → Pub}
    {rel : Set (Stmt × Wit)} {wi : ℕ → ℝ} (hrel : ∀ p, p ∉ rel) (hwi0 : ∀ c, 0 ≤ wi c) :
    PubWI law pubOf rel wi := by
  intro Q c F S _ hS hF U
  have hnone : ∀ j h hist, F j h hist = none := fun j h hist => by
    cases hx : F j h hist with
    | none => rfl
    | some x => exact absurd (hS x (hF _ _ _ x hx)).1 (hrel _)
  have hsel : wiSelector F (fun _ => false) = wiSelector F fun _ => true := by
    funext j h hist
    simp [wiSelector, hnone]
  rw [hsel]
  unfold gameAdvantage advantage
  rw [sub_self, abs_zero]
  exact mul_nonneg (Nat.cast_nonneg _) (hwi0 c)

end Congr

end GordieHowe.Ring
