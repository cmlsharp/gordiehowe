-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Model.Quantum.Interactive.PureRun
public import GordieHowe.Model.Quantum.Interactive.Bridge

@[expose] public section

/-!
# A classical oracle program as an interactive adversary

`OracleProg.toIAlg p q pad φ`: an interactive adversary of the model (`IAlg`) that runs the
classical oracle program `p` (at most `q` queries against every oracle) with basis-state queries,
after one query to the oracle on a vector `φ` of a kept pair of registers `X × Y`, whose result it
keeps in its workspace. With `φ` a basis vector this is the plain compilation of `p`, with one
extra classical query.

Its registers: a table of `q` answers, the kept pair, a request register (never used), a response
register (blank), and one query pair. Its schedule has `q + 1` query slots and no request slot. Its
Kraus maps are basis permutations:

- before slot `0`, the identity (the query pair holds `φ`);
- before slot `1`, the exchange of the query pair with the kept pair (the kept pair then holds
  `φ` queried once, the query pair the first query of `p`);
- before slot `i + 2` and after the last slot, the answer of query `i` moved into entry `i` of the
  table and the query input advanced to the next query of `p` on the answers so far
  (`OracleProg.next`, padded with `pad` once `p` has returned).

The output is the result of `p` fed the table (the result of `p` against the zero oracle if `p`
wants more answers than the table holds).

- `OracleProg.pureRun_toIAlg`: the pure run with the oracle `H` ends with the table holding the
  answers of the padded queries of `p` and the kept pair holding `φ` queried once
  (`OracleProg.progVec`).
-/

open Finset Matrix
open scoped BigOperators ENNReal ComplexOrder

namespace GordieHowe.Quantum

/-- **A mixed state from a unit vector**: the projector onto it. -/
noncomputable def MState.ofVec {ι : Type*} [Fintype ι] (ψ : QState ι) (hψ : ‖ψ‖ = 1) :
    MState ι where
  mat := proj ψ
  posSemidef := posSemidef_vecMulVec_self_star _
  trace_eq_one := by
    rw [proj, trace_vecMulVec]
    have h := EuclideanSpace.norm_sq_eq ψ
    rw [hψ, one_pow] at h
    simp only [dotProduct, RCLike.star_def]
    have h2 : ∀ i, ψ i * (starRingEnd ℂ) (ψ i) = ((‖ψ i‖ ^ 2 : ℝ) : ℂ) := fun i => by
      rw [Complex.mul_conj', Complex.ofReal_pow]
    simp only [h2, ← Complex.ofReal_sum, ← h, Complex.ofReal_one]

theorem matApply_permMat {ι : Type*} [Fintype ι] [DecidableEq ι] (π : Equiv.Perm ι)
    (ψ : QState ι) :
    matApply ((1 : Matrix ι ι ℂ).submatrix π.symm (Equiv.refl ι)) ψ = permOp π ψ := by
  ext i
  rw [matApply_apply, permOp_apply]
  simp [one_apply]

namespace IAlg

variable {X Y Req Resp O : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
  [Fintype Req] [DecidableEq Req] [Fintype Resp] [DecidableEq Resp] [AddGroup Y]
  (A : IAlg X Y Req Resp O)

/-- **The pure run with permutation operators** is the alternation of the permutations and the
queries. -/
theorem pureRun_of_perm (π : StepIdx A.slots A.post → Equiv.Perm (DReg A.W A.width X Y Req Resp))
    (H : X → Y) (ψ : QState (DReg A.W A.width X Y Req Resp)) :
    A.pureRun (fun k => (1 : Matrix _ _ ℂ).submatrix (π k).symm (Equiv.refl _)) H ψ =
      permOp (π lastStep) ((List.finRange A.post).foldl
        (fun v b => permOp (queryPerm H) (permOp (π (postStep b)) v))
        ((List.finRange A.slots).foldl
          (fun v k => permOp (queryPerm H) (permOp (π (slotStep k)) v)) ψ)) := by
  have h1 : A.pureSlot (fun k => (1 : Matrix _ _ ℂ).submatrix (π k).symm (Equiv.refl _)) H =
      fun v k => permOp (queryPerm H) (permOp (π (slotStep k)) v) := by
    funext v k
    rw [pureSlot, matApply_permMat]
  have h2 : A.purePost (fun k => (1 : Matrix _ _ ℂ).submatrix (π k).symm (Equiv.refl _)) H =
      fun v b => permOp (queryPerm H) (permOp (π (postStep b)) v) := by
    funext v b
    rw [purePost, matApply_permMat]
  rw [pureRun, h1, h2, matApply_permMat]

end IAlg

namespace OracleProg

open GordieHowe.OracleProg

variable {X Y Req Resp O : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
  [Fintype Req] [DecidableEq Req] [Fintype Resp] [DecidableEq Resp] [AddGroup Y]

/-- The workspace of the compiled program: the table of answers and the kept pair. -/
abbrev ProgW (X Y : Type) (q : ℕ) : Type := (Fin q → Y) × (X × Y)

/-- The registers of the compiled program. -/
abbrev ProgReg (X Y Req Resp : Type) (q : ℕ) : Type := DReg (ProgW X Y q) 1 X Y Req Resp

/-- Decidable equality of the registers (one instance search for the whole product exceeds the
default size limit of instance search). -/
instance instDecidableEqProgReg (q : ℕ) : DecidableEq (ProgReg X Y Req Resp q) :=
  fun a b => instDecidableEqProd a b

variable (p : OracleProg X Y O) (q : ℕ) (pad : X)

/-- The first `j` entries of a table, as a list (entries past `q` read as `0`). -/
def answers (T : Fin q → Y) (j : ℕ) : List Y :=
  (List.range j).map fun i => if h : i < q then T ⟨i, h⟩ else 0

/-- The query of `p` after the first `j` answers of the table. -/
def nextQ (T : Fin q → Y) (j : ℕ) : X :=
  p.next pad (answers q T j)

/-- Move the answer of the query pair into entry `i` of the table (an exchange). -/
def recordAns (i : Fin q) : Equiv.Perm (ProgReg X Y Req Resp q) :=
  Function.Involutive.toPerm (fun r => (((Function.update r.1.1.1 i (r.2 0).2, r.1.1.2), r.1.2),
      fun _ => ((r.2 0).1, r.1.1.1 i))) fun r => by
    obtain ⟨⟨⟨T, k⟩, rq⟩, qp⟩ := r
    refine Prod.ext (Prod.ext (Prod.ext ?_ rfl) rfl) (funext fun j => ?_)
    · funext l
      by_cases hl : l = i
      · subst hl
        simp
      · simp [Function.update_of_ne hl]
    · simp [Fin.fin_one_eq_zero j]

/-- Advance the query input from the query after `i` answers to the query after `i + 1` answers
of the table (an exchange of the two inputs, controlled by the table). -/
def advance (i : Fin q) : Equiv.Perm (ProgReg X Y Req Resp q) :=
  Function.Involutive.toPerm (fun r => (r.1, fun _ =>
      (Equiv.swap (nextQ p q pad r.1.1.1 i) (nextQ p q pad r.1.1.1 ((i : ℕ) + 1)) (r.2 0).1,
        (r.2 0).2))) fun r => by
    obtain ⟨⟨⟨T, k⟩, rq⟩, qp⟩ := r
    refine Prod.ext rfl (funext fun j => ?_)
    simp [Fin.fin_one_eq_zero j]

/-- Exchange the query pair with the kept pair. -/
def keepSwap : Equiv.Perm (ProgReg X Y Req Resp q) :=
  Function.Involutive.toPerm (fun r => (((r.1.1.1, r.2 0), r.1.2), fun _ => r.1.1.2)) fun r => by
    obtain ⟨⟨⟨T, k⟩, rq⟩, qp⟩ := r
    refine Prod.ext rfl (funext fun j => ?_)
    simp [Fin.fin_one_eq_zero j]

/-- **The permutation of the Kraus map number `k`**: the identity, the exchange with the kept
pair, then the recording of answer `k - 2` and the next query. -/
def stepPerm (k : StepIdx (q + 1) 0) : Equiv.Perm (ProgReg X Y Req Resp q) :=
  if h : (k : ℕ) < 2 then (if (k : ℕ) = 0 then Equiv.refl _ else keepSwap q)
  else (recordAns q ⟨k - 2, by have := k.2; omega⟩).trans
    (advance p q pad ⟨k - 2, by have := k.2; omega⟩)

variable [Nonempty Req]

/-- The blank request register. -/
noncomputable def req₀ : Req := Classical.arbitrary Req

/-- The initial vector: the table blank, the kept pair at the first query of `p` with answer `0`,
the request and response registers blank, the query pair holding `φ`. -/
noncomputable def initVec (φ : QState (X × Y)) : QState (ProgReg X Y Req Resp q) :=
  WithLp.toLp 2 fun r => if r.1.1.1 = 0 ∧ r.1.1.2 = (p.next pad [], 0) ∧ r.1.2 = (req₀, none) then
    φ (r.2 0) else 0

theorem norm_initVec (φ : QState (X × Y)) (hφ : ‖φ‖ = 1) :
    ‖initVec (Req := Req) (Resp := Resp) p q pad φ‖ = 1 := by
  have h : ‖initVec (Req := Req) (Resp := Resp) p q pad φ‖ ^ 2 = ‖φ‖ ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq]
    let e : ProgReg X Y Req Resp q ≃ (ProgW X Y q × Req × Option Resp) × (X × Y) :=
      { toFun := fun r => (r.1, r.2 0)
        invFun := fun s => (s.1, fun _ => s.2)
        left_inv := fun r => Prod.ext rfl (funext fun j => by simp [Fin.fin_one_eq_zero j])
        right_inv := fun s => rfl }
    rw [← e.symm.sum_comp, Fintype.sum_prod_type]
    rw [Finset.sum_eq_single ((0, (p.next pad [], 0)), req₀, none)]
    · simp [initVec, e]
    · intro b _ hb
      refine sum_eq_zero fun x _ => ?_
      have : ¬ (b.1.1 = 0 ∧ b.1.2 = (p.next pad [], 0) ∧ b.2 = (req₀, none)) := fun h =>
        hb (Prod.ext (Prod.ext h.1 h.2.1) h.2.2)
      simp [initVec, e, this]
    · simp
  rw [hφ, one_pow] at h
  exact (pow_left_inj₀ (norm_nonneg _) zero_le_one two_ne_zero).1 (by rw [h, one_pow])

/-- **The compiled program** (`OracleProg.toIAlg`, module docstring): `q + 1` query slots, no
request, permutation Kraus maps, output the result of `p` on the table.

Running time: `q + 1` queries; each Kraus map moves one answer and computes one query of `p`
(`OracleProg.next` on at most `q` answers); polynomial when `p` is. This running time is argued
here, not proved in Lean. -/
noncomputable abbrev toIAlg (φ : QState (X × Y)) (hφ : ‖φ‖ = 1) :
    IAlg X Y Req Resp O where
  W := ProgW X Y q
  width := 1
  width_pos := Nat.one_pos
  slots := q + 1
  post := 0
  sched _ := false
  R := Unit
  init := MState.ofVec (initVec p q pad φ) (norm_initVec p q pad φ hφ)
  step k := KrausMap.ofPerm (stepPerm (Req := Req) (Resp := Resp) p q pad k)
  out w := (OracleProgAns.result p (answers q w.1 q)).getD (p.run 0)

/-- **The compiled program is trace preserving**: its Kraus maps are basis permutations. -/
theorem toIAlg_tracePreserving (φ : QState (X × Y)) (hφ : ‖φ‖ = 1) :
    (toIAlg (Req := Req) (Resp := Resp) p q pad φ hφ).TracePreserving :=
  fun k => KrausMap.tp_ofPerm _

/-! ### The pure run -/

theorem permOp_trans {ι : Type*} [Fintype ι] (π σ : Equiv.Perm ι) (v : QState ι) :
    permOp (π.trans σ) v = permOp σ (permOp π v) := by
  ext r
  rfl

section Run

variable (H : X → Y) (φ : QState (X × Y))

/-- The padded query `j` of `p` against `H`. -/
def xs (j : ℕ) : X := p.paddedTrace H pad j

/-- The table holding the answers of `H` to the first `j` padded queries. -/
def tab (j : ℕ) : Fin q → Y := fun i => if (i : ℕ) < j then H (p.paddedTrace H pad i) else 0

/-- **The vector of the run**: the table `T`, the kept pair holding `φ` queried once to `H`, the
request and response registers blank, the query pair at the basis state `qp`. -/
noncomputable def progVec (T : Fin q → Y) (qp : X × Y) : QState (ProgReg X Y Req Resp q) :=
  WithLp.toLp 2 fun r => if r.1.1.1 = T ∧ r.1.2 = (req₀, none) ∧ r.2 0 = qp then
    φ (r.1.1.2.1, r.1.1.2.2 - H r.1.1.2.1) else 0

theorem progVec_apply (T : Fin q → Y) (qp : X × Y) (r : ProgReg X Y Req Resp q) :
    progVec q H φ T qp r = if r.1.1.1 = T ∧ r.1.2 = (req₀, none) ∧ r.2 0 = qp then
      φ (r.1.1.2.1, r.1.1.2.2 - H r.1.1.2.1) else 0 := rfl

theorem fin_one_fun_eq {α : Type*} {f g : Fin 1 → α} : f = g ↔ f 0 = g 0 :=
  ⟨fun h => h ▸ rfl, fun h => funext fun j => by rw [Fin.fin_one_eq_zero j, h]⟩

theorem permOp_queryPerm_progVec (T : Fin q → Y) (x : X) (y : Y) :
    permOp (queryPerm H) (progVec (Req := Req) (Resp := Resp) q H φ T (x, y)) =
      progVec q H φ T (x, y + H x) := by
  ext r
  rw [permOp_apply, progVec_apply, progVec_apply]
  have h : ((queryPerm H).symm r).2 0 = ((r.2 0).1, (r.2 0).2 - H (r.2 0).1) := by
    simp [queryPerm, sub_eq_add_neg]
  have h1 : ((queryPerm H).symm r).1 = r.1 := rfl
  rw [h, h1]
  congr 1
  apply propext
  constructor
  · rintro ⟨h1, h2, h3⟩
    refine ⟨h1, h2, ?_⟩
    rw [Prod.mk.injEq] at h3
    rw [Prod.ext_iff]
    exact ⟨h3.1, by rw [← h3.2, h3.1, sub_add_cancel]⟩
  · rintro ⟨h1, h2, h3⟩
    refine ⟨h1, h2, ?_⟩
    rw [h3, add_sub_cancel_right]

theorem permOp_recordAns_progVec (i : Fin q) (T : Fin q → Y) (x : X) (y : Y) :
    permOp (recordAns (Req := Req) (Resp := Resp) q i) (progVec q H φ T (x, y)) =
      progVec q H φ (Function.update T i y) (x, T i) := by
  ext r
  obtain ⟨⟨⟨T', k⟩, rq⟩, qp'⟩ := r
  have hs : (recordAns (Req := Req) (Resp := Resp) q i).symm (((T', k), rq), qp') =
      (((Function.update T' i (qp' 0).2, k), rq), fun _ => ((qp' 0).1, T' i)) := rfl
  rw [permOp_apply, hs, progVec_apply, progVec_apply]
  dsimp only
  congr 1
  apply propext
  constructor
  · rintro ⟨h1, h2, h3⟩
    rw [Prod.mk.injEq] at h3
    refine ⟨?_, h2, ?_⟩
    · rw [← h1, Function.update_idem, ← h3.2, Function.update_eq_self]
    · rw [Prod.ext_iff]
      refine ⟨h3.1, ?_⟩
      rw [← h1, Function.update_self]
  · rintro ⟨h1, h2, h3⟩
    refine ⟨?_, h2, ?_⟩
    · rw [h1, h3, Function.update_idem, Function.update_eq_self]
    · rw [h1, h3, Function.update_self]

theorem permOp_advance_progVec (i : Fin q) (T : Fin q → Y) (x : X) (y : Y) :
    permOp (advance (Req := Req) (Resp := Resp) p q pad i) (progVec q H φ T (x, y)) =
      progVec q H φ T (Equiv.swap (nextQ p q pad T i) (nextQ p q pad T ((i : ℕ) + 1)) x, y) := by
  ext r
  obtain ⟨⟨⟨T', k⟩, rq⟩, qp'⟩ := r
  have hs : (advance (Req := Req) (Resp := Resp) p q pad i).symm (((T', k), rq), qp') =
      (((T', k), rq), fun _ => (Equiv.swap (nextQ p q pad T' i) (nextQ p q pad T' ((i : ℕ) + 1))
        (qp' 0).1, (qp' 0).2)) := rfl
  rw [permOp_apply, hs, progVec_apply, progVec_apply]
  dsimp only
  congr 1
  apply propext
  constructor
  · rintro ⟨h1, h2, h3⟩
    refine ⟨h1, h2, ?_⟩
    subst h1
    rw [Prod.mk.injEq] at h3
    rw [Prod.ext_iff]
    exact ⟨by rw [← h3.1, Equiv.swap_apply_self], h3.2⟩
  · rintro ⟨h1, h2, h3⟩
    refine ⟨h1, h2, ?_⟩
    subst h1
    rw [h3, Equiv.swap_apply_self]

omit [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y] in
theorem answers_tab {m j : ℕ} (hjm : j ≤ m) (hm : m ≤ q) :
    answers q (tab p q pad H m) j = (List.range j).map fun i => H (xs p pad H i) := by
  refine List.map_congr_left fun i hi => ?_
  rw [List.mem_range] at hi
  have hiq : i < q := by omega
  have hi' : i < m := by omega
  simp only [hiq, ↓reduceDIte, tab, xs, hi', ↓reduceIte]

omit [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y] in
theorem nextQ_tab {m j : ℕ} (hjm : j ≤ m) (hm : m ≤ q) :
    nextQ p q pad (tab p q pad H m) j = xs p pad H j := by
  rw [nextQ, answers_tab p q pad H hjm hm, xs, paddedTrace_eq_next]
  rfl

omit [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y] in
theorem tab_zero : tab p q pad H 0 = 0 := by
  funext i
  simp [tab]

omit [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y] [AddGroup Y] in
theorem xs_zero : xs p pad H 0 = p.next pad [] := by
  rw [xs, paddedTrace_eq_next]
  rfl

omit [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y] in
theorem update_tab {j : ℕ} (hj : j < q) :
    Function.update (tab p q pad H j) ⟨j, hj⟩ (H (xs p pad H j)) = tab p q pad H (j + 1) := by
  funext i
  by_cases hi : i = ⟨j, hj⟩
  · subst hi
    simp [tab, xs]
  · rw [Function.update_of_ne hi]
    have : (i : ℕ) ≠ j := fun h => hi (Fin.ext h)
    simp only [tab]
    by_cases h : (i : ℕ) < j
    · have h' : (i : ℕ) < j + 1 := by omega
      simp only [h, h', ↓reduceIte]
    · have h' : ¬ (i : ℕ) < j + 1 := by omega
      simp only [h, h', ↓reduceIte]

omit [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y] in
theorem tab_self {j : ℕ} (hj : j < q) : tab p q pad H j ⟨j, hj⟩ = 0 := by
  simp [tab]

omit [Fintype X] [Fintype Y] [DecidableEq Y] [Fintype Req] [DecidableEq Req] [Fintype Resp]
  [DecidableEq Resp] [Nonempty Req] in
theorem stepPerm_zero : stepPerm (Req := Req) (Resp := Resp) p q pad 0 = Equiv.refl _ := by
  simp [stepPerm]

omit [Fintype X] [Fintype Y] [DecidableEq Y] [Fintype Req] [DecidableEq Req] [Fintype Resp]
  [DecidableEq Resp] [Nonempty Req] in
theorem stepPerm_one {k : StepIdx (q + 1) 0} (hk : (k : ℕ) = 1) :
    stepPerm (Req := Req) (Resp := Resp) p q pad k = keepSwap q := by
  simp [stepPerm, hk]

omit [Fintype X] [Fintype Y] [DecidableEq Y] [Fintype Req] [DecidableEq Req] [Fintype Resp]
  [DecidableEq Resp] [Nonempty Req] in
theorem stepPerm_add_two {k : StepIdx (q + 1) 0} {j : ℕ} (hk : (k : ℕ) = j + 2) (hj : j < q) :
    stepPerm (Req := Req) (Resp := Resp) p q pad k =
      (recordAns q ⟨j, hj⟩).trans (advance p q pad ⟨j, hj⟩) := by
  have h2 : ¬ (k : ℕ) < 2 := by omega
  simp only [stepPerm, h2, ↓reduceDIte]
  have : (⟨(k : ℕ) - 2, by omega⟩ : Fin q) = ⟨j, hj⟩ := Fin.ext (by simp only; omega)
  rw [this]

/-- **One recording step**: the answer to query `j` moves into the table and the query pair
advances to query `j + 1` with a blank answer. -/
theorem permOp_stepPerm_progVec {k : StepIdx (q + 1) 0} {j : ℕ} (hk : (k : ℕ) = j + 2)
    (hj : j < q) :
    permOp (stepPerm (Req := Req) (Resp := Resp) p q pad k)
      (progVec q H φ (tab p q pad H j) (xs p pad H j, H (xs p pad H j))) =
      progVec q H φ (tab p q pad H (j + 1)) (xs p pad H (j + 1), 0) := by
  rw [stepPerm_add_two p q pad hk hj, permOp_trans, permOp_recordAns_progVec,
    permOp_advance_progVec, update_tab p q pad H hj, tab_self p q pad H hj]
  simp only
  rw [nextQ_tab p q pad H (Nat.le_succ j) hj, nextQ_tab p q pad H le_rfl hj, Equiv.swap_apply_left]

/-- The vector after the first slot: the query pair holds `φ` queried once. -/
noncomputable def firstVec : QState (ProgReg X Y Req Resp q) :=
  WithLp.toLp 2 fun r => if r.1.1.1 = 0 ∧ r.1.1.2 = (p.next pad [], 0) ∧ r.1.2 = (req₀, none) then
    φ ((r.2 0).1, (r.2 0).2 - H (r.2 0).1) else 0

theorem permOp_queryPerm_initVec :
    permOp (queryPerm H) (initVec (Req := Req) (Resp := Resp) p q pad φ) =
      firstVec p q pad H φ := by
  ext r
  have h : ((queryPerm H).symm r).2 0 = ((r.2 0).1, (r.2 0).2 - H (r.2 0).1) := by
    simp [queryPerm, sub_eq_add_neg]
  have h1 : ((queryPerm H).symm r).1 = r.1 := rfl
  rw [permOp_apply, initVec, firstVec, PiLp.toLp_apply, PiLp.toLp_apply, h, h1]

theorem permOp_keepSwap_firstVec :
    permOp (keepSwap (Req := Req) (Resp := Resp) q) (firstVec p q pad H φ) =
      progVec q H φ 0 (p.next pad [], 0) := by
  ext r
  obtain ⟨⟨⟨T', k⟩, rq⟩, qp'⟩ := r
  have hs : (keepSwap (Req := Req) (Resp := Resp) q).symm (((T', k), rq), qp') =
      (((T', qp' 0), rq), fun _ => k) := rfl
  rw [permOp_apply, hs, progVec_apply]
  simp only [firstVec, PiLp.toLp_apply]
  congr 1
  apply propext
  constructor
  · rintro ⟨h1, h2, h3⟩
    exact ⟨h1, h3, h2⟩
  · rintro ⟨h1, h2, h3⟩
    exact ⟨h1, h3, h2⟩

/-- The vectors of the run after each slot (`m` slots done). -/
noncomputable def runVec : ℕ → QState (ProgReg X Y Req Resp q)
  | 0 => initVec p q pad φ
  | 1 => firstVec p q pad H φ
  | j + 2 => progVec q H φ (tab p q pad H j) (xs p pad H j, H (xs p pad H j))

theorem foldl_finRange_eq_range {α : Type*} {n : ℕ} (f : α → Fin n → α) (g : α → ℕ → α)
    (hfg : ∀ a (k : Fin n), f a k = g a k) (a : α) :
    (List.finRange n).foldl f a = (List.range n).foldl g a := by
  have hmap : (List.finRange n).map Fin.val = List.range n :=
    List.ext_getElem (by simp) fun i h1 h2 => by simp
  rw [← hmap, List.foldl_map]
  congr 1
  funext a k
  exact hfg a k

/-- One slot of the run: the Kraus map number `j`, then the query. -/
noncomputable def slotFun (v : QState (ProgReg X Y Req Resp q)) (j : ℕ) :
    QState (ProgReg X Y Req Resp q) :=
  if h : j < q + 1 then
    permOp (queryPerm H) (permOp (stepPerm p q pad ⟨j, by omega⟩) v)
  else v

theorem foldl_slotFun {m : ℕ} (hm : m ≤ q + 1) :
    (List.range m).foldl (slotFun (Req := Req) (Resp := Resp) p q pad H) (initVec p q pad φ) =
      runVec p q pad H φ m := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [List.range_succ, List.foldl_append, ih (by omega), List.foldl_cons, List.foldl_nil,
      slotFun]
    have hm' : m < q + 1 := by omega
    simp only [hm', ↓reduceDIte]
    match m, hm with
    | 0, _ =>
      rw [show (⟨0, by omega⟩ : StepIdx (q + 1) 0) = 0 from rfl, stepPerm_zero]
      exact permOp_queryPerm_initVec p q pad H φ
    | 1, _ =>
      rw [stepPerm_one p q pad rfl]
      show permOp (queryPerm H) (permOp (keepSwap q) (firstVec p q pad H φ)) = _
      rw [permOp_keepSwap_firstVec, permOp_queryPerm_progVec, zero_add, ← tab_zero p q pad H,
        ← xs_zero p pad H]
      rfl
    | j + 2, hm =>
      show permOp (queryPerm H) (permOp (stepPerm p q pad ⟨j + 2, by omega⟩)
        (progVec q H φ (tab p q pad H j) (xs p pad H j, H (xs p pad H j)))) = _
      rw [permOp_stepPerm_progVec p q pad H φ rfl (by omega), permOp_queryPerm_progVec, zero_add]
      rfl

/-- **The pure run of the compiled program** with the oracle `H`: the table holds the answers of
`H` to the `q` padded queries of `p`, the kept pair holds `φ` queried once, the query pair holds
the padded query `q` with a blank answer. -/
theorem pureRun_toIAlg (hφ : ‖φ‖ = 1) :
    (toIAlg (Req := Req) (Resp := Resp) p q pad φ hφ).pureRun
      (fun k => (1 : Matrix _ _ ℂ).submatrix (stepPerm p q pad k).symm (Equiv.refl _)) H
      (initVec p q pad φ) = progVec q H φ (tab p q pad H q) (xs p pad H q, 0) := by
  rw [IAlg.pureRun_of_perm]
  show permOp (stepPerm p q pad ⟨q + 1 + 0, by omega⟩) (List.foldl _
    (List.foldl (fun v (k : Fin (q + 1)) => permOp (queryPerm H)
      (permOp (stepPerm p q pad ⟨k, by omega⟩) v)) (initVec p q pad φ) (List.finRange (q + 1)))
    (List.finRange 0)) = _
  rw [List.finRange_zero, List.foldl_nil,
    foldl_finRange_eq_range _ (slotFun p q pad H)
      (fun v k => by simp only [slotFun, k.2, ↓reduceDIte]),
    foldl_slotFun p q pad H φ le_rfl]
  rcases q with _ | j
  · rw [stepPerm_one p 0 pad rfl]
    show permOp (keepSwap 0) (firstVec p 0 pad H φ) = _
    rw [permOp_keepSwap_firstVec, ← tab_zero p 0 pad H, ← xs_zero p pad H]
  · exact permOp_stepPerm_progVec p (j + 1) pad H φ (k := ⟨j + 1 + 1 + 0, by omega⟩) rfl (by omega)

end Run

/-! ### The output law -/

omit [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y] [AddGroup Y] in
theorem trace_map_eq_range (H : X → Y) :
    (p.trace H).map H = (List.range (p.trace H).length).map fun i => H (xs p pad H i) := by
  refine List.ext_getElem (by simp) fun i h1 h2 => ?_
  simp only [List.getElem_map, List.getElem_range, xs, paddedTrace]
  rw [List.length_map] at h1
  rw [List.getElem?_eq_getElem h1, Option.getD_some]

omit [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y] in
theorem result_answers_tab (H : X → Y) (hq : (p.trace H).length ≤ q) :
    OracleProgAns.result p (answers q (tab p q pad H q) q) = some (p.run H) := by
  refine OracleProgAns.result_of_prefix H p ?_
  rw [answers_tab p q pad H le_rfl le_rfl, trace_map_eq_range p pad H]
  obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le hq
  rw [hd, List.range_add, List.map_append]
  exact List.prefix_append _ _

/-- The registers on which the run vector is nonzero hold the table of answers. -/
theorem progVec_ne_zero {H : X → Y} {φ : QState (X × Y)} {T : Fin q → Y} {qp : X × Y}
    {r : ProgReg X Y Req Resp q} (h : progVec q H φ T qp r ≠ 0) : r.1.1.1 = T := by
  rw [progVec_apply] at h
  by_contra hT
  simp [hT] at h

omit [DecidableEq X] [Fintype Y] in
theorem norm_permOp_eq {ι : Type*} [Fintype ι] (π : Equiv.Perm ι) (v : QState ι) :
    ‖permOp π v‖ = ‖v‖ :=
  (permOp π).norm_map v

end OracleProg

namespace IAlg

variable {X Y Req Resp O : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
  [Fintype Req] [DecidableEq Req] [Fintype Resp] [DecidableEq Resp] [AddGroup Y]
  (A : IAlg X Y Req Resp O)

end IAlg

namespace OracleProg

open GordieHowe.OracleProg

variable {X Y Req Resp O : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
  [Fintype Req] [DecidableEq Req] [Fintype Resp] [DecidableEq Resp] [AddGroup Y]
  [Nonempty Req] (p : OracleProg X Y O) (q : ℕ) (pad : X)

end OracleProg

end GordieHowe.Quantum
