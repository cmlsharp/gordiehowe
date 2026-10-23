-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.ProofSystem.GKR.LayerPolynomial
public import GordieHowe.ProofSystem.Zerocheck.Round
public import Mathlib.Algebra.Polynomial.BigOperators
public import Mathlib.Data.List.FinRange
public import Mathlib.Data.List.Nodup
public import Mathlib.Data.List.NodupEquivFin

@[expose] public section

/-!
# Partial sums for Longfellow's no-copy layer

The actual `layer_h` order is bit round outermost and hand innermost:
x0, y0, x1, y1, ... . Boolean marginalization is over that explicit list.
Every round substitutes the fixed prefix, one polynomial indeterminate, and
Boolean suffix values into the concrete layer target. No target identity or
round degree is postulated.

The initial marginal is identified with the two-hand cube sum and the actual
layer binding. `GKR.LayerProtocol` supplies ordered transcript execution and
the deterministic no-healing implication used in protocol assembly.
-/
namespace GordieHowe.GKR.LayerSumcheck
open IOP
open scoped Classical
open LayerPolynomial
variable {F : Type} [Field F] {σ : Type} [Fintype σ] [DecidableEq σ]

/-- Summation over the remaining Boolean coordinates, preserving their order. -/
def marginal₂ {R : Type} [CommRing R] (base : F →+* R)
    (p : MvPolynomial σ F) (env : σ → R) : List σ → R
  | [] => MvPolynomial.eval₂ base env p
  | v :: vs => marginal₂ base p (Function.update env v 0) vs +
      marginal₂ base p (Function.update env v 1) vs

abbrev marginal (p : MvPolynomial σ F) (env : σ → F) (todo : List σ) : F :=
  marginal₂ (RingHom.id F) p env todo

omit [Fintype σ] in
theorem map_marginal₂ {R S : Type} [CommRing R] [CommRing S]
    (φ : R →+* S) (base : F →+* R) (p : MvPolynomial σ F) (env : σ → R) (todo : List σ) :
    φ (marginal₂ base p env todo) = marginal₂ (φ.comp base) p (φ ∘ env) todo := by
  induction todo generalizing env with
  | nil => exact MvPolynomial.eval₂_comp_left φ base env p
  | cons v vs ih => simp [marginal₂, ih, Function.comp_update]

omit [Fintype σ] in
/-- A factor that does not read the summed coordinates leaves the marginal:
`marginal₂ (a · b) = a(env) · marginal₂ b` when updating any summed coordinate does not change
the evaluation of `a`. -/
theorem marginal₂_mul_of_const {R : Type} [CommRing R] (base : F →+* R)
    (a b : MvPolynomial σ F) (env : σ → R) (todo : List σ)
    (ha : ∀ v ∈ todo, ∀ (e : σ → R) (x : R),
      MvPolynomial.eval₂ base (Function.update e v x) a = MvPolynomial.eval₂ base e a) :
    marginal₂ base (a * b) env todo =
      MvPolynomial.eval₂ base env a * marginal₂ base b env todo := by
  induction todo generalizing env with
  | nil => exact MvPolynomial.eval₂_mul _ _
  | cons v vs ih =>
    have hs : ∀ u ∈ vs, ∀ (e : σ → R) (x : R),
        MvPolynomial.eval₂ base (Function.update e u x) a = MvPolynomial.eval₂ base e a :=
      fun u hu => ha u (List.mem_cons_of_mem v hu)
    simp only [marginal₂]
    rw [ih _ hs, ih _ hs, ha v (by simp), ha v (by simp), mul_add]

/-- A substitution with only coordinate `next` nonconstant preserves that
coordinate's degree bound. The other substitutions can be arbitrary constants. -/
theorem substitution_degree (p : MvPolynomial σ F) (next : σ) (env : σ → Polynomial F)
    (h : ∀ v, (env v).natDegree ≤ if v = next then 1 else 0) :
    (MvPolynomial.eval₂ Polynomial.C env p).natDegree ≤ p.degreeOf next := by
  rw [MvPolynomial.eval₂_eq']
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro s hs
  apply (Polynomial.natDegree_C_mul_le _ _).trans
  apply (Polynomial.natDegree_prod_le _ _).trans
  apply (Finset.sum_le_sum fun v _ =>
    Polynomial.natDegree_pow_le.trans (Nat.mul_le_mul_left (s v) (h v))).trans
  simpa using MvPolynomial.le_degreeOf_of_mem_support next hs

theorem marginal_degree (p : MvPolynomial σ F) (next : σ) (env : σ → Polynomial F)
    (todo : List σ) (h : ∀ v, (env v).natDegree ≤ if v = next then 1 else 0) :
    (marginal₂ Polynomial.C p env todo).natDegree ≤ p.degreeOf next := by
  induction todo generalizing env with
  | nil => exact substitution_degree p next env h
  | cons v vs ih =>
    apply Polynomial.natDegree_add_le_of_degree_le
    · apply ih
      intro u
      by_cases hu : u = v
      · subst u; simp
      · simpa [Function.update_of_ne hu] using h u
    · apply ih
      intro u
      by_cases hu : u = v
      · subst u; simp
      · simpa [Function.update_of_ne hu] using h u

/-- The verifier's next true univariate polynomial after a fixed prefix. -/
noncomputable def roundPolynomial (p : MvPolynomial σ F) (env : σ → F)
    (next : σ) (suffix : List σ) : Polynomial F :=
  marginal₂ Polynomial.C p (Function.update (Polynomial.C ∘ env) next Polynomial.X) suffix

theorem round_degree (p : MvPolynomial σ F) (env : σ → F) (next : σ) (suffix : List σ) :
    (roundPolynomial p env next suffix).natDegree ≤ p.degreeOf next := by
  apply marginal_degree
  intro v
  by_cases hv : v = next
  · subst v; simp
  · simp [hv]

omit [Fintype σ] in
theorem round_eval (p : MvPolynomial σ F) (env : σ → F)
    (next : σ) (suffix : List σ) (r : F) :
    (roundPolynomial p env next suffix).eval r =
      marginal p (Function.update env next r) suffix := by
  have h := map_marginal₂ (Polynomial.evalRingHom r) Polynomial.C p
    (Function.update (Polynomial.C ∘ env) next Polynomial.X) suffix
  have hc : (Polynomial.evalRingHom r).comp Polynomial.C = RingHom.id F := by
    ext a
    simp
  have he : (Polynomial.evalRingHom r) ∘
      Function.update (Polynomial.C ∘ env) next Polynomial.X = Function.update env next r := by
    ext v
    by_cases hv : v = next <;> simp [Function.comp_def, hv]
  rw [hc, he] at h
  exact h

omit [Fintype σ] in
/-- The two Boolean endpoints partition the true remaining sum exactly. -/
theorem round_endpoints (p : MvPolynomial σ F) (env : σ → F)
    (next : σ) (suffix : List σ) :
    (roundPolynomial p env next suffix).eval 0 + (roundPolynomial p env next suffix).eval 1 =
      marginal p env (next :: suffix) := by
  simp only [round_eval, marginal, marginal₂]

omit [Fintype σ] in
/-- Once the suffix is empty, the remaining sum is the final layer evaluation. -/
theorem marginal_final (p : MvPolynomial σ F) (env : σ → F) :
    marginal p env [] = MvPolynomial.eval env p := rfl

/-- **The marginal of an evaluation function**: the sum over the Boolean values of the
coordinates `todo`, in order, of `pe` at the environment. With `pe` the evaluation of a
polynomial it is `marginal` (`marginalFn_eval`); the honest prover computes its messages this
way, from an executable evaluation of the layer polynomial. -/
def marginalFn (pe : (σ → F) → F) (env : σ → F) : List σ → F
  | [] => pe env
  | v :: vs => marginalFn pe (Function.update env v 0) vs +
      marginalFn pe (Function.update env v 1) vs

omit [Fintype σ] in
theorem marginalFn_eval (p : MvPolynomial σ F) (env : σ → F) (todo : List σ) :
    marginalFn (fun e => MvPolynomial.eval e p) env todo = marginal p env todo := by
  induction todo generalizing env with
  | nil => rfl
  | cons v vs ih => simp only [marginalFn, marginal, marginal₂, ih]

omit [Fintype σ] in
/-- The round polynomial at a point is the marginal of the evaluations with the round's
coordinate set to the point (`round_eval`). -/
theorem round_eval_marginalFn (p : MvPolynomial σ F) (env : σ → F)
    (next : σ) (suffix : List σ) (r : F) :
    (roundPolynomial p env next suffix).eval r =
      marginalFn (fun e => MvPolynomial.eval e p) (Function.update env next r) suffix := by
  rw [round_eval, marginalFn_eval]

omit [Fintype σ] in
/-- Evaluating the substitution with `X` at `next` at the point `x` evaluates at the environment
with `x` at `next`. -/
theorem eval_eval₂_update_X (p : MvPolynomial σ F) (env : σ → F) (next : σ) (x : F) :
    (MvPolynomial.eval₂ Polynomial.C (Function.update (Polynomial.C ∘ env) next Polynomial.X)
      p).eval x = MvPolynomial.eval (Function.update env next x) p :=
  round_eval p env next [] x

/-- **A substitution of degree at most one**: when `p` has degree at most one in `next`, the
substitution with `X` at `next` is the line through the evaluations at `0` and `1`. -/
theorem eval₂_update_X_of_degreeOf_le_one (p : MvPolynomial σ F) (env : σ → F) (next : σ)
    (hp : p.degreeOf next ≤ 1) :
    MvPolynomial.eval₂ Polynomial.C (Function.update (Polynomial.C ∘ env) next Polynomial.X) p =
      Polynomial.C (MvPolynomial.eval (Function.update env next 0) p) +
        Polynomial.C (MvPolynomial.eval (Function.update env next 1) p -
          MvPolynomial.eval (Function.update env next 0) p) * Polynomial.X := by
  set q := MvPolynomial.eval₂ Polynomial.C
    (Function.update (Polynomial.C ∘ env) next Polynomial.X) p
  have hq : q.natDegree ≤ 1 :=
    (substitution_degree p next (Function.update (Polynomial.C ∘ env) next Polynomial.X)
      fun v => by
        by_cases hv : v = next
        · subst v; simp
        · simp [hv]).trans hp
  have hrep := Polynomial.eq_X_add_C_of_natDegree_le_one hq
  have e0 : MvPolynomial.eval (Function.update env next 0) p = q.coeff 0 := by
    rw [← eval_eval₂_update_X p env next 0]
    change q.eval 0 = _
    rw [hrep]
    simp
  have e1 : MvPolynomial.eval (Function.update env next 1) p = q.coeff 1 + q.coeff 0 := by
    rw [← eval_eval₂_update_X p env next 1]
    change q.eval 1 = _
    rw [hrep]
    simp
  rw [e0, e1, add_sub_cancel_right]
  conv_lhs => rw [hrep]
  ring

omit [Fintype σ] in
/-- **The marginal of a round polynomial through an additive map**: summing the substitutions
over the Boolean values of coordinates other than `next`, then applying an additive map `φ` (a
coefficient), is the marginal of `φ` of the substitution at each Boolean point. -/
theorem map_marginal₂_update_X (φ : Polynomial F →+ F) (p : MvPolynomial σ F) (env : σ → F)
    (next : σ) (todo : List σ) (h : next ∉ todo) :
    φ (marginal₂ Polynomial.C p (Function.update (Polynomial.C ∘ env) next Polynomial.X) todo) =
      marginalFn (fun e => φ (MvPolynomial.eval₂ Polynomial.C
        (Function.update (Polynomial.C ∘ e) next Polynomial.X) p)) env todo := by
  induction todo generalizing env with
  | nil => rfl
  | cons v vs ih =>
    have hv : v ≠ next := fun e => h (e ▸ List.mem_cons_self)
    have hvs : next ∉ vs := fun e => h (List.mem_cons_of_mem v e)
    have hupd : ∀ a : F, Function.update (Function.update (Polynomial.C ∘ env) next Polynomial.X)
        v (Polynomial.C a) =
        Function.update (Polynomial.C ∘ Function.update env v a) next Polynomial.X := by
      intro a
      funext u
      by_cases hu : u = next
      · subst u; simp [hv.symm]
      · by_cases huv : u = v
        · subst u; simp [hu]
        · simp [hu, huv]
    simp only [marginal₂, marginalFn, map_add]
    rw [← map_zero (Polynomial.C (R := F)), ← map_one (Polynomial.C (R := F)), hupd, hupd,
      ih _ hvs, ih _ hvs]

omit [Fintype σ] in
/-- The coefficients of a round polynomial are marginals of the coefficients of the
substitutions. -/
theorem coeff_roundPolynomial (p : MvPolynomial σ F) (env : σ → F) (next : σ) (suffix : List σ)
    (h : next ∉ suffix) (k : ℕ) :
    (roundPolynomial p env next suffix).coeff k =
      marginalFn (fun e => (MvPolynomial.eval₂ Polynomial.C
        (Function.update (Polynomial.C ∘ e) next Polynomial.X) p).coeff k) env suffix :=
  map_marginal₂_update_X (Polynomial.lcoeff F k).toAddMonoidHom p env next suffix h

/-- Bit round first, then hand zero and hand one, matching `layer_h`. -/
def schedule (d : ℕ) : List (Vars d) :=
  (List.finRange d).flatMap fun j => [(false,j), (true,j)]

@[simp] theorem schedule_length (d : ℕ) : (schedule d).length = 2*d := by
  simp [schedule, List.length_flatMap, List.sum_replicate, Nat.mul_comm]

@[simp] theorem mem_schedule (d : ℕ) (v : Vars d) : v ∈ schedule d := by
  rcases v with ⟨hand,j⟩
  cases hand <;> simp [schedule, List.mem_flatMap]

theorem schedule_nodup (d : ℕ) : (schedule d).Nodup := by
  apply List.nodup_flatMap.mpr
  constructor
  · intro j _
    simp
  · apply (List.nodup_finRange d).imp
    intro i j hij
    simp only [Function.onFun, List.disjoint_left, List.mem_cons, List.not_mem_nil, or_false]
    intro v hv hv'
    rcases hv with rfl | rfl <;> simp_all

/-- Install the transcript's fixed prefix of challenges. -/
def prefixEnv (env r : σ → F) (pre : List σ) : σ → F :=
  pre.foldl (fun e v => Function.update e v (r v)) env

omit [Fintype σ] [Field F] in
theorem prefixEnv_apply (env r : σ → F) (pre : List σ) (v : σ) :
    prefixEnv env r pre v = if v ∈ pre then r v else env v := by
  induction pre generalizing env with
  | nil => simp [prefixEnv]
  | cons u us ih =>
    simp only [prefixEnv, List.foldl_cons] at *
    rw [ih]
    by_cases hv : v ∈ us <;> by_cases he : v = u <;> simp [hv, he]

omit [Field F] in
/-- After every interleaved challenge has been installed the environment is
exactly the transcript challenge vector, independently of its initial value. -/
theorem prefixEnv_schedule {d : ℕ} (env r : Vars d → F) :
    prefixEnv env r (schedule d) = r := by
  ext v
  simp [prefixEnv_apply]

/-- Install one challenge per position of an ordered variable list. -/
def install (env : σ → F) : (todo : List σ) → (Fin todo.length → F) → σ → F
  | [], _ => env
  | v :: vs, values => install (Function.update env v (values 0)) vs (fun i => values i.succ)

omit [Fintype σ] [Field F] in
theorem install_get (env r : σ → F) (todo : List σ) :
    install env todo (fun i => r (todo.get i)) = prefixEnv env r todo := by
  induction todo generalizing env with
  | nil => rfl
  | cons v vs ih => exact ih (Function.update env v (r v))

omit [Fintype σ] [Field F] in
theorem install_of_not_mem (env : σ → F) (todo : List σ)
    (values : Fin todo.length → F) (v : σ) (hv : v ∉ todo) :
    install env todo values v = env v := by
  induction todo generalizing env with
  | nil => rfl
  | cons u us ih =>
    have hne : v ≠ u := by intro he; subst v; exact hv (by simp)
    have htail : v ∉ us := fun h => hv (List.mem_cons_of_mem u h)
    exact (ih (Function.update env u (values 0)) (fun i => values i.succ) htail).trans
      (Function.update_of_ne hne _ _)

omit [Fintype σ] [Field F] in
/-- Each distinct scheduled coordinate retains exactly its own challenge. -/
theorem install_at (env : σ → F) (todo : List σ) (hnd : todo.Nodup)
    (values : Fin todo.length → F) (j : Fin todo.length) :
    install env todo values (todo.get j) = values j := by
  induction todo generalizing env with
  | nil => exact Fin.elim0 j
  | cons v vs ih =>
    rcases List.nodup_cons.mp hnd with ⟨hv, hvs⟩
    refine Fin.cases ?_ (fun i => ?_) j
    · change install (Function.update env v (values 0)) vs (fun i => values i.succ) v = values 0
      rw [install_of_not_mem _ _ _ v hv, Function.update_self]
    · exact ih _ hvs _ i

omit [Fintype σ] in
/-- Recursive Boolean marginalization enumerates every ordered Boolean suffix. -/
theorem marginal_enumerate (p : MvPolynomial σ F) (env : σ → F) (todo : List σ) :
    marginal p env todo = ∑ bits : Fin todo.length → Bool,
      MvPolynomial.eval (install env todo (fun i => boolValue (bits i))) p := by
  induction todo generalizing env with
  | nil => simp [marginal, marginal₂, install]
  | cons v vs ih =>
    have he := (Fin.consEquiv (fun _ : Fin (vs.length + 1) => Bool)).sum_comp
      (fun bits => MvPolynomial.eval (install env (v :: vs) (fun i => boolValue (bits i))) p)
    refine Eq.trans ?_ he
    simp only [Fintype.sum_prod_type, Fintype.sum_bool, Fin.consEquiv_apply,
      install, Fin.cons_zero, Fin.cons_succ, boolValue]
    simpa [marginal, marginal₂, boolValue, add_comm] using
      congrArg₂ (fun x y : F => x+y) (ih (Function.update env v 0)) (ih (Function.update env v 1))

/-- A duplicate-free complete schedule enumerates exactly the Boolean cube. -/
theorem marginal_complete (p : MvPolynomial σ F) (env : σ → F) (todo : List σ)
    (hnd : todo.Nodup) (hall : ∀ v, v ∈ todo) :
    marginal p env todo = ∑ bits : σ → Bool, MvPolynomial.eval (fun v => boolValue (bits v)) p := by
  rw [marginal_enumerate]
  let e := List.Nodup.getEquivOfForallMemList todo hnd hall
  apply Fintype.sum_equiv (Equiv.piCongrLeft' (fun _ => Bool) e)
  intro bits
  apply congrArg (fun e : σ → F => MvPolynomial.eval e p)
  let r : σ → F := fun v => boolValue (bits (e.symm v))
  have he : (fun i => boolValue (bits i)) = (fun i => r (todo.get i)) := by
    ext i
    change boolValue (bits i) = boolValue (bits (e.symm (e i)))
    rw [e.symm_apply_apply]
  rw [he, install_get]
  ext v
  simp [prefixEnv_apply, hall, r, Equiv.piCongrLeft'_apply]

/-- Functions on the two hands are pairs of Boolean cube points. -/
def handsEquiv (d : ℕ) : (Vars d → Bool) ≃ Cube d × Cube d where
  toFun bits := (fun j => bits (false,j), fun j => bits (true,j))
  invFun xy := fun (h,j) => if h then xy.2 j else xy.1 j
  left_inv bits := by ext ⟨h,j⟩; cases h <;> rfl
  right_inv xy := by rfl

/-- The source interleaved schedule's initial marginal is precisely the
two-hand Boolean sum, including the dimension-zero case. -/
theorem marginal_schedule {d : ℕ} (p : MvPolynomial (Vars d) F) (env : Vars d → F) :
    marginal p env (schedule d) = ∑ x : Cube d, ∑ y : Cube d,
      MvPolynomial.eval (point x y) p := by
  rw [marginal_complete p env (schedule d) (schedule_nodup d) (mem_schedule d)]
  calc
    _ = ∑ xy : Cube d × Cube d, MvPolynomial.eval (point xy.1 xy.2) p := by
      apply Fintype.sum_equiv (handsEquiv d)
      intro bits
      apply congrArg (fun e : Vars d → F => MvPolynomial.eval e p)
      ext ⟨h,j⟩
      cases h <;> rfl
    _ = _ := Fintype.sum_prod_type _

/-- Initial sumcheck claim equals the actual prep_v-bound layer sum. -/
theorem layer_initial {d G W T : ℕ}
    (Q : GKR.Layer F G W T) (label : Fin W → Cube d) (w : Cube d → F)
    (weight : Fin G → F) (beta : F) (env : Vars d → F) :
    marginal (target Q label w weight beta) env (schedule d) =
      Layer.bind Q (w ∘ label) weight beta := by
  rw [marginal_schedule, cube_sum]

/-- The completed layer marginal equals the factored terminal expression. -/
theorem layer_final {d G W T : ℕ}
    (Q : GKR.Layer F G W T) (label : Fin W → Cube d) (w : Cube d → F)
    (weight : Fin G → F) (beta : F) (env r : Vars d → F) :
    marginal (target Q label w weight beta) (prefixEnv env r (schedule d)) [] =
      MvPolynomial.eval r (wiring Q label weight beta) *
        (MvPolynomial.eval r (mle false w) * MvPolynomial.eval r (mle true w)) := by
  rw [prefixEnv_schedule, marginal_final, terminal]

/-- A false partial claim survives the concrete omitted-p(1) message on at most
two field challenges. Prefix and suffix are fixed before that challenge. -/
theorem layer_round_bad_count [Fintype F] {d G W T : ℕ}
    (Q : GKR.Layer F G W T) (label : Fin W → Cube d) (w : Cube d → F)
    (weight : Fin G → F) (beta : F) (env : Vars d → F)
    (next : Vars d) (suffix : List (Vars d)) (nodes : Sumcheck.Nodes F)
    (incoming p0 p2 : F)
    (hfalse : incoming ≠ marginal (target Q label w weight beta) env (next :: suffix)) :
    (Finset.univ.filter fun r : F =>
      Sumcheck.Round.coefficients nodes r 1 * (incoming-p0) +
      Sumcheck.Round.coefficients nodes r 0 * p0 + Sumcheck.Round.coefficients nodes r 2 * p2 =
        marginal (target Q label w weight beta) (Function.update env next r) suffix).card ≤ 2 := by
  have hd := (round_degree (target Q label w weight beta) env next suffix).trans
    (target_degree Q label w weight beta next)
  simpa only [round_eval] using Sumcheck.Round.reconstructed_bad_challenge_count nodes incoming p0 p2
    (roundPolynomial (target Q label w weight beta) env next suffix) hd
    (by simpa only [round_endpoints] using hfalse)

/-- The same concrete round bound in the protocol's NNReal error convention. -/
theorem layer_round_bad_count_nnreal [Fintype F] {d G W T : ℕ}
    (Q : GKR.Layer F G W T) (label : Fin W → Cube d) (w : Cube d → F)
    (weight : Fin G → F) (beta : F) (env : Vars d → F)
    (next : Vars d) (suffix : List (Vars d)) (nodes : Sumcheck.Nodes F)
    (incoming p0 p2 : F)
    (hfalse : incoming ≠ marginal (target Q label w weight beta) env (next :: suffix)) :
    ((Finset.univ.filter fun r : F =>
      Sumcheck.Round.coefficients nodes r 1 * (incoming-p0) +
      Sumcheck.Round.coefficients nodes r 0 * p0 + Sumcheck.Round.coefficients nodes r 2 * p2 =
        marginal (target Q label w weight beta) (Function.update env next r) suffix).card : NNReal) ≤
      (2 / Fintype.card F : NNReal) * Fintype.card F := by
  have hcard : (Fintype.card F : NNReal) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  rw [div_mul_cancel₀ _ hcard]
  exact_mod_cast layer_round_bad_count Q label w weight beta env next suffix nodes incoming p0 p2 hfalse

end GordieHowe.GKR.LayerSumcheck
