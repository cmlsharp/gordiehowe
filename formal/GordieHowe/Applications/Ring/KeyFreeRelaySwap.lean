-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Applications.Ring.KeyFreeRelayB
public import GordieHowe.Model.Quantum.Pure.MultiRelayResolve
public import GordieHowe.Model.Quantum.Interactive.AssignRelayChal

@[expose] public section

/-!
# The key-free relay in side-read mode under a swap of one request's side coins

# The key-free relay in side-read mode under a swap of side coins

The key-free relay in side-read mode (`kfRelaySide`,
`GordieHowe/Applications/Ring/KeyFreeRelayB.lean`)
at side coins `sc'`, against the same relay at `sc` (`MultiRelay.ProgSwap`,
`MultiRelay.SameShape`, `GordieHowe/Model/Quantum/Pure/MultiRelayResolve.lean`): off the swapped
requests the side coins agree; at a request `r₀` whose base-component signer program at `sc'` runs,
at the side function read through `r₀`'s table, as at `sc` with the signature moved by `swσ`
(`CoinSwapAt`), the resolved programs are related by the move `sw` of the main request and its
record (`recordSw`). On refusal the signer makes the same reads as on acceptance
(`sgnB`), so the relays at any two side coins have the same shape, when the base-component signer
program is in lockstep at any two side coins and the statement program at any two published values.

- `OracleProg.bind_assoc`, `OracleProg.bind_pure`, `OracleProg.mapOutput_mapOutput`,
  `OracleProg.mapOutput_bind`, `OracleProg.translate_mapOutput`, `OracleProg.after_mapOutput`:
  binds and maps of programs.
- `OracleProg.Lockstep`, `OracleProg.EqAt`: two programs in lockstep, queries related by `QA`,
  results by `RO`, at answers related by `QB` at the queries (`EqAt`: equal at equal queries);
  `Lockstep.mono`, `Lockstep.bind`, `Lockstep.mapOutput`, `Lockstep.translate`, `Lockstep.after`,
  `Lockstep.tabulate`, `lockstep_refl`.
- `OracleProg.CountsLE`: at most `q` queries satisfying `P` on every path; `CountsLE.mono`,
  `countsLE_pure`, `CountsLE.bind`, `CountsLE.mapOutput`, `CountsLE.translate`,
  `countsLE_query_of_false`, `countsLE_query`, `CountsLE.tabulate`, `countsLE_queryAll`.
- `OracleProg.SameKind`, `Lockstep.shapeOf_after`, `Lockstep.sidesLE`, `Lockstep.startsSide`,
  `Lockstep.recMain`, `sidesLE_of_countsLE`, `CountsLE.recMain`: relay programs in lockstep at
  queries of the same kind have states of the same shape, the same side reads and pad sub-slots;
  path counts of side reads bound the side reads.
- `OracleProg.resolve_bind`, `resolve_mapOutput`, `resolve_translate_side`,
  `resolve_translate_main`, `resolve_recMain_tabS`, `recMain_translate_main`,
  `after_translate_main`: resolving the side reads through binds, side-only programs, moves of the
  main requests and the recording of the main request.
- `AssignRelay.recordSw`, `recordSw_apply`, `recordOf_map_sw`, `resolve_relayOfProg_swap`,
  **`AssignRelay.progSwap_relayOf`**: `ProgSwap` of two relays of assigning relays from their
  programs at a request.
- `mapSig`, `asgOf_mapSig`, `xK_mapSig`, `replyOf_mapSig`, `translate_main_lift`,
  `resolve_kfProgK_swap`, `sigK_congr`, `kfProgK_congr`: the key-free relay program under a moved
  signature, and its reads of its own request's side coins.
- `resolve_lift_baseL_viaSide`, `KFReads.lift_bind`, `KFReads.lift_mapOutput`, `CoinSwapAt`,
  `resolve_sigK_sgnB_swap`: the resolved signature in side-read mode under a coin swap.
- `sameKind_refl`, `KFReads.lift_query`, `KFReads.lift_pure`, `Lockstep.lift_baseL_viaSide`,
  `Lockstep.lift_baseL_viaSide_any`, `lockstep_kfProgK_sgnB`, `countsLE_translate_baseL_viaSide`,
  `countsLE_kfProgK_sgnB`, `lockstep_relayOfProg_kfRelaySide`: the side-mode programs at two side
  coins in lockstep, and their side reads on every path.
- **`sameShape_kfRelaySide`** (ii-b), **`relayOf_kfRelaySide_eq_withProg`** (ii-a),
  **`progSwap_kfRelaySide`** (ii-c): the relays at side coins swapped at one request.
- `sum_map_id_of_eq_map`, **`offTagFixed_kfRelaySide`**: off `J`, the relay asks main requests
  fixed by `sw`.
-/

namespace GordieHowe

namespace OracleProg

section Basic

variable {A B R S U : Type*}

theorem bind_assoc : ∀ (p : OracleProg A B R) (f : R → OracleProg A B S)
    (g : S → OracleProg A B U), (p.bind f).bind g = p.bind fun r => (f r).bind g
  | pure _, _, _ => rfl
  | query a k, f, g => congrArg (query a) (funext fun b => bind_assoc (k b) f g)

theorem bind_pure : ∀ p : OracleProg A B R, p.bind pure = p
  | pure _ => rfl
  | query a k => congrArg (query a) (funext fun b => bind_pure (k b))

theorem mapOutput_mapOutput (f : R → S) (g : S → U) (p : OracleProg A B R) :
    (p.mapOutput f).mapOutput g = p.mapOutput (g ∘ f) := by
  simp only [mapOutput, bind_assoc]
  rfl

theorem mapOutput_bind (f : R → S) (p : OracleProg A B R) (g : S → OracleProg A B U) :
    (p.mapOutput f).bind g = p.bind (g ∘ f) := by
  simp only [mapOutput, bind_assoc]
  rfl

theorem translate_mapOutput {A' B' : Type*} (ι : A → A') (g : A → B' → B) (f : R → S)
    (p : OracleProg A B R) : translate ι g (p.mapOutput f) = (translate ι g p).mapOutput f := by
  rw [mapOutput, translate_bind]
  rfl

/-- **The state of a program with its results mapped**: the state, the result mapped. -/
theorem after_mapOutput (f : R → S) :
    ∀ (p : OracleProg A B R) (ans : List B), (p.mapOutput f).after ans = Sum.map f id (p.after ans)
  | pure _, _ => rfl
  | query _ _, [] => rfl
  | query _ k, b :: bs => after_mapOutput f (k b) bs

end Basic

/-! ### Programs in lockstep -/

section Lockstep

variable {A A' B B' R R' : Type*}

/-- **Two programs in lockstep**: at every pair of paths whose answers are related by `QB` at the
queries, both query, at queries related by `QA`, or both return, results related by `RO`. -/
def Lockstep (QA : A → A' → Prop) (QB : A → A' → B → B' → Prop) (RO : R → R' → Prop) :
    OracleProg A B R → OracleProg A' B' R' → Prop
  | pure r, pure r' => RO r r'
  | query a k, query a' k' => QA a a' ∧ ∀ b b', QB a a' b b' → Lockstep QA QB RO (k b) (k' b')
  | pure _, query _ _ => False
  | query _ _, pure _ => False

/-- **Answers equal at equal queries.** -/
def EqAt (a a' : A) (b b' : B) : Prop :=
  a = a' → b = b'

variable {QA : A → A' → Prop} {QB : A → A' → B → B' → Prop} {RO : R → R' → Prop}

theorem Lockstep.mono {QA' : A → A' → Prop} {QB' : A → A' → B → B' → Prop}
    {RO' : R → R' → Prop} (hQ : ∀ a a', QA a a' → QA' a a')
    (hB : ∀ a a' b b', QA a a' → QB' a a' b b' → QB a a' b b')
    (hR : ∀ r r', RO r r' → RO' r r') :
    ∀ {p : OracleProg A B R} {p' : OracleProg A' B' R'}, Lockstep QA QB RO p p' →
      Lockstep QA' QB' RO' p p'
  | pure _, pure _, h => hR _ _ h
  | query _ _, query _ _, h =>
    ⟨hQ _ _ h.1, fun b b' hb => Lockstep.mono hQ hB hR (h.2 b b' (hB _ _ _ _ h.1 hb))⟩
  | pure _, query _ _, h => h.elim
  | query _ _, pure _, h => h.elim

theorem Lockstep.bind {S S' : Type*} {RO₂ : S → S' → Prop} {f : R → OracleProg A B S}
    {f' : R' → OracleProg A' B' S'} (hf : ∀ r r', RO r r' → Lockstep QA QB RO₂ (f r) (f' r')) :
    ∀ {p : OracleProg A B R} {p' : OracleProg A' B' R'}, Lockstep QA QB RO p p' →
      Lockstep QA QB RO₂ (p.bind f) (p'.bind f')
  | pure _, pure _, h => hf _ _ h
  | query _ _, query _ _, h => ⟨h.1, fun b b' hb => Lockstep.bind hf (h.2 b b' hb)⟩
  | pure _, query _ _, h => h.elim
  | query _ _, pure _, h => h.elim

theorem Lockstep.mapOutput {S S' : Type*} {RO₂ : S → S' → Prop} {f : R → S} {f' : R' → S'}
    (hf : ∀ r r', RO r r' → RO₂ (f r) (f' r')) {p : OracleProg A B R} {p' : OracleProg A' B' R'}
    (h : Lockstep QA QB RO p p') : Lockstep QA QB RO₂ (p.mapOutput f) (p'.mapOutput f') :=
  h.bind (f := fun r => pure (f r)) (f' := fun r' => pure (f' r')) fun r r' hr =>
    (hf r r' hr : Lockstep QA QB RO₂ (pure (f r)) (pure (f' r')))

theorem Lockstep.translate {A₂ A₂' B₂ B₂' : Type*} {QA₂ : A₂ → A₂' → Prop}
    {QB₂ : A₂ → A₂' → B₂ → B₂' → Prop} {ι : A → A₂} {ι' : A' → A₂'} {g : A → B₂ → B}
    {g' : A' → B₂' → B'} (hι : ∀ a a', QA a a' → QA₂ (ι a) (ι' a'))
    (hg : ∀ a a' b b', QA a a' → QB₂ (ι a) (ι' a') b b' → QB a a' (g a b) (g' a' b')) :
    ∀ {p : OracleProg A B R} {p' : OracleProg A' B' R'}, Lockstep QA QB RO p p' →
      Lockstep QA₂ QB₂ RO (p.translate ι g) (p'.translate ι' g')
  | pure _, pure _, h => h
  | query a k, query a' k', h =>
    ⟨hι a a' h.1, fun b b' hb => Lockstep.translate hι hg (h.2 _ _ (hg a a' b b' h.1 hb))⟩
  | pure _, query _ _, h => h.elim
  | query _ _, pure _, h => h.elim

/-- **Programs in lockstep have related states** after the same answers, when equal answers are
related. -/
theorem Lockstep.after {QB : A → A' → B → B → Prop} (hB : ∀ a a' b, QA a a' → QB a a' b b) :
    ∀ {p : OracleProg A B R} {p' : OracleProg A' B R'}, Lockstep QA QB RO p p' →
      ∀ ans, Sum.LiftRel RO QA (p.after ans) (p'.after ans)
  | pure _, pure _, h, _ => .inl h
  | query _ _, query _ _, h, [] => .inr h.1
  | query _ _, query _ _, h, b :: bs => Lockstep.after hB (h.2 b b (hB _ _ _ h.1)) bs
  | pure _, query _ _, h, _ => h.elim
  | query _ _, pure _, h, _ => h.elim

theorem Lockstep.tabulate {ι β β' : Type*} [DecidableEq ι] (d : ι → β) (d' : ι → β')
    {P : ι → OracleProg A B β}
    {P' : ι → OracleProg A' B' β'} :
    ∀ (l : List ι), (∀ i ∈ l, Lockstep QA QB (fun _ _ => True) (P i) (P' i)) →
      Lockstep QA QB (fun _ _ => True) (OracleProg.tabulate d l P) (OracleProg.tabulate d' l P')
  | [], _ => trivial
  | i :: l, h => (h i (List.mem_cons_self ..)).bind fun _ _ _ =>
      (Lockstep.tabulate d d' l fun j hj => h j (List.mem_cons_of_mem _ hj)).bind
        fun _ _ _ => by exact trivial

/-- **A program is in lockstep with itself**, answers equal at equal queries. -/
theorem lockstep_refl {QA : A → A → Prop} (hQ : ∀ a, QA a a) :
    ∀ p : OracleProg A B R, Lockstep QA EqAt (· = ·) p p
  | pure _ => rfl
  | query a k => ⟨hQ a, fun b b' hb => (hb rfl) ▸ lockstep_refl hQ (k b)⟩

end Lockstep

/-! ### Query counts on every path -/

section Counts

variable {A B R S : Type*} (P : A → Bool)

/-- **At most `q` queries satisfying `P` on every path.** -/
def CountsLE : ℕ → OracleProg A B R → Prop
  | _, pure _ => True
  | q, query a k => if P a then 0 < q ∧ ∀ b, CountsLE (q - 1) (k b) else ∀ b, CountsLE q (k b)

variable {P}

theorem CountsLE.mono : ∀ {q q' : ℕ} {p : OracleProg A B R}, CountsLE P q p → q ≤ q' →
    CountsLE P q' p
  | _, _, pure _, _, _ => trivial
  | q, q', query a k, h, hq => by
    unfold CountsLE at h ⊢
    split_ifs at h ⊢
    · exact ⟨by omega, fun b => (h.2 b).mono (by omega)⟩
    · exact fun b => (h b).mono hq

theorem countsLE_pure (q : ℕ) (r : R) : CountsLE P q (pure r : OracleProg A B R) :=
  trivial

theorem CountsLE.bind {f : R → OracleProg A B S} {q₂ : ℕ} (hf : ∀ r, CountsLE P q₂ (f r)) :
    ∀ {q₁ : ℕ} {p : OracleProg A B R}, CountsLE P q₁ p → CountsLE P (q₁ + q₂) (p.bind f)
  | q₁, pure r, _ => (hf r).mono (Nat.le_add_left _ _)
  | q₁, query a k, h => by
    unfold CountsLE at h
    change CountsLE P (q₁ + q₂) (query a fun b => (k b).bind f)
    unfold CountsLE
    split_ifs at h ⊢
    · refine ⟨by omega, fun b => ?_⟩
      have := (h.2 b).bind hf
      rwa [show q₁ - 1 + q₂ = q₁ + q₂ - 1 by omega] at this
    · exact fun b => (h b).bind hf

theorem CountsLE.mapOutput {f : R → S} {q : ℕ} {p : OracleProg A B R} (h : CountsLE P q p) :
    CountsLE P q (p.mapOutput f) := by
  have h' := h.bind (q₂ := 0) (f := fun r => pure (f r)) fun r => countsLE_pure 0 _
  rw [Nat.add_zero] at h'
  exact h'

theorem CountsLE.translate {A' B' : Type*} {P' : A' → Bool} {ι : A → A'} {g : A → B' → B}
    (hP : ∀ a, P' (ι a) = P a) :
    ∀ {q : ℕ} {p : OracleProg A B R}, CountsLE P q p → CountsLE P' q (p.translate ι g)
  | _, pure _, _ => trivial
  | q, query a k, h => by
    unfold CountsLE at h
    change CountsLE P' q (query (ι a) fun b => (k (g a b)).translate ι g)
    unfold CountsLE
    rw [hP]
    split_ifs at h ⊢
    · exact ⟨h.1, fun b => (h.2 _).translate hP⟩
    · exact fun b => (h _).translate hP

theorem countsLE_query_of_false {a : A} {k : B → OracleProg A B R} {q : ℕ} (ha : P a = false)
    (h : ∀ b, CountsLE P q (k b)) : CountsLE P q (query a k) := by
  unfold CountsLE
  rw [ha]
  exact h

theorem countsLE_query {a : A} {k : B → OracleProg A B R} {q : ℕ} (h : ∀ b, CountsLE P q (k b)) :
    CountsLE P (q + 1) (query a k) := by
  unfold CountsLE
  split_ifs
  · exact ⟨Nat.succ_pos _, fun b => by simpa using h b⟩
  · exact fun b => (h b).mono (Nat.le_succ _)

theorem CountsLE.tabulate {ι β : Type*} [DecidableEq ι] (d : ι → β) {Pi : ι → OracleProg A B β}
    {q : ℕ} :
    ∀ (l : List ι), (∀ i ∈ l, CountsLE P q (Pi i)) →
      CountsLE P (l.length * q) (OracleProg.tabulate d l Pi)
  | [], _ => trivial
  | i :: l, h => by
    have := (h i (List.mem_cons_self ..)).bind (q₂ := l.length * q + 0)
      (f := fun b => (OracleProg.tabulate d l Pi).bind fun g => pure (Function.update g i b))
      fun _ => (CountsLE.tabulate d l fun j hj => h j (List.mem_cons_of_mem _ hj)).bind
        fun _ => countsLE_pure 0 _
    exact this.mono (by simp [List.length_cons, Nat.succ_mul, Nat.add_comm])

theorem countsLE_queryAll : ∀ (l : List A), CountsLE P l.length (queryAll l : OracleProg A B _)
  | [] => trivial
  | a :: l => countsLE_query fun _ => by
      simpa using (countsLE_queryAll l).bind (P := P) (q₂ := 0) fun _ => countsLE_pure 0 _

end Counts

/-! ### Relay programs in lockstep -/

section Relay

variable {X Xs Req' Y Ys Resp' R R' : Type}

/-- **Queries of the same kind**: two oracle queries, two side reads, or two main requests. -/
abbrev SameKind {X' Xs' Req'' : Type} : (X ⊕ Xs) ⊕ Req' → (X' ⊕ Xs') ⊕ Req'' → Prop :=
  Sum.LiftRel (Sum.LiftRel (fun _ _ => True) fun _ _ => True) fun _ _ => True

variable {QB : (X ⊕ Xs) ⊕ Req' → (X ⊕ Xs) ⊕ Req' → (Y ⊕ Ys) ⊕ Option Resp' →
  (Y ⊕ Ys) ⊕ Option Resp' → Prop} {RO : R → R' → Prop}

/-- **Programs in lockstep at queries of the same kind** have states of the same shape. -/
theorem Lockstep.shapeOf_after (hB : ∀ a a' b, SameKind a a' → QB a a' b b)
    {p : OracleProg ((X ⊕ Xs) ⊕ Req') ((Y ⊕ Ys) ⊕ Option Resp') R}
    {p' : OracleProg ((X ⊕ Xs) ⊕ Req') ((Y ⊕ Ys) ⊕ Option Resp') R'}
    (h : Lockstep SameKind QB RO p p') (ans : List ((Y ⊕ Ys) ⊕ Option Resp')) :
    Quantum.MultiRelay.shapeOf (p'.after ans) = Quantum.MultiRelay.shapeOf (p.after ans) := by
  have hr := h.after hB ans
  generalize p.after ans = u at hr
  generalize p'.after ans = u' at hr
  rcases hr with ⟨-⟩ | ⟨hq⟩
  · rfl
  · rcases hq with ⟨hq⟩ | ⟨-⟩
    · rcases hq with ⟨-⟩ | ⟨-⟩ <;> rfl
    · rfl

/-- **Programs in lockstep at queries of the same kind** make the same side reads, when every
answer of the second is related to one of the first. -/
theorem Lockstep.sidesLE (hB : ∀ a a' b', SameKind a a' → ∃ b, QB a a' b b') :
    ∀ {q : ℕ} {p : OracleProg ((X ⊕ Xs) ⊕ Req') ((Y ⊕ Ys) ⊕ Option Resp') R}
      {p' : OracleProg ((X ⊕ Xs) ⊕ Req') ((Y ⊕ Ys) ⊕ Option Resp') R'},
      Lockstep SameKind QB RO p p' → SidesLE q p → SidesLE q p'
  | _, pure _, pure _, _, _ => trivial
  | q, query a k, query a' k', h, hs => by
    have h1 := h.1
    have hk : ∀ b', ∃ b, Lockstep SameKind QB RO (k b) (k' b') := fun b' => by
      obtain ⟨b, hb⟩ := hB a a' b' h1
      exact ⟨b, h.2 b b' hb⟩
    rcases a with (x | x) | r <;> rcases a' with (x' | x') | r' <;>
      simp only [SameKind, Sum.liftRel_inl_inl, Sum.liftRel_inr_inr, Sum.not_liftRel_inl_inr,
        Sum.not_liftRel_inr_inl] at h1
    · exact fun b' => (hk b').elim fun b hb => Lockstep.sidesLE hB hb (hs b)
    · exact ⟨hs.1, fun b' => (hk b').elim fun b hb => Lockstep.sidesLE hB hb (hs.2 b)⟩
    · exact fun b' => (hk b').elim fun b hb => Lockstep.sidesLE hB hb (hs b)
  | _, pure _, query _ _, h, _ => h.elim
  | _, query _ _, pure _, h, _ => h.elim

/-- **Programs in lockstep at queries of the same kind** begin with a side read alike. -/
theorem Lockstep.startsSide
    {p : OracleProg ((X ⊕ Xs) ⊕ Req') ((Y ⊕ Ys) ⊕ Option Resp') R}
    {p' : OracleProg ((X ⊕ Xs) ⊕ Req') ((Y ⊕ Ys) ⊕ Option Resp') R'}
    (h : Lockstep SameKind QB RO p p') : p'.startsSide = p.startsSide := by
  cases p with
  | pure _ => cases p' with
    | pure _ => rfl
    | query _ _ => exact h.elim
  | query a k => cases p' with
    | pure _ => exact h.elim
    | query a' k' =>
      have h1 := h.1
      rcases a with (x | x) | r <;> rcases a' with (x' | x') | r' <;>
        simp only [SameKind, Sum.liftRel_inl_inl, Sum.liftRel_inr_inr, Sum.not_liftRel_inl_inr,
          Sum.not_liftRel_inr_inl] at h1 <;> rfl

/-- **Recording the main request keeps programs in lockstep**, answers equal at equal queries. -/
theorem Lockstep.recMain {X' Y' : Type} {QX : X' → X' → Prop} (T : X' → Option Y') :
    ∀ {p : OracleProg (X' ⊕ Req') (Y' ⊕ Option Resp') R}
      {p' : OracleProg (X' ⊕ Req') (Y' ⊕ Option Resp') R'},
      Lockstep (Sum.LiftRel QX fun _ _ => True) EqAt RO p p' →
      Lockstep (Sum.LiftRel QX fun _ _ => True) EqAt (fun _ _ => True)
        (recMain T p) (recMain T p')
  | pure _, pure _, _ => trivial
  | query a k, query a' k', h => by
    have h1 := h.1
    rcases a with x | r <;> rcases a' with x' | r' <;>
      simp only [Sum.liftRel_inl_inl, Sum.liftRel_inr_inr, Sum.not_liftRel_inl_inr,
        Sum.not_liftRel_inr_inl] at h1
    · refine ⟨.inl h1, fun b b' hb => Lockstep.recMain T (h.2 _ _ fun he => ?_)⟩
      cases he
      rw [hb rfl]
    · exact ⟨.inr trivial, fun b b' hb =>
        (Lockstep.recMain T (h.2 b b' hb)).mapOutput fun _ _ _ => trivial⟩
  | pure _, query _ _, h => h.elim
  | query _ _, pure _, h => h.elim

/-- **Side reads counted on every path** bound the side reads. -/
theorem sidesLE_of_countsLE :
    ∀ {q : ℕ} {p : OracleProg ((X ⊕ Xs) ⊕ Req') ((Y ⊕ Ys) ⊕ Option Resp') R},
      CountsLE isSideRead q p → SidesLE q p
  | _, pure _, _ => trivial
  | q, query a k, h => by
    unfold CountsLE at h
    rcases a with (x | x) | r
    · exact fun b => sidesLE_of_countsLE (h b)
    · exact ⟨h.1, fun b => sidesLE_of_countsLE (h.2 b)⟩
    · exact fun b => sidesLE_of_countsLE (h b)

/-- **Recording the main request keeps the counts** of queries read through their kind. -/
theorem CountsLE.recMain {X' Y' : Type} {P : X' ⊕ Req' → Bool} (hP : ∀ r, P (.inr r) = false)
    (T : X' → Option Y') :
    ∀ {q : ℕ} {p : OracleProg (X' ⊕ Req') (Y' ⊕ Option Resp') R}, CountsLE P q p →
      CountsLE P q (OracleProg.recMain T p)
  | _, pure _, _ => trivial
  | q, query (.inl x) k, h => by
    unfold CountsLE at h
    change CountsLE P q (query (.inl x) fun b => OracleProg.recMain T (k _))
    unfold CountsLE
    split_ifs at h ⊢
    · exact ⟨h.1, fun b => CountsLE.recMain hP T (h.2 _)⟩
    · exact fun b => CountsLE.recMain hP T (h _)
  | q, query (.inr r) k, h => by
    unfold CountsLE at h
    rw [hP] at h
    change CountsLE P q (query (.inr r) fun b => (OracleProg.recMain T (k b)).mapOutput _)
    unfold CountsLE
    rw [hP]
    exact fun b => (CountsLE.recMain hP T (h b)).mapOutput

end Relay

/-! ### Resolving the side reads -/

section Resolve

variable {X Xs Req' Y Ys Resp' R S : Type} (s : Xs → Ys)

theorem resolve_bind (f : R → OracleProg ((X ⊕ Xs) ⊕ Req') ((Y ⊕ Ys) ⊕ Option Resp') S)
    (p : OracleProg ((X ⊕ Xs) ⊕ Req') ((Y ⊕ Ys) ⊕ Option Resp') R) :
    resolve s (p.bind f) = (resolve s p).bind fun r => resolve s (f r) := by
  induction p with
  | pure _ => rfl
  | query a k ih => rcases a with (x | x) | r' <;> simp only [OracleProg.bind, resolve, ih]

theorem resolve_mapOutput (f : R → S)
    (p : OracleProg ((X ⊕ Xs) ⊕ Req') ((Y ⊕ Ys) ⊕ Option Resp') R) :
    resolve s (p.mapOutput f) = (resolve s p).mapOutput f :=
  resolve_bind s _ p

/-- **A program of side reads alone resolves to its result** at the side function. -/
theorem resolve_translate_side {A B : Type} (j : A → Xs)
    (g : A → (Y ⊕ Ys) ⊕ Option Resp' → B) :
    ∀ p : OracleProg A B R,
      resolve s (p.translate (fun a => (.inl (.inr (j a)) : (X ⊕ Xs) ⊕ Req')) g) =
        pure (p.run fun a => g a (.inl (.inr (s (j a)))))
  | pure _ => rfl
  | query a k => resolve_translate_side j g (k _)

/-- **Moving the main requests commutes with resolving.** -/
theorem resolve_translate_main (sw : Req' → Req')
    (p : OracleProg ((X ⊕ Xs) ⊕ Req') ((Y ⊕ Ys) ⊕ Option Resp') R) :
    resolve s (p.translate (Sum.map id sw) fun _ b => b) =
      (resolve s p).translate (Sum.map id sw) fun _ b => b := by
  induction p with
  | pure _ => rfl
  | query a k ih =>
    rcases a with (x | x) | r' <;> simp only [translate, resolve, Sum.map_inl, Sum.map_inr, id, ih]

/-- **Resolving commutes with recording the main request** through the table `tabS T`. -/
theorem resolve_recMain_tabS [DecidableEq X] (T : X → Option Y)
    (p : OracleProg ((X ⊕ Xs) ⊕ Req') ((Y ⊕ Ys) ⊕ Option Resp') R) :
    resolve s (recMain (tabS T) p) = recMain T (resolve s p) := by
  induction p with
  | pure _ => rfl
  | query a k ih =>
    rcases a with (x | x) | r'
    · simp only [recMain, resolve]
      refine congrArg _ (funext fun b => ?_)
      rcases b with y | _
      · rw [← ih]
        congr 2
        simp only [tabS, Sum.elim_inl, embedAns, Sum.elim_inl]
        cases T x <;> rfl
      · exact ih _
    · simp only [recMain, resolve, tabS, Sum.elim_inr, Option.getD_none, Sum.elim_inl]
      exact ih _
    · simp only [recMain, resolve, resolve_mapOutput, ih]
      refine congrArg _ (funext fun b => ?_)
      rcases b with _ | _ <;> rfl

end Resolve

section Main

variable {X Req' Y Resp' R : Type} (sw : Req' → Req')

/-- **Recording a moved main request** records the main request moved. -/
theorem recMain_translate_main (T : X → Option Y) (p : OracleProg (X ⊕ Req') (Y ⊕ Option Resp') R) :
    recMain T (p.translate (Sum.map id sw) fun _ b => b) =
      ((recMain T p).translate (Sum.map id sw) fun _ b => b).mapOutput
        fun q => (q.1, q.2.map (Prod.map sw id)) := by
  induction p with
  | pure _ => rfl
  | query a k ih =>
    rcases a with x | r'
    · simp only [translate, Sum.map_inl, id, recMain]
      refine congrArg _ (funext fun b => ?_)
      exact ih _
    · simp only [translate, Sum.map_inr, recMain]
      refine congrArg _ (funext fun b => ?_)
      change _ = ((translate (Sum.map id sw) (fun _ b => b)
        ((recMain T (k b)).mapOutput _)).mapOutput _)
      rw [ih, translate_mapOutput, mapOutput_mapOutput, mapOutput_mapOutput]
      rfl

/-- **The states of a program with its main requests moved and its results mapped.** -/
theorem after_translate_main {S : Type} (f : R → S) (p : OracleProg (X ⊕ Req') (Y ⊕ Option Resp') R)
    (ans : List (Y ⊕ Option Resp')) :
    ((p.translate (Sum.map id sw) fun _ b => b).mapOutput f).after ans =
      Sum.map f (Sum.map id sw) (p.after ans) := by
  rw [after_mapOutput]
  have := after_translate (Sum.map id sw) (fun _ b => b) id (fun _ _ => rfl) p ans
  rw [List.map_id] at this
  rw [this]
  rcases p.after ans with r | a <;> rfl

end Main

end OracleProg


/-! ### The key-free relay under a swap of one request's side coins -/

namespace Quantum.AssignRelay

variable {X Y Resp Req' Resp' : Type} [DecidableEq X]

/-- **The recorded main request moved by `sw`**: the permutation of a relay's record moving its
main request by `sw`. -/
def recordSw (sw : Equiv.Perm Req') : Equiv.Perm (RespD X Y Resp Req' Resp') :=
  Equiv.prodCongr (Equiv.refl _) (Equiv.prodCongr (Equiv.refl _)
    (Equiv.prodCongr sw (Equiv.refl _)))

theorem recordSw_apply (sw : Equiv.Perm Req') (d : RespD X Y Resp Req' Resp') :
    recordSw sw d = (d.1, d.2.1, sw d.2.2.1, d.2.2.2) :=
  rfl

/-- **The record of a moved main request** is the record moved, for `sw` fixing the padding
request. -/
theorem recordOf_map_sw {sw : Equiv.Perm Req'} {idle : Req'} (hidle : sw idle = idle)
    (res : Reply X Y Resp × Option (Req' × Option Resp')) :
    recordOf idle (res.1, res.2.map (Prod.map sw id)) = recordSw sw (recordOf idle res) := by
  rcases res with ⟨r, o⟩
  rcases o with _ | ⟨r', a⟩
  · simp [recordOf, recordSw_apply, hidle]
  · simp [recordOf, recordSw_apply]


variable {Req Xs Ys : Type} {Q : ℕ}

open _root_.GordieHowe.OracleProg in
/-- **The resolved relay program of `G'` at a request** is `G`'s with the main request moved by
`sw` and the record by `recordSw sw`, when the resolved programs of the request are
(`hP`), the relays have the same padding request and `sw` fixes it. -/
theorem resolve_relayOfProg_swap (G G' : AssignRelay X Y Req Resp Req' Resp' Xs Ys)
    (r₀ : (Req × Fin (Q + 1)) × (X → Option Y)) (sw : Equiv.Perm Req')
    (hP : resolve G.side (G'.prog r₀.2 r₀.1.2 r₀.1.1) =
      (resolve G.side (G.prog r₀.2 r₀.1.2 r₀.1.1)).translate (Sum.map id sw) fun _ b => b)
    (hidle' : G'.idle = G.idle) (hidle : sw G.idle = G.idle) :
    resolve G.side (relayOfProg G' Q r₀) =
      ((resolve G.side (relayOfProg G Q r₀)).translate (Sum.map id sw) fun _ b => b).mapOutput
        (Option.map (recordSw sw)) := by
  unfold relayOfProg
  rw [resolve_mapOutput, resolve_recMain_tabS, hP, recMain_translate_main, mapOutput_mapOutput,
    resolve_mapOutput, resolve_recMain_tabS, translate_mapOutput, mapOutput_mapOutput]
  refine congrArg (fun f => OracleProg.mapOutput f _) (funext fun res => ?_)
  simp only [Function.comp_def, hidle', Option.map_some]
  exact congrArg some (recordOf_map_sw hidle res)

open _root_.GordieHowe.OracleProg in
/-- **The relay of `G'` against the relay of `G`, moved at one request**: the programs of `G'`
are `G`'s off `J` (`hoff`); at `r₀`, both make at most `G.qS` side reads on every path, begin
with a side read alike, and their resolved programs are related by `sw` (`hP`). -/
theorem progSwap_relayOf (G G' : AssignRelay X Y Req Resp Req' Resp' Xs Ys)
    (J : (Req × Fin (Q + 1)) × (X → Option Y) → Bool) (r₀ : (Req × Fin (Q + 1)) × (X → Option Y))
    (sw : Equiv.Perm Req') (hoff : ∀ r, J r = false → relayOfProg G' Q r = relayOfProg G Q r)
    (hs : SidesLE G.qS (relayOfProg G Q r₀)) (hs' : SidesLE G.qS (relayOfProg G' Q r₀))
    (hst : (relayOfProg G' Q r₀).startsSide = (relayOfProg G Q r₀).startsSide)
    (hP : resolve G.side (G'.prog r₀.2 r₀.1.2 r₀.1.1) =
      (resolve G.side (G.prog r₀.2 r₀.1.2 r₀.1.1)).translate (Sum.map id sw) fun _ b => b)
    (hidle' : G'.idle = G.idle) (hidle : sw G.idle = G.idle) :
    (relayOf G Q).ProgSwap (relayOf G' Q).prog J (· = r₀) sw (recordSw sw) where
  off r hr := hoff r hr
  sides r hr := hr ▸ hs
  sides' r hr := hr ▸ hs'
  starts r hr := hr ▸ hst
  on r hr ans := by
    subst hr
    change (resolve G.side (relayOfProg G' Q r)).after ans = _
    rw [resolve_relayOfProg_swap G G' r sw hP hidle' hidle, after_translate_main]
    rfl

end Quantum.AssignRelay

namespace RingSignature.KeyFree

open Quantum Signature QROM OracleProg RingSignature.Insider

variable {X Y : Type} [DecidableEq X] [Zero Y] {N n : ℕ} {TS : Signature.SchemeTypes} {RMsg : Type}
  [DecidableEq TS.PK]
  (B : BaseSigner X Y N TS RMsg)
  {Pf PC : Type} [Fintype Pf] [DecidableEq Pf] [Fintype PC]
  [DecidableEq PC] [Nonempty PC]
  {PS : ProofSystem X Y (RingStmt B) (RingWit B) ⟨Pf, PC⟩} {adm : KeyRing B.PK N → Prop}
  [DecidablePred adm] {SC X₀ R : Type} (pks : Fin n → B.PK)
  (toR : X₀ → Req B PS adm n × ℕ → B.BSig → R) (dummyR : Req B PS adm n × ℕ → R) {Q : ℕ}

/-- **A signature moved by `swσ`** in a key-free signer's output. -/
def mapSig (swσ : B.BSig → B.BSig) :
    Option (B.Pub × B.BSig × List (Assignment X Y)) →
      Option (B.Pub × B.BSig × List (Assignment X Y)) :=
  Option.map (Prod.map id (Prod.map swσ id))

omit [DecidableEq TS.PK] in
variable {B} in
theorem asgOf_mapSig (swσ : B.BSig → B.BSig) (o : Option (B.Pub × B.BSig × List (Assignment X Y))) :
    asgOf B (mapSig B swσ o) = asgOf B o := by
  rcases o with _ | _ <;> rfl

variable {B} in
omit [Fintype Pf] [DecidableEq Pf] [Fintype PC] [DecidableEq PC] [Nonempty PC] in
theorem xK_mapSig {Yb : Type} (stp : RingStmt B → OracleProg (X ⊕ X) (Y ⊕ Yb) X₀)
    (swσ : B.BSig → B.BSig) (r : Req B PS adm n)
    (o : Option (B.Pub × B.BSig × List (Assignment X Y))) :
    xK B stp r (mapSig B swσ o) = xK B stp r o := by
  rcases r with _ | _ | _ <;> rcases o with _ | _ <;> rfl

variable {B} in
omit [Fintype Pf] [DecidableEq Pf] [Fintype PC] [DecidableEq PC] [Nonempty PC] in
theorem replyOf_mapSig (swσ : B.BSig → B.BSig) (r : Req B PS adm n)
    (o : Option (B.Pub × B.BSig × List (Assignment X Y))) (a : Option (MUResponse B.core ⊕ Pf)) :
    replyOf B r (mapSig B swσ o) a = replyOf B r o a := by
  rcases r with _ | _ | _ <;> rcases o with _ | _ <;> rcases a with _ | (_ | _) <;> try rfl
  all_goals (rename_i x; rcases x with _ | _ <;> rfl)

variable {Yb Xs Ys : Type}

/-- **A program over full and base reads as a relay program makes no main request**, so moving
the main requests leaves it. -/
theorem translate_main_lift (Rd : KFReads X Y Yb Xs Ys) (Tf Tb : X → Option Y) {α Req' Resp' : Type}
    (sw : Req' → Req') (p : OracleProg (X ⊕ X) (Y ⊕ Yb) α) :
    ((Rd.lift (Req' := Req') (Resp' := Resp') Tf Tb p).translate (Sum.map id sw)
      fun _ b => b) = Rd.lift Tf Tb p := by
  rw [KFReads.lift, translate_translate]
  rfl

omit [Fintype Pf] [DecidableEq Pf] [Fintype PC] [DecidableEq PC] [Nonempty PC] in
/-- **The resolved key-free relay program with one request's signature moved**: when the resolved
signatures at the side coins `sc'` are those at `sc` with the signature moved by `swσ`
(`hsig`), and `sw` moves the main requests alike (`hsw`), the resolved program at `sc'` is the
one at `sc` with its main request moved by `sw`. -/
theorem resolve_kfProgK_swap (sc sc' : Fin Q → SC)
    (sgn : B.PK → KeyRing B.PK N → ℕ → B.Msg → SC →
      OracleProg (X ⊕ X) (Y ⊕ Yb) (Option (B.Pub × B.BSig × List (Assignment X Y))))
    (stp : RingStmt B → OracleProg (X ⊕ X) (Y ⊕ Yb) X₀) (Rd : KFReads X Y Yb Xs Ys)
    (T : X → Option Y) (c : ℕ) (r : Req B PS adm n) (swσ : B.BSig → B.BSig)
    (sw : MURequest (SignOracle.none B.core) n ⊕ R → MURequest (SignOracle.none B.core) n ⊕ R)
    (hsig : resolve Rd.side (Rd.lift (Req' := MURequest (SignOracle.none B.core) n ⊕ R)
        (Resp' := MUResponse B.core ⊕ Pf) (fun _ => none) (Rd.tabB T fun _ => none)
        (sigK B pks sc' sgn c r)) =
      (resolve Rd.side (Rd.lift (fun _ => none) (Rd.tabB T fun _ => none)
        (sigK B pks sc sgn c r))).mapOutput (mapSig B swσ))
    (hsw : ∀ o x₀, sw (reqOf B toR dummyR c r o x₀) = reqOf B toR dummyR c r (mapSig B swσ o) x₀) :
    resolve Rd.side (kfProgK B pks toR dummyR sc' sgn stp Rd T c r) =
      (resolve Rd.side (kfProgK B pks toR dummyR sc sgn stp Rd T c r)).translate (Sum.map id sw)
        fun _ b => b := by
  unfold kfProgK
  rw [resolve_bind, hsig, mapOutput_bind, resolve_bind, translate_bind,
    ← resolve_translate_main, translate_main_lift]
  refine congrArg _ (funext fun o => ?_)
  simp only [Function.comp_def]
  rw [← resolve_translate_main, translate_bind, translate_main_lift, asgOf_mapSig, xK_mapSig]
  refine congrArg _ (congrArg _ (funext fun x₀ => ?_))
  simp only [translate, translate_bind, Sum.map_inr, hsw, replyOf_mapSig]

omit [Fintype Pf] [DecidableEq Pf] [Fintype PC] [DecidableEq PC] [Nonempty PC] in
/-- **The signature reads only its own request's side coins.** -/
theorem sigK_congr {sc sc' : Fin Q → SC}
    (sgn : B.PK → KeyRing B.PK N → ℕ → B.Msg → SC →
      OracleProg (X ⊕ X) (Y ⊕ Yb) (Option (B.Pub × B.BSig × List (Assignment X Y))))
    (c : ℕ) (r : Req B PS adm n)
    (h : ∀ s Rg m (hc : c < Q), r = .sign s Rg m → sc' ⟨c, hc⟩ = sc ⟨c, hc⟩) :
    sigK B pks sc' sgn c r = sigK B pks sc sgn c r := by
  rcases r with _ | ⟨s, Rg, m⟩ | _
  · rfl
  · dsimp only [sigK]
    split_ifs with hc
    · rw [h s Rg m hc.1 rfl]
    · rfl
  · rfl

omit [Fintype Pf] [DecidableEq Pf] [Fintype PC] [DecidableEq PC] [Nonempty PC] in
/-- **The key-free relay program reads only its own request's side coins.** -/
theorem kfProgK_congr {sc sc' : Fin Q → SC}
    (sgn : B.PK → KeyRing B.PK N → ℕ → B.Msg → SC →
      OracleProg (X ⊕ X) (Y ⊕ Yb) (Option (B.Pub × B.BSig × List (Assignment X Y))))
    (stp : RingStmt B → OracleProg (X ⊕ X) (Y ⊕ Yb) X₀) (Rd : KFReads X Y Yb Xs Ys)
    (T : X → Option Y) (c : ℕ) (r : Req B PS adm n)
    (h : ∀ s Rg m (hc : c < Q), r = .sign s Rg m → sc' ⟨c, hc⟩ = sc ⟨c, hc⟩) :
    kfProgK B pks toR dummyR sc' sgn stp Rd T c r =
      kfProgK B pks toR dummyR sc sgn stp Rd T c r := by
  unfold kfProgK
  rw [sigK_congr B pks sgn c r h]

end RingSignature.KeyFree


/-! ### The key-free relay in side-read mode under a swap of side coins -/

namespace RingSignature.KeyFree

open Quantum Signature QROM OracleProg RingSignature.OracleSplit RingSignature.Insider

variable {X Y Y₁ Y₂ : Type} [AddGroup Y] [AddGroup Y₁] [AddGroup Y₂] (sp : OracleSplit Y Y₁ Y₂)

/-- **A program over the base component, as base reads in side-read mode, resolves to its run** at
the side function read through the base reads' table. -/
theorem resolve_lift_baseL_viaSide (ω : X → Y₁) (Tf Tb : X → Option Y) {α Req' Resp' : Type}
    (q : OracleProg X Y₁ α) :
    resolve ω ((KFReads.viaSide (fun y => (sp y).1) ω).lift (Req' := Req') (Resp' := Resp') Tf Tb
      (baseL sp q)) = pure (q.run fun x => ((Tb x).map fun y => (sp y).1).getD (ω x)) := by
  rw [KFReads.lift, baseL, translate_translate]
  exact resolve_translate_side ω (fun x => x) _ q

theorem KFReads.lift_bind {Yb Xs Ys α β Req' Resp' : Type} (Rd : KFReads X Y Yb Xs Ys)
    (Tf Tb : X → Option Y) (p : OracleProg (X ⊕ X) (Y ⊕ Yb) α)
    (f : α → OracleProg (X ⊕ X) (Y ⊕ Yb) β) :
    Rd.lift (Req' := Req') (Resp' := Resp') Tf Tb (p.bind f) =
      (Rd.lift Tf Tb p).bind fun a => Rd.lift Tf Tb (f a) :=
  translate_bind _ _ p f

theorem KFReads.lift_mapOutput {Yb Xs Ys α β Req' Resp' : Type} (Rd : KFReads X Y Yb Xs Ys)
    (Tf Tb : X → Option Y) (p : OracleProg (X ⊕ X) (Y ⊕ Yb) α) (f : α → β) :
    Rd.lift (Req' := Req') (Resp' := Resp') Tf Tb (p.mapOutput f) =
      (Rd.lift Tf Tb p).mapOutput f :=
  translate_mapOutput _ _ f p

variable [DecidableEq X] {N n : ℕ} {TS : Signature.SchemeTypes} {RMsg : Type} [DecidableEq TS.PK]
  (B : BaseSigner X Y N TS RMsg)
  {Pf PC : Type} [Fintype Pf] [DecidableEq Pf] [Fintype PC]
  [DecidableEq PC] [Nonempty PC]
  {PS : ProofSystem X Y (RingStmt B) (RingWit B) ⟨Pf, PC⟩}
  {adm : KeyRing B.PK N → Prop} [DecidablePred adm] {SC X₀ R Pb : Type}
  (pks : Fin n → B.PK)
  {ksign : B.PK → KeyRing B.PK N → ℕ → B.Msg → SC →
    OracleProg X Y (Option (B.Pub × B.BSig × List (Assignment X Y)))}
  (F : KFSignFactors sp Pb ksign) {stmtPω : (X → Y₁) → RingStmt B → X₀}
  (S : KFStmt stmtPω)
  (toR : X₀ → Req B PS adm n × ℕ → B.BSig → R) (dummyR : Req B PS adm n × ℕ → R) {Q : ℕ}
  [Inhabited X] [Inhabited B.Pub]

/-- **The coin hypothesis of a swap at a request**: at the request `r` with number `c`, a signing
request of a member of a supported ring, the base-component program at the side coins `sc'` runs,
at the side function `ω` read through the table `T`, as at `sc` with the signature moved by
`swσ`. -/
def CoinSwapAt (sc sc' : Fin Q → SC) (ω : X → Y₁) (T : X → Option Y) (c : ℕ)
    (r : Req B PS adm n) (swσ : B.BSig → B.BSig) : Prop :=
  ∀ s Rg m (h : c < Q ∧ pks s ∈ Rg.1 ∧ adm Rg), r = .sign s Rg m →
    (F.outB (pks s) Rg c m (sc' ⟨c, h.1⟩)).run (ωT sp ω T) =
      ((F.outB (pks s) Rg c m (sc ⟨c, h.1⟩)).run (ωT sp ω T)).map (Prod.map (Prod.map id swσ) id)

omit [Fintype Pf] [DecidableEq Pf] [Fintype PC] [DecidableEq PC] [Nonempty PC] in
/-- **The resolved signature in side-read mode under a swap of side coins** is the signature at the
original coins, moved by `swσ`. -/
theorem resolve_sigK_sgnB_swap (sc sc' : Fin Q → SC) (ω : X → Y₁) (T : X → Option Y) (c : ℕ)
    (r : Req B PS adm n) (swσ : B.BSig → B.BSig)
    (hφ : CoinSwapAt sp B pks F sc sc' ω T c r swσ) :
    resolve ω ((KFReads.viaSide (fun y => (sp y).1) ω).lift
        (Req' := MURequest (SignOracle.none B.core) n ⊕ R) (Resp' := MUResponse B.core ⊕ Pf)
        (fun _ => none) ((KFReads.viaSide (fun y => (sp y).1) ω).tabB T fun _ => none)
        (sigK B pks sc' (sgnB sp B F S) c r)) =
      (resolve ω ((KFReads.viaSide (fun y => (sp y).1) ω).lift (fun _ => none)
        ((KFReads.viaSide (fun y => (sp y).1) ω).tabB T fun _ => none)
        (sigK B pks sc (sgnB sp B F S) c r))).mapOutput (mapSig B swσ) := by
  rcases r with _ | ⟨s, Rg, m⟩ | _
  · rfl
  · dsimp only [sigK]
    split_ifs with hc
    · unfold sgnB
      rw [KFReads.lift_bind, KFReads.lift_bind, resolve_bind, resolve_bind,
        resolve_lift_baseL_viaSide, resolve_lift_baseL_viaSide]
      have hω : (fun x => (((KFReads.viaSide (fun y => (sp y).1) ω).tabB T fun _ => none) x).map
          (fun y => (sp y).1) |>.getD (ω x)) = ωT sp ω T := ωT_eq sp ω T
      simp only [OracleProg.bind]
      rw [hω, hφ s Rg m hc rfl]
      rcases (F.outB (pks s) Rg c m (sc ⟨c, hc.1⟩)).run (ωT sp ω T) with _ | ⟨⟨q, σ⟩, kp⟩
      · simp only [Option.map_none]
        rw [← resolve_mapOutput, ← KFReads.lift_mapOutput]
        congr 2
        change _ = OracleProg.query _ fun b => ((baseL sp _).mapOutput _).mapOutput _
        rw [mapOutput_mapOutput]
        rfl
      · simp only [Option.map_some, Prod.map]
        rw [← resolve_mapOutput, ← KFReads.lift_mapOutput]
        rfl
    · rfl
  · rfl

section Shape

theorem sameKind_refl {X Xs Req' : Type} (a : (X ⊕ Xs) ⊕ Req') : OracleProg.SameKind a a := by
  rcases a with (_ | _) | _ <;> constructor <;> constructor <;> trivial

theorem KFReads.lift_query {Yb Xs Ys α Req' Resp' : Type} (Rd : KFReads X Y Yb Xs Ys)
    (Tf Tb : X → Option Y) (a : X ⊕ X) (k : Y ⊕ Yb → OracleProg (X ⊕ X) (Y ⊕ Yb) α) :
    Rd.lift (Req' := Req') (Resp' := Resp') Tf Tb (query a k) =
      query (.inl (a.elim Sum.inl Rd.pt)) fun b => Rd.lift Tf Tb (k (Rd.readAns Tf Tb a b)) :=
  rfl

theorem KFReads.lift_pure {Yb Xs Ys α Req' Resp' : Type} (Rd : KFReads X Y Yb Xs Ys)
    (Tf Tb : X → Option Y) (a : α) :
    Rd.lift (Req' := Req') (Resp' := Resp') Tf Tb (pure a : OracleProg (X ⊕ X) (Y ⊕ Yb) α) =
      pure a :=
  rfl

/-- **A program over the base component, as base reads in side-read mode, keeps a lockstep** at
the same tables. -/
theorem Lockstep.lift_baseL_viaSide {α α' Req' Resp' : Type} {RO : α → α' → Prop} (ω : X → Y₁)
    (Tf Tb : X → Option Y) {q : OracleProg X Y₁ α} {q' : OracleProg X Y₁ α'}
    (h : Lockstep (fun _ _ => True) EqAt RO q q') :
    Lockstep SameKind EqAt RO
      ((KFReads.viaSide (fun y => (sp y).1) ω).lift (Req' := Req') (Resp' := Resp') Tf Tb
        (baseL sp q))
      ((KFReads.viaSide (fun y => (sp y).1) ω).lift Tf Tb (baseL sp q')) := by
  rw [KFReads.lift, KFReads.lift, baseL, baseL, translate_translate, translate_translate]
  exact h.translate (fun _ _ _ => .inl (.inr trivial)) fun _ _ _ _ _ hb he => by
    cases he
    rw [hb rfl]

/-- **A program over the base component, as base reads in side-read mode, keeps a lockstep at any
answers** through any tables. -/
theorem Lockstep.lift_baseL_viaSide_any {α α' Req' Resp' : Type} {RO : α → α' → Prop}
    (ω : X → Y₁) (Tf Tb Tf' Tb' : X → Option Y) {q : OracleProg X Y₁ α}
    {q' : OracleProg X Y₁ α'} (h : Lockstep (fun _ _ => True) (fun _ _ _ _ => True) RO q q') :
    Lockstep SameKind EqAt RO
      (translate (fun a => (.inl (a.elim Sum.inl (KFReads.viaSide (fun y => (sp y).1) ω).pt) :
          (X ⊕ X) ⊕ Req')) ((KFReads.viaSide (fun y => (sp y).1) ω).readAns (Resp' := Resp') Tf Tb)
        (baseL sp q))
      (translate (fun a => (.inl (a.elim Sum.inl (KFReads.viaSide (fun y => (sp y).1) ω).pt) :
          (X ⊕ X) ⊕ Req'))
        ((KFReads.viaSide (fun y => (sp y).1) ω).readAns (Resp' := Resp') Tf' Tb')
        (baseL sp q')) := by
  rw [baseL, baseL, translate_translate, translate_translate]
  exact h.translate (fun _ _ _ => .inl (.inr trivial)) fun _ _ _ _ _ _ => trivial

omit [Fintype Pf] [DecidableEq Pf] [Fintype PC] [DecidableEq PC] [Nonempty PC] in
/-- **The side-mode key-free relay programs at any two side coins are in lockstep**, when the
base-component signer program is in lockstep at any two side coins (`houtB`) and the statement
program at any two published values (`hstmt`). -/
theorem lockstep_kfProgK_sgnB
    (houtB : ∀ pk Rg c m s s', Lockstep (fun _ _ => True) EqAt (fun _ _ => True)
      (F.outB pk Rg c m s) (F.outB pk Rg c m s'))
    (hstmt : ∀ (Rg : KeyRing B.PK N) (m : B.Msg) (y y' : B.Pub), Lockstep (fun _ _ => True)
      (fun _ _ _ _ => True) (fun _ _ => True) (S.stmtPB ⟨Rg, m, y⟩) (S.stmtPB ⟨Rg, m, y'⟩))
    (sc sc' : Fin Q → SC) (ω : X → Y₁) (T : X → Option Y) (c : ℕ) (r : Req B PS adm n) :
    Lockstep SameKind EqAt (fun _ _ => True)
      (kfProgK B pks toR dummyR sc (sgnB sp B F S) (stpB sp B S)
        (KFReads.viaSide (fun y => (sp y).1) ω) T c r)
      (kfProgK B pks toR dummyR sc' (sgnB sp B F S) (stpB sp B S)
        (KFReads.viaSide (fun y => (sp y).1) ω) T c r) := by
  have hask : ∀ {o o' : Option (B.Pub × B.BSig × List (Assignment X Y))} (x₀ x₀' : Option X₀),
      Lockstep SameKind EqAt (fun _ _ => True)
        ((OracleProg.query (.inr (reqOf B toR dummyR c r o x₀)) fun b =>
          (OracleProg.pure (b.elim (fun _ => none) id) : OracleProg ((X ⊕ X) ⊕
            (MURequest (SignOracle.none B.core) n ⊕ R)) ((Y ⊕ Y₁) ⊕ Option (MUResponse B.core ⊕ Pf))
              (Option (MUResponse B.core ⊕ Pf)))).bind fun a => .pure (replyOf B r o a))
        ((OracleProg.query (.inr (reqOf B toR dummyR c r o' x₀')) fun b =>
          (OracleProg.pure (b.elim (fun _ => none) id) : OracleProg ((X ⊕ X) ⊕
            (MURequest (SignOracle.none B.core) n ⊕ R)) ((Y ⊕ Y₁) ⊕ Option (MUResponse B.core ⊕ Pf))
              (Option (MUResponse B.core ⊕ Pf)))).bind fun a => .pure (replyOf B r o' a)) :=
    fun _ _ => ⟨.inr trivial, fun _ _ _ => by exact trivial⟩
  rcases r with i | ⟨s, Rg, m⟩ | i
  · rw [kfProgK_congr B pks toR dummyR (sc := sc) (sc' := sc') _ _ _ T c _
      (fun _ _ _ _ h => by cases h)]
    exact (lockstep_refl sameKind_refl _).mono (fun _ _ h => h) (fun _ _ _ _ _ h => h)
      fun _ _ _ => trivial
  · unfold kfProgK
    dsimp only [sigK]
    split_ifs with hc
    · unfold sgnB
      rw [KFReads.lift_bind, KFReads.lift_bind, OracleProg.bind_assoc, OracleProg.bind_assoc]
      refine Lockstep.bind (fun o o' _ => ?_)
        (Lockstep.lift_baseL_viaSide sp ω _ _ (houtB _ _ _ _ _ _))
      rcases o with _ | ⟨⟨q, σ⟩, kp⟩ <;> rcases o' with _ | ⟨⟨q', σ'⟩, kp'⟩ <;>
        dsimp only <;>
        refine ⟨.inl (.inl trivial), fun _ _ _ => ?_⟩ <;>
        simp only [KFReads.lift, translate_mapOutput, mapOutput_bind, Function.comp_def, xK, stpB,
          translate,
          OracleProg.bind] <;>
        exact Lockstep.bind (fun _ _ _ => hask _ _)
          (Lockstep.lift_baseL_viaSide_any sp ω _ _ _ _ (hstmt Rg m _ _))
    · exact (lockstep_refl sameKind_refl _).mono (fun _ _ h => h) (fun _ _ _ _ _ h => h)
        fun _ _ _ => trivial
  · rw [kfProgK_congr B pks toR dummyR (sc := sc) (sc' := sc') _ _ _ T c _
      (fun _ _ _ _ h => by cases h)]
    exact (lockstep_refl sameKind_refl _).mono (fun _ _ h => h) (fun _ _ _ _ _ h => h)
      fun _ _ _ => trivial

theorem countsLE_translate_baseL_viaSide {α Req' Resp' : Type} (ω : X → Y₁)
    (Tf Tb : X → Option Y) {q : ℕ} {p : OracleProg X Y₁ α} (h : CountsLE (fun _ => true) q p) :
    CountsLE isSideRead q
      (translate (fun a => (.inl (a.elim Sum.inl (KFReads.viaSide (fun y => (sp y).1) ω).pt) :
          (X ⊕ X) ⊕ Req')) ((KFReads.viaSide (fun y => (sp y).1) ω).readAns (Resp' := Resp') Tf Tb)
        (baseL sp p)) := by
  rw [baseL, translate_translate]
  exact h.translate fun _ => rfl

omit [Fintype Pf] [DecidableEq Pf] [Fintype PC] [DecidableEq PC] [Nonempty PC] in
/-- **The side-mode key-free relay program makes at most `qOut + qSt` side reads on every path**,
when the base-component signer program makes at most `qOut` reads (`hcO`) and the statement
program at most `qSt` (`hcS`) on every path. -/
theorem countsLE_kfProgK_sgnB
    (hcO : ∀ pk Rg c m s, CountsLE (fun _ => true) F.qOut (F.outB pk Rg c m s))
    (hcS : ∀ x, CountsLE (fun _ => true) S.qSt (S.stmtPB x))
    (sc : Fin Q → SC) (ω : X → Y₁) (T : X → Option Y) (c : ℕ) (r : Req B PS adm n) :
    CountsLE isSideRead (F.qOut + S.qSt)
      (kfProgK B pks toR dummyR sc (sgnB sp B F S) (stpB sp B S)
        (KFReads.viaSide (fun y => (sp y).1) ω) T c r) := by
  have hask : ∀ (o : Option (B.Pub × B.BSig × List (Assignment X Y))) (x₀ : Option X₀) (q : ℕ),
      CountsLE isSideRead q
        ((OracleProg.query (.inr (reqOf B toR dummyR c r o x₀)) fun b =>
          (OracleProg.pure (b.elim (fun _ => none) id) : OracleProg ((X ⊕ X) ⊕
            (MURequest (SignOracle.none B.core) n ⊕ R)) ((Y ⊕ Y₁) ⊕ Option (MUResponse B.core ⊕ Pf))
              (Option (MUResponse B.core ⊕ Pf)))).bind fun a => .pure (replyOf B r o a)) :=
    fun _ _ _ => countsLE_query_of_false rfl fun _ => trivial
  rcases r with i | ⟨s, Rg, m⟩ | i
  · exact hask _ _ _
  · unfold kfProgK
    dsimp only [sigK]
    split_ifs with hc
    · unfold sgnB
      rw [KFReads.lift_bind, OracleProg.bind_assoc]
      refine CountsLE.bind (fun o => ?_) ?_
      · rcases o with _ | ⟨⟨q, σ⟩, kp⟩ <;>
          simp only [KFReads.lift, translate_mapOutput, mapOutput_bind, Function.comp_def, xK, stpB,
            translate, OracleProg.bind] <;>
          refine countsLE_query_of_false rfl fun _ => ?_ <;>
          exact ((countsLE_translate_baseL_viaSide sp ω _ _ (hcS _)).bind (q₂ := 0)
            fun _ => hask _ _ _).mono (Nat.add_zero _).le
      · rw [KFReads.lift]
        exact countsLE_translate_baseL_viaSide sp ω _ _ (hcO _ _ _ _ _)
    · exact (hask _ _ _)
  · exact hask _ _ _

end Shape

/-! ### The relays -/

variable {Q : ℕ}

omit [Fintype Pf] [DecidableEq Pf] [Fintype PC] [DecidableEq PC] [Nonempty PC] in
/-- **The side-mode key-free relays at two side coins are in lockstep** at every request, when the
base-component signer program is in lockstep at any two side coins and the statement program at any
two published values. -/
theorem lockstep_relayOfProg_kfRelaySide
    (houtB : ∀ pk Rg c m s s', Lockstep (fun _ _ => True) EqAt (fun _ _ => True)
      (F.outB pk Rg c m s) (F.outB pk Rg c m s'))
    (hstmt : ∀ (Rg : KeyRing B.PK N) (m : B.Msg) (y y' : B.Pub), Lockstep (fun _ _ => True)
      (fun _ _ _ _ => True) (fun _ _ => True) (S.stmtPB ⟨Rg, m, y⟩) (S.stmtPB ⟨Rg, m, y'⟩))
    (sc sc' : Fin Q → SC) (ω : X → Y₁) (idle : MURequest (SignOracle.none B.core) n ⊕ R)
    (r : (Req B PS adm n × Fin (Q + 1)) × (X → Option Y)) :
    Lockstep SameKind EqAt (fun _ _ => True)
      (AssignRelay.relayOfProg (kfRelaySide sp B pks F S toR dummyR sc ω idle) Q r)
      (AssignRelay.relayOfProg (kfRelaySide sp B pks F S toR dummyR sc' ω idle) Q r) :=
  (Lockstep.recMain (tabS r.2)
    (lockstep_kfProgK_sgnB sp B pks F S toR dummyR houtB hstmt sc sc' ω r.2 r.1.2 r.1.1)).mapOutput
      fun _ _ _ => trivial

omit [Fintype Pf] [DecidableEq Pf] [Fintype PC] [DecidableEq PC] [Nonempty PC] in
/-- **(ii-b) The side-mode key-free relay at other side coins has its shape**, when the
base-component signer program is in lockstep at any two side coins and the statement program at any
two published values. -/
theorem sameShape_kfRelaySide
    (houtB : ∀ pk Rg c m s s', Lockstep (fun _ _ => True) EqAt (fun _ _ => True)
      (F.outB pk Rg c m s) (F.outB pk Rg c m s'))
    (hstmt : ∀ (Rg : KeyRing B.PK N) (m : B.Msg) (y y' : B.Pub), Lockstep (fun _ _ => True)
      (fun _ _ _ _ => True) (fun _ _ => True) (S.stmtPB ⟨Rg, m, y⟩) (S.stmtPB ⟨Rg, m, y'⟩))
    (sc sc' : Fin Q → SC) (ω : X → Y₁) (idle : MURequest (SignOracle.none B.core) n ⊕ R) :
    (AssignRelay.relayOf (kfRelaySide sp B pks F S toR dummyR sc ω idle) Q).SameShape
      (AssignRelay.relayOf (kfRelaySide sp B pks F S toR dummyR sc' ω idle) Q).prog :=
  fun r ans => (lockstep_relayOfProg_kfRelaySide sp B pks F S toR dummyR houtB hstmt sc sc' ω idle
    r).shapeOf_after (fun _ _ _ _ _ => rfl) ans

omit [Fintype Pf] [DecidableEq Pf] [Fintype PC] [DecidableEq PC] [Nonempty PC] in
/-- **(ii-a) The side-mode key-free relay at other side coins is the relay with its programs.** -/
theorem relayOf_kfRelaySide_eq_withProg (sc sc' : Fin Q → SC) (ω : X → Y₁)
    (idle : MURequest (SignOracle.none B.core) n ⊕ R) :
    AssignRelay.relayOf (kfRelaySide sp B pks F S toR dummyR sc' ω idle) Q =
      (AssignRelay.relayOf (kfRelaySide sp B pks F S toR dummyR sc ω idle) Q).withProg
        (AssignRelay.relayOf (kfRelaySide sp B pks F S toR dummyR sc' ω idle) Q).prog :=
  rfl

omit [Fintype Pf] [DecidableEq Pf] [Fintype PC] [DecidableEq PC] [Nonempty PC] in
/-- **(ii-c) The side-mode key-free relay at side coins swapped at one request**: off `J` the side
coins agree (`hoff`); at `r₀` the base-component signer program at `sc'` runs, at the side
function read through `r₀`'s table, as at `sc` with the signature moved by `swσ`
(`CoinSwapAt`), and `sw` moves the main requests alike (`hsw`) and fixes the padding request. The
programs make at most `qOut` and `qSt` reads on every path (`hcO`, `hcS`), and are in lockstep
(`houtB`, `hstmt`). -/
theorem progSwap_kfRelaySide
    (houtB : ∀ pk Rg c m s s', Lockstep (fun _ _ => True) EqAt (fun _ _ => True)
      (F.outB pk Rg c m s) (F.outB pk Rg c m s'))
    (hstmt : ∀ (Rg : KeyRing B.PK N) (m : B.Msg) (y y' : B.Pub), Lockstep (fun _ _ => True)
      (fun _ _ _ _ => True) (fun _ _ => True) (S.stmtPB ⟨Rg, m, y⟩) (S.stmtPB ⟨Rg, m, y'⟩))
    (hcO : ∀ pk Rg c m s, CountsLE (fun _ => true) F.qOut (F.outB pk Rg c m s))
    (hcS : ∀ x, CountsLE (fun _ => true) S.qSt (S.stmtPB x))
    (sc sc' : Fin Q → SC) (ω : X → Y₁) (idle : MURequest (SignOracle.none B.core) n ⊕ R)
    (J : (Req B PS adm n × Fin (Q + 1)) × (X → Option Y) → Bool)
    (r₀ : (Req B PS adm n × Fin (Q + 1)) × (X → Option Y)) (swσ : B.BSig → B.BSig)
    (sw : Equiv.Perm (MURequest (SignOracle.none B.core) n ⊕ R))
    (hoff : ∀ r, J r = false → ∀ s Rg m (hc : (r.1.2 : ℕ) < Q), r.1.1 = .sign s Rg m →
      sc' ⟨r.1.2, hc⟩ = sc ⟨r.1.2, hc⟩)
    (hφ : CoinSwapAt sp B pks F sc sc' ω r₀.2 r₀.1.2 r₀.1.1 swσ)
    (hsw : ∀ o x₀, sw (reqOf B toR dummyR r₀.1.2 r₀.1.1 o x₀) =
      reqOf B toR dummyR r₀.1.2 r₀.1.1 (mapSig B swσ o) x₀)
    (hidle : sw idle = idle) :
    (AssignRelay.relayOf (kfRelaySide sp B pks F S toR dummyR sc ω idle) Q).ProgSwap
      (AssignRelay.relayOf (kfRelaySide sp B pks F S toR dummyR sc' ω idle) Q).prog J (· = r₀) sw
      (AssignRelay.recordSw sw) := by
  have hc : ∀ sc₁ : Fin Q → SC, SidesLE (F.qOut + S.qSt)
      (AssignRelay.relayOfProg (kfRelaySide sp B pks F S toR dummyR sc₁ ω idle) Q r₀) := fun sc₁ =>
    sidesLE_of_countsLE (CountsLE.recMain (fun _ => rfl) _
      (countsLE_kfProgK_sgnB sp B pks F S toR dummyR hcO hcS sc₁ ω r₀.2 r₀.1.2 r₀.1.1)).mapOutput
  refine AssignRelay.progSwap_relayOf _ _ J r₀ sw (fun r hr => ?_) (hc sc) (hc sc')
    (lockstep_relayOfProg_kfRelaySide sp B pks F S toR dummyR houtB hstmt sc sc' ω idle
      r₀).startsSide
    (resolve_kfProgK_swap B pks toR dummyR sc sc' _ _ _ r₀.2 r₀.1.2 r₀.1.1 swσ sw
      (resolve_sigK_sgnB_swap sp B pks F S sc sc' ω r₀.2 r₀.1.2 r₀.1.1 swσ hφ) hsw) rfl hidle
  change (recMain _ (kfProgK B pks toR dummyR sc' _ _ _ _ _ _)).mapOutput _ =
    (recMain _ (kfProgK B pks toR dummyR sc _ _ _ _ _ _)).mapOutput _
  rw [kfProgK_congr B pks toR dummyR _ _ _ _ _ _ (hoff r hr)]
  rfl


/-- **A fixed point of a sum map is fixed by its right part alone.** -/
theorem sum_map_id_of_eq_map {α β : Type} (f : α → α) (g : β → β) (a : α ⊕ β)
    (h : a = Sum.map f g a) : Sum.map id g a = a := by
  rcases a with a | b
  · rfl
  · simp only [Sum.map_inr, Sum.inr.injEq] at h ⊢
    exact h.symm

omit [Fintype Pf] [DecidableEq Pf] [Fintype PC] [DecidableEq PC] [Nonempty PC] in
/-- **The side-mode key-free relay asks fixed main requests off `J`**: when `sw` fixes the main
requests of every request failing `J` (`hsw`) and the padding request (`hidle`), the resolved
programs off `J` ask main requests fixed by `sw`. -/
theorem offTagFixed_kfRelaySide (sc : Fin Q → SC) (ω : X → Y₁)
    (idle : MURequest (SignOracle.none B.core) n ⊕ R)
    (J : (Req B PS adm n × Fin (Q + 1)) × (X → Option Y) → Bool)
    (sw : Equiv.Perm (MURequest (SignOracle.none B.core) n ⊕ R))
    (hsw : ∀ r, J r = false → ∀ o x₀, sw (reqOf B toR dummyR r.1.2 r.1.1 o x₀) =
      reqOf B toR dummyR r.1.2 r.1.1 o x₀)
    (hidle : sw idle = idle) :
    (AssignRelay.relayOf (kfRelaySide sp B pks F S toR dummyR sc ω idle) Q).OffTagFixed J sw := by
  intro r hr ans
  have hmap : ∀ o : Option (B.Pub × B.BSig × List (Assignment X Y)), mapSig B id o = o := by
    intro o
    rcases o with _ | ⟨y, σ, a⟩ <;> rfl
  have hφ : CoinSwapAt sp B pks F sc sc ω r.2 r.1.2 r.1.1 id := by
    intro s Rg m h _
    rcases (F.outB (pks s) Rg r.1.2 m (sc ⟨r.1.2, h.1⟩)).run (ωT sp ω r.2) with _ | ⟨⟨q, σ⟩, kp⟩
      <;> rfl
  have hP := AssignRelay.resolve_relayOfProg_swap (Q := Q)
    (kfRelaySide sp B pks F S toR dummyR sc ω idle) (kfRelaySide sp B pks F S toR dummyR sc ω idle)
    r sw (resolve_kfProgK_swap B pks toR dummyR sc sc _ _ _ r.2 r.1.2 r.1.1 id sw
      (resolve_sigK_sgnB_swap sp B pks F S sc sc ω r.2 r.1.2 r.1.1 id hφ)
      (fun o x₀ => by rw [hmap]; exact hsw r hr o x₀)) rfl hidle
  have ha := congrArg (fun p => OracleProg.after p ans) hP
  simp only [OracleProg.after_translate_main] at ha
  exact sum_map_id_of_eq_map _ _ _ ha

end RingSignature.KeyFree

end GordieHowe
