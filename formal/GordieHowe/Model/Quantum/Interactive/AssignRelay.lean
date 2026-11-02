-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Model.Quantum.Interactive.AssignPatchLaw
public import GordieHowe.Model.Quantum.Interactive.MultiRelay
public import GordieHowe.Model.Quantum.Pure.MultiRelayTrailing

@[expose] public section

/-!
# Relays that read the oracle and assign

A request of an outer challenger answered by a classical program that reads the oracle in force,
makes exactly one request to a main challenger, and returns the outer reply with an assignment list
(Unruh 2017, ePrint 2017/398, section 2, p. 7). This is the side relay of the absorption of an
assigning challenger (`GordieHowe/Model/Quantum/Interactive/AbsorbAssign.lean`).

- `AssignRelay X Y Req Resp Req' Resp'`: the program `prog T c r` of request number `c` with
  request `r`, given the table `T` of the assignments in force before it, over queries
  `X ⊕ Req'` (an oracle read `inl x`, answered `inl`; a main request `inr r'`, answered `inr` with
  the main reply), with at most `qG` reads and exactly one main request against
  every table, oracle and main reply (`reads_le`, `asks_eq_one`); the padding main request `idle`.
  `AssignRelay.ofPlain`, `AssignRelay.IsPlain`: a relay whose program ignores the table.
- `OracleProg.head?_filterMap_trace_combineAns`: the first main request of a relay program does
  not depend on the main replies.
- `OracleProg.recMain T p`: `p` with its reads answered through the table `T`, recording its main
  request and the main reply. `OracleProg.lower m p`: `p` as a program on `X`, each main request
  `r'` answered by running the program `m r'`. `run_lower`, `length_trace_lower_le`,
  `run_recMain_fst`, `trace_recMain`. `MultiRelay.AsksIn.recMain`: recording keeps the main
  requests. `OracleProg.NoSides.recMain`, `OracleProg.NoSideAfterAsk.recMain`: recording keeps
  the absence of side reads, and of side reads after the first main request.
-/

open Finset

namespace GordieHowe

namespace OracleProg

variable {X Y Req' Resp' R : Type}

/-- **The answers of an oracle and of main replies** to the queries of a relay program. -/
def combineAns (h : X → Y) (m : Req' → Option Resp') : X ⊕ Req' → Y ⊕ Option Resp' :=
  fun a => a.elim (fun x => .inl (h x)) fun r' => .inr (m r')

section Side

variable {Xs Ys : Type}

/-- **A query without its side reads**: an oracle read or a main request kept, a side read
dropped. -/
def dropSide : (X ⊕ Xs) ⊕ Req' → Option (X ⊕ Req')
  | .inl (.inl x) => some (.inl x)
  | .inl (.inr _) => none
  | .inr r' => some (.inr r')

variable (h : X → Y) (s : Xs → Ys) (m : Req' → Option Resp')

/-- **Answering the side reads of a composed program answers those of its parts.** -/
theorem elimSide_bind {S : Type} (s : Xs → Ys) :
    ∀ (p : OracleProg ((X ⊕ Xs) ⊕ Req') ((Y ⊕ Ys) ⊕ Option Resp') R)
      (f : R → OracleProg ((X ⊕ Xs) ⊕ Req') ((Y ⊕ Ys) ⊕ Option Resp') S),
      elimSide s (p.bind f) = (elimSide s p).bind fun r => elimSide s (f r)
  | .pure _, _ => rfl
  | .query (.inl (.inl _)) k, f => by
    change OracleProg.query _ _ = OracleProg.query _ _
    exact congrArg _ (funext fun b => elimSide_bind s (k _) f)
  | .query (.inl (.inr _)) k, f => elimSide_bind s (k _) f
  | .query (.inr _) k, f => by
    change OracleProg.query _ _ = OracleProg.query _ _
    exact congrArg _ (funext fun b => elimSide_bind s (k _) f)

/-- **A program making only oracle reads has no side reads to answer**: answering the side reads
of its translation is its translation to the oracle reads. -/
theorem elimSide_translate {A B : Type} (s : Xs → Ys) (ι : A → (X ⊕ Xs) ⊕ Req') (ι' : A → X)
    (hι : ∀ a, ι a = .inl (.inl (ι' a))) (g : A → (Y ⊕ Ys) ⊕ Option Resp' → B) :
    ∀ p : OracleProg A B R,
      elimSide s (translate ι g p) =
        translate (fun a => .inl (ι' a)) (fun a b => g a (liftAnsS b)) p
  | .pure _ => rfl
  | .query a k => by
    change elimSide s (OracleProg.query (ι a) _) = OracleProg.query _ _
    rw [hι a]
    change OracleProg.query _ _ = OracleProg.query _ _
    exact congrArg _ (funext fun b => elimSide_translate s ι ι' hι g (k _))

/-- **A program making only side reads is answered classically**: its translation to side reads,
its side reads answered by `s`, is its result at the side answers. -/
theorem elimSide_translate_side {A B : Type} (s : Xs → Ys) (ι : A → (X ⊕ Xs) ⊕ Req')
    (ι' : A → Xs) (hι : ∀ a, ι a = .inl (.inr (ι' a))) (g : A → (Y ⊕ Ys) ⊕ Option Resp' → B) :
    ∀ p : OracleProg A B R,
      elimSide s (translate ι g p) = .pure (p.run fun a => g a (.inl (.inr (s (ι' a)))))
  | .pure _ => rfl
  | .query a k => by
    change elimSide s (OracleProg.query (ι a) _) = _
    rw [hι a]
    exact elimSide_translate_side s ι ι' hι g (k _)

/-- **The side reads answered classically run as the program** against the answers of the
oracle, the side function and the main replies. -/
theorem run_elimSide : ∀ p : OracleProg ((X ⊕ Xs) ⊕ Req') ((Y ⊕ Ys) ⊕ Option Resp') R,
    (elimSide s p).run (combineAns h m) =
      p.run (combineAns (Quantum.MultiRelay.sideOracle h s) m)
  | .pure _ => rfl
  | .query (.inl (.inl _)) k => run_elimSide (k _)
  | .query (.inl (.inr _)) k => run_elimSide (k _)
  | .query (.inr _) k => run_elimSide (k _)

/-- **The trace with the side reads answered classically** is the program's trace with its side
reads dropped. -/
theorem trace_elimSide : ∀ p : OracleProg ((X ⊕ Xs) ⊕ Req') ((Y ⊕ Ys) ⊕ Option Resp') R,
    (elimSide s p).trace (combineAns h m) =
      (p.trace (combineAns (Quantum.MultiRelay.sideOracle h s) m)).filterMap dropSide
  | .pure _ => rfl
  | .query (.inl (.inl x)) k => by
    change _ :: _ = _
    rw [trace_elimSide (k _)]
    rfl
  | .query (.inl (.inr x)) k => by
    change _ = (_ :: _).filterMap _
    rw [List.filterMap_cons_none rfl, ← trace_elimSide (k _)]
    rfl
  | .query (.inr r') k => by
    change _ :: _ = _
    rw [trace_elimSide (k _)]
    rfl

/-- **An oracle read** of a relay program with side reads. -/
def isRead : (X ⊕ Xs) ⊕ Req' → Bool
  | .inl (.inl _) => true
  | _ => false

/-- **A side read** of a relay program. -/
def isSideRead : (X ⊕ Xs) ⊕ Req' → Bool
  | .inl (.inr _) => true
  | _ => false

/-- Dropping the side reads keeps the oracle reads. -/
theorem length_filter_isLeft_filterMap_dropSide (l : List ((X ⊕ Xs) ⊕ Req')) :
    ((l.filterMap dropSide).filter Sum.isLeft).length = (l.filter isRead).length := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    rcases a with (x | x) | r' <;>
      simp only [dropSide, isRead, List.filterMap_cons, List.filter_cons, Sum.isLeft_inl,
        Sum.isLeft_inr, ite_true, Bool.false_eq_true, ite_false, List.length_cons] <;> omega

/-- Dropping the side reads keeps the main requests. -/
theorem filterMap_getRight_filterMap_dropSide (l : List ((X ⊕ Xs) ⊕ Req')) :
    (l.filterMap dropSide).filterMap Sum.getRight? = l.filterMap Sum.getRight? := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    rcases a with (x | x) | r' <;> simp [dropSide, List.filterMap_cons, Sum.getRight?, ih]

/-- **A side-read-free program answers its side reads by nothing**: eliminating the side reads of
`plainOf p` gives `p`. -/
theorem elimSide_plainOf : ∀ p : OracleProg (X ⊕ Req') (Y ⊕ Option Resp') R,
    elimSide s (Quantum.MultiRelay.plainOf p) = p
  | .pure _ => rfl
  | .query (.inl x) k => by
    change OracleProg.query _ (fun b => elimSide s (Quantum.MultiRelay.plainOf (k _))) = _
    congr 1
    funext b
    rcases b with y | a <;> exact elimSide_plainOf (k _)
  | .query (.inr r') k => by
    change OracleProg.query _ (fun b => elimSide s (Quantum.MultiRelay.plainOf (k _))) = _
    congr 1
    funext b
    rcases b with y | a <;> exact elimSide_plainOf (k _)

/-- **The answers to a side-read-free program** read through `plainAns` are the plain answers. -/
theorem plainAns_combineAns (a : X ⊕ Req') :
    Quantum.MultiRelay.plainAns (combineAns (Quantum.MultiRelay.sideOracle h s) m
      (Sum.map Sum.inl id a)) = combineAns h m a := by
  rcases a with x | r' <;> rfl

/-- **The trace of a side-read-free program as a relay program**: its trace, lifted. -/
theorem trace_plainOf (p : OracleProg (X ⊕ Req') (Y ⊕ Option Resp') R) :
    (Quantum.MultiRelay.plainOf (Xs := Xs) (Ys := Ys) p).trace
        (combineAns (Quantum.MultiRelay.sideOracle h s) m) =
      (p.trace (combineAns h m)).map (Sum.map Sum.inl id) := by
  rw [Quantum.MultiRelay.plainOf, trace_translate]
  exact congrArg (fun o => (p.trace o).map _) (funext (plainAns_combineAns h s m))

/-- Lifted reads have as many reads. -/
theorem length_filter_isLeft_map_inl (l : List (X ⊕ Req')) :
    ((l.map (Sum.map (Sum.inl : X → X ⊕ Xs) id)).filter Sum.isLeft).length =
      (l.filter Sum.isLeft).length := by
  induction l with
  | nil => rfl
  | cons a l ih => rcases a with x | r' <;> simp [List.filter_cons, ih]

/-- Lifted reads are oracle reads. -/
theorem length_filter_isRead_map_inl (l : List (X ⊕ Req')) :
    ((l.map (Sum.map (Sum.inl : X → X ⊕ Xs) id)).filter isRead).length =
      (l.filter Sum.isLeft).length := by
  induction l with
  | nil => rfl
  | cons a l ih => rcases a with x | r' <;> simp [List.filter_cons, isRead, ih]

/-- Lifted reads are no side reads. -/
theorem length_filter_isSideRead_map_inl (l : List (X ⊕ Req')) :
    ((l.map (Sum.map (Sum.inl : X → X ⊕ Xs) id)).filter isSideRead).length = 0 := by
  induction l with
  | nil => rfl
  | cons a l ih => rcases a with x | r' <;> simp [List.filter_cons, isSideRead, ih]

/-- **A relay program without side points makes no side read.** -/
theorem length_filter_isSideRead_of_isEmpty [IsEmpty Xs] (l : List ((X ⊕ Xs) ⊕ Req')) :
    (l.filter isSideRead).length = 0 := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    rcases a with (x | x) | r'
    · simpa [List.filter_cons, isSideRead] using ih
    · exact isEmptyElim x
    · simpa [List.filter_cons, isSideRead] using ih

/-- **A relay program without side points does not begin with a side read.** -/
theorem startsSide_of_isEmpty [IsEmpty Xs] {B : Type}
    (p : OracleProg ((X ⊕ Xs) ⊕ Req') B R) : p.startsSide = false := by
  cases p with
  | pure _ => rfl
  | query a k =>
    rcases a with (x | x) | r'
    · rfl
    · exact isEmptyElim x
    · rfl

/-- A side-read-free program does not begin with a side read. -/
theorem startsSide_plainOf (p : OracleProg (X ⊕ Req') (Y ⊕ Option Resp') R) :
    (Quantum.MultiRelay.plainOf (Xs := Xs) (Ys := Ys) p : OracleProg _ _ R).startsSide = false := by
  cases p with
  | pure _ => rfl
  | query a k => rcases a with x | r' <;> rfl

/-- Lifted reads have the same main requests. -/
theorem filterMap_getRight_map_inl (l : List (X ⊕ Req')) :
    (l.map (Sum.map (Sum.inl : X → X ⊕ Xs) id)).filterMap Sum.getRight? =
      l.filterMap Sum.getRight? := by
  induction l with
  | nil => rfl
  | cons a l ih => rcases a with x | r' <;> simp [List.filterMap_cons, ih]

end Side

/-- **The program `p` with its reads answered through the table `T`**, recording its first main
request and the main reply. -/
def recMain (T : X → Option Y) :
    OracleProg (X ⊕ Req') (Y ⊕ Option Resp') R →
      OracleProg (X ⊕ Req') (Y ⊕ Option Resp') (R × Option (Req' × Option Resp'))
  | .pure r => .pure (r, none)
  | .query (.inl x) k => .query (.inl x) fun b =>
      recMain T (k (b.elim (fun y => .inl ((T x).getD y)) .inr))
  | .query (.inr r') k => .query (.inr r') fun b =>
      (recMain T (k b)).mapOutput fun p => (p.1, some (r', b.elim (fun _ => none) id))

/-- **Recording keeps a program without side reads without side reads.** -/
theorem NoSides.recMain {Xs Ys : Type} (T : X ⊕ Xs → Option (Y ⊕ Ys)) :
    ∀ {p : OracleProg ((X ⊕ Xs) ⊕ Req') ((Y ⊕ Ys) ⊕ Option Resp') R}, p.NoSides →
      (recMain T p).NoSides
  | .pure _, _ => trivial
  | .query (.inl _) _, h => ⟨h.1, fun _ => NoSides.recMain T (h.2 _)⟩
  | .query (.inr _) _, h => ⟨h.1, fun b => (NoSides.recMain T (h.2 b)).mapOutput _⟩

/-- **Recording keeps a program without side reads after its first main request so.** -/
theorem NoSideAfterAsk.recMain {Xs Ys : Type} (T : X ⊕ Xs → Option (Y ⊕ Ys)) :
    ∀ {p : OracleProg ((X ⊕ Xs) ⊕ Req') ((Y ⊕ Ys) ⊕ Option Resp') R}, p.NoSideAfterAsk →
      (recMain T p).NoSideAfterAsk
  | .pure _, _ => trivial
  | .query (.inl _) _, h => fun _ => NoSideAfterAsk.recMain T (h _)
  | .query (.inr _) _, h => fun b => ((h b).recMain T).mapOutput _

/-- **The program `p` as a program on `X`**: each main request `r'` is answered by running the
program `m r'`. -/
def lower (m : Req' → OracleProg X Y (Option Resp')) :
    OracleProg (X ⊕ Req') (Y ⊕ Option Resp') R → OracleProg X Y R
  | .pure r => .pure r
  | .query (.inl x) k => .query x fun y => lower m (k (.inl y))
  | .query (.inr r') k => (m r').bind fun a => lower m (k (.inr a))

/-- **A lowered program runs as the program against the oracle and the main programs' runs.** -/
theorem run_lower (m : Req' → OracleProg X Y (Option Resp')) (H : X → Y) :
    ∀ p : OracleProg (X ⊕ Req') (Y ⊕ Option Resp') R,
      (lower m p).run H = p.run (combineAns H fun r' => (m r').run H)
  | .pure _ => rfl
  | .query (.inl x) k => run_lower m H (k (.inl (H x)))
  | .query (.inr r') k => by
    simp only [lower]
    rw [run_bind]
    exact run_lower m H (k (.inr ((m r').run H)))

/-- **The trace of a lowered program**: each read is one query, each main request the queries of its
main program. -/
theorem length_trace_lower_le (m : Req' → OracleProg X Y (Option Resp')) (H : X → Y) {q' : ℕ}
    (hm : ∀ r', ((m r').trace H).length ≤ q') :
    ∀ p : OracleProg (X ⊕ Req') (Y ⊕ Option Resp') R,
      ((lower m p).trace H).length ≤
        ((p.trace (combineAns H fun r' => (m r').run H)).filter Sum.isLeft).length +
          q' * ((p.trace (combineAns H fun r' => (m r').run H)).filter Sum.isRight).length
  | .pure _ => by simp [lower, trace]
  | .query (.inl x) k => by
    have ih := length_trace_lower_le m H hm (k (.inl (H x)))
    simp only [lower, trace, List.length_cons, combineAns, Sum.elim_inl, List.filter_cons,
      Sum.isLeft_inl, Sum.isRight_inl, ite_true, Bool.false_eq_true, ite_false] at ih ⊢
    omega
  | .query (.inr r') k => by
    have ih := length_trace_lower_le m H hm (k (.inr ((m r').run H)))
    simp only [lower, trace_bind, List.length_append, trace, combineAns, Sum.elim_inr,
      List.filter_cons, Sum.isLeft_inr, Sum.isRight_inr, ite_true, Bool.false_eq_true, ite_false,
      List.length_cons] at ih ⊢
    have := hm r'
    rw [Nat.mul_succ]
    omega

variable (T : X → Option Y) (h : X → Y) (m : Req' → Option Resp')

/-- **A program recording its main request runs as the program reading through the table.** -/
theorem run_recMain_fst : ∀ p : OracleProg (X ⊕ Req') (Y ⊕ Option Resp') R,
    ((recMain T p).run (combineAns h m)).1 = p.run (combineAns (Quantum.reprogT T h) m)
  | .pure _ => rfl
  | .query (.inl x) k => run_recMain_fst (k (.inl ((T x).getD (h x))))
  | .query (.inr r') k => by
    simp only [recMain, run, combineAns, Sum.elim_inr, run_mapOutput]
    exact run_recMain_fst (k (.inr (m r')))

/-- **A program recording its main request makes the queries of the program reading through the
table.** -/
theorem trace_recMain : ∀ p : OracleProg (X ⊕ Req') (Y ⊕ Option Resp') R,
    (recMain T p).trace (combineAns h m) = p.trace (combineAns (Quantum.reprogT T h) m)
  | .pure _ => rfl
  | .query (.inl x) k => by
    simp only [recMain, trace, combineAns, Sum.elim_inl]
    exact congrArg (.inl x :: ·) (trace_recMain (k (.inl ((T x).getD (h x)))))
  | .query (.inr r') k => by
    simp only [recMain, trace, combineAns, Sum.elim_inr, trace_mapOutput]
    exact congrArg (.inr r' :: ·) (trace_recMain (k (.inr (m r'))))

/-- **The recorded main request** is the first main request of the program reading through the
table, with its main reply. -/
theorem run_recMain_snd : ∀ (p : OracleProg (X ⊕ Req') (Y ⊕ Option Resp') R) (r' : Req')
    (rest : List Req'),
    (p.trace (combineAns (Quantum.reprogT T h) m)).filterMap Sum.getRight? = r' :: rest →
    ((recMain T p).run (combineAns h m)).2 = some (r', m r')
  | .pure _, _, _, hp => by simp [trace] at hp
  | .query (.inl x) k, r', rest, hp => by
    simp only [trace, combineAns, Sum.elim_inl, List.filterMap_cons, Sum.getRight?_inl] at hp
    exact run_recMain_snd (k (.inl ((T x).getD (h x)))) r' rest hp
  | .query (.inr r₀) k, r', rest, hp => by
    simp only [trace, combineAns, Sum.elim_inr, List.filterMap_cons, Sum.getRight?_inr,
      List.cons.injEq] at hp
    obtain ⟨rfl, -⟩ := hp
    simp only [recMain, run, combineAns, Sum.elim_inr, run_mapOutput]
    rfl

/-- **A program without main requests** runs alike against main replies that differ. -/
theorem run_trace_congr_of_noMain (o o' : X ⊕ Req' → Y ⊕ Option Resp')
    (ho : ∀ x, o (.inl x) = o' (.inl x)) : ∀ p : OracleProg (X ⊕ Req') (Y ⊕ Option Resp') R,
    (p.trace o).filterMap Sum.getRight? = [] → p.run o = p.run o' ∧ p.trace o = p.trace o'
  | .pure _, _ => ⟨rfl, rfl⟩
  | .query (.inl x) k, hp => by
    simp only [trace, List.filterMap_cons, Sum.getRight?_inl] at hp
    obtain ⟨h1, h2⟩ := run_trace_congr_of_noMain o o' ho (k (o (.inl x))) hp
    simp only [run, trace]
    rw [← ho x]
    exact ⟨h1, congrArg (.inl x :: ·) h2⟩
  | .query (.inr r') k, hp => by simp [trace] at hp

/-- **The first main request of a relay program does not depend on the main replies.** -/
theorem head?_filterMap_trace_combineAns (h : X → Y) (m m' : Req' → Option Resp') :
    ∀ p : OracleProg (X ⊕ Req') (Y ⊕ Option Resp') R,
      ((p.trace (combineAns h m)).filterMap Sum.getRight?).head? =
        ((p.trace (combineAns h m')).filterMap Sum.getRight?).head?
  | .pure _ => rfl
  | .query (.inl x) k => by
    simp only [trace, combineAns, Sum.elim_inl, List.filterMap_cons, Sum.getRight?_inl]
    exact head?_filterMap_trace_combineAns h m m' (k (.inl (h x)))
  | .query (.inr r') k => by
    simp [trace, combineAns]

section SideTab

variable {Xs Ys : Type} (h : X → Y) (s : Xs → Ys) (m : Req' → Option Resp')

/-- **The table of a relay program with side reads**: the table `T` at the oracle reads, nothing
at the side reads. -/
def tabS (T : X → Option Y) : X ⊕ Xs → Option (Y ⊕ Ys) :=
  Sum.elim (fun x => (T x).map Sum.inl) fun _ => none

/-- **Reading through `tabS T` with the side function** is reading through `T` beside the side
function. -/
theorem reprogT_tabS (T : X → Option Y) :
    Quantum.reprogT (tabS (Ys := Ys) T) (Quantum.MultiRelay.sideOracle h s) =
      Quantum.MultiRelay.sideOracle (Quantum.reprogT T h) s := by
  funext a
  rcases a with x | x
  · simp only [Quantum.reprogT, tabS, Sum.elim_inl, Quantum.MultiRelay.sideOracle, Sum.map_inl]
    cases T x <;> rfl
  · rfl

/-- **A recording with side reads runs as the recording with the side reads answered
classically.** -/
theorem run_recMain_tabS (T : X → Option Y) :
    ∀ p : OracleProg ((X ⊕ Xs) ⊕ Req') ((Y ⊕ Ys) ⊕ Option Resp') R,
      (recMain (tabS T) p).run (combineAns (Quantum.MultiRelay.sideOracle h s) m) =
        (recMain T (elimSide s p)).run (combineAns h m)
  | .pure _ => rfl
  | .query (.inl (.inl x)) k => by
    have := run_recMain_tabS T (k (.inl (.inl ((T x).getD (h x)))))
    simp only [recMain, elimSide, run, combineAns, Sum.elim_inl, Quantum.MultiRelay.sideOracle,
      Sum.map_inl, tabS, liftAnsS] at this ⊢
    cases hT : T x <;> simpa [hT] using this
  | .query (.inl (.inr x)) k => by
    simp only [recMain, elimSide, run, combineAns, Sum.elim_inl, Quantum.MultiRelay.sideOracle,
      Sum.map_inr, tabS, Sum.elim_inr, Option.getD_none]
    exact run_recMain_tabS T (k _)
  | .query (.inr r') k => by
    simp only [recMain, elimSide, run, combineAns, Sum.elim_inr, run_mapOutput, liftAnsS]
    rw [run_recMain_tabS T (k _)]

/-- **A recording with side reads makes the reads of the recording with the side reads answered
classically**, and its side reads. -/
theorem filterMap_trace_recMain_tabS (T : X → Option Y)
    (p : OracleProg ((X ⊕ Xs) ⊕ Req') ((Y ⊕ Ys) ⊕ Option Resp') R) :
    ((recMain (tabS T) p).trace (combineAns (Quantum.MultiRelay.sideOracle h s) m)).filterMap
        dropSide = (recMain T (elimSide s p)).trace (combineAns h m) := by
  rw [trace_recMain, trace_recMain, trace_elimSide, reprogT_tabS]

end SideTab

end OracleProg

end GordieHowe

namespace GordieHowe.Quantum

open GordieHowe.OracleProg

namespace MultiRelay

variable {X Y Req' Resp' R : Type} (ansM : List Req' → Req' → Option Resp') (H : X → Y)

/-- **A program with at most one main request has a run** against the oracle and the main replies
after `rs`, with its result, its main request and its reads. -/
theorem runsWith_of_asks_le_one [Zero Y] : ∀ (rs : List Req')
    (p : OracleProg (X ⊕ Req') (Y ⊕ Option Resp') R),
    ((p.trace (combineAns H (ansM rs))).filterMap Sum.getRight?).length ≤ 1 →
    RunsWith ansM H rs p (p.run (combineAns H (ansM rs)))
      ((p.trace (combineAns H (ansM rs))).filterMap Sum.getRight?)
      ((p.trace (combineAns H (ansM rs))).filter Sum.isLeft).length
  | rs, .pure r, _ => RunsWith.pure rs r
  | rs, .query (.inl x) k, hp => by
    simp only [OracleProg.trace, combineAns, Sum.elim_inl, List.filterMap_cons, Sum.getRight?_inl,
      List.filter_cons, Sum.isLeft_inl, ite_true, List.length_cons, OracleProg.run] at hp ⊢
    exact RunsWith.query_inl x (runsWith_of_asks_le_one rs (k (.inl (H x))) hp)
  | rs, .query (.inr r') k, hp => by
    simp only [OracleProg.trace, combineAns, Sum.elim_inr, List.filterMap_cons, Sum.getRight?_inr,
      List.filter_cons, Sum.isLeft_inr, Bool.false_eq_true, ite_false, List.length_cons,
      OracleProg.run] at hp ⊢
    have h0 : ((k (.inr (ansM rs r'))).trace (combineAns H (ansM rs))).filterMap
        Sum.getRight? = [] := List.eq_nil_of_length_eq_zero (by omega)
    obtain ⟨h1, h2⟩ := run_trace_congr_of_noMain (combineAns H (ansM rs))
      (combineAns H (ansM (rs ++ [r']))) (fun _ => rfl) (k (.inr (ansM rs r'))) h0
    have ih := runsWith_of_asks_le_one (rs ++ [r']) (k (.inr (ansM rs r')))
      (by rw [← h2, h0]; exact Nat.zero_le _)
    rw [← h1, ← h2, h0] at ih
    rw [h0]
    exact RunsWith.query_inr r' ih

/-- A run with an equal result. -/
def ProgRun.castRes {R : Type} {rs : List Req'} {p : OracleProg (X ⊕ Req') (Y ⊕ Option Resp') R}
    {res res' : R} (h : res = res') (S : ProgRun ansM H rs p res) : ProgRun ansM H rs p res' :=
  h ▸ S

theorem ProgRun.acts_castRes {R : Type} {rs : List Req'}
    {p : OracleProg (X ⊕ Req') (Y ⊕ Option Resp') R} {res res' : R} (h : res = res')
    (S : ProgRun ansM H rs p res) : (S.castRes ansM H h).acts = S.acts := by
  subst h
  rfl

/-- **A program with at most one main request has a run whose actions are its trace** against the
oracle and the main replies after `rs`. -/
theorem progRun_of_asks_le_one : ∀ (rs : List Req')
    (p : OracleProg (X ⊕ Req') (Y ⊕ Option Resp') R),
    ((p.trace (combineAns H (ansM rs))).filterMap Sum.getRight?).length ≤ 1 →
    ∃ S : ProgRun ansM H rs p (p.run (combineAns H (ansM rs))),
      S.acts = p.trace (combineAns H (ansM rs))
  | rs, .pure r, _ => ⟨ProgRun.pure rs r, rfl⟩
  | rs, .query (.inl x) k, hp => by
    simp only [OracleProg.trace, combineAns, Sum.elim_inl, List.filterMap_cons, Sum.getRight?_inl,
      OracleProg.run] at hp ⊢
    obtain ⟨S, hS⟩ := progRun_of_asks_le_one rs (k (.inl (H x))) hp
    have hrs : rs = rs ++ asksOf [(.inl x : X ⊕ Req')] := by simp [asksOf]
    refine ⟨ProgRun.query (.inl x) k (S.cast hrs rfl), ?_⟩
    change .inl x :: (S.cast hrs rfl).acts = _
    rw [ProgRun.acts_cast, hS]
  | rs, .query (.inr r') k, hp => by
    simp only [OracleProg.trace, combineAns, Sum.elim_inr, List.filterMap_cons, Sum.getRight?_inr,
      List.length_cons, OracleProg.run] at hp ⊢
    have h0 : ((k (.inr (ansM rs r'))).trace (combineAns H (ansM rs))).filterMap
        Sum.getRight? = [] := List.eq_nil_of_length_eq_zero (by omega)
    obtain ⟨h1, h2⟩ := run_trace_congr_of_noMain (combineAns H (ansM rs))
      (combineAns H (ansM (rs ++ [r']))) (fun _ => rfl) (k (.inr (ansM rs r'))) h0
    obtain ⟨S, hS⟩ := progRun_of_asks_le_one (rs ++ [r']) (k (.inr (ansM rs r')))
      (by rw [← h2, h0]; exact Nat.zero_le _)
    have hrs : rs ++ [r'] = rs ++ asksOf [(.inr r' : X ⊕ Req')] := by simp [asksOf]
    have hk : k (.inr (ansM rs r')) = k (answerOf ansM H rs [] (.inr r')) := by
      simp [answerOf]
    refine ⟨(ProgRun.query (.inr r') k (S.cast hrs hk)).castRes ansM H h1.symm, ?_⟩
    rw [ProgRun.acts_castRes]
    change .inr r' :: (S.cast hrs hk).acts = _
    rw [ProgRun.acts_cast, hS, ← h2]

/-- **Recording the main request keeps the main requests.** -/
theorem AsksIn.recMain {R : Type} (T : X → Option Y) {P : Req' → Prop} :
    ∀ {p : OracleProg (X ⊕ Req') (Y ⊕ Option Resp') R}, AsksIn Resp' p P →
      AsksIn Resp' (OracleProg.recMain T p) P
  | .pure _, _ => AsksIn.pure _ P
  | .query (.inl x) k, hp => by
    refine AsksIn.query (fun r' h => by cases h) fun b => ?_
    exact AsksIn.recMain T fun ans r' h => hp (_ :: ans) r' (by simpa using h)
  | .query (.inr r₀) k, hp => by
    refine AsksIn.query (fun r' h => hp [] r' (by cases h; simp)) fun b => ?_
    exact (AsksIn.recMain T fun ans r' h => hp (b :: ans) r' (by simpa using h)).mapOutput _

/-- **Answering the side reads keeps the main requests.** -/
theorem AsksIn.elimSide {Xs Ys R : Type} (s : Xs → Ys) {P : Req' → Prop} :
    ∀ {p : OracleProg ((X ⊕ Xs) ⊕ Req') ((Y ⊕ Ys) ⊕ Option Resp') R},
      AsksIn Resp' p P → AsksIn Resp' (OracleProg.elimSide s p) P
  | .pure _, _ => AsksIn.pure _ P
  | .query (.inl (.inl x)) k, hp =>
    AsksIn.query (fun r' h => by cases h) fun b =>
      AsksIn.elimSide s fun ans r' h => hp (_ :: ans) r' h
  | .query (.inl (.inr x)) k, hp => AsksIn.elimSide s (p := k _) fun ans r' h => hp (_ :: ans) r' h
  | .query (.inr r₀) k, hp =>
    AsksIn.query (fun r' h => hp [] r' (by cases h; rfl)) fun b =>
      AsksIn.elimSide s fun ans r' h => hp (_ :: ans) r' h

/-- **Recording the main request through the table, with the side reads answered**, keeps the
main requests of the program with its side reads answered. -/
theorem AsksIn.elimSide_recMain_tabS {Xs Ys R : Type} (s : Xs → Ys) (T : X → Option Y)
    {P : Req' → Prop} :
    ∀ {p : OracleProg ((X ⊕ Xs) ⊕ Req') ((Y ⊕ Ys) ⊕ Option Resp') R},
      AsksIn Resp' (OracleProg.elimSide s p) P →
        AsksIn Resp' (OracleProg.elimSide s (OracleProg.recMain (OracleProg.tabS T) p)) P
  | .pure _, _ => AsksIn.pure _ P
  | .query (.inl (.inl x)) k, hp => by
    refine AsksIn.query (fun r' h => by cases h) fun b => ?_
    have hb : (OracleProg.liftAnsS (Ys := Ys) b).elim
        (fun y => Sum.inl ((OracleProg.tabS (Xs := Xs) (Ys := Ys) T (.inl x)).getD y)) Sum.inr =
        OracleProg.liftAnsS (b.elim (fun y => .inl ((T x).getD y)) .inr) := by
      rcases b with y | a
      · cases hT : T x <;> simp [OracleProg.liftAnsS, OracleProg.tabS, hT]
      · rfl
    change AsksIn _ (OracleProg.elimSide s (OracleProg.recMain (OracleProg.tabS T)
      (k ((OracleProg.liftAnsS b).elim (fun y => Sum.inl ((OracleProg.tabS (Xs := Xs) (Ys := Ys) T
        (.inl x)).getD y)) Sum.inr)))) P
    rw [hb]
    exact AsksIn.elimSide_recMain_tabS s T fun ans r' h => hp (_ :: ans) r' h
  | .query (.inl (.inr x)) k, hp => AsksIn.elimSide_recMain_tabS s T (p := k _) hp
  | .query (.inr r₀) k, hp => by
    refine AsksIn.query (fun r' h => hp [] r' (by cases h; rfl)) fun b => ?_
    change AsksIn _ (OracleProg.elimSide s (OracleProg.mapOutput _ (OracleProg.recMain _ (k _)))) P
    rw [OracleProg.mapOutput, OracleProg.elimSide_bind]
    exact (AsksIn.elimSide_recMain_tabS s T fun ans r' h => hp (b :: ans) r' h).bind
      fun _ => AsksIn.pure _ _

end MultiRelay

/-! ### Relays that read the oracle and assign -/

/-- **A relay that reads the oracle and assigns** (module docstring): the program `prog T c r` of
request number `c` with request `r`, given the table `T` of the assignments in force before it,
over oracle reads `inl (inl x)`, side reads `inl (inr x)` and main requests `inr r'`; the padding
main request `idle`; the side function `side` answering the side reads; at most `qG` oracle reads,
at most `qS` side reads and exactly one main request against every table, oracle and main reply;
`qP` pad sub-slots (`MultiRelay.qP`), one for every program that begins with a side read. A relay
without side reads is `AssignRelay.ofProg`, one that also ignores the table
`AssignRelay.ofPlain`. -/
structure AssignRelay (X Y Req Resp Req' Resp' : Type) (Xs : Type := Empty) (Ys : Type := Unit)
    where
  /-- The program of request number `c` with request `r`, given the table in force. -/
  prog : (X → Option Y) → ℕ → Req →
    OracleProg ((X ⊕ Xs) ⊕ Req') ((Y ⊕ Ys) ⊕ Option Resp') (Reply X Y Resp)
  /-- The oracle reads per request. -/
  qG : ℕ
  /-- The padding main request. -/
  idle : Req'
  /-- The side function answering the side reads. -/
  side : Xs → Ys := by exact fun x => nomatch x
  /-- The side reads per request. -/
  qS : ℕ := 0
  /-- The pad sub-slots per request: a query of the fixed point `default` before a program that
  begins with a side read, since every step of the dilated distinguisher ends in a query. -/
  qP : ℕ := 0
  /-- At most one pad sub-slot. -/
  qP_le_one : qP ≤ 1 := by decide
  /-- Pad sub-slots only for a relay with side reads. -/
  qP_spec : qP = 0 ∨ Nonempty Xs := by exact Or.inl rfl
  /-- A pad sub-slot for every program that begins with a side read. -/
  pad_le : ∀ T c r, (prog T c r).startsSide = true → 1 ≤ qP
  /-- At most `qG` oracle reads. -/
  reads_le : ∀ T c r (h : X → Y) (m : Req' → Option Resp'),
    (((prog T c r).trace (combineAns (MultiRelay.sideOracle h side) m)).filter
      isRead).length ≤ qG
  /-- At most `qS` side reads. -/
  sides_le : ∀ T c r (h : X → Y) (m : Req' → Option Resp'),
    (((prog T c r).trace (combineAns (MultiRelay.sideOracle h side) m)).filter
      isSideRead).length ≤ qS
  /-- Exactly one main request. -/
  asks_eq_one : ∀ T c r (h : X → Y) (m : Req' → Option Resp'),
    (((prog T c r).trace (combineAns (MultiRelay.sideOracle h side) m)).filterMap
      Sum.getRight?).length = 1

namespace AssignRelay

variable {X Y Req Resp Req' Resp' Xs Ys : Type}

/-- **A relay without side reads**: the program of the table `T`, request number `c` and request
`r` over oracle reads and main requests. -/
def ofProg
    (prog : (X → Option Y) → ℕ → Req → OracleProg (X ⊕ Req') (Y ⊕ Option Resp') (Reply X Y Resp))
    (qG : ℕ) (idle : Req')
    (reads_le : ∀ T c r (h : X → Y) (m : Req' → Option Resp'),
      (((prog T c r).trace (combineAns h m)).filter Sum.isLeft).length ≤ qG)
    (asks_eq_one : ∀ T c r (h : X → Y) (m : Req' → Option Resp'),
      (((prog T c r).trace (combineAns h m)).filterMap Sum.getRight?).length = 1) :
    AssignRelay X Y Req Resp Req' Resp' where
  prog T c r := MultiRelay.plainOf (prog T c r)
  qG := qG
  idle := idle
  pad_le T c r h := by rw [startsSide_plainOf] at h; cases h
  reads_le T c r h m := by
    rw [trace_plainOf, length_filter_isRead_map_inl]
    exact reads_le T c r h m
  sides_le T c r h m := by
    rw [trace_plainOf, length_filter_isSideRead_map_inl]
  asks_eq_one T c r h m := by
    rw [trace_plainOf, filterMap_getRight_map_inl]
    exact asks_eq_one T c r h m

/-- **A relay whose program ignores the table in force.** -/
def ofPlain (prog : ℕ → Req → OracleProg (X ⊕ Req') (Y ⊕ Option Resp') (Reply X Y Resp))
    (qG : ℕ) (idle : Req')
    (reads_le : ∀ c r (h : X → Y) (m : Req' → Option Resp'),
      (((prog c r).trace (combineAns h m)).filter Sum.isLeft).length ≤ qG)
    (asks_eq_one : ∀ c r (h : X → Y) (m : Req' → Option Resp'),
      (((prog c r).trace (combineAns h m)).filterMap Sum.getRight?).length = 1) :
    AssignRelay X Y Req Resp Req' Resp' :=
  ofProg (fun _ => prog) qG idle (fun _ => reads_le) fun _ => asks_eq_one

/-- **A relay without side reads has no pad sub-slots.** -/
theorem qP_eq_zero [IsEmpty Xs] (G : AssignRelay X Y Req Resp Req' Resp' Xs Ys) : G.qP = 0 :=
  G.qP_spec.resolve_right fun ⟨x⟩ => isEmptyElim x

/-- **A family of relays without side reads has no pad sub-slots.** -/
theorem qP_le_zero [IsEmpty Xs] {S : Type} (G : S → AssignRelay X Y Req Resp Req' Resp' Xs Ys) :
    ∀ s, (G s).qP ≤ 0 :=
  fun s => (G s).qP_eq_zero.le

/-- **A relay whose program ignores the table in force.** -/
def IsPlain (G : AssignRelay X Y Req Resp Req' Resp' Xs Ys) : Prop :=
  ∀ T T', G.prog T = G.prog T'

variable (G : AssignRelay X Y Req Resp Req' Resp' Xs Ys)

/-- **The program with its side reads answered by the side function**, classically. -/
def elimProg (T : X → Option Y) (c : ℕ) (r : Req) :
    OracleProg (X ⊕ Req') (Y ⊕ Option Resp') (Reply X Y Resp) :=
  elimSide G.side (G.prog T c r)

/-- **A relay whose program ignores the table** answers its side reads by a program ignoring it. -/
theorem IsPlain.elimProg {G : AssignRelay X Y Req Resp Req' Resp' Xs Ys} (hG : G.IsPlain)
    (T T' : X → Option Y) : G.elimProg T = G.elimProg T' := by
  funext c r
  simp only [AssignRelay.elimProg, hG T T']

/-- **The program with its side reads answered classically makes at most `qG` oracle reads.** -/
theorem elim_reads_le (T : X → Option Y) (c : ℕ) (r : Req) (h : X → Y)
    (m : Req' → Option Resp') :
    (((G.elimProg T c r).trace (combineAns h m)).filter Sum.isLeft).length ≤ G.qG := by
  rw [elimProg, trace_elimSide, length_filter_isLeft_filterMap_dropSide]
  exact G.reads_le T c r h m

/-- **The program with its side reads answered classically makes one main request.** -/
theorem elim_asks_eq_one (T : X → Option Y) (c : ℕ) (r : Req) (h : X → Y)
    (m : Req' → Option Resp') :
    (((G.elimProg T c r).trace (combineAns h m)).filterMap Sum.getRight?).length = 1 := by
  rw [elimProg, trace_elimSide, filterMap_getRight_filterMap_dropSide]
  exact G.asks_eq_one T c r h m

/-- **A relay without side reads** runs its program. -/
@[simp] theorem elimProg_ofProg
    (prog : (X → Option Y) → ℕ → Req → OracleProg (X ⊕ Req') (Y ⊕ Option Resp') (Reply X Y Resp))
    (qG : ℕ) (idle : Req') (hr ha) :
    (ofProg prog qG idle hr ha).elimProg = prog := by
  funext T c r
  exact elimSide_plainOf _ _

end AssignRelay

end GordieHowe.Quantum
