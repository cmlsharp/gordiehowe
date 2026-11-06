-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.ProofSystem.GKR.FieldCodes
public import GordieHoweNative.Data
public import GordieHoweNative.ProofSystem.GKR.Rel

@[expose] public section

/-!
# The relational check of a GKR circuit's emission

The compiled circuit's DAG `D` (`GordieHowe.GKR.Certificate.Dag`) is the emitter's output. The
emitter's certificate maps tree nodes, coordinate by coordinate, to *wires* `c0 + c1 · n` over DAG
nodes `n` (`Wire`). For each mapped point (a *cut*) the checker compares the wire with the tree
node's one-level expression over its children's wires (`TE`). It never replays the emitter: the
order of the calls, the call style, constant folding and common subexpressions do not enter the
check.

**Polynomials** are sorted lists of monomials `κc c · v a · v b` (`a ≤ b`; `a = 0` reads the input
`0`, the constant one), coefficients as codes (`GKR.Fold.CodeArith`), no zero coefficient. Every
node is read as its *peeled atom* (`peel`: a node with the one term `k · 1 · z` is `κ k · z`,
repeated). The tree side (`TE.poly`) reads each wire `c0 + c1 · n` as `c0 + c1 · [peel n]` and each
product of wires or constants over peeled atoms.

**The lazy difference check** (`diffLoop`). For a cut, `P = c0 + c1 · [peel W.n]` and `Q` the
tree side's polynomial. While `P − Q` has a linear atom, its largest one is unfolded on each side
that carries it (an atom with equal coefficients on both sides cancels): the node is replaced by its
terms, `k · a · b` becoming `k · [peel a] · [peel b]` (`unfold`). An input atom refuses. With no
linear atom left, the rest of the two sides must agree. Every unfold reads nodes below the unfolded
one, so `W.n + 1` unfolds suffice when the tree's atoms are below `W.n`; out of fuel the check
refuses. The check accepts exactly what full expansion accepts, and costs the atoms the two sides
disagree on, not the cone. Each side keeps its linear atoms in a Patricia trie by node id, most
significant bit first (`KTrie`), so finding and removing the largest atom and adding an unfolded
node's atoms cost the branching on one path, not the number of atoms; every trie is evaluated at
every step (`KTrie.seq`), so the kernel nests no chain of pending updates.

**The checks.** A cut (`cutOk`), an assertion (`zeroOk`: the asserted DAG node `Z` has the
assertion term `0 · 1 · U` and the expression is a multiple of `U` or a cut at `U`; `Z = 0` marks an
assertion the compiler folded away, whose expression the difference check finds zero), and the
relational check (`relOk`): every cut, every assertion, and every asserted node among the DAG's.
Each check's verdict (`cutR`, `zeroR`) is `none` or the reason it refuses (`Reason`), which the
failure-reporting twins report.

**Soundness.** An unfold keeps the value (`unfold_sound`), so an accepted cut's wire has the
expression's value at the DAG's node values (`cutOk_sound`), and an accepted assertion's expression
vanishes wherever the DAG's assertions hold (`zeroOk_sound`, `relOk_sound`). Checks of separate parts
compose without a re-check (`relOk_sound_append`). Completeness is not proved; a mismatch is a
rejection, never a wrong fact.

**Fast arithmetic.** Codes below `p` of an arithmetic that is arithmetic modulo `p` there (its prime
subfield, `GKR.Fold.CodeArith.PrimeOn`) take `(a + b) % p` and `a * b % p` directly
(`GKR.Fold.CodeArith.withPrime`), which equals the arithmetic (`GKR.Fold.CodeArith.withPrime_eq`).
One rule for every field: the characteristic `p` for a prime field or an extension tower of
any depth over `ZMod p` (`GKR.Fold.ExtCode.overPrime_primeOn`, `GKR.Fold.ExtCode.primeOn`), `0` (no
fast path) for a binary field.

The definitions are in `GordieHoweNative/ProofSystem/GKR/Rel.lean`
(the compiled library `GordieHoweNative`); this module has their lemmas.
-/

namespace GordieHowe.GKR.Rel

open GordieHowe.GKR.Certificate GordieHowe.GKR.Fold

/-! ## The normal form of a DAG node -/

/-- **The DAG nodes of a tree expression's wires.** -/
def TE.wireNodes : TE → List ℕ
  | .wire _ _ n => [n]
  | .const _ => []
  | .add a b => TE.wireNodes a ++ TE.wireNodes b
  | .scale _ a => TE.wireNodes a
  | .mul a b => TE.wireNodes a ++ TE.wireNodes b

/-! ### Linear atoms by node -/

@[simp] theorem KTrie.seq_eq {α : Sort _} (t : KTrie) (k : KTrie → α) : KTrie.seq t k = k t := by
  cases t <;> rfl

section Dag

variable (w : ℕ) (D : Dag) (Kc : Consts) (ar : CodeArith)

/-- **A cut**: the wire `W` is the tree node's expression `e`. -/
def cutOk (W : Wire) (e : TE) : Bool := (cutR w D Kc ar W e).isNone

/-- **An assertion**: the non-input DAG node `Z` has the assertion term `0 · 1 · U`, and the
asserted tree expression `e` is a multiple `0 + c · U` of `U` or a cut at `U`; for `Z = 0` (the
compiler folded the assertion away), `e` is zero by the difference check (`D.size` unfolds). -/
def zeroOk (Z U : ℕ) (e : TE) : Bool := (zeroR w D Kc ar Z U e).isNone

/-- **The relational check**: every cut, every assertion, and every asserted node among the
DAG's. -/
def relOk (cuts : List (Wire × TE)) (zs : List (ℕ × ℕ × TE)) : Bool :=
  cuts.all (fun c => cutOk w D Kc ar c.1 c.2) &&
    zs.all (fun z => zeroOk w D Kc ar z.1 z.2.1 z.2.2) &&
      subsetSorted (assertedNodes zs) D.asserts

end Dag

/-! ## Soundness -/

section Soundness

variable {F : Type*} [CommRing F]

/-- **The value of a wire** at the decoding `κc` and the node values `v`. -/
def Wire.val (κc v : ℕ → F) (W : Wire) : F := κc W.c0 + κc W.c1 * v W.n

/-- The value of a monomial. -/
def Mono.val (κc v : ℕ → F) (m : Mono) : F := κc m.c * v m.a * v m.b

/-- The value of a polynomial. -/
def Poly.val (κc v : ℕ → F) (p : Poly) : F := (p.map (Mono.val κc v)).sum

/-- **The value of a tree expression** at the wires' values. -/
def TE.eval (κc v : ℕ → F) : TE → F
  | .wire c0 c1 n => κc c0 + κc c1 * v n
  | .const c => κc c
  | .add a b => a.eval κc v + b.eval κc v
  | .scale c a => κc c * a.eval κc v
  | .mul a b => a.eval κc v * b.eval κc v

variable {ar : CodeArith} {κc v : ℕ → F}

@[simp] theorem Poly.val_nil : Poly.val κc v [] = 0 := rfl

@[simp] theorem Poly.val_cons (m : Mono) (p : Poly) :
    Poly.val κc v (m :: p) = m.val κc v + Poly.val κc v p := by
  simp [Poly.val]

theorem Poly.val_append (p q : Poly) : Poly.val κc v (p ++ q) = p.val κc v + q.val κc v := by
  simp [Poly.val]

theorem Poly.val_push (hA : ar.Hom κc) (m : Mono) (p : Poly) :
    Poly.val κc v (Poly.push m p) = m.val κc v + p.val κc v := by
  unfold Poly.push
  cases h : Nat.beq m.c 0
  · simp
  · simp only [Nat.beq_eq] at h
    simp [Mono.val, h, hA.zero]

theorem mono2_val (x y c : ℕ) : (mono2 x y c).val κc v = κc c * v x * v y := by
  unfold mono2
  cases Nat.ble x y
  · simp only [Bool.cond_false, Mono.val]
    ring
  · rfl

theorem Poly.val_const (hA : ar.Hom κc) (hone : v 0 = 1) (c : ℕ) :
    (Poly.const c).val κc v = κc c := by
  simp [Poly.const, Poly.val_push hA, Mono.val, hone]

theorem Mono.same_eq {m n : Mono} (h : Mono.same m n = true) : m.a = n.a ∧ m.b = n.b := by
  simpa [Mono.same, Nat.beq_eq] using h

/-- **The merge is the sum** (any order). -/
theorem Poly.val_addBy (hA : ar.Hom κc) (lt : Mono → Mono → Bool) :
    ∀ (f : ℕ) (p q : Poly), (Poly.addBy ar lt f p q).val κc v = p.val κc v + q.val κc v
  | 0, p, q => by simp [Poly.addBy, Poly.val_append]
  | _ + 1, [], q => by simp [Poly.addBy]
  | _ + 1, m :: p, [] => by simp [Poly.addBy]
  | f + 1, m :: p, n :: q => by
    simp only [Poly.addBy]
    cases lt m n
    · cases lt n m
      · cases hs : Mono.same m n
        · simp only [Bool.cond_false, Poly.val_cons, Poly.val_addBy hA lt f p q]
          ring
        · obtain ⟨ha, hb⟩ := Mono.same_eq hs
          simp only [Bool.cond_false, Bool.cond_true, Poly.val_push hA, Poly.val_addBy hA lt f p q,
            Poly.val_cons, Mono.val, hA.add, ha, hb]
          ring
      · simp only [Bool.cond_false, Bool.cond_true, Poly.val_cons,
          Poly.val_addBy hA lt f (m :: p) q]
        ring
    · simp only [Bool.cond_true, Poly.val_cons, Poly.val_addBy hA lt f p (n :: q)]
      ring

theorem Poly.val_add2By (hA : ar.Hom κc) (lt : Mono → Mono → Bool) (p q : Poly) :
    (Poly.add2By ar lt p q).val κc v = p.val κc v + q.val κc v := Poly.val_addBy hA lt _ p q

theorem Poly.val_add2 (hA : ar.Hom κc) (p q : Poly) :
    (Poly.add2 ar p q).val κc v = p.val κc v + q.val κc v := Poly.val_add2By hA _ p q

/-- **Scaling is multiplication.** -/
theorem Poly.val_scale (hA : ar.Hom κc) (c : ℕ) :
    ∀ p : Poly, (Poly.scale ar c p).val κc v = κc c * p.val κc v
  | [] => by simp [Poly.scale]
  | m :: p => by
    have ih := Poly.val_scale hA c p
    simp only [Poly.scale, List.foldr_cons] at ih ⊢
    rw [Poly.val_push hA, ih]
    simp [Mono.val, cmul_hom hA]
    ring

theorem Poly.val_pairsBy (hA : ar.Hom κc) (lt : Mono → Mono → Bool) :
    ∀ ps : List Poly,
      ((Poly.pairsBy ar lt ps).map (Poly.val κc v)).sum = (ps.map (Poly.val κc v)).sum
  | p :: q :: r => by
    simp [Poly.pairsBy, Poly.val_add2By hA, Poly.val_pairsBy hA lt r, add_assoc]
  | [] => rfl
  | [_] => rfl

theorem Poly.val_flatten : ∀ ps : List Poly,
    Poly.val κc v ps.flatten = (ps.map (Poly.val κc v)).sum
  | [] => rfl
  | p :: ps => by
    rw [List.flatten_cons, Poly.val_append, Poly.val_flatten ps, List.map_cons, List.sum_cons]

theorem Poly.val_sumAllBy (hA : ar.Hom κc) (lt : Mono → Mono → Bool) :
    ∀ (f : ℕ) (ps : List Poly),
      (Poly.sumAllBy ar lt f ps).val κc v = (ps.map (Poly.val κc v)).sum
  | _, [] => by simp [Poly.sumAllBy]
  | _, [p] => by simp [Poly.sumAllBy]
  | 0, _ :: _ :: _ => by simp only [Poly.sumAllBy]; exact Poly.val_flatten _
  | f + 1, p :: q :: r => by
    simp only [Poly.sumAllBy]
    rw [Poly.val_sumAllBy hA lt f, Poly.val_pairsBy hA]

/-- **The sum in any order is the sum.** -/
theorem Poly.val_sumBy (hA : ar.Hom κc) (lt : Mono → Mono → Bool) (ps : List Poly) :
    (Poly.sumBy ar lt ps).val κc v = (ps.map (Poly.val κc v)).sum := Poly.val_sumAllBy hA lt _ ps

/-- **The normalized sum is the sum.** -/
theorem Poly.val_sum (hA : ar.Hom κc) (ps : List Poly) :
    (Poly.sum ar ps).val κc v = (ps.map (Poly.val κc v)).sum := Poly.val_sumBy hA _ ps

theorem Poly.lin_mem {p : Poly} (h : p.lin = true) {m : Mono} (hm : m ∈ p) : m.a = 0 := by
  have := List.all_eq_true.1 h m hm
  simpa [Nat.beq_eq] using this

theorem sum_map_eq_mul {α : Type*} (l : List α) (f g : α → F) (k : F)
    (h : ∀ a ∈ l, f a = g a * k) : (l.map f).sum = (l.map g).sum * k := by
  rw [List.map_congr_left h]
  induction l with
  | nil => simp
  | cons a l ih => simp [ih fun b hb => h b (List.mem_cons_of_mem _ hb), add_mul]

theorem Poly.val_def (p : Poly) : p.val κc v = (p.map (Mono.val κc v)).sum := rfl

/-- **The product of two linear polynomials.** -/
theorem Poly.val_mulLin (hA : ar.Hom κc) (hone : v 0 = 1) {p q : Poly} (hp : p.lin = true)
    (hq : q.lin = true) : (Poly.mulLin ar p q).val κc v = p.val κc v * q.val κc v := by
  unfold Poly.mulLin
  rw [Poly.val_sum hA, List.map_map, Poly.val_def p]
  apply sum_map_eq_mul
  intro m hm
  simp only [Function.comp]
  rw [Poly.val_sum hA, List.map_map, Poly.val_def q, mul_comm]
  apply sum_map_eq_mul
  intro n hn
  simp only [Function.comp]
  rw [Poly.val_push hA, Poly.val_nil, add_zero, mono2_val]
  simp only [Mono.val, cmul_hom hA, Poly.lin_mem hp hm, Poly.lin_mem hq hn, hone]
  ring

/-- The value of an optional atom. -/
def atomVal (κc v : ℕ → F) : Option (ℕ × ℕ × Poly) → F
  | none => 0
  | some (c, x, _) => κc c * v x

/-- An optional atom's invariant: its normal form is its node's. -/
def AtomOk (κc v : ℕ → F) : Option (ℕ × ℕ × Poly) → Prop
  | none => True
  | some (_, x, fx) => fx.val κc v = v x

/-- The value of an operand. -/
def Opnd.val (κc v : ℕ → F) (o : Opnd) : F := o.p.val κc v + atomVal κc v o.a

theorem mulp_row (hA : ar.Hom κc) (hone : v 0 = 1) {p : Poly} (hp : p.lin = true) (c x : ℕ)
    {fx : Poly} (hfx : fx.val κc v = v x) :
    (Poly.sum ar (p.map fun m =>
      cond (Nat.beq m.b 0) (Poly.scale ar (cmul ar m.c c) fx)
        (Poly.push (mono2 m.b x (cmul ar m.c c)) []))).val κc v = p.val κc v * (κc c * v x) := by
  rw [Poly.val_sum hA, List.map_map, Poly.val_def p]
  apply sum_map_eq_mul
  intro m hm
  simp only [Function.comp]
  cases h : Nat.beq m.b 0
  · simp only [Bool.cond_false]
    rw [Poly.val_push hA, Poly.val_nil, add_zero, mono2_val]
    simp only [Mono.val, cmul_hom hA, Poly.lin_mem hp hm, hone]
    ring
  · simp only [Nat.beq_eq] at h
    simp only [Bool.cond_true, Poly.val_scale hA, cmul_hom hA, Mono.val, Poly.lin_mem hp hm, h,
      hone, hfx]
    ring

theorem rowA_val (hA : ar.Hom κc) (hone : v 0 = 1) {p : Poly} (hp : p.lin = true) :
    ∀ {o : Option (ℕ × ℕ × Poly)}, AtomOk κc v o →
      (rowA ar p o).val κc v = p.val κc v * atomVal κc v o
  | none, _ => by simp [rowA, atomVal]
  | some (c, x, fx), h => mulp_row hA hone hp c x h

theorem monoA_val (hA : ar.Hom κc) :
    ∀ o o' : Option (ℕ × ℕ × Poly),
      (monoA ar o o').val κc v = atomVal κc v o * atomVal κc v o'
  | some (c, x, _), some (d, y, _) => by
    simp [monoA, Poly.val_push hA, mono2_val, atomVal, cmul_hom hA]
    ring
  | none, _ => by simp [monoA, atomVal]
  | some _, none => by simp [monoA, atomVal]

/-- **The product of two operands is their product.** -/
theorem mulp_sound (hA : ar.Hom κc) (hone : v 0 = 1) {x y : Opnd} {p : Poly}
    (hx : AtomOk κc v x.a) (hy : AtomOk κc v y.a) (h : mulp ar x y = some p) :
    p.val κc v = x.val κc v * y.val κc v := by
  unfold mulp at h
  cases hl : (x.p.lin && y.p.lin)
  · rw [hl] at h
    exact absurd h (by simp)
  · rw [hl, Bool.cond_true, Option.some.injEq] at h
    subst h
    simp only [Bool.and_eq_true] at hl
    rw [Poly.val_sum hA]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero,
      Poly.val_mulLin hA hone hl.1 hl.2, rowA_val hA hone hl.1 hy, rowA_val hA hone hl.2 hx,
      monoA_val hA, Opnd.val]
    ring

/-- What a normal-form oracle guarantees: every result is the node's value. -/
def FlatOk (κc v : ℕ → F) (flatF : ℕ → Option Poly) : Prop :=
  ∀ n p, flatF n = some p → p.val κc v = v n

/-- **A wire's normal form is its value.** -/
theorem wirePoly_sound (hA : ar.Hom κc) (hone : v 0 = 1) {flatF : ℕ → Option Poly}
    (hF : FlatOk κc v flatF) {W : Wire} {p : Poly} (h : wirePoly ar flatF W = some p) :
    p.val κc v = W.val κc v := by
  unfold wirePoly at h
  cases h01 : (Nat.beq W.c0 0 && Nat.beq W.c1 1)
  · rw [h01, Bool.cond_false] at h
    cases hf : flatF W.n with
    | none => simp [hf] at h
    | some q =>
      simp only [hf, Option.some.injEq] at h
      subst h
      simp [Poly.val_add2 hA, Poly.val_const hA hone, Poly.val_scale hA, hF _ q hf, Wire.val]
  · rw [h01, Bool.cond_true] at h
    simp only [Bool.and_eq_true, Nat.beq_eq] at h01
    rw [hF _ p h, Wire.val, h01.1, h01.2, hA.zero, hA.one]
    ring

variable {w : ℕ} {D : Dag} {Kc : Consts} {xs : ℕ → F}

local notation "V" => D.val w (Kc.decode κc) xs

theorem val_of_not_input {n : ℕ} (h : Nat.blt n D.inputs = false) :
    V n = ((terms w (D.tree.get n)).map fun t =>
      if t.a < n ∧ t.b < n then Kc.decode κc t.k * V t.a * V t.b else 0).sum := by
  rw [Dag.val_eq, h, Bool.cond_false]

/-- **Peeling preserves the value.** -/
theorem peel_sound (hA : ar.Hom κc) (hone : V 0 = 1) :
    ∀ (f n : ℕ), match peel w D Kc ar f n with
      | none => V n = 0
      | some (c, x) => V n = κc c * V x
  | 0, n => by simp [peel, hA.one]
  | f + 1, n => by
    simp only [peel]
    cases hin : Nat.blt n D.inputs
    · simp only [Bool.cond_false]
      have hv := val_of_not_input (w := w) (κc := κc) (xs := xs) (Kc := Kc) hin
      generalize hT : terms w (D.tree.get n) = T at hv ⊢
      match T with
      | [] => simpa using hv
      | [t] =>
        simp only
        cases hc : (Nat.beq t.a 0 && Nat.blt t.b n)
        · simp [hA.one]
        · simp only [Bool.and_eq_true, Nat.beq_eq, Nat.blt_eq] at hc
          obtain ⟨ha, hb⟩ := hc
          have ih := peel_sound hA hone f t.b
          simp only [Bool.cond_true]
          have hn0 : 0 < n := by omega
          have hv' : V n = Kc.decode κc t.k * V t.b := by
            rw [hv]; simp [ha, hb, hn0, hone]
          revert ih
          cases peel w D Kc ar f t.b with
          | none => intro ih; simp [hv', ih]
          | some p =>
            intro ih
            simp only [Option.map_some]
            rw [hv', ih, cmul_hom hA, Consts.decode]
            ring
      | _ :: _ :: _ => simp [hA.one]
    · simp [hA.one]

theorem nodeOpnd_sound (hA : ar.Hom κc) (hone : V 0 = 1) {flatF : ℕ → Option Poly}
    (hF : FlatOk κc V flatF) {n : ℕ} {o : Opnd} (h : nodeOpnd w D Kc ar flatF n = some o) :
    AtomOk κc V o.a ∧ o.val κc V = V n := by
  have hp := peel_sound (xs := xs) hA hone (n + 1) n
  unfold nodeOpnd at h
  generalize peel w D Kc ar (n + 1) n = r at h hp
  cases r with
  | none =>
    simp only [Option.some.injEq] at h
    subst h
    exact ⟨trivial, by simp [Opnd.val, atomVal, hp]⟩
  | some cx =>
    obtain ⟨c, x⟩ := cx
    simp only at hp h
    cases hx : Nat.beq x 0
    · simp only [hx, Bool.cond_false] at h
      cases hf : flatF x with
      | none => simp [hf] at h
      | some fx =>
        simp only [hf, Option.some.injEq] at h
        subst h
        exact ⟨hF x fx hf, by simp [Opnd.val, atomVal, hp]⟩
    · rw [hx, Bool.cond_true, Option.some.injEq] at h
      simp only [Nat.beq_eq] at hx
      subst hx h
      exact ⟨trivial, by simp [Opnd.val, atomVal, Poly.val_const hA hone, hp, hone]⟩

theorem TE.opnd_sound (hA : ar.Hom κc) (hone : V 0 = 1) {flatF : ℕ → Option Poly}
    (hF : FlatOk κc V flatF) :
    ∀ {e : TE} {o : Opnd}, TE.opnd w D Kc ar flatF e = some o →
      AtomOk κc V o.a ∧ o.val κc V = e.eval κc V
  | .const c, o, h => by
    simp only [TE.opnd, Option.some.injEq] at h
    subst h
    exact ⟨trivial, by simp [Opnd.val, atomVal, TE.eval, Poly.val_const hA hone]⟩
  | .wire c0 c1 n, o, h => by
    simp only [TE.opnd] at h
    cases ho : nodeOpnd w D Kc ar flatF n with
    | none => simp [ho] at h
    | some o' =>
      simp only [ho, Option.map_some, Option.some.injEq] at h
      subst h
      obtain ⟨hok, hv⟩ := nodeOpnd_sound hA hone hF ho
      obtain ⟨p', a'⟩ := o'
      cases a' with
      | none =>
        simp only [Opnd.val, atomVal, add_zero] at hv
        refine ⟨trivial, ?_⟩
        simp [Opnd.val, atomVal, TE.eval, Poly.val_add2 hA, Poly.val_const hA hone,
          Poly.val_scale hA, hv]
      | some q =>
        obtain ⟨c, x, fx⟩ := q
        refine ⟨hok, ?_⟩
        simp only [Opnd.val, atomVal] at hv
        simp only [Opnd.val, atomVal, Option.map_some, TE.eval, Poly.val_add2 hA,
          Poly.val_const hA hone, Poly.val_scale hA, cmul_hom hA, ← hv]
        ring
  | .add _ _, o, h | .scale _ _, o, h | .mul _ _, o, h => by simp [TE.opnd] at h

/-- **A tree expression's normal form is its value.** -/
theorem TE.poly_sound (hA : ar.Hom κc) (hone : V 0 = 1) {flatF : ℕ → Option Poly}
    (hF : FlatOk κc V flatF) :
    ∀ {e : TE} {p : Poly}, TE.poly w D Kc ar flatF e = some p → p.val κc V = e.eval κc V
  | .wire c0 c1 n, p, h => by
    simp only [TE.poly] at h
    rw [wirePoly_sound hA hone hF h]
    rfl
  | .const c, p, h => by
    simp only [TE.poly, Option.some.injEq] at h
    subst h
    simp [Poly.val_const hA hone, TE.eval]
  | .add a b, p, h => by
    simp only [TE.poly] at h
    cases ha : TE.poly w D Kc ar flatF a with
    | none => simp [ha] at h
    | some pa =>
      cases hb : TE.poly w D Kc ar flatF b with
      | none => simp [ha, hb] at h
      | some pb =>
        simp only [ha, hb, Option.some.injEq] at h
        subst h
        rw [Poly.val_add2 hA, TE.poly_sound hA hone hF ha, TE.poly_sound hA hone hF hb]
        rfl
  | .scale c a, p, h => by
    simp only [TE.poly] at h
    cases ha : TE.poly w D Kc ar flatF a with
    | none => simp [ha] at h
    | some pa =>
      simp only [ha, Option.map_some, Option.some.injEq] at h
      subst h
      rw [Poly.val_scale hA, TE.poly_sound hA hone hF ha]
      rfl
  | .mul a b, p, h => by
    simp only [TE.poly] at h
    cases ha : TE.opnd w D Kc ar flatF a with
    | none => simp [ha] at h
    | some x =>
      cases hb : TE.opnd w D Kc ar flatF b with
      | none => simp [ha, hb] at h
      | some y =>
        simp only [ha, hb] at h
        obtain ⟨hxo, hxv⟩ := TE.opnd_sound hA hone hF ha
        obtain ⟨hyo, hyv⟩ := TE.opnd_sound hA hone hF hb
        rw [mulp_sound hA hone hxo hyo h, hxv, hyv]
        rfl

theorem Poly.beq_eq : ∀ {p q : Poly}, Poly.beq p q = true → p = q
  | [], [], _ => rfl
  | m :: p, n :: q, h => by
    simp only [Poly.beq, Mono.beq, Bool.and_eq_true, Nat.beq_eq] at h
    obtain ⟨⟨⟨ha, hb⟩, hc⟩, h⟩ := h
    rw [Poly.beq_eq h]
    cases m; cases n
    simp_all
  | [], _ :: _, h => by simp [Poly.beq] at h
  | _ :: _, [], h => by simp [Poly.beq] at h

theorem TE.isWire_eval {W : Wire} : ∀ {e : TE}, e.isWire W = true → e.eval κc v = W.val κc v
  | .wire c0 c1 n, h => by
    simp only [TE.isWire, Bool.and_eq_true, Nat.beq_eq] at h
    obtain ⟨⟨rfl, rfl⟩, rfl⟩ := h
    rfl
  | .const _, h | .add _ _, h | .scale _ _, h | .mul _ _, h => by simp [TE.isWire] at h

theorem Poly.val_filter_add (q : Mono → Bool) (p : Poly) :
    Poly.val κc v (p.filter q) + Poly.val κc v (p.filter fun m => !q m) = Poly.val κc v p := by
  induction p with
  | nil => simp
  | cons m p ih =>
    cases hq : q m <;> simp [List.filter_cons, hq, ← ih] <;> ring

/-! ### The trie of linear atoms -/

theorem le_of_blt_false {a b : ℕ} (h : Nat.blt a b = false) : b ≤ a := by
  by_contra hc
  have : Nat.blt a b = true := by rw [Nat.blt_eq]; omega
  rw [this] at h
  exact absurd h (by decide)

/-- **The value of a trie**, its nodes read by `x`: every leaf's code times its node's value. -/
def KTrie.val (κc x : ℕ → F) : KTrie → F
  | .nil => 0
  | .leaf k c => κc c * x k
  | .node _ _ l r => KTrie.val κc x l + KTrie.val κc x r

theorem KTrie.val_node' (x : ℕ → F) (p b : ℕ) (l r : KTrie) :
    KTrie.val κc x (KTrie.node' p b l r) = KTrie.val κc x l + KTrie.val κc x r := by
  unfold KTrie.node'
  split <;> simp [KTrie.val]

theorem KTrie.val_join (x : ℕ → F) (k₁ : ℕ) (t₁ : KTrie) (k₂ : ℕ) (t₂ : KTrie) :
    KTrie.val κc x (KTrie.join k₁ t₁ k₂ t₂) = KTrie.val κc x t₁ + KTrie.val κc x t₂ := by
  unfold KTrie.join
  simp only
  cases KTrie.bit k₂ (bitLen 64 (k₁ ^^^ k₂) - 1)
  · simp only [Bool.cond_false, KTrie.val]
    ring
  · simp only [Bool.cond_true, KTrie.val]

theorem KTrie.val_combine (hA : ar.Hom κc) (x : ℕ → F) (k c' c : ℕ) :
    KTrie.val κc x (cond (Nat.beq (ar.add c' c) 0) .nil (.leaf k (ar.add c' c))) =
      κc c' * x k + κc c * x k := by
  cases h : Nat.beq (ar.add c' c) 0
  · simp [KTrie.val, hA.add, add_mul]
  · simp only [Nat.beq_eq] at h
    have := hA.add c' c
    rw [h, hA.zero] at this
    simp only [Bool.cond_true, KTrie.val]
    linear_combination (x k) * this

/-- **An insert adds its atom.** -/
theorem KTrie.val_insert (hA : ar.Hom κc) (x : ℕ → F) :
    ∀ (t : KTrie) (k c : ℕ),
      KTrie.val κc x (KTrie.insert ar t k c) = KTrie.val κc x t + κc c * x k
  | .nil, k, c => by
    simp only [KTrie.insert]
    cases h : Nat.beq c 0
    · simp [KTrie.val]
    · simp only [Nat.beq_eq] at h
      simp [KTrie.val, h, hA.zero]
  | .leaf k' c', k, c => by
    simp only [KTrie.insert]
    cases h : Nat.beq k' k
    · simp only [Bool.cond_false]
      cases h0 : Nat.beq c 0
      · simp [KTrie.val_join, KTrie.val]
      · simp only [Nat.beq_eq] at h0
        simp [KTrie.val, h0, hA.zero]
    · simp only [Nat.beq_eq] at h
      subst h
      simp only [Bool.cond_true, KTrie.val_combine hA, KTrie.val]
  | .node p b l r, k, c => by
    simp only [KTrie.insert]
    cases Nat.beq (k >>> (b + 1)) p
    · simp only [Bool.cond_false]
      cases h0 : Nat.beq c 0
      · simp [KTrie.val_join, KTrie.val]
      · simp only [Nat.beq_eq] at h0
        simp [KTrie.val, h0, hA.zero]
    · simp only [Bool.cond_true]
      cases KTrie.bit k b
      · simp only [Bool.cond_false, KTrie.seq_eq, KTrie.val_node', KTrie.val_insert hA x l,
          KTrie.val]
        ring
      · simp only [Bool.cond_true, KTrie.seq_eq, KTrie.val_node', KTrie.val_insert hA x r,
          KTrie.val]
        ring

/-- **The largest node, removed**: its atom plus the rest. -/
theorem KTrie.val_popMax (x : ℕ → F) :
    ∀ (t : KTrie) {k c : ℕ} {t' : KTrie},
      KTrie.popMax t = some (k, c, t') → KTrie.val κc x t = κc c * x k + KTrie.val κc x t'
  | .nil, _, _, _, h => by simp [KTrie.popMax] at h
  | .leaf k₀ c₀, k, c, t', h => by
    simp only [KTrie.popMax, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    simp [KTrie.val]
  | .node p b l r, k, c, t', h => by
    simp only [KTrie.popMax] at h
    cases hr : KTrie.popMax r with
    | some v =>
      obtain ⟨kr, cr, r'⟩ := v
      simp only [hr, KTrie.seq_eq, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      rw [KTrie.val, KTrie.val_node', KTrie.val_popMax x r hr]
      ring
    | none =>
      cases hl : KTrie.popMax l with
      | some v =>
        obtain ⟨kl, cl, l'⟩ := v
        simp only [hr, hl, KTrie.seq_eq, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl, rfl⟩ := h
        rw [KTrie.val, KTrie.val_node', KTrie.val_popMax x l hl]
        ring
      | none => simp [hr, hl] at h

/-- **A trie with no largest node is zero.** -/
theorem KTrie.val_popMax_none (x : ℕ → F) :
    ∀ (t : KTrie), KTrie.popMax t = none → KTrie.val κc x t = 0
  | .nil, _ => rfl
  | .leaf _ _, h => by simp [KTrie.popMax] at h
  | .node p b l r, h => by
    simp only [KTrie.popMax] at h
    cases hr : KTrie.popMax r with
    | some v => obtain ⟨_, _, _⟩ := v; simp [hr] at h
    | none =>
      cases hl : KTrie.popMax l with
      | some v => obtain ⟨_, _, _⟩ := v; simp [hr, hl] at h
      | none => rw [KTrie.val, KTrie.val_popMax_none x l hl, KTrie.val_popMax_none x r hr,
          add_zero]

/-- **Adding linear atoms adds their values.** -/
theorem KTrie.val_insertAll (hA : ar.Hom κc) (hone : v 0 = 1) :
    ∀ (t : KTrie) (ms : Poly) {t' : KTrie}, KTrie.insertAll ar t ms = some t' →
      KTrie.val κc v t' = KTrie.val κc v t + ms.val κc v
  | t, [], t', h => by
    simp only [KTrie.insertAll, Option.some.injEq] at h
    subst h
    simp
  | t, m :: ms, t', h => by
    simp only [KTrie.insertAll] at h
    cases hm : Nat.beq m.a 0
    · simp [hm] at h
    · simp only [hm, Bool.cond_true, KTrie.seq_eq] at h
      simp only [Nat.beq_eq] at hm
      rw [KTrie.val_insertAll hA hone _ ms h, KTrie.val_insert hA v t m.b m.c,
        Poly.val_cons, Mono.val, hm, hone]
      ring

/-- **The peeled atom is the node's value.** -/
theorem peelPoly_val (hA : ar.Hom κc) (hone : V 0 = 1) (n : ℕ) :
    (peelPoly w D Kc ar n).val κc V = V n := by
  have hp := peel_sound (xs := xs) hA hone (n + 1) n
  unfold peelPoly
  revert hp
  cases peel w D Kc ar (n + 1) n with
  | none => intro hp; simp [hp]
  | some cx =>
    obtain ⟨c, x⟩ := cx
    intro hp
    simp only at hp ⊢
    rw [Poly.val_push hA]
    simp [Mono.val, hone, hp]

theorem peelF_ok (hA : ar.Hom κc) (hone : V 0 = 1) : FlatOk κc V (peelF w D Kc ar) := by
  intro n p h
  simp only [peelF, Option.some.injEq] at h
  subst h
  exact peelPoly_val hA hone n

/-- **A term over peeled atoms is the term.** -/
theorem termMono_val (hA : ar.Hom κc) (hone : V 0 = 1) (c : ℕ) (t : Term) :
    (termMono w D Kc ar c t).val κc V = κc c * (Kc.decode κc t.k * V t.a * V t.b) := by
  have ha := peel_sound (xs := xs) hA hone (t.a + 1) t.a
  have hb := peel_sound (xs := xs) hA hone (t.b + 1) t.b
  unfold termMono
  revert ha hb
  cases peel w D Kc ar (t.a + 1) t.a with
  | none => intro ha _; simp [ha]
  | some p =>
    obtain ⟨ca, xa⟩ := p
    cases peel w D Kc ar (t.b + 1) t.b with
    | none => intro _ hb; simp [hb]
    | some q =>
      obtain ⟨cb, xb⟩ := q
      intro ha hb
      simp only at ha hb ⊢
      rw [Poly.val_push hA, Poly.val_nil, add_zero, mono2_val, ha, hb]
      simp only [cmul_hom hA, Consts.decode]
      ring

/-- **An unfold keeps the value**: node `b`'s terms times `c` are `c · V b`. -/
theorem unfold_sound (hA : ar.Hom κc) (hone : V 0 = 1) {b c : ℕ} {ul ur : Poly}
    (hin : Nat.blt b D.inputs = false) (h : unfold w D Kc ar b c = some (ul, ur)) :
    ul.val κc V + ur.val κc V = κc c * V b := by
  unfold unfold at h
  generalize hts : terms w (D.tree.get b) = ts at h
  cases hall : ts.all fun t => Nat.blt t.a b && Nat.blt t.b b
  · simp [hall] at h
  · simp only [hall, Bool.cond_true, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    rw [Poly.val_flatten, Poly.val_sum hA, val_of_not_input hin, hts]
    simp only [List.map_map]
    rw [← List.sum_map_add, ← List.sum_map_mul_left]
    refine congrArg List.sum (List.map_congr_left fun t ht => ?_)
    have hbt := List.all_eq_true.1 hall t ht
    simp only [Bool.and_eq_true, Nat.blt_eq] at hbt
    simp only [Function.comp, Poly.val_filter_add, termMono_val hA hone, hbt, and_self, if_true]

/-- The value of a side: its linear atoms (a trie) and its rest. -/
def sideVal (κc v : ℕ → F) (t : KTrie) (r : List Poly) : F :=
  KTrie.val κc v t + (r.map (Poly.val κc v)).sum

/-- **A side's unfold keeps its value**: what the continuation receives has `c · [b]` added. -/
theorem side_sound (hA : ar.Hom κc) (hone : V 0 = 1) {b c : ℕ} {t : KTrie} {r : List Poly}
    {k : KTrie → List Poly → Option Reason} (h : side w D Kc ar b c t r k = none) :
    ∃ t' r', k t' r' = none ∧
      sideVal κc V t' r' = κc c * V b + sideVal κc V t r := by
  unfold side at h
  cases hin : Nat.blt b D.inputs
  · rw [hin, Bool.cond_false] at h
    cases hu : unfold w D Kc ar b c with
    | none => simp [hu] at h
    | some u =>
      obtain ⟨ul, ur⟩ := u
      rw [hu] at h
      simp only at h
      cases hi : KTrie.insertAll ar t ul with
      | none => simp [hi] at h
      | some t' =>
        rw [hi] at h
        refine ⟨_, _, h, ?_⟩
        have hu' := unfold_sound hA hone hin hu
        simp only [sideVal, KTrie.val_insertAll hA hone _ _ hi, List.map_cons, List.sum_cons]
        rw [← hu']
        ring
  · simp [hin] at h

theorem diffLoop_final {rp rq : List Poly} {tp tq : KTrie}
    (hp : KTrie.popMax tp = none) (hq : KTrie.popMax tq = none)
    (h : cond (Poly.beq (Poly.sum ar rp) (Poly.sum ar rq)) none (some Reason.differ) = none)
    (hA : ar.Hom κc) : sideVal κc V tp rp = sideVal κc V tq rq := by
  cases hb : Poly.beq (Poly.sum ar rp) (Poly.sum ar rq)
  · simp [hb] at h
  · have := congrArg (Poly.val κc V) (Poly.beq_eq hb)
    simp only [Poly.val_sum hA] at this
    simp [sideVal, KTrie.val_popMax_none _ _ hp, KTrie.val_popMax_none _ _ hq, this]

/-- **An accepted difference loop**: the two sides have equal values. -/
theorem diffLoop_sound (hA : ar.Hom κc) (hone : V 0 = 1) :
    ∀ (f : ℕ) (tp : KTrie) (rp : List Poly) (tq : KTrie) (rq : List Poly),
      diffLoop w D Kc ar f tp rp tq rq = none →
        sideVal κc V tp rp = sideVal κc V tq rq := by
  intro f
  induction f with
  | zero =>
    intro tp rp tq rq h
    unfold diffLoop at h
    cases hp : KTrie.popMax tp <;> cases hq : KTrie.popMax tq <;>
      simp only [hp, hq] at h
    · exact diffLoop_final hp hq h hA
    all_goals simp at h
  | succ f ih =>
    intro tp rp tq rq h
    unfold diffLoop at h
    cases hp : KTrie.popMax tp with
    | none =>
      cases hq : KTrie.popMax tq with
      | none =>
        simp only [hp, hq] at h
        exact diffLoop_final hp hq h hA
      | some vq =>
        obtain ⟨kq, cq, tq'⟩ := vq
        simp only [hp, hq] at h
        obtain ⟨a, b, hk, hv⟩ := side_sound hA hone h
        have := ih _ _ _ _ hk
        have hq' := KTrie.val_popMax V tq hq (κc := κc)
        simp only [sideVal] at hv this ⊢
        rw [hq']
        linear_combination this + hv
    | some vp =>
      obtain ⟨kp, cp, tp'⟩ := vp
      have hp' := KTrie.val_popMax V tp hp (κc := κc)
      cases hq : KTrie.popMax tq with
      | none =>
        simp only [hp, hq] at h
        obtain ⟨a, b, hk, hv⟩ := side_sound hA hone h
        have := ih _ _ _ _ hk
        simp only [sideVal] at hv this ⊢
        rw [hp']
        linear_combination this - hv
      | some vq =>
        obtain ⟨kq, cq, tq'⟩ := vq
        have hq' := KTrie.val_popMax V tq hq (κc := κc)
        simp only [hp, hq] at h
        cases h1 : Nat.blt kq kp
        · rw [h1, Bool.cond_false] at h
          cases h2 : Nat.blt kp kq
          · rw [h2, Bool.cond_false] at h
            have hk : kp = kq := by
              have := le_of_blt_false h1
              have := le_of_blt_false h2
              omega
            subst hk
            cases h3 : Nat.beq cp cq
            · rw [h3, Bool.cond_false] at h
              obtain ⟨a, b, hk, hv⟩ := side_sound hA hone h
              obtain ⟨a', b', hk', hv'⟩ := side_sound hA hone hk
              have := ih _ _ _ _ hk'
              simp only [sideVal] at hv hv' this ⊢
              rw [hp', hq']
              linear_combination this - hv + hv'
            · rw [h3, Bool.cond_true] at h
              simp only [Nat.beq_eq] at h3
              subst h3
              have := ih _ _ _ _ h
              simp only [sideVal] at this ⊢
              rw [hp', hq']
              linear_combination this
          · rw [h2, Bool.cond_true] at h
            obtain ⟨a, b, hk, hv⟩ := side_sound hA hone h
            have := ih _ _ _ _ hk
            simp only [sideVal] at hv this ⊢
            rw [hq']
            linear_combination this + hv
        · rw [h1, Bool.cond_true] at h
          obtain ⟨a, b, hk, hv⟩ := side_sound hA hone h
          have := ih _ _ _ _ hk
          simp only [sideVal] at hv this ⊢
          rw [hp']
          linear_combination this - hv

/-- **An accepted difference check**: the two polynomials have equal values. -/
theorem diffCheck_sound (hA : ar.Hom κc) (hone : V 0 = 1) {f : ℕ} {p q : Poly}
    (h : diffCheck w D Kc ar f p q = none) : p.val κc V = q.val κc V := by
  unfold diffCheck at h
  cases hp : KTrie.insertAll ar .nil (p.filter Mono.isLin) with
  | none => simp [hp] at h
  | some tp =>
    cases hq : KTrie.insertAll ar .nil (q.filter Mono.isLin) with
    | none => simp [hp, hq] at h
    | some tq =>
      simp only [hp, hq] at h
      have := diffLoop_sound hA hone f _ _ _ _ h
      simp only [sideVal, KTrie.val_insertAll hA hone _ _ hp, KTrie.val_insertAll hA hone _ _ hq,
        List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero] at this
      simpa [KTrie.val, Poly.val_filter_add] using this

theorem cutR_sound (hA : ar.Hom κc) (hone : V 0 = 1) {W : Wire} {e : TE}
    (h : cutR w D Kc ar W e = none) : W.val κc V = e.eval κc V := by
  unfold cutR at h
  cases hw : e.isWire W
  · rw [hw, Bool.cond_false] at h
    cases hq : TE.poly w D Kc ar (peelF w D Kc ar) e with
    | none => simp [hq] at h
    | some q =>
      rw [hq] at h
      have hd := diffCheck_sound hA hone h
      rw [← TE.poly_sound hA hone (peelF_ok hA hone) hq, ← hd, Poly.val_add2 hA,
        Poly.val_const hA hone, Poly.val_scale hA, peelPoly_val hA hone]
      rfl
  · exact (TE.isWire_eval hw).symm

/-- **`cutOk_sound`**: an accepted cut's wire has the tree expression's value at the DAG's node
values (the children's wires read at their DAG nodes). -/
theorem cutOk_sound (hA : ar.Hom κc) (hone : V 0 = 1) {W : Wire} {e : TE}
    (h : cutOk w D Kc ar W e = true) : W.val κc V = e.eval κc V :=
  cutR_sound hA hone (Option.isNone_iff_eq_none.1 h)

/-- **`zeroOk_sound`**: an accepted assertion's tree expression is zero, when the DAG's assertions
hold and its node `Z` (unless `0`) is asserted. -/
theorem zeroOk_sound (hA : ar.Hom κc) (hone : V 0 = 1) (hD : D.Holds w (Kc.decode κc) xs)
    {Z U : ℕ} {e : TE} (hZ : Z ≠ 0 → Z ∈ D.asserts)
    (h : zeroOk w D Kc ar Z U e = true) : e.eval κc V = 0 := by
  have h' := Option.isNone_iff_eq_none.1 h
  unfold zeroR at h'
  cases hz : Nat.beq Z 0
  · rw [hz, Bool.cond_false] at h'
    cases ht : assertTermB w D Z U
    · simp [ht] at h'
    · rw [ht, Bool.cond_true] at h'
      cases hle : Nat.ble D.inputs Z
      · simp [hle] at h'
      · rw [hle, Bool.cond_true] at h'
        simp only [assertTermB, List.any_eq_true, Bool.and_eq_true, Nat.beq_eq] at ht
        obtain ⟨t, htm, ⟨hk, ha⟩, hb⟩ := ht
        have hterms : nodeTerms w D Z = terms w (D.tree.get Z) :=
          nodeTerms_of_le (by simpa using hle)
        have hZ' : Z ∈ D.asserts := hZ fun h => absurd (h ▸ hz) (by decide)
        have h0 := hD.1 Z hZ' t (hterms ▸ htm) hk
        rw [ha, hb, hone, one_mul] at h0
        cases hs : e.scalesNode U
        · rw [hs, Bool.cond_false] at h'
          rw [← cutR_sound hA hone h']
          simp [Wire.val, Wire.node, hA.zero, hA.one, h0]
        · obtain ⟨c0, c1, m⟩ | _ | _ | _ | _ := e <;> simp only [TE.scalesNode,
            Bool.false_eq_true, Bool.and_eq_true, Nat.beq_eq] at hs
          obtain ⟨rfl, rfl⟩ := hs
          simp [TE.eval, hA.zero, h0]
  · rw [hz, Bool.cond_true] at h'
    cases hq : TE.poly w D Kc ar (peelF w D Kc ar) e with
    | none => simp [hq] at h'
    | some q =>
      rw [hq] at h'
      cases hd : diffCheck w D Kc ar D.size [] q with
      | some _ => simp [hd] at h'
      | none =>
        rw [← TE.poly_sound hA hone (peelF_ok hA hone) hq, ← diffCheck_sound hA hone hd]
        rfl

theorem mem_assertedNodes {zs : List (ℕ × ℕ × TE)} {z : ℕ × ℕ × TE} (hz : z ∈ zs) (h0 : z.1 ≠ 0) :
    z.1 ∈ assertedNodes zs := by
  refine List.mem_filterMap.2 ⟨z, hz, ?_⟩
  have : Nat.beq z.1 0 = false := Bool.eq_false_iff.mpr fun h => h0 (Nat.eq_of_beq_eq_true h)
  simp [this]

/-- **The relational check is sound**: every cut's wire has its tree expression's value, and every
assertion's tree expression is zero, when the DAG's assertions hold. -/
theorem relOk_sound (hA : ar.Hom κc) (hone : V 0 = 1) (hD : D.Holds w (Kc.decode κc) xs)
    {cuts : List (Wire × TE)} {zs : List (ℕ × ℕ × TE)}
    (h : relOk w D Kc ar cuts zs = true) :
    (∀ c ∈ cuts, c.1.val κc V = c.2.eval κc V) ∧ ∀ z ∈ zs, z.2.2.eval κc V = 0 := by
  unfold relOk at h
  simp only [Bool.and_eq_true, List.all_eq_true] at h
  obtain ⟨⟨hc, hz⟩, hs⟩ := h
  refine ⟨fun c hc' => cutOk_sound hA hone (hc c hc'), fun z hz' => ?_⟩
  exact zeroOk_sound hA hone hD
    (fun h0 => mem_of_subsetSorted hs z.1 (mem_assertedNodes hz' h0)) (hz z hz')

/-- **Checks compose**: two accepted relational checks (two entries, each its own declaration) give
the conclusion on the concatenated cuts and assertions, without a re-check. -/
theorem relOk_sound_append (hA : ar.Hom κc) (hone : V 0 = 1) (hD : D.Holds w (Kc.decode κc) xs)
    {cuts₁ cuts₂ : List (Wire × TE)} {zs₁ zs₂ : List (ℕ × ℕ × TE)}
    (h₁ : relOk w D Kc ar cuts₁ zs₁ = true) (h₂ : relOk w D Kc ar cuts₂ zs₂ = true) :
    (∀ c ∈ cuts₁ ++ cuts₂, c.1.val κc V = c.2.eval κc V) ∧
      ∀ z ∈ zs₁ ++ zs₂, z.2.2.eval κc V = 0 := by
  obtain ⟨a₁, b₁⟩ := relOk_sound hA hone hD h₁
  obtain ⟨a₂, b₂⟩ := relOk_sound hA hone hD h₂
  refine ⟨fun c hc => ?_, fun z hz => ?_⟩
  · rcases List.mem_append.1 hc with hc | hc
    exacts [a₁ c hc, a₂ c hc]
  · rcases List.mem_append.1 hz with hz | hz
    exacts [b₁ z hz, b₂ z hz]

end Soundness

end GordieHowe.GKR.Rel
