-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Model.Quantum.Pure.QueryAlg
public import GordieHowe.Model.Quantum.Pure.Game
public import GordieHowe.Model.QROM.QueryBits
public import Mathlib.Order.PiLex

@[expose] public section

/-!
# The compressed phase oracle and the simulated adversary of CMS19

Chiesa–Manohar–Spooner, "Succinct Arguments in the Quantum Random Oracle Model" (CMS19, ePrint
2019/834, version of January 14, 2020; printed pages). This file defines, in the pure-vector
model of `PQ/Quantum/` (`QState`, `QueryAlg`), the objects of CMS19 sections 3.5, 3.6, 4.2 and
5.1 and Appendix A: the database register with `t` slots and its database states `|D_t⟩`, the
unitaries `Dec_x`, `Dec`, `O0` and the compressed phase oracle `O = Dec ∘ O0 ∘ Dec`, the final
state `|Sim*(A)⟩` of the simulated adversary, the measured database, and the projectors `P` and
`P_t`. Each paper sentence is quoted next to the Lean that transcribes it.

The oracle has domain `{0,1}^m` (`Bits m`) and range `{0,1}^n` written as `BitStr I J =
I → J → ZMod 2` (`n = |I| · |J|`; the soundness layer uses `I = Fin (k + e)` bytes of
`J = Fin 8` bits, the range `XOut k e` of the zero-knowledge layer), with XOR as addition. The
databases of the soundness layer hold answers in a type `B` (bytes, `Out k e`), read from
`{0,1}^n` through an equivalence `e : BitStr I J ≃ B`.

## Paper text and its transcription

Section 3.5, p. 16:

    For D : {0,1}^m ⇀ {0,1}^n and t ∈ N with |D| ≤ t ≤ 2^m, we define the pure quantum state
      |D_t⟩ := |x_1, y_1, …, x_|D|, y_|D|⟩ ⊗ |⊥, 0^n⟩^{⊗(|D|−t)}
    where x_1, …, x_|D| is the lexicographic ordering of supp(D) and y_i := D(x_i) for each
    i ∈ [|D|]. We will write |D⟩ for |D_t⟩ when the bound t is clear from context.

The database register has `t` slots, each an input in `{0,1}^m ∪ {⊥}` and an output in
`{0,1}^n` (`Slot`, `Slots`); `|D_t⟩` is the basis vector of the slot tuple `dbSlots e t D`. The
exponent `|D| − t` is read `t − |D|` (the number of empty slots). Lexicographic order: bit `0`
first, `false < true` (`lexKeys`, through Mathlib's `Lex` order on `Fin m → Bool`). The slot
tuples that are not of the form `|D_t⟩` are basis states of the register that no database
state uses; `slotsDB` reads a database off any slot tuple, and `slotsDB e (dbSlots e t D) = D`
for `|D| ≤ t`.

Section 3.6, pp. 16–17:

    Another method is to encode h in the phase of a quantum state, via the unitary matrix O'_h
    that acts as |x, u⟩ ↦ (−1)^{u·h(x)} |x, u⟩. These two encodings are equivalent under an
    efficient change of basis: O_h = (I^m ⊗ H^n) O'_h (I^m ⊗ H^n) where I^m is the identity on
    the first m qubits and H^n is the Hadamard transformation on the other n qubits. […] In this
    paper it is more convenient to always work with phase oracles. All quantum query algorithms
    will thus have an oracle phase register U instead of the oracle answer register Y.

The adversaries (`QueryAlg`) use the standard oracle `O_h = permOp (queryPerm h)`, as in the
zero-knowledge layer. Their phase-oracle form replaces every query `O_h` by
`(I ⊗ H^n) O'_h (I ⊗ H^n)`; `hadamard` is `I ⊗ H^n` on the answer register,
`H^n |y⟩ = (1/√2^n) ∑_u (−1)^{u·y} |u⟩`, and after it the answer register is the phase register
`U`. So a simulated query is `hadamard ∘ O ∘ hadamard` (`simQuery`).

    […] we follow Zhandry [Zha19] and extend the adversary's initial state with a random
    superposition of all functions h […]. In fact, instead of considering a superposition of
    functions h, we will consider a superposition of databases D, according to the compressed
    oracle formalism of [Zha19]. Specifically, throughout this paper we will only deal with the
    compressed phase oracle with m input bits and n output bits, which we denote by O. We fix
    the database query bound of the compressed oracle to be t in advance.

    Given a quantum algorithm A described by unitaries A_1, ..., A_t and initial state |φ_0⟩, we
    write |Sim*(A)⟩ to represent the final state of A before measurement when simulated using O
    as the oracle. Formally, |Sim*(A)⟩ = A_t O ··· A_1 O |φ_0, ∅⟩, where ∅ denotes that the D
    register holds the empty database with t slots, and we implicitly extend each A_i to act as
    the identity on D.

`simState A` for `A : QueryAlg (Bits m) (BitStr I J) t O`: the initial state `A.init ⊗ |∅_t⟩`
(`simInit`), then `A.step 0`, then for each of the `t` queries `simQuery` followed by the next
step, every step extended by the identity on the database register (`controlled`). With
`|φ_0⟩ = A.step 0 A.init` this is `A_t O ⋯ A_1 O |φ_0, ∅⟩` in phase form.

Appendix A, p. 47:

    Recall from [Zha19] that the compressed phase oracle O is defined as Dec ∘ O0 ∘ Dec where O0
    is the unitary that acts as |x, u, z, D⟩ ↦ (−1)^{u·D(x)} |x, u, z, D⟩ (where u·⊥ := 0), Dec
    is the unitary that acts as |x, u, z, D⟩ ↦ |x, u, z⟩ Dec_x |D⟩, and Dec_x is defined as
    follows:
      Dec_x |D⟩ := (1/√2^n) ∑_y |D + [x ↦ y]⟩   if D(x) = ⊥ and |D| < t
                   |D⟩                          if D(x) = ⊥ and |D| = t ,
                   |D⟩ + (1/√2^n) |D'⟩ − (1/√2^n) |φ_{0^n}⟩   if D(x) ≠ ⊥
    where D' := D − x, and |φ_w⟩ := (1/√2^n) ∑_y (−1)^{y·w} |D' + [x ↦ y]⟩, so that
    |D⟩ = (1/√2^n) ∑_w (−1)^{w·D(x)} |φ_w⟩.

`decX e t x D` is `Dec_x |D⟩`; `decOp` is `Dec`, `phaseOp` is `O0`, `compressedOracle` is
`O = Dec ∘ O0 ∘ Dec`. The register `z` is the work register `W` of the adversary, and `x`, `u` are
the query input and the answer register read as the phase register. Deviations: the paper defines
`Dec` and `O0` on the database states `|x, u, z, D_t⟩`; on the other basis states of the `t`-slot
register `Dec` is the identity and `O0` applies the phase of the database `slotsDB` reads off the
slots. The adversary's state never has weight there (`supported_simState`: database states are
mapped to combinations of database states), and `P_t` below projects them away. Lemma 3.2 (p. 17)
and the sentence "If |D| = t, then Dec_x does nothing" are wrong when `D(x) ≠ ⊥` (App. A, p. 47,
defines `Dec_x` to act whenever `D(x) ≠ ⊥`); the definition here is App. A's `Dec_x`, not Lemma 3.2.

Text before Definition 4.7, p. 20:

    We denote by Sim*(A) the probabilistic process that executes A while answering its queries
    with O, and then outputs ((a, b, c), D) where (a, b, c) is the output of A (obtained by
    measuring its output register in the computational basis) and D is the result of measuring
    the database registers in the computational basis after A has halted.

`simLaw e A`: the Born weights of `simState A` (`bornWeight`), pushed forward along
`(r, s) ↦ (A.out r.1, slotsDB e s)`. It is an outer measure; its total weight is `1`
(`simLaw_univ`), since the Hadamard transform, `Dec` and `O0` are unitary (`norm_hadamard`,
`norm_decOp`, `norm_phaseOp`).

Proposition 5.8 and the text after it, p. 22:

    where P := I ⊗ ∑_{D ∈ P} |D⟩⟨D| is the projector that maps all basis states of the form
    |x, u, z⟩ ⊗ |D⟩ to 0 if D ∉ P, and is otherwise the identity.
    […] define P_t := I ⊗ ∑_{D : |D| ≤ t} |D⟩⟨D| to be the projector that maps all basis states
    of the form |x, u, z⟩ ⊗ |D⟩ to 0 if |D| > t, and is otherwise the identity.

`dbProj e t P` is `I ⊗ ∑_{D ∈ P, |D| ≤ t} |D_t⟩⟨D_t|` (the states `|D_t⟩` exist for `|D| ≤ t`);
`sizeProj e t` is `P_t`, the projector onto the database states of the `t`-slot register. The
paper writes `P̄` for the projector of the negated property; it is `dbProj e t Pᶜ`.
-/

open Finset GordieHowe.Quantum
open scoped BigOperators ENNReal

namespace GordieHowe.QROM

/-! ### Bit strings -/

/-- `{0,1}^n` as `|I|` words of `|J|` bits, added bitwise (XOR). -/
abbrev BitStr (I J : Type) := I → J → ZMod 2

variable {I J : Type} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]

/-- The dot product `u · y = ∑ u_ij y_ij (mod 2)` of two bit strings (CMS19 section 3.6). -/
def BitStr.dot (u y : BitStr I J) : ZMod 2 := ∑ i, ∑ j, u i j * y i j

instance BitStr.instDecidableEq : DecidableEq (BitStr I J) :=
  inferInstanceAs (DecidableEq (I → J → ZMod 2))

/-- `(−1)^z` for a bit `z`. -/
def signOf (z : ZMod 2) : ℂ := (-1) ^ z.val

@[simp] theorem signOf_zero : signOf 0 = 1 := by simp [signOf]

@[simp] theorem signOf_one : signOf 1 = -1 := by
  rw [signOf, show (1 : ZMod 2).val = 1 from rfl, pow_one]

theorem signOf_add (a b : ZMod 2) : signOf (a + b) = signOf a * signOf b := by
  rw [signOf, ZMod.val_add, ← neg_one_pow_eq_pow_mod_two, pow_add, signOf, signOf]

theorem star_signOf (z : ZMod 2) : star (signOf z) = signOf z := by
  simp [signOf]

theorem signOf_mul_self (z : ZMod 2) : signOf z * signOf z = 1 := by
  rw [← signOf_add, CharTwo.add_self_eq_zero, signOf_zero]

omit [DecidableEq I] [DecidableEq J] in
theorem BitStr.dot_comm (u y : BitStr I J) : u.dot y = y.dot u := by
  simp only [BitStr.dot, mul_comm]

omit [DecidableEq I] [DecidableEq J] in
theorem BitStr.dot_add_left (u v y : BitStr I J) : (u + v).dot y = u.dot y + v.dot y := by
  simp only [BitStr.dot, Pi.add_apply, add_mul, Finset.sum_add_distrib]

omit [DecidableEq I] [DecidableEq J] in
@[simp] theorem BitStr.dot_zero (u : BitStr I J) : u.dot 0 = 0 := by
  simp [BitStr.dot]

/-- **Character orthogonality on `{0,1}^n`**: `∑_u (−1)^{u·w} = 2^n` if `w = 0`, else `0`. -/
theorem sum_signOf_dot (w : BitStr I J) :
    ∑ u : BitStr I J, signOf (u.dot w) = if w = 0 then (Fintype.card (BitStr I J) : ℂ) else 0 := by
  split_ifs with hw
  · simp [hw]
  · obtain ⟨i₀, j₀, h⟩ : ∃ i j, w i j ≠ 0 := by
      by_contra hc
      push_neg at hc
      exact hw (funext fun i => funext fun j => hc i j)
    have h1 : w i₀ j₀ = 1 := by
      revert h
      generalize w i₀ j₀ = z
      intro h
      fin_cases z
      · exact absurd rfl h
      · rfl
    set d : BitStr I J := Pi.single i₀ (Pi.single j₀ 1)
    have hd : d.dot w = 1 := by
      simp only [BitStr.dot, d]
      rw [Finset.sum_eq_single i₀ (fun i _ hi => by simp [hi]) (by simp)]
      rw [Finset.sum_eq_single j₀ (fun j _ hj => by simp [hj]) (by simp)]
      simp [h1]
    have hre : ∑ u : BitStr I J, signOf ((u + d).dot w) = ∑ u : BitStr I J, signOf (u.dot w) :=
      Fintype.sum_equiv (Equiv.addRight d) _ _ fun _ => rfl
    have hshift : ∑ u : BitStr I J, signOf (u.dot w) = -∑ u : BitStr I J, signOf (u.dot w) := by
      conv_lhs => rw [← hre]
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun u _ => ?_
      rw [BitStr.dot_add_left, hd, signOf_add, signOf_one, mul_neg_one]
    have := congrArg (· + ∑ u : BitStr I J, signOf (u.dot w)) hshift
    simp only [neg_add_cancel] at this
    have h2 : (2 : ℂ) * ∑ u : BitStr I J, signOf (u.dot w) = 0 := by rw [two_mul]; exact this
    simpa using h2

/-! ### The database register -/

variable {m : ℕ}

/-- The support of a database in lexicographic order (CMS19 section 3.5): bit `0` first, `false`
before `true`. -/
noncomputable def lexKeys {B : Type} (D : DB (Bits m) B) : List (Bits m) :=
  ((D.keys.map toLex.toEmbedding).sort (· ≤ ·)).map ofLex

variable (I J m) in
/-- One slot of the database register: an input in `{0,1}^m ∪ {⊥}` and an output in
`{0,1}^n`. -/
abbrev Slot := Option (Bits m) × BitStr I J

variable (I J m) in
/-- The database register with `t` slots. -/
abbrev Slots (t : ℕ) := Fin t → Slot I J m

instance Slots.instDecidableEq {t : ℕ} : DecidableEq (Slots I J m t) :=
  inferInstanceAs (DecidableEq (Fin t → _))

variable {B : Type} (e : BitStr I J ≃ B)

/-- **The slots of `|D_t⟩`** (CMS19 section 3.5): `(x_1, y_1), …, (x_|D|, y_|D|)` for the support
in lexicographic order and `y_i` the answer `D(x_i)` written in bits, then `(⊥, 0^n)` in the
remaining slots. Meant for `|D| ≤ t`. -/
noncomputable def dbSlots (t : ℕ) (D : DB (Bits m) B) : Slots I J m t := fun j =>
  if h : j.1 < (lexKeys D).length then
    (some (lexKeys D)[j.1], ((D.lookup (lexKeys D)[j.1]).map e.symm).getD 0)
  else (none, 0)

/-- **The database held by a slot tuple**: an entry `x ↦ e y` for each slot `(x, y)` with
`x ≠ ⊥` (the first such slot for each `x`). `slotsDB e (dbSlots e t D) = D` for `|D| ≤ t`. -/
def slotsDB {t : ℕ} (s : Slots I J m t) : DB (Bits m) B :=
  List.toFinmap ((List.ofFn s).filterMap fun p => p.1.map fun x => ⟨x, e p.2⟩)

/-- The basis vector `|i⟩`. -/
noncomputable abbrev ket {κ : Type} [Fintype κ] [DecidableEq κ] (i : κ) : QState κ :=
  EuclideanSpace.single i 1

variable (I J) in
/-- `1/√2^n`, with `2^n = |{0,1}^n|`. -/
noncomputable def invSqrtCard : ℂ :=
  ((Real.sqrt (Fintype.card (BitStr I J)))⁻¹ : ℝ)

/-- **`Dec_x |D⟩`** (CMS19 App. A, p. 47), for a database `D` with `|D| ≤ t`:
`(1/√2^n) ∑_y |D + [x ↦ y]⟩` if `D(x) = ⊥` and `|D| < t`; `|D⟩` if `D(x) = ⊥` and `|D| = t`;
`|D⟩ + (1/√2^n) |D'⟩ − (1/√2^n) |φ_{0^n}⟩` if `D(x) ≠ ⊥`, where `D' = D − x` and
`|φ_{0^n}⟩ = (1/√2^n) ∑_y |D' + [x ↦ y]⟩`. -/
noncomputable def decX (t : ℕ) (x : Bits m) (D : DB (Bits m) B) : QState (Slots I J m t) :=
  if D.lookup x = none then
    if D.size < t then invSqrtCard I J • ∑ y : BitStr I J, ket (dbSlots e t (D.extend x (e y)))
    else ket (dbSlots e t D)
  else
    ket (dbSlots e t D) + invSqrtCard I J • ket (dbSlots e t (D.erase x)) -
      invSqrtCard I J • (invSqrtCard I J •
        ∑ y : BitStr I J, ket (dbSlots e t (DB.extend (D.erase x) x (e y))))

/-- The computational basis of `Sim*`: the adversary's registers `|x, u, z⟩` (work register `W`
and one query register, input `x` and answer `u`) and the database register with `t` slots. -/
abbrev SimRegister (W I J : Type) (m t : ℕ) := QueryReg W 1 (Bits m) (BitStr I J) × Slots I J m t

variable {W : Type} [Fintype W] [DecidableEq W]

/-- The query input `x` of a basis state of the adversary's registers. -/
abbrev qIn (r : QueryReg W 1 (Bits m) (BitStr I J)) : Bits m := (r.2 0).1

/-- The answer register `u` of a basis state of the adversary's registers. -/
abbrev qAns (r : QueryReg W 1 (Bits m) (BitStr I J)) : BitStr I J := (r.2 0).2

instance SimRegister.instDecidableEqQueryReg : DecidableEq (QueryReg W 1 (Bits m) (BitStr I J)) :=
  inferInstanceAs (DecidableEq (W × (Fin 1 → _)))

/-- The slot tuples that are database states `|D_t⟩`, for a database with `|D| ≤ t`. -/
def IsDBState {t : ℕ} (s : Slots I J m t) : Prop :=
  ∃ D : DB (Bits m) B, D.size ≤ t ∧ dbSlots e t D = s

open Classical in
noncomputable instance {t : ℕ} (s : Slots I J m t) : Decidable (IsDBState e s) :=
  Classical.dec _

/-! ### Database states -/

section DBStates

variable {B' : Type} (D : DB (Bits m) B')

theorem mem_lexKeys {x : Bits m} : x ∈ lexKeys D ↔ x ∈ D := by
  simp [lexKeys, Finmap.mem_keys]

theorem nodup_lexKeys : (lexKeys D).Nodup :=
  (Finset.sort_nodup _ _).map ofLex.injective

theorem length_lexKeys : (lexKeys D).length = D.size := by
  simp [lexKeys, DB.size]

end DBStates

variable {t : ℕ}

omit [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J] in
/-- The slots of `|D_t⟩` as a list: the entries in lexicographic order, then empty slots. -/
theorem ofFn_dbSlots {D : DB (Bits m) B} (h : D.size ≤ t) :
    List.ofFn (dbSlots e t D) =
      (lexKeys D).map (fun x => (some x, ((D.lookup x).map e.symm).getD 0)) ++
        List.replicate (t - D.size) (none, 0) := by
  refine List.ext_getElem (by simp [length_lexKeys]; omega) fun j h1 h2 => ?_
  rw [List.getElem_ofFn]
  simp only [dbSlots]
  by_cases hj : j < (lexKeys D).length
  · rw [dif_pos hj, List.getElem_append_left (by simpa using hj), List.getElem_map]
  · rw [dif_neg hj, List.getElem_append_right (by simpa using hj), List.getElem_replicate]

omit [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J] in
/-- **The database held by `|D_t⟩` is `D`**, for `|D| ≤ t`. -/
theorem slotsDB_dbSlots {D : DB (Bits m) B} (h : D.size ≤ t) : slotsDB e (dbSlots e t D) = D := by
  have hl : (List.ofFn (dbSlots e t D)).filterMap
      (fun p => p.1.map fun x => (⟨x, e p.2⟩ : Σ _ : Bits m, B)) =
      (lexKeys D).map fun x => ⟨x, e (((D.lookup x).map e.symm).getD 0)⟩ := by
    rw [ofFn_dbSlots e h, List.filterMap_append, List.filterMap_map]
    have h0 : (List.replicate (t - D.size) ((none : Option (Bits m)), (0 : BitStr I J))).filterMap
        (fun p => p.1.map fun x => (⟨x, e p.2⟩ : Σ _ : Bits m, B)) = [] := by
      induction t - D.size with
      | zero => rfl
      | succ n ih => simpa [List.replicate_succ] using ih
    rw [h0, List.append_nil]
    induction lexKeys D with
    | nil => rfl
    | cons x l ih => simp [ih]
  refine Finmap.ext_lookup fun x => ?_
  rw [slotsDB, Finmap.dlookup_list_toFinmap, hl]
  by_cases hx : x ∈ D
  · obtain ⟨b, hb⟩ := DB.mem_iff_lookup.1 hx
    rw [hb]
    refine List.mem_dlookup ?_ ?_
    · rw [List.NodupKeys, List.keys, List.map_map]
      convert nodup_lexKeys D
      induction lexKeys D with
      | nil => rfl
      | cons x l ih => simp [ih]
    · refine List.mem_map.2 ⟨x, (mem_lexKeys D).2 hx, ?_⟩
      simp [hb]
  · rw [Finmap.lookup_eq_none.2 hx, List.dlookup_eq_none]
    simpa [List.keys, mem_lexKeys] using hx

omit [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J] in
theorem isDBState_dbSlots {D : DB (Bits m) B} (h : D.size ≤ t) : IsDBState e (dbSlots e t D) :=
  ⟨D, h, rfl⟩

omit [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J] in
/-- A database state holds a database of size at most `t`, whose state it is. -/
theorem IsDBState.dbSlots_slotsDB {s : Slots I J m t} (hs : IsDBState e s) :
    (slotsDB e s).size ≤ t ∧ dbSlots e t (slotsDB e s) = s := by
  obtain ⟨D, hD, rfl⟩ := hs
  rw [slotsDB_dbSlots e hD]
  exact ⟨hD, rfl⟩

/-- A basis vector `|D_t⟩` has no weight on the slot tuples that are not database states. -/
theorem ket_dbSlots_apply {D : DB (Bits m) B} (h : D.size ≤ t) {s : Slots I J m t}
    (hs : ¬ IsDBState e s) : ket (dbSlots e t D) s = 0 := by
  rw [ket, PiLp.single_apply, if_neg]
  rintro rfl
  exact hs (isDBState_dbSlots e h)

/-- `Dec_x |D⟩` is a combination of database states. -/
theorem decX_apply_eq_zero {x : Bits m} {D : DB (Bits m) B} (h : D.size ≤ t)
    {s : Slots I J m t} (hs : ¬ IsDBState e s) : decX e t x D s = 0 := by
  unfold decX
  split_ifs with hx ht
  · rw [PiLp.smul_apply, WithLp.ofLp_sum, Finset.sum_apply]
    rw [Finset.sum_eq_zero fun y _ => ket_dbSlots_apply e ?_ hs, smul_zero]
    rw [DB.size_extend_of_notMem (Finmap.lookup_eq_none.1 hx)]
    omega
  · exact ket_dbSlots_apply e h hs
  · have hmem : x ∈ D := by
      by_contra hn
      exact hx (Finmap.lookup_eq_none.2 hn)
    have he := DB.size_erase_of_mem hmem
    simp only [PiLp.sub_apply, PiLp.add_apply, PiLp.smul_apply, WithLp.ofLp_sum,
      Finset.sum_apply]
    rw [ket_dbSlots_apply e h hs, ket_dbSlots_apply e (by omega) hs,
      Finset.sum_eq_zero fun y _ => ket_dbSlots_apply e ?_ hs]
    · simp
    · exact DB.size_extend_le.trans (by omega)

variable (W) in
/-- **`Dec`** (CMS19 App. A, p. 47): `|x, u, z, D⟩ ↦ |x, u, z⟩ Dec_x |D⟩` on the database
states, the identity on the other basis states. -/
noncomputable def decOp (t : ℕ) :
    QState (SimRegister W I J m t) →L[ℂ] QState (SimRegister W I J m t) :=
  kernelOp fun b' b =>
    if b'.1 = b.1 then
      (if IsDBState e b.2 then decX e t (qIn b.1) (slotsDB e b.2) else ket b.2) b'.2
    else 0

/-- `(−1)^{u·D(x)}` with `u·⊥ := 0`. -/
def dbPhase (u : BitStr I J) (x : Bits m) (D : DB (Bits m) B) : ℂ :=
  match D.lookup x with
  | none => 1
  | some b => signOf (u.dot (e.symm b))

variable (W) in
/-- **`O0`** (CMS19 App. A, p. 47): `|x, u, z, D⟩ ↦ (−1)^{u·D(x)} |x, u, z, D⟩`, where
`u·⊥ := 0`; `D` is the database the slots hold. -/
noncomputable def phaseOp (t : ℕ) :
    QState (SimRegister W I J m t) →L[ℂ] QState (SimRegister W I J m t) :=
  kernelOp fun b' b => if b' = b then dbPhase e (qAns b.1) (qIn b.1) (slotsDB e b.2) else 0

variable (W) in
/-- **The compressed phase oracle with query bound `t`** (CMS19 section 3.6 and App. A, p. 47):
`O = Dec ∘ O0 ∘ Dec`. -/
noncomputable def compressedOracle (t : ℕ) :
    QState (SimRegister W I J m t) →L[ℂ] QState (SimRegister W I J m t) :=
  decOp e W t ∘L phaseOp e W t ∘L decOp e W t

variable (W) in
/-- **`I ⊗ H^n` on the answer register** (CMS19 section 3.6, p. 16):
`|x, y, z, D⟩ ↦ (1/√2^n) ∑_u (−1)^{u·y} |x, u, z, D⟩`. -/
noncomputable def hadamard (t : ℕ) :
    QState (SimRegister W I J m t) →L[ℂ] QState (SimRegister W I J m t) :=
  kernelOp fun b' b =>
    if b'.1.1 = b.1.1 ∧ qIn b'.1 = qIn b.1 ∧ b'.2 = b.2 then
      invSqrtCard I J * signOf ((qAns b'.1).dot (qAns b.1))
    else 0

variable (W) in
/-- **A simulated query** of a standard-oracle adversary: `(I ⊗ H^n) O (I ⊗ H^n)`, the phase form
of `O_h = (I^m ⊗ H^n) O'_h (I^m ⊗ H^n)` with `O'_h` replaced by `O` (CMS19 section 3.6). -/
noncomputable def simQuery (t : ℕ) :
    QState (SimRegister W I J m t) →L[ℂ] QState (SimRegister W I J m t) :=
  hadamard W t ∘L compressedOracle e W t ∘L hadamard W t

/-! ### The Hadamard transform and `O0` are unitary -/

section Unitary

theorem star_invSqrtCard : star (invSqrtCard I J) = invSqrtCard I J := by
  simp [invSqrtCard, Complex.conj_ofReal]

theorem invSqrtCard_mul_self_mul_card :
    invSqrtCard I J * invSqrtCard I J * (Fintype.card (BitStr I J) : ℂ) = 1 := by
  have hpos : (0 : ℝ) < Fintype.card (BitStr I J) := by exact_mod_cast Fintype.card_pos
  have h : ((Real.sqrt (Fintype.card (BitStr I J)))⁻¹ * (Real.sqrt (Fintype.card (BitStr I J)))⁻¹ *
      (Fintype.card (BitStr I J) : ℝ)) = 1 := by
    rw [← mul_inv, Real.mul_self_sqrt hpos.le, inv_mul_cancel₀ hpos.ne']
  simp only [invSqrtCard]
  exact_mod_cast congrArg (fun r : ℝ => (r : ℂ)) h

/-- The Hadamard matrix `(1/√2^n) (−1)^{u'·u}` on `{0,1}^n` is self-adjoint and involutive. -/
theorem hadamardMatrix_inv (u'' u : BitStr I J) :
    ∑ u', invSqrtCard I J * signOf (u''.dot u') * (invSqrtCard I J * signOf (u'.dot u)) =
      if u'' = u then 1 else 0 := by
  have : ∀ u', invSqrtCard I J * signOf (u''.dot u') * (invSqrtCard I J * signOf (u'.dot u)) =
      invSqrtCard I J * invSqrtCard I J * signOf (u'.dot (u'' + u)) := fun u' => by
    rw [BitStr.dot_comm u'' u', ← BitStr.dot_comm (u'' + u), BitStr.dot_add_left,
      BitStr.dot_comm u'' u', BitStr.dot_comm u u', signOf_add]
    ring
  simp_rw [this, ← Finset.mul_sum, sum_signOf_dot]
  have hneg : -u = u := funext fun i => funext fun j => ZMod.neg_eq_self_mod_two _
  have hz : u'' + u = 0 ↔ u'' = u := by
    rw [add_eq_zero_iff_eq_neg, hneg]
  by_cases h : u'' = u
  · rw [if_pos (hz.2 h), if_pos h, invSqrtCard_mul_self_mul_card]
  · rw [if_neg (fun h' => h (hz.1 h')), if_neg h, mul_zero]

variable {W : Type} [Fintype W] [DecidableEq W] {t : ℕ}

/-- The basis of `Sim*` with the answer register last. -/
def answerSplit (W : Type) (t : ℕ) :
    SimRegister W I J m t ≃ (W × Bits m × Slots I J m t) × BitStr I J where
  toFun b := ((b.1.1, qIn b.1, b.2), qAns b.1)
  invFun p := ((p.1.1, fun _ => (p.1.2.1, p.2)), p.1.2.2)
  left_inv b := by
    obtain ⟨⟨w, q⟩, s⟩ := b
    simp only [Prod.mk.injEq, true_and, and_true]
    exact funext fun i => by rw [Subsingleton.elim i 0]
  right_inv _ := rfl

/-- **`I ⊗ H^n` is unitary.** -/
theorem norm_hadamard (v : QState (SimRegister W I J m t)) : ‖hadamard W t v‖ = ‖v‖ := by
  set M : (W × Bits m × Slots I J m t) → BitStr I J → BitStr I J → ℂ :=
    fun _ u' u => invSqrtCard I J * signOf (u'.dot u)
  have hK : ∀ b' b : SimRegister W I J m t,
      (if b'.1.1 = b.1.1 ∧ qIn b'.1 = qIn b.1 ∧ b'.2 = b.2 then
        invSqrtCard I J * signOf ((qAns b'.1).dot (qAns b.1)) else 0) =
      if (answerSplit W t b').1 = (answerSplit W t b).1 then
        M (answerSplit W t b).1 (answerSplit W t b').2 (answerSplit W t b).2 else 0 := by
    intro b' b
    simp [answerSplit, M]
  refine norm_kernelOp_of_involutive (fun b' b => ?_) (fun b'' b => ?_) v
  · rw [hK, hK]
    exact blockKernel_symm M (fun _ i j => by
      simp only [M, star_mul', star_invSqrtCard, star_signOf, BitStr.dot_comm]) _ _
  · simp_rw [hK]
    rw [Fintype.sum_equiv (answerSplit W t) _
      (fun c => (if (answerSplit W t b'').1 = c.1 then M c.1 (answerSplit W t b'').2 c.2 else 0) *
        (if c.1 = (answerSplit W t b).1 then
          M (answerSplit W t b).1 c.2 (answerSplit W t b).2 else 0)) fun _ => rfl,
      blockKernel_inv M (fun _ i k => hadamardMatrix_inv i k)]
    simp only [(answerSplit W t).injective.eq_iff]

/-- **`O0` is unitary**: it multiplies each basis state by a sign. -/
theorem norm_phaseOp (v : QState (SimRegister W I J m t)) : ‖phaseOp e W t v‖ = ‖v‖ := by
  have hd : ∀ b : SimRegister W I J m t, star (dbPhase e (qAns b.1) (qIn b.1) (slotsDB e b.2)) =
      dbPhase e (qAns b.1) (qIn b.1) (slotsDB e b.2) ∧
      dbPhase e (qAns b.1) (qIn b.1) (slotsDB e b.2) *
        dbPhase e (qAns b.1) (qIn b.1) (slotsDB e b.2) = 1 := by
    intro b
    unfold dbPhase
    split
    · simp
    · exact ⟨star_signOf _, signOf_mul_self _⟩
  refine norm_kernelOp_of_involutive (fun b' b => ?_) (fun b'' b => ?_) v
  · by_cases h : b' = b
    · subst h
      simp [(hd b').1]
    · simp [h, Ne.symm h]
  · rw [Finset.sum_eq_single b'' (fun c _ hc => by simp [Ne.symm hc]) (by simp)]
    by_cases h : b'' = b
    · subst h
      simp [(hd b'').2]
    · simp [h]

end Unitary

/-! ### `Dec` is unitary

On the database states, `Dec_x` is a direct sum of reflections. For a database `D₀` with
`x ∉ supp(D₀)` and `|D₀| < t`, the states `|D₀⟩` and `|D₀ + [x ↦ y]⟩` span a block on which
`Dec_x = 1 − 2 u uᵀ` with `u = (|D₀⟩ − |φ_{0^n}⟩)/√2`, a unit vector; every other database state
is fixed (`x ∉ supp(D)`, `|D| = t`), and so is every slot tuple that is not a database state.
`decBlock e t x s` is the block of `s` (`D − x` for `|D⟩ = s`, when it has fewer than `t`
entries) and `decAmp e t x s` is `√2 u`'s entry at `s` (`reflKernel`). -/

section DecUnitary


variable (I J) in
/-- `1/√2^n` as a real number. -/
noncomputable def invSqrtCardR : ℝ := (Real.sqrt (Fintype.card (BitStr I J)))⁻¹

theorem invSqrtCard_eq : invSqrtCard I J = (invSqrtCardR I J : ℂ) := rfl

theorem invSqrtCardR_sq_mul_card : invSqrtCardR I J * invSqrtCardR I J *
    (Fintype.card (BitStr I J) : ℝ) = 1 := by
  have h := invSqrtCard_mul_self_mul_card (I := I) (J := J)
  rw [invSqrtCard_eq] at h
  exact_mod_cast h

variable {t : ℕ}

/-- The block of `s` for `Dec_x`: `D − x` for a database state `s = |D⟩` with `|D − x| < t`. -/
noncomputable def decBlock (t : ℕ) (x : Bits m) (s : Slots I J m t) : Option (DB (Bits m) B) :=
  if IsDBState e s ∧ DB.size ((slotsDB e s).erase x) < t then some ((slotsDB e s).erase x) else none

/-- The entry at `s` of `√2 u`, for the unit vector `u = (|D₀⟩ − |φ_{0^n}⟩)/√2` of its block:
`1` at `|D₀⟩`, `−1/√2^n` at `|D₀ + [x ↦ y]⟩`, `0` outside the blocks. -/
noncomputable def decAmp (t : ℕ) (x : Bits m) (s : Slots I J m t) : ℝ :=
  if decBlock e t x s = none then 0
  else if x ∈ slotsDB e s then -invSqrtCardR I J else 1

omit [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J] in
theorem dbSlots_inj {D D' : DB (Bits m) B} (hD : D.size ≤ t) (hD' : D'.size ≤ t) :
    dbSlots e t D' = dbSlots e t D ↔ D' = D := by
  refine ⟨fun h => ?_, fun h => h ▸ rfl⟩
  rw [← slotsDB_dbSlots e hD, ← slotsDB_dbSlots e hD', h]

open Classical in
theorem ket_dbSlots_dbSlots {D D' : DB (Bits m) B} (hD : D.size ≤ t) (hD' : D'.size ≤ t) :
    ket (dbSlots e t D) (dbSlots e t D') = if D' = D then 1 else 0 := by
  rw [ket, PiLp.single_apply]
  exact if_congr (dbSlots_inj e hD hD') rfl rfl

omit [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J] in
theorem decBlock_dbSlots {x : Bits m} {D : DB (Bits m) B} (hD : D.size ≤ t) :
    decBlock e t x (dbSlots e t D) = if DB.size (D.erase x) < t then some (D.erase x) else none := by
  simp only [decBlock, slotsDB_dbSlots e hD, isDBState_dbSlots e hD, true_and]

theorem decAmp_dbSlots {x : Bits m} {D : DB (Bits m) B} (hD : D.size ≤ t) :
    decAmp e t x (dbSlots e t D) = if DB.size (D.erase x) < t then
      (if x ∈ D then -invSqrtCardR I J else 1) else 0 := by
  simp only [decAmp, decBlock_dbSlots e hD, slotsDB_dbSlots e hD]
  split_ifs <;> simp_all

open Classical in
/-- `∑_y ⟨D'| D₀ + [x ↦ y]⟩ = [x ∈ supp(D') ∧ D' − x = D₀]`. -/
theorem sum_ket_extend {x : Bits m} {D₀ D' : DB (Bits m) B} (hx : x ∉ D₀) (hsz : D₀.size < t)
    (hD' : D'.size ≤ t) :
    ∑ y : BitStr I J, ket (dbSlots e t (D₀.extend x (e y))) (dbSlots e t D') =
      if x ∈ D' ∧ D'.erase x = D₀ then 1 else 0 := by
  have hext : ∀ y : BitStr I J, (D₀.extend x (e y)).size ≤ t := fun y => by
    rw [DB.size_extend_of_notMem hx]
    omega
  simp_rw [ket_dbSlots_dbSlots e (hext _) hD', DB.eq_extend_iff hx]
  split_ifs with h
  · obtain ⟨hmem, herase⟩ := h
    obtain ⟨b, hb⟩ := DB.mem_iff_lookup.1 hmem
    rw [Finset.sum_eq_single (e.symm b)]
    · simp [hb, herase]
    · intro y _ hy
      rw [if_neg]
      rintro ⟨h1, -⟩
      rw [hb, Option.some_inj] at h1
      exact hy (by rw [h1, Equiv.symm_apply_apply])
    · simp
  · refine Finset.sum_eq_zero fun y _ => if_neg fun ⟨h1, h2⟩ => h ⟨?_, h2⟩
    exact DB.mem_iff_lookup.2 ⟨_, h1⟩

open Classical in
/-- **`Dec_x` on database states is the reflection matrix**: for `|D|, |D'| ≤ t`,
`⟨D'| Dec_x |D⟩ = [D' = D] − 2 [same block] u(D') u(D)`. -/
theorem decX_apply_dbSlots {x : Bits m} {D D' : DB (Bits m) B} (hD : D.size ≤ t)
    (hD' : D'.size ≤ t) :
    decX e t x D (dbSlots e t D') =
      reflKernel (decBlock e t x) (decAmp e t x) (dbSlots e t D') (dbSlots e t D) := by
  unfold reflKernel
  rw [decBlock_dbSlots e hD, decBlock_dbSlots e hD', decAmp_dbSlots e hD, decAmp_dbSlots e hD',
    if_congr (dbSlots_inj e hD hD') rfl rfl]
  unfold decX
  by_cases hx : x ∈ D
  · -- `D(x) ≠ ⊥`: the block of `D − x`
    have hl : D.lookup x ≠ none := fun h' => Finmap.lookup_eq_none.1 h' hx
    have he := DB.size_erase_of_mem hx
    have hsz : DB.size (D.erase x) < t := by omega
    have hx0 : x ∉ D.erase x := Finmap.notMem_erase_self
    have hne : D.erase x ≠ D := fun h' => hx0 (by rw [h']; exact hx)
    have hk1 := ket_dbSlots_dbSlots e hD hD'
    have hk2 := ket_dbSlots_dbSlots e (D := D.erase x) (by omega) hD'
    have hs := sum_ket_extend e hx0 hsz hD'
    rw [if_neg hl]
    simp only [PiLp.sub_apply, PiLp.add_apply, PiLp.smul_apply, WithLp.ofLp_sum,
      Finset.sum_apply, smul_eq_mul, hk1, hk2, hs, invSqrtCard_eq, hsz, if_true, hx]
    by_cases h1 : D' = D.erase x
    · subst h1
      simp [hx0, DB.erase_of_notMem hx0, hsz, hne]
    · by_cases h2 : x ∈ D' ∧ D'.erase x = D.erase x
      · have hsz' : DB.size (D'.erase x) < t := h2.2 ▸ hsz
        simp [h1, h2, hsz', hsz]
      · have h4 : D'.erase x ≠ D.erase x := by
          intro h5
          by_cases hm : x ∈ D'
          · exact h2 ⟨hm, h5⟩
          · exact h1 (by rw [← h5, DB.erase_of_notMem hm])
        simp [h1, h2, h4]
  · -- `D(x) = ⊥`
    have hl : D.lookup x = none := Finmap.lookup_eq_none.2 hx
    rw [if_pos hl, DB.erase_of_notMem hx]
    have hk1 := ket_dbSlots_dbSlots e hD hD'
    by_cases hsz : D.size < t
    · have hs := sum_ket_extend e hx hsz hD'
      rw [if_pos hsz]
      simp only [PiLp.smul_apply, WithLp.ofLp_sum, Finset.sum_apply, smul_eq_mul, hs,
        invSqrtCard_eq, hsz, if_true, hx, if_false]
      by_cases h1 : D' = D
      · subst h1
        simp [hx, DB.erase_of_notMem hx, hsz]
      · by_cases h2 : x ∈ D' ∧ D'.erase x = D
        · have hsz' : DB.size (D'.erase x) < t := h2.2 ▸ hsz
          simp [h1, h2, hsz', hsz]
        · have h4 : D'.erase x ≠ D := by
            intro h5
            by_cases hm : x ∈ D'
            · exact h2 ⟨hm, h5⟩
            · exact h1 (by rw [← h5, DB.erase_of_notMem hm])
          simp [h1, h2, h4]
    · rw [if_neg hsz, hk1]
      simp [hsz]

omit [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J] in
theorem decBlock_of_not {x : Bits m} {s : Slots I J m t} (hs : ¬ IsDBState e s) :
    decBlock e t x s = none := by
  simp [decBlock, hs]

theorem decAmp_of_not {x : Bits m} {s : Slots I J m t} (hs : ¬ IsDBState e s) :
    decAmp e t x s = 0 := by
  simp [decAmp, decBlock_of_not e hs]

open Classical in
/-- **The matrix of `Dec_x` on the `t`-slot register is the reflection matrix** (database states
by `decX_apply_dbSlots`; `Dec_x` is the identity on the other slot tuples, which lie in no
block). -/
theorem decMatrix_eq (x : Bits m) (s s' : Slots I J m t) :
    (if IsDBState e s then decX e t x (slotsDB e s) else ket s) s' =
      reflKernel (decBlock e t x) (decAmp e t x) s' s := by
  by_cases hs : IsDBState e s
  · obtain ⟨hD, hsD⟩ := IsDBState.dbSlots_slotsDB e hs
    rw [if_pos hs]
    by_cases hs' : IsDBState e s'
    · obtain ⟨hD', hsD'⟩ := IsDBState.dbSlots_slotsDB e hs'
      calc decX e t x (slotsDB e s) s' = decX e t x (slotsDB e s) (dbSlots e t (slotsDB e s')) := by
            rw [hsD']
        _ = _ := decX_apply_dbSlots e hD hD'
        _ = _ := by rw [hsD, hsD']
    · have hne : s' ≠ s := fun h => hs' (h ▸ hs)
      rw [decX_apply_eq_zero e hD hs']
      simp [reflKernel, hne, decAmp_of_not e hs']
  · rw [if_neg hs, ket, PiLp.single_apply]
    simp [reflKernel, decAmp_of_not e hs]

/-- The members of the block of `D₀` for `Dec_x`: `|D₀⟩` (`none`) and `|D₀ + [x ↦ y]⟩` (`some y`). -/
noncomputable def blockSlot (t : ℕ) (x : Bits m) (D₀ : DB (Bits m) B) :
    Option (BitStr I J) → Slots I J m t
  | none => dbSlots e t D₀
  | some y => dbSlots e t (DB.extend D₀ x (e y))

/-- The database of a block member. -/
def blockDB (x : Bits m) (D₀ : DB (Bits m) B) : Option (BitStr I J) → DB (Bits m) B
  | none => D₀
  | some y => DB.extend D₀ x (e y)

section Block

variable {x : Bits m} {D₀ : DB (Bits m) B} (hx : x ∉ D₀) (hsz : D₀.size < t)
include hx hsz

omit [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J] in
theorem size_blockDB_le (o : Option (BitStr I J)) : (blockDB e x D₀ o).size ≤ t := by
  cases o with
  | none => exact hsz.le
  | some y =>
    simp only [blockDB]
    rw [DB.size_extend_of_notMem hx]
    omega

omit hx hsz [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J] in
theorem blockSlot_eq (o : Option (BitStr I J)) :
    blockSlot e t x D₀ o = dbSlots e t (blockDB e x D₀ o) := by
  cases o <;> rfl

omit [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J] in
theorem slotsDB_blockSlot (o : Option (BitStr I J)) :
    slotsDB e (blockSlot e t x D₀ o) = blockDB e x D₀ o := by
  rw [blockSlot_eq e, slotsDB_dbSlots e (size_blockDB_le e hx hsz o)]

omit [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J] in
theorem blockSlot_injective : Function.Injective (blockSlot e t x D₀) := by
  intro o o' h
  rw [blockSlot_eq e, blockSlot_eq e,
    dbSlots_inj e (size_blockDB_le e hx hsz o') (size_blockDB_le e hx hsz o)] at h
  cases o with
  | none =>
    cases o' with
    | none => rfl
    | some y' =>
      have : x ∈ blockDB e x D₀ (some y') := DB.mem_extend.2 (Or.inl rfl)
      rw [← h] at this
      exact absurd this hx
  | some y =>
    cases o' with
    | none =>
      have : x ∈ blockDB e x D₀ (some y) := DB.mem_extend.2 (Or.inl rfl)
      rw [h] at this
      exact absurd this hx
    | some y' =>
      have h' := congrArg (fun D : DB (Bits m) B => D.lookup x) h
      simp only [blockDB, DB.lookup_extend_self, Option.some_inj] at h'
      rw [e.injective h']

omit [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J] in
theorem decBlock_blockSlot (o : Option (BitStr I J)) :
    decBlock e t x (blockSlot e t x D₀ o) = some D₀ := by
  rw [blockSlot_eq e, decBlock_dbSlots e (size_blockDB_le e hx hsz o)]
  cases o with
  | none => simp [blockDB, DB.erase_of_notMem hx, hsz]
  | some y => simp [blockDB, DB.erase_extend_of_notMem hx, hsz]

theorem decAmp_blockSlot_none : decAmp e t x (blockSlot e t x D₀ none) = 1 := by
  rw [blockSlot_eq e, decAmp_dbSlots e (size_blockDB_le e hx hsz none)]
  simp [blockDB, DB.erase_of_notMem hx, hsz, hx]

theorem decAmp_blockSlot_some (y : BitStr I J) :
    decAmp e t x (blockSlot e t x D₀ (some y)) = -invSqrtCardR I J := by
  rw [blockSlot_eq e, decAmp_dbSlots e (size_blockDB_le e hx hsz (some y))]
  simp [blockDB, DB.erase_extend_of_notMem hx, hsz]

omit hx hsz [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J] in
theorem exists_blockSlot_of_decBlock {s : Slots I J m t} (h : decBlock e t x s = some D₀) :
    ∃ o, blockSlot e t x D₀ o = s := by
  have hdb : IsDBState e s ∧ DB.size ((slotsDB e s).erase x) < t ∧ (slotsDB e s).erase x = D₀ := by
    unfold decBlock at h
    split_ifs at h with h'
    exact ⟨h'.1, h'.2, Option.some_inj.1 h⟩
  obtain ⟨hdb, -, herase⟩ := hdb
  obtain ⟨-, hsD⟩ := IsDBState.dbSlots_slotsDB e hdb
  by_cases hm : x ∈ slotsDB e s
  · obtain ⟨b, hb⟩ := DB.mem_iff_lookup.1 hm
    refine ⟨some (e.symm b), ?_⟩
    simp only [blockSlot, Equiv.apply_symm_apply, ← herase, DB.extend_erase_of_lookup hb, hsD]
  · refine ⟨none, ?_⟩
    simp only [blockSlot, ← herase, DB.erase_of_notMem hm, hsD]

open Classical in
/-- A sum over the block of `D₀` is a sum over its members. -/
theorem sum_block {M : Type*} [AddCommMonoid M] (F : Slots I J m t → M) :
    ∑ s, (if decBlock e t x s = some D₀ then F s else 0) = ∑ o, F (blockSlot e t x D₀ o) :=
  (Fintype.sum_of_injective _ (blockSlot_injective e hx hsz) (fun o => F (blockSlot e t x D₀ o))
    (fun s => if decBlock e t x s = some D₀ then F s else 0)
    (fun s hs => if_neg fun h => hs (exists_blockSlot_of_decBlock e h))
    (fun o => (if_pos (decBlock_blockSlot e hx hsz o)).symm)).symm

end Block

omit [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J] in
/-- The databases of a block. -/
theorem decBlock_eq_some {x : Bits m} {s : Slots I J m t} {D₀ : DB (Bits m) B}
    (h : decBlock e t x s = some D₀) : x ∉ D₀ ∧ D₀.size < t := by
  unfold decBlock at h
  split_ifs at h with h'
  rw [← Option.some_inj.1 h]
  exact ⟨Finmap.notMem_erase_self, h'.2⟩

open Classical in
/-- Each block vector `u = (|D₀⟩ − |φ_{0^n}⟩)/√2` is a unit vector: `1 + 2^n · (1/2^n) = 2`. -/
theorem sum_decAmp_sq (x : Bits m) (s : Slots I J m t) (hs : decAmp e t x s ≠ 0) :
    ∑ s', (if decBlock e t x s' = decBlock e t x s then decAmp e t x s' ^ 2 else 0) = 2 := by
  have hb : decBlock e t x s ≠ none := fun h => hs (by simp [decAmp, h])
  obtain ⟨D₀, hD₀⟩ := Option.ne_none_iff_exists'.1 hb
  obtain ⟨hx, hsz⟩ := decBlock_eq_some e hD₀
  rw [hD₀, sum_block e hx hsz, Fintype.sum_option, decAmp_blockSlot_none e hx hsz]
  simp only [decAmp_blockSlot_some e hx hsz, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  nlinarith [invSqrtCardR_sq_mul_card (I := I) (J := J)]

open Classical in
/-- The matrix of `Dec`: `Dec_x` on the database register of each `|x, u, z⟩`. -/
theorem decOp_eq {W : Type} [Fintype W] [DecidableEq W] :
    decOp e W t = kernelOp fun b' b : SimRegister W I J m t =>
      if b'.1 = b.1 then reflKernel (decBlock e t (qIn b.1)) (decAmp e t (qIn b.1)) b'.2 b.2
      else 0 := by
  unfold decOp
  congr 1
  funext b' b
  by_cases h : b'.1 = b.1
  · rw [if_pos h, if_pos h]
    exact decMatrix_eq e _ _ _
  · rw [if_neg h, if_neg h]

open Classical in
/-- **`Dec` is unitary**: on each `|x, u, z⟩` it applies `Dec_x`, a reflection. -/
theorem norm_decOp {W : Type} [Fintype W] [DecidableEq W] (v : QState (SimRegister W I J m t)) :
    ‖decOp e W t v‖ = ‖v‖ := by
  set M : QueryReg W 1 (Bits m) (BitStr I J) → Slots I J m t → Slots I J m t → ℂ :=
    fun r => reflKernel (decBlock e t (qIn r)) (decAmp e t (qIn r))
  rw [decOp_eq]
  refine norm_kernelOp_of_involutive (fun b' b => ?_) (fun b'' b => ?_) v
  · exact blockKernel_symm M (fun r i j => reflKernel_symm _ _ i j) b b'
  · exact blockKernel_inv M (fun r i k => reflKernel_inv _ _ (fun s hs => sum_decAmp_sq e _ s hs) i k)
      b'' b

open Classical in
/-- **`Dec` is an involution** (CMS19 App. A, p. 47: "Dec_x ∘ Dec_x is the identity"); so a query
with `u = 0^n`, on which `O0` acts trivially, is fixed by `O`, and padding an adversary with such
queries does not change it. -/
theorem decOp_decOp {W : Type} [Fintype W] [DecidableEq W] (v : QState (SimRegister W I J m t)) :
    decOp e W t (decOp e W t v) = v := by
  set M : QueryReg W 1 (Bits m) (BitStr I J) → Slots I J m t → Slots I J m t → ℂ :=
    fun r => reflKernel (decBlock e t (qIn r)) (decAmp e t (qIn r))
  rw [decOp_eq]
  exact kernelOp_kernelOp_of_inv (fun b'' b => blockKernel_inv M
    (fun r i k => reflKernel_inv _ _ (fun s hs => sum_decAmp_sq e _ s hs) i k) b'' b) v

end DecUnitary

/-! ### The simulated adversary -/

variable {O : Type} {t : ℕ} (A : QueryAlg (Bits m) (BitStr I J) t O)

/-- `|φ, ∅⟩`: the adversary's initial state and the empty database with `t` slots. -/
noncomputable def simInit : QState (SimRegister A.W I J m t) :=
  WithLp.toLp 2 fun b => A.init b.1 * (if b.2 = dbSlots e t (∅ : DB (Bits m) B) then 1 else 0)

/-- The adversary's unitary `step k`, extended by the identity on the database register. -/
noncomputable def simStep (k : ℕ) : QState (SimRegister A.W I J m t) ≃ₗᵢ[ℂ] QState (SimRegister A.W I J m t) :=
  controlled fun _ => (A.toOracleAlg ∅).stepAt () k

/-- The state of `Sim*(A)` after `step k`, before the next query. -/
noncomputable def simStage (k : ℕ) : QState (SimRegister A.W I J m t) :=
  Nat.rec (simStep A 0 (simInit e A)) (fun k v => simStep A (k + 1) (simQuery e A.W t v)) k

/-- **`|Sim*(A)⟩`** (CMS19 section 3.6, p. 17): `A_t O ⋯ A_1 O |φ_0, ∅⟩`, in phase form, with the
compressed phase oracle of bound `t`. -/
noncomputable def simState : QState (SimRegister A.W I J m t) := simStage e A t

/-- **The outcome of `Sim*(A)`** (CMS19 p. 20): the Born weights of measuring the output register
and the database register of `|Sim*(A)⟩` in the computational basis, as the output and the
database the slots hold. -/
noncomputable def simLaw : MeasureTheory.OuterMeasure (O × DB (Bits m) B) :=
  MeasureTheory.OuterMeasure.map (fun b : SimRegister A.W I J m t => (A.out b.1.1, slotsDB e b.2))
    (bornWeight (simState e A))

/-! ### Database projectors -/

/-- **The slot tuple is a database state of `P`**: `|D_t⟩` for a database `D ∈ P` with
`|D| ≤ t`. -/
def InP (t : ℕ) (P : Set (DB (Bits m) B)) (s : Slots I J m t) : Prop :=
  ∃ D ∈ P, D.size ≤ t ∧ s = dbSlots e t D

theorem inP_iff {t : ℕ} {P : Set (DB (Bits m) B)} {s : Slots I J m t} :
    InP e t P s ↔ ∃ D ∈ P, D.size ≤ t ∧ s = dbSlots e t D :=
  Iff.rfl

variable (W) in
/-- **The projector of a database property** (CMS19 Proposition 5.8, p. 22):
`P := I ⊗ ∑_{D ∈ P} |D⟩⟨D|`, over the databases with a state `|D_t⟩` (`|D| ≤ t`). -/
noncomputable def dbProj (t : ℕ) (P : Set (DB (Bits m) B)) :
    QState (SimRegister W I J m t) →L[ℂ] QState (SimRegister W I J m t) :=
  mask {b | InP e t P b.2}

variable (W) in
/-- **`P_t`** (CMS19 p. 22): `I ⊗ ∑_{D : |D| ≤ t} |D⟩⟨D|`, the projector onto the database
states of the `t`-slot register. -/
noncomputable def sizeProj (t : ℕ) : QState (SimRegister W I J m t) →L[ℂ] QState (SimRegister W I J m t) :=
  mask {b | ∃ D : DB (Bits m) B, D.size ≤ t ∧ b.2 = dbSlots e t D}

variable (W) in
/-- **`P_t O P_t`** (CMS19 p. 22): the compressed oracle between two projectors onto the database
states of the `t`-slot register, the operator of one query step in Lemmas 5.9 and 5.10. -/
noncomputable def queryStepOp (t : ℕ) : QState (SimRegister W I J m t) →L[ℂ] QState (SimRegister W I J m t) :=
  sizeProj e W t ∘L compressedOracle e W t ∘L sizeProj e W t

/-! ### The simulated state is supported on database states -/

section Support

omit [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J] in
/-- An operator whose matrix has no entry from `S` to its complement preserves support in `S`. -/
theorem _root_.GordieHowe.Quantum.Supported.kernelOp {κ : Type} [Fintype κ] {S : Set κ} {K : κ → κ → ℂ}
    (hK : ∀ b' b, b ∈ S → b' ∉ S → K b' b = 0) {v : QState κ} (hv : Supported S v) :
    Supported S (kernelOp K v) := by
  intro b' hb'
  rw [kernelOp_apply]
  refine Finset.sum_eq_zero fun b _ => ?_
  by_cases hb : b ∈ S
  · rw [hK b' b hb hb', zero_mul]
  · rw [hv b hb, mul_zero]

omit [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J] in
/-- A unitary on the first register preserves support in a set of values of the second. -/
theorem _root_.GordieHowe.Quantum.Supported.controlled {κ L : Type} [Fintype κ] [Fintype L] {Q : Set L}
    (U : L → QState κ ≃ₗᵢ[ℂ] QState κ) {v : QState (κ × L)} (hv : Supported {p | p.2 ∈ Q} v) :
    Supported {p | p.2 ∈ Q} (Quantum.controlled U v) := by
  rintro ⟨i, l⟩ hl
  rw [controlled_apply]
  have : (WithLp.toLp 2 fun i' => v (i', l) : QState κ) = 0 := by
    ext i'
    exact hv (i', l) hl
  rw [this, map_zero]
  rfl

omit [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J] in
/-- On a state supported in `S`, masks of sets that agree on `S` agree. -/
theorem _root_.GordieHowe.Quantum.Supported.mask_eq {κ : Type} [Fintype κ] {S A A' : Set κ} {v : QState κ}
    (hv : Supported S v) (h : ∀ b ∈ S, b ∈ A ↔ b ∈ A') : mask A v = mask A' v := by
  ext b
  by_cases hb : b ∈ S
  · by_cases hA : b ∈ A
    · rw [mask_apply_of_mem _ hA, mask_apply_of_mem _ ((h b hb).1 hA)]
    · rw [mask_apply_of_notMem _ hA, mask_apply_of_notMem _ (fun h' => hA ((h b hb).2 h'))]
  · rw [mask_apply, mask_apply]
    by_cases hA : b ∈ A <;> by_cases hA' : b ∈ A' <;> simp [hA, hA', hv b hb]

variable {W : Type} [Fintype W] [DecidableEq W] {t : ℕ}

/-- The basis states of `Sim*` whose database register holds a database state. -/
def DBSupport (W : Type) (t : ℕ) : Set (SimRegister W I J m t) := {b | IsDBState e b.2}

theorem supported_decOp {v : QState (SimRegister W I J m t)} (hv : Supported (DBSupport (B := B) e W t) v) :
    Supported (DBSupport e W t) (decOp e W t v) := by
  refine hv.kernelOp fun b' b hb hb' => ?_
  split_ifs with h1 h2
  · exact decX_apply_eq_zero e (IsDBState.dbSlots_slotsDB e h2).1 hb'
  · exact absurd hb h2
  · rfl

theorem supported_phaseOp {v : QState (SimRegister W I J m t)}
    (hv : Supported (DBSupport (B := B) e W t) v) : Supported (DBSupport e W t) (phaseOp e W t v) := by
  refine hv.kernelOp fun b' b hb hb' => ?_
  rw [if_neg]
  rintro rfl
  exact hb' hb

theorem supported_hadamard {v : QState (SimRegister W I J m t)}
    (hv : Supported (DBSupport (B := B) e W t) v) : Supported (DBSupport e W t) (hadamard W t v) := by
  refine hv.kernelOp fun b' b hb hb' => ?_
  rw [if_neg]
  rintro ⟨-, -, h⟩
  exact hb' (show IsDBState e b'.2 from h ▸ hb)

theorem supported_simQuery {v : QState (SimRegister W I J m t)}
    (hv : Supported (DBSupport (B := B) e W t) v) : Supported (DBSupport e W t) (simQuery e W t v) := by
  rw [simQuery, compressedOracle]
  simp only [ContinuousLinearMap.comp_apply]
  exact supported_hadamard e (supported_decOp e (supported_phaseOp e (supported_decOp e
    (supported_hadamard e hv))))

variable {O : Type} (A : QueryAlg (Bits m) (BitStr I J) t O)

/-- **The state of `Sim*(A)` has weight only on database states**: the database register
starts in `|∅_t⟩`, the adversary's unitaries act as the identity on it, and the Hadamard, `Dec`
and `O0` map database states to combinations of database states. -/
theorem supported_simStage (k : ℕ) : Supported (DBSupport e A.W t) (simStage e A k) := by
  induction k with
  | zero =>
    refine Supported.controlled (Q := {s | IsDBState e s}) _ ?_
    intro b hb
    simp only [simInit, mul_ite, mul_one, mul_zero]
    rw [if_neg]
    intro h
    exact hb (show IsDBState e b.2 from h ▸ isDBState_dbSlots e (by simp))
  | succ k ih => exact Supported.controlled (Q := {s | IsDBState e s}) _ (supported_simQuery e ih)

theorem supported_simState : Supported (DBSupport e A.W t) (simState e A) :=
  supported_simStage e A t

end Support

/-! ### CMS19 Lemma 5.9 -/

section Lemma59

omit [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J] in
/-- A mask on the second register commutes with a unitary on the first. -/
theorem mask_controlled {κ L : Type} [Fintype κ] [Fintype L] (Q : Set L)
    (U : L → QState κ ≃ₗᵢ[ℂ] QState κ) (v : QState (κ × L)) :
    mask {p : κ × L | p.2 ∈ Q} (Quantum.controlled U v) =
      Quantum.controlled U (mask {p : κ × L | p.2 ∈ Q} v) := by
  ext ⟨i, l⟩
  by_cases hl : l ∈ Q
  · rw [mask_apply_of_mem _ (show (i, l) ∈ {p : κ × L | p.2 ∈ Q} from hl), controlled_apply,
      controlled_apply]
    have : (WithLp.toLp 2 fun i' => mask {p : κ × L | p.2 ∈ Q} v (i', l) : QState κ) =
        WithLp.toLp 2 fun i' => v (i', l) := by
      ext i'
      exact mask_apply_of_mem _ (show (i', l) ∈ {p : κ × L | p.2 ∈ Q} from hl)
    rw [this]
  · rw [mask_apply_of_notMem _ (show (i, l) ∉ {p : κ × L | p.2 ∈ Q} from hl), controlled_apply]
    have : (WithLp.toLp 2 fun i' => mask {p : κ × L | p.2 ∈ Q} v (i', l) : QState κ) = 0 := by
      ext i'
      exact mask_apply_of_notMem _ (show (i', l) ∉ {p : κ × L | p.2 ∈ Q} from hl)
    rw [this, map_zero]
    rfl

omit [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J] in
/-- A mask commutes with an operator whose matrix links only states on the same side of it. -/
theorem kernelOp_mask {κ : Type} [Fintype κ] {S : Set κ} {K : κ → κ → ℂ}
    (hK : ∀ b' b, K b' b ≠ 0 → (b' ∈ S ↔ b ∈ S)) (v : QState κ) :
    kernelOp K (mask S v) = mask S (kernelOp K v) := by
  ext b'
  rw [kernelOp_apply, mask_apply]
  by_cases hb' : b' ∈ S
  · rw [Set.indicator_of_mem hb', kernelOp_apply]
    refine Finset.sum_congr rfl fun b _ => ?_
    by_cases hk : K b' b = 0
    · rw [hk, zero_mul, zero_mul]
    · rw [mask_apply_of_mem _ ((hK b' b hk).1 hb')]
  · rw [Set.indicator_of_notMem hb']
    refine Finset.sum_eq_zero fun b _ => ?_
    by_cases hk : K b' b = 0
    · rw [hk, zero_mul]
    · rw [mask_apply_of_notMem _ (fun h => hb' ((hK b' b hk).2 h)), mul_zero]

omit [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J] in
theorem mask_mask_of_subset {κ : Type} [Fintype κ] {A A' : Set κ} (h : A ⊆ A') (v : QState κ) :
    mask A (mask A' v) = mask A v ∧ mask A' (mask A v) = mask A v := by
  constructor <;> ext b <;> simp only [mask_apply] <;> by_cases hb : b ∈ A
  · simp [hb, h hb]
  · simp [hb]
  · simp [hb, h hb]
  · by_cases hb' : b ∈ A' <;> simp [hb, hb']

variable {W : Type} [Fintype W] [DecidableEq W] {t : ℕ}

/-- The set of basis states whose database register is `|D_t⟩` for a `D ∈ P` with `|D| ≤ t`. -/
abbrev dbSet (W : Type) (t : ℕ) (P : Set (DB (Bits m) B)) : Set (SimRegister W I J m t) :=
  {b | InP e t P b.2}

omit [DecidableEq W] in
theorem dbProj_eq (P : Set (DB (Bits m) B)) : dbProj e W t P = mask (dbSet e W t P) := rfl

omit [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J] [Fintype W] [DecidableEq W] in
theorem dbSet_subset_sizeSet (P : Set (DB (Bits m) B)) :
    dbSet e W t P ⊆ {b | ∃ D : DB (Bits m) B, D.size ≤ t ∧ b.2 = dbSlots e t D} := by
  rintro _ ⟨D, -, hD, h⟩
  exact ⟨D, hD, h⟩

/-- `P` commutes with the Hadamard transform, which acts on the answer register. -/
theorem hadamard_dbProj (P : Set (DB (Bits m) B)) (v : QState (SimRegister W I J m t)) :
    hadamard W t (dbProj e W t P v) = dbProj e W t P (hadamard W t v) :=
  kernelOp_mask (fun b' b hk => by
    have h : b'.2 = b.2 := by
      by_contra hne
      exact hk (if_neg (fun h => hne h.2.2))
    simp only [dbSet, Set.mem_ofPred_eq, h]) v

/-- `P` commutes with the adversary's unitaries, which act as the identity on the database
register. -/
theorem simStep_dbProj {O : Type} (A : QueryAlg (Bits m) (BitStr I J) t O) (k : ℕ)
    (P : Set (DB (Bits m) B)) (v : QState (SimRegister A.W I J m t)) :
    simStep A k (dbProj e A.W t P v) = dbProj e A.W t P (simStep A k v) := by
  rw [dbProj_eq, simStep]
  exact (mask_controlled {s | ∃ D ∈ P, D.size ≤ t ∧ s = dbSlots e t D} _ v).symm

omit [DecidableEq W] in
/-- On database states, `P` and `P̄` add up to the identity. -/
theorem dbProj_add_dbProj_compl {P : Set (DB (Bits m) B)} {v : QState (SimRegister W I J m t)}
    (hv : Supported (DBSupport e W t) v) : dbProj e W t P v + dbProj e W t Pᶜ v = v := by
  ext b
  rw [PiLp.add_apply, dbProj_eq, dbProj_eq, mask_apply, mask_apply]
  by_cases hb : b ∈ DBSupport e W t
  · obtain ⟨hD, hs⟩ := IsDBState.dbSlots_slotsDB e hb
    by_cases hP : slotsDB e b.2 ∈ P
    · have h1 : b ∈ dbSet e W t P := ⟨_, hP, hD, hs.symm⟩
      have h2 : b ∉ dbSet e W t Pᶜ := by
        rintro ⟨D, hDP, hDt, hbD⟩
        exact hDP (by rwa [hbD, slotsDB_dbSlots e hDt] at hP)
      rw [Set.indicator_of_mem h1, Set.indicator_of_notMem h2, add_zero]
    · have h1 : b ∉ dbSet e W t P := by
        rintro ⟨D, hDP, hDt, hbD⟩
        exact hP (by rwa [hbD, slotsDB_dbSlots e hDt])
      have h2 : b ∈ dbSet e W t Pᶜ := ⟨_, hP, hD, hs.symm⟩
      rw [Set.indicator_of_mem h2, Set.indicator_of_notMem h1, zero_add]
  · by_cases h1 : b ∈ dbSet e W t P <;> by_cases h2 : b ∈ dbSet e W t Pᶜ <;>
      simp [Set.indicator, h1, h2, hv b hb]

/-- A simulated query preserves the norm. -/
theorem norm_simQuery (v : QState (SimRegister W I J m t)) : ‖simQuery e W t v‖ = ‖v‖ := by
  simp only [simQuery, compressedOracle, ContinuousLinearMap.comp_apply, norm_hadamard,
    norm_decOp, norm_phaseOp]

/-- One query moves at most `‖P(P_t O P_t)P̄‖` of a unit state's weight into `P`. -/
theorem norm_dbProj_simQuery_le {P : Set (DB (Bits m) B)} {v : QState (SimRegister W I J m t)}
    (hv : Supported (DBSupport e W t) v) (hv1 : ‖v‖ = 1) :
    ‖dbProj e W t P (simQuery e W t v)‖ ≤ ‖dbProj e W t P v‖ +
      ‖dbProj e W t P ∘L queryStepOp e W t ∘L
        dbProj e W t Pᶜ‖ := by
  set T := dbProj e W t P ∘L queryStepOp e W t ∘L
    dbProj e W t Pᶜ
  have hsplit : dbProj e W t P (simQuery e W t v) = dbProj e W t P (simQuery e W t (dbProj e W t P v))
      + dbProj e W t P (simQuery e W t (dbProj e W t Pᶜ v)) := by
    rw [← map_add, ← map_add, dbProj_add_dbProj_compl e hv]
  have h1 : ‖dbProj e W t P (simQuery e W t (dbProj e W t P v))‖ ≤ ‖dbProj e W t P v‖ :=
    (norm_mask_le _ _).trans (norm_simQuery e _).le
  have hT : dbProj e W t P (simQuery e W t (dbProj e W t Pᶜ v)) = hadamard W t (T (hadamard W t v)) := by
    have hPt : ∀ w : QState (SimRegister W I J m t), sizeProj e W t (dbProj e W t Pᶜ w) = dbProj e W t Pᶜ w :=
      fun w => (mask_mask_of_subset (dbSet_subset_sizeSet e Pᶜ) w).2
    have hPt' : ∀ w : QState (SimRegister W I J m t), dbProj e W t P (sizeProj e W t w) = dbProj e W t P w :=
      fun w => (mask_mask_of_subset (dbSet_subset_sizeSet e P) w).1
    simp only [simQuery, queryStepOp, ContinuousLinearMap.comp_apply, T]
    rw [hadamard_dbProj, ← hadamard_dbProj e P, hPt, hPt']
  have h2 : ‖dbProj e W t P (simQuery e W t (dbProj e W t Pᶜ v))‖ ≤ ‖T‖ := by
    rw [hT, norm_hadamard]
    calc ‖T (hadamard W t v)‖ ≤ ‖T‖ * ‖hadamard W t v‖ := T.le_opNorm _
      _ = ‖T‖ := by rw [norm_hadamard, hv1, mul_one]
  rw [hsplit]
  exact (norm_add_le _ _).trans (add_le_add h1 h2)

/-- `|Sim*(A)⟩` and every intermediate state is a unit vector: the adversary's unitaries, the
Hadamard transform, `Dec` and `O0` are unitary. -/
theorem norm_simStage {O : Type} (A : QueryAlg (Bits m) (BitStr I J) t O) (k : ℕ) :
    ‖simStage e A k‖ = 1 := by
  induction k with
  | zero =>
    rw [simStage, Nat.rec_zero, simStep, LinearIsometryEquiv.norm_map]
    exact (norm_tensorKet A.init _).trans A.norm_init
  | succ k ih =>
    show ‖simStep A (k + 1) (simQuery e A.W t (simStage e A k))‖ = 1
    rw [LinearIsometryEquiv.norm_map, norm_simQuery, ih]

/-- **The outcome of `Sim*(A)` has total weight `1`**: `simLaw` is a probability distribution. -/
theorem simLaw_univ {O : Type} (A : QueryAlg (Bits m) (BitStr I J) t O) :
    simLaw e A Set.univ = 1 := by
  rw [simLaw, MeasureTheory.OuterMeasure.map_apply, Set.preimage_univ, bornWeight_apply]
  have h : mask Set.univ (simState e A) = simState e A := by
    ext i
    simp
  rw [h, ← ofReal_norm, simState, norm_simStage]
  simp

/-- **CMS19 Lemma 5.9** (p. 22): "Let P be a database property with ∅ ∉ P. For every A ∈ C*_t,
‖P |Sim*(A)⟩‖ ≤ t · ‖P(P_t O P_t)P̄‖."

Proof (p. 23, in per-step form): `P` commutes with the adversary's unitaries and with the
Hadamard transform; on database states `P + P̄ = 1`; the Hadamard transform, `Dec` and `O0` are
unitary (`norm_hadamard`, `norm_decOp`, `norm_phaseOp`); so each query adds at most
`‖P(P_t O P_t)P̄‖` to `‖P v‖` (`norm_dbProj_simQuery_le`), and `P |φ, ∅⟩ = 0` since `∅ ∉ P`. The
paper's proof has an index slip that does not affect the statement (its factor should be
`‖(C_{i−1} P̄ ⋯ C_1 P̄) |φ_0, ∅⟩‖`). -/
theorem measured_norm_le {O : Type} (A : QueryAlg (Bits m) (BitStr I J) t O)
    (P : Set (DB (Bits m) B)) (hP : (∅ : DB (Bits m) B) ∉ P) :
    ‖dbProj e A.W t P (simState e A)‖ₑ ≤ t * ‖dbProj e A.W t P ∘L
      queryStepOp e A.W t ∘L dbProj e A.W t Pᶜ‖ₑ := by
  set N := ‖dbProj e A.W t P ∘L queryStepOp e A.W t ∘L
    dbProj e A.W t Pᶜ‖
  have hnorm := norm_simStage e A
  have h0 : dbProj e A.W t P (simInit e A) = 0 := by
    ext b
    rw [dbProj_eq, mask_apply]
    by_cases hb : b ∈ dbSet e A.W t P
    · rw [Set.indicator_of_mem hb]
      obtain ⟨D, hDP, hDt, hbD⟩ := hb
      simp only [simInit]
      rw [if_neg, mul_zero]
      · rfl
      intro h
      rw [hbD] at h
      have := (dbSlots_inj e (by simp) hDt).1 h
      exact hP (this ▸ hDP)
    · rw [Set.indicator_of_notMem hb]
      rfl
  have hstep : ∀ k, ‖dbProj e A.W t P (simStage e A k)‖ ≤ k * N := by
    intro k
    induction k with
    | zero =>
      show ‖dbProj e A.W t P (simStep A 0 (simInit e A))‖ ≤ ((0 : ℕ) : ℝ) * N
      rw [← simStep_dbProj, h0, map_zero, norm_zero, Nat.cast_zero, zero_mul]
    | succ k ih =>
      show ‖dbProj e A.W t P (simStep A (k + 1) (simQuery e A.W t (simStage e A k)))‖ ≤ (k + 1 : ℕ) * N
      rw [← simStep_dbProj, LinearIsometryEquiv.norm_map]
      refine (norm_dbProj_simQuery_le e (supported_simStage e A k) (hnorm k)).trans ?_
      push_cast
      linarith
  have h := hstep t
  rw [← ofReal_norm, ← ofReal_norm, ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
  exact ENNReal.ofReal_le_ofReal h

end Lemma59

end GordieHowe.QROM
