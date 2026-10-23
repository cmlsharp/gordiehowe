-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Foundations.ToMathlib.MvPolynomial
public import GordieHowe.Foundations.Probability.ChallengeEvent
public import GordieHowe.Language.Realizations.OfflineMemory
public import GordieHowe.Applications.Falcon512.Gadgets.SelectFirstN
public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.Data.List.Sort
public import Mathlib.Data.Set.Function
public import Mathlib.Order.Fin.Basic
public import Mathlib.Data.Fin.Tuple.Basic

@[expose] public section

/-!
# `MemoryShuffle`: ML-DSA's SampleInBall shuffle by offline memory checking

SampleInBall starts from a zero array and, at step `s` with write index
`i = N − τ + s` and checked sample `j = positions[s] ≤ i`, executes

```
c[i] := c[j]
c[j] := signs[s] ? −1 : 1
```

The gadget checks an execution by matching reads to writes.  Each step
contributes three records, `(address, value, origin)`:

```
read  (j, old value, old origin)
write (j, signed unit, s+1)
write (i, old value, old origin)
```

together with initial zero writes at the `N − τ` live addresses and one final
read per address.  A record is packed as `embed(a) + δ_enc·v + δ_enc²·o`, and
the read and write lists must be permutations, checked as a product identity at
`δ_mem`.

Cell values are the `GF(2¹⁶)` elements `0`, `1`, `θ` for `0`, `+1`, `−1`, with
`θ² + θ + 1 = 0`, so the signed unit is `1 + (θ + 1)·sign`.

The prover commits the read advice (value and 6-bit origin per step), the final array `c_enc` and
its origins. `positions` come from `SelectFirstTau` and satisfy `positions[s] ≤ N − τ + s`, which
this gadget takes as that gadget's conclusion.
-/

namespace GordieHowe.MemoryShuffle

open Polynomial

variable {K : Type*} [Field K] [DecidableEq K]

/-- The element `θ` of the subfield with `θ² + θ + 1 = 0`, encoding `−1`.  A
field fact, carried beside the selection field's data. -/
structure Theta (K : Type*) [Field K] where
  θ : K
  θ_sq : θ ^ 2 + θ + 1 = 0

omit [DecidableEq K] in
/-- In characteristic two, the defining equation gives the sign-bit identity. -/
theorem Theta.sq_add [CharP K 2] (Θ : Theta K) : Θ.θ ^ 2 + Θ.θ = 1 :=
  (eq_neg_of_add_eq_zero_left Θ.θ_sq).trans (CharTwo.neg_eq 1)

/-- Read advice for one step: the claimed old value and its origin. -/
structure ReadAdvice (K : Type*) where
  value : K
  /-- the origin label, committed as 6 bits -/
  origin : BitWires K 6

/-- The committed inputs the gadget reads, for `τ` steps over `N` cells. -/
structure Wit (K : Type*) (N τ : ℕ) where
  positions : Fin τ → BitWires K 8
  signs : Fin τ → K
  read : Fin τ → ReadAdvice K
  cEnc : Fin N → K
  finalOrigin : Fin N → K

/-- The signed unit written at step `s`. -/
def unit (Θ : Theta K) (sign : K) : K := 1 + (Θ.θ + 1) * sign

/-- Packing of a record `(address, value, origin)` at `δ_enc`. -/
def record (δenc : K) (a : K) (v o : K) : K :=
  a + δenc * v + δenc ^ 2 * o

variable {N τ S : ℕ}

/-- The write records: initial zeros, then per step the signed unit at `j` and
the moved value at `i`. -/
def writes (F : SelectionField K S) (Θ : Theta K) (wit : Wit K N τ) (δenc : K) : List K :=
  ((List.range (N - τ)).map fun k => record δenc (F.embed k) 0 0)
  ++ (List.finRange τ).flatMap fun s =>
      [record δenc (F.embedBits (by decide) (wit.positions s)) (unit Θ (wit.signs s)) (F.embed (s + 1)),
       record δenc (F.embed (N - τ + s)) (wit.read s).value (F.embedBits (by decide) (wit.read s).origin)]

/-- `DecodeTernary`: the support and sign bits of a cell value in `{0, 1, θ}`. -/
def decodeTernary (Θ : Theta K) (v : K) : K × K :=
  let sign := v ^ 2 + v
  (v + (Θ.θ + 1) * sign, sign)

/-! ### The specification -/

/-- SampleInBall's shuffle executed on the checked positions and signs, over the
integers: the final array with entries in `{−1, 0, 1}`. -/
-- spec-side
def shuffle (N τ : ℕ) (positions : Fin τ → ℕ) (signs : Fin τ → Bool) : Fin N → ℤ :=
  let step (c : Fin N → ℤ) (s : Fin τ) : Fin N → ℤ :=
    if hi : N - τ + s < N then
      let i : Fin N := ⟨N - τ + s, hi⟩
      if hj : positions s < N then
        let j : Fin N := ⟨positions s, hj⟩
        Function.update (Function.update c i (c j)) j (if signs s then -1 else 1)
      else c
    else c
  (List.finRange τ).foldl step fun _ => 0

/-- `shuffle`'s array after only the first `n` of the `τ` steps: `n = τ` is the
full shuffle. -/
-- spec-side
def shuffleAt (N τ : ℕ) (positions : Fin τ → ℕ) (signs : Fin τ → Bool) (n : ℕ) : Fin N → ℤ :=
  let step (c : Fin N → ℤ) (s : Fin τ) : Fin N → ℤ :=
    if hi : N - τ + s < N then
      let i : Fin N := ⟨N - τ + s, hi⟩
      if hj : positions s < N then
        let j : Fin N := ⟨positions s, hj⟩
        Function.update (Function.update c i (c j)) j (if signs s then -1 else 1)
      else c
    else c
  ((List.finRange τ).take n).foldl step fun _ => 0

theorem shuffleAt_of_le (N τ : ℕ) (positions : Fin τ → ℕ) (signs : Fin τ → Bool) :
    shuffleAt N τ positions signs τ = shuffle N τ positions signs := by
  unfold shuffleAt shuffle
  rw [List.take_of_length_le (by simp)]

/-- Every entry of the shuffled array is `0`, `1` or `−1`: the array starts at
zero and each step copies an entry or writes a signed unit. -/
theorem shuffle_ternary (N τ : ℕ) (positions : Fin τ → ℕ) (signs : Fin τ → Bool) (k : Fin N) :
    shuffle N τ positions signs k = 0 ∨ shuffle N τ positions signs k = 1 ∨
      shuffle N τ positions signs k = -1 := by
  unfold shuffle
  dsimp only
  have hc : ∀ k : Fin N, (fun _ : Fin N => (0 : ℤ)) k = 0 ∨ (fun _ : Fin N => (0 : ℤ)) k = 1 ∨
      (fun _ : Fin N => (0 : ℤ)) k = -1 := fun _ => Or.inl rfl
  revert hc
  generalize (fun _ : Fin N => (0 : ℤ)) = c
  generalize List.finRange τ = l
  induction l generalizing c with
  | nil => intro hc; exact hc k
  | cons s l ih =>
    intro hc
    rw [List.foldl_cons]
    apply ih
    intro k'
    split_ifs
    · rw [Function.update_apply, Function.update_apply]
      split_ifs <;> first | simp | exact hc _
    · rw [Function.update_apply, Function.update_apply]
      split_ifs <;> first | simp | exact hc _
    · exact hc k'
    · exact hc k'

/-- `shuffleAt`'s recursion: one more step of the shuffle. -/
theorem shuffleAt_succ {N τ : ℕ} (positions : Fin τ → ℕ) (signs : Fin τ → Bool) {n : ℕ}
    (hn : n < τ) (hi : N - τ + n < N) (hj : positions ⟨n, hn⟩ < N) :
    shuffleAt N τ positions signs (n + 1) =
      Function.update (Function.update (shuffleAt N τ positions signs n)
          ⟨N - τ + n, hi⟩ (shuffleAt N τ positions signs n ⟨positions ⟨n, hn⟩, hj⟩))
        ⟨positions ⟨n, hn⟩, hj⟩ (if signs ⟨n, hn⟩ then -1 else 1) := by
  unfold shuffleAt
  rw [List.take_succ_eq_append_getElem (by simpa using hn), List.foldl_append, List.foldl_cons,
    List.foldl_nil]
  have hget : (List.finRange τ)[n]'(by simpa using hn) = ⟨n, hn⟩ := by simp
  rw [hget]
  simp only [dif_pos hi, dif_pos hj]

/-- **`shuffleAt`'s recursion.**  By induction on the processed prefix length
`n`: if some step `s` below `n` targets address `a` (`positions s = a`), the
value at `a` after `n` steps is the sign of the *last* such step (address `a`
is repeatedly overwritten, and only the final write survives); otherwise
address `a` is untouched by any step below `n`, and its value is `0` unless
`a` lies in the live window (`N − τ ≤ a`) and its creation step
`a − (N − τ)` has already run (`< n`), in which case the value equals
whatever the creation step moved in from address `positions (a − (N − τ))`,
read at that earlier prefix length.  `hpos` is the sampler's own bound
(`SelectFirstTau`'s conclusion), needed so that a step below its own creation
step cannot reach a live address before it exists. -/
theorem shuffleAt_step_eq {N τ : ℕ} {positions : Fin τ → ℕ} {signs : Fin τ → Bool}
    (hτ : τ ≤ N) (hpos : ∀ s : Fin τ, positions s ≤ N - τ + (s : ℕ))
    (hposLt : ∀ s : Fin τ, positions s < N) :
    ∀ n, n ≤ τ →
      (∀ a : Fin N, ∀ s : Fin τ, (s : ℕ) < n → positions s = (a : ℕ) →
          (∀ s' : Fin τ, (s' : ℕ) < n → positions s' = (a : ℕ) → (s' : ℕ) ≤ (s : ℕ)) →
          shuffleAt N τ positions signs n a = if signs s then (-1 : ℤ) else 1)
      ∧ (∀ a : Fin N, (∀ s : Fin τ, (s : ℕ) < n → positions s ≠ (a : ℕ)) →
          shuffleAt N τ positions signs n a =
            if h : N - τ ≤ (a : ℕ) ∧ (a : ℕ) - (N - τ) < n then
              shuffleAt N τ positions signs ((a : ℕ) - (N - τ))
                ⟨positions ⟨(a : ℕ) - (N - τ), by omega⟩, hposLt _⟩
            else 0) := by
  intro n
  induction n with
  | zero =>
    intro _
    refine ⟨fun a s hs _ _ => by omega, fun a _ => ?_⟩
    rw [dif_neg (by omega)]
    simp [shuffleAt]
  | succ n ih =>
    intro hn1
    have hn : n ≤ τ := by omega
    have hn' : n < τ := by omega
    obtain ⟨ihLast, ihNone⟩ := ih hn
    set sn : Fin τ := ⟨n, hn'⟩ with hsndef
    have hi : N - τ + (n : ℕ) < N := by omega
    have hj : positions sn < N := hposLt sn
    set i : Fin N := ⟨N - τ + n, hi⟩ with hidef
    set j : Fin N := ⟨positions sn, hj⟩ with hjdef
    have hsnval : (sn : ℕ) = n := rfl
    have hival : (i : ℕ) = N - τ + n := rfl
    have hjval : (j : ℕ) = positions sn := rfl
    have hstep : shuffleAt N τ positions signs (n + 1)
        = Function.update (Function.update (shuffleAt N τ positions signs n) i
            (shuffleAt N τ positions signs n j)) j (if signs sn then (-1 : ℤ) else 1) := by
      unfold shuffleAt
      have hlen : n < (List.finRange τ).length := by simpa using hn'
      rw [List.take_succ_eq_append_getElem hlen, List.foldl_append, List.foldl_cons, List.foldl_nil]
      have hget : (List.finRange τ)[n] = sn := by simp [List.getElem_finRange, hsndef]
      rw [hget]
      simp only [hidef, hjdef, hsndef]
      rw [dif_pos hi, dif_pos hj]
    refine ⟨?_, ?_⟩
    · intro a s hs hsa hmax
      by_cases hsn : (s : ℕ) = n
      · have hseq : s = sn := Fin.ext hsn
        have hsaj : (a : Fin N) = j := by
          apply Fin.ext
          rw [hjval, ← hsa, hseq]
        rw [hstep, ← hsaj, Function.update_self, hseq]
      · have hslt : (s : ℕ) < n := by omega
        have hane_pos : positions sn ≠ (a : ℕ) := by
          intro hcontra
          have := hmax sn (by omega) hcontra
          omega
        have haj : (a : Fin N) ≠ j := by
          intro hcontra
          apply hane_pos
          rw [← hjval, ← hcontra]
        have hle : (a : ℕ) ≤ N - τ + (s : ℕ) := by rw [← hsa]; exact hpos s
        have hai : (a : Fin N) ≠ i := by
          intro hcontra
          rw [← hival, ← hcontra] at hi
          omega
        rw [hstep, Function.update_of_ne haj, Function.update_of_ne hai]
        exact ihLast a s hslt hsa (fun s' hs' hs'a => hmax s' (by omega) hs'a)
    · intro a hnone
      have hnej : positions sn ≠ (a : ℕ) := hnone sn (by omega)
      have haj : (a : Fin N) ≠ j := by
        intro hcontra
        apply hnej
        rw [← hjval, ← hcontra]
      by_cases hai : (a : Fin N) = i
      · have haival : (a : ℕ) = N - τ + n := by rw [hai]
        rw [hstep, Function.update_of_ne haj, Function.update_apply, if_pos hai]
        have hcond1 : N - τ ≤ (a : ℕ) ∧ (a : ℕ) - (N - τ) < n + 1 := by omega
        rw [dif_pos hcond1]
        have hnEq : (a : ℕ) - (N - τ) = n := by omega
        have hidxEq : (⟨(a : ℕ) - (N - τ), by omega⟩ : Fin τ) = sn := by
          apply Fin.ext
          simp only [Fin.val_mk]
          omega
        have hFinEq : (⟨positions ⟨(a : ℕ) - (N - τ), by omega⟩, hposLt _⟩ : Fin N) = j := by
          apply Fin.ext
          simp only [Fin.val_mk]
          rw [hjval, hidxEq]
        rw [hFinEq, hnEq]
      · have hai' : (a : ℕ) ≠ N - τ + n := by
          intro hcontra
          apply hai
          apply Fin.ext
          rw [hival, hcontra]
        rw [hstep, Function.update_of_ne haj, Function.update_of_ne hai]
        rw [ihNone a (fun s' hs' => hnone s' (by omega))]
        by_cases hcond : N - τ ≤ (a : ℕ) ∧ (a : ℕ) - (N - τ) < n
        · rw [dif_pos hcond, dif_pos (show N - τ ≤ (a:ℕ) ∧ (a:ℕ) - (N-τ) < n + 1 by omega)]
        · rw [dif_neg hcond]
          rw [dif_neg (show ¬ (N - τ ≤ (a:ℕ) ∧ (a:ℕ) - (N-τ) < n + 1) by omega)]

/-- The closed form when address `a` is replaced by some checked step below `n`:
the value is the sign of the last (largest-indexed) such step. -/
theorem shuffleAt_of_last {N τ : ℕ} {positions : Fin τ → ℕ} {signs : Fin τ → Bool}
    (hτ : τ ≤ N) (hpos : ∀ s : Fin τ, positions s ≤ N - τ + (s : ℕ))
    (hposLt : ∀ s : Fin τ, positions s < N)
    {n : ℕ} (hn : n ≤ τ) (a : Fin N) (s : Fin τ) (hs : (s : ℕ) < n) (hsa : positions s = (a : ℕ))
    (hmax : ∀ s' : Fin τ, (s' : ℕ) < n → positions s' = (a : ℕ) → (s' : ℕ) ≤ (s : ℕ)) :
    shuffleAt N τ positions signs n a = if signs s then (-1 : ℤ) else 1 :=
  (shuffleAt_step_eq hτ hpos hposLt n hn).1 a s hs hsa hmax

/-- The recursive/zero form when no checked step below `n` replaces address
`a`. -/
theorem shuffleAt_of_none {N τ : ℕ} {positions : Fin τ → ℕ} {signs : Fin τ → Bool}
    (hτ : τ ≤ N) (hpos : ∀ s : Fin τ, positions s ≤ N - τ + (s : ℕ))
    (hposLt : ∀ s : Fin τ, positions s < N)
    {n : ℕ} (hn : n ≤ τ) (a : Fin N) (hnone : ∀ s : Fin τ, (s : ℕ) < n → positions s ≠ (a : ℕ)) :
    shuffleAt N τ positions signs n a =
      if h : N - τ ≤ (a : ℕ) ∧ (a : ℕ) - (N - τ) < n then
        shuffleAt N τ positions signs ((a : ℕ) - (N - τ))
          ⟨positions ⟨(a : ℕ) - (N - τ), by omega⟩, hposLt _⟩
      else 0 :=
  (shuffleAt_step_eq hτ hpos hposLt n hn).2 a hnone

/-- The ternary encoding of a coefficient in `{−1, 0, 1}`. -/
-- spec-side
def encode (Θ : Theta K) (z : ℤ) : K := if z = 0 then 0 else if z = 1 then 1 else Θ.θ

/-! ### The fingerprint bridge -/

/-- Records as address/value/origin triples, before packing at `δ_enc`; matches
`writes`. -/
def writesTriples (F : SelectionField K S) (Θ : Theta K) (wit : Wit K N τ) : List (K × K × K) :=
  ((List.range (N - τ)).map fun k => (F.embed k, (0 : K), (0 : K)))
  ++ (List.finRange τ).flatMap fun s =>
      [(F.embedBits (by decide) (wit.positions s), unit Θ (wit.signs s), F.embed (s + 1)),
       (F.embed (N - τ + s), (wit.read s).value, F.embedBits (by decide) (wit.read s).origin)]

/-- Records as address/value/origin triples, before packing at `δ_enc`; matches
`reads`. -/
def readsTriples (F : SelectionField K S) (wit : Wit K N τ) : List (K × K × K) :=
  ((List.finRange τ).map fun s =>
      (F.embedBits (by decide) (wit.positions s), (wit.read s).value, F.embedBits (by decide) (wit.read s).origin))
  ++ (List.finRange N).map fun (k : Fin N) => (F.embed k, wit.cEnc k, wit.finalOrigin k)

/-! ### Soundness -/

/-- The signs as Booleans, under Booleanity. -/
-- spec-side
def signBools (wit : Wit K N τ) (s : Fin τ) : Bool := decide (wit.signs s = 1)

/-! #### Soundness helpers

Outside the bad event of the fingerprint the record triples of the reads and the writes agree as
multisets.  Restricting that equality to one address (`Multiset.filter` on the address component)
and applying `GordieHowe.OfflineMemory.chronological` there recovers, for that address, its final read
(`wit.cEnc`) and, for each step replacing it, the read immediately before that step:
`wit_chron`, then `wit_last_eq` and `wit_pred_eq`.  `wit_cEnc_eq_shuffle` then identifies the
final cells with the reference shuffle by strong induction on the address. -/

/-- A total inverse to `SelectionField.embed`, agreeing with it on the range
`< 2 ^ falconSampleBits` it is injective on (`embed_injOn`).  Used only to
give a raw field element (the final read's origin, at one address, which the
circuit never decomposes into bits) a natural-number label for
`GordieHowe.OfflineMemory.chronological`; its behaviour off that range is never
used. -/
-- spec-side
noncomputable def originOf (F : SelectionField K S) : K → ℕ :=
  Function.invFunOn F.embed (Set.Iio (2 ^ falconSampleBits))

theorem originOf_embed (F : SelectionField K S) {v : ℕ} (hv : v < 2 ^ falconSampleBits) :
    originOf F (F.embed v) = v :=
  F.embed_injOn.leftInvOn_invFunOn (Set.mem_Iio.mpr hv)

/-- **The origin check holds**: every read origin is six bits and lies below its step,
`origin_s < s + 1`. -/
structure OriginsOk (wit : Wit K N τ) : Prop where
  bool : ∀ s, Bits.AllBool (wit.read s).origin
  lt : ∀ s : Fin τ, Bits.natOfBits (wit.read s).origin < (s : ℕ) + 1

/-- The steps replacing address `a` (`positions[s] = a`). -/
-- spec-side
def replSet (wit : Wit K N τ) (a : ℕ) : Finset (Fin τ) :=
  Finset.univ.filter (fun s => Bits.natOfBits (wit.positions s) = a)

/-- The step that creates address `a` when it lies in the live window
(`N − τ ≤ a`): a named function of the case hypothesis, so every use of
`creationVal`/`creationLbl` at the same `a` refers to the same term. -/
-- spec-side
def creationStep (hτ : τ ≤ N) (a : ℕ) (ha : a < N) (hnlt : ¬ a < N - τ) : Fin τ :=
  ⟨a - (N - τ), by omega⟩

theorem creationStep_val (hτ : τ ≤ N) (a : ℕ) (ha : a < N) (hnlt : ¬ a < N - τ) :
    ((creationStep hτ a ha hnlt : Fin τ) : ℕ) = a - (N - τ) := rfl

/-- The value written at address `a`'s creation: `0` below the live window
(the gadget's explicit zero write), else the value the accepting witness
claims for the step moving a value in. -/
-- spec-side
def creationVal (wit : Wit K N τ) (hτ : τ ≤ N) (a : ℕ) (ha : a < N) : K :=
  if h : a < N - τ then 0 else (wit.read (creationStep hτ a ha h)).value

/-- The creation write's origin label: `0` below the live window, else the
natural the source read's origin bits denote. -/
-- spec-side
def creationLbl (wit : Wit K N τ) (hτ : τ ≤ N) (a : ℕ) (ha : a < N) : ℕ :=
  if h : a < N - τ then 0 else Bits.natOfBits (wit.read (creationStep hτ a ha h)).origin

/-- The per-address write chronology: the creation, then each replacement in
increasing step order (`Finset.orderEmbOfFin`), each entry labelled by a
natural via `originOf` (always an embedding, so `originOf_embed` reads off the
natural). -/
-- spec-side
noncomputable def chronW (F : SelectionField K S) (Θ : Theta K) (wit : Wit K N τ) (hτ : τ ≤ N)
    (a : ℕ) (ha : a < N) : Fin ((replSet wit a).card + 1) → K × ℕ :=
  Fin.cons (creationVal wit hτ a ha, originOf F (F.embed (creationLbl wit hτ a ha)))
    (fun i => (unit Θ (wit.signs ((replSet wit a).orderEmbOfFin rfl i)),
                originOf F (F.embed (((replSet wit a).orderEmbOfFin rfl i : ℕ) + 1))))

/-- The per-address read chronology: the claimed read before each
replacement, then the final read. -/
-- spec-side
noncomputable def chronR (F : SelectionField K S) (wit : Wit K N τ) (a : ℕ) (ha : a < N) :
    Fin ((replSet wit a).card + 1) → K × ℕ :=
  Fin.lastCases (wit.cEnc ⟨a, ha⟩, originOf F (wit.finalOrigin ⟨a, ha⟩))
    (fun i => ((wit.read ((replSet wit a).orderEmbOfFin rfl i)).value,
                Bits.natOfBits (wit.read ((replSet wit a).orderEmbOfFin rfl i)).origin))

theorem filter_eq_val_range {m v : ℕ} (hv : v < m) :
    (Multiset.filter (fun k => k = v) (↑(List.range m) : Multiset ℕ)) = {v} := by
  apply Multiset.ext.mpr
  intro b
  rw [Multiset.count_filter]
  have hmem : v ∈ (↑(List.range m) : Multiset ℕ) := by simp [hv]
  have hnodup : (↑(List.range m) : Multiset ℕ).Nodup := by
    rw [Multiset.coe_nodup]; exact List.nodup_range
  by_cases hb : b = v
  · subst hb
    have hcnt : Multiset.count b (↑(List.range m) : Multiset ℕ) = 1 :=
      Multiset.count_eq_one_of_mem hnodup hmem
    simp [hcnt]
  · simp [hb]

theorem filter_eq_val_range_of_not_lt {m v : ℕ} (hv : ¬ v < m) :
    (Multiset.filter (fun k => k = v) (↑(List.range m) : Multiset ℕ)) = 0 := by
  apply Multiset.ext.mpr
  intro b
  rw [Multiset.count_filter]
  by_cases hb : b = v
  · subst hb
    have hcnt : Multiset.count b (↑(List.range m) : Multiset ℕ) = 0 := by
      rw [Multiset.count_eq_zero]
      simp only [Multiset.mem_coe, List.mem_range]
      omega
    simp [hcnt]
  · simp [hb]

theorem filter_val_eq_finRange {n v : ℕ} (hv : v < n) :
    (Multiset.filter (fun s : Fin n => (s : ℕ) = v) (↑(List.finRange n) : Multiset (Fin n)))
      = {(⟨v, hv⟩ : Fin n)} := by
  have huniv : (↑(List.finRange n) : Multiset (Fin n)) = (Finset.univ : Finset (Fin n)).val := rfl
  rw [huniv]
  apply Multiset.ext.mpr
  intro b
  rw [Multiset.count_filter]
  have hmemb : b ∈ (Finset.univ : Finset (Fin n)).val := Finset.mem_def.mp (Finset.mem_univ _)
  have hcntb : Multiset.count b (Finset.univ : Finset (Fin n)).val = 1 :=
    Multiset.count_eq_one_of_mem (Finset.univ : Finset (Fin n)).nodup hmemb
  by_cases hb : (b : ℕ) = v
  · have hbeq : b = (⟨v, hv⟩ : Fin n) := Fin.ext hb
    simp [hbeq, hcntb]
  · have hne : b ≠ (⟨v, hv⟩ : Fin n) := by intro hh; exact hb (by rw [hh])
    simp [hb, hne]

theorem multiset_flatMap_pair {A B : Type*} (l : List A) (f g : A → B) :
    (↑(l.flatMap (fun s => [f s, g s])) : Multiset B) = ↑(l.map f) + ↑(l.map g) := by
  induction l with
  | nil => simp
  | cons x xs ih =>
    show (↑(f x :: g x :: xs.flatMap (fun s => [f s, g s])) : Multiset B)
      = ↑(f x :: xs.map f) + ↑(g x :: xs.map g)
    rw [← Multiset.cons_coe, ← Multiset.cons_coe, ← Multiset.cons_coe, ← Multiset.cons_coe, ih]
    rw [Multiset.cons_add, Multiset.add_cons]

/-- The multiset image of a Finset under `orderEmbOfFin`'s enumeration is the
Finset's own multiset. -/
theorem coe_ofFn_orderEmbOfFin {n : ℕ} (S : Finset (Fin τ)) (h : S.card = n) :
    (↑((List.finRange n).map (S.orderEmbOfFin h)) : Multiset (Fin τ)) = S.val := by
  have hmap := Finset.map_orderEmbOfFin_univ S h
  have hval := congrArg Finset.val hmap
  simpa [Finset.map_val, Multiset.map_coe] using hval

/-- **The per-address chronological argument.**  Given acceptance, the
sampler's origin and position bounds, and the fingerprint's non-bad branch
(the record triple multisets agree, `hkey`), every entry of address `a`'s
read chronology equals the corresponding entry of its write chronology:
`GordieHowe.OfflineMemory.chronological` applied to this one address, with
`Finset.orderEmbOfFin` giving the replacement steps' increasing enumeration. -/
theorem wit_chron [CharP K 2] {F : SelectionField K S} {Θ : Theta K} {wit : Wit K N τ}
    (hτ : τ ≤ N) (hN : N ≤ 256) (hτbits : τ < 64)
    (hpos : ∀ s : Fin τ, Bits.natOfBits (wit.positions s) ≤ N - τ + s)
    (hbits : ∀ s, Bits.AllBool (wit.positions s))
    (hor : OriginsOk wit)
    (hkey : (↑(writesTriples F Θ wit) : Multiset (K × K × K)) = ↑(readsTriples F wit))
    (a : ℕ) (ha : a < N) :
    ∀ i, chronR F wit a ha i = chronW F Θ wit hτ a ha i := by
  set S := replSet wit a with hSdef
  have hcard : (replSet wit a).card = S.card := rfl
  have horig : ∀ s : Fin τ, Bits.AllBool (wit.read s).origin ∧
      Bits.natOfBits (wit.read s).origin < (s : ℕ) + 1 := fun s => ⟨hor.bool s, hor.lt s⟩
  have hfsb : (2 : ℕ) ^ falconSampleBits = 65536 := by decide
  have hcreation_le : ∀ t0 : Fin τ, Bits.natOfBits (wit.positions t0) = a →
      creationLbl wit hτ a ha ≤ (t0 : ℕ) := by
    intro t0 ht0
    unfold creationLbl
    split_ifs with hlt
    · omega
    · have h1 := (horig (creationStep hτ a ha hlt)).2
      have hval := creationStep_val hτ a ha hlt
      have h2 := hpos t0
      omega
  apply GordieHowe.OfflineMemory.chronological
  · -- hW : StrictMono
    rw [Fin.strictMono_iff_lt_succ]
    intro i
    show (chronW F Θ wit hτ a ha i.castSucc).2 < (chronW F Θ wit hτ a ha i.succ).2
    have htail : ∀ i' : Fin S.card, (chronW F Θ wit hτ a ha i'.succ).2
        = ((S.orderEmbOfFin rfl i' : ℕ) + 1) := by
      intro i'
      show originOf F (F.embed ((S.orderEmbOfFin rfl i' : ℕ) + 1)) = _
      have hlt65536 : (S.orderEmbOfFin rfl i' : ℕ) + 1 < 65536 := by
        have := (S.orderEmbOfFin rfl i').isLt; omega
      rw [originOf_embed F (hfsb ▸ hlt65536)]
    rw [htail i]
    by_cases hi0 : (i : ℕ) = 0
    · have hcast0 : i.castSucc = (0 : Fin (S.card + 1)) := Fin.ext (by simpa using hi0)
      rw [hcast0]
      show originOf F (F.embed (creationLbl wit hτ a ha)) < _
      have hlt65536 : creationLbl wit hτ a ha < 65536 := by
        unfold creationLbl
        split_ifs with hlt
        · omega
        · have := Bits.natOfBits_lt (wit.read (creationStep hτ a ha hlt)).origin
          omega
      rw [originOf_embed F (hfsb ▸ hlt65536)]
      have hmem : (S.orderEmbOfFin rfl i) ∈ S := S.orderEmbOfFin_mem rfl i
      have hSmem : Bits.natOfBits (wit.positions (S.orderEmbOfFin rfl i)) = a :=
        (Finset.mem_filter.mp hmem).2
      have := hcreation_le (S.orderEmbOfFin rfl i) hSmem
      omega
    · have hilt := i.isLt
      obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hi0
      have hkval : k < S.card := by omega
      set j : Fin S.card := ⟨k, hkval⟩ with hjdef
      have hjval : (j : ℕ) = k := rfl
      have hjsucc : j.succ = i.castSucc := Fin.ext (by show k + 1 = (i : ℕ); omega)
      rw [← hjsucc, htail j]
      have hmono : (S.orderEmbOfFin rfl j : ℕ) < (S.orderEmbOfFin rfl i : ℕ) :=
        (S.orderEmbOfFin rfl).strictMono (by omega : j < i)
      omega
  · -- hperm
    have hSval : S.val = Multiset.filter (fun s : Fin τ => Bits.natOfBits (wit.positions s) = a)
        (↑(List.finRange τ) : Multiset (Fin τ)) := rfl
    have hembed_lt : ∀ v : ℕ, v < N → v < 2 ^ falconSampleBits := fun v hv => by omega
    -- The address-filtered write triples: the creation, plus one replacement
    -- entry per step in `S`.
    have hfilterW : Multiset.filter (fun t : K × K × K => t.1 = F.embed a)
        (↑(writesTriples F Θ wit) : Multiset (K × K × K))
      = {(F.embed a, creationVal wit hτ a ha, F.embed (creationLbl wit hτ a ha))}
        + Multiset.map (fun s : Fin τ => (F.embed a, unit Θ (wit.signs s), F.embed ((s : ℕ) + 1)))
            S.val := by
      have hsplit : (↑(writesTriples F Θ wit) : Multiset (K × K × K))
          = ↑((List.range (N - τ)).map (fun k => (F.embed k, (0 : K), (0 : K))))
            + ↑((List.finRange τ).map (fun s : Fin τ =>
                  (F.embedBits (by decide) (wit.positions s), unit Θ (wit.signs s),
                    F.embed ((s : ℕ) + 1))))
            + ↑((List.finRange τ).map (fun s : Fin τ =>
                  (F.embed (N - τ + (s : ℕ)), (wit.read s).value,
                    F.embedBits (by decide) (wit.read s).origin))) := by
        unfold writesTriples
        rw [← Multiset.coe_add, multiset_flatMap_pair, add_assoc]
      rw [hsplit, Multiset.filter_add, Multiset.filter_add]
      have hinit : Multiset.filter (fun t : K × K × K => t.1 = F.embed a)
          (↑((List.range (N - τ)).map (fun k => (F.embed k, (0 : K), (0 : K))))
            : Multiset (K × K × K))
        = if hlt : a < N - τ then ({(F.embed a, (0 : K), (0 : K))} : Multiset (K × K × K)) else 0 := by
        show Multiset.filter (fun t : K × K × K => t.1 = F.embed a)
            (Multiset.map (fun k => (F.embed k, (0 : K), (0 : K))) (↑(List.range (N - τ)) : Multiset ℕ))
          = _
        rw [Multiset.filter_map]
        simp only [Function.comp]
        have hcongr : Multiset.filter
              (fun k => (F.embed k, (0 : K), (0 : K)).1 = F.embed a)
              (↑(List.range (N - τ)) : Multiset ℕ)
            = Multiset.filter (fun k => k = a) (↑(List.range (N - τ)) : Multiset ℕ) := by
          apply Multiset.filter_congr
          intro k hk
          simp only [Multiset.mem_coe, List.mem_range] at hk
          constructor
          · intro he; exact F.embed_injOn (hembed_lt k (by omega)) (hembed_lt a ha) he
          · intro he; rw [he]
        rw [hcongr]
        split_ifs with hlt
        · rw [filter_eq_val_range hlt]; simp
        · rw [filter_eq_val_range_of_not_lt hlt]; simp
      have hrepl : Multiset.filter (fun t : K × K × K => t.1 = F.embed a)
          (↑((List.finRange τ).map (fun s : Fin τ =>
                (F.embedBits (by decide) (wit.positions s), unit Θ (wit.signs s),
                  F.embed ((s : ℕ) + 1)))) : Multiset (K × K × K))
        = Multiset.map (fun s : Fin τ => (F.embed a, unit Θ (wit.signs s), F.embed ((s : ℕ) + 1)))
            S.val := by
        show Multiset.filter (fun t : K × K × K => t.1 = F.embed a)
            (Multiset.map (fun s : Fin τ => (F.embedBits (by decide) (wit.positions s),
                  unit Θ (wit.signs s), F.embed ((s : ℕ) + 1)))
              (↑(List.finRange τ) : Multiset (Fin τ)))
          = _
        rw [Multiset.filter_map]
        simp only [Function.comp]
        have hcongr : Multiset.filter
              (fun s : Fin τ => (F.embedBits (by decide) (wit.positions s),
                    unit Θ (wit.signs s), F.embed ((s : ℕ) + 1)).1 = F.embed a)
              (↑(List.finRange τ) : Multiset (Fin τ))
            = Multiset.filter (fun s : Fin τ => Bits.natOfBits (wit.positions s) = a)
                (↑(List.finRange τ) : Multiset (Fin τ)) := by
          apply Multiset.filter_congr
          intro s _
          rw [F.embedBits_eq (by decide) (hbits s)]
          constructor
          · intro he
            exact F.embed_injOn (hembed_lt _ (by have := hpos s; have := s.isLt; omega))
              (hembed_lt a ha) he
          · intro he; rw [he]
        rw [hcongr, ← hSval]
        apply Multiset.map_congr rfl
        intro s hs
        have hSmem : Bits.natOfBits (wit.positions s) = a := by
          rw [hSval] at hs; exact (Multiset.mem_filter.mp hs).2
        rw [F.embedBits_eq (by decide) (hbits s), hSmem]
      have hmove : Multiset.filter (fun t : K × K × K => t.1 = F.embed a)
          (↑((List.finRange τ).map (fun s : Fin τ =>
                (F.embed (N - τ + (s : ℕ)), (wit.read s).value,
                  F.embedBits (by decide) (wit.read s).origin))) : Multiset (K × K × K))
        = if hlt : a < N - τ then 0
          else ({(F.embed a, (wit.read (creationStep hτ a ha hlt)).value,
              F.embedBits (by decide) (wit.read (creationStep hτ a ha hlt)).origin)}
            : Multiset (K × K × K)) := by
        show Multiset.filter (fun t : K × K × K => t.1 = F.embed a)
            (Multiset.map (fun s : Fin τ => (F.embed (N - τ + (s : ℕ)), (wit.read s).value,
                  F.embedBits (by decide) (wit.read s).origin))
              (↑(List.finRange τ) : Multiset (Fin τ)))
          = _
        rw [Multiset.filter_map]
        simp only [Function.comp]
        have hinner : Multiset.filter (fun s : Fin τ => (F.embed (N - τ + (s : ℕ)),
                (wit.read s).value, F.embedBits (by decide) (wit.read s).origin).1 = F.embed a)
              (↑(List.finRange τ) : Multiset (Fin τ))
            = if hlt : a < N - τ then 0 else ({creationStep hτ a ha hlt} : Multiset (Fin τ)) := by
          split_ifs with hlt
          · apply Multiset.ext.mpr
            intro s
            rw [Multiset.count_filter]
            split_ifs with hseq
            · exfalso
              have hxeq' : F.embed (N - τ + (s : ℕ)) = F.embed a := hseq
              have := F.embed_injOn (hembed_lt (N - τ + (s : ℕ)) (by have := s.isLt; omega))
                (hembed_lt a ha) hxeq'
              omega
            · rfl
          · have hlt' : a - (N - τ) < τ := by omega
            apply Multiset.ext.mpr
            intro s
            rw [Multiset.count_filter]
            split_ifs with hseq
            · have hsval : (s : ℕ) = a - (N - τ) := by
                have := F.embed_injOn (hembed_lt (N - τ + (s : ℕ)) (by have := s.isLt; omega))
                  (hembed_lt a ha) hseq
                omega
              have hseqcs : s = creationStep hτ a ha hlt := by
                apply Fin.ext; rw [hsval, creationStep_val]
              subst hseqcs
              have huniv : (↑(List.finRange τ) : Multiset (Fin τ))
                  = (Finset.univ : Finset (Fin τ)).val := rfl
              rw [huniv, Multiset.count_eq_one_of_mem (Finset.univ : Finset (Fin τ)).nodup
                (Finset.mem_def.mp (Finset.mem_univ _))]
              simp
            · symm
              rw [Multiset.count_eq_zero]
              intro hmem
              simp only [Multiset.mem_singleton] at hmem
              apply hseq
              subst hmem
              have hval : ((creationStep hτ a ha hlt : Fin τ) : ℕ) = a - (N - τ) :=
                creationStep_val hτ a ha hlt
              have heq : N - τ + ((creationStep hτ a ha hlt : Fin τ) : ℕ) = a := by omega
              rw [heq]
        rw [hinner]
        split_ifs with hlt
        · simp
        · rw [Multiset.map_singleton]
          congr 2
          have hval : ((creationStep hτ a ha hlt : Fin τ) : ℕ) = a - (N - τ) :=
            creationStep_val hτ a ha hlt
          have heq : N - τ + ((creationStep hτ a ha hlt : Fin τ) : ℕ) = a := by omega
          rw [heq]
      rw [hinit, hrepl, hmove]
      split_ifs with hlt
      · have hcv : creationVal wit hτ a ha = 0 := by unfold creationVal; rw [dif_pos hlt]
        have hcl : F.embed (creationLbl wit hτ a ha) = (0 : K) := by
          unfold creationLbl
          rw [dif_pos hlt]
          simp [SelectionField.embed, selectionEmbed]
        rw [hcv, hcl, add_zero]
      · have hcv : creationVal wit hτ a ha = (wit.read (creationStep hτ a ha hlt)).value := by
          unfold creationVal; rw [dif_neg hlt]
        have hcl : F.embed (creationLbl wit hτ a ha)
            = F.embedBits (by decide) (wit.read (creationStep hτ a ha hlt)).origin := by
          unfold creationLbl
          rw [dif_neg hlt, F.embedBits_eq (by decide) (horig (creationStep hτ a ha hlt)).1]
        rw [hcv, hcl, zero_add, add_comm]
    have hfilterR : Multiset.filter (fun t : K × K × K => t.1 = F.embed a)
        (↑(readsTriples F wit) : Multiset (K × K × K))
      = Multiset.map (fun s : Fin τ => (F.embed a, (wit.read s).value,
            F.embedBits (by decide) (wit.read s).origin)) S.val
        + {(F.embed a, wit.cEnc ⟨a, ha⟩, wit.finalOrigin ⟨a, ha⟩)} := by
      have hsplit : (↑(readsTriples F wit) : Multiset (K × K × K))
          = ↑((List.finRange τ).map (fun s : Fin τ =>
                (F.embedBits (by decide) (wit.positions s), (wit.read s).value,
                  F.embedBits (by decide) (wit.read s).origin)))
            + ↑((List.finRange N).map (fun k : Fin N =>
                  (F.embed k, wit.cEnc k, wit.finalOrigin k))) := by
        unfold readsTriples
        rw [← Multiset.coe_add]
      rw [hsplit, Multiset.filter_add]
      have hread : Multiset.filter (fun t : K × K × K => t.1 = F.embed a)
          (↑((List.finRange τ).map (fun s : Fin τ =>
                (F.embedBits (by decide) (wit.positions s), (wit.read s).value,
                  F.embedBits (by decide) (wit.read s).origin))) : Multiset (K × K × K))
        = Multiset.map (fun s : Fin τ => (F.embed a, (wit.read s).value,
              F.embedBits (by decide) (wit.read s).origin)) S.val := by
        show Multiset.filter (fun t : K × K × K => t.1 = F.embed a)
            (Multiset.map (fun s : Fin τ => (F.embedBits (by decide) (wit.positions s),
                  (wit.read s).value, F.embedBits (by decide) (wit.read s).origin))
              (↑(List.finRange τ) : Multiset (Fin τ)))
          = _
        rw [Multiset.filter_map]
        simp only [Function.comp]
        have hcongr : Multiset.filter
              (fun s : Fin τ => (F.embedBits (by decide) (wit.positions s),
                    (wit.read s).value, F.embedBits (by decide) (wit.read s).origin).1 = F.embed a)
              (↑(List.finRange τ) : Multiset (Fin τ))
            = Multiset.filter (fun s : Fin τ => Bits.natOfBits (wit.positions s) = a)
                (↑(List.finRange τ) : Multiset (Fin τ)) := by
          apply Multiset.filter_congr
          intro s _
          rw [F.embedBits_eq (by decide) (hbits s)]
          constructor
          · intro he
            exact F.embed_injOn (hembed_lt _ (by have := hpos s; have := s.isLt; omega))
              (hembed_lt a ha) he
          · intro he; rw [he]
        rw [hcongr, ← hSval]
        apply Multiset.map_congr rfl
        intro s hs
        have hSmem : Bits.natOfBits (wit.positions s) = a := by
          rw [hSval] at hs; exact (Multiset.mem_filter.mp hs).2
        rw [F.embedBits_eq (by decide) (hbits s), hSmem]
      have hfinal : Multiset.filter (fun t : K × K × K => t.1 = F.embed a)
          (↑((List.finRange N).map (fun k : Fin N => (F.embed k, wit.cEnc k, wit.finalOrigin k)))
            : Multiset (K × K × K))
        = {(F.embed a, wit.cEnc ⟨a, ha⟩, wit.finalOrigin ⟨a, ha⟩)} := by
        show Multiset.filter (fun t : K × K × K => t.1 = F.embed a)
            (Multiset.map (fun k : Fin N => (F.embed k, wit.cEnc k, wit.finalOrigin k))
              (↑(List.finRange N) : Multiset (Fin N)))
          = _
        rw [Multiset.filter_map]
        simp only [Function.comp]
        have hcongr : Multiset.filter
              (fun k : Fin N => (F.embed k, wit.cEnc k, wit.finalOrigin k).1 = F.embed a)
              (↑(List.finRange N) : Multiset (Fin N))
            = Multiset.filter (fun k : Fin N => (k : ℕ) = a)
                (↑(List.finRange N) : Multiset (Fin N)) := by
          apply Multiset.filter_congr
          intro k _
          constructor
          · intro he; exact F.embed_injOn (hembed_lt k k.isLt) (hembed_lt a ha) he
          · intro he; rw [he]
        rw [hcongr, filter_val_eq_finRange ha]
        rfl
      rw [hread, hfinal]
    have hofFnW : (↑(List.ofFn (chronW F Θ wit hτ a ha)) : Multiset (K × ℕ))
        = {(creationVal wit hτ a ha, originOf F (F.embed (creationLbl wit hτ a ha)))}
          + Multiset.map (fun s : Fin τ => (unit Θ (wit.signs s), originOf F (F.embed ((s : ℕ) + 1))))
              S.val := by
      rw [List.ofFn_succ]
      have hbase : chronW F Θ wit hτ a ha 0
          = (creationVal wit hτ a ha, originOf F (F.embed (creationLbl wit hτ a ha))) := rfl
      have htaileq : (fun i : Fin S.card => chronW F Θ wit hτ a ha i.succ)
          = fun i : Fin S.card => (unit Θ (wit.signs (S.orderEmbOfFin rfl i)),
              originOf F (F.embed ((S.orderEmbOfFin rfl i : ℕ) + 1))) := rfl
      rw [hbase, htaileq, ← Multiset.cons_coe, Multiset.singleton_add]
      congr 1
      rw [List.ofFn_eq_map, ← coe_ofFn_orderEmbOfFin S rfl, Multiset.map_coe]
      congr 1
      rw [List.map_map]
      rfl
    have hofFnR : (↑(List.ofFn (chronR F wit a ha)) : Multiset (K × ℕ))
        = Multiset.map (fun s : Fin τ => ((wit.read s).value, Bits.natOfBits (wit.read s).origin))
            S.val
          + {(wit.cEnc ⟨a, ha⟩, originOf F (wit.finalOrigin ⟨a, ha⟩))} := by
      rw [List.ofFn_succ']
      have hlast : chronR F wit a ha (Fin.last S.card)
          = (wit.cEnc ⟨a, ha⟩, originOf F (wit.finalOrigin ⟨a, ha⟩)) := by
        unfold chronR; rw [Fin.lastCases_last]
      have htaileq : (fun i : Fin S.card => chronR F wit a ha i.castSucc)
          = fun i : Fin S.card => ((wit.read (S.orderEmbOfFin rfl i)).value,
              Bits.natOfBits (wit.read (S.orderEmbOfFin rfl i)).origin) := by
        funext i
        unfold chronR; rw [Fin.lastCases_castSucc]
      rw [hlast, htaileq, List.concat_eq_append, ← Multiset.coe_add, Multiset.coe_singleton]
      congr 1
      rw [List.ofFn_eq_map, ← coe_ofFn_orderEmbOfFin S rfl, Multiset.map_coe]
      congr 1
      rw [List.map_map]
      rfl
    have hmapkey : Multiset.map (fun t : K × K × K => (t.2.1, originOf F t.2.2))
          (Multiset.filter (fun t => t.1 = F.embed a)
            (↑(writesTriples F Θ wit) : Multiset (K × K × K)))
        = Multiset.map (fun t : K × K × K => (t.2.1, originOf F t.2.2))
          (Multiset.filter (fun t => t.1 = F.embed a)
            (↑(readsTriples F wit) : Multiset (K × K × K))) := by
      rw [hkey]
    rw [hfilterW, hfilterR] at hmapkey
    simp only [Multiset.map_add, Multiset.map_singleton, Multiset.map_map, Function.comp] at hmapkey
    have hconv : ∀ x : Fin τ, originOf F (F.embedBits (by decide) (wit.read x).origin)
        = Bits.natOfBits (wit.read x).origin := by
      intro x
      rw [F.embedBits_eq (by decide) (horig x).1]
      apply originOf_embed
      have := Bits.natOfBits_lt (wit.read x).origin
      omega
    simp only [hconv] at hmapkey
    rw [hofFnW, hofFnR]
    rw [add_comm ({(creationVal wit hτ a ha, originOf F (F.embed (creationLbl wit hτ a ha)))} :
      Multiset (K × ℕ))] at hmapkey ⊢
    exact hmapkey.symm
  · -- horigin
    intro i
    show (chronR F wit a ha i.castSucc).2 < (chronW F Θ wit hτ a ha i.succ).2
    have hR : chronR F wit a ha i.castSucc
        = ((wit.read (S.orderEmbOfFin rfl i)).value,
            Bits.natOfBits (wit.read (S.orderEmbOfFin rfl i)).origin) := by
      unfold chronR
      rw [Fin.lastCases_castSucc]
    have hWv : (chronW F Θ wit hτ a ha i.succ).2
        = originOf F (F.embed ((S.orderEmbOfFin rfl i : ℕ) + 1)) := rfl
    rw [hR, hWv]
    have hlt65536 : (S.orderEmbOfFin rfl i : ℕ) + 1 < 65536 := by
      have := (S.orderEmbOfFin rfl i).isLt; omega
    rw [originOf_embed F (hfsb ▸ hlt65536)]
    exact (horig (S.orderEmbOfFin rfl i)).2

/-- **The last write to an address.**  Either some step replaces the address
and its final value is that step's signed unit, taken at the step of largest
index (`Finset.max'`); or no step does, and its value is the creation
value. -/
theorem wit_last_eq [CharP K 2] {F : SelectionField K S} {Θ : Theta K} {wit : Wit K N τ}
    (hτ : τ ≤ N) (hN : N ≤ 256) (hτbits : τ < 64)
    (hpos : ∀ s : Fin τ, Bits.natOfBits (wit.positions s) ≤ N - τ + s)
    (hbits : ∀ s, Bits.AllBool (wit.positions s))
    (hor : OriginsOk wit)
    (hkey : (↑(writesTriples F Θ wit) : Multiset (K × K × K)) = ↑(readsTriples F wit))
    (a : ℕ) (ha : a < N) :
    (∃ t : Fin τ, Bits.natOfBits (wit.positions t) = a
        ∧ (∀ t' : Fin τ, Bits.natOfBits (wit.positions t') = a → (t' : ℕ) ≤ (t : ℕ))
        ∧ wit.cEnc ⟨a, ha⟩ = unit Θ (wit.signs t))
    ∨ ((∀ t : Fin τ, Bits.natOfBits (wit.positions t) ≠ a)
        ∧ wit.cEnc ⟨a, ha⟩ = creationVal wit hτ a ha) := by
  have hchron := wit_chron hτ hN hτbits hpos hbits hor hkey a ha
  set S := replSet wit a with hSdef
  by_cases hSempty : S.card = 0
  · right
    refine ⟨?_, ?_⟩
    · intro t hcontra
      have hmem : t ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hcontra⟩
      exact absurd hSempty (Finset.card_ne_zero_of_mem hmem)
    · have hlast0 : (Fin.last S.card : Fin (S.card + 1)) = 0 := Fin.ext (by simp [hSempty])
      have hc := hchron (Fin.last S.card)
      rw [hlast0] at hc
      have hRbase : chronR F wit a ha 0
          = (wit.cEnc ⟨a, ha⟩, originOf F (wit.finalOrigin ⟨a, ha⟩)) := by
        unfold chronR
        rw [show (0 : Fin (S.card + 1)) = Fin.last S.card from hlast0.symm, Fin.lastCases_last]
      have hWbase : chronW F Θ wit hτ a ha 0
          = (creationVal wit hτ a ha, originOf F (F.embed (creationLbl wit hτ a ha))) := rfl
      rw [hRbase, hWbase] at hc
      exact (Prod.ext_iff.mp hc).1
  · left
    have hSne : S.Nonempty := Finset.card_ne_zero.mp hSempty
    have hcardpos : 0 < S.card := Finset.card_pos.mpr hSne
    have hklt : S.card - 1 < S.card := by omega
    have hlastform : (Fin.last S.card : Fin (S.card + 1)) = (⟨S.card - 1, hklt⟩ : Fin S.card).succ := by
      apply Fin.ext
      simp only [Fin.val_last, Fin.val_succ, Fin.val_mk]
      omega
    have hc := hchron (Fin.last S.card)
    have hRlast : chronR F wit a ha (Fin.last S.card)
        = (wit.cEnc ⟨a, ha⟩, originOf F (wit.finalOrigin ⟨a, ha⟩)) := by
      unfold chronR; rw [Fin.lastCases_last]
    have hWsucc : chronW F Θ wit hτ a ha ((⟨S.card - 1, hklt⟩ : Fin S.card).succ)
        = (unit Θ (wit.signs (S.orderEmbOfFin rfl ⟨S.card - 1, hklt⟩)),
            originOf F (F.embed ((S.orderEmbOfFin rfl ⟨S.card - 1, hklt⟩ : ℕ) + 1))) := rfl
    rw [hRlast] at hc
    rw [hlastform] at hc
    rw [hWsucc] at hc
    have hmax : S.orderEmbOfFin rfl ⟨S.card - 1, hklt⟩ = S.max' hSne :=
      Finset.orderEmbOfFin_last (h := rfl) hcardpos
    refine ⟨S.max' hSne, ?_, ?_, ?_⟩
    · have hmem := S.max'_mem hSne
      exact (Finset.mem_filter.mp hmem).2
    · intro t' ht'
      have hmem : t' ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_univ _, ht'⟩
      exact S.le_max' t' hmem
    · rw [hmax] at hc
      exact (Prod.ext_iff.mp hc).1

/-- **The read at a step, chronologically.**  The step's claimed read either
matches some strictly earlier step that replaces the same address, taken at
the largest such step (`Finset.max'`); or no earlier step does, and it
matches the address's creation value. -/
theorem wit_pred_eq [CharP K 2] {F : SelectionField K S} {Θ : Theta K} {wit : Wit K N τ}
    (hτ : τ ≤ N) (hN : N ≤ 256) (hτbits : τ < 64)
    (hpos : ∀ s : Fin τ, Bits.natOfBits (wit.positions s) ≤ N - τ + s)
    (hbits : ∀ s, Bits.AllBool (wit.positions s))
    (hor : OriginsOk wit)
    (hkey : (↑(writesTriples F Θ wit) : Multiset (K × K × K)) = ↑(readsTriples F wit))
    (t0 : Fin τ) (hposLt : ∀ s : Fin τ, Bits.natOfBits (wit.positions s) < N) :
    (∃ t' : Fin τ, (t' : ℕ) < (t0 : ℕ)
        ∧ Bits.natOfBits (wit.positions t') = Bits.natOfBits (wit.positions t0)
        ∧ (∀ t'' : Fin τ, (t'' : ℕ) < (t0 : ℕ) →
            Bits.natOfBits (wit.positions t'') = Bits.natOfBits (wit.positions t0) →
            (t'' : ℕ) ≤ (t' : ℕ))
        ∧ (wit.read t0).value = unit Θ (wit.signs t'))
    ∨ ((∀ t' : Fin τ, (t' : ℕ) < (t0 : ℕ) →
          Bits.natOfBits (wit.positions t') ≠ Bits.natOfBits (wit.positions t0))
        ∧ (wit.read t0).value
          = creationVal wit hτ (Bits.natOfBits (wit.positions t0)) (hposLt t0)) := by
  set c := Bits.natOfBits (wit.positions t0) with hcdef
  have hchron := wit_chron hτ hN hτbits hpos hbits hor hkey c (hposLt t0)
  set Sc := replSet wit c with hScdef
  have ht0mem : t0 ∈ Sc := Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩
  set i0 : Fin Sc.card := (Sc.orderIsoOfFin rfl).symm ⟨t0, ht0mem⟩ with hi0def
  have hi0eq : Sc.orderEmbOfFin rfl i0 = t0 := by
    have := (Sc.orderIsoOfFin rfl).apply_symm_apply (⟨t0, ht0mem⟩ : Sc)
    have h2 := congrArg (Subtype.val) this
    rwa [Finset.coe_orderIsoOfFin_apply] at h2
  -- For any `t' ∈ Sc`, its rank compares to `i0` exactly as `t'` compares to `t0`.
  have hrank : ∀ t' : Fin τ, (ht' : t' ∈ Sc) →
      ((Sc.orderIsoOfFin rfl).symm ⟨t', ht'⟩ ≤ i0 ↔ (t' : ℕ) ≤ (t0 : ℕ))
      ∧ ((Sc.orderIsoOfFin rfl).symm ⟨t', ht'⟩ < i0 ↔ (t' : ℕ) < (t0 : ℕ)) := by
    intro t' ht'
    set i' : Fin Sc.card := (Sc.orderIsoOfFin rfl).symm ⟨t', ht'⟩ with hi'def
    have hi'eq : Sc.orderEmbOfFin rfl i' = t' := by
      have := (Sc.orderIsoOfFin rfl).apply_symm_apply (⟨t', ht'⟩ : Sc)
      have h2 := congrArg (Subtype.val) this
      rwa [Finset.coe_orderIsoOfFin_apply] at h2
    constructor
    · rw [← hi0eq, ← hi'eq]
      exact (Sc.orderEmbOfFin rfl).le_iff_le.symm
    · rw [← hi0eq, ← hi'eq]
      exact (Sc.orderEmbOfFin rfl).lt_iff_lt.symm
  by_cases hi0 : (i0 : ℕ) = 0
  · right
    have hcast0 : i0.castSucc = (0 : Fin (Sc.card + 1)) := Fin.ext (by simpa using hi0)
    have hc := hchron i0.castSucc
    rw [hcast0] at hc
    have hRbase : chronR F wit c (hposLt t0) 0
        = ((wit.read t0).value, Bits.natOfBits (wit.read t0).origin) := by
      unfold chronR
      rw [show (0 : Fin (Sc.card + 1)) = i0.castSucc from hcast0.symm, Fin.lastCases_castSucc,
        hi0eq]
    have hWbase : chronW F Θ wit hτ c (hposLt t0) 0
        = (creationVal wit hτ c (hposLt t0), originOf F (F.embed (creationLbl wit hτ c (hposLt t0)))) := rfl
    rw [hRbase, hWbase] at hc
    refine ⟨?_, (Prod.ext_iff.mp hc).1⟩
    intro t' ht' hpos'
    have hSmem : t' ∈ Sc := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hpos'⟩
    have hlt' := ((hrank t' hSmem).2).mpr ht'
    rw [Fin.lt_def, hi0] at hlt'
    omega
  · left
    obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hi0
    have hkval : k < Sc.card := by have := i0.isLt; omega
    set j : Fin Sc.card := ⟨k, hkval⟩ with hjdef
    have hjsucc : j.succ = i0.castSucc := Fin.ext (by show k + 1 = (i0 : ℕ); omega)
    have hc := hchron i0.castSucc
    rw [← hjsucc] at hc
    have hRtail : chronR F wit c (hposLt t0) (i0.castSucc)
        = ((wit.read t0).value, Bits.natOfBits (wit.read t0).origin) := by
      unfold chronR
      rw [Fin.lastCases_castSucc, hi0eq]
    rw [← hjsucc] at hRtail
    have hWsucc : chronW F Θ wit hτ c (hposLt t0) (j.succ)
        = (unit Θ (wit.signs (Sc.orderEmbOfFin rfl j)),
            originOf F (F.embed ((Sc.orderEmbOfFin rfl j : ℕ) + 1))) := rfl
    rw [hRtail, hWsucc] at hc
    have hjlti0 : j < i0 := by
      apply Fin.lt_def.mpr
      simp only [hjdef]
      omega
    refine ⟨Sc.orderEmbOfFin rfl j, ?_, ?_, ?_, (Prod.ext_iff.mp hc).1⟩
    · have := (Sc.orderEmbOfFin rfl).strictMono hjlti0
      rwa [hi0eq] at this
    · have hmem := Sc.orderEmbOfFin_mem rfl j
      exact (Finset.mem_filter.mp hmem).2
    · intro t'' ht'' hpos''
      have hSmem : t'' ∈ Sc := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hpos''⟩
      have hle' := ((hrank t'' hSmem).2).mp
      have hlt0 : (t'' : ℕ) < (t0 : ℕ) := ht''
      have hi''lt : (Sc.orderIsoOfFin rfl).symm ⟨t'', hSmem⟩ < i0 := by
        rw [(hrank t'' hSmem).2]
        exact hlt0
      have hi''lej : (Sc.orderIsoOfFin rfl).symm ⟨t'', hSmem⟩ ≤ j := by
        have hjdef' : (i0 : ℕ) = j.val + 1 := by omega
        omega
      have hi'eq : Sc.orderEmbOfFin rfl ((Sc.orderIsoOfFin rfl).symm ⟨t'', hSmem⟩) = t'' := by
        have := (Sc.orderIsoOfFin rfl).apply_symm_apply (⟨t'', hSmem⟩ : Sc)
        have h2 := congrArg (Subtype.val) this
        rwa [Finset.coe_orderIsoOfFin_apply] at h2
      have := (Sc.orderEmbOfFin rfl).le_iff_le.mpr hi''lej
      rwa [hi'eq] at this

/-- The signed unit at a Boolean sign matches the reference encoding of `±1`. -/
theorem unit_eq_encode [CharP K 2] (Θ : Theta K) (sign : K) (hsign : sign = 0 ∨ sign = 1) :
    unit Θ sign = encode Θ (if sign = 1 then (-1 : ℤ) else 1) := by
  rcases hsign with rfl | rfl
  · simp [unit, encode]
  · rw [if_pos rfl]
    show (1 : K) + (Θ.θ + 1) * 1 = Θ.θ
    have h11 : (1 : K) + 1 = 0 := CharTwo.add_self_eq_zero 1
    rw [show (1 : K) + (Θ.θ + 1) * 1 = Θ.θ + (1 + 1) by ring, h11, add_zero]

/-- **The creation value matches the reference shuffle at the creation
moment, when the creation step's own source address differs from the
address it creates, and the final value matches the reference shuffle.**  By
strong induction on the address: the final value is either the last
replacement's sign (`wit_last_eq`) or the creation value; the creation
value, when the creation step's source differs from the address, is either
an earlier replacement's sign (`wit_pred_eq`) or the creation value of a
strictly smaller address (the source `positions` of the creation step,
forced smaller by `hpos` together with the difference hypothesis), whose own
creation step's source differing from it is inherited from `wit_pred_eq`'s
bound on steps earlier than the outer creation step (the inner creation step
is always earlier). -/
theorem wit_cEnc_eq_shuffle [CharP K 2] {F : SelectionField K S} {Θ : Theta K}
    {wit : Wit K N τ} (hτ : τ ≤ N) (hN : N ≤ 256) (hτbits : τ < 64)
    (hpos : ∀ s : Fin τ, Bits.natOfBits (wit.positions s) ≤ N - τ + s)
    (hbits : ∀ s, Bits.AllBool (wit.positions s))
    (hsigns : ∀ s, wit.signs s = 0 ∨ wit.signs s = 1)
    (hor : OriginsOk wit)
    (hkey : (↑(writesTriples F Θ wit) : Multiset (K × K × K)) = ↑(readsTriples F wit))
    (hposLt : ∀ s : Fin τ, Bits.natOfBits (wit.positions s) < N) :
    ∀ a : ℕ, ∀ ha : a < N,
      wit.cEnc ⟨a, ha⟩
        = encode Θ (shuffle N τ (fun s => Bits.natOfBits (wit.positions s)) (signBools wit) ⟨a, ha⟩)
      ∧ ∀ hnlt : ¬ a < N - τ,
          Bits.natOfBits (wit.positions (creationStep hτ a ha hnlt)) ≠ a →
          creationVal wit hτ a ha
            = encode Θ (shuffleAt N τ (fun s => Bits.natOfBits (wit.positions s)) (signBools wit)
                ((creationStep hτ a ha hnlt : Fin τ) : ℕ)
                ⟨Bits.natOfBits (wit.positions (creationStep hτ a ha hnlt)),
                  hposLt (creationStep hτ a ha hnlt)⟩) := by
  set positions := fun s : Fin τ => Bits.natOfBits (wit.positions s) with hposdef
  have hposeq : ∀ s : Fin τ, positions s = Bits.natOfBits (wit.positions s) := fun s => rfl
  intro a
  induction a using Nat.strong_induction_on with
  | _ a IH =>
    intro ha
    have hcreation : ∀ hnlt : ¬ a < N - τ, positions (creationStep hτ a ha hnlt) ≠ a →
        creationVal wit hτ a ha
          = encode Θ (shuffleAt N τ positions (signBools wit)
              ((creationStep hτ a ha hnlt : Fin τ) : ℕ)
              ⟨positions (creationStep hτ a ha hnlt), hposLt _⟩) := by
      intro hnlt hself
      unfold creationVal
      rw [dif_neg hnlt]
      have hread := wit_pred_eq hτ hN hτbits hpos hbits hor hkey (creationStep hτ a ha hnlt) hposLt
      rcases hread with ⟨t', ht', hpt', hmax', hval⟩ | ⟨hnone', hval⟩
      · have hshuf2 := shuffleAt_of_last (signs := signBools wit) hτ hpos hposLt
          (le_of_lt (creationStep hτ a ha hnlt).isLt)
          (⟨positions (creationStep hτ a ha hnlt), hposLt _⟩ : Fin N) t' ht' hpt'
          (fun s' hs' hs'a => hmax' s' hs' hs'a)
        have hue := unit_eq_encode Θ (wit.signs t') (hsigns t')
        have hsb : signBools wit t' = decide (wit.signs t' = 1) := rfl
        rw [hval, hshuf2, hue, hsb]; simp
      · have hcLt : positions (creationStep hτ a ha hnlt) < N := hposLt (creationStep hτ a ha hnlt)
        have hpceq := hposeq (creationStep hτ a ha hnlt)
        have hcle : positions (creationStep hτ a ha hnlt) ≤ a := by
          have := hpos (creationStep hτ a ha hnlt)
          have := creationStep_val hτ a ha hnlt
          omega
        have hclt : positions (creationStep hτ a ha hnlt) < a := by omega
        have hshuf2 := shuffleAt_of_none (signs := signBools wit) hτ hpos hposLt
          (le_of_lt (creationStep hτ a ha hnlt).isLt)
          (⟨positions (creationStep hτ a ha hnlt), hcLt⟩ : Fin N)
          (fun s' hs' => hnone' s' hs')
        by_cases hclt2 : positions (creationStep hτ a ha hnlt) < N - τ
        · have hcv0 : creationVal wit hτ (positions (creationStep hτ a ha hnlt)) hcLt = 0 := by
            unfold creationVal; rw [dif_pos hclt2]
          rw [dif_neg (show ¬ (N - τ ≤ positions (creationStep hτ a ha hnlt)
              ∧ positions (creationStep hτ a ha hnlt) - (N - τ) < (creationStep hτ a ha hnlt : ℕ))
            by omega)] at hshuf2
          rw [hval, hcv0, hshuf2]
          simp [encode]
        · have hcsval := creationStep_val hτ a ha hnlt
          have hccond : N - τ ≤ positions (creationStep hτ a ha hnlt)
              ∧ positions (creationStep hτ a ha hnlt) - (N - τ) < (creationStep hτ a ha hnlt : ℕ) :=
            ⟨by omega, by omega⟩
          rw [dif_pos hccond] at hshuf2
          have hIHc := IH (positions (creationStep hτ a ha hnlt)) hclt hcLt
          have hnextself : positions (creationStep hτ (positions (creationStep hτ a ha hnlt)) hcLt
                (show ¬ positions (creationStep hτ a ha hnlt) < N - τ by omega))
              ≠ positions (creationStep hτ a ha hnlt) := by
            apply hnone'
            have := creationStep_val hτ (positions (creationStep hτ a ha hnlt)) hcLt
              (show ¬ positions (creationStep hτ a ha hnlt) < N - τ by omega)
            have := creationStep_val hτ a ha hnlt
            omega
          have hstep3 := hIHc.2 (show ¬ positions (creationStep hτ a ha hnlt) < N - τ by omega)
            hnextself
          have hFinEq : (creationStep hτ (positions (creationStep hτ a ha hnlt)) hcLt
                (show ¬ positions (creationStep hτ a ha hnlt) < N - τ by omega) : Fin τ)
              = ⟨positions (creationStep hτ a ha hnlt) - (N - τ), by omega⟩ := by
            apply Fin.ext
            rw [creationStep_val]
          rw [hFinEq] at hstep3
          rw [hval, hstep3, hshuf2]
    rcases wit_last_eq hτ hN hτbits hpos hbits hor hkey a ha with ⟨t, ht, hmax, hcEnc⟩ | ⟨hnone, hcEnc⟩
    · have hshuf := shuffleAt_of_last (signs := signBools wit) hτ hpos hposLt (le_refl τ)
        (⟨a, ha⟩ : Fin N) t t.isLt ht (fun s' _ hs' => hmax s' hs')
      rw [shuffleAt_of_le] at hshuf
      have hue := unit_eq_encode Θ (wit.signs t) (hsigns t)
      have hsb : signBools wit t = decide (wit.signs t = 1) := rfl
      exact ⟨by rw [hcEnc, hue, hshuf, hsb]; simp, hcreation⟩
    · have hshuf : shuffleAt N τ positions (signBools wit) τ (⟨a, ha⟩ : Fin N)
          = if hh : N - τ ≤ a ∧ a - (N - τ) < τ then
              shuffleAt N τ positions (signBools wit) (a - (N - τ))
                ⟨positions ⟨a - (N - τ), by omega⟩, hposLt _⟩
            else 0 :=
        shuffleAt_of_none (signs := signBools wit) hτ hpos hposLt (le_refl τ) (⟨a, ha⟩ : Fin N)
          (fun s' _ => hnone s')
      rw [shuffleAt_of_le] at hshuf
      by_cases hlt : a < N - τ
      · refine ⟨?_, hcreation⟩
        rw [hcEnc]
        unfold creationVal
        rw [dif_pos hlt, hshuf, dif_neg (by omega)]
        simp [encode]
      · have hself : positions (creationStep hτ a ha hlt) ≠ a :=
          fun hcontra => hnone (creationStep hτ a ha hlt) hcontra
        refine ⟨?_, hcreation⟩
        rw [hcEnc, hcreation hlt hself, hshuf, dif_pos (show N - τ ≤ a ∧ a - (N - τ) < τ by omega)]
        rfl

omit [DecidableEq K] in
/-- Decoding is exact on encoded values: support and sign of `0`, `+1`, `−1`. -/
theorem decodeTernary_encode [CharP K 2] (Θ : Theta K) (z : ℤ) (hz : z = 0 ∨ z = 1 ∨ z = -1) :
    decodeTernary Θ (encode Θ z)
      = ((if z = 0 then 0 else 1 : K), (if z = -1 then 1 else 0 : K)) := by
  rcases hz with rfl | rfl | rfl
  · simp [encode, decodeTernary]
  · simp [encode, decodeTernary, CharTwo.add_self_eq_zero]
  · norm_num [encode, decodeTernary, Θ.sq_add]
    rw [← add_assoc, CharTwo.add_self_eq_zero, zero_add]

/-! ### Completeness -/

/-- The honest advice, from running the shuffle while carrying
origins. -/
-- spec-side
def memoryTrace (Θ : Theta K) (positions : Fin τ → ℕ) (signs : Fin τ → Bool) :
    (Fin τ → K × ℕ) × (Fin N → K) × (Fin N → ℕ) :=
  let step (st : (Fin N → K) × (Fin N → ℕ) × List (K × ℕ)) (s : Fin τ) :=
    let (cell, origin, adv) := st
    if hi : N - τ + s < N then
      let i : Fin N := ⟨N - τ + s, hi⟩
      if hj : positions s < N then
        let j : Fin N := ⟨positions s, hj⟩
        let adv' := adv ++ [⟨cell j, origin j⟩]
        let cell' := Function.update (Function.update cell i (cell j)) j (unit Θ (if signs s then 1 else 0))
        let origin' := Function.update (Function.update origin i (origin j)) j (s + 1)
        (cell', origin', adv')
      else st
    else st
  let (cell, origin, adv) := (List.finRange τ).foldl step (fun _ => 0, fun _ => 0, [])
  (fun s => adv.getD s ⟨0, 0⟩, cell, origin)

omit [DecidableEq K] in
/-- Generalizes `memoryTrace_cell_eq_shuffle` to an arbitrary prefix of steps and
arbitrary starting states related by `encode`, by induction on the step list. -/
theorem foldl_cell_eq_shuffle_aux [CharP K 2] (Θ : Theta K)
    (positions : Fin τ → ℕ) (signs : Fin τ → Bool) (l : List (Fin τ))
    (c0 : Fin N → ℤ) (cell0 : Fin N → K) (origin0 : Fin N → ℕ) (adv0 : List (K × ℕ))
    (h0 : ∀ b, cell0 b = encode Θ (c0 b)) (a : Fin N) :
    (l.foldl
        (fun (st : (Fin N → K) × (Fin N → ℕ) × List (K × ℕ)) (s : Fin τ) =>
          let (cell, origin, adv) := st
          if hi : N - τ + (s : ℕ) < N then
            let i : Fin N := ⟨N - τ + s, hi⟩
            if hj : positions s < N then
              let j : Fin N := ⟨positions s, hj⟩
              let adv' := adv ++ [⟨cell j, origin j⟩]
              let cell' :=
                Function.update (Function.update cell i (cell j)) j (unit Θ (if signs s then 1 else 0))
              let origin' := Function.update (Function.update origin i (origin j)) j ((s : ℕ) + 1)
              (cell', origin', adv')
            else st
          else st)
        (cell0, origin0, adv0)).1 a
      = encode Θ
          (l.foldl
            (fun (c : Fin N → ℤ) (s : Fin τ) =>
              if hi : N - τ + (s : ℕ) < N then
                let i : Fin N := ⟨N - τ + s, hi⟩
                if hj : positions s < N then
                  let j : Fin N := ⟨positions s, hj⟩
                  Function.update (Function.update c i (c j)) j (if signs s then -1 else 1)
                else c
              else c)
            c0 a) := by
  induction l generalizing c0 cell0 origin0 adv0 with
  | nil => simpa using h0 a
  | cons s l ih =>
    simp only [List.foldl_cons]
    by_cases hi : N - τ + (s : ℕ) < N
    · by_cases hj : positions s < N
      · simp only [dif_pos hi, dif_pos hj]
        apply ih
        intro b
        set i : Fin N := ⟨N - τ + s, hi⟩ with hidef
        set j : Fin N := ⟨positions s, hj⟩ with hjdef
        by_cases hbj : b = j
        · subst hbj
          simp only [Function.update_self]
          by_cases hs : signs s
          · rw [if_pos hs, if_pos hs]
            show unit Θ 1 = encode Θ (-1)
            have h11 : (1 : K) + 1 = 0 := CharTwo.add_self_eq_zero 1
            rw [unit, show (1 : K) + (Θ.θ + 1) * 1 = Θ.θ + (1 + 1) by ring, h11, add_zero]
            simp [encode]
          · rw [if_neg hs, if_neg hs]
            show unit Θ 0 = encode Θ 1
            simp [unit, encode]
        · by_cases hbi : b = i
          · subst hbi
            simp only [Function.update_of_ne hbj, Function.update_self]
            exact h0 j
          · simp only [Function.update_of_ne hbj, Function.update_of_ne hbi]
            exact h0 b
      · simp only [dif_pos hi, dif_neg hj]
        exact ih c0 cell0 origin0 adv0 h0
    · simp only [dif_neg hi]
      exact ih c0 cell0 origin0 adv0 h0

omit [DecidableEq K] in
/-- **`memoryTrace` computes `shuffle`.**  The advice-carrying honest simulation
and the reference shuffle compute the same final array, under `Θ`'s ternary
encoding: a corollary of `foldl_cell_eq_shuffle_aux` at the empty starting
state. -/
theorem memoryTrace_cell_eq_shuffle [CharP K 2] (Θ : Theta K)
    (positions : Fin τ → ℕ) (signs : Fin τ → Bool) (a : Fin N) :
    (memoryTrace (N := N) Θ positions signs).2.1 a
      = encode Θ (shuffle N τ positions signs a) := by
  unfold memoryTrace shuffle
  exact foldl_cell_eq_shuffle_aux Θ positions signs (List.finRange τ)
    (fun _ => 0) (fun _ => 0) (fun _ => 0) [] (fun b => by simp [encode]) a

/-- Honest wire witness, from the natural-number memory trace. -/
-- spec-side
def honestWit (F : SelectionField K S) (Θ : Theta K)
    (positions : Fin τ → ℕ) (signs : Fin τ → Bool) : Wit K N τ :=
  let (read, cEnc, origin) := memoryTrace (N := N) Θ positions signs
  { positions := fun s b => Bits.constBit (positions s) b
    signs := fun s => if signs s then 1 else 0
    read := fun s => ⟨(read s).1, fun b => Bits.constBit (read s).2 b⟩
    cEnc := cEnc
    finalOrigin := fun k => F.embed (origin k) }

/-! #### Completeness helpers

Two parallel prefix-fold trackers over the honest simulation, both indexed by the number of steps
processed. `forkA_bigState` carries the two fingerprint triple multisets (`wAcc`, `rAcc`) alongside
the cell/origin state, and `forkA_bigState_inv` proves the offline-memory-checking invariant: writes
account for reads together with the live array. `forkB_state` is `memoryTrace`'s own step function,
re-indexed by prefix length, tracking the advice list; `forkB_inv` and `forkB_getD_eq_state` give
the per-step origin bound and identify each advice entry with the state read at that step.
`forkA_wAcc_rAcc_eq` unrolls the triple multisets as the literal lists
`writesTriples`/`readsTriples` are built from. -/

theorem forkA_multiset_filter_lt_succ (N k : ℕ) (hk : k < N) :
    Multiset.filter (fun a : Fin N => (a : ℕ) < k + 1) (Finset.univ : Finset (Fin N)).val
      = (⟨k, hk⟩ : Fin N) ::ₘ Multiset.filter (fun a : Fin N => (a : ℕ) < k)
          (Finset.univ : Finset (Fin N)).val := by
  apply Multiset.ext.mpr
  intro a
  by_cases ha : a = (⟨k, hk⟩ : Fin N)
  · subst ha
    have hmemk : (⟨k, hk⟩ : Fin N) ∈ (Finset.univ : Finset (Fin N)).val :=
      Finset.mem_def.mp (Finset.mem_univ _)
    have hcnt : Multiset.count (⟨k, hk⟩ : Fin N) (Finset.univ : Finset (Fin N)).val = 1 :=
      Multiset.count_eq_one_of_mem (Finset.univ : Finset (Fin N)).nodup hmemk
    simp [Multiset.count_filter, hcnt]
  · have hne : (a : ℕ) ≠ k := by
      intro h
      exact ha (Fin.ext h)
    have hmema : a ∈ (Finset.univ : Finset (Fin N)).val := Finset.mem_def.mp (Finset.mem_univ _)
    have hcnt : Multiset.count a (Finset.univ : Finset (Fin N)).val = 1 :=
      Multiset.count_eq_one_of_mem (Finset.univ : Finset (Fin N)).nodup hmema
    rw [Multiset.count_cons_of_ne ha]
    simp only [Multiset.count_filter, hcnt]
    by_cases hlt : (a : ℕ) < k
    · simp [hlt, Nat.lt_succ_of_lt hlt]
    · have hnlt : ¬ (a : ℕ) < k + 1 := by omega
      simp [hlt, hnlt]

theorem forkA_range_eq (F : SelectionField K S) (N m : ℕ) (hm : m ≤ N) :
    (↑((List.range m).map fun k => (F.embed k, (0 : K), (0 : K))) : Multiset (K × K × K))
      = (Multiset.filter (fun a : Fin N => (a : ℕ) < m) (Finset.univ : Finset (Fin N)).val).map
          (fun a : Fin N => (F.embed (a : ℕ), (0 : K), F.embed (0 : ℕ))) := by
  have hembed0 : F.embed 0 = (0 : K) := by simp [SelectionField.embed, selectionEmbed]
  induction m with
  | zero => simp
  | succ m ih =>
    have hm' : m < N := by omega
    have ihm : m ≤ N := by omega
    rw [List.range_succ, List.map_append, ← Multiset.coe_add, ih ihm,
      forkA_multiset_filter_lt_succ N m hm', Multiset.map_cons]
    simp [hembed0, add_comm]

def forkA_bigStep (F : SelectionField K S) (Θ : Theta K)
    (positions : Fin τ → ℕ) (signs : Fin τ → Bool)
    (st : (Fin N → K) × (Fin N → ℕ) × Multiset (K × K × K) × Multiset (K × K × K))
    (s : Fin τ) :
    (Fin N → K) × (Fin N → ℕ) × Multiset (K × K × K) × Multiset (K × K × K) :=
  let (cell, origin, wAcc, rAcc) := st
  if hi : N - τ + (s : ℕ) < N then
    let i : Fin N := ⟨N - τ + s, hi⟩
    if hj : positions s < N then
      let j : Fin N := ⟨positions s, hj⟩
      let cell' :=
        Function.update (Function.update cell i (cell j)) j (unit Θ (if signs s then 1 else 0))
      let origin' := Function.update (Function.update origin i (origin j)) j ((s : ℕ) + 1)
      let wAcc' := wAcc + (((F.embed (j : ℕ), unit Θ (if signs s then 1 else 0), F.embed ((s : ℕ) + 1)) ::ₘ
          ({(F.embed (i : ℕ), cell j, F.embed (origin j))} : Multiset (K × K × K))))
      let rAcc' := rAcc + ({(F.embed (j : ℕ), cell j, F.embed (origin j))} : Multiset (K × K × K))
      (cell', origin', wAcc', rAcc')
    else st
  else st

def forkA_bigState (F : SelectionField K S) (Θ : Theta K)
    (positions : Fin τ → ℕ) (signs : Fin τ → Bool) (n : ℕ) :
    (Fin N → K) × (Fin N → ℕ) × Multiset (K × K × K) × Multiset (K × K × K) :=
  ((List.finRange τ).take n).foldl (forkA_bigStep F Θ positions signs)
    (fun _ => 0, fun _ => 0,
      ↑((List.range (N - τ)).map fun k => (F.embed k, (0 : K), (0 : K))), 0)

theorem forkA_bigState_succ (N : ℕ) (F : SelectionField K S) (Θ : Theta K)
    (positions : Fin τ → ℕ) (signs : Fin τ → Bool) (n : ℕ) (hn : n < τ) :
    forkA_bigState (N := N) F Θ positions signs (n + 1)
      = forkA_bigStep F Θ positions signs (forkA_bigState F Θ positions signs n) ⟨n, hn⟩ := by
  unfold forkA_bigState
  have hlen : n < (List.finRange τ).length := by simpa using hn
  have htake : (List.finRange τ).take (n + 1) = (List.finRange τ).take n ++ [(List.finRange τ)[n]] :=
    List.take_succ_eq_append_getElem hlen
  have hget : (List.finRange τ)[n] = (⟨n, hn⟩ : Fin τ) := by
    simp [List.getElem_finRange]
  rw [htake, hget, List.foldl_append, List.foldl_cons, List.foldl_nil]

/-- The invariant: after folding `n ≤ τ` steps, every origin value is at most
`n`, and the write multiset accounts for the read multiset together with the
live array (addresses below `N - τ + n`), each paired with its current value
and origin. -/
theorem forkA_bigState_inv (F : SelectionField K S) (Θ : Theta K)
    (positions : Fin τ → ℕ) (signs : Fin τ → Bool)
    (hτ : τ ≤ N) (hpos : ∀ s : Fin τ, positions s ≤ N - τ + s) :
    ∀ n, n ≤ τ →
      (∀ a : Fin N, (forkA_bigState (N := N) F Θ positions signs n).2.1 a ≤ n) ∧
      (forkA_bigState (N := N) F Θ positions signs n).2.2.1 =
        (forkA_bigState (N := N) F Θ positions signs n).2.2.2 +
          Multiset.map
            (fun a : Fin N =>
              (F.embed (a : ℕ), (forkA_bigState (N := N) F Θ positions signs n).1 a,
                F.embed ((forkA_bigState (N := N) F Θ positions signs n).2.1 a)))
            (Multiset.filter (fun a : Fin N => (a : ℕ) < N - τ + n)
              (Finset.univ : Finset (Fin N)).val) := by
  intro n
  induction n with
  | zero =>
    intro _
    constructor
    · intro a; simp [forkA_bigState]
    · unfold forkA_bigState
      simp only [List.take_zero, List.foldl_nil]
      have hz : (Multiset.filter (fun a : Fin N => (a : ℕ) < N - τ + 0) (Finset.univ : Finset (Fin N)).val)
          = Multiset.filter (fun a : Fin N => (a : ℕ) < N - τ) (Finset.univ : Finset (Fin N)).val := by
        simp
      rw [hz, ← forkA_range_eq F N (N - τ) (Nat.sub_le N τ)]
      simp
  | succ n ih =>
    intro hn1
    have hn : n ≤ τ := by omega
    have hn' : n < τ := by omega
    obtain ⟨ihorig, ihmul⟩ := ih hn
    rw [forkA_bigState_succ N F Θ positions signs n hn']
    set cell := (forkA_bigState F Θ positions signs n).1 with hcelldef
    set origin := (forkA_bigState F Θ positions signs n).2.1 with horigindef
    set wAcc := (forkA_bigState F Θ positions signs n).2.2.1 with hwdef
    set rAcc := (forkA_bigState F Θ positions signs n).2.2.2 with hrdef
    have hi : N - τ + (n : ℕ) < N := by omega
    have hj : positions ⟨n, hn'⟩ < N := by
      have := hpos ⟨n, hn'⟩
      omega
    set i : Fin N := ⟨N - τ + n, hi⟩ with hidef
    set j : Fin N := ⟨positions ⟨n, hn'⟩, hj⟩ with hjdef
    have hstep : forkA_bigStep F Θ positions signs (forkA_bigState F Θ positions signs n) ⟨n, hn'⟩
        = (Function.update (Function.update cell i (cell j)) j
              (unit Θ (if signs ⟨n, hn'⟩ then 1 else 0)),
           Function.update (Function.update origin i (origin j)) j (n + 1),
           wAcc + ((F.embed (j : ℕ), unit Θ (if signs ⟨n, hn'⟩ then 1 else 0), F.embed (n + 1)) ::ₘ
              ({(F.embed (i : ℕ), cell j, F.embed (origin j))} : Multiset (K × K × K))),
           rAcc + ({(F.embed (j : ℕ), cell j, F.embed (origin j))} : Multiset (K × K × K))) := by
      unfold forkA_bigStep
      simp only [hcelldef, horigindef, hwdef, hrdef, hidef, hjdef]
      rw [dif_pos hi, dif_pos hj]
    rw [hstep]
    refine ⟨?_, ?_⟩
    · intro a
      show Function.update (Function.update origin i (origin j)) j (n + 1) a ≤ n + 1
      by_cases haj : a = j
      · subst haj; simp [Function.update_self]
      · by_cases hai : a = i
        · subst hai
          rw [Function.update_of_ne haj, Function.update_self]
          have := ihorig j
          omega
        · rw [Function.update_of_ne haj, Function.update_of_ne hai]
          have := ihorig a
          omega
    · show wAcc +
          ((F.embed (j : ℕ), unit Θ (if signs ⟨n, hn'⟩ then 1 else 0), F.embed ((n : ℕ) + 1)) ::ₘ
              ({(F.embed (i : ℕ), cell j, F.embed (origin j))} : Multiset (K × K × K)))
          = rAcc + ({(F.embed (j : ℕ), cell j, F.embed (origin j))} : Multiset (K × K × K)) +
              Multiset.map
                (fun a : Fin N =>
                  (F.embed (a : ℕ),
                    Function.update (Function.update cell i (cell j)) j
                      (unit Θ (if signs ⟨n, hn'⟩ then 1 else 0)) a,
                    F.embed (Function.update (Function.update origin i (origin j)) j ((n : ℕ) + 1) a)))
                (Multiset.filter (fun a : Fin N => (a : ℕ) < N - τ + (n + 1))
                  (Finset.univ : Finset (Fin N)).val)
      rw [ihmul]
      have hset : Multiset.filter (fun a : Fin N => (a : ℕ) < N - τ + (n + 1))
            (Finset.univ : Finset (Fin N)).val
          = i ::ₘ Multiset.filter (fun a : Fin N => (a : ℕ) < N - τ + n)
              (Finset.univ : Finset (Fin N)).val := by
        have hik : N - τ + (n + 1) = (N - τ + n) + 1 := by omega
        rw [hik]
        exact forkA_multiset_filter_lt_succ N (N - τ + n) hi
      rw [hset, Multiset.map_cons]
      have hane : ∀ a : Fin N, (a : ℕ) < N - τ + n → a ≠ i := by
        intro a ha h
        rw [h] at ha; simp only [hidef] at ha; omega
      by_cases hji : j = i
      · have hcelli : Function.update (Function.update cell i (cell j)) j
            (unit Θ (if signs ⟨n, hn'⟩ then 1 else 0)) i
            = unit Θ (if signs ⟨n, hn'⟩ then 1 else 0) := by
          rw [hji, Function.update_self]
        have horigini : Function.update (Function.update origin i (origin j)) j ((n : ℕ) + 1) i
            = (n : ℕ) + 1 := by
          rw [hji, Function.update_self]
        rw [hcelli, horigini]
        have hRV : ((F.embed (j : ℕ), cell j, F.embed (origin j)) : K × K × K)
            = (F.embed (i : ℕ), cell j, F.embed (origin j)) := by
          rw [hji]
        have hcong : Multiset.map
              (fun a : Fin N =>
                (F.embed (a : ℕ),
                  Function.update (Function.update cell i (cell j)) j
                    (unit Θ (if signs ⟨n, hn'⟩ then 1 else 0)) a,
                  F.embed (Function.update (Function.update origin i (origin j)) j ((n : ℕ) + 1) a)))
              (Multiset.filter (fun a : Fin N => (a : ℕ) < N - τ + n) (Finset.univ : Finset (Fin N)).val)
            = Multiset.map (fun a : Fin N => (F.embed (a : ℕ), cell a, F.embed (origin a)))
                (Multiset.filter (fun a : Fin N => (a : ℕ) < N - τ + n) (Finset.univ : Finset (Fin N)).val) := by
          apply Multiset.map_congr rfl
          intro a hain
          have haN : (a : ℕ) < N - τ + n := (Multiset.mem_filter.mp hain).2
          have haine : a ≠ i := hane a haN
          have hajne : a ≠ j := by rw [hji]; exact haine
          rw [Function.update_of_ne hajne, Function.update_of_ne haine,
            Function.update_of_ne hajne, Function.update_of_ne haine]
        rw [hcong]
        simp only [hRV, hji, ← Multiset.singleton_add]
        abel
      · have hcelli : Function.update (Function.update cell i (cell j)) j
            (unit Θ (if signs ⟨n, hn'⟩ then 1 else 0)) i = cell j := by
          rw [Function.update_of_ne (Ne.symm hji), Function.update_self]
        have horigini : Function.update (Function.update origin i (origin j)) j ((n : ℕ) + 1) i
            = origin j := by
          rw [Function.update_of_ne (Ne.symm hji), Function.update_self]
        rw [hcelli, horigini]
        have hjne : (j : Fin N) ≠ i := hji
        have hjlt : (j : ℕ) < N - τ + n := by
          have hle : (j : ℕ) ≤ N - τ + n := by rw [hjdef]; exact hpos ⟨n, hn'⟩
          have hine : (j : ℕ) ≠ N - τ + n := by
            intro h
            exact hjne (Fin.ext (by rw [hidef]; exact h))
          omega
        have hjmem : j ∈ Multiset.filter (fun a : Fin N => (a : ℕ) < N - τ + n)
            (Finset.univ : Finset (Fin N)).val :=
          Multiset.mem_filter.mpr ⟨Finset.mem_def.mp (Finset.mem_univ _), hjlt⟩
        have hsetj : Multiset.filter (fun a : Fin N => (a : ℕ) < N - τ + n)
              (Finset.univ : Finset (Fin N)).val
            = j ::ₘ (Multiset.filter (fun a : Fin N => (a : ℕ) < N - τ + n)
                (Finset.univ : Finset (Fin N)).val).erase j :=
          (Multiset.cons_erase hjmem).symm
        rw [hsetj]
        simp only [Multiset.map_cons]
        have hcong : Multiset.map
              (fun a : Fin N =>
                (F.embed (a : ℕ),
                  Function.update (Function.update cell i (cell j)) j
                    (unit Θ (if signs ⟨n, hn'⟩ then 1 else 0)) a,
                  F.embed (Function.update (Function.update origin i (origin j)) j ((n : ℕ) + 1) a)))
              ((Multiset.filter (fun a : Fin N => (a : ℕ) < N - τ + n)
                  (Finset.univ : Finset (Fin N)).val).erase j)
            = Multiset.map (fun a : Fin N => (F.embed (a : ℕ), cell a, F.embed (origin a)))
                ((Multiset.filter (fun a : Fin N => (a : ℕ) < N - τ + n)
                  (Finset.univ : Finset (Fin N)).val).erase j) := by
          apply Multiset.map_congr rfl
          intro a hain
          have hnodup : (Multiset.filter (fun a : Fin N => (a : ℕ) < N - τ + n)
              (Finset.univ : Finset (Fin N)).val).Nodup :=
            (Finset.univ : Finset (Fin N)).nodup.filter _
          have hain' := Multiset.mem_of_mem_erase hain
          have haN : (a : ℕ) < N - τ + n := (Multiset.mem_filter.mp hain').2
          have haine : a ≠ i := hane a haN
          have hajne : a ≠ j := (hnodup.mem_erase_iff.mp hain).1
          rw [Function.update_of_ne hajne, Function.update_of_ne haine,
            Function.update_of_ne hajne, Function.update_of_ne haine]
        rw [hcong]
        simp only [Function.update_self, ← Multiset.singleton_add]
        abel

def forkA_cellOriginStep (Θ : Theta K) (positions : Fin τ → ℕ) (signs : Fin τ → Bool)
    (st : (Fin N → K) × (Fin N → ℕ)) (s : Fin τ) : (Fin N → K) × (Fin N → ℕ) :=
  let (cell, origin) := st
  if hi : N - τ + (s : ℕ) < N then
    let i : Fin N := ⟨N - τ + s, hi⟩
    if hj : positions s < N then
      let j : Fin N := ⟨positions s, hj⟩
      (Function.update (Function.update cell i (cell j)) j (unit Θ (if signs s then 1 else 0)),
        Function.update (Function.update origin i (origin j)) j ((s : ℕ) + 1))
    else st
  else st

def forkB_step (Θ : Theta K) (positions : Fin τ → ℕ) (signs : Fin τ → Bool)
    (st : (Fin N → K) × (Fin N → ℕ) × List (K × ℕ)) (s : Fin τ) :
    (Fin N → K) × (Fin N → ℕ) × List (K × ℕ) :=
  let (cell, origin, adv) := st
  if hi : N - τ + (s : ℕ) < N then
    let i : Fin N := ⟨N - τ + s, hi⟩
    if hj : positions s < N then
      let j : Fin N := ⟨positions s, hj⟩
      (Function.update (Function.update cell i (cell j)) j (unit Θ (if signs s then 1 else 0)),
        Function.update (Function.update origin i (origin j)) j ((s : ℕ) + 1),
        adv ++ [(cell j, origin j)])
    else st
  else st

def forkB_state (Θ : Theta K) (positions : Fin τ → ℕ) (signs : Fin τ → Bool) (n : ℕ) :
    (Fin N → K) × (Fin N → ℕ) × List (K × ℕ) :=
  ((List.finRange τ).take n).foldl (forkB_step Θ positions signs) (fun _ => 0, fun _ => 0, [])

theorem forkA_cellOrigin_eq_forkB (F : SelectionField K S) (Θ : Theta K)
    (positions : Fin τ → ℕ) (signs : Fin τ → Bool) (n : ℕ) :
    ((forkA_bigState (N := N) F Θ positions signs n).1,
        (forkA_bigState (N := N) F Θ positions signs n).2.1)
      = ((forkB_state (N := N) Θ positions signs n).1,
          (forkB_state (N := N) Θ positions signs n).2.1) := by
  have hfoldA := List.foldl_hom
    (f := fun st : (Fin N → K) × (Fin N → ℕ) × Multiset (K × K × K) × Multiset (K × K × K) =>
      (st.1, st.2.1))
    (g₁ := forkA_bigStep F Θ positions signs) (g₂ := forkA_cellOriginStep Θ positions signs)
    (l := (List.finRange τ).take n)
    (init := (fun _ => 0, fun _ => 0,
      (↑((List.range (N - τ)).map fun k => (F.embed k, (0 : K), (0 : K))) : Multiset (K × K × K)),
      (0 : Multiset (K × K × K))))
    (fun a b => by
      obtain ⟨cell, origin, wAcc, rAcc⟩ := a
      unfold forkA_bigStep forkA_cellOriginStep
      by_cases hi : N - τ + (b : ℕ) < N <;> by_cases hj : positions b < N <;> simp [hi, hj])
  have hfoldB := List.foldl_hom
    (f := fun st : (Fin N → K) × (Fin N → ℕ) × List (K × ℕ) => (st.1, st.2.1))
    (g₁ := forkB_step Θ positions signs) (g₂ := forkA_cellOriginStep Θ positions signs)
    (l := (List.finRange τ).take n) (init := (fun _ => 0, fun _ => 0, ([] : List (K × ℕ))))
    (fun a b => by
      obtain ⟨cell, origin, adv⟩ := a
      unfold forkB_step forkA_cellOriginStep
      by_cases hi : N - τ + (b : ℕ) < N <;> by_cases hj : positions b < N <;> simp [hi, hj])
  unfold forkA_bigState forkB_state
  rw [← hfoldA, ← hfoldB]

theorem forkB_state_eq_memoryTrace (Θ : Theta K) (positions : Fin τ → ℕ) (signs : Fin τ → Bool) :
    (forkB_state (N := N) Θ positions signs τ).1 = (memoryTrace (N := N) Θ positions signs).2.1
    ∧ (forkB_state (N := N) Θ positions signs τ).2.1 = (memoryTrace (N := N) Θ positions signs).2.2
    ∧ ∀ s : Fin τ, (memoryTrace (N := N) Θ positions signs).1 s
        = (forkB_state (N := N) Θ positions signs τ).2.2.getD s ⟨0, 0⟩ := by
  unfold forkB_state memoryTrace forkB_step
  rw [List.take_of_length_le (by simp)]
  refine ⟨rfl, rfl, fun s => ?_⟩
  rfl

theorem forkB_state_succ (Θ : Theta K) (positions : Fin τ → ℕ) (signs : Fin τ → Bool)
    (n : ℕ) (hn : n < τ) :
    forkB_state (N := N) Θ positions signs (n + 1)
      = forkB_step Θ positions signs (forkB_state (N := N) Θ positions signs n) ⟨n, hn⟩ := by
  unfold forkB_state
  have hlen : n < (List.finRange τ).length := by simpa using hn
  have htake : (List.finRange τ).take (n + 1) = (List.finRange τ).take n ++ [(List.finRange τ)[n]] :=
    List.take_succ_eq_append_getElem hlen
  have hget : (List.finRange τ)[n] = (⟨n, hn⟩ : Fin τ) := by simp [List.getElem_finRange]
  rw [htake, hget, List.foldl_append, List.foldl_cons, List.foldl_nil]

theorem forkB_inv (Θ : Theta K) (positions : Fin τ → ℕ) (signs : Fin τ → Bool)
    (hτ : τ ≤ N) (hpos : ∀ s : Fin τ, positions s ≤ N - τ + s) :
    ∀ n, n ≤ τ →
      (∀ a : Fin N, (forkB_state (N := N) Θ positions signs n).2.1 a ≤ n) ∧
      (forkB_state (N := N) Θ positions signs n).2.2.length = n ∧
      ∀ i : ℕ, i < n → (((forkB_state (N := N) Θ positions signs n).2.2.getD i (0, 0)).2 : ℕ) ≤ i := by
  intro n
  induction n with
  | zero => intro _; refine ⟨?_, ?_, ?_⟩ <;> simp [forkB_state]
  | succ n ih =>
    intro hn1
    have hn : n ≤ τ := by omega
    have hn' : n < τ := by omega
    obtain ⟨ihorig, ihlen, ihget⟩ := ih hn
    rw [forkB_state_succ Θ positions signs n hn']
    set cell := (forkB_state (N := N) Θ positions signs n).1 with hcelldef
    set origin := (forkB_state (N := N) Θ positions signs n).2.1 with horigindef
    set adv := (forkB_state (N := N) Θ positions signs n).2.2 with hadvdef
    have hi : N - τ + (n : ℕ) < N := by omega
    have hj : positions ⟨n, hn'⟩ < N := by have := hpos ⟨n, hn'⟩; omega
    set i : Fin N := ⟨N - τ + n, hi⟩ with hidef
    set j : Fin N := ⟨positions ⟨n, hn'⟩, hj⟩ with hjdef
    have hstep : forkB_step Θ positions signs (forkB_state (N := N) Θ positions signs n) ⟨n, hn'⟩
        = (Function.update (Function.update cell i (cell j)) j (unit Θ (if signs ⟨n, hn'⟩ then 1 else 0)),
           Function.update (Function.update origin i (origin j)) j ((n : ℕ) + 1),
           adv ++ [(cell j, origin j)]) := by
      unfold forkB_step
      simp only [hcelldef, horigindef, hadvdef, hidef, hjdef]
      rw [dif_pos hi, dif_pos hj]
    rw [hstep]
    refine ⟨?_, ?_, ?_⟩
    · intro a
      show Function.update (Function.update origin i (origin j)) j (n + 1) a ≤ n + 1
      by_cases haj : a = j
      · subst haj; simp [Function.update_self]
      · by_cases hai : a = i
        · subst hai
          rw [Function.update_of_ne haj, Function.update_self]
          have := ihorig j; omega
        · rw [Function.update_of_ne haj, Function.update_of_ne hai]
          have := ihorig a; omega
    · show (adv ++ [(cell j, origin j)]).length = n + 1
      simp [ihlen]
    · intro k hk
      show (((adv ++ [(cell j, origin j)]).getD k (0, 0)).2 : ℕ) ≤ k
      rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hklt | hkeq
      · rw [List.getD_eq_getElem?_getD, List.getElem?_append_left (by omega),
          ← List.getD_eq_getElem?_getD]
        exact (ihget k hklt).trans (by omega)
      · subst hkeq
        rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega)]
        simp [ihlen]
        have := ihorig j
        omega

theorem forkB_getD_eq_state (Θ : Theta K) (positions : Fin τ → ℕ) (signs : Fin τ → Bool)
    (hτ : τ ≤ N) (hpos : ∀ s : Fin τ, positions s ≤ N - τ + s) :
    ∀ n, n ≤ τ → ∀ k : ℕ, ∀ (hk : k < n) (hkτ : k < τ),
      (forkB_state (N := N) Θ positions signs n).2.2.getD k (0, 0)
        = ((forkB_state (N := N) Θ positions signs k).1
              ⟨positions ⟨k, hkτ⟩, by have := hpos ⟨k, hkτ⟩; omega⟩,
           (forkB_state (N := N) Θ positions signs k).2.1
              ⟨positions ⟨k, hkτ⟩, by have := hpos ⟨k, hkτ⟩; omega⟩) := by
  intro n
  induction n with
  | zero => intro _ k hk; omega
  | succ n ih =>
    intro hn1 k hk hkτ
    have hn : n ≤ τ := by omega
    have hn' : n < τ := by omega
    obtain ⟨_, ihlen, _⟩ := forkB_inv Θ positions signs hτ hpos n hn
    rw [forkB_state_succ Θ positions signs n hn']
    set cell := (forkB_state (N := N) Θ positions signs n).1 with hcelldef
    set origin := (forkB_state (N := N) Θ positions signs n).2.1 with horigindef
    set adv := (forkB_state (N := N) Θ positions signs n).2.2 with hadvdef
    have hi : N - τ + (n : ℕ) < N := by omega
    have hj : positions ⟨n, hn'⟩ < N := by have := hpos ⟨n, hn'⟩; omega
    have hstep : forkB_step Θ positions signs (forkB_state (N := N) Θ positions signs n) ⟨n, hn'⟩
        = (Function.update (Function.update cell ⟨N - τ + n, hi⟩ (cell ⟨positions ⟨n, hn'⟩, hj⟩))
              ⟨positions ⟨n, hn'⟩, hj⟩ (unit Θ (if signs ⟨n, hn'⟩ then 1 else 0)),
           Function.update (Function.update origin ⟨N - τ + n, hi⟩ (origin ⟨positions ⟨n, hn'⟩, hj⟩))
              ⟨positions ⟨n, hn'⟩, hj⟩ ((n : ℕ) + 1),
           adv ++ [(cell ⟨positions ⟨n, hn'⟩, hj⟩, origin ⟨positions ⟨n, hn'⟩, hj⟩)]) := by
      unfold forkB_step
      simp only [hcelldef, horigindef, hadvdef]
      rw [dif_pos hi, dif_pos hj]
    rw [hstep]
    show ((adv ++ [(cell ⟨positions ⟨n, hn'⟩, hj⟩, origin ⟨positions ⟨n, hn'⟩, hj⟩)]).getD k (0, 0)) = _
    rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hklt | hkeq
    · rw [List.getD_eq_getElem?_getD, List.getElem?_append_left (by omega), ← List.getD_eq_getElem?_getD]
      exact ih hn k hklt hkτ
    · subst hkeq
      rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega)]
      simp only [ihlen, Nat.sub_self]
      constructor <;> rfl

theorem forkA_wAcc_rAcc_eq (F : SelectionField K S) (Θ : Theta K)
    (positions : Fin τ → ℕ) (signs : Fin τ → Bool) (hτ : τ ≤ N)
    (hposLt : ∀ s : Fin τ, positions s < N) :
    ∀ n, n ≤ τ →
      (forkA_bigState (N := N) F Θ positions signs n).2.2.1
          = ↑((List.range (N - τ)).map (fun k => (F.embed k, (0 : K), (0 : K)))
              ++ (((List.finRange τ).take n).flatMap fun s =>
                  [(F.embed (positions s), unit Θ (if signs s then 1 else 0), F.embed ((s : ℕ) + 1)),
                    (F.embed (N - τ + (s : ℕ)),
                      (forkA_bigState (N := N) F Θ positions signs (s : ℕ)).1 ⟨positions s, hposLt s⟩,
                      F.embed ((forkA_bigState (N := N) F Θ positions signs (s : ℕ)).2.1
                        ⟨positions s, hposLt s⟩))]))
      ∧ (forkA_bigState (N := N) F Θ positions signs n).2.2.2
          = ↑(((List.finRange τ).take n).map fun s =>
              (F.embed (positions s),
                (forkA_bigState (N := N) F Θ positions signs (s : ℕ)).1 ⟨positions s, hposLt s⟩,
                F.embed ((forkA_bigState (N := N) F Θ positions signs (s : ℕ)).2.1 ⟨positions s, hposLt s⟩))) := by
  intro n
  induction n with
  | zero => intro _; refine ⟨?_, ?_⟩ <;> simp [forkA_bigState]
  | succ n ih =>
    intro hn1
    have hn : n ≤ τ := by omega
    have hn' : n < τ := by omega
    obtain ⟨ihw, ihr⟩ := ih hn
    rw [forkA_bigState_succ N F Θ positions signs n hn']
    set cell := (forkA_bigState (N := N) F Θ positions signs n).1 with hcelldef
    set origin := (forkA_bigState (N := N) F Θ positions signs n).2.1 with horigindef
    set wAcc := (forkA_bigState (N := N) F Θ positions signs n).2.2.1 with hwdef
    set rAcc := (forkA_bigState (N := N) F Θ positions signs n).2.2.2 with hrdef
    have hi : N - τ + (n : ℕ) < N := by omega
    have hj : positions ⟨n, hn'⟩ < N := hposLt ⟨n, hn'⟩
    set i : Fin N := ⟨N - τ + n, hi⟩ with hidef
    set j : Fin N := ⟨positions ⟨n, hn'⟩, hj⟩ with hjdef
    have hstep : forkA_bigStep F Θ positions signs (forkA_bigState (N := N) F Θ positions signs n) ⟨n, hn'⟩
        = (Function.update (Function.update cell i (cell j)) j
              (unit Θ (if signs ⟨n, hn'⟩ then 1 else 0)),
           Function.update (Function.update origin i (origin j)) j ((n : ℕ) + 1),
           wAcc + ((F.embed (j : ℕ), unit Θ (if signs ⟨n, hn'⟩ then 1 else 0), F.embed ((n : ℕ) + 1)) ::ₘ
              ({(F.embed (i : ℕ), cell j, F.embed (origin j))} : Multiset (K × K × K))),
           rAcc + ({(F.embed (j : ℕ), cell j, F.embed (origin j))} : Multiset (K × K × K))) := by
      unfold forkA_bigStep
      simp only [hcelldef, horigindef, hwdef, hrdef, hidef, hjdef]
      rw [dif_pos hi, dif_pos hj]
    rw [hstep]
    have htake : (List.finRange τ).take (n + 1) = (List.finRange τ).take n ++ [(⟨n, hn'⟩ : Fin τ)] := by
      have hlen : n < (List.finRange τ).length := by simpa using hn'
      rw [List.take_succ_eq_append_getElem hlen]
      simp [List.getElem_finRange]
    constructor
    · rw [htake, List.flatMap_append]
      simp only [ihw, List.flatMap_cons, List.flatMap_nil, List.append_nil, ← Multiset.singleton_add,
        ← Multiset.coe_add]
      abel
    · rw [htake, List.map_append]
      simp only [ihr, List.map_cons, List.map_nil, ← Multiset.singleton_add, ← Multiset.coe_add]
      abel

/-- **The honest record triples agree as multisets**: the honest trace's writes are its reads
(the offline memory argument's honest prover). `hτ`, `hN` and `hτbits` are parameter bounds; `hpos`
describes the successful sampler's output. -/
theorem honestWit_key [CharP K 2] (F : SelectionField K S) (Θ : Theta K)
    (hτ : τ ≤ N) (hN : N ≤ 256) (hτbits : τ < 64)
    {positions : Fin τ → ℕ} {signs : Fin τ → Bool}
    (hpos : ∀ s : Fin τ, positions s ≤ N - τ + s) :
    (↑(writesTriples F Θ (honestWit F Θ positions signs : Wit K N τ)) : Multiset (K × K × K)) =
      ↑(readsTriples F (honestWit F Θ positions signs : Wit K N τ)) := by
  set wit := honestWit F Θ positions signs with hwitdef
  have hposLt : ∀ s : Fin τ, positions s < N := by
    intro s; have := hpos s; have := s.isLt; omega
  have horiginBound : ∀ s : Fin τ, (((memoryTrace (N := N) Θ positions signs).1 s).2 : ℕ) ≤ (s : ℕ) := by
    intro s
    obtain ⟨_, _, h3⟩ := forkB_state_eq_memoryTrace Θ positions signs
    obtain ⟨_, _, hget⟩ := forkB_inv Θ positions signs hτ hpos τ le_rfl
    rw [h3 s]
    exact hget s s.isLt
  have horiginLt64 : ∀ s : Fin τ, (((memoryTrace (N := N) Θ positions signs).1 s).2 : ℕ) < 64 := by
    intro s; have := horiginBound s; have := s.isLt; omega
  have hwitpos : ∀ s : Fin τ, F.embedBits (by decide) (wit.positions s) = F.embed (positions s) := by
    intro s
    show F.embedBits (by decide) (fun b => Bits.constBit (positions s) b) = F.embed (positions s)
    rw [F.embedBits_eq (by decide) (fun b => Bits.constBit_bool (positions s) b)]
    congr 1
    rw [Bits.natOfBits_constBit]
    exact Nat.mod_eq_of_lt (by have := hposLt s; omega : positions s < 2 ^ 8)
  have hwitorigin : ∀ s : Fin τ, F.embedBits (by decide) (wit.read s).origin
      = F.embed (((memoryTrace (N := N) Θ positions signs).1 s).2) := by
    intro s
    show F.embedBits (by decide)
        (fun b => Bits.constBit (((memoryTrace (N := N) Θ positions signs).1 s).2) b)
      = F.embed (((memoryTrace (N := N) Θ positions signs).1 s).2)
    rw [F.embedBits_eq (by decide)
      (fun b => Bits.constBit_bool (((memoryTrace (N := N) Θ positions signs).1 s).2) b)]
    congr 1
    rw [Bits.natOfBits_constBit]
    exact Nat.mod_eq_of_lt (by have := horiginLt64 s; omega : _ < 2 ^ 6)
  have hAllBool : ∀ s : Fin τ, Bits.AllBool (wit.read s).origin := fun s b => Bits.constBit_bool _ _
  have hltConst1 : ∀ s : Fin τ, Bits.ltConst (wit.read s).origin ((s : ℕ) + 1) = 1 := by
    intro s
    rw [Bits.ltConst_eq (hAllBool s) (by have := s.isLt; omega : (s : ℕ) + 1 < 2 ^ 6)]
    show (if Bits.natOfBits (fun b => Bits.constBit (((memoryTrace (N := N) Θ positions signs).1 s).2) b)
        < (s : ℕ) + 1 then (1 : K) else 0) = 1
    rw [Bits.natOfBits_constBit, Nat.mod_eq_of_lt (by have := horiginLt64 s; omega)]
    have := horiginBound s
    simp only [if_pos (by omega : ((memoryTrace (N := N) Θ positions signs).1 s).2 < (s : ℕ) + 1)]
  have hval : ∀ s : Fin τ, (wit.read s).value
      = (forkA_bigState (N := N) F Θ positions signs (s : ℕ)).1 ⟨positions s, hposLt s⟩ := by
    intro s
    show ((memoryTrace (N := N) Θ positions signs).1 s).1 = _
    obtain ⟨_, _, h3⟩ := forkB_state_eq_memoryTrace Θ positions signs
    rw [h3 s, forkB_getD_eq_state Θ positions signs hτ hpos τ le_rfl s s.isLt s.isLt]
    exact (congrFun (congrArg Prod.fst (forkA_cellOrigin_eq_forkB F Θ positions signs (s : ℕ)))
      ⟨positions s, hposLt s⟩).symm
  have horig : ∀ s : Fin τ, (((memoryTrace (N := N) Θ positions signs).1 s).2 : ℕ)
      = (forkA_bigState (N := N) F Θ positions signs (s : ℕ)).2.1 ⟨positions s, hposLt s⟩ := by
    intro s
    show (((memoryTrace (N := N) Θ positions signs).1 s).2 : ℕ) = _
    obtain ⟨_, _, h3⟩ := forkB_state_eq_memoryTrace Θ positions signs
    rw [h3 s, forkB_getD_eq_state Θ positions signs hτ hpos τ le_rfl s s.isLt s.isLt]
    exact (congrFun (congrArg Prod.snd (forkA_cellOrigin_eq_forkB F Θ positions signs (s : ℕ)))
      ⟨positions s, hposLt s⟩).symm
  have htaketau : (List.finRange τ).take τ = List.finRange τ := List.take_of_length_le (by simp)
  have hwriteseq : (↑(writesTriples F Θ wit) : Multiset (K × K × K))
      = (forkA_bigState (N := N) F Θ positions signs τ).2.2.1 := by
    rw [(forkA_wAcc_rAcc_eq F Θ positions signs hτ hposLt τ le_rfl).1, htaketau]
    unfold writesTriples
    have hflat : (List.finRange τ).flatMap (fun s =>
          [(F.embedBits (by decide) (wit.positions s), unit Θ (wit.signs s), F.embed ((s : ℕ) + 1)),
            (F.embed (N - τ + (s : ℕ)), (wit.read s).value, F.embedBits (by decide) (wit.read s).origin)])
        = (List.finRange τ).flatMap (fun s =>
          [(F.embed (positions s), unit Θ (if signs s then 1 else 0), F.embed ((s : ℕ) + 1)),
            (F.embed (N - τ + (s : ℕ)),
              (forkA_bigState (N := N) F Θ positions signs (s : ℕ)).1 ⟨positions s, hposLt s⟩,
              F.embed ((forkA_bigState (N := N) F Θ positions signs (s : ℕ)).2.1
                ⟨positions s, hposLt s⟩))]) := by
      apply List.flatMap_congr
      intro s _
      have hsigns : wit.signs s = if signs s then 1 else 0 := rfl
      rw [hwitpos s, ← hval s, ← horig s, hwitorigin s, hsigns]
    rw [hflat]
  have hfinalcell : wit.cEnc = (forkA_bigState (N := N) F Θ positions signs τ).1 := by
    obtain ⟨h1, _, _⟩ := forkB_state_eq_memoryTrace Θ positions signs
    show (memoryTrace (N := N) Θ positions signs).2.1 = _
    rw [← h1]
    exact (congrArg Prod.fst (forkA_cellOrigin_eq_forkB F Θ positions signs τ)).symm
  have hfinalorigin : ∀ k, wit.finalOrigin k
      = F.embed ((forkA_bigState (N := N) F Θ positions signs τ).2.1 k) := by
    intro k
    obtain ⟨_, h2, _⟩ := forkB_state_eq_memoryTrace Θ positions signs
    show F.embed ((memoryTrace (N := N) Θ positions signs).2.2 k) = _
    rw [← h2]
    exact congrArg (fun p => F.embed (p k))
      (congrArg Prod.snd (forkA_cellOrigin_eq_forkB F Θ positions signs τ)).symm
  have hreadseq : (↑(readsTriples F wit) : Multiset (K × K × K))
      = (forkA_bigState (N := N) F Θ positions signs τ).2.2.2
        + Multiset.map (fun a : Fin N =>
            (F.embed (a : ℕ), (forkA_bigState (N := N) F Θ positions signs τ).1 a,
              F.embed ((forkA_bigState (N := N) F Θ positions signs τ).2.1 a)))
            (Finset.univ : Finset (Fin N)).val := by
    rw [(forkA_wAcc_rAcc_eq F Θ positions signs hτ hposLt τ le_rfl).2, htaketau]
    unfold readsTriples
    rw [← Multiset.coe_add]
    congr 2
    · apply List.map_congr_left
      intro s _
      rw [hwitpos s, ← hval s, ← horig s, hwitorigin s]
    · apply List.map_congr_left
      intro k _
      rw [hfinalcell, hfinalorigin k]
  have hfilt : Multiset.filter (fun a : Fin N => (a : ℕ) < N - τ + τ) (Finset.univ : Finset (Fin N)).val
      = (Finset.univ : Finset (Fin N)).val := by
    have hNττ : N - τ + τ = N := by omega
    rw [hNττ]
    apply Multiset.filter_eq_self.mpr
    intro a _
    exact a.isLt
  have hArrayPart := (forkA_bigState_inv F Θ positions signs hτ hpos τ le_rfl).2
  rw [hfilt] at hArrayPart
  have hkey : (↑(writesTriples F Θ wit) : Multiset (K × K × K)) = ↑(readsTriples F wit) := by
    rw [hwriteseq, hArrayPart, hreadseq]
  exact hkey

/-- **The honest origins pass the origin check**: each is the six bits of an origin at most its
step. -/
theorem honestWit_originsOk [CharP K 2] (F : SelectionField K S) (Θ : Theta K)
    (hτ : τ ≤ N) (hN : N ≤ 256) (hτbits : τ < 64)
    {positions : Fin τ → ℕ} {signs : Fin τ → Bool}
    (hpos : ∀ s : Fin τ, positions s ≤ N - τ + s) :
    OriginsOk (honestWit F Θ positions signs : Wit K N τ) := by
  set wit := honestWit F Θ positions signs with hwitdef
  have hposLt : ∀ s : Fin τ, positions s < N := by
    intro s; have := hpos s; have := s.isLt; omega
  have horiginBound : ∀ s : Fin τ, (((memoryTrace (N := N) Θ positions signs).1 s).2 : ℕ) ≤ (s : ℕ) := by
    intro s
    obtain ⟨_, _, h3⟩ := forkB_state_eq_memoryTrace Θ positions signs
    obtain ⟨_, _, hget⟩ := forkB_inv Θ positions signs hτ hpos τ le_rfl
    rw [h3 s]
    exact hget s s.isLt
  have horiginLt64 : ∀ s : Fin τ, (((memoryTrace (N := N) Θ positions signs).1 s).2 : ℕ) < 64 := by
    intro s; have := horiginBound s; have := s.isLt; omega
  have hwitpos : ∀ s : Fin τ, F.embedBits (by decide) (wit.positions s) = F.embed (positions s) := by
    intro s
    show F.embedBits (by decide) (fun b => Bits.constBit (positions s) b) = F.embed (positions s)
    rw [F.embedBits_eq (by decide) (fun b => Bits.constBit_bool (positions s) b)]
    congr 1
    rw [Bits.natOfBits_constBit]
    exact Nat.mod_eq_of_lt (by have := hposLt s; omega : positions s < 2 ^ 8)
  have hwitorigin : ∀ s : Fin τ, F.embedBits (by decide) (wit.read s).origin
      = F.embed (((memoryTrace (N := N) Θ positions signs).1 s).2) := by
    intro s
    show F.embedBits (by decide)
        (fun b => Bits.constBit (((memoryTrace (N := N) Θ positions signs).1 s).2) b)
      = F.embed (((memoryTrace (N := N) Θ positions signs).1 s).2)
    rw [F.embedBits_eq (by decide)
      (fun b => Bits.constBit_bool (((memoryTrace (N := N) Θ positions signs).1 s).2) b)]
    congr 1
    rw [Bits.natOfBits_constBit]
    exact Nat.mod_eq_of_lt (by have := horiginLt64 s; omega : _ < 2 ^ 6)
  have hAllBool : ∀ s : Fin τ, Bits.AllBool (wit.read s).origin := fun s b => Bits.constBit_bool _ _
  have hltConst1 : ∀ s : Fin τ, Bits.ltConst (wit.read s).origin ((s : ℕ) + 1) = 1 := by
    intro s
    rw [Bits.ltConst_eq (hAllBool s) (by have := s.isLt; omega : (s : ℕ) + 1 < 2 ^ 6)]
    show (if Bits.natOfBits (fun b => Bits.constBit (((memoryTrace (N := N) Θ positions signs).1 s).2) b)
        < (s : ℕ) + 1 then (1 : K) else 0) = 1
    rw [Bits.natOfBits_constBit, Nat.mod_eq_of_lt (by have := horiginLt64 s; omega)]
    have := horiginBound s
    simp only [if_pos (by omega : ((memoryTrace (N := N) Θ positions signs).1 s).2 < (s : ℕ) + 1)]
  exact ⟨hAllBool, fun s => by
    have h := hltConst1 s
    rw [Bits.ltConst_eq (hAllBool s) (by have := s.isLt; omega : (s : ℕ) + 1 < 2 ^ 6)] at h
    by_contra hcon
    rw [if_neg hcon] at h
    exact absurd h (by norm_num)⟩

end GordieHowe.MemoryShuffle
