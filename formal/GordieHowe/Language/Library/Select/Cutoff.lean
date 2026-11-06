-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Language.Library.Select.Scan

@[expose] public section

/-!
# Natural-number semantics of selection below a fixed bound

The scan `CutoffScan(n, bound)` of `GordieHowe/Language/Library/Select/Scan.lean`: a sample is accepted
when it lies below `bound`, a counter `count_enc` labels the selections `g^0, g^1, …`, and the
committed bit `full` ends the selection once `n` samples are taken. `sound` and `complete` are
`SelectScan.sound` and `SelectScan.complete` at this scan, and `honestRoute` is the honest
route.

`stream` is the sample stream, `route` is the committed advice
`(count_enc, full)` per position, and `bound` below is the acceptance bound. This is the natural-number semantic model of `SelectFirst` specialized to
`CutoffScan`. The wire-level gadget proves correspondence to this model;
only that gadget belongs in an arithmetic circuit.

Soundness (`sound`) quantifies over every argument, including `route` and
`out`: nothing the prover supplies is assumed correct ahead of the
`Constraints` hypothesis, and everything known about them comes from that
hypothesis. `badEvent` (the `AssertFilteredPermutation` fingerprinting
failure) is a function of the arguments alone, never of the challenge `δ`.
-/

namespace GordieHowe

open Polynomial

namespace SelectFirstCutoff.Model

variable {K : Type*} [Field K] [DecidableEq K] {S n w : ℕ}

export SelectScan (mux muxP enc)

/-- The acceptance predicate as a field bit: `[sample < bound]`. -/
def accept (bound sample : ℕ) : K := if sample < bound then 1 else 0

/-- Whether position `i` is selected: accepted, and for `i ≥ n` also not `full`. -/
def selected (n bound : ℕ) (stream : Fin S → ℕ) (route : Fin S → CutoffRoute K) (i : Fin S) : K :=
  if (i : ℕ) < n then accept bound (stream i)
  else accept bound (stream i) * (1 - (route i).full)

/-- The candidate side: the scan's `candPoly` with the counter as label. -/
noncomputable def candPoly (n : ℕ) (F : SelectionField K S w) (bound : ℕ) (stream : Fin S → ℕ)
    (route : Fin S → CutoffRoute K) : K[X] :=
  SelectScan.candPoly F (selected n bound stream route) (fun i => (route i).count_enc) stream

/-- The claimed side, with slot labels `g^j`. -/
noncomputable def claimPoly (F : SelectionField K S w) (out : Fin n → ℕ) : K[X] :=
  SelectScan.claimPoly F (fun j => F.g ^ (j : ℕ)) out

/-- `candPoly - claimPoly`: its evaluation at the challenge `δ` is `0` exactly
when the permutation check's fingerprint matches. -/
noncomputable def badPoly (n : ℕ) (F : SelectionField K S w) (bound : ℕ) (stream : Fin S → ℕ)
    (out : Fin n → ℕ) (route : Fin S → CutoffRoute K) : K[X] :=
  candPoly n F bound stream route - claimPoly F out

/-- `route[0].count_enc = 1`: the counter starts at slot `0`. -/
def Initial (route : Fin S → CutoffRoute K) : Prop :=
  ∀ i : Fin S, (i : ℕ) = 0 → (route i).count_enc = 1

/-- For every position at or past `n`, `route[i].full` is a bit, and it is
forced to `0` unless the counter has reached `g^n`. -/
def Done (F : SelectionField K S w) (n : ℕ) (route : Fin S → CutoffRoute K) : Prop :=
  ∀ i : Fin S, n ≤ (i : ℕ) →
    (route i).full * ((route i).full - 1) = 0 ∧
      (route i).full * ((route i).count_enc - F.g ^ n) = 0

/-- The counter advances by a factor of `g` exactly on a selected position, and
stays unchanged otherwise. -/
def Step (F : SelectionField K S w) (n bound : ℕ) (stream : Fin S → ℕ)
    (route : Fin S → CutoffRoute K) : Prop :=
  ∀ (i : Fin S) (hi : (i : ℕ) + 1 < S),
    (route ⟨(i : ℕ) + 1, hi⟩).count_enc
      = (route i).count_enc * SelectScan.mux (selected n bound stream route i) F.g 1

/-- The fingerprint check: `candPoly` and `claimPoly` agree at `δ`. -/
def Fingerprint (F : SelectionField K S w) (n bound : ℕ) (stream : Fin S → ℕ) (out : Fin n → ℕ)
    (route : Fin S → CutoffRoute K) (δ : K) : Prop :=
  (candPoly n F bound stream route).eval δ = (claimPoly F out).eval δ

/-- The semantic constraint groups established by the wire circuit. These are
propositions about the checked trace, not a second executable gadget. -/
structure Constraints (F : SelectionField K S w) (bound : ℕ)
    (stream : Fin S → ℕ) (out : Fin n → ℕ) (route : Fin S → CutoffRoute K) (δ : K) : Prop where
  initial : Initial route
  done : Done F n route
  step : Step F n bound stream route
  fingerprint : Fingerprint F n bound stream out route δ

omit [DecidableEq K] in
/-- The candidate and claimed fingerprint products evaluate their polynomials
at `δ`. The wire circuit uses this identity to establish `Fingerprint`. -/
theorem fingerprint_products (F : SelectionField K S w) (bound : ℕ) (stream : Fin S → ℕ)
    (out : Fin n → ℕ) (route : Fin S → CutoffRoute K) (δ : K) :
    (List.finRange S).foldl
        (fun acc i => acc * SelectScan.mux (selected n bound stream route i)
          (δ - SelectScan.enc F (route i).count_enc (stream i)) 1) 1
      = (candPoly n F bound stream route).eval δ ∧
    (List.finRange n).foldl (fun acc (j : Fin n) => acc * (δ - SelectScan.enc F (F.g ^ (j : ℕ)) (out j))) 1
      = (claimPoly F out).eval δ :=
  SelectScan.fingerprint_products F _ _ stream _ out δ

/-- The bad event for the permutation check's fingerprinting: the scan's event
with the counter's labels. `hnS` supplies the degree bound. -/
noncomputable def badEvent (F : SelectionField K S w) (bound : ℕ) (stream : Fin S → ℕ)
    (out : Fin n → ℕ) (route : Fin S → CutoffRoute K) (hnS : n ≤ S) : ChallengeEvent K :=
  SelectScan.badEvent F (selected n bound stream route) (fun i => (route i).count_enc) stream
    (fun j => F.g ^ (j : ℕ)) out hnS

/-- The number of positions among the first `m` that `selected` marks `1`: the
rank a selection at position `m` (if any) would receive. -/
def selRank (n bound : ℕ) (stream : Fin S → ℕ)
    (route : Fin S → CutoffRoute K) (m : ℕ) : ℕ :=
  SelectScan.selRank (selected n bound stream route) m

theorem selRank_zero (n bound : ℕ) (stream : Fin S → ℕ)
    (route : Fin S → CutoffRoute K) :
    selRank n bound stream route 0 = 0 :=
  SelectScan.selRank_zero _

theorem selRank_le_self (n bound : ℕ) (stream : Fin S → ℕ)
    (route : Fin S → CutoffRoute K) (m : ℕ) :
    selRank n bound stream route m ≤ m :=
  SelectScan.selRank_le_self _ m

theorem selRank_mono (n bound : ℕ) (stream : Fin S → ℕ)
    (route : Fin S → CutoffRoute K) :
    Monotone (selRank n bound stream route) :=
  SelectScan.selRank_mono _

theorem selRank_succ (n bound : ℕ) (stream : Fin S → ℕ)
    (route : Fin S → CutoffRoute K) (m : ℕ) (h : m < S) :
    selRank n bound stream route (m + 1)
      = selRank n bound stream route m
        + (if selected n bound stream route ⟨m, h⟩ = 1 then 1 else 0) :=
  SelectScan.selRank_succ _ m h

omit [DecidableEq K] in
/-- Under `Done`, `selected` takes only the values `0` and `1`. -/
theorem selected_bool {n : ℕ} (bound : ℕ) (stream : Fin S → ℕ) {F : SelectionField K S w}
    {route : Fin S → CutoffRoute K} (hDone : Done F n route) (i : Fin S) :
    selected n bound stream route i = 0 ∨ selected n bound stream route i = 1 := by
  unfold selected accept
  by_cases hi : (i : ℕ) < n
  · simp only [hi, ite_true]
    by_cases hb : stream i < bound <;> simp [hb]
  · simp only [hi, ite_false]
    obtain ⟨hbit, _⟩ := hDone i (by omega)
    by_cases hb : stream i < bound
    · have hf : (route i).full = 0 ∨ (route i).full = 1 := by
        rcases mul_eq_zero.mp hbit with h1 | h1
        · left; exact h1
        · right; exact sub_eq_zero.mp h1
      rcases hf with hf | hf <;> simp [hb, hf]
    · simp [hb]

omit [DecidableEq K] in
/-- If position `i` is selected, its sample is below `bound`. -/
theorem selected_eq_one_imp_accept {n bound : ℕ} {stream : Fin S → ℕ}
    {route : Fin S → CutoffRoute K} {i : Fin S}
    (h : selected n bound stream route i = 1) :
    stream i < bound := by
  unfold selected accept at h
  by_cases hi : (i : ℕ) < n
  · simp only [hi, ite_true] at h
    by_contra hb
    simp [hb] at h
  · simp only [hi, ite_false] at h
    by_contra hb
    simp [hb] at h

/-- Under `Initial`, `Done`, `Step`, `route[m].count_enc = g^(selRank m)`: the
counter's value is exactly `g` raised to the running selection count. -/
theorem count_enc_eq_pow_selRank {n bound : ℕ} {F : SelectionField K S w} {stream : Fin S → ℕ}
    {route : Fin S → CutoffRoute K}
    (hInit : Initial route) (hDone : Done F n route) (hStep : Step F n bound stream route)
    (m : ℕ) (hm : m < S) :
    (route ⟨m, hm⟩).count_enc = F.g ^ (selRank n bound stream route m) := by
  induction m with
  | zero =>
    rw [selRank_zero, pow_zero]
    exact hInit ⟨0, hm⟩ rfl
  | succ m ih =>
    have hmS : m < S := by omega
    have hprev := ih hmS
    rw [selRank_succ n bound stream route m hmS]
    have hstep := hStep ⟨m, hmS⟩ hm
    have hcast : (⟨(⟨m, hmS⟩ : Fin S).val + 1, hm⟩ : Fin S) = ⟨m + 1, hm⟩ := by ext; simp
    rw [hcast] at hstep
    rw [hstep, hprev]
    by_cases hsel : selected n bound stream route ⟨m, hmS⟩ = 1
    · rw [ite_eq_left hsel]
      unfold SelectScan.mux
      rw [hsel, pow_add, pow_one]
      ring
    · rw [ite_eq_right hsel]
      have hb := selected_bool bound stream hDone ⟨m, hmS⟩
      rcases hb with hb | hb
      · unfold SelectScan.mux
        rw [hb, pow_add, pow_zero]
        ring
      · exact absurd hb hsel

/-- Under `Initial`, `Done`, `Step`, `hnS`, and while the running count at `i`
is still below `n`, position `i` is selected exactly when its sample is below
`bound`: the `full` flag cannot yet be forcing rejection. -/
theorem selected_iff_accept_of_lt {n bound : ℕ} {F : SelectionField K S w} {stream : Fin S → ℕ}
    {route : Fin S → CutoffRoute K}
    (hInit : Initial route) (hDone : Done F n route) (hStep : Step F n bound stream route)
    (hnS : n ≤ S)
    (i : Fin S) (hlt : selRank n bound stream route (i : ℕ) < n) :
    selected n bound stream route i = 1 ↔ stream i < bound := by
  constructor
  · exact selected_eq_one_imp_accept
  · intro hacc
    unfold selected accept
    by_cases hi : (i : ℕ) < n
    · simp [hi, hacc]
    · simp only [hi, ite_false]
      have hcount := count_enc_eq_pow_selRank hInit hDone hStep (i : ℕ) i.isLt
      have hi2 : (⟨(i : ℕ), i.isLt⟩ : Fin S) = i := by ext; simp
      rw [hi2] at hcount
      have hfull0 : (route i).full = 0 := by
        have hprod := (hDone i (by omega)).2
        rw [hcount] at hprod
        rcases mul_eq_zero.mp hprod with h1 | h1
        · exact h1
        · exfalso
          have hle1 : selRank n bound stream route (i : ℕ) ≤ S :=
            (selRank_le_self n bound stream route (i : ℕ)).trans i.isLt.le
          have := F.g_order (selRank n bound stream route (i : ℕ)) n hle1 hnS
            (sub_eq_zero.mp h1)
          omega
      rw [hfull0]
      ring_nf
      simp [hacc]

/-- The number of stream samples below `bound` among the first `m`, capped at
`n`: the honest value of the progress counter before position `m`. -/
def acceptedBefore (n bound : ℕ) (stream : Fin S → ℕ) (m : ℕ) : ℕ :=
  min (((List.ofFn stream).take m).countP fun v => decide (v < bound)) n

/-- `acceptedBefore` at `0` is `0`. -/
theorem acceptedBefore_zero (n bound : ℕ) (stream : Fin S → ℕ) :
    acceptedBefore n bound stream 0 = 0 := by
  unfold acceptedBefore
  simp

/-- `acceptedBefore n bound stream m` is at most `m`. -/
theorem acceptedBefore_le_self (n bound : ℕ) (stream : Fin S → ℕ) (m : ℕ) :
    acceptedBefore n bound stream m ≤ m := by
  unfold acceptedBefore
  have h1 : ((List.ofFn stream).take m).countP (fun v => decide (v < bound))
      ≤ ((List.ofFn stream).take m).length := List.countP_le_length
  have h2 : ((List.ofFn stream).take m).length ≤ m := by
    rw [List.length_take]; omega
  omega

/-- `acceptedBefore` is monotone in `m`. -/
theorem acceptedBefore_mono (n bound : ℕ) (stream : Fin S → ℕ) :
    Monotone (acceptedBefore n bound stream) := by
  intro m1 m2 hm
  unfold acceptedBefore
  have := List.Sublist.countP_le (p := fun v => decide (v < bound))
    (List.take_sublist_take_left hm :
      (List.ofFn stream).take m1 |>.Sublist ((List.ofFn stream).take m2))
  omega

/-- `acceptedBefore` at `m + 1` is `acceptedBefore` at `m`, plus `1` if
position `m`'s sample is below `bound` and the count has not yet reached
`n`. -/
theorem acceptedBefore_succ (n bound : ℕ) (stream : Fin S → ℕ) (m : ℕ) (h : m < S) :
    acceptedBefore n bound stream (m + 1)
      = acceptedBefore n bound stream m
        + (if stream ⟨m, h⟩ < bound ∧ acceptedBefore n bound stream m < n
             then 1 else 0) := by
  unfold acceptedBefore
  have hlen : m < (List.ofFn stream).length := by simpa using h
  rw [List.take_succ_eq_append_getElem hlen, List.countP_append]
  simp only [List.getElem_ofFn]
  set c := ((List.ofFn stream).take m).countP (fun v => decide (v < bound)) with hc
  by_cases hb : stream ⟨m, h⟩ < bound <;> by_cases hlt : min c n < n <;> simp [hb, hlt] <;> omega

/-- Soundness: the constraints imply that `out` is exactly the first `n`
stream samples below `bound`, or the challenge `δ` lands in the bad event for
`badPoly`.

Hypotheses: `hnS` is `param` (`n ≤ S`). `hs` is `gadget:hash`: the samples are `w`-bit readouts of
the hash gadget's output bits. `ho` is `gadget:` Booleanity of the committed bits of `out`. -/
theorem sound {F : SelectionField K S w} {bound : ℕ}
    {stream : Fin S → ℕ} {out : Fin n → ℕ} {route : Fin S → CutoffRoute K} {δ : K}
    (hnS : n ≤ S)
    (hs : ∀ i, stream i < 2 ^ w) (ho : ∀ j, out j < 2 ^ w)
    (h : Constraints F bound stream out route δ) :
    firstAccepted (fun v => decide (v < bound)) stream n = some out
    ∨ ChallengeEvent.BadAt (badEvent F bound stream out route hnS) δ := by
  obtain ⟨hInit, hDone, hStep, hFing⟩ := h
  have hgpow_mem : ∀ k : ℕ, F.g ^ k ∈ F.E := fun k => Subfield.pow_mem F.E F.g_mem k
  have hcount : ∀ i : Fin S, (route i).count_enc = F.g ^ selRank n bound stream route i :=
    fun i => count_enc_eq_pow_selRank hInit hDone hStep i i.isLt
  rw [← SelectScan.scanFirst_const]
  exact SelectScan.sound (acc := fun v _ => decide (v < bound)) hnS hs ho
    (selected_bool bound stream hDone) (fun i => (hcount i).symm ▸ hgpow_mem _)
    (fun _ => hgpow_mem _)
    (fun i j _ hl => F.g_order _ _ ((selRank_le_self n bound stream route i).trans i.isLt.le)
      (j.isLt.le.trans hnS) ((hcount i).symm.trans hl))
    (fun i hlt => by rw [selected_iff_accept_of_lt hInit hDone hStep hnS i hlt]; simp)
    hFing

/-- The honest advice: the route built from `acceptedBefore`, giving each
position the counter `g^(acceptedBefore i)` and setting `full` exactly once
the count reaches `n`. -/
def honestRoute (n : ℕ) (F : SelectionField K S w) (bound : ℕ) (stream : Fin S → ℕ) :
    Fin S → CutoffRoute K :=
  fun i =>
    let k' := acceptedBefore n bound stream (i : ℕ)
    { count_enc := F.g ^ k', full := if k' = n then 1 else 0 }

omit [DecidableEq K] in
/-- Fewer than `n` stream positions cannot have filled the first `n` outputs. -/
theorem honestRoute_full_zero (n : ℕ) (F : SelectionField K S w) (bound : ℕ)
    (stream : Fin S → ℕ) (i : Fin S) (hi : i.val < n) :
    (honestRoute n F bound stream i).full = 0 := by
  have h := (acceptedBefore_le_self n bound stream i).trans_lt hi
  simp only [honestRoute, ne_of_lt h, ↓reduceIte]

omit [DecidableEq K] in
theorem honestRoute_full_bool (n : ℕ) (F : SelectionField K S w) (bound : ℕ)
    (stream : Fin S → ℕ) (i : Fin S) :
    (honestRoute n F bound stream i).full = 0 ∨
      (honestRoute n F bound stream i).full = 1 := by
  dsimp only [honestRoute]
  split <;> simp

omit [DecidableEq K] in
/-- Under `honestRoute`, `selected` at `i` is `1` exactly when `stream i`
is below `bound` and fewer than `n` samples have been accepted before `i`. -/
theorem selected_honest_eq (n : ℕ) (F : SelectionField K S w) (bound : ℕ) (stream : Fin S → ℕ)
    (i : Fin S) :
    selected n bound stream (honestRoute n F bound stream) i
      = if stream i < bound ∧ acceptedBefore n bound stream (i : ℕ) < n
        then (1 : K) else 0 := by
  unfold selected honestRoute accept
  dsimp only
  by_cases hi : (i : ℕ) < n
  · have hlt : acceptedBefore n bound stream (i : ℕ) < n :=
      lt_of_le_of_lt (acceptedBefore_le_self n bound stream i) hi
    simp only [hi, ite_true, hlt, and_true]
  · have hle : acceptedBefore n bound stream (i : ℕ) ≤ n := min_le_right _ _
    by_cases hb : stream i < bound <;>
      by_cases hlt : acceptedBefore n bound stream (i : ℕ) = n <;>
      simp [hi, hb, hlt]
    omega

omit [DecidableEq K] in
/-- `honestRoute` satisfies `Initial`. -/
theorem honestRoute_initial (n : ℕ) (F : SelectionField K S w) (bound : ℕ) (stream : Fin S → ℕ) :
    Initial (honestRoute n F bound stream) := by
  intro i hi
  show F.g ^ acceptedBefore n bound stream (i : ℕ) = 1
  rw [hi, acceptedBefore_zero]
  exact pow_zero _

omit [DecidableEq K] in
/-- `honestRoute` satisfies `Done`. -/
theorem honestRoute_done (n : ℕ) (F : SelectionField K S w) (bound : ℕ) (stream : Fin S → ℕ) :
    Done F n (honestRoute n F bound stream) := by
  intro i _
  unfold honestRoute
  dsimp only
  by_cases h : acceptedBefore n bound stream (i : ℕ) = n
  · simp [h]
  · simp [h]

omit [DecidableEq K] in
/-- `honestRoute` satisfies `Step`. -/
theorem honestRoute_step (n : ℕ) (F : SelectionField K S w) (bound : ℕ) (stream : Fin S → ℕ) :
    Step F n bound stream (honestRoute n F bound stream) := by
  intro i hi
  rw [selected_honest_eq]
  show F.g ^ acceptedBefore n bound stream ((⟨(i:ℕ)+1, hi⟩:Fin S) : ℕ)
      = F.g ^ acceptedBefore n bound stream (i : ℕ)
        * SelectScan.mux (if stream i < bound ∧ acceptedBefore n bound stream (i : ℕ) < n
                 then (1 : K) else 0) F.g 1
  have hstep := acceptedBefore_succ n bound stream (i : ℕ) i.isLt
  have hmk : stream (⟨(i : ℕ), i.isLt⟩ : Fin S) = stream i := by congr 1
  rw [hmk] at hstep
  by_cases hcond : stream i < bound ∧ acceptedBefore n bound stream (i : ℕ) < n
  · rw [show ((⟨(i:ℕ)+1, hi⟩:Fin S) : ℕ) = (i:ℕ)+1 from rfl, hstep,
      ite_eq_left hcond, ite_eq_left hcond]
    unfold SelectScan.mux
    rw [pow_add, pow_one]
    ring
  · rw [show ((⟨(i:ℕ)+1, hi⟩:Fin S) : ℕ) = (i:ℕ)+1 from rfl, hstep,
      ite_eq_right hcond, ite_eq_right hcond]
    unfold SelectScan.mux
    ring

omit [DecidableEq K] in
/-- Under `honestRoute`, `candPoly` is the product of `X - enc(…)` over
exactly the positions whose sample is below `bound` and precede the `n`-th
acceptance. -/
theorem candPoly_honest_eq_filter (n : ℕ) (F : SelectionField K S w) (bound : ℕ) (stream : Fin S → ℕ) :
    candPoly n F bound stream (honestRoute n F bound stream) =
    ∏ i ∈ (Finset.univ.filter fun i : Fin S =>
        stream i < bound ∧ acceptedBefore n bound stream (i : ℕ) < n),
      (Polynomial.X - C (SelectScan.enc F (honestRoute n F bound stream i).count_enc
        (stream i))) := by
  rw [candPoly, SelectScan.candPoly]
  have step : ∀ i : Fin S,
      SelectScan.muxP (selected n bound stream (honestRoute n F bound stream) i)
        (Polynomial.X - C (SelectScan.enc F (honestRoute n F bound stream i).count_enc (stream i))) 1
      = if stream i < bound ∧ acceptedBefore n bound stream (i : ℕ) < n
        then (Polynomial.X
          - C (SelectScan.enc F (honestRoute n F bound stream i).count_enc (stream i)))
        else 1 := by
    intro i
    unfold SelectScan.muxP
    rw [selected_honest_eq]
    by_cases hc : stream i < bound ∧ acceptedBefore n bound stream (i : ℕ) < n
    · rw [ite_eq_left hc, ite_eq_left hc]; simp
    · rw [ite_eq_right hc, ite_eq_right hc]; simp
  rw [Finset.prod_congr rfl (fun i _ => step i), Finset.prod_filter]

/-- If `hout` witnesses `out = firstAccepted … n`, then at any position `i`
accepted at rank `j` (i.e. `j = acceptedBefore i` and `stream i < bound`), the
sample at `i` equals the claimed output `out j`. -/
theorem honestRoute_stream_eq_out {bound : ℕ}
    {stream : Fin S → ℕ} {out : Fin n → ℕ}
    (hout : firstAccepted (fun v => decide (v < bound)) stream n = some out)
    {i : Fin S} (j : Fin n) (hj : (j : ℕ) = acceptedBefore n bound stream (i : ℕ))
    (hcond : stream i < bound) :
    out j = stream i := by
  obtain ⟨hcard, houtval⟩ := GordieHowe.firstAccepted_eq_some_iff.mp hout
  have hiS : (i : ℕ) < (List.ofFn stream).length := by simp
  have hpi : (fun v => decide (v < bound)) (List.ofFn stream)[(i : ℕ)] = true := by
    rw [List.getElem_ofFn]
    exact decide_eq_true hcond
  obtain ⟨hjlt, heq⟩ :=
    List.getElem_filter_of_countP_take (fun v => decide (v < bound)) (List.ofFn stream)
      (i : ℕ) hiS hpi
  rw [List.getElem_ofFn] at heq
  have hcapped : acceptedBefore n bound stream (i : ℕ)
      = ((List.ofFn stream).take (i : ℕ)).countP (fun v => decide (v < bound)) := by
    have h2 := j.isLt
    rw [hj] at h2
    unfold acceptedBefore at h2 ⊢
    omega
  have hjval : (j : ℕ) = ((List.ofFn stream).take (i : ℕ)).countP (fun v => decide (v < bound)) := by
    rw [hj, hcapped]
  have e1 : (List.filter (fun v => decide (v < bound)) (List.ofFn stream))[(j : ℕ)]?
      = some (out j) := by
    rw [List.getElem?_eq_getElem (by omega : (j : ℕ) < _)]
    congr 1
    exact (houtval j).symm
  have e2 : (List.filter (fun v => decide (v < bound)) (List.ofFn stream))[
      ((List.ofFn stream).take (i : ℕ)).countP (fun v => decide (v < bound))]?
      = some (stream i) := by
    rw [List.getElem?_eq_getElem hjlt, heq]
  rw [hjval] at e1
  rw [e1] at e2
  simpa using e2

omit [DecidableEq K] in
/-- Under the honest route and `hout`, `candPoly` equals `claimPoly`: the
selected positions correspond bijectively, in order, to the claimed output
slots. -/
theorem honestRoute_candPoly_eq_claimPoly (n : ℕ) (F : SelectionField K S w) {bound : ℕ}
    {stream : Fin S → ℕ} {out : Fin n → ℕ}
    (hout : firstAccepted (fun v => decide (v < bound)) stream n = some out) :
    candPoly n F bound stream (honestRoute n F bound stream)
      = claimPoly F out := by
  rw [candPoly_honest_eq_filter, claimPoly]
  apply Finset.prod_bij
    (i := fun (a : Fin S) (ha : a ∈ Finset.univ.filter fun i : Fin S =>
        stream i < bound ∧ acceptedBefore n bound stream (i : ℕ) < n) =>
      (⟨acceptedBefore n bound stream (a : ℕ), (Finset.mem_filter.mp ha).2.2⟩ : Fin n))
  · intro a ha
    exact Finset.mem_univ _
  · intro a1 ha1 a2 ha2 heq
    have hc1 := (Finset.mem_filter.mp ha1).2
    have hc2 := (Finset.mem_filter.mp ha2).2
    by_contra hne
    rcases lt_or_gt_of_ne (fun h => hne (Fin.ext h)) with hlt | hlt
    · have hstep := acceptedBefore_succ n bound stream (a1 : ℕ) a1.isLt
      have hmk : stream (⟨(a1 : ℕ), a1.isLt⟩ : Fin S) = stream a1 := by congr 1
      rw [hmk, ite_eq_left hc1] at hstep
      have hmono := acceptedBefore_mono n bound stream
        (show (a1 : ℕ) + 1 ≤ (a2 : ℕ) by omega)
      have hval := congrArg Fin.val heq
      simp only at hval
      omega
    · have hstep := acceptedBefore_succ n bound stream (a2 : ℕ) a2.isLt
      have hmk : stream (⟨(a2 : ℕ), a2.isLt⟩ : Fin S) = stream a2 := by congr 1
      rw [hmk, ite_eq_left hc2] at hstep
      have hmono := acceptedBefore_mono n bound stream
        (show (a2 : ℕ) + 1 ≤ (a1 : ℕ) by omega)
      have hval := congrArg Fin.val heq
      simp only at hval
      omega
  · intro b _
    obtain ⟨hcard, -⟩ := GordieHowe.firstAccepted_eq_some_iff.mp hout
    have hbk : (b : ℕ) < (List.filter (fun v => decide (v < bound)) (List.ofFn stream)).length := by
      omega
    obtain ⟨idx, hidx, hp, hc⟩ :=
      List.exists_getElem_countP_take_eq (fun v => decide (v < bound)) (List.ofFn stream)
        (b : ℕ) hbk
    have hidxS : idx < S := by simpa using hidx
    have hstream : stream ⟨idx, hidxS⟩ < bound := by
      rw [List.getElem_ofFn] at hp
      simpa using hp
    have haccepted : acceptedBefore n bound stream idx = (b : ℕ) := by
      unfold acceptedBefore
      rw [hc]
      omega
    refine ⟨⟨idx, hidxS⟩, ?_, ?_⟩
    · rw [Finset.mem_filter]
      exact ⟨Finset.mem_univ _, hstream, by rw [haccepted]; exact b.isLt⟩
    · apply Fin.ext
      simpa using haccepted
  · intro a ha
    have hc := (Finset.mem_filter.mp ha).2
    have hstream_eq := honestRoute_stream_eq_out hout
      ⟨acceptedBefore n bound stream (a : ℕ), hc.2⟩ rfl hc.1
    unfold SelectScan.enc
    rw [hstream_eq]
    congr 2

omit [DecidableEq K] in
/-- Completeness: `honestRoute` satisfies the constraint groups for the
honestly first-`n`-accepted output `out`, for every challenge `δ`.

Hypotheses: `hout` is the honest input (the advice generator's success: `out`
is `firstAccepted`'s output). `n` is implicit; it is read off `hout`'s type
(`out : Fin n → ℕ` there). `F` stays explicit: nothing earlier in the
argument list determines it. -/
theorem complete {n : ℕ} (F : SelectionField K S w) {bound : ℕ} {stream : Fin S → ℕ}
    {out : Fin n → ℕ}
    (hout : firstAccepted (fun v => decide (v < bound)) stream n = some out)
    (δ : K) :
    Constraints F bound stream out (honestRoute n F bound stream) δ := by
  refine ⟨honestRoute_initial n F bound stream, honestRoute_done n F bound stream,
    honestRoute_step n F bound stream, ?_⟩
  show (candPoly n F bound stream (honestRoute n F bound stream)).eval δ
      = (claimPoly F out).eval δ
  rw [honestRoute_candPoly_eq_claimPoly n F hout]

end SelectFirstCutoff.Model

end GordieHowe
