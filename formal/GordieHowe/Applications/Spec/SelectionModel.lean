-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.LinearCombination
public import GordieHowe.Foundations.Probability.ChallengeEvent
public import GordieHowe.Applications.Falcon512.Spec.Basic
public import GordieHowe.Applications.Spec.SelectionField
public import GordieHowe.Foundations.ToMathlib.List
public import GordieHowe.Foundations.ToMathlib.Polynomial

@[expose] public section

/-!
# Natural-number semantics of the ordered selection gadget

`SelectScan` proves the permutation argument for any scan: `SelectScan.sound`
and `SelectScan.complete` against the greedy scan `SelectScan.scanFirst`.  The
listing below is the generic gadget and Falcon's scan; ML-DSA's rising-threshold
scan is `GordieHowe.MLDSA44.SelectFirstTau`.

```
gadget SelectFirst(stream, out, state, scan, δ):
    scan.AssertInitial(state[0])
    for i in 0..|out|−1:                       // completion impossible yet
        selected[i] := scan.Accept(stream[i], state[i])
    for i in |out|..|stream|−1:
        selected[i] := scan.Accept(stream[i], state[i])
                       AND NOT scan.Done(state[i])
    for i in 0..|stream|−2:
        scan.AssertStep(state[i], state[i+1], selected[i])
    candidates := [
        (enc(scan.Label(state[i]), stream[i]), selected[i])
        for i in 0..|stream|−1
    ]
    claimed := [
        (enc(scan.OutputLabel(j), out[j]), 1)
        for j in 0..|out|−1
    ]
    AssertFilteredPermutation(candidates, claimed, δ)

gadget SelectFirstN(stream, out, route, δ):
    SelectFirst(stream, out, route, FalconScan(|out|), δ)

scan FalconScan(n):
    AssertInitial(state):
        assert state.count_enc == 1

    Accept(sample, state):
        return sample < 5q

    Done(state):
        assert state.full is a bit              // committed advice
        assert state.full·(state.count_enc − g^n) == 0
        return state.full

    AssertStep(before, after, selected):
        assert after.count_enc == before.count_enc·mux(selected, g, 1)

    Label(state):
        return state.count_enc

    OutputLabel(j):
        return g^j
```

`stream` is Falcon's sample stream, `route` is the committed advice
`(count_enc, full)` per position, and `bound` below is the acceptance bound
(`5q` in the concrete instantiation). This is the natural-number semantic model of `SelectFirst` specialized to
`FalconScan`. The wire-level gadget proves correspondence to this model;
only that gadget belongs in an arithmetic circuit.

Soundness (`sound`) quantifies over every argument, including `route` and
`out`: nothing the prover supplies is assumed correct ahead of the
`Constraints` hypothesis, and everything known about them comes from that
hypothesis. `badEvent` (the `AssertFilteredPermutation` fingerprinting
failure) is a function of the arguments alone, never of the challenge `δ`.
-/

namespace GordieHowe

open Polynomial

namespace SelectScan

/-! ### Ordered selection by a scan

`SelectFirst` selects positions of a stream, tags each selected sample with the label its scan state
carries, and matches the tagged selected samples against the claimed outputs tagged with their slot
labels, as one filtered permutation at a challenge `δ`. This namespace proves what the permutation
check gives for any scan, from three facts the scan supplies:

* `sel` takes values in `{0, 1}`;
* a selected position whose label equals slot label `j` has `j` selections
  before it (`selRank sel i = j`);
* while fewer than `n` positions have been selected, position `i` is selected
  exactly when the scan accepts its sample at the current rank
  (`acc (stream i) (selRank sel i)`).

Under these facts acceptance gives `scanFirst acc stream n = some out`, the
greedy scan's first `n` accepted samples, or `δ` is a root of the nonzero
`badPoly`.  Falcon's fixed bound (`SelectFirstN.Model`) and ML-DSA's rising
threshold (`SelectFirstTau`) are instances. -/

variable {K : Type*} [Field K] [DecidableEq K] {S n w : ℕ}

/-- `mux(b, x, y) = b·x + (1 - b)·y`. -/
def mux (b x y : K) : K := b * x + (1 - b) * y

/-- `mux` on polynomials: `muxP(b, p, q) = b·p + (1 - b)·q`, with `b` a constant. -/
noncomputable def muxP (b : K) (p q : K[X]) : K[X] := C b * p + C (1 - b) * q

omit [DecidableEq K] in
theorem eval_muxP (b : K) (p q : K[X]) (δ : K) :
    (muxP b p q).eval δ = mux b (p.eval δ) (q.eval δ) := by
  simp [muxP, mux]

/-- Pair encoding `label + X · embed(sample)`. -/
def enc (F : SelectionField K S w) (label : K) (sample : ℕ) : K := label + F.X * F.embed sample

omit [DecidableEq K] in
theorem enc_injOn {F : SelectionField K S w} {l1 l2 : K} (hl1 : l1 ∈ F.E) (hl2 : l2 ∈ F.E)
    {s1 s2 : ℕ} (hs1 : s1 < 2 ^ w) (hs2 : s2 < 2 ^ w)
    (h : enc F l1 s1 = enc F l2 s2) : l1 = l2 ∧ s1 = s2 := by
  unfold enc at h
  have hemb1 : F.embed s1 ∈ F.E := F.embed_mem s1
  have hemb2 : F.embed s2 ∈ F.E := F.embed_mem s2
  have hs : s1 = s2 := by
    by_contra hne
    apply F.X_not_mem
    have hd : F.embed s2 - F.embed s1 ≠ 0 := by
      intro hd0
      exact hne (F.embed_injOn hs1 hs2 (sub_eq_zero.mp hd0).symm)
    have hXeq : F.X = (l1 - l2) / (F.embed s2 - F.embed s1) := by
      field_simp
      linear_combination -h
    rw [hXeq]
    exact Subfield.div_mem F.E (Subfield.sub_mem F.E hl1 hl2) (Subfield.sub_mem F.E hemb2 hemb1)
  refine ⟨?_, hs⟩
  rw [hs] at h
  have hcancel : l1 - l2 = 0 := by linear_combination h
  exact sub_eq_zero.mp hcancel

/-- The candidate side of the permutation check: `X - enc(label i, stream i)` for
each selected position and the constant `1` otherwise, via `muxP`. -/
noncomputable def candPoly (F : SelectionField K S w) (sel label : Fin S → K) (stream : Fin S → ℕ) :
    K[X] :=
  ∏ i : Fin S, muxP (sel i) (Polynomial.X - C (enc F (label i) (stream i))) 1

/-- The claimed side: `∏ j, (X - enc(outLabel j, out j))`. -/
noncomputable def claimPoly (F : SelectionField K S w) (outLabel : Fin n → K) (out : Fin n → ℕ) :
    K[X] :=
  ∏ j : Fin n, (Polynomial.X - C (enc F (outLabel j) (out j)))

/-- `candPoly - claimPoly`, fixed by the committed values before `δ`. -/
noncomputable def badPoly (F : SelectionField K S w) (sel label : Fin S → K) (stream : Fin S → ℕ)
    (outLabel : Fin n → K) (out : Fin n → ℕ) : K[X] :=
  candPoly F sel label stream - claimPoly F outLabel out

omit [DecidableEq K] in
/-- `badPoly` has degree at most `S`: both sides are products of at most `S`
factors of degree at most `1`. -/
theorem badPoly_natDegree_le {F : SelectionField K S w} {sel label : Fin S → K} {stream : Fin S → ℕ}
    {outLabel : Fin n → K} {out : Fin n → ℕ} (hnS : n ≤ S) :
    (badPoly F sel label stream outLabel out).natDegree ≤ S := by
  have hcand : (candPoly F sel label stream).natDegree ≤ S := by
    rw [candPoly]
    refine (natDegree_prod_le _ _).trans ?_
    calc ∑ i : Fin S, (muxP (sel i) (Polynomial.X - C (enc F (label i) (stream i))) 1).natDegree
        ≤ ∑ _i : Fin S, 1 := by
          apply Finset.sum_le_sum
          intro i _
          unfold muxP
          refine (natDegree_add_le _ _).trans (max_le ?_ ?_)
          · exact (natDegree_C_mul_le _ _).trans (natDegree_X_sub_C_le _)
          · exact (natDegree_C_mul_le _ _).trans (by simp)
      _ = S := by simp
  have hclaim : (claimPoly F outLabel out).natDegree ≤ n := by
    rw [claimPoly]
    refine (natDegree_prod_le _ _).trans ?_
    calc ∑ j : Fin n, (Polynomial.X - C (enc F (outLabel j) (out j))).natDegree
        ≤ ∑ _j : Fin n, 1 := by
          apply Finset.sum_le_sum
          intro j _
          exact natDegree_X_sub_C_le _
      _ = n := by simp
  exact (natDegree_sub_le _ _).trans (max_le hcand (hclaim.trans hnS))

/-- The bad event of the permutation check: `badPoly` is nonzero and `δ` is a root. -/
noncomputable def badEvent (F : SelectionField K S w) (sel label : Fin S → K) (stream : Fin S → ℕ)
    (outLabel : Fin n → K) (out : Fin n → ℕ) (hnS : n ≤ S) : ChallengeEvent K where
  poly := badPoly F sel label stream outLabel out
  deg := S
  natDegree_le := badPoly_natDegree_le hnS

/-- The fingerprint check: `candPoly` and `claimPoly` agree at `δ`. -/
def Fingerprint (F : SelectionField K S w) (sel label : Fin S → K) (stream : Fin S → ℕ)
    (outLabel : Fin n → K) (out : Fin n → ℕ) (δ : K) : Prop :=
  (candPoly F sel label stream).eval δ = (claimPoly F outLabel out).eval δ

omit [DecidableEq K] in
/-- The circuit's two fingerprint products evaluate `candPoly` and `claimPoly` at `δ`. -/
theorem fingerprint_products (F : SelectionField K S w) (sel label : Fin S → K) (stream : Fin S → ℕ)
    (outLabel : Fin n → K) (out : Fin n → ℕ) (δ : K) :
    (List.finRange S).foldl
        (fun acc i => acc * mux (sel i) (δ - enc F (label i) (stream i)) 1) 1
      = (candPoly F sel label stream).eval δ ∧
    (List.finRange n).foldl (fun acc (j : Fin n) => acc * (δ - enc F (outLabel j) (out j))) 1
      = (claimPoly F outLabel out).eval δ := by
  constructor
  · rw [List.finRange_foldl_mul_eq_prod, candPoly, eval_prod]
    apply Finset.prod_congr rfl
    intro i _
    rw [eval_muxP]
    simp [mux]
  · rw [List.finRange_foldl_mul_eq_prod, claimPoly, eval_prod]
    apply Finset.prod_congr rfl
    intro j _
    simp only [eval_sub, eval_X, eval_C]

/-- On `{0, 1}`-valued selections, `candPoly` is the product over the selected positions. -/
theorem candPoly_eq_filter {F : SelectionField K S w} {sel : Fin S → K} (label : Fin S → K)
    (stream : Fin S → ℕ) (hbool : ∀ i, sel i = 0 ∨ sel i = 1) :
    candPoly F sel label stream =
      ∏ i ∈ Finset.univ.filter (fun i : Fin S => sel i = 1),
        (Polynomial.X - C (enc F (label i) (stream i))) := by
  classical
  rw [candPoly, Finset.prod_filter]
  apply Finset.prod_congr rfl
  intro i _
  rcases hbool i with h | h
  · rw [h, ite_eq_right zero_ne_one]
    simp [muxP]
  · rw [h, ite_eq_left rfl]
    simp [muxP]

/-- The number of selected positions among the first `m`: the rank a selection
at position `m` receives. -/
def selRank (sel : Fin S → K) (m : ℕ) : ℕ :=
  ((List.ofFn fun i : Fin S => decide (sel i = 1)).take m).countP id

theorem selRank_zero (sel : Fin S → K) : selRank sel 0 = 0 := by
  simp [selRank]

theorem selRank_le_self (sel : Fin S → K) (m : ℕ) : selRank sel m ≤ m := by
  unfold selRank
  exact List.countP_le_length.trans (by rw [List.length_take]; omega)

theorem selRank_mono (sel : Fin S → K) : Monotone (selRank sel) := by
  intro m1 m2 hm
  exact List.Sublist.countP_le (p := id) (List.take_sublist_take_left hm)

theorem selRank_succ (sel : Fin S → K) (m : ℕ) (h : m < S) :
    selRank sel (m + 1) = selRank sel m + if sel ⟨m, h⟩ = 1 then 1 else 0 := by
  unfold selRank
  have hlen : m < (List.ofFn fun i : Fin S => decide (sel i = 1)).length := by simpa using h
  rw [List.take_succ_eq_append_getElem hlen, List.countP_append]
  simp only [List.getElem_ofFn]
  by_cases hb : sel ⟨m, h⟩ = 1 <;> simp [hb]

/-- A selected position ranks below every later position's count. -/
theorem selRank_lt_of_sel {sel : Fin S → K} {i : Fin S} (hi : sel i = 1) {m : ℕ}
    (him : (i : ℕ) < m) : selRank sel i < selRank sel m := by
  have h := selRank_succ sel i i.isLt
  simp only [Fin.eta, hi, ite_true] at h
  have := selRank_mono sel (show (i : ℕ) + 1 ≤ m by omega)
  omega

/-- Every rank below the count at `m` is the rank of a selected position before `m`. -/
theorem exists_selRank_eq (sel : Fin S → K) :
    ∀ m, m ≤ S → ∀ k < selRank sel m, ∃ i : Fin S, (i : ℕ) < m ∧ sel i = 1 ∧ selRank sel i = k := by
  intro m
  induction m with
  | zero => intro _ k hk; rw [selRank_zero] at hk; omega
  | succ m ih =>
    intro hm k hk
    rw [selRank_succ sel m (by omega)] at hk
    by_cases hlt : k < selRank sel m
    · obtain ⟨i, hi, hs, hr⟩ := ih (by omega) k hlt
      exact ⟨i, by omega, hs, hr⟩
    · by_cases hs : sel ⟨m, by omega⟩ = 1
      · refine ⟨⟨m, by omega⟩, by simp, hs, ?_⟩
        simp only [hs, ite_true] at hk
        show selRank sel m = k
        omega
      · simp [hs] at hk; omega

/-- **Matching.**  If `badPoly` vanishes, the selected tagged samples and the
claimed tagged outputs are the same multiset.  With labels in `F.E`, samples
below `2^w` and the rank fact `hrank`, every selected position `i` carries
`out (selRank i)`, and every slot is filled by a selected position of its rank. -/
theorem matching {F : SelectionField K S w} {sel label : Fin S → K} {stream : Fin S → ℕ}
    {outLabel : Fin n → K} {out : Fin n → ℕ}
    (hs : ∀ i, stream i < 2 ^ w) (ho : ∀ j, out j < 2 ^ w)
    (hbool : ∀ i, sel i = 0 ∨ sel i = 1) (hlabel : ∀ i, label i ∈ F.E)
    (houtLabel : ∀ j, outLabel j ∈ F.E)
    (hrank : ∀ i (j : Fin n), sel i = 1 → label i = outLabel j → selRank sel i = j)
    (hzero : badPoly F sel label stream outLabel out = 0) :
    (∀ i, sel i = 1 → ∃ j : Fin n, selRank sel i = j ∧ stream i = out j) ∧
      ∀ j : Fin n, ∃ i, sel i = 1 ∧ selRank sel i = j ∧ stream i = out j := by
  classical
  set Sel := Finset.univ.filter fun i : Fin S => sel i = 1
  set A : Fin S → K := fun i => enc F (label i) (stream i)
  set B : Fin n → K := fun j => enc F (outLabel j) (out j)
  have hroot : Sel.val.map A = Finset.univ.val.map B := by
    have h := congrArg Polynomial.roots (sub_eq_zero.mp hzero)
    rwa [candPoly_eq_filter label stream hbool, claimPoly, roots_prod_X_sub_C_image,
      roots_prod_X_sub_C_image] at h
  constructor
  · intro i hi
    have hmem : A i ∈ Finset.univ.val.map B := by
      rw [← hroot]
      exact Multiset.mem_map_of_mem A (Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi⟩)
    obtain ⟨j, -, hj⟩ := Multiset.mem_map.mp hmem
    obtain ⟨hl, hv⟩ := enc_injOn (hlabel i) (houtLabel j) (hs i) (ho j) hj.symm
    exact ⟨j, hrank i j hi hl, hv⟩
  · intro j
    have hmem : B j ∈ Sel.val.map A := by
      rw [hroot]
      exact Multiset.mem_map_of_mem B (Finset.mem_univ_val j)
    obtain ⟨i, hiSel, hi⟩ := Multiset.mem_map.mp hmem
    have hsel : sel i = 1 := (Finset.mem_filter.mp (Finset.mem_val.mp hiSel)).2
    obtain ⟨hl, hv⟩ := enc_injOn (hlabel i) (houtLabel j) (hs i) (ho j) hi
    exact ⟨i, hsel, hrank i j hsel hl, hv⟩

/-! #### The greedy scan -/

/-- One step of the greedy scan: accept sample `v` at the current rank
`L.length` while fewer than `n` samples have been accepted. -/
def scanStep (acc : ℕ → ℕ → Bool) (n : ℕ) (L : List ℕ) (v : ℕ) : List ℕ :=
  if L.length < n ∧ acc v L.length = true then L ++ [v] else L

/-- The samples the greedy scan accepts from a list, in order. -/
def scanList (acc : ℕ → ℕ → Bool) (n : ℕ) (l : List ℕ) : List ℕ :=
  l.foldl (scanStep acc n) []

/-- The greedy scan's first `n` accepted samples of `stream`, or `none` if it
accepts fewer.  `acc v t` is the scan's acceptance of sample `v` at rank `t`. -/
def scanFirst (acc : ℕ → ℕ → Bool) (stream : Fin S → ℕ) (n : ℕ) : Option (Fin n → ℕ) :=
  let L := scanList acc n (List.ofFn stream)
  if h : L.length = n then some fun j => L[j]'(by omega) else none

theorem scanFirst_eq_some_iff {acc : ℕ → ℕ → Bool} {stream : Fin S → ℕ} {out : Fin n → ℕ} :
    scanFirst acc stream n = some out ↔
      ∃ h : (scanList acc n (List.ofFn stream)).length = n,
        ∀ j : Fin n, out j = (scanList acc n (List.ofFn stream))[j]'(by omega) := by
  unfold scanFirst
  dsimp only
  split_ifs with h
  · simp only [Option.some.injEq, exists_prop_of_true h]
    exact ⟨fun he j => (congrFun he j).symm, fun he => funext fun j => (he j).symm⟩
  · simp only [false_iff]
    exact fun ⟨h', _⟩ => h h'

theorem length_foldl_scanStep_le {acc : ℕ → ℕ → Bool} {n : ℕ} :
    ∀ (l L : List ℕ), L.length ≤ n → (l.foldl (scanStep acc n) L).length ≤ n
  | [], _, h => h
  | v :: l, L, h => by
    rw [List.foldl_cons]
    apply length_foldl_scanStep_le l
    unfold scanStep
    split_ifs with hc
    · simpa using hc.1
    · exact h

/-- The greedy scan accepts at most `n` samples. -/
theorem scanList_length_le (acc : ℕ → ℕ → Bool) (n : ℕ) (l : List ℕ) :
    (scanList acc n l).length ≤ n :=
  length_foldl_scanStep_le l [] (Nat.zero_le n)

/-- Scanning one more sample of the stream is one more `scanStep`. -/
theorem scanList_take_succ (acc : ℕ → ℕ → Bool) (n : ℕ) (stream : Fin S → ℕ) {m : ℕ}
    (hm : m < S) :
    scanList acc n ((List.ofFn stream).take (m + 1)) =
      scanStep acc n (scanList acc n ((List.ofFn stream).take m)) (stream ⟨m, hm⟩) := by
  rw [List.take_succ_eq_append_getElem (by simpa using hm), List.getElem_ofFn, scanList,
    List.foldl_append, List.foldl_cons, List.foldl_nil, ← scanList]

/-- On a greedy selection, the scan of the first `m` samples lists the samples
of the selected positions before `m`, each at its rank. -/
theorem scanList_take {acc : ℕ → ℕ → Bool} {sel : Fin S → K} {stream : Fin S → ℕ}
    (hsel : ∀ i, sel i = 1 ↔ selRank sel i < n ∧ acc (stream i) (selRank sel i) = true) :
    ∀ m, m ≤ S → (scanList acc n ((List.ofFn stream).take m)).length = selRank sel m ∧
      ∀ i : Fin S, (i : ℕ) < m → sel i = 1 →
        (scanList acc n ((List.ofFn stream).take m))[selRank sel i]? = some (stream i) := by
  intro m
  induction m with
  | zero => intro _; simp [scanList, selRank_zero]
  | succ m ih =>
    intro hm
    obtain ⟨hlen, hget⟩ := ih (by omega)
    rw [scanList_take_succ acc n stream (show m < S by omega), selRank_succ sel m (by omega)]
    set L := scanList acc n ((List.ofFn stream).take m)
    have hcond : (L.length < n ∧ acc (stream ⟨m, by omega⟩) L.length = true) ↔
        sel ⟨m, by omega⟩ = 1 := by
      rw [hlen, hsel]
    unfold scanStep
    by_cases hs : sel ⟨m, by omega⟩ = 1
    · rw [ite_eq_left (hcond.mpr hs), ite_eq_left hs]
      refine ⟨by simp [hlen], fun i hi hsi => ?_⟩
      by_cases him : (i : ℕ) < m
      · have hlt := selRank_lt_of_sel hsi him
        rw [List.getElem?_append_left (by omega)]
        exact hget i him hsi
      · have hi' : i = ⟨m, by omega⟩ := Fin.ext (by simp; omega)
        rw [hi', List.getElem?_append_right (by simp [hlen]), hlen]
        simp
    · rw [ite_eq_right (fun h => hs (hcond.mp h)), ite_eq_right hs]
      refine ⟨by simp [hlen], fun i hi hsi => ?_⟩
      have him : (i : ℕ) < m := by
        by_contra hc
        have hi' : i = ⟨m, by omega⟩ := Fin.ext (by simp; omega)
        rw [hi'] at hsi
        exact hs hsi
      exact hget i him hsi

/-- **Soundness of a scan.**  With the scan's three facts (`hbool`, `hrank`,
`hgreedy`), labels in `F.E` and samples below `2^w`, a passing fingerprint
means `out` is the greedy scan's output, or `δ` lands in the bad event.
`hnS` is `param`; the rest are facts the instance's constraints give. -/
theorem sound {acc : ℕ → ℕ → Bool} {F : SelectionField K S w} {sel label : Fin S → K}
    {stream : Fin S → ℕ} {outLabel : Fin n → K} {out : Fin n → ℕ} {δ : K} (hnS : n ≤ S)
    (hs : ∀ i, stream i < 2 ^ w) (ho : ∀ j, out j < 2 ^ w)
    (hbool : ∀ i, sel i = 0 ∨ sel i = 1) (hlabel : ∀ i, label i ∈ F.E)
    (houtLabel : ∀ j, outLabel j ∈ F.E)
    (hrank : ∀ i (j : Fin n), sel i = 1 → label i = outLabel j → selRank sel i = j)
    (hgreedy : ∀ i : Fin S, selRank sel i < n → (sel i = 1 ↔ acc (stream i) (selRank sel i) = true))
    (h : Fingerprint F sel label stream outLabel out δ) :
    scanFirst acc stream n = some out ∨ (badEvent F sel label stream outLabel out hnS).BadAt δ := by
  by_cases hzero : badPoly F sel label stream outLabel out = 0
  · left
    obtain ⟨hA, hB⟩ := matching hs ho hbool hlabel houtLabel hrank hzero
    have hsel : ∀ i : Fin S, sel i = 1 ↔ selRank sel i < n ∧ acc (stream i) (selRank sel i) = true := by
      intro i
      constructor
      · intro hi
        obtain ⟨j, hj, -⟩ := hA i hi
        have hlt : selRank sel i < n := hj ▸ j.isLt
        exact ⟨hlt, (hgreedy i hlt).mp hi⟩
      · rintro ⟨hlt, ha⟩
        exact (hgreedy i hlt).mpr ha
    obtain ⟨hlen, hget⟩ := scanList_take hsel S le_rfl
    rw [List.take_of_length_le (by simp)] at hlen hget
    have hcount : selRank sel S = n := by
      apply le_antisymm
      · by_contra hc
        obtain ⟨i, -, hsi, hr⟩ := exists_selRank_eq sel S le_rfl n (by omega)
        obtain ⟨j, hj, -⟩ := hA i hsi
        have := j.isLt
        omega
      · rcases Nat.eq_zero_or_pos n with hn | hn
        · omega
        · obtain ⟨i, hsi, hr, -⟩ := hB ⟨n - 1, by omega⟩
          have := selRank_lt_of_sel hsi (m := S) i.isLt
          simp only at hr
          omega
    rw [scanFirst_eq_some_iff]
    refine ⟨hlen.trans hcount, fun j => ?_⟩
    obtain ⟨i, hsi, hr, hv⟩ := hB j
    have hg := hget i i.isLt hsi
    rw [hr, List.getElem?_eq_getElem (by omega)] at hg
    rw [← hv]
    exact (Option.some.inj hg).symm
  · right
    refine ⟨hzero, ?_⟩
    show (candPoly F sel label stream - claimPoly F outLabel out).eval δ = 0
    rw [eval_sub, h, sub_self]

/-- **Completeness of a scan.**  If `sel` is the greedy selection (`hsel`), each
selected position carries the slot label of its rank (`hlabel`), and `out` is
the greedy scan's output, the fingerprint passes at every `δ`.  These are the
honest advice's properties. -/
theorem complete {acc : ℕ → ℕ → Bool} (F : SelectionField K S w) {sel label : Fin S → K}
    {stream : Fin S → ℕ} {outLabel : Fin n → K} {out : Fin n → ℕ}
    (hbool : ∀ i, sel i = 0 ∨ sel i = 1)
    (hsel : ∀ i, sel i = 1 ↔ selRank sel i < n ∧ acc (stream i) (selRank sel i) = true)
    (hlabel : ∀ i (j : Fin n), sel i = 1 → selRank sel i = j → label i = outLabel j)
    (hout : scanFirst acc stream n = some out) (δ : K) :
    Fingerprint F sel label stream outLabel out δ := by
  classical
  obtain ⟨hlen, hget⟩ := scanList_take hsel S le_rfl
  rw [List.take_of_length_le (by simp)] at hlen hget
  obtain ⟨hn, hout⟩ := scanFirst_eq_some_iff.mp hout
  have hcount : selRank sel S = n := hlen.symm.trans hn
  have hrank : ∀ i : Fin S, sel i = 1 → selRank sel i < n := fun i hi => ((hsel i).mp hi).1
  unfold Fingerprint
  congr 1
  rw [candPoly_eq_filter label stream hbool, claimPoly]
  apply Finset.prod_bij (fun (i : Fin S) hi => (⟨selRank sel i, hrank i (Finset.mem_filter.mp hi).2⟩ : Fin n))
  · intro i _
    exact Finset.mem_univ _
  · intro i₁ h₁ i₂ h₂ heq
    have h₁' := (Finset.mem_filter.mp h₁).2
    have h₂' := (Finset.mem_filter.mp h₂).2
    have heq' : selRank sel i₁ = selRank sel i₂ := congrArg Fin.val heq
    by_contra hne
    rcases lt_or_gt_of_ne (fun h => hne (Fin.ext h)) with hlt | hlt
    · have := selRank_lt_of_sel h₁' hlt; omega
    · have := selRank_lt_of_sel h₂' hlt; omega
  · intro j _
    obtain ⟨i, -, hsi, hr⟩ := exists_selRank_eq sel S le_rfl j (by omega)
    exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hsi⟩, Fin.ext hr⟩
  · intro i hi
    have hsi := (Finset.mem_filter.mp hi).2
    have hg := hget i i.isLt hsi
    rw [List.getElem?_eq_getElem (by have := hrank i hsi; omega)] at hg
    have hv : out ⟨selRank sel i, hrank i hsi⟩ = stream i := by
      rw [hout]
      exact Option.some.inj hg
    rw [hlabel i ⟨selRank sel i, hrank i hsi⟩ hsi rfl, hv]

end SelectScan

namespace Falcon512.SelectFirstN.Model

variable {K : Type*} [Field K] [DecidableEq K] {S n w : ℕ}

export SelectScan (mux muxP enc)

/-- The acceptance predicate as a field bit: `[sample < bound]`. -/
def accept (bound sample : ℕ) : K := if sample < bound then 1 else 0

/-- Whether position `i` is selected: accepted, and for `i ≥ n` also not `full`. -/
def selected (n bound : ℕ) (stream : Fin S → ℕ) (route : Fin S → Route K) (i : Fin S) : K :=
  if (i : ℕ) < n then accept bound (stream i)
  else accept bound (stream i) * (1 - (route i).full)

/-- The candidate side: the scan's `candPoly` with the counter as label. -/
noncomputable def candPoly (n : ℕ) (F : SelectionField K S w) (bound : ℕ) (stream : Fin S → ℕ)
    (route : Fin S → Route K) : K[X] :=
  SelectScan.candPoly F (selected n bound stream route) (fun i => (route i).count_enc) stream

/-- The claimed side, with slot labels `g^j`. -/
noncomputable def claimPoly (F : SelectionField K S w) (out : Fin n → ℕ) : K[X] :=
  SelectScan.claimPoly F (fun j => F.g ^ (j : ℕ)) out

/-- `candPoly - claimPoly`: its evaluation at the challenge `δ` is `0` exactly
when the permutation check's fingerprint matches. -/
noncomputable def badPoly (n : ℕ) (F : SelectionField K S w) (bound : ℕ) (stream : Fin S → ℕ)
    (out : Fin n → ℕ) (route : Fin S → Route K) : K[X] :=
  candPoly n F bound stream route - claimPoly F out

/-- `route[0].count_enc = 1`: the counter starts at slot `0`. -/
def Initial (route : Fin S → Route K) : Prop :=
  ∀ i : Fin S, (i : ℕ) = 0 → (route i).count_enc = 1

/-- For every position at or past `n`, `route[i].full` is a bit, and it is
forced to `0` unless the counter has reached `g^n`. -/
def Done (F : SelectionField K S w) (n : ℕ) (route : Fin S → Route K) : Prop :=
  ∀ i : Fin S, n ≤ (i : ℕ) →
    (route i).full * ((route i).full - 1) = 0 ∧
      (route i).full * ((route i).count_enc - F.g ^ n) = 0

/-- The counter advances by a factor of `g` exactly on a selected position, and
stays unchanged otherwise. -/
def Step (F : SelectionField K S w) (n bound : ℕ) (stream : Fin S → ℕ)
    (route : Fin S → Route K) : Prop :=
  ∀ (i : Fin S) (hi : (i : ℕ) + 1 < S),
    (route ⟨(i : ℕ) + 1, hi⟩).count_enc
      = (route i).count_enc * SelectScan.mux (selected n bound stream route i) F.g 1

/-- The fingerprint check: `candPoly` and `claimPoly` agree at `δ`. -/
def Fingerprint (F : SelectionField K S w) (n bound : ℕ) (stream : Fin S → ℕ) (out : Fin n → ℕ)
    (route : Fin S → Route K) (δ : K) : Prop :=
  (candPoly n F bound stream route).eval δ = (claimPoly F out).eval δ

/-- The semantic constraint groups established by the wire circuit. These are
propositions about the checked trace, not a second executable gadget. -/
structure Constraints (F : SelectionField K S w) (bound : ℕ)
    (stream : Fin S → ℕ) (out : Fin n → ℕ) (route : Fin S → Route K) (δ : K) : Prop where
  initial : Initial route
  done : Done F n route
  step : Step F n bound stream route
  fingerprint : Fingerprint F n bound stream out route δ

omit [DecidableEq K] in
/-- The candidate and claimed fingerprint products evaluate their polynomials
at `δ`. The wire circuit uses this identity to establish `Fingerprint`. -/
theorem fingerprint_products (F : SelectionField K S w) (bound : ℕ) (stream : Fin S → ℕ)
    (out : Fin n → ℕ) (route : Fin S → Route K) (δ : K) :
    (List.finRange S).foldl
        (fun acc i => acc * SelectScan.mux (selected n bound stream route i)
          (δ - SelectScan.enc F (route i).count_enc (stream i)) 1) 1
      = (candPoly n F bound stream route).eval δ ∧
    (List.finRange n).foldl (fun acc (j : Fin n) => acc * (δ - SelectScan.enc F (F.g ^ (j : ℕ)) (out j))) 1
      = (claimPoly F out).eval δ :=
  SelectScan.fingerprint_products F _ _ stream _ out δ

/-- The bad event for the permutation check's fingerprinting: the scan's event
with Falcon's labels. `hnS` supplies the degree bound. -/
noncomputable def badEvent (F : SelectionField K S w) (bound : ℕ) (stream : Fin S → ℕ)
    (out : Fin n → ℕ) (route : Fin S → Route K) (hnS : n ≤ S) : ChallengeEvent K :=
  SelectScan.badEvent F (selected n bound stream route) (fun i => (route i).count_enc) stream
    (fun j => F.g ^ (j : ℕ)) out hnS

/-- The number of positions among the first `m` that `selected` marks `1`: the
rank a selection at position `m` (if any) would receive. -/
def selRank (n bound : ℕ) (stream : Fin S → ℕ)
    (route : Fin S → Route K) (m : ℕ) : ℕ :=
  SelectScan.selRank (selected n bound stream route) m

theorem selRank_zero (n bound : ℕ) (stream : Fin S → ℕ)
    (route : Fin S → Route K) :
    selRank n bound stream route 0 = 0 :=
  SelectScan.selRank_zero _

theorem selRank_le_self (n bound : ℕ) (stream : Fin S → ℕ)
    (route : Fin S → Route K) (m : ℕ) :
    selRank n bound stream route m ≤ m :=
  SelectScan.selRank_le_self _ m

theorem selRank_mono (n bound : ℕ) (stream : Fin S → ℕ)
    (route : Fin S → Route K) :
    Monotone (selRank n bound stream route) :=
  SelectScan.selRank_mono _

theorem selRank_succ (n bound : ℕ) (stream : Fin S → ℕ)
    (route : Fin S → Route K) (m : ℕ) (h : m < S) :
    selRank n bound stream route (m + 1)
      = selRank n bound stream route m
        + (if selected n bound stream route ⟨m, h⟩ = 1 then 1 else 0) :=
  SelectScan.selRank_succ _ m h

omit [DecidableEq K] in
/-- Under `Done`, `selected` takes only the values `0` and `1`. -/
theorem selected_bool {n : ℕ} (bound : ℕ) (stream : Fin S → ℕ) {F : SelectionField K S w}
    {route : Fin S → Route K} (hDone : Done F n route) (i : Fin S) :
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
    {route : Fin S → Route K} {i : Fin S}
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
    {route : Fin S → Route K}
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
    {route : Fin S → Route K}
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

/-- Under `Initial`, `Done`, `Step`, while `selRank` at `m` is still below `n`,
it agrees with `acceptedBefore` at `m`: the `min` in `acceptedBefore`'s
definition is inactive, because the hypothesis already keeps the raw count
below `n`. -/
theorem selRank_eq_countP_take_of_lt {n bound : ℕ} {F : SelectionField K S w} {stream : Fin S → ℕ}
    {route : Fin S → Route K}
    (hInit : Initial route) (hDone : Done F n route) (hStep : Step F n bound stream route)
    (hnS : n ≤ S) :
    ∀ m, m ≤ S → selRank n bound stream route m < n →
      selRank n bound stream route m = acceptedBefore n bound stream m := by
  have hraw : ∀ m, m ≤ S → selRank n bound stream route m < n →
      selRank n bound stream route m
        = ((List.ofFn stream).take m).countP (fun v => decide (v < bound)) := by
    intro m
    induction m with
    | zero => intro _ _; rw [selRank_zero]; simp
    | succ m ih =>
      intro hmS hlt
      have hmS' : m < S := by omega
      have hltm : selRank n bound stream route m < n := by
        have hmono := selRank_mono n bound stream route (show m ≤ m + 1 by omega)
        omega
      have ihm := ih (le_of_lt hmS') hltm
      have hiff := selected_iff_accept_of_lt hInit hDone hStep hnS
        ⟨m, hmS'⟩ hltm
      have hcbsucc : ((List.ofFn stream).take (m + 1)).countP (fun v => decide (v < bound))
          = ((List.ofFn stream).take m).countP (fun v => decide (v < bound))
            + (if stream ⟨m, hmS'⟩ < bound then 1 else 0) := by
        have hlen : m < (List.ofFn stream).length := by simpa using hmS'
        rw [List.take_succ_eq_append_getElem hlen, List.countP_append]
        simp only [List.getElem_ofFn]
        by_cases hb' : stream ⟨m, hmS'⟩ < bound
        · simp [hb']
        · simp [hb']
      rw [selRank_succ n bound stream route m hmS', hcbsucc, ihm]
      by_cases hb : stream ⟨m, hmS'⟩ < bound
      · have hsel : selected n bound stream route ⟨m, hmS'⟩ = 1 := hiff.mpr hb
        simp [hsel, hb]
      · have hsel : selected n bound stream route ⟨m, hmS'⟩ ≠ 1 := fun hc => hb (hiff.mp hc)
        simp [hsel, hb]
  intro m hmS hlt
  have h := hraw m hmS hlt
  have hlt' : ((List.ofFn stream).take m).countP (fun v => decide (v < bound)) < n := by
    rw [← h]; exact hlt
  unfold acceptedBefore
  rw [h, min_eq_left hlt'.le]

/-- Soundness: the constraints imply that `out` is exactly the first `n`
stream samples below `bound`, or the challenge `δ` lands in the bad event for
`badPoly`.

Hypotheses: `hnS` is `param` (`n ≤ S`). `hs` is `gadget:hash`: the samples are `w`-bit readouts of
the hash gadget's output bits. `ho` is `gadget:` Booleanity of the committed bits of `out`. -/
theorem sound {F : SelectionField K S w} {bound : ℕ}
    {stream : Fin S → ℕ} {out : Fin n → ℕ} {route : Fin S → Route K} {δ : K}
    (hnS : n ≤ S)
    (hs : ∀ i, stream i < 2 ^ w) (ho : ∀ j, out j < 2 ^ w)
    (h : Constraints F bound stream out route δ) :
    firstAccepted (fun v => decide (v < bound)) stream n = some out
    ∨ ChallengeEvent.BadAt (badEvent F bound stream out route hnS) δ := by
  obtain ⟨hInit, hDone, hStep, hFing⟩ := h
  by_cases hbad : badPoly n F bound stream out route = 0
  · left
    have hgpow_mem : ∀ k : ℕ, F.g ^ k ∈ F.E := fun k => Subfield.pow_mem F.E F.g_mem k
    have hcount : ∀ i : Fin S, (route i).count_enc = F.g ^ selRank n bound stream route i :=
      fun i => count_enc_eq_pow_selRank hInit hDone hStep i i.isLt
    obtain ⟨-, hB⟩ := SelectScan.matching (sel := selected n bound stream route)
      (label := fun i => (route i).count_enc) (outLabel := fun j : Fin n => F.g ^ (j : ℕ))
      hs ho (selected_bool bound stream hDone)
      (fun i => (hcount i).symm ▸ hgpow_mem _) (fun _ => hgpow_mem _)
      (fun i j _ hl => F.g_order _ _ ((selRank_le_self n bound stream route i).trans i.isLt.le)
        (j.isLt.le.trans hnS) ((hcount i).symm.trans hl)) hbad
    choose φ hφselected hφselRank hφstream using hB
    have hφaccept : ∀ j, stream (φ j) < bound := fun j =>
      selected_eq_one_imp_accept (hφselected j)
    have hφacceptedBefore : ∀ j, acceptedBefore n bound stream (φ j : ℕ) = (j : ℕ) := by
      intro j
      rw [← hφselRank j]
      exact (selRank_eq_countP_take_of_lt hInit hDone hStep hnS
        (φ j : ℕ) (φ j).isLt.le (lt_of_eq_of_lt (hφselRank j) j.isLt)).symm
    have hcountjeq : ∀ j : Fin n,
        ((List.ofFn stream).take (φ j : ℕ)).countP (fun v => decide (v < bound)) = (j : ℕ) := by
      intro j
      have hacc := hφacceptedBefore j
      unfold acceptedBefore at hacc
      have hjlt : (j : ℕ) < n := j.isLt
      omega
    have hkey : ∀ j : Fin n, ∃ hj : (j : ℕ) < (List.filter (fun v => decide (v < bound))
        (List.ofFn stream)).length,
        (List.filter (fun v => decide (v < bound)) (List.ofFn stream))[(j : ℕ)]'hj = out j := by
      intro j
      have hpi : (fun v => decide (v < bound)) (List.ofFn stream)[(φ j : ℕ)] = true := by
        rw [List.getElem_ofFn]
        exact decide_eq_true (hφaccept j)
      obtain ⟨hj, heq⟩ := List.getElem_filter_of_countP_take (fun v => decide (v < bound))
        (List.ofFn stream) (φ j : ℕ) (by simp) hpi
      rw [List.getElem_ofFn] at heq
      have hcj := hcountjeq j
      generalize hgv : ((List.ofFn stream).take (φ j : ℕ)).countP
          (fun v => decide (v < bound)) = v at hj heq hcj
      subst hcj
      refine ⟨hj, ?_⟩
      rw [heq]
      exact hφstream j
    have hlenge : n ≤ (List.filter (fun v => decide (v < bound)) (List.ofFn stream)).length := by
      rcases Nat.eq_zero_or_pos n with hn0 | hnpos
      · omega
      · obtain ⟨hj, -⟩ := hkey ⟨n - 1, by omega⟩
        simp only at hj
        omega
    rw [GordieHowe.firstAccepted_eq_some_iff]
    refine ⟨hlenge, fun j => ?_⟩
    obtain ⟨hj, heq⟩ := hkey j
    exact heq.symm
  · right
    refine ⟨hbad, ?_⟩
    show (candPoly n F bound stream route - claimPoly F out).eval δ = 0
    rw [eval_sub, hFing, sub_self]

/-- The honest advice: the route built from `acceptedBefore`, giving each
position the counter `g^(acceptedBefore i)` and setting `full` exactly once
the count reaches `n`. -/
def hashToPointRoute (n : ℕ) (F : SelectionField K S w) (bound : ℕ) (stream : Fin S → ℕ) :
    Fin S → Route K :=
  fun i =>
    let k' := acceptedBefore n bound stream (i : ℕ)
    { count_enc := F.g ^ k', full := if k' = n then 1 else 0 }

omit [DecidableEq K] in
/-- Fewer than `n` stream positions cannot have filled the first `n` outputs. -/
theorem hashToPointRoute_full_zero (n : ℕ) (F : SelectionField K S w) (bound : ℕ)
    (stream : Fin S → ℕ) (i : Fin S) (hi : i.val < n) :
    (hashToPointRoute n F bound stream i).full = 0 := by
  have h := (acceptedBefore_le_self n bound stream i).trans_lt hi
  simp only [hashToPointRoute, ne_of_lt h, ↓reduceIte]

omit [DecidableEq K] in
theorem hashToPointRoute_full_bool (n : ℕ) (F : SelectionField K S w) (bound : ℕ)
    (stream : Fin S → ℕ) (i : Fin S) :
    (hashToPointRoute n F bound stream i).full = 0 ∨
      (hashToPointRoute n F bound stream i).full = 1 := by
  dsimp only [hashToPointRoute]
  split <;> simp

omit [DecidableEq K] in
/-- Under `hashToPointRoute`, `selected` at `i` is `1` exactly when `stream i`
is below `bound` and fewer than `n` samples have been accepted before `i`. -/
theorem selected_honest_eq (n : ℕ) (F : SelectionField K S w) (bound : ℕ) (stream : Fin S → ℕ)
    (i : Fin S) :
    selected n bound stream (hashToPointRoute n F bound stream) i
      = if stream i < bound ∧ acceptedBefore n bound stream (i : ℕ) < n
        then (1 : K) else 0 := by
  unfold selected hashToPointRoute accept
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
/-- `hashToPointRoute` satisfies `Initial`. -/
theorem hashToPointRoute_initial (n : ℕ) (F : SelectionField K S w) (bound : ℕ) (stream : Fin S → ℕ) :
    Initial (hashToPointRoute n F bound stream) := by
  intro i hi
  show F.g ^ acceptedBefore n bound stream (i : ℕ) = 1
  rw [hi, acceptedBefore_zero]
  exact pow_zero _

omit [DecidableEq K] in
/-- `hashToPointRoute` satisfies `Done`. -/
theorem hashToPointRoute_done (n : ℕ) (F : SelectionField K S w) (bound : ℕ) (stream : Fin S → ℕ) :
    Done F n (hashToPointRoute n F bound stream) := by
  intro i _
  unfold hashToPointRoute
  dsimp only
  by_cases h : acceptedBefore n bound stream (i : ℕ) = n
  · simp [h]
  · simp [h]

omit [DecidableEq K] in
/-- `hashToPointRoute` satisfies `Step`. -/
theorem hashToPointRoute_step (n : ℕ) (F : SelectionField K S w) (bound : ℕ) (stream : Fin S → ℕ) :
    Step F n bound stream (hashToPointRoute n F bound stream) := by
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
/-- Under `hashToPointRoute`, `candPoly` is the product of `X - enc(…)` over
exactly the positions whose sample is below `bound` and precede the `n`-th
acceptance. -/
theorem candPoly_honest_eq_filter (n : ℕ) (F : SelectionField K S w) (bound : ℕ) (stream : Fin S → ℕ) :
    candPoly n F bound stream (hashToPointRoute n F bound stream) =
    ∏ i ∈ (Finset.univ.filter fun i : Fin S =>
        stream i < bound ∧ acceptedBefore n bound stream (i : ℕ) < n),
      (Polynomial.X - C (SelectScan.enc F (hashToPointRoute n F bound stream i).count_enc
        (stream i))) := by
  rw [candPoly, SelectScan.candPoly]
  have step : ∀ i : Fin S,
      SelectScan.muxP (selected n bound stream (hashToPointRoute n F bound stream) i)
        (Polynomial.X - C (SelectScan.enc F (hashToPointRoute n F bound stream i).count_enc (stream i))) 1
      = if stream i < bound ∧ acceptedBefore n bound stream (i : ℕ) < n
        then (Polynomial.X
          - C (SelectScan.enc F (hashToPointRoute n F bound stream i).count_enc (stream i)))
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
theorem hashToPointRoute_stream_eq_out {bound : ℕ}
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
theorem hashToPointRoute_candPoly_eq_claimPoly (n : ℕ) (F : SelectionField K S w) {bound : ℕ}
    {stream : Fin S → ℕ} {out : Fin n → ℕ}
    (hout : firstAccepted (fun v => decide (v < bound)) stream n = some out) :
    candPoly n F bound stream (hashToPointRoute n F bound stream)
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
    have hstream_eq := hashToPointRoute_stream_eq_out hout
      ⟨acceptedBefore n bound stream (a : ℕ), hc.2⟩ rfl hc.1
    unfold SelectScan.enc
    rw [hstream_eq]
    congr 2

omit [DecidableEq K] in
/-- Completeness: `hashToPointRoute` satisfies the constraint groups for the
honestly first-`n`-accepted output `out`, for every challenge `δ`.

Hypotheses: `hout` is the honest input (the advice generator's success: `out`
is `firstAccepted`'s output). `n` is implicit; it is read off `hout`'s type
(`out : Fin n → ℕ` there). `F` stays explicit: nothing earlier in the
argument list determines it. -/
theorem complete {n : ℕ} (F : SelectionField K S w) {bound : ℕ} {stream : Fin S → ℕ}
    {out : Fin n → ℕ}
    (hout : firstAccepted (fun v => decide (v < bound)) stream n = some out)
    (δ : K) :
    Constraints F bound stream out (hashToPointRoute n F bound stream) δ := by
  refine ⟨hashToPointRoute_initial n F bound stream, hashToPointRoute_done n F bound stream,
    hashToPointRoute_step n F bound stream, ?_⟩
  show (candPoly n F bound stream (hashToPointRoute n F bound stream)).eval δ
      = (claimPoly F out).eval δ
  rw [hashToPointRoute_candPoly_eq_claimPoly n F hout]

end Falcon512.SelectFirstN.Model

end GordieHowe
