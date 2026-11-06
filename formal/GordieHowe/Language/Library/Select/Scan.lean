-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.LinearCombination
public import GordieHowe.Foundations.Probability.ChallengeEvent
public import GordieHowe.Language.Library.Select.Field
public import GordieHowe.Language.Library.Select.First
public import GordieHowe.Foundations.ToMathlib.List
public import GordieHowe.Foundations.ToMathlib.Polynomial

@[expose] public section

/-!
# Natural-number semantics of the ordered selection gadget

`SelectScan` proves the permutation argument for any scan: `SelectScan.sound`
and `SelectScan.complete` against the greedy scan `SelectScan.scanFirst`.  The
listing below is the generic gadget and the scan below a fixed bound; ML-DSA's rising-threshold
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

gadget SelectFirstCutoff(stream, out, route, bound, δ):
    SelectFirst(stream, out, route, CutoffScan(|out|, bound), δ)

scan CutoffScan(n, bound):
    AssertInitial(state):
        assert state.count_enc == 1

    Accept(sample, state):
        return sample < bound

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

`CutoffScan`'s natural-number model, its soundness and its completeness are
`GordieHowe/Language/Library/Select/Cutoff.lean`.
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
`badPoly`.  The fixed bound (`SelectFirstCutoff.Model`) and ML-DSA's rising
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

/-- **A scan whose acceptance ignores the rank** keeps the first `n` accepted samples. -/
theorem foldl_scanStep_const (a : ℕ → Bool) (n : ℕ) :
    ∀ (l L : List ℕ), L.length ≤ n →
      l.foldl (scanStep (fun v _ => a v) n) L = (L ++ l.filter a).take n
  | [], L, h => by simp [List.take_of_length_le h]
  | v :: l, L, h => by
    rw [List.foldl_cons]
    by_cases hv : a v = true
    · by_cases hL : L.length < n
      · have hs : scanStep (fun v _ => a v) n L v = L ++ [v] := by simp [scanStep, hL, hv]
        rw [hs, foldl_scanStep_const a n l (L ++ [v]) (by simp; omega),
          List.filter_cons_of_pos hv, List.append_assoc, List.singleton_append]
      · have hs : scanStep (fun v _ => a v) n L v = L := by simp [scanStep, hL]
        rw [hs, foldl_scanStep_const a n l L h, List.filter_cons_of_pos hv,
          List.take_append_of_le_length (by omega), List.take_append_of_le_length (by omega)]
    · have hs : scanStep (fun v _ => a v) n L v = L := by simp [scanStep, hv]
      rw [hs, foldl_scanStep_const a n l L h, List.filter_cons_of_neg hv]

/-- **The greedy scan of a rank-independent acceptance** is the first `n` accepted samples. -/
theorem scanFirst_const (a : ℕ → Bool) (stream : Fin S → ℕ) (n : ℕ) :
    scanFirst (fun v _ => a v) stream n = firstAccepted a stream n := by
  unfold scanFirst firstAccepted scanList
  simp only [foldl_scanStep_const a n _ [] (Nat.zero_le n), List.nil_append, List.length_take]
  by_cases h : n ≤ ((List.ofFn stream).filter a).length
  · rw [dif_pos (show min n ((List.ofFn stream).filter a).length = n by omega), dif_pos h]
    simp
  · rw [dif_neg (show ¬ min n ((List.ofFn stream).filter a).length = n by omega), dif_neg h]

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

end GordieHowe
