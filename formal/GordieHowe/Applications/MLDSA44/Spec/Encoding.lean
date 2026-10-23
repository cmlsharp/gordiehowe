-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Applications.MLDSA44.Spec.Basic
public import GordieHowe.Foundations.ToMathlib.ForIn
public import GordieHowe.Foundations.ToMathlib.Vector
public import LatticeCrypto.MLDSA.Concrete.LawBounds
import all LatticeCrypto.MLDSA.Concrete.Rounding
import all LatticeCrypto.MLDSA.Concrete.Encoding

@[expose] public section

/-!
# ML-DSA signature codec

The byte-level facts the ML-DSA extraction needs about the vendored FIPS 204 codec
(`Vendor/LatticeCrypto/MLDSA/Concrete/Encoding.lean`), mirroring
`GordieHowe/Applications/Falcon512/Spec/Encoding.lean`:

- `hintBitPack_eq`: the bytes `hintBitPack` (FIPS 204 Algorithm 20) produces when the total hint
  weight is at most `ω`, as the closed form `hintBytes`;
- `hintBitUnpack_hintBitPack`: `hintBitUnpack` (Algorithm 21) inverts it;
- `sigDecode_sigEncode`: the signature roundtrip (Algorithms 26 and 27) for `z` in the packing
  window `(-γ₁, γ₁]` and hint weight at most `ω`;
- `extract_accepted_signature`: a semantic signature that verifies (`Verifies`) encodes to bytes
  that verify (`VerifiesBytes`). The packing window and hint weight follow from Algorithm 8's own checks;
- `w1Encode_bit`: the bit layout of `w1Encode` (Algorithm 28) that the H circuit reads.

Every hint polynomial `Vector Bool 256` has a unique encoding, so the circuit's hint check needs only
the weight bound; FIPS 204's canonical-form checks in `HintBitUnpack` (strictly increasing indices
within a polynomial, nondecreasing counts, zero padding) hold for `hintBitPack`'s output.
-/

namespace GordieHowe.MLDSA44

open _root_.MLDSA _root_.MLDSA.Concrete

/-! ### The hint codec -/

variable {p : MLDSA.Params}

/-- Polynomial `i` of a hint vector, read as `hintBitPack` and `hintBitUnpack` read it:
all-false past the end. -/
def hintPoly (h : Vector Hint p.k) (i : ℕ) : Hint := h.toArray.getD i (Vector.ofFn fun _ => false)

/-- The set positions of one hint polynomial, in increasing order. -/
def hintSupport (hi : Hint) : List ℕ := (List.range ringDegree).filter fun j => hi.toArray.getD j false

/-- The set positions of hint polynomials `0, …, n - 1`, concatenated. -/
def hintPositions (h : Vector Hint p.k) (n : ℕ) : List ℕ :=
  (List.range n).flatMap fun i => hintSupport (hintPoly h i)

theorem hintPositions_succ (h : Vector Hint p.k) (n : ℕ) :
    hintPositions h (n + 1) = hintPositions h n ++ hintSupport (hintPoly h n) := by
  simp [hintPositions, List.range_succ, List.flatMap_append]

theorem hintPositions_length_mono (h : Vector Hint p.k) {m n : ℕ} (hmn : m ≤ n) :
    (hintPositions h m).length ≤ (hintPositions h n).length := by
  induction n with
  | zero => simp [Nat.le_zero.mp hmn]
  | succ n ih =>
    rcases Nat.of_le_succ hmn with h' | h'
    · rw [hintPositions_succ, List.length_append]; have := ih h'; omega
    · rw [h']

def packInner (p : MLDSA.Params) (hi : Hint) (s : Array Byte × ℕ) (j : ℕ) : Array Byte × ℕ :=
  if hi.toArray.getD j false then
    (if s.2 < p.omega then s.1.set! s.2 j.toUInt8 else s.1, s.2 + 1)
  else s

def packOuter (p : MLDSA.Params) (h : Vector Hint p.k) (s : Array Byte × ℕ) (i : ℕ) :
    Array Byte × ℕ :=
  let r := (List.range ringDegree).foldl (packInner p (hintPoly h i)) s
  (r.1.set! (p.omega + i) r.2.toUInt8, r.2)

theorem hintBitPack_eq_foldl (p : MLDSA.Params) (h : Vector Hint p.k) :
    hintBitPack p h = ByteArray.mk ((List.range p.k).foldl (packOuter p h)
      (Array.replicate (p.omega + p.k) 0, 0)).1 := by
  unfold hintBitPack
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size, Nat.sub_zero,
    Nat.add_sub_cancel, Nat.div_one, ← List.range_eq_range']
  congr 1
  rw [List.forIn_id_eq_foldl _ _ _ (packOuter p h)]
  · rfl
  intro i s
  simp only [packOuter]
  rw [List.forIn_id_eq_foldl _ _ _ (packInner p _)]
  · rfl
  intro j s
  rcases s with ⟨o, c⟩
  simp only [packInner, hintPoly]
  split_ifs <;> simp_all <;> rfl

theorem set_length_append {α : Type*} (P T : List α) (n : ℕ) (x y : α) :
    (P ++ (y :: List.replicate n y) ++ T).set P.length x = P ++ [x] ++ List.replicate n y ++ T := by
  rw [List.append_assoc, List.set_append_right _ _ (le_refl _), Nat.sub_self]
  simp

theorem packInner_foldl (p : MLDSA.Params) (hi : Hint) (l : List ℕ) (P T : List Byte)
    (hP : P.length + (l.filter fun j => hi.toArray.getD j false).length ≤ p.omega) :
    l.foldl (packInner p hi) (Array.mk (P ++ List.replicate (p.omega - P.length) 0 ++ T), P.length) =
      (Array.mk (P ++ (l.filter fun j => hi.toArray.getD j false).map Nat.toUInt8 ++
          List.replicate (p.omega - (P.length + (l.filter fun j => hi.toArray.getD j false).length)) 0
          ++ T),
        P.length + (l.filter fun j => hi.toArray.getD j false).length) := by
  induction l generalizing P with
  | nil => simp
  | cons j l ih =>
    rw [List.foldl_cons]
    by_cases hj : hi.toArray.getD j false = true
    · rw [List.filter_cons_of_pos (p := fun j => hi.toArray.getD j false) hj] at hP ⊢
      simp only [List.length_cons] at hP
      have hlt : P.length < p.omega := by omega
      have hstep : packInner p hi (Array.mk (P ++ List.replicate (p.omega - P.length) 0 ++ T),
          P.length) j = (Array.mk ((P ++ [j.toUInt8]) ++
            List.replicate (p.omega - (P ++ [j.toUInt8]).length) 0 ++ T),
            (P ++ [j.toUInt8]).length) := by
        have hrep : List.replicate (p.omega - P.length) (0 : Byte) =
            0 :: List.replicate (p.omega - (P ++ [j.toUInt8]).length) 0 := by
          rw [List.length_append, List.length_singleton, ← List.replicate_succ]; congr 1; omega
        simp only [packInner, hj, ite_true, hlt]
        refine Prod.ext ?_ (by simp)
        apply Array.ext'
        rw [Array.set!_eq_setIfInBounds, Array.toList_setIfInBounds, hrep, set_length_append]
      rw [hstep, ih (P ++ [j.toUInt8]) (by rw [List.length_append, List.length_singleton]; omega)]
      have e : ∀ a b : ℕ, a + 1 + b = a + (b + 1) := by omega
      simp only [List.length_append, List.map_cons, List.length_cons, List.append_assoc,
        List.singleton_append, List.length_nil, Nat.zero_add, e]
    · rw [List.filter_cons_of_neg (p := fun j => hi.toArray.getD j false) hj] at hP ⊢
      have hstep : packInner p hi (Array.mk (P ++ List.replicate (p.omega - P.length) 0 ++ T),
          P.length) j = (Array.mk (P ++ List.replicate (p.omega - P.length) 0 ++ T), P.length) := by
        simp [packInner, hj]
      rw [hstep, ih P hP]

theorem packOuter_foldl (h : Vector Hint p.k) {n : ℕ} (hn : n ≤ p.k)
    (hω : (hintPositions h n).length ≤ p.omega) :
    (List.range n).foldl (packOuter p h) (Array.replicate (p.omega + p.k) 0, 0) =
      (Array.mk ((hintPositions h n).map Nat.toUInt8 ++
          List.replicate (p.omega - (hintPositions h n).length) 0 ++
          ((List.range n).map (fun i => (hintPositions h (i + 1)).length.toUInt8) ++
            List.replicate (p.k - n) 0)),
        (hintPositions h n).length) := by
  induction n with
  | zero =>
    simp only [List.range_zero, List.foldl_nil, hintPositions, List.flatMap_nil, List.map_nil,
      List.length_nil, Nat.sub_zero, List.nil_append]
    refine Prod.ext ?_ rfl
    apply Array.ext'
    simp only [Array.toList_replicate, List.replicate_append_replicate]
  | succ n ih =>
    have hn' : n ≤ p.k := by omega
    have hmono := hintPositions_length_mono h (Nat.le_succ n)
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil,
      ih hn' (le_trans hmono hω)]
    have hsucc := hintPositions_succ h n
    have hlen : (hintPositions h (n + 1)).length =
        (hintPositions h n).length + (hintSupport (hintPoly h n)).length := by
      rw [hsucc, List.length_append]
    simp only [packOuter]
    have hP := packInner_foldl p (hintPoly h n) (List.range ringDegree)
      ((hintPositions h n).map Nat.toUInt8)
      ((List.range n).map (fun i => (hintPositions h (i + 1)).length.toUInt8) ++
        List.replicate (p.k - n) 0)
      (by rw [List.length_map]; unfold hintSupport at hlen; omega)
    rw [List.length_map] at hP
    rw [hP]
    dsimp only
    have hS : (List.range ringDegree).filter (fun j => (hintPoly h n).toArray.getD j false) =
        hintSupport (hintPoly h n) := rfl
    rw [hS, ← hlen]
    refine Prod.ext ?_ rfl
    apply Array.ext'
    have hA : ((hintPositions h n).map Nat.toUInt8 ++ (hintSupport (hintPoly h n)).map Nat.toUInt8 ++
        List.replicate (p.omega - (hintPositions h (n + 1)).length) (0 : Byte)).length = p.omega := by
      simp only [List.length_append, List.length_map, List.length_replicate]; omega
    have hB : ((List.range n).map (fun i => (hintPositions h (i + 1)).length.toUInt8)).length = n := by
      simp
    rw [Array.set!_eq_setIfInBounds, Array.toList_setIfInBounds,
      List.set_append_right _ _ (by omega), hA, Nat.add_sub_cancel_left,
      show p.k - n = (p.k - (n + 1)) + 1 by omega, List.replicate_succ,
      List.set_append_right _ _ (by omega), hB, Nat.sub_self, List.set_cons_zero]
    simp only [hsucc, List.map_append, List.map_cons, List.map_nil, List.append_assoc,
      List.cons_append, List.nil_append]


/-- `hintWeight` counts the set positions. -/
theorem hintWeight_eq_length (hi : Hint) : hintWeight hi = (hintSupport hi).length := by
  have hfold : ∀ (l : List Bool) (a : ℕ),
      l.foldl (fun acc b => acc + cond b 1 0) a = a + l.count true := by
    intro l
    induction l with
    | nil => simp
    | cons b l ih =>
      intro a
      rw [List.foldl_cons, ih, List.count_cons]
      cases b <;> simp
      omega
  unfold hintWeight hintSupport
  rw [hfold, Nat.zero_add, Vector.toList_eq_map_range_getD hi false, List.count_eq_countP,
    List.countP_map, List.countP_eq_length_filter]
  congr 1
  apply List.filter_congr
  intro j _
  simp

/-- `hintWeightVec` is the number of set positions over all `k` polynomials. -/
theorem hintWeightVec_eq_length (h : Vector Hint p.k) :
    hintWeightVec h = (hintPositions h p.k).length := by
  unfold hintWeightVec hintPositions
  rw [Vector.toList_eq_map_range_getD h (Vector.ofFn fun _ => false), List.map_map,
    List.length_flatMap]
  congr 1
  apply List.map_congr_left
  intro i _
  simp [hintPoly, hintWeight_eq_length]

/-- The weight of a hint vector built from a Boolean table is the number of set entries. -/
theorem hintWeightVec_ofFn {k : ℕ} (f : Fin k → Fin ringDegree → Bool) :
    hintWeightVec (Vector.ofFn fun i => Vector.ofFn (f i)) =
      (Finset.univ.filter fun ik : Fin k × Fin ringDegree => f ik.1 ik.2 = true).card := by
  have hfold : ∀ (l : List Bool) (a : ℕ),
      l.foldl (fun acc b => acc + cond b 1 0) a = a + (l.map fun b => cond b 1 0).sum := by
    intro l
    induction l with
    | nil => simp
    | cons b l ih =>
      intro a
      rw [List.foldl_cons, ih, List.map_cons, List.sum_cons]
      omega
  unfold hintWeightVec hintWeight
  simp only [Vector.toList_ofFn, List.map_ofFn, Function.comp_def, hfold, zero_add,
    List.sum_ofFn, Finset.card_filter, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  cases f i j <;> rfl

/-- The bytes `hintBitPack` produces when the total weight is at most `ω`: the set positions in
order (polynomial by polynomial, increasing within each), zero padding up to `ω` bytes, then for
each polynomial `i` the number of positions set in polynomials `0, …, i`. -/
def hintBytes (h : Vector Hint p.k) : List Byte :=
  (hintPositions h p.k).map Nat.toUInt8 ++
    List.replicate (p.omega - (hintPositions h p.k).length) 0 ++
    (List.range p.k).map fun i => (hintPositions h (i + 1)).length.toUInt8

/-- What `hintBitPack` produces, when the total hint weight is at most `ω`. -/
theorem hintBitPack_eq (h : Vector Hint p.k) (hω : hintWeightVec h ≤ p.omega) :
    hintBitPack p h = ByteArray.mk (Array.mk (hintBytes h)) := by
  rw [hintWeightVec_eq_length] at hω
  rw [hintBitPack_eq_foldl, packOuter_foldl h (le_refl _) hω]
  simp [hintBytes]


/-! ### Decoding the packed bytes -/

theorem hintPositions_prefix (h : Vector Hint p.k) {m n : ℕ} (hmn : m ≤ n) :
    hintPositions h m <+: hintPositions h n := by
  induction n with
  | zero => rw [Nat.le_zero.mp hmn]
  | succ n ih =>
    rcases Nat.of_le_succ hmn with h' | h'
    · rw [hintPositions_succ]; exact (ih h').trans (List.prefix_append _ _)
    · rw [h']

/-- Entry `|positions below i| + t` of the positions list is entry `t` of polynomial `i`'s
support. -/
theorem hintPositions_getElem (h : Vector Hint p.k) {i n t : ℕ} (hi : i < n)
    (ht : t < (hintSupport (hintPoly h i)).length) :
    ∃ hlt : (hintPositions h i).length + t < (hintPositions h n).length,
      (hintPositions h n)[(hintPositions h i).length + t] = (hintSupport (hintPoly h i))[t] := by
  have hpre := hintPositions_prefix h (Nat.succ_le_of_lt hi)
  have hlen : (hintPositions h (i + 1)).length =
      (hintPositions h i).length + (hintSupport (hintPoly h i)).length := by
    rw [hintPositions_succ, List.length_append]
  have hlt1 : (hintPositions h i).length + t < (hintPositions h (i + 1)).length := by omega
  refine ⟨lt_of_lt_of_le hlt1 hpre.length_le, ?_⟩
  rw [← hpre.getElem hlt1]
  simp only [hintPositions_succ]
  rw [List.getElem_append_right (by omega)]
  simp

theorem hintSupport_lt (hi : Hint) {j : ℕ} (hj : j ∈ hintSupport hi) : j < ringDegree :=
  List.mem_range.mp (List.mem_filter.mp hj).1

theorem hintSupport_pairwise (hi : Hint) : (hintSupport hi).Pairwise (· < ·) :=
  (List.pairwise_lt_range).filter _

theorem hintBytes_length (h : Vector Hint p.k) (hω : (hintPositions h p.k).length ≤ p.omega) :
    (hintBytes h).length = p.omega + p.k := by
  simp only [hintBytes, List.length_append, List.length_map, List.length_replicate, List.length_range]
  omega

theorem getByteD_mk (B : List Byte) (x : ℕ) :
    getByteD (ByteArray.mk (Array.mk B)) x = B.getD x 0 := by
  unfold getByteD
  by_cases hx : x < B.length
  · rw [getElem?_pos (ByteArray.mk (Array.mk B)) x (by simpa [ByteArray.size] using hx),
      List.getD_eq_getElem _ _ hx]
    rfl
  · rw [getElem?_neg (ByteArray.mk (Array.mk B)) x (by simpa [ByteArray.size] using hx),
      List.getD_eq_default _ _ (by omega)]
    rfl


theorem hintBytes_getD_position (h : Vector Hint p.k) {x : ℕ} (hx : x < (hintPositions h p.k).length) :
    (hintBytes h).getD x 0 = ((hintPositions h p.k)[x]).toUInt8 := by
  unfold hintBytes
  rw [List.append_assoc, List.getD_append _ _ _ _ (by simpa using hx)]
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hx]
  rfl

theorem hintBytes_getD_padding (h : Vector Hint p.k) {x : ℕ} (hx : (hintPositions h p.k).length ≤ x)
    (hxω : x < p.omega) : (hintBytes h).getD x 0 = 0 := by
  unfold hintBytes
  rw [List.append_assoc, List.getD_append_right _ _ _ _ (by simpa using hx),
    List.getD_append _ _ _ _ (by simp; omega)]
  simp

theorem hintBytes_getD_count (h : Vector Hint p.k) (hω : (hintPositions h p.k).length ≤ p.omega)
    {i : ℕ} (hi : i < p.k) :
    (hintBytes h).getD (p.omega + i) 0 = (hintPositions h (i + 1)).length.toUInt8 := by
  unfold hintBytes
  rw [List.getD_append_right _ _ _ _ (by simp; omega)]
  simp only [List.length_append, List.length_map, List.length_replicate]
  rw [show p.omega + i - ((hintPositions h p.k).length + (p.omega - (hintPositions h p.k).length)) = i
    by omega]
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hi]
  rfl

def unpackInner (bytes : ByteArray) (s : Option (Option (Vector Hint p.k)) × Array Bool × ℕ)
    (j : ℕ) : Option (Option (Vector Hint p.k)) × Array Bool × ℕ :=
  (none, s.2.1.set! (getByteD bytes j).toNat true, (getByteD bytes j).toNat)

def unpackOuter (h : Vector Hint p.k) (s : Option (Option (Vector Hint p.k)) × Array Hint × ℕ)
    (i : ℕ) : Option (Option (Vector Hint p.k)) × Array Hint × ℕ :=
  (none, s.2.1.push (hintPoly h i), (hintPositions h (i + 1)).length)

theorem unpackOuter_foldl (h : Vector Hint p.k) (n : ℕ) :
    (List.range n).foldl (unpackOuter h) (none, Array.mkEmpty p.k, 0) =
      (none, Array.mk ((List.range n).map (hintPoly h)), (hintPositions h n).length) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [List.range_succ, List.foldl_append, ih]
    simp [unpackOuter]

theorem unpackInner_foldl (bytes : ByteArray) (a : Array Bool) (c t : ℕ) :
    (List.range' c t).foldl (unpackInner (p := p) bytes) (none, a, 0) =
      (none, (List.range' c t).foldl (fun a j => a.set! (getByteD bytes j).toNat true) a,
        if t = 0 then 0 else (getByteD bytes (c + t - 1)).toNat) := by
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [List.range'_concat, List.foldl_append, ih, List.foldl_append]
    simp [unpackInner]

theorem mem_hintSupport {hi : Hint} {j : ℕ} :
    j ∈ hintSupport hi ↔ j < ringDegree ∧ hi.toArray.getD j false = true := by
  simp [hintSupport]

theorem toNat_toUInt8 {x : ℕ} (hx : x < 256) : x.toUInt8.toNat = x := by
  rw [Nat.toUInt8, UInt8.toNat_ofNat', Nat.mod_eq_of_lt (by simpa using hx)]

theorem hintBitUnpack_hintBytes (h : Vector Hint p.k) (hω : (hintPositions h p.k).length ≤ p.omega)
    (hω256 : p.omega < 256) :
    hintBitUnpack p (ByteArray.mk (Array.mk (hintBytes h))) = some h := by
  set bytes := ByteArray.mk (Array.mk (hintBytes h)) with hbytes
  have hbyte : ∀ x, getByteD bytes x = (hintBytes h).getD x 0 := getByteD_mk _
  unfold hintBitUnpack
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size, Nat.sub_zero,
    Nat.add_sub_cancel, Nat.div_one, ← List.range_eq_range']
  rw [List.forIn_id_eq_foldl_of_yield _ _ _ (unpackOuter h)]
  · rw [unpackOuter_foldl]
    simp only [Id.bind_eq_apply]
    rw [List.forIn_id_eq_foldl_of_yield _ _ _ (fun _ _ => (none, ()))]
    · have hconst : ∀ l : List ℕ,
          l.foldl (fun _ _ => ((none : Option (Option (Vector Hint p.k))), ())) (none, ()) =
            (none, ()) := by
        intro l; induction l with
        | nil => rfl
        | cons a l ih => exact ih
      simp only [hconst, Id.run_pure]
      congr 1
      apply Vector.ext
      intro i hi
      simp only [Vector.getElem_ofFn, Array.getD_eq_getD_getElem?, List.getElem?_toArray,
        List.getElem?_map, List.getElem?_range hi, Option.map_some, Option.getD_some, hintPoly]
      simp [hi]
    · intro t ht
      rw [List.length_range'] at ht
      rw [List.getElem_range', hbyte, hintBytes_getD_padding h (by omega) (by omega)]
      rfl
  · intro n hn
    rw [List.length_range] at hn
    simp only [List.getElem_range, List.take_range, Nat.min_eq_left hn.le, unpackOuter_foldl]
    have hcount : (getByteD bytes (p.omega + n)).toNat = (hintPositions h (n + 1)).length := by
      have hle := hintPositions_length_mono h (show n + 1 ≤ p.k by omega)
      rw [hbyte, hintBytes_getD_count h hω hn, toNat_toUInt8 (by omega)]
    have hmono : (hintPositions h n).length ≤ (hintPositions h (n + 1)).length :=
      hintPositions_length_mono h n.le_succ
    have hle := hintPositions_length_mono h (show n + 1 ≤ p.k by omega)
    simp only [hcount]
    rw [ite_eq_right_of_eq_false _ _ (by simp; omega)]
    have hlen : (hintPositions h (n + 1)).length - (hintPositions h n).length =
        (hintSupport (hintPoly h n)).length := by
      rw [hintPositions_succ, List.length_append]; omega
    have hbyteS : ∀ t (ht : t < (hintSupport (hintPoly h n)).length),
        (getByteD bytes ((hintPositions h n).length + t)).toNat = (hintSupport (hintPoly h n))[t] := by
      intro t ht
      obtain ⟨hlt, heq⟩ := hintPositions_getElem h hn ht
      rw [hbyte, hintBytes_getD_position h hlt, heq,
        toNat_toUInt8 (hintSupport_lt _ (List.getElem_mem _))]
    have hmap : (List.range' (hintPositions h n).length
          (hintSupport (hintPoly h n)).length).map (fun j => (getByteD bytes j).toNat) =
        hintSupport (hintPoly h n) := by
      apply List.ext_getElem (by rw [List.length_map, List.length_range'])
      intro t h1 h2
      rw [List.getElem_map, List.getElem_range', Nat.one_mul, hbyteS t h2]
    rw [hlen]
    rw [List.forIn_id_eq_foldl_of_yield _ _ _ (unpackInner bytes)]
    · have hv : (Vector.ofFn fun j : Fin ringDegree =>
            ((List.range' (hintPositions h n).length (hintSupport (hintPoly h n)).length).foldl
              (fun a j => a.set! (getByteD bytes j).toNat true)
              (Array.replicate ringDegree false)).getD j false) = hintPoly h n := by
        have hfold : (List.range' (hintPositions h n).length (hintSupport (hintPoly h n)).length).foldl
              (fun a j => a.set! (getByteD bytes j).toNat true) (Array.replicate ringDegree false) =
            (hintSupport (hintPoly h n)).foldl (fun (a : Array Bool) j => a.set! j true)
              (Array.replicate ringDegree false) := by
          conv_rhs => rw [← hmap]
          rw [List.foldl_map]
        rw [hfold]
        apply Vector.ext
        intro j hj
        rw [Vector.getElem_ofFn, Array.getD_foldl_set!_true _ _ (by simpa using hj)]
        simp only [Array.getD_eq_getD_getElem?, Array.getElem?_replicate, hj, ite_true,
          Option.getD_some, Bool.false_or]
        have hget : (hintPoly h n).toArray.getD j false = (hintPoly h n)[j] := by
          simp [Array.getD_eq_getD_getElem?, hj]
        rw [Bool.eq_iff_iff, decide_eq_true_iff, mem_hintSupport, hget]
        exact ⟨fun h' => h'.2, fun h' => ⟨hj, h'⟩⟩
      rw [unpackInner_foldl]
      simp only [Id.bind_eq_apply, unpackOuter, hv]
      rfl
    · intro t ht
      rw [List.length_range'] at ht
      rw [List.getElem_range', Nat.one_mul, List.take_range'_of_le ht.le, unpackInner_foldl,
        hbyteS t ht]
      have hS := hintSupport_lt (hintPoly h n) (List.getElem_mem ht)
      rw [ite_eq_right_of_eq_false _ _ (eq_false (not_le.mpr hS))]
      rw [ite_eq_right_of_eq_false _ _ ?_]
      · simp only [unpackInner, hbyteS t ht]
        rfl
      · rcases Nat.eq_zero_or_pos t with rfl | htpos
        · simp
        · rw [ite_eq_right_of_eq_false _ _ (eq_false (by omega)), show (hintPositions h n).length + t - 1 =
            (hintPositions h n).length + (t - 1) by omega, hbyteS (t - 1) (by omega)]
          have := (List.pairwise_iff_getElem.mp (hintSupport_pairwise (hintPoly h n)))
            (t - 1) t (by omega) ht (by omega)
          apply eq_false
          simp only [Bool.and_eq_true, decide_eq_true_eq, not_and, not_le]
          exact fun _ => this


/-- `hintBitUnpack` inverts `hintBitPack` when the total hint weight is at most `ω`. `ω < 256`
(a `param`) makes every stored count a byte. -/
theorem hintBitUnpack_hintBitPack (h : Vector Hint p.k) (hω : hintWeightVec h ≤ p.omega)
    (hω256 : p.omega < 256) : hintBitUnpack p (hintBitPack p h) = some h := by
  rw [hintBitPack_eq h hω]
  rw [hintWeightVec_eq_length] at hω
  exact hintBitUnpack_hintBytes h hω hω256

/-! ### Reading concatenated byte arrays -/

theorem getByteD_append_left (X Y : ByteArray) {i : ℕ} (hi : i < X.size) :
    getByteD (X ++ Y) i = getByteD X i := by
  unfold getByteD
  rw [getElem?_pos (X ++ Y) i (by rw [ByteArray.size_append]; omega), getElem?_pos X i hi,
    Option.getD_some, Option.getD_some, ByteArray.getElem_append_left hi]

theorem getByteD_append_right (X Y : ByteArray) {i : ℕ} (hi : X.size ≤ i) :
    getByteD (X ++ Y) i = getByteD Y (i - X.size) := by
  unfold getByteD
  by_cases hy : i - X.size < Y.size
  · rw [getElem?_pos (X ++ Y) i (by rw [ByteArray.size_append]; omega),
      getElem?_pos Y (i - X.size) hy, Option.getD_some, Option.getD_some,
      ByteArray.getElem_append_right hi]
  · rw [getElem?_neg (X ++ Y) i (by rw [ByteArray.size_append]; omega),
      getElem?_neg Y (i - X.size) hy]

theorem sliceByteArray_size (ba : ByteArray) (offset len : ℕ) :
    (sliceByteArray ba offset len).size = len := by
  unfold sliceByteArray
  exact Array.size_ofFn

/-- Two byte arrays of equal size with the same total reads below that size are equal. -/
theorem ByteArray.ext_getByteD {X Y : ByteArray} (hsize : X.size = Y.size)
    (h : ∀ i < X.size, getByteD X i = getByteD Y i) : X = Y := by
  apply ByteArray.ext
  apply Array.ext hsize
  intro i h1 h2
  have := h i h1
  unfold getByteD at this
  rw [getElem?_pos X i h1, getElem?_pos Y i h2, Option.getD_some, Option.getD_some] at this
  exact this

/-- Slicing the middle part out of `A ++ B ++ C` recovers `B`. -/
theorem sliceByteArray_append_middle (A B C : ByteArray) :
    sliceByteArray (A ++ B ++ C) A.size B.size = B := by
  apply ByteArray.ext_getByteD (sliceByteArray_size _ _ _)
  intro i hi
  rw [sliceByteArray_size] at hi
  rw [getByteD_sliceByteArray _ hi, getByteD_append_left _ _ (by rw [ByteArray.size_append]; omega),
    getByteD_append_right _ _ (by omega), Nat.add_sub_cancel_left]

/-- Slicing the last part out of `AB ++ C` recovers `C`. -/
theorem sliceByteArray_append_last (AB C : ByteArray) :
    sliceByteArray (AB ++ C) AB.size C.size = C := by
  apply ByteArray.ext_getByteD (sliceByteArray_size _ _ _)
  intro i hi
  rw [sliceByteArray_size] at hi
  rw [getByteD_sliceByteArray _ hi, getByteD_append_right _ _ (by omega), Nat.add_sub_cancel_left]

/-! ### The signature codec -/

/-- The `z` packer's chunk size is `polyZPackedBytes`, the size `sigDecode` slices by. -/
theorem polyZPack_size (p : MLDSA.Params) (f : Rq) : (polyZPack p f).size = polyZPackedBytes p := by
  unfold polyZPack polyZPackedBytes
  rw [bitPackPoly_size, show ringDegree = 256 from rfl]
  omega

/-- `polyZUnpack` inverts `polyZPack` on polynomials whose centered coefficients lie in the
FIPS 204 `z` window `(-γ₁, γ₁]`, for an approved parameter set (a `param`), where the window
is exactly `2 ^ width` wide. -/
theorem polyZUnpack_polyZPack {p : MLDSA.Params} (hp : p.isApproved) (f : Rq)
    (hf : ∀ i, -(p.gamma1 : ℤ) < LatticeCrypto.centeredRepr (f.get i) ∧
      LatticeCrypto.centeredRepr (f.get i) ≤ p.gamma1) :
    polyZUnpack p (polyZPack p f) = f := by
  obtain ⟨hwidth, -⟩ := approved_gamma1_width p hp
  unfold polyZUnpack polyZPack
  apply bitUnpackPoly_bitPackPoly
  intro i
  have hw : (2 : ℤ) ^ rangeWidth (-(p.gamma1 : ℤ) + 1) (p.gamma1 : ℤ) = 2 * p.gamma1 := by
    exact_mod_cast hwidth
  rw [hw]
  have := hf i
  omega

/-- **Signature roundtrip.** For an approved parameter set (a `param`), `sigDecode` inverts
`sigEncode` on every `(c̃, z, h)` whose `z` coefficients lie in the packing window `(-γ₁, γ₁]`
(centered) and whose hint weight is at most `ω`. -/
theorem sigDecode_sigEncode {p : MLDSA.Params} (hp : p.isApproved) (cTilde : CommitHashBytes p)
    (z : RqVec p.l) (h : Vector Hint p.k)
    (hz : ∀ j i, -(p.gamma1 : ℤ) < LatticeCrypto.centeredRepr ((z.get j).get i) ∧
      LatticeCrypto.centeredRepr ((z.get j).get i) ≤ p.gamma1)
    (hω : hintWeightVec h ≤ p.omega) :
    sigDecode p (sigEncode p cTilde z h) = some (cTilde, z, h) := by
  have hω256 : p.omega < 256 := by rcases hp with rfl | rfl | rfl <;> decide
  have hA : (vectorToByteArray cTilde).size = p.lambda / 4 := by
    simp [vectorToByteArray, ByteArray.size]
  have hB : (packPolyVector z (polyZPack p)).size = p.l * polyZPackedBytes p :=
    packPolyVector_size z _ (polyZPack_size p)
  have hC : (hintBitPack p h).size = p.omega + p.k := by
    rw [hintBitPack_eq h hω]
    rw [hintWeightVec_eq_length] at hω
    simpa [ByteArray.size] using hintBytes_length h hω
  unfold sigDecode sigEncode
  simp only [ByteArray.size_append, hA, hB, hC, ne_eq, not_true_eq_false, ite_false]
  have hcTilde : byteArrayToVector (vectorToByteArray cTilde ++ packPolyVector z (polyZPack p) ++
      hintBitPack p h) 0 (p.lambda / 4) = cTilde := by
    apply Vector.ext
    intro i hi
    simp only [byteArrayToVector, Vector.getElem_ofFn, Nat.zero_add]
    change getByteD _ i = _
    rw [getByteD_append_left _ _ (by rw [ByteArray.size_append]; omega),
      getByteD_append_left _ _ (by omega)]
    unfold getByteD
    rw [getElem?_pos _ i (by omega), Option.getD_some]
    rfl
  have hzSlice := sliceByteArray_append_middle (vectorToByteArray cTilde)
    (packPolyVector z (polyZPack p)) (hintBitPack p h)
  have hhSlice := sliceByteArray_append_last
    (vectorToByteArray cTilde ++ packPolyVector z (polyZPack p)) (hintBitPack p h)
  rw [hA, hB] at hzSlice
  rw [ByteArray.size_append, hA, hB, hC] at hhSlice
  rw [hcTilde, hzSlice, hhSlice, hintBitUnpack_hintBitPack h hω hω256,
    unpackPolyVector_packPolyVector z _ _ (polyZPack_size p)
      (fun j => polyZUnpack_polyZPack hp _ (hz j))]

/-- **Extraction to serialized bytes.** A semantic signature `(c̃, z, h)` that verifies
(`Verifies`, FIPS 204 Algorithm 8) on the framed message encodes, by the vendored `sigEncode`,
to bytes that verify (`VerifiesBytes`, Algorithm 3). Algorithm 8 itself checks `‖z‖∞ < γ₁ − β`
and hint weight at most `ω`, which put `z` in the packing window and `h` in the hint codec's
domain, so no codec condition is assumed. The context bound `hctx` is Algorithm 3's own check on
the public context. -/
theorem extract_accepted_signature
    {pk : PublicKey _root_.MLDSA.mldsa44 (concretePrimitives _root_.MLDSA.mldsa44)} {ctx msg : List UInt8}
    {cTilde : CommitHashBytes _root_.MLDSA.mldsa44} {z : RqVec _root_.MLDSA.mldsa44.l} {h : Vector Hint _root_.MLDSA.mldsa44.k}
    (hctx : ctx.length ≤ 255) (hverify : Verifies pk (frame ctx msg) ⟨cTilde, z, h⟩) :
    VerifiesBytes pk ctx msg (sigEncode _root_.MLDSA.mldsa44 cTilde z h) := by
  have hchecks := hverify.checks
  unfold verifyChecks at hchecks
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hchecks
  obtain ⟨⟨hnorm, -⟩, hweight⟩ := hchecks
  have hz : ∀ j i, -(_root_.MLDSA.mldsa44.gamma1 : ℤ) < LatticeCrypto.centeredRepr ((z.get j).get i) ∧
      LatticeCrypto.centeredRepr ((z.get j).get i) ≤ _root_.MLDSA.mldsa44.gamma1 := by
    intro j i
    have := natAbs_centeredRepr_le_polyVecNorm z j i
    omega
  exact ⟨hctx, cTilde, z, h, sigDecode_sigEncode (Or.inl rfl) cTilde z h hz hweight, hverify⟩

/-! ### The `w1` bit layout -/

/-- `w1Encode` at ML-DSA-44 is `768` bytes, `6144 = 4 · 256 · 6` bits. -/
theorem w1Encode_length_mldsa44 (w1 : Vector High _root_.MLDSA.mldsa44.k) :
    (w1Encode _root_.MLDSA.mldsa44 w1).length = 768 := by
  have := w1Encode_length _root_.MLDSA.mldsa44 w1
  have hw : simpleWidth ((modulus - 1) / (2 * _root_.MLDSA.mldsa44.gamma2) - 1) = 6 := by decide
  rw [hw] at this
  change 8 * _ = 4 * 256 * 6 at this
  omega

/-- **`w1` bit layout at ML-DSA-44.** Reading the `w1Encode` bytes as a little-endian bit string
(bit `t % 8` of byte `t / 8`), coefficient `c` of polynomial `i` occupies bits
`(i · ringDegree + c) · 6 + b` for `b < 6` (`ringDegree = 256`), least significant bit first: bit `b` there is bit `b` of the
coefficient's value. -/
theorem w1Encode_testBit (w1 : Vector High _root_.MLDSA.mldsa44.k) (i : Fin _root_.MLDSA.mldsa44.k) (c : Fin ringDegree)
    (b : Fin 6) :
    ((w1Encode _root_.MLDSA.mldsa44 w1).getD (((i * ringDegree + c) * 6 + b) / 8) 0).toNat.testBit
        (((i * ringDegree + c) * 6 + b) % 8) =
      ((w1.get i).get c).val.testBit b := by
  have hw : simpleWidth ((modulus - 1) / (2 * _root_.MLDSA.mldsa44.gamma2) - 1) = 6 := by decide
  have h := w1Encode_bit _root_.MLDSA.mldsa44 w1 i c (b := b) (by rw [hw]; exact b.isLt)
  rw [hw] at h
  rw [Nat.testBit_eq_decide_div_mod_eq, Nat.testBit_eq_decide_div_mod_eq, h]

end GordieHowe.MLDSA44
