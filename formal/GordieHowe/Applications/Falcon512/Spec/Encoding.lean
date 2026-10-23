-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Applications.Falcon512.Spec.Decoded
import all LatticeCrypto.Falcon.Concrete.Encoding

@[expose] public section

/-!
# Constructive signature encoding for the Falcon encodability checks

These are codec specifications, not hypotheses about the circuit: the A
circuit establishes `EncodingBounds` from its constraints; the C++ implements the same checks (7699eec).
The target here is the current keyless verifier and its 625-byte payload;
correspondence to the intended external verifier remains a separate obligation.
-/

namespace GordieHowe.Falcon512

/-- Arithmetic conditions sufficient for the selected Falcon signature codec. -/
structure EncodingBounds (P : Params) (s : _root_.Falcon.IntPoly P.n) : Prop where
  coefficients : ∀ i, (s.get i).natAbs < Codec.magnitudeBound
  highSum : ∑ i, (s.get i).natAbs / Codec.lowRadix ≤ P.encodingHighBudget

theorem coeffBits_length (x : ℤ) :
    (_root_.Falcon.Concrete.coeffBits x).length =
      Codec.baseCoefficientBits + x.natAbs / Codec.lowRadix := by
  simp [_root_.Falcon.Concrete.coeffBits,
    _root_.Falcon.Concrete.natBits_length, Codec.baseCoefficientBits_eq,
    Codec.lowRadix_eq]
  omega

theorem sum_add_const {n c : ℕ} (xs : List (Fin n)) (f : Fin n → ℕ) :
    (xs.map fun i => c + f i).sum = c * xs.length + (xs.map f).sum := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      simp only [List.map_cons, List.sum_cons, List.length_cons, ih, Nat.mul_succ]
      omega

theorem compressedBits_length {n : ℕ} (s : _root_.Falcon.IntPoly n) :
    ((List.finRange n).flatMap fun i =>
      _root_.Falcon.Concrete.coeffBits (s.get i)).length =
        Codec.baseCoefficientBits * n +
          ∑ i, (s.get i).natAbs / Codec.lowRadix := by
  rw [List.length_flatMap]
  simp_rw [coeffBits_length]
  rw [sum_add_const, List.length_finRange]
  simp only [← List.sum_toFinset _ (List.nodup_finRange _),
    List.toFinset_finRange]

/-- Encode the extracted integer polynomial outside the circuit. -/
def encodeSignature (P : Params) (salt : _root_.Falcon.Bytes 40)
    (s : _root_.Falcon.IntPoly P.n) :
    Option _root_.Falcon.Signature :=
  (_root_.Falcon.Concrete.compress P.n s P.sigPayloadBytes).map fun bytes =>
    { salt := salt, compressedS2 := bytes }

/-- The magnitude and high-part bounds guarantee successful compression. -/
theorem compress_exists {P : Params} {s : _root_.Falcon.IntPoly P.n}
    (h : EncodingBounds P s) :
    ∃ bytes, _root_.Falcon.Concrete.compress P.n s P.sigPayloadBytes = some bytes := by
  have hcoeff : ∀ i : Fin P.n, -2047 ≤ s.get i ∧ s.get i ≤ 2047 := by
    intro i
    have hi := h.coefficients i
    rw [Codec.magnitudeBound_eq] at hi
    have habs : |s.get i| ≤ (2047 : ℤ) := by
      rw [Int.abs_eq_natAbs]
      have : (s.get i).natAbs ≤ 2047 := by omega
      exact_mod_cast this
    exact abs_le.mp habs
  let bits := (List.finRange P.n).flatMap fun i =>
    _root_.Falcon.Concrete.coeffBits (s.get i)
  have hbitsLength :
      bits.length = Codec.baseCoefficientBits * P.n +
        ∑ i, (s.get i).natAbs / Codec.lowRadix := by
    exact compressedBits_length s
  have hfit : bits.length ≤ 8 * P.sigPayloadBytes := by
    rw [hbitsLength]
    have hhigh := h.highSum
    have hbase := P.encodingFits
    simp only [Params.encodingHighBudget] at hhigh
    omega
  unfold _root_.Falcon.Concrete.compress
  rw [ite_eq_left hcoeff]
  dsimp only
  rw [ite_eq_right (Nat.not_lt.mpr hfit)]
  exact ⟨_, rfl⟩

/-- Codec correctness for the explicit external reconstruction algorithm. -/
theorem encodeSignature_spec {P : Params} {salt : _root_.Falcon.Bytes 40}
    {s : _root_.Falcon.IntPoly P.n} {sig : _root_.Falcon.Signature}
    (h : encodeSignature P salt s = some sig) :
    sig.salt = salt ∧
      _root_.Falcon.Concrete.decompress P.n sig.compressedS2 P.sigPayloadBytes = some s := by
  unfold encodeSignature at h
  cases hcompress : _root_.Falcon.Concrete.compress P.n s P.sigPayloadBytes with
  | none => simp [hcompress] at h
  | some bytes =>
      simp only [hcompress, Option.map_some, Option.some.injEq] at h
      subst sig
      exact ⟨rfl, _root_.Falcon.Concrete.decompress_compress
        P.n s P.sigPayloadBytes bytes hcompress⟩

/-! ### The format `decompress` accepts

The decoder accepts only the canonical code: every coefficient code it parses is `coeffBits` of
the parsed coefficient, of magnitude at most `2047`. A decoded signature polynomial therefore
satisfies the encodability bounds (`encodingBounds_of_decompress`). -/

section Canonical

open _root_.Falcon.Concrete

/-- **A parsed unary part is canonical**: `q` zeros and a one, the magnitude `m + 128 q` at most
`2047`, and the sign the sign bit (`-0` is rejected). -/
theorem parseUnary_eq_some {t : Bool} : ∀ {bits : List Bool} {m : ℕ} {x : ℤ} {rest : List Bool},
    m ≤ 2047 → parseUnary t m bits = some (x, rest) →
      ∃ q, bits = List.replicate q false ++ true :: rest ∧ x.natAbs = m + 128 * q ∧
        decide (x < 0) = t ∧ m + 128 * q ≤ 2047
  | [], _, _, _, _, h => by simp [parseUnary] at h
  | true :: bs, m, x, rest, hm, h => by
    cases t
    · simp only [parseUnary, Bool.false_eq_true, and_false, ↓reduceIte, Option.some.injEq,
        Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨0, by simp, by simp, by simp, by omega⟩
    · simp only [parseUnary, and_true, ↓reduceIte] at h
      split_ifs at h with h0
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨0, by simp, by simp, by simp; omega, by omega⟩
  | false :: bs, m, x, rest, hm, h => by
    simp only [parseUnary] at h
    split_ifs at h with hb
    obtain ⟨q, hbits, hx, ht, hq⟩ := parseUnary_eq_some (by omega) h
    exact ⟨q + 1, by rw [hbits]; simp [List.replicate_succ], by rw [hx]; ring, ht, by omega⟩

/-- **A parsed coefficient code is canonical**: the bits are `coeffBits x` followed by the rest,
and `|x| ≤ 2047`. -/
theorem parseCoeff_eq_some {bits rest : List Bool} {x : ℤ}
    (h : parseCoeff bits = some (x, rest)) :
    bits = coeffBits x ++ rest ∧ x.natAbs ≤ 2047 := by
  cases bits with
  | nil => simp [parseCoeff] at h
  | cons t r =>
    simp only [parseCoeff] at h
    split_ifs at h with hr
    have hlow := natOfBits_lt (r.take 7)
    rw [List.length_take, min_eq_left hr] at hlow
    obtain ⟨q, hbits, hx, ht, hq⟩ := parseUnary_eq_some (by omega) h
    refine ⟨?_, by omega⟩
    have hmod : x.natAbs % 128 = natOfBits (r.take 7) := by omega
    have hdiv : x.natAbs / 128 = q := by omega
    have hnb : natBits 7 (natOfBits (r.take 7)) = r.take 7 := by
      have := natBits_natOfBits (r.take 7)
      rwa [List.length_take, min_eq_left hr] at this
    simp only [coeffBits, hmod, hdiv, ht, hnb, List.cons_append, List.append_assoc]
    congr 1
    conv_lhs => rw [← List.take_append_drop 7 r, hbits]
    simp

/-- **Parsed coefficient codes are canonical**: `k` coefficients of magnitude at most `2047`,
whose codes are the bits read. -/
theorem parseCoeffs_eq_some : ∀ {k : ℕ} {bits rest : List Bool} {xs : List ℤ},
    parseCoeffs k bits = some (xs, rest) →
      bits = xs.flatMap coeffBits ++ rest ∧ xs.length = k ∧ ∀ x ∈ xs, x.natAbs ≤ 2047
  | 0, bits, rest, xs, h => by
    simp only [parseCoeffs, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    simp
  | k + 1, bits, rest, xs, h => by
    unfold parseCoeffs at h
    cases h1 : parseCoeff bits with
    | none => simp [h1] at h
    | some p =>
      obtain ⟨x, r⟩ := p
      cases h2 : parseCoeffs k r with
      | none => simp [h1, h2] at h
      | some p' =>
        obtain ⟨xs', r'⟩ := p'
        simp only [h1, h2, Option.bind_eq_bind, Option.bind_some, Option.pure_def,
          Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        obtain ⟨hb, hx⟩ := parseCoeff_eq_some h1
        obtain ⟨hb', hl, hxs⟩ := parseCoeffs_eq_some h2
        refine ⟨by rw [hb, hb']; simp, by simp [hl], ?_⟩
        intro y hy
        rcases List.mem_cons.mp hy with rfl | hy
        · exact hx
        · exact hxs y hy

/-- The bit stream of `d` has `8` bits per byte. -/
theorem bytesToBits_length (d : List UInt8) : (bytesToBits d).length = 8 * d.length := by
  induction d with
  | nil => rfl
  | cons b d ih =>
    rw [bytesToBits, List.flatMap_cons, List.length_append, ← bytesToBits, ih, byteBits,
      natBits_length, List.length_cons]
    ring

/-- **A decoded signature polynomial satisfies the encodability bounds**: `decompress` accepts
only canonical codes of coefficients of magnitude at most `2047` that fit the payload, so the
magnitude bound and the high-part budget of `EncodingBounds` hold. -/
theorem encodingBounds_of_decompress {P : Params} {d : List UInt8} {s : _root_.Falcon.IntPoly P.n}
    (h : decompress P.n d P.sigPayloadBytes = some s) : EncodingBounds P s := by
  unfold decompress at h
  split_ifs at h with hlen
  cases hp : parseCoeffs P.n (bytesToBits d) with
  | none => simp [hp] at h
  | some p =>
    obtain ⟨vals, rest⟩ := p
    simp only [hp] at h
    split_ifs at h with hz
    cases h
    obtain ⟨hbits, hvl, hb⟩ := parseCoeffs_eq_some hp
    have hget : ∀ i : Fin P.n, (Vector.ofFn fun i : Fin P.n => vals.getD i.val 0).get i =
        vals[i.val]'(by omega) := by
      intro i
      rw [Vector.get_ofFn, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega),
        Option.getD_some]
    have hmap : ((List.finRange P.n).map fun i =>
        (Vector.ofFn fun i : Fin P.n => vals.getD i.val 0).get i) = vals := by
      apply List.ext_getElem (by simp [hvl])
      intro j h1 h2
      simp only [List.getElem_map, List.getElem_finRange]
      rw [hget]
      rfl
    refine ⟨fun i => ?_, ?_⟩
    · rw [Codec.magnitudeBound_eq, hget]
      have := hb (vals[i.val]'(by omega)) (List.getElem_mem _)
      omega
    · have hlenb := congrArg List.length hbits
      rw [bytesToBits_length, List.length_append] at hlenb
      have hfm : ((List.finRange P.n).flatMap fun i =>
          coeffBits ((Vector.ofFn fun i : Fin P.n => vals.getD i.val 0).get i)) =
            vals.flatMap coeffBits := by
        conv_rhs => rw [← hmap]
        rw [List.flatMap_map]
      have hc := compressedBits_length (Vector.ofFn fun i : Fin P.n => vals.getD i.val 0)
      rw [hfm] at hc
      have hd : d.length = P.sigPayloadBytes := by omega
      unfold Params.encodingHighBudget
      omega

end Canonical

/-- Conditional bridge consumed by the proposed circuit composition. The
encoding bounds must be derived from that circuit, not assumed in its final
soundness theorem. The result identifies the output of an explicit encoder. -/
theorem extract_accepted_signature
    {pk : _root_.Falcon.PublicKey _root_.Falcon.Concrete.params512}
    {msg : List UInt8} {salt : _root_.Falcon.Bytes 40} {s : _root_.Falcon.IntPoly 512}
    (hbounds : EncodingBounds falcon512 s)
    (hverify : verifyDecoded pk msg salt (_root_.Falcon.IntPoly.toRq s)) :
    ∃ sig, encodeSignature falcon512 salt s = some sig ∧ verify pk msg sig := by
  obtain ⟨bytes, hcompress⟩ := compress_exists hbounds
  let sig : _root_.Falcon.Signature :=
    { salt := salt, compressedS2 := bytes }
  refine ⟨sig, ?_, (verify_iff_verifyDecoded pk msg sig).2 ?_⟩
  · simp [sig, encodeSignature, hcompress]
  · refine ⟨s, ?_, hverify⟩
    change _root_.Falcon.Concrete.decompress 512 bytes 625 = some s
    exact _root_.Falcon.Concrete.decompress_compress 512 s 625 bytes hcompress

end GordieHowe.Falcon512
