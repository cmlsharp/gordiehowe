-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Applications.MLDSA44.Spec.Basic
public import GordieHowe.Language.Realizations.MemoryShuffle
public import GordieHowe.Foundations.ToMathlib.ForIn
public import GordieHowe.Foundations.ToMathlib.UInt8
import all LatticeCrypto.MLDSA.Concrete.Encoding

@[expose] public section

/-!
# ML-DSA `SampleInBall` on a fixed stream

FIPS 204 Algorithm 29 draws 8 sign bytes and then one-byte candidate positions from `SHAKE256(c̃)`.
Placement `t` (write index `i = N − τ + t`) takes the next candidate `j ≤ i` and executes
`c[i] := c[j]; c[j] := ±1`. An H circuit reads a fixed stream of `C + 8` bytes (`C` candidates):
`SelectFirstTau` selects the accepted candidates among the `C` candidate bytes, and `MemoryShuffle`
checks the placements against the spec `MemoryShuffle.shuffle`. `fixedStreamChallenge` is that
composition: the selection `GordieHowe.MLDSA44.acceptedCandidates` followed by `MemoryShuffle.shuffle` with the
sign bits `sampleInBallSign`, or `none` if the `C` candidates hold fewer than `τ` acceptances. The
H circuit reads `272` bytes (`C = 264`, `lib/gordiehowe/examples/mldsa/mldsa_hash.h`, `kSibBytes`;
`GordieHowe.MLDSA44.PoP.stream`).

`fixedStreamChallenge_agree` is the statement that when the fixed stream succeeds the vendored
bounded sampler `MLDSA.Concrete.sampleInBallPoly?`
(`Vendor/LatticeCrypto/MLDSA/ConcretePrimitives.lean`) succeeds with the same challenge, for `C` at
most its budget of `264` candidates: its walk reads the fixed stream's `C` candidates first.
-/

namespace GordieHowe.MLDSA44

open _root_.MLDSA _root_.MLDSA.Concrete

/-! ### Selection -/

/-- The first candidate at most `i`, with the candidates after it. -/
def nextAccepted (i : ℕ) : List ℕ → Option (ℕ × List ℕ)
  | [] => none
  | j :: u => if j ≤ i then some (j, u) else nextAccepted i u

/-- The selection state after `n` placements from the candidates `u`, when placement `t`
accepts a candidate at most `i₀ + t`: the accepted candidates in order and the candidates not
yet read, or `none` if the candidates run out first. -/
def acceptState (i₀ : ℕ) (u : List ℕ) : ℕ → Option (List ℕ × List ℕ)
  | 0 => some ([], u)
  | n + 1 => (acceptState i₀ u n).bind fun s =>
      (nextAccepted (i₀ + n) s.2).map fun r => (s.1 ++ [r.1], r.2)

theorem nextAccepted_le {i : ℕ} {u : List ℕ} {j : ℕ} {t : List ℕ}
    (h : nextAccepted i u = some (j, t)) : j ≤ i := by
  induction u with
  | nil => simp [nextAccepted] at h
  | cons x u ih =>
    unfold nextAccepted at h
    split_ifs at h with hx
    · cases h; exact hx
    · exact ih h

theorem nextAccepted_suffix {i : ℕ} {u : List ℕ} {j : ℕ} {t : List ℕ}
    (h : nextAccepted i u = some (j, t)) : t <:+ u := by
  induction u with
  | nil => simp [nextAccepted] at h
  | cons x u ih =>
    unfold nextAccepted at h
    split_ifs at h with hx
    · cases h; exact List.suffix_cons _ _
    · exact (ih h).trans (List.suffix_cons _ _)

theorem nextAccepted_append {i : ℕ} {l : List ℕ} {j : ℕ} {t : List ℕ}
    (h : nextAccepted i l = some (j, t)) (r : List ℕ) :
    nextAccepted i (l ++ r) = some (j, t ++ r) := by
  induction l with
  | nil => simp [nextAccepted] at h
  | cons x l ih =>
    unfold nextAccepted at h
    rw [List.cons_append]
    unfold nextAccepted
    split_ifs at h ⊢ with hx
    · cases h; rfl
    · exact ih h

theorem acceptState_succ_eq_some {i₀ : ℕ} {u : List ℕ} {n : ℕ} {s' : List ℕ × List ℕ}
    (h : acceptState i₀ u (n + 1) = some s') :
    ∃ s j t, acceptState i₀ u n = some s ∧ nextAccepted (i₀ + n) s.2 = some (j, t) ∧
      s' = (s.1 ++ [j], t) := by
  simp only [acceptState, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
  obtain ⟨s, hs, ⟨j, t⟩, hr, rfl⟩ := h
  exact ⟨s, j, t, hs, hr, rfl⟩

theorem acceptState_length {i₀ : ℕ} {u : List ℕ} :
    ∀ {n : ℕ} {s : List ℕ × List ℕ}, acceptState i₀ u n = some s → s.1.length = n
  | 0, s, h => by simp [acceptState] at h; subst h; rfl
  | n + 1, s, h => by
    obtain ⟨s₀, j, t, hs, -, rfl⟩ := acceptState_succ_eq_some h
    simp [acceptState_length hs]

theorem acceptState_suffix {i₀ : ℕ} {u : List ℕ} :
    ∀ {n : ℕ} {s : List ℕ × List ℕ}, acceptState i₀ u n = some s → s.2 <:+ u
  | 0, s, h => by simp [acceptState] at h; subst h; exact List.suffix_refl _
  | n + 1, s, h => by
    obtain ⟨s₀, j, t, hs, hr, rfl⟩ := acceptState_succ_eq_some h
    exact (nextAccepted_suffix hr).trans (acceptState_suffix hs)

/-- An earlier state of a successful selection is some, and its accepted list is a prefix. -/
theorem acceptState_of_le {i₀ : ℕ} {u : List ℕ} {m n : ℕ} (hmn : m ≤ n)
    {s : List ℕ × List ℕ} (h : acceptState i₀ u n = some s) :
    ∃ s₀, acceptState i₀ u m = some s₀ ∧ s₀.1 <+: s.1 := by
  induction n generalizing s with
  | zero => exact ⟨s, by rw [Nat.le_zero.mp hmn]; exact h, List.prefix_refl _⟩
  | succ n ih =>
    rcases Nat.eq_or_lt_of_le hmn with rfl | hlt
    · exact ⟨s, h, List.prefix_refl _⟩
    · obtain ⟨s₁, j, t, hs₁, -, rfl⟩ := acceptState_succ_eq_some h
      obtain ⟨s₀, hs₀, hpre⟩ := ih (by omega) hs₁
      exact ⟨s₀, hs₀, hpre.trans (List.prefix_append _ _)⟩

/-- Extra candidates after a successful selection change only the unread candidates. -/
theorem acceptState_append {i₀ : ℕ} {l : List ℕ} (r : List ℕ) :
    ∀ {n : ℕ} {s : List ℕ × List ℕ}, acceptState i₀ l n = some s →
      acceptState i₀ (l ++ r) n = some (s.1, s.2 ++ r)
  | 0, s, h => by
    simp only [acceptState, Option.some.injEq] at h ⊢
    subst h
    rfl
  | n + 1, s, h => by
    obtain ⟨s₀, j, t, hs₀, hr, rfl⟩ := acceptState_succ_eq_some h
    simp only [acceptState, acceptState_append r hs₀, Option.bind_some,
      nextAccepted_append hr r, Option.map_some]

/-! ### The fixed-stream sampler -/

variable (P : Params) {C : ℕ}

/-- The `C` candidate bytes `stream[8..C + 8)`. -/
def streamCandidates (stream : Fin (C + 8) → ℕ) : List ℕ :=
  List.ofFn fun j : Fin C => stream ⟨8 + j, by omega⟩

/-- Sign bit `s`: bit `s % 8` of stream byte `s / 8`, for `s < 64`; FIPS 204 reads the first
`8` bytes as a little-endian `64`-bit string. -/
def sampleInBallSign (stream : Fin (C + 8) → ℕ) (s : ℕ) : Bool :=
  if h : s < 64 then (stream ⟨s / 8, by omega⟩).testBit (s % 8) else false

/-- The accepted candidates of the fixed stream: placement `t` takes the next candidate at most
`N − τ + t`. This is `SelectFirstTau`'s specification. -/
def acceptedCandidates (stream : Fin (C + 8) → ℕ) : Option (Fin P.τ → ℕ) :=
  (acceptState (P.N - P.τ) (streamCandidates stream) P.τ).map fun s t => s.1.getD t 0

/-- Fixed-stream `SampleInBall`: the selection followed by the memory shuffle's specification
`MemoryShuffle.shuffle` with the stream's sign bits, or `none` if fewer than `τ` of the `C`
candidates are accepted. -/
def fixedStreamChallenge (stream : Fin (C + 8) → ℕ) : Option (Fin P.N → ℤ) :=
  (acceptedCandidates P stream).map fun pos =>
    MemoryShuffle.shuffle P.N P.τ pos fun s => sampleInBallSign stream s

/-- **Bridge to the memory shuffle.** The fixed sampler succeeds exactly when the selection
does, and then it is `MemoryShuffle.shuffle` of the selected positions and the sign bits. -/
theorem fixedStreamChallenge_eq_some_iff {stream : Fin (C + 8) → ℕ} {c : Fin P.N → ℤ} :
    fixedStreamChallenge P stream = some c ↔
      ∃ pos, acceptedCandidates P stream = some pos ∧
        c = MemoryShuffle.shuffle P.N P.τ pos fun s => sampleInBallSign stream s := by
  unfold fixedStreamChallenge
  rw [Option.map_eq_some_iff]
  exact exists_congr fun pos => and_congr_right fun _ => eq_comm

/-- The selected positions satisfy the memory shuffle's hypotheses: position `t` is at most the
write index `N − τ + t`, hence below `N` when `τ ≤ N`. -/
theorem acceptedCandidates_le {stream : Fin (C + 8) → ℕ} {pos : Fin P.τ → ℕ}
    (h : acceptedCandidates P stream = some pos) (t : Fin P.τ) :
    pos t ≤ P.N - P.τ + t := by
  unfold acceptedCandidates at h
  rw [Option.map_eq_some_iff] at h
  obtain ⟨s, hs, rfl⟩ := h
  obtain ⟨s₁, hs₁, hpre⟩ := acceptState_of_le (Nat.succ_le_of_lt t.isLt) hs
  obtain ⟨s₀, j, u, hs₀, hr, rfl⟩ := acceptState_succ_eq_some hs₁
  have hlen := acceptState_length hs₀
  have hlt : (t : ℕ) < (s₀.1 ++ [j], u).1.length := by simp [hlen]
  have hget : s.1.getD t 0 = j := by
    rw [List.getD_eq_getElem _ _ (by rw [acceptState_length hs]; exact t.isLt),
      ← List.IsPrefix.getElem hpre hlt]
    simp [hlen]
  show s.1.getD t 0 ≤ _
  rw [hget]
  exact nextAccepted_le hr

/-! ### Agreement with the vendored sampler -/

/-- The vendored candidate search, read through `nextAccepted`: if the candidates from `cursor`
on contain one at most `i`, and the fuel covers them, the search returns it and the position
after it. -/
theorem findAccepted_eq (cand : Array UInt8) (i : ℕ) :
    ∀ (fuel cursor : ℕ) {j : ℕ} {t : List ℕ}, cand.size - cursor ≤ fuel →
      nextAccepted i ((cand.toList.map UInt8.toNat).drop cursor) = some (j, t) →
      sampleInBallFindAccepted cand i cursor fuel = some (j, cand.size - t.length) := by
  intro fuel
  induction fuel with
  | zero =>
    intro cursor j t hfuel h
    rw [List.drop_eq_nil_of_le (by simp; omega)] at h
    simp [nextAccepted] at h
  | succ fuel ih =>
    intro cursor j t hfuel h
    have hlt : cursor < cand.size := by
      by_contra hge
      rw [List.drop_eq_nil_of_le (by simp; omega)] at h
      simp [nextAccepted] at h
    rw [List.drop_eq_getElem_cons (by simpa using hlt)] at h
    unfold nextAccepted at h
    rw [sampleInBallFindAccepted, Array.getElem?_eq_getElem hlt]
    simp only [List.getElem_map, Array.getElem_toList] at h
    dsimp only
    split_ifs at h ⊢ with hx
    · cases h
      simp only [List.length_drop, List.length_map, Array.length_toList, Option.some.injEq,
        Prod.mk.injEq, true_and]
      omega
    · exact ih (cursor + 1) (by omega) h

/-- The vendored loop after `n` placements, when the selection over its candidates `cand`
succeeds with the accepted list `sτ.1`: the loop has not failed, the cursor sits after the
`n`-th accepted candidate and the array is `shuffleAt n`. -/
theorem step_foldl (cand : Array UInt8) {τ : ℕ} (hτ : τ ≤ 256)
    (sgn : ℕ → Bool) {sτ : List ℕ × List ℕ}
    (hsel : acceptState (256 - τ) (cand.toList.map UInt8.toNat) τ = some sτ) :
    ∀ n, n ≤ τ → ∃ s st, acceptState (256 - τ) (cand.toList.map UInt8.toNat) n = some s ∧
      (List.range' (256 - τ) n).foldl (sampleInBallStep cand (256 - τ) sgn)
          (some (Array.replicate 256 0, 0)) = some st ∧
      st.2 = cand.size - s.2.length ∧ st.1.size = 256 ∧
      ∀ k (hk : k < 256), st.1[k]! =
        ((MemoryShuffle.shuffleAt 256 τ (fun t => sτ.1.getD t 0) (fun t => sgn t) n ⟨k, hk⟩ : ℤ) :
          Coeff) := by
  have hUlen : (cand.toList.map UInt8.toNat).length = cand.size := by simp
  intro n
  induction n with
  | zero =>
    intro _
    refine ⟨([], cand.toList.map UInt8.toNat), _, rfl, rfl, by simp [hUlen], by simp, ?_⟩
    intro k hk
    have hk' : k < (Array.replicate 256 (0 : Coeff)).size := by simpa using hk
    rw [getElem!_pos _ k hk']
    simp [MemoryShuffle.shuffleAt]
  | succ n ih =>
    intro hn
    obtain ⟨s, st, hs, hst, hcur, hsize, hval⟩ := ih (by omega)
    obtain ⟨s', hs', hpre'⟩ := acceptState_of_le hn hsel
    obtain ⟨s₀, j, t, hs₀, hr, rfl⟩ := acceptState_succ_eq_some hs'
    rw [hs] at hs₀
    cases hs₀
    have hsuffix := acceptState_suffix hs
    have hdrop : (cand.toList.map UInt8.toNat).drop (cand.size - s.2.length) = s.2 := by
      rw [List.suffix_iff_eq_drop] at hsuffix
      rw [hUlen] at hsuffix
      exact hsuffix.symm
    have hfind : sampleInBallFindAccepted cand (256 - τ + n) (cand.size - s.2.length) cand.size =
        some (j, cand.size - t.length) :=
      findAccepted_eq cand _ _ _ (by omega) (by rw [hdrop]; exact hr)
    have hjle := nextAccepted_le hr
    have hlen := acceptState_length hs
    have hposn : sτ.1.getD n 0 = j := by
      rw [List.getD_eq_getElem _ _ (by rw [acceptState_length hsel]; omega),
        ← List.IsPrefix.getElem hpre' (by simp [hlen])]
      simp [hlen]
    have hi : 256 - τ + n < 256 := by omega
    have hj256 : j < 256 := by omega
    have hn' : n < τ := by omega
    refine ⟨_, ((st.1.set! (256 - τ + n) st.1[j]!).set! j (if sgn n then -1 else 1),
      cand.size - t.length), hs', ?_, rfl, by simp [hsize], ?_⟩
    · rw [List.range'_concat, List.foldl_append, List.foldl_cons, List.foldl_nil, hst]
      unfold sampleInBallStep
      rw [Nat.one_mul]
      simp only [Option.bind_some, hcur, hfind, Option.map_some,
        show 256 - τ + n - (256 - τ) = n by omega]
    intro k hk
    rw [MemoryShuffle.shuffleAt_succ (fun t => sτ.1.getD t 0) (fun t => sgn t) hn' hi
      (by simp only [hposn]; exact hj256)]
    simp only [hposn]
    by_cases hkj : k = j
    · subst hkj
      rw [Array.getElem!_set!_self _ _ _ (by simp [hsize]; exact hj256)]
      simp only [Function.update_self]
      split <;> simp
    · rw [Array.getElem!_set!_ne _ _ _ _ (Ne.symm hkj),
        Function.update_of_ne (by intro h; exact hkj (congrArg Fin.val h))]
      by_cases hki : k = 256 - τ + n
      · subst hki
        rw [Array.getElem!_set!_self _ _ _ (by rw [hsize]; exact hi), Function.update_self,
          hval j hj256]
      · rw [Array.getElem!_set!_ne _ _ _ _ (Ne.symm hki),
          Function.update_of_ne (by intro h; exact hki (congrArg Fin.val h)), hval k hk]

/-- Bit `j` of a byte, as the vendored sampler reads it. -/
theorem shiftRight_and_one_beq (b : UInt8) {j : ℕ} (hj : j < 8) :
    ((b >>> j.toUInt8) &&& 1 == 1) = b.toNat.testBit j := by
  have hnat : ((b >>> j.toUInt8) &&& 1).toNat = b.toNat / 2 ^ j % 2 := by
    rw [UInt8.toNat_and, UInt8.toNat_shiftRight, show (1 : UInt8).toNat = 1 from rfl,
      Nat.and_one_is_mod, Nat.shiftRight_eq_div_pow, Nat.toUInt8, UInt8.toNat_ofNat',
      Nat.mod_eq_of_lt (show j < 2 ^ 8 by omega), Nat.mod_eq_of_lt (show j < 8 by omega)]
  rw [Nat.testBit_eq_decide_div_mod_eq, ← hnat]
  by_cases hx : (b >>> j.toUInt8) &&& 1 = 1
  · simp [hx]
  · have : ((b >>> j.toUInt8) &&& 1).toNat ≠ 1 := fun h => hx (UInt8.toNat_inj.mp h)
    rw [beq_eq_false_iff_ne.mpr hx]
    exact (decide_eq_false this).symm

/-- **Agreement with the vendored sampler**: when the fixed stream of `C ≤ 264` candidates
succeeds, the vendored bounded `sampleInBallPoly?` succeeds with the same challenge (its
`264`-candidate walk reads the `C` candidates of the fixed stream first). -/
theorem fixedStreamChallenge_agree {cTilde : CommitHashBytes _root_.MLDSA.mldsa44}
    {c : Fin mldsa44.N → ℤ} (hC : C ≤ sampleInBallCandidateBudget)
    (hc : fixedStreamChallenge mldsa44 (xofFin GordieHowe.shake256 (cTilde.toList.map UInt8.toNat) (C + 8)) =
      some c) :
    sampleInBallPoly? _root_.MLDSA.mldsa44 cTilde = some (ofCoeff fun k => (c k : Coeff)) := by
  obtain ⟨V, hV⟩ : ∃ V, SLHDSA.Concrete.Keccak.shake256 (ByteArray.mk cTilde.toList.toArray)
      (8 + sampleInBallCandidateBudget) = V := ⟨_, rfl⟩
  have hVsize : V.size = 8 + sampleInBallCandidateBudget :=
    hV ▸ SLHDSA.Concrete.Keccak.shake256_size _ _
  have hfV : ∀ (b : ℕ) (hb : b < C + 8),
      xofFin GordieHowe.shake256 (cTilde.toList.map UInt8.toNat) (C + 8) ⟨b, hb⟩ = V[b]!.toNat := by
    intro b hb
    rw [xofFin_shake256_prefix _ (show C + 8 ≤ 8 + sampleInBallCandidateBudget by omega) ⟨b, hb⟩,
      xofFin_shake256_eq_getElem!, List.map_toUInt8_map_toNat, hV]
  generalize xofFin GordieHowe.shake256 (cTilde.toList.map UInt8.toNat) (C + 8) = f at hc hfV
  obtain ⟨pos, hpos, rfl⟩ := (fixedStreamChallenge_eq_some_iff mldsa44).mp hc
  unfold acceptedCandidates at hpos
  obtain ⟨s128, hs128, rfl⟩ := Option.map_eq_some_iff.mp hpos
  have hstream : shake256List (byteArrayToList (vectorToByteArray cTilde))
      (8 + sampleInBallCandidateBudget) = V := by
    rw [← hV]
    rfl
  set cand := (V.extract 8 (8 + sampleInBallCandidateBudget)).data with hcand
  have hcandsize : cand.size = sampleInBallCandidateBudget := by
    change (V.extract 8 (8 + sampleInBallCandidateBudget)).size = sampleInBallCandidateBudget
    rw [ByteArray.size_extract, hVsize]
    omega
  have hcandget : ∀ (x : ℕ) (hx : x < sampleInBallCandidateBudget),
      (cand[x]'(by omega)).toNat = V[8 + x]!.toNat := by
    intro x hx
    rw [getElem!_pos V (8 + x) (by omega)]
    have h1 : x < (V.extract 8 (8 + sampleInBallCandidateBudget)).size := by
      show x < cand.size
      omega
    rw [← ByteArray.getElem_extract h1]
    rfl
  set U := cand.toList.map UInt8.toNat with hU
  have hUlen : U.length = sampleInBallCandidateBudget := by simp [hU, hcandsize]
  have hU128 : streamCandidates f = U.take C := by
    have hlen : (streamCandidates f).length = C := by
      rw [streamCandidates, List.length_ofFn]
    apply List.ext_getElem (by rw [hlen, List.length_take, hUlen]; omega)
    intro x h1 h2
    rw [hlen] at h1
    simp only [List.getElem_take, hU, List.getElem_map, Array.getElem_toList]
    rw [hcandget x (by omega)]
    simp only [streamCandidates, List.getElem_ofFn]
    exact hfV _ _
  have hsel : acceptState (256 - _root_.MLDSA.mldsa44.tau) U _root_.MLDSA.mldsa44.tau =
      some (s128.1, s128.2 ++ U.drop C) := by
    have := acceptState_append (U.drop C) hs128
    rw [hU128, List.take_append_drop] at this
    exact this
  set sgn : ℕ → Bool := fun k =>
    ((V.extract 0 8)[k / 8]! >>> (k % 8).toUInt8 &&& 1 == 1) with hsgn
  have hsign : (fun s : Fin mldsa44.τ => sampleInBallSign f s) = fun s : Fin mldsa44.τ => sgn s := by
    funext s
    have hs : (s : ℕ) < 39 := s.isLt
    simp only [sampleInBallSign, dif_pos (show (s : ℕ) < 64 by omega), hsgn]
    have hbyte : (V.extract 0 8)[(s : ℕ) / 8]! = V[(s : ℕ) / 8]! := by
      have h1 : (s : ℕ) / 8 < (V.extract 0 8).size := by
        rw [ByteArray.size_extract, hVsize]; omega
      rw [getElem!_pos (V.extract 0 8) ((s : ℕ) / 8) (by exact h1), getElem!_pos V ((s : ℕ) / 8) (by omega),
        ByteArray.getElem_extract]
      simp only [Nat.zero_add]
    rw [shiftRight_and_one_beq _ (Nat.mod_lt _ (by norm_num)), hfV, hbyte]
  obtain ⟨sfin, st, hsfin, hst, -, hsize, hval⟩ := step_foldl cand (by decide) sgn hsel
    _root_.MLDSA.mldsa44.tau le_rfl
  have hst' : (List.range' (ringDegree - _root_.MLDSA.mldsa44.tau) _root_.MLDSA.mldsa44.tau).foldl
      (sampleInBallStep cand (ringDegree - _root_.MLDSA.mldsa44.tau) sgn)
      (some (Array.replicate ringDegree 0, 0)) = some st := hst
  unfold sampleInBallPoly?
  simp only [hstream]
  show Option.map (fun st : Array Coeff × ℕ => (Vector.ofFn fun i : Fin ringDegree => st.1[i]! : Rq))
    ((List.range' (ringDegree - _root_.MLDSA.mldsa44.tau) _root_.MLDSA.mldsa44.tau).foldl
      (sampleInBallStep cand (ringDegree - _root_.MLDSA.mldsa44.tau) sgn)
      (some (Array.replicate ringDegree 0, 0))) = _
  rw [hst', Option.map_some]
  apply congrArg some
  rw [← ofCoeff_coeff (Vector.ofFn _)]
  apply congrArg ofCoeff
  funext i
  rw [show coeff (Vector.ofFn fun i : Fin ringDegree => st.1[i]!) i = st.1[i.1]! from
    Vector.get_ofFn _ i]
  rw [hval i i.isLt, hsign, ← MemoryShuffle.shuffleAt_of_le]
  rfl

/-! ### The converse: a successful vendored sampler selects on the fixed stream -/

/-- The vendored candidate search, read back through `nextAccepted`: a successful search from
`cursor` returns the first candidate at most `i` after `cursor` and the cursor just past it. -/
theorem nextAccepted_of_findAccepted (cand : Array UInt8) (i : ℕ) :
    ∀ (fuel cursor : ℕ) {j c : ℕ}, sampleInBallFindAccepted cand i cursor fuel = some (j, c) →
      nextAccepted i ((cand.toList.map UInt8.toNat).drop cursor) =
        some (j, (cand.toList.map UInt8.toNat).drop c) := by
  intro fuel
  induction fuel with
  | zero => intro cursor j c h; simp [sampleInBallFindAccepted] at h
  | succ fuel ih =>
    intro cursor j c h
    rw [sampleInBallFindAccepted] at h
    cases hc : cand[cursor]? with
    | none => rw [hc] at h; simp at h
    | some b =>
      rw [hc] at h
      have hlt : cursor < cand.size := by
        rcases Array.getElem?_eq_some_iff.mp hc with ⟨hlt, -⟩
        exact hlt
      have hb : cand[cursor] = b := by
        rcases Array.getElem?_eq_some_iff.mp hc with ⟨_, hb⟩
        exact hb
      rw [List.drop_eq_getElem_cons (by simpa using hlt)]
      simp only [List.getElem_map, Array.getElem_toList, hb]
      unfold nextAccepted
      dsimp only at h
      split_ifs at h ⊢ with hx
      · cases h; rfl
      · exact ih (cursor + 1) h

/-- **The vendored loop reads the selection**: if the vendored loop survives `n` placements from
the write index `start`, the selection with threshold `start + t` at placement `t` succeeds on
the vendored candidates, its unread candidates those after the loop's cursor. -/
theorem acceptState_of_foldl (cand : Array UInt8) (start : ℕ) (sgn : ℕ → Bool)
    (a₀ : Array Coeff) :
    ∀ (n : ℕ) {st : Array Coeff × ℕ}, (List.range' start n).foldl
        (sampleInBallStep cand start sgn) (some (a₀, 0)) = some st →
      ∃ s, acceptState start (cand.toList.map UInt8.toNat) n = some s ∧
        s.2 = (cand.toList.map UInt8.toNat).drop st.2 := by
  intro n
  induction n with
  | zero =>
    intro st h
    simp only [List.range'_zero, List.foldl_nil, Option.some.injEq] at h
    subst h
    exact ⟨([], _), rfl, rfl⟩
  | succ n ih =>
    intro st h
    rw [List.range'_concat, List.foldl_append, List.foldl_cons, List.foldl_nil] at h
    cases hpre : (List.range' start n).foldl (sampleInBallStep cand start sgn) (some (a₀, 0)) with
    | none => rw [hpre] at h; simp [sampleInBallStep] at h
    | some st₀ =>
      rw [hpre] at h
      obtain ⟨s, hs, hs2⟩ := ih hpre
      simp only [sampleInBallStep, Option.bind_some, Option.map_eq_some_iff] at h
      obtain ⟨⟨j, c⟩, hfind, rfl⟩ := h
      have hnext := nextAccepted_of_findAccepted cand _ _ _ hfind
      rw [← hs2, Nat.one_mul] at hnext
      refine ⟨(s.1 ++ [j], (cand.toList.map UInt8.toNat).drop c), ?_, rfl⟩
      simp only [acceptState, hs, Option.bind_some, hnext, Option.map_some]

/-- **The converse of `fixedStreamChallenge_agree`**: when the vendored bounded sampler
`sampleInBallPoly?` succeeds on `c̃`, the selection on the fixed stream of its whole budget of
`264` candidates succeeds. -/
theorem acceptedCandidates_isSome_of_sampleInBallPoly? {cTilde : CommitHashBytes _root_.MLDSA.mldsa44}
    (h : (sampleInBallPoly? _root_.MLDSA.mldsa44 cTilde).isSome) :
    (acceptedCandidates mldsa44 (xofFin GordieHowe.shake256 (cTilde.toList.map UInt8.toNat)
      (sampleInBallCandidateBudget + 8))).isSome := by
  obtain ⟨V, hV⟩ : ∃ V, SLHDSA.Concrete.Keccak.shake256 (ByteArray.mk cTilde.toList.toArray)
      (8 + sampleInBallCandidateBudget) = V := ⟨_, rfl⟩
  have hVsize : V.size = 8 + sampleInBallCandidateBudget :=
    hV ▸ SLHDSA.Concrete.Keccak.shake256_size _ _
  have hfV : ∀ (b : ℕ) (hb : b < sampleInBallCandidateBudget + 8),
      xofFin GordieHowe.shake256 (cTilde.toList.map UInt8.toNat) (sampleInBallCandidateBudget + 8)
        ⟨b, hb⟩ = V[b]!.toNat := by
    intro b hb
    rw [xofFin_shake256_prefix _ (show sampleInBallCandidateBudget + 8 ≤
        8 + sampleInBallCandidateBudget by omega) ⟨b, hb⟩,
      xofFin_shake256_eq_getElem!, List.map_toUInt8_map_toNat, hV]
  generalize xofFin GordieHowe.shake256 (cTilde.toList.map UInt8.toNat)
    (sampleInBallCandidateBudget + 8) = f at hfV ⊢
  have hstream : shake256List (byteArrayToList (vectorToByteArray cTilde))
      (8 + sampleInBallCandidateBudget) = V := by
    rw [← hV]
    rfl
  set cand := (V.extract 8 (8 + sampleInBallCandidateBudget)).data with hcand
  have hcandsize : cand.size = sampleInBallCandidateBudget := by
    change (V.extract 8 (8 + sampleInBallCandidateBudget)).size = sampleInBallCandidateBudget
    rw [ByteArray.size_extract, hVsize]
    omega
  have hcandget : ∀ (x : ℕ) (hx : x < sampleInBallCandidateBudget),
      (cand[x]'(by omega)).toNat = V[8 + x]!.toNat := by
    intro x hx
    rw [getElem!_pos V (8 + x) (by omega)]
    have h1 : x < (V.extract 8 (8 + sampleInBallCandidateBudget)).size := by
      show x < cand.size
      omega
    rw [← ByteArray.getElem_extract h1]
    rfl
  set U := cand.toList.map UInt8.toNat with hU
  have hUlen : U.length = sampleInBallCandidateBudget := by simp [hU, hcandsize]
  have hUeq : streamCandidates f = U := by
    have hlen : (streamCandidates f).length = sampleInBallCandidateBudget := by
      rw [streamCandidates, List.length_ofFn]
    apply List.ext_getElem (by rw [hlen, hUlen])
    intro x h1 h2
    rw [hlen] at h1
    simp only [hU, List.getElem_map, Array.getElem_toList]
    rw [hcandget x h1]
    simp only [streamCandidates, List.getElem_ofFn]
    exact hfV _ _
  unfold sampleInBallPoly? at h
  simp only [hstream] at h
  generalize hst : List.foldl _ _ _ = o at h
  cases o with
  | none => exact absurd h Bool.false_ne_true
  | some st =>
  obtain ⟨s, hs, -⟩ := acceptState_of_foldl cand _ _ _ _ hst
  unfold acceptedCandidates
  rw [hUeq, Option.isSome_map]
  exact Option.isSome_iff_exists.mpr ⟨s, hs⟩

/-- `fixedStreamChallenge_agree` for the total `SampleInBall` of the primitives record. -/
theorem fixedStreamChallenge_agree_prims {cTilde : CommitHashBytes _root_.MLDSA.mldsa44}
    {c : Fin mldsa44.N → ℤ} (hC : C ≤ sampleInBallCandidateBudget)
    (hc : fixedStreamChallenge mldsa44 (xofFin GordieHowe.shake256 (cTilde.toList.map UInt8.toNat) (C + 8)) =
      some c) :
    (concretePrimitives _root_.MLDSA.mldsa44).sampleInBall cTilde =
      ofCoeff fun k => (c k : Coeff) := by
  simp only [concretePrimitives, sampleInBallPoly]
  rw [fixedStreamChallenge_agree hC hc, Option.getD_some]

end GordieHowe.MLDSA44
