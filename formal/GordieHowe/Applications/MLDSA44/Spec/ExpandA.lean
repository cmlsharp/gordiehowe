-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import LatticeCrypto.MLDSA.ConcretePrimitives
public import GordieHowe.Applications.Keccak.Xof
public import Init.Internal.Order.While

@[expose] public section

/-!
# `ExpandA` (FIPS 204 Algorithms 30 and 32), unbounded and within a byte budget

FIPS 204 Algorithm 30 (`RejNTTPoly`) squeezes SHAKE128 on `ρ ‖ IntegerToBytes(s, 1) ‖
IntegerToBytes(r, 1)` until `256` three-byte candidates are accepted. The vendored
`_root_.MLDSA.Concrete.expandAPoly?` squeezes a fixed number of candidates. This file states the
unbounded algorithm and its bounded form: candidate `k` is the three bytes `[3k, 3k + 3)` of the
SHAKE128 output, read from a squeeze of `3 (k + 1)` bytes (SHAKE output of a given length is a
prefix of every longer output), and decoded by the vendored `decodeCoeffLE3`.

* `rejNTTAccepted ρ r s n`: the accepted coefficients among the first `n` candidates.
* `RejNTTPolyOk ρ r s`: some prefix of the candidates holds `256` acceptances, so Algorithm 30
  terminates.
* `ExpandAOk p ρ`: Algorithm 30 terminates at every entry of the `k × l` matrix, so Algorithm 32
  does.
* `expandAOf h`: Algorithm 32's matrix, computed by searching for the shortest prefix
  (`Nat.find`), given that it terminates; `expandAFull p ρ` is the same matrix as a total
  function (`0` where Algorithm 32 does not terminate), and `expandAOf_eq` relates the two.

FIPS 204 Appendix C permits an implementation to bound the SHAKE128 output `RejNTTPoly` reads, at
no fewer than the `894` bytes of its Table 3; past the bound the algorithm returns an error. The
bounded form reads at most `rejNTTByteBudget = 1008` bytes (`336` candidates) per call:

* `RejNTTPolyWithin ρ r s`: the first `336` candidates hold `256` acceptances, decidable;
  `rejNTTPolyWithin_iff` says this holds exactly when Algorithm 30 terminates and its shortest
  prefix (`Nat.find`) has at most `336` candidates.
* `ExpandAWithin p ρ`: `RejNTTPolyWithin` at every entry, decidable.
* `expandABounded p ρ`: the matrix read from the first `336` candidates of every entry, a total
  computable function; where `ExpandAWithin` holds it is Algorithm 32's matrix
  (`expandABounded_eq_expandAOf`, `expandABounded_eq_expandAFull`).

The vendored `_root_.MLDSA.Concrete.expandAPoly?` reads `768` candidates from one squeeze of
`2304` bytes. Where `RejNTTPolyWithin` holds it returns `rejNTTPolyBounded`
(`expandAPoly?_eq_of_within`), so where `ExpandAWithin` holds the vendored `expandA` and `expandA?`
give `expandABounded` (`expandA_eq_expandABounded`, `expandA?_eq_of_within`). `expandAWithinB`
decides `ExpandAWithin` from one squeeze per entry (`expandAWithinB_iff`). The known-answer test of
the vendored `expandA` (`Test/GordieHoweTest/ExpandA44Check.lean`) evaluates `expandAWithinB` at its
seed, so it tests `expandABounded` too.
-/
namespace GordieHowe.MLDSA44

open _root_.MLDSA _root_.MLDSA.Concrete

/-- **Candidate `k` of `RejNTTPoly`** for the entry at row `row` and column `col` (FIPS 204
Algorithm 30, called by Algorithm 32 on `ρ ‖ IntegerToBytes(col, 1) ‖ IntegerToBytes(row, 1)`):
bytes `3k`, `3k + 1`, `3k + 2` of the SHAKE128 output, decoded by `decodeCoeffLE3` (the top bit of
the third byte masked, rejected at or above `q`). The bytes are read from a squeeze of
`3 (k + 1)` bytes. -/
def rejNTTCandidate (rho : Bytes 32) (row col k : ℕ) : Option Coeff :=
  let stream := shake128Bytes (vectorToByteArray rho ++ ByteArray.mk #[col.toUInt8, row.toUInt8])
    (3 * (k + 1))
  decodeCoeffLE3 stream[3 * k]! stream[3 * k + 1]! stream[3 * k + 2]!

/-- **The accepted coefficients among the first `n` candidates** of `RejNTTPoly`, in order. -/
def rejNTTAccepted (rho : Bytes 32) (row col n : ℕ) : List Coeff :=
  (List.range n).filterMap (rejNTTCandidate rho row col)

/-- **`RejNTTPoly` terminates** at the entry: some prefix of the candidates holds `256`
acceptances. -/
def RejNTTPolyOk (rho : Bytes 32) (row col : ℕ) : Prop :=
  ∃ n, ringDegree ≤ (rejNTTAccepted rho row col n).length

/-- **`RejNTTPoly`'s polynomial** (FIPS 204 Algorithm 30) when it terminates: the first `256`
accepted coefficients, read from the shortest prefix of candidates holding them.

Running time: `Nat.find` evaluates `rejNTTAccepted` on the prefixes `0, 1, …, n` for the
shortest sufficient `n`, each a SHAKE128 evaluation per candidate, so it is polynomial in `n`;
`n` depends on the seed and is not bounded in advance (`RejNTTPolyOk` only says it exists). -/
def rejNTTPolyOf {rho : Bytes 32} {row col : ℕ} (h : RejNTTPolyOk rho row col) : Tq :=
  LatticeCrypto.TransformPoly.ofPoly
    (Vector.ofFn fun i : Fin ringDegree => (rejNTTAccepted rho row col (Nat.find h)).getD i 0)

/-- **`ExpandA` terminates** (FIPS 204 Algorithm 32): `RejNTTPoly` terminates at every entry of
the `k × l` matrix. -/
def ExpandAOk (p : Params) (rho : Bytes 32) : Prop :=
  ∀ (i : Fin p.k) (j : Fin p.l), RejNTTPolyOk rho i j

/-- **`ExpandA(ρ)`** (FIPS 204 Algorithm 32) when it terminates: the `k × l` matrix of
`RejNTTPoly` polynomials.

Running time: `k · l` evaluations of `rejNTTPolyOf`. -/
def expandAOf {p : Params} {rho : Bytes 32} (h : ExpandAOk p rho) : TqMatrix p.k p.l :=
  Vector.ofFn fun i : Fin p.k => Vector.ofFn fun j : Fin p.l => rejNTTPolyOf (h i j)

/-- **`ExpandA(ρ)` as a total function** (FIPS 204 Algorithm 32): `expandAOf` where it terminates,
the zero matrix where it does not. Noncomputable: whether it terminates is not decided. -/
noncomputable def expandAFull (p : Params) (rho : Bytes 32) : TqMatrix p.k p.l :=
  open Classical in
  if h : ExpandAOk p rho then expandAOf h else Vector.replicate p.k (Vector.replicate p.l 0)

/-- Where `ExpandA` terminates, `expandAOf` is `expandAFull`. -/
theorem expandAOf_eq {p : Params} {rho : Bytes 32} (h : ExpandAOk p rho) :
    expandAOf h = expandAFull p rho := by
  unfold expandAFull
  simp [h]

/-! ### The bounded form (FIPS 204 Appendix C) -/

/-- **The SHAKE128 output bytes a bounded `RejNTTPoly` reads**: `1008`, six SHAKE128 blocks of
`168` bytes, at least the `894` bytes FIPS 204 Appendix C, Table 3 requires of a bounded
`RejNTTPoly` (`fips204_le_rejNTTByteBudget`). -/
def rejNTTByteBudget : ℕ := 1008

/-- **The candidates within the byte budget**: `rejNTTByteBudget / 3 = 336` three-byte
candidates. -/
def rejNTTCandidateBudget : ℕ := rejNTTByteBudget / 3

/-- The byte budget is at least FIPS 204 Appendix C, Table 3's minimum for `RejNTTPoly`, `894`
bytes. -/
theorem fips204_le_rejNTTByteBudget : 894 ≤ rejNTTByteBudget := by decide

/-- The candidate budget is `336`. -/
theorem rejNTTCandidateBudget_eq : rejNTTCandidateBudget = 336 := rfl

/-- The candidates of the budget fit in the byte budget: `3 · 336 = 1008`. -/
theorem three_mul_rejNTTCandidateBudget : 3 * rejNTTCandidateBudget = rejNTTByteBudget := rfl

/-- The accepted coefficients of a shorter prefix of candidates are a prefix of those of a longer
one. -/
theorem rejNTTAccepted_prefix (rho : Bytes 32) (row col : ℕ) {m n : ℕ} (h : m ≤ n) :
    rejNTTAccepted rho row col m <+: rejNTTAccepted rho row col n := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
  rw [rejNTTAccepted, rejNTTAccepted, List.range_add, List.filterMap_append]
  exact List.prefix_append _ _

/-- A coefficient accepted among the first `m` candidates is the same among the first `n ≥ m`. -/
theorem rejNTTAccepted_getD_of_le (rho : Bytes 32) (row col : ℕ) {m n i : ℕ} (h : m ≤ n)
    (hi : i < (rejNTTAccepted rho row col m).length) :
    (rejNTTAccepted rho row col m).getD i 0 = (rejNTTAccepted rho row col n).getD i 0 := by
  have hp := rejNTTAccepted_prefix rho row col h
  rw [List.getD_eq_getElem _ _ hi, List.getD_eq_getElem _ _ (lt_of_lt_of_le hi hp.length_le)]
  exact hp.getElem hi

/-- **`RejNTTPoly` finishes within the byte budget** at the entry (FIPS 204 Algorithm 30 with its
SHAKE128 output bounded as Appendix C permits): the first `rejNTTCandidateBudget` candidates hold
`256` acceptances. -/
def RejNTTPolyWithin (rho : Bytes 32) (row col : ℕ) : Prop :=
  ringDegree ≤ (rejNTTAccepted rho row col rejNTTCandidateBudget).length

instance (rho : Bytes 32) (row col : ℕ) : Decidable (RejNTTPolyWithin rho row col) :=
  Nat.decLe _ _

/-- Within the byte budget, `RejNTTPoly` terminates. -/
theorem RejNTTPolyWithin.ok {rho : Bytes 32} {row col : ℕ} (h : RejNTTPolyWithin rho row col) :
    RejNTTPolyOk rho row col :=
  ⟨_, h⟩

/-- **`RejNTTPoly` finishes within the byte budget exactly when it terminates and its shortest
sufficient prefix has at most `rejNTTCandidateBudget` candidates.** -/
theorem rejNTTPolyWithin_iff {rho : Bytes 32} {row col : ℕ} :
    RejNTTPolyWithin rho row col ↔ ∃ h : RejNTTPolyOk rho row col, Nat.find h ≤ rejNTTCandidateBudget := by
  refine ⟨fun h => ⟨h.ok, Nat.find_min' _ h⟩, fun ⟨h, hle⟩ => ?_⟩
  exact (Nat.find_spec h).trans (rejNTTAccepted_prefix rho row col hle).length_le

/-- **`RejNTTPoly`'s polynomial within the byte budget**: the first `256` accepted coefficients
among the first `rejNTTCandidateBudget` candidates (`0` past the accepted ones). Where
`RejNTTPolyWithin` holds it is Algorithm 30's polynomial (`rejNTTPolyBounded_eq`).

Running time: `rejNTTCandidateBudget` SHAKE128 evaluations of at most `rejNTTByteBudget`
bytes. -/
def rejNTTPolyBounded (rho : Bytes 32) (row col : ℕ) : Tq :=
  LatticeCrypto.TransformPoly.ofPoly
    (Vector.ofFn fun i : Fin ringDegree => (rejNTTAccepted rho row col rejNTTCandidateBudget).getD i 0)

/-- **Within the byte budget, the bounded `RejNTTPoly` is the unbounded one.** -/
theorem rejNTTPolyBounded_eq {rho : Bytes 32} {row col : ℕ} (h : RejNTTPolyWithin rho row col) :
    rejNTTPolyBounded rho row col = rejNTTPolyOf h.ok := by
  unfold rejNTTPolyBounded rejNTTPolyOf
  congr 2
  funext i
  exact (rejNTTAccepted_getD_of_le rho row col (Nat.find_min' h.ok h)
    (lt_of_lt_of_le i.isLt (Nat.find_spec h.ok))).symm

/-- **`ExpandA` finishes within the byte budget** (FIPS 204 Algorithm 32 with every
`RejNTTPoly` call bounded as Appendix C permits): `RejNTTPolyWithin` at every entry of the
`k × l` matrix. -/
def ExpandAWithin (p : Params) (rho : Bytes 32) : Prop :=
  ∀ (i : Fin p.k) (j : Fin p.l), RejNTTPolyWithin rho i j

instance (p : Params) (rho : Bytes 32) : Decidable (ExpandAWithin p rho) := by
  unfold ExpandAWithin
  infer_instance

/-- Within the byte budget, `ExpandA` terminates. -/
theorem ExpandAWithin.ok {p : Params} {rho : Bytes 32} (h : ExpandAWithin p rho) :
    ExpandAOk p rho :=
  fun i j => (h i j).ok

/-- **`ExpandA(ρ)` within the byte budget**: the `k × l` matrix of `rejNTTPolyBounded`
polynomials. Where `ExpandAWithin` holds it is Algorithm 32's matrix
(`expandABounded_eq_expandAOf`, `expandABounded_eq_expandAFull`).

Running time: `k · l` evaluations of `rejNTTPolyBounded`. -/
def expandABounded (p : Params) (rho : Bytes 32) : TqMatrix p.k p.l :=
  Vector.ofFn fun i : Fin p.k => Vector.ofFn fun j : Fin p.l => rejNTTPolyBounded rho i j

/-- **Within the byte budget, the bounded `ExpandA` is the unbounded one** (`Nat.find`). -/
theorem expandABounded_eq_expandAOf {p : Params} {rho : Bytes 32} (h : ExpandAWithin p rho) :
    expandABounded p rho = expandAOf h.ok := by
  unfold expandABounded expandAOf
  congr 1
  funext i
  congr 1
  funext j
  exact rejNTTPolyBounded_eq (h i j)

/-- **Within the byte budget, the bounded `ExpandA` is `expandAFull`.** -/
theorem expandABounded_eq_expandAFull {p : Params} {rho : Bytes 32} (h : ExpandAWithin p rho) :
    expandABounded p rho = expandAFull p rho :=
  (expandABounded_eq_expandAOf h).trans (expandAOf_eq h.ok)

/-! ### The vendored `ExpandA`

`_root_.MLDSA.Concrete.expandAPoly?` walks the `768` three-byte candidates of one squeeze of
`2304` SHAKE128 bytes with a `while` loop, keeping the decoded ones until `256` are kept. In this
toolchain a `while` loop is `Lean.Loop.forIn`; `Lean.Loop.forIn_eq_of_monadTail` unfolds it in
`Id`. -/

section RejectionLoop

variable {δ : Type} (n bound step : ℕ) (cand : ℕ → Option δ)

/-- **The rejection loop** of `expandAPoly?`: starting from `out` and `cursor`, append the
candidate `cand cursor` when it decodes, advance `cursor` by `step`, and repeat while
`out.size < n` and `cursor + step ≤ bound`. -/
def rejectionLoop (out : Array δ) (cursor : ℕ) : Array δ :=
  Id.run do
    let mut out := out
    let mut cursor := cursor
    while out.size < n ∧ cursor + step ≤ bound do
      match cand cursor with
      | some c => out := out.push c
      | none => pure ()
      cursor := cursor + step
    return out

/-- One-step unfolding of `rejectionLoop`. -/
theorem rejectionLoop_unfold (out : Array δ) (cursor : ℕ) :
    rejectionLoop n bound step cand out cursor =
      if out.size < n ∧ cursor + step ≤ bound then
        rejectionLoop n bound step cand ((cand cursor).elim out out.push) (cursor + step)
      else out := by
  show (Lean.Loop.forIn (m := Id) { } (out, cursor)
    (fun _ (s : Array δ × ℕ) =>
      if s.1.size < n ∧ s.2 + step ≤ bound then
        (match cand s.2 with
        | some c => pure (ForInStep.yield (s.1.push c, s.2 + step))
        | none => pure (ForInStep.yield (s.1, s.2 + step)))
      else pure (ForInStep.done (s.1, s.2)))).run.1 = _
  rw [Lean.Loop.forIn_eq_of_monadTail]
  split
  · cases cand cursor <;> rfl
  · rfl

/-- `rejectionLoop`'s output is `out` followed by the first `n - out.size` decoded candidates
among `cand cursor, cand (cursor + step), …` before `bound`, in order. -/
theorem rejectionLoop_toList_eq (hstep : 0 < step) :
    ∀ (m : ℕ) (out : Array δ) (cursor : ℕ), bound - cursor ≤ m →
      (rejectionLoop n bound step cand out cursor).toList =
        out.toList ++ ((List.range ((bound - cursor) / step)).filterMap
          (fun j => cand (cursor + step * j))).take (n - out.toList.length) := by
  intro m
  induction m using Nat.strongRecOn with
  | _ m ih =>
    intro out cursor hm
    rw [rejectionLoop_unfold]
    by_cases hcond : out.size < n ∧ cursor + step ≤ bound
    · rw [ite_eq_left hcond]
      obtain ⟨hn, hb⟩ := hcond
      have hkdiv : (bound - cursor) / step = (bound - (cursor + step)) / step + 1 := by
        rw [show bound - cursor = step + (bound - (cursor + step)) by omega, Nat.add_comm,
          Nat.add_div_right _ hstep]
      have hm' : bound - (cursor + step) < m := by omega
      rw [ih _ hm' _ (cursor + step) (Nat.le_refl _), hkdiv, List.range_succ_eq_map,
        List.filterMap_cons, List.filterMap_map]
      have hcandeq : (fun j => cand (cursor + step * j)) ∘ Nat.succ =
          fun j => cand (cursor + step + step * j) := by
        funext j
        simp only [Function.comp_apply, Nat.mul_succ]
        congr 1
        omega
      rw [hcandeq, Nat.mul_zero, Nat.add_zero]
      have hlen : out.toList.length < n := by simpa [Array.length_toList] using hn
      cases hc : cand cursor with
      | none => rfl
      | some c =>
        simp only [Option.elim, Array.toList_push, List.length_append, List.length_singleton]
        rw [List.append_assoc, List.singleton_append,
          show n - out.toList.length = (n - out.toList.length - 1).succ by omega,
          List.take_succ_cons,
          show n - (out.toList.length + 1) = n - out.toList.length - 1 by omega]
    · rw [ite_eq_right hcond]
      by_cases hA : out.size < n
      · have hB : ¬ cursor + step ≤ bound := fun hB => hcond ⟨hA, hB⟩
        have : (bound - cursor) / step = 0 := Nat.div_eq_of_lt (by omega)
        rw [this, List.range_zero, List.filterMap_nil, List.take_nil, List.append_nil]
      · have hlen0 : n - out.toList.length = 0 := by
          simp only [Array.length_toList]; omega
        rw [hlen0, List.take_zero, List.append_nil]

end RejectionLoop

/-- The vendored `shake128Bytes` output at a position does not depend on the requested length,
as long as the position is within range for both requests. -/
theorem shake128Bytes_getElem!_prefix (input : ByteArray) {m m' k : ℕ} (hk : k < m)
    (hm : m ≤ m') : (shake128Bytes input m)[k]! = (shake128Bytes input m')[k]! := by
  unfold shake128Bytes SLHDSA.Concrete.Keccak.shake128
  exact Keccak.squeezeXof_prefix _ (by decide) hk hm

/-- **The candidates of one squeeze**: candidate `j < m` of one squeeze of `3m` SHAKE128 bytes is
`rejNTTCandidate`. -/
theorem decodeCoeffLE3_stream_eq (rho : Bytes 32) (row col : ℕ) {m j : ℕ} (hj : j < m) :
    decodeCoeffLE3
        (shake128Bytes (vectorToByteArray rho ++ ByteArray.mk #[col.toUInt8, row.toUInt8])
          (3 * m))[3 * j]!
        (shake128Bytes (vectorToByteArray rho ++ ByteArray.mk #[col.toUInt8, row.toUInt8])
          (3 * m))[3 * j + 1]!
        (shake128Bytes (vectorToByteArray rho ++ ByteArray.mk #[col.toUInt8, row.toUInt8])
          (3 * m))[3 * j + 2]! =
      rejNTTCandidate rho row col j := by
  have hle : 3 * (j + 1) ≤ 3 * m := by omega
  unfold rejNTTCandidate
  dsimp only
  rw [shake128Bytes_getElem!_prefix _ (show 3 * j < 3 * (j + 1) by omega) hle,
    shake128Bytes_getElem!_prefix _ (show 3 * j + 1 < 3 * (j + 1) by omega) hle,
    shake128Bytes_getElem!_prefix _ (show 3 * j + 2 < 3 * (j + 1) by omega) hle]

/-- **The accepted coefficients from one squeeze**: the decoded candidates among the `n`
three-byte candidates of one squeeze of `3n` SHAKE128 bytes, in order. They are
`rejNTTAccepted` (`rejNTTAcceptedOneSqueeze_eq`), which squeezes once per candidate.

Running time: one SHAKE128 evaluation of `3n` bytes and `n` decodings. -/
def rejNTTAcceptedOneSqueeze (rho : Bytes 32) (row col n : ℕ) : List Coeff :=
  let stream := shake128Bytes (vectorToByteArray rho ++ ByteArray.mk #[col.toUInt8, row.toUInt8])
    (3 * n)
  (List.range n).filterMap fun j =>
    decodeCoeffLE3 stream[3 * j]! stream[3 * j + 1]! stream[3 * j + 2]!

/-- The accepted coefficients from one squeeze are `rejNTTAccepted`. -/
theorem rejNTTAcceptedOneSqueeze_eq (rho : Bytes 32) (row col n : ℕ) :
    rejNTTAcceptedOneSqueeze rho row col n = rejNTTAccepted rho row col n := by
  unfold rejNTTAcceptedOneSqueeze rejNTTAccepted
  apply List.filterMap_congr
  intro j hj
  exact decodeCoeffLE3_stream_eq rho row col (List.mem_range.mp hj)

/-- **`ExpandAWithin` from one squeeze per entry**: the first `rejNTTCandidateBudget` candidates
of one squeeze of `rejNTTByteBudget` bytes hold `256` acceptances at every entry; it decides
`ExpandAWithin` (`expandAWithinB_iff`).

Running time: `k · l` SHAKE128 evaluations of `rejNTTByteBudget` bytes. -/
def expandAWithinB (p : Params) (rho : Bytes 32) : Bool :=
  decide (∀ (i : Fin p.k) (j : Fin p.l),
    ringDegree ≤ (rejNTTAcceptedOneSqueeze rho i j rejNTTCandidateBudget).length)

/-- `expandAWithinB` decides `ExpandAWithin`. -/
theorem expandAWithinB_iff (p : Params) (rho : Bytes 32) :
    expandAWithinB p rho = true ↔ ExpandAWithin p rho := by
  unfold expandAWithinB ExpandAWithin RejNTTPolyWithin
  simp only [decide_eq_true_eq, rejNTTAcceptedOneSqueeze_eq]

/-- The candidate budget of the bounded form is at most the vendored one: `336 ≤ 768`. -/
theorem rejNTTCandidateBudget_le : rejNTTCandidateBudget ≤ expandACandidateBudget := by decide

/-- **Within the byte budget, the vendored `RejNTTPoly` is the bounded one**: where
`RejNTTPolyWithin` holds, the vendored `expandAPoly?` (`768` candidates) returns
`rejNTTPolyBounded` (`336` candidates): its first `256` decoded candidates lie among the first
`336`. -/
theorem expandAPoly?_eq_of_within {rho : Bytes 32} {row col : ℕ}
    (h : RejNTTPolyWithin rho row col) :
    expandAPoly? rho row col = some (rejNTTPolyBounded rho row col) := by
  unfold expandAPoly?
  extract_lets seed stream out0 cursor0 coeffs
  have hseed : seed = vectorToByteArray rho ++ ByteArray.mk #[col.toUInt8, row.toUInt8] := rfl
  have hstream : stream = shake128Bytes seed (3 * expandACandidateBudget) := rfl
  have hout0 : out0 = #[] := rfl
  have hcursor0 : cursor0 = 0 := rfl
  clear_value stream
  have hcoeffs : coeffs = rejectionLoop ringDegree stream.size 3
      (fun cursor => decodeCoeffLE3 stream[cursor]! stream[cursor + 1]! stream[cursor + 2]!)
      out0 cursor0 := by
    simp only [coeffs, rejectionLoop, Id.run]
    congr 1
    congr 1
    funext u s
    split
    · cases decodeCoeffLE3 stream[s.2]! stream[s.2 + 1]! stream[s.2 + 2]! <;> rfl
    · rfl
  clear_value coeffs out0 cursor0 seed
  subst hseed hout0 hcursor0
  have hcand0 : ∀ j < expandACandidateBudget,
      decodeCoeffLE3 stream[0 + 3 * j]! stream[0 + 3 * j + 1]! stream[0 + 3 * j + 2]! =
        rejNTTCandidate rho row col j := by
    intro j hj
    simp only [Nat.zero_add]
    rw [hstream]
    exact decodeCoeffLE3_stream_eq rho row col hj
  have hsize : stream.size = 3 * expandACandidateBudget := by
    rw [hstream]; exact SLHDSA.Concrete.Keccak.shake128_size _ _
  have hloop := rejectionLoop_toList_eq ringDegree stream.size 3
    (fun cursor => decodeCoeffLE3 stream[cursor]! stream[cursor + 1]! stream[cursor + 2]!)
    (by norm_num) _ #[] 0 (Nat.le_refl _)
  rw [← hcoeffs] at hloop
  -- The decoded candidates of the vendored stream are `rejNTTCandidate`'s.
  have hcand : (List.range ((stream.size - 0) / 3)).filterMap
      (fun j => decodeCoeffLE3 stream[0 + 3 * j]! stream[0 + 3 * j + 1]! stream[0 + 3 * j + 2]!) =
      rejNTTAccepted rho row col expandACandidateBudget := by
    rw [hsize, Nat.sub_zero, Nat.mul_div_cancel_left _ (by norm_num), rejNTTAccepted]
    apply List.filterMap_congr
    intro j hj
    exact hcand0 j (List.mem_range.mp hj)
  rw [hcand] at hloop
  simp only [List.nil_append, List.length_nil, Nat.sub_zero] at hloop
  -- The first `256` decoded candidates lie among the first `336`.
  have hpre := rejNTTAccepted_prefix rho row col rejNTTCandidateBudget_le
  have htake : (rejNTTAccepted rho row col expandACandidateBudget).take ringDegree =
      (rejNTTAccepted rho row col rejNTTCandidateBudget).take ringDegree := by
    obtain ⟨t, ht⟩ := hpre
    rw [← ht, List.take_append_of_le_length h]
  rw [htake] at hloop
  have hlen : coeffs.size = ringDegree := by
    rw [← Array.length_toList, hloop, List.length_take]
    exact Nat.min_eq_left h
  have hentries : (fun i : Fin ringDegree => coeffs[i]!) =
      fun i : Fin ringDegree => (rejNTTAccepted rho row col rejNTTCandidateBudget).getD i 0 := by
    funext i
    have hi : i.val < coeffs.size := by rw [hlen]; exact i.isLt
    show coeffs[i.val]! = _
    rw [getElem!_pos coeffs i.val hi, ← Array.getElem_toList hi]
    simp only [hloop, List.getElem_take]
    exact (List.getD_eq_getElem _ _ (lt_of_lt_of_le i.isLt h)).symm
  rw [ite_eq_right (by rw [hlen]; exact lt_irrefl _), hentries]
  rfl

/-- **Within the byte budget, the vendored `ExpandA` is `expandABounded`.** -/
theorem expandA_eq_expandABounded {p : Params} {rho : Bytes 32} (h : ExpandAWithin p rho) :
    expandA p rho = expandABounded p rho := by
  unfold expandA expandABounded expandAPoly
  congr 1
  funext i
  congr 1
  funext j
  rw [expandAPoly?_eq_of_within (h i j)]
  rfl

/-- **Within the byte budget, the vendored bounded `ExpandA` succeeds with `expandABounded`.** -/
theorem expandA?_eq_of_within {p : Params} {rho : Bytes 32} (h : ExpandAWithin p rho) :
    expandA? p rho = some (expandABounded p rho) := by
  unfold expandA?
  rw [ite_eq_left fun i j => by rw [expandAPoly?_eq_of_within (h i j)]; rfl,
    expandA_eq_expandABounded h]

end GordieHowe.MLDSA44
