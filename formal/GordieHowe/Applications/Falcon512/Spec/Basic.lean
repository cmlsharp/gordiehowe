-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Applications.Params
public import GordieHowe.Applications.Spec.Rq
public import GordieHowe.Applications.Keccak.Bytes
public import GordieHowe.Applications.Keccak.Xof
public import GordieHowe.Foundations.ToMathlib.UInt8
public import GordieHowe.Foundations.ToMathlib.Fintype
public import LatticeCrypto.Falcon.ConcretePrimitives
public import Init.Internal.Order.While

@[expose] public section

/-!
# Falcon-512 verification

Layer 0 for Falcon verification is the vendored `_root_.Falcon.verify`
(`Vendor/LatticeCrypto/Falcon/Verify.lean`), closed over a keyless instantiation of
`Falcon.VerifyPrimitives` built from the vendored `Falcon.Concrete.hashToPoint`, `publicKeyBytes`
and `decompress` (`Vendor/LatticeCrypto/Falcon/ConcretePrimitives.lean`,
`Vendor/LatticeCrypto/Falcon/Concrete/Encoding.lean`). `GordieHowe.falcon512` (`GordieHowe/Applications/Params.lean`) is the
parameter record of the circuits; `falcon512_matches` checks it against the vendored
`Falcon.Concrete.params512`.

`HashToPoint` (Falcon specification v1.2, Algorithm 3) draws 16-bit big-endian samples from
`SHAKE256(salt ‖ msg)` and keeps those below `5q`, reduced mod `q`, until `n` are accepted.
`Falcon.Concrete.hashToPoint` (the vendored concrete primitive) extends this with the FIPS 206
draft's raw-message binding to a verification-key byte string; our `prims512` supplies an empty
verification-key string, recovering the classic Algorithm 3. The circuits' fixed-stream form of
`HashToPoint` is `acceptedCandidates`, whose values reduced mod `q` are the coefficients: the
circuit draws `S = n + 127` samples and fails otherwise. The local concrete adapter in
`Vendor/LatticeCrypto/Falcon/ConcretePrimitives.lean` uses
a larger budget (`n + n / 2 + 256`) and returns `none` if it runs out, so `verify` rejects.
`fixedStreamChallenge_agree` states that the adapter succeeds with the same point when the shorter
circuit stream succeeds. This adapter is not an unbounded sampler and has not been validated against
Falcon known-answer vectors.

`verify` takes the message as the vendored byte type `List UInt8`. The circuit definitions
(`GordieHowe.Falcon512.streamCandidates`, `GordieHowe.Falcon512.acceptedCandidates`) read bytes as
naturals below `256`, the representation of the H circuit and the SHAKE256 gadget;
`fixedStreamChallenge_agree` relates the two through `List.map UInt8.toNat`.
-/

namespace GordieHowe

namespace Falcon512

variable (P : Params)

/-- The sample stream: `2S` bytes of `SHAKE256(nonce ‖ msg)` as 16-bit values. -/
def streamCandidates (shake : XOF) (nonce msg : List ℕ) : Fin P.S → ℕ :=
  samples16 (xofFin shake (nonce ++ msg) (2 * P.S))

/-- The first `n` samples below `5q`, before reduction. This is what the H circuit shares with the A
circuit. -/
def acceptedCandidates (shake : XOF) (nonce msg : List ℕ) : Option (Fin P.n → ℕ) :=
  firstAccepted (fun v => decide (v < P.bound)) (streamCandidates P shake nonce msg) P.n

/-- `GordieHowe.falcon512`'s modulus and degree match the vendored `Falcon.Concrete.params512`
(the computable stand-in for `Falcon.falcon512` that `Falcon.Concrete.verify512`
closes over; see `Vendor/LatticeCrypto/Falcon/ConcretePrimitives.lean`). -/
theorem falcon512_matches :
    GordieHowe.falcon512.q = _root_.Falcon.modulus ∧
      GordieHowe.falcon512.n = _root_.Falcon.Concrete.params512.n := by
  decide

/-- Keyless Falcon-512 verification primitives: `hashToPoint` ignores its
verification-key argument and uses Algorithm 3's input and acceptance rule
(`SHAKE256(salt ‖ msg)`, no key bound in), with the finite candidate budget
and exhaustion behavior documented above, by calling the vendored
`Falcon.Concrete.hashToPoint` with an empty verification-key byte string.
`publicKeyBytes` and `decompress` reuse the vendored `Falcon.Concrete.publicKeyBytes`
and `Falcon.Concrete.decompress` unchanged (`publicKeyBytes` is consequently never
read by `_root_.Falcon.verify`, since `hashToPoint` ignores the key it would produce). -/
def prims512 : _root_.Falcon.VerifyPrimitives _root_.Falcon.Concrete.params512 where
  publicKeyBytes h := _root_.Falcon.Concrete.publicKeyBytes _root_.Falcon.Concrete.params512.logn h
  hashToPoint salt _vrfyKey msg := _root_.Falcon.Concrete.hashToPoint 512 salt ByteArray.empty msg
  decompress bytes dlen := _root_.Falcon.Concrete.decompress 512 bytes dlen

/-- Falcon-512 verification (Algorithm 16) of the message bytes `msg`, closed over the
keyless `prims512`. Wraps the vendored `_root_.Falcon.verify`. -/
def verify (pk : _root_.Falcon.PublicKey _root_.Falcon.Concrete.params512) (msg : List UInt8)
    (sig : _root_.Falcon.Signature) : Prop :=
  _root_.Falcon.verify _root_.Falcon.Concrete.params512 prims512 pk msg sig = true

/-! ### Characterizing `Falcon.Concrete.hashToPoint`'s `Id.run do` loops

`Falcon.Concrete.hashToPoint`'s body is `Id.run do` with one `while` loop that walks
candidates from a byte stream, keeping the accepted ones (reduced mod the modulus) until `n`
are collected or the stream is exhausted; fewer than `n` acceptances give `none`.
In this toolchain a `while` loop is `Lean.Loop.forIn`, built on `repeatM`; unfolding it needs
`Lean.Loop.forIn_eq_of_monadTail` (`Init/Internal/Order/While.lean`), which holds for `Id`.

The lemmas below characterize this exact loop shape in general: general in `n`, in the
candidate-stepping `bound`/`step`, and in the candidate/accept/reduce functions, not unfolded
over any concrete stream length. `hashToPoint`'s own loop is the instance with `step = 2`
(2-byte candidates), `cand cursor` the 16-bit big-endian value at byte `cursor`, `accept d`
the acceptance test `d < 5 * modulus`, and `reduce d` the reduction `d % modulus`. -/

section HashToPointLoop

variable {γ δ : Type} (n bound step : ℕ) (cand : ℕ → γ) (accept : γ → Prop)
  [DecidablePred accept] (reduce : γ → δ)

/-- The first loop: starting from `out` and `cursor`, append `reduce (cand cursor)` when
`accept (cand cursor)` holds, advance `cursor` by `step`, and repeat while `out.size < n` and
`cursor` has not reached `bound`. -/
def loop1 (out : Array δ) (cursor : ℕ) : Array δ × ℕ :=
  Id.run do
    let mut out := out
    let mut cursor := cursor
    while out.size < n ∧ cursor + step ≤ bound do
      if accept (cand cursor) then out := out.push (reduce (cand cursor))
      cursor := cursor + step
    return (out, cursor)

/-- One-step unfolding of `loop1`, from `Lean.Loop.forIn_eq_of_monadTail`. -/
theorem loop1_unfold (out : Array δ) (cursor : ℕ) :
    loop1 n bound step cand accept reduce out cursor =
      if out.size < n ∧ cursor + step ≤ bound then
        loop1 n bound step cand accept reduce
          (if accept (cand cursor) then out.push (reduce (cand cursor)) else out) (cursor + step)
      else (out, cursor) := by
  show (Lean.Loop.forIn (m := Id) { } (out, cursor)
    (fun _ (s : Array δ × ℕ) =>
      if s.1.size < n ∧ s.2 + step ≤ bound then
        (if accept (cand s.2) then
          pure (ForInStep.yield (s.1.push (reduce (cand s.2)), s.2 + step))
        else pure (ForInStep.yield (s.1, s.2 + step)))
      else pure (ForInStep.done (s.1, s.2)))).run = _
  rw [Lean.Loop.forIn_eq_of_monadTail]
  split
  · split
    · rfl
    · rfl
  · rfl

/-- `loop1`'s output is `out` followed by the first `n - out.size` accepted-and-reduced
candidates among `cand cursor, cand (cursor + step), …`, up to `bound`, in order. -/
theorem loop1_toList_eq (hstep : 0 < step) :
    ∀ (m : ℕ) (out : Array δ) (cursor : ℕ), bound - cursor ≤ m →
      (loop1 n bound step cand accept reduce out cursor).1.toList =
        out.toList ++ ((((List.range ((bound - cursor) / step)).map
            (fun j => cand (cursor + step * j))).filter (fun d => decide (accept d))).map
              reduce).take (n - out.toList.length) := by
  intro m
  induction m using Nat.strongRecOn with
  | _ m ih =>
    intro out cursor hm
    rw [loop1_unfold]
    by_cases hcond : out.size < n ∧ cursor + step ≤ bound
    · rw [ite_eq_left hcond]
      obtain ⟨hn, hb⟩ := hcond
      have hlen_eq : out.toList.length = out.size := Array.length_toList
      have hkdiv : (bound - cursor) / step = (bound - (cursor + step)) / step + 1 := by
        rw [show bound - cursor = step + (bound - (cursor + step)) by omega, Nat.add_comm,
          Nat.add_div_right _ hstep]
      have hm' : bound - (cursor + step) < m := by omega
      rw [ih _ hm' _ (cursor + step) (Nat.le_refl _), hkdiv, List.range_succ_eq_map]
      have hcandeq : ∀ j : ℕ, cand (cursor + step * j.succ) = cand (cursor + step + step * j) := by
        intro j; congr 1; rw [Nat.mul_succ]; omega
      simp only [List.map_cons, List.map_map, Function.comp_def, hcandeq, Nat.mul_zero,
        Nat.add_zero]
      have hlen : out.toList.length < n := by simpa [Array.length_toList] using hn
      by_cases hacc : accept (cand cursor)
      · rw [ite_eq_left hacc,
          List.filter_cons_of_pos (p := fun d => decide (accept d)) (decide_eq_true_iff.mpr hacc),
          List.map_cons, Array.toList_push]
        simp only [List.length_append, List.length_singleton]
        rw [List.append_assoc, List.singleton_append,
          show n - out.toList.length = (n - out.toList.length - 1).succ by omega,
          List.take_succ_cons,
          show n - (out.toList.length + 1) = n - out.toList.length - 1 by omega]
      · rw [ite_eq_right hacc, List.filter_cons_of_neg (p := fun d => decide (accept d))
          (fun h => hacc (decide_eq_true_iff.mp h))]
    · rw [ite_eq_right hcond]
      by_cases hA : out.size < n
      · have hB : ¬ cursor + step ≤ bound := fun hB => hcond ⟨hA, hB⟩
        have : (bound - cursor) / step = 0 := Nat.div_eq_of_lt (by omega)
        rw [this, List.range_zero, List.map_nil, List.filter_nil, List.map_nil, List.take_nil,
          List.append_nil]
      · have hlen0 : n - out.toList.length = 0 := by
          simp only [Array.length_toList]; omega
        rw [hlen0, List.take_zero, List.append_nil]

/-- The loop of `hashToPoint`, run from the empty array: the first `n` accepted-and-reduced
candidates found before `bound`. -/
theorem oneLoop_toList_eq (hstep : 0 < step) :
    (Id.run do
      let mut out : Array δ := #[]
      let mut cursor := 0
      while out.size < n ∧ cursor + step ≤ bound do
        if accept (cand cursor) then out := out.push (reduce (cand cursor))
        cursor := cursor + step
      return out).toList =
      ((((List.range (bound / step)).map (fun j => cand (step * j))).filter
        (fun d => decide (accept d))).map reduce).take n := by
  show (loop1 n bound step cand accept reduce #[] 0).1.toList = _
  rw [loop1_toList_eq n bound step cand accept reduce hstep (bound - 0) #[] 0 (Nat.le_refl _)]
  simp

end HashToPointLoop

/-- The fixed-stream samples of the circuit definitions are the 16-bit big-endian candidates of the
larger-budget SHAKE256 stream that `prims512.hashToPoint` reads (prefix consistency of `shake256`).
-/
theorem samples16_xofFin_shake256_eq_stream {salt : _root_.Falcon.Bytes 40} {msg : List UInt8}
    {stream : ByteArray}
    (hstream : SLHDSA.Concrete.Keccak.shake256
      (ByteArray.mk salt.toArray ++ ByteArray.empty ++
        ByteArray.mk (List.toArray (α := _root_.Falcon.Byte) msg))
      (2 * _root_.Falcon.Concrete.hashToPointCandidateBudget 512) = stream)
    (j : Fin falcon512.S) :
    samples16 (xofFin GordieHowe.shake256 (salt.toList.map UInt8.toNat ++ msg.map UInt8.toNat)
      (2 * falcon512.S)) j =
      stream[2 * (j : ℕ)]!.toNat <<< 8 + stream[2 * (j : ℕ) + 1]!.toNat := by
  -- The hash inputs of the circuit definitions and of the vendored code are the same bytes.
  have hbytes_eq :
      ByteArray.mk ((salt.toList.map UInt8.toNat ++ msg.map UInt8.toNat).map Nat.toUInt8).toArray =
        ByteArray.mk salt.toArray ++ ByteArray.empty ++
          ByteArray.mk (List.toArray (α := _root_.Falcon.Byte) msg) := by
    apply congrArg ByteArray.mk
    apply Array.toList_inj.mp
    simp only [Vector.toList_toArray, List.map_append, List.map_toUInt8_map_toNat,
      ByteArray.data_append, ByteArray.data_empty, Array.toList_append, List.append_nil]
  have hle : 2 * falcon512.S ≤ 2 * _root_.Falcon.Concrete.hashToPointCandidateBudget 512 := by
    decide
  have h2j : 2 * (j : ℕ) < 2 * falcon512.S := by omega
  have h2j1 : 2 * (j : ℕ) + 1 < 2 * falcon512.S := by omega
  unfold samples16
  rw [xofFin_shake256_prefix _ hle ⟨2 * (j : ℕ), h2j⟩,
    xofFin_shake256_prefix _ hle ⟨2 * (j : ℕ) + 1, h2j1⟩,
    xofFin_shake256_eq_getElem!, xofFin_shake256_eq_getElem!, hbytes_eq, hstream,
    Nat.shiftLeft_eq, Nat.mul_comm]

/-- Agreement between the circuit fixed-stream sampler and the larger-budget `prims512.hashToPoint`,
for `GordieHowe.shake256`: whenever `acceptedCandidates` accepts `n` samples, `prims512.hashToPoint`
succeeds with their reductions as coefficients, for every verification-key byte string
(`prims512.hashToPoint` ignores its key argument). The circuit definitions read the salt and message
bytes as naturals. -/
theorem fixedStreamChallenge_agree {salt : _root_.Falcon.Bytes 40} {msg : List UInt8}
    {c : Fin falcon512.n → ℕ}
    (hc : acceptedCandidates falcon512 GordieHowe.shake256 (salt.toList.map UInt8.toNat) (msg.map UInt8.toNat)
      = some c)
    (vrfyKey : ByteArray) :
    prims512.hashToPoint salt vrfyKey msg =
      some (ofCoeff fun i => (c i : _root_.Falcon.Coeff)) := by
  unfold prims512 _root_.Falcon.Concrete.hashToPoint
  dsimp only
  -- `msg` is read at the vendored type `Falcon.Byte` here, as in `hashToPoint`: a `UInt8`
  -- spelling makes the kernel unfold `shake256` to compare the two.
  generalize hstream : SLHDSA.Concrete.Keccak.shake256
    (ByteArray.mk salt.toArray ++ ByteArray.empty ++
      ByteArray.mk (List.toArray (α := _root_.Falcon.Byte) msg))
    (2 * _root_.Falcon.Concrete.hashToPointCandidateBudget 512) = stream
  generalize hcoeffs : (Id.run do
      let mut out : Array _root_.Falcon.Coeff := #[]
      let mut cursor := 0
      while out.size < 512 ∧ cursor + 2 ≤ stream.size do
        if stream[cursor]!.toNat <<< 8 + stream[cursor + 1]!.toNat < 5 * _root_.Falcon.modulus then
          out := out.push
            (((stream[cursor]!.toNat <<< 8 + stream[cursor + 1]!.toNat) % _root_.Falcon.modulus : ℕ) :
              _root_.Falcon.Coeff)
        cursor := cursor + 2
      return out) = coeffs
  have hbound_eq : falcon512.bound = 5 * _root_.Falcon.modulus := by
    show 5 * falcon512.q = 5 * _root_.Falcon.modulus
    rw [falcon512_matches.1]
  have hcoeffsToList : coeffs.toList =
      ((((List.range (stream.size / 2)).map
          (fun j => stream[2 * j]!.toNat <<< 8 + stream[2 * j + 1]!.toNat)).filter
            (fun d => decide (d < falcon512.bound))).map
              (fun d => ((d % _root_.Falcon.modulus : ℕ) : _root_.Falcon.Coeff))).take 512 := by
    rw [hbound_eq, ← hcoeffs]
    exact oneLoop_toList_eq 512 stream.size 2
      (fun cursor => stream[cursor]!.toNat <<< 8 + stream[cursor + 1]!.toNat)
      (fun d => d < 5 * _root_.Falcon.modulus)
      (fun d => ((d % _root_.Falcon.modulus : ℕ) : _root_.Falcon.Coeff)) (by norm_num)
  -- Candidates agree between the fixed-stream sampler and the larger-budget sampler.
  have hcand_eq := samples16_xofFin_shake256_eq_stream hstream
  -- Expose `firstAccepted`'s conclusion and align its acceptance test with `hcoeffsToList`'s.
  unfold acceptedCandidates streamCandidates at hc
  obtain ⟨hlen, hceq⟩ := firstAccepted_eq_some_iff.mp hc
  -- The fixed-length (`S`-sample) candidate list is the corresponding prefix of the
  -- larger-budget candidate list.
  set cand2 : ℕ → ℕ := fun j => stream[2 * j]!.toNat <<< 8 + stream[2 * j + 1]!.toNat with hcand2_def
  have hlist_eq : List.ofFn (fun i : Fin falcon512.S =>
      samples16 (xofFin GordieHowe.shake256 (salt.toList.map UInt8.toNat ++ msg.map UInt8.toNat)
        (2 * falcon512.S)) i) =
      (List.range falcon512.S).map cand2 := by
    apply List.ext_getElem
    · simp
    · intro i hi hj
      rw [List.getElem_ofFn, List.getElem_map, List.getElem_range]
      exact hcand_eq ⟨i, by simpa using hi⟩
  simp only [hlist_eq] at hlen hceq
  have hstream_size : stream.size = 2 * 1024 := by
    rw [← hstream]; exact SLHDSA.Concrete.Keccak.shake256_size _ _
  have hprefix : (List.range falcon512.S).map cand2 =
      ((List.range (stream.size / 2)).map cand2).take falcon512.S := by
    rw [← List.map_take, List.take_range, hstream_size]
    congr 1
  simp only [hprefix] at hlen hceq
  simp only [← List.countP_eq_length_filter] at hlen
  -- Enough candidates are accepted among the first `S`, hence among all `budget` of them:
  -- the budget is not exhausted.
  have hacc_ge : falcon512.n ≤
      (((List.range (stream.size / 2)).map cand2).filter
        (fun d => decide (d < falcon512.bound))).length :=
    le_trans hlen
      (List.countP_take_le (fun d => decide (d < falcon512.bound))
        ((List.range (stream.size / 2)).map cand2) falcon512.S)
  simp only [List.take_filter_eq_filter_take_countP] at hceq
  set k := (((List.range (stream.size / 2)).map cand2).take falcon512.S).countP
    (fun d => decide (d < falcon512.bound)) with hk_def
  set filtAcc := ((List.range (stream.size / 2)).map cand2).filter
    (fun d => decide (d < falcon512.bound)) with hfiltAcc_def
  have hn512 : falcon512.n = 512 := rfl
  have hacclen : (512 : ℕ) ≤ filtAcc.length := hn512 ▸ hacc_ge
  have hacc_take_len : ((filtAcc.map fun d => ((d % _root_.Falcon.modulus : ℕ) :
      _root_.Falcon.Coeff)).take 512).length = 512 := by
    rw [List.length_take, List.length_map]; omega
  have hsize : coeffs.size = 512 := by
    rw [← Array.length_toList, hcoeffsToList]
    exact hacc_take_len
  rw [if_neg (by omega)]
  -- Finish: read off coefficient `i` on both sides.
  rw [show (ofCoeff fun i => (c i : _root_.Falcon.Coeff)) = Vector.ofFn fun i => (c i :
      _root_.Falcon.Coeff) from by unfold ofCoeff; rfl]
  apply congrArg some
  apply congrArg Vector.ofFn
  funext i
  show coeffs[(i : ℕ)]! = _
  rw [← Array.getElem!_toList, hcoeffsToList]
  have hi512 : (i : ℕ) < 512 := i.2
  have hb1 : (i : ℕ) < ((filtAcc.map fun d => ((d % _root_.Falcon.modulus : ℕ) :
      _root_.Falcon.Coeff)).take 512).length := by rw [hacc_take_len]; exact hi512
  rw [getElem!_pos _ i.1 hb1, List.getElem_take, List.getElem_map]
  have hcival : c i = filtAcc[i.1]'(by omega) := (hceq i).trans List.getElem_take
  rw [← hcival]
  exact ZMod.natCast_mod (c i) _root_.Falcon.modulus

end Falcon512

namespace Falcon512

/-- The fraction of uniformly distributed `2S`-byte strings whose sample stream has
fewer than `n` samples below `5q`. A rational number: the count over all strings
divided by `256^(2S)`. -/
def unsupportedFraction (P : Params) : ℚ :=
  ((Finset.univ.filter fun bytes : Fin (2 * P.S) → Fin 256 =>
      firstAccepted (fun v => decide (v < P.bound))
        (samples16 fun i => (bytes i : ℕ)) P.n = none).card : ℚ) / (256 : ℚ) ^ (2 * P.S)

set_option maxRecDepth 8000 in
/-- For Falcon-512, at most a `2^-256` fraction of `1434`-byte strings has fewer than
`512` samples below `61445` among its `717` big-endian 16-bit samples. The fraction is
the binomial tail `Σ_{k<512} C(717,k) · 61445^k · 4091^(717−k) / 65536^717`, about
`2^(-256.18)`. This is a statement about uniform byte strings; applying it to SHAKE256
output is a random-oracle assumption on SHAKE256. -/
theorem unsupportedFraction_le : unsupportedFraction falcon512 ≤ (2 : ℚ) ^ (-(256 : ℤ)) := by
  have hS : falcon512.S = 717 := by decide
  have hn : falcon512.n = 512 := by decide
  have hboundeq : falcon512.bound = 61445 := by decide
  have hbound : falcon512.bound ≤ 65536 := by decide
  have hcard : (Finset.univ.filter fun bytes : Fin (2 * falcon512.S) → Fin 256 =>
      firstAccepted (fun v => decide (v < falcon512.bound))
        (samples16 fun i => (bytes i : ℕ)) falcon512.n = none).card
      = binomialTail falcon512.S falcon512.bound 65536 falcon512.n := by
    rw [binomialTail_eq, ← Finset.card_filter_lt_fin_lt_choose_sum hbound falcon512.S falcon512.n,
      ← Finset.card_filter_congr (samples16Equiv falcon512.S)
        (fun v : Fin falcon512.S → Fin 65536 =>
          (Finset.univ.filter fun i => (v i : ℕ) < falcon512.bound).card < falcon512.n)]
    apply congrArg Finset.card
    apply Finset.filter_congr
    intro bytes _
    rw [firstAccepted_eq_none_iff, ← List.countP_eq_length_filter,
      List.countP_ofFn (fun v => decide (v < falcon512.bound))]
    have hAB : (Finset.univ.filter fun i : Fin falcon512.S =>
          decide (samples16 (fun i => (bytes i : ℕ)) i < falcon512.bound) = true)
        = (Finset.univ.filter fun i =>
            (samples16Equiv falcon512.S bytes i : ℕ) < falcon512.bound) := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, decide_eq_true_eq]
      rw [samples16Equiv_apply bytes i]
    rw [hAB]
  have hnat : 2 ^ 256 * binomialTail falcon512.S falcon512.bound 65536 falcon512.n
      ≤ 65536 ^ falcon512.S := by
    rw [hS, hn, hboundeq]
    decide
  have hpow256 : (256 : ℚ) ^ (2 * falcon512.S) = (65536 : ℚ) ^ falcon512.S := by
    rw [pow_mul, show (256 : ℚ) ^ 2 = 65536 from by norm_num]
  unfold unsupportedFraction
  rw [hcard, hpow256, show (2 : ℚ) ^ (-(256 : ℤ)) = 1 / (2 : ℚ) ^ 256 from by norm_num,
    div_le_div_iff₀ (by positivity) (by positivity), one_mul]
  exact_mod_cast hnat

/-- The algebraic core of Falcon verification on decoded values, Algorithm 16
steps 3 and 4: `s₁ := c − s₂·h` and `‖(s₁, s₂)‖² ≤ ⌊β²⌋`, at the degree and
norm bound of `P`.  This is what the A circuit establishes; `verify` adds
hashing and decoding around it. -/
def algebraOk (P : Params) (h c s₂ : _root_.Falcon.Rq P.n) : Prop :=
  _root_.Falcon.pairL2NormSq (c - s₂ * h) s₂ ≤ P.βSq

/-- `verify` is `algebraOk` at the hash of the salt and message and the
decompressed `s₂`.  Wraps the body of the vendored `Falcon.verify`. -/
theorem verify_iff_algebraOk (pk : _root_.Falcon.PublicKey _root_.Falcon.Concrete.params512)
    (msg : List UInt8) (sig : _root_.Falcon.Signature) :
    verify pk msg sig ↔
      ∃ s2Int c, prims512.decompress sig.compressedS2 _root_.Falcon.Concrete.params512.sbytelen
          = some s2Int
        ∧ prims512.hashToPoint sig.salt (prims512.publicKeyBytes pk.h) msg = some c
        ∧ algebraOk falcon512 pk.h c (_root_.Falcon.IntPoly.toRq s2Int) := by
  unfold verify _root_.Falcon.verify
  split
  · simp_all
  · rename_i s2Int hdec
    simp only [_root_.Falcon.VerifyPrimitives.hashToPointForPublicKey]
    split
    · simp_all
    · rename_i c hc
      simp only [algebraOk, decide_eq_true_eq]
      constructor
      · intro h
        exact ⟨s2Int, c, hdec, hc, h⟩
      · rintro ⟨s', c', hd', hc', h⟩
        rw [hdec] at hd'
        rw [hc] at hc'
        cases hd'
        cases hc'
        exact h

end Falcon512

end GordieHowe
