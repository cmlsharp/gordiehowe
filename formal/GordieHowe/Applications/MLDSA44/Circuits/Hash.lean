-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Applications.Falcon512.Circuits.Hash
public import GordieHowe.Applications.MLDSA44.Gadgets.SelectFirstTau
public import GordieHowe.Applications.MLDSA44.Spec.Encoding
public import GordieHowe.Applications.MLDSA44.Spec.Hash

@[expose] public section

/-!
# ML-DSA-44: the H circuit's wires

```
CIRCUIT H_ml:
  pub   r[0..chunks) (from K_mac), M̃, tr, ctx, δ_G, δ_mem, δ_enc
  wit   c̃, msg, j[0..τ), SHAKE advice, thr_low[0..128), read advice, c_enc, final origins,
        w1_tilde, P_mac

  μ      := SHAKE256(tr ‖ 0 ‖ |ctx| ‖ ctx ‖ msg, 64)
  out    := SHAKE256(c̃, 136)
  SelectFirstTau(out[8..136), j, thr_low, δ_G)
  (sup, sgn) := MemoryShuffle(j, signs = bits 0..τ−1 of out[0..8), read advice, c_enc, δ_enc, δ_mem)
  assert SHAKE256(μ ‖ w1_tilde, 32) == c̃
  X := chunks(w1_tilde) ‖ chunks(sup_0, sgn_0, sup_1, sgn_1, …)
  assert Σ_c X[c]·r[c] + P_mac == M̃
```

The builder is `MLDSAHashVerify::assert_hash_side` (`ml_dsa_hash_circuit.h`, default variant
`kSibGpMemScalar`). The flagship native ML-DSA-44 system (`MLDSANativeSystem` in
`lib/gordiehowe/examples/mldsa/mldsa_native.h`, benchmarked by `MLDSANative.DISABLED_Bench`) hashes as its
sponge form does in `mldsa_hash_side` (`lib/gordiehowe/examples/mldsa/mldsa_hash.h`) and binds the
crossing with `crossing` (`mldsa_native.h`). The ladder `r[c] = K_mac^(c+1)` is a public input the
verifier derives. `tr` and `ctx` are public input bits; the context length is a compile-time
constant.

This file holds the H circuit's wires and their specification:

* `muInput`, `commitInput`: the SHAKE256 inputs `tr ‖ 0 ‖ |ctx| ‖ ctx ‖ msg` and
  `μ ‖ w1_tilde`, Boolean on Boolean inputs (`muInput_allBool`, `commitInput_allBool`), with
  their bytes (`inputBytes_commitInput`, `ofFn_mu`);
* `candidates`, `signWires`: the candidate bytes `out[8..C + 8)` and the sign bits that
  SampleInBall reads from its stream;
* `cBits`, `crossBits`: the challenge bits, coefficient `k` at MAC bit `2k` (support) and
  `2k + 1` (sign), and the crossing `X`: the `8 · 768` bits of `w1_tilde` (committed as `768`
  bytes, least significant bit first), then the `2 · N` challenge bits, cut into
  `mldsa44.chunks mw` chunks of `mw` bits: `52` chunks at `mw = 128` (`48` of `w1_tilde`, then
  `4`) and `26` at `mw = 256` (`mul_chunks_le`; exactly under `mldsa44.MACWidth mw`, `cover`);
* the specification: `mu` (FIPS 204 Algorithm 3), `ternaryBits`, `w1Bit_lt` and
  `natOfBits_byteWires_w1Encode`.
-/

namespace GordieHowe.MLDSA44.HashCircuit

open Falcon512.HashCircuit (byteWires byteWires_allBool wiresOfByteVec wiresOfByteVec_allBool natOfBits_byteWires_wiresOfByteVec)

variable {K : Type*} [Field K] [DecidableEq K]

variable {sl : Keccak.Slicing} {mw ctxLen msgLen : ℕ}

/-- The `μ` input `tr ‖ 0 ‖ |ctx| ‖ ctx ‖ msg` (`ml_dsa_derive_mu`). -/
def muInput (tr : BitWires K (8 * 64)) (ctx : BitWires K (8 * ctxLen))
    (msg : BitWires K (8 * msgLen)) : Fin (64 + (2 + (ctxLen + msgLen))) → BitWires K 8 :=
  Fin.append (byteWires tr)
    (Fin.append ![Shake256.constByte 0, Shake256.constByte ctxLen]
      (Fin.append (byteWires ctx) (byteWires msg)))

/-- The candidate bytes `out[8..C + 8)` of a stream of `C + 8` bytes (`136` here, `272` in
GordieHowe). -/
def candidates {C : ℕ} (out : Fin (C + 8) → BitWires K 8) (i : Fin C) : BitWires K 8 :=
  out ⟨8 + i, by omega⟩

/-- Sign bit `s`: bit `s mod 8` of `out[s / 8]` (`out[s / 8][s % 8]`). -/
def signWires {C : ℕ} (out : Fin (C + 8) → BitWires K 8) (s : Fin mldsa44.τ) : K :=
  out ⟨s / 8, by have := s.isLt; change (s : ℕ) < 39 at this; omega⟩ ⟨s % 8, by omega⟩

/-- The challenge crossing bits: coefficient `k` at bits `2k` (support) and
`2k + 1` (sign). -/
def cBits (dec : Fin mldsa44.N → K × K) : BitWires K (2 * mldsa44.N) := fun t =>
  if (t : ℕ) % 2 = 0 then (dec ⟨t / 2, by have := t.isLt; change (t : ℕ) < 512 at this; change _ < 256; omega⟩).1
  else (dec ⟨t / 2, by have := t.isLt; change (t : ℕ) < 512 at this; change _ < 256; omega⟩).2

/-- The `c̃'` input `μ ‖ w1_tilde` (`assert_ctilde`). -/
def commitInput (mu : Fin 64 → BitWires K 8) (w1 : BitWires K (8 * 768)) :
    Fin (64 + 768) → BitWires K 8 :=
  Fin.append mu (byteWires w1)

/-- The `mw`-bit MAC chunks cover at most the crossing's `w1` and challenge bits. -/
theorem mul_chunks_le (mw : ℕ) : mw * mldsa44.chunks mw ≤ 8 * 768 + 2 * mldsa44.N :=
  Nat.mul_div_le _ mw

/-- Under `mldsa44.MACWidth mw` (`GordieHowe/Applications/Params.lean`), the chunks cover the crossing (`8 · 768`
bits of `w1_tilde`, then `2 · N` challenge bits) exactly. -/
theorem cover (mw : ℕ) [h : mldsa44.MACWidth mw] :
    mw * mldsa44.chunks mw = 8 * 768 + 2 * mldsa44.N :=
  h.cover

/-- The crossing in MAC chunk order: bit `t` is `w1_tilde` bit `t` for `t < 8 · 768`
(`w1_chunks`), then challenge bit `t − 8 · 768`. -/
def crossBits (w1 : BitWires K (8 * 768)) (c : BitWires K (2 * mldsa44.N)) :
    BitWires K (mw * mldsa44.chunks mw) := fun t =>
  if h : (t : ℕ) < 8 * 768 then w1 ⟨t, h⟩
  else c ⟨t - 8 * 768, by have := t.isLt; have := mul_chunks_le mw; omega⟩

/-! ### The specification -/

/-- `μ = SHAKE256(tr ‖ M′, 64)` with `M′ = frame ctx msg` (FIPS 204 Algorithm 3). -/
-- spec-side
def mu (tr : List ℕ) (ctx msg : List UInt8) : Fin 64 → ℕ :=
  xofFin shake256 (tr ++ (MLDSA44.frame ctx msg).map UInt8.toNat) 64

/-- Support and sign bits of a coefficient in `{−1, 0, 1}`. -/
-- spec-side
def ternaryBits (z : ℤ) : K × K := (if z = 0 then 0 else 1, if z = -1 then 1 else 0)

/-- Bit `b` of coefficient `c` of polynomial `i` in the `w1Encode` bit string
(`w1Encode_testBit`). -/
theorem w1Bit_lt (i : Fin _root_.MLDSA.mldsa44.k) (c : Fin _root_.MLDSA.ringDegree) (b : Fin 6) :
    ((i : ℕ) * _root_.MLDSA.ringDegree + c) * 6 + b < 8 * 768 := by
  have hi := i.isLt
  have hc := c.isLt
  have hb := b.isLt
  change (i : ℕ) < 4 at hi
  change (c : ℕ) < 256 at hc
  change ((i : ℕ) * 256 + c) * 6 + b < 8 * 768
  omega

/-- **`w1_tilde` bytes from coefficient bits.**  Wires laid out as the `w1Encode` bit string
of `w1` (bit `b` of coefficient `c` of polynomial `i` at wire `(i · 256 + c) · 6 + b`) read,
byte by byte, the `w1Encode` bytes of `w1`. -/
theorem natOfBits_byteWires_w1Encode {a : BitWires K (8 * 768)}
    {w1 : Vector _root_.MLDSA.Concrete.High _root_.MLDSA.mldsa44.k}
    (ha : ∀ (i : Fin _root_.MLDSA.mldsa44.k) (c : Fin _root_.MLDSA.ringDegree) (b : Fin 6), a ⟨((i : ℕ) * _root_.MLDSA.ringDegree + c) * 6 + b, w1Bit_lt i c b⟩ =
      Bits.constBit ((w1.get i).get c).val b)
    (j : Fin 768) :
    Bits.natOfBits (byteWires a j) = ((_root_.MLDSA.Concrete.w1Encode _root_.MLDSA.mldsa44 w1).getD j 0).toNat := by
  have key : ∀ b8 : Fin 8, byteWires a j b8 =
      Bits.constBit ((_root_.MLDSA.Concrete.w1Encode _root_.MLDSA.mldsa44 w1).getD j 0).toNat b8 := by
    intro b8
    have hj := j.isLt
    have hb8 := b8.isLt
    let i : Fin _root_.MLDSA.mldsa44.k := ⟨(8 * (j : ℕ) + b8) / 1536, by change _ < 4; omega⟩
    let c : Fin _root_.MLDSA.ringDegree := ⟨(8 * (j : ℕ) + b8) / 6 % 256, by change _ < 256; omega⟩
    let b : Fin 6 := ⟨(8 * (j : ℕ) + b8) % 6, by omega⟩
    have hidx : ((i : ℕ) * _root_.MLDSA.ringDegree + c) * 6 + b = 8 * j + b8 := by
      change ((8 * (j : ℕ) + b8) / 1536 * 256 + (8 * (j : ℕ) + b8) / 6 % 256) * 6 + (8 * (j : ℕ) + b8) % 6 = _
      omega
    have hw := MLDSA44.w1Encode_testBit w1 i c b
    rw [hidx, show (8 * (j : ℕ) + b8) / 8 = j by omega, show (8 * (j : ℕ) + b8) % 8 = b8 by omega] at hw
    rw [SelectFirstTau.constBit_eq_ite_testBit, hw, ← SelectFirstTau.constBit_eq_ite_testBit, ← ha i c b]
    exact congrArg a (Fin.ext hidx.symm)
  have hbool : Bits.AllBool (byteWires a j) := fun b8 => by
    rw [key b8]
    exact Bits.constBit_bool _ _
  rw [(Bits.eq_constBit_iff hbool _).mp key]
  exact Nat.mod_eq_of_lt (UInt8.toNat_lt _)

/-! ### Soundness -/

/-- The `c̃'` hash reads `μ ‖ w1_tilde`. -/
theorem inputBytes_commitInput (mu : Fin 64 → BitWires K 8) (w1 : BitWires K (8 * 768)) :
    Shake256.inputBytes (commitInput mu w1) =
      List.ofFn (fun j => Bits.natOfBits (mu j)) ++
        List.ofFn fun i : Fin 768 => Bits.natOfBits (byteWires w1 i) := by
  rw [Shake256.inputBytes, List.ofFn_add]
  simp only [commitInput, Fin.append_left', Fin.append_right]

omit [DecidableEq K] in
theorem muInput_allBool {tr : BitWires K (8 * 64)} {ctx : BitWires K (8 * ctxLen)}
    {msg : BitWires K (8 * msgLen)} (htr : Bits.AllBool tr) (hctx : Bits.AllBool ctx)
    (hmsg : Bits.AllBool msg) (i : Fin (64 + (2 + (ctxLen + msgLen)))) :
    Bits.AllBool (muInput tr ctx msg i) := by
  refine Fin.addCases (fun i => ?_) (fun i => ?_) i
  · rw [muInput, Fin.append_left]
    exact byteWires_allBool htr i
  · rw [muInput, Fin.append_right]
    refine Fin.addCases (fun i => ?_) (fun i => ?_) i
    · rw [Fin.append_left]
      intro b
      fin_cases i <;> exact Bits.constBit_bool _ _
    · rw [Fin.append_right]
      refine Fin.addCases (fun i => ?_) (fun i => ?_) i
      · rw [Fin.append_left]
        exact byteWires_allBool hctx i
      · rw [Fin.append_right]
        exact byteWires_allBool hmsg i

omit [DecidableEq K] in
theorem commitInput_allBool {mu : Fin 64 → BitWires K 8} {w1 : BitWires K (8 * 768)}
    (hmu : ∀ j, Bits.AllBool (mu j)) (hw1 : Bits.AllBool w1) (i : Fin (64 + 768)) :
    Bits.AllBool (commitInput mu w1 i) := by
  refine Fin.addCases (fun i => ?_) (fun i => ?_) i
  · rw [commitInput, Fin.append_left]
    exact hmu i
  · rw [commitInput, Fin.append_right]
    exact byteWires_allBool hw1 i

/-- `μ` read as a vector is the vendored `hashMessage` on the framed message. -/
theorem ofFn_mu (tr : _root_.MLDSA.Bytes 64) (ctx msg : List UInt8) :
    List.ofFn (mu (tr.toList.map UInt8.toNat) ctx msg) =
      (_root_.MLDSA.Concrete.hashMessage tr (MLDSA44.frame ctx msg)).toList.map UInt8.toNat := by
  apply List.ext_getElem (by simp)
  intro j h₁ h₂
  rw [List.getElem_ofFn, List.getElem_map, Vector.getElem_toList]
  have := MLDSA44.hashMessage_get tr (MLDSA44.frame ctx msg) ⟨j, by simpa using h₁⟩
  rw [Vector.get_eq_getElem] at this
  rw [this]
  rfl

end GordieHowe.MLDSA44.HashCircuit
