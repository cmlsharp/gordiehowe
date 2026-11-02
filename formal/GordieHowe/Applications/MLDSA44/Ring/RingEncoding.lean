-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Applications.MLDSA44.Ring.Scheme
public import GordieHowe.Applications.Ring.RingBytes
public import GordieHowe.Applications.Ring.RingUnforgeability

@[expose] public section

/-!
# The base messages of the ML-DSA-44 ring signatures

The base message the ML-DSA-44 base signer signs is a FIPS 204 message representative
`M′ = 0 ‖ |ctx| ‖ ctx ‖ M` (Algorithm 2, line 10), here with the empty context (the compiled ring
programs' `ctxBytes = 0`), so `M′ = 0 ‖ 0 ‖ M` (`frame0`; `frame0_toList`: it is
`GordieHowe.MLDSA44.frame [] M`).

- `convertedMsg`: the converted signatures, `M = m` for a `32`-byte ring message (the compiled
  programs' `msgBytes = 32`).
- `keyBytes`, `keyBytes_injective`: a key as `32 + 1024 · 3` bytes, `ρ` then the `1024`
  coefficients of `t₁` as three little-endian bytes of their value below `q < 2^24` (injective on
  every key, encodable by `pkEncode` or not).
- `bindingMsg`: the ring-binding signatures, `M = m ‖ encode R` (`GordieHowe.Ring.encodeRingMsg`
  at `keyBytes`, `ringMsgLen` bytes, BKM06 §5); `bindsRing_bindingMsg`: the base signer at
  `bindingMsg` binds the ring.
-/

namespace GordieHowe.MLDSA44.Ring

open GordieHowe.Ring GordieHowe.RingSignature _root_.MLDSA _root_.MLDSA.Concrete

/-- **The message representative with the empty context**: `0 ‖ 0 ‖ M`. -/
def frame0 {n : ℕ} (m : Bytes n) : Bytes (2 + n) :=
  (#v[0, 0] : Vector UInt8 2) ++ m

theorem frame0_toList {n : ℕ} (m : Bytes n) :
    (frame0 m).toList = GordieHowe.MLDSA44.frame [] m.toList := by
  simp [frame0, GordieHowe.MLDSA44.frame]

theorem frame0_injective {n : ℕ} : Function.Injective (frame0 (n := n)) := by
  intro a b h
  apply Vector.ext
  intro i hi
  have := congrArg (fun v : Bytes (2 + n) => v[2 + i]'(by omega)) h
  simpa [frame0, Vector.getElem_append] using this

/-- The coefficient `256 i + j` of `t₁`. -/
def t1Coeff (pk : PublicKey) (c : Fin 1024) : Coeff :=
  (pk.t1.get ((finProdFinEquiv (m := _root_.MLDSA.mldsa44.k) (n := ringDegree)).symm c).1).get
    ((finProdFinEquiv (m := _root_.MLDSA.mldsa44.k) (n := ringDegree)).symm c).2

/-- **A key as `32 + 1024 · 3` bytes**: `ρ`, then byte `b` of coefficient `c` of `t₁` (its value
`v < q`, byte `⌊v / 256^b⌋ mod 256`). -/
def keyBytes (pk : PublicKey) : Fin (32 + 1024 * 3) → UInt8 :=
  Fin.append (fun i => pk.rho.get i) fun j =>
    (((t1Coeff pk (finProdFinEquiv.symm j).1).val / 256 ^ ((finProdFinEquiv.symm j).2 : ℕ)) %
      256).toUInt8

/-- **`keyBytes` is injective.** -/
theorem keyBytes_injective : Function.Injective keyBytes := by
  rintro ⟨r, t⟩ ⟨r', t'⟩ h
  obtain ⟨hr, ht⟩ := GordieHowe.Ring.fin_append_inj h
  have hrho : r = r' := Vector.ext fun i hi => by
    simpa [Vector.get_eq_getElem] using congrFun hr ⟨i, hi⟩
  have hc : ∀ c : Fin 1024, t1Coeff ⟨r, t⟩ c = t1Coeff ⟨r', t'⟩ c := by
    intro c
    have hb : ∀ b : Fin 3, (t1Coeff ⟨r, t⟩ c).val / 256 ^ (b : ℕ) % 256 =
        (t1Coeff ⟨r', t'⟩ c).val / 256 ^ (b : ℕ) % 256 := fun b => by
      have := congrFun ht (finProdFinEquiv (c, b))
      simp only [Equiv.symm_apply_apply] at this
      exact GordieHowe.Ring.toUInt8_inj (Nat.mod_lt _ (by norm_num)) (Nat.mod_lt _ (by norm_num))
        this
    apply ZMod.val_injective
    have h1 := ZMod.val_lt (t1Coeff ⟨r, t⟩ c)
    have h2 := ZMod.val_lt (t1Coeff ⟨r', t'⟩ c)
    have e0 := hb 0
    have e1 := hb 1
    have e2 := hb 2
    simp only [Fin.val_zero, Fin.val_one, Fin.val_two, pow_zero, pow_one, Nat.div_one] at e0 e1 e2
    change _ < 8380417 at h1 h2
    omega
  subst hrho
  congr 1
  apply Vector.ext
  intro i hi
  apply LatticeCrypto.Poly.ext_get_eq
  intro j
  have := hc (finProdFinEquiv (m := _root_.MLDSA.mldsa44.k) (n := ringDegree) (⟨i, hi⟩, j))
  simpa [t1Coeff, Vector.get_eq_getElem] using this

/-- **A key of the primitives `prims eS eM` as bytes**: the bytes of its concrete key. -/
def keyBytesOf (eS : Bytes 64 → RqVec _root_.MLDSA.mldsa44.l × RqVec _root_.MLDSA.mldsa44.k)
    (eM : Bytes 64 → ℕ → RqVec _root_.MLDSA.mldsa44.l)
    (k : _root_.MLDSA.PublicKey _root_.MLDSA.mldsa44 (prims eS eM)) : Fin (32 + 1024 * 3) → UInt8 :=
  keyBytes (toKey eS eM k)

theorem keyBytesOf_injective (eS : Bytes 64 → RqVec _root_.MLDSA.mldsa44.l × RqVec _root_.MLDSA.mldsa44.k)
    (eM : Bytes 64 → ℕ → RqVec _root_.MLDSA.mldsa44.l) :
    Function.Injective (keyBytesOf eS eM) :=
  keyBytes_injective.comp (toKey_injective eS eM)

variable (eS : Bytes 64 → RqVec _root_.MLDSA.mldsa44.l × RqVec _root_.MLDSA.mldsa44.k)
  (eM : Bytes 64 → ℕ → RqVec _root_.MLDSA.mldsa44.l)

/-- **The converted base message**: the representative `0 ‖ 0 ‖ m` of the `32`-byte ring message
`m`, whatever the ring. -/
def convertedMsg (_R : KeyRing (_root_.MLDSA.PublicKey _root_.MLDSA.mldsa44 (prims eS eM)) 64)
    (m : Bytes 32) : Bytes (2 + 32) :=
  frame0 m

theorem convertedMsg_injective (R : KeyRing (_root_.MLDSA.PublicKey _root_.MLDSA.mldsa44 (prims eS eM)) 64) :
    Function.Injective (convertedMsg eS eM R) :=
  frame0_injective

/-- The length of the ring-binding message `m ‖ encode R`: `32` message bytes, one length byte and
`64` key slots of `32 + 1024 · 3` bytes. -/
abbrev ringMsgLen : ℕ := 32 + (1 + 64 * (32 + 1024 * 3))

/-- **The ring-binding base message**: the representative `0 ‖ 0 ‖ (m ‖ encode R)` of the
`32`-byte ring message followed by the ring's bytes (`GordieHowe.Ring.encodeRingMsg` at
`keyBytesOf`). -/
def bindingMsg (R : KeyRing (_root_.MLDSA.PublicKey _root_.MLDSA.mldsa44 (prims eS eM)) 64)
    (m : Bytes 32) : Bytes (2 + ringMsgLen) :=
  frame0 (Vector.ofFn (encodeRingMsg (keyBytesOf eS eM) R m.get))

theorem bindingMsg_inj {R R' : KeyRing (_root_.MLDSA.PublicKey _root_.MLDSA.mldsa44 (prims eS eM)) 64}
    {m m' : Bytes 32} (h : bindingMsg eS eM R m = bindingMsg eS eM R' m') : R = R' ∧ m = m' := by
  have h1 := frame0_injective h
  have h2 : encodeRingMsg (keyBytesOf eS eM) R m.get = encodeRingMsg (keyBytesOf eS eM) R' m'.get :=
    funext fun i => by simpa using congrArg (·.get i) h1
  obtain ⟨hR, hm⟩ := encodeRingMsg_inj (keyBytesOf_injective eS eM) (by norm_num) h2
  exact ⟨hR, Vector.ext fun i hi => by simpa [Vector.get_eq_getElem] using congrFun hm ⟨i, hi⟩⟩

theorem bindingMsg_injective (R : KeyRing (_root_.MLDSA.PublicKey _root_.MLDSA.mldsa44 (prims eS eM)) 64) :
    Function.Injective (bindingMsg eS eM R) :=
  fun _ _ h => (bindingMsg_inj eS eM h).2

/-- **The ML-DSA-44 base signer at `bindingMsg` binds the ring.** -/
theorem bindsRing_bindingMsg {Xo Yo : Type} (maxAttempts : ℕ) :
    (baseSigner eS eM Xo Yo maxAttempts (bindingMsg eS eM)).BindsRing :=
  fun _ _ _ _ h => bindingMsg_inj eS eM h

end GordieHowe.MLDSA44.Ring
