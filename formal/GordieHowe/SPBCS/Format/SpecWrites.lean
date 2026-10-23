-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.SPBCS.Format.Codec
public import GordieHowe.Model.IOP.AppendView
public import GordieHowe.ProofSystem.GKR.SourceCircuit
public import GordieHowe.ProofSystem.GKR.Transcript
public import GordieHowe.Applications.Keccak.HashCircuit.Skip
public import GordieHowe.ProofSystem.Ligero.Tableau
public import GordieHowe.Model.IOP.AppendN
public import GordieHowe.Model.IOP.DropMessage
public import GordieHowe.ProofSystem.Program.AppPhase
public import GordieHowe.Language.Realizations.MAC
public import GordieHowe.Foundations.ToMathlib.DegreeLT

@[expose] public section

/-!
# Write codecs for every prover message of a protocol

`SpecWrites P B`: a write codec (`WriteCodec`) for every prover message of the protocol `P`, each of
at most `B` bytes. A transcript format needs one for every prover round after the commitment round;
this file builds them from the pieces the protocols are made of:

- `SpecWrites.ofNone` (no prover message), `one` (one prover message), `append`, `appendN`
  (the `m`-fold append), `dropMsg` (a protocol with a prover round removed);
  `WriteCodec.appendInl`, `appendInr` read a part's codec at the round of the appended protocol
  that runs it;
- the GKR schedule (`gkrRounds`, `gkrCircuit`, `gkrSpec`: each sumcheck message and each pair of
  wire claims is two field elements, `fieldPair`) and a source reduction's protocol
  (`sourceInteraction`);
- a two-stage test (`twoStage`: the auxiliary message and the response), with the codecs of the
  Ligero tableau's messages (`WriteCodec.ligeroAux`: the IDOT/IQUAD masks).

The codecs follow the C++ writes where the C++ writes a field element or an array of field elements
(`Codec.fieldElem`, `Codec.fieldArray`: tag, `u64le` length, the element bytes); the field element
bytes are a parameter (`Codec.FieldBytes`). Byte identity with the C++ is not a goal; what the
format needs is that each codec is injective, self-delimiting and bounded.
-/

namespace GordieHowe.SPBCS
open GordieHowe.QROM

open GordieHowe.IOP IOP.ProtocolSpec GKR.Schedule Polynomial

/-! ### Field element bytes from an enumeration -/

namespace Codec.FieldBytes

variable {F : Type} {c fb : ℕ}

/-- **Field element bytes from an enumeration** `e : F ≃ Fin c` with `c ≤ 256^fb`: the `fb`
little-endian base-256 digits of `e x` (`finFunctionFinEquiv`); a string of `fb` bytes whose
value is not below `c` does not parse. -/
def ofEquiv (e : F ≃ Fin c) (h : c ≤ 256 ^ fb) : Codec.FieldBytes F fb where
  toBytes x := finFunctionFinEquiv.symm (Fin.castLE h (e x))
  ofBytes v := if hv : (finFunctionFinEquiv v).1 < c then some (e.symm ⟨_, hv⟩) else none
  ofBytes_toBytes x := by
    simp only [Equiv.apply_symm_apply, Fin.val_castLE, Fin.is_lt, ↓reduceDIte]
    simp
  toBytes_ofBytes {v x} hx := by
    split_ifs at hx with hv
    rw [← Option.some_inj.mp hx, Equiv.apply_symm_apply, Equiv.symm_apply_eq]
    exact Fin.ext rfl

/-- `d` coordinates of `b` bits fit in `fb` bytes when `b · d ≤ 8 · fb`. -/
theorem coords_le {b d : ℕ} (h : b * d ≤ 8 * fb) : (2 ^ b) ^ d ≤ 256 ^ fb := by
  rw [← pow_mul, show (256 : ℕ) = 2 ^ 8 from rfl, ← pow_mul]
  exact Nat.pow_le_pow_right (by norm_num) h

/-- **Field element bytes in coordinates, packed** (the C++ `to_bytes_field` of the prime-field
extensions and of `GF(2^k)`): for coordinates `e x : Fin d → ZMod p` in a basis, coordinate `i`,
as its residue in `[0, p)`, occupies the `b` bits `[b · i, b · i + b)` of a little-endian integer
of `fb` bytes, the remaining high bits zero (`p ≤ 2^b`, `b · d ≤ 8 · fb`). At `b = 8c` this is
coordinate `i` as `c` little-endian bytes at bytes `[c · i, c · i + c)`. Parsing splits the
integer into its `b`-bit digits (`finFunctionFinEquiv`) and checks that the high bits are zero and
every digit is below `p`. -/
def ofCoords {d p b : ℕ} [NeZero p] (e : F ≃ (Fin d → ZMod p)) (hp : p ≤ 2 ^ b)
    (h : b * d ≤ 8 * fb) : Codec.FieldBytes F fb where
  toBytes x := finFunctionFinEquiv.symm (Fin.castLE (coords_le h)
    (finFunctionFinEquiv fun i => ⟨(e x i).val, (ZMod.val_lt _).trans_le hp⟩))
  ofBytes v :=
    if hv : (finFunctionFinEquiv v).1 < (2 ^ b) ^ d then
      if hd : ∀ i, ((finFunctionFinEquiv.symm ⟨_, hv⟩ : Fin d → Fin (2 ^ b)) i : ℕ) < p then
        some (e.symm fun i => (((finFunctionFinEquiv.symm ⟨_, hv⟩ : Fin d → Fin (2 ^ b)) i : ℕ) :
          ZMod p))
      else none
    else none
  ofBytes_toBytes x := by
    have hv : (finFunctionFinEquiv (finFunctionFinEquiv.symm (Fin.castLE (coords_le h)
        (finFunctionFinEquiv fun i => (⟨(e x i).val, (ZMod.val_lt _).trans_le hp⟩ :
          Fin (2 ^ b)))))).1 < (2 ^ b) ^ d := by
      simp only [Equiv.apply_symm_apply, Fin.val_castLE]
      exact (finFunctionFinEquiv _).isLt
    rw [dite_cond_eq_true (eq_true hv)]
    have hf : (finFunctionFinEquiv.symm ⟨_, hv⟩ : Fin d → Fin (2 ^ b)) =
        fun i => ⟨(e x i).val, (ZMod.val_lt _).trans_le hp⟩ := by
      rw [Equiv.symm_apply_eq]
      ext
      simp
    have hd : ∀ i, ((finFunctionFinEquiv.symm ⟨_, hv⟩ : Fin d → Fin (2 ^ b)) i : ℕ) < p := by
      intro i
      rw [hf]
      exact ZMod.val_lt _
    rw [dite_cond_eq_true (eq_true hd), Option.some_inj, Equiv.symm_apply_eq, hf]
    funext i
    simp
  toBytes_ofBytes {v x} hx := by
    split_ifs at hx with hv hd
    rw [← Option.some_inj.mp hx, Equiv.apply_symm_apply, Equiv.symm_apply_eq]
    have hval : ∀ i, (⟨(((finFunctionFinEquiv.symm ⟨_, hv⟩ : Fin d → Fin (2 ^ b)) i : ℕ) :
        ZMod p).val, (ZMod.val_lt _).trans_le hp⟩ : Fin (2 ^ b)) =
        (finFunctionFinEquiv.symm ⟨_, hv⟩ : Fin d → Fin (2 ^ b)) i :=
      fun i => Fin.ext (ZMod.val_natCast_of_lt (hd i))
    simp only [hval, Equiv.apply_symm_apply]
    exact Fin.ext rfl

end Codec.FieldBytes

namespace Codec

variable {F : Type} {fb : ℕ}

/-- An array of `m` field elements serializes to `9 + m · fb` bytes. -/
theorem length_ser_fieldArray (FB : FieldBytes F fb) (m : ℕ) (x : Fin m → F) :
    ((fieldArray FB m).ser x).length = 9 + m * fb := by
  simp [fieldArray, mapPartial, framed]
  omega

/-- A field element serializes to `1 + fb` bytes. -/
theorem length_ser_fieldElem (FB : FieldBytes F fb) (x : F) :
    ((fieldElem FB).ser x).length = 1 + fb := by
  simp [fieldElem, mapPartial, framed]
  omega

end Codec

/-! ### Codecs of the message types -/

namespace WriteCodec

variable {F : Type} {fb : ℕ}

/-- Two field elements, one after the other. -/
def fieldPair (FB : Codec.FieldBytes F fb) : WriteCodec (F × F) :=
  (fieldElem FB).prod (fieldElem FB)

theorem fieldArray_B (FB : Codec.FieldBytes F fb) (m : ℕ) :
    (fieldArray FB m).B = 9 + m * fb := rfl

theorem fieldPair_B (FB : Codec.FieldBytes F fb) : (fieldPair FB).B = 2 * (1 + fb) := by
  simp only [fieldPair, prod, fieldElem]
  omega

/-- **The Ligero mask message's write**: the IDOT and IQUAD masks at the `N` code positions, two
arrays of field elements. -/
def ligeroAux (FB : Codec.FieldBytes F fb) (N : ℕ) : WriteCodec (Ligero.Tableau.Aux F N) :=
  (fieldArray FB N).prod (fieldArray FB N)

variable {n₁ n₂ : ℕ} {P₁ : ProtocolSpec n₁} {P₂ : ProtocolSpec n₂}

/-- A codec of prover round `j` of `P₁`, read at the round `i` of `P₁ ++ P₂` that runs it. -/
def appendInl {i : (P₁ ++ P₂).MessageIdx} {j : P₁.MessageIdx} (c : WriteCodec (P₁.Type j.1))
    (h : messageIdxEquiv i = .inl j) : WriteCodec ((P₁ ++ P₂).Type i.1) :=
  c.mapEquiv (Equiv.cast ((congrArg (fun i : (P₁ ++ P₂).MessageIdx => (P₁ ++ P₂).Type i.1)
    (MessageIdx.eq_inl_of_equiv h)).trans (append_Type_castAdd j.1)))

/-- A codec of prover round `j` of `P₂`, read at the round `i` of `P₁ ++ P₂` that runs it. -/
def appendInr {i : (P₁ ++ P₂).MessageIdx} {j : P₂.MessageIdx} (c : WriteCodec (P₂.Type j.1))
    (h : messageIdxEquiv i = .inr j) : WriteCodec ((P₁ ++ P₂).Type i.1) :=
  c.mapEquiv (Equiv.cast ((congrArg (fun i : (P₁ ++ P₂).MessageIdx => (P₁ ++ P₂).Type i.1)
    (MessageIdx.eq_inr_of_equiv h)).trans (append_Type_natAdd j.1)))

@[simp] theorem appendInl_B {i : (P₁ ++ P₂).MessageIdx} {j : P₁.MessageIdx}
    (c : WriteCodec (P₁.Type j.1)) (h : messageIdxEquiv i = .inl j) : (c.appendInl h).B = c.B :=
  rfl

@[simp] theorem appendInr_B {i : (P₁ ++ P₂).MessageIdx} {j : P₂.MessageIdx}
    (c : WriteCodec (P₂.Type j.1)) (h : messageIdxEquiv i = .inr j) : (c.appendInr h).B = c.B :=
  rfl

end WriteCodec

/-! ### Write codecs of every prover message -/

/-- **Write codecs for every prover message of `P`**, each of at most `B` bytes. -/
structure SpecWrites {n : ℕ} (P : ProtocolSpec n) (B : ℕ) where
  /-- The codec of each prover message. -/
  write : (i : P.MessageIdx) → WriteCodec (P.Type i.1)
  /-- Each codec writes at most `B` bytes. -/
  le : ∀ i, (write i).B ≤ B

namespace SpecWrites

variable {n n₁ n₂ B B' : ℕ}

/-- A protocol without prover messages. -/
def ofNone {P : ProtocolSpec n} (h : ∀ i, P.dir i = .V_to_P) : SpecWrites P B where
  write i := absurd (i.2.symm.trans (h i.1)) (by decide)
  le i := absurd (i.2.symm.trans (h i.1)) (by decide)

/-- One prover message. -/
def one {M : Type} (c : WriteCodec M) (hc : c.B ≤ B) : SpecWrites (GKR.Schedule.one .P_to_V M) B :=
  ⟨fun _ => c, fun _ => hc⟩

/-- One verifier message. -/
def oneV {M : Type} : SpecWrites (GKR.Schedule.one .V_to_P M) B :=
  ofNone fun _ => rfl

variable {P₁ : ProtocolSpec n₁} {P₂ : ProtocolSpec n₂}

/-- The codec of prover round `i` of an appended protocol, given the part's round `s` that it
is. -/
def appendOf (W₁ : SpecWrites P₁ B) (W₂ : SpecWrites P₂ B) (i : (P₁ ++ P₂).MessageIdx) :
    ∀ s, messageIdxEquiv i = s → WriteCodec ((P₁ ++ P₂).Type i.1)
  | .inl j, h => (W₁.write j).appendInl h
  | .inr j, h => (W₂.write j).appendInr h

theorem appendOf_le (W₁ : SpecWrites P₁ B) (W₂ : SpecWrites P₂ B)
    (i : (P₁ ++ P₂).MessageIdx) : ∀ s h, (appendOf W₁ W₂ i s h).B ≤ B
  | .inl j, _ => W₁.le j
  | .inr j, _ => W₂.le j

/-- **The codecs of an appended protocol**: each round's codec is its part's. -/
def append (W₁ : SpecWrites P₁ B) (W₂ : SpecWrites P₂ B) : SpecWrites (P₁ ++ P₂) B :=
  ⟨fun i => appendOf W₁ W₂ i _ rfl, fun i => appendOf_le W₁ W₂ i _ rfl⟩

/-- `W₁ ++ W₂` is `W₁.append W₂`. -/
instance : HAppend (SpecWrites P₁ B) (SpecWrites P₂ B) (SpecWrites (P₁ ++ P₂) B) := ⟨append⟩

/-- **The codecs of an `m`-fold append** (`ProtocolSpec.appendN`): each round's codec is its
part's, by the recursion of `appendN`. -/
def appendN : (m : ℕ) → {n : Fin m → ℕ} → {P : (i : Fin m) → ProtocolSpec (n i)} →
    (∀ i, SpecWrites (P i) B) → SpecWrites (ProtocolSpec.appendN m P) B
  | 0, _, _, _ => ofNone fun i => i.elim0
  | 1, _, _, W => W 0
  | m + 2, _, _, W => W 0 ++ (appendN (m + 1) fun i => W i.succ)

/-- **The codecs of a protocol with a prover round removed** (`ProtocolSpec.dropMsg`): each round
keeps its codec. -/
def dropMsg {P : ProtocolSpec n} (W : SpecWrites P B) (s : Fin n) : SpecWrites (P.dropMsg s) B :=
  ⟨fun i => W.write (dropMsgIdx i), fun i => W.le (dropMsgIdx i)⟩

/-! ### The GKR schedule -/

section GKR

variable {F : Type} [Field F] {fb : ℕ} (FB : Codec.FieldBytes F fb)

/-- The sumcheck rounds: each prover message is two field elements. -/
def gkrRounds (hB : 2 * (1 + fb) ≤ B) : (k : ℕ) → SpecWrites (GKR.Schedule.rounds F k) B
  | 0 => ofNone fun i => i.elim0
  | k + 1 => one (WriteCodec.fieldPair FB) ((WriteCodec.fieldPair_B FB).trans_le hB) ++
      (oneV (M := F) (B := B) ++ gkrRounds hB k)

/-- The circuit's transcript: per layer, the sumcheck rounds and the two wire claims, two field
elements each. -/
def gkrCircuit (hB : 2 * (1 + fb) ≤ B) :
    {d : ℕ} → (C : GKR.Circuit F d) → SpecWrites (GKR.Schedule.circuit F C) B
  | _, .input _ => oneV
  | _, .layer (inDim := b) _ tail => oneV (M := F × F) (B := B) ++ (gkrRounds FB hB (2 * b) ++
      (one (WriteCodec.fieldPair FB) ((WriteCodec.fieldPair_B FB).trans_le hB) ++
        (gkrCircuit hB tail)))

/-- The GKR protocol of a circuit: the initial challenge, then the circuit's transcript. -/
def gkrSpec (hB : 2 * (1 + fb) ≤ B) {d : ℕ} (C : GKR.Circuit F d) :
    SpecWrites (GKR.Schedule.spec F C) B :=
  oneV (M := Fin d → F) (B := B) ++ gkrCircuit FB hB C

variable [Fintype F] {d : ℕ}

/-- **The codecs of a source circuit's GKR protocol** (`GordieHowe.GKR.LayeredCircuit.interaction`). -/
def sourceInteraction [DecidableEq F] (hB : 2 * (1 + fb) ≤ B) (S : GordieHowe.GKR.LayeredCircuit F d)
    (nodes : Sumcheck.Nodes F) : SpecWrites (S.interaction nodes).spec B := by
  cases S with
  | mk outDim inDim terms Q tail hdim =>
    cases hdim
    exact gkrSpec FB hB (.layer Q tail)

end GKR

/-! ### The Ligero phases -/

section Ligero

variable {F : Type} [Field F] {fb : ℕ} (FB : Codec.FieldBytes F fb)

/-- **The codecs of a two-stage test**: the auxiliary message (round 0) and the response
(round 2). -/
def twoStage {Aux Ch Rsp Q : Type} (cA : WriteCodec Aux) (cR : WriteCodec Rsp) (hA : cA.B ≤ B)
    (hR : cR.B ≤ B) : SpecWrites (Ligero.TwoStageTest.spec Aux Ch Rsp Q) B where
  write
    | ⟨⟨0, _⟩, _⟩ => cA
    | ⟨⟨1, _⟩, h⟩ => absurd h (by simp)
    | ⟨⟨2, _⟩, _⟩ => cR
    | ⟨⟨3, _⟩, h⟩ => absurd h (by simp)
  le
    | ⟨⟨0, _⟩, _⟩ => hA
    | ⟨⟨1, _⟩, h⟩ => absurd h (by simp)
    | ⟨⟨2, _⟩, _⟩ => hR
    | ⟨⟨3, _⟩, h⟩ => absurd h (by simp)

end Ligero

end SpecWrites

end GordieHowe.SPBCS
