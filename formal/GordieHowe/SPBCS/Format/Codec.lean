-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.SPBCS.Extraction.Transcript
public import Mathlib.Data.Set.Finite.List

@[expose] public section

/-!
# The transcript byte encoding

The byte codecs of the chains of a protocol `P` (`GordieHowe/SPBCS/Extraction/Transcript.lean`), modelling the writes of
`lib/random/transcript.h` at `f4e27b3c`; the chain-input encoding of the compiler
(`GordieHowe/SPBCS/Encoding.lean`, `GordieHowe/SPBCS/Bytes.lean`) is built from them:

- tags `TAG_BSTR = 0`, `TAG_FIELD_ELEM = 1`, `TAG_ARRAY = 2`, `TAG_CHALLENGE = 3` (line 184), one
  byte each (`tag`, lines 328–332);
- lengths as 8 little-endian bytes (`length`, lines 334–340; `u64_to_le`,
  `third_party/longfellow/lib/util/serialization.h` lines 22–31);
- a byte string is `TAG_BSTR ‖ length ‖ bytes` (`write`, lines 268–274);
- a field element is `TAG_FIELD_ELEM ‖ to_bytes_field` (lines 291–296, 362–367);
- an array of `m` field elements is `TAG_ARRAY ‖ length m ‖ m · to_bytes_field`
  (lines 299–309);
- the challenge write-back is `TAG_CHALLENGE ‖ length k ‖ head()` (`close_point`, lines 343–355,
  called first in `write_untyped`, so it is absorbed at the next write);
- the constructor writes the label as a byte string (lines 197–204); the Fiat–Shamir salt
  write `TranscriptEncoding.saltBytes σ` follows (empty when `kS = 0`); `absorb_statement`
  (`lib/zk/zk_common.h` lines 780–800) then writes the statement, each part as a byte string;
  the model takes the statement writes as a codec of the statement (`Codec`), so the writes
  before round 0 are a codec of the Fiat–Shamir salt and the statement
  (`TranscriptEncoding.saltedCodec`), and a transcript parse runs its decoder.

**The absorbed digest.** The hash chain absorbs the first `k` bytes of each round's
XOF answer, as `tagAbsorb ‖ length k ‖ d` with `tagAbsorb = 3`: the C++ `close_point` writes
`TAG_CHALLENGE = 3` (used by no other write), then the 8-byte little-endian length `k`, then the
first `k` bytes of the challenge point's stream (`head()`). The parse (`ItemCodec.parseList`) does
not need the fresh tag: it reads the chain by position, and the protocol fixes which positions are
prover rounds, so an absorbed digest is never confused with a root-only round's write
`TAG_BSTR ‖ length k ‖ root` (`lib/ligero/ligero_transcript.h` line 34).

**The Fiat–Shamir salt.** The proof's Fiat–Shamir salt (`NIProof.salt`, C++ b90f5046) is
written into the transcript as its first write after the label, as the byte string
`0x00 ‖ u64le(kS) ‖ σ` (`TranscriptEncoding.saltBytes`), before the statement writes of
`absorb_statement`; it is also part of every XOF input. The encoding is therefore of a Fiat–Shamir
salt and a statement (`SaltedStatement kS X`), and every `transcript` input carries the Fiat–Shamir
salt. At `kS = 0` there is no Fiat–Shamir salt: the salt write is empty and the writes before
round 0 are the label and the statement (`TranscriptEncoding.saltBytes`).

**Prover writes.** Round `i`'s write `Wr i` supplies a `WriteCodec`: an injective,
self-delimiting byte serialization (`Codec`) whose first byte is a tag other than
`tagAbsorb` (so it is never empty), with a length bound. `Codec.bstr`, `Codec.fieldElem`,
`Codec.fieldArray` and `Codec.prod` build the codecs of the C++ writes; a round's write
type is a product of them. A chain's bytes do not record round indices; `parseAt r` reads
position `r` with round `r`'s codec, and the laws hold on well-formed chains (`chainWF`).

The running hash of the C++ (`sha_.Update` in `write_untyped`, line 308, and in `close_point`)
hashes the concatenation of all writes and write-backs; the model's `transcript` query is the whole
concatenation.
-/

namespace GordieHowe.SPBCS
open GordieHowe.QROM

open GordieHowe.IOP
open scoped ENNReal

namespace Enc

/-- `TAG_BSTR` (`transcript.h` line 184). -/
def tagBstr : Byte := 0
/-- `TAG_FIELD_ELEM` (`transcript.h` line 184). -/
def tagFieldElem : Byte := 1
/-- `TAG_ARRAY` (`transcript.h` line 184). -/
def tagArray : Byte := 2
/-- The tag of an absorbed digest, `TAG_CHALLENGE` (`transcript.h` line 184). -/
def tagAbsorb : Byte := 3

/-- The 8-byte little-endian length (`u64_to_le`, `third_party/longfellow/lib/util/serialization.h` lines 22–31). -/
def le64 (x : ℕ) : List Byte :=
  List.ofFn fun i : Fin 8 => ⟨x / 256 ^ (i : ℕ) % 256, Nat.mod_lt _ (by norm_num)⟩

@[simp] theorem length_le64 (x : ℕ) : (le64 x).length = 8 := by simp [le64]

/-- Two naturals with the same base-`b` digits below position `m` agree modulo `b ^ m`. -/
theorem _root_.Nat.mod_pow_eq_of_digits {x y b : ℕ} :
    ∀ m, (∀ i < m, x / b ^ i % b = y / b ^ i % b) → x % b ^ m = y % b ^ m
  | 0, _ => by simp [Nat.mod_one]
  | m + 1, h => by
    rw [Nat.mod_pow_succ, Nat.mod_pow_succ, Nat.mod_pow_eq_of_digits m fun i hi => h i (by omega),
      h m (by omega)]

/-- **The 8-byte little-endian length is injective below `2^64`.** -/
theorem le64_inj {x y : ℕ} (hx : x < 2 ^ 64) (hy : y < 2 ^ 64) (h : le64 x = le64 y) : x = y := by
  have hd : ∀ i < 8, x / 256 ^ i % 256 = y / 256 ^ i % 256 := fun i hi => by
    have := congrArg Fin.val (congrFun (List.ofFn_injective h) ⟨i, hi⟩)
    simpa using this
  have := Nat.mod_pow_eq_of_digits 8 hd
  rwa [show (256 : ℕ) ^ 8 = 2 ^ 64 by norm_num, Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt hy] at this

/-! ### Stripping a fixed prefix and reading a fixed number of bytes -/

/-- Strip the prefix `p` from `s`. -/
def strip : List Byte → List Byte → Option (List Byte)
  | [], s => some s
  | _ :: _, [] => none
  | a :: p, b :: s => if a = b then strip p s else none

@[simp] theorem strip_append (p t : List Byte) : strip p (p ++ t) = some t := by
  induction p with
  | nil => rfl
  | cons a p ih => simp [strip, ih]

theorem eq_of_strip : ∀ {p s t : List Byte}, strip p s = some t → s = p ++ t
  | [], s, t, h => by simp [strip] at h; simp [h]
  | _ :: _, [], _, h => by simp [strip] at h
  | a :: p, b :: s, t, h => by
    unfold strip at h
    split_ifs at h with hab
    · rw [hab, eq_of_strip h]; rfl

/-- Read `m` bytes. -/
def takeFin (m : ℕ) (s : List Byte) : Option ((Fin m → Byte) × List Byte) :=
  if h : m ≤ s.length then some (fun i => s[i.1]'(by omega), s.drop m) else none

@[simp] theorem takeFin_append {m : ℕ} (v : Fin m → Byte) (t : List Byte) :
    takeFin m (List.ofFn v ++ t) = some (v, t) := by
  unfold takeFin
  rw [dite_cond_eq_true (eq_true (by simp : m ≤ (List.ofFn v ++ t).length))]
  congr 2
  · funext i
    simp [List.getElem_append_left]
  · simp

theorem eq_of_takeFin {m : ℕ} {s t : List Byte} {v : Fin m → Byte}
    (h : takeFin m s = some (v, t)) : s = List.ofFn v ++ t := by
  unfold takeFin at h
  split_ifs at h with hm
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some_inj.1 h)
  conv_lhs => rw [← List.take_append_drop m s]
  congr 1
  refine List.ext_getElem (by simp; omega) fun i h1 h2 => ?_
  simp

end Enc

open Enc

/-! ### Codecs -/

/-- An injective, self-delimiting byte serialization: `parse` reads one value off the front
of a byte string and returns the rest. -/
structure Codec (A : Type) where
  ser : A → List Byte
  parse : List Byte → Option (A × List Byte)
  parse_ser : ∀ a t, parse (ser a ++ t) = some (a, t)
  ser_parse : ∀ {s a t}, parse s = some (a, t) → s = ser a ++ t

namespace Codec

variable {A B : Type}

theorem ser_injective (C : Codec A) : Function.Injective C.ser := fun a b h => by
  have := C.parse_ser a []
  rw [h, C.parse_ser b []] at this
  exact (Prod.mk.inj (Option.some_inj.1 this)).1.symm

/-- **The bytes of a codec are prefix-free**: a value's bytes that begin another value's bytes
are those of the same value. -/
theorem prefixFree (C : Codec A) {a b : A} (h : C.ser a <+: C.ser b) : a = b := by
  obtain ⟨t, ht⟩ := h
  have h1 := C.parse_ser a t
  rw [ht, ← List.append_nil (C.ser b), C.parse_ser b []] at h1
  exact (Prod.mk.inj (Option.some_inj.1 h1)).1.symm

/-- The bytes `hdr ‖ v` for a fixed header `hdr` and `m` bytes `v`. -/
def framed (hdr : List Byte) (m : ℕ) : Codec (Fin m → Byte) where
  ser v := hdr ++ List.ofFn v
  parse s := (strip hdr s).bind (takeFin m)
  parse_ser v t := by simp
  ser_parse {s v t} h := by
    obtain ⟨u, hu, hv⟩ := Option.bind_eq_some_iff.1 h
    rw [eq_of_strip hu, eq_of_takeFin hv, List.append_assoc]

/-- A framed value serializes to `hdr.length + m` bytes, whatever the value. -/
theorem length_ser_framed (hdr : List Byte) (m : ℕ) (v : Fin m → Byte) :
    ((framed hdr m).ser v).length = hdr.length + m := by
  simp only [framed, List.length_append, List.length_ofFn]

/-- A codec transported along a partial inverse: `of` recovers `a` from `to a` and fails
off the image of `to`. -/
def mapPartial (C : Codec A) (enc : B → A) (dec : A → Option B)
    (dec_enc : ∀ b, dec (enc b) = some b) (enc_dec : ∀ {a b}, dec a = some b → enc b = a) :
    Codec B where
  ser b := C.ser (enc b)
  parse s := (C.parse s).bind fun p => (dec p.1).map fun b => (b, p.2)
  parse_ser b t := by simp [C.parse_ser, dec_enc]
  ser_parse {s b t} h := by
    obtain ⟨⟨a, u⟩, hp, hb⟩ := Option.bind_eq_some_iff.1 h
    obtain ⟨b', hb', he⟩ := Option.map_eq_some_iff.1 hb
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj he
    rw [C.ser_parse hp, enc_dec hb']

/-- A codec transported along an equivalence. -/
def mapEquiv (C : Codec A) (f : B ≃ A) : Codec B :=
  C.mapPartial f (fun a => some (f.symm a)) (by simp) (by
    intro a b h
    rw [← Option.some_inj.1 h, Equiv.apply_symm_apply])

/-- Two values written one after the other. -/
def prod (C : Codec A) (D : Codec B) : Codec (A × B) where
  ser p := C.ser p.1 ++ D.ser p.2
  parse s := (C.parse s).bind fun p => (D.parse p.2).map fun q => ((p.1, q.1), q.2)
  parse_ser p t := by simp [List.append_assoc, C.parse_ser, D.parse_ser]
  ser_parse {s p t} h := by
    obtain ⟨⟨a, u⟩, ha, hb⟩ := Option.bind_eq_some_iff.1 h
    obtain ⟨⟨b, v⟩, hb', he⟩ := Option.map_eq_some_iff.1 hb
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj he
    dsimp only at hb' ⊢
    rw [C.ser_parse ha, D.ser_parse hb', List.append_assoc]

/-- A byte string of `m` bytes: `TAG_BSTR ‖ length m ‖ bytes` (`transcript.h`
lines 268–274). -/
def bstr (m : ℕ) : Codec (Fin m → Byte) := framed (tagBstr :: le64 m) m

/-- The absorbed digest: `tagAbsorb ‖ length k ‖ d` (`close_point`, `transcript.h`, lines
343–355). -/
def absorb (k : ℕ) : Codec (Digest k) := framed (tagAbsorb :: le64 k) k

/-- The canonical `fb`-byte encoding of a field element (`to_bytes_field`) and its partial
inverse (`of_bytes_field`, which fails on non-canonical strings). -/
structure FieldBytes (F : Type) (fb : ℕ) where
  toBytes : F → Fin fb → Byte
  ofBytes : (Fin fb → Byte) → Option F
  ofBytes_toBytes : ∀ x, ofBytes (toBytes x) = some x
  toBytes_ofBytes : ∀ {v x}, ofBytes v = some x → toBytes x = v

/-- One field element: `TAG_FIELD_ELEM ‖ to_bytes_field x` (`transcript.h` lines 291–296). -/
def fieldElem {F : Type} {fb : ℕ} (FB : FieldBytes F fb) : Codec F :=
  (framed [tagFieldElem] fb).mapPartial FB.toBytes FB.ofBytes FB.ofBytes_toBytes
    FB.toBytes_ofBytes

/-- All components defined. -/
def optPi {m : ℕ} {F : Type} (f : Fin m → Option F) : Option (Fin m → F) :=
  if h : ∀ i, (f i).isSome then some fun i => (f i).get (h i) else none

theorem optPi_some {m : ℕ} {F : Type} (g : Fin m → F) : optPi (fun i => some (g i)) = some g := by
  simp [optPi]

theorem eq_of_optPi {m : ℕ} {F : Type} {f : Fin m → Option F} {g : Fin m → F}
    (h : optPi f = some g) (i : Fin m) : f i = some (g i) := by
  unfold optPi at h
  split_ifs at h with hs
  rw [← Option.some_inj.1 h]
  simp

/-- The bytes of `m` field elements, element `i` at bytes `[i·fb, (i+1)·fb)`. -/
def chunks (m fb : ℕ) : (Fin (m * fb) → Byte) ≃ (Fin m → Fin fb → Byte) :=
  (finProdFinEquiv.arrowCongr (Equiv.refl Byte)).symm.trans (Equiv.curry _ _ _)

/-- An array of `m` field elements: `TAG_ARRAY ‖ length m ‖ to_bytes_field x_0 ‖ …`
(`transcript.h` lines 299–309, with stride `ince = 1`). -/
def fieldArray {F : Type} {fb : ℕ} (FB : FieldBytes F fb) (m : ℕ) : Codec (Fin m → F) :=
  (framed (tagArray :: le64 m) (m * fb)).mapPartial
    (fun x => (chunks m fb).symm fun i => FB.toBytes (x i))
    (fun v => optPi fun i => FB.ofBytes (chunks m fb v i))
    (fun x => by simpa [FB.ofBytes_toBytes] using optPi_some x)
    (by
      intro v x h
      apply (chunks m fb).injective
      rw [Equiv.apply_symm_apply]
      funext i
      exact FB.toBytes_ofBytes (eq_of_optPi h i))

end Codec

/-- The codec of a prover round's write: its first byte is never `tagAbsorb`, and it has
at most `B` bytes. This is what the write type `W` must provide. -/
structure WriteCodec (W : Type) extends Codec W where
  B : ℕ
  head_ser : ∀ w, ∃ b r, ser w = b :: r ∧ b ≠ tagAbsorb
  length_ser_le : ∀ w, (ser w).length ≤ B

namespace WriteCodec

variable {A B : Type}

/-- A byte string write of `m` bytes (a Merkle root, `m = k`). -/
def bstr (m : ℕ) : WriteCodec (Fin m → Byte) where
  toCodec := Codec.bstr m
  B := 9 + m
  head_ser v := ⟨tagBstr, le64 m ++ List.ofFn v, rfl, by decide⟩
  length_ser_le v := by simp [Codec.bstr, Codec.framed]

/-- One field element write. -/
def fieldElem {F : Type} {fb : ℕ} (FB : Codec.FieldBytes F fb) : WriteCodec F where
  toCodec := Codec.fieldElem FB
  B := 1 + fb
  head_ser x := ⟨tagFieldElem, List.ofFn (FB.toBytes x), by
    simp [Codec.fieldElem, Codec.mapPartial, Codec.framed], by decide⟩
  length_ser_le x := by
    simp [Codec.fieldElem, Codec.mapPartial, Codec.framed]

/-- An array write of `m` field elements. -/
def fieldArray {F : Type} {fb : ℕ} (FB : Codec.FieldBytes F fb) (m : ℕ) :
    WriteCodec (Fin m → F) where
  toCodec := Codec.fieldArray FB m
  B := 9 + m * fb
  head_ser x := ⟨tagArray, le64 m ++ List.ofFn ((Codec.chunks m fb).symm fun i => FB.toBytes (x i)),
    by simp only [Codec.fieldArray, Codec.mapPartial, Codec.framed, List.cons_append],
    by decide⟩
  length_ser_le x := by
    simp [Codec.fieldArray, Codec.mapPartial, Codec.framed]

/-- Two writes of one round, one after the other. -/
def prod (C : WriteCodec A) (D : WriteCodec B) : WriteCodec (A × B) where
  toCodec := C.toCodec.prod D.toCodec
  B := C.B + D.B
  head_ser p := by
    obtain ⟨b, r, h, hb⟩ := C.head_ser p.1
    exact ⟨b, r ++ D.ser p.2, by simp [Codec.prod, h], hb⟩
  length_ser_le p := by
    simp only [Codec.prod, List.length_append]
    exact Nat.add_le_add (C.length_ser_le _) (D.length_ser_le _)

/-- **A type with a write codec is finite**: the serialization is injective and takes values in
the byte strings of at most `B` bytes, of which there are finitely many. -/
theorem finite (C : WriteCodec A) : Finite A :=
  have : Finite {l : List Byte // l.length ≤ C.B} := (List.finite_length_le Byte C.B).to_subtype
  Finite.of_injective (fun a => (⟨C.ser a, C.length_ser_le a⟩ : {l : List Byte // l.length ≤ C.B}))
    fun _ _ h => C.ser_injective (congrArg Subtype.val h)

/-- An infinite type has no write codec (`WriteCodec.finite`). -/
theorem isEmpty_of_infinite [Infinite A] : IsEmpty (WriteCodec A) :=
  ⟨fun C => C.finite.false⟩

/-- A write transported along an equivalence. -/
def mapEquiv (C : WriteCodec A) (f : B ≃ A) : WriteCodec B where
  toCodec := C.toCodec.mapEquiv f
  B := C.B
  head_ser b := by simpa [Codec.mapEquiv, Codec.mapPartial] using C.head_ser (f b)
  length_ser_le b := C.length_ser_le (f b)

end WriteCodec

/-- **`n + 1` writes of one codec, one after the other**, the value at `0` first. -/
def WriteCodec.repeat {A : Type} (C : WriteCodec A) : (n : ℕ) → WriteCodec (Fin (n + 1) → A)
  | 0 => C.mapEquiv (Equiv.funUnique (Fin 1) A)
  | n + 1 => (C.prod (C.repeat n)).mapEquiv (Fin.consEquiv fun _ => A).symm

@[simp] theorem WriteCodec.repeat_B {A : Type} (C : WriteCodec A) :
    ∀ n, (C.repeat n).B = (n + 1) * C.B
  | 0 => (one_mul _).symm
  | n + 1 => by
    change C.B + (C.repeat n).B = _
    rw [WriteCodec.repeat_B C n]
    ring

/-- **The roots of `m` trees**, one byte-string write per root in order,
`TAG_BSTR ‖ u64le(k) ‖ root` (the C++ `LigeroTranscript::write_commitment`,
`lib/ligero/ligero_transcript.h` lines 30–35, once per tree). -/
def WriteCodec.roots (m k : ℕ) [NeZero m] : WriteCodec (Fin m → Digest k) :=
  ((WriteCodec.bstr k).repeat (m - 1)).mapEquiv
    ((finCongr (Nat.sub_add_cancel (NeZero.one_le (n := m))).symm).arrowCongr (Equiv.refl _))

@[simp] theorem WriteCodec.roots_B (m k : ℕ) [NeZero m] :
    (WriteCodec.roots m k).B = m * (9 + k) := by
  change ((WriteCodec.bstr k).repeat (m - 1)).B = _
  rw [WriteCodec.repeat_B, Nat.sub_add_cancel (NeZero.one_le (n := m))]
  rfl

/-! ### Items and chains -/

namespace ItemCodec

variable {k n : ℕ} {P : ProtocolSpec n} {Wr : P.MessageIdx → Type}
  (C : (i : P.MessageIdx) → WriteCodec (Wr i))

/-- The bytes of one chain item: the write of its round, or the absorbed digest. The round
index is not written; the parse reads it from the item's position. -/
def ser : Item k (Σ i, Wr i) → List Byte
  | .write w => (C w.1).ser w.2
  | .absorb d => (Codec.absorb k).ser d

/-- Read the item at position `r` of a chain of `P`: round `r`'s write if `r` is a prover
round, an absorbed digest if it is a challenge round. -/
def parseAt (r : ℕ) (s : List Byte) : Option (Item k (Σ i, Wr i) × List Byte) :=
  if h : r < n then
    if hd : P.dir ⟨r, h⟩ = .P_to_V then
      ((C ⟨⟨r, h⟩, hd⟩).parse s).map fun p => (.write ⟨⟨⟨r, h⟩, hd⟩, p.1⟩, p.2)
    else ((Codec.absorb k).parse s).map fun p => (.absorb p.1, p.2)
  else none

theorem parseAt_ser {r : ℕ} {it : Item k (Σ i, Wr i)} (hf : Fits P r it) (t : List Byte) :
    parseAt C r (ser C it ++ t) = some (it, t) := by
  cases it with
  | write w =>
    obtain ⟨⟨⟨r', hr'⟩, hd⟩, w⟩ := w
    obtain rfl : r' = r := hf
    unfold parseAt
    rw [dif_pos hr', dif_pos hd]
    simp only [ser]
    rw [(C ⟨⟨r', hr'⟩, hd⟩).parse_ser]
    rfl
  | absorb d =>
    obtain ⟨hr, hd⟩ := hf
    have hd' : ¬ P.dir ⟨r, hr⟩ = .P_to_V := by simp [hd]
    simp [parseAt, hr, hd', ser, (Codec.absorb k).parse_ser]

theorem ser_parseAt {r : ℕ} {s : List Byte} {it : Item k (Σ i, Wr i)} {t : List Byte}
    (h : parseAt C r s = some (it, t)) : s = ser C it ++ t ∧ Fits P r it := by
  unfold parseAt at h
  split_ifs at h with hr hd
  · obtain ⟨⟨w, u⟩, hp, he⟩ := Option.map_eq_some_iff.1 h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj he
    exact ⟨(C _).ser_parse hp, rfl⟩
  · obtain ⟨⟨d, u⟩, hp, he⟩ := Option.map_eq_some_iff.1 h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj he
    exact ⟨(Codec.absorb k).ser_parse hp, hr, by cases h' : P.dir ⟨r, hr⟩ <;> simp_all⟩

theorem ser_ne_nil (it : Item k (Σ i, Wr i)) : ser C it ≠ [] := by
  cases it with
  | write w =>
    obtain ⟨b, r, h, -⟩ := (C w.1).head_ser w.2
    simp [ser, h]
  | absorb d => simp [ser, Codec.absorb, Codec.framed]

theorem length_ser_le {B : ℕ} (hB : ∀ i, (C i).B ≤ B) (it : Item k (Σ i, Wr i)) :
    (ser C it).length ≤ max B (9 + k) := by
  cases it with
  | write w => exact ((C w.1).length_ser_le w.2).trans ((hB w.1).trans (le_max_left _ _))
  | absorb d =>
    simp only [ser, Codec.absorb, Codec.framed, List.length_append, List.length_cons,
      length_le64, List.length_ofFn]
    omega

/-- The bytes of a list of items. -/
def serList (l : List (Item k (Σ i, Wr i))) : List Byte := (l.map (ser C)).flatten

/-- Read items from position `r` on until the input is exhausted; `fuel` bounds the number
of items. -/
def parseList : ℕ → ℕ → List Byte → Option (List (Item k (Σ i, Wr i)))
  | _, _, [] => some []
  | 0, _, _ :: _ => none
  | fuel + 1, r, b :: s =>
    (parseAt C r (b :: s)).bind fun p => (parseList fuel (r + 1) p.2).map (p.1 :: ·)

theorem parseList_serList (l : List (Item k (Σ i, Wr i))) :
    ∀ r, (∀ j (hj : j < l.length), Fits P (r + j) l[j]) →
      ∀ fuel, (serList C l).length ≤ fuel → parseList C fuel r (serList C l) = some l := by
  induction l with
  | nil => intro r _ fuel _; cases fuel <;> rfl
  | cons it l ih =>
    intro r hf fuel hfuel
    have hne := ser_ne_nil C it
    obtain ⟨b, s, hbs⟩ := List.exists_cons_of_ne_nil hne
    have hs : serList C (it :: l) = b :: (s ++ serList C l) := by
      simp [serList, hbs]
    have hlen : (serList C (it :: l)).length = (ser C it).length + (serList C l).length := by
      simp [serList]
    have hit : Fits P r it := hf 0 (by simp)
    have hl : ∀ j (hj : j < l.length), Fits P (r + 1 + j) l[j] := fun j hj => by
      have := hf (j + 1) (by simp; omega)
      rwa [show r + (j + 1) = r + 1 + j by omega] at this
    cases fuel with
    | zero => rw [hs] at hfuel; simp at hfuel
    | succ fuel =>
      have hp : parseAt C r (b :: (s ++ serList C l)) = some (it, serList C l) := by
        rw [← List.cons_append, ← hbs]; exact parseAt_ser C hit _
      rw [hs, parseList, hp, Option.bind_some, ih (r + 1) hl fuel (by
        have : 1 ≤ (ser C it).length := List.length_pos_of_ne_nil hne
        omega)]
      rfl

/-- **Parsed items fit their positions.** -/
theorem fits_of_parseList : ∀ (fuel r : ℕ) {s : List Byte} {l : List (Item k (Σ i, Wr i))},
    parseList C fuel r s = some l → ∀ j (hj : j < l.length), Fits P (r + j) l[j]
  | fuel, _, [], l, h => by
    cases fuel <;> simp [parseList] at h <;> (subst h; intro j hj; simp at hj)
  | 0, _, _ :: _, _, h => by simp [parseList] at h
  | fuel + 1, r, b :: s, l, h => by
    rw [parseList] at h
    obtain ⟨⟨it, u⟩, hp, hl⟩ := Option.bind_eq_some_iff.1 h
    obtain ⟨l', hl', rfl⟩ := Option.map_eq_some_iff.1 hl
    intro j hj
    cases j with
    | zero => simpa using (ser_parseAt C hp).2
    | succ j =>
      have := fits_of_parseList fuel (r + 1) hl' j (by simp at hj; omega)
      rw [show r + 1 + j = r + (j + 1) by omega] at this
      simpa using this

theorem serList_of_parseList : ∀ (fuel r : ℕ) {s : List Byte} {l : List (Item k (Σ i, Wr i))},
    parseList C fuel r s = some l → serList C l = s
  | fuel, _, [], l, h => by
    cases fuel <;> simp [parseList] at h <;> (subst h; rfl)
  | 0, _, _ :: _, _, h => by simp [parseList] at h
  | fuel + 1, r, b :: s, l, h => by
    rw [parseList] at h
    obtain ⟨⟨it, u⟩, hp, hl⟩ := Option.bind_eq_some_iff.1 h
    obtain ⟨l', hl', rfl⟩ := Option.map_eq_some_iff.1 hl
    have e := serList_of_parseList fuel (r + 1) hl'
    dsimp only at e ⊢
    rw [(ser_parseAt C hp).1, ← e]
    simp [serList]

theorem length_serList_le {B : ℕ} (hB : ∀ i, (C i).B ≤ B) (l : List (Item k (Σ i, Wr i))) :
    (serList C l).length ≤ l.length * max B (9 + k) := by
  induction l with
  | nil => simp [serList]
  | cons it l ih =>
    have h1 := length_ser_le C hB it
    simp only [serList, List.map_cons, List.flatten_cons, List.length_append,
      List.length_cons] at ih ⊢
    rw [Nat.succ_mul]
    omega

end ItemCodec

/-! ### Bounded byte strings -/

section Bytes
open GordieHowe.QROM.Bytes

variable {L : ℕ}

/-- A list of at most `L` bytes as `Bytes L`; longer lists map to the empty string (the
encodings below never are). -/
def _root_.GordieHowe.QROM.Bytes.ofList (l : List Byte) : Bytes L :=
  if h : l.length ≤ L then ⟨⟨l.length, by omega⟩, fun i => l[i.1]'(by simp)⟩
  else ⟨0, Fin.elim0⟩

/-- The bytes of `b`. -/
def _root_.GordieHowe.QROM.Bytes.toList (b : Bytes L) : List Byte := List.ofFn b.data

theorem _root_.GordieHowe.QROM.Bytes.toList_ofList {l : List Byte} (h : l.length ≤ L) : toList (ofList (L := L) l) = l := by
  rw [ofList, dif_pos h, toList]
  exact List.ext_getElem (by simp) fun i _ _ => by simp

theorem _root_.GordieHowe.QROM.Bytes.ofList_toList (b : Bytes L) : ofList (toList b) = b := by
  obtain ⟨⟨m, hm⟩, v⟩ := b
  have hl : (List.ofFn v).length ≤ L := by simp; omega
  rw [toList, ofList, dif_pos hl]
  exact Bytes.ext (Fin.ext (by simp)) ((Fin.heq_fun_iff (by simp)).2 fun i => by simp)

theorem _root_.GordieHowe.QROM.Bytes.length_toList_le (b : Bytes L) : (toList b).length ≤ L := by
  simp [toList]; omega

end Bytes

/-! ### Leaves read by a codec -/

namespace Codec

variable {α : Type} {kN L : ℕ}

/-- **The value of a Merkle leaf read by a codec**: the value parsed from the leaf's bytes, or
`z` if the leaf is missing or its bytes are not exactly one serialized value. -/
def decodeLeaf (C : Codec α) (z : α) : Option (MerkleLeaf kN L) → α
  | some ⟨_, b⟩ => match C.parse (Bytes.toList b) with
    | some (a, []) => a
    | _ => z
  | none => z

/-- A leaf holding the serialization of `c`, with any salt, reads as `c` when serializations fit
in `L` bytes. -/
theorem decodeLeaf_ser {C : Codec α} {z : α} (hfit : ∀ c, (C.ser c).length ≤ L)
    (ν : MerkleSalt kN) (c : α) : C.decodeLeaf (L := L) z (some ⟨ν, Bytes.ofList (C.ser c)⟩) = c := by
  simp only [decodeLeaf, Bytes.toList_ofList (hfit c)]
  have := C.parse_ser c []
  rw [List.append_nil] at this
  rw [this]

end Codec

/-! ### The encoding -/

namespace TranscriptEncoding

/-- The label write of the constructor, `TAG_BSTR ‖ length ‖ label` (`transcript.h`
lines 197–204). -/
def labelBytes (label : List Byte) : List Byte := tagBstr :: le64 label.length ++ label

/-- The length of the salt write of a `kS`-byte Fiat–Shamir salt: `9 + kS` bytes, or none when there is no
Fiat–Shamir salt (`kS = 0`). -/
def saltLen (kS : ℕ) : ℕ := if kS = 0 then 0 else 9 + kS

theorem saltLen_le (kS : ℕ) : saltLen kS ≤ 9 + kS := by
  unfold saltLen
  split_ifs <;> omega

/-- The Fiat–Shamir salt write, `TAG_BSTR ‖ u64le(kS) ‖ σ`: the first write after the
label (C++ b90f5046). A Fiat–Shamir salt of zero bytes is the case without a Fiat–Shamir salt, whose write is empty. -/
def saltBytes {kS : ℕ} (σ : FiatShamirSalt kS) : List Byte := if kS = 0 then [] else (Codec.bstr kS).ser σ

@[simp] theorem length_saltBytes {kS : ℕ} (σ : FiatShamirSalt kS) : (saltBytes σ).length = saltLen kS := by
  unfold saltBytes saltLen
  split_ifs
  · rfl
  · simp [Codec.bstr, Codec.framed]; omega

/-- **The codec of the Fiat–Shamir salt write** (`saltBytes`): the byte string of the `kS` salt
bytes (`Codec.bstr kS`), or no bytes when `kS = 0`.

Running time: at most `9 + kS` byte comparisons and copies. This running time is argued here, not
proved in Lean. -/
def saltCodec (kS : ℕ) : Codec (FiatShamirSalt kS) where
  ser := saltBytes
  parse s := if kS = 0 then some (fun _ => 0, s) else (Codec.bstr kS).parse s
  parse_ser σ t := by
    unfold saltBytes
    split_ifs with hk
    · subst hk
      simp only [List.nil_append, Option.some.injEq, Prod.mk.injEq, and_true]
      exact Subsingleton.elim _ _
    · exact (Codec.bstr kS).parse_ser σ t
  ser_parse {s σ t} h := by
    unfold saltBytes
    split_ifs at h ⊢ with hk
    · obtain ⟨-, rfl⟩ := Prod.mk.inj (Option.some_inj.1 h)
      rfl
    · exact (Codec.bstr kS).ser_parse h

variable {X : Type}

/-- **The codec of the writes before the first round**: the label write `lab`, the Fiat–Shamir
salt write (`saltCodec`), then the statement writes of the codec `CX`. Its decoder strips the
label, reads the salt and runs `CX`'s decoder.

Running time: `lab.length` byte comparisons, at most `9 + kS` for the salt, then one run of
`CX.parse`. This running time is argued here, not proved in Lean. -/
def saltedCodec {kS : ℕ} (lab : List Byte) (CX : Codec X) : Codec (SaltedStatement kS X) where
  ser p := lab ++ saltBytes p.salt ++ CX.ser p.stmt
  parse s := (strip lab s).bind fun u => ((saltCodec kS).parse u).bind fun q =>
    (CX.parse q.2).map fun r => (⟨q.1, r.1⟩, r.2)
  parse_ser p t := by
    have h1 : (saltCodec kS).parse (saltBytes p.salt ++ (CX.ser p.stmt ++ t)) =
        some (p.salt, CX.ser p.stmt ++ t) :=
      (saltCodec kS).parse_ser _ _
    simp only [List.append_assoc, strip_append, Option.bind_some, h1, CX.parse_ser,
      Option.map_some]
  ser_parse {s p t} h := by
    obtain ⟨u, hu, h⟩ := Option.bind_eq_some_iff.1 h
    obtain ⟨⟨σ, v⟩, hv, h⟩ := Option.bind_eq_some_iff.1 h
    obtain ⟨⟨x, w⟩, hw, he⟩ := Option.map_eq_some_iff.1 h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj he
    dsimp only at hw ⊢
    rw [eq_of_strip hu, (saltCodec kS).ser_parse hv, CX.ser_parse hw]
    simp only [List.append_assoc]
    rfl

variable {k L n : ℕ} {P : ProtocolSpec n} {Wr : P.MessageIdx → Type}
  (C : (i : P.MessageIdx) → WriteCodec (Wr i)) (CX : Codec X)

variable {C CX}

variable (C)

variable (CX) (dg : (Σ i, Wr i) → Finset (Digest k)) {nd : ℕ} (B : ℕ)

end TranscriptEncoding

end GordieHowe.SPBCS
