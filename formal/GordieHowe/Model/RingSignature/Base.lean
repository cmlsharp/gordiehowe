-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Model.RingSignature.Scheme
public import GordieHowe.Model.Signature.Scheme
public import GordieHowe.Model.NARG.Prover

public section

/-!
# Ring signatures from a base signer and a proof system

The construction of the library's ring signatures as one `RingScheme` (`ofBase`): a ring signature
on `(R, m)` is a public value `y` with a proof `π` of the ring relation for the statement `(R, m, y)`,
the witness being the signer's position and a base signature.

- `BaseSigner X Y N T RMsg`: what a ring signature proves knowledge of: a base scheme
  (`Signature.BaseScheme`, `GordieHowe/Model/Signature/Scheme.lean`: the scheme's keys, its
  ordinary signer `ssign` on base messages, base verification `bverify` at the oracle and the public
  value `pub`) extended with the base message of a ring and a message (`bmsg`: `m`, or
  `m ‖ encode R`) and the ring-aware base signer `bsign` (from the secret key, the ring, the
  signer's position, the message and coins; it may refuse). `ssign` serves the joint-security game.
- `RingStmtOf`, `RingWitOf`: statements and witnesses, depending only on the base signer's key,
  message, public-value and signature types.
- `RingStmt B`, `RingWit B`, `RingRel B adm H`, `ringRel B adm H`: statements `(R, m, y)`, witnesses
  `(i, σ)` and the ring relation at the oracle `H` on the supported rings `adm`:
  `adm R ∧ i < |R| ∧ bverify_H(R_i, bmsg R m, σ) ∧ pub_H(R_i, σ) = y`.
  `ringRel_mono`: fewer supported rings give a smaller relation.
- `ringRelAll B adm`: the ring relation at every oracle (`ringRel_of_mem_ringRelAll`).
- `BaseSigner.BindsRing`: the base message binds the ring and the ring message.
- `ProofSystem X Y Stmt Wit`: a non-interactive proof system with an honest prover (a classical
  oracle program from a statement, a witness and uniform coins) and a verifier at the oracle;
  `ProofSystem.prover`, `ProofSystem.ofProver`: as a `NARG.Prover` and back.
- `ofBase B adm PS`: the ring scheme. Signing locates the signer's key in the ring (its first
  position `i`), refuses rings without it and unsupported rings, runs `bsign` at `i`, computes
  `y = pub(R_i, σ)` and proves `(R, m, y)` with the witness `(i, σ)`; verification runs `PS`'s
  verifier on `(R, m, y)`.
- Sanity: `ofBase_refusesOutside`, `run_signAt_of_bsign` (an honest signature is the public value
  and the proof of the base signature), `ringRel_of_bsign` (a verifying base signature of the
  signer at its position is a witness of the statement it signs: the relation is satisfiable on
  honest signatures), `verify_ofBase`.

## Sources and deliberate differences

The construction is BKM06's generic one (ePrint 2005/304, section 5: a signature `σ'` of the
signer's standard scheme on `M ‖ PK_1 ‖ … ‖ PK_n` and a witness-indistinguishable proof that one of
the ring's keys signed it), with spBCS in place of ZAPs and encryption, and with the public value
`y` in the statement. The differences:

1. **The public value is in the statement.** A part `y` of the base signature leaves the circuit
   (Falcon's salt, which `HashToPoint` reads outside it; ML-DSA's `w₁` in the ring publishing it);
   `y = Unit` gives BKM06's shape.
2. **The base message may not bind the ring** (`bmsg R m = m`, converted signatures): BKM06 signs
   `M ‖ PK_1 ‖ … ‖ PK_n`. Which unforgeability holds depends on it (`Joint.lean`).
3. **The base signer reads the ring** (`bsign` takes the ring and the position) and may refuse:
   the generic rings read it only through `bmsg`; the ML-DSA ring publishing `w₁` reads the members'
   published `t₀` and hashes for its keep decision and refuses rings failing the public check.
4. **The supported rings `adm`** are a parameter of the construction (the ring sizes the proof
   system's circuit is compiled for), enforced by the signer and by the relation.
5. **`pub` is a classical oracle program**, so the signer, itself an oracle program, can compute
   it; `bverify` is a function of the oracle, read only by the relation.
-/

namespace GordieHowe.RingSignature

open GordieHowe.Signature (KeyPair)

open scoped ENNReal

/-- **A base signer** with the random oracle `X → Y` for rings of at most `N` keys, the scheme
types `T` (public keys, secret keys, the coins of key generation, base messages, base signatures,
public values and the coins of signing) and the ring messages `RMsg`: a base scheme
(`Signature.BaseScheme`: keys from uniform coins, the ordinary base signer on base messages with at
most `q` queries, base verification at the oracle, and the public value of a base signature under a
key with at most `qPub` queries) with the base message of a ring and a ring message, and the
ring-aware base signer from the secret key, the ring, the signer's position, the message and
uniform coins (at most `q` queries; it may refuse). -/
structure BaseSigner (X Y : Type) (N : ℕ) (T : Signature.SchemeTypes) (RMsg : Type) extends
    core : Signature.BaseScheme X Y T where
  /-- The base message of a ring and a ring message. -/
  bmsg : KeyRing T.PK N → RMsg → T.BMsg
  /-- The ring-aware base signer at a position of the ring; `none` is a refusal. -/
  bsign : T.SK → KeyRing T.PK N → ℕ → RMsg → T.Coins → OracleProg X Y (Option T.BSig)
  /-- It makes at most `q` queries. -/
  bsign_queries : ∀ sk R i m c, (bsign sk R i m c).QueriesLE q

namespace BaseSigner

variable {X Y : Type} {N : ℕ} {T : Signature.SchemeTypes} {RMsg : Type}

/-- Public keys: those of the types `T`. -/
abbrev PK (_ : BaseSigner X Y N T RMsg) : Type := T.PK

/-- Secret keys: those of the types `T`. -/
abbrev SK (_ : BaseSigner X Y N T RMsg) : Type := T.SK

/-- The coins of key generation: those of the types `T`. -/
abbrev KeyCoins (_ : BaseSigner X Y N T RMsg) : Type := T.KeyCoins

/-- Ring messages: `RMsg`. -/
abbrev Msg (_ : BaseSigner X Y N T RMsg) : Type := RMsg

/-- Base messages: those of the types `T`. -/
abbrev BMsg (_ : BaseSigner X Y N T RMsg) : Type := T.BMsg

/-- Base signatures: those of the types `T`. -/
abbrev BSig (_ : BaseSigner X Y N T RMsg) : Type := T.BSig

/-- Public values: those of the types `T`. -/
abbrev Pub (_ : BaseSigner X Y N T RMsg) : Type := T.Pub

/-- The coins of signing: those of the types `T`. -/
abbrev Coins (_ : BaseSigner X Y N T RMsg) : Type := T.Coins

end BaseSigner

namespace BaseSigner

variable {X Y : Type} {N : ℕ}

/-- **The base signer that signs a ring as the scheme `C` signs the base message**: the scheme `C`,
the base message `bmsg R m` of a ring and a ring message, and `bsign` running `C.ssign` on it. The
ring and the position are read only through `bmsg`. -/
@[expose] def ofCore {S : Signature.SchemeTypes} (C : Signature.BaseScheme X Y S) {RMsg : Type}
    (bmsg : KeyRing S.PK N → RMsg → S.BMsg) : BaseSigner X Y N S RMsg where
  core := C
  bmsg := bmsg
  bsign sk R _ m c := C.ssign sk (bmsg R m) c
  bsign_queries sk R _ m c := C.ssign_queries sk (bmsg R m) c

section ofCore

variable {S : Signature.SchemeTypes} (C : Signature.BaseScheme X Y S) {RMsg : Type}
  (bmsg : KeyRing S.PK N → RMsg → S.BMsg)

/-- The scheme of `ofCore C bmsg` is `C`. -/
@[simp] theorem ofCore_core : (ofCore C bmsg).core = C := rfl

/-- The base message of `ofCore C bmsg` is `bmsg`. -/
@[simp] theorem ofCore_bmsg : (ofCore C bmsg).bmsg = bmsg := rfl

/-- The ring-aware signer of `ofCore C bmsg` runs `C.ssign` on the base message. -/
@[simp] theorem ofCore_bsign (sk : S.SK) (R : KeyRing S.PK N) (i : ℕ) (m : RMsg) (c : S.Coins) :
    (ofCore C bmsg).bsign sk R i m c = C.ssign sk (bmsg R m) c := rfl

end ofCore

/-- **The base message binds the ring and the message** (BKM06 section 5, ePrint 2005/304: the
base signature is on `M ‖ PK_1 ‖ … ‖ PK_n`): `bmsg R m = bmsg R' m'` gives `R = R'` and
`m = m'`. -/
@[expose] def BindsRing {T : Signature.SchemeTypes} {RMsg : Type}
    (B : BaseSigner X Y N T RMsg) : Prop :=
  ∀ (R R' : KeyRing B.PK N) (m m' : B.Msg), B.bmsg R m = B.bmsg R' m' → R = R' ∧ m = m'

end BaseSigner

variable {X Y : Type} {N : ℕ}

/-- **The ring relation's statement**, depending only on the base signer's key, message and
public-value types: a ring of at most `N` keys, a ring message and a public value. -/
structure RingStmtOf (PK Msg Pub : Type) (N : ℕ) where
  /-- The ring. -/
  ring : KeyRing PK N
  /-- The ring message. -/
  msg : Msg
  /-- The public value. -/
  pub : Pub
deriving DecidableEq

/-- **Ring statements as triples** of a ring, a ring message and a public value. -/
@[expose] def RingStmtOf.equivProd (PK Msg Pub : Type) (N : ℕ) :
    RingStmtOf PK Msg Pub N ≃ KeyRing PK N × Msg × Pub where
  toFun x := (x.ring, x.msg, x.pub)
  invFun p := ⟨p.1, p.2.1, p.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- **The ring statements are finite** for finite keys, messages and public values. -/
noncomputable instance {PK Msg Pub : Type} [Fintype PK] [DecidableEq PK] [Fintype Msg] [Fintype Pub]
    {N : ℕ} : Fintype (RingStmtOf PK Msg Pub N) :=
  Fintype.ofEquiv _ (RingStmtOf.equivProd PK Msg Pub N).symm

/-- **The ring relation's witness**, depending only on the base signer's signature type: the
signer's position and a base signature. -/
structure RingWitOf (BSig : Type) where
  /-- The signer's position. -/
  idx : ℕ
  /-- The base signature. -/
  sig : BSig
deriving DecidableEq

/-- **A statement of the ring relation** of the base signer `B` (`RingStmtOf` at its key,
message and public-value types): a ring, a ring message and a public value. -/
abbrev RingStmt {T : Signature.SchemeTypes} {RMsg : Type} (_ : BaseSigner X Y N T RMsg) : Type :=
  RingStmtOf T.PK RMsg T.Pub N

/-- **A witness of the ring relation** of the base signer `B` (`RingWitOf` at its signature
type): the signer's position and a base signature. -/
abbrev RingWit {T : Signature.SchemeTypes} {RMsg : Type} (_ : BaseSigner X Y N T RMsg) : Type :=
  RingWitOf T.BSig

/-- **The ring relation** `R_ring((R, m, y), (i, σ))` at the oracle `H` on the supported rings
`adm`: the ring is supported, `i` is a position of it, `σ` verifies on the base message
`bmsg R m` under the key at `i`, and its public value under that key is `y`. -/
structure RingRel {T : Signature.SchemeTypes} {RMsg : Type} (B : BaseSigner X Y N T RMsg)
    (adm : KeyRing B.PK N → Prop) (H : X → Y)
    (x : RingStmt B) (w : RingWit B) : Prop where
  /-- The ring is supported. -/
  supported : adm x.ring
  /-- The position is in the ring. -/
  idx_lt : w.idx < x.ring.keys.length
  /-- The base signature verifies under the key at the position. -/
  verify_eq : B.bverify H (x.ring.keys[w.idx]'idx_lt) (B.bmsg x.ring x.msg) w.sig = true
  /-- Its public value is the statement's. -/
  pub_eq : (B.pub (x.ring.keys[w.idx]'idx_lt) w.sig).run H = x.pub

/-- **A decided test of the statements of the empty ring** at the statement map `stmt`: `isNil`
accepts the statement `stmt y` of a ring statement `y` exactly when the ring of `y` is empty. -/
structure EmptyRingTest {T : Signature.SchemeTypes} {RMsg : Type} {B : BaseSigner X Y N T RMsg}
    {X₀ : Type} (stmt : RingStmt B → X₀) where
  /-- The test. -/
  isNil : X₀ → Bool
  /-- It accepts the statements of the empty ring, and only those among the statements. -/
  isNil_stmt_iff : ∀ y : RingStmt B, isNil (stmt y) = true ↔ y.ring.IsEmpty

/-- **The ring statements themselves have the emptiness of their ring as the test.** -/
def EmptyRingTest.self {T : Signature.SchemeTypes} {RMsg : Type}
    {B : BaseSigner X Y N T RMsg} : EmptyRingTest (B := B) id where
  isNil y := y.ring.keys.isEmpty
  isNil_stmt_iff y := List.isEmpty_iff

/-- **The ring relation is decided** on decided supported rings: the support, the position, the
base verification and the public value are each decided. -/
instance RingRel.instDecidable {T : Signature.SchemeTypes} {RMsg : Type}
    (B : BaseSigner X Y N T RMsg) (adm : KeyRing B.PK N → Prop)
    [DecidablePred adm] [DecidableEq T.Pub] (H : X → Y) (x : RingStmt B) (w : RingWit B) :
    Decidable (RingRel B adm H x w) :=
  decidable_of_iff (adm x.ring ∧ ∃ h : w.idx < x.ring.keys.length,
      B.bverify H (x.ring.keys[w.idx]'h) (B.bmsg x.ring x.msg) w.sig = true ∧
        (B.pub (x.ring.keys[w.idx]'h) w.sig).run H = x.pub)
    ⟨fun ⟨ha, hi, hv, hp⟩ => ⟨ha, hi, hv, hp⟩,
      fun h => ⟨h.supported, h.idx_lt, h.verify_eq, h.pub_eq⟩⟩

/-- **The ring relation as a set** of statement-witness pairs. -/
@[expose] def ringRel {T : Signature.SchemeTypes} {RMsg : Type} (B : BaseSigner X Y N T RMsg)
    (adm : KeyRing B.PK N → Prop) (H : X → Y) :
    Set (RingStmt B × RingWit B) :=
  {p | RingRel B adm H p.1 p.2}

/-- **The ring relation on fewer supported rings is smaller.** -/
theorem ringRel_mono {T : Signature.SchemeTypes} {RMsg : Type} (B : BaseSigner X Y N T RMsg)
    {adm adm' : KeyRing B.PK N → Prop}
    (h : ∀ R, adm' R → adm R) (H : X → Y) : ringRel B adm' H ⊆ ringRel B adm H :=
  fun _ hp => ⟨h _ hp.supported, hp.idx_lt, hp.verify_eq, hp.pub_eq⟩

/-- **The ring relation at every oracle**: the pairs in `ringRel B adm H` for every oracle `H`. -/
@[expose] def ringRelAll {T : Signature.SchemeTypes} {RMsg : Type} (B : BaseSigner X Y N T RMsg)
    (adm : KeyRing B.PK N → Prop) :
    Set (RingStmt B × RingWit B) :=
  {p | ∀ H, p ∈ ringRel B adm H}

/-- **A pair of `ringRelAll B adm` is in the ring relation at every oracle**: the condition `hrel`
of the generic unforgeability theorems (`insiderForgeProb_le_of_knowledgeBound`) holds at the
relation `ringRelAll B adm`. -/
theorem ringRel_of_mem_ringRelAll {T : Signature.SchemeTypes} {RMsg : Type}
    {B : BaseSigner X Y N T RMsg}
    {adm : KeyRing B.PK N → Prop} :
    ∀ x w, (x, w) ∈ ringRelAll B adm → ∀ H, RingRel B adm H x w :=
  fun _ _ h H => h H

/-- **The types of a proof system**: proofs and the prover's coins. A `ProofSystem` takes its
types as this parameter. The record holds types only: the finiteness and decidable equality the
games read are instance-implicit binders on its projections (`[Fintype TP.Coins]`), found by
instance search on the named types of a concrete record. -/
structure PSTypes where
  /-- Proofs. -/
  Proof : Type
  /-- The prover's coins. -/
  Coins : Type

/-- **A non-interactive proof system** with the random oracle `X → Y` and the types `T`: proofs,
uniform prover coins, the honest prover (a classical oracle program with at most `q` queries) and
the verifier at the oracle. The relation it is sound for is a property, not data. -/
structure ProofSystem (X Y Stmt Wit : Type) (T : PSTypes) where
  /-- The bound on the prover's queries. -/
  q : ℕ
  /-- The honest prover. -/
  prove : Stmt → Wit → T.Coins → OracleProg X Y T.Proof
  /-- It makes at most `q` queries. -/
  prove_queries : ∀ x w c, (prove x w c).QueriesLE q
  /-- The verifier at an oracle. -/
  verify : (X → Y) → Stmt → T.Proof → Bool

namespace ProofSystem

variable {Stmt Wit : Type} {T : PSTypes}

/-- Proofs: those of the types `T`. -/
abbrev Proof (_ : ProofSystem X Y Stmt Wit T) : Type := T.Proof

/-- The prover's coins: those of the types `T`. -/
abbrev Coins (_ : ProofSystem X Y Stmt Wit T) : Type := T.Coins

/-- **The honest prover as a `NARG.Prover`**. Its coins are uniform: the probability semantics
that read them take `PMF.uniformOfFintype PS.Coins`. -/
@[expose] def prover (PS : ProofSystem X Y Stmt Wit T) :
    NARG.Prover X Y Stmt Wit PS.Proof PS.Coins where
  prog := PS.prove
  q := PS.q
  prog_queries := PS.prove_queries

/-- The program of `prover` is the honest prover. -/
theorem prover_prog (PS : ProofSystem X Y Stmt Wit T) : PS.prover.prog = PS.prove :=
  rfl

/-- The query bound of `prover` is `q`. -/
theorem prover_q (PS : ProofSystem X Y Stmt Wit T) : PS.prover.q = PS.q :=
  rfl

/-- **The proof system of a `NARG.Prover`** and a verifier. Its coins are uniform; its prover is
`P` (`prover_ofProver`). -/
@[expose] def ofProver {Proof Coins : Type} (P : NARG.Prover X Y Stmt Wit Proof Coins)
    (verify : (X → Y) → Stmt → Proof → Bool) : ProofSystem X Y Stmt Wit ⟨Proof, Coins⟩ where
  q := P.q
  prove := P.prog
  prove_queries := P.prog_queries
  verify := verify

section ofProver

variable {Proof Coins : Type} (P : NARG.Prover X Y Stmt Wit Proof Coins)
  (verify : (X → Y) → Stmt → Proof → Bool)

/-- The query bound of `ofProver` is the prover's. -/
theorem ofProver_q : (ofProver P verify).q = P.q :=
  rfl

/-- The honest prover of `ofProver` is the prover's program. -/
theorem ofProver_prove : (ofProver P verify).prove = P.prog :=
  rfl

/-- The verifier of `ofProver` is `verify`. -/
theorem ofProver_verify : (ofProver P verify).verify = verify :=
  rfl

end ofProver

/-- **A prover is the prover of its proof system.** -/
theorem prover_ofProver {Proof Coins : Type} (P : NARG.Prover X Y Stmt Wit Proof Coins)
    (verify : (X → Y) → Stmt → Proof → Bool) : (ofProver P verify).prover = P :=
  rfl

end ProofSystem

/-! ### The ring scheme -/

/-- **A ring signature of `ofBase`** (BKM06 section 5): the public value `y` of the base signature
and the proof `π` of `(R, m, y)`. -/
abbrev RingSig (Pub Proof : Type) : Type := Pub × Proof

/-- The public value. -/
@[simp] abbrev RingSig.pub {Pub Proof : Type} (s : RingSig Pub Proof) : Pub := s.1

/-- The proof. -/
@[simp] abbrev RingSig.proof {Pub Proof : Type} (s : RingSig Pub Proof) : Proof := s.2

/-- **The signing coins of `ofBase`**: the base signer's and the prover's. -/
abbrev RingSignCoins (Base Prover : Type) : Type := Base × Prover

/-- The base signer's coins. -/
@[simp] abbrev RingSignCoins.base {Base Prover : Type} (c : RingSignCoins Base Prover) : Base :=
  c.1

/-- The prover's coins. -/
@[simp] abbrev RingSignCoins.prover {Base Prover : Type} (c : RingSignCoins Base Prover) :
    Prover :=
  c.2

/-- **A ring-signing request**: a ring of at most `N` keys and a ring message (`RingStmtOf`
without the public value). -/
abbrev RingMsg (PK Msg : Type) (N : ℕ) : Type := KeyRing PK N × Msg

/-- The ring. -/
@[simp] abbrev RingMsg.ring {PK Msg : Type} {N : ℕ} (p : RingMsg PK Msg N) : KeyRing PK N := p.1

/-- The ring message. -/
@[simp] abbrev RingMsg.msg {PK Msg : Type} {N : ℕ} (p : RingMsg PK Msg N) : Msg := p.2

/-- **A request of the combined signing oracle**: a ring-signing request (`inl`) or a base message
(`inr`). -/
abbrev RingStdMsg (PK Msg BMsg : Type) (N : ℕ) : Type := RingMsg PK Msg N ⊕ BMsg

/-- **The types of the ring scheme from a base signer and a proof system** (`ofBase`): the keys,
key-generation coins of the base signer's scheme types `T` and the ring messages `RMsg`; signatures,
a public value and a proof of `TP`; signing coins, the base signer's and the prover's. -/
abbrev ofBaseT (T : Signature.SchemeTypes) (RMsg : Type) (TP : PSTypes) : RingTypes where
  PK := T.PK
  SK := T.SK
  Msg := RMsg
  Sig := RingSig T.Pub TP.Proof
  KeyCoins := T.KeyCoins
  SignCoins := RingSignCoins T.Coins TP.Coins

variable {T : Signature.SchemeTypes} {RMsg : Type} {TP : PSTypes} (B : BaseSigner X Y N T RMsg)
  (PS : ProofSystem X Y (RingStmt B) (RingWit B) TP)

/-- **Signing at a position**: the base signature `σ` of the secret key `sk` at position `i` of
`R` on `m` (refusing if `bsign` refuses), its public value `y` under `pk`, and the proof of `(R, m, y)`
with the witness `(i, σ)`; the ring signature is `(y, π)`. -/
@[expose] def signAt (pk : B.PK) (sk : B.SK) (R : KeyRing B.PK N) (i : ℕ) (m : B.Msg)
    (c : RingSignCoins B.Coins PS.Coins) : OracleProg X Y (Option (RingSig B.Pub PS.Proof)) :=
  (B.bsign sk R i m c.base).bind fun
    | none => .pure none
    | some σ => (B.pub pk σ).bind fun y =>
        (PS.prove ⟨R, m, y⟩ ⟨i, σ⟩ c.prover).mapOutput fun π => some (y, π)

/-- Signing at a position makes at most `q + (qPub + PS.q)` queries. -/
theorem signAt_queries (pk : B.PK) (sk : B.SK) (R : KeyRing B.PK N) (i : ℕ) (m : B.Msg)
    (c : RingSignCoins B.Coins PS.Coins) :
    (signAt B PS pk sk R i m c).QueriesLE (B.q + (B.qPub + PS.q)) := by
  refine (B.bsign_queries sk R i m c.base).bind fun o => ?_
  rcases o with _ | σ
  · exact OracleProg.QueriesLE.pure _ _
  · exact (B.pub_queries pk σ).bind fun y => (PS.prove_queries _ _ c.prover).mapOutput _

/-- `signAt`, unfolded. -/
theorem signAt_eq (pk : B.PK) (sk : B.SK) (R : KeyRing B.PK N) (i : ℕ) (m : B.Msg)
    (c : RingSignCoins B.Coins PS.Coins) :
    signAt B PS pk sk R i m c = (B.bsign sk R i m c.base).bind fun
      | none => .pure none
      | some σ => (B.pub pk σ).bind fun y =>
          (PS.prove ⟨R, m, y⟩ ⟨i, σ⟩ c.prover).mapOutput fun π => some (y, π) :=
  rfl

variable [DecidableEq T.PK]

/-- **The ring signature from a base signer and a proof system** on the supported rings `adm`:
public keys, secret keys, key generation and ring messages of the base signer; signatures
`(y, π)`; signing coins those of the base signer and of the prover. Signing by the key pair
`(pk, sk)` finds the first position `i` of `pk` in the ring, refuses (`none`) when `pk` is not in
the ring or the ring is not supported, and otherwise is `signAt` at `i`. Verification is `PS`'s
verifier on `(R, m, y)`. -/
@[expose] def ofBase (adm : KeyRing B.PK N → Prop) [DecidablePred adm] :
    RingScheme X Y N (ofBaseT T RMsg TP) where
  keyGen := B.keyGen
  q := B.q + (B.qPub + PS.q)
  sign kp R m c :=
    if R.keys.idxOf kp.pk < R.keys.length ∧ adm R then
      signAt B PS kp.pk kp.sk R (R.keys.idxOf kp.pk) m c
    else .pure none
  sign_queries kp R m c := by
    split_ifs
    · exact signAt_queries B PS _ _ _ _ _ _
    · exact OracleProg.QueriesLE.pure _ _
  verify H R m s := PS.verify H ⟨R, m, RingSig.pub s⟩ (RingSig.proof s)
  Supported := adm

variable (adm : KeyRing B.PK N → Prop) [DecidablePred adm]

/-- Key generation of `ofBase` is the base signer's. -/
theorem ofBase_keyGen : (ofBase B PS adm).keyGen = B.keyGen :=
  rfl

/-- The query bound of `ofBase`. -/
theorem ofBase_q : (ofBase B PS adm).q = B.q + (B.qPub + PS.q) :=
  rfl

/-- **Signing of `ofBase`**: `signAt` at the first position of the key on a supported ring
holding it, refusal otherwise. -/
theorem ofBase_sign (kp : KeyPair B.PK B.SK) (R : KeyRing B.PK N) (m : B.Msg)
    (c : RingSignCoins B.Coins PS.Coins) :
    (ofBase B PS adm).sign kp R m c =
      if R.keys.idxOf kp.pk < R.keys.length ∧ adm R then
        signAt B PS kp.pk kp.sk R (R.keys.idxOf kp.pk) m c
      else .pure none :=
  rfl

/-- The supported rings of `ofBase` are `adm`. -/
theorem ofBase_supported : (ofBase B PS adm).Supported = adm :=
  rfl

/-- Verification of `ofBase` is the proof system's verifier on `(R, m, y)`. -/
theorem verify_ofBase (H : X → Y) (R : KeyRing B.PK N) (m : B.Msg) (s : RingSig B.Pub PS.Proof) :
    (ofBase B PS adm).verify H R m s = PS.verify H ⟨R, m, s.pub⟩ s.proof :=
  rfl

/-- **The signer of `ofBase` refuses outside its rings.** -/
theorem ofBase_refusesOutside : (ofBase B PS adm).RefusesOutside := by
  refine (RingScheme.refusesOutside_iff _).2 fun kp R m c H h => ?_
  simp only [ofBase]
  split_ifs with hc
  · rcases h with h | h
    · exact absurd (List.idxOf_lt_length_iff.1 hc.1) h
    · exact absurd hc.2 h
  · rfl

/-- **On a supported ring holding its key, the signer of `ofBase` signs at the key's first
position.** -/
theorem sign_ofBase_of_mem {kp : KeyPair B.PK B.SK} {R : KeyRing B.PK N} (hR : kp.pk ∈ R)
    (ha : adm R)
    (m : B.Msg) (c : RingSignCoins B.Coins PS.Coins) :
    (ofBase B PS adm).sign kp R m c = signAt B PS kp.pk kp.sk R (R.keys.idxOf kp.pk) m c := by
  simp only [ofBase]
  split_ifs with hc
  · rfl
  · exact absurd ⟨List.idxOf_lt_length_iff.2 hR, ha⟩ hc

omit [DecidableEq T.PK] in
/-- **An honest ring signature is the public value and the proof of the base signature**: when
`bsign` outputs `σ` at the oracle `H`, signing at the position outputs `(y, π)` with `y` the public
value of `σ` under `pk` and `π` the prover's proof of `(R, m, y)` with the witness `(i, σ)`. -/
theorem run_signAt_of_bsign {H : X → Y} {pk : B.PK} {sk : B.SK} {R : KeyRing B.PK N} {i : ℕ}
    {m : B.Msg} {c : RingSignCoins B.Coins PS.Coins} {σ : B.BSig}
    (hσ : (B.bsign sk R i m c.base).run H = some σ) :
    (signAt B PS pk sk R i m c).run H =
      some ((B.pub pk σ).run H,
        (PS.prove ⟨R, m, (B.pub pk σ).run H⟩ ⟨i, σ⟩ c.prover).run H) := by
  simp only [signAt, OracleProg.run_bind, hσ, OracleProg.run_mapOutput]

omit [DecidablePred adm] [DecidableEq T.PK] in
/-- **The relation holds on honest signatures**: a base signature `σ` of the key at position `i` of
a supported ring that verifies on `bmsg R m` is a witness, with `i`, of the statement `(R, m, y)`
whose public value `y` is that of `σ`. The relation is satisfiable whenever the base signer outputs a
verifying signature. -/
theorem ringRel_of_bsign {H : X → Y} {R : KeyRing B.PK N} {i : ℕ} (hi : i < R.keys.length)
    {m : B.Msg} {σ : B.BSig} (ha : adm R)
    (hv : B.bverify H (R.keys[i]'hi) (B.bmsg R m) σ = true) :
    (⟨R, m, (B.pub (R.keys[i]'hi) σ).run H⟩, ⟨i, σ⟩) ∈ ringRel B adm H :=
  ⟨ha, hi, hv, rfl⟩

end GordieHowe.RingSignature
