-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Applications.Ring.KeyFreeMain
public import GordieHowe.Applications.Ring.RingInsider
public import GordieHowe.Model.Quantum.Interactive.AssignRelayOuter

@[expose] public section

/-!
# The relay of the key-free unforgeability route

The relay of the key-free route (`GordieHowe/Applications/Ring/KeyFreeMain.lean`): the requests of
the insider unforgeability game of `ofBase B PS adm` answered by a classical program that reads
the oracle in force, assigns, and makes exactly one request to the main challenger (an
`AssignRelay`, `GordieHowe/Model/Quantum/Interactive/AssignRelay.lean`). It is generic in a
key-free signer `ksign` (public key, ring, request number, message and side coins, returning a
public value, a base signature and an assignment list) and in a statement program `stmtP`. The
route ends in MU-EUF-NMA^corr; this is not a strong-unforgeability relay.

Request number `c`:
- `corrupt i`: the main request `inl (corrupt i)`, the key coins of its reply, no assignments;
- `sign s R m` with `pks s ∈ R` and `adm R`, below `Q`: `ksign (pks s) R c m (sc c)` reading the
  oracle; on `none` the dummy request `inr (dummyR (r, c))` and no reply; on `some (y, σ, asg)`,
  `stmtP ⟨R, m, y⟩` reading the oracle reprogrammed by `asg` (the program's own assignments are
  not yet in force: the bookkeeping `readL (lastAssign asg)`), then the main request
  `inr (toR x₀ (r, c) σ)`, the reply `signature (y, π)` from the main proof `π`, and the assignments
  `asg`;
- otherwise the dummy request and no reply.

- `readL`, `askM`, `trace_readL`, `run_readL`: reading the oracle through a table, one main
  request.
- `sigP`, `asgOf`, `xP`, `reqOf`, `replyOf`, `kfProg`, `run_kfProg`, `trace_kfProg`: the program
  and its run. `reqOf_inr_tag`, `mem_trace_kfProg_tag`: the proof queries carry `(r, c)`.
  `run_xP_sign`: the statement program runs at the oracle reprogrammed by `asg`.
- `KFReads`, `KFReads.real`, `KFReads.viaSide`, `KFReads.lift`, `fullOnly`, `sigK`, `xK`,
  `kfProgK`, `kfRelayOn` (**one key-free relay over base reads**): the program over full reads and
  base reads, its base reads realized as oracle reads (real-query mode) or as side reads of a side
  function (side-read mode). `elimSide_kfProgK_real`: in real-query mode, of programs reading only
  the oracle, it is `kfProg`. `kfProgK_noSideAfterAsk`: it makes no side read after its main
  request.
- `kfRelay`, `kfRelay_isPlain`: the relay in real-query mode (`reads_le` with `qG = qk + qs`, `asks_eq_one`); its
  program ignores the table.
- `kfRelay_safeAssign`: assignments keeping a view `f` of the oracle are safe, for a main
  challenger whose replies do not see reprogramming that keeps `f`.
- `kfGame_keepsView`: the outer challenger keeps a view of the oracle kept by the safe
  assignments.
- `kfGame`, `kfGame_run_eq`, `kfGame_relaysChallenger`: the outer challenger answering by the
  relay's programs against a main challenger that reads its history only through its length below
  the cap (`ReadsLength`), and its relay condition (`AssignRelay.RelaysChallenger`).
- `muChallenger_none_respond_eq`, `kfMain_readsLength`, `kfMainSim_readsLength`: the main
  challengers read their history only through its length below the cap.
- `reqOf_inr_rel`, `stmt_ne_of_freshAt`: the freshness discharge; an in-relation proof query comes
  from a signing request with that ring and message, so it differs from a claim for a fresh ring
  and message.
- `KFEncoding`: the well-formed main-request encoding (dummy and idle requests have dummy
  statements, idle is not a corruption, the statement program's outputs read back its input and
  are carried by `toR`).
-/

namespace GordieHowe

open Quantum Signature QROM OracleProg

namespace RingSignature.KeyFree

open RingSignature.Insider

variable {X Y : Type} [DecidableEq X] [Zero Y] {Req' Resp' : Type}

/-! ### Reading the oracle through a table, and one main request -/

/-- **A program reading the oracle through the table `T`**, as a relay program: each query `x` is
the oracle read `inl x`, answered by `T x` if it has an entry. -/
def readL {α : Type} (T : X → Option Y) (p : OracleProg X Y α) :
    OracleProg (X ⊕ Req') (Y ⊕ Option Resp') α :=
  translate Sum.inl (fun x b => (T x).getD (b.elim id fun _ => 0)) p

/-- **One main request** `r'`, returning the main reply. -/
def askM (r' : Req') : OracleProg (X ⊕ Req') (Y ⊕ Option Resp') (Option Resp') :=
  .query (.inr r') fun b => .pure (b.elim (fun _ => none) id)

omit [DecidableEq X] in
theorem trace_readL {α : Type} (T : X → Option Y) (p : OracleProg X Y α) (h : X → Y)
    (m : Req' → Option Resp') :
    (readL (Req' := Req') (Resp' := Resp') T p).trace (combineAns h m) =
      (p.trace (reprogT T h)).map Sum.inl := by
  rw [readL, trace_translate]
  rfl

omit [DecidableEq X] in
theorem run_readL {α : Type} (T : X → Option Y) (p : OracleProg X Y α) (h : X → Y)
    (m : Req' → Option Resp') :
    (readL (Req' := Req') (Resp' := Resp') T p).run (combineAns h m) = p.run (reprogT T h) := by
  rw [readL, run_translate]
  rfl

variable {N n : ℕ} {TB : BaseTypes} [DecidableEq TB.PK]
  (B : BaseSigner X Y N TB) {Pf PC : Type} [Fintype Pf] [DecidableEq Pf]
  [Fintype PC]
  [DecidableEq PC] [Nonempty PC]
  {PS : ProofSystem X Y (RingStmt B) (RingWit B) ⟨Pf, PC⟩}
  {adm : KeyRing B.PK N → Prop} [DecidablePred adm] {SC X₀ R : Type}
  (pks : Fin n → B.PK)
  (ksign : B.PK → KeyRing B.PK N → ℕ → B.Msg → SC →
    OracleProg X Y (Option (B.Pub × B.BSig × List (Assignment X Y))))
  (stmtP : RingStmt B → OracleProg X Y X₀) (toR : X₀ → Req B PS adm n × ℕ → B.BSig → R)
  (dummyR : Req B PS adm n × ℕ → R) {Q : ℕ} (sc : Fin Q → SC)

/-! ### The program -/

open Classical in
/-- **The key-free signature of request number `c`**: `ksign` for a signing request by a member of
a supported ring below `Q`, `none` otherwise. -/
noncomputable def sigP (c : ℕ) :
    Req B PS adm n → OracleProg X Y (Option (B.Pub × B.BSig × List (Assignment X Y)))
  | .sign s Rg m =>
    if h : c < Q ∧ pks s ∈ Rg.1 ∧ adm Rg then ksign (pks s) Rg c m (sc ⟨c, h.1⟩) else .pure none
  | _ => .pure none

/-- The assignments of a key-free signature. -/
def asgOf (o : Option (B.Pub × B.BSig × List (Assignment X Y))) : List (Assignment X Y) :=
  o.elim [] fun p => p.2.2

/-- **The statement program of a signed request**: `stmtP ⟨R, m, y⟩` for a signing request with
a signature, nothing otherwise. -/
def xP : Req B PS adm n → Option (B.Pub × B.BSig × List (Assignment X Y)) →
    OracleProg X Y (Option X₀)
  | .sign _ Rg m, some p => (stmtP ⟨Rg, m, p.1⟩).mapOutput some
  | _, _ => .pure none

/-- **The main request of request number `c`**: the corruption itself, the proof query
`toR x₀ (r, c) σ` of a signed request, the dummy request `dummyR (r, c)` otherwise; the proof
queries carry the request number `c`. -/
def reqOf (c : ℕ) : (r : Req B PS adm n) → Option (B.Pub × B.BSig × List (Assignment X Y)) →
    Option X₀ → MURequest (SignOracle.none B.core) n ⊕ R
  | .corrupt i, _, _ => .inl (.corrupt i)
  | r, some p, some x₀ => .inr (toR x₀ (r, c) p.2.1)
  | r, _, _ => .inr (dummyR (r, c))

/-- **The outer reply**: the key coins of a corruption's main reply; for a signed request, the
signature `(y, π)` from the main proof `π` and the assignments; nothing otherwise. -/
def replyOf : Req B PS adm n → Option (B.Pub × B.BSig × List (Assignment X Y)) →
    Option (MUResponse B.core ⊕ Pf) → Reply X Y (Resp B PS adm)
  | .corrupt _, _, some (.inl (.keyCoins kc)) => ⟨some (.keyCoins kc), []⟩
  | .sign _ _ _, some p, a =>
    ⟨(a.bind Sum.getRight?).map fun π => .signature ((p.1, π) : B.Pub × Pf), p.2.2⟩
  | _, _, _ => ⟨none, []⟩

/-- **The relay program of request number `c`** (module docstring). -/
noncomputable def kfProg (c : ℕ) (r : Req B PS adm n) :
    OracleProg (X ⊕ (MURequest (SignOracle.none B.core) n ⊕ R))
      (Y ⊕ Option (MUResponse B.core ⊕ Pf)) (Reply X Y (Resp B PS adm)) :=
  (readL (fun _ => none) (sigP B pks ksign sc c r)).bind fun o =>
    (readL (lastAssign (asgOf B o)) (xP B stmtP r o)).bind fun x₀ =>
      (askM (reqOf B toR dummyR c r o x₀)).bind fun a => .pure (replyOf B r o a)

variable (h : X → Y) (m : MURequest (SignOracle.none B.core) n ⊕ R → Option (MUResponse B.core ⊕ Pf))

omit [Fintype Pf] [DecidableEq Pf] [Fintype PC] [DecidableEq PC] [Nonempty PC] in
/-- **The run of the relay program**: the signature at the oracle, the statement program at the
oracle reprogrammed by its assignments, the main reply to the main request. -/
theorem run_kfProg (c : ℕ) (r : Req B PS adm n) :
    (kfProg B pks ksign stmtP toR dummyR sc c r).run (combineAns h m) =
      replyOf B r ((sigP B pks ksign sc c r).run h)
        (m (reqOf B toR dummyR c r ((sigP B pks ksign sc c r).run h)
          ((xP B stmtP r ((sigP B pks ksign sc c r).run h)).run
            (h.reprogram (asgOf B ((sigP B pks ksign sc c r).run h)))))) := by
  simp only [kfProg, run_bind, run_readL, reprogT_none, ← reprogram_eq_reprogT]
  rfl

omit [Fintype Pf] [DecidableEq Pf] [Fintype PC] [DecidableEq PC] [Nonempty PC] in
/-- **The trace of the relay program**: the reads of the signature, then of the statement
program, then the main request. -/
theorem trace_kfProg (c : ℕ) (r : Req B PS adm n) :
    (kfProg B pks ksign stmtP toR dummyR sc c r).trace (combineAns h m) =
      ((sigP B pks ksign sc c r).trace h).map Sum.inl ++
        (((xP B stmtP r ((sigP B pks ksign sc c r).run h)).trace
          (h.reprogram (asgOf B ((sigP B pks ksign sc c r).run h)))).map Sum.inl ++
        [.inr (reqOf B toR dummyR c r ((sigP B pks ksign sc c r).run h)
          ((xP B stmtP r ((sigP B pks ksign sc c r).run h)).run
            (h.reprogram (asgOf B ((sigP B pks ksign sc c r).run h)))))]) := by
  simp only [kfProg, trace_bind, trace_readL, run_readL, reprogT_none,
    ← reprogram_eq_reprogT]
  rfl

omit [DecidableEq X] [Zero Y]
  [Fintype Pf] [DecidableEq Pf] [Fintype PC] [DecidableEq PC] [Nonempty PC] in
/-- **The proof query of request number `c` carries `(r, c)`**: it is `toR x₀ (r, c) σ` or
`dummyR (r, c)`. -/
theorem reqOf_inr_tag (c : ℕ) (r : Req B PS adm n)
    (o : Option (B.Pub × B.BSig × List (Assignment X Y))) (x : Option X₀) (q : R)
    (hq : reqOf B toR dummyR c r o x = .inr q) :
    (∃ x₀ σ, q = toR x₀ (r, c) σ) ∨ q = dummyR (r, c) := by
  rcases r with i | ⟨s, Rg, msg⟩ | ⟨i, bm⟩ <;> rcases o with _ | p <;> rcases x with _ | x₀ <;>
    simp only [reqOf, Sum.inr.injEq, reduceCtorEq] at hq <;> subst hq <;>
    first | exact .inl ⟨_, _, rfl⟩ | exact .inr rfl

omit [Fintype Pf] [DecidableEq Pf] [Fintype PC] [DecidableEq PC] [Nonempty PC] in
/-- **Every proof query the relay program of request number `c` makes carries `(r, c)`.** -/
theorem mem_trace_kfProg_tag (c : ℕ) (r : Req B PS adm n) (q : R)
    (hq : .inr (.inr q) ∈ (kfProg B pks ksign stmtP toR dummyR sc c r).trace (combineAns h m)) :
    (∃ x₀ σ, q = toR x₀ (r, c) σ) ∨ q = dummyR (r, c) := by
  rw [trace_kfProg] at hq
  simp only [List.mem_append, List.mem_map, reduceCtorEq, and_false, exists_false,
    List.mem_singleton, Sum.inr.injEq, false_or] at hq
  exact reqOf_inr_tag B toR dummyR c r _ _ q hq.symm

omit [Fintype Pf] [DecidableEq Pf] [Fintype PC] [DecidableEq PC] [Nonempty PC] in
/-- **The bookkeeping**: for a signed request, the statement program reads the oracle
reprogrammed by the signature's assignments, so it runs as `stmtP` at `h.reprogram asg`. -/
theorem run_xP_sign (s : Fin n) (Rg : KeyRing B.PK N) (msg : B.Msg) (y : B.Pub) (σ : B.BSig)
    (asg : List (Assignment X Y)) :
    (readL (Req' := MURequest (SignOracle.none B.core) n ⊕ R) (Resp' := MUResponse B.core ⊕ Pf)
        (lastAssign asg)
        (xP B (PS := PS) (adm := adm) stmtP (.sign s Rg msg) (some (y, σ, asg)))).run
        (combineAns h m) =
      some ((stmtP ⟨Rg, msg, y⟩).run (h.reprogram asg)) := by
  rw [run_readL, ← reprogram_eq_reprogT]
  simp [xP, run_mapOutput]

/-! ### The relay program over base reads -/

/-- **How a relay realizes the base reads** of a program over full reads `inl x` and base reads
`inr x` (answers `Y ⊕ Yb`): the base view `π` of an oracle answer; the relay read `pt x` of a base
read at `x`, an oracle read or a side read; the base view `ans x` of its answer; whether the base
reads read the table in force themselves (`viaTab`: a side read is not patched by the table in
force); and the side function. -/
structure KFReads (X Y Yb Xs Ys : Type) where
  /-- The base view of an oracle answer. -/
  π : Y → Yb
  /-- The relay read of a base read. -/
  pt : X → X ⊕ Xs
  /-- The base view of the answer to that read. -/
  ans : X → Y ⊕ Ys → Yb
  /-- Whether the base reads read the table in force themselves. -/
  viaTab : Bool
  /-- The side function. -/
  side : Xs → Ys

/-- **Base reads as oracle reads** (real-query mode): a base read at `x` reads the oracle at `x`
and takes the base view `π` of the answer. -/
def KFReads.real {Yb : Type} (π : Y → Yb) : KFReads X Y Yb Empty Unit where
  π := π
  pt := Sum.inl
  ans _ b := π (b.elim id fun _ => 0)
  viaTab := false
  side x := nomatch x

/-- **Base reads as side reads** of the side function `s` (side-read mode): a base read at `x` is
the side read at `x`, answered by `s x`, read through the table in force by `π`. -/
def KFReads.viaSide {Yb : Type} (π : Y → Yb) (s : X → Yb) : KFReads X Y Yb X Yb where
  π := π
  pt := Sum.inr
  ans _ b := b.elim π id
  viaTab := true
  side := s

section Reads

variable {Yb Xs Ys : Type} (Rd : KFReads X Y Yb Xs Ys)

/-- **The answer to a read** of a program over full and base reads, through the table `Tf` for
the full reads and `Tb` for the base reads. -/
def KFReads.readAns (Tf Tb : X → Option Y) : X ⊕ X → (Y ⊕ Ys) ⊕ Option Resp' → Y ⊕ Yb
  | .inl x, b => .inl ((Tf x).getD (b.elim (fun c => c.elim id fun _ => 0) fun _ => 0))
  | .inr x, b => .inr (((Tb x).map Rd.π).getD (Rd.ans x (b.elim id fun _ => .inl 0)))

/-- **A program over full and base reads as a relay program**: a full read at `x` is the oracle
read at `x`, read through `Tf`; a base read is the relay read `Rd.pt x`, read through `Tb`. -/
def KFReads.lift (Tf Tb : X → Option Y) {α : Type} (p : OracleProg (X ⊕ X) (Y ⊕ Yb) α) :
    OracleProg ((X ⊕ Xs) ⊕ Req') ((Y ⊕ Ys) ⊕ Option Resp') α :=
  translate (fun a => .inl (a.elim Sum.inl Rd.pt)) (Rd.readAns (Resp' := Resp') Tf Tb) p

/-- The tables the base reads read through: the full reads' table, overridden by the table in
force `T` when the base reads read it themselves. -/
def KFReads.tabB (T L : X → Option Y) : X → Option Y :=
  if Rd.viaTab then overT T L else L

end Reads

/-- **A program reading only the oracle** as a program over full and base reads. -/
def fullOnly {Yb α : Type} (p : OracleProg X Y α) : OracleProg (X ⊕ X) (Y ⊕ Yb) α :=
  translate Sum.inl (fun _ b => b.elim id fun _ => 0) p

variable {Yb Xs Ys : Type}

open Classical in
/-- **The key-free signature over base reads** of request number `c`: `sgn` for a signing request
by a member of a supported ring below `Q`, `none` otherwise. -/
noncomputable def sigK
    (sgn : B.PK → KeyRing B.PK N → ℕ → B.Msg → SC →
      OracleProg (X ⊕ X) (Y ⊕ Yb) (Option (B.Pub × B.BSig × List (Assignment X Y)))) (c : ℕ) :
    Req B PS adm n → OracleProg (X ⊕ X) (Y ⊕ Yb) (Option (B.Pub × B.BSig × List (Assignment X Y)))
  | .sign s Rg m =>
    if h : c < Q ∧ pks s ∈ Rg.1 ∧ adm Rg then sgn (pks s) Rg c m (sc ⟨c, h.1⟩) else .pure none
  | _ => .pure none

/-- **The statement program over base reads of a signed request**: `stp ⟨R, m, y⟩` for a signing
request with a signature, nothing otherwise. -/
def xK (stp : RingStmt B → OracleProg (X ⊕ X) (Y ⊕ Yb) X₀) :
    Req B PS adm n → Option (B.Pub × B.BSig × List (Assignment X Y)) →
    OracleProg (X ⊕ X) (Y ⊕ Yb) (Option X₀)
  | .sign _ Rg m, some p => (stp ⟨Rg, m, p.1⟩).mapOutput some
  | _, _ => .pure none

/-- **The key-free relay program over base reads** of request number `c`, given the table in
force `T`, with the base reads realized by `Rd`: the signature `sigK`, the statement `xK` reading
the oracle reprogrammed by the signature's assignments, the main request, the outer reply. -/
noncomputable def kfProgK
    (sgn : B.PK → KeyRing B.PK N → ℕ → B.Msg → SC →
      OracleProg (X ⊕ X) (Y ⊕ Yb) (Option (B.Pub × B.BSig × List (Assignment X Y))))
    (stp : RingStmt B → OracleProg (X ⊕ X) (Y ⊕ Yb) X₀) (Rd : KFReads X Y Yb Xs Ys) (T : X → Option Y) (c : ℕ)
    (r : Req B PS adm n) :
    OracleProg ((X ⊕ Xs) ⊕ (MURequest (SignOracle.none B.core) n ⊕ R))
      ((Y ⊕ Ys) ⊕ Option (MUResponse B.core ⊕ Pf)) (Reply X Y (Resp B PS adm)) :=
  (Rd.lift (fun _ => none) (Rd.tabB T fun _ => none) (sigK B pks sc sgn c r)).bind fun o =>
    (Rd.lift (lastAssign (asgOf B o)) (Rd.tabB T (lastAssign (asgOf B o))) (xK B stp r o)).bind
      fun x₀ => (OracleProg.query (.inr (reqOf B toR dummyR c r o x₀)) fun b =>
        .pure (b.elim (fun _ => none) id)).bind fun a => .pure (replyOf B r o a)

omit [Fintype Pf] [DecidableEq Pf] [Fintype PC] [DecidableEq PC] [Nonempty PC] in
/-- **The key-free relay program makes no side read after its main request**: its reads come
before its one main request, and its reply follows it. -/
theorem kfProgK_noSideAfterAsk
    (sgn : B.PK → KeyRing B.PK N → ℕ → B.Msg → SC →
      OracleProg (X ⊕ X) (Y ⊕ Yb) (Option (B.Pub × B.BSig × List (Assignment X Y))))
    (stp : RingStmt B → OracleProg (X ⊕ X) (Y ⊕ Yb) X₀) (Rd : KFReads X Y Yb Xs Ys)
    (T : X → Option Y) (c : ℕ) (r : Req B PS adm n) :
    (kfProgK B pks toR dummyR sc sgn stp Rd T c r).NoSideAfterAsk :=
  OracleProg.NoAsks.bind_noSideAfterAsk (OracleProg.noAsks_translate _ _ (fun _ => rfl) _)
    fun _ => OracleProg.NoAsks.bind_noSideAfterAsk
      (OracleProg.noAsks_translate _ _ (fun _ => rfl) _) fun _ _ => trivial

omit [Fintype Pf] [DecidableEq Pf] [Fintype PC] [DecidableEq PC] [Nonempty PC] in
/-- **Base reads as oracle reads, of programs reading only the oracle**: the relay program over
base reads in real-query mode, of the signer and the statement program reading only the oracle,
with its (absent) side reads answered, is the key-free relay program. -/
theorem elimSide_kfProgK_real (T : X → Option Y) (c : ℕ) (r : Req B PS adm n) :
    elimSide (KFReads.real (X := X) (Y := Y) (Yb := Y) id).side
        (kfProgK B pks toR dummyR sc (fun pk Rg c m s => fullOnly (ksign pk Rg c m s))
          (fun x => fullOnly (stmtP x)) (KFReads.real id) T c r) =
      kfProg B pks ksign stmtP toR dummyR sc c r := by
  have hlift : ∀ {α : Type} (Tf : X → Option Y) (p : OracleProg X Y α),
      elimSide (KFReads.real (X := X) (Y := Y) (Yb := Y) id).side
        ((KFReads.real (X := X) (Y := Y) (Yb := Y) id).lift
          (Req' := MURequest (SignOracle.none B.core) n ⊕ R) (Resp' := MUResponse B.core ⊕ Pf)
          Tf (KFReads.real (X := X) (Y := Y) (Yb := Y) id |>.tabB T Tf) (fullOnly p)) =
        readL Tf p := by
    intro α Tf p
    rw [KFReads.lift, fullOnly, translate_translate]
    refine (elimSide_translate _ _ id (fun _ => rfl) _ p).trans ?_
    rw [readL]
    refine translate_congr (fun x b => ?_) p
    rcases b with y | a <;> rfl
  have hsig : sigK B pks sc (fun pk Rg c m s => fullOnly (Yb := Y) (ksign pk Rg c m s)) c r =
      fullOnly (sigP B pks ksign sc c r) := by
    rcases r with i | ⟨s, Rg, msg⟩ | ⟨i, bm⟩
    · rfl
    · by_cases hc : c < Q ∧ pks s ∈ Rg.1 ∧ adm Rg
      · rw [sigK, sigP, dite_eq_left_of_eq_true (eq_true hc), dite_eq_left_of_eq_true (eq_true hc)]
      · rw [sigK, sigP, dite_eq_right_of_eq_false (eq_false hc),
          dite_eq_right_of_eq_false (eq_false hc)]
        rfl
    · rfl
  have hx : ∀ o, xK B (fun x => fullOnly (Yb := Y) (stmtP x)) r o = fullOnly (xP B stmtP r o) := by
    intro o
    rcases r with i | ⟨s, Rg, msg⟩ | ⟨i, bm⟩ <;> rcases o with _ | p
    all_goals try rfl
    simp only [xK, xP, fullOnly, mapOutput, translate_bind]
    rfl
  rw [kfProgK, elimSide_bind, hsig, hlift, kfProg]
  refine congrArg _ (funext fun o => ?_)
  rw [elimSide_bind, hx, hlift]
  refine congrArg _ (funext fun x₀ => ?_)
  rw [elimSide_bind, askM]
  change OracleProg.bind (OracleProg.query _ _) _ = OracleProg.bind (OracleProg.query _ _) _
  refine congrArg (fun k => OracleProg.bind (OracleProg.query _ k) _) (funext fun b => ?_)
  rcases b with y | a <;> rfl

/-! ### The relay -/

variable {qk qs : ℕ}

omit [DecidableEq X] [Zero Y]
  [Fintype Pf] [DecidableEq Pf] [Fintype PC] [DecidableEq PC] [Nonempty PC] in
theorem sigP_queriesLE (hk : ∀ pk Rg c msg s, (ksign pk Rg c msg s).QueriesLE qk) (c : ℕ)
    (r : Req B PS adm n) : (sigP B pks ksign sc c r).QueriesLE qk := by
  rcases r with i | ⟨s, Rg, msg⟩ | ⟨i, bm⟩
  · exact fun _ => by simp [sigP]
  · by_cases hc : c < Q ∧ pks s ∈ Rg.1 ∧ adm Rg
    · rw [sigP, dite_eq_left_of_eq_true (eq_true hc)]
      exact hk _ _ _ _ _
    · rw [sigP, dite_eq_right_of_eq_false (eq_false hc)]
      exact fun _ => by simp [trace]
  · exact fun _ => by simp [sigP]

omit [DecidableEq X] [Zero Y]
  [Fintype Pf] [DecidableEq Pf] [Fintype PC] [DecidableEq PC] [Nonempty PC] in
theorem xP_queriesLE (hs : ∀ x, (stmtP x).QueriesLE qs) (r : Req B PS adm n)
    (o : Option (B.Pub × B.BSig × List (Assignment X Y))) :
    (xP B stmtP r o).QueriesLE qs := by
  rcases r with i | ⟨s, Rg, msg⟩ | ⟨i, bm⟩ <;> rcases o with _ | p
  all_goals first
    | exact (hs _).mapOutput _
    | exact fun _ => by simp [xP]

/-- The base reads in side-read mode read the table in force. -/
@[simp] theorem KFReads.tabB_viaSide {Yb : Type} (π : Y → Yb) (s : X → Yb) (T L : X → Option Y) :
    (KFReads.viaSide π s).tabB T L = overT T L :=
  rfl

/-- The base reads in real-query mode read only the full reads' table. -/
@[simp] theorem KFReads.tabB_real {Yb : Type} (π : Y → Yb) (T L : X → Option Y) :
    (KFReads.real π).tabB T L = L :=
  rfl

/-- **The answers to the reads of a program over full and base reads in side-read mode**: a full
read at `x` the oracle `h` through `Tf`, a base read the side function `s` through `Tb`. -/
def viaSideAns {Yb : Type} (π : Y → Yb) (s : X → Yb) (h : X → Y) (Tf Tb : X → Option Y) :
    X ⊕ X → Y ⊕ Yb :=
  fun a => a.elim (fun x => .inl ((Tf x).getD (h x))) fun x => .inr (((Tb x).map π).getD (s x))

/-- **A program over full and base reads in side-read mode runs** against the oracle and the side
function answering its full and base reads. -/
theorem run_lift_viaSide {Yb α : Type} (π : Y → Yb) (s : X → Yb) (Tf Tb : X → Option Y)
    (p : OracleProg (X ⊕ X) (Y ⊕ Yb) α) (h : X → Y) (m : Req' → Option Resp') :
    ((KFReads.viaSide π s).lift Tf Tb p).run
        (combineAns (MultiRelay.sideOracle h (KFReads.viaSide π s).side) m) =
      p.run (viaSideAns π s h Tf Tb) := by
  rw [KFReads.lift, run_translate]
  congr 1
  funext a
  rcases a with x | x <;> rfl

/-- **The reads of a program over full and base reads in side-read mode**: its full reads as
oracle reads, its base reads as side reads. -/
theorem trace_lift_viaSide {Yb α : Type} (π : Y → Yb) (s : X → Yb) (Tf Tb : X → Option Y)
    (p : OracleProg (X ⊕ X) (Y ⊕ Yb) α) (h : X → Y) (m : Req' → Option Resp') :
    ((KFReads.viaSide π s).lift Tf Tb p).trace
        (combineAns (MultiRelay.sideOracle h (KFReads.viaSide π s).side) m) =
      (p.trace (viaSideAns π s h Tf Tb)).map Sum.inl := by
  rw [KFReads.lift, trace_translate]
  have : (fun a : X ⊕ X => (Sum.inl (a.elim Sum.inl (KFReads.viaSide π s).pt) :
      (X ⊕ X) ⊕ Req')) = Sum.inl := funext fun a => by rcases a with x | x <;> rfl
  rw [this]
  congr 1
  congr 1
  funext a
  rcases a with x | x <;> rfl

omit [DecidableEq X] [Zero Y] in
/-- The oracle reads of a program's reads as relay reads in side-read mode: its full reads. -/
theorem length_filter_isRead_map_viaSide {Xs' : Type} (l : List (X ⊕ X)) :
    ((l.map (Sum.inl : X ⊕ X → (X ⊕ X) ⊕ Xs')).filter isRead).length =
      (l.filter Sum.isLeft).length := by
  induction l with
  | nil => rfl
  | cons a l ih => rcases a with x | x <;> simp [List.filter_cons, isRead, ih]

omit [DecidableEq X] [Zero Y] in
/-- The side reads of a program's reads as relay reads in side-read mode: its base reads. -/
theorem length_filter_isSideRead_map_viaSide {Xs' : Type} (l : List (X ⊕ X)) :
    ((l.map (Sum.inl : X ⊕ X → (X ⊕ X) ⊕ Xs')).filter isSideRead).length =
      (l.filter Sum.isRight).length := by
  induction l with
  | nil => rfl
  | cons a l ih => rcases a with x | x <;> simp [List.filter_cons, isSideRead, ih]

/-- **The trace of a program over full and base reads as a relay program**: its reads, as relay
reads. -/
theorem trace_lift {Yb Xs Ys α : Type} (Rd : KFReads X Y Yb Xs Ys) (Tf Tb : X → Option Y)
    (p : OracleProg (X ⊕ X) (Y ⊕ Yb) α) (o : (X ⊕ Xs) ⊕ Req' → (Y ⊕ Ys) ⊕ Option Resp') :
    ((Rd.lift Tf Tb p).trace o).filterMap Sum.getRight? = [] := by
  rw [KFReads.lift, trace_translate]
  induction (p.trace _) with
  | nil => rfl
  | cons a l ih => simpa [Sum.getRight?] using ih

omit [Fintype Pf] [DecidableEq Pf] [Fintype PC] [DecidableEq PC] [Nonempty PC] in
/-- **The relay program over base reads makes exactly one main request.** -/
theorem filterMap_trace_kfProgK {Yb Xs Ys : Type}
    (sgn : B.PK → KeyRing B.PK N → ℕ → B.Msg → SC →
      OracleProg (X ⊕ X) (Y ⊕ Yb) (Option (B.Pub × B.BSig × List (Assignment X Y))))
    (stp : RingStmt B → OracleProg (X ⊕ X) (Y ⊕ Yb) X₀) (Rd : KFReads X Y Yb Xs Ys)
    (T : X → Option Y) (c : ℕ) (r : Req B PS adm n)
    (o : (X ⊕ Xs) ⊕ (MURequest (SignOracle.none B.core) n ⊕ R) →
      (Y ⊕ Ys) ⊕ Option (MUResponse B.core ⊕ Pf)) :
    ((kfProgK B pks toR dummyR sc sgn stp Rd T c r).trace o).filterMap Sum.getRight? =
      [reqOf B toR dummyR c r ((Rd.lift (fun _ => none) (Rd.tabB T fun _ => none)
          (sigK B pks sc sgn c r)).run o)
        ((Rd.lift (lastAssign (asgOf B ((Rd.lift (fun _ => none) (Rd.tabB T fun _ => none)
          (sigK B pks sc sgn c r)).run o)))
          (Rd.tabB T (lastAssign (asgOf B ((Rd.lift (fun _ => none) (Rd.tabB T fun _ => none)
            (sigK B pks sc sgn c r)).run o))))
          (xK B stp r ((Rd.lift (fun _ => none) (Rd.tabB T fun _ => none)
            (sigK B pks sc sgn c r)).run o))).run o)] := by
  simp only [kfProgK, trace_bind, List.filterMap_append, trace_lift, run_bind, List.nil_append]
  rfl

/-- **The key-free relay over base reads** (module docstring): the relay program `kfProgK` of the
signer `sgn` and the statement program `stp` over full and base reads, the base reads realized by
`Rd` (`KFReads.real`: as oracle reads, `KFReads.viaSide`: as side reads), with at most `qG`
oracle reads, `qS` side reads, `qP` pad sub-slots and exactly one main request. -/
noncomputable def kfRelayOn {Yb Xs Ys : Type}
    (sgn : B.PK → KeyRing B.PK N → ℕ → B.Msg → SC →
      OracleProg (X ⊕ X) (Y ⊕ Yb) (Option (B.Pub × B.BSig × List (Assignment X Y))))
    (stp : RingStmt B → OracleProg (X ⊕ X) (Y ⊕ Yb) X₀) (Rd : KFReads X Y Yb Xs Ys)
    (qG qS qP : ℕ) (hqP : qP ≤ 1) (hspec : qP = 0 ∨ Nonempty Xs)
    (hpad : ∀ T c r, (kfProgK B pks toR dummyR sc sgn stp Rd T c r).startsSide = true → 1 ≤ qP)
    (hreads : ∀ T c r (h : X → Y) m,
      (((kfProgK B pks toR dummyR sc sgn stp Rd T c r).trace
        (combineAns (MultiRelay.sideOracle h Rd.side) m)).filter isRead).length ≤ qG)
    (hsides : ∀ T c r (h : X → Y) m,
      (((kfProgK B pks toR dummyR sc sgn stp Rd T c r).trace
        (combineAns (MultiRelay.sideOracle h Rd.side) m)).filter isSideRead).length ≤ qS)
    (idle : MURequest (SignOracle.none B.core) n ⊕ R) :
    AssignRelay X Y (Req B PS adm n) (Resp B PS adm) (MURequest (SignOracle.none B.core) n ⊕ R)
      (MUResponse B.core ⊕ Pf) Xs Ys where
  prog := kfProgK B pks toR dummyR sc sgn stp Rd
  qG := qG
  idle := idle
  side := Rd.side
  qS := qS
  qP := qP
  qP_le_one := hqP
  qP_spec := hspec
  pad_le := hpad
  reads_le := hreads
  sides_le := hsides
  asks_eq_one T c r h m := by rw [filterMap_trace_kfProgK]; rfl

omit [DecidableEq X] [Fintype Pf] [DecidableEq Pf] [DecidableEq TB.PK] in
/-- **A program over full and base reads as a relay program makes no main request.** -/
theorem asksIn_lift {Yb Xs Ys α : Type} (Rd : KFReads X Y Yb Xs Ys) (Tf Tb : X → Option Y)
    (p : OracleProg (X ⊕ X) (Y ⊕ Yb) α) (P : MURequest (SignOracle.none B.core) n ⊕ R → Prop) :
    MultiRelay.AsksIn (MUResponse B.core ⊕ Pf)
      (Rd.lift (Req' := MURequest (SignOracle.none B.core) n ⊕ R) Tf Tb p) P :=
  MultiRelay.AsksIn.translate_noMain _ (fun _ _ h => by cases h) _ p P

section Over

variable {Yb Xs Ys : Type}
  (sgn : B.PK → KeyRing B.PK N → ℕ → B.Msg → SC →
    OracleProg (X ⊕ X) (Y ⊕ Yb) (Option (B.Pub × B.BSig × List (Assignment X Y))))
  (stp : RingStmt B → OracleProg (X ⊕ X) (Y ⊕ Yb) X₀) (Rd : KFReads X Y Yb Xs Ys)

omit [Fintype PC] [DecidableEq PC] [Nonempty PC] [Fintype Pf] [DecidableEq Pf] in
/-- **Every main request of the relay program over base reads is a `reqOf` of its request.** -/
theorem asksIn_kfProgK_reqOf (T : X → Option Y) (c : ℕ) (r : Req B PS adm n) :
    MultiRelay.AsksIn (MUResponse B.core ⊕ Pf) (kfProgK B pks toR dummyR sc sgn stp Rd T c r)
      fun r' => ∃ o x, r' = reqOf B toR dummyR c r o x := by
  unfold kfProgK
  refine MultiRelay.AsksIn.bind (asksIn_lift B _ _ _ _ _) fun o => ?_
  refine MultiRelay.AsksIn.bind (asksIn_lift B _ _ _ _ _) fun x₀ => ?_
  refine MultiRelay.AsksIn.bind ?_ fun _ => MultiRelay.AsksIn.pure _ _
  refine MultiRelay.AsksIn.query (fun r' h => ?_) fun _ => MultiRelay.AsksIn.pure _ _
  cases h
  exact ⟨o, x₀, rfl⟩

omit [Fintype PC] [DecidableEq PC] [Nonempty PC] [Fintype Pf] [DecidableEq Pf] in
/-- **A main corruption of the relay program over base reads comes from a corruption.** -/
theorem asksIn_kfProgK_corrupt (T : X → Option Y) (c : ℕ) (r : Req B PS adm n) :
    MultiRelay.AsksIn (MUResponse B.core ⊕ Pf) (kfProgK B pks toR dummyR sc sgn stp Rd T c r)
      fun r' => ∀ i, r' = .inl (.corrupt i) → r = .corrupt i := by
  refine MultiRelay.AsksIn.mono (asksIn_kfProgK_reqOf B pks toR dummyR sc sgn stp Rd T c r) ?_
  rintro r' ⟨o, x, rfl⟩ i hi
  rcases r with j | ⟨s, Rg, msg⟩ | ⟨j, bm⟩
  · simp only [reqOf, Sum.inl.injEq, MURequest.corrupt.injEq] at hi
    rw [hi]
  · rcases o with _ | p <;> rcases x with _ | x <;> simp [reqOf] at hi
  · rcases o with _ | p <;> rcases x with _ | x <;> simp [reqOf] at hi

end Over

/-- **The key-free relay** at the public keys `pks` and the side coins `sc` (module docstring):
the key-free relay over base reads (`kfRelayOn`) of the signer and the statement program reading
only the oracle, in real-query mode (`KFReads.real`); at most `qk + qs` reads and exactly one main
request. -/
noncomputable def kfRelay (hk : ∀ pk Rg c msg s, (ksign pk Rg c msg s).QueriesLE qk)
    (hs : ∀ x, (stmtP x).QueriesLE qs) (idle : MURequest (SignOracle.none B.core) n ⊕ R) :
    AssignRelay X Y (Req B PS adm n) (Resp B PS adm) (MURequest (SignOracle.none B.core) n ⊕ R)
      (MUResponse B.core ⊕ Pf) :=
  kfRelayOn B pks toR dummyR sc (fun pk Rg c m s => fullOnly (ksign pk Rg c m s))
    (fun x => fullOnly (stmtP x)) (KFReads.real id) (qk + qs) 0 0 (Nat.zero_le _) (Or.inl rfl)
    (fun _ _ _ h => by rw [startsSide_of_isEmpty] at h; cases h)
    (fun T c r h m => by
      rw [← length_filter_isLeft_filterMap_dropSide, ← trace_elimSide,
        elimSide_kfProgK_real, trace_kfProg]
      have h1 := sigP_queriesLE B pks ksign sc hk c r h
      have h2 := xP_queriesLE B stmtP hs r ((sigP B pks ksign sc c r).run h)
        (h.reprogram (asgOf B ((sigP B pks ksign sc c r).run h)))
      simp only [List.filter_append, List.filter_map, List.length_append, List.length_map,
        Function.comp_def, Sum.isLeft_inl, List.filter_true, List.filter_cons, Sum.isLeft_inr,
        Bool.false_eq_true, ↓reduceIte, List.filter_nil, List.length_nil]
      omega)
    (fun T c r h m => by rw [length_filter_isSideRead_of_isEmpty]) idle

omit [Fintype Pf] [DecidableEq Pf] [Fintype PC] [DecidableEq PC] [Nonempty PC] in
/-- **The key-free relay's program, its side reads answered**, is `kfProg`. -/
@[simp] theorem elimProg_kfRelay (hk : ∀ pk Rg c msg s, (ksign pk Rg c msg s).QueriesLE qk)
    (hs : ∀ x, (stmtP x).QueriesLE qs) (idle : MURequest (SignOracle.none B.core) n ⊕ R)
    (T : X → Option Y) :
    (kfRelay B pks ksign stmtP toR dummyR sc hk hs idle).elimProg T =
      kfProg B pks ksign stmtP toR dummyR sc :=
  funext fun c => funext fun r => elimSide_kfProgK_real B pks ksign stmtP toR dummyR sc T c r

omit [Fintype Pf] [DecidableEq Pf] [Fintype PC] [DecidableEq PC] [Nonempty PC] in
/-- The key-free relay's padding main request. -/
@[simp] theorem idle_kfRelay (hk : ∀ pk Rg c msg s, (ksign pk Rg c msg s).QueriesLE qk)
    (hs : ∀ x, (stmtP x).QueriesLE qs) (idle : MURequest (SignOracle.none B.core) n ⊕ R) :
    (kfRelay B pks ksign stmtP toR dummyR sc hk hs idle).idle = idle :=
  rfl

omit [Fintype Pf] [DecidableEq Pf] [Fintype PC] [DecidableEq PC] [Nonempty PC] in
/-- **The key-free relay's program ignores the table.** -/
theorem kfRelay_isPlain (hk : ∀ pk Rg c msg s, (ksign pk Rg c msg s).QueriesLE qk)
    (hs : ∀ x, (stmtP x).QueriesLE qs) (idle : MURequest (SignOracle.none B.core) n ⊕ R) :
    (kfRelay B pks ksign stmtP toR dummyR sc hk hs idle).IsPlain := fun _ _ => rfl

/-! ### Safe assignments -/

/-- **Assignments keeping the view `f` of the oracle are safe** for the key-free relay: the
signer's assignments keep `f` of the oracle it reads (`hP`), and the main challenger's replies do
not see reprogramming that keeps `f` (`hresp`). -/
noncomputable def kfRelay_safeAssign (hk : ∀ pk Rg c msg s, (ksign pk Rg c msg s).QueriesLE qk)
    (hs : ∀ x, (stmtP x).QueriesLE qs) (idle : MURequest (SignOracle.none B.core) n ⊕ R)
    (C' : Challenger X Y (MURequest (SignOracle.none B.core) n ⊕ R) (MUResponse B.core ⊕ Pf))
    {Z : Type} (f : (X → Y) → Z)
    (hP : ∀ pk Rg c msg s H p, (ksign pk Rg c msg s).run H = some p →
      f (H.reprogram p.2.2) = f H)
    (hresp : ∀ c' hist r' (H : X → Y) (L : List (Assignment X Y)), f (H.reprogram L) = f H →
      (C'.respond c' hist r').run (H.reprogram L) = (C'.respond c' hist r').run H) :
    AssignRelay.SafeAssign C' (kfRelay B pks ksign stmtP toR dummyR sc hk hs idle) where
  Safe H L := f (H.reprogram L) = f H
  safe_nil _ := rfl
  safe_append H a b ha hb := by
    rw [QROM.reprogram_append, hb, ha]
  safe_prog _ c r h m := by
    rw [elimProg_kfRelay]
    change f (h.reprogram
      ((kfProg B pks ksign stmtP toR dummyR sc c r).run (combineAns h m)).assignments) = f h
    rw [run_kfProg]
    generalize hsig : (sigP B pks ksign sc c r).run h = o
    generalize m _ = a
    rcases r with i | ⟨s, Rg, msg⟩ | ⟨i, bm⟩
    · rcases a with _ | (_ | _ | kc) | _ <;> rfl
    · rcases o with _ | p
      · rfl
      · simp only [replyOf]
        by_cases hc : c < Q ∧ pks s ∈ Rg.1 ∧ adm Rg
        · rw [sigP, dite_eq_left_of_eq_true (eq_true hc)] at hsig
          exact hP _ _ _ _ _ _ _ hsig
        · rw [sigP, dite_eq_right_of_eq_false (eq_false hc)] at hsig
          simp [run] at hsig
    · rfl
  respond_reprogram := hresp

/-! ### The outer challenger -/

/-- **A main challenger that reads its history only through its length** below the cap
`Q`. -/
def ReadsLength (C' : Challenger X Y Req' Resp') (Q : ℕ) : Prop :=
  ∀ c' (hist hist' : List (HistoryEntry Req' Resp')) r', hist.length = hist'.length →
    hist.length < Q → C'.respond c' hist r' = C'.respond c' hist' r'

variable {Ro Rs : Type}

/-- **A placeholder history of `chalD`** of the length of an outer history: every entry
answered, with the padding main request. -/
def padHist (G : AssignRelay X Y Ro Rs Req' Resp') {Q : ℕ}
    (hist : List (HistoryEntry Ro Rs)) :
    List (HistoryEntry (Ro × Fin (Q + 1)) (AssignRelay.RespD X Y Rs Req' Resp')) :=
  hist.map fun e => ⟨(e.request, 0), some (none, fun _ => none, (G.idle, none))⟩

/-- **The outer challenger of an assigning relay** against a main challenger `C'` reading its
history only through its length: request `r` after the history `hist` runs the relay's program
of number `|hist|` with the main request answered by `C'` after a main history of length
`|hist|`, returning its response and its assignments. -/
def kfGame (C' : Challenger X Y Req' Resp') (G : AssignRelay X Y Ro Rs Req' Resp') (Q : ℕ) :
    Challenger X Y Ro Rs where
  Coins := C'.Coins
  coins := C'.coins
  Q := Q
  q := G.qG + C'.q
  respond c' hist r :=
    (AssignRelay.relayProg C' G c' (padHist G (Q := Q) hist) (fun _ => none) (fun _ => none)
      hist.length r).mapOutput Prod.fst
  respond_queries c' hist r H := by
    rw [trace_mapOutput]
    exact AssignRelay.length_trace_relayProg_le C' G c' _ _ _ _ _ H

omit [DecidableEq X] [Zero Y] in
/-- **The relay condition of `kfGame`** (`AssignRelay.RelaysChallenger.run_eq`) at main histories
whose entries are all answered, for a relay whose program ignores the table (`hG`) and a main
challenger reading its history only through its length below the cap. -/
theorem kfGame_run_eq [Fintype X] [Fintype Y] [Nonempty Y] {C' : Challenger X Y Req' Resp'}
    {G : AssignRelay X Y Ro Rs Req' Resp'} {Q : ℕ} (hG : G.IsPlain) (hC : ReadsLength C' Q)
    (c' : C'.Coins)
    (histD : List (HistoryEntry (Ro × Fin (Q + 1)) (AssignRelay.RespD X Y Rs Req' Resp')))
    (hsome : ∀ e ∈ histD, e.response.isSome) (r : Ro) (H' : X → Y) (hlen : histD.length < Q) :
    ((kfGame C' G Q).respond c' (histD.map AssignRelay.stripEntry) r).run H' =
      ⟨((AssignRelay.relayProg C' G c' histD (fun _ => none) (AssignRelay.histTab histD)
          histD.length r).run H').1.response,
        ((AssignRelay.relayProg C' G c' histD (fun _ => none) (AssignRelay.histTab histD)
          histD.length r).run H').1.assignments⟩ := by
  have hm : ∀ (l : List (HistoryEntry (Ro × Fin (Q + 1)) (AssignRelay.RespD X Y Rs Req' Resp'))),
      (∀ e ∈ l, e.response.isSome) → (AssignRelay.mainHist l).length = l.length := by
    intro l hl
    induction l with
    | nil => rfl
    | cons e l ih =>
      obtain ⟨x, hx⟩ := Option.isSome_iff_exists.1 (hl e (by simp))
      simp only [AssignRelay.mainHist, List.filterMap_cons, hx, Option.map_some,
        List.length_cons] at ih ⊢
      rw [ih fun e he => hl e (by simp [he])]
  have hpad : AssignRelay.mainHist (padHist G (Q := Q) (histD.map AssignRelay.stripEntry)) =
      (histD.map AssignRelay.stripEntry).map
        fun _ => (⟨G.idle, none⟩ : HistoryEntry Req' Resp') := by
    simp [AssignRelay.mainHist, padHist, List.filterMap_map, Function.comp_def]
  have hL : (AssignRelay.mainHist histD).length =
      (AssignRelay.mainHist (padHist G (Q := Q) (histD.map AssignRelay.stripEntry))).length := by
    rw [hpad, hm histD hsome]
    simp
  have hresp : ∀ r', C'.respond c'
      (AssignRelay.mainHist (padHist G (Q := Q) (histD.map AssignRelay.stripEntry))) r' =
      C'.respond c' (AssignRelay.mainHist histD) r' := by
    intro r'
    refine hC c' _ _ r' hL.symm ?_
    rw [← hL, hm histD hsome]
    exact hlen
  simp only [kfGame, run_mapOutput, List.length_map, AssignRelay.relayProg, hresp,
    hG.elimProg (fun _ => none) (AssignRelay.histTab histD)]

omit [Zero Y] in
/-- **`kfGame` relays the main challenger through the relay** (`AssignRelay.RelaysChallenger`) at
every coins, for a relay whose program ignores the table (`hG`) and a main challenger reading its
history only through its length below the cap. -/
theorem kfGame_relaysChallenger [Fintype X] [Fintype Y] [Nonempty Y]
    {C' : Challenger X Y Req' Resp'} {G : AssignRelay X Y Ro Rs Req' Resp'} {Q : ℕ}
    (hG : G.IsPlain) (hC : ReadsLength C' Q) (c' : C'.Coins) :
    AssignRelay.RelaysChallenger G (kfGame C' G Q) c' C' c' where
  run_eq histD r H' hlen hsome := kfGame_run_eq hG hC c' histD hsome r H' hlen

section Keeps

variable {X Y Ro Rs Req' Resp' Z : Type} [Fintype X] [DecidableEq X] [Fintype Y] [Nonempty Y]
  {C' : Challenger X Y Req' Resp'} {G : AssignRelay X Y Ro Rs Req' Resp'}

omit [Fintype X] [Fintype Y] [Nonempty Y] in
/-- **The outer challenger of an assigning relay keeps a view kept by the safe assignments**:
for safe assignments that keep `f` of the oracle they are safe at (`hf`). -/
theorem kfGame_keepsView (hS : AssignRelay.SafeAssign C' G) {f : (X → Y) → Z}
    (hf : ∀ H L, hS.Safe H L → f (H.reprogram L) = f H) (Q : ℕ) :
    (kfGame C' G Q).KeepsView f := by
  intro c hist r H
  refine hf _ _ ?_
  simp only [kfGame, run_mapOutput, AssignRelay.relayProg, run_lower,
    run_recMain_fst, reprogT_none]
  exact hS.safe_prog _ _ _ _ _

end Keeps

section ReadsLength

variable {Stmt Wit Proof Coins SC' Rq : Type} (rel : Stmt → Wit → Prop) [DecidableRel rel]
  (enc : MURequest (SignOracle.none B.core) n ⊕ Rq → ProofQuery Stmt Wit)

omit [DecidableEq X] [Zero Y] [DecidableEq TB.PK] in
/-- **The multi-user part without messages answers by fixed replies below the cap**, so it reads
its history only through its length there. -/
theorem muChallenger_none_respond_eq (keys : Fin n → B.KeyCoins) (Q : ℕ)
    (c : (muNone (X := X) (Y := Y) B keys Q).Coins)
    (hist hist' : List (HistoryEntry (MURequest (SignOracle.none B.core) n) (MUResponse B.core)))
    (r : MURequest (SignOracle.none B.core) n) (h : hist.length < Q) (h' : hist'.length < Q) :
    (muNone B keys Q).respond c hist r = (muNone (X := X) (Y := Y) B keys Q).respond c hist' r := by
  simp only [muNone, h, h', ↓reduceIte]

omit [DecidableEq X] [Zero Y] [DecidableEq TB.PK] in
/-- **The main challenger of the key-free route reads its history only through its length**
below the cap. -/
theorem kfMain_readsLength [Fintype Coins] [DecidableEq Coins]
    (P : NARG.Prover X Y Stmt Wit Proof Coins) (μ : PMF Coins) (keys : Fin n → B.KeyCoins) (Q : ℕ) :
    ReadsLength (kfMain B rel P μ enc keys Q) Q := by
  intro c hist hist' r hl hQ
  rcases r with r | q
  · have h1 : (leftHist hist).length < Q := lt_of_le_of_lt (List.length_filterMap_le _ _) hQ
    have h2 : (leftHist hist').length < Q :=
      lt_of_le_of_lt (List.length_filterMap_le _ _) (hl ▸ hQ)
    simp only [kfMain, Challenger.sumDummy]
    rw [muChallenger_none_respond_eq B keys Q c.1 _ _ r h1 h2]
  · simp only [kfMain, Challenger.sumDummy, realChallenger, dummyHist, List.length_map, hl]

omit [DecidableEq X] [Zero Y] [DecidableEq TB.PK] in
/-- **The simulated main challenger of the key-free route reads its history only through its
length** below the cap. -/
theorem kfMainSim_readsLength [Fintype SC'] [DecidableEq SC']
    (S : NARG.Simulator X Y Stmt Proof SC') (keys : Fin n → B.KeyCoins) (Q : ℕ) :
    ReadsLength (kfMainSim B rel S enc keys Q) Q := by
  intro c hist hist' r hl hQ
  rcases r with r | q
  · have h1 : (leftHist hist).length < Q := lt_of_le_of_lt (List.length_filterMap_le _ _) hQ
    have h2 : (leftHist hist').length < Q :=
      lt_of_le_of_lt (List.length_filterMap_le _ _) (hl ▸ hQ)
    simp only [kfMainSim, Challenger.sumDummy]
    rw [muChallenger_none_respond_eq B keys Q c.1 _ _ r h1 h2]
  · simp only [kfMainSim, Challenger.sumDummy, simChallenger, dummyHist, List.length_map, hl]

end ReadsLength

/-! ### Freshness -/

variable {Stmt Wit : Type} (enc : MURequest (SignOracle.none B.core) n ⊕ R → ProofQuery Stmt Wit)
  (rel : Stmt → Wit → Prop) (stmtX : Stmt → X₀) (fstX : X₀ → RingStmt B)

omit [DecidableEq X] [Zero Y]
  [Fintype Pf] [DecidableEq Pf] [Fintype PC] [DecidableEq PC] [Nonempty PC] in
/-- **An in-relation proof query comes from a signed request with its ring and message**: if the
main request of request `r` is a proof query `q` in the relation, then `r` is a signing request
`(s, R, m)` and the ring statement of `q`'s statement has the ring `R` and the message `m`, for
dummy requests outside the relation (`hdum`), a statement program whose output reads back its
input (`hfst`), and `toR` carrying the program's outputs (`htoR`). -/
theorem reqOf_inr_rel
    (hdum : ∀ r, ¬ rel (enc (.inr (dummyR r))).stmt (enc (.inr (dummyR r))).wit)
    (hfst : ∀ x H, fstX ((stmtP x).run H) = x)
    (htoR : ∀ x H r σ,
      stmtX (enc (.inr (toR ((stmtP x).run H) r σ))).stmt = (stmtP x).run H)
    (c : ℕ) (r : Req B PS adm n) (o : Option (B.Pub × B.BSig × List (Assignment X Y)))
    (H : X → Y) (q : R) (hq : reqOf B toR dummyR c r o ((xP B stmtP r o).run H) = .inr q)
    (hrel : rel (enc (.inr q)).stmt (enc (.inr q)).wit) :
    ∃ s Rg msg, r = .sign s Rg msg ∧ (fstX (stmtX (enc (.inr q)).stmt)).ring = Rg ∧
      (fstX (stmtX (enc (.inr q)).stmt)).msg = msg := by
  rcases r with i | ⟨s, Rg, msg⟩ | ⟨i, bm⟩
  · simp [reqOf] at hq
  · rcases o with _ | p
    · simp only [reqOf, Sum.inr.injEq] at hq
      subst hq
      exact absurd hrel (hdum _)
    · simp only [xP, run_mapOutput, reqOf, Sum.inr.injEq] at hq
      subst hq
      refine ⟨s, Rg, msg, rfl, ?_⟩
      rw [htoR, hfst]
      exact ⟨rfl, rfl⟩
  · simp only [xP, run, reqOf, Sum.inr.injEq] at hq
    subst hq
    exact absurd hrel (hdum _)

omit [DecidableEq X] [Zero Y]
  [Fintype Pf] [DecidableEq Pf] [Fintype PC] [DecidableEq PC] [Nonempty PC] in
/-- **The freshness discharge**: an in-relation proof query asked for a request among `rs`
differs from every claim `x₀` whose ring statement has a ring and a message no request of `rs`
signed (`hnot`, the `not_sign` part of `FreshAt`). -/
theorem stmt_ne_of_freshAt
    (hdum : ∀ r, ¬ rel (enc (.inr (dummyR r))).stmt (enc (.inr (dummyR r))).wit)
    (hfst : ∀ x H, fstX ((stmtP x).run H) = x)
    (htoR : ∀ x H r σ,
      stmtX (enc (.inr (toR ((stmtP x).run H) r σ))).stmt = (stmtP x).run H)
    (rs : List (Req B PS adm n)) (Rg : KeyRing B.PK N) (msg : B.Msg)
    (hnot : ∀ s, UnforgeRequest.sign s Rg msg ∉ rs) (x₀ : X₀)
    (hx₀ : (fstX x₀).ring = Rg ∧ (fstX x₀).msg = msg)
    (c : ℕ) (r : Req B PS adm n) (hr : r ∈ rs) (o : Option (B.Pub × B.BSig × List (Assignment X Y)))
    (H : X → Y) (q : R) (hq : reqOf B toR dummyR c r o ((xP B stmtP r o).run H) = .inr q)
    (hrel : rel (enc (.inr q)).stmt (enc (.inr q)).wit) :
    stmtX (enc (.inr q)).stmt ≠ x₀ := by
  obtain ⟨s, Rg', msg', rfl, h1, h2⟩ :=
    reqOf_inr_rel B stmtP toR dummyR enc rel stmtX fstX hdum hfst htoR c r o H q hq hrel
  intro he
  rw [he, hx₀.1] at h1
  rw [he, hx₀.2] at h2
  subst h1 h2
  exact hnot s hr

/-! ### The well-formed main-request encoding -/

/-- **A well-formed main-request encoding** of the key-free relay: for the encoding `enc` of the
main requests as proof queries, the statement reading `stmtX`, the dummy test `isDummy`, the idle
request `idle`, the dummy and signing main requests `dummyR` and `toR`, the statement program
`stmtP` and the ring statement `fstX` of its outputs,
- the dummy requests have dummy statements (`hdumS`);
- on every path, the statement program's outputs read back its input (`hfst`);
- on every path, `toR` carries the statement program's output as its statement (`htoR`);
- the idle request's proof requests have dummy statements (`hidleS`);
- the idle request is not a corruption (`hidleC`). -/
structure KFEncoding {X Y : Type} {N n : ℕ} {TB : BaseTypes}
    {B : BaseSigner X Y N TB}
    {R Stmt Wit X₀ Rr Sig X' Y' : Type}
    (enc : MURequest (SignOracle.none B.core) n ⊕ R → ProofQuery Stmt Wit) (stmtX : Stmt → X₀)
    (isDummy : X₀ → Bool) (idle : MURequest (SignOracle.none B.core) n ⊕ R) (dummyR : Rr → R)
    (toR : X₀ → Rr → Sig → R) (stmtP : RingStmt B → OracleProg X' Y' X₀)
    (fstX : X₀ → RingStmt B) : Prop where
  /-- The dummy requests have dummy statements. -/
  hdumS : ∀ r, isDummy (stmtX (enc (.inr (dummyR r))).stmt) = true
  /-- The statement program's outputs read back its input, on every path. -/
  hfst : ∀ x, (stmtP x).AllOut fun x₀ => fstX x₀ = x
  /-- `toR` carries the statement program's outputs, on every path. -/
  htoR : ∀ x, (stmtP x).AllOut fun x₀ => ∀ r σ, stmtX (enc (.inr (toR x₀ r σ))).stmt = x₀
  /-- The idle request's proof requests have dummy statements. -/
  hidleS : ∀ q, idle = .inr q → isDummy (stmtX (enc (.inr q)).stmt) = true
  /-- The idle request is not a corruption. -/
  hidleC : ∀ i, idle ≠ .inl (.corrupt i)

end RingSignature.KeyFree

end GordieHowe
