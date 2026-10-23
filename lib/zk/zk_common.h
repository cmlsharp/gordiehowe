// Copyright 2026 Google LLC.
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.
// Modified 2026 by Chad Sharp and Paul Grubbs: optional caller-supplied linear constraints with hashed tag, and packed-bit and extension-packed constraint setup

#ifndef PRIVACY_PROOFS_ZK_LIB_ZK_ZK_COMMON_H_
#define PRIVACY_PROOFS_ZK_LIB_ZK_ZK_COMMON_H_

#include <cstddef>
#include <cstdint>
#include <functional>
#include <initializer_list>
#include <vector>

#include "arrays/dense.h"
#include "arrays/eq.h"
#include "arrays/eqs.h"
#include "ligero/ligero_param.h"
#include "random/transcript.h"
#include "sumcheck/circuit.h"
#include "sumcheck/quad.h"
#include "sumcheck/transcript_sumcheck.h"
#include "util/crypto.h"
#include "util/panic.h"
#include "zk/zk_extension_packed.h"
#include "zk/zk_packed.h"

namespace proofs {

template <class Field>
// ZkCommon
//
// Used by prover and verifier to mimic the checks that the sumcheck verifier
// applies to the sumcheck transcript. The difference is that the transcript
// will now be encrypted with a random pad, and the checks will be verified
// by the Ligero proof system with respect to a hiding commitment scheme.
class ZkCommon {
  using index_t = typename Quad<Field>::index_t;
  using Elt = typename Field::Elt;
  using CPoly = typename LayerProof<Field>::CPoly;
  using WPoly = typename LayerProof<Field>::WPoly;

public:
  using Llc = LigeroLinearConstraint<Field>;

  // Caller-supplied linear constraints over the COMMITTED witness, appended
  // after the sumcheck-derived ones.  Witness index w corresponds to circuit
  // input (w + circuit.npub_in) -- see input_constraint() below, which uses the
  // same convention.  Both prover and verifier must supply the identical
  // callback, since each rebuilds the constraint list independently.
  //
  // This lets a relation that is LINEAR in the committed values be discharged
  // by Ligero's linear test instead of by circuit gates.  The motivating case
  // is an NTT:  sum_k M[i][k]*in_k - out_i - q*d_i = 0  is linear in (in, out,
  // d) jointly, so it needs no gates at all -- and because gen_alphal() gives
  // every constraint an independent FULL-FIELD challenge squeezed post-commit,
  // a violated row survives with probability ~1/|F| with no repetitions.
  //
  // NB linear constraints are FREE in proof size: LigeroParam depends on the
  // witness size and the QUADRATIC constraint count only, never on nl.  The
  // cost is O(number of sparse terms) on both sides.
  struct ExtraConstraints {
    // Appends constraints and advances ci.
    std::function<void(std::vector<Llc> &a, std::vector<Elt> &b, size_t &ci)>
        gen;

    // Compact, unambiguous description of what `gen` emits.  THIS is what gets
    // bound into the transcript, instead of hashing the expanded term list.
    //
    // Hashing the expanded list would cost O(#terms) on both sides on top of
    // the O(#terms) already spent forming the dot product -- for the ML-DSA
    // algebra ~1.2M terms, tens of MB of hashing -- and it buys nothing: the
    // constraints are a deterministic function of a few public parameters (the
    // transform matrices, q, the limb base, the witness offsets), so binding
    // THOSE binds the statement just as tightly.  Both sides build the tag from
    // public data; if they disagree the hashes differ and the proof fails.
    std::vector<uint8_t> tag;

    // OPTIONAL fast path.  If set, `gen` need only emit the RHS b (and advance
    // ci); the coefficient side is contributed straight into Ligero's
    // inner-product vector A, avoiding the sparse triple list entirely.  Adding
    // A[w] += sum_c k_{c,w} * alphal_c with a streaming dense loop is an order
    // of magnitude cheaper than building and walking millions of 32-byte
    // triples, and it is paid by BOTH prover and verifier (A depends only on
    // alphal and the constraint system, never on the witness).
    std::function<void(Elt *A, const Elt *alphal, size_t ci_base)> accumulate;

    // Opt-in: caller supplies indices AFTER PackedLayout, BEFORE extension
    // packing. No automatic conversion of arbitrary bit-linear rows is implied.
    bool packed_coordinates = false;
  };

  // Describes the extra theorem statement for pre-GKR transcript binding.
  // With no injected constraints, the rows are implied by the circuit and
  // its public inputs, so no additional digest is absorbed. With injected
  // constraints the list is NOT implied by the circuit, so "both sides used the
  // same constraints" would otherwise be an assumption rather than a fact.
  // The input is
  //     0x04 || u8(len(label)) || label || u64le(packed_coordinates)
  //          || u64le(len(tag)) || tag,
  // a statement digest (util/crypto.h) whose label names the kind of rows:
  // "constraints" by default, "keccak-link" for the Keccak link and
  // "native-linear" for circuits/ntt/native_linear.h.
  template <class Hash = UpstreamHash>
  static BasicLigeroHash<Hash> hash_of_constraints(
      const std::vector<uint8_t> &tag, bool packed_coordinates,
      const char *label = "constraints") {
    Hash sha;
    begin_statement_digest(sha, label);
    sha.Update8(packed_coordinates ? 1 : 0);
    sha.Update8(static_cast<uint64_t>(tag.size()));
    if (!tag.empty()) {
      sha.Update(tag.data(), tag.size());
    }
    BasicLigeroHash<Hash> h;
    sha.DigestData(h.bytes);
    return h;
  }
  template <class Hash = UpstreamHash>
  static BasicLigeroHash<Hash> hash_of_constraints(
      const ExtraConstraints *extra) {
    if (extra == nullptr) {
      return BasicLigeroHash<Hash>{};
    }
    return hash_of_constraints<Hash>(extra->tag, extra->packed_coordinates);
  }

  // Packed-bit state for verifier_constraints (zk/zk_packed.h).  The prover
  // passes its committed witness and receives the masked values M; the
  // verifier passes the M it read from the proof.
  struct Packed {
    const PackedLayout<Field> *layout = nullptr;
    const Elt *committed = nullptr; // prover only
    std::vector<Elt> *m = nullptr;  // [Field::kSubFieldBits]
    // Test hook, prover only: added to M after it is computed and before it
    // is absorbed, to model a prover that reveals wrong masked values.
    const std::vector<Elt> *m_delta = nullptr;
  };

  static bool packed(const Circuit<Field> &c) { return !c.packed_bits.empty(); }

  static bool extension_packed(const Circuit<Field> &c) {
    const bool on = c.extension_packing && ExtensionTraits<Field>::supported;
    return on && c.subfield_boundary > c.npub_in;
  }
  static ExtensionLayout<Field> extension_layout(const Circuit<Field> &c,
                                                 size_t w) {
    size_t n = (c.ninputs - c.npub_in) + pad_size(c);
    size_t sub = c.subfield_boundary - c.npub_in;
    if constexpr (Field::kCharacteristicTwo)
      if (packed(c)) {
        const PackedLayout<Field> old(c, w);
        n = old.committed_size(pad_size(c));
        sub = old.boundary;
      }
    return ExtensionLayout<Field>(n, sub, w);
  }

  // Number of quadratic constraints: one per layer, plus the Frobenius chain
  // of a packed circuit.
  static size_t num_quadratic(const Circuit<Field> &c) {
    if constexpr (Field::kCharacteristicTwo) {
      if (packed(c))
        return c.nl + PackedLayout<Field>::kChain + c.input_products.size();
    }
    return c.nl + c.input_products.size();
  }

  // Ligero parameters for proving circuit C.  BLOCK_ENC = 0 searches powers of
  // two.  A packed circuit's committed size depends on the row width, which
  // depends on BLOCK_ENC, so BLOCK_ENC is fixed first from the unaligned size
  // and the aligned size is laid out at that BLOCK_ENC.  MODE selects the
  // Ligero options (LigeroMode; off by default).
  template <class Hash = UpstreamHash>
  static LigeroParam<Field, Hash> make_param(const Circuit<Field> &c,
                                             size_t rate, size_t nreq,
                                             size_t block_enc = 0,
                                             LigeroMode mode = {}) {
    const size_t nq = num_quadratic(c);
    auto mk = [&](size_t nw, size_t be) {
      return be == 0 ? LigeroParam<Field, Hash>(nw, nq, rate, nreq, mode)
                     : LigeroParam<Field, Hash>(nw, nq, rate, nreq, be, mode);
    };
    if (extension_packed(c)) {
      const auto unaligned = extension_layout(c, 0);
      const auto p0 = mk(unaligned.size, block_enc);
      const auto aligned = extension_layout(c, p0.w);
      return mk(aligned.size, p0.block_enc);
    }
    if constexpr (Field::kCharacteristicTwo) {
      if (packed(c)) {
        const size_t gkr = pad_size(c);
        const PackedLayout<Field> unaligned(c, /*w=*/0);
        const LigeroParam<Field, Hash> p0 =
            mk(unaligned.committed_size(gkr), block_enc);
        const PackedLayout<Field> layout(c, p0.w);
        return mk(layout.committed_size(gkr), p0.block_enc);
      }
    }
    return mk((c.ninputs - c.npub_in) + pad_size(c), block_enc);
  }

  // Quadratic constraints of the packed Frobenius chain,
  // s_{k,j} = s_{k,j-1}^2 with s_{k,0} = sigma_k, appended after the layers'.
  static void setup_packed_lqc(const Circuit<Field> &C,
                               const PackedLayout<Field> &L,
                               std::vector<LigeroQuadraticConstraint> &lqc) {
    const size_t gkr = pad_size(C);
    size_t q = C.nl;
    for (size_t k = 1; k < PackedLayout<Field>::kPack; ++k) {
      for (size_t j = 1; j <= k; ++j) {
        const size_t x = (j == 1) ? L.sigma(gkr, k) : L.chain(gkr, k, j - 1);
        lqc.at(q).x = x;
        lqc.at(q).y = x;
        lqc.at(q).z = L.chain(gkr, k, j);
        ++q;
      }
    }
    check(q + C.input_products.size() == num_quadratic(C), "packed chain count");
  }

  // The input claim GKR ends with, after the layer rows: the claim
  //   <eq(g0, .) + alpha eq(g1, .), inputs> = got,
  // and PI, the index just past the layer pads.  G points into the caller's
  // Challenge.
  struct InputClaim {
    size_t logv;
    const Elt *g[2];
    Elt alpha, got;
    size_t pi;
  };

  // The layer rows of verifier_constraints and the input-binding challenge,
  // without the input row: callers that lay out the inputs themselves
  // (gordiehowe/tree_zk.h) build it from the returned claim.
  template <class Hash>
  static InputClaim layer_constraints(const Circuit<Field> &circuit,
                                      const Proof<Field> &proof,
                                      const ProofAux<Field> *aux,
                                      std::vector<Llc> &a,
                                      std::vector<Elt> &b,
                                      BasicTranscript<Hash> &tsv, size_t pi,
                                      const Field &F, Challenge<Field> &ch,
                                      size_t &ci) {
    Claims cla = layers(circuit, proof, aux, a, b, tsv, pi, F, ch, ci);
    Elt alpha = tsv.elt(F);
    auto plr = &proof.l[circuit.nl - 1];
    Elt got = F.addf(plr->wc[0], F.mulf(alpha, plr->wc[1]));
    return InputClaim{cla.logv, {cla.g[0], cla.g[1]}, alpha, got, pi};
  }

  // pi: witness index for first pad element in a larger commitment
  template <class Hash>
  static size_t verifier_constraints(
      const Circuit<Field> &circuit, const Dense<Field> &pub,
      const Proof<Field> &proof, const ProofAux<Field> *aux,
      std::vector<Llc> &a, std::vector<typename Field::Elt> &b,
      BasicTranscript<Hash> &tsv,
      size_t pi, const Field &F, const ExtraConstraints *extra = nullptr,
      size_t *ci_before_extra = nullptr, Packed *pk = nullptr) {
    const size_t ninp = circuit.ninputs, npub = circuit.npub_in;

    Challenge<Field> ch(circuit.nl);
    size_t ci = 0;
    Claims cla = layers(circuit, proof, aux, a, b, tsv, pi, F, ch, ci);

    // Constraints induced by the input binding
    //   <eq0 + alpha.eq1, witness> = W_l + alpha.W_r
    Elt alpha = tsv.elt(F);
    auto plr = &proof.l[circuit.nl - 1];
    Elt got = F.addf(plr->wc[0], F.mulf(alpha, plr->wc[1]));

    if (packed(circuit)) {
      // Extra rows must explicitly use the packed witness coordinates.
      check(extra == nullptr || extra->packed_coordinates,
            "extra constraints require packed coordinates");
      check(pk != nullptr && pk->layout != nullptr && pk->m != nullptr,
            "packed circuit without packed state");
      if constexpr (Field::kCharacteristicTwo) {
        ci = packed_input_constraints(cla, pub, npub, ninp, pi, got, alpha, *pk,
                                      a, b, ci, tsv, F);
      }
    } else {
      ci = input_constraint(cla, pub, npub, ninp, pi, got, alpha, a, b, ci, F);
    }
    if (ci_before_extra != nullptr) {
      *ci_before_extra = ci;
    }
    if (extra != nullptr) {
      extra->gen(a, b, ci);
    }
    return ci;
  }

 private:
  struct Claims;
  // The sumcheck verifier's layer rows; advances PI past the layer pads.
  template <class Hash>
  static Claims layers(const Circuit<Field> &circuit, const Proof<Field> &proof,
                       const ProofAux<Field> *aux, std::vector<Llc> &a,
                       std::vector<Elt> &b, BasicTranscript<Hash> &tsv,
                       size_t &pi, const Field &F, Challenge<Field> &ch,
                       size_t &ci) {
    TranscriptSumcheck<Field, Hash> tss(tsv, F);

    check(circuit.logv <= Proof<Field>::kMaxBindings,
          "circuit.logv <= kMaxBindings");
    tss.begin_circuit(ch.q, ch.g);
    Claims cla = Claims{
        .logv = circuit.logv,
        .claim = {F.zero(), F.zero()},
        .q = ch.q,
        .g = {ch.g, ch.g},
    };

    const typename WPoly::dot_interpolation dot_wpoly(F);

    // no copies in this version.
    check(circuit.logc == 0, "assuming that copies=1");

    // Constraints from the sumcheck verifier.
    for (size_t ly = 0; ly < circuit.nl; ++ly) {
      auto clr = &circuit.l.at(ly);
      auto plr = &proof.l[ly];
      auto challenge = &ch.l[ly];

      tss.begin_layer(challenge->alpha, challenge->beta, ly);

      // The loop below assumes at least one round.
      check(clr->logw > 0, "clr->logw > 0");
      check(clr->logw <= Proof<Field>::kMaxBindings,
            "clr->logw <= kMaxBindings");

      PadLayout pl(clr->logw);
      ConstraintBuilder cb(pl, F); // representing 0

      cb.first(challenge->alpha, cla.claim);
      // now cb contains claim_{-1} from the previous layer

      for (size_t round = 0; round < clr->logw; ++round) {
        for (size_t hand = 0; hand < 2; ++hand) {
          size_t r = 2 * round + hand;
          const WPoly &hp = plr->hp[hand][round];
          challenge->hb[hand][round] = tss.round(hp);
          const WPoly lag = dot_wpoly.coef(challenge->hb[hand][round], F);

          cb.next(r, &lag[0], hp.t_);
          // now cb contains a symbolic representation of claim_{r}
        }
      }

      // Verify
      //        claim = EQ[Q,C] QUAD[R,L] W[R,C] W[L,C]
      // by substituting in the symbolic constraint on p(1) from the relation:
      //      claim = <lag, (p(0), p(1), p(2))>.
      Elt quad = aux == nullptr ? bind_quad(clr, cla, challenge, F)
                                : aux->bound_quad[ly];
      Elt eqv =
          Eq<Field>::eval(circuit.logc, circuit.nc, ch.q, challenge->cb, F);
      Elt eqq = F.mulf(eqv, quad);

      // Add the final constraint from above.
      cb.finalize(plr->wc, eqq, ci++, ly, pi, a, b);

      tss.write(&plr->wc[0], 1, 2);

      cla = Claims{
          .logv = clr->logw,
          .claim = {plr->wc[0], plr->wc[1]},
          .q = challenge->cb,
          .g = {challenge->hb[0], challenge->hb[1]},
      };

      pi += pl.layer_size(); // Update index to poly_pad(0,0) of the
                             // next layer
    }
    return cla;
  }

 public:

  // Returns the size of the proof pad for circuit C.
  static size_t pad_size(const Circuit<Field> &C) {
    size_t sz = 0;
    for (size_t i = 0; i < C.nl; ++i) {
      PadLayout pl(C.l[i].logw);
      sz += pl.layer_size();
    }
    return sz;
  }

  // Setup lqc based on proof pad layout.
  static void setup_lqc(const Circuit<Field> &C,
                        std::vector<LigeroQuadraticConstraint> &lqc,
                        size_t start_pad) {
    size_t pi = start_pad;
    for (size_t i = 0; i < C.nl; ++i) {
      PadLayout pl(C.l[i].logw);
      lqc[i].x = pi + pl.claim_pad(0);
      lqc[i].y = pi + pl.claim_pad(1);
      lqc[i].z = pi + pl.claim_pad(2);
      pi += pl.layer_size();
    }
  }

  static void setup_input_products(const Circuit<Field>& c,
      const PackedLayout<Field>* layout,std::vector<LigeroQuadraticConstraint>& lqc) {
    size_t offset=num_quadratic(c)-c.input_products.size();
    auto map=[&](size_t i) {
      check(i>=c.npub_in && i<c.ninputs,"input product must reference private input");
      if(layout) {size_t j=layout->map.at(i);check(j!=PackedLayout<Field>::kNone,"input product cannot reference a packed bit");return j;}
      return i-c.npub_in;
    };
    for(auto q:c.input_products) lqc.at(offset++)={map(q[0]),map(q[1]),map(q[2])};
  }

  // The sumcheck preamble. The statement (circuit id, public inputs, extra
  // digest) is not written here: every protocol absorbs it once, at the start
  // of its transcript and before any commitment, with absorb_statement below.
  template <class Hash>
  static void initialize_sumcheck_fiat_shamir(BasicTranscript<Hash> &ts,
                                              const Circuit<Field> &circuit,
                                              const Field &F) {
    // Outputs pro-forma:
    ts.write(F.zero(), F);

    // Enough zeroes for correlation intractability, one byte
    // per term.
    ts.write0(circuit.nterms());
  }

private:
  // The claims struct mimics the same object in the sumcheck code. This
  // helps the verifier_constraints method above mimic the same steps as
  // the sumcheck verifier.
  struct Claims {
    size_t logv;
    Elt claim[2];
    const Elt *q;
    const Elt *g[2];
  };

  class PadLayout {
    size_t logw_;

  public:
    explicit PadLayout(size_t logw) : logw_(logw) {}

    // Layout of padding in the expr_.symbolic array.
    //
    // A *claim pad* is a triple [dWC[0], dWC[1], dWC[0]*dWC[1]].
    //
    // A *poly pad* is a pair [dP(0), dP(2)], where "2" is a generic
    // name for the third evaluation point of the sumcheck round
    // polynomial (could be X for binary fields GF(2)[X] / (Q(X))).
    //
    // The layout of expr_.symbolic is
    //  [CLAIM_PAD[layer - 1], POLY_PAD[0], POLY_PAD[1], ..
    //   POLY_PAD[LOGW - 1], CLAIM_PAD[layer]]
    //
    // The layout of adjacent layers thus overlaps.  For layer 0
    // we still lay out CLAIM_PAD[layer - 1] to keep the representation
    // uniform, but we don't output the corresponding Ligero terms.

    // Because of different use cases, we have two indexing schemes:
    //
    //  "with overlap":     the first element is CLAIM_PAD[layer - 1][0]
    //  "without overlap":  the first element is POLY_PAD[0][0]

    //------------------------------------------------------------
    // Indexing without overlap.
    //------------------------------------------------------------
    size_t poly_pad(size_t r, size_t point) const {
      check(point == 0 || point == 2, "unknown poly_pad() layout");
      if (point == 0) {
        return 2 * r;
      } else if (point == 2) {
        return 2 * r + 1;
      }
      return 0; // silence noreturn warning
    }
    // index of CLAIM_PAD[layer][n]
    size_t claim_pad(size_t n) const { return poly_pad(2 * logw_, 0) + n; }

    // size of the layer
    size_t layer_size() const { return claim_pad(3); }

    //------------------------------------------------------------
    // Indexing with overlap.
    //------------------------------------------------------------
    // index of CLAIM_PAD[layer - 1][n]
    size_t ovp_claim_pad_m1(size_t n) const { return n; }
    size_t ovp_poly_pad(size_t r, size_t point) const {
      return 3 + poly_pad(r, point);
    }
    size_t ovp_claim_pad(size_t n) const { return 3 + claim_pad(n); }
    size_t ovp_layer_size() const { return ovp_claim_pad(3); }
  };

  // Represent symbolic expressions of the form
  //
  // KNOWN + SUM_{i} SYMBOLIC[i] * WITNESS[i]
  //
  // and support simple linear operations on such quantities
  class Expression {
    Elt known_;
    std::vector<Elt> symbolic_;
    const Field &f_;

  public:
    Expression(size_t nvar, const Field &F)
        : known_(F.zero()), symbolic_(nvar, F.zero()), f_(F) {}

    Elt known() { return known_; }
    std::vector<Elt> symbolic() { return symbolic_; }

    void scale(const Elt &k) {
      f_.mul(known_, k);
      for (auto &e : symbolic_) {
        f_.mul(e, k);
      }
    }

    // We don't need the general case of combining two
    // Expressions.  Instead, we only need the two operations
    // below.

    // *this += k * (known_value + witness[var]).
    void axpy(size_t var, const Elt &known_value, const Elt &k) {
      f_.add(known_, f_.mulf(k, known_value));
      f_.add(symbolic_[var], k);
    }

    // *this -= k * (known_value + witness[var])
    void axmy(size_t var, const Elt &known_value, const Elt &k) {
      f_.sub(known_, f_.mulf(k, known_value));
      f_.sub(symbolic_[var], k);
    }
  };

  class ConstraintBuilder {
    Expression expr_;
    const PadLayout &pl_;
    const Field &f_;

  public:
    ConstraintBuilder(const PadLayout &pl, const Field &F)
        : expr_(pl.ovp_layer_size(), F), pl_(pl), f_(F) {}

    // For given unpadded variable X in the original non-ZK prover,
    // the transcript contains the padded variable Xhat = X - dX
    // where dX is the padding of X.  Thus the unpadded variable is
    //
    //    X = Xhat + dX
    //
    // The ZK verifier needs to compute linear combinations (and one
    // quadratic combination) of the X's, but it only has access to
    // the Xhat's and to a commitment to the dX's.  We also want to
    // discuss the verifier algorithm as if the verifier were
    // operating on X, in order to keep the discussion simple.
    //
    // To this end, the Expression class keeps a symbolic
    // representation of a variable X as
    //
    //     X = KNOWN + SUM_{i} SYMBOLIC[i] dX[i]
    //
    // which is sufficient to capture any linear combination of
    // X variables.  We do something special for the quadratic
    // combination in finalize().

    // We store only one quantity EXPR_ that represents either
    // p(1) at some certain round, or a claim at some round.
    // Comments make it clear which is which.

    // Initially, compute claim_{-1} = cl0 + alpha*cl1
    void first(Elt alpha, const Elt claims[]) {
      // expr_ contains zero
      expr_.axpy(pl_.ovp_claim_pad_m1(0), claims[0], f_.one());
      expr_.axpy(pl_.ovp_claim_pad_m1(1), claims[1], alpha);
      // expr_ contains claim_{-1} = cl0 + alpha*cl1
    }

    // Given claim_{r-1}, compute claim_{r}
    void next(size_t r, const Elt lag[], const Elt tr[]) {
      // expr contains claim_{r-1}
      expr_.axmy(pl_.ovp_poly_pad(r, 0), tr[0], f_.one());
      // expr contains p_{r}(1) = claim_{r-1} - p_{r}(0)

      // Compute the dot-product <lag_{r}, p_{r}> in place:
      //  claim_{r} = p_{r}(1) * lag[1], overwriting expr_
      //  claim_{r} += lag[0] * p_{r}(0)
      //  claim_{r} += lag[2] * p_{r}(2)
      expr_.scale(lag[1]);
      expr_.axpy(pl_.ovp_poly_pad(r, 0), tr[0], lag[0]);
      expr_.axpy(pl_.ovp_poly_pad(r, 2), tr[2], lag[2]);
      // expr_ contains claim_{r} = <lag_{r}, p_{r}>
    }

    // The finalize method uses the last sumcheck claim to
    // add a constraint on the dX's (the pad) to the Ligero system.
    //
    // Our goal is to verify that
    //
    //            CLAIM = EQQ * W[R,C] * W[L,C]
    //
    // where EQQ = EQ[Q,C] QUAD[R,L] and all variables are unpadded.
    //
    // We have a symbolic representation of CLAIM in expr_, the proof
    // contains W_hat[{R,L},C], the padding witnesses are at index pi,
    // pi+1, and their product is at index pi+2.
    //
    // Let CLAIM = KNOWN + SUM_{i} SYMBOLIC[i] dX[i] from the
    // Expression class.  Then
    //
    //     KNOWN + SUM_{i} SYMBOLIC[i] dX[i]
    //        = EQQ * (W_hat[R,C] + dW[R,C]) * (W_hat[L,C] + dW[L,C])
    //
    // Rearranging in the Ax = b form needed for ligero, we have
    //
    //  SUM_{i} SYMBOLIC[i] dX[i] - (EQQ * W[R, C]) dW[L, C]
    //      - (EQQ * W[L, C]) dW[R, C] - EQQ * dW[R,C] * dW[L,C]
    //   = EQQ * W[R,C] * W[L,C] - KNOWN
    void finalize(const Elt wc[], const Elt &eqq, size_t ci, size_t ly,
                  size_t pi, std::vector<Llc> &a, std::vector<Elt> &b) {
      // break the Expression abstraction and split into constituents.

      // EQQ * W[R,C] * W[L,C] - known
      Elt rhs = f_.subf(f_.mulf(eqq, f_.mulf(wc[0], wc[1])), expr_.known());

      // symbolic part
      std::vector<Elt> lhs = expr_.symbolic();
      f_.sub(lhs[pl_.ovp_claim_pad(0)], f_.mulf(eqq, wc[1]));
      f_.sub(lhs[pl_.ovp_claim_pad(1)], f_.mulf(eqq, wc[0]));
      f_.sub(lhs[pl_.ovp_claim_pad(2)], eqq);

      b.push_back(rhs);

      // Layer 0 does not refer to CLAIM_PAD[layer - 1]
      size_t i0 = (ly == 0) ? pl_.ovp_poly_pad(0, 0) : pl_.ovp_claim_pad_m1(0);

      for (size_t i = i0; i < lhs.size(); ++i) {
        // "i" is in the "with overlap" reference frame.
        // "pi" is in the "without overlap" reference frame.
        //
        // In theory at least, (pi - pl_.ovp_poly_pad(0, 0))
        // could overflow, but (pi + i) - pl_.ovp_poly_pad(0, 0) cannot.
        a.push_back(Llc{ci, (pi + i) - pl_.ovp_poly_pad(0, 0), lhs[i]});
      }
    }
  };

  // binding(inputs, R) = binding(pub_inputs, R_p) + binding(witness, R_w)
  // This method explicitly computes the public binding, and then adds the
  // constraints that
  //    binding(witness, R_w) = got - binding(pub_inputs, R_p)
  static size_t input_constraint(const Claims &cla, const Dense<Field> &pub,
                                 size_t pub_inputs, size_t num_inputs,
                                 size_t pi, Elt got, Elt alpha,
                                 std::vector<Llc> &a, std::vector<Elt> &b,
                                 size_t ci, const Field &F) {
    Eqs<Field> eq0(cla.logv, num_inputs, cla.g[0], F);
    Eqs<Field> eq1(cla.logv, num_inputs, cla.g[1], F);
    Elt pub_binding = F.zero();
    for (index_t i = 0; i < num_inputs; ++i) {
      Elt b_i = F.addf(eq0.at(i), F.mulf(alpha, eq1.at(i)));
      if (i < pub_inputs) {
        F.add(pub_binding, F.mulf(b_i, pub.at(i)));
      } else {
        // Use (i - pub_inputs) for the index of private inputs.
        a.push_back(Llc{ci, i - pub_inputs, b_i});
      }
    }

    // We view the input constraints as being at fake layer
    // one past the last real layer.  The alternative of
    // considering the input as part of the last real layer
    // yields code that looks even more convoluted.
    PadLayout pl(/*logw=*/0);

    // This paranoid assertion holds unless the circuit has zero
    // layers, which is not guaranteed by this function alone.
    check(pi >= pl.ovp_poly_pad(0, 0), "pi >= pl.ovp_poly_pad(0, 0)");

    size_t claim_pad_m1 = pi - pl.ovp_poly_pad(0, 0);
    a.push_back(Llc{ci, claim_pad_m1 + 0, F.mone()});
    a.push_back(Llc{ci, claim_pad_m1 + 1, F.negf(alpha)});
    b.push_back(F.subf(got, pub_binding));
    return ++ci;
  }

  // The input binding of a packed circuit.  PI is the index just past the
  // GKR pads, which is where the sigma pads begin.  The unpacked inputs enter
  // the input row as in input_constraint(); the packed ones enter through the
  // masked values M_k (see zk/zk_packed.h):
  //
  //   <b, unpacked> + SUM_k pi_k - dW_l - alpha.dW_r
  //       = got - binding(pub) - SUM_k M_k^(2^k)
  //   <a_k, packed> + sigma_k = M_k                      for each k.
  //
  // M_k is absorbed into the transcript before Ligero draws its challenges.
  template <class Hash>
  static size_t packed_input_constraints(const Claims &cla,
                                         const Dense<Field> &pub,
                                         size_t pub_inputs, size_t num_inputs,
                                         size_t pi, Elt got, Elt alpha,
                                         Packed &pk, std::vector<Llc> &a,
                                         std::vector<Elt> &b, size_t ci,
                                         BasicTranscript<Hash> &tsv,
                                         const Field &F) {
    using Layout = PackedLayout<Field>;
    constexpr size_t kPack = Layout::kPack;
    const Layout &L = *pk.layout;
    check(L.ninputs == num_inputs && L.npub == pub_inputs, "packed layout");
    check(pi >= L.n_witness, "packed pads precede the inputs");
    const size_t gkr = pi - L.n_witness;
    auto sigma = [&](size_t k) { return L.sigma(gkr, k); };
    auto pi_k = [&](size_t k) { return L.pi(gkr, k); };

    const PackedBasis<Field> basis(F);
    const PackedForms<Field> forms(basis, cla.logv, L.group.size(), cla.g[0],
                                   cla.g[1], alpha, F);

    std::vector<Elt> &m = *pk.m;
    if (pk.committed != nullptr) {
      m.assign(kPack, F.zero());
      for (size_t k = 0; k < kPack; ++k) {
        m[k] = F.addf(forms.z(k, L, pk.committed, F), pk.committed[sigma(k)]);
        if (pk.m_delta != nullptr)
          F.add(m[k], pk.m_delta->at(k));
      }
    }
    check(m.size() == kPack, "packed M size");
    tsv.write(&m[0], 1, kPack, F);

    // Input row.
    Eqs<Field> eq0(cla.logv, num_inputs, cla.g[0], F);
    Eqs<Field> eq1(cla.logv, num_inputs, cla.g[1], F);
    Elt pub_binding = F.zero();
    for (index_t i = 0; i < num_inputs; ++i) {
      Elt b_i = F.addf(eq0.at(i), F.mulf(alpha, eq1.at(i)));
      if (i < pub_inputs) {
        F.add(pub_binding, F.mulf(b_i, pub.at(i)));
      } else if (L.map[i] != Layout::kNone) {
        a.push_back(Llc{ci, L.map[i], b_i});
      }
    }
    Elt rhs = F.subf(got, pub_binding);
    for (size_t k = 0; k < kPack; ++k) {
      a.push_back(Llc{ci, pi_k(k), F.one()});
      F.sub(rhs, frobenius(m[k], k, F));
    }
    PadLayout pl(/*logw=*/0);
    check(pi >= pl.ovp_poly_pad(0, 0), "pi >= pl.ovp_poly_pad(0, 0)");
    size_t claim_pad_m1 = pi - pl.ovp_poly_pad(0, 0);
    a.push_back(Llc{ci, claim_pad_m1 + 0, F.mone()});
    a.push_back(Llc{ci, claim_pad_m1 + 1, F.negf(alpha)});
    b.push_back(rhs);
    ++ci;

    // Masked forms.
    for (size_t k = 0; k < kPack; ++k) {
      const std::vector<Elt> &ak = forms.a(k);
      for (size_t Y = 0; Y < L.group.size(); ++Y) {
        if (L.group[Y] != Layout::kNone) {
          a.push_back(Llc{ci, L.group[Y], ak[Y]});
        }
      }
      a.push_back(Llc{ci, sigma(k), F.one()});
      b.push_back(m[k]);
      ++ci;
    }
    return ci;
  }

  static Elt bind_quad(const Layer<Field> *clr, const Claims &cla,
                       const LayerChallenge<Field> *chal, const Field &F) {
    return clr->quad->bind_gh_all(
        // G
        cla.logv, cla.g[0], cla.g[1], chal->alpha, chal->beta,
        // H
        clr->logw, chal->hb[0], chal->hb[1],
        // Field
        F, clr->unit_coefficient_shortcuts);
  }
};

// The statement's public parameters, in the order the protocol fixes them:
// runs of field elements of any field (each at its field's fixed width) and
// byte strings. absorb_statement writes each part as one length-prefixed byte
// string.
class StatementParams {
public:
  template <class Field>
  StatementParams &elts(const Field &F, const typename Field::Elt *e,
                        size_t n) {
    std::vector<uint8_t> b(n * Field::kBytes);
    for (size_t i = 0; i < n; ++i)
      F.to_bytes_field(&b[i * Field::kBytes], e[i]);
    parts_.push_back(std::move(b));
    return *this;
  }
  template <class Field>
  StatementParams &elts(const Field &F,
                        const std::vector<typename Field::Elt> &v) {
    return elts(F, v.data(), v.size());
  }
  // Public inputs [begin, end) of a circuit.
  template <class Field>
  StatementParams &slots(const Field &F, const Dense<Field> &pub, size_t begin,
                         size_t end) {
    check(begin <= end && end <= pub.v_.size(), "statement slots");
    return elts(F, pub.v_.data() + begin, end - begin);
  }
  StatementParams &bytes(const uint8_t *b, size_t n) {
    parts_.emplace_back(b, b + n);
    return *this;
  }
  StatementParams &bytes(const std::vector<uint8_t> &b) {
    return bytes(b.data(), b.size());
  }
  const std::vector<std::vector<uint8_t>> &parts() const { return parts_; }

private:
  std::vector<std::vector<uint8_t>> parts_;
};

// The Fiat-Shamir statement prefix. A transcript is created with its label;
// every protocol then calls this once, before any commitment, with every
// circuit id it uses (in protocol order), all public parameters fixed before
// the protocol starts, and the digest of each set of extra constraints
// (ZkCommon::hash_of_constraints). ZkProver::prove and ZkVerifier::verify
// write none of these, so a public input derived during the protocol must
// already be on the transcript (a challenge, or an absorbed prover message).
template <class Hash>
void absorb_statement(BasicTranscript<Hash> &ts,
                      std::initializer_list<const uint8_t *> circuit_ids,
                      const StatementParams &pub,
                      std::initializer_list<BasicLigeroHash<Hash>> digests) {
  for (const uint8_t *id : circuit_ids)
    ts.write(id, Hash::kDigestSize);
  for (const auto &part : pub.parts())
    ts.write(part.data(), part.size());
  for (const auto &d : digests)
    ts.write(d.bytes, d.kLength);
}

// The statement of one circuit whose public inputs are all fixed before the
// protocol starts: its id, public inputs [0, npub_in) and, with extra
// constraints, their digest.
template <class Field, class Hash>
void absorb_circuit_statement(
    BasicTranscript<Hash> &ts, const Circuit<Field> &circuit,
    const Dense<Field> &pub, const Field &F,
    const typename ZkCommon<Field>::ExtraConstraints *extra = nullptr) {
  StatementParams params;
  params.slots(F, pub, 0, circuit.npub_in);
  if (extra != nullptr) {
    absorb_statement<Hash>(
        ts, {circuit.id}, params,
        {ZkCommon<Field>::template hash_of_constraints<Hash>(extra)});
  } else {
    absorb_statement<Hash>(ts, {circuit.id}, params, {});
  }
}
} // namespace proofs

#endif // PRIVACY_PROOFS_ZK_LIB_ZK_ZK_COMMON_H_
