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
// Modified 2026 by Chad Sharp and Paul Grubbs: hash-policy template parameter, packed-bit and extension-packed witness commitment, ldt_commit, extra linear constraints, phase profiling

#ifndef PRIVACY_PROOFS_ZK_LIB_ZK_ZK_PROVER_H_
#define PRIVACY_PROOFS_ZK_LIB_ZK_ZK_PROVER_H_

#include <stddef.h>

#include <cstdint>
#include <memory>
#include <vector>

#include "arrays/dense.h"
#include "ligero/ligero_param.h"
#include "ligero/ligero_prover.h"
#include "random/random.h"
#include "random/transcript.h"
#include "sumcheck/circuit.h"
#include "sumcheck/prover_layers.h"
#include "sumcheck/transcript_sumcheck.h"
#include "util/log.h"
#include "util/panic.h"
#include "util/prover_profile.h"
#include "zk/zk_common.h"
#include "zk/zk_packed.h"
#include "zk/zk_proof.h"

namespace proofs {
// ZK Prover
//
// This class implements a zero-knowledge argument over a sumcheck transcript
// by first committing to a sumcheck witness and a random pad to encrypt
// a sumcheck transcript, then running the sumcheck protocol over the original
// claim and witness, but outputting the encrypted transcript, and finally
// using a Ligero prover to prove the statement: "the committed witness and
// pad, when used to decrypt the encrypted sumcheck transcript satisfies the
// sumcheck verifier."
//
// While this statement is complex, it can be implemented easily because
// the sumcheck verifier essentially checks the evaluations of degree-2 or -3
// polynomials, and performs one multiplication per layer of the circuit. The
// Hyrax paper makes a similar observation, but uses an elliptic-curve based
// proof, whereas here we use the Ligero system.
// Hash is the protocol hash policy (util/crypto.h) of the commitment and
// the transcript.
template <class Field, class ReedSolomonFactory, class Hash = UpstreamHash>
class ZkProver : public ProverLayers<Field> {
  using super = ProverLayers<Field>;
  using typename super::bindings;
  using Elt = typename Field::Elt;
  using typename super::inputs;

public:
  ZkProver(const Circuit<Field> &CIRCUIT, const Field &F,
           const ReedSolomonFactory &rs_factory)
      : ProverLayers<Field>(F), c_(CIRCUIT),
        n_witness_(c_.ninputs - c_.npub_in), f_(F), rsf_(rs_factory),
        pad_(c_.nl), witness_(n_witness_), lqc_(ZkCommon<Field>::num_quadratic(c_)), lp_(nullptr) {}

  // The transcript counters (TranscriptStats) at the phase boundaries of the
  // last commit and prove, and the committed subfield boundary. Without
  // extension packing, batching equals gkr.
  struct TranscriptPhases {
    TranscriptStats commit_begin, commit_end;
    TranscriptStats prove_begin, sumcheck_init, gkr, batching, ligero;
  };
  TranscriptPhases phases;
  size_t committed_subfield_boundary = 0;

  void commit(ZkProof<Field, Hash> &zkp, const Dense<Field> &W,
              BasicTranscript<Hash> &tp,
              RandomEngine &rng) {
    log(INFO, "ZK Commit start");
    phases.commit_begin = tp.stats();
    profiling::Session profile("commit", typeid(Field).name(), c_.ninputs,
                                c_.nl);

    size_t subfield_boundary = 0;
    if (ZkCommon<Field>::packed(c_)) {
      if constexpr (Field::kCharacteristicTwo) {
        subfield_boundary = commit_packed_inputs(zkp, W);
      }
    } else {
      // Copy witnesses for commitment
      // Layout of the com: 0 ...<witnesses>... start_pad <pad> len
      // Only commit the private witnesses, which begin at index c_.npub_in.
      for (size_t i = 0; i < n_witness_; ++i) {
        witness_[i] = W.v_[i + c_.npub_in];
      }
      start_pad_ = n_witness_;

      // Rebase the circuit SUBFIELD_BOUNDARY (if any) to start at
      // NPUB_IN,
      if (c_.subfield_boundary >= c_.npub_in) {
        subfield_boundary = c_.subfield_boundary - c_.npub_in;
      }
    }

    // Fill pad with random values, add pad to witness, record lqc.
    fill_pad(rng);
    ZkCommon<Field>::setup_lqc(c_, lqc_, start_pad_);
    if (ZkCommon<Field>::packed(c_)) {
      if constexpr (Field::kCharacteristicTwo) {
        fill_packed_pads(rng);
        ZkCommon<Field>::setup_packed_lqc(c_, *layout_, lqc_);
      }
    }
    ZkCommon<Field>::setup_input_products(c_, layout_.get(), lqc_);
    if (ZkCommon<Field>::extension_packed(c_)) {
      extension_layout_ = std::make_unique<ExtensionLayout<Field>>(
          ZkCommon<Field>::extension_layout(c_, zkp.param.w));
      original_witness_ = std::move(witness_);
      witness_ = extension_layout_->pack(original_witness_, rng, f_);
      extension_layout_->remap(lqc_);
      subfield_boundary = extension_layout_->prefix;
      extension_layout_->bind(tp);
    }
    check(witness_.size() == zkp.param.nw, "committed witness size");

    // Commit to witness and pad.
    lp_ = std::make_unique<LigeroProver<Field, ReedSolomonFactory, Hash>>(
        zkp.param);
    profile.mark("setup");
    lp_->commit(zkp.com, tp, &witness_[0], subfield_boundary, &lqc_[0], rsf_,
                rng, f_);
    committed_subfield_boundary = subfield_boundary;
    phases.commit_end = tp.stats();

    log(INFO, "ZK Commitment done");
    profile.mark("ligero_commit");
  }

  // List-radius Ligero (LigeroMode::list_radius): the low-degree round of
  // this commitment, after every commitment of the enclosing protocol and
  // before any other challenge (LigeroProver::ldt_commit).
  void ldt_commit(ZkProof<Field, Hash> &zkp, BasicTranscript<Hash> &tp) {
    check(lp_ != nullptr, "must run commit before ldt_commit");
    lp_->ldt_commit(zkp.com_proof, tp, f_);
  }

  // `extra`, if non-null, appends caller-supplied LINEAR constraints over the
  // committed witness (see ZkCommon::ExtraConstraints).  The verifier MUST pass
  // an identical callback.
  bool
  prove(ZkProof<Field, Hash> &zkp, const Dense<Field> &W,
        BasicTranscript<Hash> &tsp,
        const typename ZkCommon<Field>::ExtraConstraints *extra = nullptr) {
    check(lp_ != nullptr, "must run commit before prove");
    check(extra == nullptr || !ZkCommon<Field>::packed(c_) ||
              extra->packed_coordinates,
          "extra constraints on a packed circuit");
    profiling::Session profile("prove", typeid(Field).name(), c_.ninputs,
                                c_.nl);
    phases.prove_begin = tsp.stats();

    // The statement (circuit id, public inputs, digest of `extra`) opens the
    // transcript before any commitment (absorb_statement in zk_common.h).
    ZkCommon<Field>::initialize_sumcheck_fiat_shamir(tsp, c_, f_);
    phases.sumcheck_init = tsp.stats();
    BasicTranscript<Hash> tst = tsp.clone();
    profile.mark("statement");

    // Run sumcheck to generate a padded proof.
    inputs in;
    auto V = super::eval_circuit(&in, &c_, W.clone(), f_);
    if (V == nullptr) {
      log(ERROR, "eval_circuit failed");
      return false;
    }
    for (size_t i = 0; this->require_satisfied && i < V->n1_; ++i) {
      if (V->v_[i] != f_.zero()) {
        log(ERROR, "V->v_[i] != F.zero()");
        return false;
      };
    }
    bindings bnd;
    profile.mark("evaluate");
    ProofAux<Field> aux(c_.nl);

    TranscriptSumcheck<Field, Hash> tsts(tst, f_);
    super::prove(&zkp.proof, &pad_, &c_, in, &aux, bnd, tsts, f_);
    log(INFO, "ZK sumcheck done");
    profile.mark("sumcheck");

    // 5. Simulate the verifier to assemble constraints on the committed vals.
    //    Form the sparse matrix A and vector b such that A*w = b.
    std::vector<LigeroLinearConstraint<Field>> a;
    std::vector<Elt> b;
    size_t ci_before_extra = 0;
    typename ZkCommon<Field>::Packed pk;
    pk.layout = layout_.get();
    pk.committed =
        extension_layout_ ? original_witness_.data() : witness_.data();
    pk.m = &zkp.packed_m;
    if (!packed_m_delta_.empty())
      pk.m_delta = &packed_m_delta_;
    size_t ci = ZkCommon<Field>::verifier_constraints(
        c_, W, zkp.proof, &aux, a, b, tsp, start_pad_, f_, extra,
        &ci_before_extra, &pk);
    phases.gkr = tsp.stats();
    phases.batching = phases.gkr;
    log(INFO, "ZK constraints done");
    profile.mark("constraints");

    if (extension_layout_) {
      ExtensionForms<Field> forms(*extension_layout_, ci, a, b, tsp, extra,
                                  ci_before_extra, f_);
      forms.reveal(zkp.extension_m, *extension_layout_, witness_.data(), f_);
      if (!extension_m_delta_.empty()) {
        check(extension_m_delta_.size() == zkp.extension_m.size(),
              "extension test delta size");
        for (size_t i = 0; i < extension_m_delta_.size(); ++i)
          f_.add(zkp.extension_m[i], extension_m_delta_[i]);
      }
      tsp.write(zkp.extension_m.data(), 1, zkp.extension_m.size(), f_);
      phases.batching = tsp.stats();
      typename LigeroProver<Field, ReedSolomonFactory, Hash>::Accumulator acc =
          [&](Elt *out, const Elt *alpha) {
            forms.accumulate(out, alpha, *extension_layout_, f_);
          };
      profile.mark("extension_claim");
      lp_->prove(zkp.com_proof, tsp, ExtensionTraits<Field>::degree + 1, 0,
                 nullptr, lqc_.data(), rsf_, f_, &acc);
      phases.ligero = tsp.stats();
      profile.mark("ligero");
      return true;
    }

    // 6. Produce proof over commitment.
    // Circuit-derived rows are determined by the transcript. Caller-supplied
    // rows are bound by their digest in the statement prefix. Ligero continues
    // that transcript without absorbing the statement a second time.
    typename LigeroProver<Field, ReedSolomonFactory, Hash>::Accumulator acc;
    const auto *accp = (extra != nullptr && extra->accumulate) ? &acc : nullptr;
    if (accp != nullptr) {
      const size_t ci_base = ci_before_extra;
      acc = [extra, ci_base](Elt *A, const Elt *alphal) {
        extra->accumulate(A, alphal, ci_base);
      };
    }
    lp_->prove(zkp.com_proof, tsp, ci, a.size(), &a[0], &lqc_[0], rsf_, f_,
               accp);
    phases.ligero = tsp.stats();

    log(INFO, "Prover Done: flag");
    profile.mark("ligero");
    return true;
  }

  // Fill proof with random pad values for a given circuit.
  void fill_pad(RandomEngine &rng) {
    for (size_t i = 0; i < c_.nl; ++i) {
      for (size_t j = 0; j < c_.logc; ++j) {
        for (size_t k = 0; k < 4; ++k) {
          if (k != 1) { // P(1) optimization
            Elt r = rng.elt(f_);
            pad_.l[i].cp[j].t_[k] = r;
            witness_.push_back(r);
          } else {
            pad_.l[i].cp[j].t_[k] = f_.zero();
          }
        }
      }
      for (size_t j = 0; j < c_.l[i].logw; ++j) {
        for (size_t h = 0; h < 2; ++h) {
          for (size_t k = 0; k < 3; ++k) {
            if (k != 1) { // P(1) optimization
              Elt r = rng.elt(f_);
              pad_.l[i].hp[h][j].t_[k] = r;
              witness_.push_back(r);
            } else {
              pad_.l[i].hp[h][j].t_[k] = f_.zero();
            }
          }
        }
      }
      for (size_t k = 0; k < 2; ++k) {
        Elt r = rng.elt(f_);
        pad_.l[i].wc[k] = r;
        witness_.push_back(r);
      }

      // Commit to product of pads for product proof.
      Elt rr = f_.mulf(pad_.l[i].wc[0], pad_.l[i].wc[1]);
      witness_.push_back(rr);
    }
  }

  // Packed layout: packed subfield elements, the zeros that make their rows
  // whole subfield rows, then the unpacked inputs (see zk/zk_packed.h).
  // Returns the committed subfield boundary.
  size_t commit_packed_inputs(const ZkProof<Field, Hash> &zkp,
                              const Dense<Field> &W) {
    constexpr size_t kPack = PackedLayout<Field>::kPack;
    layout_ = std::make_unique<PackedLayout<Field>>(c_, zkp.param.w);
    const PackedLayout<Field> &L = *layout_;
    witness_.assign(L.n_witness, f_.zero());
    for (size_t Y = 0; Y < L.group.size(); ++Y) {
      if (L.group[Y] == PackedLayout<Field>::kNone || L.alias_target[Y] != PackedLayout<Field>::kNone)
        continue;
      uint64_t u = 0;
      for (size_t i = 0; i < kPack; ++i) {
        const Elt &x = W.v_[kPack * Y + i];
        check((x == f_.zero()) | (x == f_.one()), "packed input is not a bit");
        u |= uint64_t(x == f_.one()) << i;
      }
      witness_[L.group[Y]] = f_.of_scalar(u);
    }
    for (size_t i = c_.npub_in; i < c_.ninputs; ++i) {
      if (L.map[i] != PackedLayout<Field>::kNone) {
        witness_[L.map[i]] = W.v_[i];
      }
    }
    start_pad_ = L.n_witness;
    lqc_.resize(ZkCommon<Field>::num_quadratic(c_));
    return L.boundary;
  }

  // sigma_k uniform, then the chain s_{k,j} = sigma_k^(2^j), 1 <= j <= k.
  void fill_packed_pads(RandomEngine &rng) {
    constexpr size_t kPack = PackedLayout<Field>::kPack;
    std::vector<Elt> sigma(kPack);
    for (size_t k = 0; k < kPack; ++k) {
      sigma[k] = rng.elt(f_);
      witness_.push_back(sigma[k]);
    }
    for (size_t k = 1; k < kPack; ++k) {
      Elt s = sigma[k];
      for (size_t j = 1; j <= k; ++j) {
        s = f_.mulf(s, s);
        witness_.push_back(s);
      }
    }
  }

  const Circuit<Field> &c_;
  const size_t n_witness_;
  size_t start_pad_ = 0;
  std::unique_ptr<PackedLayout<Field>> layout_;
  std::unique_ptr<ExtensionLayout<Field>> extension_layout_;
  std::vector<Elt> original_witness_;
  std::vector<Elt>
      extension_m_delta_; // adversarial test hook, empty in production
  std::vector<Elt> packed_m_delta_; // test hook, see ZkCommon::Packed
  const Field &f_;
  const ReedSolomonFactory &rsf_;
  Proof<Field> pad_;
  std::vector<Elt> witness_;
  std::vector<LigeroQuadraticConstraint> lqc_;
  std::unique_ptr<LigeroProver<Field, ReedSolomonFactory, Hash>> lp_;
};

} // namespace proofs

#endif // PRIVACY_PROOFS_ZK_LIB_ZK_ZK_PROVER_H_
