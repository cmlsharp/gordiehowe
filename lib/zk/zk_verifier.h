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
// Modified 2026 by Chad Sharp and Paul Grubbs: templated on Hash with Ligero mode, packed and extension layouts, subfield-row checks, and split recv_ldt

#ifndef PRIVACY_PROOFS_ZK_LIB_ZK_ZK_VERIFIER_H_
#define PRIVACY_PROOFS_ZK_LIB_ZK_ZK_VERIFIER_H_

#include <stddef.h>

#include <memory>
#include <vector>

#include "arrays/dense.h"
#include "ligero/ligero_param.h"
#include "ligero/ligero_verifier.h"
#include "random/transcript.h"
#include "sumcheck/circuit.h"
#include "util/log.h"
#include "util/prover_profile.h"
#include "zk/zk_common.h"
#include "zk/zk_packed.h"
#include "zk/zk_proof.h"

namespace proofs {
// ZK Verifier
//
// Verifies a zk proof. See note in the prover for the design.
// To verify a proof, instantiate the class, then call recv_commitment with
// the commitment, and finally call verify. It is possible to receive several
// commitments, or run other protocols between the recv_commitment and verify
// calls. This allows composing two proofs in parallel.
// To support this, the interface to both accepts a raw Transcript.
// Hash is the protocol hash policy (util/crypto.h) of the commitment and
// the transcript.
template <class Field, class RSFactory, class Hash = UpstreamHash>
class ZkVerifier {
  using Elt = typename Field::Elt;

public:
  explicit ZkVerifier(const Circuit<Field> &c, const RSFactory &rsf,
                      size_t rate, size_t nreq, const Field &F)
      : ZkVerifier(c, rsf, rate, nreq, /*block_enc=*/0, F) {}

  // BLOCK_ENC = 0 searches powers of two, as ZkProof does.  MODE: the
  // Ligero options (LigeroMode), as the prover's.
  explicit ZkVerifier(const Circuit<Field> &c, const RSFactory &rsf,
                      size_t rate, size_t nreq, size_t block_enc,
                      const Field &F, LigeroMode mode = {})
      : circ_(c), n_witness_(c.ninputs - c.npub_in),
        param_(ZkCommon<Field>::template make_param<Hash>(c, rate, nreq,
                                                          block_enc, mode)),
        lqc_(ZkCommon<Field>::num_quadratic(c)), rsf_(rsf), f_(F) {
    size_t start_pad = n_witness_;
    if (ZkCommon<Field>::packed(c)) {
      if constexpr (Field::kCharacteristicTwo) {
        layout_ = std::make_unique<PackedLayout<Field>>(c, param_.w);
        start_pad = layout_->n_witness;
        subfield_wrows_ = layout_->subfield_wrows;
        ZkCommon<Field>::setup_packed_lqc(c, *layout_, lqc_);
      }
    }
    start_pad_ = start_pad;
    ZkCommon<Field>::setup_lqc(c, lqc_, start_pad_);
    ZkCommon<Field>::setup_input_products(c, layout_.get(), lqc_);
    if (ZkCommon<Field>::extension_packed(c)) {
      extension_layout_ = std::make_unique<ExtensionLayout<Field>>(
          ZkCommon<Field>::extension_layout(c, param_.w));
      extension_layout_->remap(lqc_);
      subfield_wrows_ = extension_layout_->prefix / param_.w;
    }
  }

  // False leaves the subfield rows to the caller: Ligero then checks no row
  // for subfield membership, and the caller checks rows
  // [0, subfield_rows()) of the opened columns itself (GordieHowe's
  // subfield step, gordiehowe/packing.h).
  bool enforce_subfield_rows = true;
  size_t subfield_rows() const { return subfield_wrows_; }
  const LigeroParam<Field, Hash> &param() const { return param_; }

  void recv_commitment(const ZkProof<Field, Hash> &zk,
                       BasicTranscript<Hash> &t) const {
    log(INFO, "verifier: recv commit");
    if (extension_layout_)
      extension_layout_->bind(t);
    LigeroVerifier<Field, RSFactory, Hash>::receive_commitment(zk.com, t);
  }

  // List-radius Ligero: the low-degree round after every commitment
  // (ZkProver::ldt_commit); verify() then uses its challenge.
  void recv_ldt(const ZkProof<Field, Hash> &zk, BasicTranscript<Hash> &t) {
    LigeroVerifier<Field, RSFactory, Hash>::receive_ldt(param_, zk.com_proof,
                                                        t, u_ldt_, f_);
    have_ldt_ = true;
  }

  // Verifies the proof.
  // `extra` must match the prover's callback exactly (see ZkProver::prove).
  bool verify(
      const ZkProof<Field, Hash> &zk, const Dense<Field> &pub,
      BasicTranscript<Hash> &tv,
      const typename ZkCommon<Field>::ExtraConstraints *extra = nullptr) const {
    log(INFO, "verifier: verify");
    profiling::Session profile("verify", typeid(Field).name(), circ_.ninputs,
                                circ_.nl);

    // The statement opens the transcript (absorb_statement in zk_common.h).
    ZkCommon<Field>::initialize_sumcheck_fiat_shamir(tv, circ_, f_);

    // Derive constraints on the witness.
    using Llc = LigeroLinearConstraint<Field>;
    std::vector<Llc> A;
    std::vector<Elt> b;
    size_t ci_before_extra = 0;
    std::vector<Elt> m = zk.packed_m;
    typename ZkCommon<Field>::Packed pk;
    pk.layout = layout_.get();
    pk.m = &m;
    if (ZkCommon<Field>::packed(circ_)) {
      if constexpr (Field::kCharacteristicTwo) {
        if ((extra != nullptr && !extra->packed_coordinates) ||
            m.size() != PackedLayout<Field>::kPack) {
          log(INFO, "verify done: malformed packed proof");
          return false;
        }
      }
    }
    size_t cn = ZkCommon<Field>::verifier_constraints(
        circ_, pub, zk.proof, /*aux=*/nullptr, A, b, tv, start_pad_, f_, extra,
        &ci_before_extra, &pk);

    profile.mark("constraints");
    if (extension_layout_) {
      if (zk.extension_m.size() != ExtensionTraits<Field>::degree)
        return false;
      ExtensionForms<Field> forms(*extension_layout_, cn, A, b, tv, extra,
                                  ci_before_extra, f_);
      tv.write(zk.extension_m.data(), 1, zk.extension_m.size(), f_);
      auto rhs = forms.rhs(zk.extension_m, f_);
      typename LigeroVerifier<Field, RSFactory, Hash>::Accumulator acc =
          [&](Elt *out, const Elt *alpha) {
            forms.accumulate(out, alpha, *extension_layout_, f_);
          };
      const char *why = "";
      profile.mark("extension_claim");
      bool ok = LigeroVerifier<Field, RSFactory, Hash>::verify(
          &why, param_, zk.com, zk.com_proof, tv, rhs.size(), 0, nullptr,
          rhs.data(), lqc_.data(), rsf_, f_, &acc,
          enforce_subfield_rows ? subfield_wrows_ : 0, ldt());
      profile.mark("ligero");
      return ok;
    }

    const char *why = "";
    typename LigeroVerifier<Field, RSFactory, Hash>::Accumulator acc;
    const auto *accp = (extra != nullptr && extra->accumulate) ? &acc : nullptr;
    if (accp != nullptr) {
      const size_t ci_base = ci_before_extra;
      acc = [extra, ci_base](Elt *Av, const Elt *alphal) {
        extra->accumulate(Av, alphal, ci_base);
      };
    }
    bool ok = LigeroVerifier<Field, RSFactory, Hash>::verify(
        &why, param_, zk.com, zk.com_proof, tv, cn, A.size(), &A[0], &b[0],
        &lqc_[0], rsf_, f_, accp, enforce_subfield_rows ? subfield_wrows_ : 0,
        ldt());

    profile.mark("ligero");
    log(INFO, "verify done: %s", why);
    return ok;
  }

private:
  // The low-degree challenge of recv_ldt, if it ran.
  const std::vector<Elt> *ldt() const { return have_ldt_ ? &u_ldt_ : nullptr; }

  const Circuit<Field> &circ_;
  const size_t n_witness_;
  const LigeroParam<Field, Hash> param_;
  std::vector<LigeroQuadraticConstraint> lqc_;
  std::unique_ptr<PackedLayout<Field>> layout_;
  std::unique_ptr<ExtensionLayout<Field>> extension_layout_;
  size_t start_pad_ = 0;
  size_t subfield_wrows_ = 0; // enforced only for packed circuits
  std::vector<Elt> u_ldt_;
  bool have_ldt_ = false;
  const RSFactory &rsf_;
  const Field &f_;
};
} // namespace proofs

#endif // PRIVACY_PROOFS_ZK_LIB_ZK_ZK_VERIFIER_H_
