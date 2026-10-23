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
// Modified 2026 by Chad Sharp and Paul Grubbs: Hash-templated transcript helpers, LDT challenge draw of ldt_reps * nldt elements, point-budget extension for constraint challenges

#ifndef PRIVACY_PROOFS_ZK_LIB_LIGERO_LIGERO_TRANSCRIPT_H_
#define PRIVACY_PROOFS_ZK_LIB_LIGERO_LIGERO_TRANSCRIPT_H_

#include <stddef.h>

#include <array>

#include "ligero/ligero_param.h"
#include "random/transcript.h"

namespace proofs {
template <class Field>
class LigeroTranscript {
 public:
  using Elt = typename Field::Elt;

  template <class Hash>
  static void write_commitment(const LigeroCommitment<Field, Hash>& commitment,
                               BasicTranscript<Hash>& ts) {
    ts.write(commitment.root.data, commitment.root.kLength);
  }

  // The low-degree challenges: LDT_REPS x NLDT elements, repetition-major,
  // in one draw (one verifier message).
  template <class Hash>
  static void gen_uldt(Elt u[/*ldt_reps, nldt*/],
                       const LigeroParam<Field, Hash>& p,
                       BasicTranscript<Hash>& ts, const Field& F) {
    ts.elt(u, p.mode.ldt_reps * p.nldt, F);
  }

  template <class Hash>
  static void gen_alphal(size_t nl, Elt alpha[/*nl*/],
                         BasicTranscript<Hash>& ts, const Field& F) {
    if (nl > 0) {
      // One challenge per linear row: the point grows with the rows.
      ts.extend_point_budget_for(nl, F);
      ts.elt(alpha, nl, F);
    }
  }

  template <class Hash>
  static void gen_alphaq(std::array<Elt, 3> alpha[/*nq*/],
                         const LigeroParam<Field, Hash>& p,
                         BasicTranscript<Hash>& ts, const Field& F) {
    if (p.nq > 0) {
      // Three challenges per quadratic constraint, from the linear test's
      // point: the point grows with them as with its rows.
      ts.extend_point_budget_for(3 * p.nq, F);
      ts.elt(&alpha[0][0], 3 * p.nq, F);
    }
  }

  template <class Hash>
  static void gen_uquad(Elt u[/*nqtriples*/],
                        const LigeroParam<Field, Hash>& p,
                        BasicTranscript<Hash>& ts, const Field& F) {
    if (p.nqtriples > 0) {
      // One challenge per row triple of the quadratic test, from the same
      // point as alphal and alphaq.
      ts.extend_point_budget_for(p.nqtriples, F);
      ts.elt(u, p.nqtriples, F);
    }
  }

  // Choose p.nreq distinct naturals in [0, p.block_enc - p.dblock)
  template <class Hash>
  static void gen_idx(size_t idx[/*p.nreq*/],
                      const LigeroParam<Field, Hash>& p,
                      BasicTranscript<Hash>& ts, const Field& F) {
    check(p.block_enc >= p.dblock, "p.block_enc >= p.dblock");
    check(p.block_enc - p.dblock >= p.nreq, "p.block_enc - p.dblock >= p.nreq");
    ts.choose(idx, p.block_enc - p.dblock, p.nreq);
  }
};
}  // namespace proofs

#endif  // PRIVACY_PROOFS_ZK_LIB_LIGERO_LIGERO_TRANSCRIPT_H_
