// Copyright 2026 Chad Sharp and Paul Grubbs
// SPDX-License-Identifier: Apache-2.0

// GordieHowe: a batch's counted work (op_counts.h), by kind.

#ifndef PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_COMPILER_OP_COUNT_TYPES_H_
#define PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_COMPILER_OP_COUNT_TYPES_H_

#include <cstdint>

namespace proofs::gordiehowe::compiler {

// A batch's work by kind (op_counts.h): field operations, which
// CountingField tallies; the bit-sliced kernels' byte-lane steps (16 rows
// per step: table lookups and skip-subfield products) and the bit operand
// map's lane terms; and LIN, the table words its opening row's form spans.
// MAP_MUL, MAP_ADD and MAP_MAC are the operand map's share of MUL, ADD and
// MAC (its forward pass and adjoint, map_work), which the bit-sliced
// batches price apart from the skip's. REGION (bit-sliced batches): the
// coefficients the batch's claim row spans at the packing tree's root, W
// Frobenius forms over every group of the bit node's region (tree_zk.h's
// root: the row's parts), which the root combines and the verifier
// recomputes.
struct OpCounts {
  uint64_t mul = 0, add = 0, mac = 0, reduce = 0, inv = 0;
  uint64_t lane_lookup = 0, lane_mul = 0, lane_term = 0;
  uint64_t lin = 0;
  uint64_t map_mul = 0, map_add = 0, map_mac = 0;
  uint64_t region = 0;
  bool operator==(const OpCounts &o) const {
    return mul == o.mul && add == o.add && mac == o.mac &&
           reduce == o.reduce && inv == o.inv &&
           lane_lookup == o.lane_lookup && lane_mul == o.lane_mul &&
           lane_term == o.lane_term && lin == o.lin &&
           map_mul == o.map_mul && map_add == o.map_add &&
           map_mac == o.map_mac && region == o.region;
  }
};

}  // namespace proofs::gordiehowe::compiler

#endif  // PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_COMPILER_OP_COUNT_TYPES_H_
