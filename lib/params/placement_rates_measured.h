// Copyright 2026 Chad Sharp and Paul Grubbs
// SPDX-License-Identifier: Apache-2.0
//
// Generated from a rate measurement; do not edit.
//
// Run: a 128-core AMD EPYC 9754 host, 2026-10-15T07:16:20Z, governor
// performance on cores 64-97, 15 proofs per point after 2 warm-ups, 3 rounds,
// instance counts 2048,4096,8192,16384 (triples
// 1024,2048,3072,4096,5120,6144,7168,8192).

#ifndef PRIVACY_PROOFS_ZK_LIB_PARAMS_PLACEMENT_RATES_MEASURED_H_
#define PRIVACY_PROOFS_ZK_LIB_PARAMS_PLACEMENT_RATES_MEASURED_H_

#include <type_traits>

#include "algebra/fp14_n.h"
#include "algebra/fp24_6.h"
#include "algebra/fp_goldilocks.h"
#include "algebra/fp_goldilocks4.h"
#include "algebra/fp_native_wide.h"
#include "algebra/fp_p128.h"
#include "ec/p256.h"
#include "gf2k/gf2_128.h"
#include "gf2k/gf2_256.h"
#include "gordiehowe/compiler/placement_rates.h"

namespace proofs::param_sets {

// The placement rule's rates per field (gordiehowe/compiler/placement.h): what
// a committed coordinate, a GKR quad term, a quadratic triple and a batch of
// each first-round evaluator, degree and skip width cost in a domain over F, in
// microseconds of commit + prove + verify, fitted from placement_test's
// DISABLED_Rates, and the packing time of each packing-tree chain (stage),
// prover plus verifier, as fixed + coord N + other M, fitted from
// tree_cost_test's DISABLED_Rates. Constants,
// so plans are reproducible. Each fit predicts every measured point's excess
// over its reference within 10 %; no rate is derived or entered by
// hand.
template <class F>
gordiehowe::compiler::PlacementRates placement_rates() {
  using R = gordiehowe::compiler::PlacementRates;
  using E = gordiehowe::compiler::BatchEval;
  R r;
  r.source = "benchmarks/2026-10-15-rates-v2";
  if constexpr (std::is_same_v<F, Fp24_6>) {
    // narrow.ml-dsa
    r.field = "Fp24_6";
    r.commit_full = 3.05175;
    r.commit_sub = 1.08975;
    r.gkr_term = 0.355948;
    r.triple = 1.01045;
    r.triple_row = 1647.93;
    r.triple_fixed = -118.789;
    // The batch rates per evaluator (op_counts.h): {evaluator, fixed, mul,
    // add, mac, lane_lookup, lane_mul, lane_term, lin,
    // map_mul, map_add, map_mac, region}
    r.batch = {
        {E::kSubfield, 167.254, 0.018832, 0.0112295, 0.106641, 0, 0, 0, 0.0518123,
         0.018832, 0.0112295, 0.106641, 0},
    };
    // The packing chains: {chain, prover fixed, coord, other, verifier fixed,
    // coord, other}
    r.stage.chains = {
        {{1, 2, 6}, 7.67521, 0.205296, 0.0533888, 1.32001, 0.144943, 0.0466573},
        {{1, 3, 6}, 12.6203, 0.19805, 0.0534677, -8.8727, 0.147166, 0.0467019},
        {{1, 6}, 10.7752, 0.147794, 0.0271455, 0.185955, 0.118898, 0.0203109},
    };
  } else if constexpr (std::is_same_v<F, MlDsaField11>) {
    // wide.ml-dsa
    r.field = "MlDsaField11";
    r.commit_full = 7.14622;
    r.commit_sub = 2.39921;
    r.gkr_term = 0.961173;
    r.triple = -0.587028;
    r.triple_row = 3771.73;
    r.triple_fixed = 100.508;
    // The batch rates per evaluator (op_counts.h): {evaluator, fixed, mul,
    // add, mac, lane_lookup, lane_mul, lane_term, lin,
    // map_mul, map_add, map_mac, region}
    r.batch = {
        {E::kSubfield, 306.471, 0.0308901, 0.0580695, 0.108468, 0, 0, 0, 0.162763,
         0.0308901, 0.0580695, 0.108468, 0},
    };
  } else if constexpr (std::is_same_v<F, Fp14_9>) {
    // narrow.falcon
    r.field = "Fp14_9";
    r.commit_full = 3.53217;
    r.commit_sub = 1.39282;
    r.gkr_term = 0.530454;
    r.triple = 3.03727;
    r.triple_row = 1127.95;
    r.triple_fixed = -92.1736;
    // The batch rates per evaluator (op_counts.h): {evaluator, fixed, mul,
    // add, mac, lane_lookup, lane_mul, lane_term, lin,
    // map_mul, map_add, map_mac, region}
    r.batch = {
        {E::kSubfield, 195.379, 0.0297425, 0.0173311, 0.149002, 0, 0, 0, 0.0680724,
         0.0297425, 0.0173311, 0.149002, 0},
    };
    // The packing chains: {chain, prover fixed, coord, other, verifier fixed,
    // coord, other}
    r.stage.chains = {
        {{1, 3, 9}, 17.9114, 0.314421, 0.0770542, 2.19739, 0.234846, 0.0693269},
        {{1, 9}, 18.2902, 0.272138, 0.0382755, -4.12084, 0.229077, 0.0301035},
    };
  } else if constexpr (std::is_same_v<F, FalconField20>) {
    // wide.falcon
    r.field = "FalconField20";
    r.commit_full = 23.7902;
    r.commit_sub = 6.79669;
    r.gkr_term = 3.00929;
    r.triple = 65.2068;
    r.triple_fixed = 168.252;
    // The batch rates per evaluator (op_counts.h): {evaluator, fixed, mul,
    // add, mac, lane_lookup, lane_mul, lane_term, lin,
    // map_mul, map_add, map_mac, region}
    r.batch = {
        {E::kSubfield, 398.702, 0.220133, 0.0405882, 4.00711, 0, 0, 0, 0.87247,
         0.220133, 0.0405882, 4.00711, 0},
    };
    // The packing chains: {chain, prover fixed, coord, other, verifier fixed,
    // coord, other}
    r.stage.chains = {
        {{1, 2, 20}, -54.0529, 2.14109, 0.457685, -96.8833, 1.64859, 0.421057},
        {{1, 4, 20}, 7.43307, 1.74499, 0.456644, -7.55546, 1.36032, 0.420783},
        {{1, 5, 20}, 56.3392, 1.80247, 0.457015, -20.3912, 1.44041, 0.422206},
        {{1, 10, 20}, 88.3343, 2.4302, 0.45816, 20.444, 2.11144, 0.420786},
        {{1, 20}, 1.65369, 2.49508, 0.234328, -92.9009, 2.26129, 0.198394},
    };
  } else if constexpr (std::is_same_v<F, Fp64G2>) {
    // narrow.emulated
    r.field = "Fp64G2";
    r.commit_full = 1.01347;
    r.commit_sub = 0.622981;
    r.gkr_term = 0.133752;
    r.triple = 0.102317;
    r.triple_b = 1.09814e-05;
    r.triple_row = -46.9127;
    r.triple_row_b = 0.133911;
    r.triple_hash = 0.00728781;
    r.triple_fixed = -180.484;
    r.triple_fixed_b = 0.0320139;
    // The batch rates per evaluator (op_counts.h): {evaluator, fixed, mul,
    // add, mac, lane_lookup, lane_mul, lane_term, lin,
    // map_mul, map_add, map_mac, region}
    r.batch = {
        {E::kSubfield, 148.591, 0.00763234, 0.00332924, 0.081234, 0, 0, 0, 0.0310577,
         0.00763234, 0.00332924, 0.081234, 0},
    };
  } else if constexpr (std::is_same_v<F, Fp64G4>) {
    // wide.emulated
    r.field = "Fp64G4";
    r.commit_full = 2.7558;
    r.commit_sub = 1.20491;
    r.gkr_term = 0.388122;
    r.triple = 0.710266;
    r.triple_b = 9.73214e-06;
    r.triple_row = -229.956;
    r.triple_row_b = 0.257051;
    r.triple_hash = 0.124368;
    r.triple_fixed = 473.184;
    r.triple_fixed_b = -0.0183875;
    // The batch rates per evaluator (op_counts.h): {evaluator, fixed, mul,
    // add, mac, lane_lookup, lane_mul, lane_term, lin,
    // map_mul, map_add, map_mac, region}
    r.batch = {
        {E::kSubfield, 196.757, 0.0128218, 0.0267965, 0.0367226, 0, 0, 0, 0.084968,
         0.0128218, 0.0267965, 0.0367226, 0},
    };
    // The packing chains: {chain, prover fixed, coord, other, verifier fixed,
    // coord, other}
    r.stage.chains = {
        {{1, 2, 4}, -10.7277, 0.244207, 0.0577566, -4.05959, 0.180726, 0.0491549},
        {{1, 4}, 1.92994, 0.129285, 0.0293331, 2.81427, 0.0992014, 0.0213349},
    };
  } else if constexpr (std::is_same_v<F, GF2_128<>>) {
    // narrow.hash
    r.field = "GF2_128";
    r.commit_full = 1.13781;
    r.commit_sub = 0.333936;
    r.gkr_term = 0.0646066;
    r.triple = 0.0499641;
    r.triple_b = 4.13265e-06;
    r.triple_row = -163.869;
    r.triple_row_b = 0.0888343;
    r.triple_hash = 0.000411171;
    r.triple_fixed = 241.483;
    r.triple_fixed_b = -0.00048858;
    // The batch rates per evaluator (op_counts.h): {evaluator, fixed, mul,
    // add, mac, lane_lookup, lane_mul, lane_term, lin,
    // map_mul, map_add, map_mac, region}
    r.batch = {
        {E::kBitSliced, -52.321, 0.0121809, 0, 0, 0, 0, 0, 0,
         0.0114379, 0, 0, 0.0162061},
    };
    // The packing chains: {chain, prover fixed, coord, other, verifier fixed,
    // coord, other}
    r.stage.chains = {
        {{16, 32, 128}, -44.4126, 0.0959728, 0.0262463, -78.2318, 0.0370065, 0.0206035},
        {{16, 64, 128}, -43.8949, 0.0924757, 0.0266012, -48.7387, 0.0361082, 0.0199434},
        {{16, 128}, 143.71, 0.0890186, 0.0109124, 121.695, 0.035228, 0.00457767},
    };
  } else if constexpr (std::is_same_v<F, GF2_256<>>) {
    // wide.hash
    r.field = "GF2_256";
    r.commit_full = 2.26165;
    r.commit_sub = 0.765242;
    r.gkr_term = 0.108608;
    r.triple = -0.431616;
    r.triple_b = 2.71959e-05;
    r.triple_row = -118.722;
    r.triple_row_b = 0.122825;
    r.triple_hash = 0.125195;
    r.triple_fixed = 1248.27;
    r.triple_fixed_b = -0.0309402;
    // The batch rates per evaluator (op_counts.h): {evaluator, fixed, mul,
    // add, mac, lane_lookup, lane_mul, lane_term, lin,
    // map_mul, map_add, map_mac, region}
    r.batch = {
        {E::kBitSliced, -450.47, 0.0190255, 0, 0, 0, 0, 0, 0,
         0.0282798, 0, 0, 0.0231095},
    };
    // The packing chains: {chain, prover fixed, coord, other, verifier fixed,
    // coord, other}
    r.stage.chains = {
        {{16, 32, 256}, 136.588, 0.169306, 0.037218, 128.597, 0.0971027, 0.031622},
        {{16, 64, 256}, 113.293, 0.156363, 0.0381863, 283.531, 0.0859215, 0.0298172},
        {{16, 256}, 583.447, 0.193336, 0.0157084, 511.741, 0.131751, 0.00983188},
    };
  } else if constexpr (std::is_same_v<F, Fp256Base>) {
    // narrow.p256
    r.field = "Fp256Base";
    r.commit_full = 11.77;
    r.commit_sub = 11.7202;
    r.gkr_term = 0.336642;
    r.triple = 1.8833;
    r.triple_b = 1.20572e-05;
    r.triple_row = -1565.81;
    r.triple_row_b = 1.26471;
    r.triple_hash = -0.0530002;
    r.triple_fixed = -1226.12;
    r.triple_fixed_b = 0.368169;
  } else if constexpr (std::is_same_v<F, Fp128<>>) {
    // narrow.fp128
    r.field = "Fp128";
    r.commit_full = 1.0947;
    r.commit_sub = 1.09561;
    r.gkr_term = 0.125768;
    r.triple = 0.784874;
    r.triple_b = -1.94764e-07;
    r.triple_row = -89.8964;
    r.triple_row_b = 0.148391;
    r.triple_hash = -0.0258527;
    r.triple_fixed = -87.187;
    r.triple_fixed_b = -0.0201777;
    // The batch rates per evaluator (op_counts.h): {evaluator, fixed, mul,
    // add, mac, lane_lookup, lane_mul, lane_term, lin,
    // map_mul, map_add, map_mac, region}
    r.batch = {
        {E::kField, 184.717, 0.00309139, 0.00797398, 0.0733798, 0, 0, 0, 0.0571929,
         0.00309139, 0.00797398, 0.0733798, 0},
    };
  } else {
    return R{};
  }
  return r;
}

}  // namespace proofs::param_sets

#endif  // PRIVACY_PROOFS_ZK_LIB_PARAMS_PLACEMENT_RATES_MEASURED_H_
