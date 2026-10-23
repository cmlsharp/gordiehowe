// Copyright 2026 Chad Sharp and Paul Grubbs
// SPDX-License-Identifier: Apache-2.0

//! Timing and correctness driver (longfellow-zk benchmarks/voleith).
//!
//!   pop_bench pop FIXTURE_DIR WARMUPS TRIALS
//!     The proof of knowledge of a 32-byte message and an ML-DSA-44 signature
//!     on it under a public key: the paper's masked circuit with r the private
//!     message and the public H(M, pi_1) zero (com = r = M), on the fixture
//!     pk.hex / msg.hex / sig.hex. Per trial:
//!       P      phase 1 (compute_commitment_private_message: VOLE generation
//!              for F2, commitment to M) + phase 2 (prove: witness generation
//!              and the rest of the proof), one timed region
//!       P1     phase 1 alone (the paper's Sign1 position)
//!       P2     phase 2 alone (the paper's Sign3)
//!       V      prep + Vcore, one timed region
//!       prep   public inputs from pk: pkDecode, tr, ExpandA, t1 (and the
//!              zero H(M, pi_1))
//!       Vcore  verify_masked on those public inputs
//!     then the correctness checks (valid; one flipped bit of z; one flipped
//!     bit of the message).
//!
//!   pop_bench published WARMUPS TRIALS
//!     The paper's blind signature as published (Masked), with benches/
//!     bmldsa.rs's key, message and transcript: Sign1 (compute_commitment),
//!     Sign3 (prove) and Verify on the prover's public inputs.
//!
//! The configuration is the paper's Table 4 row: general ORAM, theta_max =
//! 213, B = 8 (ThreeBits), the (3,0) SHAKE256 plan (Fwd3), edaBitE
//! (ExponentCheck), CRT masks.
use blind_mldsa::{
    BlindMLDSA, CommitmentMode, IssuerHidingMode, MLDSALengthCheck, ORAMMode, ShakeSegmentPlan,
    mldsa::{
        constants::{K, L, N, Q},
        reference::{self, DecodedPk},
    },
    protocol::proof::BlindMLDSAProof,
};
use swanky_field_binary::F2;
use swanky_field_f23p::Fq;
use merlin::Transcript;
use ml_dsa::{KeyExport, KeyInit, Keypair, MlDsa44, Seed, Signer, SigningKey};
use rand::thread_rng;
use schmivitz::{parameters::FullFieldMaskMethod, proof::EdabitVariant};
use std::panic::{AssertUnwindSafe, catch_unwind};
use std::time::Instant;

fn config(commitment_type: CommitmentMode) -> BlindMLDSA {
    BlindMLDSA {
        version: MLDSALengthCheck::ThreeBits,
        segment_plan: ShakeSegmentPlan::Fwd3,
        oram_mode: ORAMMode::GeneralORAM,
        maximal_iterations_oram: 213,
        commitment_type,
        issuer_hiding_mode: IssuerHidingMode::NoHiding,
        mask_method: FullFieldMaskMethod::Crt,
        edabit_variant: EdabitVariant::ExponentCheck,
    }
}

fn read_hex(path: &str) -> Vec<u8> {
    let s = std::fs::read_to_string(path).expect("read fixture");
    let s = s.trim();
    (0..s.len() / 2)
        .map(|i| u8::from_str_radix(&s[2 * i..2 * i + 2], 16).expect("hex"))
        .collect()
}

fn ms(t: Instant) -> f64 {
    t.elapsed().as_secs_f64() * 1000.0
}

const LABEL: &[u8] = b"longfellow-zk voleith-mldsa pop";

/// Both phases of the proof; returns the proof and the phase times (ms).
fn prove_pop(
    blind: &BlindMLDSA,
    pk: &[u8],
    sig: &[u8],
    msg: &[u8; 32],
) -> Result<(BlindMLDSAProof, f64, f64), String> {
    let transcript = Transcript::new(LABEL);
    let t = Instant::now();
    let state = blind
        .compute_commitment_private_message(msg, &mut transcript.clone(), &mut thread_rng())
        .map_err(|e| format!("phase 1: {e:?}"))?;
    let p1 = ms(t);
    let t = Instant::now();
    let (proof, _) = blind
        .prove(state, pk, sig, msg, &mut transcript.clone(), &mut thread_rng())
        .map_err(|e| format!("phase 2: {e:?}"))?;
    Ok((proof, p1, ms(t)))
}

/// The verifier's public inputs from pk alone: `tr` and the zero `H(M, pi_1)`
/// over F2; `Â` column major (`(j*K + i)*N + n`, as `public_fq_inputs` lays it
/// out for the prover) and `t1` over Fq. `public_inputs_from_pk_masked` emits
/// `Â` row major, which the circuit reads as the transpose (K = L = 4 hides
/// the mismatch from the types), so the verifier rejects with it.
fn public_inputs(pk: &[u8]) -> (Vec<F2>, Vec<Fq>) {
    let DecodedPk { rho, t1, tr } = reference::decode_pk(pk).expect("pk");
    let a_hat = reference::expand_a(&rho);
    let mut f2 = Vec::with_capacity(64 * 8 + 32 * 8);
    for byte in tr.iter().chain([0u8; 32].iter()) {
        for j in 0..8 {
            f2.push(F2::from((byte >> j) & 1 == 1));
        }
    }
    let to_fq = |v: i64| Fq::try_from(v.rem_euclid(Q) as u32).unwrap();
    let mut fq = Vec::with_capacity(N * K * L + N * K);
    for j in 0..L {
        for row in a_hat.iter().take(K) {
            fq.extend(row[j].iter().map(|&v| to_fq(v)));
        }
    }
    for poly in t1.iter() {
        fq.extend(poly.iter().map(|&v| to_fq(v)));
    }
    (f2, fq)
}

/// "accepted", "rejected: ...", "prover error: ..." or "prover panicked".
fn outcome(blind: &BlindMLDSA, pk: &[u8], sig: &[u8], msg: &[u8; 32]) -> String {
    let r = catch_unwind(AssertUnwindSafe(|| match prove_pop(blind, pk, sig, msg) {
        Err(e) => format!("prover error: {e}"),
        Ok((proof, _, _)) => {
            let (pf2, pfq) = public_inputs(pk);
            match blind.verify(&proof, &pf2, &pfq, &mut Transcript::new(LABEL)) {
                Ok(()) => "accepted".to_string(),
                Err(e) => format!("rejected: {e:?}"),
            }
        }
    }));
    r.unwrap_or_else(|_| "prover panicked".to_string())
}

fn run_pop(dir: &str, warmups: usize, trials: usize) {
    let blind = config(CommitmentMode::Masked);
    let pk = read_hex(&format!("{dir}/pk.hex"));
    let sig = read_hex(&format!("{dir}/sig.hex"));
    let msg: [u8; 32] = read_hex(&format!("{dir}/msg.hex")).try_into().expect("32-byte msg");
    let threads = std::env::var("RAYON_NUM_THREADS").unwrap_or_else(|_| "default".into());
    if std::env::var("BB_DIAG").is_ok() {
        let transcript = Transcript::new(LABEL);
        let state = blind
            .compute_commitment_private_message(&msg, &mut transcript.clone(), &mut thread_rng())
            .unwrap();
        let (proof, inputs) = blind
            .prove(state, &pk, &sig, &msg, &mut transcript.clone(), &mut thread_rng())
            .unwrap();
        let (pf2, pfq) = public_inputs(&pk);
        println!(
            "DIAG f2_eq={} fq_eq={} f2_len={} {}",
            pf2 == inputs.public_f2,
            pfq == inputs.public_fq,
            pf2.len(),
            inputs.public_f2.len()
        );
        let r = blind.verify(&proof, &inputs.public_f2, &inputs.public_fq, &mut transcript.clone());
        println!("DIAG verify_with_prover_inputs={:?}", r.is_ok());
        return;
    }
    for r in 0..warmups + trials {
        let t = Instant::now();
        let (proof, p1, p2) = prove_pop(&blind, &pk, &sig, &msg).expect("proving failed");
        let p = ms(t);
        let t = Instant::now();
        let (pf2, pfq) = public_inputs(&pk);
        let prep = ms(t);
        let t1 = Instant::now();
        let ok = blind.verify(&proof, &pf2, &pfq, &mut Transcript::new(LABEL)).is_ok();
        let vcore = ms(t1);
        let v = ms(t);
        println!(
            "BB_TRIAL mode=pop r={r} warm={} rayon_threads={threads} P={p:.3} P1={p1:.3} \
             P2={p2:.3} V={v:.3} prep={prep:.3} Vcore={vcore:.3} bytes={} ok={}",
            u8::from(r < warmups),
            proof.proof_size_estimate(),
            u8::from(ok)
        );
        assert!(ok, "verification failed");
    }
    println!("BB_CHECK case=valid outcome={}", outcome(&blind, &pk, &sig, &msg));
    // One flipped bit of z: bit 0 of z's first byte (after the 32-byte c_tilde).
    let mut bad_sig = sig.clone();
    bad_sig[32] ^= 1;
    println!("BB_CHECK case=z-bit outcome={}", outcome(&blind, &pk, &bad_sig, &msg));
    let mut bad_msg = msg;
    bad_msg[0] ^= 1;
    println!("BB_CHECK case=msg-bit outcome={}", outcome(&blind, &pk, &sig, &bad_msg));
}

fn run_published(warmups: usize, trials: usize) {
    let blind = config(CommitmentMode::Masked);
    let transcript = Transcript::new(b"Happy Benchmarking.");
    let mut seed = Seed::default();
    seed.copy_from_slice(&[7u8; 32]);
    let sk = SigningKey::<MlDsa44>::new(&seed);
    let vk = sk.verifying_key().to_bytes().to_vec();
    let message = "We benchmarks our blind mldsa construction.";
    let threads = std::env::var("RAYON_NUM_THREADS").unwrap_or_else(|_| "default".into());
    for r in 0..warmups + trials {
        let t = Instant::now();
        let (state, com) =
            blind.compute_commitment(message.to_owned(), &mut transcript.clone(), &mut thread_rng());
        let sign1 = ms(t);
        let sig = sk.sign(&com).encode().to_vec();
        let t = Instant::now();
        let (proof, inputs) = blind
            .prove(state, &vk, &sig, &com, &mut transcript.clone(), &mut thread_rng())
            .expect("proving failed");
        let sign3 = ms(t);
        let t = Instant::now();
        let ok = blind
            .verify(&proof, &inputs.public_f2, &inputs.public_fq, &mut transcript.clone())
            .is_ok();
        let v = ms(t);
        println!(
            "BB_TRIAL mode=published r={r} warm={} rayon_threads={threads} Sign1={sign1:.3} \
             Sign3={sign3:.3} V={v:.3} bytes={} ok={}",
            u8::from(r < warmups),
            proof.proof_size_estimate(),
            u8::from(ok)
        );
        assert!(ok, "verification failed");
    }
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    // The circuits need a large stack (README: RUST_MIN_STACK=536870912).
    let h = std::thread::Builder::new()
        .stack_size(1 << 30)
        .spawn(move || match args.get(1).map(String::as_str) {
            Some("pop") => run_pop(&args[2], args[3].parse().unwrap(), args[4].parse().unwrap()),
            Some("published") => run_published(args[2].parse().unwrap(), args[3].parse().unwrap()),
            _ => panic!("usage: pop_bench pop DIR W T | published W T"),
        })
        .expect("spawn");
    h.join().expect("driver thread");
}
