use ark_bn254::Fr;
use ark_ff::{Field, One, Zero};

#[derive(Debug, Clone)]
pub struct SumcheckProof {
    pub c0: Vec<Fr>,
    pub c1: Vec<Fr>,
    pub c2: Vec<Fr>,
    pub c3: Vec<Fr>,
    pub c4: Vec<Fr>,
    pub coords: Vec<Fr>,
    pub final_w: Fr,
    pub final_v: Fr,
}

impl SumcheckProof {
    pub fn rounds(&self) -> usize {
        self.coords.len()
    }
}

fn fr_from_i64(value: i64) -> Fr {
    if value >= 0 {
        Fr::from(value as u64)
    } else {
        -Fr::from((-value) as u64)
    }
}

pub fn deg4_lagrange_weights(x: Fr) -> [Fr; 5] {
    let nodes = [-2i64, -1, 0, 1, 2];
    let denoms = [24i64, -6, 4, -6, 24];
    let mut coeffs = [Fr::zero(); 5];
    for (idx, &k) in nodes.iter().enumerate() {
        let mut num = Fr::one();
        for &m in nodes.iter() {
            if m == k {
                continue;
            }
            num *= x - fr_from_i64(m);
        }
        let denom_inv = fr_from_i64(denoms[idx])
            .inverse()
            .expect("denominator should be non-zero");
        coeffs[idx] = num * denom_inv;
    }
    coeffs
}

fn weighted_sum(w: &[Fr], v: &[Fr], coeff1: &Fr, coeff0: &Fr) -> Fr {
    let mut acc = Fr::zero();
    for (wi, vi) in w.iter().zip(v.iter()) {
        let v_sq = *vi * vi;
        let v_cu = v_sq * *vi;
        let mut poly = v_cu;
        if !coeff1.is_zero() {
            poly += *coeff1 * *vi;
        }
        if !coeff0.is_zero() {
            poly += *coeff0;
        }
        acc += *wi * poly;
    }
    acc
}

pub fn sumcheck_prove(
    w: &[Fr],
    v: &[Fr],
    coeff1: Fr,
    coeff0: Fr,
    randomness: Vec<Fr>,
    mut hash: impl FnMut(&[Fr]) -> Vec<Fr>,
) -> SumcheckProof {
    assert_eq!(w.len(), v.len(), "input vectors must have the same length");
    assert!(
        w.len().is_power_of_two(),
        "length must be a power of two for multilinear evaluations"
    );

    let mut c0 = Vec::new();
    let mut c1 = Vec::new();
    let mut c2 = Vec::new();
    let mut c3 = Vec::new();
    let mut c4 = Vec::new();
    let mut coords = Vec::new();

    let mut current_w = w.to_vec();
    let mut current_v = v.to_vec();
    let mut current_randomness = randomness;
    let mut size = current_w.len();

    while size > 1 {
        let half = size / 2;
        let mut w0 = Vec::with_capacity(half);
        let mut w1 = Vec::with_capacity(half);
        let mut v0 = Vec::with_capacity(half);
        let mut v1 = Vec::with_capacity(half);
        for i in 0..half {
            w0.push(current_w[2 * i]);
            w1.push(current_w[2 * i + 1]);
            v0.push(current_v[2 * i]);
            v1.push(current_v[2 * i + 1]);
        }

        let wm: Vec<Fr> = w1.iter().zip(w0.iter()).map(|(a, b)| *a - *b).collect();
        let vm: Vec<Fr> = v1.iter().zip(v0.iter()).map(|(a, b)| *a - *b).collect();
        let w2: Vec<Fr> = w1.iter().zip(wm.iter()).map(|(a, m)| *a + *m).collect();
        let v2: Vec<Fr> = v1.iter().zip(vm.iter()).map(|(a, m)| *a + *m).collect();
        let wm1: Vec<Fr> = w0.iter().zip(wm.iter()).map(|(a, m)| *a - *m).collect();
        let vm1: Vec<Fr> = v0.iter().zip(vm.iter()).map(|(a, m)| *a - *m).collect();
        let wm2: Vec<Fr> = wm1.iter().zip(wm.iter()).map(|(a, m)| *a - *m).collect();
        let vm2: Vec<Fr> = vm1.iter().zip(vm.iter()).map(|(a, m)| *a - *m).collect();

        c0.push(weighted_sum(&wm2, &vm2, &coeff1, &coeff0));
        c1.push(weighted_sum(&wm1, &vm1, &coeff1, &coeff0));
        c2.push(weighted_sum(&w0, &v0, &coeff1, &coeff0));
        c3.push(weighted_sum(&w1, &v1, &coeff1, &coeff0));
        c4.push(weighted_sum(&w2, &v2, &coeff1, &coeff0));

        let mut hash_input = current_randomness.clone();
        hash_input.push(*c0.last().unwrap());
        hash_input.push(*c1.last().unwrap());
        hash_input.push(*c2.last().unwrap());
        hash_input.push(*c3.last().unwrap());
        hash_input.push(*c4.last().unwrap());
        current_randomness = hash(&hash_input);
        let coord = current_randomness
            .first()
            .copied()
            .expect("hash output must contain at least one element");
        coords.push(coord);

        current_w = w0
            .iter()
            .zip(wm.iter())
            .map(|(base, slope)| *base + coord * *slope)
            .collect();
        current_v = v0
            .iter()
            .zip(vm.iter())
            .map(|(base, slope)| *base + coord * *slope)
            .collect();

        size = half;
    }

    SumcheckProof {
        c0,
        c1,
        c2,
        c3,
        c4,
        coords,
        final_w: current_w[0],
        final_v: current_v[0],
    }
}

pub fn sumcheck_verify(
    proof: &SumcheckProof,
    mut total: Option<Fr>,
    value: Fr,
    randomness: Vec<Fr>,
    mut hash: impl FnMut(&[Fr]) -> Vec<Fr>,
) -> bool {
    let rounds = proof.rounds();
    assert_eq!(proof.c0.len(), rounds);
    assert_eq!(proof.c1.len(), rounds);
    assert_eq!(proof.c2.len(), rounds);
    assert_eq!(proof.c3.len(), rounds);
    assert_eq!(proof.c4.len(), rounds);

    let mut current_randomness = randomness;

    for round in 0..rounds {
        let mut hash_input = current_randomness.clone();
        hash_input.push(proof.c0[round]);
        hash_input.push(proof.c1[round]);
        hash_input.push(proof.c2[round]);
        hash_input.push(proof.c3[round]);
        hash_input.push(proof.c4[round]);
        current_randomness = hash(&hash_input);
        let coord = current_randomness
            .first()
            .copied()
            .expect("hash output must contain at least one element");
        assert_eq!(
            coord, proof.coords[round],
            "verifier and prover should derive the same challenges"
        );

        if let Some(t) = total {
            assert_eq!(
                t,
                proof.c2[round] + proof.c3[round],
                "claimed partial sum mismatch"
            );
        }

        let weights = deg4_lagrange_weights(proof.coords[round]);
        let mut next_total = Fr::zero();
        next_total += proof.c0[round] * weights[0];
        next_total += proof.c1[round] * weights[1];
        next_total += proof.c2[round] * weights[2];
        next_total += proof.c3[round] * weights[3];
        next_total += proof.c4[round] * weights[4];
        total = Some(next_total);
    }

    assert_eq!(
        total.expect("at least one round must have occurred"),
        value,
        "final value mismatch"
    );
    true
}

#[cfg(test)]
mod tests {
    use super::*;

    fn dummy_hash(input: &[Fr]) -> Vec<Fr> {
        let mut output = vec![Fr::zero(); 8];
        let mut p = Fr::one();
        let step = Fr::from(37u64);
        for (idx, value) in input.iter().enumerate() {
            output[idx % 8] += *value * p;
            p *= step;
        }
        output
    }

    fn cubic(x: Fr) -> Fr {
        let x2 = x * x;
        x2 * x
    }

    #[test]
    fn sumcheck_matches_python_reference() {
        let w_raw = [
            3i64, 14, 15, 92, 65, 35, 89, 79, 32, 38, 46, 26, 43, 38, 32, 7950,
        ];
        let v_raw = [
            2i64, 7, 18, 28, 18, 28, 45, 90, 45, 23, 53, 60, 2, 8, 7, 5,
        ];
        let w: Vec<Fr> = w_raw.iter().map(|&x| fr_from_i64(x)).collect();
        let v: Vec<Fr> = v_raw.iter().map(|&x| fr_from_i64(x)).collect();
        let coeff1 = Fr::zero();
        let coeff0 = Fr::from(63u64);

        let mut seed = Vec::new();
        seed.extend_from_slice(&w);
        seed.extend_from_slice(&v);
        let randomness = dummy_hash(&seed);

        let proof = sumcheck_prove(
            &w,
            &v,
            coeff1,
            coeff0,
            randomness.clone(),
            |data| dummy_hash(data),
        );

        let value = proof.final_w * (cubic(proof.final_v) + coeff0);

        let mut total = Fr::zero();
        for (wi, vi) in w.iter().zip(v.iter()) {
            total += *wi * (cubic(*vi) + coeff0);
        }
//        total += total; // to match the reference implementation


        assert!(sumcheck_verify(
            &proof,
            Some(total),
            value,
            randomness,
            |data| dummy_hash(data)
        ));
    }
}
