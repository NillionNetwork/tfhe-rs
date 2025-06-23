use super::*;
use rand::RngCore;

#[derive(Clone, Debug)]
pub struct PublicParams<G: Curve> {
    g_lists: GroupElements<G>,
}

impl<G: Curve> PublicParams<G> {
    pub fn from_vec(
        g_list: Vec<Affine<G::Zp, G::G1>>,
        g_hat_list: Vec<Affine<G::Zp, G::G2>>,
    ) -> Self {
        Self {
            g_lists: GroupElements::from_vec(g_list, g_hat_list),
        }
    }
}

#[derive(Clone, Debug)]
pub struct PublicCommit<G: Curve> {
    v_hat: G::G2,  // Commitment to μ
    c_hat: G::G2,  // Commitment to word
    k: usize,      // Start index of μ in word
    l: usize,      // Length of μ
}

#[derive(Clone, Debug)]
pub struct PrivateCommit<G: Curve> {
    r: G::Zp,      // Randomness for v_hat
    gamma: G::Zp,  // Randomness for c_hat
    word: Vec<u64>,  // The full binary vector word
}

#[derive(Clone, Debug)]
pub struct Proof<G: Curve> {
    pi: G::G1,     // The membership proof
}

pub fn crs_gen<G: Curve>(n: usize, rng: &mut dyn RngCore) -> PublicParams<G> {
    let alpha = G::Zp::rand(rng);
    PublicParams {
        g_lists: GroupElements::new(n, alpha),
    }
}

pub fn commit<G: Curve>(
    mu: u64,
    k: usize,
    l: usize,
    word: &[u64],
    public: &PublicParams<G>,
    rng: &mut dyn RngCore,
) -> (PublicCommit<G>, PrivateCommit<G>) {
    let g_hat = G::G2::GENERATOR;
    let n = word.len();
    let w = OneBased::new_ref(&*word);

    // Generate randomness
    let r = G::Zp::rand(rng);     // randomness for v_hat
    let gamma = G::Zp::rand(rng); // randomness for c_hat

    // Compute v_hat = g_hat^r * g_hat_1^μ
    let v_hat = g_hat.mul_scalar(r) + 
        G::G2::projective(public.g_lists.g_hat_list[1]).mul_scalar(G::Zp::from_u64(mu));

    // Compute c_hat = g_hat^γ * ∏ g_hat_j^word_j
    let mut c_hat = g_hat.mul_scalar(gamma);
    for j in 1..n+1 { // w and g_hat_list start at index 1 and finish at index n
        if w[j] != 0 {
            c_hat += G::G2::projective(public.g_lists.g_hat_list[j]);
        }
    }

    (
        PublicCommit { v_hat, c_hat, k, l },
        PrivateCommit { r, gamma, word: word.to_vec() },
    )
}

pub fn prove<G: Curve>(
    public: (&PublicParams<G>, &PublicCommit<G>),
    private: &PrivateCommit<G>,
    rng: &mut dyn RngCore,
) -> Proof<G> {
    let _ = rng;
    let &PublicCommit { k, l, .. } = public.1;
    let &PrivateCommit { r, gamma, ref word, .. } = private;
    let g_list = &public.0.g_lists.g_list;
    let n = word.len();
    let w = OneBased::new_ref(&*word);

    // Compute π = g_n^-r * ∏(g_{n+1-i}^γ * ∏_{j≠i} g_{n+1+j-i}^word_j)^{2^{i-1-k}}
    let mut pi = G::G1::projective(g_list[n]).mul_scalar(-r);

    for i in k+1..(k+1 + l) { // i in L = {k+1, ..., k+l}
        let mut term = G::G1::projective(g_list[n + 1 - i]).mul_scalar(gamma);
        
        // Compute ∏_{j≠i} g_j^word_j
        for j in 1..n+1 { // j in {1, ..., n}
            if j != i && w[j] != 0 {
                term += G::G1::projective(g_list[n + 1 - i + j]);
            }
        }

        // Raise to power 2^{i-1-k}
        let power = 1 << (i - 1- k);
        term = term.mul_scalar(G::Zp::from_u64(power as u64));
        
        pi += term;
    }

    Proof { pi }
}

#[allow(clippy::result_unit_err)]
pub fn verify<G: Curve>(
    proof: &Proof<G>,
    public: (&PublicParams<G>, &PublicCommit<G>),
) -> Result<(), ()> {
    let e = G::Gt::pairing;
    let &PublicCommit { v_hat, c_hat, k, l, .. } = public.1;
    let g_list = &public.0.g_lists.g_list;
    let n = public.0.g_lists.message_len;

    // Compute left side: e(∏ g_{n+1-i}^{2^{i-1-k}}, c_hat)
    let mut left_side = G::G1::ZERO;
    for i in k+1..(k+1 + l) { // i in L = {k+1, ..., k+l}
        let power = 1 << (i - 1 - k);
        left_side += G::G1::projective(g_list[n + 1 - i]).mul_scalar(G::Zp::from_u64(power as u64));
    }
    let left_side = e(left_side, c_hat);

    // Compute right side: e(g_n, v_hat) * e(π, g_hat)
    let right_side = e(G::G1::projective(g_list[n]), v_hat) + e(proof.pi, G::G2::GENERATOR);

    if left_side == right_side {
        Ok(())
    } else {
        Err(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use rand::rngs::StdRng;
    use rand::{Rng, SeedableRng};

    #[test]
    fn test_membership() {
        let rng = &mut StdRng::seed_from_u64(0);

        // Parameters
        let n = 16;  // Total length of word
        let k = 4;   // Start index of μ in word
        let l = 8;   // Length of μ
        println!("n: {}, k: {}, l: {}", n, k, l);

        // Generate a random μ and its binary representation
        let max = (1u64 << l) - 1;
        let mu = rand::thread_rng().gen_range(0..=max);
        println!("mu: {}", mu);
        let mu_bits: Vec<u64> = (0..l).map(|i| (mu >> i) & 1).collect();
        println!("mu_bits: {:?}", mu_bits);


        // Generate a random binary vector word
        let mut word = vec![0u64; n];
        for i in 0..n {
            word[i] = rng.gen::<u64>() & 1;
        }
        // Insert μ's bits into word at position k
        for i in 0..l {
            word[k + i] = mu_bits[i];
        }
        println!("word: {:?}", word);
        
        // Generate CRS and commitments
        let public_params = crs_gen::<crate::curve_api::Bls12_446>(n, rng);
        let (public_commit, private_commit) = commit(mu, k, l, &word, &public_params, rng);

        // Generate and verify proof
        let proof = prove((&public_params, &public_commit), &private_commit, rng);
        assert!(verify(&proof, (&public_params, &public_commit)).is_ok());

        // Test with invalid μ
        let invalid_mu = (mu + 1) % (1 << l);
        let (invalid_public_commit, invalid_private_commit) = 
            commit(invalid_mu, k, l, &word, &public_params, rng);
        let invalid_proof = prove(
            (&public_params, &invalid_public_commit),
            &invalid_private_commit,
            rng,
        );
        assert!(verify(&invalid_proof, (&public_params, &public_commit)).is_err());
    }
} 