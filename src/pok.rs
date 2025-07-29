use curve25519_dalek::RistrettoPoint;
use rand::{CryptoRng, RngCore};
use sha3::{Digest, Sha3_512};

use curve25519_dalek::ristretto::CompressedRistretto;
use curve25519_dalek::scalar::Scalar;

#[derive(Clone)]
pub struct Proof {
    pub r: CompressedRistretto,
    pub mu: Scalar,
}

// Generates a non-interactive zero-knowledge proof for the knowledge of a
// scalar `s` such that `p = s*g`. Label is some arbitrary data that can be
// attached to the proof, for example, to protect against replay attacks.
pub fn generate_pok<R: RngCore + CryptoRng>(
    rng: &mut R,
    p: &CompressedRistretto,
    s: &Scalar,
    label: &[u8],
) -> Proof {
    let k = Scalar::random(rng);
    let r = RistrettoPoint::mul_base(&k).compress();

    let c = hash_to_scalar(p, &r, label);

    let mu = k + *s * c;
    Proof { r, mu }
}

// Verifies a proof for the knowledge of a scalar `s` such that `p=g*s`. Also
// verifies that the proof is correctly labeled.
pub fn verify_pok(p: &CompressedRistretto, mu: &Proof, label: &[u8]) -> bool {
    let p_decompressed = match p.decompress() {
        Some(point) => point,
        None => return false,
    };
    let c = hash_to_scalar(p, &mu.r, label);
    let r_ver = RistrettoPoint::mul_base(&mu.mu) + p_decompressed * -c;
    mu.r == r_ver.compress()
}

fn hash_to_scalar(p: &CompressedRistretto, r: &CompressedRistretto, label: &[u8]) -> Scalar {
    let mut hasher = Sha3_512::new();
    hasher.update(p.to_bytes());
    hasher.update(r.to_bytes());
    hasher.update(label);
    Scalar::from_hash(hasher)
}
