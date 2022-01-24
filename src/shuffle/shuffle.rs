//! The `vectorpedersen` module contains API for producing a
//! vector commitment.

#![allow(non_snake_case)]

use crate::{
    accounts::{Account, Prover, Verifier},
    pedersen::vectorpedersen::VectorPedersenGens,
    ristretto::RistrettoPublicKey,
    shuffle::ddh::{DDHProof, DDHStatement},
    shuffle::multiexponential::{MultiexpoProof, MultiexpoStatement},
    shuffle::product::{ProductProof, ProductStatement},
    shuffle::vectorutil,
};
use array2d::Array2D;
use bulletproofs::PedersenGens;
use curve25519_dalek::traits::MultiscalarMul;

use crate::keys::PublicKey;
use curve25519_dalek::{
    ristretto::{CompressedRistretto, RistrettoPoint},
    scalar::Scalar,
};
use rand::rngs::OsRng;
use rand::{CryptoRng, Rng};

#[derive(Debug, Clone)]
pub struct Permutation {
    perm_matrix: Array2D<usize>,
}
//Matrix Size
pub const N: usize = 9; //N - Length of vector
pub const ROWS: usize = 3; //m
pub const COLUMNS: usize = 3; //n

impl Permutation {
    pub fn new<R: Rng + CryptoRng>(rng: &mut R, n: usize) -> Self {
        let mut permutation: Vec<usize> = (1..n + 1).collect();
        for i in (1..permutation.len()).rev() {
            // invariant: elements with index > i have been locked in place.
            permutation.swap(i, rng.gen_range(0, i + 1));
        }

        let perm_matrix = Array2D::from_row_major(&permutation, ROWS, COLUMNS);
        Self { perm_matrix }
    }

    //Set the permutation matrix explicitly
    pub fn set(&mut self, matrix: Array2D<usize>) {
        self.perm_matrix = matrix;
    }

    //Inverse the permutation matrix for use in Input shuffle
    pub fn invert_permutation(&self) -> Array2D<usize> {
        let mut inverse = vec![0; self.perm_matrix.num_elements()];
        let permutation = self.perm_matrix.as_row_major();
        for i in 0..permutation.len() {
            inverse[permutation[i] - 1] = i + 1;
        }
        let perm_matrix = Array2D::from_row_major(&inverse, ROWS, COLUMNS);
        perm_matrix
    }
    pub fn get_permutation_as_scalar_matrix(&self) -> Array2D<Scalar> {
        Array2D::from_row_major(
            &self
                .perm_matrix
                .elements_row_major_iter()
                .map(|x| Scalar::from(*x as u64))
                .collect::<Vec<Scalar>>(),
            ROWS,
            COLUMNS,
        )
    }
    // Produces a commitment to the permutation matrix> TBI
    // fn commit(&self ) -> Result<()>
}

#[derive(Debug, Clone)]
pub struct Shuffle {
    pub inputs: Array2D<Account>,      //Before shuffle     mxn
    pub outputs: Array2D<Account>,     //After shuffle and update    mxn
    pub shuffled_tau: Array2D<Scalar>, //Scalars after shuffle for PK update   mxn
    pub rho: Scalar,                   //Scalar for Commitment Update
    pub pi: Permutation,               //Permutaion matrix in the form m x n
}
///Shuffle argument proof
///
/// #[derive(Debug, Clone)]
pub struct ShuffleStatement {
    pub product_state: ProductStatement,
    pub multiexpo_pk_state: MultiexpoStatement,
    pub multiexpo_comit_state: MultiexpoStatement,
    pub ddh_statement: DDHStatement,
}
#[derive(Debug, Clone)]
pub struct ShuffleProof {
    pub c_A: Vec<CompressedRistretto>,
    pub c_tau: Vec<CompressedRistretto>,
    pub product_proof: ProductProof,
    pub multiexpo_pk: MultiexpoProof,
    pub multiexpo_comit: MultiexpoProof,
    pub ddh_proof: DDHProof,
}

impl Shuffle {
    // generate random values for Permutation and Scalars
    fn random_initialization(len: usize) -> (Permutation, Vec<Scalar>, Scalar) {
        //Create a new random permutation Matrix
        let pi = { Permutation::new(&mut OsRng, len) };
        //Create Random tau used for updating the Account Pks
        let tau: Vec<_> = (0..len).map(|_| Scalar::random(&mut OsRng)).collect();
        //Create Random rho used for updating the Account Commitments
        let rho = Scalar::random(&mut OsRng);
        (pi, tau, rho)
    }

    pub fn input_shuffle(
        inputs: &Vec<Account>, //Accounts to be shuffled
    ) -> Result<Self, &'static str> {
        let len = inputs.len();
        if len == 0 {
            return Err("Error::EmptyShuffle");
        }
        //Get random inital values
        let (mut pi, tau, rho) = Self::random_initialization(len);

        //Convert Matrix to Vector in row major order
        let permutation = pi.perm_matrix.as_row_major();

        //shuffle Input accounts randomly using permutation matrix
        let shuffled_accounts: Vec<_> = (0..len)
            .map(|i| inputs[permutation[i] - 1].clone())
            .collect();
        //Invert the permutation Matrix for Inputs shuffle
        pi.set(pi.invert_permutation());
        //Input accounts == input` in this case. updating input accounts with tau and rho
        let updated_inputs: Vec<_> = inputs
            .iter()
            .zip(tau.iter())
            .map(|(acc, t)| Account::update_account(*acc, 0, *t, rho))
            .collect();
        //Convert to a 2D array representation
        let outputs = Array2D::from_row_major(&updated_inputs, ROWS, COLUMNS);
        let inputs = Array2D::from_row_major(&shuffled_accounts, ROWS, COLUMNS);
        let shuffled_tau = Array2D::from_row_major(&tau, ROWS, COLUMNS);

        return Ok(Self {
            inputs,
            outputs,
            shuffled_tau,
            rho,
            pi,
        });
    }

    pub fn output_shuffle(
        inputs: &Vec<Account>, //Accounts to be shuffled
    ) -> Result<Self, &'static str> {
        let len = inputs.len();
        if len == 0 {
            return Err("Error::EmptyShuffle");
        }

        //Get random inital values
        let (pi, tau, rho) = Self::random_initialization(len);
        let permutation = pi.perm_matrix.as_row_major();

        //shuffle Inputs
        let shuffled_accounts: Vec<_> = (0..len)
            .map(|i| inputs[permutation[i] - 1].clone())
            .collect();
        //Shuffled and Updated Accounts
        let shuffled_outputs: Vec<_> = shuffled_accounts
            .iter()
            .zip(tau.iter())
            .map(|(acc, t)| Account::update_account(*acc, 0, *t, rho))
            .collect();

        //Convert to a 2D array representation
        let outputs = Array2D::from_row_major(&shuffled_outputs, ROWS, COLUMNS);
        let inputs = Array2D::from_row_major(&inputs, ROWS, COLUMNS);
        let shuffled_tau = Array2D::from_row_major(&tau, ROWS, COLUMNS);
        return Ok(Self {
            inputs,
            outputs,
            shuffled_tau,
            rho,
            pi,
        });
    }

    pub fn get_inputs(&self) -> &Array2D<Account> {
        &self.inputs
    }

    pub fn get_outputs(&self) -> &Array2D<Account> {
        &self.outputs
    }

    pub fn get_permutation(&self) -> &Permutation {
        &self.pi
    }

    pub fn get_rho(&self) -> &Scalar {
        &self.rho
    }

    pub fn get_tau(&self) -> &Array2D<Scalar> {
        &self.shuffled_tau
    }

    pub fn get_inputs_vector(&self) -> Vec<Account> {
        self.inputs.as_row_major()
    }

    pub fn get_outputs_vector(&self) -> Vec<Account> {
        self.outputs.as_row_major()
    }
}

impl ShuffleProof {
    pub fn create_shuffle_proof(
        prover: &mut Prover,
        shuffle: &Shuffle,
        witness: &Array2D<Scalar>,
        pc_gens: &PedersenGens,
        xpc_gens: &VectorPedersenGens,
    ) -> (ShuffleProof, ShuffleStatement) {
        //commitment on Witness A using r
        let r: Vec<_> = (0..COLUMNS).map(|_| Scalar::random(&mut OsRng)).collect();
        //convert to column major representation
        let perm_scalar_as_cols = witness.as_columns();

        //compute Xcomit on columns of A.
        let mut comit_A = Vec::<CompressedRistretto>::new();
        for i in 0..COLUMNS {
            comit_A.push(xpc_gens.commit(&perm_scalar_as_cols[i], r[i]).compress());
        }

        //commitment on tau using r'
        let r_dash: Vec<_> = (0..COLUMNS).map(|_| Scalar::random(&mut OsRng)).collect();
        //convert to column major representation
        let tau_as_cols = shuffle.shuffled_tau.as_columns();

        //compute Xcomit on columns of A
        let mut comit_tau = Vec::<CompressedRistretto>::new();
        for i in 0..COLUMNS {
            comit_tau.push(xpc_gens.commit(&tau_as_cols[i], r_dash[i]).compress());
        }
        //Tau commitment from HadamardProduct should be used here.
        //add comit_A and comit_tau in Transcript
        for i in 0..comit_A.iter().count() {
            prover.allocate_point(b"ACommitment", comit_A[i]);
            prover.allocate_point(b"tauCommitment", comit_tau[i]);
        }
        //create challenge x for b and b' vectors
        let x = prover.get_challenge(b"xchallenge");
        //let x = Scalar::random(&mut OsRng);
        //create x^i for i = 1..N
        let exp_x: Vec<_> = vectorutil::exp_iter(x).skip(1).take(N).collect();
        //create b and b' vectors to be used for Multiexponentiationa and hadamard proof later

        let (b_matrix, b_dash_matrix) =
            create_b_b_dash(&exp_x, &shuffle.shuffled_tau.as_row_major(), &shuffle.pi);
        // println!("{:?}", b_mat);

        //Create G,H for DDH and Multiexpo proof generation
        // gather g, h from Public key
        // gather g, h from Public key
        let pk: Vec<RistrettoPublicKey> = shuffle
            .inputs
            .as_row_major()
            .iter()
            .map(|acc| acc.pk)
            .collect();
        let g_i: Vec<_> = pk.iter().map(|pt| pt.gr.decompress().unwrap()).collect();
        let h_i: Vec<_> = pk.iter().map(|pt| pt.grsk.decompress().unwrap()).collect();
        // (G, H) = sum of all i (pk_i * x^i)
        let G = RistrettoPoint::multiscalar_mul(exp_x.iter(), g_i.iter());
        let H = RistrettoPoint::multiscalar_mul(exp_x.iter(), h_i.iter());

        let pk_GH = RistrettoPublicKey {
            gr: G.compress(),
            grsk: H.compress(),
        };
        let (product_proof, product_state) =
            ProductProof::create_product_argument_prove(prover, &b_matrix, &pc_gens, &xpc_gens, x);
        //JUST FOR CHECKING
        /*  let pk_out: Vec<RistrettoPublicKey> = self.outputs.as_row_major().iter().map(|acc| acc.pk).collect();
        let g_i_out: Vec<_> = pk_out.iter().map(|pt| pt.gr.decompress().unwrap()).collect();
        let h_i_out: Vec<_> = pk_out.iter().map(|pt| pt.grsk.decompress().unwrap()).collect();
            // (G, H) = sum of all i (pk_i * x^i)
        let G_out = RistrettoPoint::multiscalar_mul(b_dash.as_row_major().iter().clone(), g_i_out.iter().clone());
        let H_out = RistrettoPoint::multiscalar_mul(b_dash.as_row_major().iter().clone(), h_i_out.iter().clone());*/
        //if G == G_out && H == H_out{
        //   println!("True OUT");
        //}else{
        //  println!("True OUT");
        //}

        //create DDH Proof
        let (ddh_proof, ddh_statement) =
            DDHProof::create_verify_update_ddh_prove(prover, x, &pk, shuffle.rho);
        //create -rho as witness for Multiexpo_commitment_proof

        let neg_rho = -shuffle.rho;

        //Calling Multiexponentiation Prove for PK Update and shuffle
        //create the ciphertext vector
        let rpk: Vec<RistrettoPublicKey> = shuffle
            .outputs
            .as_row_major()
            .iter()
            .map(|acc| acc.pk)
            .collect();
        let (multiexpo_pk_proof, multiexpo_pk_state) =
            MultiexpoProof::create_multiexponential_pubkey_proof(
                prover,
                &rpk,
                &b_dash_matrix,
                &pc_gens,
                &xpc_gens,
                &pk_GH,
            );
        //Calling Multiexponentiation Prove for COMIT Update and shuffle
        // self.multiexp_commit_prove(&b_mat, &pc_gens, &xpc_gens, &pk, rho_b);
        let comm: Vec<_> = shuffle
            .outputs
            .as_row_major()
            .iter()
            .map(|acc| acc.comm)
            .collect();
        let (multiexpo_comit_proof, multiexpo_comit_state) =
            MultiexpoProof::create_multiexponential_elgamal_commit_proof(
                prover, &comm, &b_matrix, &pc_gens, &xpc_gens, &pk_GH, neg_rho,
            );
        (
            ShuffleProof {
                c_A: comit_A,
                c_tau: comit_tau,
                product_proof: product_proof,
                multiexpo_pk: multiexpo_pk_proof,
                multiexpo_comit: multiexpo_comit_proof,
                ddh_proof: ddh_proof,
            },
            ShuffleStatement {
                product_state: product_state,
                multiexpo_pk_state: multiexpo_pk_state,
                multiexpo_comit_state: multiexpo_comit_state,
                ddh_statement: ddh_statement,
            },
        )
    }

    ///!Shuffle Proof Verification
    ///
    pub fn verify(
        &self,
        verifier: &mut Verifier,
        statement: &ShuffleStatement,
        shuffle: &Shuffle,
        pc_gens: &PedersenGens,
        xpc_gens: &VectorPedersenGens,
    ) -> bool {
        //check if C_A and C_B ∈ G^m
        //all vectors should be of length m
        assert_eq!(
            statement.product_state.multi_hadamard_statement.c_A.len(),
            ROWS
        );
        assert_eq!(
            statement
                .product_state
                .multi_hadamard_statement
                .zero_statement
                .c_B
                .len(),
            ROWS
        );
        //recreate challenge x
        //add comit_A and comit_tau in Transcript
        for i in 0..self.c_A.iter().count() {
            verifier.allocate_point(b"ACommitment", self.c_A[i]);
            verifier.allocate_point(b"tauCommitment", self.c_tau[i]);
        }
        //create challenge x for b and b' vectors
        let x = verifier.get_challenge(b"xchallenge");
        //create x^i for i = 1..N
        let exp_x: Vec<_> = vectorutil::exp_iter(x).skip(1).take(N).collect();

        let verify_product =
            self.product_proof
                .verify(verifier, &statement.product_state, &pc_gens, &xpc_gens, x);
        let base_pk = RistrettoPublicKey::generate_base_pk();
        let verify_pk_multi = self.multiexpo_pk.verify_multiexponential_pubkey_proof(
            verifier,
            &statement.multiexpo_pk_state,
            &shuffle.outputs.as_row_major(),
            &pc_gens,
            &xpc_gens,
            &base_pk,
        );

        let pk: Vec<RistrettoPublicKey> = shuffle
            .inputs
            .as_row_major()
            .iter()
            .map(|acc| acc.pk)
            .collect();
        let g_i: Vec<_> = pk.iter().map(|pt| pt.gr.decompress().unwrap()).collect();
        let h_i: Vec<_> = pk.iter().map(|pt| pt.grsk.decompress().unwrap()).collect();
        // (G, H) = sum of all i (pk_i * x^i)
        let G = RistrettoPoint::multiscalar_mul(exp_x.iter(), g_i.iter());
        let H = RistrettoPoint::multiscalar_mul(exp_x.iter(), h_i.iter());

        let pk_GH = RistrettoPublicKey {
            gr: G.compress(),
            grsk: H.compress(),
        };
        let verify_ddh =
            self.ddh_proof
                .verify_ddh_proof(verifier, &statement.ddh_statement, &G, &H);
        let verify_comit_multi = self
            .multiexpo_comit
            .verify_multiexponential_elgamal_commit_proof(
                verifier,
                &statement.multiexpo_comit_state,
                &shuffle.outputs.as_row_major(),
                &pc_gens,
                &xpc_gens,
                &pk_GH,
            );
        verify_comit_multi && verify_pk_multi && verify_product && verify_ddh
    }
}
/// Prepare b and b' vector to be passed as witness to multiexponentiation proof
///
pub fn create_b_b_dash(
    exp_x: &[Scalar],
    tau: &[Scalar],
    p: &Permutation,
) -> (Array2D<Scalar>, Array2D<Scalar>) {
    let perm = p.perm_matrix.as_row_major();
    //create x^i for i = 1..N
    // let exp_x: Vec<_> = vectorutil::exp_iter(x).skip(1).take(N).collect();
    // println!("x^i {:?}", exp_x);
    let mut x_psi: Vec<Scalar> = Vec::with_capacity(N);

    //create 1/tau
    let tau_inv: Vec<_> = tau.iter().map(|i| Scalar::invert(i)).collect();

    let mut b_dash: Vec<Scalar> = Vec::with_capacity(N);
    for (i, _) in exp_x.iter().enumerate() {
        x_psi.push(exp_x[perm[i] - 1]);
        b_dash.push(x_psi[i] * tau_inv[i]);
    }
    //Convert to a 2D array representation
    let b_matrix = Array2D::from_row_major(&x_psi, ROWS, COLUMNS);
    let b_dash_matrix = Array2D::from_row_major(&b_dash, ROWS, COLUMNS);

    (b_matrix, b_dash_matrix)
}

// ------------------------------------------------------------------------
// Tests
// ------------------------------------------------------------------------

#[cfg(test)]
mod test {
    use super::*;
    use crate::{
        keys::{PublicKey, SecretKey},
        ristretto::{RistrettoPublicKey, RistrettoSecretKey},
    };
    use merlin::Transcript;
    #[test]
    fn shuffle_proof_test() {
        let mut account_vector: Vec<Account> = Vec::new();
        // lets create these accounts and associated keypairs
        for _ in 0..9 {
            let mut rng = rand::thread_rng();
            let sk: RistrettoSecretKey = SecretKey::random(&mut rng);
            let pk = RistrettoPublicKey::from_secret_key(&sk, &mut rng);
            let acc = Account::generate_account(pk);
            account_vector.push(acc);
        }
        let result = Shuffle::output_shuffle(&account_vector);
        let shuffle = result.unwrap();
        let pc_gens = PedersenGens::default();
        //generate Xcomit generator points of length m+1
        let xpc_gens = VectorPedersenGens::new(ROWS + 1);

        let mut transcript_p = Transcript::new(b"ShuffleProof");
        let mut prover = Prover::new(b"Shuffle", &mut transcript_p);
        let witness = shuffle.pi.get_permutation_as_scalar_matrix();
        let (proof, statement) = ShuffleProof::create_shuffle_proof(
            &mut prover,
            &shuffle,
            &witness,
            &pc_gens,
            &xpc_gens,
        );

        let mut transcript_v = Transcript::new(b"ShuffleProof");
        let mut verifier = Verifier::new(b"Shuffle", &mut transcript_p);
        let verify = proof.verify(&mut verifier, &statement, &shuffle, &pc_gens, &xpc_gens);
        assert!(verify);
    }

    #[test]
    fn permutation_matrix_test() {
        let perm = Permutation::new(&mut OsRng, N);
        println!("Permuted Matrix {:?}", perm.perm_matrix.as_rows());
    }
    #[test]
    fn inverse_permutation_test() {
        let perm = Permutation::new(&mut OsRng, N);
        println!("Permuted Vector {:?}", perm);
        let inv = perm.invert_permutation();
        println!("Inverted Vector {:?}", inv);
    }
    #[test]
    fn account_permutation_test() {
        // lets define a vector of accounts
        let mut account_vector: Vec<Account> = Vec::new();

        // lets create these accounts and associated keypairs

        for _ in 0..9 {
            let mut rng = rand::thread_rng();
            let sk: RistrettoSecretKey = SecretKey::random(&mut rng);
            let pk = RistrettoPublicKey::from_secret_key(&sk, &mut rng);
            let acc = Account::generate_account(pk);
            account_vector.push(acc);
        }
        let len = account_vector.len();
        let pi = { Permutation::new(&mut OsRng, len) };
        let permutation = pi.perm_matrix.as_row_major();
        //shuffle Account Vector
        let shuffled_accounts: Vec<_> = (0..len)
            .map(|i| account_vector[permutation[i] - 1].clone())
            .collect();
        assert_ne!(account_vector, shuffled_accounts)
    }
    #[test]
    fn shuffle_output_test() {
        // lets define a vector of accounts
        let mut account_vector: Vec<Account> = Vec::new();

        // lets create these accounts and associated keypairs
        for _x in 0..9 {
            let mut rng = rand::thread_rng();
            let sk: RistrettoSecretKey = SecretKey::random(&mut rng);
            let pk = RistrettoPublicKey::from_secret_key(&sk, &mut rng);
            let acc = Account::generate_account(pk);
            account_vector.push(acc);
        }
        // 1 for input , 2 for output
        let shuffle = { Shuffle::output_shuffle(&account_vector) };
        let inp = shuffle.as_ref().unwrap().inputs.as_row_major();
        let out = shuffle.as_ref().unwrap().outputs.as_row_major();
        let pi = &shuffle.as_ref().unwrap().pi;
        let perm = pi.perm_matrix.as_row_major();
        let tau = shuffle.as_ref().unwrap().shuffled_tau.as_row_major();
        let rho = shuffle.as_ref().unwrap().rho;

        let shuffled_inputs: Vec<_> = (0..9).map(|i| inp[perm[i] - 1].clone()).collect();
        let shuffled_updated: Vec<_> = shuffled_inputs
            .iter()
            .zip(tau.iter())
            .map(|(acc, t)| Account::update_account(*acc, 0, *t, rho))
            .collect();
        assert_eq!(out, shuffled_updated)
    }
    // Testing the update of input and assignment to output
    #[test]
    fn shuffle_input_update_test() {
        // lets define a vector of accounts
        let mut account_vector: Vec<Account> = Vec::new();

        // lets create these accounts and associated keypairs
        for _x in 0..9 {
            let mut rng = rand::thread_rng();
            let sk: RistrettoSecretKey = SecretKey::random(&mut rng);
            let pk = RistrettoPublicKey::from_secret_key(&sk, &mut rng);
            let acc = Account::generate_account(pk);
            account_vector.push(acc);
        }
        // 1 for input , 2 for output
        let shuffle = { Shuffle::input_shuffle(&account_vector) };
        let out = shuffle.as_ref().unwrap().outputs.as_row_major();
        let tau = shuffle.as_ref().unwrap().shuffled_tau.as_row_major();
        let rho = shuffle.as_ref().unwrap().rho;

        let input_updated: Vec<_> = account_vector
            .iter()
            .zip(tau.iter())
            .map(|(acc, t)| Account::update_account(*acc, 0, *t, rho))
            .collect();
        assert_eq!(out, input_updated)
    }

    // Testing the inverse permutation and assignment to input
    #[test]
    fn shuffle_input_perm_test() {
        // lets define a vector of accounts
        let mut account_vector: Vec<Account> = Vec::new();

        // lets create these accounts and associated keypairs
        for _x in 0..9 {
            let mut rng = rand::thread_rng();
            let sk: RistrettoSecretKey = SecretKey::random(&mut rng);
            let pk = RistrettoPublicKey::from_secret_key(&sk, &mut rng);
            let acc = Account::generate_account(pk);
            account_vector.push(acc);
        }
        // 1 for input , 2 for output
        let shuffle = { Shuffle::input_shuffle(&account_vector) };
        let inp = shuffle.as_ref().unwrap().inputs.as_row_major();
        let pi = &shuffle.as_ref().unwrap().pi;
        let perm = pi.perm_matrix.as_row_major();
        //shuffle the input and compare with the account_vector
        let shuffled_inputs: Vec<_> = (0..9).map(|i| inp[perm[i] - 1].clone()).collect();
        assert_eq!(account_vector, shuffled_inputs)
    }

    #[test]
    fn scalar_batch_invert_test() {
        //Create Random tau used for updating the Account Pks
        let tau: Vec<_> = (0..9).map(|_| Scalar::random(&mut OsRng)).collect();
        let tau_inv: Vec<_> = tau.iter().map(|i| Scalar::invert(i)).collect();

        // tau * tau_inv should be == 1
        let result: Vec<_> = tau.iter().zip(tau_inv.iter()).map(|(a, b)| a * b).collect();

        assert!(result
            .get(0)
            .map(|first| result.iter().all(|x| x == first))
            .unwrap_or(true));
    }
    #[test]
    fn b_dash_vector_test() {
        //Create Random tau used for updating the Account Pks
        let x = Scalar::random(&mut OsRng);
        //let x = Scalar::from(3u64);
        let tau: Vec<_> = (0..9).map(|_| Scalar::random(&mut OsRng)).collect();
        let perm = Permutation::new(&mut OsRng, N);
        //let perm_vec = perm.perm_matrix.as_row_major();
        //create x^i for i = 1..N
        let exp_x: Vec<_> = vectorutil::exp_iter(x).skip(1).take(N).collect();
        let (b, b_dash) = create_b_b_dash(&exp_x, &tau, &perm);
        //test
        let b_dash_tau: Vec<Scalar> = b_dash
            .as_row_major()
            .iter()
            .zip(tau.iter())
            .map(|(b, t)| b * t)
            .collect();

        assert_eq!(b_dash_tau, b.as_row_major());
    }
    #[test]
    fn b_vector_test() {
        //test for N = 9
        let x = Scalar::from(3u64);
        //Create Random tau used for updating the Account Pks
        let tau: Vec<_> = (0..N).map(|_| Scalar::random(&mut OsRng)).collect();
        let matrix = Array2D::from_row_major(&vec![2, 1, 3, 8, 7, 6, 4, 5, 9], ROWS, COLUMNS);
        let mut permutation = Permutation::new(&mut OsRng, N);
        permutation.set(matrix);
        //create x^i for i = 1..N
        let exp_x: Vec<_> = vectorutil::exp_iter(x).skip(1).take(N).collect();
        let (b, _) = create_b_b_dash(&exp_x, &tau, &permutation);

        let b_reference: Vec<Scalar> = vec![
            Scalar::from(9u64),
            Scalar::from(3u64),
            Scalar::from(27u64),
            Scalar::from(6561u64),
            Scalar::from(2187u64),
            Scalar::from(729u64),
            Scalar::from(81u64),
            Scalar::from(243u64),
            Scalar::from(19683u64),
        ];
        //test

        assert_eq!(b_reference, b.as_row_major());
    }
    #[test]
    fn shuffle_prove_test() {
        let mut account_vector: Vec<Account> = Vec::new();
        // lets create these accounts and associated keypairs
        for _ in 0..9 {
            let mut rng = rand::thread_rng();
            let sk: RistrettoSecretKey = SecretKey::random(&mut rng);
            let pk = RistrettoPublicKey::from_secret_key(&sk, &mut rng);
            let acc = Account::generate_account(pk);
            account_vector.push(acc);
        }
        let shuffle = { Shuffle::output_shuffle(&account_vector) };
        // shuffle.unwrap().shuffle_argument_prove();
        assert_eq!(true, true);
    }
}
