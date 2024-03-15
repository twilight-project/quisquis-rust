//! The `vectorpedersen` module contains API for producing a
//! vector commitment.

#![allow(non_snake_case)]

use crate::{
    accounts::{Account, Prover, Verifier, transcript},
    elgamal::ElGamalCommitment,
    pedersen::vectorpedersen::VectorPedersenGens,
    ristretto::RistrettoPublicKey,
    shuffle::ddh::{DDHProof, DDHStatement},
    shuffle::hadamard::{HadamardProof, HadamardStatement},
    shuffle::multiexponential::MultiexpoProof,
    shuffle::product::{ProductProof, ProductStatement},
    shuffle::vectorutil,
};
use array2d::Array2D;
use bulletproofs::PedersenGens;
use curve25519_dalek::traits::{MultiscalarMul, Identity};
use std::convert::TryInto;

use crate::keys::PublicKey;
use curve25519_dalek::{
    ristretto::{CompressedRistretto, RistrettoPoint},
    scalar::Scalar,
};
use rand::rngs::OsRng;
use rand::{CryptoRng, Rng};
// use serde::{Deserialize, Serialize};
use serde_derive::{Deserialize, Serialize};

use super::{singlevalueproduct::SVPProof, product::{MultiHadamardProof, MultiHadamardStatement}};

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
    pub fn from_array2D(matrix: Array2D<usize>) -> Self {
        Self { perm_matrix: matrix }
    }
    //Set the permutation matrix explicitly
    pub fn set(&mut self, matrix: Array2D<usize>) {
        self.perm_matrix = matrix;
    }

    //Get the permutation matrix arranged as row major 1D array
    pub fn get_row_major(&self) -> [usize; 9] {
        self.perm_matrix
            .as_row_major()
            .try_into()
            .unwrap_or_else(|_v: Vec<usize>| panic!("Expected a Vec of length {}", 9))
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

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct ShuffleStatement {
    pub hadamard_statement: HadamardStatement,
    pub product_statement: ProductStatement,
    pub ddh_statement: DDHStatement,
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct ShuffleProof {
    pub c_A: Vec<CompressedRistretto>,
    pub c_tau: Vec<CompressedRistretto>,
    pub c_B: Vec<CompressedRistretto>,
    pub c_B_dash: Vec<CompressedRistretto>,
    pub hadamard_proof: HadamardProof,
    pub product_proof: ProductProof,
    pub multi_exponential_pk_proof: MultiexpoProof,
    pub multi_exponential_commitment_proof: MultiexpoProof,
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
        inputs: &[Account], //Accounts to be shuffled
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
            .map(|(acc, t)| Account::update_account(*acc, 0u64.into(), *t, rho))
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
            .map(|(acc, t)| Account::update_account(*acc, 0u64.into(), *t, rho))
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

    pub fn get_permutation_as_vector(&self) -> Vec<usize> {
        self.pi.get_row_major().to_vec()
    }

    pub fn get_shuffled_tau_vector(&self) -> Vec<Scalar> {
        self.shuffled_tau.as_row_major()
    }
    // pub fn to_hex(&self) -> String {
    //     //convert inputs to row major order
    //     let mut bytes = Vec::new();
    //     let inputs = self.inputs. 
    //     let bincode = bincode::serialize(self).unwrap();
    //     //convert to hex
    //     let hex = hex::encode(bincode);
    //     hex
    // }
    // pub fn from_hex(hex: &str) -> Self {
    //     //convert to bincode
    //     let bincode = hex::decode(hex).unwrap();
    //     //convert to struct
    //     let shuffle: Self = bincode::deserialize(&bincode).unwrap();
    //     shuffle
    // }
    /// Prepares data for shuffle proof parallel implementation
    /// @ return (x, y, z, B Matrix, B' Matrix, exp(x), commitment_witness, commitment_tau, commitment_b, commitment_b_dash, s, s_dash, r, r_dash)
    /// prepares data for Hadamard and Product proof
    pub fn create_shuflle_proof_challenges(&self) -> (Scalar, Scalar, Array2D<Scalar>, Array2D<Scalar>, 
        [Scalar; N], [CompressedRistretto;ROWS], [CompressedRistretto;COLUMNS], [CompressedRistretto;ROWS], 
        [CompressedRistretto;ROWS], [Scalar;ROWS], [Scalar;ROWS], [Scalar;ROWS], [Scalar;ROWS]) {
        
        //create transcript and prover for shuffle proof
        let mut transcript = merlin::Transcript::new(b"ProofTransScript");
        // create prover to generate TranscriptRng for random scalar generation
        let mut prover = Prover::new(b"ShuffleProof", &mut transcript);
        let xpc_gens = VectorPedersenGens::new(ROWS + 1);
        //extract permuatation witness
        let witness = self.pi.get_permutation_as_scalar_matrix();
         //arrange the witness as vec of vec in row major order
         let perm_scalar_as_rows = witness.as_rows();
         
        //******Add witness Scalars to TranscriptRng  */ 
        // transcriptRng using public transcript data + secret for proof + external source
        let prover_scalars: Vec<_> = witness.elements_column_major_iter()
            //.chain(rscalar2.iter().cloned())
            .chain(self.shuffled_tau.elements_row_major_iter())
            .cloned()
            .collect();
        let mut rng =
            prover.prove_rekey_witness_transcript_rng(&prover_scalars);
        
        //commit on Witness A using r
        let r: Vec<_> = (0..ROWS).map(|_| Scalar::random(&mut OsRng)).collect();
        //compute Xcomit on rows of witness "A" Matrix.
        let mut commitment_witness:[CompressedRistretto; ROWS] = [CompressedRistretto::identity(); ROWS];
        for i in 0..ROWS {
            commitment_witness[i] = xpc_gens.commit(&perm_scalar_as_rows[i], r[i]).compress();
        }
        
        //commitment on tau using r'
        let r_dash: Vec<_> = (0..ROWS).map(|_| Scalar::random(&mut rng)).collect();
        //convert to column major representation
        let tau_as_rows = self.shuffled_tau.as_rows();

        //compute Xcomit on columns of tau
        let mut commitment_tau:[CompressedRistretto; COLUMNS] = [CompressedRistretto::identity(); COLUMNS];
        for i in 0..COLUMNS {
            commitment_tau[i] = xpc_gens.commit(&tau_as_rows[i], r_dash[i]).compress();
        }
        //Tau commitment from HadamardProduct should be used here.
        //add commitment_witness and commitment_tau in Transcript
        for (a, tau) in commitment_witness.iter().zip(commitment_tau.iter()) {
            prover.allocate_point(b"ACommitment", a);
            prover.allocate_point(b"tauCommitment", tau);
        }
        //create challenge x
        let x = prover.get_challenge(b"xChallenge");
        
        //create x^i for i = 1..N
        let exp_x: [Scalar; N] = vectorutil::exp_iter(x).skip(1).take(N).collect::<Vec<Scalar>>().try_into().unwrap_or_else(|_|
            panic!("exp_x is not created properly"));
        
        //create b and b' vectors to be used for Multiexponentiationa and hadamard proof later
        let (b_matrix, b_dash_matrix) =
            create_b_b_dash(&exp_x, &self.shuffled_tau.as_row_major(), &self.pi);

        //convert b and b' to row major representation
        let b_as_rows = b_matrix.as_rows();
        let b_dash_as_rows = b_dash_matrix.as_rows();
        //commitment on b using s and b' using s'
        let s: Vec<_> = (0..ROWS).map(|_| Scalar::random(&mut rng)).collect();
        let s_dash: Vec<_> = (0..ROWS).map(|_| Scalar::random(&mut rng)).collect();
        //compute Xcomit on rows of b
        let mut commitment_b:[CompressedRistretto;ROWS] = [CompressedRistretto::identity();ROWS];
        for i in 0..ROWS {
            commitment_b[i] = xpc_gens.commit(&b_as_rows[i], s[i]).compress();
        }
        //compute Xcomit on rows of b'
        let mut commitment_b_dash:[CompressedRistretto;ROWS]= [CompressedRistretto::identity();ROWS]   ;
        for i in 0..ROWS {
            commitment_b_dash[i] = xpc_gens.commit(&b_dash_as_rows[i], s_dash[i]).compress();
        }
        //add comit_b and comit_b_dash in Transcript
        for (cb, cbdash) in commitment_b.iter().zip(commitment_b_dash.iter()) {
            prover.allocate_point(b"BCommitment", cb);
            prover.allocate_point(b"BDashCommitment", cbdash);
        }
        
        //create challenge y,z for product argument creation
        let y = prover.get_challenge(b"yChallenge");
        let z = prover.get_challenge(b"zChallenge");
        (
            y,
            z,
            b_matrix,
            b_dash_matrix,
            exp_x,
            commitment_witness,
            commitment_tau,
            commitment_b,
            commitment_b_dash,
            s.try_into().unwrap(),
            s_dash.try_into().unwrap(),
            r.try_into().unwrap(),
            r_dash.try_into().unwrap(),
        )
    }
    pub fn create_ddh_multiexponential_proof_data(&self, exp_x: &[Scalar])-> (RistrettoPoint, RistrettoPoint, Vec<RistrettoPoint>, Vec<RistrettoPoint>, Vec<RistrettoPublicKey>, Vec<ElGamalCommitment>){
                //Create G,H for DDH and Multiexpo proof generation
                let pk: Vec<RistrettoPublicKey> = self
                .inputs
                .as_row_major()
                .iter()
                .map(|acc| acc.pk)
                .collect();
            // gather g, h from Public key
            let g_i: Vec<_> = pk.iter().map(|pt| pt.gr.decompress().unwrap()).collect();
            let h_i: Vec<_> = pk.iter().map(|pt| pt.grsk.decompress().unwrap()).collect();
            // (G, H) = sum of all i (pk_i * x^i)
            let G = RistrettoPoint::multiscalar_mul(exp_x.iter(), g_i.iter());
            let H = RistrettoPoint::multiscalar_mul(exp_x.iter(), h_i.iter());

             //create the ciphertext vector of pk and commitment
            let mut upk: Vec<_> = Vec::<RistrettoPublicKey>::new();
            let mut updated_commitment: Vec<_> = Vec::<ElGamalCommitment>::new();
            for acc in self.outputs.as_row_major().iter() {
            upk.push(acc.pk);
            updated_commitment.push(acc.comm);
            }
            (G, H, g_i, h_i, upk, updated_commitment)
    }
    pub fn create_shuffle_proof_parallel(
        shuffle: Self,
    ) -> Result<(ShuffleProof, ShuffleStatement), &'static str> {
        //use std::time::Instant;
       // let now = Instant::now();
        //extract permuatation witness
        let witness = shuffle.pi.get_permutation_as_scalar_matrix();
        // create data for Hadamard and Product proof
        let (y, z, b_matrix, b_dash_matrix,
             exp_x, commitment_witness, commitment_tau, 
             commitment_b, commitment_b_dash, s, 
             s_dash, r, r_dash) = shuffle.create_shuflle_proof_challenges();

        // create data for DDH and multiexponential proofs
        // should be called after create_shuflle_proof_challenges
        let (G, H, g_i, h_i, upk,
             updated_commitment) = shuffle.create_ddh_multiexponential_proof_data(&exp_x);
        // needed for multiexponential proof
        let pk_GH = RistrettoPublicKey {
            gr: G.compress(),
            grsk: H.compress(),
        };
        
        //******  the rest of the functions can now be called in parallel ***//
        let shuffled_tau = shuffle.shuffled_tau.clone();
        let b_dash_matrix_hadamard = b_dash_matrix.clone();
        let b_matrix_hadamard = b_matrix.clone();
        let s_dash_hadamard = s_dash.clone();
       // let now = Instant::now();
        // Hadamard proof: b' o tau = b
         // Spawn a new thread to create MultiHadamard proof in parallel 
         let handle_multi_hadamard: std::thread::JoinHandle<(HadamardProof, HadamardStatement)> = std::thread::spawn(move || {
         wrapper_hadamard_proof(
            b_dash_matrix_hadamard,
            shuffled_tau,
            b_matrix_hadamard,
            commitment_b_dash,
            commitment_tau,
            commitment_b,
            s_dash_hadamard,
            r_dash,
            s.clone(),
        )
    });
       // println!("Elapsed: Hadamard {:.2?}", now.elapsed());
        
        //Prepare for Product argument.
        // [f] =  y [a] + [b]
        // possible to parallelize at the second level
        let witness_product = witness.clone();
        let b_matrix_product = b_matrix.clone();
       //spawn a new thread to create Product proof in parallel
         let handle_product: std::thread::JoinHandle<(ProductProof, ProductStatement)> = std::thread::spawn(move || {
          wrapper_product_proof(
                witness_product,
                b_matrix_product,
                y,
                z, 
              r,
              s, 
          )
        });
       // println!("Elapsed: Product {:.2?}", now.elapsed());
       // let now = Instant::now()
        //create DDH Proof
        let exp_x_ddh  = exp_x.clone();
        let shuffle_rho_ddh = shuffle.rho.clone();
        //spawn a new thread to create DDH proof in parallel
        let handle_ddh: std::thread::JoinHandle<(DDHProof, DDHStatement)> = std::thread::spawn(move || {
            wrapper_ddh_proof(
                g_i,
                h_i,
                exp_x_ddh,
                G,
                H,
                shuffle_rho_ddh,
            )
        });
            
        //println!("Elapsed: DDH {:.2?}", now.elapsed());
       // let now = Instant::now();
       
        //Calling Multiexponentiation Prove for Pk Update and shuffle
       // spawn a new thread to create Multiexponential proof for publicKeys of updated output accounts in parallel
       let b_dash_matrix_multiexp = b_dash_matrix.clone();
        let handle_multi_pk: std::thread::JoinHandle<MultiexpoProof> = std::thread::spawn(move || {
            self::wrapper_multiexponential_publickey(
                upk,
                b_dash_matrix_multiexp,
                s_dash,
            )
        });
        //println!("Elapsed: Multiexpopk {:.2?}", now.elapsed());
        //let now = Instant::now();
        //create -rho as witness for Multiexpo_commitment_proof
        let neg_rho = -shuffle.rho;
        //Calling Multiexponentiation Prove for Commitment Update and shuffle
        //spawn a new thread
        let b_matrix_multiexpo = b_matrix.clone(); 
        let s_multiexo = s.clone();
        let handle_multi_commit: std::thread::JoinHandle<MultiexpoProof> = std::thread::spawn(move || {
            wrapper_multiexponential_commitment(
                updated_commitment,
                b_matrix_multiexpo,
                s_multiexo,
                neg_rho,
                pk_GH,
            )
        });
        //println!("Elapsed: Multiexpocommit {:.2?}", now.elapsed());
        //let now = Instant::now();
        //join all threads
       
        let multiexpo_pk_proof = match handle_multi_pk.join(){
            Ok(result) => result,
            Err(_) => return Err("Error in Joining MultiPK Proof Thread"),
        };
        let (hadamard_proof, hadamard_statement) = match handle_multi_hadamard.join(){
            Ok(result) => result,
            Err(_) => return Err("Error in Joining MultiHadamard Proof Thread"),
        };
        let (product_proof, product_statement) = match handle_product.join(){
            Ok(result) => result,
            Err(_) => return Err("Error in Joining Product Proof Thread"),
        };
        let (ddh_proof, ddh_statement) = match handle_ddh.join(){
            Ok(result) => result,
            Err(_) => return Err("Error in Joining DDH Proof Thread"),
        };
        let multiexpo_commit_proof = match handle_multi_commit.join(){
            Ok(result) => result,
            Err(_) => return Err("Error in Joining MultiCommit Proof Thread"),
        };
       // println!("Elapsed: Multiexpocommit {:.2?}", now.elapsed());
       
       let shuffle_proof = ShuffleProof {
            c_A: commitment_witness.to_vec(),
            c_tau: commitment_tau.to_vec(),
            c_B: commitment_b.to_vec(),
            c_B_dash: commitment_b_dash.to_vec(),
            hadamard_proof,
            product_proof,
            multi_exponential_pk_proof: multiexpo_pk_proof,
            multi_exponential_commitment_proof: multiexpo_commit_proof,
            ddh_proof,
        };
        let shuffle_statement = ShuffleStatement {
            hadamard_statement,
            product_statement,
            ddh_statement,
        };
       
        Ok((shuffle_proof, shuffle_statement))
    }
}

impl ShuffleProof {
    pub fn create_shuffle_proof(
       
        shuffle: Shuffle,
    ) -> (ShuffleProof, ShuffleStatement) {
            //create transcript and prover for shuffle proof
       let mut transcript = merlin::Transcript::new(b"ProofTransScript");
       // create prover to generate TranscriptRng for random scalar generation
       let mut prover = Prover::new(b"ShuffleProof", &mut transcript);
      
      // create xpc_gens for Pedersen Commitment
       let xpc_gens = VectorPedersenGens::new(ROWS + 1);
       // create pc_gens for Pedersen Commitment
       let pc_gens = PedersenGens::default();
       // use std::time::Instant;
       // let now = Instant::now();
        //extract permuatation witness
        let witness = shuffle.pi.get_permutation_as_scalar_matrix();
        //commit on Witness A using r
        let r: Vec<_> = (0..ROWS).map(|_| Scalar::random(&mut OsRng)).collect();
        //arrange the witness as vec of vec in row major order
        let perm_scalar_as_rows = witness.as_rows();
        //compute Xcomit on rows of witness "A" Matrix.
        let mut commitment_witness = Vec::<CompressedRistretto>::new();
        for i in 0..ROWS {
            commitment_witness.push(xpc_gens.commit(&perm_scalar_as_rows[i], r[i]).compress());
        }
        // transcriptRng using public transcript data + secret for proof + external source
        let mut rng =
            prover.prove_rekey_witness_transcript_rng(&shuffle.shuffled_tau.as_row_major());
        //commitment on tau using r'
        let r_dash: Vec<_> = (0..ROWS).map(|_| Scalar::random(&mut rng)).collect();
        //convert to column major representation
        let tau_as_rows = shuffle.shuffled_tau.as_rows();

        //compute Xcomit on columns of tau
        let mut commitment_tau = Vec::<CompressedRistretto>::new();
        for i in 0..COLUMNS {
            commitment_tau.push(xpc_gens.commit(&tau_as_rows[i], r_dash[i]).compress());
        }
        //Tau commitment from HadamardProduct should be used here.
        //add commitment_witness and commitment_tau in Transcript
        for (a, tau) in commitment_witness.iter().zip(commitment_tau.iter()) {
            prover.allocate_point(b"ACommitment", a);
            prover.allocate_point(b"tauCommitment", tau);
        }
        //create challenge x
        let x = prover.get_challenge(b"xChallenge");
        //create x^i for i = 1..N
        let exp_x: Vec<_> = vectorutil::exp_iter(x).skip(1).take(N).collect();
        //create b and b' vectors to be used for Multiexponentiationa and hadamard proof later
        let (b_matrix, b_dash_matrix) =
            create_b_b_dash(&exp_x, &shuffle.shuffled_tau.as_row_major(), &shuffle.pi);

        //convert b and b' to row major representation
        let b_as_rows = b_matrix.as_rows();
        let b_dash_as_rows = b_dash_matrix.as_rows();
        //commitment on b using s and b' using s'
        let s: Vec<_> = (0..ROWS).map(|_| Scalar::random(&mut rng)).collect();
        let s_dash: Vec<_> = (0..ROWS).map(|_| Scalar::random(&mut rng)).collect();
        //compute Xcomit on rows of b
        let mut commitment_b = Vec::<CompressedRistretto>::new();
        for i in 0..ROWS {
            commitment_b.push(xpc_gens.commit(&b_as_rows[i], s[i]).compress());
        }
        //compute Xcomit on rows of b'
        let mut commitment_b_dash = Vec::<CompressedRistretto>::new();
        for i in 0..ROWS {
            commitment_b_dash.push(xpc_gens.commit(&b_dash_as_rows[i], s_dash[i]).compress());
        }
        //add comit_b and comit_b_dash in Transcript
        for (cb, cbdash) in commitment_b.iter().zip(commitment_b_dash.iter()) {
            prover.allocate_point(b"BCommitment", cb);
            prover.allocate_point(b"BDashCommitment", cbdash);
        }
        // Hadamard proof: b' o tau = b
        let (hadamard_proof, hadamard_statement) = HadamardProof::create_hadamard_argument_proof(
          //  prover,
            &xpc_gens,
            &b_dash_matrix,
            &shuffle.shuffled_tau,
            &b_matrix,
            &commitment_b_dash,
            &commitment_tau,
            &commitment_b,
            &s_dash,
            &r_dash,
            &s,
        );
       // println!("Elapsed: Hadamard {:.2?}", now.elapsed());
        
       // let now = Instant::now();
        //create challenge y,z for product argument creation
        let y = prover.get_challenge(b"yChallenge");
        let z = prover.get_challenge(b"zChallenge");
        //Prepare for Product argument.
        // [f] =  y [a] + [b]
        let a_as_rows = witness.as_row_major();
        let b_as_rows = b_matrix.as_row_major();
        let f: Vec<_> = a_as_rows
            .iter()
            .zip(b_as_rows.iter())
            .map(|(a, b)| a * y + b)
            .collect();
        // [t] =  y [r] + [s]
        let t: Vec<_> = r.iter().zip(s.iter()).map(|(r, s)| r * y + s).collect();

        let e: Vec<_> = f.iter().map(|f| f - z).collect();
        let e_2d = Array2D::from_column_major(&e, ROWS, COLUMNS);
        let (product_proof, product_statement) =
            ProductProof::create_product_argument_proof( &e_2d, &t, &pc_gens, &xpc_gens);
       // println!("Elapsed: Product {:.2?}", now.elapsed());
       // let now = Instant::now();
        //Create G,H for DDH and Multiexpo proof generation
        let pk: Vec<RistrettoPublicKey> = shuffle
            .inputs
            .as_row_major()
            .iter()
            .map(|acc| acc.pk)
            .collect();
        // gather g, h from Public key
        let g_i: Vec<_> = pk.iter().map(|pt| pt.gr.decompress().unwrap()).collect();
        let h_i: Vec<_> = pk.iter().map(|pt| pt.grsk.decompress().unwrap()).collect();
        // (G, H) = sum of all i (pk_i * x^i)
        let G = RistrettoPoint::multiscalar_mul(exp_x.iter(), g_i.iter());
        let H = RistrettoPoint::multiscalar_mul(exp_x.iter(), h_i.iter());

        let pk_GH = RistrettoPublicKey {
            gr: G.compress(),
            grsk: H.compress(),
        };
        //create DDH Proof
        let (ddh_proof, ddh_statement) =
            DDHProof::create_verify_update_ddh_prove(&g_i, &h_i, &exp_x, G, H, shuffle.rho);
        //println!("Elapsed: DDH {:.2?}", now.elapsed());
       // let now = Instant::now();
        //create the ciphertext vector of pk and commitment
        let mut upk: Vec<_> = Vec::<RistrettoPublicKey>::new();
        let mut updated_commitment: Vec<_> = Vec::<ElGamalCommitment>::new();
        for acc in shuffle.outputs.as_row_major().iter() {
            upk.push(acc.pk);
            updated_commitment.push(acc.comm);
        }
        // create base pk pair for reencryption in proof
        let base_pk = RistrettoPublicKey::generate_base_pk();
        //Calling Multiexponentiation Prove for Pk Update and shuffle
        let multiexpo_pk_proof = MultiexpoProof::create_multiexponential_pubkey_proof(
           // prover,
            &upk,
            &b_dash_matrix,
            &s_dash,
            &pc_gens,
            &xpc_gens,
            &base_pk,
        );
       // println!("Elapsed: Multiexpopk {:.2?}", now.elapsed());
        //let now = Instant::now();
        //create -rho as witness for Multiexpo_commitment_proof
        let neg_rho = -shuffle.rho;
        //Calling Multiexponentiation Prove for Commitment Update and shuffle
        let multiexpo_commit_proof = MultiexpoProof::create_multiexponential_elgamal_commit_proof(
           // prover,
            &updated_commitment,
            &b_matrix,
            &s,
            &pc_gens,
            &xpc_gens,
            &pk_GH,
            neg_rho,
        );
       // println!("Elapsed: Multiexpocommit {:.2?}", now.elapsed());
        (
            ShuffleProof {
                c_A: commitment_witness,
                c_tau: commitment_tau,
                c_B: commitment_b,
                c_B_dash: commitment_b_dash,
                hadamard_proof,
                product_proof,
                multi_exponential_pk_proof: multiexpo_pk_proof,
                multi_exponential_commitment_proof: multiexpo_commit_proof,
                ddh_proof,
            },
            ShuffleStatement {
                hadamard_statement,
                product_statement,
                ddh_statement,
            },
        )
    }
    

    ///!Shuffle Proof Verification
    ///
    pub fn verify(
        &self,
        //verifier: &mut Verifier,
        statement: &ShuffleStatement,
        shuffle_input: &[Account],
        shuffle_output: &[Account],
    ) -> Result<(), &'static str> {
        //check length of commitment vectors
        
        if self.c_A.len() == ROWS
            && self.c_B.len() == ROWS
            && self.c_B_dash.len() == ROWS
            && self.c_tau.len() == ROWS
        {
            //create transcript and verifier for shuffle proof
            let mut transcript = merlin::Transcript::new(b"ProofTransScript");
            let mut verifier = Verifier::new(b"ShuffleProof", &mut transcript);
            // create xpc_gens for Pedersen Commitment
            let xpc_gens = VectorPedersenGens::new(ROWS + 1);
            // create pc_gens for Pedersen Commitment
            let pc_gens = PedersenGens::default();

            //recreate challenge x

            //add c_A and c_tau in Transcript
            for (ca, ctau) in self.c_A.iter().zip(self.c_tau.iter()) {
                verifier.allocate_point(b"ACommitment", ca);
                verifier.allocate_point(b"tauCommitment", ctau);
            }
            //create challenge x
            let x: Scalar = verifier.get_challenge(b"xChallenge");

            //create x^i for i = 1..N
            let exp_x: Vec<_> = vectorutil::exp_iter(x).skip(1).take(N).collect();
            let base_pk = RistrettoPublicKey::generate_base_pk();
            //add comit_b and comit_b_dash in Transcript
            for (b, bdash) in self.c_B.iter().zip(self.c_B_dash.iter()) {
                verifier.allocate_point(b"BCommitment", b);
                verifier.allocate_point(b"BDashCommitment", bdash);
            }

            //Verify Hadamard Proof : b' o tau = b
            self.hadamard_proof.verify(
              //  verifier,
                &xpc_gens,
                &statement.hadamard_statement,
                &self.c_B_dash,
                &self.c_tau,
                &self.c_B,
            )?;

            //create challenge y,z for product argument verification
            let y = verifier.get_challenge(b"yChallenge");
            let z = verifier.get_challenge(b"zChallenge");
            //test prod of i..N (e_i) == prod pf i .. N (yi + x^i -z)
            let mut product = Scalar::one();
            let mut scalar: Scalar;
            for (i, xi) in exp_x.iter().enumerate() {
                scalar = Scalar::from((i + 1) as u64);
                product = product * (y * scalar + xi - z);
            }
            //check bvec == prod i =[1..N] {yi + x^i -z}
            if product == statement.product_statement.svp_statement.b {
                //recreate c_E from C_F & C_-Z

                let mut c_F = Vec::<RistrettoPoint>::new();
                for (ca, cb) in self.c_A.iter().zip(self.c_B.iter()) {
                    c_F.push(
                        ca.decompress()
                            .ok_or("ShuffleProof Verify: Decompression Failed")?
                            * y
                            + cb.decompress()
                                .ok_or("ShuffleProof Verify: Decompression Failed")?,
                    );
                }
          
                //create  C_-Z
                let z_neg: Vec<Scalar> = (0..N).map(|_| -z.clone()).collect();
                let z_neg_2d_as_cols = Array2D::from_row_major(&z_neg, ROWS, COLUMNS).as_columns();
                let mut comit_z_neg = Vec::<RistrettoPoint>::new();
                for i in 0..COLUMNS {
                    comit_z_neg.push(xpc_gens.commit(&z_neg_2d_as_cols[i], Scalar::zero()));
                }
                //recreate c_E to verified in product proof
                let c_E: Vec<_> = c_F
                    .iter()
                    .zip(comit_z_neg.iter())
                    .map(|(ca, cb)| ca + cb)
                    .collect();
                //product proof verify
                self.product_proof.verify(
                  //  verifier,
                    &statement.product_statement,
                    &c_E,
                    &pc_gens,
                    &xpc_gens,
                )?;
                //prepare for multiexponentiation and DDH proof on account public keys
                let pk: Vec<RistrettoPublicKey> = shuffle_input.iter().map(|acc| acc.pk).collect();
                let g_i: Vec<_> = pk
                    .iter()
                    .map(|pt| {
                        pt.gr
                            .decompress()
                            .ok_or("ShuffleProof Verify: Decompression Failed")
                    })
                    .collect::<Result<Vec<_>, _>>()?;
                let h_i: Vec<_> = pk
                    .iter()
                    .map(|pt| {
                        pt.grsk
                            .decompress()
                            .ok_or("ShuffleProof Verify: Decompression Failed")
                    })
                    .collect::<Result<Vec<_>, _>>()?;
                // (G, H) = sum of all i (pk_i * x^i)
                let G = RistrettoPoint::multiscalar_mul(exp_x.iter(), g_i.iter());
                let H = RistrettoPoint::multiscalar_mul(exp_x.iter(), h_i.iter());

                let pk_GH = RistrettoPublicKey {
                    gr: G.compress(),
                    grsk: H.compress(),
                };
                //verify DDH proof on pk's
                self.ddh_proof.verify_ddh_proof(
                    &statement.ddh_statement,
                    pk_GH.gr,
                    pk_GH.grsk,
                )?;
                //multiexponentiation proof on account public keys

                self.multi_exponential_pk_proof.verify_multiexponential_pubkey_proof(
                  //  verifier,
                    &self.c_B_dash,
                    shuffle_output,
                    &pc_gens,
                    &xpc_gens,
                    &base_pk,
                    &pk_GH,
                )?;
                //multiexponentiation proof on account commitments
                self.multi_exponential_commitment_proof
                    .verify_multiexponential_elgamal_commit_proof(
                       // verifier,
                        &self.c_B,
                        shuffle_output,
                        shuffle_input,
                        &pc_gens,
                        &xpc_gens,
                        &pk_GH,
                        &exp_x,
                    )?;
                Ok(())
            } else {
                Err("Shuffle Proof Verify:prod pf i .. N (yi + x^i -z) failed")
            }
        } else {
            Err("Shuffle Proof Verify: Invalid length of commitment vectors")
        }
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

// Wrapper functions to keep the underlying serial implementation consistent with parallel implementation
// These functions are used in the parallel implementation of shuffle proof
// The fundtion arguments are passed as vectors directly to the parallel implementation

fn wrapper_hadamard_proof(b_dash: Array2D<Scalar>, shuffled_tau: Array2D<Scalar>, b_matrix:Array2D<Scalar>,
commitment_b_dash:[CompressedRistretto; ROWS], commitment_tau: [CompressedRistretto; ROWS], commitment_b: [CompressedRistretto; ROWS],
s_dash: [Scalar; ROWS], r_dash: [Scalar; ROWS], s: [Scalar; ROWS]) -> (HadamardProof, HadamardStatement){
           
           let xpc_gens = VectorPedersenGens::new(ROWS + 1);
           // Hadamard proof: b' o tau = b
            HadamardProof::create_hadamard_argument_proof(
            //  prover,
              &xpc_gens,
              &b_dash,
              &shuffled_tau,
              &b_matrix,
              &commitment_b_dash,
              &commitment_tau,
              &commitment_b,
              &s_dash,
              &r_dash,
              &s,
          )
}

fn wrapper_product_proof(witness: Array2D<Scalar>, b_matrix: Array2D<Scalar>, y: Scalar, z: Scalar, r: [Scalar;ROWS], s:[Scalar; ROWS])->(ProductProof, ProductStatement) {
    let xpc_gens = VectorPedersenGens::new(ROWS + 1);
   // let pc_gens = PedersenGens::default();

    let a_as_rows = witness.as_row_major();
    let b_as_rows = b_matrix.as_row_major();
    let f: Vec<_> = a_as_rows
        .iter()
        .zip(b_as_rows.iter())
        .map(|(a, b)| a * y + b)
        .collect();
    // [t] =  y [r] + [s]
    let t: Vec<_> = r.iter().zip(s.iter()).map(|(r, s)| r * y + s).collect();

    let e: Vec<_> = f.iter().map(|f| f - z).collect();
    let e_2d = Array2D::from_column_major(&e, ROWS, COLUMNS);

   // ProductProof::create_product_argument_proof( &e_2d, &t, &pc_gens, &xpc_gens)
    // recreate product proof here using multi threads for MultiHadamard and SVP proof
     // create a random transcript for proof
     let mut transcript = merlin::Transcript::new(b"ProductProof");
     // create prover to generate TranscriptRng for random scalar generation
     let  prover = Prover::new(b"ShuffleProof", &mut transcript);
     //convert witness to column major representation
     let witness_as_cols = e_2d.as_columns();

     //compute Xcomit on Witness Matrix
     let mut c_prod_A = Vec::<RistrettoPoint>::new();
     for i in 0..ROWS {
         c_prod_A.push(xpc_gens.commit(&witness_as_cols[i], t[i]));
     }
     // cb = com(product (from 1 to m) a1j, ..., product (from 1 to m)
     let mut bvec = Vec::<Scalar>::new();
     let mut product: Scalar;
     for row_iter in e_2d.rows_iter() {
         product = Scalar::one();
         for element in row_iter {
             product = product * element;
         }
         bvec.push(product);
     }
       // transcriptRng using public transcript data + secret for proof + external source
        let mut rng = prover.prove_rekey_witness_transcript_rng(&bvec);
        //create challenge s for bvec comit
        let s: Scalar = Scalar::random(&mut rng);
        let cb = xpc_gens.commit(&bvec, s);

        //create b. i.e., product of all elements in A
        let b = bvec.iter().product::<Scalar>();

        let svp_state = crate::shuffle::singlevalueproduct::SVPStatement {
            commitment_a: cb.compress(),
            b,
        };
        //spawn a new thread to create MultiHadamard proof for Product argument in parallel
        //create multihadamard product proof
        let witness_matrix = e_2d.clone();
        let bvec_hadamard = bvec.clone();
        let handle_multi_hadamard: std::thread::JoinHandle<(MultiHadamardProof, MultiHadamardStatement)> = std::thread::spawn(move || {
            crate::shuffle::product::wrapper_product_argument_multihadamard_proof(witness_matrix, bvec_hadamard,c_prod_A, cb, t, s)
        });

        //create single value product proof
        // spawn a new thread to create SVP proof in parallel
        let s_svp = s.clone();
        let bvec_svp = bvec.clone();
        let handle_svp: std::thread::JoinHandle<SVPProof> = std::thread::spawn(move || {
            crate::shuffle::product::wrapper_single_value_product_proof(s_svp, bvec_svp)
        });

        //join all threads
        let (multi_hadamard_proof, multi_hadamard_statement) = match handle_multi_hadamard.join(){
            Ok(result) => result,
            Err(_) => panic!("Error in Joining MultiHadamard Proof Thread"),
        };
        let svp_proof = match handle_svp.join(){
            Ok(result) => result,
            Err(_) => panic!("Error in Joining SVP Proof Thread"),
        };
        //create product proof
        let product_proof = ProductProof {
            multi_hadamard_proof,
            svp_proof,
        };
        let product_statement = ProductStatement {
            multi_hadamard_statement,
            svp_statement: svp_state,
        };
        (product_proof, product_statement)
        
}
fn wrapper_ddh_proof(g_i: Vec<RistrettoPoint>, h_i:Vec<RistrettoPoint>, exp_x:[Scalar;N], G:RistrettoPoint, H:RistrettoPoint, rho:Scalar) -> (DDHProof, DDHStatement){
    DDHProof::create_verify_update_ddh_prove(&g_i, &h_i, &exp_x, G, H, rho)
}

fn wrapper_multiexponential_publickey(upk: Vec<RistrettoPublicKey>, b_dash_matrix: Array2D<Scalar>, s_dash:[Scalar; ROWS]) -> MultiexpoProof {
    let xpc_gens = VectorPedersenGens::new(ROWS + 1);
    let pc_gens = PedersenGens::default();
    let base_pk = RistrettoPublicKey::generate_base_pk();
    MultiexpoProof::create_multiexponential_pubkey_proof(
        // prover,
         &upk,
         &b_dash_matrix,
         &s_dash,
         &pc_gens,
         &xpc_gens,
         &base_pk,
     )
}

fn wrapper_multiexponential_commitment(updated_commitment: Vec<ElGamalCommitment>, b_matrix: Array2D<Scalar>, s:[Scalar; ROWS], rho: Scalar, pk_GH: RistrettoPublicKey) -> MultiexpoProof {
    let xpc_gens = VectorPedersenGens::new(ROWS + 1);
    let pc_gens = PedersenGens::default();
    MultiexpoProof::create_multiexponential_elgamal_commit_proof(
        // prover,
         &updated_commitment,
         &b_matrix,
         &s,
         &pc_gens,
         &xpc_gens,
         &pk_GH,
         rho,
     )
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
            let (acc, _) = Account::generate_account(pk);
            account_vector.push(acc);
        }
        let result = Shuffle::input_shuffle(&account_vector);
        let shuffle = result.unwrap();
       // let pc_gens = PedersenGens::default();
        //generate Xcomit generator points of length m+1
       // let xpc_gens = VectorPedersenGens::new(ROWS + 1);

        //let mut transcript_p = Transcript::new(b"ShuffleProof");
        //let mut prover = Prover::new(b"Shuffle", &mut transcript_p);
        //let witness = shuffle.pi.get_permutation_as_scalar_matrix();
        //println!("Shuffle witness {:?}", witness);
        // time this code
        use std::time::Instant;
        let now = Instant::now();

        let (proof, statement) =
            ShuffleProof::create_shuffle_proof(shuffle.clone());
            println!("Elapsed: {:.2?}", now.elapsed());
      //  let mut transcript_v = Transcript::new(b"ShuffleProof");
      //  let mut verifier = Verifier::new(b"Shuffle", &mut transcript_v);
        let now = Instant::now();
        let verify = proof.verify(
            &statement,
            &shuffle.get_inputs_vector(),
            &shuffle.get_outputs_vector(),
        );
        println!("Elapsed:Verify {:.2?}", now.elapsed());
        println!("Shuffle verify: {:?}", verify);
        assert!(verify.is_ok());
    }

    #[test]
    fn shuffle_proof_parallel_test() {
        let mut account_vector: Vec<Account> = Vec::new();
        // lets create these accounts and associated keypairs
        for _ in 0..9 {
            let mut rng = rand::thread_rng();
            let sk: RistrettoSecretKey = SecretKey::random(&mut rng);
            let pk = RistrettoPublicKey::from_secret_key(&sk, &mut rng);
            let (acc, _) = Account::generate_account(pk);
            account_vector.push(acc);
        }
        let result = Shuffle::input_shuffle(&account_vector);
        let shuffle = result.unwrap();
   
        // time this code
        use std::time::Instant;
        let now = Instant::now();

        let (proof, statement) =
            Shuffle::create_shuffle_proof_parallel(shuffle.clone()).unwrap();
            println!("Elapsed: {:.2?}", now.elapsed());
    
        let now = Instant::now();
        let verify = proof.verify(
            &statement,
            &shuffle.get_inputs_vector(),
            &shuffle.get_outputs_vector(),
        );
        println!("Elapsed:Verify {:.2?}", now.elapsed());
        println!("Shuffle verify: {:?}", verify);
        assert!(verify.is_ok());
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
            let (acc, _) = Account::generate_account(pk);
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
            let (acc, _) = Account::generate_account(pk);
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
            .map(|(acc, t)| Account::update_account(*acc, 0u64.into(), *t, rho))
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
            let (acc, _) = Account::generate_account(pk);
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
            .map(|(acc, t)| Account::update_account(*acc, 0u64.into(), *t, rho))
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
            let (acc, _) = Account::generate_account(pk);
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
}
