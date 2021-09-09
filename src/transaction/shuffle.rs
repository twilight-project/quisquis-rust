use curve25519_dalek::{
    scalar::Scalar
};
use crate::{
    accounts::Account
};

use rand::rngs::OsRng;
use rand::{CryptoRng, Rng};
use array2d::{Array2D};

#[derive(Debug, Clone)]
pub struct Permutation {
    perm_matrix: Array2D<usize>,
}
//Matrix Size 
const N: usize = 9;   //N - Length of vector
const ROWS: usize = 3;   //m
const COLUMNS: usize = 3; //n


impl Permutation {
    pub fn new<R: Rng + CryptoRng>(rng: &mut R, n: usize) -> Self {
        let mut permutation: Vec<usize> = (0..n).collect();
        for i in (1..permutation.len()).rev() {
            // invariant: elements with index > i have been locked in place.
            permutation.swap(i, rng.gen_range(0, i + 1));
        }
        let perm_matrix = Array2D::from_row_major(&permutation, ROWS,COLUMNS);
        Self {perm_matrix}
    }

    //Set the permutation matrix explicitly
    pub fn set(&mut self, matrix: Array2D<usize>){
        self.perm_matrix = matrix;
    }

    //Inverse the permutation matrix for use in Input shuffle
    pub fn invert_permutation(&self)-> Array2D<usize> {
        let mut inverse = vec![0; N];
        let permutation = self.perm_matrix.as_row_major();
       for i in 0..permutation.len() {
            inverse[permutation[i]]  = i ;            
        }
        let perm_matrix = Array2D::from_row_major(&inverse, ROWS,COLUMNS);
        perm_matrix
    }
    // Produces a commitment to the permutation matrix> TBI
   // fn commit(&self ) -> Result<()> 
}

#[derive(Debug, Clone)]
pub struct Shuffle {
    inputs: Array2D<Account>,     //Before shuffle     mxn
    outputs: Array2D<Account>,    //After shuffle and update    mxn
    shuffled_tau: Array2D<Scalar>,         //Scalars after shuffle for PK update   mxn 
    rho: Scalar,                  //Scalar for Commitment Update  
    pi: Permutation,              //Permutaion matrix in the form m x n
}


impl Shuffle {
    pub fn new(
        inputs: &Vec<Account>,   //Accounts to be shuffled
        shuffle: u32      // 1 -> Input shuffle, 2-> Output shuffle
    ) -> Result<Self, &'static str> {
        let len = inputs.len();
        if len == 0 {
            return Err("Error::EmptyShuffle");
        }

        let mut pi = {
            Permutation::new(&mut OsRng, len)
        };

        let tau: Vec<_> = (0..len).map(|_| Scalar::random(&mut OsRng)).collect();
        let rho = Scalar::random(&mut OsRng);
        let permutation =  pi.perm_matrix.as_row_major();

        //shuffle Inputs
        let shuffled_accounts: Vec<_> = (0..len).map(|i| inputs[permutation[i]].clone()).collect();
        
        //if Input account shuffle according to QuisQuis
        if shuffle == 1{
            
            //Invert the permutation for Inputs shuffle
            pi.set(pi.invert_permutation());
            
             //Input accounts == input` in this case. updating inputs with tau and rho
            let updated_inputs: Vec<_> = inputs.iter().zip(tau.iter()).map(|(acc, t)| Account::update_account(*acc, 0, *t, rho)).collect();
            
            //Convert to a 2D array representation
            let outputs = Array2D::from_row_major(&updated_inputs, ROWS,COLUMNS);
            let inputs = Array2D::from_row_major(&shuffled_accounts, ROWS,COLUMNS);
            let shuffled_tau = Array2D::from_row_major(&tau, ROWS,COLUMNS);
            return Ok(Self {inputs, outputs, shuffled_tau, rho, pi });
        }
        else if shuffle == 2{
            //Shuffled and Updated Accounts
            let shuffled_outputs: Vec<_> = shuffled_accounts.iter().zip(tau.iter()).map(|(acc, t)| Account::update_account(*acc, 0, *t, rho)).collect();
            //Convert to a 2D array representation
            let outputs = Array2D::from_row_major(&shuffled_outputs, ROWS,COLUMNS);
            let inputs = Array2D::from_row_major(&inputs, ROWS,COLUMNS);
            let shuffled_tau = Array2D::from_row_major(&tau, ROWS,COLUMNS);
            return Ok(Self {inputs, outputs, shuffled_tau, rho, pi });
        }
        return Err("Error::Invalid Shuffle Selection");

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

    //pub fn gen_proof(&self,)
        
}
/*
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ShuffleProof {

}
impl ShuffleProof {
    
}*/


// ------------------------------------------------------------------------
// Tests
// ------------------------------------------------------------------------

#[cfg(test)]
mod test {
    use super::*;
    use crate::{
        keys::{PublicKey, SecretKey},
        ristretto::{
            RistrettoPublicKey,
            RistrettoSecretKey
        }
    };
    #[test]
    fn permutation_matrix_test() {
        let perm = Permutation::new(&mut OsRng, N);
        println!("Permuted Matrix {:?}",perm.perm_matrix.as_rows());
    }
    #[test]
    fn inverse_permutation_test() {
        let perm = Permutation::new(&mut OsRng, N);
        println!("Permuted Vector {:?}",perm);
        let inv = perm.invert_permutation();
        println!("Inverted Vector {:?}",inv);
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
         let pi = {
             Permutation::new(&mut OsRng, len)
         };
         let permutation =  pi.perm_matrix.as_row_major();
         //shuffle Account Vector
         let shuffled_accounts: Vec<_> = (0..len).map(|i| account_vector[permutation[i]].clone()).collect();
         assert_ne!(account_vector, shuffled_accounts)

    }
    #[test]
    fn shuffle_test() {
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
        let shuffle = {
            Shuffle::new(&account_vector,1)
        };
        let inp = shuffle.as_ref().unwrap().inputs.as_row_major();
        let out = shuffle.as_ref().unwrap().outputs.as_row_major();
        let pi = &shuffle.as_ref().unwrap().pi;
        let perm = pi.perm_matrix.as_row_major();
        let tau = shuffle.as_ref().unwrap().shuffled_tau.as_row_major();
        let rho = shuffle.as_ref().unwrap().rho;
        
        let shuffled_inputs: Vec<_> = (0..9).map(|i| inp[perm[i]].clone()).collect();
        let shuffled_updated: Vec<_> = shuffled_inputs.iter().zip(tau.iter()).map(|(acc, t)| Account::update_account(*acc, 0, *t, rho)).collect();

        assert_eq!(out, shuffled_updated)
    
    }
}