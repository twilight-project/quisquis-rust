use bulletproofs::PedersenGens;
use curve25519_dalek::{
    ristretto::{CompressedRistretto, RistrettoPoint},
    scalar::Scalar,
    constants::RISTRETTO_BASEPOINT_POINT
};
use crate::{
    accounts::{Account,Prover, Verifier},
    ristretto::RistrettoPublicKey,
    elgamal::ElGamalCommitment
};
use sha3::Sha3_512;
use rand::rngs::OsRng;
use rand::{CryptoRng, Rng};
use array2d::{Array2D};
use curve25519_dalek::traits::MultiscalarMul;
use curve25519_dalek::traits::VartimeMultiscalarMul;
use std::convert::TryInto;


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
        let mut permutation: Vec<usize> = (1..n+1).collect();
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
        let mut inverse = vec![0; self.perm_matrix.num_elements()];
        let permutation = self.perm_matrix.as_row_major();
       for i in 0..permutation.len() {
            inverse[permutation[i]-1]  = i + 1;            
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
    // generate random values for Permutation and Scalars
    fn random_initialization(len: usize) -> (Permutation, Vec<Scalar>, Scalar){
        //Create a new random permutation Matrix 
        let pi = {
            Permutation::new(&mut OsRng, len)
        };
        
        //Create Random tau used for updating the Account Pks
        let tau: Vec<_> = (0..len).map(|_| Scalar::random(&mut OsRng)).collect();
        
        //Create Random rho used for updating the Account Commitments
        let rho = Scalar::random(&mut OsRng);
        (pi, tau, rho)
    }


    pub fn input_shuffle(
        inputs: &Vec<Account>,   //Accounts to be shuffled
    ) -> Result<Self, &'static str> {
        let len = inputs.len();
        if len == 0 {
            return Err("Error::EmptyShuffle");
        }
        //Get random inital values
        let (mut pi, tau, rho) = Self::random_initialization(len);

        //Convert Matrix to Vector in row major order
        let permutation =  pi.perm_matrix.as_row_major();

        //shuffle Input accounts randomly using permutation matrix
        let shuffled_accounts: Vec<_> = (0..len).map(|i| inputs[permutation[i]-1].clone()).collect();    
        
        //Invert the permutation Matrix for Inputs shuffle
        pi.set(pi.invert_permutation());
            
        //Input accounts == input` in this case. updating input accounts with tau and rho
        let updated_inputs: Vec<_> = inputs.iter().zip(tau.iter()).map(|(acc, t)| Account::update_account(*acc, 0, *t, rho)).collect();
            
        //Convert to a 2D array representation
        let outputs = Array2D::from_row_major(&updated_inputs, ROWS,COLUMNS);
        let inputs = Array2D::from_row_major(&shuffled_accounts, ROWS,COLUMNS);
        let shuffled_tau = Array2D::from_row_major(&tau, ROWS,COLUMNS);
        
        return Ok(Self {inputs, outputs, shuffled_tau, rho, pi });      
    }

    pub fn output_shuffle(
        inputs: &Vec<Account>,   //Accounts to be shuffled
    ) -> Result<Self, &'static str> {
        let len = inputs.len();
        if len == 0 {
            return Err("Error::EmptyShuffle");
        }

        //Get random inital values
        let (pi, tau, rho) = Self::random_initialization(len);
        let permutation =  pi.perm_matrix.as_row_major();

        //shuffle Inputs
        let shuffled_accounts: Vec<_> = (0..len).map(|i| inputs[permutation[i]-1].clone()).collect();
        
        //Shuffled and Updated Accounts
        let shuffled_outputs: Vec<_> = shuffled_accounts.iter().zip(tau.iter()).map(|(acc, t)| Account::update_account(*acc, 0, *t, rho)).collect();
        
        //Convert to a 2D array representation
        let outputs = Array2D::from_row_major(&shuffled_outputs, ROWS,COLUMNS);
        let inputs = Array2D::from_row_major(&inputs, ROWS,COLUMNS);
        let shuffled_tau = Array2D::from_row_major(&tau, ROWS,COLUMNS);
        return Ok(Self {inputs, outputs, shuffled_tau, rho, pi });

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
//product and multiexponential argument
    pub fn shuffle_argument_prove(&self){
        let pc_gens = PedersenGens::default();
        //generate Xcomit generator points of length m+1
        let xpc_gens = extended_pedersen_gen(ROWS+1, pc_gens.B, pc_gens.B_blinding);

        //create challenge x for b and b' vectors    
        let x = Scalar::random(&mut OsRng);
        //create b and b' vectors to be used for Multiexponentiationa and hadamard proof later
        let (b_mat, b_dash) = create_b_b_dash(x, &self.shuffled_tau.as_row_major(), &self.pi.perm_matrix.as_row_major());
       // println!("{:?}", b_mat);

        //Create Pk^x^ for testing purposes here. Should be refactored later.
        // x^i
        let exp_xx: Vec<_> = exp_iter(x).take(9).collect();
        // gather g, h from Public key    
        // gather g, h from Public key
        let pk: Vec<RistrettoPublicKey> = self.inputs.as_row_major().iter().map(|acc| acc.pk).collect();
        
        let g_i: Vec<_> = pk.iter().map(|pt| pt.gr.decompress().unwrap()).collect();
        let h_i: Vec<_> = pk.iter().map(|pt| pt.grsk.decompress().unwrap()).collect();
        // (G, H) = sum of all i (pk_i * x^i)
        let G = RistrettoPoint::multiscalar_mul(exp_xx.iter().clone(), g_i.iter().clone());
        let H = RistrettoPoint::multiscalar_mul(&exp_xx, h_i.iter().clone());

        let pk = RistrettoPublicKey{gr: G.compress(), grsk: H.compress()};

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

        //create vector of -rho of length N
        //let neg_rho = -self.rho;
        //let rho_vec: Vec<Scalar> = vec![neg_rho, neg_rho, neg_rho, neg_rho, neg_rho, neg_rho, neg_rho, neg_rho, neg_rho];   

        //create rho = -rho . b
        //let rho_b = vector_multiply_scalar(&rho_vec, &b_mat.as_row_major());

        //Calling Multiexponentiation Prove for PK Update and shuffle
       
        self.multiexp_pubkey_prove(&b_dash, &pc_gens , &xpc_gens, G, H);
        
        //Calling Multiexponentiation Prove for COMIT Update and shuffle
        //self.multiexp_commit_prove(&b_mat, &pc_gens, &xpc_gens, &pk, rho_b);
       
      // self.product_argument_prove(&b_mat, &pc_gens, &xpc_gens, x);
      
        
    }

    pub fn verify_shuffle_argument(a_comit: &[RistrettoPoint], b_comit: &[RistrettoPoint])/*-> bool*/ {
        //check if C_A and C_B ∈ G^m
        //all vectors should be of length m 
        assert_eq!(a_comit.len(), ROWS);
        assert_eq!(b_comit.len(), ROWS);
        
        
        
        

        
    }

    pub fn product_argument_prove(&self, b_matrix: &Array2D<Scalar>, pc_gens: &PedersenGens, xpc_gens: &Vec<RistrettoPoint>, x_chal: Scalar){
        //create random number r to vector commit on witness. The commitment is on columns of A matrix
        //compute r. it is the witness in c_A
        let r: Vec<_> = (0..COLUMNS).map(|_| Scalar::random(&mut OsRng)).collect();

         //create statement 
         //compute Xcomit on A
         //convert to column major representation
         //convrt pi matrix to scalar
        //let pi_scalar: Vec<_> = self.pi.perm_matrix.as_row_major().iter().map(|i| Scalar::from(*i as u64)).collect();
        
        /*CREATING PI MATRIX FOR TESTING THE CODE. Actually the pi matrix sghould have values from 1 to 9. There should be no 0 value. Avoiding 0 for the time being. Adjust the pi matrix and shuffle accordingly */
        
        let pi_scalar: Vec<_> = vec![Scalar::from(7u64),Scalar::from(6u64),Scalar::from(1u64),Scalar::from(5u64),Scalar::from(3u64),Scalar::from(4u64),Scalar::from(2u64),Scalar::from(8u64),Scalar::from(9u64)];
        let pi_2d = Array2D::from_row_major(&pi_scalar, ROWS, COLUMNS);
        let perm_scalar_as_cols = pi_2d.as_columns();
        let mut comit_a_vec = Vec::<RistrettoPoint>::new();
        for i in 0..COLUMNS{
            comit_a_vec.push(extended_commit(&perm_scalar_as_cols[i], r[i], &xpc_gens));
        }
        // cb = com(product (from 1 to m) a1j, ..., product (from 1 to m) 
        //println!("{:?}",pi_2d);
        let mut bvec = Vec::<Scalar>::new();
        for row_iter in pi_2d.rows_iter() {
            let mut product = Scalar::one();
            for element in row_iter {
               product = product * element;
            }
            bvec.push(product);
        }
       // println!("{:?}",bvec);

        //create challenge s for bvec comit    
        let s = Scalar::random(&mut OsRng);
        let cb = extended_commit(&bvec, s, &xpc_gens);

        //create b. i.e., product of all elements in A
        let b = bvec.iter().product::<Scalar>();
        // hadamard argument convinces verifier you know
	    // A and b st prod prod A = b :) with b a VECTOR
        self.hadamard_product_arg(&pi_2d, &pc_gens, &xpc_gens, &bvec, &comit_a_vec, &cb, x_chal, r, s);
        //self.single_value_argument_prover(&pc_gens, &xpc_gens, cb, b, s, &bvec);

    }
    pub fn hadamard_product_arg(&self, pi_2d: &Array2D<Scalar>, pc_gens: &PedersenGens, xpc_gens: &Vec<RistrettoPoint>, bvec: &Vec<Scalar>, comit_a: &Vec<RistrettoPoint>, cb: &RistrettoPoint, x_chal: Scalar, r: Vec<Scalar>, s_3: Scalar){
        // ai, b, vectors of length n
        // cA, cb, a1, ..., am, bvec, st bvec = product ai
        // (with entrywise multiplication)
        // cA = com(A;rvec); cb = com(bvec; s)
        
        //s1 = r[0]
        let s_1 = r[0];

        //create b1,b2....bm
        let perm_scalar_as_cols = pi_2d.as_columns();
        // b1 =a1
        let b1 = perm_scalar_as_cols[0].clone();
        // b2 = a1 * a2
        let a2 = perm_scalar_as_cols[1].clone();
        let b2: Vec<_> = b1.iter().zip(a2.iter()).map(|(i, j)| i * j).collect();
        //b3 = b
        let b3 = bvec.clone();

        let s2 = Scalar::random(&mut OsRng);
        let c_B2 = extended_commit(&b2, s2, &xpc_gens);
        let c_B1 = comit_a[0].clone();
        let c_B3 = cb.clone();

        //Send C_B vector to verifier

        //CREATE CHALLENGE X AND Y
        let x = x_chal;
        let y = Scalar::random(&mut OsRng);
        
        let x_exp: Vec<_> = exp_iter(x).take(2*ROWS).collect();
        //let x_exp_m = &x_exp[1..4].to_vec();
        let c_D1 = c_B1 * x_exp[1];
        let c_D2 = c_B2 * x_exp[2];
        let c_D3 = c_B3 * x_exp[3];
        //c_D = c_B_2 ^ x c_B_3^x^2
        let c_D = c_B2 * x_exp[1] + c_B3 * x_exp[2];
        let scalar_one = Scalar::one();
        //println!("{:?}", scalar_one);

        let scalar_one_inv = -scalar_one;
        
        //println!("{:?}", scalar_one_inv);
        let mut scalars:Vec<Scalar> = vec![
            scalar_one_inv.clone(),
            scalar_one_inv.clone(),
            scalar_one_inv.clone(),
        ];

        let c_minus_one = extended_commit(&scalars, Scalar::zero(), &xpc_gens);

        //Calculate openings of c_D1, c_D2, and c_D3
        //d1 = xb1
        let d_1: Vec<_> = b1.iter().map(|i| i * x_exp[1]).collect();
        let d_2: Vec<_> = b2.iter().map(|i| i * x_exp[2]).collect();
        let d_3: Vec<_> = b3.iter().map(|i| i * x_exp[3]).collect();
        
        //compute t's
        let t_1 = s_1 *  x_exp[1];
        let t_2 = s2 *  x_exp[2];
        let t_3 = s_3 *  x_exp[3];
       
        //compute d 
        let xb2 : Vec<_> = b2.iter().map(|i| i * x_exp[1]).collect();
        let x2b3 : Vec<_> = b3.iter().map(|i| i * x_exp[2]).collect();
        let d: Vec<_> = xb2.iter().zip(x2b3.iter()).map(|(i, j)| i + j).collect();
       
        //compute t 
        let xs2 = x_exp[1] * s2;
        let x2s3 = x_exp[2] * s_3;
        let t = xs2 + x2s3;

        
        //create A and B matrices and r,s arrays to be used in Zero argument
        //create r and s vector for Zero Argument. r would be the same while s now will be t
        let s: Vec<Scalar> = vec![t_1, t_2, t];
        
        //create A as matrix for zero argument. A is actually a2,a3,a-1
        
        let a_columns = vec![perm_scalar_as_cols[1].clone(),perm_scalar_as_cols[2].clone(),scalars];
        let a_array = Array2D::from_columns(&a_columns);

        //create B as matrix for zero argument. B is actually D here
        let columns = vec![d_1,d_2,d];
        let d_array = Array2D::from_columns(&columns);

        
        //cA = (cA2,cA3,c-1) with openings a2,a3,-1 and r = (r2,r3,0)
        let cA:Vec<RistrettoPoint> = vec![ comit_a[1],comit_a[2], c_minus_one];
        //cB = (cD1,cD2,cD) with openings d1,d2,d and s=(s1,s2,s)

        let cB:Vec<RistrettoPoint> = vec![ c_D1,c_D2, c_D];


        
        // engage in a zero argument, for the committed values satisfying 0 = a2 ⇤ d1 + a3 ⇤ d2   1 ⇤ d.
        self.zero_argument(&a_array, &d_array, pc_gens, xpc_gens, &cA,&cB, &r, &s, y);

    }

    pub fn zero_argument(&self, a_2d: &Array2D<Scalar>, b_2d: &Array2D<Scalar>, pc_gens: &PedersenGens, xpc_gens: &Vec<RistrettoPoint>, comit_a: &Vec<RistrettoPoint>, comit_b: &Vec<RistrettoPoint>, r_vec: &Vec<Scalar>, s_vec:&Vec<Scalar>,y: Scalar){
        //pick a0, bm 
        let a0: Vec<_> = (0..COLUMNS).map(|_| Scalar::random(&mut OsRng)).collect();
        let b3: Vec<_> = (0..COLUMNS).map(|_| Scalar::random(&mut OsRng)).collect();

        //pick r0, s3
        let r0 = Scalar::random(&mut OsRng);
        let s3 = Scalar::random(&mut OsRng);

        //comit on a0 and bm
        let c_a0 = extended_commit(&a0, r0, xpc_gens);
        let c_b3= extended_commit(&b3, s3, xpc_gens);

        
        //Create Full A and B vector to be used in bilinearmap. Add a0 to A and b3 to B
        let a_orig_colums = a_2d.as_columns();
        //for creating the new matrix
        let a_columns = vec![a0, a_orig_colums[0].clone(), a_orig_colums[1].clone(), a_orig_colums[2].clone()];
        let a_Array = Array2D::from_columns(&a_columns);

        let b_orig_colums = b_2d.as_columns();
        //for creating the new matrix
        let b_columns = vec![b_orig_colums[0].clone(), b_orig_colums[1].clone(), b_orig_colums[2].clone(), b3];
        let b_Array = Array2D::from_columns(&b_columns);
        
        //for k = 0,...,2m : compute d_k

        //BILINEAR MAP
        
        let dv = bilnearmap(&a_Array, &b_Array, y);

        //pick random t for committing d
        let mut t: Vec<_> = (0..2*ROWS+1).map(|_| Scalar::random(&mut OsRng)).collect();
        t[ROWS+1] = Scalar::zero();

        //calculate regular committments to all d's
        let c_D : Vec<_> = dv.iter().zip(t.iter()).map(|(i, t)| pc_gens.commit(*i, *t) ).collect();

        //The verifier picks a challenge x which is z in my view

        let z_chal = Scalar::random(&mut OsRng);

        // set x = (x, x^2, x^3, x^4.., x^m). Thesis says length should be m but rebekkah has its length as 2m-2
        let x_exp: Vec<_> = exp_iter(z_chal).take(2*ROWS+1).collect();
        let x_exp_m = &x_exp[0..4].to_vec();
        let x_k = &x_exp[0..2*ROWS+1].to_vec();
        //creating this explicitly for now. Shold be done in iterator
        let mut x_m_j = x_exp_m.clone();
        x_m_j.reverse();
        
        
        //creating a_bar 
        //get columns of A matrix 
        let a_cols = a_Array.as_columns();
        let b_cols = b_Array.as_columns();
        
        //calculate a0 + a1x + a2x^2 + ...
        let a1x: Vec<_> = a_cols[1].iter().map(| i | i * x_exp_m[1]).collect();
        let a2x2: Vec<_> = a_cols[2].iter().map(| i | i * x_exp_m[2]).collect();
        let a3x3: Vec<_> = a_cols[3].iter().map(| i | i * x_exp_m[3]).collect();

        //calculate x3b0 + b1x2 + b2x + ...
        let b0x3: Vec<_> = b_cols[0].iter().map(| i | i * x_m_j[0]).collect();
        let b1x2: Vec<_> = b_cols[1].iter().map(| i | i * x_m_j[1]).collect();
        let b2x: Vec<_> = b_cols[2].iter().map(| i | i * x_m_j[2]).collect();

        let mut a_bar_vec = Vec::<Scalar>::new();
        let mut b_bar_vec = Vec::<Scalar>::new();
        //creating a_bar and b_bar
        for i in 0..3{
            a_bar_vec.push(a_cols[0][i] + a1x[i] + a2x2[i] + a3x3[i]);
            b_bar_vec.push(b0x3[i] + b1x2[i] + b2x[i] + b_cols[3][i]);

        }
        //extend r and s vectors 
        let r_ext_vec = vec![r0, r_vec[1],r_vec[2], Scalar::zero()];
        let s_ext_vec = vec![s_vec[0], s_vec[1],s_vec[2], s3];

        //compute r_bar = r . x. x is [0....x^n]
       let r_bar: Scalar = vector_multiply_scalar(&r_ext_vec,&x_exp_m);
       
       //compute s_bar = s . x. x is [0....x^n]
       let s_bar: Scalar = vector_multiply_scalar(&s_ext_vec,&x_m_j);

       //compute t_bar = t . x. x is [0....x^2m+1]
       let t_bar: Scalar = vector_multiply_scalar(&t,&x_k);


        //Third Message. Send a_bar, b_bar, r_bar, s_bar, t_bar  
       
       
        //VERIFICATION CODE HERE. Move to other function later
       
       //Verifying c_d_m+1 = com(0,0)
       let comit_d_m_1 = c_D[ROWS+1];
       let zz = Scalar::zero();let zzz = Scalar::zero();
       let comit_0_0 = pc_gens.commit(zz, zzz);
       if comit_0_0 == comit_d_m_1{
           println!("Cdm+1 TRUE");
       }


       // prod i=0..m (c_Ai^x^i ) = com(a_bar,r)
       //Com_A_0 ^ X^0 = com_a0
        
        //can use multiscalar_multiplication. should be done for all elements. 
        let x_m_1 = &x_exp_m[1..4].to_vec();
        let temp_a = RistrettoPoint::multiscalar_mul(x_m_1.iter().clone(), comit_a.iter().clone());
        let comit_a_product = c_a0 + temp_a;

       //com(a_bar,r)
       let comit_a_bar = extended_commit(&a_bar_vec, r_bar, xpc_gens);
       if comit_a_bar == comit_a_product{
        println!(" comit_a_bar Verifies");
        }
       // prod j=0..m (c_Bj^x^(m-j) ) = com(b_bar,s)
       //Com_B_m ^ X^0 = com_b3
 
        //can use multiscalar_multiplication. should be done for all elements. 
        let  b_full = vec![comit_b[0], comit_b[1],comit_b[2], c_b3];
        let comit_b_full = RistrettoPoint::multiscalar_mul(x_m_j.iter().clone(), b_full.iter().clone());

       //com(b_bar,s)
       let comit_b_bar = extended_commit(&b_bar_vec, s_bar, xpc_gens);
       if comit_b_bar == comit_b_full{
        println!(" comit_b_bar Verifies");
       }else{
        println!(" comit_b_bar Veification fails");
       }
       
       // Verify for k=0..2m c_D_k ^(x ^k)  ==  com(a_bar * b_bar; t) where * is bilinear map

       //com(a_bar * b_bar; t)
       //create y^i 
       let y_exp: Vec<_> = exp_iter(y).take(ROWS+1).collect();
       let y_i = &y_exp[1..4].to_vec();
       let a_bar_b_bar = single_bilinearmap(&a_bar_vec, &b_bar_vec, y_i );
       let comit_a_bar_b_bar = pc_gens.commit(a_bar_b_bar, t_bar);

       //k=0..2m c_D_k ^(x ^k)
       let c_D_x_k:RistrettoPoint = c_D.iter().zip(x_k.iter()).map(|(c, xk)| c*xk ).sum();
       
       if comit_a_bar_b_bar == c_D_x_k{
        println!(" c_D_x_k Verifies");
       }else{
        println!(" c_D_x_k Veification fails");
       }


        
    }
    pub fn single_value_argument_prover(&self, pc_gens: &PedersenGens, xpc_gens: &Vec<RistrettoPoint>, comit_a: RistrettoPoint, b:Scalar, r: Scalar, a_vec:&Vec<Scalar>){
        //compute the first message
        //compute b1 =a1 =58,b2 =a1 ·a2 =48,b3 =b2 ·b3 =75,b4 =b3 ·a4 =b=10,
        let mut bvec = Vec::<Scalar>::new();

	    let mut prod :Scalar =  Scalar::one();
	    for ai in a_vec.iter() {
		    prod = prod * ai;
		    bvec.push(prod);
	    }
        //println!("{:?}", bvec);
        //println!("{:?}", a_vec);
        //Pick d1,...,dn, and rd randomly
        let d_vec: Vec<_> = (0..COLUMNS).map(|_| Scalar::random(&mut OsRng)).collect();
        let rd = Scalar::random(&mut OsRng);
        
        let comit_d = extended_commit(&d_vec, rd, &xpc_gens); //send it to verifier

        //compute random delta of COLUMN size and set delta_1 as d_1 and delta_n as 0
        let mut delta_vec: Vec<_> = (0..COLUMNS).map(|_| Scalar::random(&mut OsRng)).collect();
        delta_vec[0] = d_vec[0];
        delta_vec[COLUMNS-1] = Scalar::zero();
        //println!("{:?}", d_vec);
        //println!("{:?}", delta_vec);
        //pick s_1 and s_x
        let s_1 = Scalar::random(&mut OsRng);
        let s_x = Scalar::random(&mut OsRng);

        //Create commitments on delta and d_delta
        //The msg terms are smaller than the number of commitment keys in extended commitment function. Ideally should change the function to accomodate for multiple keys based on the length of the msg array
        // For the time being creating it explicitly here
        //Creating the delta
        
        // cdelta and cDelta have n-1 entries
	    let mut delta = Vec::<Scalar>::new();
        let mut d_delta = Vec::<Scalar>::new();

	    // delta[i] = - delta_vec[i] * d_vec[i+1]
	    for i in 0..COLUMNS-1{
		    delta.push((-delta_vec[i]) * d_vec[i+1]);
	    }

	    // d_Delta[i] = delta_vec[i+1] - a[i+1]*delta_vec[i] - bvec[i]*dvec[i+1]
	    for i in 0..COLUMNS-1 {
            d_delta.push(delta_vec[i+1] - (a_vec[i+1] * delta_vec[i]) - (bvec[i]* d_vec[i+1]));
	    }
        println!("{:?}", delta);
        println!("{:?}", d_delta);
        //Create commitment
        let comit_delta = extended_commit(&delta, s_1, &xpc_gens[0..delta.len()+1].to_vec()); //send it to verifier

        let comit_d_delta = extended_commit(&d_delta, s_x, &xpc_gens[0..d_delta.len()+1].to_vec()); //send it to verifier
        //println!("{:?}", comit_delta);
        //println!("{:?}", comit_d_delta);
         //SEND comit_d, comit_delta, comit_d_delta to the verifier

        // Compute Challenge x
        let x = Scalar::random(&mut OsRng);

        //compute a_bar = x *a_vec + d_vec

        let a_bar: Vec<_> = a_vec.iter().zip(d_vec.iter()).map(|(a,d)| a*x + d).collect();
        
        //compute b_bar = x *bvec + delta_vec

        let b_bar: Vec<_> = bvec.iter().zip(delta_vec.iter()).map(|(b,d)| b*x + d).collect();

        //compute rbar = xr + rd
        let rbar = r*x + rd;

        //compute sbar = xs_x + s_1
        let sbar = s_x * x + s_1;

        //send all this to verifier

        //Verification Code
        // a_bar1 == b_bar1
        if a_bar[0] == b_bar[0]{
            println!("a1 == b1");
        }
        // b_bar_n == b * xllkj
        let xb = b * x;
        if b_bar[COLUMNS-1] == xb{
            println!("xb == bn");
        }
        
        //c_a^x * c_d == com(abar;rbar)

        let comit_a_bar = extended_commit(&a_bar, rbar, xpc_gens);
        let cax = comit_a * x;
        let caxcd = cax + comit_d;

        if caxcd == comit_a_bar{
            println!("caxcd == comit_a_bar");
        }

        //cx∆cδ = comck(x ̃b2 − ̃b1 ̃a2,...,x ̃bn − ̃bn−1 ̃an;  ̃s)

        let cxddelta = comit_d_delta * x;
        let cxdeltadelta = cxddelta + comit_delta;

        let mut comvec = Vec::<Scalar>::new();
        // comvec[i] = x * b_bar[i+1] - b_bar[i]a_bar[i+1]
	    
        for i in 0..COLUMNS-1 {
            comvec.push((b_bar[i+1] * x) - ( b_bar[i] * a_bar[i+1]));
	    }
        let comit_verify = extended_commit(&comvec, sbar, &xpc_gens[0..comvec.len()+1].to_vec()); //send it to verifier

        if cxdeltadelta == comit_verify{
            println!("cxdeltadelta verified");
        }else{
            println!("FALSE");
        }
    }

 
    pub fn multiexp_commit_prove(&self, a_witness: &Array2D<Scalar>, pc_gens: &PedersenGens, xpc_gens: &Vec<RistrettoPoint>, pk: &RistrettoPublicKey, rho: Scalar){
        //create random number s' to vector commit on witness. The commitment is on columns of A matrix
         //compute s'. it is the witness in c_A
         let s_dash: Vec<_> = (0..COLUMNS).map(|_| Scalar::random(&mut OsRng)).collect();

         //create statement 
         //compute Xcomit on A
         //convert to column major representation
         let perm_scalar_as_cols = a_witness.as_columns();
         let mut comit_a_vec = Vec::<RistrettoPoint>::new();
         for i in 0..COLUMNS{
             comit_a_vec.push(extended_commit(&perm_scalar_as_cols[i], s_dash[i], &xpc_gens));
         }         
         //compute random a_0 vectors of length n and r_0 
         let a_0: Vec<_> = (0..COLUMNS).map(|_| Scalar::random(&mut OsRng)).collect();
         let r_0 = Scalar::random(&mut OsRng);
         
         //compute random vectors b, s, and tau of length 2*m. 
         let mut b_vec: Vec<_> = (0..2*ROWS).map(|_| Scalar::random(&mut OsRng)).collect();
         let mut s_vec: Vec<_> = (0..2*ROWS).map(|_| Scalar::random(&mut OsRng)).collect();    
         let mut tau_vec: Vec<_> = (0..2*ROWS).map(|_| Scalar::random(&mut OsRng)).collect();         
     
         //explicitly set values at index m 
         b_vec[ROWS] = Scalar::zero(); 
         s_vec[ROWS] = Scalar::zero();
         tau_vec[ROWS] = rho;
         
         //compute Xcomit on a_0
         let c_A_0 = extended_commit(&a_0, r_0, &xpc_gens);
         //compute standard pedersen commitment on all items of b_vec
         let cb_k: Vec<_> = b_vec.iter().zip(s_vec.iter()).map(|(b, s)| pc_gens.commit(*b, *s).compress()).collect();
        
         //create E_k
         let (ek_c,ek_d) = create_ek_comm(&self.outputs, &a_witness, &a_0, pk, &b_vec, &tau_vec);

         //send C_A_0, cb_k and E_k to the Verifier. 1st Message
         
         //create challenge x for hiding a and b
          
        //let x = Scalar::random(&mut OsRng);
         let x = Scalar::from(3u64);
         // set x = (x, x^2, x^3, x^4.., x^m). Thesis says length should be m but rebekkah has its length as 2m-2
         let x_exp: Vec<_> = exp_iter(x).take(2*ROWS).collect();
         let x_exp_m = &x_exp[1..4].to_vec();
         let x_k = &x_exp[1..6].to_vec();
         
         //compute a_vec = a_0 + Ax
         //borrow A
         let perm_scalar_rows = a_witness.as_rows();

         let ax: Vec<Scalar> = (0..ROWS).map(|i| vector_multiply_scalar(&perm_scalar_rows[i],&x_exp_m)).collect();    
         let mut a_vec = Vec::<Scalar>::new();
         //let a_vec: Vec<Scalar> = ax.iter().zip(a_0.iter()).map(|(i,j)| i+j).collect(); 
         for i in 0..ax.len(){
            a_vec.push(ax[i]+a_0[i]);
        }

        //compute r_vec = r . x. r is s' in thi case
        let rx: Scalar = vector_multiply_scalar(&s_dash,&x_exp_m);
        let r =  r_0 + rx;

        //compute b = b0 + sum from 1 to 2m-1 (bk.x^k)
        let bx = vector_multiply_scalar(&b_vec[1..6].to_vec(),&x_k);
        let b = b_vec[0] + bx;

        //compute s = s0 + sum from 1 to 2m-1 (sk.x^k)
        let sx = vector_multiply_scalar(&s_vec[1..6].to_vec(),&x_k);
        let s = s_vec[0] + sx;

        //compute t = t0 + sum from 1 to 2m-1 (tk.x^k)
        let tx = vector_multiply_scalar(&tau_vec[1..6].to_vec(),&x_k);
        let t = tau_vec[0] + tx;


        //Third Message. Send a_vec, r, b, s  
        //VERIFICATION CODE HERE. Move to other function later
        
        //Verifying c_B_m = com(0,0)
        let comit_b_m = cb_k[ROWS];
        let zz = Scalar::zero();let zzz = Scalar::zero();
        let comit_0_0 = pc_gens.commit(zz, zzz);
        if comit_0_0.compress() == comit_b_m{
            println!("Cbm TRUE");
        }
        
        // Verify c_A_0 . c_A_vec^(x_vec) = com (a_vec,r)
        //println!("{:?}",x_exp_m);
        //compute C_A^x_vec
        let c_a_x_vec = RistrettoPoint::multiscalar_mul(x_exp_m.iter().clone(), comit_a_vec.iter().clone());        
        //let trying = extended_commit(&ax, rx, &xpc_gens);
        
        let c_a_0_c_a_x_vec = c_a_x_vec + c_A_0;
        //compute comit(a_vec:r). The commitment is on the a_vec from second message. 
        let c_a_r = extended_commit(&a_vec, r, &xpc_gens);
        
        if c_a_0_c_a_x_vec == c_a_r{
            println!("CA TRUE");
        }else{
            println!("CA FALSE");
        }

        //Verifying Cb_0 .. == comit(b;s)
        let comit_b_s = pc_gens.commit(b, s);
        //product of (c_B_k)^(x^k)
        let len_cb = cb_k.len(); 
        let c_b_k = &cb_k[1..len_cb].to_vec();
        let c_b_k_x_k = RistrettoPoint::optional_multiscalar_mul(x_k.iter().clone(), c_b_k.iter().map(|pt| pt.decompress()));   
        //c_B_0 + product of c_B_k..
        let cb_sum = cb_k[0].decompress().unwrap() + c_b_k_x_k.unwrap();
        if comit_b_s == cb_sum{
            println!("CB TRUE");
        }else{
            println!("CB FALSE");
        }

        //checking E_m == C . In this case C is product of all N Pk^x^i. Which is also G, and H. Check this later 
        
        //Creating C on the prover and checking
        let (em_g, em_h) = create_C_comit_prover(&self.outputs, &a_witness, pk, rho);
        if ek_c[ROWS] == em_g && ek_d[ROWS] == em_h{
            println!("Em == Cprover  TRUE");
        }else{
            println!("Em ==Cprover  FALSE");
        }

        //Big verification
        //computing the left hand side. E0 + product of Ek^x^k
        //Ek^x^k for k = 1..2m-1 
        let ek_g_1_5 = &ek_c[1..6].to_vec();
        let ek_h_1_5 = &ek_d[1..6].to_vec();
       // println!("{:?}",x_k);
       // println!("{:?}",ek_g);
        let E_k_g_x_k = RistrettoPoint::multiscalar_mul(x_k.iter().clone(), ek_g_1_5.iter().clone());   
        let E_k_h_x_k = RistrettoPoint::multiscalar_mul(x_k.iter().clone(), ek_h_1_5.iter().clone());   
        let lhs_g = ek_c[0] + E_k_g_x_k;
        let lhs_h = ek_d[0] + E_k_h_x_k;

        //computing the rhs. 
         //extract commitments from accounts
         let comm: Vec<ElGamalCommitment> = self.outputs.as_row_major().iter().map(|acc| acc.comm).collect();
         //convert to 2D array representation
         let comm_matrix_as_rows = Array2D::from_row_major(&comm, ROWS,COLUMNS).as_rows();
         
     
     
     //Preparing vectors for multiscalar
     let c1 = &comm_matrix_as_rows[0];
     let c2 = &comm_matrix_as_rows[1];
     let c3 = &comm_matrix_as_rows[2];
 
     // gather c, d from ElgamalCommitment
     let c1_c: Vec<_> = c1.iter().map(|pt| pt.c.decompress().unwrap()).collect();
     let c1_d: Vec<_> = c1.iter().map(|pt| pt.d.decompress().unwrap()).collect();
     let c2_c: Vec<_> = c2.iter().map(|pt| pt.c.decompress().unwrap()).collect();
     let c2_d: Vec<_> = c2.iter().map(|pt| pt.d.decompress().unwrap()).collect();
     let c3_c: Vec<_> = c3.iter().map(|pt| pt.c.decompress().unwrap()).collect();
     let c3_d: Vec<_> = c3.iter().map(|pt| pt.d.decompress().unwrap()).collect();
     
        //reencryption 
        let c_bb = reencrypt_commitment(pk, t, b);        

        //product of i ..m C_i^(x^m-i)a
        // for i = 1
        //computing the scalar x^3-1)a = x^2.a 
        let x_2 = x_exp_m[1];
        let x_2_a: Vec<_> = a_vec.iter().map(|i| i * x_2).collect();

       let c1_g_xa = RistrettoPoint::multiscalar_mul(x_2_a.clone(), c1_c.clone());
       let c1_h_xa = RistrettoPoint::multiscalar_mul(x_2_a.clone(), c1_d.clone());

       // for i = 2
        //computing the scalar x^3-2)a = x.a 
        let x_1 = x_exp_m[0];
        let x_1_a: Vec<_> = a_vec.iter().map(|i| i * x_1).collect();

       let c2_g_xa = RistrettoPoint::multiscalar_mul(x_1_a.clone(), c2_c.clone());
       let c2_h_xa = RistrettoPoint::multiscalar_mul(x_1_a.clone(), c2_d.clone());


// for i = 3
        //computing the scalar x^3-3)a = a 
       let c3_g_xa = RistrettoPoint::multiscalar_mul(a_vec.clone(), c3_c.clone());
       let c3_h_xa = RistrettoPoint::multiscalar_mul(a_vec.clone(), c3_d.clone());

       //adding all points together
       let c_g_x = c3_g_xa + c1_g_xa + c2_g_xa; 
       let c_h_x = c3_h_xa + c1_h_xa + c2_h_xa; 

       let rhs_g = c_g_x + c_bb.c.decompress().unwrap();
       let rhs_h = c_h_x + c_bb.d.decompress().unwrap();

       if lhs_g == rhs_g && lhs_h == rhs_h{
        println!("lhs == rhs TRUE");
    }else{
        println!("Lhs ==rhs  FALSE");
    }




    }

    //b' is the witness and trated as A in the arguent described in paper 
    pub fn multiexp_pubkey_prove(&self, a_witness: &Array2D<Scalar>, pc_gens: &PedersenGens, xpc_gens: &Vec<RistrettoPoint>, G: RistrettoPoint, H: RistrettoPoint){
        //create random number s' to vector commit on witness. The commitment is on columns of A matrix
         //compute s'. it is the witness in c_A
         let s_dash: Vec<_> = (0..COLUMNS).map(|_| Scalar::random(&mut OsRng)).collect();

         //create statement 
         //compute Xcomit on A
         //convert to column major representation
         let perm_scalar_as_cols = a_witness.as_columns();
         let mut comit_a_vec = Vec::<RistrettoPoint>::new();
         for i in 0..COLUMNS{
             comit_a_vec.push(extended_commit(&perm_scalar_as_cols[i], s_dash[i], &xpc_gens));
         }         
         //compute random a_0 vectors of length n and r_0 
         let a_0: Vec<_> = (0..COLUMNS).map(|_| Scalar::random(&mut OsRng)).collect();
         let r_0 = Scalar::random(&mut OsRng);
         
         //compute random vectors b, and s of length 2*m. No need fpr tau in this case.
         let mut b_vec: Vec<_> = (0..2*ROWS).map(|_| Scalar::random(&mut OsRng)).collect();
         let mut s_vec: Vec<_> = (0..2*ROWS).map(|_| Scalar::random(&mut OsRng)).collect();         
         //explicitly set values at index m 
         b_vec[ROWS] = Scalar::zero(); 
         s_vec[ROWS] = Scalar::zero();
         
         //compute Xcomit on a_0
         let c_A_0 = extended_commit(&a_0, r_0, &xpc_gens);
         //compute standard pedersen commitment on all items of b_vec
         let cb_k: Vec<_> = b_vec.iter().zip(s_vec.iter()).map(|(b, s)| pc_gens.commit(*b, *s).compress()).collect();
         
         let (ek_g,ek_h) = create_ek_pk(&self.outputs, &a_witness, &a_0, G, H, &b_vec);

         //send C_A_0, cb_k and E_k to the Verifier. 1st Message
         //create challenge x for hiding a and b
          
        //let x = Scalar::random(&mut OsRng);
         let x = Scalar::from(3u64);
         // set x = (x, x^2, x^3, x^4.., x^m). Thesis says length should be m but rebekkah has its length as 2m-2
         let x_exp: Vec<_> = exp_iter(x).take(2*ROWS).collect();
         let x_exp_m = &x_exp[1..4].to_vec();
         let x_k = &x_exp[1..6].to_vec();
         
         //compute a_vec = a_0 + Ax
         //borrow A
         let perm_scalar_rows = a_witness.as_rows();

         let ax: Vec<Scalar> = (0..ROWS).map(|i| vector_multiply_scalar(&perm_scalar_rows[i],&x_exp_m)).collect();    
         let mut a_vec = Vec::<Scalar>::new();
         //let a_vec: Vec<Scalar> = ax.iter().zip(a_0.iter()).map(|(i,j)| i+j).collect(); 
        for i in 0..ax.len(){
            a_vec.push(ax[i]+a_0[i]);
        }

        //compute r_vec = r . x. r is s' in thi case
        let rx: Scalar = vector_multiply_scalar(&s_dash,&x_exp_m);
        let r =  r_0 + rx;

        //compute b = b0 + sum from 1 to 2m-1 (bk.x^k)
        let bx = vector_multiply_scalar(&b_vec[1..6].to_vec(),&x_k);
        let b = b_vec[0] + bx;

        //compute s = s0 + sum from 1 to 2m-1 (sk.x^k)
        let sx = vector_multiply_scalar(&s_vec[1..6].to_vec(),&x_k);
        let s = s_vec[0] + sx;

        //Third Message. Send a_vec, r, b, s  
        
        //VERIFICATION CODE HERE. Move to other function later
        
        //Verifying c_B_m = com(0,0)
        let comit_b_m = cb_k[ROWS];
        let zz = Scalar::zero();let zzz = Scalar::zero();
        let comit_0_0 = pc_gens.commit(zz, zzz);
        if comit_0_0.compress() == comit_b_m{
            println!("Cbm TRUE");
        }
        
        // Verify c_A_0 . c_A_vec^(x_vec) = com (a_vec,r)
        //println!("{:?}",x_exp_m);
        //compute C_A^x_vec
        let c_a_x_vec = RistrettoPoint::multiscalar_mul(x_exp_m.iter().clone(), comit_a_vec.iter().clone());        
        //let trying = extended_commit(&ax, rx, &xpc_gens);
        
        let c_a_0_c_a_x_vec = c_a_x_vec + c_A_0;
        //compute comit(a_vec:r)
        let c_a_r = extended_commit(&a_vec, r, &xpc_gens);
        
        if c_a_0_c_a_x_vec == c_a_r{
            println!("CA TRUE");
        }else{
            println!("CA FALSE");
        }

        //Verifying Cb_0 .. == comit(b;s)
        let comit_b_s = pc_gens.commit(b, s);
        //product of (c_B_k)^(x^k)
        let len_cb = cb_k.len(); 
        let c_b_k = &cb_k[1..len_cb].to_vec();
        let c_b_k_x_k = RistrettoPoint::optional_multiscalar_mul(x_k.iter().clone(), c_b_k.iter().map(|pt| pt.decompress()));   
        //c_B_0 + product of c_B_k..
        let cb_sum = cb_k[0].decompress().unwrap() + c_b_k_x_k.unwrap();
        if comit_b_s == cb_sum{
            println!("CB TRUE");
        }else{
            println!("CB FALSE");
        }

        //checking E_m == C . In this case C is product of all N Pk^x^i. Which is also G, and H. Check this later 
        if ek_g[ROWS] == G && ek_h[ROWS] == H{
            println!("Em == C^x  TRUE");
        }else{
            println!("Em == C^x  FALSE");
        }
        //Creating C on the prover and checking
        let (em_g, em_h) = create_C_pk_prover(&self.outputs, &a_witness);
        if ek_g[ROWS] == em_g && ek_h[ROWS] == em_h{
            println!("Em == Cprover  TRUE");
        }else{
            println!("Em ==Cprover  FALSE");
        }

        //Big verification
        //computing the left hand side. E0 + product of Ek^x^k
        //Ek^x^k for k = 1..2m-1 
        let ek_g_1_5 = &ek_g[1..6].to_vec();
        let ek_h_1_5 = &ek_h[1..6].to_vec();
       // println!("{:?}",x_k);
       // println!("{:?}",ek_g);
        let E_k_g_x_k = RistrettoPoint::multiscalar_mul(x_k.iter().clone(), ek_g_1_5.iter().clone());   
        let E_k_h_x_k = RistrettoPoint::multiscalar_mul(x_k.iter().clone(), ek_h_1_5.iter().clone());   
        let lhs_g = ek_g[0] + E_k_g_x_k;
        let lhs_h = ek_h[0] + E_k_h_x_k;

        //computing the rhs. 
         //extract commitments from accounts
         let pk: Vec<RistrettoPublicKey> = self.outputs.as_row_major().iter().map(|acc| acc.pk).collect();
         //convert to 2D array representation
         let pk_matrix_as_rows = Array2D::from_row_major(&pk, ROWS,COLUMNS).as_rows();
     
     
     //Preparing vectors for multiscalar
     let c1 = &pk_matrix_as_rows[0];
     let c2 = &pk_matrix_as_rows[1];
     let c3 = &pk_matrix_as_rows[2];
 
     // gather c, d from ElgamalCommitment
     let c1_c: Vec<_> = c1.iter().map(|pt| pt.gr.decompress().unwrap()).collect();
     let c1_d: Vec<_> = c1.iter().map(|pt| pt.grsk.decompress().unwrap()).collect();
     let c2_c: Vec<_> = c2.iter().map(|pt| pt.gr.decompress().unwrap()).collect();
     let c2_d: Vec<_> = c2.iter().map(|pt| pt.grsk.decompress().unwrap()).collect();
     let c3_c: Vec<_> = c3.iter().map(|pt| pt.gr.decompress().unwrap()).collect();
     let c3_d: Vec<_> = c3.iter().map(|pt| pt.grsk.decompress().unwrap()).collect();
     
        //reencryption (G,H)^b
        let g_bb = G * b;
        let h_bb = H * b;        

        //product of i ..m C_i^(x^m-i)a
        // for i = 1
        //computing the scalar x^3-1)a = x^2.a 
        let x_2 = x_exp_m[1];
        let x_2_a: Vec<_> = a_vec.iter().map(|i| i * x_2).collect();

       let c1_g_xa = RistrettoPoint::multiscalar_mul(x_2_a.clone(), c1_c.clone());
       let c1_h_xa = RistrettoPoint::multiscalar_mul(x_2_a.clone(), c1_d.clone());

       // for i = 2
        //computing the scalar x^3-2)a = x.a 
        let x_1 = x_exp_m[0];
        let x_1_a: Vec<_> = a_vec.iter().map(|i| i * x_1).collect();

       let c2_g_xa = RistrettoPoint::multiscalar_mul(x_1_a.clone(), c2_c.clone());
       let c2_h_xa = RistrettoPoint::multiscalar_mul(x_1_a.clone(), c2_d.clone());


// for i = 3
        //computing the scalar x^3-3)a = a 
       let c3_g_xa = RistrettoPoint::multiscalar_mul(a_vec.clone(), c3_c.clone());
       let c3_h_xa = RistrettoPoint::multiscalar_mul(a_vec.clone(), c3_d.clone());

       //adding all points together
       let c_g_x = c3_g_xa + c1_g_xa + c2_g_xa; 
       let c_h_x = c3_h_xa + c1_h_xa + c2_h_xa; 

       let rhs_g = c_g_x + g_bb;
       let rhs_h = c_h_x + h_bb;

       if lhs_g == rhs_g && lhs_h == rhs_h{
        println!("lhs == rhs TRUE");
    }else{
        println!("Lhs ==rhs  FALSE");
    }



    }    

    
        
}

pub fn bilnearmap(a: &Array2D<Scalar>, b: &Array2D<Scalar>, y_chal:Scalar) -> Vec<Scalar>{
    //Estimate complete bilinear map for Matrix A and B. A and B are constructed in the calling function

    //create y^i 
    let y_exp: Vec<_> = exp_iter(y_chal).take(ROWS+1).collect();
    let y_i = &y_exp[1..4].to_vec();

    //converting Array2D to column representation. Can also use column iterator. Should look into it
    let a_as_cols = a.as_columns();
    let b_as_cols = b.as_columns();
    let mut dvec = Vec::<Scalar>::new();
   
    for k in 0isize..7 {
        //println!("K = , {:?}",k);
		let mut sum = Scalar::zero();
		for i in 0isize..=3 {
          //  println!("i = {:?}",i);
            for j in 0isize..=3 {
            //    println!("j = {:?}",j);
              //  println!("ROWS - k + i = {:?}",(3 - k + i));
				if j == (3 - k + i) {
					sum = single_bilinearmap(&a_as_cols[i as usize], &b_as_cols[j as usize], &y_i) + sum;
				} else {
					continue;
				}
			}
		}
		dvec.push(sum);
	}
    dvec
}
pub fn single_bilinearmap(ai: &Vec<Scalar>, bj: &Vec<Scalar>, yi: &Vec<Scalar>) -> Scalar {
    let d: Scalar = ai.iter().zip(bj.iter()).zip(yi.iter()).map(|((i, j), k)| i *j * k).sum();
    d

}
pub fn running_checks_for_confirmation(accounts: &Array2D<Account>, b_mat: &Array2D<Scalar>, b_dash: &Array2D<Scalar> , b: &Vec<Scalar>, pk:&RistrettoPublicKey, rho:Scalar){

}

pub fn create_C_comit_prover(accounts: &Array2D<Account>, pi: &Array2D<Scalar>, pk:&RistrettoPublicKey, rho:Scalar)-> (RistrettoPoint, RistrettoPoint){
    //extract commitments from accounts
    let comm: Vec<ElGamalCommitment> = accounts.as_row_major().iter().map(|acc| acc.comm).collect();
    //convert to 2D array representation
    let comm_matrix_as_rows = Array2D::from_row_major(&comm, ROWS,COLUMNS).as_rows();
    
    //convert to column major representation
    let perm_scalar_as_cols = pi.as_columns();
    
    //Creating ek's as individual entites. Should be refactored later. this is only done for testing purposes
    
    //Preparing vectors for multiscalar
    let c1 = &comm_matrix_as_rows[0];
    let c2 = &comm_matrix_as_rows[1];
    let c3 = &comm_matrix_as_rows[2];

    // gather c, d from ElgamalCommitment
    let c1_c: Vec<_> = c1.iter().map(|pt| pt.c.decompress().unwrap()).collect();
    let c1_d: Vec<_> = c1.iter().map(|pt| pt.d.decompress().unwrap()).collect();
    let c2_c: Vec<_> = c2.iter().map(|pt| pt.c.decompress().unwrap()).collect();
    let c2_d: Vec<_> = c2.iter().map(|pt| pt.d.decompress().unwrap()).collect();
    let c3_c: Vec<_> = c3.iter().map(|pt| pt.c.decompress().unwrap()).collect();
    let c3_d: Vec<_> = c3.iter().map(|pt| pt.d.decompress().unwrap()).collect();

    //Column vectors for A
    let a1 = &perm_scalar_as_cols[0];
    let a2 = &perm_scalar_as_cols[1];
    let a3 = &perm_scalar_as_cols[2];

     
    // (e3_c, e3_d) = product of all i -> m  (C_i^(a_i))
    let mut combined_scalars = a1.clone(); combined_scalars.extend(a2.clone()); combined_scalars.extend(a3.clone());
    let mut point_c = c1_c.clone(); point_c.extend(c2_c.clone());point_c.extend(c3_c.clone());
    let mut point_d = c1_d.clone(); point_d.extend(c2_d.clone());point_d.extend(c3_d.clone());
    let e3_c = RistrettoPoint::multiscalar_mul(combined_scalars.iter(), point_c.iter());
    let e3_d = RistrettoPoint::multiscalar_mul(combined_scalars.iter(), point_d.iter());

   // reencryption
   let xero = Scalar::zero();
   let comit = reencrypt_commitment(pk,rho , xero);
   let C_c = e3_c + comit.c.decompress().unwrap(); 
   let C_d = e3_d + comit.d.decompress().unwrap(); 
    (C_c,C_d) 
}
pub fn create_C_pk_prover(accounts: &Array2D<Account>, pi: &Array2D<Scalar>)-> (RistrettoPoint, RistrettoPoint){
    //extract commitments from accounts
    let comm: Vec<RistrettoPublicKey> = accounts.as_row_major().iter().map(|acc| acc.pk).collect();
    //convert to 2D array representation
    let comm_matrix_as_rows = Array2D::from_row_major(&comm, ROWS,COLUMNS).as_rows();
    
    //convert to column major representation
    let perm_scalar_as_cols = pi.as_columns();
    //println!("{:?}",perm_scalar_as_cols);
    //Creating ek's as individual entites. Should be refactored later. this is only done for testing purposes
    
    //Preparing vectors for multiscalar
    let c1 = &comm_matrix_as_rows[0];
    let c2 = &comm_matrix_as_rows[1];
    let c3 = &comm_matrix_as_rows[2];

    // gather c, d from ElgamalCommitment
    let c1_c: Vec<_> = c1.iter().map(|pt| pt.gr.decompress().unwrap()).collect();
    let c1_d: Vec<_> = c1.iter().map(|pt| pt.grsk.decompress().unwrap()).collect();
    let c2_c: Vec<_> = c2.iter().map(|pt| pt.gr.decompress().unwrap()).collect();
    let c2_d: Vec<_> = c2.iter().map(|pt| pt.grsk.decompress().unwrap()).collect();
    let c3_c: Vec<_> = c3.iter().map(|pt| pt.gr.decompress().unwrap()).collect();
    let c3_d: Vec<_> = c3.iter().map(|pt| pt.grsk.decompress().unwrap()).collect();

    //Column vectors for A
    let a1 = &perm_scalar_as_cols[0];
    let a2 = &perm_scalar_as_cols[1];
    let a3 = &perm_scalar_as_cols[2];

     
    // (e3_c, e3_d) = product of all i -> m  (C_i^(a_i))
    let mut combined_scalars = a1.clone(); combined_scalars.extend(a2.clone()); combined_scalars.extend(a3.clone());
    let mut point_c = c1_c.clone(); point_c.extend(c2_c.clone());point_c.extend(c3_c.clone());
    let mut point_d = c1_d.clone(); point_d.extend(c2_d.clone());point_d.extend(c3_d.clone());
    let e3_c = RistrettoPoint::multiscalar_mul(combined_scalars.iter(), point_c.iter());
    let e3_d = RistrettoPoint::multiscalar_mul(combined_scalars.iter(), point_d.iter());

   // let encrypt_1_rho = 
    (e3_c,e3_d) 
}

pub fn create_ek_comm(accounts: &Array2D<Account>, b_mat: &Array2D<Scalar>, a0: &Vec<Scalar>, pk: &RistrettoPublicKey, b_random: &Vec<Scalar>, tau: &Vec<Scalar>)-> (Vec<RistrettoPoint>,Vec<RistrettoPoint>){
    //extract commitments from accounts
    let comm: Vec<ElGamalCommitment> = accounts.as_row_major().iter().map(|acc| acc.comm).collect();
    //convert to 2D array representation
    let comm_matrix_as_rows = Array2D::from_row_major(&comm, ROWS,COLUMNS).as_rows();
    
    //convert to column major representation
    let perm_scalar_as_cols = b_mat.as_columns();
    
    //Creating ek's as individual entites. Should be refactored later. this is only done for testing purposes
    
    //Preparing vectors for multiscalar
    let c1 = &comm_matrix_as_rows[0];
    let c2 = &comm_matrix_as_rows[1];
    let c3 = &comm_matrix_as_rows[2];

    // gather c, d from ElgamalCommitment
    let c1_c: Vec<_> = c1.iter().map(|pt| pt.c.decompress().unwrap()).collect();
    let c1_d: Vec<_> = c1.iter().map(|pt| pt.d.decompress().unwrap()).collect();
    let c2_c: Vec<_> = c2.iter().map(|pt| pt.c.decompress().unwrap()).collect();
    let c2_d: Vec<_> = c2.iter().map(|pt| pt.d.decompress().unwrap()).collect();
    let c3_c: Vec<_> = c3.iter().map(|pt| pt.c.decompress().unwrap()).collect();
    let c3_d: Vec<_> = c3.iter().map(|pt| pt.d.decompress().unwrap()).collect();

    //Column vectors for A
    let a1 = &perm_scalar_as_cols[0];
    let a2 = &perm_scalar_as_cols[1];
    let a3 = &perm_scalar_as_cols[2];

    //E_5. 
    // (e5_c, e5_d) = sum of all i (c1^a3)
    let e5_c = RistrettoPoint::multiscalar_mul(a3.iter().clone(), c1_c.iter().clone());
    let e5_d = RistrettoPoint::multiscalar_mul(a3.iter().clone(), c1_d.iter().clone());

    //E_4. 
    // (e4_c, e4_d) = sum of all i (c1^a2.c2^a3)
    let mut combined_scalars = a2.clone(); combined_scalars.extend(a3.clone());
    let mut point_c = c1_c.clone(); point_c.extend(c2_c.clone());
    let mut point_d = c1_d.clone(); point_d.extend(c2_d.clone());
    let e4_c = RistrettoPoint::multiscalar_mul(combined_scalars.iter(), point_c.iter());
    let e4_d = RistrettoPoint::multiscalar_mul(combined_scalars.iter(), point_d.iter());

    //E_3. 
    // (e3_c, e3_d) = sum of all i (c1^a1.c2^a2.c3^a3)
    let mut combined_scalars = a1.clone(); combined_scalars.extend(a2.clone()); combined_scalars.extend(a3.clone());
    let mut point_c = c1_c.clone(); point_c.extend(c2_c.clone());point_c.extend(c3_c.clone());
    let mut point_d = c1_d.clone(); point_d.extend(c2_d.clone());point_d.extend(c3_d.clone());
    let e3_c = RistrettoPoint::multiscalar_mul(combined_scalars.iter(), point_c.iter());
    let e3_d = RistrettoPoint::multiscalar_mul(combined_scalars.iter(), point_d.iter());

    //E_2. 
    // (e2_c, e2_d) = sum of all i (c1^a0. c2^a1.c3^a2)
    let mut combined_scalars = a1.clone(); combined_scalars.extend(a2.clone());combined_scalars.extend(a0.clone());
    let mut point_c = c2_c.clone(); point_c.extend(c3_c.clone());point_c.extend(c1_c.clone());
    let mut point_d = c2_d.clone(); point_d.extend(c3_d.clone());point_d.extend(c1_d.clone());
    let e2_c = RistrettoPoint::multiscalar_mul(combined_scalars.iter(), point_c.iter());
    let e2_d = RistrettoPoint::multiscalar_mul(combined_scalars.iter(), point_d.iter());

    //E_1. 
    // (e1_c, e1_d) = sum of all i (c2^a0 . c3^a1)
    let mut combined_scalars = a0.clone(); combined_scalars.extend(a1.clone());
    let mut point_c = c2_c.clone(); point_c.extend(c3_c.clone());
    let mut point_d = c2_d.clone(); point_d.extend(c3_d.clone());
    let e1_c = RistrettoPoint::multiscalar_mul(combined_scalars.iter(), point_c.iter());
    let e1_d = RistrettoPoint::multiscalar_mul(combined_scalars.iter(), point_d.iter());

    //E_0. 
    // (e0_c, e0_d) = sum of all i (c3^a0)
    let e0_c = RistrettoPoint::multiscalar_mul(a0.iter().clone(), c3_c.iter().clone());
    let e0_d = RistrettoPoint::multiscalar_mul(a0.iter().clone(), c3_d.iter().clone());

    let e_c = vec![e0_c, e1_c, e2_c, e3_c, e4_c, e5_c];
    let e_d = vec![e0_d, e1_d, e2_d, e3_d, e4_d, e5_d];

    //reencryption
    //creating encrytpion for eack ek
    let encrypt_comit: Vec<_> = b_random.iter().zip(tau.iter()).map(|(b,i)| reencrypt_commitment(pk, *i,*b)).collect();

    let c_encrypt : Vec<_> = encrypt_comit.iter().map(|com| com.c.decompress()).collect();
    let d_encrypt : Vec<_> = encrypt_comit.iter().map(|com| com.d.decompress()).collect();

    let E_c : Vec<_> = c_encrypt.iter().zip(e_c.iter()).map(|(ee,e)| ee.unwrap() + e).collect();

    let E_d : Vec<_> = d_encrypt.iter().zip(e_d.iter()).map(|(dd,d)| dd.unwrap() + d).collect();



    (E_c,E_d)
    //(e_c,e_d)
}
pub fn create_ek_pk(accounts: &Array2D<Account>, b_dash: &Array2D<Scalar>, a0: &Vec<Scalar>, G: RistrettoPoint, H: RistrettoPoint, b_random: &Vec<Scalar>)-> (Vec<RistrettoPoint>,Vec<RistrettoPoint>){
    //extract commitments from accounts
    let pk: Vec<RistrettoPublicKey> = accounts.as_row_major().iter().map(|acc| acc.pk).collect();
    //convert to 2D array representation
    let pk_matrix_as_rows = Array2D::from_row_major(&pk, ROWS,COLUMNS).as_rows();
    
    
    //convert b' to column major representation
    let perm_scalar_as_cols = b_dash.as_columns();
    
    //Creating ek's as individual entites. Should be refactored later. this is only done for testing purposes
    
    //Preparing vectors for multiscalar
    let c1 = &pk_matrix_as_rows[0];
    let c2 = &pk_matrix_as_rows[1];
    let c3 = &pk_matrix_as_rows[2];

    // gather g, h from Publickey
    let c1_c: Vec<_> = c1.iter().map(|pt| pt.gr.decompress().unwrap()).collect();
    let c1_d: Vec<_> = c1.iter().map(|pt| pt.grsk.decompress().unwrap()).collect();
    let c2_c: Vec<_> = c2.iter().map(|pt| pt.gr.decompress().unwrap()).collect();
    let c2_d: Vec<_> = c2.iter().map(|pt| pt.grsk.decompress().unwrap()).collect();
    let c3_c: Vec<_> = c3.iter().map(|pt| pt.gr.decompress().unwrap()).collect();
    let c3_d: Vec<_> = c3.iter().map(|pt| pt.grsk.decompress().unwrap()).collect();

    //Column vectors for A
    let a1 = &perm_scalar_as_cols[0];
    let a2 = &perm_scalar_as_cols[1];
    let a3 = &perm_scalar_as_cols[2];

    //E_5. 
    // (e5_c, e5_d) = sum of all i (c1^a3)
    let e5_c = RistrettoPoint::multiscalar_mul(a3.iter().clone(), c1_c.iter().clone());
    let e5_d = RistrettoPoint::multiscalar_mul(a3.iter().clone(), c1_d.iter().clone());
    //reencryption
    let e5_g_encrypt = G * b_random[5];
    let e5_h_encrypt = H * b_random[5];

    let e5_g = e5_c + e5_g_encrypt; 
    let e5_h = e5_d + e5_h_encrypt; 


    //E_4. 
    // (e4_c, e4_d) = sum of all i (c1^a2.c2^a3)
    let mut combined_scalars = a2.clone(); combined_scalars.extend(a3.clone());
    let mut point_c = c1_c.clone(); point_c.extend(c2_c.clone());
    let mut point_d = c1_d.clone(); point_d.extend(c2_d.clone());
    let e4_c = RistrettoPoint::multiscalar_mul(combined_scalars.iter(), point_c.iter());
    let e4_d = RistrettoPoint::multiscalar_mul(combined_scalars.iter(), point_d.iter());

    //reencryption
    let e4_g_encrypt = G * b_random[4];
    let e4_h_encrypt = H * b_random[4];

    let e4_g = e4_c + e4_g_encrypt; 
    let e4_h = e4_d + e4_h_encrypt; 


    //E_3. 
    // (e3_c, e3_d) = sum of all i (c1^a1.c2^a2.c3^a3)
    let mut combined_scalars = a1.clone(); combined_scalars.extend(a2.clone()); combined_scalars.extend(a3.clone());
    let mut point_c = c1_c.clone(); point_c.extend(c2_c.clone());point_c.extend(c3_c.clone());
    let mut point_d = c1_d.clone(); point_d.extend(c2_d.clone());point_d.extend(c3_d.clone());
    let e3_c = RistrettoPoint::multiscalar_mul(combined_scalars.iter(), point_c.iter());
    let e3_d = RistrettoPoint::multiscalar_mul(combined_scalars.iter(), point_d.iter());
//reencryption
let e3_g_encrypt = G * b_random[3];
let e3_h_encrypt = H * b_random[3];

let e3_g = e3_c + e3_g_encrypt; 
let e3_h = e3_d + e3_h_encrypt; 



    //E_2. 
    // (e2_c, e2_d) = sum of all i (c1^a0. c2^a1.c3^a2)
    let mut combined_scalars = a1.clone(); combined_scalars.extend(a2.clone());combined_scalars.extend(a0.clone());
    let mut point_c = c2_c.clone(); point_c.extend(c3_c.clone());point_c.extend(c1_c.clone());
    let mut point_d = c2_d.clone(); point_d.extend(c3_d.clone());point_d.extend(c1_d.clone());
    let e2_c = RistrettoPoint::multiscalar_mul(combined_scalars.iter(), point_c.iter());
    let e2_d = RistrettoPoint::multiscalar_mul(combined_scalars.iter(), point_d.iter());

    //reencryption
let e2_g_encrypt = G * b_random[2];
let e2_h_encrypt = H * b_random[2];

let e2_g = e2_c + e2_g_encrypt; 
let e2_h = e2_d + e2_h_encrypt;

    //E_1. 
    // (e1_c, e1_d) = sum of all i (c2^a0 . c3^a1)
    let mut combined_scalars = a0.clone(); combined_scalars.extend(a1.clone());
    let mut point_c = c2_c.clone(); point_c.extend(c3_c.clone());
    let mut point_d = c2_d.clone(); point_d.extend(c3_d.clone());
    let e1_c = RistrettoPoint::multiscalar_mul(combined_scalars.iter(), point_c.iter());
    let e1_d = RistrettoPoint::multiscalar_mul(combined_scalars.iter(), point_d.iter());
    //reencryption
let e1_g_encrypt = G * b_random[1];
let e1_h_encrypt = H * b_random[1];

let e1_g = e1_c + e1_g_encrypt; 
let e1_h = e1_d + e1_h_encrypt;

    //E_0. 
    // (e0_c, e0_d) = sum of all i (c3^a0)
    let e0_c = RistrettoPoint::multiscalar_mul(a0.iter().clone(), c3_c.iter().clone());
    let e0_d = RistrettoPoint::multiscalar_mul(a0.iter().clone(), c3_d.iter().clone());

    //reencryption
    let e0_g_encrypt = G * b_random[0];
    let e0_h_encrypt = H * b_random[0];

    let e0_g = e0_c + e0_g_encrypt; 
    let e0_h = e0_d + e0_h_encrypt;

    let e_c = vec![e0_g, e1_g, e2_g, e3_g, e4_g, e5_g];
    let e_d = vec![e0_h, e1_h, e2_h, e3_h, e4_h, e5_h];

    //without encryption ek
    //let e_c_W_E = vec![e0_c, e1_c, e2_c, e3_c, e4_c, e5_c];
    //let e_d_W_E = vec![e0_d, e1_d, e2_d, e3_d, e4_d, e5_d];



    (e_c,e_d)
}

pub fn reencrypt_commitment(p: &RistrettoPublicKey, rscalar: Scalar, bl_scalar: Scalar) -> ElGamalCommitment  {

    // lets make c
    let c = &rscalar * &p.gr.decompress().unwrap();

    // lets multiply balance scalar with the basepoint scalar
    let gv = &bl_scalar * &RISTRETTO_BASEPOINT_POINT;
  
    let kh = &rscalar * &p.grsk.decompress().unwrap();

    // lets make d
    let d = &gv + &kh;

    ElGamalCommitment{c: c.compress(),
                      d: d.compress()}
}
pub fn vector_multiply(row: &Vec<usize>, col: &Vec<Scalar>)-> Scalar{
    let sum: Vec<_> = row.iter().zip(col.iter()).map(|(i,j)| Scalar::from(*i as u64) *j).collect();
    sum.iter().sum()
}

pub fn vector_multiply_scalar(row: &Vec<Scalar>, col: &Vec<Scalar>)-> Scalar{
    let sum: Vec<_> = row.iter().zip(col.iter()).map(|(i,j)| i *j).collect();
    sum.iter().sum()
}
//Hardcoding for inital verification. Should be flexible in terms of size of m.ROWS
//Creating generators for extended pedersen commit. 
pub fn 
extended_pedersen_gen(capacity: usize, g: RistrettoPoint, h: RistrettoPoint) -> Vec<RistrettoPoint>{
    let mut gens = Vec::<RistrettoPoint>::new();
    gens.push(h);
    for i in 0..(capacity-2){
        gens.push(RistrettoPoint::hash_from_bytes::<Sha3_512>(
            gens[i].compress().as_bytes()));
    }
    let mut final_gens = Vec::<RistrettoPoint>::new();
    final_gens.push(h); final_gens.push(g);
    let len = gens.len();
    final_gens.extend(&gens[1..len]);
    final_gens
}
//Performing extended pedersen commit on vectors 
pub fn extended_commit(msg: &Vec<Scalar>, rscalar: Scalar, gens: &Vec<RistrettoPoint>)->  RistrettoPoint{
    let mut scalar = vec![rscalar];
    scalar.extend(msg);
    RistrettoPoint::multiscalar_mul(scalar.iter().clone(), gens.iter().clone())
}
/// Provides an iterator over the powers of a `Scalar`.
///
/// This struct is created by the `exp_iter` function.
pub struct ScalarExp {
    x: Scalar,
    next_exp_x: Scalar,
}

impl Iterator for ScalarExp {
    type Item = Scalar;

    fn next(&mut self) -> Option<Scalar> {
        let exp_x = self.next_exp_x;
        self.next_exp_x *= self.x;
        Some(exp_x)
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        (usize::max_value(), None)
    }
}

/// Return an iterator of the powers of `x`.
pub fn exp_iter(x: Scalar) -> ScalarExp {
    let next_exp_x = Scalar::one();
    ScalarExp { x, next_exp_x }
}

pub fn create_b_b_dash(x: Scalar, tau: &Vec<Scalar>, perm: &Vec<usize>) -> (Array2D<Scalar>, Array2D<Scalar>)
{
    //create x^i for i = 1..N
    let mut exp_x: Vec<_> = exp_iter(x).skip(1).take(N).collect();
    let mut x_psi: Vec<Scalar> = Vec::with_capacity(N);
    
    //create 1/tau 
    let tau_inv: Vec<_> = tau.iter().map(|i| Scalar::invert(i)).collect();

    let mut b_dash: Vec<Scalar> = Vec::with_capacity(N);
    for (i,_) in exp_x.iter().enumerate(){
        x_psi.push(exp_x[perm[i]-1]);
        b_dash.push(x_psi[i]*tau_inv[i]);
    }
    //Convert to a 2D array representation
    let b_matrix = Array2D::from_row_major(&x_psi, ROWS,COLUMNS);
    let b_dash_matrix = Array2D::from_row_major(&b_dash, ROWS,COLUMNS);
    (b_matrix,b_dash_matrix)
}

pub fn hadamard_product_proof_prover(tau: Array2D<Scalar>, pi: Permutation)->(Vec<RistrettoPoint>,Vec<RistrettoPoint>,Vec<RistrettoPoint>){
    //create pedersen generators for Xtended commitment
    let pc_gens = PedersenGens::default();
        //generate Xcomit generator points of length m+1
    let gens = extended_pedersen_gen(ROWS+1, pc_gens.B, pc_gens.B_blinding);
 
    //Store Xtended commitments for tau, b and b'
    let mut c_tau : Vec<RistrettoPoint> = Vec::new();
    let mut c_b : Vec<RistrettoPoint> = Vec::new();
    let mut c_b_dash : Vec<RistrettoPoint> = Vec::new();
    
    // X challenge from the verifier
    let x = Scalar::random(&mut OsRng);
    
    let (b, b_dash) = create_b_b_dash(x, &tau.as_row_major(), &pi.perm_matrix.as_row_major());
   
    //process matrices as columns
    let tau_cols = tau.as_rows();
    let b_cols = b.as_rows();
    let b_dash_cols = b_dash.as_rows();
    
    //rscalar blindings for Xtended commits
    let rscalar_tau = Scalar::random(&mut OsRng);
    let rscalar_b = Scalar::random(&mut OsRng);
    let rscalar_b_dash = Scalar::random(&mut OsRng);
    
    //Create Xtended commitment on tau, b and b' 
    for i in 0..3{ 
        c_tau.push(extended_commit(&tau_cols[i], rscalar_tau, &gens));
        c_b.push(extended_commit(&b_cols[i], rscalar_b, &gens));
        c_b_dash.push(extended_commit(&b_dash_cols[i], rscalar_b_dash, &gens));
    }
    (c_tau, c_b, c_b_dash)
}


pub fn verify_update_ddh_prove(x: Scalar, pk: &Vec<RistrettoPublicKey>, rho: Scalar)->(Scalar, Scalar, CompressedRistretto,CompressedRistretto) 
{
    // x^i
    let exp_x: Vec<_> = exp_iter(x).take(9).collect();
    // gather g, h from Public key
    let g_i: Vec<_> = pk.iter().map(|pt| pt.gr.decompress().unwrap()).collect();
    let h_i: Vec<_> = pk.iter().map(|pt| pt.grsk.decompress().unwrap()).collect();
    // (G, H) = sum of all i (pk_i * x^i)
    let G = RistrettoPoint::multiscalar_mul(exp_x.iter().clone(), g_i.iter().clone());
    let H = RistrettoPoint::multiscalar_mul(&exp_x, h_i.iter().clone());
    // x^i * rho
    let exp_x_rho: Vec<_> = exp_x.iter().map(|x| x * rho).collect();
    // (G', H')
    let G_dash = RistrettoPoint::multiscalar_mul(exp_x_rho.iter().clone(), g_i.iter().clone());
    let H_dash = RistrettoPoint::multiscalar_mul(&exp_x_rho, h_i.iter().clone());
    
    //create the ddh prove
    let (z,chal) = Prover::verify_update_ddh_prover(G, H, G_dash, H_dash, rho); 
    (z, chal, G_dash.compress(), H_dash.compress())
}


pub fn verify_update_ddh_verify(x: Scalar, pk: &Vec<RistrettoPublicKey>, g_dash: CompressedRistretto, h_dash: CompressedRistretto, z: Scalar, chal:Scalar)-> bool
{
     // x^i
    let exp_x: Vec<_> = exp_iter(x).take(9).collect(); 
    // gather g, h from Public key
    let g_i: Vec<_> = pk.iter().map(|pt| pt.gr.decompress().unwrap()).collect();
    let h_i: Vec<_> = pk.iter().map(|pt| pt.grsk.decompress().unwrap()).collect();
    // (G, H) = sum of all i (pk_i * x^i)
    let G = RistrettoPoint::multiscalar_mul(exp_x.iter().clone(), g_i.iter().clone());
    let H = RistrettoPoint::multiscalar_mul(&exp_x, h_i.iter().clone());
     
    //verify the ddh prove
    Verifier::verify_update_ddh_verifier(G.compress(), H.compress(), g_dash, h_dash, z, chal)
    
}

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
    fn multiexpo_prove_test() {
        let mut account_vector: Vec<Account> = Vec::new();
        // lets create these accounts and associated keypairs
        for _ in 0..9 {
            let mut rng = rand::thread_rng();
            let sk: RistrettoSecretKey = SecretKey::random(&mut rng);
            let pk = RistrettoPublicKey::from_secret_key(&sk, &mut rng);
            let acc = Account::generate_account(pk);
            account_vector.push(acc);
        }
        let shuffle = {
            Shuffle::output_shuffle(&account_vector)
        };        
        shuffle.unwrap().shuffle_argument_prove();
        assert_eq!(true, true);
    }


    #[test]
    fn ek_creation_test() {
        let mut account_vector: Vec<Account> = Vec::new();
        // lets create these accounts and associated keypairs
        for _ in 0..9 {
            let mut rng = rand::thread_rng();
            let sk: RistrettoSecretKey = SecretKey::random(&mut rng);
            let pk = RistrettoPublicKey::from_secret_key(&sk, &mut rng);
            let acc = Account::generate_account(pk);
            account_vector.push(acc);
        }
        let accounts = Array2D::from_row_major(&account_vector, ROWS,COLUMNS);
        let perm = Permutation::new(&mut OsRng, N);
        //println!("{:?}",perm.perm_matrix);
        //println!("{:?}",perm.perm_matrix.as_columns());

       // create_ek_comm(&accounts,&perm);   
    }
    #[test]
    fn ddh_prove_test() {
        let mut account_vector: Vec<Account> = Vec::new();
        // lets create these accounts and associated keypairs
        for _ in 0..9 {
            let mut rng = rand::thread_rng();
            let sk: RistrettoSecretKey = SecretKey::random(&mut rng);
            let pk = RistrettoPublicKey::from_secret_key(&sk, &mut rng);
            let acc = Account::generate_account(pk);
            account_vector.push(acc);
        }
        let pk: Vec<RistrettoPublicKey> = account_vector.iter().map(|acc| acc.pk).collect();
        let x = Scalar::random(&mut OsRng);
        let rho = Scalar::random(&mut OsRng);
        let xx = Scalar::from(2u64);
        let yy = Scalar::from(6u64);
        
        let rho = Scalar::random(&mut OsRng);
        let (z, chal, G_dash, H_dash) = verify_update_ddh_prove(x,&pk,rho);
        let verify = verify_update_ddh_verify(x, &pk, G_dash, H_dash, z, chal);
        println!("{:?}",verify);
        assert_eq!(verify, true);
    }

    #[test]
    fn extended_pedersen_gen_test() {
        let perm = Permutation::new(&mut OsRng, N);
        let cols = perm.perm_matrix.as_columns();
        let pc_gens = PedersenGens::default();
        //generate Xcomit generator points of length m+1
        let gens = extended_pedersen_gen(ROWS+1, pc_gens.B, pc_gens.B_blinding);
       
        println!("Permuted Matrix {:?}",perm.perm_matrix.as_rows());
        println!("{:?}",cols[0]);
        println!("{:?}",gens);
    }
    #[test]
    fn extended_commit_test(){
        let perm = Permutation::new(&mut OsRng, N);
        let cols = perm.perm_matrix.as_columns();
        let pc_gens = PedersenGens::default();
        //generate Xcomit generator points of length m+1
        let gens = extended_pedersen_gen(ROWS+1, pc_gens.B, pc_gens.B_blinding);
        let shuffle_scalar: Vec<_> = cols[0].iter().map(|i| Scalar::from(*i as u64).clone()).collect();
        let rscalar = Scalar::random(&mut OsRng);
        let c = extended_commit(&shuffle_scalar, rscalar, &gens);
        println!("{:?}",c);
    }
    #[test]
    fn exp_iter_test() {
        let x = Scalar::random(&mut OsRng);
        let exp_2: Vec<_> = exp_iter(x).take(9).collect();
        println!("{:?}",x);
        println!("{:?}",exp_2);
        //assert_eq!(exp_2[0], Scalar::from(1u64));
    }
    #[test]
    fn x_psi_test() {
        //let x = Scalar::random(&mut OsRng);
        let x = Scalar::from(2u64);
        let exp_x: Vec<_> = exp_iter(x).take(9).collect();
        let perm = Permutation::new(&mut OsRng, N);
        let perm_vec = perm.perm_matrix.as_row_major();
        let mut x_psi: Vec<Scalar> = Vec::with_capacity(9);
        for i in 0..9{
            x_psi.push(exp_x[perm_vec[i]])
        }
        println!("{:?}",exp_x);
        println!("{:?}",perm_vec);
        println!("{:?}",x_psi);
        
        //assert_eq!(exp_2[0], Scalar::from(1u64));
    }
    #[test]
    fn scalar_batch_invert_test() {
        //Create Random tau used for updating the Account Pks
        let tau: Vec<_> = (0..9).map(|_| Scalar::random(&mut OsRng)).collect();       
        println!("{:?}",tau);
        let allinv: Vec<_> = tau.iter().map(|i| Scalar::invert(i)).collect();
        println!("{:?}",allinv);
    }
    #[test]
    fn b_dash_vector_test() {
        //Create Random tau used for updating the Account Pks
        let x = Scalar::random(&mut OsRng);
       //let x = Scalar::from(3u64); 
       let tau: Vec<_> = (0..9).map(|_| Scalar::random(&mut OsRng)).collect();       
        let perm = Permutation::new(&mut OsRng, N);
        let perm_vec = perm.perm_matrix.as_row_major();
        
        let (b,b_dash) = create_b_b_dash(x,&tau,&perm_vec);

        //test
        let b_dash_tau : Vec<Scalar> = b_dash.as_row_major().iter().zip(tau.iter()).map(|(b, t)| b*t).collect();
        
        assert_eq!(b_dash_tau, b.as_row_major());

    }
    #[test]
    fn b_vector_test() {
       //test for N = 9 
       let x = Scalar::from(3u64); 
        //Create Random tau used for updating the Account Pks
       let tau: Vec<_> = (0..N).map(|_| Scalar::random(&mut OsRng)).collect();       
       
       let permutation: Vec<usize> = vec![2,1,3,8,7,6,4,5,9];
        
       let (b,b_dash) = create_b_b_dash(x,&tau,&permutation);
        
       let b_reference: Vec<Scalar> = vec![Scalar::from(9u64), Scalar::from(3u64), Scalar::from(27u64), Scalar::from(6561u64), Scalar::from(2187u64), Scalar::from(729u64) , Scalar::from(81u64) ,Scalar::from(243u64) ,Scalar::from(19683u64)];
       //println!("{:?}",b.as_row_major());
       //println!("{:?}",b_reference);

        //test
        
        assert_eq!(b_reference, b.as_row_major());

    }
    #[test]
    fn hadamard_product_test() {
        let tau: Vec<_> = (0..9).map(|_| Scalar::random(&mut OsRng)).collect();       
        let tau_2d = Array2D::from_row_major(&tau, 3, 3);
        let perm = Permutation::new(&mut OsRng, N);
        let (t, b, bd) = hadamard_product_proof_prover(tau_2d, perm);
        let b_dash_tau : Vec<RistrettoPoint> = bd.iter().zip(t.iter()).map(|(b, t)| b+t).collect();
        assert_eq!(b_dash_tau, b);

       // println!("{:?}",x);
       // println!("{:?}",exp_2);
        //assert_eq!(exp_2[0], Scalar::from(1u64));
    }
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
         let shuffled_accounts: Vec<_> = (0..len).map(|i| account_vector[permutation[i]-1].clone()).collect();
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
        let shuffle = {
            Shuffle::output_shuffle(&account_vector)
        };
        let inp = shuffle.as_ref().unwrap().inputs.as_row_major();
        let out = shuffle.as_ref().unwrap().outputs.as_row_major();
        let pi = &shuffle.as_ref().unwrap().pi;
        let perm = pi.perm_matrix.as_row_major();
        let tau = shuffle.as_ref().unwrap().shuffled_tau.as_row_major();
        let rho = shuffle.as_ref().unwrap().rho;
        
        let shuffled_inputs: Vec<_> = (0..9).map(|i| inp[perm[i]-1].clone()).collect();
        let shuffled_updated: Vec<_> = shuffled_inputs.iter().zip(tau.iter()).map(|(acc, t)| Account::update_account(*acc, 0, *t, rho)).collect();

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
        let shuffle = {
            Shuffle::input_shuffle(&account_vector)
        };
        let out = shuffle.as_ref().unwrap().outputs.as_row_major();
        let tau = shuffle.as_ref().unwrap().shuffled_tau.as_row_major();
        let rho = shuffle.as_ref().unwrap().rho;
        
        let input_updated: Vec<_> = account_vector.iter().zip(tau.iter()).map(|(acc, t)| Account::update_account(*acc, 0, *t, rho)).collect();
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
        let shuffle = {
            Shuffle::input_shuffle(&account_vector)
        };
        let inp = shuffle.as_ref().unwrap().inputs.as_row_major();
        let pi = &shuffle.as_ref().unwrap().pi;
        let perm = pi.perm_matrix.as_row_major();
        //shuffle the input and compare with the account_vector
        let shuffled_inputs: Vec<_> = (0..9).map(|i| inp[perm[i]-1].clone()).collect();
        assert_eq!(account_vector, shuffled_inputs)
    }
}