//! The `vectorpedersen` module contains API for producing a
//! vector commitment.

#![allow(non_snake_case)]


use bulletproofs::PedersenGens;
use curve25519_dalek::{
    ristretto::{CompressedRistretto, RistrettoPoint},
    scalar::Scalar,
    constants::RISTRETTO_BASEPOINT_POINT
};
use crate::{
    accounts::{Account,Prover, Verifier},
    ristretto::RistrettoPublicKey,
    elgamal::ElGamalCommitment,
    shuffle::vectorutil,
    shuffle::Shuffle,
    pedersen::vectorpedersen::VectorPedersenGens,
};
use rand::rngs::OsRng;
use array2d::{Array2D};
use curve25519_dalek::traits::MultiscalarMul;
use curve25519_dalek::traits::VartimeMultiscalarMul;
use crate::shuffle::shuffle::COLUMNS;
use crate::shuffle::shuffle::ROWS;



pub fn multiexp_commit_prove(shuf: &Shuffle, a_witness: &Array2D<Scalar>, pc_gens: &PedersenGens, xpc_gens: &VectorPedersenGens, pk: &RistrettoPublicKey, rho: Scalar){
    //create random number s' to vector commit on witness. The commitment is on columns of A matrix
     //compute s'. it is the witness in c_A
     let s_dash: Vec<_> = (0..COLUMNS).map(|_| Scalar::random(&mut OsRng)).collect();

     //create statement 
     //compute Xcomit on A
     //convert to column major representation
     let perm_scalar_as_cols = a_witness.as_columns();
     let mut comit_a_vec = Vec::<RistrettoPoint>::new();
     for i in 0..COLUMNS{
         //comit_a_vec.push(extended_commit(&perm_scalar_as_cols[i], s_dash[i], &xpc_gens));
         comit_a_vec.push(xpc_gens.commit(&perm_scalar_as_cols[i], s_dash[i]));
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
     //let c_A_0 = extended_commit(&a_0, r_0, &xpc_gens);
     let c_A_0 = xpc_gens.commit(&a_0, r_0);

     //compute standard pedersen commitment on all items of b_vec
     let cb_k: Vec<_> = b_vec.iter().zip(s_vec.iter()).map(|(b, s)| pc_gens.commit(*b, *s).compress()).collect();
    
     //create E_k
     let (ek_c,ek_d) = create_ek_comm(&shuf.outputs, &a_witness, &a_0, pk, &b_vec, &tau_vec);

     //send C_A_0, cb_k and E_k to the Verifier. 1st Message
     
     //create challenge x for hiding a and b
      
    //let x = Scalar::random(&mut OsRng);
     let x = Scalar::from(3u64);
     // set x = (x, x^2, x^3, x^4.., x^m). Thesis says length should be m but rebekkah has its length as 2m-2
     let x_exp: Vec<_> = vectorutil::exp_iter(x).take(2*ROWS).collect();
     let x_exp_m = &x_exp[1..4].to_vec();
     let x_k = &x_exp[1..6].to_vec();
     
     //compute a_vec = a_0 + Ax
     //borrow A
     let perm_scalar_rows = a_witness.as_rows();

     let ax: Vec<Scalar> = (0..ROWS).map(|i| vectorutil::vector_multiply_scalar(&perm_scalar_rows[i],&x_exp_m)).collect();    
     let mut a_vec = Vec::<Scalar>::new();
     //let a_vec: Vec<Scalar> = ax.iter().zip(a_0.iter()).map(|(i,j)| i+j).collect(); 
     for i in 0..ax.len(){
        a_vec.push(ax[i]+a_0[i]);
    }

    //compute r_vec = r . x. r is s' in thi case
    let rx: Scalar = vectorutil::vector_multiply_scalar(&s_dash,&x_exp_m);
    let r =  r_0 + rx;

    //compute b = b0 + sum from 1 to 2m-1 (bk.x^k)
    let bx = vectorutil::vector_multiply_scalar(&b_vec[1..6].to_vec(),&x_k);
    let b = b_vec[0] + bx;

    //compute s = s0 + sum from 1 to 2m-1 (sk.x^k)
    let sx = vectorutil::vector_multiply_scalar(&s_vec[1..6].to_vec(),&x_k);
    let s = s_vec[0] + sx;

    //compute t = t0 + sum from 1 to 2m-1 (tk.x^k)
    let tx = vectorutil::vector_multiply_scalar(&tau_vec[1..6].to_vec(),&x_k);
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
   // let c_a_r = extended_commit(&a_vec, r, &xpc_gens);
    let c_a_r = xpc_gens.commit(&a_vec, r);
    
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
    let (em_g, em_h) = create_C_comit_prover(&shuf.outputs, &a_witness, pk, rho);
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
     let comm: Vec<ElGamalCommitment> = shuf.outputs.as_row_major().iter().map(|acc| acc.comm).collect();
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
pub fn multiexp_pubkey_prove(shuf: &Shuffle, a_witness: &Array2D<Scalar>, pc_gens: &PedersenGens, xpc_gens: &VectorPedersenGens, G: RistrettoPoint, H: RistrettoPoint){
    //create random number s' to vector commit on witness. The commitment is on columns of A matrix
     //compute s'. it is the witness in c_A
     let s_dash: Vec<_> = (0..COLUMNS).map(|_| Scalar::random(&mut OsRng)).collect();

     //create statement 
     //compute Xcomit on A
     //convert to column major representation
     let perm_scalar_as_cols = a_witness.as_columns();
     let mut comit_a_vec = Vec::<RistrettoPoint>::new();
     for i in 0..COLUMNS{
         //comit_a_vec.push(extended_commit(&perm_scalar_as_cols[i], s_dash[i], &xpc_gens));
         comit_a_vec.push(xpc_gens.commit(&perm_scalar_as_cols[i], s_dash[i]));
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
     //let c_A_0 = extended_commit(&a_0, r_0, &xpc_gens);
     let c_A_0 = xpc_gens.commit(&a_0, r_0);   
     //compute standard pedersen commitment on all items of b_vec
     let cb_k: Vec<_> = b_vec.iter().zip(s_vec.iter()).map(|(b, s)| pc_gens.commit(*b, *s).compress()).collect();
     
     let (ek_g,ek_h) = create_ek_pk(&shuf.outputs, &a_witness, &a_0, G, H, &b_vec);

     //send C_A_0, cb_k and E_k to the Verifier. 1st Message
     //create challenge x for hiding a and b
      
    //let x = Scalar::random(&mut OsRng);
     let x = Scalar::from(3u64);
     // set x = (x, x^2, x^3, x^4.., x^m). Thesis says length should be m but rebekkah has its length as 2m-2
     let x_exp: Vec<_> = vectorutil::exp_iter(x).take(2*ROWS).collect();
     let x_exp_m = &x_exp[1..4].to_vec();
     let x_k = &x_exp[1..6].to_vec();
     
     //compute a_vec = a_0 + Ax
     //borrow A
     let perm_scalar_rows = a_witness.as_rows();

     let ax: Vec<Scalar> = (0..ROWS).map(|i| vectorutil::vector_multiply_scalar(&perm_scalar_rows[i],&x_exp_m)).collect();    
     let mut a_vec = Vec::<Scalar>::new();
     //let a_vec: Vec<Scalar> = ax.iter().zip(a_0.iter()).map(|(i,j)| i+j).collect(); 
    for i in 0..ax.len(){
        a_vec.push(ax[i]+a_0[i]);
    }

    //compute r_vec = r . x. r is s' in thi case
    let rx: Scalar = vectorutil::vector_multiply_scalar(&s_dash,&x_exp_m);
    let r =  r_0 + rx;

    //compute b = b0 + sum from 1 to 2m-1 (bk.x^k)
    let bx = vectorutil::vector_multiply_scalar(&b_vec[1..6].to_vec(),&x_k);
    let b = b_vec[0] + bx;

    //compute s = s0 + sum from 1 to 2m-1 (sk.x^k)
    let sx = vectorutil::vector_multiply_scalar(&s_vec[1..6].to_vec(),&x_k);
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
    //let c_a_r = extended_commit(&a_vec, r, &xpc_gens);
    let c_a_r = xpc_gens.commit(&a_vec, r);
    
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
    let (em_g, em_h) = create_C_pk_prover(&shuf.outputs, &a_witness);
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
     let pk: Vec<RistrettoPublicKey> = shuf.outputs.as_row_major().iter().map(|acc| acc.pk).collect();
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
    use crate::{
        accounts::{Account},
        shuffle::vectorutil,
        shuffle::shuffle,
        shuffle::{Shuffle, Permutation},
    };
    use array2d::{Array2D};
    use rand::rngs::OsRng;
    use crate::shuffle::shuffle::COLUMNS;
    use crate::shuffle::shuffle::ROWS;      
    const N: usize = 9;   //N - Length of vector
    
    
    
    #[test]
    fn multiexpo_pk_prove_test() {
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
        let xpc_gens = VectorPedersenGens::new(ROWS+1);
        
        
        //create challenge x for b and b' vectors    
        let x = Scalar::random(&mut OsRng);
        //create b and b' vectors to be used for Multiexponentiationa and hadamard proof later
        let (_, b_dash) = shuffle::create_b_b_dash(x, &shuffle.shuffled_tau.as_row_major(), &shuffle.pi);
        //Create Pk^x^ for testing purposes here. Should be refactored later.
        // x^i
        let exp_xx: Vec<_> = vectorutil::exp_iter(x).take(9).collect();
        // gather g, h from Public key    
        // gather g, h from Public key
        let pk: Vec<RistrettoPublicKey> = shuffle.inputs.as_row_major().iter().map(|acc| acc.pk).collect();
        
        let g_i: Vec<_> = pk.iter().map(|pt| pt.gr.decompress().unwrap()).collect();
        let h_i: Vec<_> = pk.iter().map(|pt| pt.grsk.decompress().unwrap()).collect();
        // (G, H) = sum of all i (pk_i * x^i)
        let G = RistrettoPoint::multiscalar_mul(exp_xx.iter().clone(), g_i.iter().clone());
        let H = RistrettoPoint::multiscalar_mul(&exp_xx, h_i.iter().clone());
        
        multiexp_pubkey_prove(&shuffle, &b_dash, &pc_gens , &xpc_gens, G, H);
        assert_eq!(true, true);
    }
    #[test]
    fn multiexpo_comm_prove_test() {
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
        let xpc_gens = VectorPedersenGens::new(ROWS+1);
        
        
        //create challenge x for b and b' vectors    
        let x = Scalar::random(&mut OsRng);
        //create b and b' vectors to be used for Multiexponentiationa and hadamard proof later
        let (b_mat, _) = shuffle::create_b_b_dash(x, &shuffle.shuffled_tau.as_row_major(), &shuffle.pi);
        //Create Pk^x^ for testing purposes here. Should be refactored later.
        // x^i
        let exp_xx: Vec<_> = vectorutil::exp_iter(x).take(9).collect();
        // gather g, h from Public key    
        // gather g, h from Public key
        let pk: Vec<RistrettoPublicKey> = shuffle.inputs.as_row_major().iter().map(|acc| acc.pk).collect();
        
        let g_i: Vec<_> = pk.iter().map(|pt| pt.gr.decompress().unwrap()).collect();
        let h_i: Vec<_> = pk.iter().map(|pt| pt.grsk.decompress().unwrap()).collect();
        // (G, H) = sum of all i (pk_i * x^i)
        let G = RistrettoPoint::multiscalar_mul(exp_xx.iter().clone(), g_i.iter().clone());
        let H = RistrettoPoint::multiscalar_mul(&exp_xx, h_i.iter().clone());
        let pk = RistrettoPublicKey{gr: G.compress(), grsk: H.compress()};

        //create vector of -rho of length N
        let neg_rho = -shuffle.rho;
        let rho_vec: Vec<Scalar> = vec![neg_rho, neg_rho, neg_rho, neg_rho, neg_rho, neg_rho, neg_rho, neg_rho, neg_rho];   

        //create rho = -rho . b
        let rho_b = vectorutil::vector_multiply_scalar(&rho_vec, &b_mat.as_row_major());
        multiexp_commit_prove(&shuffle, &b_mat, &pc_gens, &xpc_gens, &pk, rho_b);
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

        //create_ek_comm(&accounts,&perm);   
    }
}