//Polynomial Field STARTS here
use crate::shuffle::shuffle::COLUMNS;
use crate::shuffle::shuffle::ROWS;
use array2d::Array2D;
use bulletproofs::PedersenGens;
use curve25519_dalek::traits::MultiscalarMul;

use crate::keys::PublicKey;
use crate::pedersen::vectorpedersen::VectorPedersenGens;
use crate::shuffle::vectorutil;
use core::fmt::Debug;
use curve25519_dalek::{
    ristretto::{CompressedRistretto, RistrettoPoint},
    scalar::Scalar,
};
use itertools::EitherOrBoth::{Both, Left, Right};
use itertools::Itertools;
use rand::rngs::OsRng;
use rand::{CryptoRng, Rng};
use std::ops::Add;
use std::ops::{Sub, SubAssign};
//scalar_zero = Scalar::zero();
fn pretty_print_coefficients(coefficients: &[Scalar], deg: usize) -> String {
    if coefficients.is_empty() {
        return String::from("0");
    }
    let scalar_zero = Scalar::zero();
    let trailing_zeros_warning: &str = match coefficients.last() {
        Some(scalar_zero) => "Trailing zeros!",
        _ => "",
    };

    let mut outputs: Vec<String> = Vec::new();
    let pol_degree = deg;
    for i in 0..=pol_degree {
        let pow = pol_degree - i;

        if coefficients[pow] != scalar_zero {
            // operator: plus or minus
            let mut operator_str = "";
            if i != 0 && coefficients[pow] != scalar_zero {
                operator_str = " + ";
            }
            // outputs.push(format!(
            //     "{}{}{}",
            //     operator_str,
            //     if coefficients[pow] == Scalar::one() {
            //         String::from("")
            //     } else {
            //         coefficients[pow].to_string()
            //     },
            //     if pow == 0 && coefficients[pow] == Scalar::one() {
            //         String::from("1")
            //     } else if pow == 0 {
            //         String::from("")
            //     } else if pow == 1 {
            //         String::from("x")
            //     } else {
            //         let mut result = "x^".to_owned();
            //         let borrowed_string = pow.to_string().to_owned();
            //         result.push_str(&borrowed_string);
            //         result
            //     }
            // ));
        }
    }
    format!("{}{}", trailing_zeros_warning, outputs.join(""))
}

//Create a single degree polynomial: aX + b
fn create_1D_poly(a: Scalar, b: Scalar) -> Polynomial {
    let coeffiecient: Vec<Scalar> = vec![b, a];
    if a == Scalar::zero() {
        Polynomial {
            coefficients: coeffiecient,
            degree: 0,
        }
    } else {
        Polynomial {
            coefficients: coeffiecient,
            degree: 1,
        }
    }
}

//Create a monomial of a given degree
fn create_ND_poly(a: Scalar, n: usize) -> Polynomial {
    let mut coeff: Vec<Scalar> = vec![Scalar::zero(); n + 1];
    coeff[n] = a;
    Polynomial {
        coefficients: coeff,
        degree: n,
    }
}
#[derive(Debug, Clone)]
pub struct Polynomial {
    pub coefficients: Vec<Scalar>,
    pub degree: usize,
}

impl Polynomial {
    //Print Polynomial
    pub fn print_polynomial(&self) {
        println!("Degree {:?} ", self.degree);
        for (i, x) in self.coefficients.iter().enumerate() {
            // if *x == Scalar::zero() {
            //     continue;
            // } else {
            print!("{:?} X^ {} + ", x, i);
            //}
        }
    }
    //Adjusts degree of the polynomial
    //Very Important in this implementation
    pub fn poly_deg_adjust(&mut self) {
        let mut h_term: usize = 0;
        // println!("{:?}", self.degree);

        for i in 0..=self.degree {
            if self.coefficients[i] == Scalar::zero() {
                continue;
            } else {
                h_term = i;
                //  println!("{:?}", i);
            }
        }
        self.degree = h_term;
        //println!("{:?}", self.degree);
        let mut newcoeff = Vec::<Scalar>::with_capacity(h_term);
        for i in 0..=self.degree {
            newcoeff.push(self.coefficients[i]);
        }
        self.coefficients = newcoeff;
        //self.print_polynomial();
    }
    // Remove trailing zeros from coefficients
    // Borrow mutably when you mutate the data, but don't want to consume it
    pub fn normalize(&mut self) {
        let zero = Scalar::zero();
        while *self.coefficients.last().unwrap() == zero {
            self.coefficients.pop();
            self.degree = self.degree - 1;
        }
    }
    //Polynomial Scalar Multiply: a(X) * c
    fn multiply_scalar(&self, scalar: Scalar) -> Self {
        //create polynomial with zero coefficients with the highest term
        let mut coefficients = self.coefficients.clone();
        for i in 0..=self.degree {
            coefficients[i] = coefficients[i] * scalar;
        }
        Self {
            coefficients,
            degree: self.degree,
        }
    }

    //Polynomial Scalar Divide: a(X) / c
    fn divide_scalar(&self, scalar: Scalar) -> Self {
        //create polynomial with zero coefficients with the highest term
        let mut coefficients = self.coefficients.clone();
        let inv_scalar = scalar.invert();
        for i in 0..=self.degree {
            coefficients[i] = coefficients[i] * inv_scalar;
        }
        Self {
            coefficients,
            degree: self.degree,
        }
    }

    // Polynomial Multipliucation modulo m: a(X) * b(X)
    pub fn multiply(&self, other: &Self) -> Self {
        // If either polynomial is zero, return zero

        if self.coefficients.is_empty() || other.coefficients.is_empty() {
            return Polynomial {
                coefficients: vec![],
                degree: 0,
            };
        }
        let degree = self.degree + other.degree;
        //let self_degree = self.degree;
        //let other_degree = other.degree;
        let mut result_coeff: Vec<Scalar> = vec![Scalar::from(0u64); degree + 1];

        for i in 0..=self.degree {
            for j in 0..=other.degree {
                let mul = self.coefficients[i] * other.coefficients[j];
                result_coeff[i + j] += mul;
            }
        }
        Self {
            coefficients: result_coeff,
            degree: degree,
        }
    }
    //Polynomial Division modulo m
    //Works correctly only for this protocol
    //Assumes that both the polynomials are monic
    //Assumes that the polynomial a(X) has higher degree than b(X)
    //Assumes that both the polynomials have degree greater than 0
    //Evaluates (a(X) / b(X))
    //REMOVED: Also checks correctness of resulting polynomial for protocol
    pub fn divide(&mut self, denom: &mut Self, deg: usize) -> Self {
        self.poly_deg_adjust();
        denom.poly_deg_adjust();

        //let mut degree = self.degree - denom.degree;
        let mut degree: isize = deg as isize;
        let mut result_coeff: Vec<Scalar> = vec![Scalar::from(0u64); deg + 1];
        while self.degree >= denom.degree {
            //println!("Num degree {:?}", self.degree);
            //println!("Denom degree {:?}", denom.degree);

            let poly_t = create_ND_poly(self.coefficients[self.degree], self.degree - denom.degree);
            //println!("degree {:?}", degree);
            result_coeff[degree as usize] = poly_t.coefficients[degree as usize];
            degree = degree - 1;
            //degree = degree.checked_sub(1).unwrap_or(0);
            let poly_d = multiply_mut(denom, &poly_t);
            *self -= &poly_d;
            //self.sub_assign(&poly_d);
            self.poly_deg_adjust();
        }
        Self {
            coefficients: result_coeff,
            degree: deg,
        }
    }
    /// This evaluates a provided polynomial (in coefficient form) at `x`.
    pub fn evaluate_polynomial(&self, x: Scalar) -> Scalar {
        // TODO: parallelize?
        self.coefficients
            .iter()
            .rev()
            .fold(Scalar::zero(), |acc, coeff| acc * x + coeff)
    }
    // pub fn subtract_mut(a: &mut Polynomial, b: &Polynomial) {
    //     let result = (a as &Polynomial) - b;
    //     *a = result;
    // }
    //Multiplies polynomial p(X) with a vector "a" and returns a vector of polynomial
    pub fn polynomial_vector_product(&self, a: &[Scalar]) -> Vec<Polynomial> {
        a.iter()
            .map(|i| self.multiply(&create_1D_poly(Scalar::from(0u64), *i)))
            .collect()
    }
}
//Vectorial polynomial addition. Add vecftors of polynomials such that c[i] = A[i] + B[i].
pub fn polynomial_vectorial_add(a: &[Polynomial], b: &[Polynomial]) -> Vec<Polynomial> {
    assert_eq!(a.len(), b.len());
    a.iter().zip(b.iter()).map(|(x, y)| x + y).collect()
}

fn distinct(x: Scalar, a: &[Scalar]) -> bool {
    for i in 0..3 {
        if x == a[i] {
            return false;
        }
    }
    return true;
}
// Polynomial Multipliucation with mutable parameters modulo m: a(X) * b(X)
fn multiply_mut(a: &mut Polynomial, b: &Polynomial) -> Polynomial {
    // If either polynomial is zero, return zero

    if a.coefficients.is_empty() || b.coefficients.is_empty() {
        return Polynomial {
            coefficients: vec![],
            degree: 0,
        };
    }
    let degree = a.degree + b.degree;
    //let self_degree = self.degree;
    //let other_degree = other.degree;
    let mut result_coeff: Vec<Scalar> = vec![Scalar::from(0u64); degree + 1];

    for i in 0..=a.degree {
        for j in 0..=b.degree {
            let mul = a.coefficients[i] * b.coefficients[j];
            result_coeff[i + j] += mul;
        }
    }
    Polynomial {
        coefficients: result_coeff,
        degree: degree,
    }
}

//product of polynomials. (X-w_i)
fn create_l_x_polynomial(w: &[Scalar]) -> Polynomial {
    //Create l(X)
    let mut l = create_1D_poly(Scalar::from(1u64), -w[0]);
    for i in 1..w.len() {
        l = multiply_mut(&mut l, &create_1D_poly(Scalar::from(1u64), -w[i]));
    }
    return l;
}
//Create "l(X)" and "li(X)" polynomials
pub fn create_l_i_x_polynomial(w: &[Scalar]) -> [Polynomial; 4] {
    //check length of vector
    assert_eq!(w.len(), 3);
    //create l(X)
    let l_x = create_l_x_polynomial(&w[0..]);
    l_x.print_polynomial();
    //Create l_1(X) assuming length of w = 3
    let poly_num_1 = create_l_x_polynomial(&w[1..]);
    let poly_denom_1 = (w[0] - w[1]) * (w[0] - w[2]);
    let l_1_x = poly_num_1.divide_scalar(poly_denom_1);
    l_1_x.print_polynomial();
    //Create l_2(X) assuming length of w = 3
    let scalar: Vec<Scalar> = vec![w[0], w[2]];
    let poly_num_2 = create_l_x_polynomial(&scalar);
    let poly_denom_2 = (w[1] - w[0]) * (w[1] - w[2]);
    let l_2_x = poly_num_2.divide_scalar(poly_denom_2);
    l_2_x.print_polynomial();
    //Create l_3(X) assuming length of w = 3
    let poly_num_3 = create_l_x_polynomial(&w[0..2]);
    let poly_denom_3 = (w[2] - w[0]) * (w[2] - w[1]);
    let l_3_x = poly_num_3.divide_scalar(poly_denom_3);
    l_3_x.print_polynomial();
    //0 -> l(X), 1-> l_1(X), 2-> l_2(X), 3-> l_3(X)
    [l_x, l_1_x, l_2_x, l_3_x]
}

// //Create "l(X)" and "li(X)" polynomials
// pub fn create_l_poly(w: &[Scalar]) -> [Polynomial; 4] {
//     // let mut result_poly: Vec<Polynomial> = Vec::<Polynomial>::with_capacity(4);
//     println!("  ");
//     println!("In New");
//     //create l(X)
//     let l_x = create_l_x_polynomial(&w[1..]);
//     l_x.print_polynomial();
//     //result_poly.push(l_x.clone());
//     //Create li(X)
//     let num_1 = l_x
//         .clone()
//         .divide(&mut create_1D_poly(Scalar::from(1u64), -w[1]), 2);
//     let poly_denom_1 = (w[1] - w[2]) * (w[1] - w[3]);
//     let l_1_x = num_1.multiply(&create_1D_poly(Scalar::from(0u64), poly_denom_1.invert()));
//     l_1_x.print_polynomial();

//     let num_2 = l_x
//         .clone()
//         .divide(&mut create_1D_poly(Scalar::from(1u64), -w[2]), 2);
//     let poly_denom_2 = (w[2] - w[1]) * (w[2] - w[3]);
//     let l_2_x = num_2.multiply(&create_1D_poly(Scalar::from(0u64), poly_denom_2.invert()));
//     l_2_x.print_polynomial();

//     let num_3 = l_x
//         .clone()
//         .divide(&mut create_1D_poly(Scalar::from(1u64), -w[3]), 2);
//     let poly_denom_3 = (w[3] - w[1]) * (w[3] - w[2]);
//     let l_3_x = num_3.multiply(&create_1D_poly(Scalar::from(0u64), poly_denom_3.invert()));
//     l_3_x.print_polynomial();

//     // for i in 1..4
//     // {
//     // 	let denom = Scalar::from(1u64); //Denominator
//     // 	let num = l_x.divide(&mut create_1D_poly(Scalar::from(1u64), -w[i]), 2);
//     // 	for (int j = 1; j <= dim; j++)
//     // 		if (i != j)	denom = denom * (w[i] - w[j]);
//     // 	denom = ((denom % m) + m) % m;
//     // 	int inv = mul_inv(m, denom);
//     // 	l[i] = poly_product(l[i], create_1D_poly(0, inv));
//     // }

//     [l_x, l_1_x, l_2_x, l_3_x]
// }
//Polynomial Addition modulo m: a(X) + b(X)
impl<'a, 'b> Add<&'a Polynomial> for &'b Polynomial {
    type Output = Polynomial;
    fn add(self, other: &Polynomial) -> Polynomial {
        // let c_degree = 0 as usize;
        //create polynomial with zero coefficients with the highest term
        // let mut c = vec![Scalar::zero(); h_degree + 1];
        // for i in 0..=self.degree {
        //     c[i] = c[i] + self.coefficients[i];
        // }
        // for i in 0..=other.degree {
        //     c[i] = c[i] + other.coefficients[i];
        // }
        let summed: Vec<Scalar> = self
            .coefficients
            .iter()
            .zip_longest(other.coefficients.iter())
            .map(|a: itertools::EitherOrBoth<&Scalar, &Scalar>| match a {
                Both(l, r) => (*l + *r),
                Left(l) => *l,
                Right(r) => *r,
            })
            .collect();
        let degree = summed.len() - 1;
        Polynomial {
            coefficients: summed,
            degree: degree,
        }
    }
}

//Polynomial Subtraction modulo m: a(X) - b(X)

impl<'a, 'b> Sub<&'a Polynomial> for &'b Polynomial {
    type Output = Polynomial;

    fn sub(self, other: &Polynomial) -> Polynomial {
        //create polynomial with zero coefficients with the highest term
        let diff: Vec<Scalar> = self
            .coefficients
            .iter()
            .zip_longest(other.coefficients.iter())
            .map(|a: itertools::EitherOrBoth<&Scalar, &Scalar>| match a {
                Both(l, r) => (*l - *r),
                Left(l) => *l,
                Right(r) => -*r,
            })
            .collect();
        let degree = diff.len() - 1;
        Polynomial {
            coefficients: diff,
            degree: degree,
        }
    }
}
impl<'b> SubAssign<&'b Polynomial> for Polynomial {
    fn sub_assign(&mut self, rhs: &Polynomial) {
        let result = (self as &Polynomial) - rhs;
        *self = result;
    }
}
impl PartialEq for Polynomial {
    fn eq(&self, other: &Polynomial) -> bool {
        if self.degree == other.degree {
            self.coefficients == other.coefficients
        } else {
            false
        }
    }
}

pub fn compute_polynomial_expression(
    l_x_vec: &[Polynomial],
    a: &Array2D<Scalar>,
    a_0: &[Scalar],
) -> Vec<Polynomial> {
    //convert witness Matrices to row major order
    let a_row = a.as_rows();
    let a_0_l_x = l_x_vec[0].polynomial_vector_product(&a_0);
    let a_1_l_1_x = l_x_vec[1].polynomial_vector_product(&a_row[0]);
    let a_2_l_2_x = l_x_vec[2].polynomial_vector_product(&a_row[1]);
    let a_3_l_3_x = l_x_vec[3].polynomial_vector_product(&a_row[2]);

    polynomial_vectorial_add(
        &polynomial_vectorial_add(&polynomial_vectorial_add(&a_0_l_x, &a_1_l_1_x), &a_2_l_2_x),
        &a_3_l_3_x,
    )
}

pub fn create_hadamard_proof(
    a: &Array2D<Scalar>,
    b: &Array2D<Scalar>,
    c: &Array2D<Scalar>,
    witness_r: &[Scalar],
    witness_s: &[Scalar],
    witness_t: &[Scalar], //random scalar vector of length m for Commiting on witness
    comit_a: &[RistrettoPoint],
    comit_b: &[RistrettoPoint],
    comit_c: &[RistrettoPoint],
    pc_gens: &PedersenGens,
    xpc_gens: &VectorPedersenGens,
) {
    //create ca_0,cb_0,cc_0
    let a_0: Vec<_> = (0..COLUMNS).map(|_| Scalar::random(&mut OsRng)).collect();
    let b_0: Vec<_> = (0..COLUMNS).map(|_| Scalar::random(&mut OsRng)).collect();
    let c_0 = vectorutil::hadamard_product(&a_0, &b_0);

    //pick r0, s0, t0
    let r_0 = Scalar::random(&mut OsRng);
    let s_0 = Scalar::random(&mut OsRng);
    let t_0 = Scalar::random(&mut OsRng);

    //comit on a0 and b0 and c0
    let c_a_0 = xpc_gens.commit(&a_0, r_0).compress();
    let c_b_0 = xpc_gens.commit(&b_0, s_0).compress();
    let c_c_0 = xpc_gens.commit(&c_0, t_0).compress();

    //Finding Polynomials l(X) and li(X) for 1 <= i <= 3
    //These polynomials are stored in "l" array
    //l[0] stores l(X), l[1] stores l1(X), l[2] stores l2(X), and so on as required
    //Both Prover and Verifier agrees on w_i (omega) values
    //w_0 is not used

    let w: Vec<_> = (0..3).map(|_| Scalar::random(&mut OsRng)).collect();
    let l_x_vec = create_l_i_x_polynomial(&w);
    //check if the vector is constructed properly
    if l_x_vec.len() != 4 {
        panic!("L(X) polynomials are not constructed properly");
    }

    //Finding Delta_i for 0 <= i <= 3 from Step 4 equation (Page 84) of Stephanie Bayer Thesis
    //Need a loop if committed vectors are "k", here k = 3, since we have a0, a1, a2, a3
    //RHS of the equation is directly calculated below

    let a_expression = compute_polynomial_expression(&l_x_vec, a, &a_0);
    let b_expression = compute_polynomial_expression(&l_x_vec, b, &b_0);
    let c_expression = compute_polynomial_expression(&l_x_vec, c, &c_0);

    // poly * A = poly_vectorial_add(
    //     poly_vectorial_add(poly_vec_product(l[0], a0), poly_vec_product(l[1], a1)),
    //     poly_vec_product(l[2], a2),
    // );

    // poly * B = poly_vectorial_add(
    //     poly_vectorial_add(poly_vec_product(l[0], b0), poly_vec_product(l[1], b1)),
    //     poly_vec_product(l[2], b2),
    // );
    // poly * C = poly_vectorial_add(
    //     poly_vectorial_add(poly_vec_product(l[0], c0), poly_vec_product(l[1], c1)),
    //     poly_vec_product(l[2], c2),
    // );

    //Evaluates (a.l(X) x b.l(X)) - cl(X))
    let a_b_c: Vec<_> = a_expression
        .iter()
        .zip(b_expression.iter())
        .zip(c_expression.iter())
        .map(|((a, b), c)| &a.multiply(b) - c)
        .collect();
    println!("abc size {}", a_b_c.len());
    //Evaluates (a.l(X) x b.l(X)) - cl(X)) / l(X)
    let div_res: Vec<Polynomial> = a_b_c
        .into_iter()
        .map(|mut poly| poly.divide(&mut l_x_vec[0].clone(), poly.degree - l_x_vec[0].degree))
        .collect();
    println!("res size {}", div_res.len());
    div_res[0].print_polynomial();
    div_res[1].print_polynomial();
    div_res[2].print_polynomial();

    //extract delta_i from delta_i * X^i
    // for (int i = 0; i < (2 + 1); i++)
    // 	for (int j = 0; j < dim; j++)
    // 		Delta[i][j] = RHS[j].coeff[i];
    let mut delta_vec: Vec<Vec<Scalar>> = Vec::new();
    for i in 0..4 {
        let mut inner_vec: Vec<Scalar> = Vec::new();
        for j in 0..3 {
            inner_vec.push(div_res[j].coefficients[i]);
        }
        delta_vec.push(inner_vec);
    }
    println!("{:?}", delta_vec);

    //commit on Delta vector
    let rho: Vec<_> = (0..a.num_rows() + 1)
        .map(|_| Scalar::random(&mut OsRng))
        .collect();
    let mut comit_delta_vec = Vec::<RistrettoPoint>::new();

    for (i, row) in delta_vec.iter().enumerate() {
        comit_delta_vec.push(xpc_gens.commit(row, rho[i]));
    }

    //Send: ca0,cb0,cc0,c 0,...,c m

    //Challenge: x Z⇤q \ ⌦

    let x = Scalar::random(&mut OsRng);

    //Prover evaluates a_bar, b_bar, c_bar, r_bar, s_bar, t_bar, rho_bar
    let mut a_bar: [Scalar; 3] = [Scalar::zero(), Scalar::zero(), Scalar::zero()];
    let mut b_bar: [Scalar; 3] = [Scalar::zero(), Scalar::zero(), Scalar::zero()];
    let mut c_bar: [Scalar; 3] = [Scalar::zero(), Scalar::zero(), Scalar::zero()];
    for i in 0..3
    // <dim
    {
        a_bar[i] = a_expression[i].evaluate_polynomial(x);
        b_bar[i] = b_expression[i].evaluate_polynomial(x);
        c_bar[i] = c_expression[i].evaluate_polynomial(x);
    }
    let mut eval = l_x_vec[0].evaluate_polynomial(x);
    let mut r_bar = r_0 * eval;
    let mut s_bar = s_0 * eval;
    let mut t_bar = t_0 * eval;
    for i in 0..3 {
        eval = l_x_vec[i + 1].evaluate_polynomial(x);
        r_bar = r_bar + (witness_r[i] * eval);
        s_bar = s_bar + (witness_s[i] * eval);
        t_bar = t_bar + (witness_t[i] * eval);
    }
    let exp_x: Vec<_> = vectorutil::exp_iter(x).take(4).collect();
    let x_i_rho_i: Scalar = exp_x.iter().zip(rho.iter()).map(|(x, r)| x * r).sum();
    let rho_bar = l_x_vec[0].evaluate_polynomial(x) * x_i_rho_i;
    // Send: a_bar, b_bar, c_bar, r_bar, s_bar, t_bar, rho_bar
    //Verifier checks commitments and accept accordingly
    //Check for a_bar
    let comit_a_bar = xpc_gens.commit(&a_bar, r_bar);
    let comit_b_bar = xpc_gens.commit(&b_bar, s_bar);
    let comit_c_bar = xpc_gens.commit(&c_bar, t_bar);

    let mut eval_l = l_x_vec[0].evaluate_polynomial(x);
    let mut comit_a_0: RistrettoPoint = c_a_0.decompress().unwrap() * eval_l;
    let mut comit_b_0: RistrettoPoint = c_b_0.decompress().unwrap() * eval_l;
    let mut comit_c_0: RistrettoPoint = c_c_0.decompress().unwrap() * eval_l;

    for i in 0..3 {
        eval_l = l_x_vec[i + 1].evaluate_polynomial(x);
        comit_a_0 = comit_a_0 + (comit_a[i] * eval_l);
        comit_b_0 = comit_b_0 + (comit_b[i] * eval_l);
        comit_c_0 = comit_c_0 + (comit_c[i] * eval_l);
    }

    //check
    if comit_a_0 == comit_a_bar && comit_b_0 == comit_b_bar && comit_c_0 == comit_c_bar {
        println!("true");
    } else {
        println!("false");
    }
    //check delta
    let mut commitment_delta: RistrettoPoint = comit_delta_vec[0];
    for i in 1..4 {
        commitment_delta = commitment_delta + (comit_delta_vec[i] * exp_x[i]);
    }
    let lhs = commitment_delta * l_x_vec[0].evaluate_polynomial(x);
    let a_bar_b_bar = vectorutil::hadamard_product(&a_bar, &b_bar);
    let a_bar_b_bar_c_bar: Vec<_> = a_bar_b_bar
        .iter()
        .zip(c_bar.iter())
        .map(|(ab, c)| ab - c)
        .collect();
    let rhs = xpc_gens.commit(&a_bar_b_bar_c_bar, rho_bar);
    if lhs == rhs {
        println!("LHS true");
    } else {
        println!("LHS false");
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use curve25519_dalek::scalar::Scalar;
    #[test]

    fn create_polynomial_test() {
        let poly = create_1D_poly(Scalar::from(1u64), Scalar::from(3u64));
        poly.print_polynomial();
        //assert_eq!(reference, exp_2);
    }
    #[test]

    fn create_ND_polynomial_test() {
        let poly = create_ND_poly(Scalar::from(4u64), 7);
        poly.print_polynomial();
        //assert_eq!(reference, exp_2);
    }
    #[test]
    fn deg_adjust_polynomial_test() {
        let mut poly = create_ND_poly(Scalar::from(3u64), 2);
        //poly.print_polynomial();
        poly.poly_deg_adjust();
        poly.print_polynomial();
        //assert_eq!(reference, exp_2);
    }
    #[test]
    fn normalize_polynomial_test() {
        let mut poly = Polynomial {
            coefficients: vec![
                Scalar::from(2u64),
                Scalar::from(3u64),
                Scalar::from(0u64),
                Scalar::from(0u64),
            ],
            degree: 3,
        };
        poly.print_polynomial();
        poly.normalize();
        poly.print_polynomial();

        //assert_eq!(reference, exp_2);
    }
    #[test]
    fn add_polynomial_same_degree_test() {
        let polya = Polynomial {
            coefficients: vec![
                Scalar::from(2u64),
                Scalar::from(3u64),
                Scalar::from(4u64),
                Scalar::from(6u64),
            ],
            degree: 3,
        };
        let polyb = Polynomial {
            coefficients: vec![
                Scalar::from(1u64),
                Scalar::from(2u64),
                Scalar::from(3u64),
                Scalar::from(4u64),
            ],
            degree: 3,
        };
        let add = &polya + &polyb;
        // let add = polya.add(&polyb);
        add.print_polynomial();

        //assert_eq!(reference, exp_2);
    }
    #[test]
    fn add_polynomial_different_degree_test() {
        let polya = Polynomial {
            coefficients: vec![Scalar::from(2u64), Scalar::from(3u64)],
            degree: 1,
        };
        let polyb = Polynomial {
            coefficients: vec![
                Scalar::from(1u64),
                Scalar::from(2u64),
                Scalar::from(3u64),
                Scalar::from(4u64),
            ],
            degree: 3,
        };
        //let add = polya.add(&polyb);
        let add = &polya + &polyb;
        add.print_polynomial();

        //assert_eq!(reference, exp_2);
    }
    #[test]
    fn sub_polynomial_same_degree_test() {
        let polya = Polynomial {
            coefficients: vec![
                Scalar::from(2u64),
                Scalar::from(3u64),
                Scalar::from(4u64),
                Scalar::from(6u64),
            ],
            degree: 3,
        };
        let polyb = Polynomial {
            coefficients: vec![
                Scalar::from(1u64),
                Scalar::from(2u64),
                Scalar::from(3u64),
                Scalar::from(4u64),
            ],
            degree: 3,
        };
        let sub = &polya - &polyb;
        // let add = polya.sub(&polyb);
        sub.print_polynomial();

        //assert_eq!(reference, exp_2);
    }
    #[test]
    fn subassign_polynomial_test() {
        let mut polya = Polynomial {
            coefficients: vec![
                Scalar::from(2u64),
                Scalar::from(3u64),
                Scalar::from(4u64),
                Scalar::from(6u64),
            ],
            degree: 3,
        };
        let polyb = Polynomial {
            coefficients: vec![
                Scalar::from(1u64),
                Scalar::from(2u64),
                Scalar::from(3u64),
                Scalar::from(4u64),
            ],
            degree: 3,
        };
        polya -= &polyb;
        // let add = polya.sub(&polyb);
        polya.print_polynomial();

        //assert_eq!(reference, exp_2);
    }
    #[test]
    fn sub_polynomial_different_degree_test() {
        let polya = Polynomial {
            coefficients: vec![Scalar::from(2u64), Scalar::from(3u64)],
            degree: 1,
        };
        let polyb = Polynomial {
            coefficients: vec![
                Scalar::from(1u64),
                Scalar::from(2u64),
                Scalar::from(3u64),
                Scalar::from(4u64),
            ],
            degree: 3,
        };
        let sub = &polya - &polyb;
        //let add = polyb.sub(&polya);
        sub.print_polynomial();

        //assert_eq!(reference, exp_2);
    }
    #[test]
    fn multiply_scalar_test() {
        let polya = Polynomial {
            coefficients: vec![Scalar::from(2u64), Scalar::from(3u64)],
            degree: 1,
        };
        let res = polya.multiply_scalar(Scalar::from(3u64));
        res.print_polynomial();

        //assert_eq!(reference, exp_2);
    }
    #[test]
    fn divide_scalar_test() {
        let polya = Polynomial {
            coefficients: vec![Scalar::from(4u64), Scalar::from(2u64)],
            degree: 1,
        };
        let res = polya.divide_scalar(Scalar::from(2u64));
        res.print_polynomial();

        //assert_eq!(reference, exp_2);
    }
    #[test]
    fn multiply_polynomial_test() {
        let polya = Polynomial {
            coefficients: vec![Scalar::from(2u64), Scalar::from(3u64)],
            degree: 1,
        };
        let polyb = Polynomial {
            coefficients: vec![Scalar::from(5u64), Scalar::from(2u64)],
            degree: 1,
        };
        let res = polya.multiply(&polyb);
        res.print_polynomial();

        //assert_eq!(reference, exp_2);
    }
    #[test]
    fn divide_polynomial_test() {
        let s = Scalar::from(2u64);
        let mut num = Polynomial {
            coefficients: vec![Scalar::from(6u64), Scalar::from(1u64), Scalar::from(1u64)],
            degree: 2,
        };
        let mut denom = Polynomial {
            coefficients: vec![Scalar::from(3u64), Scalar::from(1u64)],
            degree: 1,
        };
        let res = num.divide(&mut denom, 1);
        let reference = Polynomial {
            coefficients: vec![-s, Scalar::from(1u64)],
            degree: 1,
        };
        //res.print_polynomial();

        assert_eq!(reference, res);
    }
    #[test]
    fn polynomial_vec_product_test() {
        let poly = Polynomial {
            //x^2 + x + 6
            coefficients: vec![Scalar::from(6u64), Scalar::from(1u64), Scalar::from(1u64)],
            degree: 2,
        };
        let scalar = vec![Scalar::from(3u64), Scalar::from(1u64)];
        let reference = vec![
            Polynomial {
                //3x^2 + 3x +18
                coefficients: vec![Scalar::from(18u64), Scalar::from(3u64), Scalar::from(3u64)],
                degree: 2,
            },
            Polynomial {
                //x^2 + x + 6
                coefficients: vec![Scalar::from(6u64), Scalar::from(1u64), Scalar::from(1u64)],
                degree: 2,
            },
        ];
        let res = poly.polynomial_vector_product(&scalar);

        assert_eq!(reference[0], res[0]);
        assert_eq!(reference[1], res[1]);
    }
    #[test]
    fn vectorial_polynomial_add_test() {
        let x = vec![
            Polynomial {
                coefficients: vec![Scalar::from(1u64), Scalar::from(1u64), Scalar::from(1u64)],
                degree: 2,
            },
            Polynomial {
                coefficients: vec![
                    Scalar::from(3u64),
                    Scalar::from(0u64),
                    Scalar::from(1u64),
                    Scalar::from(2u64),
                ],
                degree: 3,
            },
            Polynomial {
                coefficients: vec![Scalar::from(3u64), Scalar::from(9u64)],
                degree: 1,
            },
        ];

        let y = vec![
            Polynomial {
                coefficients: vec![Scalar::from(2u64), Scalar::from(3u64)],
                degree: 1,
            },
            Polynomial {
                coefficients: vec![Scalar::from(5u64), Scalar::from(4u64), Scalar::from(9u64)],
                degree: 2,
            },
            Polynomial {
                coefficients: vec![Scalar::from(0u64), Scalar::from(1u64)],
                degree: 1,
            },
        ];
        let reference = vec![
            Polynomial {
                coefficients: vec![Scalar::from(3u64), Scalar::from(4u64), Scalar::from(1u64)],
                degree: 2,
            },
            Polynomial {
                coefficients: vec![
                    Scalar::from(8u64),
                    Scalar::from(4u64),
                    Scalar::from(10u64),
                    Scalar::from(2u64),
                ],
                degree: 3,
            },
            Polynomial {
                coefficients: vec![Scalar::from(3u64), Scalar::from(10u64)],
                degree: 1,
            },
        ];
        let res = polynomial_vectorial_add(&x, &y);

        assert_eq!(reference[0], res[0]);
        assert_eq!(reference[1], res[1]);
        assert_eq!(reference[2], res[2]);
    }
    #[test]
    fn l_x_polynomial_test() {
        let w: Vec<Scalar> = vec![Scalar::from(1u64), Scalar::from(2u64), Scalar::from(3u64)];
        let poly = create_l_x_polynomial(&w);
        let s = Scalar::from(6u64);
        let reference = Polynomial {
            coefficients: vec![-s, Scalar::from(11u64), -s, Scalar::from(1u64)],
            degree: 3,
        };
        // poly.print_polynomial();

        assert_eq!(reference, poly);
    }
    #[test]
    fn l_i_x_polynomial_test() {
        let w: Vec<Scalar> = vec![
            Scalar::from(5u64),
            Scalar::from(1u64),
            Scalar::from(2u64),
            Scalar::from(3u64),
        ];
        let _poly = create_l_i_x_polynomial(&w);
        // let _poly2 = create_l_poly(&w);
        // poly.print_polynomial();

        //assert_eq!(reference, exp_2);
    }
    #[test]
    fn evaluate_polynomial_test() {
        let polya = Polynomial {
            coefficients: vec![Scalar::from(2u64), Scalar::from(3u64)],
            degree: 1,
        };
        let x: Scalar = Scalar::from(3u64);
        let polyb = Polynomial {
            coefficients: vec![
                Scalar::from(1u64),
                Scalar::from(2u64),
                Scalar::from(3u64),
                Scalar::from(4u64),
            ],
            degree: 3,
        };

        // println!("Polya {:?}", polya.evaluate_polynomial(x));
        // println!("Polyb {:?}", polyb.evaluate_polynomial(x));
        assert_eq!(polya.evaluate_polynomial(x), Scalar::from(11u64));
        assert_eq!(polyb.evaluate_polynomial(x), Scalar::from(142u64));
    }

    #[test]
    fn create_hadamard_proof_test() {
        //generate Xcomit generator points of length m+1
        let xpc_gens = VectorPedersenGens::new(ROWS + 1);
        let pc_gens = PedersenGens::default();
        let a_scalar: Vec<_> = vec![
            Scalar::from(7u64),
            Scalar::from(6u64),
            Scalar::from(1u64),
            Scalar::from(5u64),
            Scalar::from(3u64),
            Scalar::from(4u64),
            Scalar::from(2u64),
            Scalar::from(8u64),
            Scalar::from(9u64),
        ];

        let b_scalar: Vec<_> = vec![
            Scalar::from(3u64),
            Scalar::from(2u64),
            Scalar::from(1u64),
            Scalar::from(7u64),
            Scalar::from(3u64),
            Scalar::from(5u64),
            Scalar::from(8u64),
            Scalar::from(3u64),
            Scalar::from(6u64),
        ];

        let c_scalar = vectorutil::hadamard_product(&a_scalar, &b_scalar);
        let a_2d = Array2D::from_row_major(&a_scalar, ROWS, COLUMNS);
        let b_2d = Array2D::from_row_major(&b_scalar, ROWS, COLUMNS);
        let c_2d = Array2D::from_row_major(&c_scalar, ROWS, COLUMNS);

        let r: Vec<_> = vec![Scalar::from(6u64), Scalar::from(2u64), Scalar::from(5u64)];
        let s: Vec<_> = vec![Scalar::from(7u64), Scalar::from(1u64), Scalar::from(3u64)];
        let t: Vec<_> = vec![Scalar::from(5u64), Scalar::from(2u64), Scalar::from(1u64)];

        let a_2d_as_rows = a_2d.as_rows();
        //let r: Vec<_> = (0..COLUMNS).map(|_| Scalar::random(&mut OsRng)).collect();
        let mut comit_a_vec = Vec::<RistrettoPoint>::new();
        for i in 0..COLUMNS {
            comit_a_vec.push(xpc_gens.commit(&a_2d_as_rows[i], r[i]));
        }

        let b_2d_as_rows = b_2d.as_rows();
        //let r: Vec<_> = (0..COLUMNS).map(|_| Scalar::random(&mut OsRng)).collect();
        let mut comit_b_vec = Vec::<RistrettoPoint>::new();
        for i in 0..COLUMNS {
            comit_b_vec.push(xpc_gens.commit(&b_2d_as_rows[i], s[i]));
        }
        let c_2d_as_rows = c_2d.as_rows();
        //let r: Vec<_> = (0..COLUMNS).map(|_| Scalar::random(&mut OsRng)).collect();
        let mut comit_c_vec = Vec::<RistrettoPoint>::new();
        for i in 0..COLUMNS {
            comit_c_vec.push(xpc_gens.commit(&c_2d_as_rows[i], t[i]));
        }

        create_hadamard_proof(
            &a_2d,
            &b_2d,
            &c_2d,
            &r,
            &s,
            &t,
            &comit_a_vec,
            &comit_b_vec,
            &comit_c_vec,
            &pc_gens,
            &xpc_gens,
        )

        // println!("Polya {:?}", polya.evaluate_polynomial(x));
        // println!("Polyb {:?}", polyb.evaluate_polynomial(x));
        //  assert_eq!(polya.evaluate_polynomial(x), Scalar::from(11u64));
        // assert_eq!(polyb.evaluate_polynomial(x), Scalar::from(142u64));
    }
}
