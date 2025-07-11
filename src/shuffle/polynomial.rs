/// Polynomial utilities for the Quisquis shuffle protocol.
///
/// This module provides types and functions for constructing, manipulating, and evaluating polynomials
/// used in shuffle and Hadamard argument proofs.
///
/// ## Core Components
///
/// - [`crate::shuffle::polynomial::Polynomial`] - Polynomial type and arithmetic
/// - Utility functions for Lagrange interpolation, vector products, and polynomial operations
///
use crate::shuffle::shuffle::COLUMNS;
use array2d::Array2D;

use crate::pedersen::vectorpedersen::VectorPedersenGens;
use crate::shuffle::vectorutil;
use core::fmt::Debug;
use curve25519_dalek::{ristretto::RistrettoPoint, scalar::Scalar};
use itertools::EitherOrBoth::{Both, Left, Right};
use itertools::Itertools;
use rand::rngs::OsRng;
use std::ops::Add;
use std::ops::{Sub, SubAssign};

///Create a single degree polynomial: aX + b
///
/// # Arguments
///
/// * `a` - a `Scalar` instance carrying the coefficient of the polynomial
/// * `b` - a `Scalar` instance carrying the constant term of the polynomial
///
/// # Returns
///
/// A `Polynomial` instance carrying the polynomial.
fn create_1d_poly(a: Scalar, b: Scalar) -> Polynomial {
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

///Create a monomial of a given degree
///
/// # Arguments
///
/// * `a` - a `Scalar` instance carrying the coefficient of the polynomial
/// * `n` - a `usize` instance carrying the degree of the polynomial
///
/// # Returns
///
/// A `Polynomial` instance carrying the polynomial.
fn create_n_degree_poly(a: Scalar, n: usize) -> Polynomial {
    let mut coeff: Vec<Scalar> = vec![Scalar::zero(); n + 1];
    coeff[n] = a;
    Polynomial {
        coefficients: coeff,
        degree: n,
    }
}
/// A univariate polynomial over Scalars, represented by its coefficients and degree.
///
/// Coefficients are stored in ascending order, where the i-th element corresponds to the coefficient of X^i.
#[derive(Debug, Clone)]
pub struct Polynomial {
    /// Coefficients of the polynomial in ascending order of degree.
    pub coefficients: Vec<Scalar>,
    /// Degree of the polynomial.
    pub degree: usize,
}

impl Polynomial {
    /// Prints the polynomial to stdout in human-readable form.
    ///
    /// It displays the degree and each coefficient term as `coef * X^power`.
    pub fn print_polynomial(&self) {
        println!("Degree {:?} ", self.degree);
        for (i, x) in self.coefficients.iter().enumerate() {
            print!("{:?} X^ {} + ", x, i);
        }
    }
    /// Adjusts the stored degree to match the highest non-zero coefficient.
    ///
    /// Trailing zero coefficients are removed, and the degree field is updated.
    pub fn poly_deg_adjust(&mut self) {
        let mut h_term: usize = 0;

        for i in 0..=self.degree {
            if self.coefficients[i] == Scalar::zero() {
                continue;
            } else {
                h_term = i;
            }
        }
        self.degree = h_term;
        let mut newcoeff = Vec::<Scalar>::with_capacity(h_term);
        for i in 0..=self.degree {
            newcoeff.push(self.coefficients[i]);
        }
        self.coefficients = newcoeff;
    }
    /// Removes any trailing zero coefficients and updates the degree accordingly.
    ///
    /// This ensures that `degree` accurately reflects the highest term with a non-zero coefficient.
    pub fn normalize(&mut self) {
        // Borrow mutably when you mutate the data, but don't want to consume it
        let zero = Scalar::zero();
        while *self.coefficients.last().unwrap() == zero {
            self.coefficients.pop();
            self.degree = self.degree - 1;
        }
    }
    /// Scales the polynomial by multiplying every coefficient by `scalar`.
    ///
    /// # Arguments
    ///
    /// * `scalar` - The scalar to multiply each coefficient by.
    ///
    /// # Returns
    ///
    /// A new `Polynomial` with all coefficients scaled.
    pub fn multiply_scalar(&self, scalar: Scalar) -> Self {
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

    /// Scales the polynomial by dividing every coefficient by `scalar`.
    ///
    /// # Arguments
    ///
    /// * `scalar` - The scalar divisor for each coefficient (must be invertible).
    ///
    /// # Returns
    ///
    /// A new `Polynomial` with all coefficients divided.
    pub fn divide_scalar(&self, scalar: Scalar) -> Self {
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

    /// Multiplies two polynomials using standard long multiplication.
    ///
    /// # Arguments
    ///
    /// * `other` - The polynomial to multiply with.
    ///
    /// # Returns
    ///
    /// The product polynomial.
    pub fn multiply(&self, other: &Self) -> Self {
        // If either polynomial is zero, return zero

        if self.coefficients.is_empty() || other.coefficients.is_empty() {
            return Polynomial {
                coefficients: vec![],
                degree: 0,
            };
        }
        let degree = self.degree + other.degree;
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

    /// Divides this polynomial by the provided denominator polynomial using long division.
    ///
    /// This method assumes both `self` and `denom` are monic polynomials, and that
    /// the degree of `self` is strictly greater than the degree of `denom`. The
    /// returned polynomial has the specified degree `deg`.
    ///
    /// # Arguments
    ///
    /// * `denom` – The monic denominator polynomial.
    /// * `deg` – The degree of the resulting quotient polynomial.
    ///
    /// # Returns
    ///
    /// A `Polynomial` representing the quotient of the division.
    pub fn divide(&mut self, denom: &mut Self, deg: usize) -> Self {
        self.poly_deg_adjust();
        denom.poly_deg_adjust();

        //let mut degree = self.degree - denom.degree;
        let mut degree: isize = deg as isize;
        let mut result_coeff: Vec<Scalar> = vec![Scalar::from(0u64); deg + 1];
        while self.degree >= denom.degree {
            //println!("Num degree {:?}", self.degree);
            //println!("Denom degree {:?}", denom.degree);

            let poly_t =
                create_n_degree_poly(self.coefficients[self.degree], self.degree - denom.degree);
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
    /// Evaluates the polynomial at the given scalar point `x`.
    ///
    /// Uses Horner's method for efficient computation.
    ///
    /// # Arguments
    ///
    /// * `x` - The point at which to evaluate the polynomial.
    ///
    /// # Returns
    ///
    /// The resulting `Scalar` value.
    pub fn evaluate_polynomial(&self, x: Scalar) -> Scalar {
        // TODO: parallelize?
        self.coefficients
            .iter()
            .rev()
            .fold(Scalar::zero(), |acc, coeff| acc * x + coeff)
    }
    /// Applies this polynomial to each element of a scalar slice, returning a vector of results.
    ///
    /// # Arguments
    ///
    /// * `a` - Slice of Scalars to which to apply the polynomial.
    ///
    /// # Returns
    ///
    /// A vector of `Polynomial` instances corresponding to `self(X) * a[i]`.
    pub fn polynomial_vector_product(&self, a: &[Scalar]) -> Vec<Polynomial> {
        a.iter()
            .map(|i| self.multiply(&create_1d_poly(Scalar::from(0u64), *i)))
            .collect()
    }
}
///Vectorial polynomial addition. Add vectors of polynomials such that `c[i] = a[i] + b[i]`.
///
/// # Arguments
///
/// * `a` - a `Vec<Polynomial>` instance carrying the vector of polynomials
/// * `b` - a `Vec<Polynomial>` instance carrying the vector of polynomials
///
/// # Returns
///
/// A `Vec<Polynomial>` instance carrying the vector of polynomials.
pub fn polynomial_vectorial_add(a: &[Polynomial], b: &[Polynomial]) -> Vec<Polynomial> {
    assert_eq!(a.len(), b.len());
    a.iter().zip(b.iter()).map(|(x, y)| x + y).collect()
}
/// Checks if a scalar is distinct from a vector of scalars.
///
/// # Arguments
///
/// * `num` - a `Scalar` instance carrying the scalar
/// * `vec` - a `Vec<Scalar>` instance carrying the vector of scalars
///
/// # Returns
///
/// A `bool` instance carrying the result of the check.
pub fn distinct(num: Scalar, vec: &[Scalar]) -> bool {
    for s in vec.iter() {
        if num == *s {
            return false;
        }
    }
    return true;
}
/// Multiply two polynomials, using a mutable reference to the first polynomial and a borrowed reference to the second.
///
/// This method performs standard polynomial long multiplication: each coefficient in `a` is
/// multiplied by each coefficient in `b`, and the products are summed into the appropriate
/// coefficient positions in the result.
///
/// # Arguments
///
/// * `a` – The multiplicand polynomial, provided as a mutable reference.
/// * `b` – The multiplier polynomial, provided as a borrowed reference.
///
/// # Returns
///
/// A new `Polynomial` representing the product `a(X) * b(X)`.
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

/// Constructs the polynomial `l(X) = ∏_{i=0..n-1} (X - w[i])` for a given witness vector.
///
/// # Arguments
///
/// * `w` - Slice of Scalars for roots of the polynomial.
///
/// # Returns
///
/// The polynomial with roots at each `w[i]`.
pub fn create_l_x_polynomial(w: &[Scalar]) -> Polynomial {
    //Create l(X)
    let mut l = create_1d_poly(Scalar::from(1u64), -w[0]);
    for i in 1..w.len() {
        l = multiply_mut(&mut l, &create_1d_poly(Scalar::from(1u64), -w[i]));
    }
    return l;
}
/// Create "l(X)" and "li(X)" polynomials
///
/// # Arguments
///
/// * `w` - a `Vec<Scalar>` instance carrying the vector of scalars
///
/// # Returns
///
/// A `[Polynomial; 4]` instance carrying the vector of polynomials.
pub fn create_l_i_x_polynomial(w: &[Scalar]) -> [Polynomial; 4] {
    //check length of vector
    assert_eq!(w.len(), 3);
    //create l(X)
    let l_x = create_l_x_polynomial(&w[0..]);
    //  l_x.print_polynomial();
    //Create l_1(X) assuming length of w = 3
    let poly_num_1 = create_l_x_polynomial(&w[1..]);
    let poly_denom_1 = (w[0] - w[1]) * (w[0] - w[2]);
    let l_1_x = poly_num_1.divide_scalar(poly_denom_1);
    // l_1_x.print_polynomial();
    //Create l_2(X) assuming length of w = 3
    let scalar: Vec<Scalar> = vec![w[0], w[2]];
    let poly_num_2 = create_l_x_polynomial(&scalar);
    let poly_denom_2 = (w[1] - w[0]) * (w[1] - w[2]);
    let l_2_x = poly_num_2.divide_scalar(poly_denom_2);
    // l_2_x.print_polynomial();
    //Create l_3(X) assuming length of w = 3
    let poly_num_3 = create_l_x_polynomial(&w[0..2]);
    let poly_denom_3 = (w[2] - w[0]) * (w[2] - w[1]);
    let l_3_x = poly_num_3.divide_scalar(poly_denom_3);
    // l_3_x.print_polynomial();
    //0 -> l(X), 1-> l_1(X), 2-> l_2(X), 3-> l_3(X)
    [l_x, l_1_x, l_2_x, l_3_x]
}

/// Adds two polynomials term-wise, extending zeros to match degrees.
///
/// # Returns
///
/// The sum polynomial.
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
                Both(l, r) => *l + *r,
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

/// Polynomial Subtraction modulo m: a(X) - b(X)
impl<'a, 'b> Sub<&'a Polynomial> for &'b Polynomial {
    type Output = Polynomial;
    ///
    /// Subtracts two polynomials, returning a new polynomial that is the difference of the two.
    ///
    /// # Arguments
    ///
    /// * `self` - a `Polynomial` instance carrying the polynomial
    /// * `other` - a `Polynomial` instance carrying the other polynomial
    fn sub(self, other: &Polynomial) -> Polynomial {
        //create polynomial with zero coefficients with the highest term
        let diff: Vec<Scalar> = self
            .coefficients
            .iter()
            .zip_longest(other.coefficients.iter())
            .map(|a: itertools::EitherOrBoth<&Scalar, &Scalar>| match a {
                Both(l, r) => *l - *r,
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
    /// Polynomial Subtraction modulo m: a(X) - b(X)
    ///
    /// # Arguments
    ///
    /// * `self` - a `Polynomial` instance carrying the polynomial
    /// * `rhs` - a `Polynomial` instance carrying the other polynomial
    ///
    fn sub_assign(&mut self, rhs: &Polynomial) {
        let result = (self as &Polynomial) - rhs;
        *self = result;
    }
}
impl PartialEq for Polynomial {
    /// Checks if two polynomials are equal.
    fn eq(&self, other: &Polynomial) -> bool {
        if self.degree == other.degree {
            self.coefficients == other.coefficients
        } else {
            false
        }
    }
}

/// Computes the linear combination of polynomials for shuffle proofs.
///
/// Given L(X) polynomials, a matrix `a`, and witness vector `a_0`, this returns the combined polynomial expressions.
///
/// # Returns
///
/// A vector of `Polynomial` instances representing the expression.
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
/// Creates a Hadamard proof for the given matrices and witness.
///
/// # Arguments
///
/// * `a` - a `Array2D<Scalar>` instance carrying the matrix
/// * `b` - a `Array2D<Scalar>` instance carrying the matrix
/// * `c` - a `Array2D<Scalar>` instance carrying the matrix
/// * `witness_r` - a `Vec<Scalar>` instance carrying the witness
/// * `witness_s` - a `Vec<Scalar>` instance carrying the witness
/// * `witness_t` - a `Vec<Scalar>` instance carrying the witness
/// * `comit_a` - a `Vec<RistrettoPoint>` instance carrying the witness
/// * `comit_b` - a `Vec<RistrettoPoint>` instance carrying the witness
/// * `comit_c` - a `Vec<RistrettoPoint>` instance carrying the witness
/// * `xpc_gens` - a `VectorPedersenGens` instance carrying the vector pedersen generators
///
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

    //Evaluates (a.l(X) x b.l(X)) - cl(X))
    let a_b_c: Vec<_> = a_expression
        .iter()
        .zip(b_expression.iter())
        .zip(c_expression.iter())
        .map(|((a, b), c)| &a.multiply(b) - c)
        .collect();
    //println!("abc size {}", a_b_c.len());
    //Evaluates (a.l(X) x b.l(X)) - cl(X)) / l(X)
    let div_res: Vec<Polynomial> = a_b_c
        .into_iter()
        .map(|mut poly| poly.divide(&mut l_x_vec[0].clone(), poly.degree - l_x_vec[0].degree))
        .collect();
    div_res[0].print_polynomial();
    div_res[1].print_polynomial();
    div_res[2].print_polynomial();

    //extract delta_i from delta_i * X^i

    let mut delta_vec: Vec<Vec<Scalar>> = Vec::new();
    for i in 0..4 {
        let mut inner_vec: Vec<Scalar> = Vec::new();
        for j in 0..3 {
            inner_vec.push(div_res[j].coefficients[i]);
        }
        delta_vec.push(inner_vec);
    }

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
        let poly = create_1d_poly(Scalar::from(1u64), Scalar::from(3u64));
        poly.print_polynomial();
        //assert_eq!(reference, exp_2);
    }
    #[test]

    fn create_n_degree_polynomial_test() {
        let poly = create_n_degree_poly(Scalar::from(4u64), 7);
        poly.print_polynomial();
        //assert_eq!(reference, exp_2);
    }
    #[test]
    fn deg_adjust_polynomial_test() {
        let mut poly = create_n_degree_poly(Scalar::from(3u64), 2);
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
    // TODO: Add test for l_i_x_polynomial
    // TODO: Add test for create_l_i_x_polynomial
    // TODO: Need to figure out a Reference Polynomial vector
    // #[test]
    // fn l_i_x_polynomial_test() {
    //     let w: Vec<Scalar> = vec![
    //         Scalar::from(5u64),
    //         Scalar::from(1u64),
    //         Scalar::from(2u64),
    //         Scalar::from(3u64),
    //     ];
    //     let _poly = create_l_i_x_polynomial(&w);
    //     let reference = vec![
    //         Polynomial {
    //             coefficients: vec![Scalar::from(1u64), Scalar::from(1u64), Scalar::from(1u64)],
    //             degree: 2,
    //         },
    //         Polynomial {
    //             coefficients: vec![Scalar::from(1u64), Scalar::from(1u64), Scalar::from(1u64)],
    //             degree: 2,
    //         },

    //     ];
    //     assert_eq!(reference, _poly);
    // }
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
}
