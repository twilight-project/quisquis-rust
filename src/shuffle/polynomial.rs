//Polynomial Field STARTS here
use array2d::Array2D;
use bulletproofs::PedersenGens;
use curve25519_dalek::traits::MultiscalarMul;

use crate::keys::PublicKey;
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
use std::ops::Sub;
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
    Polynomial {
        coefficients: coeffiecient,
        degree: 1,
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
            if *x == Scalar::zero() {
                continue;
            } else {
                print!("{:?} X^ {} + ", x, i);
            }
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
                println!("{:?}", i);
            }
        }
        self.degree = h_term;
        println!("{:?}", self.degree);
        let mut newcoeff = Vec::<Scalar>::with_capacity(h_term);
        for i in 0..=self.degree {
            newcoeff.push(self.coefficients[i]);
        }
        self.coefficients = newcoeff;
        self.print_polynomial();
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
    fn multiply(&self, other: &Self) -> Self {
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
    //Assumes that the polynomial is monic
    //Assumes that the polynomial a(X) has higher degree than b(X)
    //Assumes that both the polynomials have degree greater than 0
    //Evaluates (a(X) / b(X))
    //REMOVED: Also checks correctness of resulting polynomial for protocol
    pub fn polynomial_division(&mut self, other: &mut Self) -> Self {
        self.poly_deg_adjust();
        other.poly_deg_adjust();

        let degree = self.degree - other.degree;

        let mut result_coeff: Vec<Scalar> = vec![Scalar::from(0u64); degree + 1];

        // while (self.degree >= other.degree) {
        //     let poly_t = create_ND_poly(self.coefficients[self.degree], self.degree - other.degree);
        //     result_coeff[degree] = poly_t.coefficients[degree];
        //     degree = degree - 1;
        //     let poly_d = other * poly_t;
        //     other = &N - &d;
        //     self.poly_deg_adjust();
        // }
        Self {
            coefficients: result_coeff,
            degree: degree,
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
}
fn distinct(x: Scalar, a: &[Scalar]) -> bool {
    for i in 0..3 {
        if x == a[i] {
            return false;
        }
    }
    return true;
}
//Create "l(X)" and "li(X)" polynomials
fn create_l_x_polynomial(w:&[Scalar])-> Polynomial
{
    //Create l(X)
	let mut l = create_1D_poly(Scalar::from(1u64), -w[1]);
	for i in 2..w.len(){
		l = &l * &create_1D_poly(Scalar::from(1u64), -w[i]);
    }
	
	return l;
}
//Create "l(X)" and "li(X)" polynomials
fn create_l_i_x_polynomial(w:&[Scalar])-> Polynomial
{
    //Create li(X)
	for (int i = 1; i <= dim; i++)
	{
		int denom = 1; //Denominator
		poly_division(poly_copy(l[0]), create_1D_poly(1, -w[i]), l[i]);
		for (int j = 1; j <= dim; j++)
			if (i != j)	denom = denom * (w[i] - w[j]);
		denom = ((denom % m) + m) % m;
		int inv = mul_inv(m, denom);
		l[i] = poly_product(l[i], create_1D_poly(0, inv));
	}
}
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
}

// let c_degree = if self.degree >= other.degree{
//             self.degree;
//         }
//         else{
//             other.degree;
//         };
