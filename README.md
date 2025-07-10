# Quisquis Protocol

[![Crates.io](https://img.shields.io/crates/v/quisquis-rust.svg)](https://crates.io/crates/quisquis-rust)
[![docs.rs](https://docs.rs/quisquis-rust/badge.svg)](https://docs.rs/quisquis-rust)
[![CI](https://github.com/twilight-project/quisquis-rust/workflows/CI/badge.svg)](https://github.com/twilight-project/quisquis-rust/actions)
[![License: MIT](https://img.shields.io/badge/License-MIT-yellow.svg)](https://opensource.org/licenses/MIT)
[![License: Apache 2.0](https://img.shields.io/badge/License-Apache%202.0-blue.svg)](https://opensource.org/licenses/Apache-2.0)

_A Rust library for privacy-preserving cryptocurrency accounts and transactions._

A Rust implementation of Quisquis, a privacy-preserving cryptocurrency protocol that enables anonymous transactions through advanced cryptographic techniques including ElGamal commitments, zero-knowledge proofs, and updatable accounts.

## Features

- **Privacy-Preserving Accounts**: Cryptographically secure accounts with encrypted balances using ElGamal commitments
- **Account Updates**: Update account keys and balances while maintaining privacy guarantees
- **Zero-Knowledge Proofs**: Integration with bulletproofs and Schnorr signatures for transaction privacy
- **Ristretto Group Operations**: Built on the secure Ristretto group over Curve25519
- **Shuffle Protocols**: Advanced cryptographic shuffling for enhanced anonymity
- **Pedersen Commitments**: Homomorphic commitments for balance privacy

## Table of Contents

- [Installation](#installation)
- [Quick Start](#quick-start)
- [Usage](#usage)
- [Examples](#examples)
- [API Documentation](#api-documentation)
- [Security](#security)
- [Contributing](#contributing)
- [License](#license)

## Installation

Add to your project:

```bash
cargo add quisquislib
```

### Building from Source

```bash
git clone https://github.com/twilight-project/quisquis-rust.git
cd quisquis-rust
cargo build --release
```

## Quick Start

```rust, ignore
use quisquislib::*;
use curve25519_dalek::scalar::Scalar;
use rand::rngs::OsRng;

// Generate a new account
let mut rng = OsRng;
let secret_key = RistrettoSecretKey::random(&mut rng);
let public_key = RistrettoPublicKey::from_secret_key(&secret_key, &mut rng);

// Create an account with zero balance
let (account, commitment_scalar) = Account::generate_account(public_key);
println!("Generated account: {:?}", account);

// Update account with a new balance
let update_scalar = Scalar::random(&mut rng);
let commitment_scalar = Scalar::random(&mut rng);
let balance = Scalar::from(100u64); // 100 units

let updated_account = Account::update_account(
    account,
    balance,
    update_scalar,
    commitment_scalar
);
```

## Usage

### Core Components

#### Accounts
Accounts are the fundamental unit in Quisquis, consisting of a public key and an ElGamal commitment to the balance:

```rust, ignore
use quisquislib::accounts::Account;

// Verify an account
account.verify_account(&secret_key, balance)?;

// Decrypt account balance (requires secret key)
let decrypted_balance = account.decrypt_account_balance_value(&secret_key)?;
```

#### ElGamal Commitments
ElGamal commitments provide homomorphic encryption for account balances:

```rust, ignore
use quisquislib::elgamal::ElGamalCommitment;

let commitment = ElGamalCommitment::generate_commitment(
    &public_key,
    &random_scalar,
    &balance
);

// Commitments can be added homomorphically
let sum_commitment = ElGamalCommitment::add_commitments(&comm1, &comm2);
```

#### Key Management
Ristretto-based key operations for enhanced security:

```rust, ignore 
use quisquislib::ristretto::{RistrettoPublicKey, RistrettoSecretKey};

// Generate keypair
let secret_key = RistrettoSecretKey::random(&mut rng);
let public_key = RistrettoPublicKey::from_secret_key(&secret_key, &mut rng);

// Update public key
let update_scalar = Scalar::random(&mut rng);
let updated_key = RistrettoPublicKey::update_public_key(&public_key, update_scalar);
```

### Privacy Features

#### Account Updates
Update accounts while preserving unlinkability:

```rust, ignore 
// Create delta and epsilon accounts for privacy
let (delta_accounts, epsilon_accounts, r_scalars) = 
    Account::create_delta_and_epsilon_accounts(
        &accounts,
        &balances,
        base_public_key
    );
```

#### Shuffle Protocols
Use cryptographic shuffles for enhanced anonymity:

```rust, ignore
use quisquislib::shuffle::*;
// Shuffle operations for mixing transactions
```

<!-- ## Examples

See the [`examples/`](examples/) directory for complete examples:


Run examples with:
```bash
cargo run --example 
```
-->
## API Documentation

Generate and view the full API documentation:

```bash
cargo doc --open
```


## Security

⚠️ Experimental research software — do not use in production without review.  
See [SECURITY.md](.github/SECURITY.md) for full policy.


## Roadmap

- [ ] Transaction implementation with full privacy guarantees
- [ ] Network protocol for transaction broadcasting
- [ ] Performance optimizations and SIMD support
- [ ] Formal security audit
- [ ] Mobile-friendly builds (WASM)

## Contributing

We welcome contributions! Please see [CONTRIBUTING.md](.github/CONTRIBUTING.md).

### Development Setup

```bash
# Clone the repository
git clone https://github.com/twilight-project/quisquis-rust.git
cd quisquis-rust

# Install development dependencies
cargo install cargo-audit cargo-deny

# Run tests
cargo test

# Run security audit
cargo audit

# Check formatting
cargo fmt --check

# Run clippy
cargo clippy -- -D warnings
```

## Acknowledgments

This implementation is based on the Quisquis research paper and related cryptographic work. Special thanks to:

- The Quisquis research team
- The Rust cryptography community

## License

Licensed under either of

- Apache License, Version 2.0, ([LICENSE-APACHE](LICENSE-APACHE) or <http://www.apache.org/licenses/LICENSE-2.0>)
- MIT license ([LICENSE-MIT](LICENSE-MIT) or <http://opensource.org/licenses/MIT>)

at your option.

### Contribution

Unless you explicitly state otherwise, any contribution intentionally submitted for inclusion in the work by you, as defined in the Apache-2.0 license, shall be dual licensed as above, without any additional terms or conditions.
