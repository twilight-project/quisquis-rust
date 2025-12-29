# Changelog

All notable changes to this project will be documented in this file.

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.0.0/),
and this project adheres to [Semantic Versioning](https://semver.org/spec/v2.0.0.html).

## [Unreleased]
- No pending changes.

## [0.1.1] – 2025-12-29
### Maintenance
- Adjusted dependency specification to improve long-term stability:
  - Replaced `bincode = "*"` with `bincode = "1"` to restrict upgrades to compatible 1.x releases.
- No public API or behavioral changes are included in this release.
- Security posture unchanged; this remains an **experimental testnet release**.

---
## [0.1.0] – 2025-07-15

### Security Warning ⚠️

- This is an **experimental testnet release** and is **not safe for production use**.
- It contains known timing-leak vulnerabilities inherited from upstream crates. Please see the [Security Policy](.github/SECURITY.md) for full details before using this software.

### Added

- Privacy-preserving accounts with ElGamal commitments and encrypted balance updates.
- Ristretto group cryptography (Curve25519) for secure key generation and serialization.
- Homomorphic Pedersen commitments for vector operations.
- Transaction structures and Schnorr signature logic for confidential transfers.
- Range proofs using Bulletproofs for confidential balance verification.
- Advanced cryptographic shuffle protocols (shuffle, DDH, Hadamard, multi-exponential, product arguments) for transaction anonymity.
- Utility modules for address handling, vector/matrix operations, and integration helpers.
- Inline binaries demonstrating example workflows (key generation, account creation, proofs).
- Full rustdoc coverage across all public APIs (accounts, Ristretto, ElGamal, Pedersen, transaction, shuffle).
- Inline maintainer comments in example binaries.

### Changed
- (none for initial release)

### Fixed

- **Linter Warnings**
  - All public items now have documentation, resolving previous linter warnings about missing doc comments.

---
<!-- No compare link: initial release -->
