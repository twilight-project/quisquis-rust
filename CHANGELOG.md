# Changelog

This changelog covers the major documentation and maintainability improvements. For future releases, please add entries for new features, bug fixes, and breaking changes. 

All *notable* changes to this project are recorded here.

## [Unreleased] – 0.1.0

- (future changes go here)

## [0.1.0] – 2025-07-15

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