+# Quisquis Protocol v0.1.0 Testnet Release Notes
+
+Released: 2025-07-15
+
+This initial public release of **quisquis-rust** is for research and testnet experimentation only. It contains known cryptographic vulnerabilities inherited from upstream crates and must not be used with real funds.
+
+## Highlights
+
+- Privacy-preserving accounts with ElGamal commitments and encrypted balance updates
+- Ristretto group key operations (Curve25519)
+- Range proofs via Bulletproofs for confidential balances
+- Cryptographic shuffle protocols for transaction anonymity
+- Example binaries and extensive API documentation
+
+See the [CHANGELOG](CHANGELOG.md) for a full list of additions.
+
+## Security Status
+
+- **Testnet-only** build with timing-leak issues in `curve25519-dalek v3.2.1` and `ed25519-dalek v1.0.1`
+- Fixes are scheduled for **v0.2.0**; see [SECURITY.md](.github/SECURITY.md) for details
+- Do **not** use this release in production or to protect real value
+
+## Getting Started
+
+1. Clone the repository and build from source:
+   ```bash
+   git clone https://github.com/twilight-project/quisquis-rust.git
+   cd quisquis-rust
+   cargo build --release
+   ```
+2. Explore the example binaries and API documentation to test the protocol on a local testnet.
+
+Feedback and contributions are welcome! Please review the [CONTRIBUTING guide](.github/CONTRIBUTING.md) for development tips and the release checklist.
