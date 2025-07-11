# Security Policy

## ⚠ Pre‑release security status (v0.1.x‑testnet)

This is an **experimental test‑net build**.  
- Includes known timing‑leak issues in **curve25519‑dalek v3.2.1** (RUSTSEC‑2024‑0344) and **ed25519‑dalek v1.0.1** (RUSTSEC‑2022‑0093).  
- Safe only for development / research use — **do not protect real value with this release.**  
- Fixes are scheduled for **v0.2.0** (see Roadmap).  

## Supported Versions
| Version | Supported | Notes                                   |
| ------- | --------- | --------------------------------------- |
| 0.1.x   | ⚠️ (testnet) | Known vulnerabilities; security fixes scheduled for v0.1.x‑patch & v0.2.0 |
| < 0.1   | ❌        | No further security updates (EOL)       |

## Vulnerability Disclosure

Please report security issues privately via the GitHub [“Report a vulnerability” form](https://github.com/twilight-project/quisquis-rust/security/advisories/new).  
**Response timetable**

- **Day 0:** Report received  
- **≤ 48 h:** Acknowledgement  
- **Day 1–7:** Triage & severity classification  
- **Day 7–30:** Fix development & testing  
- **Day 30–90:** Coordinated release & public advisory

## Security Considerations & Threat Model
- **Attacker Goals:** privacy compromise, key extraction, denial-of-service  
- **Assumptions:**  
  - Honest-but-curious network participants  
  - Discrete logarithm hardness in Ristretto group  
  - Secure random number generation from system entropy  
  - Trusted compilation environment  

## Best Practices
- **Use the latest 0.1.x release**  
- **Use secure RNG (`OsRng`)**  
- **Prefer constant‑time implementations; audit or avoid `unsafe`**  
- **Zeroize secrets (`zeroize` crate)**  
- **Run `cargo audit` & `cargo deny` regularly**  
- **Check UB with `cargo +nightly miri test`**

## Cryptographic Dependencies
This project currently depends on:

- `curve25519-dalek` **3.2.1** – Ristretto curve operations  
- `bulletproofs` **4.x** – Zero‑knowledge proof generators  
- `merlin` **1.4.x** – Transcript and Fiat‑Shamir support  
- `zkschnorr` **0.1.x** – Schnorr signature schemes  

---

### Known Vulnerabilities (last update: July 2025)

This build ships with two acknowledged upstream RustSec advisories.

| Crate | Advisory | Risk | Planned fix |
|-------|----------|------|-------------|
| curve25519-dalek 3.2.1 | RUSTSEC-2024-0344 (timing leak) | Low–Med | Upgrade to ≥ 4.2.0 in v0.2.0 |
| ed25519-dalek 1.0.1 | RUSTSEC-2022-0093 (oracle attack) | Med | Upgrade to ≥ 2.2.0 in v0.2.0 |

`zkschnorr` inherits the curve25519‑dalek issue and will be patched alongside.

*No formal audit has been performed. Do not use this software with real value.*

## Roadmap

| Milestone                    | Target date      | Action |
|------------------------------|------------------|--------|
| **v0.1.x‑testnet (current)** | July 2025        | Publish known‑issue build; test‑net only |
| **v0.1.x‑patch** | Aug 2025  | Back‑port constant‑time mitigations; add CI `cargo audit` gating |
| **v0.2.0** | Oct 2025 | Upgrade to fixed cryptographic crates; add sanitiser & fuzzing; begin external audit |
| **v1.0.0** | 1H 2026 | Production‑ready release after full audit |

## Acknowledgments
We appreciate the contributions of security researchers and maintainers. Researchers who responsibly disclose vulnerabilities will be credited in our public advisories unless anonymity is requested.

_Last Updated: July 2025_  
_Next Review: August 2025_ 