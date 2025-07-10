# Security Policy

## Supported Versions
| Version | Supported | Notes                                   |
| ------- | --------- | --------------------------------------- |
| 0.1.x   | ✅        | Critical and security patches provided  |
| < 0.1   | ❌        | No further security updates (EOL)       |

## Vulnerability Disclosure Process
To report a potential security vulnerability:
1. Navigate to the [**Security** tab](https://github.com/twilight-project/quisquis-rust/security) of this repository.
2. Click [**Report a vulnerability**](https://github.com/twilight-project/quisquis-rust/security/advisories/new) under _Security Advisories_.
3. Complete the form with:
   - **Type of vulnerability** (e.g., cryptographic weakness, side-channel)
   - **Location** (file path and line numbers)
   - **Steps to reproduce** and **proof of concept** if available
   - **Impact assessment** (what an attacker could achieve)
   - **Suggested fix** (optional)
   
**Timeline:**
- **Day 0**: Report received (via GitHub Security Advisories)
- **Within 48 hours**: Acknowledgment of receipt
- **Day 1–7**: Initial assessment and severity classification
- **Day 7–30**: Development and testing of a fix
- **Day 30–90**: Security release and coordinated public advisory

## Security Considerations & Threat Model
- **Attacker Goals:** privacy compromise, key extraction, denial-of-service  
- **Assumptions:**  
  - Honest-but-curious network participants  
  - Discrete logarithm hardness in Ristretto group  
  - Secure random number generation from system entropy  
  - Trusted compilation environment  

## Best Practices
- **Upgrade Quickly:** Always use the latest supported version (0.1.x).  
- **Secure RNG:** Use `OsRng` or equivalent for randomness.  
- **Constant-Time:** Prefer constant-time implementations; audit or avoid `unsafe` code.  
- **Zeroize Secrets:** Wipe key material from memory after use (`zeroize` crate).  
- **Dependency Audits:** Run `cargo audit` and `cargo deny` regularly.  
- **Undefined Behavior Checks:** Use tools like Miri (`cargo +nightly miri test`).  

## Cryptographic Dependencies
This project relies on:
- `curve25519-dalek` – Ristretto curve operations  
- `bulletproofs` – Zero-knowledge proof generators  
- `merlin` – Transcript and Fiat-Shamir support  
- `zkschnorr` – Schnorr signature schemes  

## Acknowledgments
We appreciate the contributions of security researchers and maintainers. Researchers who responsibly disclose vulnerabilities will be credited in our public advisories unless anonymity is requested.

_Last Updated: July 2025_  
_Next Review: January 2026_  