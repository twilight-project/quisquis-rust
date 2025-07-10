
# Contributing to Quisquis Rust

## Table of Contents
1. [Development Process](#development-process)
2. [Pull Requests](#pull-requests)
3. [Development Setup](#development-setup)
4. [Code Quality Checks](#code-quality-checks)
5. [Testing](#testing)
6. [Benchmarking](#benchmarking)
7. [Coding Standards](#coding-standards)
8. [Issue Reporting](#issue-reporting)
9. [Feature Requests](#feature-requests)
10. [Security Issues](#security-issues)
11. [Code Review Process](#code-review-process)
12. [Release Process](#release-process)
13. [Community Guidelines](#community-guidelines)
14. [License](#license)
15. [Additional Resources](#additional-resources)

We love your input! We want to make contributing to Quisquis Protocol as easy and transparent as possible, whether it's:

- Reporting a bug
- Discussing the current state of the code
- Submitting a fix
- Proposing new features
- Becoming a maintainer

## Development Process

We use GitHub to host code, to track issues and feature requests, as well as accept pull requests.

## Pull Requests

1. Fork the repo and create your branch from `develop`.
2. If you've added code that should be tested, add tests.
3. If you've changed APIs, update the documentation.
4. Ensure the test suite passes.
5. Make sure your code follows the existing style.
6. Submit your pull request against `develop`. Describe your changes and link any relevant issues.

## Development Setup

### Prerequisites

- Rust 1.70+ (2021 edition)
- Git
- A C compiler (for some dependencies)

### Local Development

```bash
# Clone your fork
git clone https://github.com/your-username/quisquis-rust.git
cd quisquis-rust

# Install development tools
cargo install cargo-audit cargo-deny cargo-outdated

# Build the project
cargo build

# Run tests
cargo test

# Run all checks (recommended before submitting)
make check-all  # or run individual commands below
```

### Code Quality Checks

We maintain high code quality standards. Please run these checks before submitting:

```bash
# Format code
cargo fmt

# Lint with Clippy
cargo clippy -- -D warnings

# Run security audit
cargo audit

# Check for vulnerabilities and license issues
cargo deny check

# Run all tests
cargo test --all-features

# Generate and check documentation
cargo doc --all-features --no-deps
```

### Testing

We use a comprehensive testing strategy:

```bash
# Unit tests
cargo test --lib

# Integration tests
cargo test --tests

# Documentation tests
cargo test --doc

# Run specific test
cargo test test_name

# Run tests with output
cargo test -- --nocapture
```

### Benchmarking

For performance-critical changes:

```bash
# Install criterion if not already installed
cargo install cargo-criterion

# Run benchmarks
cargo bench

# Compare with baseline
cargo bench -- --save-baseline main
cargo bench -- --baseline main
```

## Coding Standards

### Rust Style Guide

We follow the official Rust style guide:

- Use `cargo fmt` for formatting
- Follow Rust naming conventions
- Use meaningful variable and function names
- Add documentation for public APIs

### Code Organization

- Keep modules focused and cohesive
- Use clear, descriptive names for functions and types
- Group related functionality together
- Separate concerns appropriately

### Documentation

- Document all public APIs with `///` comments
- Include examples in documentation where helpful
- Update README.md for user-facing changes
- Add inline comments for complex algorithms

### Error Handling

- Use `Result<T, E>` for fallible operations
- Provide meaningful error messages
- Use custom error types where appropriate
- Document error conditions in function docs

### Security Considerations

This is a cryptographic library, so special care is required:

- **Constant-time operations**: Use constant-time implementations where timing attacks are a concern
- **Memory safety**: Avoid unsafe code unless absolutely necessary and well-justified
- **Randomness**: Use cryptographically secure random number generators (`OsRng`)
- **Key material**: Zeroize sensitive data when no longer needed
- **Side channels**: Be aware of potential side-channel attacks

### Performance Guidelines

- Profile before optimizing
- Prefer readability over premature optimization
- Use benchmarks to validate performance improvements
- Consider memory usage and allocation patterns

## Commit Messages

We use conventional commits for clear history:

```
<type>[optional scope]: <description>

[optional body]

[optional footer(s)]
```

Types:
- `feat`: New feature
- `fix`: Bug fix
- `docs`: Documentation changes
- `style`: Code style changes (formatting, etc.)
- `refactor`: Code refactoring
- `test`: Adding or updating tests
- `chore`: Maintenance tasks

Examples:
```
feat(accounts): add account update verification
fix(elgamal): resolve commitment verification issue
docs: update README with new examples
test(shuffle): add comprehensive shuffle protocol tests
```

## Issue Reporting

### Bug Reports

When filing an issue, make sure to answer these questions:

1. What version of Rust are you using?
2. What operating system and processor architecture are you using?
3. What did you do?
4. What did you expect to see?
5. What did you see instead?

### Feature Requests

We track feature requests as GitHub issues. When requesting a feature:

1. Explain the problem you're trying to solve
2. Describe the solution you'd like
3. Describe alternatives you've considered
4. Provide any additional context

## Security Issues

For vulnerability reports, please see [SECURITY.md](./SECURITY.md).

## Code Review Process

All submissions require review. We use GitHub pull requests for this purpose.

### Review Criteria

- **Correctness**: Does the code do what it's supposed to do?
- **Security**: Are there any security implications?
- **Performance**: Will this impact performance?
- **Maintainability**: Is the code easy to understand and maintain?
- **Testing**: Are there adequate tests?
- **Documentation**: Is the code properly documented?

### Review Timeline

- Initial review: Within 2-3 business days
- Follow-up reviews: Within 1-2 business days
- Final approval: After all concerns are addressed

## Release Process

We follow semantic versioning (SemVer):

- **MAJOR** version for incompatible API changes
- **MINOR** version for backwards-compatible functionality additions
- **PATCH** version for backwards-compatible bug fixes

### Release Checklist

- [ ] All tests pass
- [ ] Documentation is updated
- [ ] CHANGELOG.md is updated
- [ ] Version is bumped in Cargo.toml
- [ ] Security audit passes
- [ ] Performance benchmarks are acceptable

## Community Guidelines

### Code of Conduct

Please note that this project is released with a [Code of Conduct](CODE_OF_CONDUCT.md). By participating in this project, you agree to abide by its terms.

### Communication

- Be respectful and constructive
- Focus on the technical merits
- Assume good intentions
- Ask questions when unclear
- Provide helpful feedback

### Getting Help

- Check existing issues and documentation first
- Use clear, descriptive titles for new issues
- Provide minimal reproducible examples
- Include relevant version information

## Recognition

Contributors are recognized in several ways:

- Listed in the repository contributors
- Mentioned in release notes for significant contributions
- Invited to join the maintainer team for sustained contributions

## License

By contributing, you agree that your contributions will be licensed under both the MIT and Apache 2.0 licenses, matching the project's dual-license approach.

## Additional Resources

- [Rust Book](https://doc.rust-lang.org/book/)
- [Rust API Guidelines](https://rust-lang.github.io/api-guidelines/)
- [Rust Secure Code Guidelines](https://anssi-fr.github.io/rust-guide/)
- [Cryptographic Engineering Guidelines](https://cryptography.rs/)

Thank you for contributing to Quisquis Protocol! 