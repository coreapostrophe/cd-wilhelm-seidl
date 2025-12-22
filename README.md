# Rust Template

A production-ready Rust workspace template with CI/CD and development container support.

## Quick Start

1. Click "Use this template" on GitHub
2. Clone and build:
   ```bash
   git clone https://github.com/yourusername/your-repo-name.git
   cd your-repo-name
   cargo build
   cargo test
   ```

**Prerequisites:** Rust 1.90.0 or later

## Project Structure

```
rust-template/
├── .devcontainer/          # VS Code devcontainer
├── .github/workflows/      # CI/CD pipeline
├── crates/                 # Workspace crates
│   └── foundations/        # Example crate
├── Cargo.toml              # Workspace configuration
└── README.md
```

## Development

```bash
# Build
cargo build

# Test
cargo test

# Format
cargo fmt

# Lint
cargo clippy --all-targets --all-features

# Add new crate
cargo new --lib crates/your-crate-name
```

## Dev Container

Open in VS Code and click "Reopen in Container" for a pre-configured Rust development environment.

## CI/CD

GitHub Actions automatically runs tests, formatting, linting, and security audits on push/PR to `main` and `develop`.

---

Happy coding! 🦀