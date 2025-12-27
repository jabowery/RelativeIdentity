# UniversalityTheorem

### Identity, Equality, and Universality
A Condensation of the Works of Tom Etter
Based on the writings of Tom Etter

Abstract

This document synthesizes the theoretical framework of relative identity. It proceeds from the definition of the intrinsic “Quine Identity” within standard axiom systems to the generalization of identity as a three-place predicate (x regards y as z). It demonstrates that while standard equality is a logical dead-end, three-place identity is an open-ended system capable of expressing all of mathematics, including Zermelo-Fraenkel set theory.

See the docs for the paper UniversalityOfThreePlaceIdentity.tex

This Lean 4 project proves the **Universality Theorem** for **Relative Identity**:


```lean
/-!
## 4. The Universality Theorem
-/
UniversalityTheorem.Universality.theorem slang_universality_ZFC
```

## Quick Start (for users unfamiliar with Lean 4)

### 1. Install Lean 4
Install Lean 4 via the Elan toolchain manager, which provides `lake`.

**On Linux/macOS:**
```bash
curl [https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh](https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh) -sSf | sh
source ~/.profile  # or restart your terminal / source the appropriate file
```

**On Windows:**
Download and run the PowerShell script from the [official guide](https://leanprover-community.github.io/get_started.html).

*Full installation instructions: [Lean 4 Quickstart](https://leanprover.github.io/lean4/doc/quickstart.html).*

The `lean-toolchain` file in this repository pins the exact Lean version—Elan will download it automatically.

### 2. Clone the repository

```bash
git clone <your-repo-url-here>
cd UniversalityTheorem
```

### 3. Build the project

```bash
lake build
```

* **Success** means the theorem is fully proved (all files type-check with no `sorry`s).
* The first build may take several minutes as it downloads dependencies and compiles them.
* Build artifacts go into `.lake/` (ignored by Git).

### 4. Verify interactively (recommended)

1.  Install **VS Code** and the **Lean 4 extension**.
2.  Open the repository folder in VS Code.
3.  Navigate to `UniversalityTheorem.lean`—the infoview will show proof status.

## Project Structure

| File | Purpose |
| :--- | :--- |
| `UniversalityTheorem.lean` | Main source file containing the theorem statement and proof. |
| `lakefile.toml` | Lake build configuration (package name, dependencies, etc.). |
| `lean-toolchain` | Specifies the exact Lean 4 version to use. |
| `lake-manifest.json` | Auto-generated record of exact dependency versions (do not edit). |
| `README.md` | This file. |

## Common Lake Commands

* `lake update` — Update dependencies to latest compatible versions.
* `lake clean` — Remove build artifacts.
* `lake exe cache get` — (If using Mathlib) Download pre-compiled cache for faster builds.
* `lake build UniversalityTheorem` — Build only the library.

## Troubleshooting

* **`lake: command not found`** → Restart your terminal or re-source your shell profile.
* **Dependency download failures** → Try `lake update` or check your internet connection.
* **Slow builds** → Normal on first run; subsequent builds are much faster.
* **VS Code shows errors after cloning** → Run `lake build` first, then restart VS Code.

## More documentation

* [Lean 4 Manual](https://leanprover.github.io/lean4/doc/)
* [Lake User Guide](https://github.com/leanprover/lake)
* [Mathlib (if used)](https://leanprover-community.github.io/mathlib4_docs/)

Enjoy exploring the proof!
