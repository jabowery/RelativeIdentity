# UniversalityTheorem

### Identity, Equality, and Universality
A Condensation of the Works of Tom Etter
As Interpreted by colleague James Bowery


Abstract

This document synthesizes the theoretical framework of relative identity. It proceeds from the definition of the intrinsic “Quine Identity” within standard axiom systems to the generalization of identity as a three-place predicate (x regards y as z). It demonstrates that while standard equality is a logical dead-end, three-place identity is an open-ended system capable of expressing all of mathematics, including Zermelo-Fraenkel set theory.

See the docs for the paper UniversalityOfThreePlaceIdentity.pdf

This Lean 4 project proves the **Universality Theorem** for **Relative Identity**:


```lean
/-!
## 4. The Universality Theorem
-/
UniversalityTheorem.slang_universality_ZFC
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
git clone https://github.com/jabowery/RelativeIdentity.git
cd RelativeIdentity
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

The development is multi-module; `UniversalityTheorem.lean` is an aggregator that imports
the library modules.

| File | Purpose |
| :--- | :--- |
| `UniversalityTheorem.lean` | Aggregator: imports all library modules below. |
| `UniversalityTheorem/Universality.lean` | **Main body.** The Universality Theorem `slang_universality_ZFC` and the round-trip core (Etter, *Three-place Identity*). |
| `UniversalityTheorem/EtterEq.lean` | Relative-identity structures and Etter equality. |
| `UniversalityTheorem/Scaffold.lean` | Slang scaffolding layer (used by `Progress`). |
| `UniversalityTheorem/Progress.lean` | Sanity checks that key declarations are complete. |
| `UniversalityTheorem/Stereo.lean` | **Appendix A.** A kernel proof that the naive intersection candidate `¬(E1∧E2)` cannot be a ZF membership (`intersectionMem_not_ZF`) — motivating, not refuting, Etter's theorem; a faithful transcription of Etter's [E3 fn.5] link construction (`WeakEq`, `Meet`, `MemPrime`); and the two-equality result stated as a precise **conjecture** `etterStereoConjecture : Prop` (not a theorem, no `sorry`). |
| `UniversalityTheorem/Cell.lean` | **Appendix B.** Etter's cell construction over `ZFSet` (*The Expressive Power of Equality*): Theorems 1 & 2 (`first_iff`, `mem_iff`) — the corrected RCV→ZF membership. |
| `UniversalityTheorem/RCV.lean` | RCV-language interface over `Cell`: `Mem_RCV := cEd`, with definability and ZF-property theorems. |
| `lakefile.toml` | Lake build configuration (package name, dependencies, etc.). |
| `lean-toolchain` | Specifies the exact Lean 4 version to use. |
| `lake-manifest.json` | Auto-generated record of exact dependency versions (do not edit). |
| `README.md` | This file. |

## Status and corrections

The main body (Definitions D1/D2, Theorems 4.1–4.3, the round-trip, and the "universality"
claim) is correct and stands. The **appendix** constructions were corrected after checking
against Etter's primary sources:

- [`docs/Errata.pdf`](docs/Errata.pdf) (source `docs/Errata.tex`) — the corrections: the appendices' `¬(E1 ∧ E2)` / `¬(R ∧ C)`
  membership is *symmetric* and is **not** a ZF membership; Etter's actual RCV→ZF route is
  the cell construction of *The Expressive Power of Equality*, now mechanized in `Cell.lean`.
- [`ROADMAP.md`](ROADMAP.md) — the plan and status of the correction work, phase by phase.
- [`AGENTS.md`](AGENTS.md) — the proof discipline this repo follows (no load-bearing claim
  in natural language; every key result is `#print axioms`-audited).

The development is **`sorry`-free**. The two-equality "Stereo Equality Theorem" is *not* a
finished theorem in Etter's surviving papers — *Membership and Identity* develops the
machinery and breaks off before proving it — so rather than dress it up as a Lean `theorem`,
we transcribe Etter's [E3 fn.5] link construction faithfully and state the result as a
precise, falsifiable conjecture `Stereo.etterStereoConjecture : Prop`. It is the intended
subject of a future paper that proves it or refutes it in Lean.

The corrected paper exists in two forms that share the corrected appendices and differ
**only in the abstract**: `docs/UniversalityOfThreePlaceIdentity.pdf` keeps the original
tabular abstract, while `docs/vancouver.pdf` is the World Scientific / Festschrift submission,
whose abstract inlines the definitions as text because that venue disallows tables in the
abstract; it cites *The Expressive Power of Equality* as reference [9]. Because the corrected
paper folds the corrections in directly, submitting it makes the separate `docs/Errata.pdf`
followup unnecessary; the errata is retained for the case where the uncorrected version has
already been published.

## Common Lake Commands

* `lake update` — Update dependencies to latest compatible versions.
* `lake clean` — Remove build artifacts.
* `lake exe cache get` — Download pre-compiled cache for faster builds.
* `lake build UniversalityTheorem` — Build only the library.

## Troubleshooting

* **`lake: command not found`** → Restart your terminal or re-source your shell profile.
* **Dependency download failures** → Try `lake update` or check your internet connection.
* **Slow builds** → Normal on first run; subsequent builds are much faster.
* **VS Code shows errors after cloning** → Run `lake build` first, then restart VS Code.

## More documentation

* [Lean 4 Manual](https://leanprover.github.io/lean4/doc/)
* [Lake User Guide](https://github.com/leanprover/lake)

Enjoy exploring the proof!
