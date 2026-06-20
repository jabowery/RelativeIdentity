# ROADMAP — Correcting the RelativeIdentity codebase

Status: **draft**. Authority for the math: Etter's primary sources. Authority for the
proof discipline: [`AGENTS.md`](AGENTS.md). Authority for *what is currently wrong*:
[`docs/Errata.pdf`](docs/Errata.pdf) (source `docs/Errata.tex`).

This document plans the work to bring the Lean development and the repository into
alignment with (a) Etter's actual constructions and (b) the AGENTS.md rule that *no
load-bearing claim may live in natural language*. It is the plan, not the proof; every
claim it sketches becomes real only when a kernel goal closes.

---

## 0. The problem in one paragraph

The appendix modules `Stereo.lean` and `RCV.lean` formalize a membership the present
author *reconstructed* — `y ∈′ x :⇔ ¬(E1 y x ∧ E2 y x)` — which does **not** occur in
Etter's papers and is provably **symmetric** (intersection of two equivalence relations),
hence cannot be a ZF membership (Extensionality fails). The modules then prove only
disconnected, true-but-vacuous fragments (irreflexivity, a definitional link lemma,
partial uniqueness), never state the symmetry that refutes the construction, never relate
the membership and link predicates, and never establish any ZF axiom. Meanwhile Etter's
*correct* RCV→ZF result — the **cell construction** of *The Expressive Power of Equality*
[E1] — is fully proved in the source and is simply absent from the code. Separately, the
repo's `UniversalityTheorem.lean` imports `RCV.lean`, which is **untracked**, so a fresh
clone does not build, and `docs/` is full of untracked build artifacts.

The net effect (per the Errata) *raises* the standing of the program: the three-equality
result is complete and correct in [E1] and just needs to be cited and mechanized faithfully.

---

## 1. Source-of-truth map

| Claim | Governing source | Current code status | Target |
|---|---|---|---|
| Quine identity / 3-place identity / D1, D2, Thm 4.1–4.3, round-trip §5 | *Three-place Identity* [E3] | **Correct, keep** (`Universality.lean`, `EtterEq.lean`) | unchanged |
| "Universality" = expressive adequacy / relative interpretability | Etter's open-system notion [E3] | **Correct, keep** | unchanged |
| RCV → ZF (three equalities) | **The Expressive Power of Equality [E1]** — cell construction | **Wrong** (`RCV.lean`: symmetric intersection, V unused, wrong citation) | rebuild on cells |
| Stereo / two-equality theorem (Appendix A) | *Membership and Identity* [E2] (unfinished draft); link sketch [E3 fn.5] | **Wrong + overclaimed** (`Stereo.lean`) | refute old, mark genuinely-incomplete honestly |

Primary sources on disk: `docs/EtterPapers/Expressive_Equality.pdf` [E1],
`MembershipAndIdentity.pdf` [E2], `Three-place_Identity.pdf` [E3],
`Notes on Identity and Pairing.odt` [E4], `Equality and Quine IDs s1-6.odt` [E5].

---

## 2. Etter's correct construction (the spec to mechanize), from [E1]

A **cell** is an ordered triple `⟨x, y, n⟩` with `x ε y` and `n ∈ {1, 2}`.
`Val(⟨x,y,n⟩) = x if n=1 else y`. Three equalities **on cells**:

- `R(c=c')` — same row: `x=x' ∧ y=y'`
- `C(c=c')` — same column: `n=n'`
- `V(c=c')` — same value: `Val(c)=Val(d)`

with `R ∧ C ∧ V ⇒ c = c'` (RCV conjunction is cell identity), and `V` taken as the
identity. Membership is recovered from R, C, V **alone**:

- **Theorem 1:** `First(c) ⇔ ∀d ∃e (V(e=d) ∧ C(e=c))`  (column-1 ⇔ "hits every value")
- **Theorem 2:** `cEd ⇔ ∃e,f (R(e=f) ∧ First(e) ∧ V(c=e) ∧ ¬First(f) ∧ V(d=f))`

The argument-asymmetry that makes membership non-symmetric is carried entirely by
`First(e) ∧ ¬First(f)` — exactly what the old intersection formula lacks. The result is
**relative consistency / interpretability**: assuming the ZF axioms for `cEd`+`V` does not
contradict the nine equality axioms, because under `Val` the abstract axioms become
theorems of ZF. The mechanization must state *that*, not an absolute "this is a ZF model."

---

## 3. Phases

### Phase 0 — Repository hygiene (prerequisite; no math)  ✓ DONE

Goal: a fresh clone builds, and the repo tracks only required files.

0.1 **Add `.gitignore`** (proposed contents in §4) covering Lean build output, LaTeX
    intermediates, editor swap files, and office lock files.

0.2 **Fix the broken import graph.** `RCV.lean` is imported by `UniversalityTheorem.lean`
    but untracked → `git add` it (after Phase 1–2 rewrite, so we do not commit the wrong
    version as "the" RCV module; until then the aggregator must not depend on a file the
    repo lacks). Decide per 0.3 whether it is tracked as-is, rewritten, or quarantined.

0.3 **Triage stray Lean files** (untracked today): `Basic.lean`, `StereoEquality.lean`,
    `UniversalityCore_AssumingEq.lean`, `Scaffold.lean` (tracked but **not** imported by
    the aggregator). For each: promote to a tracked, imported module; or delete. No
    orphan files, no tracked-but-unbuilt files. Remove `.Progress.lean.swp`.

0.4 **Establish a green baseline.** Run `lake build`, paste the invocation and output
    (AGENTS.md "Execution honesty"). Record which modules currently close and which carry
    `sorry`. This is the line we must not regress below.

0.5 **Decide tracked binaries.** Keep distributed PDFs (`Errata.pdf`, the EtterPapers
    sources, `UniversalityOfThreePlaceIdentity.pdf`); confirm `.tex` sources are tracked
    so PDFs are reproducible; let `.gitignore` drop the rest.

Exit: `git status` clean except intended changes; `lake build` reproduces the recorded
baseline from a clean checkout.

### Phase 1 — Refute the incorrect construction (the missing red test)  ✓ DONE

> Implemented in `Stereo.lean`: `intersectionMem_symm` (the symmetry red test),
> `symm_mem_no_empty_member`, and `intersectionMem_not_ZF` — all axiom-free
> (`#print axioms` reports no dependence). False ZF claims downgraded in `Stereo.lean` and
> `RCV.lean`. `lake build` green.

Per AGENTS.md "Red tests": prove the *bad* property and accept the refutation, rather than
relying on the absence of a proof.

1.1 State and prove
    `example : IntersectionMem S a b ↔ IntersectionMem S b a` — the symmetry the Errata says was never
    stated. Closing this is the discriminating red test.

1.2 State that symmetric membership contradicts Extensionality (e.g. construct a two-point
    model where the symmetric relation forces `a ∈ b ∧ b ∈ a` with `a ≠ b`, or derive the
    contradiction abstractly). This is the kernel-checked version of Erratum 1.

1.3 Downgrade or delete every comment/name in `Stereo.lean`/`RCV.lean` that asserts "ZF
    set theory," "satisfies the axioms of ZF," or cites the wrong source. Names and
    comments are proposals, not facts (AGENTS.md "the one rule").

Exit: the symmetry/extensionality refutation closes with clean `#print axioms`; no
surviving NL claim that the intersection membership is a ZF membership.

### Phase 2 — Implement Etter's cell construction [E1]  ✓ DONE

> Implemented in new module `Cell.lean` over Mathlib's `ZFSet` (genuine ZF membership):
> `Cell`, `Val`, `R`/`C`/`V` (+ `equiv_*`), `cell_identity`/`rcv_identity`, `First`, `Mem`,
> and Etter's **Theorem 1** (`first_iff`) and **Theorem 2** (`mem_iff`) as discharged `↔`s.
> Imported by the aggregator. `#print axioms` on every result: only `[propext]`
> (+ `Quot.sound` for `first_iff`, inherent to `ZFSet`) — no `sorryAx`, no `Classical.choice`.
> Column index `n ∈ {1,2}` modeled as `col : Bool` (documented modeling choice).

2.1 `Cell` type and `Val` (over an ambient ZF-like carrier with `ε` and equality).
2.2 `R`, `C`, `V` as equalities on cells; prove each is an `Equivalence`.
2.3 Prove `R ∧ C ∧ V ⇒ c = c'` (cell identity).
2.4 `First` and **Theorem 1** as a proven `↔`.
2.5 Cell membership `cEd := Val c ε Val d`; **Theorem 2** as a proven `↔` against the
    `First`/`¬First` RCV formula.

Exit: Theorems 1 and 2 close as stated `↔`s; `#print axioms` clean.

### Phase 3 — State and discharge the real claim (spec-first)  ✓ DONE

> `Cell.lean` gained `val_surjective` (the `Val` homomorphism is onto), `mem_iff_zf`
> (`cEd` *is* ZF membership, definitionally), and the asymmetry green test
> (`mem_irreflexive`, `mem_asymmetric`, and the concrete witness `mem_not_symmetric`:
> `∅ ∈ {∅}` but `{∅} ∉ ∅`). `RCV.lean` was rewritten: the abstract `RCVModel`/symmetric
> `¬(R ∧ C)` formula and the `toStereo` projection are gone; `Mem_RCV := Cell.Mem` (cEd,
> using all three of R, C, V), with `mem_RCV_definable`/`first_RCV_definable` (Etter's
> Theorems 2/1) and `mem_RCV_irreflexive`/`mem_RCV_asymmetric`. The meta-claim
> *Con(ZF) ⇒ Con(RCV)* is documented as the interpretation's soundness (not a kernel goal).
> Whole project builds warning-free; `#print axioms` only `[propext]` (+ `Quot.sound`).

3.1 Write the top-level goal *before* finishing the plumbing (AGENTS.md "Spec first"):
    the `cEd ⇔ Val c ε Val d` correspondence and the relative-interpretability statement
    — assuming ZF for `ε` lets us assume ZF for `cEd`+`V` without contradicting the nine
    equality axioms.
3.2 Add the discriminating **green** test the old code lacked: exhibit a model where
    `cEd` is **not** symmetric (witnessing that the asymmetry is real), the positive
    counterpart to Phase 1's refutation.
3.3 Replace `Mem_RCV`'s body and the `toStereo` projection: `V` must be *used*; the
    membership must be `cEd`, not the intersection.

Exit: the correspondence/interpretability goal closes without `sorry`; the asymmetry
witness closes; `#print axioms` clean on every key result.

### Phase 4 — The two-equality Stereo theorem (honest incompleteness)  ✓ DONE

> **Revised after reading the primary sources.** The two-equality "Stereo Equality Theorem"
> is *not* finished in Etter's papers: *Three-place Identity* [E3 §3] states it informally and
> defers the proof to *Membership and Identity* [E2 §3], but the surviving M&I draft breaks off
> before reaching it (p. 17 is a bare unproved theorem; §4 is a stub). So `Stereo.lean` does
> **not** assert a theorem. It transcribes Etter's [E3 fn.5] link construction faithfully —
> `WeakEq` (equality without transitivity), `Meet` (the `=:` operator), `MemPrime` (the link
> membership `∈'`) — and states the result as a precise `def etterStereoConjecture : Prop`
> (a surjection onto `ZFSet` under which `MemPrime` is genuine ZF membership). It is **not** a
> `theorem` and carries **no** `sorry`; it is the intended subject of a future paper proving
> `etterStereoConjecture` or `¬ etterStereoConjecture`. An earlier invented automorphism-
> invariance statement was removed. `stereo_irreflexivity` and the intersection-candidate lemmas kept. The project
> is now `sorry`-free; the conjecture is a clean `Prop` (`[propext]`).

Per Erratum 3, this is the *only* genuinely incomplete item.

4.1 Keep `stereo_irreflexivity` (valid for Definition A.2; the definition, not the
    derivation, was at issue).
4.2 State the two-equality claim as an explicit `theorem … := by sorry` **or** as a
    clearly labeled load-bearing-and-unverified `axiom`/conjecture, citing [E2] and the
    link sketch in [E3 fn.5] (AGENTS.md "No-oracle claims"). Do not present it as proved.
4.3 If the [E3 fn.5] link construction can be completed, do so; otherwise it remains the
    one acknowledged open goal, visible in `#print axioms`.

Exit: no `sorry` is silent; the incomplete item is a single, labeled, cited goal.

### Phase 5 — Documentation & paper alignment  ✓ DONE

> `README.md`: rewrote the Project Structure table (now the real multi-module layout),
> fixed the stale headline-theorem name, and added a "Status and corrections" section
> cross-linking `Errata.pdf`, `ROADMAP.md`, `AGENTS.md`. `UniversalityOfThreePlaceIdentity.tex`:
> added the missing `etter_power` bibitem (*The Expressive Power of Equality* [E1]); marked
> the Appendix A two-equality theorem as the open item; flagged the symmetric `¬(E1∧E2)` /
> `¬(R∧C)` formulas as the refuted reconstruction and replaced the "project onto Stereo"
> passage with Etter's cell construction (Theorems 1 & 2), citing [E1]. Paper recompiles
> clean under lualatex (`scripts/buildpaper.sh`), no errors / undefined refs; PDF regenerated.

5.1 Rewrite `README.md` "Project Structure" (currently claims a single main file; the
    project is multi-module) and the abstract's appendix description. Also fix the stale
    headline-theorem reference: README cites
    `UniversalityTheorem.Universality.slang_universality_ZFC`, but the real fully-qualified
    name is `UniversalityTheorem.slang_universality_ZFC` (audited clean: depends only on
    `propext, Quot.sound`).
5.2 Appendix B of the paper cites **[E1]** and uses the cell construction; Appendix A is
    marked as the two-equality open item. Fold the Errata's corrections into the source
    `.tex`.
5.3 Cross-link `ROADMAP.md`, `AGENTS.md`, `docs/Errata.pdf` from the README.

5.4 **Two-document split (post-review).** The corrected paper and the errata are now
    separate artifacts: `docs/UniversalityOfThreePlaceIdentity.tex` is a *clean* corrected
    paper (no errata language; appendices present the cell construction and the stereo
    conjecture directly) suitable to replace the Festschrift submission; `docs/Errata.tex`
    (→ `docs/Errata.pdf`) is a standalone errata paper referencing the uncorrected
    published version, for separate later publication. The source-less root `Errata.pdf`
    was removed in favour of `docs/Errata.{tex,pdf}`.

Exit: README structure table matches `git ls-files`; no doc asserts the withdrawn claims.

### Phase 6 — Audit & CI  ✓ DONE

> `docs/AxiomAudit.md` archives `#print axioms` for all key results (generated by
> `scripts/audit.sh`): the project is `sorry`-free — every result is `[propext]`
> (+ `Quot.sound`), and `etterStereoConjecture` is a clean `Prop`. CI
> (`.github/workflows/lean_action_ci.yml`) now runs `scripts/verify_tracked.sh` (every
> imported module is git-tracked → clone builds), `leanprover/lean-action` (`lake build` on
> the committed tree), and `scripts/audit_check.sh` (fails on **any** `sorryAx`). The
> correction work is committed on branch
> `correct-appendices-cell-construction`; `Cell.lean` and the rewritten `RCV.lean` are now
> tracked, closing the Phase 0 clone-build blocker.

6.1 `#print axioms` on every key theorem; `sorryAx` or stray axiom ⇒ the test was vacuous.
6.2 Add/repair `.github` CI to run `lake build` on a clean checkout (catches the
    "imported but untracked" class of bug permanently).

Exit: CI green from a clean clone; axiom report archived.

---

## 4. Proposed `.gitignore`

The repo today tracks only `/.lake`, leaving LaTeX artifacts, swap files, and office lock
files untracked-and-noisy. Proposed replacement (keeps `.tex`/`.pdf`/`.odt`/`.lean`
sources; drops generated noise):

```gitignore
# Lean / Lake build output
/.lake/
/build/

# Editor swap & backup files
*.swp
*.swo
*~
.*.swp
.*.swo

# LibreOffice / OpenOffice lock files
.~lock.*#

# LaTeX build intermediates (keep .tex sources and final .pdf)
*.aux
*.log
*.out
*.toc
*.lof
*.lot
*.fls
*.fdb_latexmk
*.synctex.gz
*.bbl
*.blg
*.bcf
*.run.xml
*.nav
*.snm
*.vrb
*.idx
*.ilg
*.ind
texput.log
```

Notes:
- No `.log`/`.aux`/etc. files are currently tracked, so this cleans `git status` without
  needing `git rm --cached`. Verify with `git status` after adding.
- PDFs are intentionally **not** ignored — distributed outputs
  (`Errata.pdf`, `UniversalityOfThreePlaceIdentity.pdf`, EtterPapers) stay tracked.
- If any tracked `.tex` needs a companion generated file checked in, whitelist it
  explicitly with a `!` rule.

---

## 5. File disposition (current → target)

| File | Now | Action |
|---|---|---|
| `UniversalityTheorem/Universality.lean` | tracked, correct | keep |
| `UniversalityTheorem/EtterEq.lean` | tracked, correct | keep |
| `UniversalityTheorem/Progress.lean` | tracked | review; keep if it carries real goals |
| `UniversalityTheorem/Stereo.lean` | tracked, **wrong** | refute (Phase 1), then host two-equality open item (Phase 4) |
| `UniversalityTheorem/RCV.lean` | **untracked**, **wrong** | rewrite on cells (Phase 2–3), then track |
| `UniversalityTheorem/Scaffold.lean` | tracked, imported by `Progress.lean:17` | keep (was mis-flagged as orphan in earlier draft) |
| `UniversalityTheorem/Basic.lean` | untracked | triage: promote or delete |
| `UniversalityTheorem/StereoEquality.lean` | untracked | triage: promote or delete |
| `UniversalityTheorem/UniversalityCore_AssumingEq.lean` | untracked | triage: promote or delete |
| `UniversalityTheorem/.Progress.lean.swp` | untracked | delete (and gitignore) |
| `docs/**` artifacts, `texput.log` | untracked noise | gitignore |
| `Errata.pdf`, EtterPapers PDFs, `.tex` sources | untracked | track the sources/outputs we distribute |

---

## 6. Acceptance checklist (mirrors AGENTS.md "Done")

- [x] Fresh clone of the branch builds with `lake build` (RCV/Cell now tracked, verified by
      `scripts/verify_tracked.sh`; CI runs `lake build` on the committed tree).
- [x] The real RCV→ZF claim (Theorems 1 & 2 + correspondence/interpretability) is a stated
      goal that closes without `sorry` (`Cell.mem_iff`, `Cell.first_iff`, `Cell.mem_iff_zf`,
      `Cell.val_surjective`).
- [x] The discriminating property is proven on the side claimed: symmetry refutation for the
      old formula (`Stereo.intersectionMem_not_ZF`) **and** an asymmetry witness for the cell `cEd`
      (`Cell.mem_not_symmetric`/`mem_asymmetric`).
- [x] The project is `sorry`-free. The two-equality Stereo result is not a proved theorem but
      a stated, falsifiable conjecture `Stereo.etterStereoConjecture : Prop`, faithfully
      transcribing Etter's [E3 fn.5] link construction (Etter's own statement is unfinished).
- [x] `#print axioms` clean on every key result; report archived (`docs/AxiomAudit.md`).
- [x] No comment or name asserts more than its goal proves; no "satisfies the axioms of ZF"
      survives on the intersection formula (Phases 1 & 3 cleanups).
- [x] README structure table matches `git ls-files`; appendices cite [E1] (new `etter_power`
      bibitem).

---

## References

- [E1] Etter, *The Expressive Power of Equality*, Boundary Institute, 2001 — cell construction; proof of the RCV→ZF expressiveness theorem.
- [E2] Etter, *Membership and Identity*, Boundary Institute, 2006 — incomplete draft (two-equality theorem).
- [E3] Etter, *Three-place Identity*, Boundary Institute, 2006 — D1/D2, Thm 4.1–4.3; link sketch, fn. 5.
- [E4] Etter, *Notes on Identity and Pairing*, Boundary Institute, 2001.
- [E5] Etter, *Equalities and Quine Identities §§1–6*, Boundary Institute, 2001.
