# AGENTS.md — Lean 4 proof discipline

The theorem statement is the specification; the kernel is the only test runner.
Anything that matters lives in a goal the kernel must discharge — never in a
comment, a name, or a `def`.

## The one rule
No load-bearing claim may exist in natural language. If a property matters,
state it as `theorem`/`example` and let `lake build` force a proof. Comments,
docstrings, and identifier names are untested commentary — proposals, never
facts. Choosing *which* proposition to state is the author's job; it is the only
part the kernel cannot do, and the only place failures hide.

## Workflow
1. **Spec first.** Before the construction, write the goal that captures the
   actual claim, e.g. `example : IsZFModel (myMem M) := by sorry`. It may be
   unfinished; it may not be unstated.
2. **Discriminating test.** Identify the property that separates a correct
   construction from a broken one, and prove the side you claim (see Red tests).
3. **Build to green.** Implement only until the kernel discharges the spec.
4. **Audit.** `#print axioms <result>` on every key theorem. `sorryAx` or a
   stray axiom means the test was vacuous.
5. Re-read every comment and name as hostile: if it asserts more than the
   adjacent goal proves, cut it or downgrade it.

## pytest ↔ Lean 4
| pytest | Lean 4 |
|---|---|
| `def test_*: assert P` | `example : P := by …` |
| `assert f x == v` | `#guard f x == v`  /  `example : f x = v := by decide` |
| `pytest.raises` / stdout snapshot | `#guard_msgs in <cmd>` |
| Hypothesis (property-based) | `slim_check` / `Plausible` |
| `pytest` runner | `lake build` (elaboration *is* the run); `lake test` |
| catching `assert True` / stubs | `#print axioms` |
| `tests/` directory | `test/` of `.lean` files, built, outside the lib |

## Red tests
"Fails to compile" is **not** evidence — an unclosable goal may just be beyond
your tactics. Every check ends in a *compiling* proof:
- Confirm a suspected defect → prove the forbidden property:
  `example : badProp := …` closing ⇒ broken.
- Assure correctness → prove the discriminating property the defect would
  violate: `example : extensionality myMem := …`.
Never rely on *failing* to prove the bad thing; prove the good thing, or prove
the bad thing and accept the refutation.

Worked instance: a membership defined `¬(E1 y x ∧ E2 y x)` is provably symmetric
(because `E1`, `E2` are), and symmetric membership contradicts extensionality —
so `example : myMem a b ↔ myMem b a := …` closing is the red test that ends the
matter. Write that test, not just the green `irreflexivity` lemma.

## Execution honesty
You have a shell — use it. Never report a build, a passing proof, or a closed
goal you did not run. Paste the `lake build` / `lake env lean` invocation and its
output. "Compiles," asserted without the run, is itself a confabulation.

## No-oracle claims
Some claims have no kernel check: "this statement faithfully formalizes that
informal theorem," "these names match the source paper." There is no green to
reach. State them explicitly as load-bearing-and-unverified, cite the primary
source, and do not build further work on them as settled.

## Done
- [ ] The real claim is a stated goal that closes without `sorry`.
- [ ] The discriminating property is proven on the side you claim.
- [ ] `#print axioms` is clean on every key result.
- [ ] No comment or name asserts more than its goal proves.
- [ ] Every reported compile was actually run, with output shown.
