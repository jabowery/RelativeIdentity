import Mathlib.Logic.Relation
import Mathlib.Tactic
import Mathlib.SetTheory.ZFC.Basic

namespace UniversalityTheorem
namespace Stereo

universe u
variable {U : Type u}

/-!
## Appendix A: Stereo equality, and why the naive intersection membership fails

A Stereo structure is two independent equivalence relations `E1`, `E2` on `U`.

**What this section does (see `docs/Errata.pdf`).** Before Etter's actual construction we
record why the simplest guess at a membership fails. The intersection candidate
`IntersectionMem y x := ¬(E1 y x ∧ E2 y x)` — the present author's reconstruction, which does
**not** occur in Etter's papers — is *symmetric* (`intersectionMem_symm`), and ZF membership
is not symmetric (`∅ ∈ {∅}` but `{∅} ∉ ∅`), so it cannot be a ZF membership
(`intersectionMem_not_ZF`). This refutes the **candidate formula**, not Etter's Stereo
Equality theorem; it is exactly what motivates the directed link construction
(`etterStereoConjecture`, below) and the asymmetric cell construction of `RCV.lean`.
-/

/-- A Stereo Equality structure consisting of two independent equivalence relations. -/
structure StereoModel (U : Type u) where
  E1 : U → U → Prop
  E2 : U → U → Prop
  equiv1 : Equivalence E1
  equiv2 : Equivalence E2

/-!
### 1. The naive intersection candidate (shown below to fail)
`y ∈' x  :⇔  ¬(E1 y x ∧ E2 y x)` — the intersection of the two equalities.
-/
def IntersectionMem (S : StereoModel U) (y x : U) : Prop :=
  ¬ (S.E1 y x ∧ S.E2 y x)

/-!
### Why the intersection candidate is not a ZF membership

Per `AGENTS.md` ("Red tests"): we do not rely on *failing* to prove the bad thing — we
*prove* it. The discriminating defect is symmetry; we prove it, then derive the resulting
contradiction with the existence of an empty set. This is a fact about the **candidate
formula** `IntersectionMem`; it says nothing against Etter's Stereo Equality theorem.
-/

/-- The intersection candidate is *symmetric*, because `E1` and `E2` are equivalence
relations — the property that disqualifies it as a membership. -/
theorem intersectionMem_symm (S : StereoModel U) (a b : U) :
    IntersectionMem S a b ↔ IntersectionMem S b a := by
  unfold IntersectionMem
  constructor <;> intro h hcon <;>
    exact h ⟨S.equiv1.symm hcon.1, S.equiv2.symm hcon.2⟩

/-- No **symmetric** relation can be a ZF membership: ZF proves `∅ ∈ {∅}` while `∅` is
empty, so symmetry would force `{∅} ∈ ∅`. Abstractly, a symmetric relation admits no
element that is simultaneously a member of something and itself empty. -/
theorem symm_mem_no_empty_member
    (Mem : U → U → Prop) (symm : ∀ x y, Mem x y → Mem y x)
    (a s : U) (mem_a_s : Mem a s) (a_empty : ∀ x, ¬ Mem x a) : False :=
  a_empty s (symm a s mem_a_s)

/-- Therefore the intersection candidate cannot be a ZF membership: an "empty" set that is
itself a member yields `False`, and ZF requires exactly that (`∅ ∈ {∅}` with `∅` empty).
A fact about the candidate formula, not about Etter's theorem. -/
theorem intersectionMem_not_ZF (S : StereoModel U)
    (a s : U) (mem_a_s : IntersectionMem S a s) (a_empty : ∀ x, ¬ IntersectionMem S x a) :
    False :=
  symm_mem_no_empty_member (IntersectionMem S)
    (fun x y h => (intersectionMem_symm S x y).mp h) a s mem_a_s a_empty

/-!
### 2. Proof of Irreflexivity
Theorem from Appendix A.2:
Derived membership is irreflexive (no set contains itself).
-/
theorem stereo_irreflexivity (S : StereoModel U) (x : U) :
    ¬ IntersectionMem S x x := by
  -- Unfold the definition: ¬ (¬ (E1 x x ∧ E2 x x))
  unfold IntersectionMem
  -- Intuitionistic proof: To prove ¬¬P, assume ¬P and derive False.
  intro h_not_mem
  -- We know E1 x x and E2 x x are true by reflexivity.
  have h1 : S.E1 x x := S.equiv1.refl x
  have h2 : S.E2 x x := S.equiv2.refl x
  -- h_not_mem states that (E1 x x ∧ E2 x x) is false.
  -- But we have h1 and h2, so it is true. Contradiction.
  apply h_not_mem
  exact ⟨h1, h2⟩

/-!
## Appendix A.3: Encoding Ordered Pairs

The paper states that an ordered pair ⟨x, y⟩ can be encoded by a 'link' object q.
The defining condition is E1(q, x) ∧ (∃ q', E1(q, q') ∧ E2(q', y)).
-/

/--
The predicate `IsLink S q x y` determines if object `q` serves as a link
between `x` and `y` in the Stereo structure `S`.
-/
def IsLink (S : StereoModel U) (q x y : U) : Prop :=
  S.E1 q x ∧ ∃ q', S.E1 q q' ∧ S.E2 q' y

/-!
### 3. Connection Proof
We prove that if a "perfect link" exists (an object `q` that is E1-equivalent to `x`
and E2-equivalent to `y`), it satisfies the IsLink definition.
-/
theorem perfect_link_is_link (S : StereoModel U) (q x y : U) :
    S.E1 q x → S.E2 q y → IsLink S q x y := by
  intro h1 h2
  unfold IsLink
  constructor
  -- 1. E1(q, x) holds by assumption
  · exact h1
  -- 2. We need ∃ q', E1(q, q') ∧ E2(q', y). We choose q' = q.
  · use q
    constructor
    · apply S.equiv1.refl -- E1(q, q) is true by reflexivity
    · exact h2            -- E2(q, y) holds by assumption

/-!
### 4. Uniqueness of the First Component
We prove that `q` uniquely determines `x` up to E1-equivalence.
If `q` links `x` and `y`, and also links `x'` and `y'`, then `x` is E1-equivalent to `x'`.
-/
theorem link_determines_x (S : StereoModel U) (q x x' y y' : U) :
    IsLink S q x y → IsLink S q x' y' → S.E1 x x' := by
  intro h1 h2
  -- Extract E1(q, x) and E1(q, x') from the IsLink hypotheses
  have hqx : S.E1 q x := h1.1
  have hqx' : S.E1 q x' := h2.1
  -- Use symmetry and transitivity of E1 to show x ~ x'
  -- x ~ q (symm) and q ~ x' (direct) implies x ~ x'
  apply S.equiv1.trans (S.equiv1.symm hqx) hqx'

/-!
## The Stereo Equality "Theorem" — an unfinished Etter conjecture, stated for future work

**Status (checked against the primary sources; see `docs/Errata.pdf` Erratum 3).** The
**three**-equality RCV→ZF result is complete and proved (`RCV.mem_RCV_definable`, via
`Cell`). The **two**-equality "Stereo Equality Theorem" is *not* a theorem in Etter's
surviving papers. *Three-place Identity* [E3, §3] states it informally and says the proof is
"in Section 3 of *Membership and Identity* [E2]" — but the surviving M&I draft develops the
machinery (intrinsic identity, *division*, *Other*) and then **breaks off** before stating
or proving it (M&I p. 17 is a bare unproved theorem; §4 is a stub; R. Shoup notes the paper
was never completed). So there is no finished Etter statement to transcribe.

The only concrete construction Etter gives is the **link sketch of [E3, fn. 5]**, transcribed
faithfully below as `def`initions and assembled into a precise, falsifiable **conjecture**
(`etterStereoConjecture : Prop`). It is deliberately **not** a Lean `theorem` and carries no
`sorry`: it is a stated proposition — the intended subject of a future paper that proves
`etterStereoConjecture` or `¬ etterStereoConjecture` in Lean.

Two earlier stand-ins here — the symmetric intersection candidate `¬(E1 ∧ E2)` (refuted
above as `intersectionMem_not_ZF`) and an automorphism-invariance structure — were both
*inventions*, not Etter's, and are removed in favour of the fn-5 link construction.

### Etter's [E3, fn. 5] construction

* `[x=y]` is **equality without transitivity** — reflexive and symmetric only (`WeakEq`).
* `[x =: y, z, …]` means "x equals y and z …, and anything unequal to y is unequal to x,
  ditto z, …": x lies at the *meet* of their neighbourhoods (`WeakEq.Meet`).
* `x ∈' y` is the existential link formula (`WeakEq.MemPrime`).
* Etter's claim: "there is a set model of `[x=y]` such that `x∈'y` is membership in a set
  model of set theory."

**Fidelity caveats (`AGENTS.md` "No-oracle claims") — mine, none kernel-checkable:**
(i) [E3, fn. 5]'s *symbolic* rendering of `=:` has transcription typos; we follow its
unambiguous *prose* ("anything unequal to y is unequal to x"). (ii) fn. 5 uses a *single*
non-transitive equality, which Etter says is "at the heart of" the stereo (two-equality)
theorem; we formalize the fn-5 construction, not the never-pinned-down "two equalities"
slogan. (iii) "membership in a set model of set theory" is rendered as: a surjection onto
`ZFSet` under which `∈'` matches genuine ZF membership. The conjecture's *content* is
Etter's; this precise Lean *rendering* is a reconstruction by Claude Opus 4.8.
-/

/-- Etter's `[x=y]` ([E3, fn. 5]): an equality with **transitivity dropped** — reflexive
and symmetric only. Deliberately *not* an `Equivalence`. -/
structure WeakEq (U : Type u) where
  eq : U → U → Prop
  refl : ∀ x, eq x x
  symm : ∀ {x y}, eq x y → eq y x

namespace WeakEq

/-- Etter's meet operator `[x =: ys]`: `x` equals each member of `ys`, and anything unequal
to any member of `ys` is unequal to `x` (so `x`'s neighbourhood lies under each of theirs). -/
def Meet (W : WeakEq U) (x : U) (ys : List U) : Prop :=
  (∀ y ∈ ys, W.eq x y) ∧ (∀ y ∈ ys, ∀ w, ¬ W.eq w y → ¬ W.eq w x)

/-- Etter's link membership `x ∈' y` from [E3, fn. 5]:
`∃ x' x'' y' y'' q q' q''` with
`[q =: x,q'] ∧ [q' =: y,q,q''] ∧ [x' =: x,x''] ∧ [x'' =: x,x'] ∧ [y' =: y,y''] ∧ [y'' =: y,y']`. -/
def MemPrime (W : WeakEq U) (x y : U) : Prop :=
  ∃ x' x'' y' y'' q q' q'' : U,
    W.Meet q [x, q'] ∧ W.Meet q' [y, q, q''] ∧
    W.Meet x' [x, x''] ∧ W.Meet x'' [x, x'] ∧
    W.Meet y' [y, y''] ∧ W.Meet y'' [y, y']

end WeakEq

/-- **Etter's Stereo Equality Conjecture** — a reconstruction of [E3, fn. 5]; see the section
note for status and fidelity caveats. There is a carrier `U` with a non-transitive equality
`W`, and a surjection `val : U → ZFSet` under which Etter's link membership `MemPrime` is
*exactly* ZF membership of values — i.e. `∈'` is "membership in a set model of set theory".

This is a stated `Prop`, **not** a proved theorem and **not** a `sorry`. Intended future
work: a Lean proof of `etterStereoConjecture`, or of its negation. -/
def etterStereoConjecture : Prop :=
  ∃ (U : Type 1) (W : WeakEq U) (val : U → ZFSet.{0}),
    Function.Surjective val ∧ ∀ x y : U, W.MemPrime x y ↔ val x ∈ val y

end Stereo
end UniversalityTheorem
