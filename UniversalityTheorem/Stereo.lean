import Mathlib.Logic.Relation
import Mathlib.Tactic

namespace UniversalityTheorem
namespace Stereo

universe u
variable {U : Type u}

/-!
## Appendix A: The Stereo Equality Theorem

As described in the paper, Stereo Equality consists of two independent
equivalence relations E1 and E2 on a domain U.
-/

/-- A Stereo Equality structure consisting of two independent equivalence relations. -/
structure StereoModel (U : Type u) where
  E1 : U → U → Prop
  E2 : U → U → Prop
  equiv1 : Equivalence E1
  equiv2 : Equivalence E2

/-!
### 1. Derived Membership
Definition from Appendix A.2:
y ∈' x iff ¬(E1(y, x) ∧ E2(y, x))
-/
def StereoMem (S : StereoModel U) (y x : U) : Prop :=
  ¬ (S.E1 y x ∧ S.E2 y x)

/-!
### 2. Proof of Irreflexivity
Theorem from Appendix A.2:
Derived membership is irreflexive (no set contains itself).
-/
theorem stereo_irreflexivity (S : StereoModel U) (x : U) :
    ¬ StereoMem S x x := by
  -- Unfold the definition: ¬ (¬ (E1 x x ∧ E2 x x))
  unfold StereoMem
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

end Stereo
end UniversalityTheorem