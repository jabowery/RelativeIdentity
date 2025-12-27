/-
File: UniversalityTheorem/Scaffold.lean

Purpose:
  "Middle layer" that *only* depends on EtterEq.
  This is where we formalize:
    Slang (raw) → Slang identity → Slang equality
  without accidentally reverting to Lean's (=) or collapsing namespaces.

Policy:
  - Do not open/alias Lean equality as the intended object-language equality.
  - When you mean equality in the model, say `M.eq`.
  - When you mean membership in the model, say `M.mem`.
-/
import UniversalityTheorem.EtterEq

namespace UniversalityTheorem
namespace Scaffold

open EtterEq

universe u
variable {U : Type u}

/-- A "Slang model" is just: an underlying domain together with a 3-place identity. -/
structure SlangModel (U : Type u) where
  RI : EtterEq.RelativeIdentity U

/-- Slang-derived membership: y ∈' x := ¬ x(y=x) -/
def mem' (S : SlangModel U) : U → U → Prop :=
  EtterEq.MemFromId S.RI

/-
Etter’s intended pipeline (as you’ve described it):

  Slang (RI) ──defines──▶ mem'
  mem' (with enough axioms) ──yields──▶ “ZF-ish” / “ZFC-ish” structure
  then: identity ⟹ equality (this is the later ‘Equality Derivation Problem’)

For now, we *only* build the parts that are legitimately “equality-representation”
and keep the later identity→equality derivation explicitly pending.
-/

/-- If we *already* have a ZFCModel in EtterEq, we can view its RI as a SlangModel. -/
def slangOfZFC (M : EtterEq.ZFCModel U) : SlangModel U :=
  ⟨EtterEq.RelativeIdentity_from_ZFCModel M⟩

/--
Sanity check: the `mem'` computed from the SlangModel coming from `M`
agrees with the `Mem'_from_ZFCModel` already defined in EtterEq.
-/
theorem mem'_agrees (M : EtterEq.ZFCModel U) :
    mem' (slangOfZFC (U := U) M) = EtterEq.Mem'_from_ZFCModel (U := U) M := by
  rfl

/-
This is the key separation point:

- EtterEq provides:
    (a) M.mem, M.eq   (primitive, “two layers removed”)
    (b) RI-from-mem, mem'-from-RI, and the ZFC preservation theorem about mem'

- Scaffold should provide:
    SlangModel, mem', and the *statements* that the final Universality proof will need.

What Scaffold must *not* do yet:
    Derive M.eq from RI (identity). That’s the next file’s job.
-/

/-- “Universality, staged”: from a ZFC model we get ZFC axioms for the derived mem'. -/
theorem slang_universality_ZFC (M : EtterEq.ZFCModel U) :
    let m' := mem' (slangOfZFC (U := U) M)
    EtterEq.ZF_Extensionality m' M.eq ∧
    EtterEq.ZF_Congruence    m' M.eq ∧
    EtterEq.ZF_Foundation    m' ∧
    EtterEq.ZF_EmptySet      m' ∧
    EtterEq.ZF_Pairing       m' M.eq ∧
    EtterEq.ZF_Union         m' ∧
    EtterEq.ZF_PowerSet      m' ∧
    EtterEq.ZF_Separation    m' ∧
    EtterEq.ZF_Infinity      m' M.eq ∧
    EtterEq.ZF_Replacement   m' M.eq ∧
    EtterEq.ZF_Choice        m' M.eq ∧
    (∀ y x, m' y x ↔ M.mem y x) := by
  -- This is *supposed* to be just a thin wrapper around EtterEq’s theorem.
  -- If this ever breaks, it indicates “regression” in the layering.
  simpa [mem', slangOfZFC] using (EtterEq.universality_theorem_ZFC (U := U) M)


end Scaffold
end UniversalityTheorem
