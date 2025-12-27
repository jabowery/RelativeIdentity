/-
This namespace provides a representation of equality and membership
for ZF/ZFC models used in the Universality Theorem project.

All equality symbols here are model-internal and must not be confused
with Lean's built-in equality.
-/
import Mathlib.Data.Set.Basic
import Mathlib.Logic.Relation
import Mathlib.Order.WellFounded

/-!
# Universality Core (EtterEq)

This module implements Etter's Universality Theorem assuming a pre-existing
ZF Model with a disciplined, model-internal equality predicate `eq`.

## Namespace: EtterEq
All definitions are scoped to `EtterEq` to explicitly distinguish this
abstracted version from the final, fully reduced theory.

Usage:
  import UniversalityTheorem.EtterEq
  -- Access via: EtterEq.ZFCModel, EtterEq.universality_theorem_ZFC
-/

namespace EtterEq

universe u

-- ============================================================================
-- PART 1: Logic & Equality Primitives
-- ============================================================================

variable {U : Type u}

/--
Custom uniqueness quantifier.
Replaces Lean's `∃!`. Uniqueness is defined relative to the model's `eq`.
-/
def ExistsUnique_eq (P : U → Prop) (eq : U → U → Prop) : Prop :=
  ∃ x, P x ∧ ∀ y, P y → eq y x

-- ============================================================================
-- PART 2: The Purged ZFC Axioms
-- ============================================================================

/-- Extensionality: Sets with same members are `eq` -/
def ZF_Extensionality (mem : U → U → Prop) (eq : U → U → Prop) : Prop :=
  ∀ s t : U, (∀ x : U, mem x s ↔ mem x t) → eq s t

/-- Congruence: `eq` behaves like equality for membership -/
def ZF_Congruence (mem : U → U → Prop) (eq : U → U → Prop) : Prop :=
  ∀ x x' y y', eq x x' → eq y y' → (mem x y ↔ mem x' y')

/-- Foundation: Purely relational -/
def ZF_Foundation (mem : U → U → Prop) : Prop :=
  WellFounded (fun x y => mem x y)

/-- Pairing: Defined using `eq` -/
def ZF_Pairing (mem : U → U → Prop) (eq : U → U → Prop) : Prop :=
  ∀ x y : U, ∃ p : U, ∀ z : U, mem z p ↔ (eq z x ∨ eq z y)

/-- Union: Purely relational -/
def ZF_Union (mem : U → U → Prop) : Prop :=
  ∀ s : U, ∃ u : U, ∀ x : U, mem x u ↔ ∃ t : U, mem t s ∧ mem x t

/-- Power Set: Purely relational -/
def ZF_PowerSet (mem : U → U → Prop) : Prop :=
  ∀ s : U, ∃ p : U, ∀ t : U, mem t p ↔ (∀ x : U, mem x t → mem x s)

/-- Separation: Purely relational -/
def ZF_Separation (mem : U → U → Prop) : Prop :=
  ∀ (P : U → Prop) (s : U), ∃ t : U, ∀ x : U, mem x t ↔ (mem x s ∧ P x)

/-- Empty Set: Purely relational -/
def ZF_EmptySet (mem : U → U → Prop) : Prop :=
  ∃ e : U, ∀ x : U, ¬ mem x e

/-- Infinity: Defined using `eq` for the successor condition -/
def ZF_Infinity (mem : U → U → Prop) (eq : U → U → Prop) : Prop :=
  ∃ inf : U,
    (∃ e : U, (∀ x : U, ¬ mem x e) ∧ mem e inf) ∧
    (∀ x : U, mem x inf → ∃ sx : U,
      (∀ z : U, mem z sx ↔ (eq z x ∨ mem z x)) ∧ mem sx inf)

/-- Replacement: Uses `ExistsUnique_eq` -/
def ZF_Replacement (mem : U → U → Prop) (eq : U → U → Prop) : Prop :=
  ∀ (F : U → U → Prop) (s : U),
    (∀ x : U, mem x s → ExistsUnique_eq (F x) eq) →
    ∃ t : U, ∀ y : U, mem y t ↔ ∃ x : U, mem x s ∧ F x y

/-- Choice: Uses `eq` for disjointness and uniqueness -/
def ZF_Choice (mem : U → U → Prop) (eq : U → U → Prop) : Prop :=
  ∀ s : U,
    (∀ x : U, mem x s → ∃ y : U, mem y x) → -- non-empty members
    (∀ x y : U, mem x s → mem y s → ¬ eq x y →
      ¬∃ z : U, mem z x ∧ mem z y) → -- pairwise disjoint (using ¬ eq)
    ∃ c : U, ∀ x : U, mem x s →
      ExistsUnique_eq (fun y => mem y x ∧ mem y c) eq -- unique selection

-- ============================================================================
-- PART 3: The ZFC Model Structure
-- ============================================================================

structure ZFCModel (U : Type u) where
  mem : U → U → Prop
  eq : U → U → Prop
  -- Logical Properties
  eq_equiv : Equivalence eq
  congruence : ZF_Congruence mem eq
  extensionality : ZF_Extensionality mem eq
  -- Axioms
  foundation : ZF_Foundation mem
  empty_set : ZF_EmptySet mem
  pairing : ZF_Pairing mem eq
  union : ZF_Union mem
  power_set : ZF_PowerSet mem
  separation : ZF_Separation mem
  infinity : ZF_Infinity mem eq
  replacement : ZF_Replacement mem eq
  choice : ZF_Choice mem eq

-- ============================================================================
-- PART 4: Relative Identity Definitions
-- ============================================================================

structure RelativeIdentity (U : Type u) where
  Id : U → U → U → Prop
  refl : ∀ x y : U, Id x y y
  symm : ∀ x y z : U, Id x y z → Id x z y
  trans : ∀ x y z w : U, Id x y z → Id x z w → Id x y w

def MemFromId {U : Type u} (RI : RelativeIdentity U) (y x : U) : Prop :=
  ¬ RI.Id x y x

def IdFromMem {U : Type u} (mem : U → U → Prop) (x y z : U) : Prop :=
  (mem y x ∧ mem z x) ∨ (¬ mem y x ∧ ¬ mem z x)

def IdFromMem_is_RelativeIdentity {U : Type u} (mem : U → U → Prop) :
    RelativeIdentity U where
  Id := IdFromMem mem
  refl := fun x y => by
    unfold IdFromMem
    by_cases h : mem y x
    · exact Or.inl ⟨h, h⟩
    · exact Or.inr ⟨h, h⟩
  symm := fun x y z h => by
    unfold IdFromMem at h ⊢
    cases h with
    | inl hyz => exact Or.inl ⟨hyz.2, hyz.1⟩
    | inr hyz => exact Or.inr ⟨hyz.2, hyz.1⟩
  trans := fun x y z w hyz hzw => by
    unfold IdFromMem at hyz hzw ⊢
    cases hyz with
    | inl hyz =>
      cases hzw with
      | inl hzw => exact Or.inl ⟨hyz.1, hzw.2⟩
      | inr hzw => exact False.elim (hzw.1 hyz.2)
    | inr hyz =>
      cases hzw with
      | inl hzw => exact False.elim (hyz.2 hzw.1)
      | inr hzw => exact Or.inr ⟨hyz.1, hzw.2⟩

-- ============================================================================
-- PART 5: The Round-Trip Proofs
-- ============================================================================

theorem Foundation_implies_no_self_mem (mem : U → U → Prop) (h : ZF_Foundation mem) :
    ∀ x : U, ¬ mem x x := by
  intro x hxx
  have : Acc (fun a b => mem a b) x := h.apply x
  induction this with
  | intro x _ ih =>
    exact ih x hxx hxx

def RelativeIdentity_from_ZFCModel (M : ZFCModel U) : RelativeIdentity U :=
  IdFromMem_is_RelativeIdentity M.mem

def Mem'_from_ZFCModel (M : ZFCModel U) (y x : U) : Prop :=
  MemFromId (RelativeIdentity_from_ZFCModel M) y x

theorem ZFCModel_roundtrip (M : ZFCModel U) (y x : U) :
    Mem'_from_ZFCModel M y x ↔ M.mem y x := by
  unfold Mem'_from_ZFCModel MemFromId RelativeIdentity_from_ZFCModel
  unfold IdFromMem_is_RelativeIdentity IdFromMem
  simp only
  have nxx : ¬ M.mem x x := Foundation_implies_no_self_mem M.mem M.foundation x
  tauto

-- ============================================================================
-- PART 6: Axiom Preservation
-- ============================================================================

theorem Extensionality_preserved (M : ZFCModel U) :
    ZF_Extensionality (Mem'_from_ZFCModel M) M.eq := by
  intro s t h
  apply M.extensionality
  intro x
  -- Switch derived membership to original membership
  rw [←ZFCModel_roundtrip M x s]
  rw [←ZFCModel_roundtrip M x t]
  exact h x

theorem Congruence_preserved (M : ZFCModel U) :
    ZF_Congruence (Mem'_from_ZFCModel M) M.eq := by
  intro x x' y y' hx hy
  rw [ZFCModel_roundtrip, ZFCModel_roundtrip]
  exact M.congruence x x' y y' hx hy

theorem Foundation_preserved (M : ZFCModel U) :
    ZF_Foundation (Mem'_from_ZFCModel M) := by
  unfold ZF_Foundation
  have h : ∀ x y, Mem'_from_ZFCModel M x y ↔ M.mem x y := ZFCModel_roundtrip M
  constructor
  intro a
  have hacc : Acc (fun x y => M.mem x y) a := M.foundation.apply a
  induction hacc with
  | intro x _ ih =>
    apply Acc.intro
    intro y hy
    rw [h] at hy
    exact ih y hy

theorem EmptySet_preserved (M : ZFCModel U) :
    ZF_EmptySet (Mem'_from_ZFCModel M) := by
  obtain ⟨e, he⟩ := M.empty_set
  use e
  intro x
  rw [ZFCModel_roundtrip]
  exact he x

theorem Pairing_preserved (M : ZFCModel U) :
    ZF_Pairing (Mem'_from_ZFCModel M) M.eq := by
  intro x y
  obtain ⟨p, hp⟩ := M.pairing x y
  use p
  intro z
  rw [ZFCModel_roundtrip]
  exact hp z

theorem Union_preserved (M : ZFCModel U) :
    ZF_Union (Mem'_from_ZFCModel M) := by
  intro s
  obtain ⟨u, hu⟩ := M.union s
  use u
  intro x
  rw [ZFCModel_roundtrip]
  constructor
  · intro h
    obtain ⟨t, ht1, ht2⟩ := (hu x).mp h
    exact ⟨t, (ZFCModel_roundtrip M t s).mpr ht1, (ZFCModel_roundtrip M x t).mpr ht2⟩
  · intro ⟨t, ht1, ht2⟩
    apply (hu x).mpr
    exact ⟨t, (ZFCModel_roundtrip M t s).mp ht1, (ZFCModel_roundtrip M x t).mp ht2⟩

theorem PowerSet_preserved (M : ZFCModel U) :
    ZF_PowerSet (Mem'_from_ZFCModel M) := by
  intro s
  obtain ⟨p, hp⟩ := M.power_set s
  use p
  intro t
  rw [ZFCModel_roundtrip]
  constructor
  · intro h x hx
    rw [ZFCModel_roundtrip] at hx ⊢
    exact (hp t).mp h x hx
  · intro h
    apply (hp t).mpr
    intro x hx
    rw [← ZFCModel_roundtrip]
    exact h x ((ZFCModel_roundtrip M x t).mpr hx)

theorem Separation_preserved (M : ZFCModel U) :
    ZF_Separation (Mem'_from_ZFCModel M) := by
  intro P s
  obtain ⟨t, ht⟩ := M.separation P s
  use t
  intro x
  rw [ZFCModel_roundtrip]
  constructor
  · intro h
    obtain ⟨h1, h2⟩ := (ht x).mp h
    exact ⟨(ZFCModel_roundtrip M x s).mpr h1, h2⟩
  · intro ⟨h1, h2⟩
    apply (ht x).mpr
    exact ⟨(ZFCModel_roundtrip M x s).mp h1, h2⟩

theorem Infinity_preserved (M : ZFCModel U) :
    ZF_Infinity (Mem'_from_ZFCModel M) M.eq := by
  obtain ⟨inf, ⟨e, he1, he2⟩, hinf⟩ := M.infinity
  use inf
  constructor
  · use e
    constructor
    · intro x; rw [ZFCModel_roundtrip]; exact he1 x
    · rw [ZFCModel_roundtrip]; exact he2
  · intro x hx
    rw [ZFCModel_roundtrip] at hx
    obtain ⟨sx, hsx1, hsx2⟩ := hinf x hx
    use sx
    constructor
    · intro z
      simp only [ZFCModel_roundtrip]
      exact hsx1 z
    · rw [ZFCModel_roundtrip]
      exact hsx2

theorem Replacement_preserved (M : ZFCModel U) :
    ZF_Replacement (Mem'_from_ZFCModel M) M.eq := by
  intro F s hF
  have hF' : ∀ x : U, M.mem x s → ExistsUnique_eq (F x) M.eq := by
    intro x hx
    exact hF x ((ZFCModel_roundtrip M x s).mpr hx)
  obtain ⟨t, ht⟩ := M.replacement F s hF'
  use t
  intro y
  rw [ZFCModel_roundtrip]
  constructor
  · intro h
    obtain ⟨x, hx1, hx2⟩ := (ht y).mp h
    exact ⟨x, (ZFCModel_roundtrip M x s).mpr hx1, hx2⟩
  · intro ⟨x, hx1, hx2⟩
    apply (ht y).mpr
    exact ⟨x, (ZFCModel_roundtrip M x s).mp hx1, hx2⟩

theorem Choice_preserved (M : ZFCModel U) :
    ZF_Choice (Mem'_from_ZFCModel M) M.eq := by
  intro s h_nonempty h_disjoint
  -- 1. Translate Disjointness Hypothesis to base model terms
  have h_disjoint' : ∀ x y : U, M.mem x s → M.mem y s → ¬ M.eq x y →
      ¬∃ z : U, M.mem z x ∧ M.mem z y := by
    intro x y hxs hys hneq ⟨z, hzx, hzy⟩
    apply h_disjoint x y ((ZFCModel_roundtrip M x s).mpr hxs)
      ((ZFCModel_roundtrip M y s).mpr hys) hneq
    exact ⟨z, (ZFCModel_roundtrip M z x).mpr hzx, (ZFCModel_roundtrip M z y).mpr hzy⟩
  -- 2. Translate Non-empty Hypothesis
  have h_nonempty' : ∀ x : U, M.mem x s → ∃ y : U, M.mem y x := by
    intro x hxs
    obtain ⟨y, hyx⟩ := h_nonempty x ((ZFCModel_roundtrip M x s).mpr hxs)
    exact ⟨y, (ZFCModel_roundtrip M y x).mp hyx⟩
  -- 3. Apply Choice
  obtain ⟨c, hc⟩ := M.choice s h_nonempty' h_disjoint'
  -- 4. Translate Result back
  use c
  intro x hxs
  have hxc : ExistsUnique_eq (fun y => M.mem y x ∧ M.mem y c) M.eq :=
    hc x ((ZFCModel_roundtrip M x s).mp hxs)
  obtain ⟨y, ⟨hyx, hyc⟩, h_uniq⟩ := hxc
  exists y
  constructor
  · simp only [ZFCModel_roundtrip]
    exact ⟨hyx, hyc⟩
  · intro y' hy'
    simp only [ZFCModel_roundtrip] at hy'
    exact h_uniq y' hy'

-- ============================================================================
-- PART 7: The ZFC Universality Theorem
-- ============================================================================

/--
The Full Universality Theorem for ZFC.

It asserts that from any ZFC model `M`, we can construct a derived membership
relation `mem'` (defined via Relative Identity) that:
1. Is extensionally equivalent to `M.mem` (Roundtrip).
2. Satisfies ALL ZFC axioms (including Choice, Extensionality, etc.).
3. Uses strictly `M.eq` for all equality/uniqueness conditions.
-/
theorem universality_theorem_ZFC (M : ZFCModel U) :
    let mem' := Mem'_from_ZFCModel M
    ZF_Extensionality mem' M.eq ∧
    ZF_Congruence mem' M.eq ∧
    ZF_Foundation mem' ∧
    ZF_EmptySet mem' ∧
    ZF_Pairing mem' M.eq ∧
    ZF_Union mem' ∧
    ZF_PowerSet mem' ∧
    ZF_Separation mem' ∧
    ZF_Infinity mem' M.eq ∧
    ZF_Replacement mem' M.eq ∧
    ZF_Choice mem' M.eq ∧
    (∀ y x, mem' y x ↔ M.mem y x) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact Extensionality_preserved M
  · exact Congruence_preserved M
  · exact Foundation_preserved M
  · exact EmptySet_preserved M
  · exact Pairing_preserved M
  · exact Union_preserved M
  · exact PowerSet_preserved M
  · exact Separation_preserved M
  · exact Infinity_preserved M
  · exact Replacement_preserved M
  · exact Choice_preserved M
  · exact ZFCModel_roundtrip M

end EtterEq
