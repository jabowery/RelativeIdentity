import UniversalityTheorem.EtterEq

namespace UniversalityTheorem

open EtterEq

universe u
variable {U : Type u}

/-!
## 1. Slang: primitive identity
-/
structure SlangModel (U : Type u) where
  Id : U → U → U → Prop
  refl : ∀ x y : U, Id x y y
  symm : ∀ x y z : U, Id x y z → Id x z y
  trans : ∀ x y z w : U, Id x y z → Id x z w → Id x y w

def SlangModel.toRelativeIdentity (M : SlangModel U) : EtterEq.RelativeIdentity U :=
{ Id := M.Id, refl := M.refl, symm := M.symm, trans := M.trans }

def SlangMem (M : SlangModel U) : U → U → Prop :=
  EtterEq.MemFromId (M.toRelativeIdentity)

/-!
## 2. Slang equality (Quine Identity)
-/
/-- Slang equality: The "Quine Identity" of the membership predicate.
    [cite_start]x = y iff they are indistinguishable as elements and as sets. [cite: 140, 146] -/
def SlangEq (M : SlangModel U) (x y : U) : Prop :=
  (∀ z, SlangMem M z x ↔ SlangMem M z y) ∧ -- Indistinguishable as sets
  (∀ w, SlangMem M x w ↔ SlangMem M y w)   -- Indistinguishable as elements

theorem SlangEq_equiv (M : SlangModel U) : Equivalence (SlangEq M) := by
  constructor
  · intro x; exact ⟨by simp, by simp⟩
  · intro x y h; exact ⟨fun z => (h.1 z).symm, fun w => (h.2 w).symm⟩
  · intro x y z hxy hyz
    constructor
    · intro w; rw [hxy.1 w, hyz.1 w]
    · intro w; rw [hxy.2 w, hyz.2 w]

theorem SlangEq_congruence (M : SlangModel U) :
      EtterEq.ZF_Congruence (SlangMem M) (SlangEq M) := by
  intro x x' y y' hx hy
  rw [hx.2 y] -- Uses "indistinguishable as elements" part of Quine Identity
  rw [hy.1 x'] -- Uses "indistinguishable as sets" part of Quine Identity

/-!
## 3. Slang ZFC axioms
We include Extensionality here because Quine Identity implies Congruence
definitionally, but Extensionality is a property the model must satisfy.
-/
structure SlangZFC (M : SlangModel U) : Prop where
  extensionality : EtterEq.ZF_Extensionality (SlangMem M) (SlangEq M)
  foundation   : EtterEq.ZF_Foundation (SlangMem M)
  empty_set    : EtterEq.ZF_EmptySet (SlangMem M)
  pairing      : EtterEq.ZF_Pairing (SlangMem M) (SlangEq M)
  union        : EtterEq.ZF_Union (SlangMem M)
  power_set    : EtterEq.ZF_PowerSet (SlangMem M)
  separation   : EtterEq.ZF_Separation (SlangMem M)
  infinity     : EtterEq.ZF_Infinity (SlangMem M) (SlangEq M)
  replacement  : EtterEq.ZF_Replacement (SlangMem M) (SlangEq M)
  choice       : EtterEq.ZF_Choice (SlangMem M) (SlangEq M)

def SlangZFC.toEtterEqZFCModel (M : SlangModel U) (h : SlangZFC (U := U) M) :
    EtterEq.ZFCModel U :=
{ mem           := SlangMem M
  eq            := SlangEq M
  eq_equiv      := SlangEq_equiv M
  congruence    := SlangEq_congruence M
  extensionality:= h.extensionality
  foundation    := h.foundation
  empty_set     := h.empty_set
  pairing       := h.pairing
  union         := h.union
  power_set     := h.power_set
  separation    := h.separation
  infinity      := h.infinity
  replacement   := h.replacement
  choice        := h.choice }

/-!
## 4. The Universality Theorem
-/
theorem slang_universality_ZFC (M : SlangModel U) (h : SlangZFC (U := U) M) :
    let mem' := SlangMem M
    let eq' := SlangEq M
    EtterEq.ZF_Extensionality mem' eq' ∧
    EtterEq.ZF_Congruence    mem' eq' ∧
    EtterEq.ZF_Foundation    mem' ∧
    EtterEq.ZF_EmptySet      mem' ∧
    EtterEq.ZF_Pairing       mem' eq' ∧
    EtterEq.ZF_Union         mem' ∧
    EtterEq.ZF_PowerSet      mem' ∧
    EtterEq.ZF_Separation    mem' ∧
    EtterEq.ZF_Infinity      mem' eq' ∧
    EtterEq.ZF_Replacement   mem' eq' ∧
    EtterEq.ZF_Choice        mem' eq' ∧
    (∀ y x, mem' y x ↔ (SlangZFC.toEtterEqZFCModel M h).mem y x) := by
  -- We unpack the proofs directly from the hypothesis `h` and our congruence theorem.
  refine ⟨h.extensionality, SlangEq_congruence M, h.foundation, h.empty_set,
          h.pairing, h.union, h.power_set, h.separation, h.infinity,
          h.replacement, h.choice, ?_⟩
  -- The last goal is to show SlangMem M ↔ EM.mem
  -- Since EM was constructed using SlangMem M, this is definitionally true.
  intro y x
  rfl
end UniversalityTheorem
