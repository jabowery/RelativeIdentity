import Mathlib.SetTheory.ZFC.Basic

/-!
# Appendix B: Etter's cell construction (RCV → ZF)

A faithful mechanization of the construction in Tom Etter, *The Expressive Power of
Equality* [E1] — the construction the appendices **should** have used (see `docs/Errata.pdf`,
Errata 2 & 4). It replaces the refuted symmetric-intersection membership of `Stereo.lean`
/ `RCV.lean`.

We work over Mathlib's `ZFSet`, so the membership `cEd` below is genuine ZF membership,
not an abstract placeholder. The development culminates in Etter's two key results stated
as kernel-discharged `↔`s:

* `first_iff`  — Etter's **Theorem 1**: `First c ↔ ∀ d, ∃ e, V e d ∧ C e c`.
* `mem_iff`    — Etter's **Theorem 2**: `cEd ↔ ∃ e f, R e f ∧ First e ∧ V c e ∧ ¬First f ∧ V d f`.

Together they express ZF membership (`cEd`) and `First` using **only** the R, C, V
equalities — the core of Etter's expressiveness theorem.

Modeling note (load-bearing-but-unverified, per `AGENTS.md` "No-oracle claims"): Etter's
column index `n ∈ {1,2}` is modeled by `col : Bool` (`true ↔ n = 1`, the first column).
This is a faithful encoding of "one of two definite labels"; it is not kernel-checkable
that it matches Etter's intent, only that the resulting theorems hold.
-/

namespace UniversalityTheorem

open ZFSet

/-- A **cell** is Etter's `⟨x, y, n⟩` with `x ε y` and `n ∈ {1,2}`. The membership
constraint `x ∈ y` is carried as the field `mem`; the column `n` is `col : Bool`. -/
structure Cell where
  x : ZFSet
  y : ZFSet
  col : Bool
  mem : x ∈ y

namespace Cell

/-- `Val ⟨x,y,n⟩ = x` if `n = 1` (first column), else `y`. Etter's cell value. -/
def Val (c : Cell) : ZFSet := cond c.col c.x c.y

/-- Row equality: same `x` and same `y`. -/
def R (c d : Cell) : Prop := c.x = d.x ∧ c.y = d.y

/-- Column equality: same `n`. -/
def C (c d : Cell) : Prop := c.col = d.col

/-- Value equality: `Val c = Val d`. This is the equality taken as ZF identity. -/
def V (c d : Cell) : Prop := Val c = Val d

/-- `First c` ⇔ `c` is in the first column (`n = 1`). -/
def First (c : Cell) : Prop := c.col = true

/-- Cell membership `cEd := Val c ∈ Val d` (genuine ZF membership of the values). -/
def Mem (c d : Cell) : Prop := Val c ∈ Val d

/-! ## R, C, V are equalities (equivalence relations) -/

theorem equiv_R : Equivalence R :=
  ⟨fun _ => ⟨rfl, rfl⟩,
   fun ⟨h1, h2⟩ => ⟨Eq.symm h1, Eq.symm h2⟩,
   fun ⟨h1, h2⟩ ⟨h3, h4⟩ => ⟨Eq.trans h1 h3, Eq.trans h2 h4⟩⟩

theorem equiv_C : Equivalence C :=
  ⟨fun _ => rfl, fun h => Eq.symm h, fun h1 h2 => Eq.trans h1 h2⟩

theorem equiv_V : Equivalence V :=
  ⟨fun _ => rfl, fun h => Eq.symm h, fun h1 h2 => Eq.trans h1 h2⟩

/-! ## RCV conjunction is cell identity

Etter: `R(c=d) ∧ C(c=d) ∧ V(c=d) ⇒ c = d`. In fact `R ∧ C` already determines the cell
(then `V` follows), which we record as `cell_identity`; the literal three-equality form is
`rcv_identity`. -/

theorem cell_identity {c d : Cell} (hR : R c d) (hC : C c d) : c = d := by
  obtain ⟨cx, cy, cc, ch⟩ := c
  obtain ⟨dx, dy, dc, dh⟩ := d
  simp only [R, C] at hR hC
  obtain ⟨hx, hy⟩ := hR
  subst hx; subst hy; subst hC
  rfl

theorem rcv_identity {c d : Cell} (hR : R c d) (hC : C c d) (_hV : V c d) : c = d :=
  cell_identity hR hC

/-! ## Theorem 1: `First` from the RCV equalities

`First(c) ⇔ ∀ d, ∃ e, V(e=d) ∧ C(e=c)`. Forward: every set is the value of a
first-column cell (over its singleton), so column 1 hits every value. Backward: `∅` is the
value of some cell but of **no** second-column cell (a second-column value `y` has a
member, so `y ≠ ∅`); requiring every value to be matched in `c`'s column forces column 1. -/

theorem first_iff (c : Cell) :
    First c ↔ ∀ d : Cell, ∃ e : Cell, V e d ∧ C e c := by
  constructor
  · -- First c → every value is reachable in c's column (column 1)
    intro hc d
    refine ⟨⟨Val d, {Val d}, true, mem_singleton.mpr rfl⟩, ?_, ?_⟩
    · rfl
    · exact Eq.symm hc
  · -- the column condition forces First c
    intro H
    obtain ⟨e, hV, hC⟩ := H ⟨∅, {∅}, true, mem_singleton.mpr rfl⟩
    have hVe : Val e = ∅ := hV
    have hece : e.col = c.col := hC
    have hecol : e.col = true := by
      cases hcol : e.col
      · -- e.col = false: its value is e.y ⊇ e.x, yet equals ∅ — contradiction
        exfalso
        have hy : Val e = e.y := by simp [Val, hcol]
        have hmem : e.x ∈ e.y := e.mem
        rw [← hy, hVe] at hmem
        exact notMem_empty _ hmem
      · rfl
    unfold First
    rw [← hece]
    exact hecol

/-! ## Theorem 2: ZF membership `cEd` from the RCV equalities

`cEd ⇔ ∃ e f, R(e=f) ∧ First(e) ∧ V(c=e) ∧ ¬First(f) ∧ V(d=f)`. The witnesses are the two
cells `⟨Val c, Val d, 1⟩` and `⟨Val c, Val d, 2⟩` of the same row — they are well-formed
exactly when `Val c ∈ Val d`. -/

theorem mem_iff (c d : Cell) :
    Mem c d ↔ ∃ e f : Cell, R e f ∧ First e ∧ V c e ∧ ¬ First f ∧ V d f := by
  constructor
  · intro h
    -- h : Val c ∈ Val d, so both cells ⟨Val c, Val d, _⟩ are well-formed
    refine ⟨⟨Val c, Val d, true, h⟩, ⟨Val c, Val d, false, h⟩, ?_, ?_, ?_, ?_, ?_⟩
    · exact ⟨rfl, rfl⟩
    · rfl
    · rfl
    · simp [First]
    · rfl
  · rintro ⟨e, f, ⟨_hRx, hRy⟩, hFe, hVc, hFf, hVd⟩
    unfold Mem
    have he : e.col = true := hFe
    have hVe : Val e = e.x := by simp [Val, he]
    have hfcol : f.col = false := by
      cases hcol : f.col
      · rfl
      · exact absurd hcol hFf
    have hVf : Val f = f.y := by simp [Val, hfcol]
    have hVc' : Val c = Val e := hVc
    have hVd' : Val d = Val f := hVd
    rw [hVc', hVe, hVd', hVf, ← hRy]
    exact e.mem

/-! ## The value homomorphism is onto, and `cEd` is genuine ZF membership

`Val` surjects onto `ZFSet` (every set is the value of a first-column cell), and `Mem` is,
by definition, ZF membership of the values. So the cell model *is* the ZF universe viewed
through `Val`, with `V` as identity — Etter's homomorphism-becomes-isomorphism. -/

/-- Every ZF set is the value of some cell (its first-column singleton cell). -/
theorem val_surjective (s : ZFSet) : ∃ c : Cell, Val c = s :=
  ⟨⟨s, {s}, true, mem_singleton.mpr rfl⟩, rfl⟩

/-- `cEd` is, definitionally, genuine ZF membership of the cell values. -/
theorem mem_iff_zf (c d : Cell) : Mem c d ↔ Val c ∈ Val d := Iff.rfl

/-! ## `cEd` is a genuine (irreflexive, asymmetric) membership — the green test

Counterpart to `Stereo.Refutation` (Phase 1): the refuted intersection membership was
*symmetric*; the cell membership inherits ZF's irreflexivity and asymmetry, and we exhibit
a concrete witness — `∅ ∈ {∅}` but `{∅} ∉ ∅`. -/

/-- `cEd` is irreflexive (genuine ZF Foundation content, via regularity). -/
theorem mem_irreflexive (c : Cell) : ¬ Mem c c := mem_irrefl _

/-- `cEd` is asymmetric — the discriminating contrast with the refuted *symmetric*
intersection membership (`Stereo.Refutation.stereoMem_symm`). -/
theorem mem_asymmetric {c d : Cell} : Mem c d → ¬ Mem d c := fun h => mem_asymm h

/-- Concrete witness that `cEd` is not symmetric: `∅ ∈ {∅}` while `{∅} ∉ ∅`. -/
theorem mem_not_symmetric : ∃ c d : Cell, Mem c d ∧ ¬ Mem d c := by
  refine ⟨⟨∅, {∅}, true, mem_singleton.mpr rfl⟩,
          ⟨{∅}, {{∅}}, true, mem_singleton.mpr rfl⟩, ?_, ?_⟩
  · exact mem_singleton.mpr rfl
  · exact notMem_empty _

end Cell
end UniversalityTheorem
