import UniversalityTheorem.Cell

/-!
# Appendix B: the RCV language and its ZF membership (corrected)

Following Etter, *The Expressive Power of Equality* [E1] (see `docs/Errata.pdf`, Errata 2 & 4),
the three RCV equalities are the **row**, **column**, and **value** equalities `R`, `C`,
`V` *on cells* (`UniversalityTheorem.Cell`) — not three arbitrary equivalence relations,
and `V` is **not** unused. ZF membership is the cell membership `cEd` (`Cell.Mem`),
recovered from `R`, `C`, `V` alone by Etter's Theorem 2 (`Cell.mem_iff`); `First` is
recovered by Theorem 1 (`Cell.first_iff`).

This module is the RCV-language interface over the corrected construction. The previous
contents — an abstract `RCVModel` whose membership reused the *symmetric* intersection
`¬(R y x ∧ C y x)` and dropped `V` — were refuted in `docs/Errata.pdf` and have been removed;
see `Stereo.intersectionMem_not_ZF` for the kernel-checked proof that that intersection
candidate fails.

**Scope of what the kernel certifies here (a `No-oracle` note, per `AGENTS.md`).** The
theorems below certify the *interpretation*: `Val` maps cell membership/identity to genuine
ZF membership/identity (`Cell.mem_iff_zf`, `Cell.val_surjective`), membership and `First`
are definable from `R, C, V` alone (`mem_RCV_definable`, `first_RCV_definable`), and the
membership has the right ZF character (irreflexive, asymmetric). Etter's full conclusion —
*Con(ZF) ⇒ Con(RCV set theory)* — is the soundness of this interpretation; that
meta-implication is argued informally in [E1] and is **not** itself a kernel goal here.
-/

namespace UniversalityTheorem
namespace RCV

open Cell

/-- RCV membership: Etter's cell membership `cEd`, i.e. genuine ZF membership of the cell
values. It is defined over the cell construction that uses all three RCV equalities. -/
def Mem_RCV (c d : Cell) : Prop := Cell.Mem c d

/-- `Mem_RCV` is, definitionally, genuine ZF membership of the cell values. -/
theorem mem_RCV_iff_zf (c d : Cell) : Mem_RCV c d ↔ Val c ∈ Val d := Iff.rfl

/-- **Etter's Theorem 2.** ZF membership is definable from the three RCV equalities alone. -/
theorem mem_RCV_definable (c d : Cell) :
    Mem_RCV c d ↔ ∃ e f : Cell, R e f ∧ First e ∧ V c e ∧ ¬ First f ∧ V d f :=
  Cell.mem_iff c d

/-- **Etter's Theorem 1.** `First` (first column) is definable from the RCV equalities. -/
theorem first_RCV_definable (c : Cell) :
    First c ↔ ∀ d : Cell, ∃ e : Cell, V e d ∧ C e c :=
  Cell.first_iff c

/-- The corrected membership is irreflexive — genuine ZF Foundation content (via
regularity), not the trivial `x ∉ x` sliver of the refuted construction. -/
theorem mem_RCV_irreflexive (c : Cell) : ¬ Mem_RCV c c := Cell.mem_irreflexive c

/-- The corrected membership is asymmetric — the discriminating contrast with the refuted
*symmetric* intersection candidate (`Stereo.intersectionMem_symm`). -/
theorem mem_RCV_asymmetric {c d : Cell} : Mem_RCV c d → ¬ Mem_RCV d c :=
  Cell.mem_asymmetric

end RCV
end UniversalityTheorem
