module

public import GraphMinor.GM08.Section15Defs
public import GraphMinor.GM12.Section3Punctured
import GraphMinor.GM12.Section3PuncturedModel
import GraphMinor.GM12.Section3BoundaryEquality
import GraphMinor.GM12.Section3ModelComplexity

/-!
# The cylinder between the adjusted empty sides

Removing the interiors of two disjoint discs from a sphere leaves a
cylinder. Its cuffs are exactly the lifted disc boundaries. Apply the
proved model and boundary formulas for punctured surfaces. This is the
cylinder carrying all framing roots in the disc construction of (15.4).
-/

public section

namespace GraphMinor.GM08

open Set GraphMinor.Surface

universe w

/-- The complement of two disjoint disc interiors in a sphere is a
cylinder, with those two boundaries as its cuffs. This is the adjusted
framing surface in VIII (15.4), page 282. -/
theorem cylinder_complement_two_discs {S : Type w} [TopologicalSpace S] [ConnectedSpace S]
    (hS : IsClosedSurface S) (hsph : IsSphere S) {D E : Set S}
    (hD : IsClosedDisc D) (hE : IsClosedDisc E) (hDE : Disjoint D E) :
    let Q := GM12.discComplement (![D, E] : Fin 2 → Set S)
    IsCylinder Q ∧
      cuffs Q = {(Subtype.val : Q → S) ⁻¹' discBd D, (Subtype.val : Q → S) ⁻¹' discBd E} ∧
      (Subtype.val : Q → S) ⁻¹' discBd D ≠ (Subtype.val : Q → S) ⁻¹' discBd E ∧
      bd Q = (Subtype.val : Q → S) ⁻¹' (discBd D ∪ discBd E) := by
  classical
  have : T2Space S := hS.2.1
  let P : Fin 2 → Set S := ![D, E]
  have hP : ∀ i, IsClosedDisc (P i) := by intro i; fin_cases i <;> assumption
  have hdis : Pairwise (fun i j => Disjoint (P i) (P j)) := by
    intro i j hij
    fin_cases i <;> fin_cases j
    · exact (hij rfl).elim
    · exact hDE
    · exact hDE.symm
    · exact (hij rfl).elim
  have hsurf := GM12.discComplement_isSurface hS P hP hdis
  obtain ⟨eS⟩ := hsph
  obtain ⟨eM⟩ := GM12.isSphere_model_zero
  have hmodel := GM12.discComplement_model_of_closed_model hS P hP hdis (eS.trans eM.symm)
  rw [Nat.card_fin] at hmodel
  have hcyl : IsCylinder (GM12.discComplement P) := ⟨hsurf, hmodel⟩
  have hcf : cuffs (GM12.discComplement P) =
      {(Subtype.val : GM12.discComplement P → S) ⁻¹' discBd D,
        (Subtype.val : GM12.discComplement P → S) ⁻¹' discBd E} := by
    rw [GM12.discComplement_cuffs_eq hS P hP hdis]
    ext C
    constructor
    · rintro ⟨i, rfl⟩
      fin_cases i <;> simp [P]
    · rintro (rfl | rfl)
      · exact ⟨0, rfl⟩
      · exact ⟨1, rfl⟩
  refine ⟨hcyl, hcf, ?_, ?_⟩
  · intro heq
    have hc := hcyl.ncard_cuffs
    rw [hcf, heq, pair_eq_singleton, ncard_singleton] at hc
    exact (by decide : (1 : ℕ) ≠ 2) hc
  · rw [GM12.discComplement_boundary_eq hS P hP]
    congr 1
    ext x
    simp [P, Fin.exists_fin_two]

end GraphMinor.GM08
