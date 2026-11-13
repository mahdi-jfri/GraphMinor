module

public import GraphMinor.Surface.Defs
import GraphMinor.GM16.FiniteDrawingUnion

/-!
# Adding the cellular loop drawings at old vertices

The new petal drawings meet the old drawing only at their marked
vertices and meet one another only at old vertices. The finite drawing
union therefore keeps exactly the old vertex set and takes the union
of the edge sets. Properness is preserved as well. This assembles the
cellular loop replacement in VIII, Section 12, page 274.
-/

public section

namespace GraphMinor.GM08

open Set Surface

universe u v

/-- Add finitely many drawings attached at old vertices, as in the
cellular loop replacement for VIII, Section 12. The point and edge sets
are their unions, and the vertex set stays unchanged. -/
theorem exists_drawing_union_at_vertices {S : Type u} [TopologicalSpace S] [T2Space S]
    (D : Drawing S) {ι : Type v} [Finite ι] (P : ι → Drawing S)
    (hPV : ∀ i, (P i).V ⊆ D.V)
    (hPD : ∀ i, (P i).U ∩ D.U ⊆ (P i).V)
    (hPP : Pairwise fun i j => (P i).U ∩ (P j).U ⊆ D.V)
    (hDprop : D.IsProper) (hPprop : ∀ i, (P i).IsProper) :
    ∃ H : Drawing S, H.V = D.V ∧ H.E = D.E ∪ ⋃ i, (P i).E ∧
      H.U = D.U ∪ ⋃ i, (P i).U ∧ H.IsProper := by
  classical
  let A : Option ι → Drawing S := fun i => match i with | none => D | some i => P i
  have hAZ : ∀ i ∈ (univ : Set (Option ι)), (A i).U ∩ D.V ⊆ (A i).V := by
    intro i _ x hx
    cases i with
    | none => exact hx.2
    | some i => exact hPD i ⟨hx.1, D.V_subset_U hx.2⟩
  have hAA : ∀ i ∈ (univ : Set (Option ι)), ∀ j ∈ univ, i ≠ j →
      (A i).U ∩ (A j).U ⊆ D.V := by
    intro i _ j _ hij x hx
    cases i with
    | none =>
      cases j with
      | none => exact False.elim (hij rfl)
      | some j => exact hPV j (hPD j ⟨hx.2, hx.1⟩)
    | some i =>
      cases j with
      | none => exact hPV i (hPD i hx)
      | some j => exact hPP (fun h => hij (congrArg some h)) hx
  obtain ⟨H, hHU, hHV, hHE⟩ := GM16.exists_drawing_of_finite_drawings
    (I := (univ : Set (Option ι))) (toFinite _) D.finite_V A hAZ hAA
  have hV : H.V = D.V := by
    rw [hHV]
    apply Subset.antisymm
    · rintro x (hx | hx)
      · exact hx
      · obtain ⟨i, _, hi⟩ := mem_iUnion₂.mp hx
        cases i with
        | none => exact hi
        | some i => exact hPV i hi
    · exact subset_union_left
  have hE : H.E = D.E ∪ ⋃ i, (P i).E := by
    rw [hHE]
    simp only [mem_univ, iUnion_true, iUnion_option]
    rfl
  have hU : H.U = D.U ∪ ⋃ i, (P i).U := by
    rw [hHU]
    apply Subset.antisymm
    · rintro x (hx | hx)
      · exact .inl (D.V_subset_U hx)
      · obtain ⟨i, _, hi⟩ := mem_iUnion₂.mp hx
        cases i with
        | none => exact .inl hi
        | some i => exact .inr (mem_iUnion.mpr ⟨i, hi⟩)
    · rintro x (hx | hx)
      · exact .inr (mem_iUnion₂.mpr ⟨none, mem_univ _, hx⟩)
      · obtain ⟨i, hi⟩ := mem_iUnion.mp hx
        exact .inr (mem_iUnion₂.mpr ⟨some i, mem_univ _, hi⟩)
  refine ⟨H, hV, hE, hU, ?_⟩
  rintro x ⟨hxbd, hxU⟩
  rw [hV]
  rw [hU] at hxU
  rcases hxU with hxD | hxP
  · exact hDprop ⟨hxbd, hxD⟩
  · obtain ⟨i, hi⟩ := mem_iUnion.mp hxP
    exact hPV i (hPprop i ⟨hxbd, hi⟩)

end GraphMinor.GM08
