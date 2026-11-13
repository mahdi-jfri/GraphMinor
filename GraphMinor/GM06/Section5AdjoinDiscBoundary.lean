module

public import GraphMinor.GM06.Defs
import GraphMinor.GM06.DiscRegions
import GraphMinor.GM11.ArcDrawings
import GraphMinor.GM11.RadialBasics

/-!
# Adjoining the boundary in the cut disc

For the region argument in the one-path case of VI Section 5, add the
disc boundary to the proper off-seam drawing. Its boundary vertices
already include the seam ends. Mark all existing boundary vertices
and glue the boundary circle to the drawing at those points. No vertex
is added, and each new edge lies on the boundary.
-/

public section
namespace GraphMinor.GM06
open Set GraphMinor.Surface

universe u

/-- A proper drawing in a closed disc with a boundary vertex can have
the disc boundary adjoined without adding vertices. The extra edges
are on that boundary. This supplies the augmented cut graph for the
one-path region argument of VI Section 5. -/
theorem exists_drawing_adjoining_disc_boundary
    {S : Type u} [TopologicalSpace S] [T2Space S] (hS : IsClosedDiscSpace S)
    (G : Drawing S) (hG : G.IsProper) (hne : (G.V ∩ bd S).Nonempty) :
    ∃ F : Drawing S, G.IsSubdrawing F ∧ F.U = G.U ∪ bd S ∧ F.V = G.V ∧
      ∀ e ∈ F.E, e ∈ G.E ∨ e ⊆ bd S := by
  obtain ⟨B, hBU, hBV⟩ := GM11.exists_drawing_on_oArc hS.isOArc_bd
    (G.finite_V.inter_of_left (bd S)) hne inter_subset_right
  have hmeet : G.U ∩ B.U ⊆ G.V ∩ B.V := by
    rintro x ⟨hxG, hxB⟩
    rw [hBU] at hxB
    have hxV := hG ⟨hxB, hxG⟩
    exact ⟨hxV, hBV.symm ▸ ⟨hxV, hxB⟩⟩
  let F := G.glue B hmeet
  have hFU : F.U = G.U ∪ bd S := by
    change G.U ∪ B.U = _
    rw [hBU]
  have hFV : F.V = G.V := by
    change G.V ∪ B.V = _
    rw [hBV]
    exact union_eq_left.mpr inter_subset_left
  have hFE : F.E = G.E ∪ B.E := Drawing.glue_E hmeet
  refine ⟨F, ⟨by rw [hFV], by rw [hFE]; exact subset_union_left⟩, hFU, hFV, ?_⟩
  intro e he
  rw [hFE] at he
  rcases he with he | he
  · exact Or.inl he
  · right
    intro x hx
    rw [← hBU]
    exact (he.2.1 hx).1

end GraphMinor.GM06
