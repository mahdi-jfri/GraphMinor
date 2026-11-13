module

public import GraphMinor.GM06.Defs
import GraphMinor.GM11.Defs
import GraphMinor.GM11.Walks

/-!
# A closed union of whole edges is a subdrawing

Retain every vertex on the closed set and every edge contained in
it. Closedness retains the edge ends. If every edge meeting the set
lies wholly in it, the retained point set is exactly that set.
This constructs the boundary subdrawing used to turn first contact
at vertices into first contact at all points on the cut disc in
the proof of VI (5.1), page 129.
-/

public section
namespace GraphMinor.GM06
open Set Topology GraphMinor.Surface
universe u

/-- A closed subset of a drawing which is a union of whole edges
and vertices is itself the point set of a subdrawing. -/
theorem exists_subdrawing_on_closed_union_of_edges
    {S : Type u} [TopologicalSpace S] [T2Space S] (F : Drawing S)
    {T : Set S} (hT : IsClosed T) (hTF : T ⊆ F.U)
    (hwhole : ∀ e ∈ F.E, (e ∩ T).Nonempty → e ⊆ T) :
    ∃ B : Drawing S, B.IsSubdrawing F ∧ B.V = F.V ∩ T ∧ B.U = T := by
  let E := {e : Set S | e ∈ F.E ∧ e ⊆ T}
  let B := F.span (F.V ∩ T) E
  have hBF : B.IsSubdrawing F := Drawing.span_isSubdrawing F _ _
  have hBE : B.E = E := by
    rw [Drawing.span_E]
    exact inter_eq_left.mpr (fun e he => he.1)
  have hBV : B.V = F.V ∩ T := by
    apply subset_antisymm
    · intro x hx
      refine ⟨hBF.1 hx, ?_⟩
      change x ∈ F.spanV (F.V ∩ T) E at hx
      rcases hx with hx | hx
      · exact hx.1.2
      · obtain ⟨e, he, hxe⟩ := mem_iUnion₂.mp hx
        exact closure_minimal he.1.2 hT hxe.1
    · intro x hx
      change x ∈ F.spanV (F.V ∩ T) E
      exact Or.inl ⟨hx, hx.1⟩
  have hBU : B.U = T := by
    apply subset_antisymm
    · rw [B.U_eq]
      apply union_subset
      · rw [hBV]
        exact inter_subset_right
      · apply iUnion₂_subset
        intro e he
        have heE : e ∈ E := hBE ▸ he
        exact closure_minimal heE.2 hT
    · intro x hx
      by_cases hxV : x ∈ F.V
      · exact B.V_subset_U (hBV.symm ▸ ⟨hxV, hx⟩)
      · obtain ⟨e, he, hxe⟩ := F.exists_edge_of_mem (hTF hx) hxV
        have heB : e ∈ B.E := hBE.symm ▸ ⟨he, hwhole e he ⟨x, hxe, hx⟩⟩
        exact (heB.2.1 hxe).1
  exact ⟨B, hBF, hBV, hBU⟩

end GraphMinor.GM06
