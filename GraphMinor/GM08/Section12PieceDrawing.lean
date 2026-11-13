module

public import GraphMinor.GM08.Section11Topo
public import GraphMinor.GM08.Section8Sleeve
import GraphMinor.GM11.Walks

/-!
# The drawing inside one foundation ring

Keep exactly the vertices in the bounded disc and the edges inside
the ring. Their ends remain in the disc because it is closed. The
ring is normal, so it is also normal for the smaller drawing. This
constructs the geometric piece used for a label on VIII, page 272.
-/

public section

namespace GraphMinor.GM08

open Set Surface

universe u

/-- A normal ring cuts out a drawing with exactly the vertices and
edges specified in the derived portrait construction of VIII,
Section 11, page 272, used in Section 12. -/
theorem exists_drawing_inside_ring {S : Type u} [TopologicalSpace S]
    (hS : IsClosedDisc (univ : Set S)) (D : Drawing S)
    {F : Set S} (hF : IsOArc F) (hNormal : D.IsNormal F) :
    ∃ J : Drawing S, J.IsSubdrawing D ∧
      J.V = D.V ∩ (F ∪ insideSet F) ∧
      J.E = edgesInsideOArc D univ F ∧
      J.U ⊆ F ∪ insideSet F ∧ J.IsNormal F := by
  obtain ⟨B, hB, hBd, hInt, hDisc⟩ := exists_ring_disc hS hF
  have hcl : ∀ e ∈ edgesInsideOArc D univ F, closure e ⊆ B := by
    intro e he
    have heInside : e ⊆ insideSet F := he.2
    exact closure_minimal (heInside.trans (by rw [hInt]; exact discInt_subset B))
      (isClosed_ring hS hF |> fun h => hDisc ▸ h)
  have hends : ∀ e ∈ edgesInsideOArc D univ F,
      closure e ∩ D.V ⊆ D.V ∩ (F ∪ insideSet F) := by
    intro e he x hx
    exact ⟨hx.2, hDisc.symm ▸ hcl e he hx.1⟩
  obtain ⟨J, hJ, hJV, hJE⟩ := exists_span_subdrawing_in_disc hS
    (subset_univ D.U) inter_subset_left (fun e he => he.1) hends
  refine ⟨J, hJ, hJV, hJE, ?_, ?_⟩
  · rw [J.U_eq]
    refine union_subset (hJV ▸ inter_subset_right) (iUnion₂_subset fun e he => ?_)
    rw [hJE] at he
    exact hDisc.symm ▸ hcl e he
  · intro x hx
    rw [hJV]
    exact ⟨hNormal ⟨hx.1, hJ.U_subset hx.2⟩, .inl hx.1⟩

end GraphMinor.GM08
