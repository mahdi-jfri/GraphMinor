module

public import GraphMinor.Surface.Defs
public import GraphMinor.Surface.TopologyStatements
import GraphMinor.GM05.ParallelLine
import GraphMinor.GM11.Forest
import GraphMinor.GM11.Walks
import GraphMinor.GM11.RadialCorners
import GraphMinor.Surface.SurfaceGraph

/-!
# Adding another parallel edge curve

For the copy drawings in GM V, (8.14), forbid all previous parallel
curves and the original drawing with the chosen open edge removed.
This is closed and meets the original edge closure only at its ends.
A parallel line then avoids both the original drawing and the previous
curves away from vertices.
-/

public section
namespace GraphMinor.GM05
open Set Surface

/-- Insert one more parallel edge curve while avoiding all previous
curves away from the original vertices, for GM V, (8.14), page 113. -/
theorem exists_fresh_parallel_edge {S : Type} [TopologicalSpace S]
    (hS : IsClosedSurface S) (D : Drawing S) {e : Set S} {u v : S}
    (hl : D.toGraph.IsLink e u v) (huv : u ≠ v)
    {F : Set (Set S)} (hF : F.Finite) (hFc : ∀ Q ∈ F, IsClosed Q)
    (hFU : ∀ Q ∈ F, Q ∩ D.U ⊆ D.V) :
    ∃ P : Set S, IsLineWithEnds P u v ∧ P ∩ D.U = {u,v} ∧
      ∀ Q ∈ F, P ∩ Q ⊆ D.V := by
  let : T2Space S := hS.2.1
  have he : e ∈ D.E := hl.edge_mem
  have hcap : closure e ∩ D.V = {u,v} := hl.2.2.2
  have hline := GM11.isLine_closure he huv hcap
  let Z : Set S := (D.U \ e) ∪ ⋃ Q ∈ F, Q
  have hZ : IsClosed Z := by
    apply ((GM11.deleteEdge_U D he).symm ▸ (D.deleteEdge e).isClosed_U).union
    exact hF.isClosed_biUnion hFc
  have hLZ : closure e ∩ Z ⊆ {u,v} := by
    rintro x ⟨hxL,hxZ⟩
    have hxV : x ∈ D.V := by
      rcases hxZ with hx | hx
      · by_contra hn
        exact hx.2 ((D.closure_diff_V he).subset ⟨hxL,hn⟩)
      · obtain ⟨Q,hQ,hxQ⟩ := mem_iUnion₂.mp hx
        exact hFU Q hQ ⟨hxQ,D.closure_subset_U he hxL⟩
    exact hcap ▸ ⟨hxL,hxV⟩
  obtain ⟨P,hP,hPZ,hPL⟩ := exists_parallel_line_closed_surface hS hline huv hZ hLZ
  have hendsV : ({u,v} : Set S) ⊆ D.V := pair_subset hl.left_mem hl.right_mem
  have hPU : P ∩ D.U = {u,v} := by
    apply subset_antisymm
    · rintro x ⟨hxP,hxU⟩
      by_cases hxe : x ∈ e
      · exact hPL ▸ ⟨hxP,subset_closure hxe⟩
      · exact hPZ ⟨hxP,Or.inl ⟨hxU,hxe⟩⟩
    · rintro x (rfl | rfl)
      · exact ⟨hP.left_mem,D.V_subset_U hl.left_mem⟩
      · exact ⟨hP.right_mem,D.V_subset_U hl.right_mem⟩
  refine ⟨P,hP,hPU,?_⟩
  intro Q hQ x hx
  exact hendsV (hPZ ⟨hx.1,Or.inr (mem_iUnion₂.mpr ⟨Q,hQ,hx.2⟩)⟩)

end GraphMinor.GM05
