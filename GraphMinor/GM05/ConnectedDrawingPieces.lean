module

public import GraphMinor.Surface.Defs
public import GraphMinor.Minor.Model
import GraphMinor.GM11.Walks
import GraphMinor.GM07.Section46WalkOfConnected

/-!
# Connected pieces of a drawing

In the union construction of GM V, (8.14), each vertex branch is a
connected union of subdivided arcs. Once crossings are vertices, such
a union contains every edge that it meets away from the vertices.
Taking those edges and its vertices gives a connected subdrawing.
-/

public section
namespace GraphMinor.GM05
open Set Graph Surface

/-- A piece made of whole edges and vertices is the support of a
subdrawing. The edge condition is checked after subdividing at its
boundary points. -/
theorem exists_subdrawing_of_edge_closed_piece {S : Type*}
    [TopologicalSpace S] [T2Space S] (D : Drawing S) {A : Set S}
    (hAU : A ⊆ D.U)
    (hedge : ∀ e ∈ D.E, (e ∩ A).Nonempty → closure e ⊆ A) :
    ∃ B : Drawing S, B.IsSubdrawing D ∧ B.U = A ∧ B.V = A ∩ D.V := by
  classical
  let F : Set (Set S) := {e | closure e ⊆ A}
  have hV : D.spanV A F = A ∩ D.V := by
    apply subset_antisymm
    · rintro x (hx | hx)
      · exact hx
      · obtain ⟨e, he, hx⟩ := mem_iUnion₂.mp hx
        exact ⟨he.1 hx.1, hx.2⟩
    · exact subset_union_left
  refine ⟨D.span A F, D.span_isSubdrawing A F, ?_, hV⟩
  change D.spanU A F = A
  rw [Drawing.spanU, hV]
  apply subset_antisymm
  · exact union_subset inter_subset_left (iUnion₂_subset fun e he ↦ he.1)
  · intro x hx
    by_cases hxV : x ∈ D.V
    · exact .inl ⟨hx, hxV⟩
    · obtain ⟨e, he, hxe⟩ := D.exists_edge_of_mem (hAU hx) hxV
      exact .inr (mem_iUnion₂.mpr ⟨e, ⟨hedge e he ⟨x, hxe, hx⟩, he⟩,
        subset_closure hxe⟩)

/-- A connected piece containing a vertex gives a connected branch
subgraph. This supplies the branch connectivity in GM V, (8.14). -/
theorem exists_connected_subdrawing_of_edge_closed_piece {S : Type*}
    [TopologicalSpace S] [T2Space S] (D : Drawing S) {A : Set S}
    (hAU : A ⊆ D.U) (hA : IsPreconnected A) (hv : (A ∩ D.V).Nonempty)
    (hedge : ∀ e ∈ D.E, (e ∩ A).Nonempty → closure e ⊆ A) :
    ∃ B : Drawing S, B.IsSubdrawing D ∧ B.U = A ∧ B.V = A ∩ D.V ∧
      GraphConnected B.toGraph := by
  obtain ⟨B, hB, hU, hV⟩ := exists_subdrawing_of_edge_closed_piece D hAU hedge
  refine ⟨B, hB, hU, hV, ?_, ?_⟩
  · change B.V.Nonempty
    rwa [hV]
  · intro x hx y hy
    change x ∈ B.V at hx
    change y ∈ B.V at hy
    have hxA : x ∈ A := (hV ▸ hx).1
    have hyA : y ∈ A := (hV ▸ hy).1
    obtain ⟨W⟩ := GM07.exists_walk_of_preconnected B hA (hU ▸ subset_rfl) hx hxA hy hyA
    clear hx hy hxA hyA
    induction W with
    | nil _ => exact Relation.ReflTransGen.refl
    | cons hl _ ih => exact Relation.ReflTransGen.head hl.adj ih

end GraphMinor.GM05
