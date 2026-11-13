module

public import GraphMinor.Surface.Defs
public import GraphMinor.GM11.Defs
import GraphMinor.GM11.Walks

/-!
# The closed sets avoided when thickening edges

Deleting the open part of one edge leaves a closed subset of a finite
drawing. Indeed it is the vertices and the closures of all other edges.
Distinct edge closures meet only at vertices. These facts supply the
closed protected sets for the edge-thickening construction of the
derived portrait on VIII, page 272, used in Section 12.
-/

public section

namespace GraphMinor.GM08

open Set Surface

universe u

/-- Distinct closed drawing edges meet only at vertices. This is used
when choosing the protected sets for thickened edges in Section 12. -/
theorem closure_edges_inter_subset_vertices {S : Type u} [TopologicalSpace S]
    (D : Drawing S) {e f : Set S} (he : e ∈ D.E) (hf : f ∈ D.E) (hne : e ≠ f) :
    closure e ∩ closure f ⊆ D.V := by
  rintro x ⟨hxe, hxf⟩
  by_contra hxV
  have hxe' : x ∈ e := D.closure_diff_V he ▸ And.intro hxe hxV
  have hxf' : x ∈ f := D.closure_diff_V hf ▸ And.intro hxf hxV
  exact hne (D.edge_eq_of_mem he hf hxe' hxf')

/-- The part of a finite drawing outside one open edge is closed.
It is the finite union of its vertices and the other closed edges. -/
theorem drawing_sdiff_edge_isClosed {S : Type u} [TopologicalSpace S] [T1Space S]
    (D : Drawing S) {e : Set S} (he : e ∈ D.E) : IsClosed (D.U \ e) := by
  have heq : D.U \ e = D.V ∪ ⋃ f ∈ {f ∈ D.E | f ≠ e}, closure f := by
    ext x
    constructor
    · rintro ⟨hxU, hxe⟩
      by_cases hxV : x ∈ D.V
      · exact .inl hxV
      · obtain ⟨f, hf, hxf⟩ := D.exists_edge_of_mem hxU hxV
        have hfe : f ≠ e := fun h => hxe (h ▸ hxf)
        exact .inr (mem_iUnion₂.mpr ⟨f, ⟨hf, hfe⟩, subset_closure hxf⟩)
    · rintro (hxV | hxF)
      · exact ⟨D.V_subset_U hxV, fun hxe => (he.2.1 hxe).2 hxV⟩
      · obtain ⟨f, ⟨hf, hfe⟩, hxf⟩ := mem_iUnion₂.mp hxF
        refine ⟨D.closure_subset_U hf hxf, ?_⟩
        intro hxe
        exact (he.2.1 hxe).2
          (closure_edges_inter_subset_vertices D he hf hfe.symm ⟨subset_closure hxe, hxf⟩)
  rw [heq]
  exact D.finite_V.isClosed.union
    ((D.finite_edges.subset (sep_subset _ _)).isClosed_biUnion fun _ _ => isClosed_closure)

/-- A non-loop edge has a line as its closure with two distinct ends.
This is the line to which the lens construction is applied when the
remaining edges are thickened on VIII, page 272. -/
theorem exists_line_ends_of_not_loop {S : Type u} [TopologicalSpace S]
    {D : Drawing S} {e : Set S} (he : e ∈ D.E) (hn : ¬ D.IsLoop e) :
    ∃ u v, u ≠ v ∧ closure e ∩ D.V = {u, v} ∧ IsLineWithEnds (closure e) u v := by
  rcases D.edge_cond e he with ⟨u, v, huv, hcap, hl⟩ | ⟨v, hcap, _⟩
  · exact ⟨u, v, huv, hcap, hl⟩
  · exact False.elim (hn ⟨he, v, hcap⟩)

end GraphMinor.GM08
