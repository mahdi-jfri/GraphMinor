module

public import GraphMinor.GM16.Defs
import GraphMinor.GM16.VertexExtensions
import GraphMinor.Minor.Basic

/-!
# The null outgrowth used at the end of XVI (1.3)

On page 52, graphs of bounded order are vertex extensions of the null
graph. The null graph is drawn on any nonempty surface and needs no
rings. The empty vertex and edge sets discharge all drawing conditions.
-/

public section
namespace GraphMinor.GM16
open Set Graph Surface
universe u v w

/-- A null graph is an outgrowth with no rings on any nonempty surface,
as used at the end of XVI (1.3), page 52. -/
theorem isOutgrowthByRings_of_vertexSet_eq_empty
    {S : Type w} [TopologicalSpace S] [Nonempty S]
    {α : Type u} {β : Type v} (H : Graph α β) (hV : V(H) = ∅) (d r : ℕ) :
    IsOutgrowthByRings S H d r := by
  classical
  have hE : E(H) = ∅ := by
    apply eq_empty_iff_forall_notMem.mpr
    intro e he
    obtain ⟨x, y, hxy⟩ := H.exists_isLink_of_mem_edgeSet he
    exact notMem_empty x (hV ▸ hxy.left_mem)
  refine ⟨H, H, ⟨Iso.refl H⟩, 0, Fin.elim0, Fin.elim0, Fin.elim0,
    fun _ => Classical.choice ‹Nonempty S›, fun _ => ∅, ?_⟩
  simp only [hV, hE, Nat.zero_le, le_refl, Fin.forall_fin_zero, iUnion_of_empty,
    union_empty, Set.injOn_empty, notMem_empty, false_implies, implies_true,
    and_self]

/-- Deleting every vertex gives a null graph, so a finite graph of
order at most `w` is a `w`-vertex extension of a null outgrowth. -/
theorem exists_null_outgrowth_extension
    {S : Type w} [TopologicalSpace S] [Nonempty S]
    {α : Type u} {β : Type v} (G : Graph α β) {w₀ d r : ℕ}
    (hcard : V(G).ncard ≤ w₀) :
    ∃ H : Graph α β, IsVertexExtension w₀ G H ∧ IsOutgrowthByRings S H d r := by
  refine ⟨GM09.deleteVertices G V(G),
    isVertexExtension_of_deleteVertices_eq (Subset.refl _) hcard rfl, ?_⟩
  apply isOutgrowthByRings_of_vertexSet_eq_empty
  exact Set.sdiff_self

end GraphMinor.GM16
