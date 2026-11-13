module

public import GraphMinor.Surface.Defs
import GraphMinor.GM11.ArcDrawings
import GraphMinor.GM08.Section9DiscContext

/-!
# The one-edge drawing on a loop petal

The boundary of a petal with its marked vertex is a drawing with one
loop edge. Its open edge is the boundary minus that vertex, and its
closure is the whole boundary. These exact sets let the cellular loop
construction keep the abstract graph and its root vertices unchanged.
-/

public section

namespace GraphMinor.GM08

open Set Surface

universe u

/-- The single-loop drawing used for each cellular petal in VIII,
Section 12, page 274, with its vertex and edge sets specified exactly. -/
theorem exists_one_loop_drawing {S : Type u} [TopologicalSpace S] [T2Space S]
    {F : Set S} (hF : IsOArc F) {v : S} (hv : v ∈ F) :
    ∃ P : Drawing S, P.U = F ∧ P.V = {v} ∧ P.E = {F \ {v}} ∧ closure (F \ {v}) = F := by
  classical
  obtain ⟨P, hU, hV⟩ := GM11.exists_loop_drawing hF hv
  have hpc := Surface.isPathConnected_oArc_diff hF hv
  have huniq : ∀ e ∈ P.E, e = F \ {v} := by
    intro e he
    change e ∈ arcComponentsIn (P.U \ P.V) at he
    rw [hU, hV] at he
    obtain ⟨-, hsub, -, hmax⟩ := he
    exact (hmax _ Subset.rfl hpc hsub).symm
  obtain ⟨e, he⟩ := drawing_edges_nonempty_of_oArc (D := P) hF (by rw [hU])
  have heloop : F \ {v} ∈ P.E := huniq e he ▸ he
  have hE : P.E = {F \ {v}} := by
    ext e
    exact ⟨fun he => mem_singleton_iff.mpr (huniq e he), fun he => mem_singleton_iff.mp he ▸ heloop⟩
  have hvcl : v ∈ closure (F \ {v}) := by
    obtain ⟨a, b, hab⟩ := P.toGraph.exists_isLink_of_mem_edgeSet heloop
    have ha : a = v := mem_singleton_iff.mp (hV ▸ hab.left_mem)
    have hac : a ∈ closure (F \ {v}) :=
      (hab.2.2.2.symm ▸ (show a ∈ ({a, b} : Set S) from mem_insert a {b})).1
    exact ha ▸ hac
  refine ⟨P, hU, hV, hE, ?_⟩
  apply Subset.antisymm
  · simpa only [hU] using P.closure_subset_U heloop
  · intro x hx
    have hxP : x ∈ P.U := hU.symm ▸ hx
    rw [P.U_eq] at hxP
    rcases hxP with hxV | hxE
    · have hxv : x = v := mem_singleton_iff.mp (hV ▸ hxV)
      exact hxv.symm ▸ hvcl
    · obtain ⟨e, he, hxe⟩ := mem_iUnion₂.mp hxE
      have heq : e = F \ {v} := mem_singleton_iff.mp (hE ▸ he)
      exact heq ▸ hxe

end GraphMinor.GM08
