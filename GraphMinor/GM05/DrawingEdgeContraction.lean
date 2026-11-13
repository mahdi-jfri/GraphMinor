module

public import GraphMinor.Surface.TopologyStatements
import GraphMinor.GM05.DrawingEdgeCollapse
import GraphMinor.GM11.Forest
import GraphMinor.GM11.Section5
import GraphMinor.GM19.Section6a

/-!
# Contracting any edge of a surface drawing

For the contraction step in GM V, (8.14), a nonloop edge is collapsed
by the surface arc-collapse theorem. A loop is simply deleted. Both
operations have the same endpoint description, since a loop has just
one endpoint. The remaining open edges correspond bijectively, even
when contractions create new loops.
-/

public section
namespace GraphMinor.GM05
open Set Topology Surface GM11

/-- One-edge contraction for the drawing argument of GM V, (8.14),
page 113. No loop-free or parallel-edge condition is required. -/
theorem exists_drawing_contract_edge {S : Type} [TopologicalSpace S]
    (hS : IsClosedSurface S) (D : Drawing S) {f : Set S} (hf : f∈D.E) :
    ∃ (D' : Drawing S) (π : S → S),Continuous π ∧
      D'.U=π '' (D.U\f) ∧ D'.V=π '' D.V ∧
      (∀ x∈D.V,∀ y∈D.V,π x=π y ↔ x=y ∨ (x∈tilde f ∧ y∈tilde f)) ∧
      BijOn (image π) (D.E\{f}) D'.E ∧
      ∀ e∈D.E,e≠f → tilde (π '' e)=π '' tilde e := by
  let : T2Space S := hS.2.1
  rcases D.edge_cond f hf with ⟨u,v,-,-,hline⟩|⟨u,hcap,-⟩
  · exact exists_drawing_collapse_nonloop hS D hf hline
  · have htilde : tilde f={u} := (GM19.tilde_eq_inter_V D hf).trans hcap
    refine ⟨D.deleteEdge f,id,continuous_id,?_,?_,?_,?_,?_⟩
    · simpa only [image_id] using deleteEdge_U D hf
    · simpa only [image_id] using deleteEdge_V D f
    · intro x _ y _
      simp only [id_eq,htilde,mem_singleton_iff]
      constructor
      · exact Or.inl
      · rintro (rfl|⟨rfl,rfl⟩) <;> rfl
    · have him : (image (id : S → S))=(id : Set S → Set S) := funext fun s ↦ image_id s
      rw [him,deleteEdge_E]
      exact bijOn_id _
    · intro e _ _
      simp only [image_id]

end GraphMinor.GM05
