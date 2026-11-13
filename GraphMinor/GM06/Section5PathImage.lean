module

public import GraphMinor.GM06.Defs
import GraphMinor.GM06.Section4
import GraphMinor.GM11.Walks

/-!
# Images of path drawings under a map injective on the path

In Reduction 3 of VI, page 129, the suffix after the collapsed edge
is carried injectively to its new path. Map each link of the simple
walk and compose its parametrization with the continuous map. Only
injectivity on the original point set is needed.
-/

public section
namespace GraphMinor.GM06
open Set Topology GraphMinor.Surface

private theorem exists_image_walk
    {P Q : Drawing ClosedCylinder} {π : ClosedCylinder → ClosedCylinder}
    (hV : ∀ x ∈ P.V, π x ∈ Q.V)
    (hlink : ∀ e x y, P.toGraph.IsLink e x y →
      Q.toGraph.IsLink (π '' e) (π x) (π y))
    {s t : ClosedCylinder} (W : GraphWalk P.toGraph s t) :
    ∃ W' : GraphWalk Q.toGraph (π s) (π t),
      W'.support = W.support.map π ∧ W'.edges = W.edges.map (image π) := by
  induction W with
  | nil hv => exact ⟨.nil (hV _ hv), rfl, rfl⟩
  | cons hl R ih =>
    obtain ⟨R', hs, he⟩ := ih
    exact ⟨.cons (hlink _ _ _ hl) R', by simp [hs], by simp [he]⟩

/-- Exact image vertices and edges under a continuous map injective
on a path drawing's point set give another path drawing. -/
theorem isPathDrawing_image_of_injOn_pointSet
    {P Q : Drawing ClosedCylinder} {s t : ClosedCylinder}
    (hP : IsPathDrawing P s t) (π : C(ClosedCylinder, ClosedCylinder))
    (hi : InjOn π P.U)
    (hU : Q.U = π '' P.U) (hV : Q.V = π '' P.V)
    (hE : Q.E = (image π) '' P.E) :
    IsPathDrawing Q (π s) (π t) := by
  have hlink : ∀ e x y, P.toGraph.IsLink e x y →
      Q.toGraph.IsLink (π '' e) (π x) (π y) := by
    intro e x y hl
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [hE]; exact mem_image_of_mem (image π) hl.1
    · rw [hV]; exact mem_image_of_mem π hl.2.1
    · rw [hV]; exact mem_image_of_mem π hl.2.2.1
    · rw [hV, π.continuous.isClosedMap.closure_image_eq_of_continuous π.continuous,
        ← hi.image_inter (P.closure_subset_U hl.1) P.V_subset_U,
        hl.2.2.2, image_pair]
  constructor
  · obtain ⟨W, hW, hPV, hPE⟩ := hP.1
    obtain ⟨W', hs, he⟩ := exists_image_walk
      (fun x hx => hV.symm ▸ mem_image_of_mem π hx) hlink W
    refine ⟨W', ?_, ?_, ?_⟩
    · change W'.support.Nodup
      rw [hs]
      exact List.Nodup.map_on (fun x hx y hy hxy => hi
        (P.V_subset_U (hPV.symm ▸ hx)) (P.V_subset_U (hPV.symm ▸ hy)) hxy) hW
    · rw [hV, hPV, hs]
      ext x
      simp
    · rw [hE, hPE, he]
      ext e
      simp
  · obtain ⟨f, hf⟩ := hP.2
    refine ⟨π.comp f, ?_, ?_, congrArg π hf.2.2.1, congrArg π hf.2.2.2⟩
    · intro x y hxy
      exact hf.1 (hi (hf.2.1 ▸ mem_range_self x) (hf.2.1 ▸ mem_range_self y) hxy)
    · change range (π ∘ f) = Q.U
      rw [range_comp, hf.2.1, hU]

end GraphMinor.GM06
