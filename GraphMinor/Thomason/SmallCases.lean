module

public import GraphMinor.GM13.Defs
public import GraphMinor.GM16.Defs
import GraphMinor.GM13.Section7FourProof

/-!
# The one-vertex case of Thomason's bound

Every non-null graph has a model of `K₁`, including when its ambient edge
type is empty. No edge map value is needed because `K₁` has no edges.
-/

public section

namespace GraphMinor.Thomason

open Graph GraphMinor.GM13 GraphMinor.GM16

/-- A non-null graph contains a model of `K₁` without any assumption on its
ambient edge type. This verifies the `p = 1` conclusion of XIII (5.5). -/
theorem hasGraphModel_completeGraph_one {α β : Type*} (G : Graph α β)
    (hne : V(G).Nonempty) : HasGraphModel (completeGraph 1) G := by
  obtain ⟨a, ha⟩ := hne
  exact hasGraphModel_completeGraph_of_le_one ha le_rfl

/-- The one-vertex graph with empty edge type has a model of `K₁`. -/
theorem hasGraphModel_completeGraph_one_noEdge :
    HasGraphModel (completeGraph 1) (Graph.noEdge Set.univ Empty : Graph Unit Empty) := by
  exact hasGraphModel_completeGraph_one _ ⟨(), Set.mem_univ _⟩

end GraphMinor.Thomason
