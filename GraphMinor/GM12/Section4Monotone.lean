module

public import GraphMinor.GM12.Defs
public import GraphMinor.Statement
import GraphMinor.GM12.Section4Minor
import GraphMinor.GM12.Section4ControlComposition
import GraphMinor.GM12.Section4EdgeLabels
import GraphMinor.Minor.Basic

/-!
# Graph Minors XII, (4.2): control passes to a target minor

Compose the controlled branch model with a model of the target minor.
Each new branch contains an old branch and the new target has no more
vertices, so the small-side exclusion is preserved.

The host edge-label type is assumed inhabited because `ControlsMinor`
uses total maps on ambient labels. `Section4AmbientEdges.lean` proves that this
assumption cannot be removed from that definition. The paper maps only
actual edges. An unused edge label on the intermediate target handles
its possible empty ambient edge type.
-/

public section

namespace GraphMinor.GM12

open Set Graph Hypergraph

/-- Graph Minors XII, (4.2), page 249. Control passes to any target minor.
The inhabited host edge-label assumption accounts for total edge maps
in `ControlsMinor`; it is automatic for drawings. -/
theorem theorem_4_2_proof {α β γ δ γ' δ' : Type*} [Nonempty β]
    {G : Graph α β} (hV : G.vertexSet.Finite) (hE : G.edgeSet.Finite)
    {L : Graph γ δ} {L' : Graph γ' δ'}
    (hV' : L'.vertexSet.Finite) (hE' : L'.edgeSet.Finite)
    (hminor : IsIsoMinor L L') {θ : ℕ}
    {T : Set (Hypergraph α β × Hypergraph α β)}
    (hc : ControlsMinor (Hypergraph.ofGraph G hV hE) θ T L') :
    ControlsMinor (Hypergraph.ofGraph G hV hE) θ T L := by
  obtain ⟨K, ⟨φ⟩, _, hVK, hEK⟩ := exists_option_edge_copy L' hV' hE'
  have hcK : ControlsMinor (Hypergraph.ofGraph G hV hE) θ T K :=
    controlsMinor_of_iso φ.symm hc
  have hminorK : IsIsoMinor L K := φ.isIsoMinor_right hminor
  obtain ⟨a, b, hm⟩ := exists_isMinorModel_of_isIsoMinor hVK hEK hminorK
  exact controlsMinor_of_target_model hV hE hm hVK hcK

end GraphMinor.GM12
