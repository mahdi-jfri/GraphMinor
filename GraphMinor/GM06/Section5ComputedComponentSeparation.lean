module

public import GraphMinor.GM06.Section5ComputedComponentPort
public import GraphMinor.GM06.Section5VertexSeparation

/-!
# Constructing the separation found by the component scan

For Reduction 2 in VI (5.7), page 133, retain the drawing induced
on vertices outside the computed component. Its attachment property
gives a separation with at most the removed vertex in the overlap.
The live source is removed, so the retained graph is strictly smaller.
Linkage preservation is checked from the protected-vertex test.
-/

public section
namespace GraphMinor.GM06
open Set GraphMinor.Surface GraphMinor.Compute
universe u

/-- A live computed component yields an actual separation and a
strictly smaller retained graph. The finite representation supplies
only vertex labels, active edge labels, and their exact links. -/
theorem exists_separation_of_computed_punctured_component
    {S : Type u} [TopologicalSpace S] [T1Space S] {n : ℕ} (G : Drawing S)
    (tagged : List ((Fin n × Fin n) × ℕ)) (vertex : Fin n ↪ S)
    (edge : Fin tagged.length → Set S)
    (hlinks : ∀ j : Fin tagged.length, tagged[j].2 = 1 →
      G.toGraph.IsLink (edge j) (vertex tagged[j].1.1) (vertex tagged[j].1.2))
    (hcover : ∀ e ∈ G.E, ∃ j : Fin tagged.length, tagged[j].2 = 1 ∧ edge j = e)
    (cut source : Fin n) (hsource : source ≠ cut) (hsourceV : vertex source ∈ G.V) :
    let X := vertex '' {r | (gm06PuncturedGraphData tagged cut).vertexGraph.Reachable source r} ∩ G.V
    ∃ T : Drawing S,
      IsGraphSeparation G.toGraph (induceDrawing G (G.V \ X)).toGraph T.toGraph ∧
      (induceDrawing G (G.V \ X)).V ∩ T.V ⊆ {vertex cut} ∧
      (induceDrawing G (G.V \ X)).toGraph ≠ G.toGraph := by
  let X := vertex '' {r | (gm06PuncturedGraphData tagged cut).vertexGraph.Reachable source r} ∩ G.V
  have hX : X ⊆ G.V := inter_subset_right
  have hport := computed_punctured_component_port G.toGraph tagged vertex edge hlinks hcover cut source hsource
  obtain ⟨T, hsep, hsepV⟩ := exists_separation_of_set_attached_at_vertex G hX hport
  refine ⟨T, hsep, hsepV, ?_⟩
  have hsX : vertex source ∈ X :=
    ⟨⟨source, SimpleGraph.Reachable.refl _, rfl⟩, hsourceV⟩
  intro heq
  have hV : (induceDrawing G (G.V \ X)).V = G.V := congrArg Graph.vertexSet heq
  have hsV : vertex source ∈ (induceDrawing G (G.V \ X)).V := hV.symm ▸ hsourceV
  rw [induceDrawing_V G sdiff_subset] at hsV
  exact hsV.2 hsX

end GraphMinor.GM06
