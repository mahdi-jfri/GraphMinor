module

public import GraphMinor.GM06.Defs
import GraphMinor.GM06.Section5PuncturedEdgeConnected
import GraphMinor.GM11.Walks

/-!
# Edges attached to a retained punctured component

For the retained barrier in VI (5.5), page 130, begin with a
connected drawing away from the attachment and include every
selected edge having an endpoint there. Each punctured edge
closure remains connected to that drawing through its other end.
Their union is consequently connected after the attachment is removed.
-/

public section
namespace GraphMinor.GM06
open Set GraphMinor.Surface

/-- A connected retained component together with incident edge
closures stays connected after a different attachment vertex is removed. -/
theorem isConnected_union_punctured_incident_edges
    {S : Type} [TopologicalSpace S] [T2Space S] {G P : Drawing S}
    (hPG : P.IsSubdrawing G) (hP : IsConnected P.U)
    {s : S} (hs : s ∈ G.V) (hsP : s ∉ P.U)
    {E : Set (Set S)} (hEG : E ⊆ G.E)
    (hEP : ∀ e ∈ E, ∃ v ∈ P.V, v ∈ closure e) :
    IsConnected (P.U ∪ ⋃ e ∈ E, (closure e \ {s})) := by
  obtain ⟨a, ha⟩ := hP.nonempty
  refine ⟨⟨a, Or.inl ha⟩, isPreconnected_of_forall a ?_⟩
  intro x hx
  rcases hx with hxP | hxE
  · exact ⟨P.U, subset_union_left, ha, hxP, hP.isPreconnected⟩
  · obtain ⟨e, he, hxe⟩ := mem_iUnion₂.mp hxE
    obtain ⟨v, hvP, hvcl⟩ := hEP e he
    have hvs : v ≠ s := fun h => hsP (h ▸ P.V_subset_U hvP)
    have hvPiece : v ∈ closure e \ {s} := ⟨hvcl, hvs⟩
    have hpre := isPreconnected_closure_edge_diff_attachment G (hEG he) hs (hPG.1 hvP) hvcl hvs
    have hconn : IsConnected (P.U ∪ (closure e \ {s})) :=
      hP.union ⟨v, P.V_subset_U hvP, hvPiece⟩ ⟨⟨v, hvPiece⟩, hpre⟩
    refine ⟨P.U ∪ (closure e \ {s}), ?_, Or.inl ha, Or.inr hxe, hconn.isPreconnected⟩
    exact union_subset_union_right _ (fun y hy => mem_iUnion₂.mpr ⟨e, he, hy⟩)

end GraphMinor.GM06
