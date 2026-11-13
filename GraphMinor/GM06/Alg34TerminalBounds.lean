module

public import GraphMinor.Compute.GM06Alg34TerminalBounds
public import GraphMinor.GM06.Alg34ComponentRep

/-!
# Connectivity justified by the canonical component count

Reachability in the supplied endpoint graph is exactly existence of a
walk between the interpreted vertices. If that graph is preconnected
and nonempty, the drawing graph is connected. In particular, the
single-root case tested by the driver permits passage to the disc dual.
-/

public section
namespace GraphMinor.Compute.GM06DrawingRep

open Set Surface GM06
universe u
variable {S : Type u} [TopologicalSpace S] [T1Space S]
  {x : GM06DrawingData} {G : Drawing S} {Δ : Set (Set S)}

/-- Finite preconnectedness and a positive vertex count imply actual graph connectivity. -/
theorem connected_of_vertexGraph_preconnected (h : GM06DrawingRep x G Δ)
    (hn : 0 < x.n) (hc : x.vertexGraph.Preconnected) : IsGraphConnected G.toGraph := by
  refine ⟨⟨(h.vertex ⟨0, hn⟩).val, (h.vertex ⟨0, hn⟩).property⟩, ?_⟩
  intro u hu v hv
  let a := h.vertex.symm ⟨u, hu⟩
  let b := h.vertex.symm ⟨v, hv⟩
  have ha : (h.vertex a).val = u := congrArg Subtype.val (h.vertex.apply_symm_apply ⟨u, hu⟩)
  have hb : (h.vertex b).val = v := congrArg Subtype.val (h.vertex.apply_symm_apply ⟨v, hv⟩)
  simpa only [ha, hb] using (h.vertex_reachable_iff a b).mp (hc a b)

/-- The non-null single-root branch of the finite driver is an actual connected drawing. -/
theorem connected_of_roots_length_le_one (h : GM06DrawingRep x G Δ)
    (hn : 0 < x.n) (hk : x.componentRoots.length ≤ 1) : IsGraphConnected G.toGraph :=
  h.connected_of_vertexGraph_preconnected hn (x.preconnected_of_roots_length_le_one hk)

end GraphMinor.Compute.GM06DrawingRep
