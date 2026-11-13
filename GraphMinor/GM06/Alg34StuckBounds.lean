module

public import GraphMinor.Compute.GM06Alg34StuckBounds
public import GraphMinor.GM06.Alg34FiniteCounts
import GraphMinor.GM06.Alg34SingletonExhaustCorrect

/-!
# Geometric bounds justified by exhausted finite searches

A non-null input with no interior component has a supplied cuff vertex,
which the representation places on the actual boundary. A division
covering that boundary has a nonempty finite union. If singleton search
also fails and the graph is connected, the finite graph has an edge.
These are the local conditions required for dual progress and edge loss.
-/

public section
namespace GraphMinor.Compute.GM06DrawingRep

open Set Surface GM06
universe u
variable {S : Type u} [TopologicalSpace S] [T1Space S]
  {x : GM06DrawingData} {G : Drawing S} {Δ : Set (Set S)}

/-- Exhausting interior component search in a non-null graph forces a boundary vertex. -/
theorem boundary_nonempty_of_no_interior (h : GM06DrawingRep x G Δ)
    (hn : 0 < x.n) (hfind : x.findInteriorComponent = none) :
    (G.V ∩ bd S).Nonempty := by
  obtain ⟨L, hL, b, hb⟩ := x.cuff_vertex_of_no_interior hn hfind
  obtain ⟨i, hi, heq⟩ := List.mem_iff_getElem.mp hL
  let c : Fin x.cuffs.length := ⟨i, hi⟩
  have hmem : b ∈ x.cuffs[c] := by change b ∈ x.cuffs[i]; rw [heq]; exact hb
  have himage : (h.vertex b).val ∈
      (fun v => (h.vertex v).val) '' GM06DrawingData.block x.cuffs[c] := ⟨b, hmem, rfl⟩
  have hpC := ((h.cuff_vertices c) ▸ himage).2
  have hpbd : (h.vertex b).val ∈ bd S :=
    (sUnion_cuffs (S := S)) ▸ (show (h.vertex b).val ∈ ⋃₀ cuffs S from
      ⟨_, (h.cuff c).property, hpC⟩)
  exact ⟨(h.vertex b).val, (h.vertex b).property, hpbd⟩

/-- A nonempty interpreted division union has a nonempty finite union. -/
theorem divisionUnion_nonempty (h : GM06DrawingRep x G Δ)
    (hne : (divisionUnion Δ).Nonempty) : (divisionUnion x.divisionSet).Nonempty := by
  obtain ⟨p, B, hB, hp⟩ := hne
  obtain ⟨L, hL, heq⟩ := h.division.subset hB
  obtain ⟨v, hv, _⟩ := heq.symm ▸ hp
  exact ⟨v, GM06DrawingData.block L, ⟨L, hL, rfl⟩, hv⟩

/-- The connected non-null state with exhausted interior and singleton
searches has an edge, as required to charge its dual singleton deletion. -/
theorem edges_pos_of_stuck (h : GM06DrawingRep x G Δ)
    (hc : IsGraphConnected G.toGraph) (hbd : divisionUnion Δ = G.V ∩ bd S)
    (hn : 0 < x.n) (hI : x.findInteriorComponent = none)
    (hS : gm06FindSingleton x.division = none) : 0 < x.ends.length := by
  have hb := h.boundary_nonempty_of_no_interior hn hI
  have hd : (divisionUnion Δ).Nonempty := hbd.symm ▸ hb
  exact x.edges_pos_of_no_singleton (h.vertexGraph_preconnected hc) (h.divisionUnion_nonempty hd) hS

end GraphMinor.Compute.GM06DrawingRep
