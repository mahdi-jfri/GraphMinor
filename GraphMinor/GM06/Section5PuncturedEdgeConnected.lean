module

public import GraphMinor.GM06.Defs
import GraphMinor.Surface.Fan

/-!
# Puncturing an edge at an attachment vertex

For the retained barrier in VI (5.5), page 130, every selected
edge has an endpoint in the retained component away from the
attachment. Removing the attachment leaves that edge closure
preconnected. A line loses at most one endpoint. A loop with the
other endpoint cannot contain the attachment as a different vertex.
-/

public section
namespace GraphMinor.GM06
open Set GraphMinor.Surface

/-- Removing a vertex from an edge closure leaves it preconnected
if the edge has another endpoint at a distinct vertex. -/
theorem isPreconnected_closure_edge_diff_attachment
    {S : Type} [TopologicalSpace S] [T2Space S] (G : Drawing S)
    {e : Set S} (he : e ∈ G.E) {s v : S}
    (hs : s ∈ G.V) (hv : v ∈ G.V) (hvcl : v ∈ closure e) (hvs : v ≠ s) :
    IsPreconnected (closure e \ {s}) := by
  rcases G.edge_cond e he with ⟨u, w, _, hcap, hline⟩ | ⟨u, hcap, hO⟩
  · by_cases hscl : s ∈ closure e
    · have hsend : s ∈ ({u, w} : Set S) := hcap ▸ ⟨hscl, hs⟩
      rcases hsend with rfl | hsw
      · exact hline.isPreconnected_diff_left
      · rw [mem_singleton_iff.mp hsw]
        exact hline.isPreconnected_diff_right
    · rw [sdiff_singleton_eq_self hscl]
      obtain ⟨j, _, _⟩ := hline
      exact (isConnected_iff_connectedSpace.mpr (j.surjective.connectedSpace j.continuous)).isPreconnected
  · have hvu : v = u := mem_singleton_iff.mp (show v ∈ ({u} : Set S) from hcap ▸ ⟨hvcl, hv⟩)
    have hscl : s ∉ closure e := by
      intro h
      have hsu : s = u := mem_singleton_iff.mp (show s ∈ ({u} : Set S) from hcap ▸ ⟨h, hs⟩)
      exact hvs (hvu.trans hsu.symm)
    rw [sdiff_singleton_eq_self hscl]
    obtain ⟨j⟩ := hO
    exact (isConnected_iff_connectedSpace.mpr (j.surjective.connectedSpace j.continuous)).isPreconnected

end GraphMinor.GM06
