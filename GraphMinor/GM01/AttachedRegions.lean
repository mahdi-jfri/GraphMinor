module

public import GraphMinor.GM01.VertexAvoidanceRegions
public import GraphMinor.GM09.Basic

/-!
# Avoidance regions after adjoining the root path

In the graph on page 55 of Graph Minors I, the root path meets the
subdivided comb at one vertex. If that attachment is outside an avoidance
region of the comb, adjoining the path cannot enlarge that region.
Any first edge entering the added path would have to use its attachment.
This lets the spine regions be computed in the comb alone.
-/

public section

namespace GraphMinor.GM01

open Set Graph GraphMinor.GM09

/-- Adding a subgraph attached outside an avoidance region leaves that
region unchanged. The intersection assumption states where the added
subgraph is attached, rather than assuming the desired reachability fact. -/
theorem vertexAvoidanceRegion_subgraphUnion_eq {α β : Type*} {G N R : Graph α β}
    (hN : N ≤ G) (hR : R ≤ G) {last cut attach : α}
    (hlast : last ∈ V(N)) (hne : last ≠ cut)
    (hmeet : V(N) ∩ V(R) ⊆ {attach})
    (hattach : attach ∉ vertexAvoidanceRegion N last cut) :
    vertexAvoidanceRegion (subgraphUnion G N R) last cut =
      vertexAvoidanceRegion N last cut := by
  let H := subgraphUnion G N R
  have hNH : N ≤ H := le_subgraphUnion_left hN hR
  have hRH : R ≤ H := le_subgraphUnion_right hN hR
  have hstart := last_mem_vertexAvoidanceRegion hlast hne
  have step : ∀ {x y}, x ∈ vertexAvoidanceRegion N last cut →
      (H.deleteVerts {cut}).Adj x y →
      (N.deleteVerts {cut}).Adj x y := by
    intro x y hx hxy
    obtain ⟨e, he⟩ := hxy
    have hHlink := he.mono Graph.deleteVerts_le
    have hedge := hHlink.edge_mem
    rw [edgeSet_subgraphUnion hN hR] at hedge
    rcases hedge with heN | heR
    · have hlink := (hNH.isLink_iff heN).mpr hHlink
      have hdel := (H.deleteVerts_isLink {cut}).mp he
      exact ⟨e, (N.deleteVerts_isLink {cut}).mpr ⟨hlink, hdel.2⟩⟩
    · have hRlink := (hRH.isLink_iff heR).mpr hHlink
      have hxN := (vertexAvoidanceRegion_subset N last cut hx).1
      have heq : x = attach := hmeet ⟨hxN, hRlink.left_mem⟩
      exact False.elim (hattach (heq ▸ hx))
  apply Subset.antisymm
  · intro x hx
    have lift : ∀ {y}, Relation.ReflTransGen (H.deleteVerts {cut}).Adj last y →
        y ∈ vertexAvoidanceRegion N last cut := by
      intro y hr
      induction hr with
      | refl => exact hstart
      | tail hr hxy ih =>
        obtain ⟨e, he⟩ := step ih hxy
        exact ⟨he.right_mem, ih.2.tail ⟨e, he⟩⟩
    exact lift hx.2
  · intro x hx
    have hmono : ∀ {a b}, (N.deleteVerts {cut}).Adj a b →
        (H.deleteVerts {cut}).Adj a b := by
      intro a b hab
      obtain ⟨e, he⟩ := hab
      obtain ⟨hlink, ha, hb⟩ := (N.deleteVerts_isLink {cut}).mp he
      exact ⟨e, (H.deleteVerts_isLink {cut}).mpr ⟨hlink.mono hNH, ha, hb⟩⟩
    refine ⟨?_, Relation.ReflTransGen.mono (fun _ _ h ↦ hmono h) last x hx.2⟩
    have hmem := hx.1
    rw [vertexSet_deleteVerts] at hmem ⊢
    exact ⟨hNH.vertexSet_mono hmem.1, hmem.2⟩

end GraphMinor.GM01
