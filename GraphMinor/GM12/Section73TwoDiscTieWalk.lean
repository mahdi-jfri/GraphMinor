module

public import GraphMinor.GM12.Section73CircuitJoin
public import GraphMinor.GM12.Section73DiscPiece
import GraphMinor.GM12.Section73TieBoundary
import GraphMinor.GM12.Section77
import GraphMinor.GM12.Section73UnchangedCircuit
import GraphMinor.GM11.NiceSets
import GraphMinor.GM11.Restraints
import GraphMinor.GM11.Section6
import GraphMinor.GM11.Ties

/-!
# The two-disc case of the tie walk selection

For the two-disc tie used in XII (7.3), page 262, read both
boundary circuits from their common point and concatenate them.
The common point is on both boundaries and is a radial vertex.
The selected side of each boundary circuit is its disc. Since
the circuits have disjoint edge sets in the perimeter drawing,
the combined walk has no greater length than the perimeter. It
visits every vertex at most twice.
-/

public section

namespace GraphMinor.GM12

open Set Topology Surface GM11

/-- The boundary of either disc in a union meeting at one point
lies on the boundary of that union, including the attachment. -/
theorem disc_boundary_subset_frontier_union_of_singleton_inter
    {S : Type*} [TopologicalSpace S] [T2Space S] [ConnectedSpace S]
    (hS : IsClosedSurface S) {D E : Set S} {p : S}
    (hD : IsClosedDisc D) (hE : IsClosedDisc E) (hDE : D ∩ E = {p}) :
    discBd D ⊆ frontier (D ∪ E) := by
  apply oArc_subset_of_frontier_union_of_finite_attachment hE.isCompact.isClosed
    isClosed_frontier (by rw [IsClosedDisc.frontier_eq_discBd hS hD]) hD.isOArc_discBd
  · apply (finite_singleton p).subset
    intro x hx
    exact hDE ▸ (⟨Surface.discBd_subset D hx.1, hx.2⟩ : x ∈ D ∩ E)
  · exact Subset.rfl

/-- A restraint that is a union of two discs meeting in one point
has an enclosing walk no longer than its perimeter and with at
most two visits to each vertex. This is the fourth tie shape in
the XI (9.2) selection used by XII (7.3), page 262. -/
theorem exists_two_disc_restraint_walk_with_visit_bound
    {S : Type*} [TopologicalSpace S] [T2Space S] [ConnectedSpace S]
    (hS : IsClosedSurface S) {K : Drawing S} {k : ℕ} {ins : Drawing S → Set S}
    (hs : IsSlope K k ins) {D E : Set S} {p : S}
    (hX : IsRestraint K ins k (D ∪ E))
    (hD : IsClosedDisc D) (hE : IsClosedDisc E) (hDE : D ∩ E = {p}) :
    ∃ W : GraphWalk K.toGraph p p, W.length ≤ perimeterWalkLength K (D ∪ E) ∧
      W.length < k ∧ D ∪ E ⊆ insWalk ins K W ∧
      ∀ v, walkVertexCount v W ≤ 2 := by
  have hBD := disc_boundary_subset_frontier_union_of_singleton_inter hS hD hE hDE
  have hBE : discBd E ⊆ frontier (D ∪ E) := by
    rw [union_comm]
    exact disc_boundary_subset_frontier_union_of_singleton_inter hS hE hD (inter_comm D E ▸ hDE)
  obtain ⟨C, hC, hCN, hCU, _, hCI⟩ := exists_selected_boundary_circuit_of_disc_piece
    hS hs hX hD subset_union_left hBD
  obtain ⟨F, hF, hFN, hFU, _, hFI⟩ := exists_selected_boundary_circuit_of_disc_piece
    hS hs hX hE subset_union_right hBE
  have hNK : (K.interSet (frontier (D ∪ E))).IsSubdrawing K := Drawing.span_isSubdrawing K _ _
  have hCK := hCN.trans hNK
  have hFK := hFN.trans hNK
  have hCF : C.U ∩ F.U ⊆ {p} := by
    rw [hCU, hFU]
    intro x hx
    exact hDE ▸ (⟨Surface.discBd_subset D hx.1, Surface.discBd_subset E hx.2⟩ : x ∈ D ∩ E)
  obtain ⟨hpD, hpE⟩ := disc_attachment_mem_boundaries hS hD hE hDE
  have hpC : p ∈ C.U := hCU.symm ▸ hpD
  have hpF : p ∈ F.U := hFU.symm ▸ hpE
  have hpK := mem_vertices_of_subdrawing_inter_singleton hCK hFK hpC hpF hCF
  have hpCV : p ∈ C.V := isSubdrawing_U_inter_V hCK ▸ (⟨hpC, hpK⟩ : p ∈ C.U ∩ K.V)
  have hpFV : p ∈ F.V := isSubdrawing_U_inter_V hFK ▸ (⟨hpF, hpK⟩ : p ∈ F.U ∩ K.V)
  obtain ⟨P, hPdraw, hPlen, hPcount⟩ := exists_circuit_walk_at_with_visit_bound hC hCK hpCV
  obtain ⟨Q, hQdraw, hQlen, hQcount⟩ := exists_circuit_walk_at_with_visit_bound hF hFK hpFV
  obtain ⟨u, R, _, hRlen, hRshort, _, hRdraw⟩ := hX.exists_walk hS
  have hCR : C.IsSubdrawing (walkDrawing K R) := hRdraw.symm ▸ hCN
  have hFR : F.IsSubdrawing (walkDrawing K R) := hRdraw.symm ▸ hFN
  have hdis : Disjoint C.E F.E := disjoint_edges_of_subsingleton_inter hCK hFK
    (fun x hx y hy => (hCF hx).trans (hCF hy).symm)
  have hlen : (P.append Q).length ≤ perimeterWalkLength K (D ∪ E) := by
    rw [GraphWalk.length_append, hPlen, hQlen, ← hRlen]
    exact circuit_lengths_add_le_walk_length R hCR hFR hdis
  have hCjoin : C.IsSubdrawing (walkDrawing K (P.append Q)) := by
    rw [← hPdraw]
    apply walkDrawing_mono
    · intro x hx; exact (GraphWalk.mem_support_append _ _).mpr (Or.inl hx)
    · intro e he; rw [GraphWalk.edges_append]; exact List.mem_append_left _ he
  have hFjoin : F.IsSubdrawing (walkDrawing K (P.append Q)) := by
    rw [← hQdraw]
    apply walkDrawing_mono
    · intro x hx; exact (GraphWalk.mem_support_append _ _).mpr (Or.inr hx)
    · intro e he; rw [GraphWalk.edges_append]; exact List.mem_append_right _ he
  refine ⟨P.append Q, hlen, hlen.trans_lt (hRlen ▸ hRshort), ?_, ?_⟩
  · intro x hx
    rcases hx with hx | hx
    · exact Or.inr (mem_iUnion₂.mpr ⟨C, ⟨hC, hCjoin⟩, hCI.symm ▸ hx⟩)
    · exact Or.inr (mem_iUnion₂.mpr ⟨F, ⟨hF, hFjoin⟩, hFI.symm ▸ hx⟩)
  · intro v
    rw [walkVertexCount_append]
    have hp := hPcount v
    have hq := hQcount v
    omega

end GraphMinor.GM12
