module

public import GraphMinor.GM12.Section73CircuitVisitCount
import GraphMinor.GM12.Section73UnchangedCircuit
import GraphMinor.GM11.OArcCircuit
import GraphMinor.GM11.NiceSets
import GraphMinor.GM11.Restraints
import GraphMinor.GM11.Section6
import GraphMinor.GM11.Section7

/-!
# The closed-disc case of the tie walk selection

For the visit bounds used in XII (7.3), page 262, a tie that
is a closed disc needs only its boundary circuit. The boundary
lies in the drawing because the restraint is nice. Its circuit
is no longer than the restraint's shortest perimeter walk. The
restraint's outside condition forces the selected side of that
circuit to be this disc. A circuit walk then encloses the disc
and visits every vertex at most once.
-/

public section

namespace GraphMinor.GM12

open Set Topology Surface GM11

/-- A closed-disc restraint has an enclosing walk of no greater
length than its perimeter, with at most one visit to each vertex.
This proves the disc case of the tie selection used in XII
(7.3), page 262, after XI (9.2). -/
theorem exists_disc_restraint_walk_with_visit_bound
    {S : Type*} [TopologicalSpace S] [T2Space S] [ConnectedSpace S]
    (hS : IsClosedSurface S) {K : Drawing S} {k : ℕ} {ins : Drawing S → Set S}
    (hs : IsSlope K k ins) {X : Set S} (hX : IsRestraint K ins k X)
    (hDisc : IsClosedDisc X) :
    ∃ (a : S) (W : GraphWalk K.toGraph a a), W.length ≤ perimeterWalkLength K X ∧
      W.length < k ∧ X ⊆ insWalk ins K W ∧ ∀ v, walkVertexCount v W ≤ 1 := by
  let N := K.interSet (frontier X)
  have hNK : N.IsSubdrawing K := Drawing.span_isSubdrawing K _ _
  have hNU : N.U = frontier X := frontier_interSet hS hX.isClosed hX.isGammaNice
  have hfront : frontier X = discBd X := IsClosedDisc.frontier_eq_discBd hS hDisc
  have hFU : discBd X ⊆ K.U := by
    have hFN : discBd X ⊆ N.U := by rw [hNU, hfront]
    exact hFN.trans hNK.U_subset
  obtain ⟨C, hC, hCK, hCU⟩ := exists_circuit_of_oArc hDisc.isOArc_discBd hFU
  have hCN : C.IsSubdrawing N := isSubdrawing_of_U_subset_common hCK hNK
    (by rw [hCU, hNU, hfront])
  have hshort : C.length < k := hX.isConfined hS C hC hCN
  obtain ⟨u, P, _, hPlen, _, _, hPdraw⟩ := hX.exists_walk hS
  have hCP : C.IsSubdrawing (walkDrawing K P) := hPdraw.symm ▸ hCN
  have hClen : C.length ≤ perimeterWalkLength K X := by
    rw [← hPlen]
    apply (ncard_le_ncard (fun e he => ?_) P.edges.finite_toSet).trans (ncard_mem_list_le P.edges)
    have hem := hCP.2 he
    rwa [walkDrawing_E] at hem
  have hIns : ins C = X := by
    by_contra hne
    have hD := hs.isClosedDisc C hC hCK hshort
    have hbd : discBd (ins C) = discBd X := by
      rw [← IsClosedDisc.frontier_eq_discBd hS hD, ← subBd_eq_frontier,
        hs.subBd_eq C hC hCK hshort, hCU]
    have hcover := cover_of_discBd_eq hS hD hDisc hbd hne
    apply hX.compl_not_subset
    have hCB : C.IsSubdrawing (K.interSet (subBd X)) := by rw [subBd_eq_frontier]; exact hCN
    intro x hx
    have hxC : x ∈ ins C := (hcover.superset (mem_univ x)).resolve_right hx.2
    exact Or.inr (mem_iUnion₂.mpr ⟨C, ⟨hC, hCB⟩, hxC⟩)
  obtain ⟨a, W, hdraw, hlen, hcount⟩ := exists_circuit_walk_with_visit_bound hC hCK
  refine ⟨a, W, hlen ▸ hClen, hlen ▸ hshort, ?_, hcount⟩
  intro x hx
  have hCW : C.IsSubdrawing (walkDrawing K W) := hdraw.symm ▸ Drawing.IsSubdrawing.refl C
  exact Or.inr (mem_iUnion₂.mpr ⟨C, ⟨hC, hCW⟩, hIns.symm ▸ hx⟩)

end GraphMinor.GM12
