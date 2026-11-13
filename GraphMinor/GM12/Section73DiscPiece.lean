module

public import GraphMinor.GM11.Defs
import GraphMinor.GM12.Section73UnchangedCircuit
import GraphMinor.GM11.OArcCircuit
import GraphMinor.GM11.NiceSets
import GraphMinor.GM11.Restraints
import GraphMinor.GM11.Section6
import GraphMinor.GM11.Section7

/-!
# Selected sides of disc pieces of a tie

In the tie argument used in XII (7.3), page 262, the boundary of
each disc piece is a circuit of the perimeter drawing. Its selected
side is the disc piece itself. Otherwise its selected side together
with the piece covers the surface, putting the entire outside of
the restraint inside its perimeter drawing. This contradicts the
outside condition in the definition of a restraint.
-/

public section

namespace GraphMinor.GM12

open Set Topology Surface GM11

/-- A disc contained in a restraint, with its boundary in the
restraint's frontier, is the selected side of its boundary circuit.
This supplies the disc pieces for the tie walks in XII (7.3). -/
theorem exists_selected_boundary_circuit_of_disc_piece
    {S : Type*} [TopologicalSpace S] [T2Space S] [ConnectedSpace S]
    (hS : IsClosedSurface S) {K : Drawing S} {k : ℕ} {ins : Drawing S → Set S}
    (hs : IsSlope K k ins) {X D : Set S} (hX : IsRestraint K ins k X)
    (hD : IsClosedDisc D) (hDX : D ⊆ X) (hBD : discBd D ⊆ frontier X) :
    ∃ C : Drawing S, C.IsCircuit ∧ C.IsSubdrawing (K.interSet (frontier X)) ∧
      C.U = discBd D ∧ C.length < k ∧ ins C = D := by
  let N := K.interSet (frontier X)
  have hNK : N.IsSubdrawing K := Drawing.span_isSubdrawing K _ _
  have hNU : N.U = frontier X := frontier_interSet hS hX.isClosed hX.isGammaNice
  have hBU : discBd D ⊆ N.U := hNU.symm ▸ hBD
  obtain ⟨C, hC, hCN, hCU⟩ := exists_circuit_of_oArc hD.isOArc_discBd hBU
  have hCK := hCN.trans hNK
  have hshort : C.length < k := hX.isConfined hS C hC hCN
  refine ⟨C, hC, hCN, hCU, hshort, ?_⟩
  by_contra hne
  have hI := hs.isClosedDisc C hC hCK hshort
  have hbd : discBd (ins C) = discBd D := by
    rw [← IsClosedDisc.frontier_eq_discBd hS hI, ← subBd_eq_frontier,
      hs.subBd_eq C hC hCK hshort, hCU]
  have hcover := cover_of_discBd_eq hS hI hD hbd hne
  apply hX.compl_not_subset
  have hCB : C.IsSubdrawing (K.interSet (subBd X)) := by rw [subBd_eq_frontier]; exact hCN
  intro x hx
  have hxC : x ∈ ins C := (hcover.superset (mem_univ x)).resolve_right (fun hxD => hx.2 (hDX hxD))
  exact Or.inr (mem_iUnion₂.mpr ⟨C, ⟨hC, hCB⟩, hxC⟩)

end GraphMinor.GM12
