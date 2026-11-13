module

public import GraphMinor.GM12.Section73CircuitVisitCount
import GraphMinor.GM11.NiceSets
import GraphMinor.GM11.Restraints

/-!
# The point case of the tie walk selection

For the visit bounds used in XII (7.3), page 262, a singleton
tie needs a zero-edge walk at its unique point. A shortest
perimeter walk exists for the restraint. Its point set lies in
the restraint's frontier and hence in this singleton. It cannot
use an edge, since an edge's interior misses the drawing vertices
and the initial vertex already occupies the singleton. Thus its
length and all departure counts are zero.
-/

public section

namespace GraphMinor.GM12

open Set Topology Surface GM11

/-- A one-point restraint is enclosed by a zero-edge walk. This
proves the point case of the tie selection used in XII (7.3),
page 262, after XI (9.2). -/
theorem exists_point_restraint_walk_with_visit_bound
    {S : Type*} [TopologicalSpace S] [T2Space S] [ConnectedSpace S]
    (hS : IsClosedSurface S) {K : Drawing S} {k : ℕ} {ins : Drawing S → Set S}
    {X : Set S} (hX : IsRestraint K ins k X) (hsub : X.Subsingleton) :
    ∃ (a : S) (W : GraphWalk K.toGraph a a), W.length = 0 ∧
      W.length ≤ perimeterWalkLength K X ∧ W.length < k ∧
      X ⊆ insWalk ins K W ∧ ∀ v, walkVertexCount v W = 0 := by
  obtain ⟨a, W, _, hlen, hshort, _, hdraw⟩ := hX.exists_walk hS
  have hWU : (walkDrawing K W).U ⊆ X := by
    rw [hdraw, frontier_interSet hS hX.isClosed hX.isGammaNice]
    exact hX.isClosed.frontier_subset
  have haV : a ∈ (walkDrawing K W).V := by rw [walkDrawing_V]; exact W.start_mem_support
  have haU : a ∈ (walkDrawing K W).U := (walkDrawing K W).V_subset_U haV
  have haX : a ∈ X := hWU haU
  have haK : a ∈ K.V := W.mem_vertexSet_of_mem_support W.start_mem_support
  have hEdges : W.edges = [] := by
    apply List.eq_nil_iff_forall_not_mem.mpr
    intro e he
    have heW : e ∈ (walkDrawing K W).E := by rw [walkDrawing_E]; exact he
    have heK := (walkDrawing_isSubdrawing K W).2 heW
    obtain ⟨x, hxe⟩ := heK.1
    have hxU : x ∈ (walkDrawing K W).U := (heW.2.1 hxe).1
    have hxa : x = a := hsub (hWU hxU) haX
    exact (heK.2.1 hxe).2 (hxa.symm ▸ haK)
  have hzero : W.length = 0 := congrArg List.length hEdges
  refine ⟨a, W, hzero, hlen.le, hshort, ?_, ?_⟩
  · intro x hx
    have hxa : x = a := hsub hx haX
    exact Or.inl (hxa.symm ▸ haU)
  · intro v
    cases hcase : W with
    | nil h => rfl
    | cons h R => rw [hcase, GraphWalk.length_cons] at hzero; omega

end GraphMinor.GM12
