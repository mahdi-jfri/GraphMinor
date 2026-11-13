module

public import GraphMinor.GM12.Section73LineWalk
import GraphMinor.GM11.RadialChord
import GraphMinor.GM11.NiceSets
import GraphMinor.GM11.Restraints
import GraphMinor.GM11.Section4c

/-!
# The line case of the tie walk selection

For XII (7.3), page 262, a line-shaped tie can be enclosed by a
walk visiting every vertex at most twice, and either end at most
once. A line in a surface has empty interior, since it is the
point set of a one-edge drawing. The shortest perimeter walk of
the restraint therefore has precisely the line as its point set.
We replace this walk by a shortest path along the line and back.
-/

public section

namespace GraphMinor.GM12

open Set Topology Surface GM11

/-- A line in a closed surface has empty interior: view it as a
one-edge drawing and use the empty interior of drawings. -/
theorem line_interior_eq_empty
    {S : Type*} [TopologicalSpace S] [T2Space S] [ConnectedSpace S]
    (hS : IsClosedSurface S) {L : Set S} {a b : S}
    (hLine : IsLineWithEnds L a b) : interior L = ∅ := by
  have hab : a ≠ b := by
    obtain ⟨e, he0, he1⟩ := hLine
    intro he
    have h01 : (0 : unitInterval) = 1 := e.injective (Subtype.ext (he0.trans (he.trans he1.symm)))
    exact zero_ne_one h01
  apply not_nonempty_iff_eq_empty.mp
  intro hne
  obtain ⟨x, hx, hxU⟩ := exists_notMem_U (Γ := lineDrawing hLine hab) hS isOpen_interior hne
  exact hxU (interior_subset hx)

/-- A line restraint admits a closed walk of no greater length
than its perimeter, enclosing it with at most two visits to each
vertex and at most one visit to either end. This is the line case
of the tie selection used by XII (7.3), page 262. -/
theorem exists_line_restraint_walk_with_visit_bound
    {S : Type*} [TopologicalSpace S] [T2Space S] [ConnectedSpace S]
    (hS : IsClosedSurface S) {K : Drawing S} {k : ℕ} {ins : Drawing S → Set S}
    {X : Set S} {a b : S} (hX : IsRestraint K ins k X)
    (hLine : IsLineWithEnds X a b) :
    ∃ W : GraphWalk K.toGraph a a, W.length ≤ perimeterWalkLength K X ∧
      W.length < k ∧ X ⊆ insWalk ins K W ∧
      (∀ v, walkVertexCount v W ≤ 2) ∧
      (∀ v, v = a ∨ v = b → walkVertexCount v W ≤ 1) := by
  obtain ⟨u, P, _, hlen, hshort, _, hdraw⟩ := hX.exists_walk hS
  have hfront : frontier X = X := by
    change closure X \ interior X = X
    rw [hX.isClosed.closure_eq, line_interior_eq_empty hS hLine, sdiff_empty]
  have hPU : (walkDrawing K P).U = X := by
    rw [hdraw, frontier_interSet hS hX.isClosed hX.isGammaNice, hfront]
  obtain ⟨W, hWP, hWU, hcount, hends⟩ := exists_line_walk_with_visit_bound P (hPU.symm ▸ hLine)
  refine ⟨W, hWP.trans_eq hlen, hWP.trans_lt hshort, ?_, hcount, hends⟩
  intro x hx
  exact Or.inl (hWU.symm ▸ (hPU.symm ▸ hx))

end GraphMinor.GM12
