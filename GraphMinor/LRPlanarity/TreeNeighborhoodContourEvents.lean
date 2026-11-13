module

public import GraphMinor.LRPlanarity.DefsContour
import Mathlib.Data.Fintype.Sum

/-!
# Finite local contour incidence lists

Part IV, opening and Section 7b of the planarity note orders the child
incidences and the source and target ports at each vertex. There are
finitely many such events. Listing the legal events once gives an initial
valid local order. Boundary traversal can then replace each local list
by a permutation in the required cyclic order.
-/

public section
namespace GraphMinor.LRPlanarity

instance instFiniteContourEvent (N : ℕ) : Finite (ContourEvent N) := by
  let encode : ContourEvent N → Fin N ⊕ (Arc N × Bool) := fun e => match e with
    | .child w => Sum.inl w
    | .port p => Sum.inr (p.edge,p.source)
  apply Finite.of_injective encode
  intro e f he
  cases e with
  | child w =>
    cases f with
    | child z =>
      have hwz : w = z := Sum.inl.inj he
      exact congrArg ContourEvent.child hwz
    | port p => cases he
  | port p =>
    cases f with
    | child w => cases he
    | port q =>
      have hpq : (p.edge,p.source) = (q.edge,q.source) := Sum.inr.inj he
      cases p with
      | mk e side =>
        cases q with
        | mk f side' =>
          change (e,side) = (f,side') at hpq
          cases hpq
          rfl

/-- Every finite parent relation and graph have valid local incidence
lists. This assertion orders no contours and imposes no nonalternation. -/
theorem exists_validContourOrder {N : ℕ} (T : Forest N) (G : SimpleGraph (Fin N)) :
    ∃ order : ContourOrder N, ValidContourOrder T G order := by
  classical
  let legal := fun v (event : ContourEvent N) => match event with
    | .child w => T.parent w = some v
    | .port p => T.BackEdge G p.edge ∧ (if p.source then p.edge.1 = v else p.edge.2 = v)
  let order := fun v => (Set.toFinite {event | legal v event}).toFinset.toList
  refine ⟨order,?_⟩
  intro v
  constructor
  · simp only [order,Finset.nodup_toList]
  · intro event
    change event ∈ (Set.toFinite {e | legal v e}).toFinset.toList ↔ legal v event
    simp only [Finset.mem_toList,Set.Finite.mem_toFinset,Set.mem_ofPred_eq]

end GraphMinor.LRPlanarity
