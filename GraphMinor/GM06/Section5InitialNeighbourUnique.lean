module

public import GraphMinor.GM06.Defs
import GraphMinor.GM06.Section4PathTools
import GraphMinor.GM06.Section5Red
import GraphMinor.GM11.Walks

/-!
# The initial leaf has one edge and one neighbour

The given path row in VI (5.7), page 133, selects a non-loop edge
at its initial vertex. A path drawing cannot have a loop, since
that would be a closed walk in a forest. If the initial vertex has
valency one, every other incident edge is excluded by the valency
lemma used in Reduction 3. The link relation then fixes its other
endpoint as well. This makes the computed neighbour test complete.
-/

public section
namespace GraphMinor.GM06
open Set GraphMinor.Surface GraphMinor.GM11
universe u

/-- A link in a path drawing has distinct ends, because a loop
would give a nonempty simple closed walk in its graph forest. -/
theorem isPathDrawing_ne_of_isLink
    {S : Type u} [TopologicalSpace S] [T2Space S]
    {P : Drawing S} {s t a b : S} {e : Set S}
    (hP : IsPathDrawing P s t) (hl : P.toGraph.IsLink e a b) : a ≠ b := by
  intro hab
  subst b
  let W := GraphWalk.cons hl (GraphWalk.nil hl.right_mem)
  have hW : W.IsSimpleClosed := ⟨List.nodup_singleton _, List.nodup_singleton _⟩
  have hh := isGraphForest_of_isPathDrawing hP _ W hW
  change (1 : ℕ) = 0 at hh
  exact Nat.one_ne_zero hh

/-- At an initial vertex of valency one, a non-loop incident link
is the only incident edge and its other endpoint is the only neighbour. -/
theorem initial_link_unique_of_valency_one
    {k : ℕ} {G : Drawing ClosedCylinder} {i : Fin k}
    {e f : Set ClosedCylinder} {v w : ClosedCylinder}
    (hval : vertexValency G.toGraph (cylinderM1Point k i) = 1)
    (hl : G.toGraph.IsLink e (cylinderM1Point k i) v)
    (hvs : v ≠ cylinderM1Point k i)
    (hf : G.toGraph.IsLink f (cylinderM1Point k i) w) : f = e ∧ w = v := by
  have hscl : cylinderM1Point k i ∈ closure f :=
    (show cylinderM1Point k i ∈ closure f ∩ G.V from hf.2.2.2.symm ▸ mem_insert _ _).1
  have hfe : f = e := by
    by_contra hne
    exact not_mem_closure_edge_of_ne_red3 hval hl hvs hf.edge_mem hne hscl
  refine ⟨hfe, ?_⟩
  have hother : G.toGraph.IsLink e (cylinderM1Point k i) w := hfe ▸ hf
  rcases hl.eq_and_eq_or_eq_and_eq hother with ⟨_, hvw⟩ | ⟨_, hvs'⟩
  · exact hvw.symm
  · exact False.elim (hvs hvs')

end GraphMinor.GM06
