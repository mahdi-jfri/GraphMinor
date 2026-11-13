module

public import GraphMinor.Compute.TwoPathsSearchWalk
public import GraphMinor.GM02.DeletedComponents
public import Mathlib.Combinatorics.Graph.Simple

/-!
# Computing a component after deleting a candidate separator

The component test in II (3.1), page 316, uses a graph search with the
candidate separator forbidden. Give those vertices label two and all
others label zero. The existing Word RAM breadth-first search then
returns exactly the component of a single starting vertex in the
remaining graph. Its queue history lists that component without repeats.
-/

@[expose] public section
namespace GraphMinor.Compute
open Graph SimpleGraph Set Relation Classical
variable {n : ℕ}

/-- Initial search labels for deleting a proposed separator. -/
def gm02ComponentLabels (X : Finset (Fin n)) (v : Fin n) : ℕ := if v ∈ X then 2 else 0

private theorem walk_reachable_avoiding {G : SimpleGraph (Fin n)} {X : Finset (Fin n)}
    {a b : Fin n} (W : G.Walk a b) (hW : ∀ v ∈ W.support, v ∉ X) :
    ReflTransGen ((Graph.ofSimpleGraph G).induce
      (V(Graph.ofSimpleGraph G) \ (X : Set (Fin n)))).Adj a b := by
  induction W with
  | nil => exact .refl
  | @cons a b c hab W ih =>
    apply (ReflTransGen.single ?_).trans (ih (fun v hv => hW v (List.mem_cons_of_mem _ hv)))
    refine ⟨s(a, b), ?_⟩
    rw [Graph.induce_isLink]
    exact ⟨⟨rfl, (SimpleGraph.mem_edgeSet _).2 hab⟩,
      ⟨Set.mem_univ _, hW a (List.mem_cons_self)⟩,
      ⟨Set.mem_univ _, hW b (List.mem_cons_of_mem _ W.start_mem_support)⟩⟩

/-- A completed search with a single unblocked source lists exactly its
component after deleting the candidate separator. -/
theorem gm02ComponentSearch_mem_iff {G : SimpleGraph (Fin n)} {X : Finset (Fin n)}
    {a b : Fin n} (ha : a ∉ X) {s₀ s : State} {items : List ℕ}
    (hs : TwoPaths.SInv G (gm02ComponentLabels X) [a.val] s₀ items items.length s) :
    b.val ∈ items ↔ b ∈ GM02.deletedComponent (Graph.ofSimpleGraph G) (X : Set (Fin n)) a := by
  constructor
  · intro hb
    obtain ⟨p, _, hp⟩ := hs.par
    obtain ⟨r, W, _, hr, hW, _, _⟩ := TwoPaths.exists_walk_of_parentOK hp
      (items.length + 1) b hb (by have h := List.idxOf_lt_length_iff.2 hb; omega)
    have hra : r = a := Fin.ext (List.mem_singleton.1 hr)
    subst r
    have hfree (v : Fin n) (hv : v.val ∈ items) : v ∉ X := by
      have h := hs.free v hv
      by_contra hx
      simp only [gm02ComponentLabels, ite_eq_left hx] at h
      contradiction
    exact ⟨⟨Set.mem_univ _, hfree b hb⟩, walk_reachable_avoiding W
      (fun v hv => hfree v (hW v hv).1)⟩
  · intro hb
    have hreach := hb.2
    clear hb
    induction hreach with
    | refl => exact hs.srcs a (List.mem_singleton_self _) (by simp [gm02ComponentLabels, ha])
    | @tail b c hp hbc ih =>
      obtain ⟨e, he⟩ := hbc
      rw [Graph.induce_isLink] at he
      have hadj : G.Adj b c := (Graph.ofSimpleGraph_adj_iff _ _).1 ⟨e, he.1⟩
      have hfree : gm02ComponentLabels X c = 0 := by
        exact ite_eq_right (show c ∉ X from he.2.2.2)
      rcases hs.closed b (by simpa using ih) c hadj with hblocked | hc
      · exact (hblocked hfree).elim
      · exact hc

end GraphMinor.Compute
