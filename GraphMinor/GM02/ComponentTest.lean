module

public import GraphMinor.GM02.SeparationComponents

/-!
# The complete component test for a balanced separator

Algorithm II (3.1) tries every vertex set of the permitted size. Its test
accepts exactly when every component of the complement contains at most
two thirds of the remaining terminals. Grouping components proves the
forward construction. Components staying on one side prove that rejecting
all candidates rules out every balanced separation.
-/

public section
namespace GraphMinor.GM02
open Graph Set Classical
universe u v

/-- The component-test equivalence used by Graph Minors II (3.1), page 316.
This supplies correctness of the search, separately from its implementation
and running time. -/
theorem balanced_separation_iff_component_test {α : Type u} {β : Type v}
    (G : Graph α β) (hV : (V(G)).Finite) (Q : Set α) (hQ : Q ⊆ V(G)) (w : ℕ) :
    (∃ H H', IsSeparation G H H' ∧ (V(H) ∩ V(H')).ncard ≤ w ∧
      3 * ((V(H) \ V(H')) ∩ Q).ncard ≤ 2 * (Q \ (V(H) ∩ V(H'))).ncard ∧
      3 * ((V(H') \ V(H)) ∩ Q).ncard ≤ 2 * (Q \ (V(H) ∩ V(H'))).ncard) ↔
    ∃ X ⊆ V(G), X.ncard ≤ w ∧ ∀ a ∈ V(G) \ X,
      3 * (deletedComponent G X a ∩ Q).ncard ≤ 2 * (Q \ X).ncard := by
  constructor
  · rintro ⟨H, H', hsep, hsize, hL, hR⟩
    exact ⟨V(H) ∩ V(H'), Set.inter_subset_left.trans hsep.1.vertexSet_mono,
      hsize, fun _ ha => balanced_separation_component_bound hV hsep hL hR ha⟩
  · rintro ⟨X, hX, hsize, hcomp⟩
    obtain ⟨H, H', hsep, hinter, hL, hR⟩ :=
      exists_balanced_separation_of_components hV hX hQ hcomp
    exact ⟨H, H', hsep, hinter.symm ▸ hsize, hL, hR⟩

end GraphMinor.GM02
