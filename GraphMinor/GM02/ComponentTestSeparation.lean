module

public import GraphMinor.GM02.Separation
public import GraphMinor.GM02.DeletedComponents
import GraphMinor.GM02.GroupedComponents

/-!
# Building a separation from the component test

Algorithm II (3.1) examines a proposed separator and counts terminals in
each remaining component. When every component has at most two thirds
of the remaining terminals, group the components as in (2.6) and assign
the edges to the resulting two sides. The separator is exactly the
proposed vertex set.
-/

public section
namespace GraphMinor.GM02
open Graph Set Classical
universe u v

/-- The successful component test in Graph Minors II (3.1), page 316,
produces a separation with the proposed separator and both printed
balance inequalities. -/
theorem exists_balanced_separation_of_components {α : Type u} {β : Type v}
    {G : Graph α β} {X Q : Set α} (hV : (V(G)).Finite)
    (hX : X ⊆ V(G)) (hQ : Q ⊆ V(G))
    (hcomp : ∀ a ∈ V(G) \ X,
      3 * (deletedComponent G X a ∩ Q).ncard ≤ 2 * (Q \ X).ncard) :
    ∃ H H', IsSeparation G H H' ∧ (V(H) ∩ V(H')) = X ∧
      3 * ((V(H) \ V(H')) ∩ Q).ncard ≤ 2 * (Q \ (V(H) ∩ V(H'))).ncard ∧
      3 * ((V(H') \ V(H)) ∩ Q).ncard ≤ 2 * (Q \ (V(H) ∩ V(H'))).ncard := by
  obtain ⟨Y, Y', hpart, hdis, hsep, hYcount, hY'count⟩ :=
    exists_grouped_components_of_two_thirds hV hQ hcomp
  obtain ⟨H, H', hHH', hHV, hH'V⟩ := exists_separation_of_partition hX hpart hsep
  have hYX : ∀ a ∈ Y, a ∉ X := by
    intro a ha
    have ha' : a ∈ V(G) \ X := by rw [← hpart]; exact Or.inl ha
    exact ha'.2
  have hY'X : ∀ a ∈ Y', a ∉ X := by
    intro a ha
    have ha' : a ∈ V(G) \ X := by rw [← hpart]; exact Or.inr ha
    exact ha'.2
  have hinter : V(H) ∩ V(H') = X := by
    rw [hHV, hH'V]
    ext a
    constructor
    · rintro ⟨haX | haY, haX' | haY'⟩
      · exact haX
      · exact haX
      · exact haX'
      · exact (Set.disjoint_left.1 hdis haY haY').elim
    · intro ha
      exact ⟨Or.inl ha, Or.inl ha⟩
  have hleft : V(H) \ V(H') = Y := by
    rw [hHV, hH'V]
    ext a
    constructor
    · rintro ⟨haX | haY, hn⟩
      · exact (hn (Or.inl haX)).elim
      · exact haY
    · intro ha
      exact ⟨Or.inr ha, fun h => h.elim (hYX a ha)
        (fun ha' => Set.disjoint_left.1 hdis ha ha')⟩
  have hright : V(H') \ V(H) = Y' := by
    rw [hHV, hH'V]
    ext a
    constructor
    · rintro ⟨haX | haY, hn⟩
      · exact (hn (Or.inl haX)).elim
      · exact haY
    · intro ha
      exact ⟨Or.inr ha, fun h => h.elim (hY'X a ha)
        (fun ha' => Set.disjoint_left.1 hdis ha' ha)⟩
  exact ⟨H, H', hHH', hinter,
    by rwa [hinter, hleft], by rwa [hinter, hright]⟩

end GraphMinor.GM02
