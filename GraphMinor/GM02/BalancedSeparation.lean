module

public import GraphMinor.GM02.TreeDecomposition
public import GraphMinor.GM02.Separation
import GraphMinor.GM02.BalancedSeparator
import GraphMinor.GM02.GroupedComponents

/-!
# Two-thirds-balanced separations

Graph Minors II (2.6) first uses (2.5) to bound each component by half.
Group those components into two sides whose counts are at most two thirds,
then divide the graph's edges between the two sides and their separator.
-/

public section
namespace GraphMinor.GM02
open Graph Set Classical
universe u v

/-- Graph Minors II, (2.6), page 313:
"If $G$ has tree-width $< w$ and $Q \subseteq V(G)$, there exists a separation
$(H, H')$ of $G$ such that $|V(H) \cap V(H')| \le w$ and"
$$
\begin{aligned}
&|(V(H) - V(H')) \cap Q|, |(V(H') - V(H)) \cap Q| \\
&\quad \le \frac{2}{3} |Q - (V(H) \cap V(H'))|.
\end{aligned}
$$

The inequalities are multiplied by three to avoid division. -/

theorem theorem_2_6_proof {α : Type u} {β : Type v} (G : Graph α β)
    (hV : (V(G)).Finite) (hE : (E(G)).Finite) {w : ℕ} {Q : Set α}
    (hw : treeWidth G hV hE < w) (hQ : Q ⊆ V(G)) :
    ∃ H H', IsSeparation G H H' ∧ (V(H) ∩ V(H')).ncard ≤ w ∧
      3 * ((V(H) \ V(H')) ∩ Q).ncard ≤ 2 * (Q \ (V(H) ∩ V(H'))).ncard ∧
      3 * ((V(H') \ V(H)) ∩ Q).ncard ≤ 2 * (Q \ (V(H) ∩ V(H'))).ncard := by
  have hwpos : 0 < w := Nat.zero_lt_of_lt hw
  have htw : TreeWidthLE G (w - 1) :=
    (treeWidth_le_iff G hV hE (w - 1)).1 (by omega)
  obtain ⟨ι, hι, T, B, hD, hB⟩ := htw
  let _ := hι
  have hwidth : ∀ i, (B i).ncard ≤ w := by
    intro i
    have h := hB i
    omega
  obtain ⟨X, hX, hsize, hhalf⟩ := theorem_2_5_proof hD hV hwidth hQ
  obtain ⟨Y, Y', hpart, hdis, hsep, hYcount, hY'count⟩ :=
    exists_grouped_components hV hQ hhalf
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
  exact ⟨H, H', hHH', hinter ▸ hsize,
    by rwa [hinter, hleft], by rwa [hinter, hright]⟩

end GraphMinor.GM02
