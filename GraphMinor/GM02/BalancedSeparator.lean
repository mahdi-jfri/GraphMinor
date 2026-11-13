module

public import GraphMinor.GM02.TreeSidePartition
public import GraphMinor.GM02.SeparatorComponents
import GraphMinor.GM02.TrimmedSeparator
import GraphMinor.GM02.MutualBranches

/-!
# Half-balanced separators

Graph Minors II (2.5) has two cases. A bag whose branches are all small
is already a separator, by (2.3). Otherwise choose a large branch at every
tree node. Two such choices face each other across an edge. The cut at
that edge has two separated sides. Removing the surplus vertices of the
heavier side inside one endpoint bag makes their counts equal.
-/

public section
namespace GraphMinor.GM02
open Graph Set Classical
universe u v t

private theorem edge_case {α : Type u} {β : Type v} {ι : Type t}
    {G : Graph α β} {T : SimpleGraph ι} {X : ι → Set α} {Q : Set α} {w : ℕ}
    (hD : IsTreeDecomposition G T X) (hG : (V(G)).Finite) (hQ : Q ⊆ V(G))
    (hwidth : ∀ i, (X i).ncard ≤ w) {j j' : ι} (hjj' : T.Adj j j')
    (hheavy : (treeSideOutside (T := T) X j' j ∩ Q).ncard ≤
      (treeSideOutside (T := T) X j j' ∩ Q).ncard)
    (hlarge : (Q \ X j).ncard < 2 * (treeSideOutside (T := T) X j' j ∩ Q).ncard) :
    ∃ S ⊆ V(G), S.ncard ≤ w ∧ ∀ a ∈ V(G) \ S,
      2 * (deletedComponent G S a ∩ Q).ncard ≤ (Q \ S).ncard := by
  obtain ⟨hpart, hdis⟩ := treeSideOutside_partition hD hjj'
  apply exists_balanced_separator_in_bag hG hQ hpart hdis
    (B := X j) (hAB := Set.inter_subset_left) (hBG := hD.bag_subset_vertices j)
    (hB := hwidth j) (hheavy := hheavy) (hmajority := hlarge)
  · intro a ha b hb haA hbA hp
    exact theorem_2_4_proof hD hjj' a ha.1 b hb.1 haA hbA hp
  · apply Set.disjoint_left.2
    intro a haB haR
    rw [← opposite_treeSide_sdiff_bag hD hjj'] at haR
    exact haR.2 haB

/-- Graph Minors II, (2.5), page 312:
"If the tree-decomposition has width $< w$ and $Q \subseteq V(G)$, then there
exists $X \subseteq V(G)$ with $|X| \le w$ such that every component of
$G \setminus X$ has at most $\frac{1}{2} |Q - X|$ vertices which are in $Q$."

The bag bound is the equivalent integral form of width strictly less than `w`.
The doubled component count avoids division in the statement. The proof prints
"$|(W - Y) \cap Q| = |W' \cup Q|$" for $|W' \cap Q|$ on page 313; the Lean makes the two counts
equal, as meant. See the correction to the proof of (2.5) in `corrections/GM02.md`. -/
theorem theorem_2_5_proof {α : Type u} {β : Type v} {ι : Type t} [Fintype ι]
    {G : Graph α β} {T : SimpleGraph ι} {X : ι → Set α} {Q : Set α} {w : ℕ}
    (hD : IsTreeDecomposition G T X) (hG : (V(G)).Finite)
    (hwidth : ∀ i, (X i).ncard ≤ w) (hQ : Q ⊆ V(G)) :
    ∃ S ⊆ V(G), S.ncard ≤ w ∧ ∀ a ∈ V(G) \ S,
      2 * (deletedComponent G S a ∩ Q).ncard ≤ (Q \ S).ncard := by
  by_cases hsmall : ∃ i, ∀ B : BranchAt T i,
      2 * (branchRegion X i B ∩ Q).ncard ≤ (Q \ X i).ncard
  · obtain ⟨i, hi⟩ := hsmall
    refine ⟨X i, hD.bag_subset_vertices i, hwidth i, ?_⟩
    intro a ha
    have hsub := deletedComponent_inter_subset_branchRegion hD i ⟨a, ha⟩ Q
    exact (Nat.mul_le_mul_left 2 (Set.ncard_le_ncard hsub
      ((hG.subset hQ).subset Set.inter_subset_right))).trans (hi _)
  · have hlarge : ∀ i, ∃ B : BranchAt T i,
        (Q \ X i).ncard < 2 * (branchRegion X i B ∩ Q).ncard := by
      intro i
      by_contra hn
      apply hsmall
      refine ⟨i, fun B => ?_⟩
      exact Nat.le_of_not_gt (fun h => hn ⟨B, h⟩)
    choose B hB using hlarge
    obtain ⟨j, j', hjj', hj', hj⟩ := exists_mutual_branches hD.isTree B
    have hR := hB j
    rw [branchRegion_eq_opposite_treeSide hD hjj' hj'] at hR
    have hL := hB j'
    rw [branchRegion_eq_opposite_treeSide hD hjj'.symm hj] at hL
    by_cases hheavy : (treeSideOutside (T := T) X j' j ∩ Q).ncard ≤
        (treeSideOutside (T := T) X j j' ∩ Q).ncard
    · exact edge_case hD hG hQ hwidth hjj' hheavy hR
    · exact edge_case hD hG hQ hwidth hjj'.symm (Nat.le_of_lt (Nat.lt_of_not_ge hheavy)) hL

end GraphMinor.GM02
