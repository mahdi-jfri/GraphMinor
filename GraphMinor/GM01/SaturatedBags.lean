module

public import GraphMinor.GM01.PathWidth
import Lean.Elab.Tactic.Omega

/-!
# A bag used entirely by a subgraph

For the unbounded-tree-width observation in Graph Minors I, page 40,
a subgraph requiring width at least `k` must use a whole bag of any
width-`k` decomposition. Restrict the bags to its vertices. If every
restricted bag had at most `k` vertices, they would give width `k-1`.
A larger restricted bag therefore fills the original bag entirely.
-/

public section

namespace GraphMinor.GM01

open Set Graph

/-- A subgraph excluding width `k-1` fills a bag in any width-`k`
decomposition. This is the counting step for observation (b) on
page 40 of GM01. -/
theorem PathDecomposition.exists_saturated_bag {α β : Type*}
    {G K : Graph α β} {k : ℕ} (D : PathDecomposition G)
    (hD : ∀ i, (D.bag i).Finite ∧ (D.bag i).ncard ≤ k + 1)
    (hk : 0 < k) (hKG : K ≤ G) (hNo : ¬ HasPathWidthLE K (k - 1)) :
    ∃ i, (D.bag i).Nonempty ∧ D.bag i ⊆ V(K) := by
  have hLarge : ∃ i, k + 1 ≤ (D.bag i ∩ V(K)).ncard := by
    by_contra h
    have hSmall : ∀ i, (D.bag i ∩ V(K)).ncard ≤ k := by
      intro i
      have hn : ¬ k + 1 ≤ (D.bag i ∩ V(K)).ncard := fun hi ↦ h ⟨i, hi⟩
      omega
    apply hNo
    refine ⟨⟨D.length, fun i ↦ D.bag i ∩ V(K), fun _ _ hx ↦ hx.2, ?_, ?_⟩, ?_⟩
    · intro e x y he
      obtain ⟨i, hx, hy⟩ := D.edge_covered e x y (he.mono hKG)
      exact ⟨i, ⟨hx, he.left_mem⟩, ⟨hy, he.right_mem⟩⟩
    · intro i j l hij hjl x hx
      exact ⟨D.interval i j l hij hjl ⟨hx.1.1, hx.2.1⟩, hx.1.2⟩
    · intro i
      refine ⟨(hD i).1.subset inter_subset_left, ?_⟩
      change (D.bag i ∩ V(K)).ncard ≤ k - 1 + 1
      have hi := hSmall i
      omega
  obtain ⟨i, hi⟩ := hLarge
  have heq : D.bag i ∩ V(K) = D.bag i :=
    Set.eq_of_subset_of_ncard_le inter_subset_left ((hD i).2.trans hi) (hD i).1
  refine ⟨i, ?_, ?_⟩
  · apply (Set.ncard_pos (hD i).1).mp
    have hcard : (D.bag i ∩ V(K)).ncard ≤ (D.bag i).ncard :=
      Set.ncard_le_ncard inter_subset_left (hD i).1
    omega
  · intro x hx
    have hx' : x ∈ D.bag i ∩ V(K) := heq.symm ▸ hx
    exact hx'.2

end GraphMinor.GM01
