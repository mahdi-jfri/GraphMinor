module

public import Mathlib.Combinatorics.SimpleGraph.Acyclic

/-!
# Forest facts for the low-valency input to Graph Minors X, (4.2)

We prove that a finite forest with at least two vertices has two vertices
with at most one neighbour. These facts support the maximal-component
cycle argument for the external low-valency theorem, following the proof
of Illingworth and Wood, J. Graph Theory 110 (2025), Theorem 7, page 450.
-/

public section

namespace GraphMinor.GM10

open SimpleGraph

universe u

private theorem neighborSet_subset_snd_of_maximal_path
    {V : Type u} {G : SimpleGraph V} (hG : G.IsAcyclic)
    {a b : V} (p : G.Walk a b) (hp : p.IsPath)
    (hmax : ∀ x y (q : G.Walk x y), q.IsPath → q.length ≤ p.length) :
    G.neighborSet a ⊆ {p.snd} := by
  intro x hax
  apply hG.eq_snd_of_adj_start hp hax
  by_contra hx
  have hpath : (p.cons hax.symm).IsPath := hp.cons hx
  have hlen := hmax _ _ _ hpath
  simp only [SimpleGraph.Walk.length_cons] at hlen
  omega

/-- A finite forest with at least two vertices has two distinct vertices
with at most one neighbour. No connectivity assumption is needed. -/
theorem exists_two_small_neighbor_sets_of_acyclic
    {V : Type u} [Fintype V] [Nontrivial V] (G : SimpleGraph V) (hG : G.IsAcyclic) :
    ∃ a b, a ≠ b ∧ (G.neighborSet a).ncard ≤ 1 ∧ (G.neighborSet b).ncard ≤ 1 := by
  classical
  obtain ⟨a, b, p, hp, hmax⟩ := SimpleGraph.Walk.exists_isPath_forall_isPath_length_le_length G
  by_cases hnil : p.Nil
  · have hp0 : p.length = 0 := SimpleGraph.Walk.length_eq_zero_iff.2 hnil
    have hno : ∀ x y, ¬ G.Adj x y := by
      intro x y hxy
      have hpath : (SimpleGraph.Walk.cons hxy SimpleGraph.Walk.nil).IsPath := by
        simp [SimpleGraph.Walk.isPath_def, hxy.ne]
      have hlen := hmax x y _ hpath
      simp only [SimpleGraph.Walk.length_cons, SimpleGraph.Walk.length_nil, hp0] at hlen
      omega
    have hsmall : ∀ x, (G.neighborSet x).ncard ≤ 1 := by
      intro x
      have heq : G.neighborSet x = ∅ := Set.eq_empty_iff_forall_notMem.2 (hno x)
      rw [heq, Set.ncard_empty]
      omega
    obtain ⟨x, y, hxy⟩ := exists_pair_ne V
    exact ⟨x, y, hxy, hsmall x, hsmall y⟩
  · have hab : a ≠ b := fun heq ↦ hnil (hp.nil_iff_eq.2 heq)
    have hsuba := neighborSet_subset_snd_of_maximal_path hG p hp hmax
    have hmaxr : ∀ x y (q : G.Walk x y), q.IsPath → q.length ≤ p.reverse.length := by
      simpa only [SimpleGraph.Walk.length_reverse] using hmax
    have hsubb := neighborSet_subset_snd_of_maximal_path hG p.reverse hp.reverse hmaxr
    refine ⟨a, b, hab, ?_, ?_⟩
    · exact (Set.ncard_le_ncard hsuba (Set.finite_singleton _)).trans (by simp)
    · exact (Set.ncard_le_ncard hsubb (Set.finite_singleton _)).trans (by simp)

/-- A nonempty finite forest has a vertex with at most one neighbour. -/
theorem exists_small_neighbor_set_of_acyclic
    {V : Type u} [Fintype V] [Nonempty V] (G : SimpleGraph V) (hG : G.IsAcyclic) :
    ∃ a, (G.neighborSet a).ncard ≤ 1 := by
  classical
  by_cases hnt : Nontrivial V
  · let : Nontrivial V := hnt
    obtain ⟨a, _, _, ha, _⟩ := exists_two_small_neighbor_sets_of_acyclic G hG
    exact ⟨a, ha⟩
  · have hs : Subsingleton V := not_nontrivial_iff_subsingleton.1 hnt
    let : Subsingleton V := hs
    obtain ⟨a⟩ := ‹Nonempty V›
    refine ⟨a, ?_⟩
    have heq : G.neighborSet a = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.2
      intro b hab
      exact hab.ne (Subsingleton.elim a b)
    rw [heq, Set.ncard_empty]
    omega

/-- A nonempty finite graph with at least two neighbours at every vertex
contains a cycle. -/
theorem exists_cycle_of_two_le_neighbors
    {V : Type u} [Fintype V] [Nonempty V] (G : SimpleGraph V)
    (hdeg : ∀ a, 2 ≤ (G.neighborSet a).ncard) :
    ∃ a, ∃ p : G.Walk a a, p.IsCycle := by
  classical
  by_contra! hno
  have hforest : G.IsAcyclic := by
    intro a p
    exact hno a p
  obtain ⟨a, ha⟩ := exists_small_neighbor_set_of_acyclic G hforest
  have := hdeg a
  omega

end GraphMinor.GM10
