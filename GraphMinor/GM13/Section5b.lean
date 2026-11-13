module

public import GraphMinor.GM13.Section5a

/-!
# Graph Minors XIII, Section 5 (Part B): Loop and Contraction Steps of (5.3)

This file formalizes the loop-deletion reduction (`theorem_5_3_step_loop`), the
disjoint-from-`Z` reduction (`theorem_5_3_base_no_other_edges`), and Claim (2)
(`theorem_5_3_step_contract`, edge contraction) in the proof of (5.3) of
Graph Minors XIII (pages 80–81).
-/

@[expose] public section

namespace GraphMinor.GM13

open Set Function Classical
open Graph SimpleGraph Hypergraph
open GraphMinor.Surface

universe u v w

variable {α : Type u} {β : Type v}

/-- Deleting a loop `e₀` (`H.head e₀ = H.tail e₀` when `e₀ ∈ H.edgeSet`) from `H` preserves walks
between any two vertices. -/
lemma GraphWalk.of_delete_loop {H : Digraph α β} {e₀ : β}
    (hloop : e₀ ∈ H.edgeSet → H.head e₀ = H.tail e₀)
    {u v : α} (W : GraphWalk H.toGraph u v) :
    Nonempty (GraphWalk (H.subdigraphOf H.vertexSet (H.edgeSet \ {e₀})).toGraph u v) := by
  induction W with
  | nil hu =>
    exact ⟨.nil ⟨hu, hu⟩⟩
  | @cons x y z e hlink W' ih =>
    rcases ih with ⟨W''⟩
    by_cases he : e = e₀
    · subst he
      have hl : H.head e = H.tail e := hloop hlink.1
      have hxy : x = y := by
        rcases hlink.2 with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · exact h1.symm.trans (hl ▸ h2)
        · exact (h1.symm.trans (hl.symm ▸ h2)).symm
      subst hxy
      exact ⟨W''⟩
    · have hlink' : (H.subdigraphOf H.vertexSet (H.edgeSet \ {e₀})).toGraph.IsLink e x y := by
        refine ⟨⟨⟨hlink.1, hlink.1, he⟩, H.head_mem hlink.1, H.tail_mem hlink.1⟩, hlink.2⟩
      exact ⟨.cons hlink' W''⟩

/-- If every edge of `G` is between distinct `sub i` and `sub j`, and some `sub i₀` is disjoint
from `Z`, then `theorem_5_3_proof` holds (by restricting `G` to `⋃ i, (sub i).vertexSet` and applying
`theorem_5_3_base_matching`). -/
theorem theorem_5_3_base_no_other_edges {G : Digraph α β} {Z : Set α} {ξ k : ℕ}
    (hfin : G.IsFinite)
    (hZ : Z ⊆ G.vertexSet) (hZcard : Z.ncard = ξ)
    (hk : (3 * ξ) / 2 ≤ k)
    {sub : Fin k → Digraph α β}
    (hsub : ∀ i : Fin k, (sub i).IsSubdigraph G)
    (hdisj : Pairwise (fun i j : Fin k => Disjoint (sub i).vertexSet (sub j).vertexSet))
    (hi : ∀ i : Fin k, (sub i).IsConnected ∨
      ((sub i).vertexSet.Nonempty ∧
        ∀ u ∈ (sub i).vertexSet, ∃ z ∈ Z ∩ (sub i).vertexSet,
          Nonempty (GraphWalk (sub i).toGraph u z)))
    (hii : ∀ i j : Fin k, i < j →
      (((sub i).vertexSet ∩ Z).Nonempty ∧ ((sub j).vertexSet ∩ Z).Nonempty) ∨
        G.HasEdgeBetween (sub i).vertexSet (sub j).vertexSet)
    (hiii : ∀ (i : Fin k) (A B : Digraph α β),
      G.IsSeparation A B → Z ⊆ A.vertexSet → (G.interSub A (sub i)).IsNull →
      ξ ≤ Digraph.separationOrder A B)
    (i₀ : Fin k) (hi₀Z : (sub i₀).vertexSet ∩ Z = ∅)
    (hedges_between : ∀ e ∈ G.edgeSet, ∃ i j : Fin k, i ≠ j ∧
      G.head e ∈ (sub i).vertexSet ∧ G.tail e ∈ (sub j).vertexSet) :
    ∃ (μ : ℕ) (_ : μ ≤ ξ) (H : Fin (k - (ξ - μ) / 2) → Digraph α β),
      (∀ i, (H i).IsSubdigraph G) ∧
      (∀ i, (H i).IsConnected) ∧
      Pairwise (fun i j => Disjoint (H i).vertexSet (H j).vertexSet) ∧
      (∀ i : Fin (k - (ξ - μ) / 2),
        (i.1 < ξ → ((H i).vertexSet ∩ Z).ncard = 1) ∧
        (ξ ≤ i.1 → (H i).vertexSet ∩ Z = ∅)) ∧
      (∀ i j : Fin (k - (ξ - μ) / 2), i < j →
        ¬ G.HasEdgeBetween (H i).vertexSet (H j).vertexSet → i.1 < μ ∧ j.1 < μ) := by
  let U : Set α := ⋃ i : Fin k, (sub i).vertexSet
  have hU_sub : U ⊆ G.vertexSet := iUnion_subset (fun i => (hsub i).vertexSet_subset)
  -- Every edge of `G` has both ends in `U`.
  have hE_ends (e : β) (he : e ∈ G.edgeSet) : G.head e ∈ U ∧ G.tail e ∈ U := by
    rcases hedges_between e he with ⟨i₁, i₂, _, h1, h2⟩
    exact ⟨mem_iUnion.mpr ⟨i₁, h1⟩, mem_iUnion.mpr ⟨i₂, h2⟩⟩
  -- `Z ⊆ U`: if `z₀ ∈ Z \ U`, then `(G.subdigraphOf Z ∅, G.subdigraphOf (G.vertexSet \ {z₀}) G.edgeSet)`
  -- is a separation of `G` of order `< ξ` with `A ∩ sub i₀` null, contradicting `hiii`.
  have hZ_sub_U : Z ⊆ U := by
    intro z₀ hz₀Z
    by_contra hz₀NotU
    let A : Digraph α β := G.subdigraphOf Z ∅
    let B : Digraph α β := G.subdigraphOf (G.vertexSet \ {z₀}) G.edgeSet
    have hAV : A.vertexSet = Z := inter_eq_self_of_subset_right hZ
    have hAE : A.edgeSet = ∅ := by
      ext e
      simp only [A, Digraph.subdigraphOf, mem_inter_iff, mem_empty_iff_false, and_false,
        false_and, mem_ofPred_eq]
    have hBV : B.vertexSet = G.vertexSet \ {z₀} := inter_eq_self_of_subset_right sdiff_subset
    have hsep : G.IsSeparation A B := {
      sub_left := G.subdigraphOf_isSubdigraph Z ∅
      sub_right := G.subdigraphOf_isSubdigraph (G.vertexSet \ {z₀}) G.edgeSet
      vertexSet_union := by
        rw [hAV, hBV]
        ext u
        simp only [mem_union, mem_sdiff, mem_singleton_iff]
        exact ⟨fun h => h.elim (fun h1 => hZ h1) (fun h2 => h2.1),
          fun huG => if huz : u = z₀ then Or.inl (huz ▸ hz₀Z) else Or.inr ⟨huG, huz⟩⟩
      edgeSet_union := by
        rw [hAE, empty_union]
        ext e
        simp only [B, Digraph.subdigraphOf, mem_inter_iff, mem_sdiff, mem_singleton_iff,
          mem_ofPred_eq]
        refine ⟨fun h => h.1.1, fun heG => ⟨⟨heG, heG⟩, ?_, ?_⟩⟩
        · exact ⟨G.head_mem heG, fun h => hz₀NotU (h ▸ (hE_ends e heG).1)⟩
        · exact ⟨G.tail_mem heG, fun h => hz₀NotU (h ▸ (hE_ends e heG).2)⟩
      edgeSet_disjoint := by
        rw [hAE]
        exact disjoint_iff_inter_eq_empty.mpr (empty_inter _)
    }
    have hZA : Z ⊆ A.vertexSet := by rw [hAV]
    have hAnull : (G.interSub A (sub i₀)).IsNull := by
      refine ⟨?_, ?_⟩
      · ext u
        simp only [Digraph.interSub, Digraph.subdigraphOf, hAV, mem_inter_iff,
          mem_empty_iff_false, iff_false, not_and]
        intro _ huZ hui₀
        have h : u ∈ (sub i₀).vertexSet ∩ Z := ⟨hui₀, huZ⟩
        rw [hi₀Z] at h
        exact h
      · ext e
        simp only [Digraph.interSub, Digraph.subdigraphOf, hAE, empty_inter, mem_inter_iff,
          mem_empty_iff_false, and_false, false_and, mem_ofPred_eq]
    have hord_ge : ξ ≤ Digraph.separationOrder A B := hiii i₀ A B hsep hZA hAnull
    have hAB_eq : A.vertexSet ∩ B.vertexSet = Z \ {z₀} := by
      rw [hAV, hBV]
      ext u
      simp only [mem_inter_iff, mem_sdiff, mem_singleton_iff]
      exact ⟨fun ⟨huZ, _, hne⟩ => ⟨huZ, hne⟩, fun ⟨huZ, hne⟩ => ⟨huZ, hZ huZ, hne⟩⟩
    have hord_eq : Digraph.separationOrder A B + 1 = ξ := by
      unfold Digraph.separationOrder
      rw [hAB_eq, ← ncard_singleton z₀]
      have h1 := ncard_sdiff_add_ncard_of_subset (singleton_subset_iff.mpr hz₀Z) (hfin.finite_V.subset hZ)
      omega
    omega
  -- Restrict `G` to `G' = G.induce U`
  let G' : Digraph α β := G.induce U
  have hG'_sub : G'.IsSubdigraph G := G.induce_isSubdigraph U
  have hG'V : G'.vertexSet = U := inter_eq_self_of_subset_right hU_sub
  have hG'E : G'.edgeSet = G.edgeSet := by
    ext e
    simp only [G', Digraph.induce, mem_ofPred_eq, and_iff_left_iff_imp]
    intro he
    exact hE_ends e he
  have hG'fin : G'.IsFinite := ⟨hfin.finite_V.subset hG'_sub.vertexSet_subset,
    hfin.finite_E.subset hG'_sub.edgeSet_subset⟩
  have hsub' (i : Fin k) : (sub i).IsSubdigraph G' := {
    vertexSet_subset := by
      rw [hG'V]
      exact subset_iUnion (fun j => (sub j).vertexSet) i
    edgeSet_subset := by
      rw [hG'E]
      exact (hsub i).edgeSet_subset
    head_eq := fun _ he => (hsub i).head_eq he
    tail_eq := fun _ he => (hsub i).tail_eq he
  }
  have hii' (i j : Fin k) (hlt : i < j) :
      (((sub i).vertexSet ∩ Z).Nonempty ∧ ((sub j).vertexSet ∩ Z).Nonempty) ∨
        G'.HasEdgeBetween (sub i).vertexSet (sub j).vertexSet := by
    rcases hii i j hlt with h1 | ⟨e, he, h2⟩
    · exact Or.inl h1
    · exact Or.inr ⟨e, hG'E.symm ▸ he, h2⟩
  have hiii' (i : Fin k) (A' B' : Digraph α β)
      (hsep' : G'.IsSeparation A' B') (hZA' : Z ⊆ A'.vertexSet)
      (hnull' : (G'.interSub A' (sub i)).IsNull) :
      ξ ≤ Digraph.separationOrder A' B' := by
    let B : Digraph α β := G.subdigraphOf (B'.vertexSet ∪ (G.vertexSet \ U)) B'.edgeSet
    have hA'_sub : A'.IsSubdigraph G := hsep'.sub_left.trans hG'_sub
    have hB_sub : B.IsSubdigraph G := G.subdigraphOf_isSubdigraph _ _
    have hBV : B.vertexSet = B'.vertexSet ∪ (G.vertexSet \ U) := by
      apply inter_eq_self_of_subset_right
      exact union_subset (hsep'.sub_right.trans hG'_sub).vertexSet_subset sdiff_subset
    have hBE : B.edgeSet = B'.edgeSet := by
      ext e
      simp only [B, Digraph.subdigraphOf, mem_inter_iff, mem_union, mem_sdiff, mem_ofPred_eq]
      refine ⟨fun h => h.1.2, fun heB' => ?_⟩
      have heG' : e ∈ G'.edgeSet := hsep'.sub_right.edgeSet_subset heB'
      have heG : e ∈ G.edgeSet := hG'E ▸ heG'
      have hhB' : G.head e ∈ B'.vertexSet :=
        hsep'.sub_right.head_eq heB' ▸ B'.head_mem heB'
      have htB' : G.tail e ∈ B'.vertexSet :=
        hsep'.sub_right.tail_eq heB' ▸ B'.tail_mem heB'
      exact ⟨⟨heG, heB'⟩, Or.inl hhB', Or.inl htB'⟩
    have hsep : G.IsSeparation A' B := {
      sub_left := hA'_sub
      sub_right := hB_sub
      vertexSet_union := by
        rw [hBV, ← union_assoc, hsep'.vertexSet_union, hG'V]
        ext u
        simp only [mem_union, mem_sdiff]
        exact ⟨fun h => h.elim (fun hU => hU_sub hU) (fun h => h.1),
          fun huG => if huU : u ∈ U then Or.inl huU else Or.inr ⟨huG, huU⟩⟩
      edgeSet_union := by
        rw [hBE, hsep'.edgeSet_union, hG'E]
      edgeSet_disjoint := by
        rw [hBE]
        exact hsep'.edgeSet_disjoint
    }
    have hnull : (G.interSub A' (sub i)).IsNull := by
      refine ⟨?_, ?_⟩
      · have h1 := hnull'.1
        simp only [Digraph.interSub, Digraph.subdigraphOf] at h1 ⊢
        rw [inter_eq_self_of_subset_right (inter_subset_left.trans hA'_sub.vertexSet_subset)]
        rw [inter_eq_self_of_subset_right (inter_subset_left.trans hsep'.sub_left.vertexSet_subset)] at h1
        exact h1
      · ext e
        simp only [Digraph.interSub, Digraph.subdigraphOf, mem_inter_iff, mem_ofPred_eq,
          mem_empty_iff_false, iff_false]
        intro h
        exact eq_empty_iff_forall_notMem.mp hnull'.2 e
          ⟨⟨hG'E.symm ▸ h.1.1, h.1.2⟩, h.2⟩
    have hord := hiii i A' B hsep hZA' hnull
    have hAB_eq : A'.vertexSet ∩ B.vertexSet = A'.vertexSet ∩ B'.vertexSet := by
      rw [hBV]
      ext u
      simp only [mem_inter_iff, mem_union, mem_sdiff]
      refine ⟨fun ⟨huA', h⟩ => ⟨huA', ?_⟩, fun ⟨huA', huB'⟩ => ⟨huA', Or.inl huB'⟩⟩
      rcases h with huB' | ⟨_, huNotU⟩
      · exact huB'
      · exfalso
        exact huNotU (hG'V ▸ hsep'.sub_left.vertexSet_subset huA')
    unfold Digraph.separationOrder at hord ⊢
    rw [hAB_eq] at hord
    exact hord
  have hedges' : ∀ e ∈ G'.edgeSet, ∃ i j : Fin k, i ≠ j ∧
      G'.head e ∈ (sub i).vertexSet ∧ G'.tail e ∈ (sub j).vertexSet := by
    intro e he
    exact hedges_between e (hG'E ▸ he)
  obtain ⟨μ, hμ, H, hH_sub', hH_conn, hH_disj, hH_a, hH_b⟩ :=
    theorem_5_3_base_matching hG'fin (hG'V.symm ▸ hZ_sub_U) hZcard hk
      hsub' hdisj hi hii' hiii' hedges' hG'V.symm
  refine ⟨μ, hμ, H, fun i => (hH_sub' i).trans hG'_sub, hH_conn, hH_disj, hH_a, ?_⟩
  intro i j hlt hnoEdge
  apply hH_b i j hlt
  rintro ⟨e, heG', h⟩
  exact hnoEdge ⟨e, hG'E ▸ heG', h⟩

/-- Loop deletion step of `theorem_5_3_proof`: if `e₀ ∈ G.edgeSet` is a loop (`G.head e₀ = G.tail e₀`),
deleting `e₀` from `G` and from each `sub i` preserves all hypotheses of `(5.3)`. -/
theorem theorem_5_3_step_loop {G : Digraph α β} {Z : Set α} {ξ k : ℕ}
    {sub : Fin k → Digraph α β}
    (hsub : ∀ i : Fin k, (sub i).IsSubdigraph G)
    (hdisj : Pairwise (fun i j : Fin k => Disjoint (sub i).vertexSet (sub j).vertexSet))
    (hi : ∀ i : Fin k, (sub i).IsConnected ∨
      ((sub i).vertexSet.Nonempty ∧
        ∀ u ∈ (sub i).vertexSet, ∃ z ∈ Z ∩ (sub i).vertexSet,
          Nonempty (GraphWalk (sub i).toGraph u z)))
    (hii : ∀ i j : Fin k, i < j →
      (((sub i).vertexSet ∩ Z).Nonempty ∧ ((sub j).vertexSet ∩ Z).Nonempty) ∨
        G.HasEdgeBetween (sub i).vertexSet (sub j).vertexSet)
    (hiii : ∀ (i : Fin k) (A B : Digraph α β),
      G.IsSeparation A B → Z ⊆ A.vertexSet → (G.interSub A (sub i)).IsNull →
      ξ ≤ Digraph.separationOrder A B)
    (e₀ : β) (he₀ : e₀ ∈ G.edgeSet) (hloop : G.head e₀ = G.tail e₀)
    (ih : ∀ (G' : Digraph α β) (sub' : Fin k → Digraph α β),
      G'.vertexSet = G.vertexSet → G'.edgeSet = G.edgeSet \ {e₀} →
      G'.IsSubdigraph G →
      (∀ i, (sub' i).IsSubdigraph G') →
      Pairwise (fun i j => Disjoint (sub' i).vertexSet (sub' j).vertexSet) →
      (∀ i, (sub' i).IsConnected ∨
        ((sub' i).vertexSet.Nonempty ∧
          ∀ u ∈ (sub' i).vertexSet, ∃ z ∈ Z ∩ (sub' i).vertexSet,
            Nonempty (GraphWalk (sub' i).toGraph u z))) →
      (∀ i j, i < j →
        (((sub' i).vertexSet ∩ Z).Nonempty ∧ ((sub' j).vertexSet ∩ Z).Nonempty) ∨
          G'.HasEdgeBetween (sub' i).vertexSet (sub' j).vertexSet) →
      (∀ i A' B', G'.IsSeparation A' B' → Z ⊆ A'.vertexSet →
        (G'.interSub A' (sub' i)).IsNull → ξ ≤ Digraph.separationOrder A' B') →
      ∃ (μ : ℕ) (_ : μ ≤ ξ) (H : Fin (k - (ξ - μ) / 2) → Digraph α β),
        (∀ i, (H i).IsSubdigraph G') ∧
        (∀ i, (H i).IsConnected) ∧
        Pairwise (fun i j => Disjoint (H i).vertexSet (H j).vertexSet) ∧
        (∀ i : Fin (k - (ξ - μ) / 2),
          (i.1 < ξ → ((H i).vertexSet ∩ Z).ncard = 1) ∧
          (ξ ≤ i.1 → (H i).vertexSet ∩ Z = ∅)) ∧
        (∀ i j : Fin (k - (ξ - μ) / 2), i < j →
          ¬ G'.HasEdgeBetween (H i).vertexSet (H j).vertexSet → i.1 < μ ∧ j.1 < μ)) :
    ∃ (μ : ℕ) (_ : μ ≤ ξ) (H : Fin (k - (ξ - μ) / 2) → Digraph α β),
      (∀ i, (H i).IsSubdigraph G) ∧
      (∀ i, (H i).IsConnected) ∧
      Pairwise (fun i j => Disjoint (H i).vertexSet (H j).vertexSet) ∧
      (∀ i : Fin (k - (ξ - μ) / 2),
        (i.1 < ξ → ((H i).vertexSet ∩ Z).ncard = 1) ∧
        (ξ ≤ i.1 → (H i).vertexSet ∩ Z = ∅)) ∧
      (∀ i j : Fin (k - (ξ - μ) / 2), i < j →
        ¬ G.HasEdgeBetween (H i).vertexSet (H j).vertexSet → i.1 < μ ∧ j.1 < μ) := by
  let G' : Digraph α β := G.subdigraphOf G.vertexSet (G.edgeSet \ {e₀})
  let sub' (i : Fin k) : Digraph α β :=
    (sub i).subdigraphOf (sub i).vertexSet ((sub i).edgeSet \ {e₀})
  have hG'V : G'.vertexSet = G.vertexSet := inter_self _
  have hG'E : G'.edgeSet = G.edgeSet \ {e₀} := by
    ext e
    simp only [G', Digraph.subdigraphOf, mem_inter_iff, mem_sdiff, mem_singleton_iff, mem_ofPred_eq]
    exact ⟨fun h => h.1.2, fun ⟨he, hne⟩ => ⟨⟨he, he, hne⟩, G.head_mem he, G.tail_mem he⟩⟩
  have hG'_sub : G'.IsSubdigraph G := G.subdigraphOf_isSubdigraph _ _
  have hsub'V (i : Fin k) : (sub' i).vertexSet = (sub i).vertexSet := inter_self _
  have hsub'E (i : Fin k) : (sub' i).edgeSet = (sub i).edgeSet \ {e₀} := by
    ext e
    simp only [sub', Digraph.subdigraphOf, mem_inter_iff, mem_sdiff, mem_singleton_iff, mem_ofPred_eq]
    exact ⟨fun h => h.1.2, fun ⟨he, hne⟩ => ⟨⟨he, he, hne⟩, (sub i).head_mem he, (sub i).tail_mem he⟩⟩
  have hsub'_sub (i : Fin k) : (sub' i).IsSubdigraph G' := {
    vertexSet_subset := by rw [hsub'V, hG'V]; exact (hsub i).vertexSet_subset
    edgeSet_subset := by
      rw [hsub'E, hG'E]
      exact sdiff_le_sdiff_right (hsub i).edgeSet_subset
    head_eq := fun _ he => (hsub i).head_eq (by rw [hsub'E] at he; exact he.1)
    tail_eq := fun _ he => (hsub i).tail_eq (by rw [hsub'E] at he; exact he.1)
  }
  have hdisj' : Pairwise (fun i j => Disjoint (sub' i).vertexSet (sub' j).vertexSet) := by
    intro i j hne
    rw [hsub'V, hsub'V]
    exact hdisj hne
  have hi' (i : Fin k) : (sub' i).IsConnected ∨
      ((sub' i).vertexSet.Nonempty ∧
        ∀ u ∈ (sub' i).vertexSet, ∃ z ∈ Z ∩ (sub' i).vertexSet,
          Nonempty (GraphWalk (sub' i).toGraph u z)) := by
    have hloop_i : e₀ ∈ (sub i).edgeSet → (sub i).head e₀ = (sub i).tail e₀ := by
      intro he
      rw [(hsub i).head_eq he, (hsub i).tail_eq he, hloop]
    rcases hi i with ⟨hne, hconn⟩ | ⟨hne, hcomp⟩
    · left
      unfold Digraph.IsConnected
      rw [hsub'V]
      exact ⟨hne, fun u hu v hv =>
        let ⟨W⟩ := hconn u hu v hv
        GraphWalk.of_delete_loop hloop_i W⟩
    · right
      rw [hsub'V]
      refine ⟨hne, fun u hu => ?_⟩
      rcases hcomp u hu with ⟨z, hz, ⟨W⟩⟩
      exact ⟨z, hz, GraphWalk.of_delete_loop hloop_i W⟩
  have hii' (i j : Fin k) (hlt : i < j) :
      (((sub' i).vertexSet ∩ Z).Nonempty ∧ ((sub' j).vertexSet ∩ Z).Nonempty) ∨
        G'.HasEdgeBetween (sub' i).vertexSet (sub' j).vertexSet := by
    rw [hsub'V, hsub'V]
    rcases hii i j hlt with h1 | ⟨e, heG, h2⟩
    · exact Or.inl h1
    · right
      have he_ne : e ≠ e₀ := by
        rintro rfl
        rcases h2 with ⟨ha, hb⟩ | ⟨ha, hb⟩
        · exact Set.disjoint_left.mp (hdisj (ne_of_lt hlt)) ha (hloop ▸ hb)
        · exact Set.disjoint_left.mp (hdisj (ne_of_lt hlt)) hb (hloop ▸ ha)
      exact ⟨e, hG'E.symm ▸ ⟨heG, he_ne⟩, h2⟩
  have hiii' (i : Fin k) (A' B' : Digraph α β)
      (hsep' : G'.IsSeparation A' B') (hZA' : Z ⊆ A'.vertexSet)
      (hnull' : (G'.interSub A' (sub' i)).IsNull) :
      ξ ≤ Digraph.separationOrder A' B' := by
    -- The loop vertex `G.head e₀` is in `A'.vertexSet` or `B'.vertexSet`.
    -- Add `e₀` to `B'` if `G.head e₀ ∈ B'.vertexSet`, otherwise to `A'`.
    have hv_mem : G.head e₀ ∈ A'.vertexSet ∪ B'.vertexSet := by
      rw [hsep'.vertexSet_union, hG'V]
      exact G.head_mem he₀
    by_cases hvB : G.head e₀ ∈ B'.vertexSet
    · let B : Digraph α β := G.subdigraphOf B'.vertexSet (insert e₀ B'.edgeSet)
      have hBV : B.vertexSet = B'.vertexSet :=
        inter_eq_self_of_subset_right (hsep'.sub_right.trans hG'_sub).vertexSet_subset
      have hBE : B.edgeSet = insert e₀ B'.edgeSet := by
        ext e
        simp only [B, Digraph.subdigraphOf, mem_inter_iff, mem_insert_iff, mem_ofPred_eq]
        refine ⟨fun h => h.1.2, ?_⟩
        rintro (rfl | heB')
        · exact ⟨⟨he₀, Or.inl rfl⟩, hvB, hloop ▸ hvB⟩
        · have heG' := hsep'.sub_right.edgeSet_subset heB'
          exact ⟨⟨(hG'_sub.edgeSet_subset heG'), Or.inr heB'⟩,
            hsep'.sub_right.head_eq heB' ▸ B'.head_mem heB',
            hsep'.sub_right.tail_eq heB' ▸ B'.tail_mem heB'⟩
      have hsep : G.IsSeparation A' B := {
        sub_left := hsep'.sub_left.trans hG'_sub
        sub_right := G.subdigraphOf_isSubdigraph _ _
        vertexSet_union := by rw [hBV, hsep'.vertexSet_union, hG'V]
        edgeSet_union := by
          rw [hBE, union_insert, hsep'.edgeSet_union, hG'E,
            insert_sdiff_singleton, insert_eq_of_mem he₀]
        edgeSet_disjoint := by
          rw [hBE, disjoint_insert_right]
          refine ⟨?_, hsep'.edgeSet_disjoint⟩
          intro heA'
          have heG' := hsep'.sub_left.edgeSet_subset heA'
          rw [hG'E] at heG'
          exact heG'.2 rfl
      }
      have hnull : (G.interSub A' (sub i)).IsNull := by
        refine ⟨?_, ?_⟩
        · have h1 := hnull'.1
          simp only [Digraph.interSub, Digraph.subdigraphOf, hsub'V] at h1 ⊢
          rw [inter_eq_self_of_subset_right (inter_subset_left.trans (hsep'.sub_left.trans hG'_sub).vertexSet_subset)]
          rw [inter_eq_self_of_subset_right (inter_subset_left.trans hsep'.sub_left.vertexSet_subset)] at h1
          exact h1
        · ext e
          simp only [Digraph.interSub, Digraph.subdigraphOf, mem_inter_iff, mem_ofPred_eq,
            mem_empty_iff_false, iff_false]
          intro h
          have hu_empty : A'.vertexSet ∩ (sub i).vertexSet = ∅ := by
            have h1 := hnull'.1
            simp only [Digraph.interSub, Digraph.subdigraphOf, hsub'V] at h1
            rw [inter_eq_self_of_subset_right (inter_subset_left.trans hsep'.sub_left.vertexSet_subset)] at h1
            exact h1
          have hhead : G.head e ∈ A'.vertexSet ∩ (sub i).vertexSet := h.2.1
          rw [hu_empty] at hhead
          exact hhead
      have hord := hiii i A' B hsep hZA' hnull
      unfold Digraph.separationOrder at hord ⊢
      rw [hBV] at hord
      exact hord
    · have hvA : G.head e₀ ∈ A'.vertexSet := hv_mem.resolve_right hvB
      let A : Digraph α β := G.subdigraphOf A'.vertexSet (insert e₀ A'.edgeSet)
      have hAV : A.vertexSet = A'.vertexSet :=
        inter_eq_self_of_subset_right (hsep'.sub_left.trans hG'_sub).vertexSet_subset
      have hAE : A.edgeSet = insert e₀ A'.edgeSet := by
        ext e
        simp only [A, Digraph.subdigraphOf, mem_inter_iff, mem_insert_iff, mem_ofPred_eq]
        refine ⟨fun h => h.1.2, ?_⟩
        rintro (rfl | heA')
        · exact ⟨⟨he₀, Or.inl rfl⟩, hvA, hloop ▸ hvA⟩
        · have heG' := hsep'.sub_left.edgeSet_subset heA'
          exact ⟨⟨(hG'_sub.edgeSet_subset heG'), Or.inr heA'⟩,
            hsep'.sub_left.head_eq heA' ▸ A'.head_mem heA',
            hsep'.sub_left.tail_eq heA' ▸ A'.tail_mem heA'⟩
      have hsep : G.IsSeparation A B' := {
        sub_left := G.subdigraphOf_isSubdigraph _ _
        sub_right := hsep'.sub_right.trans hG'_sub
        vertexSet_union := by rw [hAV, hsep'.vertexSet_union, hG'V]
        edgeSet_union := by
          rw [hAE, insert_union, hsep'.edgeSet_union, hG'E,
            insert_sdiff_singleton, insert_eq_of_mem he₀]
        edgeSet_disjoint := by
          rw [hAE, disjoint_insert_left]
          refine ⟨?_, hsep'.edgeSet_disjoint⟩
          intro heB'
          have heG' := hsep'.sub_right.edgeSet_subset heB'
          rw [hG'E] at heG'
          exact heG'.2 rfl
      }
      have hu_empty : A'.vertexSet ∩ (sub i).vertexSet = ∅ := by
        have h1 := hnull'.1
        simp only [Digraph.interSub, Digraph.subdigraphOf, hsub'V] at h1
        rw [inter_eq_self_of_subset_right (inter_subset_left.trans hsep'.sub_left.vertexSet_subset)] at h1
        exact h1
      have hnull : (G.interSub A (sub i)).IsNull := by
        refine ⟨?_, ?_⟩
        · simp only [Digraph.interSub, Digraph.subdigraphOf, hAV]
          rw [inter_eq_self_of_subset_right (inter_subset_left.trans (hsep'.sub_left.trans hG'_sub).vertexSet_subset)]
          exact hu_empty
        · ext e
          simp only [Digraph.interSub, Digraph.subdigraphOf, hAV, mem_inter_iff, mem_ofPred_eq,
            mem_empty_iff_false, iff_false]
          intro h
          have hhead : G.head e ∈ A'.vertexSet ∩ (sub i).vertexSet := h.2.1
          rw [hu_empty] at hhead
          exact hhead
      have hord := hiii i A B' hsep (hAV.symm ▸ hZA') hnull
      unfold Digraph.separationOrder at hord ⊢
      rw [hAV] at hord
      exact hord
  obtain ⟨μ, hμ, H, hH_sub', hH_conn, hH_disj, hH_a, hH_b⟩ :=
    ih G' sub' hG'V hG'E hG'_sub hsub'_sub hdisj' hi' hii' hiii'
  refine ⟨μ, hμ, H, fun i => (hH_sub' i).trans hG'_sub, hH_conn, hH_disj, hH_a, ?_⟩
  intro i j hlt hnoEdge
  apply hH_b i j hlt
  rintro ⟨e, heG', h⟩
  exact hnoEdge ⟨e, hG'_sub.edgeSet_subset heG', h⟩

/-- Contracting an edge `e₀` by mapping `u ↦ v` (where `v ∈ G.vertexSet` and `u ≠ v`). -/
noncomputable def Digraph.contractEdge (G : Digraph α β) (u v : α) (e₀ : β)
    (hv : v ∈ G.vertexSet) (hne : u ≠ v) : Digraph α β where
  vertexSet := G.vertexSet \ {u}
  edgeSet := G.edgeSet \ {e₀}
  head e := if G.head e = u then v else G.head e
  tail e := if G.tail e = u then v else G.tail e
  head_mem _ he := by
    split_ifs with h
    · exact ⟨hv, hne.symm⟩
    · exact ⟨G.head_mem he.1, h⟩
  tail_mem _ he := by
    split_ifs with h
    · exact ⟨hv, hne.symm⟩
    · exact ⟨G.tail_mem he.1, h⟩

/-- Contracting a subdigraph `S` along `u ↦ v` and deleting `e₀`. -/
noncomputable def Digraph.contractSub (S : Digraph α β) (u v : α) (e₀ : β) : Digraph α β where
  vertexSet := (fun x => if x = u then v else x) '' S.vertexSet
  edgeSet := S.edgeSet \ {e₀}
  head e := if S.head e = u then v else S.head e
  tail e := if S.tail e = u then v else S.tail e
  head_mem e he := ⟨S.head e, S.head_mem he.1, rfl⟩
  tail_mem e he := ⟨S.tail e, S.tail_mem he.1, rfl⟩

/-- Any walk in `S` maps to a walk in `S.contractSub u v e₀` provided `e₀` (if in `S`) links `u` and `v`. -/
lemma GraphWalk.contractWalk {S : Digraph α β} {u v : α} {e₀ : β}
    (he₀_ends : e₀ ∈ S.edgeSet →
      (S.head e₀ = u ∧ S.tail e₀ = v) ∨ (S.head e₀ = v ∧ S.tail e₀ = u))
    {x y : α} (W : GraphWalk S.toGraph x y) :
    Nonempty (GraphWalk (S.contractSub u v e₀).toGraph
      (if x = u then v else x) (if y = u then v else y)) := by
  induction W with
  | nil hx =>
    exact ⟨.nil ⟨_, hx, rfl⟩⟩
  | @cons a b c e hlink W' ih =>
    rcases ih with ⟨W''⟩
    by_cases he : e = e₀
    · subst he
      have hab : (if a = u then v else a) = (if b = u then v else b) := by
        rcases he₀_ends hlink.1 with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
          rcases hlink.2 with ⟨h3, h4⟩ | ⟨h3, h4⟩ <;>
          simp [← h3, ← h4, h1, h2]
      rw [hab]
      exact ⟨W''⟩
    · have hlink' : (S.contractSub u v e₀).toGraph.IsLink e
          (if a = u then v else a) (if b = u then v else b) := by
        refine ⟨⟨hlink.1, he⟩, ?_⟩
        rcases hlink.2 with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · exact Or.inl ⟨by dsimp [Digraph.contractSub]; rw [h1],
            by dsimp [Digraph.contractSub]; rw [h2]⟩
        · exact Or.inr ⟨by dsimp [Digraph.contractSub]; rw [h1],
            by dsimp [Digraph.contractSub]; rw [h2]⟩
      exact ⟨.cons hlink' W''⟩

/-- Uncontracting a subdigraph `H'` of `G.contractEdge u v e₀ hv hne` back to a subdigraph of `G`. -/
noncomputable def Digraph.uncontractSub (G : Digraph α β) (u v : α) (e₀ : β) (H' : Digraph α β) :
    Digraph α β :=
  G.subdigraphOf {x ∈ G.vertexSet | (if x = u then v else x) ∈ H'.vertexSet}
    (if v ∈ H'.vertexSet then insert e₀ H'.edgeSet else H'.edgeSet)

lemma Digraph.uncontractSub_vertexSet (G : Digraph α β) (u v : α) (e₀ : β) (H' : Digraph α β) :
    (G.uncontractSub u v e₀ H').vertexSet =
      {x ∈ G.vertexSet | (if x = u then v else x) ∈ H'.vertexSet} :=
  inter_eq_self_of_subset_right (sep_subset _ _)

lemma Digraph.uncontractSub_isSubdigraph (G : Digraph α β) (u v : α) (e₀ : β) (H' : Digraph α β) :
    (G.uncontractSub u v e₀ H').IsSubdigraph G :=
  G.subdigraphOf_isSubdigraph _ _

lemma Digraph.uncontractSub_edgeSet {G : Digraph α β} {u v : α} {e₀ : β}
    (hv : v ∈ G.vertexSet) (hne : u ≠ v) (hlink₀ : G.toGraph.IsLink e₀ u v)
    {H' : Digraph α β} (hH' : H'.IsSubdigraph (G.contractEdge u v e₀ hv hne)) :
    (G.uncontractSub u v e₀ H').edgeSet =
      if v ∈ H'.vertexSet then insert e₀ H'.edgeSet else H'.edgeSet := by
  ext e
  simp only [Digraph.uncontractSub, Digraph.subdigraphOf, mem_inter_iff, mem_ofPred_eq]
  refine ⟨fun h => h.1.2, fun he => ?_⟩
  have he_cases : (e = e₀ ∧ v ∈ H'.vertexSet) ∨ e ∈ H'.edgeSet := by
    split_ifs at he with hvH'
    · rcases he with he_eq | he'
      · exact Or.inl ⟨he_eq, hvH'⟩
      · exact Or.inr he'
    · exact Or.inr he
  rcases he_cases with ⟨he_eq, hvH'⟩ | heH'
  · rw [he_eq]
    have hends : (if G.head e₀ = u then v else G.head e₀) = v ∧
        (if G.tail e₀ = u then v else G.tail e₀) = v := by
      rcases hlink₀.2 with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> simp [h1, h2]
    exact ⟨⟨hlink₀.1, he_eq ▸ he⟩, ⟨G.head_mem hlink₀.1, hends.1.symm ▸ hvH'⟩,
      ⟨G.tail_mem hlink₀.1, hends.2.symm ▸ hvH'⟩⟩
  · have heG' := hH'.edgeSet_subset heH'
    have heG : e ∈ G.edgeSet := heG'.1
    have hh : (if G.head e = u then v else G.head e) ∈ H'.vertexSet := by
      have h1 := H'.head_mem heH'
      rw [hH'.head_eq heH'] at h1
      exact h1
    have ht : (if G.tail e = u then v else G.tail e) ∈ H'.vertexSet := by
      have h1 := H'.tail_mem heH'
      rw [hH'.tail_eq heH'] at h1
      exact h1
    exact ⟨⟨heG, he⟩, ⟨G.head_mem heG, hh⟩, ⟨G.tail_mem heG, ht⟩⟩

lemma Digraph.uncontractSub_isConnected {G : Digraph α β} {u v : α} {e₀ : β}
    (hv : v ∈ G.vertexSet) (hne : u ≠ v) (hlink₀ : G.toGraph.IsLink e₀ u v)
    {H' : Digraph α β} (hH' : H'.IsSubdigraph (G.contractEdge u v e₀ hv hne))
    (hconn : H'.IsConnected) :
    (G.uncontractSub u v e₀ H').IsConnected := by
  let H := G.uncontractSub u v e₀ H'
  have hHV := G.uncontractSub_vertexSet u v e₀ H'
  have hHE := G.uncontractSub_edgeSet hv hne hlink₀ hH'
  have huG : u ∈ G.vertexSet := G.toGraph.left_mem_of_isLink hlink₀
  have hH'V_sub : H'.vertexSet ⊆ H.vertexSet := by
    intro x hx
    have hxG' := hH'.vertexSet_subset hx
    rw [hHV]
    refine ⟨hxG'.1, ?_⟩
    have hxu : x ≠ u := hxG'.2
    simp only [hxu, ↓reduceIte, hx]
  -- Every `x ∈ H.vertexSet` has a walk in `H` to `if x = u then v else x`.
  have hwalk_to_r (x : α) (hx : x ∈ H.vertexSet) :
      Nonempty (GraphWalk H.toGraph x (if x = u then v else x)) := by
    by_cases hxu : x = u
    · rw [hxu]
      simp only [↓reduceIte]
      have hvH' : v ∈ H'.vertexSet := by
        rw [hHV] at hx
        simpa [hxu] using hx.2
      have he₀H : e₀ ∈ H.edgeSet := by
        rw [hHE]
        simp [hvH']
      have hlink_H : H.toGraph.IsLink e₀ u v := ⟨he₀H, hlink₀.2⟩
      exact ⟨.cons hlink_H (.nil (hH'V_sub hvH'))⟩
    · simp only [hxu, ↓reduceIte]
      exact ⟨.nil hx⟩
  -- Every walk in `H'` lifts to a walk in `H`.
  have hwalk_lift : ∀ {a b : α}, GraphWalk H'.toGraph a b →
      Nonempty (GraphWalk H.toGraph a b) := by
    intro a b W
    induction W with
    | nil ha =>
      exact ⟨.nil (hH'V_sub ha)⟩
    | @cons x y z e hlink W' ih =>
      rcases ih with ⟨W_yz⟩
      have heH' : e ∈ H'.edgeSet := hlink.1
      have heH : e ∈ H.edgeSet := by
        rw [hHE]
        split_ifs <;> simp [heH']
      have hhH : G.head e ∈ H.vertexSet := H.head_mem heH
      have htH : G.tail e ∈ H.vertexSet := H.tail_mem heH
      have hlink_e : H.toGraph.IsLink e (G.head e) (G.tail e) :=
        ⟨heH, Or.inl ⟨rfl, rfl⟩⟩
      rcases hwalk_to_r (G.head e) hhH with ⟨Wh⟩
      rcases hwalk_to_r (G.tail e) htH with ⟨Wt⟩
      have hlink' := hlink.2
      rw [hH'.head_eq heH', hH'.tail_eq heH'] at hlink'
      dsimp [Digraph.contractEdge] at hlink'
      rcases hlink' with ⟨hx, hy⟩ | ⟨hx, hy⟩
      · subst hx hy
        have W_xy := GraphWalk.append (GraphWalk.reverse Wh)
          (GraphWalk.cons hlink_e Wt)
        exact ⟨GraphWalk.append W_xy W_yz⟩
      · subst hx hy
        have W_xy := GraphWalk.append (GraphWalk.reverse Wt)
          (GraphWalk.cons hlink_e.symm Wh)
        exact ⟨GraphWalk.append W_xy W_yz⟩
  rcases hconn.1 with ⟨v₀, hv₀⟩
  refine ⟨⟨v₀, hH'V_sub hv₀⟩, fun x hx y hy => ?_⟩
  have hrx : (if x = u then v else x) ∈ H'.vertexSet := by rw [hHV] at hx; exact hx.2
  have hry : (if y = u then v else y) ∈ H'.vertexSet := by rw [hHV] at hy; exact hy.2
  rcases hconn.2 _ hrx _ hry with ⟨W'⟩
  rcases hwalk_lift W' with ⟨W_mid⟩
  rcases hwalk_to_r x hx with ⟨Wx⟩
  rcases hwalk_to_r y hy with ⟨Wy⟩
  exact ⟨GraphWalk.append Wx (GraphWalk.append W_mid (GraphWalk.reverse Wy))⟩

/-- Contraction step (Claim (2) of Graph Minors XIII, (5.3), pages 80–81):
if `e₀ ∈ G.edgeSet` is a non-loop edge not between distinct `sub i` and `sub j`, and Claim (1)
holds (`hno_sep1`), then at least one end `u` of `e₀` is outside `Z`, and contracting `e₀` via
`u ↦ v` preserves all hypotheses of `(5.3)` and lifts `H'` back to `G`. -/
theorem theorem_5_3_step_contract {G : Digraph α β} {Z : Set α} {ξ k : ℕ}
    (hfin : G.IsFinite)
    (hZ : Z ⊆ G.vertexSet) (hZcard : Z.ncard = ξ)
    {sub : Fin k → Digraph α β}
    (hsub : ∀ i : Fin k, (sub i).IsSubdigraph G)
    (hdisj : Pairwise (fun i j : Fin k => Disjoint (sub i).vertexSet (sub j).vertexSet))
    (hi : ∀ i : Fin k, (sub i).IsConnected ∨
      ((sub i).vertexSet.Nonempty ∧
        ∀ u ∈ (sub i).vertexSet, ∃ z ∈ Z ∩ (sub i).vertexSet,
          Nonempty (GraphWalk (sub i).toGraph u z)))
    (hii : ∀ i j : Fin k, i < j →
      (((sub i).vertexSet ∩ Z).Nonempty ∧ ((sub j).vertexSet ∩ Z).Nonempty) ∨
        G.HasEdgeBetween (sub i).vertexSet (sub j).vertexSet)
    (hiii : ∀ (i : Fin k) (A B : Digraph α β),
      G.IsSeparation A B → Z ⊆ A.vertexSet → (G.interSub A (sub i)).IsNull →
      ξ ≤ Digraph.separationOrder A B)
    (i₀ : Fin k) (hi₀Z : (sub i₀).vertexSet ∩ Z = ∅)
    (hno_sep1 : ∀ (i : Fin k) (A B : Digraph α β),
      G.IsSeparation A B → Z ⊆ A.vertexSet → (G.interSub A (sub i)).IsNull →
      Digraph.separationOrder A B ≤ ξ → A.vertexSet \ B.vertexSet = ∅ ∧ A.edgeSet = ∅)
    (e₀ : β) (he₀ : e₀ ∈ G.edgeSet) (hnoloop : G.head e₀ ≠ G.tail e₀)
    (hnot_between : ¬ ∃ i j : Fin k, i ≠ j ∧
      G.head e₀ ∈ (sub i).vertexSet ∧ G.tail e₀ ∈ (sub j).vertexSet)
    (ih : ∀ (u v : α) (hv : v ∈ G.vertexSet) (hne : u ≠ v),
      u ∈ G.vertexSet → u ∉ Z →
      let G' := G.contractEdge u v e₀ hv hne
      let sub' := fun i => (sub i).contractSub u v e₀
      G'.IsFinite → Z ⊆ G'.vertexSet →
      (∀ i, (sub' i).IsSubdigraph G') →
      Pairwise (fun i j => Disjoint (sub' i).vertexSet (sub' j).vertexSet) →
      (∀ i, (sub' i).IsConnected ∨
        ((sub' i).vertexSet.Nonempty ∧
          ∀ w ∈ (sub' i).vertexSet, ∃ z ∈ Z ∩ (sub' i).vertexSet,
            Nonempty (GraphWalk (sub' i).toGraph w z))) →
      (∀ i j, i < j →
        (((sub' i).vertexSet ∩ Z).Nonempty ∧ ((sub' j).vertexSet ∩ Z).Nonempty) ∨
          G'.HasEdgeBetween (sub' i).vertexSet (sub' j).vertexSet) →
      (∀ i A' B', G'.IsSeparation A' B' → Z ⊆ A'.vertexSet →
        (G'.interSub A' (sub' i)).IsNull → ξ ≤ Digraph.separationOrder A' B') →
      ∃ (μ : ℕ) (_ : μ ≤ ξ) (H : Fin (k - (ξ - μ) / 2) → Digraph α β),
        (∀ i, (H i).IsSubdigraph G') ∧
        (∀ i, (H i).IsConnected) ∧
        Pairwise (fun i j => Disjoint (H i).vertexSet (H j).vertexSet) ∧
        (∀ i : Fin (k - (ξ - μ) / 2),
          (i.1 < ξ → ((H i).vertexSet ∩ Z).ncard = 1) ∧
          (ξ ≤ i.1 → (H i).vertexSet ∩ Z = ∅)) ∧
        (∀ i j : Fin (k - (ξ - μ) / 2), i < j →
          ¬ G'.HasEdgeBetween (H i).vertexSet (H j).vertexSet → i.1 < μ ∧ j.1 < μ)) :
    ∃ (μ : ℕ) (_ : μ ≤ ξ) (H : Fin (k - (ξ - μ) / 2) → Digraph α β),
      (∀ i, (H i).IsSubdigraph G) ∧
      (∀ i, (H i).IsConnected) ∧
      Pairwise (fun i j => Disjoint (H i).vertexSet (H j).vertexSet) ∧
      (∀ i : Fin (k - (ξ - μ) / 2),
        (i.1 < ξ → ((H i).vertexSet ∩ Z).ncard = 1) ∧
        (ξ ≤ i.1 → (H i).vertexSet ∩ Z = ∅)) ∧
      (∀ i j : Fin (k - (ξ - μ) / 2), i < j →
        ¬ G.HasEdgeBetween (H i).vertexSet (H j).vertexSet → i.1 < μ ∧ j.1 < μ) := by
  -- Step 1: Not both ends of `e₀` belong to `Z` (by `hno_sep1` on `A = G.subdigraphOf Z {e₀}`).
  have hend_not_Z : ∃ u v : α, G.toGraph.IsLink e₀ u v ∧ u ∉ Z := by
    by_cases hhZ : G.head e₀ ∈ Z
    · by_cases htZ : G.tail e₀ ∈ Z
      · exfalso
        let A : Digraph α β := G.subdigraphOf Z {e₀}
        let B : Digraph α β := G.subdigraphOf G.vertexSet (G.edgeSet \ {e₀})
        have hAV : A.vertexSet = Z := inter_eq_self_of_subset_right hZ
        have hAE : A.edgeSet = {e₀} := by
          ext e
          simp only [A, Digraph.subdigraphOf, mem_inter_iff, mem_singleton_iff, mem_ofPred_eq]
          refine ⟨fun h => h.1.2, ?_⟩
          rintro rfl
          exact ⟨⟨he₀, rfl⟩, hhZ, htZ⟩
        have hBV : B.vertexSet = G.vertexSet := inter_self _
        have hBE : B.edgeSet = G.edgeSet \ {e₀} := by
          ext e
          simp only [B, Digraph.subdigraphOf, mem_inter_iff, mem_sdiff, mem_singleton_iff, mem_ofPred_eq]
          exact ⟨fun h => h.1.2, fun ⟨he, hne⟩ => ⟨⟨he, he, hne⟩, G.head_mem he, G.tail_mem he⟩⟩
        have hsep : G.IsSeparation A B := {
          sub_left := G.subdigraphOf_isSubdigraph _ _
          sub_right := G.subdigraphOf_isSubdigraph _ _
          vertexSet_union := by rw [hAV, hBV, union_eq_self_of_subset_left hZ]
          edgeSet_union := by rw [hAE, hBE, singleton_union, insert_sdiff_singleton, insert_eq_of_mem he₀]
          edgeSet_disjoint := by rw [hAE, hBE, disjoint_singleton_left]; exact fun h => h.2 rfl
        }
        have hAnull : (G.interSub A (sub i₀)).IsNull := by
          have hV_emp : A.vertexSet ∩ (sub i₀).vertexSet = ∅ := by
            rw [hAV, inter_comm, hi₀Z]
          refine ⟨?_, ?_⟩
          · simp only [Digraph.interSub, Digraph.subdigraphOf]
            rw [inter_eq_self_of_subset_right (inter_subset_left.trans (G.subdigraphOf_isSubdigraph _ _).vertexSet_subset)]
            exact hV_emp
          · ext e
            simp only [Digraph.interSub, Digraph.subdigraphOf, mem_inter_iff, mem_ofPred_eq,
              mem_empty_iff_false, iff_false]
            intro h
            have hh : G.head e ∈ A.vertexSet ∩ (sub i₀).vertexSet := h.2.1
            rw [hV_emp] at hh
            exact hh
        have hord_le : Digraph.separationOrder A B ≤ ξ := by
          unfold Digraph.separationOrder
          rw [hAV, hBV, inter_eq_self_of_subset_left hZ, hZcard]
        have hAE_emp := (hno_sep1 i₀ A B hsep (by rw [hAV]) hAnull hord_le).2
        rw [hAE] at hAE_emp
        exact singleton_ne_empty e₀ hAE_emp
      · exact ⟨G.tail e₀, G.head e₀, ⟨he₀, Or.inr ⟨rfl, rfl⟩⟩, htZ⟩
    · exact ⟨G.head e₀, G.tail e₀, ⟨he₀, Or.inl ⟨rfl, rfl⟩⟩, hhZ⟩
  rcases hend_not_Z with ⟨u, v, hlink₀, huNotZ⟩
  have huG : u ∈ G.vertexSet := G.toGraph.left_mem_of_isLink hlink₀
  have hvG : v ∈ G.vertexSet := G.toGraph.left_mem_of_isLink hlink₀.symm
  have hne : u ≠ v := by
    rintro rfl
    rcases hlink₀.2 with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> exact hnoloop (h1.trans h2.symm)
  let G' := G.contractEdge u v e₀ hvG hne
  let sub' := fun i => (sub i).contractSub u v e₀
  have hG'fin : G'.IsFinite := ⟨hfin.finite_V.sdiff, hfin.finite_E.sdiff⟩
  have hZG' : Z ⊆ G'.vertexSet := fun z hz => ⟨hZ hz, fun h => huNotZ (h ▸ hz)⟩
  have hsub'_sub (i : Fin k) : (sub' i).IsSubdigraph G' := {
    vertexSet_subset := by
      rintro _ ⟨x, hx, rfl⟩
      dsimp
      split_ifs with hxu
      · exact ⟨hvG, hne.symm⟩
      · exact ⟨(hsub i).vertexSet_subset hx, hxu⟩
    edgeSet_subset := sdiff_le_sdiff_right (hsub i).edgeSet_subset
    head_eq := fun e he => by
      dsimp [sub', G', Digraph.contractSub, Digraph.contractEdge]
      rw [(hsub i).head_eq he.1]
    tail_eq := fun e he => by
      dsimp [sub', G', Digraph.contractSub, Digraph.contractEdge]
      rw [(hsub i).tail_eq he.1]
  }
  have hdisj' : Pairwise (fun i j => Disjoint (sub' i).vertexSet (sub' j).vertexSet) := by
    intro i j hij
    rw [Set.disjoint_iff]
    rintro _ ⟨⟨x, hx, rfl⟩, ⟨y, hy, hy_eq⟩⟩
    have hxy_ne : x ≠ y := fun h => Set.disjoint_left.mp (hdisj hij) hx (h ▸ hy)
    -- Since `(if x = u then v else x) = (if y = u then v else y)` and `x ≠ y`, `{x, y} = {u, v}`.
    have huv : (x = u ∧ y = v) ∨ (x = v ∧ y = u) := by
      dsimp at hy_eq
      split_ifs at hy_eq with hyu hxu hxu
      · exact False.elim (hxy_ne (hxu.trans hyu.symm))
      · exact Or.inr ⟨hy_eq.symm, hyu⟩
      · exact Or.inl ⟨hxu, hy_eq⟩
      · exact False.elim (hxy_ne hy_eq.symm)
    rcases huv with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rcases hlink₀.2 with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact hnot_between ⟨i, j, hij, h1.symm ▸ hx, h2.symm ▸ hy⟩
    · exact hnot_between ⟨j, i, hij.symm, h1.symm ▸ hy, h2.symm ▸ hx⟩
    · exact hnot_between ⟨j, i, hij.symm, h1.symm ▸ hy, h2.symm ▸ hx⟩
    · exact hnot_between ⟨i, j, hij, h1.symm ▸ hx, h2.symm ▸ hy⟩
  have hi' (i : Fin k) : (sub' i).IsConnected ∨
      ((sub' i).vertexSet.Nonempty ∧
        ∀ w ∈ (sub' i).vertexSet, ∃ z ∈ Z ∩ (sub' i).vertexSet,
          Nonempty (GraphWalk (sub' i).toGraph w z)) := by
    have he₀_ends : e₀ ∈ (sub i).edgeSet →
        ((sub i).head e₀ = u ∧ (sub i).tail e₀ = v) ∨
        ((sub i).head e₀ = v ∧ (sub i).tail e₀ = u) := by
      intro he
      rw [(hsub i).head_eq he, (hsub i).tail_eq he]
      exact hlink₀.2
    rcases hi i with ⟨⟨x₀, hx₀⟩, hconn⟩ | ⟨⟨x₀, hx₀⟩, hcomp⟩
    · left
      refine ⟨⟨_, ⟨x₀, hx₀, rfl⟩⟩, ?_⟩
      rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
      rcases hconn x hx y hy with ⟨W⟩
      exact GraphWalk.contractWalk he₀_ends W
    · right
      refine ⟨⟨_, ⟨x₀, hx₀, rfl⟩⟩, ?_⟩
      rintro _ ⟨x, hx, rfl⟩
      rcases hcomp x hx with ⟨z, ⟨hzZ, hzi⟩, ⟨W⟩⟩
      have hzu : z ≠ u := fun h => huNotZ (h ▸ hzZ)
      have hz_mem : z ∈ (sub' i).vertexSet := ⟨z, hzi, by simp [hzu]⟩
      rcases GraphWalk.contractWalk he₀_ends W with ⟨W'⟩
      simp only [hzu, ↓reduceIte] at W'
      exact ⟨z, ⟨hzZ, hz_mem⟩, ⟨W'⟩⟩
  have hii' (i j : Fin k) (hlt : i < j) :
      (((sub' i).vertexSet ∩ Z).Nonempty ∧ ((sub' j).vertexSet ∩ Z).Nonempty) ∨
        G'.HasEdgeBetween (sub' i).vertexSet (sub' j).vertexSet := by
    rcases hii i j hlt with ⟨⟨z₁, hz₁i, hz₁Z⟩, ⟨z₂, hz₂j, hz₂Z⟩⟩ | ⟨e, heG, h2⟩
    · left
      have hz₁u : z₁ ≠ u := fun h => huNotZ (h ▸ hz₁Z)
      have hz₂u : z₂ ≠ u := fun h => huNotZ (h ▸ hz₂Z)
      exact ⟨⟨z₁, ⟨z₁, hz₁i, by simp [hz₁u]⟩, hz₁Z⟩,
        ⟨z₂, ⟨z₂, hz₂j, by simp [hz₂u]⟩, hz₂Z⟩⟩
    · right
      have he_ne : e ≠ e₀ := by
        rintro rfl
        rcases h2 with ⟨h3, h4⟩ | ⟨h3, h4⟩
        · exact hnot_between ⟨i, j, ne_of_lt hlt, h3, h4⟩
        · exact hnot_between ⟨j, i, (ne_of_lt hlt).symm, h3, h4⟩
      refine ⟨e, ⟨heG, he_ne⟩, ?_⟩
      rcases h2 with ⟨h3, h4⟩ | ⟨h3, h4⟩
      · exact Or.inl ⟨⟨G.head e, h3, rfl⟩, ⟨G.tail e, h4, rfl⟩⟩
      · exact Or.inr ⟨⟨G.head e, h3, rfl⟩, ⟨G.tail e, h4, rfl⟩⟩
  have hiii' (i : Fin k) (A' B' : Digraph α β)
      (hsep' : G'.IsSeparation A' B') (hZA' : Z ⊆ A'.vertexSet)
      (hnull' : (G'.interSub A' (sub' i)).IsNull) :
      ξ ≤ Digraph.separationOrder A' B' := by
    by_contra hlt_ord
    rw [not_le] at hlt_ord
    -- Lift `(A', B')` to `(A, B)` in `G` via `uncontractSub`.
    let VA : Set α := {x ∈ G.vertexSet | (if x = u then v else x) ∈ A'.vertexSet}
    let VB : Set α := {x ∈ G.vertexSet | (if x = u then v else x) ∈ B'.vertexSet}
    let EA : Set β := if v ∈ A'.vertexSet then insert e₀ A'.edgeSet else A'.edgeSet
    let EB : Set β := if v ∈ A'.vertexSet then B'.edgeSet else insert e₀ B'.edgeSet
    let A : Digraph α β := G.subdigraphOf VA EA
    let B : Digraph α β := G.subdigraphOf VB EB
    have hAV : A.vertexSet = VA := inter_eq_self_of_subset_right (sep_subset _ _)
    have hBV : B.vertexSet = VB := inter_eq_self_of_subset_right (sep_subset _ _)
    have hAE : A.edgeSet = EA :=
      G.uncontractSub_edgeSet hvG hne hlink₀ hsep'.sub_left
    have hBE : B.edgeSet = EB := by
      by_cases hvA' : v ∈ A'.vertexSet
      · ext e
        simp only [B, EB, hvA', ↓reduceIte, Digraph.subdigraphOf, mem_inter_iff, mem_ofPred_eq]
        refine ⟨fun h => h.1.2, fun heB' => ?_⟩
        have heG' := hsep'.sub_right.edgeSet_subset heB'
        have hh : (if G.head e = u then v else G.head e) ∈ B'.vertexSet := by
          have h1 := B'.head_mem heB'
          rw [hsep'.sub_right.head_eq heB'] at h1
          exact h1
        have ht : (if G.tail e = u then v else G.tail e) ∈ B'.vertexSet := by
          have h1 := B'.tail_mem heB'
          rw [hsep'.sub_right.tail_eq heB'] at h1
          exact h1
        exact ⟨⟨heG'.1, heB'⟩, ⟨G.head_mem heG'.1, hh⟩, ⟨G.tail_mem heG'.1, ht⟩⟩
      · have hvB' : v ∈ B'.vertexSet := by
          have hvG' : v ∈ G'.vertexSet := ⟨hvG, hne.symm⟩
          rw [← hsep'.vertexSet_union] at hvG'
          exact hvG'.resolve_left hvA'
        have hEB_eq : EB = if v ∈ B'.vertexSet then insert e₀ B'.edgeSet else B'.edgeSet := by
          simp [EB, hvA', hvB']
        change (G.subdigraphOf VB EB).edgeSet = EB
        rw [hEB_eq]
        exact G.uncontractSub_edgeSet hvG hne hlink₀ hsep'.sub_right
    have hsep : G.IsSeparation A B := {
      sub_left := G.subdigraphOf_isSubdigraph _ _
      sub_right := G.subdigraphOf_isSubdigraph _ _
      vertexSet_union := by
        rw [hAV, hBV]
        ext x
        simp only [VA, VB, mem_union, mem_ofPred_eq]
        refine ⟨fun h => h.elim (fun h1 => h1.1) (fun h2 => h2.1), fun hxG => ?_⟩
        have hrxG' : (if x = u then v else x) ∈ G'.vertexSet := by
          split_ifs with hxu
          · exact ⟨hvG, hne.symm⟩
          · exact ⟨hxG, hxu⟩
        rw [← hsep'.vertexSet_union] at hrxG'
        exact hrxG'.imp (fun h => ⟨hxG, h⟩) (fun h => ⟨hxG, h⟩)
      edgeSet_union := by
        rw [hAE, hBE]
        dsimp [EA, EB]
        split_ifs with hvA'
        · rw [insert_union, hsep'.edgeSet_union]
          change insert e₀ (G.edgeSet \ {e₀}) = G.edgeSet
          rw [insert_sdiff_singleton, insert_eq_of_mem he₀]
        · rw [union_insert, hsep'.edgeSet_union]
          change insert e₀ (G.edgeSet \ {e₀}) = G.edgeSet
          rw [insert_sdiff_singleton, insert_eq_of_mem he₀]
      edgeSet_disjoint := by
        rw [hAE, hBE]
        dsimp [EA, EB]
        split_ifs with hvA'
        · rw [disjoint_insert_left]
          exact ⟨fun heB' => (hsep'.sub_right.edgeSet_subset heB').2 rfl, hsep'.edgeSet_disjoint⟩
        · rw [disjoint_insert_right]
          exact ⟨fun heA' => (hsep'.sub_left.edgeSet_subset heA').2 rfl, hsep'.edgeSet_disjoint⟩
    }
    have hZA : Z ⊆ A.vertexSet := by
      rw [hAV]
      intro z hz
      have hzu : z ≠ u := fun h => huNotZ (h ▸ hz)
      exact ⟨hZ hz, by simp [hzu, hZA' hz]⟩
    have hAV_disj : A.vertexSet ∩ (sub i).vertexSet = ∅ := by
      rw [hAV]
      ext x
      simp only [VA, mem_inter_iff, mem_ofPred_eq, mem_empty_iff_false, iff_false]
      rintro ⟨⟨_, hrxA'⟩, hxi⟩
      have h1 := eq_empty_iff_forall_notMem.mp hnull'.1 (if x = u then v else x)
      apply h1
      simp only [Digraph.interSub, Digraph.subdigraphOf, mem_inter_iff]
      exact ⟨hsep'.sub_left.vertexSet_subset hrxA', hrxA', ⟨x, hxi, rfl⟩⟩
    have hAnull : (G.interSub A (sub i)).IsNull := by
      refine ⟨?_, ?_⟩
      · simp only [Digraph.interSub, Digraph.subdigraphOf]
        rw [inter_eq_self_of_subset_right (inter_subset_left.trans (G.subdigraphOf_isSubdigraph _ _).vertexSet_subset)]
        exact hAV_disj
      · ext e
        simp only [Digraph.interSub, Digraph.subdigraphOf, mem_inter_iff, mem_ofPred_eq,
          mem_empty_iff_false, iff_false]
        intro h
        have hh : G.head e ∈ A.vertexSet ∩ (sub i).vertexSet := h.2.1
        rw [hAV_disj] at hh
        exact hh
    -- Compare `A.vertexSet ∩ B.vertexSet` with `A'.vertexSet ∩ B'.vertexSet`.
    have hAB_sub : A.vertexSet ∩ B.vertexSet ⊆ insert u (A'.vertexSet ∩ B'.vertexSet) := by
      rw [hAV, hBV]
      rintro x ⟨⟨_, hrxA'⟩, ⟨_, hrxB'⟩⟩
      by_cases hxu : x = u
      · exact Or.inl hxu
      · simp only [hxu, ↓reduceIte] at hrxA' hrxB'
        exact Or.inr ⟨hrxA', hrxB'⟩
    by_cases hvA' : v ∈ A'.vertexSet
    · have hord_le : Digraph.separationOrder A B ≤ ξ := by
        unfold Digraph.separationOrder at hlt_ord ⊢
        have h1 := ncard_le_ncard hAB_sub (hfin.finite_V.subset (by
          rintro x (rfl | ⟨hxA', _⟩)
          · exact huG
          · exact (hsep'.sub_left.vertexSet_subset hxA').1))
        have h2 := ncard_insert_le u (A'.vertexSet ∩ B'.vertexSet)
        omega
      have hAE_emp := (hno_sep1 i A B hsep hZA hAnull hord_le).2
      rw [hAE] at hAE_emp
      dsimp [EA] at hAE_emp
      simp only [hvA', ↓reduceIte] at hAE_emp
      have hmem : e₀ ∈ (∅ : Set β) := hAE_emp ▸ mem_insert e₀ A'.edgeSet
      exact hmem
    · have hAB_sub' : A.vertexSet ∩ B.vertexSet ⊆ A'.vertexSet ∩ B'.vertexSet := by
        rw [hAV, hBV]
        rintro x ⟨⟨_, hrxA'⟩, ⟨_, hrxB'⟩⟩
        have hxu : x ≠ u := by
          rintro rfl
          simp only [↓reduceIte] at hrxA'
          exact hvA' hrxA'
        simp only [hxu, ↓reduceIte] at hrxA' hrxB'
        exact ⟨hrxA', hrxB'⟩
      have hord_lt : Digraph.separationOrder A B < ξ := by
        unfold Digraph.separationOrder at hlt_ord ⊢
        have h1 := ncard_le_ncard hAB_sub' (hfin.finite_V.subset (by
          rintro x ⟨hxA', _⟩
          exact (hsep'.sub_left.vertexSet_subset hxA').1))
        omega
      exact not_le_of_gt hord_lt (hiii i A B hsep hZA hAnull)
  obtain ⟨μ, hμ, H', hH'_sub, hH'_conn, hH'_disj, hH'_a, hH'_b⟩ :=
    ih u v hvG hne huG huNotZ hG'fin hZG' hsub'_sub hdisj' hi' hii' hiii'
  let H := fun i => G.uncontractSub u v e₀ (H' i)
  have hHV (i : Fin (k - (ξ - μ) / 2)) :
      (H i).vertexSet = {x ∈ G.vertexSet | (if x = u then v else x) ∈ (H' i).vertexSet} :=
    G.uncontractSub_vertexSet u v e₀ (H' i)
  refine ⟨μ, hμ, H, fun i => G.uncontractSub_isSubdigraph u v e₀ (H' i),
    fun i => G.uncontractSub_isConnected hvG hne hlink₀ (hH'_sub i) (hH'_conn i),
    ?_, ?_, ?_⟩
  · -- Pairwise Disjoint
    intro i j hij
    rw [hHV, hHV, Set.disjoint_iff]
    rintro x ⟨⟨_, hrx_i⟩, ⟨_, hrx_j⟩⟩
    exact Set.disjoint_left.mp (hH'_disj hij) hrx_i hrx_j
  · -- Condition (a)
    intro i
    have hHZ_eq : (H i).vertexSet ∩ Z = (H' i).vertexSet ∩ Z := by
      rw [hHV]
      ext z
      simp only [mem_inter_iff, mem_ofPred_eq]
      refine ⟨fun ⟨⟨_, hrz⟩, hzZ⟩ => ⟨?_, hzZ⟩, fun ⟨hzH', hzZ⟩ => ⟨⟨hZ hzZ, ?_⟩, hzZ⟩⟩
      · have hzu : z ≠ u := fun h => huNotZ (h ▸ hzZ)
        simpa [hzu] using hrz
      · have hzu : z ≠ u := fun h => huNotZ (h ▸ hzZ)
        simpa [hzu] using hzH'
    rw [hHZ_eq]
    exact hH'_a i
  · -- Condition (b)
    intro i j hlt hnoEdge
    apply hH'_b i j hlt
    rintro ⟨e, heG', h⟩
    apply hnoEdge
    refine ⟨e, heG'.1, ?_⟩
    rw [hHV, hHV]
    rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Or.inl ⟨⟨G.head_mem heG'.1, h1⟩, ⟨G.tail_mem heG'.1, h2⟩⟩
    · exact Or.inr ⟨⟨G.head_mem heG'.1, h1⟩, ⟨G.tail_mem heG'.1, h2⟩⟩

end GraphMinor.GM13
