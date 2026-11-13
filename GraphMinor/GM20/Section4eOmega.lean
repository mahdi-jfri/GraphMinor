module

public import GraphMinor.GM20.Basic
import GraphMinor.GM04.Patchwork.StarWQO
import GraphMinor.GM04.HigmanProof

/-!
# The label order in Graph Minors XX, (4.10)

On page 334, Graph Minors XX orders the removable labelled patchworks on at most `N` vertices
by simulation. The paper says that this is a well-quasi-order by the proof of Graph Minors IV,
(8.4) (pages 249–251).

We apply that proof to the star with one node, whose part is the whole hypergraph. Its tip set
is empty. Thus claims (1)–(6) of IV fix vertex coordinates and root marches, sort edges by their
marches and patches, and apply Higman's lemma in each finite class. Claims (7)–(8) have no tips
to compare. Removability gives the realization with no adjacencies for the unmatched edges.
The library uses the same expansion and simulation definitions for IV and XVIII, so no change
of the simulation relation is needed. The only specialization is the one-node decomposition.
-/

public section

namespace GraphMinor.GM20

open Set GraphMinor.GM04 Hypergraph

universe u v w

variable {Ω : Type w} {α : Type u} {β : Type v}

private def oneNodeStar : RootedTree Unit where
  verts := {()}
  root := ()
  parent := id
  root_mem := Finset.mem_singleton_self _
  parent_mem _ hv := hv
  parent_root := rfl
  exists_iterate_eq_root _ _ := ⟨0, Subsingleton.elim _ _⟩

private theorem oneNodeStar_edges : oneNodeStar.edges = ∅ := by
  simp [RootedTree.edges, oneNodeStar]

private theorem oneNodeDecomposition (G : RootedHypergraph α β) :
    IsTreeDecomposition G oneNodeStar (fun _ ↦ G) where
  le _ _ := le_rfl
  biUnion_eq := Hypergraph.biUnion_singleton () (fun _ : Unit ↦ G.toHypergraph)
  edgeSet_inter_eq _ _ _ _ hne := (hne (Subsingleton.elim _ _)).elim
  inter_le _ _ _ _ _ _ _ := GM10.inter_le_left (G := G.toHypergraph) le_rfl le_rfl
  roots_root := rfl
  rootSet_edge _ hf := by rw [oneNodeStar_edges] at hf; exact (Finset.notMem_empty _ hf).elim

/-- The omitted claim in Graph Minors XX, proof of (4.10), page 334: removable
`Ω`-patchworks with at most `N` vertices are well-quasi-ordered by simulation.
This is the proof of IV (8.4) with the whole hypergraph at the sole node of a star.
There are no tips, so its tip hypothesis has no instances. -/
theorem wqo_boundedPatchwork [Preorder Ω] (hΩ : WellQuasiOrderedLE Ω) (N : ℕ) :
    WellQuasiOrdered (fun (P Q : {P : Patchwork Ω α β //
      P.G.vertexSet.ncard ≤ N ∧ P.IsRemovable}) ↦ Simulated P.1 Q.1) := by
  intro P
  exact theorem_8_4_proof higman_8_3.{0, 0} hΩ N (fun i ↦ (P i).1)
    (fun i ↦ (P i).2.2) (fun _ ↦ oneNodeStar) (fun i _ ↦ (P i).1.G)
    (fun _ _ _ ↦ rfl) (fun i ↦ oneNodeDecomposition (P i).1.G)
    (fun i ↦ (P i).2.1) (by
      intro Q hQ
      obtain ⟨i, s, hs, _⟩ := hQ 0
      rw [oneNodeStar_edges] at hs
      exact (Finset.notMem_empty _ hs).elim)

/-- The elements of `Ω₁` in the proof of Graph Minors XX, (4.10), page 334. -/
@[expose] def BoundedPatchwork (Ω : Type w) (α : Type u) (β : Type v) (N : ℕ) :=
  {P : Patchwork Ω α β // P.G.vertexSet.ncard ≤ N ∧ P.IsRemovable}

instance [Preorder Ω] (N : ℕ) : Preorder (BoundedPatchwork Ω α β N) where
  le P Q := Simulated P.1 Q.1
  le_refl P := Simulated.refl P.1
  le_trans _ _ _ hPQ hQR := hPQ.trans hQR

/-- The label order `Ω₁` used in Graph Minors XX, (4.10), page 334, is a well-quasi-order. -/
theorem wqo_omega₁ [Preorder Ω] (hΩ : WellQuasiOrderedLE Ω) (N : ℕ) :
    WellQuasiOrderedLE (BoundedPatchwork Ω α β N) :=
  ⟨wqo_boundedPatchwork hΩ N⟩

end GraphMinor.GM20
