module

public import GraphMinor.Compute.Specs105

/-!
# Branch decompositions under vertex embeddings

Adding isolated vertices and renaming endpoints does not change the width of
a branch decomposition. An edge bijection transfers the leaf map, while the
vertex embedding gives a bijection of each tree-edge boundary. This is used
when the compact graph in Algorithm (9.9) is returned to the caller's labels.
-/

@[expose] public section
namespace GraphMinor.Compute

/-- Transport a decomposition along a vertex embedding and an endpoint-preserving
edge bijection. Vertices outside the embedding may occur in the target, but the
edge bijection ensures that they are isolated. -/
theorem alg99_branchDecomp_embed {t B : ℕ} (C D : ComputeDigraph)
    (f : Fin C.numVerts → Fin D.numVerts) (hf : Function.Injective f)
    (e : Fin C.numEdges ≃ Fin D.numEdges)
    (hhead : ∀ i, D.head (e i) = f (C.head i))
    (htail : ∀ i, D.tail (e i) = f (C.tail i))
    (T : SimpleGraph (Fin t)) [DecidableRel T.Adj] (τ : Fin C.numEdges → Fin t)
    (hbd : IsDigraphBranchDecompOfWidthLe B C T τ) :
    IsDigraphBranchDecompOfWidthLe B D T (τ ∘ e.symm) := by
  classical
  have hinc : ∀ v i, digraphIncident D (f v) (e i) ↔ digraphIncident C v i := by
    intro v i
    simp only [digraphIncident, hhead, htail, hf.eq_iff]
  have hbound : ∀ g, digraphTreeEdgeCutVerts D T (τ ∘ e.symm) g =
      (digraphTreeEdgeCutVerts C T τ g).image f := by
    intro g
    ext v
    simp only [digraphTreeEdgeCutVerts, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_image]
    constructor
    · rintro ⟨i, j, hi, hj, hr⟩
      have hv : ∃ x, f x = v := by
        rcases hi with h | h
        · have hm := hhead (e.symm i)
          simp only [e.apply_symm_apply] at hm
          exact ⟨C.head (e.symm i), hm.symm.trans h⟩
        · have hm := htail (e.symm i)
          simp only [e.apply_symm_apply] at hm
          exact ⟨C.tail (e.symm i), hm.symm.trans h⟩
      obtain ⟨x, rfl⟩ := hv
      refine ⟨x, ⟨e.symm i, e.symm j, ?_, ?_, hr⟩, rfl⟩
      · exact (hinc x (e.symm i)).1 (by simpa using hi)
      · exact (hinc x (e.symm j)).1 (by simpa using hj)
    · rintro ⟨x, ⟨i, j, hi, hj, hr⟩, rfl⟩
      exact ⟨e i, e j, (hinc x i).2 hi, (hinc x j).2 hj, by simpa using hr⟩
  refine ⟨hbd.1, ?_, ?_⟩
  · refine ⟨?_, ?_, ?_⟩
    · intro i _
      exact hbd.2.1.1 (Set.mem_univ _)
    · intro i _ j _ hij
      exact e.symm.injective (hbd.2.1.2.1 (Set.mem_univ _) (Set.mem_univ _) hij)
    · intro v hv
      obtain ⟨i, _, hi⟩ := hbd.2.1.2.2 hv
      exact ⟨e i, Set.mem_univ _, by simpa using hi⟩
  · intro g hg
    unfold digraphTreeEdgeOrder
    rw [hbound, Finset.card_image_of_injective _ hf]
    exact hbd.2.2 g hg

end GraphMinor.Compute
