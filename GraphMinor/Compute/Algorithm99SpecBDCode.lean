module

public import GraphMinor.Compute.Algorithm99CompactEdges
public import GraphMinor.Compute.Algorithm99SpecBDTransport
public import GraphMinor.Compute.Join13BDSlice72

/-!
# Decomposition codes for the compact and original graphs

Compaction keeps every individual edge at the same active-pair index. A valid
code for the compact graph therefore remains valid after restoring the
original endpoint labels and the isolated deleted vertices.
-/

@[expose] public section
namespace GraphMinor.Compute

/-- The same serialized code decomposes the deleted graph and its compact
version, with the same width bound. -/
theorem alg99_validBDCode_of_compact {n B : ℕ} (G : MultiDigraph n)
    (Z : Finset (Fin n)) (code : List ℕ)
    (hbd : IsValidBranchDecompCode B ((G.deleteVertices Z).deleteVerticesCompact Z) code) :
    IsValidBranchDecompCode B (G.deleteVertices Z) code := by
  let C := (G.deleteVertices Z).deleteVerticesCompact Z
  let D := G.deleteVertices Z
  have hm : C.numEdges = D.numEdges := alg99_numEdges_compact G Z
  let e : Fin C.numEdges ≃ Fin D.numEdges := finCongr hm
  have hend : ∀ i, D.edgeEndpoints (e i) =
      Prod.map (compactEmb Z) (compactEmb Z) (C.edgeEndpoints i) :=
    alg99_compact_edgeEndpoints G Z
  obtain ⟨hmcode, htbound, hlen, hcase⟩ := hbd
  refine ⟨hmcode.trans hm, htbound, hlen, ?_⟩
  rcases hcase with hsmall | ⟨hlarge, ht, hp0, hp, hτ, hdec⟩
  · exact Or.inl ⟨by rw [← hm]; exact hsmall.1, hsmall.2⟩
  · refine Or.inr ⟨by rw [← hm]; exact hlarge, ht, hp0, hp, ?_, ?_⟩
    · intro i
      exact hτ (e.symm i)
    · have htrans := alg99_branchDecomp_embed C.toMultiComputeDigraph D.toMultiComputeDigraph
        (compactEmb Z) (compactEmb Z).injective e
        (fun i => congrArg Prod.snd (hend i)) (fun i => congrArg Prod.fst (hend i))
        (bdTree code) (bdTau C code ht) hdec
      apply isDigraphBranchDecompOfWidthLe_congr B D.toMultiComputeDigraph rfl _ htrans
      funext i
      rfl

/-- When the code is nontrivial, the prepared core tree and leaf assignment
still give its branch decomposition. -/
theorem alg99_multiCoreInput72_decomp {n B : ℕ} (G : MultiDigraph n)
    (code : List ℕ) (hbd : IsValidBranchDecompCode B G code) (hm : 2 ≤ G.numEdges) :
    let x := multiCoreInput72 G code hbd
    IsDigraphBranchDecompOfWidthLe B G.toMultiComputeDigraph (parentTree x.t x.p) x.τ := by
  let x := alg41EmptyCodeInput G code hbd
  rcases hbd.2.2.2 with hsmall | ⟨_, ht, _, hp, _, hdec⟩
  · omega
  · have htc : bdNumTreeVerts code = tCode x := by simp [tCode, x, ht]
    have htree : parentTree (bdNumTreeVerts code) (normParentCodeFn x) = bdTree code :=
      parentTree_normParentCodeFn_eq_bdTree x ht hp
    have hdec' : IsDigraphBranchDecompOfWidthLe B G.toMultiComputeDigraph
        (parentTree (bdNumTreeVerts code) (normParentCodeFn x)) (bdTau G code ht) :=
      isDigraphBranchDecompOfWidthLe_of_eq htree.symm hdec
    exact isDigraphBranchDecompOfWidthLe_cast_t (G := G.toMultiComputeDigraph)
      htc (normParentCodeFn x) (bdTau G code ht) (multiTau72 x)
      (fun e => by simp [multiTau72, x, alg41EmptyCodeInput, ht]) hdec'

end GraphMinor.Compute
