module

public import GraphMinor.Compute.Join13Core72

/-!
# Decomposition-code slices for the (7.2) core input

For a nonempty tree code, the normalized parent and leaf arrays of the core
input are the corresponding slices of the caller's code. The empty tree code
uses one zero parent and zero leaf assignments.
-/

@[expose] public section
namespace GraphMinor.Compute

/-- The effective core tree has one vertex exactly when the caller's tree code
is empty. -/
theorem multiCoreInput72_t {n B : ℕ} (G : MultiDigraph n) (bdCode : List ℕ)
    (hbd : IsValidBranchDecompCode B G bdCode) :
    (multiCoreInput72 G bdCode hbd).t =
      if 0 < bdNumTreeVerts bdCode then bdNumTreeVerts bdCode else 1 := by rfl

/-- For a positive tree size, every parent is copied from the valid code. -/
theorem multiCoreInput72_parent_eq_bdParent {n B : ℕ} (G : MultiDigraph n) (bdCode : List ℕ)
    (hbd : IsValidBranchDecompCode B G bdCode) (ht : 0 < bdNumTreeVerts bdCode)
    (z : ℕ) (hz : z < (multiCoreInput72 G bdCode hbd).t) :
    (multiCoreInput72 G bdCode hbd).p z = bdParent bdCode z := by
  rw [multiCoreInput72_parent G bdCode hbd z hz]
  by_cases hz0 : z = 0
  · subst z
    simp only [↓reduceIte]
    rcases hbd.2.2.2 with ⟨_, ht0, _⟩ | ⟨_, _, hroot, _⟩
    · omega
    · exact hroot.symm
  · rw [ite_eq_right hz0]

/-- In the caller's edge order, the leaf index is read directly from its code. -/
theorem multiCoreInput72_leaf {n B : ℕ} (G : MultiDigraph n) (bdCode : List ℕ)
    (hbd : IsValidBranchDecompCode B G bdCode) (ht : 0 < bdNumTreeVerts bdCode)
    (e : Fin G.numEdges) :
    ((multiCoreInput72 G bdCode hbd).τ e).1 = bdCode.getD (2 + bdNumTreeVerts bdCode + e.1) 0 := by
  have hgood : bdCode.getD (2 + bdNumTreeVerts bdCode + e.1) 0 < bdNumTreeVerts bdCode := by
    rcases hbd.2.2.2 with ⟨_, ht0, _⟩ | ⟨_, _, _, _, hτ, _⟩
    · omega
    · exact hτ e
  change (multiTau72 (alg41EmptyCodeInput G bdCode hbd) e).1 = _
  simp only [multiTau72, alg41EmptyCodeInput, ht, ↓reduceDIte]
  change (bdTau G bdCode ht e).1 = _
  unfold bdTau
  rw [dite_eq_left hgood]

/-- The parent array is the slice starting after the two-word code header. -/
theorem multiCoreInput72_parentWords {n B : ℕ} (G : MultiDigraph n) (bdCode : List ℕ)
    (hbd : IsValidBranchDecompCode B G bdCode) (ht : 0 < bdNumTreeVerts bdCode) :
    (bdCode.drop 2).take (bdNumTreeVerts bdCode) =
      List.ofFn (fun z : Fin (multiCoreInput72 G bdCode hbd).t =>
        (multiCoreInput72 G bdCode hbd).p z.1) := by
  have hlen : bdCode.length = 2 + bdNumTreeVerts bdCode + G.numEdges := by
    rw [← hbd.1]
    exact hbd.2.2.1
  have htree : (multiCoreInput72 G bdCode hbd).t = bdNumTreeVerts bdCode := by rw [multiCoreInput72_t, ite_eq_left ht]
  apply List.ext_getElem (by simp only [List.length_take, List.length_drop, List.length_ofFn, hlen, htree]; omega)
  intro i hi hj
  have hi' : i < bdNumTreeVerts bdCode := by simpa [htree] using hj
  rw [List.getElem_take, List.getElem_drop, List.getElem_ofFn,
    multiCoreInput72_parent_eq_bdParent G bdCode hbd ht i (by omega)]
  unfold bdParent
  rw [List.getD_eq_getElem _ _ (by omega)]

/-- The leaf array is the slice following all parent entries. -/
theorem multiCoreInput72_leafWords {n B : ℕ} (G : MultiDigraph n) (bdCode : List ℕ)
    (hbd : IsValidBranchDecompCode B G bdCode) (ht : 0 < bdNumTreeVerts bdCode) :
    bdCode.drop (2 + bdNumTreeVerts bdCode) =
      List.ofFn (fun e : Fin G.numEdges => ((multiCoreInput72 G bdCode hbd).τ e).1) := by
  have hlen : bdCode.length = 2 + bdNumTreeVerts bdCode + G.numEdges := by
    rw [← hbd.1]
    exact hbd.2.2.1
  apply List.ext_getElem (by simp [List.length_drop, hlen])
  intro i hi hj
  have hi' : i < G.numEdges := by simpa using hj
  rw [List.getElem_drop, List.getElem_ofFn, multiCoreInput72_leaf G bdCode hbd ht ⟨i, hi'⟩,
    List.getD_eq_getElem _ _ (by omega)]

/-- The empty tree code gives the one-node parent array of the core convention. -/
theorem multiCoreInput72_parentWords_zero {n B : ℕ} (G : MultiDigraph n) (bdCode : List ℕ)
    (hbd : IsValidBranchDecompCode B G bdCode) (ht : bdNumTreeVerts bdCode = 0) :
    List.ofFn (fun z : Fin (multiCoreInput72 G bdCode hbd).t =>
      (multiCoreInput72 G bdCode hbd).p z.1) = [0] := by
  have htree : (multiCoreInput72 G bdCode hbd).t = 1 := by simp [multiCoreInput72_t, ht]
  apply List.ext_getElem (by simp [htree])
  intro i hi hj
  have hi0 : i = 0 := by simpa using hj
  subst i
  rw [List.getElem_ofFn, multiCoreInput72_parent G bdCode hbd 0 (by omega)]
  simp

/-- With an empty tree code all effective leaf indices are zero. -/
theorem multiCoreInput72_leafWords_zero {n B : ℕ} (G : MultiDigraph n) (bdCode : List ℕ)
    (hbd : IsValidBranchDecompCode B G bdCode) (ht : bdNumTreeVerts bdCode = 0) :
    List.ofFn (fun e : Fin G.numEdges => ((multiCoreInput72 G bdCode hbd).τ e).1) =
      List.replicate G.numEdges 0 := by
  have hτ : ∀ e : Fin G.numEdges, ((multiCoreInput72 G bdCode hbd).τ e).1 = 0 := by
    intro e
    change (multiTau72 (alg41EmptyCodeInput G bdCode hbd) e).1 = _
    simp [multiTau72, alg41EmptyCodeInput, ht]
  simp only [hτ, List.ofFn_const]

end GraphMinor.Compute
