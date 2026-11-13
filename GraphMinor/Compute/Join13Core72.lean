module

public import GraphMinor.Compute.Join13Defs

/-!
# The core input for the (7.2) call to (4.1)

The caller's decomposition uses the edge order of `toMultiComputeDigraph`.
We keep that order in the core input, so the packed leaf assignment can be read
directly from the decomposition code. For at most one edge the empty tree code
is replaced by the one-node convention of the core program.
-/

@[expose] public section
namespace GraphMinor.Compute

/-- The leaf assignment in the caller's edge order. -/
def multiTau72 {B : ℕ} (x : Alg41CodeInput 0 B) (e : Fin x.G.numEdges) : Fin (tCode x) :=
  if ht : 0 < bdNumTreeVerts x.bdCode then
    let v := bdTau x.G x.bdCode ht e
    ⟨v.1, by simpa only [tCode, ht, ↓reduceIte] using v.2⟩
  else ⟨0, htCode x⟩

/-- Convert the unrooted (7.2) input to the core (4.1) input without reordering
its individual edges. -/
noncomputable def multiCoreInput72 {n B : ℕ} (G : MultiDigraph n) (bdCode : List ℕ)
    (hbd : IsValidBranchDecompCode B G bdCode) : Alg41CoreInput 0 B :=
  let x := alg41EmptyCodeInput G bdCode hbd
  Alg41CoreInput.ofBranchDecompOrSmall G.toMultiComputeDigraph ∅ (by simp)
    (tCode x) (htCode x) (tCode_le x)
    (normParentCodeFn x) (normParentCodeFn_zero x) (normParentCodeFn_lt x)
    (multiTau72 x)
    (by
      rcases hbd.2.2.2 with ⟨hm, ht, _⟩ | ⟨_, ht, _, hpar, _, hdecomp⟩
      · exact Or.inl ⟨hm, by simp [x, tCode, ht]⟩
      · right
        have htc : bdNumTreeVerts bdCode = tCode x := by simp [tCode, x, ht]
        have htree : parentTree (bdNumTreeVerts bdCode) (normParentCodeFn x) = bdTree bdCode :=
          parentTree_normParentCodeFn_eq_bdTree x ht hpar
        have hdecomp' : IsDigraphBranchDecompOfWidthLe B G.toMultiComputeDigraph
            (parentTree (bdNumTreeVerts bdCode) (normParentCodeFn x)) (bdTau G bdCode ht) :=
          isDigraphBranchDecompOfWidthLe_of_eq htree.symm hdecomp
        exact isDigraphBranchDecompOfWidthLe_cast_t (G := G.toMultiComputeDigraph) htc (normParentCodeFn x)
          (bdTau G bdCode ht) (multiTau72 x)
          (fun e => by simp [multiTau72, x, alg41EmptyCodeInput, ht]) hdecomp')

/-- The graph size is unchanged by the input conversion. -/
theorem alg41CoreSize_multiCoreInput72 {n B : ℕ} (G : MultiDigraph n) (bdCode : List ℕ)
    (hbd : IsValidBranchDecompCode B G bdCode) :
    alg41CoreSize (multiCoreInput72 G bdCode hbd) = G.numEdges + n + 1 := by
  rfl

/-- The parent entry at zero is normalized to zero. Other parent entries are
read from the caller's decomposition code. -/
theorem multiCoreInput72_parent {n B : ℕ} (G : MultiDigraph n) (bdCode : List ℕ)
    (hbd : IsValidBranchDecompCode B G bdCode) (z : ℕ)
    (hz : z < (multiCoreInput72 G bdCode hbd).t) :
    (multiCoreInput72 G bdCode hbd).p z =
      if z = 0 then 0 else bdParent bdCode z := by
  change z < tCode (alg41EmptyCodeInput G bdCode hbd) at hz
  change normParentCodeFn (alg41EmptyCodeInput G bdCode hbd) z = _
  unfold normParentCodeFn
  split_ifs with hzero
  · rfl
  · unfold pCode
    have hzpos : 0 < z := by omega
    have htpos : 0 < bdNumTreeVerts bdCode := by
      by_contra ht
      have hz1 : z < 1 := by simpa [tCode, alg41EmptyCodeInput, ht] using hz
      omega
    rcases hbd.2.2.2 with ⟨_, htz, _⟩ | ⟨_, _, _, hp, _, _⟩
    · omega
    · have hz' : z < bdNumTreeVerts bdCode := by
        simpa [tCode, alg41EmptyCodeInput, htpos] using hz
      rw [ite_eq_left (hp z hzpos hz')]

end GraphMinor.Compute
