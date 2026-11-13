module

public import GraphMinor.Mader.ApexComponentLinks

/-!
# All links of the forest attachment subdivision

Component-chain segments use their tree link proofs. Attachment and core
edges are not subdivided and keep their two endpoint images. Splitting
chain edges into these cases proves link preservation for the whole graph.
-/

public section

namespace GraphMinor.Mader

open Graph Kruskal

variable {k n m : ℕ} {s : Fin n → OrderedTree} {t : Fin m → OrderedTree}
    (σ : Fin n ↪ Fin m) (φ : ∀ i, OrderedTree.AddressEmbedding (s i) (t (σ i)))
    (f : Fin n → List ℕ → Fin k → ℕ) (g : Fin m → List ℕ → Fin k → ℕ)
    (c d : Fin k × Fin k → ℕ)
    (hf : ∀ i (p : V(rootedGraph (s i).toRootedTree)) a,
      f i p.val a ≤ g (σ i) ((φ i).vertices p).val a)
    (hc : ∀ p, c p ≤ d p)

/-- Unsubdivided attachment and core edges retain the images of their two ends. -/
theorem apexChainLinks_added (e : AttachmentEdge s f ⊕ CoreEdge c) :
    (apexForest t g d).IsLink
      (apexChainEdges σ φ f g c d hf hc
        (assembleApexChainEdge s f c (fun i ↦ (φ i).internalCount) (.inr e)))
      (apexChainVertices f c σ φ ⟨.inl (apexForestLeft s f c (.inr e)), trivial⟩)
      (apexChainVertices f c σ φ ⟨.inl (apexForestRight s f c (.inr e)), trivial⟩) := by
  cases e with
  | inl e =>
    obtain ⟨⟨i, v⟩, a, j⟩ := e
    exact Or.inl ⟨rfl, rfl⟩
  | inr e =>
    obtain ⟨a, b, j⟩ := e
    exact Or.inl ⟨rfl, rfl⟩

/-- The assembled edge and vertex maps preserve every link of the chain graph. -/
theorem apexChainLinks
    (e : E(apexChains s f c (fun i ↦ (φ i).internalCount)))
    (x y : V(apexChains s f c (fun i ↦ (φ i).internalCount)))
    (h : (apexChains s f c (fun i ↦ (φ i).internalCount)).IsLink e.val x.val y.val) :
    (apexForest t g d).IsLink (apexChainEdges σ φ f g c d hf hc e)
      (apexChainVertices f c σ φ x) (apexChainVertices f c σ φ y) := by
  classical
  obtain ⟨e, rfl⟩ := (apexChainEdgeEquiv s f c
    (fun i ↦ (φ i).internalCount)).symm.surjective e
  cases e with
  | inl e =>
    obtain ⟨i, e⟩ := e
    let u := chainStem (s i).addressParent e.val.1 (e.val.2 / 2)
    let v := chainFinish (s i).addressChild (φ i).internalCount e.val
    have hlocal : (φ i).chains.IsLink e.val u v := ⟨e.property, Or.inl ⟨rfl, rfl⟩⟩
    let u' : V((φ i).chains) := ⟨u, hlocal.left_mem⟩
    let v' : V((φ i).chains) := ⟨v, hlocal.right_mem⟩
    let U := assembleApexChainVertex s f c (fun i ↦ (φ i).internalCount) (.inr ⟨i, u'⟩)
    let V' := assembleApexChainVertex s f c (fun i ↦ (φ i).internalCount) (.inr ⟨i, v'⟩)
    have hu := assemble_component_stem s f c (fun i ↦ (φ i).internalCount)
      i e.val.1 (e.val.2 / 2) hlocal.left_mem
    have hv := assemble_component_finish s f c (fun i ↦ (φ i).internalCount)
      i e.val.1 e.val.2 hlocal.right_mem
    have himg := apexChainLinks_component σ φ f g c d hf hc i e u' v' hlocal
    rcases h.2 with ⟨hx, hy⟩ | ⟨hx, hy⟩
    · have hx' : x = U := Subtype.ext (hx.trans hu.symm)
      have hy' : y = V' := Subtype.ext (hy.trans hv.symm)
      subst x
      subst y
      exact himg
    · have hx' : x = V' := Subtype.ext (hx.trans hv.symm)
      have hy' : y = U := Subtype.ext (hy.trans hu.symm)
      subst x
      subst y
      exact himg.symm
  | inr e =>
    let U : V(apexChains s f c (fun i ↦ (φ i).internalCount)) :=
      ⟨.inl (apexForestLeft s f c (.inr e)), trivial⟩
    let V' : V(apexChains s f c (fun i ↦ (φ i).internalCount)) :=
      ⟨.inl (apexForestRight s f c (.inr e)), trivial⟩
    have himg := apexChainLinks_added σ φ f g c d hf hc e
    have h' : (apexChains s f c (fun i ↦ (φ i).internalCount)).IsLink
        (.inr e, 0) x.val y.val := h
    have hh : (x.val = U.val ∧ y.val = V'.val) ∨
        (x.val = V'.val ∧ y.val = U.val) := by
      simpa only [assembleApexChainEdge, chainStem, chainFinish, apexInternalCount,
        Nat.zero_div, Nat.mul_zero, ↓reduceIte] using h'.2
    rcases hh with ⟨hx, hy⟩ | ⟨hx, hy⟩
    · have hx' : x = U := Subtype.ext hx
      have hy' : y = V' := Subtype.ext hy
      subst x
      subst y
      exact himg
    · have hx' : x = V' := Subtype.ext hx
      have hy' : y = U := Subtype.ext hy
      subst x
      subst y
      exact himg.symm

end GraphMinor.Mader
