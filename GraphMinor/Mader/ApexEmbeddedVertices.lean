module

public import GraphMinor.Mader.ApexChainVertices

/-!
# Injective vertex maps for forest attachment subdivisions

Map the chosen vertices identically. In each forest component use its
address-chain embedding, and use the injective component matching to keep
different components apart. The chain decomposition makes the combined
vertex map injective without any new path-separation argument.
-/

@[expose] public section

namespace GraphMinor.Mader

open Graph Kruskal

variable {k n m : ℕ} {s : Fin n → OrderedTree} {t : Fin m → OrderedTree}
    (f : Fin n → List ℕ → Fin k → ℕ) (c : Fin k × Fin k → ℕ)
    (σ : Fin n ↪ Fin m) (φ : ∀ i, OrderedTree.AddressEmbedding (s i) (t (σ i)))

/-- The vertex embedding on the original forest vertices. -/
def forestVertexEmbedding : ForestVertex s ↪ ForestVertex t :=
  Function.Embedding.sigmaMap σ (fun i ↦ (φ i).vertices)

/-- The local chain vertex map, with its target-address membership proof. -/
def componentChainVertices (i : Fin n) : V((φ i).chains) ↪ V(rootedGraph (t (σ i)).toRootedTree) where
  toFun x := ⟨(φ i).chainVertices x, (φ i).rawVertex_mem x⟩
  inj' := by
    intro x y hxy
    exact (φ i).chainVertices.injective
      (congrArg (fun z : V(rootedGraph (t (σ i)).toRootedTree) ↦ z.val) hxy)

/-- The combined chain vertex map fixes the chosen vertices and maps
component chains into distinct target components. -/
def apexChainVertices :
    V(apexChains s f c (fun i ↦ (φ i).internalCount)) ↪ (Fin k ⊕ ForestVertex t) :=
  (apexChainVertexEquiv s f c (fun i ↦ (φ i).internalCount)).toEmbedding.trans
    (Function.Embedding.sumMap (Function.Embedding.refl _)
      (Function.Embedding.sigmaMap σ (componentChainVertices σ φ)))

/-- An original chosen vertex stays at the same chosen vertex. -/
theorem apexChainVertices_chosen (a : Fin k) :
    apexChainVertices f c σ φ ⟨.inl (.inl a), trivial⟩ = .inl a := by rfl

/-- An original forest vertex is sent by its component's address map. -/
theorem apexChainVertices_forest (i : Fin n) (v : V(rootedGraph (s i).toRootedTree)) :
    apexChainVertices f c σ φ ⟨.inl (.inr ⟨i, v⟩), trivial⟩ =
      .inr ⟨σ i, (φ i).vertices v⟩ := by rfl

/-- A local chain vertex has the same image in the whole graph as in its
component, with the target component index prefixed. -/
theorem apexChainVertices_component (i : Fin n) (v : V((φ i).chains)) :
    apexChainVertices f c σ φ
      (assembleApexChainVertex s f c (fun i ↦ (φ i).internalCount) (.inr ⟨i, v⟩)) =
      .inr ⟨σ i, componentChainVertices σ φ i v⟩ := by
  change Function.Embedding.sumMap _ _
    (decomposeApexChainVertex s f c (fun i ↦ (φ i).internalCount)
      (assembleApexChainVertex s f c (fun i ↦ (φ i).internalCount) (.inr ⟨i, v⟩))) = _
  rw [decompose_assembleApexChainVertex]
  rfl

end GraphMinor.Mader
