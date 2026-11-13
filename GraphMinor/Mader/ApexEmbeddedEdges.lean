module

public import GraphMinor.Mader.ApexEmbeddedVertices
public import GraphMinor.Mader.ApexChainEdges
public import GraphMinor.Kruskal.EmbeddedChainLinks
public import Mathlib.Data.Fin.Embedding

/-!
# Injective edge maps for forest attachment subdivisions

Tree-chain segments use the injective edge maps of their components.
Attachment and core edges retain their parallel-edge indices. The label
inequalities ensure that those indices fit in the target multiplicities.
The three edge kinds are disjoint, so the assembled edge map is injective.
-/

@[expose] public section

namespace GraphMinor.Mader

open Graph Kruskal

variable {k n m : ℕ} {s : Fin n → OrderedTree} {t : Fin m → OrderedTree}
    (σ : Fin n ↪ Fin m) (φ : ∀ i, OrderedTree.AddressEmbedding (s i) (t (σ i)))

/-- A local chain edge maps to an actual edge of its target tree. -/
noncomputable def componentChainEdges (i : Fin n) :
    E((φ i).chains) ↪ E(rootedGraph (t (σ i)).toRootedTree) where
  toFun e := ⟨(φ i).chainEdges e, (φ i).chainEdges_mem e⟩
  inj' := by
    intro e h heh
    exact (φ i).chainEdges.injective
      (congrArg (fun z : E(rootedGraph (t (σ i)).toRootedTree) ↦ z.val) heh)

variable (f : Fin n → List ℕ → Fin k → ℕ) (g : Fin m → List ℕ → Fin k → ℕ)
    (c d : Fin k × Fin k → ℕ)
    (hf : ∀ i (p : V(rootedGraph (s i).toRootedTree)) a,
      f i p.val a ≤ g (σ i) ((φ i).vertices p).val a)
    (hc : ∀ p, c p ≤ d p)

/-- Attachment edges map to the image forest vertex, the same chosen
vertex, and the same index among parallel edges. -/
def attachmentEdgeEmbedding : AttachmentEdge s f ↪ AttachmentEdge t g :=
  Function.Embedding.sigmaMap (forestVertexEmbedding σ φ) (fun v ↦
    Function.Embedding.sigmaMap (Function.Embedding.refl _) (fun a ↦
      Fin.castLEEmb (hf v.1 v.2 a)))

/-- Core edges retain their two chosen ends and their parallel-edge index. -/
def coreEdgeEmbedding : CoreEdge c ↪ CoreEdge d :=
  Function.Embedding.sigmaMap (Function.Embedding.refl _) (fun a ↦
    Function.Embedding.sigmaMap (Function.Embedding.refl _) (fun b ↦
      Fin.castLEEmb (hc (a, b))))

/-- All chain edges map injectively into the target attachment graph. -/
noncomputable def apexChainEdges :
    E(apexChains s f c (fun i ↦ (φ i).internalCount)) ↪ ApexForestEdge t g d :=
  (apexChainEdgeEquiv s f c (fun i ↦ (φ i).internalCount)).toEmbedding.trans
    (Function.Embedding.sumMap
      (Function.Embedding.sigmaMap σ (componentChainEdges σ φ))
      (Function.Embedding.sumMap (attachmentEdgeEmbedding σ φ f g hf)
        (coreEdgeEmbedding c d hc)))

/-- A component-chain segment uses its component's edge map. -/
theorem apexChainEdges_component (i : Fin n) (e : E((φ i).chains)) :
    apexChainEdges σ φ f g c d hf hc
      (assembleApexChainEdge s f c (fun i ↦ (φ i).internalCount) (.inl ⟨i, e⟩)) =
      .inl ⟨σ i, componentChainEdges σ φ i e⟩ := by
  change Function.Embedding.sumMap _
    (Function.Embedding.sumMap (attachmentEdgeEmbedding σ φ f g hf) (coreEdgeEmbedding c d hc))
    (decomposeApexChainEdge s f c (fun i ↦ (φ i).internalCount)
      (assembleApexChainEdge s f c (fun i ↦ (φ i).internalCount) (.inl ⟨i, e⟩))) = _
  rw [decompose_assembleApexChainEdge]
  rfl

end GraphMinor.Mader
