module

public import GraphMinor.Mader.ApexEmbeddedEdges

/-!
# Links within the embedded forest components

Each component chain already maps its links to links of the target tree.
Prefixing the target component index and inserting the forest edge kind
turns those links into links of the full attachment graph.
-/

public section

namespace GraphMinor.Mader

open Graph Kruskal

/-- A link in an ordered-tree component is also a link of the full graph. -/
theorem apexForest_link_of_component {k m : ℕ} (t : Fin m → OrderedTree)
    (g : Fin m → List ℕ → Fin k → ℕ) (d : Fin k × Fin k → ℕ)
    (i : Fin m) (e : E(rootedGraph (t i).toRootedTree))
    (x y : V(rootedGraph (t i).toRootedTree))
    (h : (rootedGraph (t i).toRootedTree).IsLink e.val x.val y.val) :
    (apexForest t g d).IsLink (.inl ⟨i, e⟩) (.inr ⟨i, x⟩) (.inr ⟨i, y⟩) := by
  rcases h.2 with ⟨hx, hy⟩ | ⟨hx, hy⟩
  · have hx' : x = (t i).addressParent e := Subtype.ext hx
    have hy' : y = (t i).addressChild e := Subtype.ext hy
    subst x
    subst y
    exact Or.inl ⟨rfl, rfl⟩
  · have hx' : x = (t i).addressChild e := Subtype.ext hx
    have hy' : y = (t i).addressParent e := Subtype.ext hy
    subst x
    subst y
    exact Or.inr ⟨rfl, rfl⟩

/-- Links of component chains are preserved by the assembled vertex and
edge maps into the full target graph. -/
theorem apexChainLinks_component {k n m : ℕ} {s : Fin n → OrderedTree}
    {t : Fin m → OrderedTree} (σ : Fin n ↪ Fin m)
    (φ : ∀ i, OrderedTree.AddressEmbedding (s i) (t (σ i)))
    (f : Fin n → List ℕ → Fin k → ℕ) (g : Fin m → List ℕ → Fin k → ℕ)
    (c d : Fin k × Fin k → ℕ)
    (hf : ∀ i (p : V(rootedGraph (s i).toRootedTree)) a,
      f i p.val a ≤ g (σ i) ((φ i).vertices p).val a)
    (hc : ∀ p, c p ≤ d p) (i : Fin n)
    (e : E((φ i).chains)) (x y : V((φ i).chains))
    (h : (φ i).chains.IsLink e.val x.val y.val) :
    (apexForest t g d).IsLink
      (apexChainEdges σ φ f g c d hf hc
        (assembleApexChainEdge s f c (fun i ↦ (φ i).internalCount) (.inl ⟨i, e⟩)))
      (apexChainVertices f c σ φ
        (assembleApexChainVertex s f c (fun i ↦ (φ i).internalCount) (.inr ⟨i, x⟩)))
      (apexChainVertices f c σ φ
        (assembleApexChainVertex s f c (fun i ↦ (φ i).internalCount) (.inr ⟨i, y⟩))) := by
  rw [apexChainEdges_component, apexChainVertices_component, apexChainVertices_component]
  exact apexForest_link_of_component t g d (σ i) _ _ _ ((φ i).chainLinks e x y h)

end GraphMinor.Mader
