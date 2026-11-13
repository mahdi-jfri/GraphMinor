module

public import GraphMinor.Mader.ApexChainVertices

/-!
# Edges of a subdivided forest with added vertices

Each edge of a component chain retains its component index. Every
attachment or core edge has just its final chain segment, at position
zero. These alternatives give an explicit equivalence on chain edges.
-/

@[expose] public section

namespace GraphMinor.Mader

open Graph Kruskal

variable {k n : ℕ} (s : Fin n → OrderedTree)
    (f : Fin n → List ℕ → Fin k → ℕ) (c : Fin k × Fin k → ℕ)
    (len : ∀ i, E(rootedGraph (s i).toRootedTree) → ℕ)

/-- Insert a local chain segment or an unsubdivided edge into the whole chain graph. -/
def assembleApexChainEdge :
    ((Σ i, E(componentChains s len i)) ⊕ (AttachmentEdge s f ⊕ CoreEdge c)) →
      E(apexChains s f c len)
  | .inl ⟨i, ⟨(e, j), hj⟩⟩ => ⟨(.inl ⟨i, e⟩, j), hj⟩
  | .inr e => ⟨(.inr e, 0), Or.inl rfl⟩

/-- Separate the local chain segments from the unsubdivided edges. -/
def decomposeApexChainEdge (d : E(apexChains s f c len)) :
    (Σ i, E(componentChains s len i)) ⊕ (AttachmentEdge s f ⊕ CoreEdge c) := by
  obtain ⟨⟨e, j⟩, hj⟩ := d
  cases e with
  | inl e => exact .inl ⟨e.1, ⟨(e.2, j), hj⟩⟩
  | inr e => exact .inr e

/-- Decomposing an assembled edge recovers the local segment or added edge. -/
theorem decompose_assembleApexChainEdge
    (d : (Σ i, E(componentChains s len i)) ⊕ (AttachmentEdge s f ⊕ CoreEdge c)) :
    decomposeApexChainEdge s f c len (assembleApexChainEdge s f c len d) = d := by
  cases d with
  | inl d => obtain ⟨i, ⟨⟨e, j⟩, hj⟩⟩ := d; rfl
  | inr e => rfl

/-- An unsubdivided edge has only the segment at position zero. -/
theorem assemble_decomposeApexChainEdge (d : E(apexChains s f c len)) :
    assembleApexChainEdge s f c len (decomposeApexChainEdge s f c len d) = d := by
  obtain ⟨⟨e, j⟩, hj⟩ := d
  cases e with
  | inl e => rfl
  | inr e =>
    have hj' : j = 0 := by
      change j = 2 * 0 ∨ j % 2 = 1 ∧ j < 2 * 0 at hj
      omega
    subst j
    rfl

/-- All chain edges split into local component segments and unsubdivided edges. -/
def apexChainEdgeEquiv : E(apexChains s f c len) ≃
    ((Σ i, E(componentChains s len i)) ⊕ (AttachmentEdge s f ⊕ CoreEdge c)) where
  toFun := decomposeApexChainEdge s f c len
  invFun := assembleApexChainEdge s f c len
  left_inv := assemble_decomposeApexChainEdge s f c len
  right_inv := decompose_assembleApexChainEdge s f c len

end GraphMinor.Mader
