module

public import GraphMinor.Mader.ApexForest
public import GraphMinor.Kruskal.EmbeddedChainVertices

/-!
# Vertices of a subdivided forest with added vertices

Only the forest edges need subdivision. Thus the chain vertices are the
chosen vertices together with the chain vertices inside each forest
component. We give the equivalence explicitly before mapping those
components into distinct target trees.
-/

@[expose] public section

namespace GraphMinor.Mader

open Graph Kruskal

variable {k n : ℕ} (s : Fin n → OrderedTree)
    (f : Fin n → List ℕ → Fin k → ℕ) (c : Fin k × Fin k → ℕ)
    (len : ∀ i, E(rootedGraph (s i).toRootedTree) → ℕ)

/-- The attachment and core edges have no internal vertices. -/
def apexInternalCount : ApexForestEdge s f c → ℕ
  | .inl ⟨i, e⟩ => len i e
  | .inr _ => 0

/-- Simultaneously subdivide just the forest edges. -/
noncomputable abbrev apexChains :=
  edgeChains (apexForestLeft s f c) (apexForestRight s f c)
    (apexInternalCount s f c len)

/-- The local chain graph of a forest component. -/
noncomputable abbrev componentChains (i : Fin n) :=
  edgeChains (s i).addressParent (s i).addressChild (len i)

/-- Insert a chosen vertex or a local chain vertex into the whole chain graph. -/
def assembleApexChainVertex :
    (Fin k ⊕ Σ i, V(componentChains s len i)) → V(apexChains s f c len)
  | .inl a => ⟨.inl (.inl a), trivial⟩
  | .inr ⟨i, ⟨.inl v, _⟩⟩ => ⟨.inl (.inr ⟨i, v⟩), trivial⟩
  | .inr ⟨i, ⟨.inr (e, j), hj⟩⟩ => ⟨.inr (.inl ⟨i, e⟩, j), hj⟩

/-- Separate the chosen vertices from the local chain vertices. -/
def decomposeApexChainVertex (x : V(apexChains s f c len)) :
    Fin k ⊕ Σ i, V(componentChains s len i) := by
  obtain ⟨x, hx⟩ := x
  cases x with
  | inl v =>
    cases v with
    | inl a => exact .inl a
    | inr v => exact .inr ⟨v.1, ⟨.inl v.2, trivial⟩⟩
  | inr e =>
    obtain ⟨e, j⟩ := e
    cases e with
    | inl e => exact .inr ⟨e.1, ⟨.inr (e.2, j), hx⟩⟩
    | inr e => exact (Nat.not_lt_zero j hx).elim

/-- Decomposing an assembled chain vertex recovers the original vertex. -/
theorem decompose_assembleApexChainVertex
    (x : Fin k ⊕ Σ i, V(componentChains s len i)) :
    decomposeApexChainVertex s f c len (assembleApexChainVertex s f c len x) = x := by
  cases x with
  | inl a => rfl
  | inr x =>
    obtain ⟨i, ⟨x, hx⟩⟩ := x
    cases x <;> rfl

/-- Assembling a decomposed chain vertex recovers the original vertex. -/
theorem assemble_decomposeApexChainVertex (x : V(apexChains s f c len)) :
    assembleApexChainVertex s f c len (decomposeApexChainVertex s f c len x) = x := by
  obtain ⟨x, hx⟩ := x
  cases x with
  | inl v => cases v <;> rfl
  | inr e =>
    obtain ⟨e, j⟩ := e
    cases e with
    | inl e => rfl
    | inr e => exact (Nat.not_lt_zero j hx).elim

/-- All chain vertices split into chosen vertices and local component chains. -/
def apexChainVertexEquiv :
    V(apexChains s f c len) ≃ (Fin k ⊕ Σ i, V(componentChains s len i)) where
  toFun := decomposeApexChainVertex s f c len
  invFun := assembleApexChainVertex s f c len
  left_inv := assemble_decomposeApexChainVertex s f c len
  right_inv := decompose_assembleApexChainVertex s f c len

/-- Inserting a component chain preserves the start of each segment. -/
theorem assemble_component_stem (i : Fin n) (e : E(rootedGraph (s i).toRootedTree))
    (q : ℕ) (hx : chainStem (s i).addressParent e q ∈ V(componentChains s len i)) :
    (assembleApexChainVertex s f c len
      (.inr ⟨i, ⟨chainStem (s i).addressParent e q, hx⟩⟩)).val =
      chainStem (apexForestLeft s f c) (.inl ⟨i, e⟩) q := by
  cases q <;> rfl

/-- Inserting a component chain preserves the end of each segment. -/
theorem assemble_component_finish (i : Fin n) (e : E(rootedGraph (s i).toRootedTree))
    (q : ℕ) (hx : chainFinish (s i).addressChild (len i) (e, q) ∈
      V(componentChains s len i)) :
    (assembleApexChainVertex s f c len
      (.inr ⟨i, ⟨chainFinish (s i).addressChild (len i) (e, q), hx⟩⟩)).val =
      chainFinish (apexForestRight s f c) (apexInternalCount s f c len) (.inl ⟨i, e⟩, q) := by
  classical
  unfold chainFinish
  dsimp only [apexInternalCount]
  by_cases h : q = 2 * len i e
  · simp only [h, ↓reduceIte]
    rfl
  · simp only [h, ↓reduceIte]
    rfl

end GraphMinor.Mader
