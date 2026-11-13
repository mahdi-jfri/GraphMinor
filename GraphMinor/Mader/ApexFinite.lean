module

public import GraphMinor.Mader.ApexForest

/-!
# Finiteness of forest attachment graphs

There are finitely many ordered components, and each has finitely many
vertices and edges. Each attachment and core multiplicity is a natural
number, so the constructed multigraph has finite vertex and edge sets.
-/

public section

namespace GraphMinor.Mader

open Graph Kruskal

instance forestVertex_finite {n : ℕ} (t : Fin n → OrderedTree) : Finite (ForestVertex t) := by
  let : ∀ i, Fintype V(rootedGraph (t i).toRootedTree) :=
    fun i ↦ (rootedGraph_finite (t i).toRootedTree).1.fintype
  exact inferInstance

instance forestEdge_finite {n : ℕ} (t : Fin n → OrderedTree) : Finite (ForestEdge t) := by
  let : ∀ i, Fintype E(rootedGraph (t i).toRootedTree) :=
    fun i ↦ (rootedGraph_finite (t i).toRootedTree).2.fintype
  exact inferInstance

/-- Both sets of the graph built from finite component and multiplicity
data are finite, without a uniform bound on the multiplicities. -/
theorem apexForest_finite {k n : ℕ} (t : Fin n → OrderedTree)
    (f : Fin n → List ℕ → Fin k → ℕ) (c : Fin k × Fin k → ℕ) :
    V(apexForest t f c).Finite ∧ E(apexForest t f c).Finite :=
  ⟨Set.toFinite _, Set.toFinite _⟩

end GraphMinor.Mader
