module

public import GraphMinor.Compute.GM02NumberedInstance
public import GraphMinor.Compute.GM02CompactEdges

/-!
# Numbering an actual child by computed vertex ranks

When the computed deletion set is the complement of an actual child's
vertex set, compact ranks give a bijection on precisely those vertices.
Apply the general numbered-instance construction with this bijection.
Its graph and matching are the pullbacks through the stored old names,
while feasibility and width retain their original meaning.
-/

@[expose] public section
namespace GraphMinor.Compute
open Graph Set Classical GraphMinor.GM02

/-- Number an actual child using the complement of its computed deletion set. -/
noncomputable def gm02CompactNumberedInstance {n : ℕ} {β : Type*}
    (G : Graph (Fin n) β) (A : Termination V(G)) (Z : Finset (Fin n))
    (hV : V(G) = {v : Fin n | v ∉ Z}) : GM02SimpleTerminatedInput :=
  gm02NumberedInstance G A ((Set.equivOfEq hV).trans (gm02CompactEquiv Z))

private theorem compact_numbering_inverse {n : ℕ} {β : Type*}
    (G : Graph (Fin n) β) (Z : Finset (Fin n))
    (hV : V(G) = {v : Fin n | v ∉ Z}) :
    (fun i => (((Set.equivOfEq hV).trans (gm02CompactEquiv Z)).symm i).val) =
      compactEmb Z := by
  funext i
  exact gm02CompactEquiv_symm_val Z i

/-- The compact child graph is exactly the original path graph on old names. -/
theorem gm02CompactNumberedInstance_graph {n : ℕ} {β : Type*}
    (G : Graph (Fin n) β) (A : Termination V(G)) (Z : Finset (Fin n))
    (hV : V(G) = {v : Fin n | v ∉ Z}) :
    (gm02CompactNumberedInstance G A Z hV).G = (pathGraph G).comap (compactEmb Z) := by
  unfold gm02CompactNumberedInstance
  rw [gm02NumberedInstance_graph, compact_numbering_inverse]

/-- The compact child matching uses the same old-name pullback. -/
theorem gm02CompactNumberedInstance_pairGraph {n : ℕ} {β : Type*}
    (G : Graph (Fin n) β) (A : Termination V(G)) (Z : Finset (Fin n))
    (hV : V(G) = {v : Fin n | v ∉ Z}) :
    (gm02CompactNumberedInstance G A Z hV).A.pairGraph =
      A.pairGraph.comap (compactEmb Z) := by
  unfold gm02CompactNumberedInstance
  rw [gm02NumberedInstance_pairGraph, compact_numbering_inverse]

/-- The child index is unchanged by compact numbering. -/
theorem gm02CompactNumberedInstance_index {n : ℕ} {β : Type*}
    (G : Graph (Fin n) β) (A : Termination V(G)) (Z : Finset (Fin n))
    (hV : V(G) = {v : Fin n | v ∉ Z}) :
    (gm02CompactNumberedInstance G A Z hV).A.index = A.index :=
  gm02NumberedInstance_index G A _

/-- A compact recursive feasibility answer applies to the actual child. -/
theorem gm02CompactNumberedInstance_feasible_iff {n : ℕ} {β : Type*}
    (G : Graph (Fin n) β) (A : Termination V(G)) (Z : Finset (Fin n))
    (hV : V(G) = {v : Fin n | v ∉ Z}) :
    (gm02CompactNumberedInstance G A Z hV).A.Feasible
      (Graph.ofSimpleGraph (gm02CompactNumberedInstance G A Z hV).G) ↔ A.Feasible G :=
  gm02NumberedInstance_feasible_iff G A _

/-- Compact recursive width bounds apply to the actual child. -/
theorem gm02CompactNumberedInstance_treeWidthLE_iff {n : ℕ} {β : Type*}
    (G : Graph (Fin n) β) (A : Termination V(G)) (Z : Finset (Fin n))
    (hV : V(G) = {v : Fin n | v ∉ Z}) (k : ℕ) :
    TreeWidthLE (Graph.ofSimpleGraph (gm02CompactNumberedInstance G A Z hV).G) k ↔
      TreeWidthLE G k := gm02NumberedInstance_treeWidthLE_iff G A _ k

end GraphMinor.Compute
