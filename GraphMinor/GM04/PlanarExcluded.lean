module

public import GraphMinor.Planar.Defs
public import GraphMinor.Statement
import GraphMinor.GM04.Main
import GraphMinor.GM05.FullPlanar
import GraphMinor.GM03.Section1

/-!
# Excluding a planar graph

Graph Minors IV derives (1.4) on page 229 from (1.5): "This implies (1.4) because it is proved in
[10] that the class of graphs involved in (1.4) has bounded tree-width." The cited result is
Graph Minors V, (1.5), proved as `GM05.Full.theorem_1_5`. Its vertex bags are the bags of IV's
tree-decompositions (`GM03.treeWidthLE_gm04_of_treeWidthLE`), and IV (1.5) is
`GM04.theorem_1_5_proved`.
-/

public section

namespace GraphMinor.GM04

open Graph

universe u v u' v'

/-- A vertex-bag tree-decomposition of V, Section 1, is one of III, Section 1. -/
private theorem gm03_treeWidthLE_of_full {α : Type u} {β : Type v} {G : Graph α β} {w : ℕ}
    (h : GM05.Full.TreeWidthLE G w) : GM03.TreeWidthLE G w := by
  obtain ⟨ι, hι, T, χ, hD, hw⟩ := h
  refine (GM03.treeWidthLE_iff_exists_isTreeDecomposition G w).mpr ⟨ι, hι, T, χ, ?_, hw⟩
  refine ⟨hD.isTree, fun t => ?_, hD.iUnion_eq, hD.edge_mem, hD.inter_subset⟩
  rw [← hD.iUnion_eq]
  exact Set.subset_iUnion χ t

/-- Graph Minors IV, (1.4), page 229:
"For any planar graph $H$, the class of all graphs with no minor isomorphic to $H$ is well-quasi-ordered by minors."
The proof is the paper's: the graphs with no `H` minor have bounded tree-width by
Graph Minors V, (1.5) (`GM05.Full.theorem_1_5`), so IV (1.5) (`theorem_1_5_proved`) applies. -/
theorem theorem_1_4_proof {α' : Type u'} {β' : Type v'} (H : Graph α' β') (hH : IsPlanar H)
    {α : Type u} {β : Type v} (G : ℕ → Graph α β)
    (hV : ∀ n, V(G n).Finite) (hE : ∀ n, E(G n).Finite)
    (hexcl : ∀ n, ¬ IsIsoMinor H (G n)) :
    ∃ i j, i < j ∧ IsIsoMinor (G i) (G j) := by
  obtain ⟨w, hw⟩ := GM05.Full.theorem_1_5_proof (α := α) (β := β) H hH
  refine theorem_1_5_proved w G hV hE fun n => ?_
  exact GM03.treeWidthLE_gm04_of_treeWidthLE (hV n) (hE n)
    (gm03_treeWidthLE_of_full (hw (G n) (hV n) (hE n) (hexcl n)))

end GraphMinor.GM04
