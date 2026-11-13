module

public import GraphMinor.GM01.ForestGraphs
public import GraphMinor.GM01.ForestUniversality
import GraphMinor.GM01.Basic
import GraphMinor.Minor.Basic

/-!
# Reducing forest exclusion to one branching tree

The proof of Graph Minors I, (1.1), page 51, chooses an odd-depth branching
tree that has the given forest as a minor. We transfer the branch-set
construction to multigraph forests and use transitivity of the minor
relation to carry the exclusion to that branching tree.
-/

public section

namespace GraphMinor.GM01

open Graph SimpleGraph

variable {α β : Type*}

/-- The elementary observation in the proof of Graph Minors I, (1.1), page
51, for the paper's multigraphs: every finite forest is a minor of some
`Y_ℓ` with positive odd `ℓ`. The simple-graph model is transferred along
`simpleGraphIso`, which preserves every vertex and edge. -/
theorem exists_odd_forestTree_minor (H : Graph α β) (hfin : V(H).Finite)
    (hforest : IsForest H) :
    ∃ ℓ : ℕ, 0 < ℓ ∧ Odd ℓ ∧ IsIsoMinor H (forestTreeGraph ℓ) := by
  let : Finite V(H) := hfin.to_subtype
  let : H.Simple := hforest.1
  let S := SimpleGraph.toSubgraph H.toSimpleGraph le_top
  have hSfin : S.verts.Finite := Set.finite_univ
  let hom : S.coe →g H.toSimpleGraph :=
    { toFun := Subtype.val
      map_rel' := fun h ↦ h }
  have hSacyc : S.coe.IsAcyclic := hforest.2.comap hom Subtype.val_injective
  obtain ⟨ℓ, hpos, hodd, hminor⟩ :=
    exists_odd_forestTree_minor_of_isAcyclic S hSfin hSacyc
  have hminor' : IsIsoMinor (Graph.ofSimpleGraph H.toSimpleGraph) (forestTreeGraph ℓ) := by
    rwa [ofSimpleGraph_eq_toGraph H.toSimpleGraph]
  exact ⟨ℓ, hpos, hodd, (simpleGraphIso H).symm.isIsoMinor_left hminor'⟩

/-- The reduction used in the proof of Graph Minors I, (1.1), page 51.
If a graph excludes the given forest, then it excludes one fixed
odd-depth branching tree. The chosen depth depends only on the forest. -/
theorem forest_exclusion_reduction (H : Graph α β) (hfin : V(H).Finite)
    (hforest : IsForest H) :
    ∃ ℓ : ℕ, 0 < ℓ ∧ Odd ℓ ∧
      ∀ {γ δ : Type*} (G : Graph γ δ), ¬ IsIsoMinor H G → ¬ IsIsoMinor (forestTreeGraph ℓ) G := by
  obtain ⟨ℓ, hpos, hodd, hminor⟩ := exists_odd_forestTree_minor H hfin hforest
  exact ⟨ℓ, hpos, hodd, fun _ hno htree ↦ hno (hminor.trans htree)⟩

end GraphMinor.GM01
