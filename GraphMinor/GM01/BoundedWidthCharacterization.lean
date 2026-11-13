module

public import GraphMinor.GM01.PathWidth
public import GraphMinor.GM01.ForestGraphs
import GraphMinor.GM01.MainReduction
import GraphMinor.GM01.ForestTreeForests
import GraphMinor.GM01.ForestTreeWidthLowerBound
import GraphMinor.GM01.PathWidthMinors
import GraphMinor.GM01.Basic

/-!
# Bounded path-width is equivalent to excluding a forest

Graph Minors I, (1.2), page 40, follows from the main theorem and its
two elementary observations. A uniformly bounded family excludes
an odd-height tree whose path-width is larger than its bound,
because path-width does not increase under minors. Conversely,
apply (1.1) to a forest excluded by every graph of the family.
-/

public section

namespace GraphMinor.GM01

open Set Graph

universe u v

/-- Graph Minors I, (1.2), page 40: "Let $\mathcal{F}$ be a set of
graphs. Then the following are equivalent:"
"for some integer $w$, every $G \in \mathcal{F}$ has path-width $\le w$;"
"there is a forest $H$ such that no $G \in \mathcal{F}$ has a minor
isomorphic to $H$."
All graphs are finite by the paper's convention. The excluded forest
may have its own vertex and edge types, distinct from those of the family. -/
theorem theorem_1_2_proof {α : Type u} {β : Type v} (F : Set (Graph α β))
    (hFinite : ∀ G ∈ F, V(G).Finite ∧ E(G).Finite) :
    (∃ w : ℕ, ∀ G ∈ F, HasPathWidthLE G w) ↔
    ∃ (ν ε : Type) (H : Graph ν ε), V(H).Finite ∧ E(H).Finite ∧ IsForest H ∧
      ∀ G ∈ F, ¬ IsIsoMinor H G := by
  constructor
  · rintro ⟨w, hw⟩
    refine ⟨ForestTreeVertex, Sym2 ForestTreeVertex, forestTreeGraph (2 * w + 1),
      forestTree_vertices_finite _, finite_edgeSet_of_finite_verts (forestTree_vertices_finite _),
      forestTreeGraph_isForest _, ?_⟩
    intro G hGF hMinor
    exact forestTree_odd_not_hasPathWidthLE w
      ((hw G hGF).of_isIsoMinor (forestTree_vertices_finite _)
        (hFinite G hGF).1 (hFinite G hGF).2 hMinor)
  · rintro ⟨ν, ε, H, hV, _, hForest, hNo⟩
    obtain ⟨w, hw⟩ := theorem_1_1_proof.{u, v} H hV hForest
    exact ⟨w, fun G hGF ↦ hw G (hFinite G hGF).1 (hFinite G hGF).2 (hNo G hGF)⟩

end GraphMinor.GM01
