module

public import GraphMinor.GM01.ForestGraphs
public import GraphMinor.GM01.Statements
import GraphMinor.GM01.ForestReduction
import GraphMinor.GM01.ForestTreeWidth

/-!
# The forest-exclusion theorem from its branching-tree case

This is the proof of Graph Minors I, (1.1), on page 51. Choose an odd-depth
tree containing the given forest as a minor. A graph excluding the forest
also excludes that tree, so the bound in (3.1) applies. The forest-minor
construction is proved in `ForestUniversality` and transferred to
multigraphs in `ForestReduction`.
-/

public section

namespace GraphMinor.GM01

open Graph

universe u v u' v'

/-- Graph Minors I, (1.1), page 39, from the paper's later result (3.1):
"For every forest $H$ there is an integer $w$ such that every graph with no minor isomorphic to $H$ has path-width $\le w$."

The proof on page 51 reduces forest exclusion to exclusion of an odd-depth
branching tree. The elementary forest-minor observation in that proof is
proved here rather than assumed. Apply the proved numbered bound (3.1). -/
theorem theorem_1_1_proof
    {α : Type u'} {β : Type v'} (H : Graph α β) (hfin : V(H).Finite)
    (hforest : IsForest H) :
    ∃ w : ℕ, ∀ {γ : Type u} {δ : Type v} (G : Graph γ δ),
      V(G).Finite → E(G).Finite → ¬ IsIsoMinor H G → HasPathWidthLE G w := by
  obtain ⟨ℓ, hpos, hodd, hexclusion⟩ := forest_exclusion_reduction H hfin hforest
  obtain ⟨w, hw⟩ := theorem_3_1_proof.{u, v} ℓ hpos hodd
  exact ⟨w, fun G hV hE hno ↦ hw G hV hE (hexclusion G hno)⟩

end GraphMinor.GM01
