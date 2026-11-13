module

public import GraphMinor.GM05.CircuitPackingDefs
import GraphMinor.GM05.BoundedCircuitPacking
import GraphMinor.GM05.LoopCircuitPacking
import GraphMinor.GM05.GridLoopMinor
import GraphMinor.GM05.ShadowMinor
import GraphMinor.GM05.Main
import GraphMinor.Minor.Basic

/-!
# The Erdős–Pósa theorem for circuits

A graph without `k` disjoint circuits excludes a minor of `k` disjoint
loops. Those loops occur as a minor of a fixed grid. Graph Minors V, (7.3),
therefore bounds its tree-width. The subtree packing argument for the
circuits in a tree-decomposition then gives a bounded set meeting them all.
-/

public section

namespace GraphMinor.GM05

open Graph Set GM01 GM09

universe u v

/-- Graph Minors V, (8.1), page 109: "For any integer $k \ge 0$ there is an
integer $k' \ge 0$ such that for every graph $G$, at least one of the following is true:"
The alternatives are `k` disjoint circuits, or deletion of at most `k'`
vertices leaving no circuits. This proof derives the result from the
proved grid bound (7.3) and the subtree packing lemma. -/
theorem theorem_8_1_proof (k : ℕ) : ∃ k' : ℕ,
    ∀ {α : Type u} {β : Type v} (G : Graph α β),
      V(G).Finite → E(G).Finite →
      HasDisjointCircuits G k ∨ ∃ X ⊆ V(G), X.ncard ≤ k' ∧
        ¬ ∃ C, IsGraphCircuit (deleteVertices G X) C := by
  refine ⟨(k-1)*(θ₉ (2*k+6)+1), ?_⟩
  intro α β G hV hE
  by_cases hp : HasDisjointCircuits G k
  · exact Or.inl hp
  · have hno : ¬ IsIsoMinor (loopCopies k) (toGraph (simpleShadow G)) := by
      intro hm
      exact hp (disjointCircuits_of_loopCopies_minor hV hE
        (hm.trans (simpleShadow_isIsoMinor G hV hE)))
    have hw : TreeWidthLE (simpleShadow G) (θ₉ (2*k+6)) :=
      treeWidthLE_of_not_isIsoMinor_proved (by omega)
        (show Even (2*k+6) from ⟨k+3, by omega⟩) hV hno (loopCopies_minor_grid k)
    rcases circuits_pack_or_hit_of_treeWidthLE hV hw with hpack | ⟨X,hX,hcard,hhit⟩
    · exact Or.inl hpack
    · exact Or.inr ⟨X,hX,hcard,hhit.no_circuit_delete⟩

end GraphMinor.GM05
