module

public import GraphMinor.GM02.MinorTreeWidth
public import GraphMinor.GM02.InducedTerminatedGraphs
import GraphMinor.GM02.BalancedSeparation
public import GraphMinor.GM02.InducedPathIntersections

/-!
# Validating width reports in the alternating recursion

A rejected balanced-separation search forces the width threshold by
(2.6). A recursive child's width report also holds for its parent by
(2.7), since each induced graph is a subgraph of the parent. These are
the two width-reporting steps in II's A1/A2 algorithms, pages 316–317.
-/

public section
namespace GraphMinor.GM02
open Graph Set Classical
universe u v

/-- Failure of the balanced-separation search gives the width report used
in Step 1 of both recursive routines, Graph Minors II, pages 316–317. -/
theorem recursive_width_of_no_separation {α : Type u} {β : Type v}
    (G : Graph α β) (hV : V(G).Finite) (hE : E(G).Finite) (Q : Set α) (hQ : Q ⊆ V(G))
    (w : ℕ)
    (hno : ¬∃ H H', IsSeparation G H H' ∧ (V(H) ∩ V(H')).ncard ≤ w ∧
      3 * ((V(H) \ V(H')) ∩ Q).ncard ≤ 2 * (Q \ (V(H) ∩ V(H'))).ncard ∧
      3 * ((V(H') \ V(H)) ∩ Q).ncard ≤ 2 * (Q \ (V(H) ∩ V(H'))).ncard) :
    w ≤ treeWidth G hV hE := by
  apply Nat.le_of_not_gt
  intro hw
  exact hno (theorem_2_6_proof G hV hE hw hQ)

/-- Subgraph width monotonicity as the special case of II (2.7) used in
propagating recursive child reports to the parent. -/
theorem treeWidth_le_of_subgraph {α : Type u} {β : Type v} {G K : Graph α β}
    (hV : V(G).Finite) (hE : E(G).Finite) (hKG : K ≤ G) :
    treeWidth K (hV.subset hKG.vertexSet_mono) (hE.subset hKG.edgeSet_mono) ≤ treeWidth G hV hE := by
  obtain ⟨L, hLK, F, hF, hIso⟩ := GraphMinor.IsIsoMinor.refl K
  have hminor : GraphMinor.IsIsoMinor K G := ⟨L, hLK.trans hKG, F, hF, hIso⟩
  have h := theorem_2_7_proof hV hE (hV.subset hKG.vertexSet_mono) (hE.subset hKG.edgeSet_mono)
    hminor (Nat.lt_succ_self (treeWidth G hV hE))
  exact Nat.lt_succ_iff.mp h

/-- A first-side induced child's width report is valid for the parent,
as in Step 2 of A1 and A2, Graph Minors II, pages 316–317. -/
theorem recursive_width_of_left_child {α : Type u} {β : Type v} {G H H' : Graph α β}
    (hV : V(G).Finite) (hE : E(G).Finite) (hsep : IsSeparation G H H')
    {A : Termination V(G)} (C : CrossingScheme G H H' A) {w : ℕ}
    (hchild : w ≤ treeWidth C.inducedLeft (hV.subset (C.inducedLeft_le hsep).vertexSet_mono)
      (hE.subset (C.inducedLeft_le hsep).edgeSet_mono)) : w ≤ treeWidth G hV hE :=
  hchild.trans (treeWidth_le_of_subgraph hV hE (C.inducedLeft_le hsep))

/-- A second-side induced child's width report propagates in the same way. -/
theorem recursive_width_of_right_child {α : Type u} {β : Type v} {G H H' : Graph α β}
    (hV : V(G).Finite) (hE : E(G).Finite) (hsep : IsSeparation G H H')
    {A : Termination V(G)} (C : CrossingScheme G H H' A) {w : ℕ}
    (hchild : w ≤ treeWidth C.inducedRight (hV.subset (C.inducedRight_le hsep).vertexSet_mono)
      (hE.subset (C.inducedRight_le hsep).edgeSet_mono)) : w ≤ treeWidth G hV hE :=
  hchild.trans (treeWidth_le_of_subgraph hV hE (C.inducedRight_le hsep))

end GraphMinor.GM02
