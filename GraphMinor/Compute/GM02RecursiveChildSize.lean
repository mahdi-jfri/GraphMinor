module

public import GraphMinor.Compute.GM02RecursiveChosenChild
public import GraphMinor.Compute.GM02RecursiveSides
public import GraphMinor.GM02.RecursiveSizeBounds

/-!
# Sizes of the actual compact recursive inputs

The constructed child is a renaming of the corrected induced graph.
Read its vertex count and matching index through that renaming. The
paper's containment argument then bounds both chosen inputs by their
parent's vertex count, independently of the chosen crossing scheme.
-/

public section
set_option backward.isDefEq.respectTransparency.types false
namespace GraphMinor.Compute
open Graph Set Classical GraphMinor.GM02

/-- Compact numbering preserves the chosen induced child's vertex count. -/
theorem gm02RecursiveChosenInput_size (right : Bool) (x : GM02SimpleTerminatedInput)
    (L R : Finset (Fin x.n)) (C : (gm02CompressedBoundaryInput x L R).schemes) :
    (gm02RecursiveChosenInput right x L R C).n =
      if right then V((gm02CanonicalBoundaryScheme x L R C).inducedRight).ncard
      else V((gm02CanonicalBoundaryScheme x L R C).inducedLeft).ncard := by
  cases right with
  | false =>
    change (gm02CanonicalLeftInput x.G L R x.A _).n = _
    rw [gm02CanonicalLeftInput_eq_numbered]
    exact gm02NumberedInstance_size _ _ _
  | true =>
    change (gm02CanonicalRightInput x.G L R x.A _).n = _
    rw [gm02CanonicalRightInput_eq_numbered]
    exact gm02NumberedInstance_size _ _ _

/-- Compact numbering preserves the selected template's matching index. -/
theorem gm02RecursiveChosenInput_index (right : Bool) (x : GM02SimpleTerminatedInput)
    (L R : Finset (Fin x.n)) (C : (gm02CompressedBoundaryInput x L R).schemes) :
    (gm02RecursiveChosenInput right x L R C).A.index =
      if right then C.right.index else C.left.index := by
  cases right with
  | false =>
    change (gm02CanonicalLeftInput x.G L R x.A _).A.index = C.left.index
    rw [gm02CanonicalLeftInput_eq_numbered, gm02CompactNumberedInstance_index,
      Termination.rebase_index, gm02CanonicalBoundaryScheme_left_index]
  | true =>
    change (gm02CanonicalRightInput x.G L R x.A _).A.index = C.right.index
    rw [gm02CanonicalRightInput_eq_numbered, gm02CompactNumberedInstance_index,
      Termination.rebase_index, gm02CanonicalBoundaryScheme_right_index]

/-- Every actual recursive side input has no more vertices than its parent. -/
theorem gm02RecursiveChosenInput_size_le (right allVertices : Bool) (x : GM02SimpleTerminatedInput)
    (q : ℕ) (L R : Finset (Fin x.n)) (C : (gm02CompressedBoundaryInput x L R).schemes)
    (hvalid : (gm02RecursiveSeparatorInput allVertices x).validSides (q : ℤ)
      (gm02VertexBits L) (gm02VertexBits R)) :
    (gm02RecursiveChosenInput right x L R C).n ≤ x.n := by
  have hsep := gm02RecursiveSides_canonical allVertices x q L R hvalid
  have hs := recursive_A2_child_size (Set.toFinite _) hsep (gm02CanonicalBoundaryScheme x L R C)
  have hn : V(Graph.ofSimpleGraph x.G).ncard = x.n := by
    change (Set.univ : Set (Fin x.n)).ncard = x.n
    simp only [Set.ncard_univ, Nat.card_fin]
  rw [hn] at hs
  rw [gm02RecursiveChosenInput_size]
  cases right with
  | false => exact hs.1
  | true => exact hs.2

/-- Above the exhaustive bound, every A1 child shrinks by the paper's three-quarter factor. -/
theorem gm02RecursiveChosenInput_A1_shrink (right : Bool) (x : GM02SimpleTerminatedInput)
    (q : ℕ) (L R : Finset (Fin x.n)) (C : (gm02CompressedBoundaryInput x L R).schemes)
    (hlarge : 4 * q < x.n)
    (hvalid : (gm02RecursiveSeparatorInput true x).validSides (q : ℤ)
      (gm02VertexBits L) (gm02VertexBits R)) :
    4 * (gm02RecursiveChosenInput right x L R C).n ≤ 3 * x.n ∧
      (gm02RecursiveChosenInput right x L R C).n < x.n := by
  have hn : V(Graph.ofSimpleGraph x.G).ncard = x.n := by
    change (Set.univ : Set (Fin x.n)).ncard = x.n
    simp only [Set.ncard_univ, Nat.card_fin]
  have hsep := gm02RecursiveSides_canonical true x q L R hvalid
  have horder : (V((Graph.ofSimpleGraph x.G).induce (L : Set (Fin x.n))) ∩
      V(((Graph.ofSimpleGraph x.G).induce (R : Set (Fin x.n))).deleteEdges
        E((Graph.ofSimpleGraph x.G).induce (L : Set (Fin x.n))))).ncard ≤ q := by
    change ((L : Set (Fin x.n)) ∩ (R : Set (Fin x.n))).ncard ≤ q
    rw [← Finset.coe_inter, Set.ncard_coe_finset]
    exact gm02RecursiveSides_order true x q L R hvalid
  have hL := gm02RecursiveSides_left_balance true x q L R hvalid
  have hR := gm02RecursiveSides_right_balance true x q L R hvalid
  simp only [gm02RecursiveSubset, ↓reduceIte, Finset.coe_univ, Set.inter_univ] at hL hR
  have hs := recursive_A1_child_shrink (Set.toFinite _) hsep (gm02CanonicalBoundaryScheme x L R C)
    (by simpa only [hn] using hlarge) horder hL hR
  rw [hn] at hs
  rw [gm02RecursiveChosenInput_size]
  cases right with
  | false => exact hs.1
  | true => exact hs.2

end GraphMinor.Compute
