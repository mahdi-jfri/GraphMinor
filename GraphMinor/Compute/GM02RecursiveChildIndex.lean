module

public import GraphMinor.Compute.GM02RecursiveChildSize
public import GraphMinor.GM02.RecursiveIndexBounds

/-!
# Index bounds for the exact recursive child inputs

The compact child keeps the selected scheme's matching index. Apply
(2.10) to that scheme on the canonical sides. A1 uses the printed
five-halves input bound, while A2 uses the terminal-support balance
returned by its separator query. These give the opposite routine's
required index bound for both actual child encodings.
-/

public section
set_option backward.isDefEq.respectTransparency.types false
namespace GraphMinor.Compute
open Graph Set Classical GraphMinor.GM02

/-- A1's actual compact children satisfy A2's three-width index promise. -/
theorem gm02RecursiveChosenInput_A1_index (right : Bool) (x : GM02SimpleTerminatedInput)
    (q : ℕ) (L R : Finset (Fin x.n)) (C : (gm02CompressedBoundaryInput x L R).schemes)
    (hindex : 2 * x.A.index ≤ 5 * q)
    (hvalid : (gm02RecursiveSeparatorInput true x).validSides (q : ℤ)
      (gm02VertexBits L) (gm02VertexBits R)) :
    (gm02RecursiveChosenInput right x L R C).A.index ≤ 3 * q := by
  have horder : (V((Graph.ofSimpleGraph x.G).induce (L : Set (Fin x.n))) ∩
      V(((Graph.ofSimpleGraph x.G).induce (R : Set (Fin x.n))).deleteEdges
        E((Graph.ofSimpleGraph x.G).induce (L : Set (Fin x.n))))).ncard ≤ q := by
    change ((L : Set (Fin x.n)) ∩ (R : Set (Fin x.n))).ncard ≤ q
    rw [← Finset.coe_inter, Set.ncard_coe_finset]
    exact gm02RecursiveSides_order true x q L R hvalid
  have hs := recursive_A1_child_index (gm02CanonicalBoundaryScheme x L R C)
    (Set.toFinite _) horder hindex
  rw [gm02CanonicalBoundaryScheme_left_index, gm02CanonicalBoundaryScheme_right_index] at hs
  rw [gm02RecursiveChosenInput_index]
  cases right with
  | false => exact hs.1
  | true => exact hs.2

/-- A2's terminal-balanced compact children satisfy A1's five-halves index promise. -/
theorem gm02RecursiveChosenInput_A2_index (right : Bool) (x : GM02SimpleTerminatedInput)
    (q : ℕ) (L R : Finset (Fin x.n)) (C : (gm02CompressedBoundaryInput x L R).schemes)
    (hindex : x.A.index ≤ 3 * q)
    (hvalid : (gm02RecursiveSeparatorInput false x).validSides (q : ℤ)
      (gm02VertexBits L) (gm02VertexBits R)) :
    2 * (gm02RecursiveChosenInput right x L R C).A.index ≤ 5 * q := by
  have horder : (V((Graph.ofSimpleGraph x.G).induce (L : Set (Fin x.n))) ∩
      V(((Graph.ofSimpleGraph x.G).induce (R : Set (Fin x.n))).deleteEdges
        E((Graph.ofSimpleGraph x.G).induce (L : Set (Fin x.n))))).ncard ≤ q := by
    change ((L : Set (Fin x.n)) ∩ (R : Set (Fin x.n))).ncard ≤ q
    rw [← Finset.coe_inter, Set.ncard_coe_finset]
    exact gm02RecursiveSides_order false x q L R hvalid
  have hL := gm02RecursiveSides_left_balance false x q L R hvalid
  have hR := gm02RecursiveSides_right_balance false x q L R hvalid
  simp only [gm02RecursiveSubset, Bool.false_eq_true, ↓reduceIte, gm02TerminalVertices_toFinset] at hL hR
  have hs := recursive_A2_child_index (gm02CanonicalBoundaryScheme x L R C)
    (Set.toFinite _) horder hindex hL hR
  rw [gm02CanonicalBoundaryScheme_left_index, gm02CanonicalBoundaryScheme_right_index] at hs
  rw [gm02RecursiveChosenInput_index]
  cases right with
  | false => exact hs.1
  | true => exact hs.2

end GraphMinor.Compute
