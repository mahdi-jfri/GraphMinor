module

public import GraphMinor.Compute.GM02BuildSeparatorInput
public import GraphMinor.Compute.GM02CompressedBoundary
public import GraphMinor.GM02.CanonicalSeparation

/-!
# Mathematical data recovered from recursive separator bits

A successful separator search provides actual side graphs with the
encoded vertex sets. Canonicalize their edge assignment while keeping
those sets, and read the separator order from their intersection. The
printed recursive index bound then gives the proved seven-width bound
for the finite catalogue input.
-/

public section
namespace GraphMinor.Compute
open Graph Set Classical GraphMinor.GM02

/-- Recursive side bits use the standard membership-array representation. -/
theorem gm02VertexBits_eq_bitSetList {n : ℕ} (S : Finset (Fin n)) :
    gm02VertexBits S = bitSetList S := by
  unfold gm02VertexBits bitSetList
  congr

/-- Successful recursive side bits determine a canonical edge-disjoint separation. -/
theorem gm02RecursiveSides_canonical (allVertices : Bool) (x : GM02SimpleTerminatedInput)
    (q : ℕ) (L R : Finset (Fin x.n))
    (h : (gm02RecursiveSeparatorInput allVertices x).validSides (q : ℤ)
      (gm02VertexBits L) (gm02VertexBits R)) :
    IsSeparation (Graph.ofSimpleGraph x.G)
      ((Graph.ofSimpleGraph x.G).induce (L : Set (Fin x.n)))
      (((Graph.ofSimpleGraph x.G).induce (R : Set (Fin x.n))).deleteEdges
        E((Graph.ofSimpleGraph x.G).induce (L : Set (Fin x.n)))) := by
  obtain ⟨H, H', hsep, hL, hR, _, _, _⟩ := h
  have hL' : V(H) = (L : Set (Fin x.n)) := hL.trans (gm02DecodedVertices_bits L)
  have hR' : V(H') = (R : Set (Fin x.n)) := hR.trans (gm02DecodedVertices_bits R)
  have hc := hsep.canonicalize
  rw [hL', hR'] at hc
  exact hc

/-- The separator order is the cardinality of the intersection of the two bitsets. -/
theorem gm02RecursiveSides_order (allVertices : Bool) (x : GM02SimpleTerminatedInput)
    (q : ℕ) (L R : Finset (Fin x.n))
    (h : (gm02RecursiveSeparatorInput allVertices x).validSides (q : ℤ)
      (gm02VertexBits L) (gm02VertexBits R)) : (L ∩ R).card ≤ q := by
  obtain ⟨H, H', _, hL, hR, horder, _, _⟩ := h
  have hL' : V(H) = (L : Set (Fin x.n)) := hL.trans (gm02DecodedVertices_bits L)
  have hR' : V(H') = (R : Set (Fin x.n)) := hR.trans (gm02DecodedVertices_bits R)
  rw [hL', hR'] at horder
  change (((L : Set (Fin x.n)) ∩ (R : Set (Fin x.n))).ncard : ℤ) ≤ q at horder
  rw [← Finset.coe_inter, Set.ncard_coe_finset] at horder
  exact_mod_cast horder

/-- Every successful recursive separator has a catalogue boundary bounded solely by width. -/
theorem gm02RecursiveSides_boundary_bound (allVertices : Bool) (x : GM02SimpleTerminatedInput)
    (q : ℕ) (L R : Finset (Fin x.n)) (hindex : x.A.index ≤ 3 * q)
    (h : (gm02RecursiveSeparatorInput allVertices x).validSides (q : ℤ)
      (gm02VertexBits L) (gm02VertexBits R)) :
    (gm02CompressedBoundaryInput x L R).n ≤ 7 * q :=
  gm02CompressedBoundaryInput_size_bound x L R hindex (gm02RecursiveSides_order allVertices x q L R h)

/-- The first side has exactly the balance inequality returned by the selected phase. -/
theorem gm02RecursiveSides_left_balance (allVertices : Bool) (x : GM02SimpleTerminatedInput)
    (q : ℕ) (L R : Finset (Fin x.n))
    (h : (gm02RecursiveSeparatorInput allVertices x).validSides (q : ℤ)
      (gm02VertexBits L) (gm02VertexBits R)) :
    3 * (((L : Set (Fin x.n)) \ R) ∩ (gm02RecursiveSubset allVertices x : Set (Fin x.n))).ncard ≤
      2 * ((gm02RecursiveSubset allVertices x : Set (Fin x.n)) \ ((L : Set (Fin x.n)) ∩ R)).ncard := by
  obtain ⟨H, H', _, hL, hR, _, hbal, _⟩ := h
  have hL' : V(H) = (L : Set (Fin x.n)) := hL.trans (gm02DecodedVertices_bits L)
  have hR' : V(H') = (R : Set (Fin x.n)) := hR.trans (gm02DecodedVertices_bits R)
  rw [hL', hR'] at hbal
  exact hbal

/-- The second side has the symmetric balance inequality. -/
theorem gm02RecursiveSides_right_balance (allVertices : Bool) (x : GM02SimpleTerminatedInput)
    (q : ℕ) (L R : Finset (Fin x.n))
    (h : (gm02RecursiveSeparatorInput allVertices x).validSides (q : ℤ)
      (gm02VertexBits L) (gm02VertexBits R)) :
    3 * (((R : Set (Fin x.n)) \ L) ∩ (gm02RecursiveSubset allVertices x : Set (Fin x.n))).ncard ≤
      2 * ((gm02RecursiveSubset allVertices x : Set (Fin x.n)) \ ((L : Set (Fin x.n)) ∩ R)).ncard := by
  obtain ⟨H, H', _, hL, hR, _, _, hbal⟩ := h
  have hL' : V(H) = (L : Set (Fin x.n)) := hL.trans (gm02DecodedVertices_bits L)
  have hR' : V(H') = (R : Set (Fin x.n)) := hR.trans (gm02DecodedVertices_bits R)
  rw [hL', hR'] at hbal
  exact hbal

end GraphMinor.Compute
