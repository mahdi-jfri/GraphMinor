module

public import GraphMinor.Compute.GM06Alg34GapInput
public import GraphMinor.Compute.GM06Alg34DualGapRelation

/-!
# Interpreting supplied cuff gap incidence

Each supplied cuff gap is interpreted as a boundary segment and its
incident region label. Its position is between successive supplied
cuff vertices. Crossing tests record that cyclic order for primal pairs
and gap pairs. These are interpretation witnesses of finite drawing
data. No dual drawing, reduction, or feasibility result is part of the
input or its representation.
-/

public section
namespace GraphMinor.Compute

open Set Surface GM06

universe u

/-- Interpretation of one cuff's gap incidence list. Segments and their
cyclic order are those of VI Section 2, page 117. Region labels record
which region meets each gap, as used in Section 3, pages 119–120.
Geometric points and segments occur only in this representation witness. -/
structure GM06CuffGapRep {x : GM06DrawingData} {S : Type u} [TopologicalSpace S]
    {G : Drawing S} {Δ : Set (Set S)} (h : GM06DrawingRep x G Δ)
    (c : Fin x.cuffs.length) (R : List (Fin x.regions.length)) where
  region : Fin x.cuffs[c].length → Fin x.regions.length
  region_list : List.ofFn region = R
  segment : Fin x.cuffs[c].length → Set S
  segment_mem : ∀ i, segment i ∈ segmentsOf (h.cuff c).val (G.V ∩ (h.cuff c).val)
  segment_injective : Function.Injective segment
  segment_cover : ∀ seg ∈ segmentsOf (h.cuff c).val (G.V ∩ (h.cuff c).val),
    ∃ i, segment i = seg
  region_meets : ∀ i, ((h.region (region i)).val ∩ segment i).Nonempty
  point : Fin x.cuffs[c].length → S
  point_mem : ∀ i, point i ∈ segment i
  primal_gap_order : ∀ a b i j,
    GM06DrawingData.pairCrossesGaps x.cuffs[c] a b i j = true ↔
      CrossesOn (h.cuff c).val (h.vertex a).val (h.vertex b).val (point i) (point j)
  gap_order : ∀ i j k l : Fin x.cuffs[c].length,
    GM06DrawingData.crossesOnList (List.finRange x.cuffs[c].length) i j k l = true ↔
      CrossesOn (h.cuff c).val (point i) (point j) (point k) (point l)

/-- An augmented word array describes the original drawing and, on each
cuff, the supplied boundary gap region incidence in cyclic order. Every
field concerns the finite input's interpretation, not an algorithm output. -/
structure GM06GapInputRep (x : GM06GapInput) {S : Type u} [TopologicalSpace S]
    (G : Drawing S) (Δ : Set (Set S)) where
  drawing : GM06DrawingRep x.drawing G Δ
  gap_count : x.gapRegions.length = x.drawing.cuffs.length
  gap : ∀ c : Fin x.drawing.cuffs.length,
    GM06CuffGapRep drawing c
      (x.gapRegions[c.val]'(by rw [gap_count]; exact c.isLt))

end GraphMinor.Compute
