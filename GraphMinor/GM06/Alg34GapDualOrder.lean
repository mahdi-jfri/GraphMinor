module

public import GraphMinor.GM06.Alg34GapInputRep
public import GraphMinor.GM06.Alg34GapPointTransfer
public import GraphMinor.GM06.Alg34GapDivision
public import GraphMinor.GM06.Alg34GapDisc

/-!
# Reading the supplied gap order at the dual vertices

Each supplied gap region contains its actual dual vertex on that gap.
Moving the interpretation points to those vertices preserves crossing
against primal vertex pairs and against other gap pairs. The computed
gap classes therefore give the paper's dual division on the actual dual
boundary, with no geometric data read by the finite program.
-/

@[expose] public section
namespace GraphMinor.Compute.GM06CuffGapRep

open Set Surface GM06
universe u
variable {S : Type u} [TopologicalSpace S]
  {x : GM06DrawingData} {G D : Drawing S} {Δ : Set (Set S)}
  {h : GM06DrawingRep x G Δ} {c : Fin x.cuffs.length}
  {R : List (Fin x.regions.length)}

/-- The geometric dual point represented by a supplied gap region label.
This is an interpretation map, not part of the finite input. -/
noncomputable def dualPoint (g : GM06CuffGapRep h c R)
    (hd : IsDiscDualDrawing G D) (i : Fin x.cuffs[c].length) : S :=
  (h.dualVertexLabel hd (g.region i)).val

/-- The corresponding dual vertex lies in the supplied gap. -/
theorem dualPoint_mem (g : GM06CuffGapRep h c R) (hS : IsClosedDiscSpace S)
    (hd : IsDiscDualDrawing G D) (i : Fin x.cuffs[c].length) :
    g.dualPoint hd i ∈ g.segment i := by
  have hs := g.segment_mem i
  rw [h.disc_cuff_eq_bd hS c] at hs
  exact h.dualVertexLabel_mem_gap hS hd (g.region i) hs (g.region_meets i)

/-- The finite cyclic gap order is the order of the actual dual boundary vertices. -/
theorem dualPoint_gap_order (g : GM06CuffGapRep h c R) (hS : IsClosedDiscSpace S)
    (hd : IsDiscDualDrawing G D) (a b i j : Fin x.cuffs[c].length) :
    GM06DrawingData.crossesOnList (List.finRange x.cuffs[c].length) a b i j = true ↔
      CrossesOn (bd S) (g.dualPoint hd a) (g.dualPoint hd b)
        (g.dualPoint hd i) (g.dualPoint hd j) := by
  have hs := g.segment_mem
  have ho := g.gap_order a b i j
  rw [h.disc_cuff_eq_bd hS c] at hs ho
  exact ho.trans (GM06DrawingRep.gap_points_crosses_iff hS.isOArc_bd
    g.segment hs g.segment_injective g.point (g.dualPoint hd) g.point_mem
      (g.dualPoint_mem hS hd) a b i j)

/-- Crossing against every primal pair can be read at the actual dual vertices,
including primal labels outside the boundary cuff. -/
theorem dualPoint_primal_order (g : GM06CuffGapRep h c R) (hS : IsClosedDiscSpace S)
    (hd : IsDiscDualDrawing G D) (a b : Fin x.n) (i j : Fin x.cuffs[c].length) :
    GM06DrawingData.pairCrossesGaps x.cuffs[c] a b i j = true ↔
      CrossesOn (bd S) (h.vertex a).val (h.vertex b).val
        (g.dualPoint hd i) (g.dualPoint hd j) := by
  have hs := g.segment_mem
  have ho := g.primal_gap_order a b i j
  rw [h.disc_cuff_eq_bd hS c] at hs ho
  rw [ho]
  constructor
  · intro hc
    exact (GM06DrawingRep.gap_crosses_iff (hs i) (hs j)
      ⟨(h.vertex a).property, hc.1⟩ ⟨(h.vertex b).property, hc.2.2.1⟩
      (g.point_mem i) (g.point_mem j) (g.dualPoint_mem hS hd i)
      (g.dualPoint_mem hS hd j)).mp hc
  · intro hc
    exact (GM06DrawingRep.gap_crosses_iff (hs i) (hs j)
      ⟨(h.vertex a).property, hc.1⟩ ⟨(h.vertex b).property, hc.2.2.1⟩
      (g.point_mem i) (g.point_mem j) (g.dualPoint_mem hS hd i)
      (g.dualPoint_mem hS hd j)).mpr hc

/-- The supplied gap region labels are distinct for a connected proper drawing. -/
theorem region_injective (g : GM06CuffGapRep h c R) (hS : IsClosedDiscSpace S)
    (hproper : G.IsProper) (hconn : IsGraphConnected G.toGraph) :
    Function.Injective g.region := by
  have hs := g.segment_mem
  rw [h.disc_cuff_eq_bd hS c] at hs
  exact h.gap_region_labels_injective hS hproper hconn g.segment
    g.segment_injective g.region hs g.region_meets

/-- The finite gap classes map exactly to the dual division on the actual vertices. -/
theorem dualDivision_image (g : GM06CuffGapRep h c R) (hS : IsClosedDiscSpace S)
    (hd : IsDiscDualDrawing G D) :
    (Set.image (g.dualPoint hd)) '' x.dualGapDivisionSet x.cuffs[c] =
      dualDivision (bd S) (Set.range (g.dualPoint hd)) Δ :=
  h.dualGapDivision_image x.cuffs[c] (g.dualPoint hd) (g.dualPoint_primal_order hS hd)

/-- The actual points indexed by the gap data cover precisely the dual boundary vertices. -/
theorem dualPoint_range (g : GM06CuffGapRep h c R) (hS : IsClosedDiscSpace S)
    (hd : IsDiscDualDrawing G D) : Set.range (g.dualPoint hd) = D.V ∩ bd S := by
  have hs := g.segment_mem
  have hcover := g.segment_cover
  rw [h.disc_cuff_eq_bd hS c] at hs hcover
  exact h.gap_region_labels_boundary hS hd g.segment g.region hs hcover g.region_meets

end GraphMinor.Compute.GM06CuffGapRep
