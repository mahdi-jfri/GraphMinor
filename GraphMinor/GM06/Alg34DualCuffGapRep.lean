module

public import GraphMinor.GM06.Alg34DualDataRep
public import GraphMinor.GM06.Alg34DualGapSegments
public import GraphMinor.Compute.GM06Alg34DualGapInput
import GraphMinor.GM06.Alg34GapLabelOrderTransfer
import GraphMinor.Compute.GM06Alg34GapPositionCast

/-!
# Interpreting the computed gap metadata of the dual

At each dual cuff position, use the next primal boundary vertex as the
gap point and the dual region indexed by that vertex as its incident
region. The shifted order and segment enumeration prove all fields of
the augmented cuff interpretation. These witnesses interpret the
computed finite data rather than supplying information to the program.
-/

public section
namespace GraphMinor.Compute.GM06CuffGapRep

open Set Surface GM06
universe u
variable {S : Type u} [TopologicalSpace S] [T1Space S]
  {x : GM06DrawingData} {G D : Drawing S} {Δ : Set (Set S)}
  {h : GM06DrawingRep x G Δ} {c : Fin x.cuffs.length}
  {R : List (Fin x.regions.length)}

/-- The computed next-primal-vertex labels have the full cuff-gap
interpretation for every cuff slot of the assembled disc dual. -/
theorem dualCuffGapRep (g : GM06CuffGapRep h c R) (hS : IsClosedDiscSpace S)
    (hconn : IsGraphConnected G.toGraph) (hd : IsDiscDualDrawing G D)
    (hR : 0 < x.regions.length)
    (j : Fin (x.dualData x.cuffs[c] hR g.region).cuffs.length) :
    Nonempty (GM06CuffGapRep (g.dualDataRep hS hconn hd hR) j
      (List.ofFn (x.dualGapRegionLabel x.cuffs[c] hR g.region))) := by
  let y := x.dualData x.cuffs[c] hR g.region
  let hy := g.dualDataRep hS hconn hd hR
  have hj : j.val = 0 := by
    have hh := j.isLt
    change j.val < [List.ofFn g.region].length at hh
    simp only [List.length_cons, List.length_nil] at hh
    omega
  have hget : y.cuffs[j] = List.ofFn g.region := by
    change [List.ofFn g.region][j.val] = _
    simp only [hj, List.getElem_cons_zero]
  simp only [Fin.getElem_fin] at hget
  let e : y.cuffs[j].length = x.cuffs[c].length :=
    (congrArg List.length hget).trans List.length_ofFn
  have hC := hy.disc_cuff_eq_bd hS j
  have hen := g.dualFollowingSegments_enumerate hS hconn hd
  refine ⟨{
    region := fun i => x.dualGapRegionLabel x.cuffs[c] hR g.region (Fin.cast e i)
    region_list := gm06OfFn_cast e _
    segment := fun i => g.dualFollowingSegment D (Fin.cast e i)
    segment_mem := ?_
    segment_injective := ?_
    segment_cover := ?_
    region_meets := ?_
    point := fun i => g.dualFollowingPoint (Fin.cast e i)
    point_mem := fun i => g.dualFollowingPoint_mem_segment hS hd (Fin.cast e i)
    primal_gap_order := ?_
    gap_order := ?_ }⟩
  · intro i
    rw [hC]
    exact hen.1 _
  · intro i k he
    have hh := hen.2.1 he
    exact (Fin.cast_injective e) hh
  · intro seg hs
    rw [hC] at hs
    obtain ⟨i, hi⟩ := hen.2.2 seg hs
    exact ⟨Fin.cast e.symm i, hi⟩
  · intro i
    refine ⟨g.dualFollowingPoint (Fin.cast e i), ?_,
      g.dualFollowingPoint_mem_segment hS hd (Fin.cast e i)⟩
    change (h.vertex (x.cuffs[c].get (gm06CycleSucc (Fin.cast e i)))).val ∈
      (h.dualRegionLabel hd (x.cuffs[c].get (gm06CycleSucc (Fin.cast e i)))).val
    exact h.vertex_mem_dualRegionLabel hd _
  · intro a b i k
    rw [hC]
    have ht := gm06PairCrossesGaps_ofFn_iff g.region (g.region_injective hS hd.1 hconn)
      (fun a => (h.dualVertexLabel hd a).val) (bd S) g.dualFollowingPoint
      (g.dualVertex_mem_boundary_iff hS hd) (g.dualFollowingPoint_primal_order hS hd)
      a b (Fin.cast e i) (Fin.cast e k)
    have he : GM06DrawingData.pairCrossesGaps y.cuffs[j] a b i k =
        GM06DrawingData.pairCrossesGaps (List.ofFn g.region) a b
          (Fin.cast List.length_ofFn.symm (Fin.cast e i))
          (Fin.cast List.length_ofFn.symm (Fin.cast e k)) := by
      exact congrArg (fun A : List (Fin y.n) =>
        (decide (a ∈ A ∧ b ∈ A ∧ a ≠ b) &&
          GM06DrawingData.cyclicBetween (2 * A.idxOf a) (2 * A.idxOf b) (2 * i.val + 1)) !=
        (decide (a ∈ A ∧ b ∈ A ∧ a ≠ b) &&
          GM06DrawingData.cyclicBetween (2 * A.idxOf a) (2 * A.idxOf b) (2 * k.val + 1))) hget
    refine (Eq.to_iff (congrArg (fun v : Bool => v = true) he)).trans ?_
    exact ht
  · intro a b i k
    rw [hC]
    have he : GM06DrawingData.crossesOnList (List.finRange y.cuffs[j].length) a b i k =
        GM06DrawingData.crossesOnList (List.finRange x.cuffs[c].length)
          (Fin.cast e a) (Fin.cast e b) (Fin.cast e i) (Fin.cast e k) := by
      exact (gm06CrossesFinRange_map (Fin.cast e)
        (by intro u v huv; exact huv) a b i k).symm
    exact (Eq.to_iff (congrArg (fun v : Bool => v = true) he)).trans
      (g.dualFollowingPoint_gap_order hS _ _ _ _)

end GraphMinor.Compute.GM06CuffGapRep
