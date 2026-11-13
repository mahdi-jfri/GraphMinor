module

public import GraphMinor.GM06.Alg34GapInducedIncidence
public import GraphMinor.Compute.GM06Alg34GapZipLabels
import GraphMinor.Compute.GM06Alg34GapPositionCast

/-!
# Correct interpretation of one updated cuff gap list

Transport the retained gap points and segments to the positions of the
computed induced cuff list. Their crossing order, exhaustive segment
enumeration, and incident region labels have already been proved. This
assembles those facts into the input interpretation for the updated list.
-/

public section
namespace GraphMinor.Compute.GM06CuffGapRep

open Set Surface GM06 GM06DrawingData

universe u
variable {S : Type u} [TopologicalSpace S] [T1Space S]
  {x : GM06DrawingData} {G : Drawing S} {Δ : Set (Set S)}
  {h : GM06DrawingRep x G Δ}

/-- The finite retained-gap update represents exactly the segments and
incident regions of the induced drawing on each disc cuff. -/
theorem inducedCuffGapRep (hS : IsClosedDiscSpace S) (hproper : G.IsProper)
    (vs : List (Fin x.n)) (c : Fin (x.inducedData vs).cuffs.length)
    {R : List (Fin x.regions.length)}
    (g : GM06CuffGapRep h (Fin.cast (x.inducedData_cuffs_length vs) c) R) :
    Nonempty (GM06CuffGapRep (h.inducedGapBaseRep vs) c
      (x.gapRegionsAfterDeletion vs x.cuffs[Fin.cast (x.inducedData_cuffs_length vs) c] R)) := by
  let old := Fin.cast (x.inducedData_cuffs_length vs) c
  have hL : (x.inducedData vs).cuffs[c] = x.relabelVertexList vs x.cuffs[old] := by
    change (x.cuffs.map (x.relabelVertexList vs))[c.val] = _
    rw [List.getElem_map]
    rfl
  let e := congrArg List.length hL
  let f : Fin (x.inducedData vs).cuffs[c].length →
      Fin (x.relabelVertexList vs x.cuffs[old]).length := Fin.cast e
  have hC : ((h.inducedGapBaseRep vs).cuff c).val = (h.cuff old).val := rfl
  obtain ⟨hs, hi, hcover⟩ := g.inducedSegments_enumerate hS vs
  refine ⟨{
    region := fun i => x.regionAfterDeletion vs (g.region (gm06InducedGapPosition x vs x.cuffs[old] (f i)))
    region_list := ?_
    segment := fun i => g.inducedSegment vs (f i)
    segment_mem := ?_
    segment_injective := ?_
    segment_cover := ?_
    region_meets := ?_
    point := fun i => g.inducedPoint vs (f i)
    point_mem := fun i => g.inducedPoint_mem_segment vs (f i)
    primal_gap_order := ?_
    gap_order := ?_ }⟩
  · refine (gm06OfFn_cast e (fun j => x.regionAfterDeletion vs
      (g.region (gm06InducedGapPosition x vs x.cuffs[old] j)))).trans ?_
    exact (gm06GapRegionsAfterDeletion_eq_ofFn x vs _
      (h.cuff_nodup _ (List.getElem_mem old.isLt)) g.region).symm.trans
      (congrArg (x.gapRegionsAfterDeletion vs x.cuffs[old]) g.region_list)
  · intro i
    rw [hC]
    exact hs (f i)
  · exact hi.comp (finCongr e).injective
  · intro seg hseg
    rw [hC] at hseg
    obtain ⟨j, hj⟩ := hcover seg hseg
    obtain ⟨i, hi⟩ := (finCongr e).surjective j
    exact ⟨i, by change g.inducedSegment vs ((finCongr e) i) = seg; rw [hi]; exact hj⟩
  · intro i
    exact g.induced_region_meets hS hproper vs (f i)
  · intro a b i j
    rw [gm06PairCrossesGaps_cast hL, hC]
    exact g.inducedPoint_primal_order vs a b (f i) (f j)
  · intro a b i j
    rw [gm06CrossesFinRange_cast e, hC]
    exact g.inducedPoint_gap_order vs (f a) (f b) (f i) (f j)

end GraphMinor.Compute.GM06CuffGapRep
