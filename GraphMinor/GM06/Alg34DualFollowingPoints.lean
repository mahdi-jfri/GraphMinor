module

public import GraphMinor.GM06.Alg34GapDualOrder
public import GraphMinor.Compute.GM06Alg34DualGapShift
import GraphMinor.Compute.GM06Alg34GapListPositions
import GraphMinor.Compute.GM06Alg34DiscRep

/-!
# Primal vertices as following gap points of the dual

After exchanging primal vertices and gaps, the next primal boundary
vertex supplies a point in each dual gap. The finite cyclic-shift
identity gives its crossing order with the dual boundary vertices.
The original vertex order also gives the order among these new gap
points. No new geometric points have to be chosen.
-/

@[expose] public section
namespace GraphMinor.Compute.GM06CuffGapRep

open Set Surface GM06
universe u
variable {S : Type u} [TopologicalSpace S]
  {x : GM06DrawingData} {G D : Drawing S} {Δ : Set (Set S)}
  {h : GM06DrawingRep x G Δ} {c : Fin x.cuffs.length}
  {R : List (Fin x.regions.length)}

/-- The next supplied primal cuff vertex, viewed as a point in a dual gap. -/
def dualFollowingPoint (g : GM06CuffGapRep h c R) (i : Fin x.cuffs[c].length) : S :=
  (h.vertex (x.cuffs[c].get (gm06CycleSucc i))).val

/-- These primal vertices lie on the boundary outside the dual vertex set. -/
theorem dualFollowingPoint_mem (g : GM06CuffGapRep h c R)
    (hS : IsClosedDiscSpace S) (hd : IsDiscDualDrawing G D) (i : Fin x.cuffs[c].length) :
    g.dualFollowingPoint i ∈ bd S \ (D.V ∩ bd S) := by
  have hp := (h.cuff_vertices c).subset
    ⟨x.cuffs[c].get (gm06CycleSucc i), List.get_mem _ _, rfl⟩
  rw [h.disc_cuff_eq_bd hS c] at hp
  refine ⟨hp.2, ?_⟩
  intro hdV
  have hm : g.dualFollowingPoint i ∈ G.V ∩ D.V := ⟨hp.1, hdV.1⟩
  rw [hd.V_inter_dual_V_eq_empty] at hm
  exact hm

/-- The old crossing order, with the pairs exchanged, is exactly the
new primal-versus-gap comparison at the next old primal vertices. -/
theorem dualFollowingPoint_primal_order (g : GM06CuffGapRep h c R)
    (hS : IsClosedDiscSpace S) (hd : IsDiscDualDrawing G D)
    (a b i j : Fin x.cuffs[c].length) :
    GM06DrawingData.pairCrossesGaps (List.finRange x.cuffs[c].length) a b
      (Fin.cast List.length_finRange.symm i) (Fin.cast List.length_finRange.symm j) = true ↔
      CrossesOn (bd S) (g.dualPoint hd a) (g.dualPoint hd b)
        (g.dualFollowingPoint i) (g.dualFollowingPoint j) := by
  simp only [Fin.getElem_fin] at *
  have ht := g.dualPoint_primal_order hS hd
    (x.cuffs[c].get (gm06CycleSucc i)) (x.cuffs[c].get (gm06CycleSucc j)) a b
  simp only [Fin.getElem_fin] at ht ⊢
  rw [gm06PairCrossesGaps_get (h.cuff_nodup _ (List.getElem_mem c.isLt))] at ht
  refine (Eq.to_iff (congrArg (fun v : Bool => v = true)
    (gm06PairCrossesGaps_dual_shift a b i j))).trans ?_
  exact ht.trans ⟨fun hc => hc.comm hS.isOArc_bd, fun hc => hc.comm hS.isOArc_bd⟩

/-- The complete supplied old cuff list is the unique list of a disc. -/
private theorem cuff_singleton (h : GM06DrawingRep x G Δ) (hS : IsClosedDiscSpace S) : x.cuffs = [x.cuffs[c]] := by
  obtain ⟨L, hL⟩ := h.exists_cuff_list hS
  have hc : c.val = 0 := by have hh := c.isLt; have hlen := h.cuffs_length_one hS; omega
  have hget : x.cuffs[c] = L := by simp only [Fin.getElem_fin, hL, hc, List.getElem_cons_zero]
  exact hL.trans (congrArg (fun A => [A]) hget.symm)

/-- Advancing all original cuff positions preserves the geometric order
among the new dual gap points. -/
theorem dualFollowingPoint_gap_order (g : GM06CuffGapRep h c R)
    (hS : IsClosedDiscSpace S) (a b i j : Fin x.cuffs[c].length) :
    GM06DrawingData.crossesOnList (List.finRange x.cuffs[c].length) a b i j = true ↔
      CrossesOn (bd S) (g.dualFollowingPoint a) (g.dualFollowingPoint b)
        (g.dualFollowingPoint i) (g.dualFollowingPoint j) := by
  simp only [Fin.getElem_fin] at *
  have ht := h.order (x.cuffs[c].get (gm06CycleSucc a))
    (x.cuffs[c].get (gm06CycleSucc b)) (x.cuffs[c].get (gm06CycleSucc i))
    (x.cuffs[c].get (gm06CycleSucc j))
  have hcross (u v r t : Fin x.n) : x.crosses u v r t =
      GM06DrawingData.crossesOnList x.cuffs[c] u v r t := by
    unfold GM06DrawingData.crosses
    calc
      _ = [x.cuffs[c]].any (fun L => GM06DrawingData.crossesOnList L u v r t) :=
        congrArg (fun A => A.any (fun L => GM06DrawingData.crossesOnList L u v r t))
          (cuff_singleton (c := c) h hS)
      _ = _ := by simp only [List.any_cons, List.any_nil, Bool.or_false]
  rw [hcross] at ht
  simp only [alg34_gap_disc_cuffs_eq hS, mem_singleton_iff, exists_eq_left,
    Fin.getElem_fin] at ht
  rw [gm06CrossesOnList_get (h.cuff_nodup _ (List.getElem_mem c.isLt)),
    gm06CrossesFinRange_succ] at ht
  exact ht

end GraphMinor.Compute.GM06CuffGapRep
