module

public import GraphMinor.Surface.ArcTools
public import Mathlib.Analysis.Convex.Segment
import GraphMinor.LRPlanarity.PolygonalizationApproximation
import GraphMinor.LRPlanarity.PolygonalizationLoopErasure

/-!
# Polygonal edges with radial endpoint tails

Part IV, Section 7a of the planarity note appends the two radial segments
to the polygonal approximation of a middle arc. Erasing self-intersections
in the finite segment arrangement leaves a simple polygonal arc between
the original vertex points. Its image stays inside the two radial tails
and the chosen open neighborhood of the middle arc.
-/

public section
namespace GraphMinor.LRPlanarity

open Set

/-- Part IV, Section 7a: approximate the middle arc, append its two radial
tails, and remove self-intersections without leaving those three sets. -/
theorem exists_polygonal_arc_with_tails {f : unitInterval → ℂ} (hf : Continuous f)
    {U : Set ℂ} (hU : IsOpen U) (hfU : range f ⊆ U)
    (a b : ℂ) (hab : a ≠ b) :
    ∃ L : Set ℂ, Surface.IsLineWithEnds L a b ∧
      L ⊆ segment ℝ a (f 0) ∪ U ∪ segment ℝ (f 1) b ∧
      ∃ pieces : Finset (ℂ × ℂ), L = ⋃ p ∈ pieces, segment ℝ p.1 p.2 := by
  obtain ⟨n, hn, p, hp0, hp1, hseg⟩ := exists_polygonal_walk_in_open hf hU hfU
  let q : Fin (n + 3) → ℂ := Fin.cons a (Fin.snoc p b)
  have hq0 : q 0 = a := rfl
  have hq1 : q (Fin.last (n + 2)) = b := by simp [q]
  have hqmid : ∀ j : Fin (n + 1), q j.castSucc.succ = p j := by
    intro j
    dsimp only [q]
    rw [Fin.cons_succ, Fin.snoc_castSucc]
  have hqsub : ∀ i : Fin (n + 2), segment ℝ (q i.castSucc) (q i.succ) ⊆
      segment ℝ a (f 0) ∪ U ∪ segment ℝ (f 1) b := by
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · simpa [q, hp0] using
        (subset_union_left : segment ℝ a (f 0) ⊆ segment ℝ a (f 0) ∪ U) |>.trans subset_union_left
    · refine Fin.lastCases ?_ (fun k => ?_) j
      · change segment ℝ (q (Fin.last n).succ.castSucc) (q (Fin.last n).succ.succ) ⊆ _
        have he : (Fin.last n).succ.succ = Fin.last (n + 2) := by
          rw [Fin.succ_last, Fin.succ_last]
        rw [Fin.castSucc_succ, hqmid, he, hq1, hp1]
        exact subset_union_right
      · change segment ℝ (q k.castSucc.succ.castSucc) (q k.castSucc.succ.succ) ⊆ _
        have he : k.castSucc.succ.succ = k.succ.castSucc.succ :=
          congrArg Fin.succ (Fin.succ_castSucc k)
        rw [Fin.castSucc_succ, hqmid, he, hqmid]
        exact (hseg k).trans
          ((subset_union_right : U ⊆ segment ℝ a (f 0) ∪ U).trans subset_union_left)
  obtain ⟨L, hL, hsub, pieces, hpieces⟩ :=
    polygonal_walk_contains_polygonal_arc (Nat.succ_pos (n + 1)) q
      (by simpa only [hq0, hq1] using hab)
  refine ⟨L, ?_, hsub.trans (iUnion_subset hqsub), pieces, hpieces⟩
  simpa only [hq0, hq1] using hL

end GraphMinor.LRPlanarity
