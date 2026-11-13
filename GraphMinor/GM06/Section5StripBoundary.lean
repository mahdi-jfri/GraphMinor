module

public import GraphMinor.GM06.Section5StripImage
import GraphMinor.GM06.Section5RegionPoint

/-!
# Which linkage paths meet a strip closure

In VI (5.1), page 129, the paths Qᵢ stay between Pᵢ and Pᵢ₊₁.
The compact disc description of the strip shows that no other linkage
path meets its closure. A point of another path would lift into the
disc on an indexed linkage curve. Every such curve except the two
boundary curves has already been excluded from the disc.
-/

public section

namespace GraphMinor.GM06

open Set GraphMinor.Surface

/-- Passing to the next indexed lift passes to the next cyclic
linkage index, also when the last index wraps to zero. -/
theorem modIdx_natCast_succ_add_one {k : ℕ} (hk : 0 < k) (i : Fin k) :
    modIdx k hk (((i.val : ℤ) + 1) + 1) = finSuccCycle i := by
  by_cases hi : i.val + 1 < k
  · let j : Fin k := ⟨i.val + 1, hi⟩
    have he : ((i.val : ℤ) + 1) + 1 = (j.val : ℤ) + 1 := by
      dsimp [j]
    rw [he, modIdx_natCast_succ]
    simp only [j, finSuccCycle, hi, dite_true]
  · have hik : i.val + 1 = k := by omega
    have he : ((i.val : ℤ) + 1) + 1 = 1 + (k : ℤ) * 1 := by omega
    rw [he, modIdx_add_mul]
    have hz := modIdx_natCast_succ hk (⟨0, hk⟩ : Fin k)
    simpa [finSuccCycle, hi] using hz

/-- The closure of a linkage strip misses every path except its two
cyclic neighbours. -/
theorem disjoint_closure_strip_path_of_not_neighbour
    {k : ℕ} {G : Drawing ClosedCylinder} {θ : ℝ}
    (L : CylinderLinkage k G) (hG : IsCylinderSection5Drawing k G)
    (hθ : L.HasTheta θ) (i j : Fin k) (hji : j ≠ i) (hjs : j ≠ finSuccCycle i) :
    Disjoint (closure (cylinderStrip L i)) (L.pathDrawing j).U := by
  let m : ℤ := (i.val : ℤ) + 1
  obtain ⟨D, hD, hBd, hstrip⟩ := exists_closedDisc_of_liftedStripBoundary L hG hθ m
  have him := image_stripDisc_eq_closure_strip L hG hθ i hD hBd hstrip
  apply disjoint_left.mpr
  intro x hx hxj
  obtain ⟨p, hp, hpx⟩ := him.symm ▸ hx
  obtain ⟨t, ht⟩ := (L.curve_parametrizes j).2.1.symm ▸ hxj
  have hr : p.1 = (L.curve j t).1.1 := by
    rw [← radialCylinderProjection_fst (hstrip hp), hpx, ht]
  have ha : Circle.exp p.2 = (L.curve j t).1.2 := by
    have hh := congrArg (fun z : ClosedCylinder => z.1.2) (hpx.trans ht.symm)
    exact hh
  obtain ⟨n, hn⟩ := exists_index_of_linkage_projection hG.1 L j t p hr ha
  have hjn : j = modIdx k hG.1 n := by
    by_contra hne
    have hxn : x ∈ (L.pathDrawing (modIdx k hG.1 n)).U := by
      rw [← hpx, ← hn, radialCylinderProjection_liftedLinkageCurve]
      exact (L.curve_parametrizes _).2.1 ▸ mem_range_self t
    exact disjoint_left.mp (L.pairwise_disjoint hne) hxj hxn
  have hnm : n ≠ m := by
    intro he
    rw [he, modIdx_natCast_succ] at hjn
    exact hji hjn
  have hnm1 : n ≠ m + 1 := by
    intro he
    rw [he, modIdx_natCast_succ_add_one] at hjn
    exact hjs hjn
  exact disjoint_left.mp (disjoint_stripDisc_of_other_index L hG hθ hnm hnm1 hD hBd hstrip)
    ⟨t, hn⟩ hp

/-- The same exclusion holds for the smaller region Rᵢ whose
boundary supplies the path Qᵢ in VI (5.1). -/
theorem disjoint_closure_region_path_of_not_neighbour
    {k : ℕ} {G : Drawing ClosedCylinder} {θ : ℝ}
    (L : CylinderLinkage k G) (hG : IsCylinderSection5Drawing k G)
    (hθ : L.HasTheta θ) (i j : Fin k) (hji : j ≠ i) (hjs : j ≠ finSuccCycle i) :
    Disjoint (closure (cylinderRegion k G i)) (L.pathDrawing j).U :=
  (disjoint_closure_strip_path_of_not_neighbour L hG hθ i j hji hjs).mono_left
    (closure_mono (cylinderRegion_subset_strip L i))

end GraphMinor.GM06
