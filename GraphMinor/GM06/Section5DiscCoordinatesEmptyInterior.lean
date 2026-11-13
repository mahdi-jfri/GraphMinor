module

public import GraphMinor.Surface.DiscGrow
import GraphMinor.Surface.DiscsInSurface
import Mathlib.Analysis.Normed.Module.RCLike.Real

/-!
# Empty curve interior in disc coordinates

For the small attachment fibre in VI (5.5), page 130, choose an
omitted point in disc coordinates. Empty interior is preserved by
those coordinates. An open coordinate set contains points inside
the unit circle, and its inverse-chart image is open in the surface.
If it lay in the curve image, that image would have nonempty interior.
-/

public section
namespace GraphMinor.GM06
open Set Topology Metric GraphMinor.Surface

/-- A subset with empty surface interior also has empty interior
in the coordinates of a closed disc containing it. -/
theorem interior_chart_image_eq_empty
    {S : Type*} [TopologicalSpace S] [T2Space S]
    (hman : ∀ x : S, IsManifoldPoint x)
    {D X : Set S} {h : S → ℂ} {j : ℂ → S} (c : IsChart D h j)
    (hXD : X ⊆ D) (hX : interior X = ∅) : interior (h '' X) = ∅ := by
  apply eq_empty_iff_forall_notMem.mpr
  intro y hy
  let V := interior (h '' X)
  have hVcb : V ⊆ closedBall (0 : ℂ) 1 :=
    interior_subset.trans (image_subset_iff.mpr (fun _ hx => c.hm (hXD hx)))
  have hycl : y ∈ closure (ball (0 : ℂ) 1) := by
    rw [closure_ball (0 : ℂ) one_ne_zero]
    exact hVcb hy
  obtain ⟨z, hzV, hzb⟩ := mem_closure_iff.mp hycl V isOpen_interior hy
  let W := V ∩ ball (0 : ℂ) 1
  have hWcb : W ⊆ closedBall (0 : ℂ) 1 := inter_subset_right.trans ball_subset_closedBall
  have hopen : IsOpen (j '' W) := isOpen_image_of_manifold
    (isOpen_interior.inter isOpen_ball) (c.gc.mono hWcb) (c.injOn.mono hWcb)
    (fun _ _ => hman _)
  have hsub : j '' W ⊆ X := by
    rintro _ ⟨w, hw, rfl⟩
    obtain ⟨x, hx, he⟩ := interior_subset hw.1
    rw [← he, c.gh (hXD hx)]
    exact hx
  have hsmall := interior_maximal hsub hopen
  rw [hX] at hsmall
  exact hsmall (mem_image_of_mem j ⟨hzV, hzb⟩)

end GraphMinor.GM06
