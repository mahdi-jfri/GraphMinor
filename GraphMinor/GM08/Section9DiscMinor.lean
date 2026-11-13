module

public import GraphMinor.GM08.Section9
public import GraphMinor.GM07.Defs
public import GraphMinor.Minor.Model
import GraphMinor.GM08.Section9MinorModel
import GraphMinor.GM08.Section9DiscContext
import GraphMinor.GM08.Section9GraftDrawing
import GraphMinor.Surface.Disc
import GraphMinor.GM08.Section9RingDistance
import GraphMinor.GM08.Section9NestLinkage
import GraphMinor.GM07.Section9
import GraphMinor.GM06.DiscRegions
import GraphMinor.Surface.DiscsInSurface

/-!
# Applying VII (9.4) to the boundary-linked nest of VIII (9.3)

Two parallel rings enclose a long portion of the nest. The intervening
circuits give transverse distance, the radial paths give linkage between
the rings, and boundary linkage gives paths from the inner ring to the
boundary. These are precisely the hypotheses of VII (9.4).
-/

public section

namespace GraphMinor.GM08

open Set Surface

universe u

/-- The geometric application of VII (9.4) in VIII (9.3), page 270.
A sufficiently large boundary-linked nest contains a boundary-rooted
minor of any proper surface digraph with the same boundary vertices. -/
theorem boundaryRootedMinor_of_boundaryLinkedNest {S : Type u}
    [TopologicalSpace S] [T2Space S] [CompactSpace S] [ConnectedSpace S]
    (hS : IsSurface S) (hΔ : IsClosedDisc (univ : Set S))
    (hcuffs : cuffs S = {bd S}) (H G : GM07.SurfaceDigraph S)
    (hH : H.IsProper) (hG : G.IsProper)
    (hbd : G.G.V ∩ bd S = H.G.V ∩ bd S)
    {r s : ℕ}
    (hr : GM07.rCylinderBound H.G * 5 ^ (H.G.V.ncard + H.G.E.ncard) ≤ r)
    (hs : 2 * (GM07.rCylinderBound H.G * 5 ^ (H.G.V.ncard + H.G.E.ncard)) + 3 ≤ s)
    (N : DrawingNest G.G univ r s) (hBL : IsBoundaryLinkedNest G.G univ N) :
    GM07.IsBoundaryRootedMinor H G := by
  let R := GM07.rCylinderBound H.G * 5 ^ (H.G.V.ncard + H.G.E.ncard)
  obtain ⟨B₁, B₂, hB₁, hB₂, hi, hj, hk, hl, hn₁, hn₂, hin, hd, hbd₂, hdist⟩ :=
    N.exists_parallel_discs_with_distance hΔ hs
  have hB₂Δ : B₂ ⊆ (univ : Set S) := subset_univ _
  have hB₁₂ : B₁ ⊆ B₂ := hin.trans (discInt_subset _)
  have hlast : B₂ ⊆ discInt (N.circuit ⟨s - 1, by omega⟩).ins :=
    hl.trans (N.insideDisc_subset_of_le hΔ
      (i := ⟨2 * R + 2, by omega⟩) (j := ⟨s - 1, by omega⟩)
      (by change 2 * R + 2 ≤ s - 1; dsimp [R]; omega)).2
  have hnormbd : G.G.IsNormal (discBd (univ : Set S)) := by
    rw [GM06.discBd_univ]
    exact hG
  apply GM07.theorem_9_4_proof hS hΔ hcuffs H G hH hG hbd hn₁ hn₂
    hB₁.isOArc_discBd hB₂.isOArc_discBd hd
  · intro x hx
    refine Or.inl ⟨?_, B₂, hB₂, rfl, hin (discBd_subset _ hx)⟩
    exact isNullHomotopicOArcIn_of_subset_disc hB₂.isOArc_discBd
      (subset_univ _) hB₂ (discBd_subset _)
  · rw [← GM06.discBd_univ S]
    exact hbd₂.mono_left (discBd_subset _)
  · intro F hn hF hmeet₁ hmeet₂
    have hconn : IsPreconnected F := by
      obtain ⟨f⟩ := hF
      have heq : F = range (fun t => (f t).1) := by
        ext z
        exact ⟨fun hz => ⟨f.symm ⟨z, hz⟩, by simp⟩,
          by rintro ⟨t, rfl⟩; exact (f t).2⟩
      rw [heq]
      exact isPreconnected_range (by fun_prop)
    exact hdist F hn hconn (subset_univ _) hmeet₁ hmeet₂
  · exact hr.trans (N.le_maxDisjointPaths_parallel_rings hΔ (subset_univ _) (by omega)
      hB₁ hB₂ hB₁₂ hB₂Δ hn₁ hn₂ hi hlast)
  · rw [← GM06.discBd_univ S]
    exact N.boundary_le_maxDisjointPaths_parallel_ring hΔ (subset_univ _) (by omega)
      hBL hB₁ (subset_univ _) hn₁ hnormbd hi

/-- The undirected drawing form of the application of VII (9.4) in
VIII (9.3), page 270. The two drawings have the same boundary vertices. -/
theorem exists_minorModel_of_boundaryLinkedNest {S : Type u} [TopologicalSpace S]
    (hΔ : IsClosedDisc (univ : Set S)) (H G : Drawing S)
    (hH : H.IsProper) (hG : G.IsProper) (hbd : G.V ∩ bd S = H.V ∩ bd S)
    {r s : ℕ}
    (hr : GM07.rCylinderBound H * 5 ^ (H.V.ncard + H.E.ncard) ≤ r)
    (hs : 2 * (GM07.rCylinderBound H * 5 ^ (H.V.ncard + H.E.ncard)) + 3 ≤ s)
    (N : DrawingNest G univ r s) (hBL : IsBoundaryLinkedNest G univ N) :
    ∃ (ηv : S → Set S) (ηe : Set S → Set S),
      IsMinorModel H.toGraph G.toGraph ηv ηe ∧
      ∀ v ∈ H.V ∩ bd S, v ∈ ηv v := by
  have hS := isSurface_of_closedDisc_univ hΔ
  have : CompactSpace S := hS.1
  have : T2Space S := hS.2.1
  have : ConnectedSpace S := connectedSpace_iff_univ.mpr hΔ.isPathConnected.isConnected
  obtain ⟨x, -⟩ := hΔ.isPathConnected.nonempty
  have : Nonempty S := ⟨x⟩
  obtain ⟨HH, hHH⟩ := exists_surfaceDigraph_of_drawing H
  obtain ⟨GG, hGG⟩ := exists_surfaceDigraph_of_drawing G
  have hH' : HH.IsProper := by simpa only [GM07.SurfaceDigraph.IsProper, hHH] using hH
  have hG' : GG.IsProper := by simpa only [GM07.SurfaceDigraph.IsProper, hGG] using hG
  have hbd' : GG.G.V ∩ bd S = HH.G.V ∩ bd S := by rw [hHH, hGG]; exact hbd
  have hr' : GM07.rCylinderBound HH.G * 5 ^ (HH.G.V.ncard + HH.G.E.ncard) ≤ r := by
    rw [hHH]; exact hr
  have hs' : 2 * (GM07.rCylinderBound HH.G * 5 ^ (HH.G.V.ncard + HH.G.E.ncard)) + 3 ≤ s := by
    rw [hHH]; exact hs
  let N' : DrawingNest GG.G univ r s := hGG.symm ▸ N
  have hBL' : IsBoundaryLinkedNest GG.G univ N' := by
    dsimp only [N']
    cases hGG
    exact hBL
  have hm := boundaryRootedMinor_of_boundaryLinkedNest hS hΔ (cuffs_of_closedDisc_univ hΔ)
    HH GG hH' hG' hbd' hr' hs' N' hBL'
  simpa only [hHH, hGG] using exists_minorModel_of_boundaryRootedMinor hm

end GraphMinor.GM08
