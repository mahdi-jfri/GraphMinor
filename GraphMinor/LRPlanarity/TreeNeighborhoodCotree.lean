module

public import GraphMinor.LRPlanarity.TreeNeighborhoodUnion
public import GraphMinor.LRPlanarity.TreeNeighborhoodPlacement
import GraphMinor.LRPlanarity.TreeNeighborhoodPorts
import GraphMinor.LRPlanarity.TreeNeighborhoodInteriors
import GraphMinor.LRPlanarity.TreeNeighborhoodCenterlines
import Mathlib.Tactic.Linarith

/-!
# Cotree intersections with the polygon and strip union

Part IV, Section 7b of the planarity note keeps all strips off cotree
edges, and all nonincident polygons off them as well. Thus a cotree edge
meets the tree neighborhood only in its two endpoint polygons. The normal
facet equations identify these intersections as exactly the two endpoint
tails. The strict tails lie in the polygon interiors.
-/

public section
namespace GraphMinor.LRPlanarity

open Set Surface

/-- Part IV, Section 7b: a straight edge missing the strips and all
nonincident polygons meets their union only in the two normal endpoint
tails, whose strict parts are interior. -/
theorem cotree_edge_union_coordinates {N : ℕ} (point : Fin N → ℂ)
    (directions : Fin N → Finset ℝ) (r : Fin N → ℝ) (R : Fin N → Set ℂ)
    (S : Finset (Fin N)) (s t : Fin N) (hs : s ∈ S) (ht : t ∈ S)
    (μ ν d : ℝ) (hd : 0 < d)
    (hendpoint : point s + eC μ * (d : ℂ) = point t)
    (hopposite : eC ν = -eC μ) (hμ : μ ∈ directions s) (hν : ν ∈ directions t)
    (hstrips : ∀ v ∈ S, Disjoint (R v) (segment ℝ (point s) (point t)))
    (hpolygons : ∀ v ∈ S, v ≠ s → v ≠ t → Disjoint
      (vertexPolygonAt (point v) (directions v) (r v)) (segment ℝ (point s) (point t))) :
    let P := fun v => vertexPolygonAt (point v) (directions v) (r v)
    let D := forestCellUnion P R S
    (∀ z ∈ Icc (0 : ℝ) d,
      point s + eC μ * (z : ℂ) ∈ D ↔ z ≤ r s ∨ d - r t ≤ z) ∧
    (∀ z ∈ Icc (0 : ℝ) d, z < r s ∨ d - r t < z →
      point s + eC μ * (z : ℂ) ∈ interior D) := by
  intro P D
  have hreverse : ∀ z : ℝ, point s + eC μ * (z : ℂ) =
      point t + (d - z) • eC ν := by
    intro z
    rw [← hendpoint, hopposite, Complex.real_smul]
    push_cast
    ring
  have hsource : ∀ z : ℝ, point s + eC μ * (z : ℂ) = point s + z • eC μ := by
    intro z
    rw [Complex.real_smul, mul_comm]
  have hline : ∀ z ∈ Icc (0 : ℝ) d,
      point s + eC μ * (z : ℂ) ∈ segment ℝ (point s) (point t) := by
    intro z hz
    rw [← hendpoint]
    exact stripCenterline_subset_segment _ _ hd le_rfl le_rfl ⟨z, hz, rfl⟩
  have hPsub : ∀ v ∈ S, P v ⊆ D := by
    intro v hv x hx
    exact mem_iUnion.mpr ⟨v, mem_iUnion.mpr ⟨hv, Or.inl hx⟩⟩
  constructor
  · intro z hz
    constructor
    · intro hx
      obtain ⟨v, hv⟩ := mem_iUnion.mp hx
      obtain ⟨hvS, hxv⟩ := mem_iUnion.mp hv
      rcases hxv with hxP | hxR
      · by_cases hvs : v = s
        · subst v
          rw [hsource] at hxP
          exact Or.inl ((ray_point_mem_vertexPolygonAt_iff _ _ hz.1 hμ).mp hxP)
        · by_cases hvt : v = t
          · subst v
            rw [hreverse] at hxP
            have h := (ray_point_mem_vertexPolygonAt_iff _ _ (sub_nonneg.mpr hz.2) hν).mp hxP
            exact Or.inr (by linarith)
          · exact (disjoint_left.mp (hpolygons v hvS hvs hvt) hxP (hline z hz)).elim
      · exact (disjoint_left.mp (hstrips v hvS) hxR (hline z hz)).elim
    · intro hx
      rcases hx with hzs | hzt
      · apply hPsub s hs
        rw [hsource]
        exact (ray_point_mem_vertexPolygonAt_iff _ _ hz.1 hμ).mpr hzs
      · apply hPsub t ht
        rw [hreverse]
        exact (ray_point_mem_vertexPolygonAt_iff _ _ (sub_nonneg.mpr hz.2) hν).mpr (by linarith)
  · intro z hz htail
    rcases htail with hzs | hzt
    · exact interior_mono (hPsub s hs)
        (ray_point_mem_polygon_interior _ _ μ hz.1 hzs)
    · rw [hreverse]
      have hpoint := ray_point_mem_polygon_interior (point t) (directions t) ν
        (sub_nonneg.mpr hz.2) (show d - z < r t by linarith)
      rw [Complex.real_smul, mul_comm]
      exact interior_mono (hPsub t ht) hpoint

end GraphMinor.LRPlanarity
