module

public import GraphMinor.GM06.Section5StripCuffs
import GraphMinor.GM06.Section5RegionPoint
import GraphMinor.GM11.Walks
import GraphMinor.GM07.NetExists

/-!
# Excluding initial-cuff edges from the region path

For VI (5.1), page 129, the region path is chosen to avoid the added
edge across the initial cuff gap. Every initial-cuff edge in the
region closure is that same edge. A point on any such edge lies on
the closed cuff gap. Since it is not a vertex, it is on the open gap,
where uniqueness of drawing edges identifies the two edges.
-/

public section

namespace GraphMinor.GM06

open Set GraphMinor.Surface

/-- Every initial-cuff edge in the closure of Rᵢ is the added edge
across its initial gap. -/
theorem eq_initial_gap_edge_of_subset_region_closure
    {k : ℕ} {G F : Drawing ClosedCylinder} {θ : ℝ}
    (L : CylinderLinkage k G) (hG : IsCylinderSection5Drawing k G)
    (hθ : L.HasTheta θ) (hFV : F.V = G.V) (i : Fin k)
    {e d : Set ClosedCylinder} (he : e ∈ F.E) (hd : d ∈ F.E)
    (hgap : initialCuffGapCurve k i '' Ioo 0 1 ⊆ e)
    (hdR : d ⊆ closure (cylinderRegion k G i)) (hdC : d ⊆ cylinderCuff1) : d = e := by
  obtain ⟨x, hx⟩ := hd.1
  have hxStrip : x ∈ closure (cylinderStrip L i) :=
    closure_mono (cylinderRegion_subset_strip L i) (hdR hx)
  obtain ⟨t, ht⟩ := closure_strip_inter_initial_cuff_subset_gap L hG hθ i ⟨hxStrip, hdC hx⟩
  have hxV : x ∉ G.V := by
    rw [← hFV]
    exact (hd.2.1 hx).2
  have hstart (j : Fin k) : cylinderM1Point k j ∈ G.V := by
    have hh : cylinderM1Point k j ∈ G.V ∩ bd ClosedCylinder :=
      hG.2.2.symm ▸ Or.inl ⟨j, rfl⟩
    exact hh.1
  have hf := initialCuffGapCurve_props hG i
  have ht0 : t ≠ 0 := by
    intro hh
    rw [hh, hf.1] at ht
    exact hxV (ht ▸ hstart i)
  have ht1 : t ≠ 1 := by
    intro hh
    rw [hh, hf.2.1] at ht
    exact hxV (ht ▸ hstart (finSuccCycle i))
  have htI : t ∈ Ioo (0 : unitInterval) 1 :=
    ⟨unitInterval.pos_iff_ne_zero.mpr ht0, unitInterval.lt_one_iff_ne_one.mpr ht1⟩
  exact GM07.arcComponentsIn_eq_of_mem hd he hx (hgap ⟨t, htI, ht⟩)

/-- A region-closure subpath avoiding the initial gap edge uses no
edge contained in the initial cuff. -/
theorem not_subset_initial_cuff_of_avoids_gap_edge
    {k : ℕ} {G F Q : Drawing ClosedCylinder} {θ : ℝ}
    (L : CylinderLinkage k G) (hG : IsCylinderSection5Drawing k G)
    (hθ : L.HasTheta θ) (hFV : F.V = G.V) (i : Fin k)
    (hQ : Q.IsSubdrawing F) (hQR : Q.U ⊆ closure (cylinderRegion k G i))
    {e : Set ClosedCylinder} (he : e ∈ F.E)
    (hgap : initialCuffGapCurve k i '' Ioo 0 1 ⊆ e) (heQ : e ∉ Q.E)
    {d : Set ClosedCylinder} (hd : d ∈ Q.E) : ¬ d ⊆ cylinderCuff1 := by
  intro hdC
  have hdR : d ⊆ closure (cylinderRegion k G i) := fun _ hx => hQR ((hd.2.1 hx).1)
  have hde := eq_initial_gap_edge_of_subset_region_closure L hG hθ hFV i he (hQ.2 hd) hgap hdR hdC
  exact heQ (hde ▸ hd)

end GraphMinor.GM06
