module

public import GraphMinor.GM06.Section5LinkageStripCircle
public import GraphMinor.GM06.Section5RadialProjection
import GraphMinor.GM06.Section5AdjacentStripUnion
import GraphMinor.GM06.Section5StripHalfNeighbourhood
import GraphMinor.GM06.Section5LiftedPaths
import GraphMinor.Surface.DiscGrow
import Mathlib.Analysis.Complex.CoveringMap

/-!
# Adjacent strip images cover a neighbourhood of their shared start

For the boundary-contact proof of VI (5.1), page 129, the boundary
of two joined lifted strip discs near their shared initial point
lies only on the bottom cuff. Their union fills a half-neighbourhood
in the radial strip. Angular projection is open relative to that
strip, so the images cover a cylinder neighbourhood of the start.
-/

public section
namespace GraphMinor.GM06
open Set Topology GraphMinor.Surface

/-- Angular projection carries a relatively open part of the closed
radial strip to an open set of the cylinder, including cuff points. -/
theorem isOpen_image_radialCylinderProjection_inter_strip
    {O : Set (ℝ × ℝ)} (hO : IsOpen O) :
    IsOpen (radialCylinderProjection '' ({p : ℝ × ℝ | 1 ≤ p.1 ∧ p.1 ≤ 2} ∩ O)) := by
  have hopen := (IsOpenMap.id.prodMap Circle.isCoveringMap_exp.isOpenMap) O hO
  have heq : radialCylinderProjection '' ({p : ℝ × ℝ | 1 ≤ p.1 ∧ p.1 ≤ 2} ∩ O) =
      Subtype.val ⁻¹' ((Prod.map id Circle.exp) '' O) := by
    ext x
    constructor
    · rintro ⟨p, ⟨hpstrip, hpO⟩, rfl⟩
      refine ⟨p, hpO, ?_⟩
      apply Prod.ext
      · exact (radialCylinderProjection_fst hpstrip).symm
      · rfl
    · rintro ⟨p, hpO, he⟩
      have hpstrip : 1 ≤ p.1 ∧ p.1 ≤ 2 :=
        (congrArg Prod.fst he).symm ▸ x.2.1
      refine ⟨p, ⟨hpstrip, hpO⟩, ?_⟩
      apply Subtype.ext
      apply Prod.ext
      · exact (radialCylinderProjection_fst hpstrip).trans (congrArg Prod.fst he)
      · change Circle.exp p.2 = x.1.2
        exact congrArg Prod.snd he
  rw [heq]
  exact hopen.preimage continuous_subtype_val

/-- The images of adjacent lifted strips cover a cylinder
neighbourhood of the initial point of their common linkage lift. -/
theorem exists_nhds_subset_adjacent_strip_images
    {k : ℕ} {G : Drawing ClosedCylinder} {θ : ℝ}
    (L : CylinderLinkage k G) (hG : IsCylinderSection5Drawing k G)
    (hθ : L.HasTheta θ) (m : ℤ)
    {D E : Set (ℝ × ℝ)} (hD : IsClosedDisc D) (hE : IsClosedDisc E)
    (hBdD : discBd D = liftedStripBoundary hG.1 L m)
    (hBdE : discBd E = liftedStripBoundary hG.1 L (m + 1))
    (hstripD : D ⊆ {p : ℝ × ℝ | 1 ≤ p.1 ∧ p.1 ≤ 2})
    (hstripE : E ⊆ {p : ℝ × ℝ | 1 ≤ p.1 ∧ p.1 ≤ 2}) :
    ∃ W : Set ClosedCylinder, IsOpen W ∧
      radialCylinderProjection (liftedLinkageCurve hG.1 L (m + 1) 0) ∈ W ∧
      W ⊆ radialCylinderProjection '' D ∪ radialCylinderProjection '' E := by
  let c := liftedLinkageCurve hG.1 L (m + 1) 0
  let A := range (liftedLinkageCurve hG.1 L m)
  let B := range (liftedLinkageCurve hG.1 L (m + 1 + 1))
  let N := (A ∪ B ∪ {p : ℝ × ℝ | p.1 = 2})ᶜ
  have hA : IsClosed A := (isCompact_range (liftedLinkageCurve hG.1 L m).continuous).isClosed
  have hB : IsClosed B := (isCompact_range (liftedLinkageCurve hG.1 L (m + 1 + 1)).continuous).isClosed
  have hN : IsOpen N := (hA.union hB |>.union (isClosed_eq continuous_fst continuous_const)).isOpen_compl
  have hc1 : c.1 = 1 := (liftedLinkageCurve_props_raw hG.1 L (m + 1)).2.1
  have hcmid : c ∈ range (liftedLinkageCurve hG.1 L (m + 1)) := mem_range_self 0
  have hcN : c ∈ N := by
    rintro ((hcA | hcB) | hc2)
    · exact disjoint_left.mp (disjoint_range_liftedLinkageCurve hG.1 L (m := m + 1) (n := m)
        (by omega)) hcmid hcA
    · exact disjoint_left.mp (disjoint_range_liftedLinkageCurve hG.1 L (m := m + 1) (n := m + 1 + 1)
        (by omega)) hcmid hcB
    · have heq := hc1.symm.trans hc2
      norm_num at heq
  obtain ⟨hU, hboundary⟩ := adjacent_liftedStripDiscs_union L hG hθ m hD hE hBdD hBdE hstripD hstripE
  have hcU : c ∈ D ∪ E := by
    apply Or.inl
    apply discBd_subset D
    rw [hBdD]
    exact Or.inl (Or.inl (Or.inr hcmid))
  have hbdN : N ∩ discBd (D ∪ E) ⊆ {p : ℝ × ℝ | p.1 = 1} := by
    intro p hp
    rcases hboundary hp.2 with hpout | hpC
    · exact False.elim (hp.1 (Or.inl hpout))
    · rcases hpC with hp1 | hp2
      · exact hp1
      · exact False.elim (hp.1 (Or.inr hp2))
  have hstripU := union_subset hstripD hstripE
  obtain ⟨O, hO, hcO, hcover⟩ := exists_strip_half_neighbourhood_of_boundary_germ
    hU hstripU hcU hN hcN hbdN
  refine ⟨radialCylinderProjection '' ({p : ℝ × ℝ | 1 ≤ p.1 ∧ p.1 ≤ 2} ∩ O),
    isOpen_image_radialCylinderProjection_inter_strip hO, ⟨c, ⟨hstripU hcU, hcO⟩, rfl⟩, ?_⟩
  rw [← image_union]
  exact image_mono hcover

end GraphMinor.GM06
