module

public import GraphMinor.GM11.LocalCone
public import GraphMinor.GM06.Section5PolarRimCoordinates
import GraphMinor.GM06.Section5PolarRayCurves
import GraphMinor.GM06.Section5PolarRegionProjection
import GraphMinor.GM06.Section5PolarSubdrawingRegions
import GraphMinor.GM06.Section5TwoAccessCircle
import GraphMinor.GM06.Section5AttachedRegionCircles
import GraphMinor.GM11.Regions
import GraphMinor.GM11.EdgeSides
import GraphMinor.Surface.CutComp

/-!
# A retained region has one angular corner at the attachment

For VI (5.5), page 130, the retained barrier remains connected
after the attachment is removed. Two polar accesses in one region
bound a circle through that attachment. Sphere separation gives a
disc inside the region with the attachment added. A small half-disc
on its inside has both accesses in its closure. Angular projection
of that connected half-disc joins the two rim directions within
the same local region. Thus the rim part of each region is connected.
-/

public section
namespace GraphMinor.GM06
open Set Topology GraphMinor.Surface GraphMinor.GM11 unitInterval

/-- A region of a punctured connected barrier occupies a preconnected
set of polar rim directions at the attachment. -/
theorem isPreconnected_polar_rim_region_of_punctured_barrier
    {S : Type*} [TopologicalSpace S] [T2Space S] [ConnectedSpace S]
    (hS : IsClosedSurface S) (hsph : IsSphere S)
    {Γ T : Drawing S} (hT : T.IsSubdrawing Γ) {s : S}
    {Φ : C(ClosedUnitDisc, S)} (hp : IsPolar Γ s Φ)
    (hsT : s ∈ T.U) (hTp : IsPreconnected (T.U \ {s}))
    (hscl : s ∈ closure (T.U \ {s}))
    {r : Set S} (hr : r ∈ T.R) :
    IsPreconnected ((polarRimMap Φ) ⁻¹' r) := by
  let : LocallyConnectedSpace S := IsClosedSurface.locallyConnectedSpace hS
  obtain ⟨q, hqc, hqray, hqr⟩ := exists_region_preserving_polar_angular_projection hT hp hr hsT
  have hsr : s ∉ r := fun h => region_subset hr h hsT
  have hrp : IsPathConnected r := isPathConnected_of_isOpen hS
    (region_isOpen hr) (region_isPreconnected hr) (region_nonempty hr)
  have hrc : r ∈ componentsIn T.Uᶜ := by
    have hh : (univ \ T.U : Set S) = T.Uᶜ := by ext y; simp
    change r ∈ componentsIn (univ \ T.U) at hr
    rwa [hh] at hr
  apply isPreconnected_of_forall_pair
  intro w₁ hw₁ w₂ hw₂
  by_cases hww : w₁ = w₂
  · subst w₂
    exact ⟨{w₁}, singleton_subset_iff.mpr hw₁, mem_singleton w₁,
      mem_singleton w₁, isPreconnected_singleton⟩
  let g₁ := polarRayCurve Φ w₁
  let g₂ := polarRayCurve Φ w₂
  have hq₁ (a : I) (ha : 0 < a) : q (g₁ a) = w₁ := hqray a ha w₁
  have hq₂ (a : I) (ha : 0 < a) : q (g₂ a) = w₂ := hqray a ha w₂
  have h₁0 : g₁ 0 = s := polarRayCurve_zero hp w₁
  have h₂0 : g₂ 0 = s := polarRayCurve_zero hp w₂
  have h₁ : ∀ t, 0 < t → g₁ t ∈ r := by
    intro t ht
    have hh := polar_ray_mem_region_of_subdrawing hT hp hr
      (polarDiscPoint_one_ne_centre w₁) hw₁ t ht
    rwa [discScale_polarDiscPoint_one] at hh
  have h₂ : ∀ t, 0 < t → g₂ t ∈ r := by
    intro t ht
    have hh := polar_ray_mem_region_of_subdrawing hT hp hr
      (polarDiscPoint_one_ne_centre w₂) hw₂ t ht
    rwa [discScale_polarDiscPoint_one] at hh
  have hdis : ∀ a b, g₁ a = g₂ b → g₁ a = s := by
    intro a b he
    by_cases ha : a = 0
    · rwa [ha]
    by_cases hb : b = 0
    · rw [he, hb, h₂0]
    have hangle := congrArg q he
    rw [hq₁ a (pos_iff_ne_zero.mpr ha),
      hq₂ b (pos_iff_ne_zero.mpr hb)] at hangle
    exact (hww hangle).elim
  obtain ⟨F, e, t₀, s₀, O, hF, hFr, ht₀, hs₀, he0, hep, heF, hgF, hO, hsO, hOr⟩ :=
    exists_circle_following_two_accesses hrp hsr g₁ g₂ (polarRayCurve_injective hp w₂)
      h₁0 h₂0 h₁ h₂ hdis
  obtain ⟨D, hDr, hD, hDb⟩ :=
    exists_disc_for_circle_in_region_with_attachment hS hsph hTp hscl hrc hFr hF
  have hsD : s ∈ discBd D := hDb.symm ▸ heF ⟨0, ⟨le_rfl, ht₀.le⟩, he0⟩
  obtain ⟨A, N, hN, hsN, hAp, hAD, hAb, hAX, _, hclA⟩ :=
    exists_half_nbhd hD isOpen_interior.isClosed_compl hsD (by
      exact fun hn => hn hp.nhd)
  have hAr : A ⊆ r := by
    intro y hy
    rcases hDr (hAD hy) with hyr | hys
    · exact hyr
    · exact False.elim (disjoint_left.mp hAb hy (mem_singleton_iff.mp hys ▸ hsD))
  have hAΦ : A ⊆ range Φ := by
    intro y hy
    apply interior_subset
    by_contra hyn
    exact disjoint_left.mp hAX hy hyn
  have hAq : A ⊆ range Φ \ {s} := by
    intro y hy
    exact ⟨hAΦ hy, fun he => hsr (mem_singleton_iff.mp he ▸ hAr hy)⟩
  have hqAp : IsPreconnected (q '' A) := hAp.image q (hqc.mono hAq)
  have hqAr : q '' A ⊆ (polarRimMap Φ) ⁻¹' r := by
    rintro w ⟨y, hy, rfl⟩
    exact hqr y ⟨hAΦ hy, hAr hy⟩
  obtain ⟨t, ht, htt₀, htN⟩ := exists_pos_le e.continuous (hN.inter hO)
    (by rw [he0]; exact ⟨hsN, hsO⟩) ht₀
  obtain ⟨u, hu, hus₀, huN⟩ := exists_pos_le g₂.continuous hN
    (by rw [h₂0]; exact hsN) hs₀
  have htecl : e t ∈ closure A :=
    hclA ⟨(htN t le_rfl).1, hDb.symm ▸ heF ⟨t, ⟨ht.le, htt₀⟩, rfl⟩⟩
  have hugecl : g₂ u ∈ closure A :=
    hclA ⟨huN u le_rfl, hDb.symm ▸ hgF ⟨u, ⟨hu.le, hus₀⟩, rfl⟩⟩
  obtain ⟨a, ha⟩ := hOr t (htN t le_rfl).2
  have ha0 : 0 < a := pos_iff_ne_zero.mpr fun he => by
    have hts : e t = s := ha.symm.trans (by rw [he, h₁0])
    exact hsr (hts ▸ hep t ht)
  have hteq : e t ∈ range Φ \ {s} := by
    refine ⟨ha ▸ mem_range_self (polarDiscPoint a w₁), ?_⟩
    intro he
    exact hsr (mem_singleton_iff.mp he ▸ hep t ht)
  have hugeq : g₂ u ∈ range Φ \ {s} := by
    refine ⟨mem_range_self (polarDiscPoint u w₂), ?_⟩
    intro he
    exact hsr (mem_singleton_iff.mp he ▸ h₂ u hu)
  have hw₁cl : w₁ ∈ closure (q '' A) := by
    have hh := ((hqc (e t) hteq).mono hAq).mem_closure_image htecl
    rwa [← ha, hq₁ a ha0] at hh
  have hw₂cl : w₂ ∈ closure (q '' A) := by
    have hh := ((hqc (g₂ u) hugeq).mono hAq).mem_closure_image hugecl
    rwa [hq₂ u hu] at hh
  let C := insert w₁ (insert w₂ (q '' A))
  have hCcl : C ⊆ closure (q '' A) := by
    exact insert_subset_iff.mpr ⟨hw₁cl, insert_subset_iff.mpr ⟨hw₂cl, subset_closure⟩⟩
  have hAC : q '' A ⊆ C := fun z hz => Or.inr (Or.inr hz)
  have hCp : IsPreconnected C := hqAp.subset_closure hAC hCcl
  have hCW : C ⊆ (polarRimMap Φ) ⁻¹' r :=
    insert_subset_iff.mpr ⟨hw₁, insert_subset_iff.mpr ⟨hw₂, hqAr⟩⟩
  exact ⟨C, hCW, Or.inl rfl, Or.inr (Or.inl rfl), hCp⟩

end GraphMinor.GM06
