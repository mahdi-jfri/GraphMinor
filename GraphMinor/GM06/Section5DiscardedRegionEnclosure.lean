module

public import GraphMinor.GM11.LocalCone
import GraphMinor.GM06.Section5LocalDiscardedSeed
import GraphMinor.GM06.Section5PolarLocalDrawingDirections
import GraphMinor.GM06.Section5AttachedCompactEnclosure
import GraphMinor.GM06.Section5CompactRegionEnclosure
import GraphMinor.Surface.DiscMerge
import GraphMinor.GM11.Regions

/-!
# Enclosing a whole discarded region piece

For Reduction 2 in VI (5.5), page 130, the seed covers discarded
points near the attachment. The remaining part is compact: away
from the attachment a region frontier cannot meet the discarded
side. Enlarge the seed to include that compact part. If the region
has no discarded rim direction, its whole discarded part is compact
and an ordinary disc inside the region suffices. In both cases the
boundary misses the full drawing except possibly at the attachment.
-/

public section
namespace GraphMinor.GM06
open Set Topology GraphMinor.Surface GraphMinor.GM11 unitInterval

/-- Enclose the entire part of the other separation side in one
retained region. Only the attachment can lie on the enclosing
boundary in the full drawing. -/
theorem exists_disc_enclosing_discarded_region_piece
    {S : Type*} [TopologicalSpace S] [T2Space S] [ConnectedSpace S]
    (hS : IsClosedSurface S) (hsph : IsSphere S)
    {Γ T H : Drawing S} (hT : T.IsSubdrawing Γ) (hH : H.IsSubdrawing Γ) {s : S}
    {Φ : C(ClosedUnitDisc, S)} (hp : IsPolar Γ s Φ)
    (hsT : s ∈ T.U) (hTp : IsPreconnected (T.U \ {s}))
    (hscl : s ∈ closure (T.U \ {s})) (hover : H.U ∩ T.U ⊆ {s})
    (hcover : Γ.U ⊆ T.U ∪ H.U) {r : Set S} (hr : r ∈ T.R) :
    ∃ E : Set S, IsClosedDisc E ∧ E ⊆ r ∪ {s} ∧
      H.U ∩ r ⊆ discInt E ∧ discBd E ∩ Γ.U ⊆ {s} := by
  classical
  let : LocallyConnectedSpace S := IsClosedSurface.locallyConnectedSpace hS
  let : CompactSpace S := hS.1
  have hman : ∀ x : S, IsManifoldPoint x := fun x => (hS.2.2 x).isManifoldPoint
  have hrc : r ∈ componentsIn T.Uᶜ := by
    have hh : (univ \ T.U : Set S) = T.Uᶜ := by ext y; simp
    change r ∈ componentsIn (univ \ T.U) at hr
    rwa [hh] at hr
  let N := interior (range Φ)
  let K := (H.U ∩ r) \ N
  have hKeq : K = (H.U ∩ closure r) \ N := by
    ext y
    constructor
    · rintro ⟨⟨hyH, hyr⟩, hyN⟩
      exact ⟨⟨hyH, subset_closure hyr⟩, hyN⟩
    · rintro ⟨⟨hyH, hycl⟩, hyN⟩
      refine ⟨⟨hyH, ?_⟩, hyN⟩
      rcases closure_region_subset hr hycl with hyr | hyT
      · exact hyr
      · have hys : y = s := hover ⟨hyH, hyT⟩
        exact False.elim (hyN (hys.symm ▸ hp.nhd))
  have hK : IsCompact K := by
    rw [hKeq]
    exact ((H.isClosed_U.inter isClosed_closure).inter isOpen_interior.isClosed_compl).isCompact
  have hKr : K ⊆ r := fun y hy => hy.1.2
  have finish (E : Set S) (hE : IsClosedDisc E) (hEr : E ⊆ r ∪ {s})
      (hHE : H.U ∩ r ⊆ discInt E) :
      IsClosedDisc E ∧ E ⊆ r ∪ {s} ∧ H.U ∩ r ⊆ discInt E ∧ discBd E ∩ Γ.U ⊆ {s} := by
    refine ⟨hE, hEr, hHE, ?_⟩
    rintro y ⟨hyb, hyΓ⟩
    rcases hEr (GraphMinor.Surface.discBd_subset E hyb) with hyr | hys
    · rcases hcover hyΓ with hyT | hyH
      · exact False.elim (region_subset hr hyr hyT)
      · exact False.elim ((hHE ⟨hyH, hyr⟩).2 hyb)
    · exact hys
  by_cases hne : ((polarRimMap Φ) ⁻¹' (H.U ∩ r)).Nonempty
  · obtain ⟨D, hD, hsD, hDr, hlocal⟩ := exists_seed_containing_local_discarded_region
      hS hsph hT hH hp hsT hTp hscl hover hr hne
    obtain ⟨E, hE, hDE, hKE, _, hEr, _⟩ := exists_attached_disc_enclosing_compact_in_region
      hS hsph T.isClosed_U hTp hscl hrc hK hKr hD hDr
      (GraphMinor.Surface.discBd_subset D hsD)
    refine ⟨E, finish E hE hEr ?_⟩
    intro y hy
    by_cases hyN : y ∈ N
    · exact discInt_mono hman hD hDE (hlocal ⟨hy, hyN⟩)
    · exact hKE ⟨hy, hyN⟩
  · have hwhole : H.U ∩ r ⊆ K := by
      intro y hy
      refine ⟨hy, ?_⟩
      intro hyN
      obtain ⟨_, w, _, _, _, hw⟩ := exists_rim_direction_of_local_subdrawing_region_point
        hS hT hH hp hsT hr hyN hy.1 hy.2
      exact hne ⟨w, hw⟩
    have hTc : IsConnected T.U := by
      refine ⟨⟨s, hsT⟩, hTp.subset_closure sdiff_subset ?_⟩
      intro y hy
      by_cases he : y = s
      · exact he.symm ▸ hscl
      · exact subset_closure ⟨hy, he⟩
    obtain ⟨E, hE, hEr, hKE, _⟩ := exists_disc_enclosing_compact_in_sphere_region
      hS hsph T.isClosed_U hTc hrc hK hKr
    exact ⟨E, finish E hE (hEr.trans subset_union_left) (hwhole.trans hKE)⟩

end GraphMinor.GM06
