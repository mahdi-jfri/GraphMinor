module

public import GraphMinor.GM06.Section5CoverSides
import GraphMinor.GM06.Section5CoverDisc
import GraphMinor.GM06.Section5IndexedStripImage
import GraphMinor.GM06.Section5InitialStripNeighbourhood
import GraphMinor.GM06.Section5StripInjective
import GraphMinor.GM06.Section5StripImage

/-!
# Agreement of clockwise incidence with the printed reduction

When there are at least two linkage paths, the closed strip disc
projects injectively. Its inverse lifts an incident edge in the printed
preceding strip. Connectedness puts this lift in the preceding cover
component, and continuity at the initial vertex gives the required
incidence with its chosen lift.
-/

public section
namespace GraphMinor.GM06
open Set Topology GraphMinor.Surface

/-- For at least two paths, the side-sensitive edge condition agrees
with the incidence and strip-containment condition of VI Reduction 1,
page 128. Thus its correction changes only the one-path case. -/
theorem isClockwiseInitialEdge_iff_of_two_le
    {k : ℕ} {G : Drawing ClosedCylinder}
    (L : CylinderLinkage k G) (hG : IsCylinderSection5Drawing k G)
    (hk : 1 < k) (i : Fin k)
    {e : Set ClosedCylinder} (he : e ∈ G.E) :
    IsClockwiseInitialEdge L i e ↔
      cylinderM1Point k i ∈ closure e ∧ e ⊆ cylinderStrip L (finPredCycle i) := by
  constructor
  · exact IsClockwiseInitialEdge.incident_and_subset
  rintro ⟨hs, heS⟩
  obtain ⟨θ, hθ⟩ := CylinderLinkage.exists_hasTheta hG.1 L
  let m : ℤ := (i.val : ℤ)
  obtain ⟨D, hD, hBd, hstrip, him⟩ := exists_indexed_stripDisc_with_image L hG hθ m
  rw [show modIdx k hG.1 m = finPredCycle i from modIdx_natCast_eq_finPredCycle hG.1 i] at him
  let : CompactSpace D := isCompact_iff_compactSpace.mp hD.isCompact
  have hinj := injOn_radialCylinderProjection_stripDisc L hG hk hθ m hD hBd hstrip
  let πD : D → ClosedCylinder := fun p => radialCylinderProjection p.1
  have hπc : Continuous πD := continuous_radialCylinderProjection.comp continuous_subtype_val
  have hπi : Function.Injective πD := fun p q h => Subtype.ext (hinj p.2 q.2 h)
  let H : D ≃ₜ range πD := Continuous.homeoOfEquivCompactToT2
    (f := Equiv.ofInjective πD hπi) hπc.rangeFactorization
  let B : Set (range πD) := Subtype.val ⁻¹' e
  let g : range πD → CylinderCover := fun x => planeToCylinderCover (H.symm x).1
  have hgc : Continuous g := continuous_planeToCylinderCover.comp
    (continuous_subtype_val.comp H.symm.continuous)
  have heK : e ⊆ range πD := by
    intro x hx
    obtain ⟨p, hp, hpmap⟩ := him.symm ▸ subset_closure (heS hx)
    exact ⟨⟨p, hp⟩, hpmap⟩
  have hBim : Subtype.val '' B = e := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact hy
    · intro hx
      exact ⟨⟨x, heK hx⟩, hx, rfl⟩
  have hB : IsConnected B := by
    refine ⟨?_, IsInducing.subtypeVal.isPreconnected_image.mp ?_⟩
    · obtain ⟨x, hx⟩ := he.1
      exact ⟨⟨x, heK hx⟩, hx⟩
    · rw [hBim]
      exact he.2.2.1.isConnected.isPreconnected
  have hgproj (x : range πD) : cylinderCoverProjection (g x) = x.1 := by
    have h := congrArg Subtype.val (H.apply_symm_apply x)
    change radialCylinderProjection (H.symm x).1 = x.1 at h
    exact h
  let q := liftedLinkageCurve hG.1 L (m + 1) 0
  have hqD : q ∈ D := by
    apply discBd_subset D
    rw [hBd]
    exact Or.inl (Or.inl (Or.inr (mem_range_self 0)))
  have hqproj : radialCylinderProjection q = cylinderM1Point k i := by
    rw [radialCylinderProjection_liftedLinkageCurve, modIdx_natCast_succ]
    exact (L.curve_parametrizes i).2.2.1
  let sK : range πD := ⟨cylinderM1Point k i, ⟨⟨q, hqD⟩, hqproj⟩⟩
  have hgs : g sK = cylinderInitialLift k i := by
    have hInv : (H.symm sK).1 = q :=
      hinj (H.symm sK).2 hqD
        ((congrArg Subtype.val (H.apply_symm_apply sK)).trans hqproj.symm)
    change planeToCylinderCover (H.symm sK).1 = _
    rw [hInv]
    apply Prod.ext
    · apply Subtype.ext
      change max 1 (min 2 q.1) = 1
      rw [(liftedLinkageCurve_props_raw hG.1 L (m + 1)).2.1]
      norm_num
    · change q.2 = _
      rw [(liftedLinkageCurve_props_raw hG.1 L (m + 1)).2.2.2.1]
      dsimp [m, cylinderInitialLift]
      push_cast
      rfl
  refine ⟨g '' B, hB.image g hgc.continuousOn, ?_, ?_, ?_⟩
  · ext x
    constructor
    · rintro ⟨_, ⟨y, hy, rfl⟩, rfl⟩
      change y.1 ∈ e at hy
      simpa only [hgproj] using hy
    · intro hx
      exact ⟨g ⟨x, heK hx⟩, ⟨⟨x, heK hx⟩, hx, rfl⟩, hgproj _⟩
  · rw [← hgs]
    apply mem_closure_image hgc.continuousAt
    apply closure_subtype.mpr
    rw [hBim]
    exact hs
  · rintro _ ⟨x, hx, rfl⟩
    apply mem_cylinderCoverStrip_of_mem_disc L hG hθ m hD hBd hstrip
    · have hp := (H.symm x).2
      change (max 1 (min 2 (H.symm x).1.1), (H.symm x).1.2) ∈ D
      rw [min_eq_right (hstrip hp).2, max_eq_right (hstrip hp).1]
      exact hp
    · rw [hgproj]
      exact (connectedComponentIn_subset _ _ (heS hx)).2

/-- For at least two paths, the corrected Reduction 1 is exactly the printed
edge deletion, with its unchanged linkage, from VI, page 128. -/
theorem section5Reduction1Step_iff_of_two_le
    {k : ℕ} {G G' : Drawing ClosedCylinder}
    (L : CylinderLinkage k G) (L' : CylinderLinkage k G')
    (hG : IsCylinderSection5Drawing k G) (hk : 1 < k) :
    Section5Reduction1Step k G L G' L' ↔
      ∃ (i : Fin k) (e : Set ClosedCylinder),
        e ∈ G.E ∧ cylinderM1Point k i ∈ closure e ∧
        e ⊆ cylinderStrip L (finPredCycle i) ∧ G'.V = G.V ∧
        G'.E = G.E \ {e} ∧ G'.U = G.U \ e ∧
        L'.pathDrawing = L.pathDrawing ∧ L'.curve = L.curve := by
  constructor
  · rintro ⟨i, e, he, hside, hV, hE, hU, hP, hf⟩
    exact ⟨i, e, he, hside.incident_and_subset.1, hside.incident_and_subset.2,
      hV, hE, hU, hP, hf⟩
  · rintro ⟨i, e, he, hs, hstrip, hV, hE, hU, hP, hf⟩
    exact ⟨i, e, he, (isClockwiseInitialEdge_iff_of_two_le L hG hk i he).mpr
      ⟨hs, hstrip⟩, hV, hE, hU, hP, hf⟩

end GraphMinor.GM06
