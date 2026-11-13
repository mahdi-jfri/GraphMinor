module

public import GraphMinor.GM06.Defs
import GraphMinor.GM06.Section5CoverLocalHomeomorph
import GraphMinor.GM06.Section5CoverSides
import GraphMinor.GM06.Section5ArcImageInterior
import Mathlib.Topology.GDelta.Basic
import Mathlib.Topology.Separation.Regular

/-!
# A simple lifted curve leaves interior points available

For the disc detours in the Reduction 2 proof of VI (5.5), page 130,
the projection of an injective cover curve has empty interior. Cover
charts make the projected curve locally injective. Compactness gives
finitely many closed pieces on which it is injective. Each image is
closed with empty interior, so their finite union has empty interior.
-/

public section
namespace GraphMinor.GM06
open Set Topology GraphMinor.Surface

/-- The cylinder image of an injective angular-cover curve has
empty interior, so it cannot fill any open disc. -/
theorem interior_projection_injective_cover_curve_eq_empty
    (q : C(unitInterval, CylinderCover)) (hq : Function.Injective q) :
    interior (cylinderCoverProjection '' range q) = ∅ := by
  classical
  let f : Curve ClosedCylinder := ⟨fun t => cylinderCoverProjection (q t),
    continuous_cylinderCoverProjection.comp q.continuous⟩
  have hlocal (t : unitInterval) : ∃ K : Set unitInterval,
      K ∈ 𝓝 t ∧ IsClosed K ∧ InjOn f K := by
    obtain ⟨η, htη, hη⟩ := isLocalHomeomorph_cylinderCoverProjection (q t)
    obtain ⟨K, hKt, hKc, hKsub⟩ := exists_mem_nhds_isClosed_subset
      ((η.open_source.preimage q.continuous).mem_nhds htη)
    refine ⟨K, hKt, hKc, ?_⟩
    intro a ha b hb he
    apply hq
    apply η.injOn (hKsub ha) (hKsub hb)
    rw [← hη]
    exact he
  choose K hKt hKc hKi using hlocal
  have hcover : (univ : Set unitInterval) ⊆ ⋃ t, interior (K t) := by
    intro t _
    exact mem_iUnion.mpr ⟨t, mem_interior_iff_mem_nhds.mpr (hKt t)⟩
  obtain ⟨T, hT⟩ := isCompact_univ.elim_finite_subcover (fun t => interior (K t))
    (fun _ => isOpen_interior) hcover
  have hpieces (t) : IsNowhereDense (f '' K t) := by
    change interior (closure (f '' K t)) = ∅
    rw [((hKc t).isCompact.image f.continuous).isClosed.closure_eq]
    exact interior_image_compact_injOn_curve_eq_empty f (hKc t).isCompact (hKi t)
  have hfinite : IsNowhereDense (⋃ t ∈ T, f '' K t) := IsNowhereDense.biUnion (fun t _ => hpieces t)
  have hsub : range f ⊆ ⋃ t ∈ T, f '' K t := by
    rintro y ⟨t, rfl⟩
    obtain ⟨u, huT, htu⟩ := mem_iUnion₂.mp (hT (mem_univ t))
    exact mem_iUnion₂.mpr ⟨u, huT, t, interior_subset htu, rfl⟩
  have hsmall := hfinite.mono hsub
  have him : range f = cylinderCoverProjection '' range q := by
    ext x
    constructor
    · rintro ⟨t, rfl⟩
      exact mem_image_of_mem cylinderCoverProjection (mem_range_self t)
    · rintro ⟨y, ⟨t, rfl⟩, rfl⟩
      exact mem_range_self t
  rw [← him]
  have he : closure (range f) = range f := (isCompact_range f.continuous).isClosed.closure_eq
  simpa only [IsNowhereDense, he] using hsmall

end GraphMinor.GM06
