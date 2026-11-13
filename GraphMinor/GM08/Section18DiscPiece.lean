module

public import GraphMinor.GM07.CutStages
public import GraphMinor.GM11.Defs
import GraphMinor.GM07.Section8
import GraphMinor.Surface.InvarianceOfDomain
import GraphMinor.Surface.CutComp
import GraphMinor.Surface.Cuffs

/-!
# A disc piece of a cut gives a planar circle

When we cut along the arcs of a schism, we must rule out pieces that are
closed discs (VIII (18.2), page 286). Suppose a piece `D` of a cut along `F`
is a closed disc, the cut map is one to one on `D`, and `D` holds a lift of a
point of `F`. The boundary circle of `D` lies over `F ∪ bd(Σ)`, and it meets
the lift of `F`, so it lies over `F`. Its image is a circle in `F` that lies in
the disc `ψ(D)`, so it is planar (`exists_planar_oArc_of_disc_piece`). For a
schism this is impossible, since its circles are not planar.
-/

@[expose] public section

namespace GraphMinor.GM08

open Set Topology GraphMinor.Surface GraphMinor.GM11

universe w

/-- The one to one image of a closed disc is a closed disc, with the image
boundary. -/
theorem isClosedDisc_image_of_injOn {S T : Type w} [TopologicalSpace S] [TopologicalSpace T]
    [T2Space S] {θ : T → S} (hθ : Continuous θ) {D : Set T} (hD : IsClosedDisc D)
    (hinj : InjOn θ D) : IsClosedDisc (θ '' D) ∧ discBd (θ '' D) = θ '' discBd D := by
  obtain ⟨φ⟩ := hD
  have : CompactSpace ClosedUnitDisc := isCompact_iff_compactSpace.mp (isCompact_closedBall _ _)
  have : CompactSpace D := φ.compactSpace
  let f : D → S := fun x => θ x.1
  have hf : Continuous f := hθ.comp continuous_subtype_val
  have hfi : Function.Injective f := fun x y h => Subtype.ext (hinj x.2 y.2 h)
  let e₀ : D ≃ₜ range f := (hf.isClosedEmbedding hfi).isEmbedding.toHomeomorph
  have hrange : range f = θ '' D := by
    ext x
    constructor
    · rintro ⟨y, rfl⟩
      exact ⟨y.1, y.2, rfl⟩
    · rintro ⟨y, hy, rfl⟩
      exact ⟨⟨y, hy⟩, rfl⟩
  let e : D ≃ₜ θ '' D := e₀.trans (Homeomorph.setCongr hrange)
  refine ⟨⟨φ.trans e⟩, ?_⟩
  rw [disc_boundary (θ '' D) (φ.trans e), disc_boundary D φ, image_image]
  rfl

/-- **A disc piece gives a planar circle.** If a cut along a closed set `F`
that misses the boundary has an open and closed piece `D` that is a closed
disc, on which the cut map is one to one, and `D` meets the lift of `F`, then
some circle in `F` is planar. -/
theorem exists_planar_oArc_of_disc_piece {S T : Type w} [TopologicalSpace S] [TopologicalSpace T]
    (hS : IsSurface S) {F : Set S} (hF : IsClosed F) (hFbd : Disjoint F (bd S)) {θ : T → S}
    (hθ : GM07.IsCutAlongSet F θ) {D : Set T} (hDo : IsOpen D) (hD : IsClosedDisc D)
    (hinj : InjOn θ D) (hmeet : (D ∩ θ ⁻¹' F).Nonempty) :
    ∃ Z ⊆ F, IsOArc Z ∧ IsPlanar Z := by
  have : T2Space S := hS.2.1
  have hθc : Continuous θ := hθ.quotientMap.continuous
  obtain ⟨hdisc, hbdeq⟩ := isClosedDisc_image_of_injOn hθc hD hinj
  set Z := θ '' discBd D
  have hZ : IsOArc Z := hbdeq ▸ hdisc.isOArc_discBd
  have hdiscBd : discBd D = D ∩ bd T := by
    ext z
    constructor
    · rintro ⟨z', hz', rfl⟩
      exact ⟨z'.2, (mem_bd_sub hDo).mp hz'⟩
    · rintro ⟨hzD, hzb⟩
      exact ⟨⟨z, hzD⟩, (mem_bd_sub hDo).mpr hzb, rfl⟩
  have hZsub : Z ⊆ F ∪ bd S := by
    rintro _ ⟨z, hz, rfl⟩
    rw [hdiscBd] at hz
    have : z ∈ θ ⁻¹' (bd S ∪ F) := hθ.preimage_bd ▸ hz.2
    exact this.elim Or.inr Or.inl
  obtain ⟨z, hzD, hzF⟩ := hmeet
  have hzZ : θ z ∈ Z := by
    refine ⟨z, ?_, rfl⟩
    rw [hdiscBd]
    exact ⟨hzD, hθ.preimage_bd ▸ (Or.inr hzF : θ z ∈ bd S ∪ F)⟩
  have hbdc : IsClosed (bd S) := (cuff_statement S hS).1
  have hZF : Z ⊆ F := by
    rcases (isPreconnected_iff_subset_of_disjoint_closed.mp (GM07.IsOArc.isConnected hZ).isPreconnected)
        F (bd S) hF hbdc hZsub (by
          rw [hFbd.inter_eq, inter_empty]) with h | h
    · exact h
    · exact absurd (h hzZ) (disjoint_left.mp hFbd hzF)
  refine ⟨Z, hZF, hZ, θ '' D, hdisc, ?_⟩
  exact image_mono (Subtype.coe_image_subset _ _)
