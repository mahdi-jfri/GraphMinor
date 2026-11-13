module

public import GraphMinor.GM06.Defs
public import GraphMinor.GM06.Section5CoverTranslation
import GraphMinor.GM06.Section5ContractionCoverMap
import GraphMinor.GM06.Section5Red
import GraphMinor.GM11.Walks
import GraphMinor.GM06.Section5CoverCurvePoint

/-!
# The exceptional fibre in a specified angular sheet

In the cover form of Reduction 3 in VI (5.5), page 130, the fibre
of the chosen initial lift is exactly the lift of the closed
contracted edge. Uniqueness of cover curves shows that the lifted
edge is collapsed to that point. Full-turn equivariance excludes
all its other sheet copies from the fibre.
-/

public section
namespace GraphMinor.GM06
open Set GraphMinor.Surface

/-- The interior parameters of a non-loop closed-edge parametrization
trace exactly the open edge, with no end vertices. -/
theorem image_Ioo_of_parametrizesSet_closure_edge
    {G : Drawing ClosedCylinder} {e : Set ClosedCylinder} {s v : ClosedCylinder}
    (hl : G.toGraph.IsLink e s v) (γ : Curve ClosedCylinder)
    (hγ : ParametrizesSet γ (closure e) s v) : γ '' Ioo 0 1 = e := by
  apply subset_antisymm
  · rintro x ⟨t, ht, rfl⟩
    have hcl : γ t ∈ closure e := hγ.2.1 ▸ mem_range_self t
    have hnotV : γ t ∉ G.V := by
      intro htV
      have he : γ t ∈ ({s, v} : Set ClosedCylinder) := hl.2.2.2 ▸ ⟨hcl, htV⟩
      rcases he with he | he
      · exact ht.1.ne' (hγ.1 (he.trans hγ.2.2.1.symm))
      · exact ht.2.ne (hγ.1 ((mem_singleton_iff.mp he).trans hγ.2.2.2.symm))
    exact G.closure_diff_V hl.1 ▸ ⟨hcl, hnotV⟩
  · intro x hx
    obtain ⟨t, ht⟩ := hγ.2.1 ▸ subset_closure hx
    have ht0 : t ≠ 0 := by
      intro he
      have hxs : x = s := ht.symm.trans (he ▸ hγ.2.2.1)
      exact (hl.1.2.1 hx).2 (hxs ▸ hl.2.1)
    have ht1 : t ≠ 1 := by
      intro he
      have hxv : x = v := ht.symm.trans (he ▸ hγ.2.2.2)
      exact (hl.1.2.1 hx).2 (hxv ▸ hl.2.2.1)
    exact ⟨t, ⟨lt_of_le_of_ne (show 0 ≤ t from bot_le) ht0.symm,
      lt_of_le_of_ne (show t ≤ 1 from le_top) ht1⟩, ht⟩

/-- A lifted arc parametrizing the exceptional fibre is precisely
the fibre over its fixed initial cover point. -/
theorem preimage_singleton_cover_contraction_eq_range
    (π : C(ClosedCylinder, ClosedCylinder)) (Φ : C(CylinderCover, CylinderCover))
    (hproj : ∀ p, cylinderCoverProjection (Φ p) = π (cylinderCoverProjection p))
    (htrans : ∀ z p, Φ (cylinderCoverTranslation z p) = cylinderCoverTranslation z (Φ p))
    (γ : Curve ClosedCylinder) (q : C(unitInterval, CylinderCover))
    (hq : ∀ t, cylinderCoverProjection (q t) = γ t)
    (p : CylinderCover) (hq0 : q 0 = p) (hfix : Φ p = p)
    (hfibre : π ⁻¹' {cylinderCoverProjection p} = range γ) :
    Φ ⁻¹' {p} = range q := by
  have hγ (t) : π (γ t) = cylinderCoverProjection p := by
    have hm : γ t ∈ π ⁻¹' {cylinderCoverProjection p} := hfibre ▸ mem_range_self t
    exact hm
  let r : C(unitInterval, CylinderCover) := Φ.comp q
  have hr : r = ContinuousMap.const _ p := cover_curves_eq_of_projection_eq
    r (ContinuousMap.const _ p) (fun t => by
      change cylinderCoverProjection (Φ (q t)) = cylinderCoverProjection p
      rw [hproj, hq, hγ]) 0 (by
        change Φ (q 0) = p
        rw [hq0, hfix])
  have hcollapsed (t) : Φ (q t) = p :=
    congrArg (fun c : C(unitInterval, CylinderCover) => c t) hr
  ext x
  constructor
  · intro hx
    have hπx : π (cylinderCoverProjection x) = cylinderCoverProjection p := by
      rw [← hproj, show Φ x = p from hx]
    have hxrange : cylinderCoverProjection x ∈ range γ := hfibre ▸ hπx
    obtain ⟨t, ht⟩ := hxrange
    refine ⟨t, ?_⟩
    exact cover_map_injective_on_projection_fibre Φ htrans
      ((hq t).trans ht) ((hcollapsed t).trans (show Φ x = p from hx).symm)
  · rintro ⟨t, rfl⟩
    exact hcollapsed t

/-- The exceptional fibre over a fixed initial lift is parametrized
by one lifted copy of the old non-loop edge. -/
theorem exists_parametrized_cover_contraction_fibre
    {G : Drawing ClosedCylinder} {e : Set ClosedCylinder} {s v : ClosedCylinder}
    (hl : G.toGraph.IsLink e s v) (hv : v ≠ s)
    (π : C(ClosedCylinder, ClosedCylinder)) (Φ : C(CylinderCover, CylinderCover))
    (hproj : ∀ p, cylinderCoverProjection (Φ p) = π (cylinderCoverProjection p))
    (htrans : ∀ z p, Φ (cylinderCoverTranslation z p) = cylinderCoverTranslation z (Φ p))
    (hfibre : π ⁻¹' {s} = closure e)
    (p : CylinderCover) (hp : cylinderCoverProjection p = s) (hfix : Φ p = p) :
    ∃ γ : Curve ClosedCylinder, ∃ q : C(unitInterval, CylinderCover),
      ParametrizesSet γ (closure e) s v ∧ q 0 = p ∧
      (∀ t, cylinderCoverProjection (q t) = γ t) ∧ Φ ⁻¹' {p} = range q := by
  obtain ⟨γ, hγ⟩ := exists_parametrizesSet_closure_edge G hl hv.symm
  obtain ⟨q, hq0, hq⟩ := exists_cover_curve_through_point γ 0 p (hp.trans hγ.2.2.1.symm)
  have hf : π ⁻¹' {cylinderCoverProjection p} = range γ := by
    rw [hp, hfibre, hγ.2.1]
  exact ⟨γ, q, hγ, hq0, hq,
    preimage_singleton_cover_contraction_eq_range π Φ hproj htrans γ q hq p hq0 hfix hf⟩

/-- A specified old neighbour lift supplies a neighbour preimage
for every sheet above the contraction value. -/
theorem exists_neighbour_preimage_in_each_sheet
    (Φ : C(CylinderCover, CylinderCover))
    (htrans : ∀ z p, Φ (cylinderCoverTranslation z p) = cylinderCoverTranslation z (Φ p))
    (p w : CylinderCover) (hw : Φ w = p) {s v : ClosedCylinder}
    (hp : cylinderCoverProjection p = s) (hwv : cylinderCoverProjection w = v)
    (q : CylinderCover) (hq : cylinderCoverProjection q = s) :
    ∃ x, Φ x = q ∧ cylinderCoverProjection x = v := by
  obtain ⟨z, hz⟩ := exists_cover_translation_of_projection_eq (hq.trans hp.symm)
  refine ⟨cylinderCoverTranslation z w, ?_, ?_⟩
  · rw [htrans, hw, ← hz]
  · rw [cylinderCoverProjection_translation, hwv]

/-- Choose a section of the lifted contraction that sends every
exceptional value to the old neighbour in its corresponding sheet. -/
theorem exists_cover_contraction_section_at_neighbour
    (π : C(ClosedCylinder, ClosedCylinder)) (Φ : C(CylinderCover, CylinderCover))
    (s v : ClosedCylinder)
    (hproj : ∀ p, cylinderCoverProjection (Φ p) = π (cylinderCoverProjection p))
    (htrans : ∀ z p, Φ (cylinderCoverTranslation z p) = cylinderCoverTranslation z (Φ p))
    (hsurj : ∀ x, x ≠ s → ∃ y, π y = x)
    (p w : CylinderCover) (hw : Φ w = p)
    (hp : cylinderCoverProjection p = s) (hwv : cylinderCoverProjection w = v) :
    ∃ ρ : CylinderCover → CylinderCover, (∀ q, Φ (ρ q) = q) ∧
      ∀ q, cylinderCoverProjection q = s → cylinderCoverProjection (ρ q) = v := by
  classical
  have hpoint (q : CylinderCover) : ∃ x, Φ x = q ∧
      (cylinderCoverProjection q = s → cylinderCoverProjection x = v) := by
    by_cases hq : cylinderCoverProjection q = s
    · obtain ⟨x, hx, hxv⟩ := exists_neighbour_preimage_in_each_sheet Φ htrans p w hw hp hwv q hq
      exact ⟨x, hx, fun _ => hxv⟩
    · obtain ⟨x, hx⟩ := cover_contraction_surjective_away_from_value π Φ s hproj htrans hsurj q hq
      exact ⟨x, hx, fun he => False.elim (hq he)⟩
  choose ρ hρ hρv using hpoint
  exact ⟨ρ, hρ, hρv⟩

end GraphMinor.GM06
