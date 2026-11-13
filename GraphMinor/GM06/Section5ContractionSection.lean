module

public import GraphMinor.GM06.Defs
public import GraphMinor.GM06.Section5CoverTranslation
import GraphMinor.GM06.Section5ContractionCoverMap

/-!
# Vertex and endpoint properties of the contraction section

The finite-visit construction for VI (5.5), page 130, chooses the
old neighbour above each collapsed vertex and the unique inverse
elsewhere. This section preserves vertex membership and fixes all
nonexceptional boundary lifts. Points outside the new drawing pull
back outside the old drawing, so unchanged intervals stay normal.
-/

public section
namespace GraphMinor.GM06
open Set GraphMinor.Surface

/-- Projecting a section of the lifted contraction gives an actual
preimage under the cylinder contraction. -/
theorem projection_section_cover_contraction
    (π : C(ClosedCylinder, ClosedCylinder)) (Φ : C(CylinderCover, CylinderCover))
    (hproj : ∀ p, cylinderCoverProjection (Φ p) = π (cylinderCoverProjection p))
    (ρ : CylinderCover → CylinderCover) (hρ : ∀ q, Φ (ρ q) = q) (q : CylinderCover) :
    π (cylinderCoverProjection (ρ q)) = cylinderCoverProjection q :=
  (hproj _).symm.trans (congrArg cylinderCoverProjection (hρ q))

/-- Choosing the old neighbour above the exceptional value preserves
vertex membership exactly in every angular sheet. -/
theorem vertex_mem_iff_of_cover_contraction_section
    {G G' : Drawing ClosedCylinder}
    (π : C(ClosedCylinder, ClosedCylinder)) (Φ : C(CylinderCover, CylinderCover))
    (s v : ClosedCylinder)
    (hproj : ∀ p, cylinderCoverProjection (Φ p) = π (cylinderCoverProjection p))
    (hinj : ∀ x y, π x ≠ s → π y ≠ s → π x = π y → x = y)
    (hV : G'.V = π '' G.V) (hv : v ∈ G.V) (hs : s ∈ G'.V)
    (ρ : CylinderCover → CylinderCover) (hρ : ∀ q, Φ (ρ q) = q)
    (hρv : ∀ q, cylinderCoverProjection q = s → cylinderCoverProjection (ρ q) = v)
    (q : CylinderCover) :
    cylinderCoverProjection (ρ q) ∈ G.V ↔ cylinderCoverProjection q ∈ G'.V := by
  have hπ := projection_section_cover_contraction π Φ hproj ρ hρ q
  by_cases hqs : cylinderCoverProjection q = s
  · exact iff_of_true (hρv q hqs ▸ hv) (hqs ▸ hs)
  · rw [hV]
    constructor
    · intro hq
      exact ⟨_, hq, hπ⟩
    · rintro ⟨x, hx, hxq⟩
      have hxi : x = cylinderCoverProjection (ρ q) := hinj x _
        (by rw [hxq]; exact hqs) (by rw [hπ]; exact hqs) (hxq.trans hπ.symm)
      exact hxi ▸ hx

/-- Outside points stay outside the old drawing under a section of
the lifted contraction. -/
theorem not_mem_drawing_of_cover_contraction_section
    {G G' : Drawing ClosedCylinder}
    (π : C(ClosedCylinder, ClosedCylinder)) (Φ : C(CylinderCover, CylinderCover))
    (hproj : ∀ p, cylinderCoverProjection (Φ p) = π (cylinderCoverProjection p))
    (hU : G'.U = π '' G.U)
    (ρ : CylinderCover → CylinderCover) (hρ : ∀ q, Φ (ρ q) = q)
    {q : CylinderCover} (hq : cylinderCoverProjection q ∉ G'.U) :
    cylinderCoverProjection (ρ q) ∉ G.U := by
  intro hmem
  exact hq (hU ▸ ⟨_, hmem, projection_section_cover_contraction π Φ hproj ρ hρ q⟩)

/-- Every nonexceptional fixed point is fixed by the section, in
particular the helix endpoint lifts on the cuffs. -/
theorem section_eq_self_of_fixed_cover_contraction
    (π : C(ClosedCylinder, ClosedCylinder)) (Φ : C(CylinderCover, CylinderCover))
    (s : ClosedCylinder)
    (hproj : ∀ p, cylinderCoverProjection (Φ p) = π (cylinderCoverProjection p))
    (htrans : ∀ z p, Φ (cylinderCoverTranslation z p) = cylinderCoverTranslation z (Φ p))
    (hinj : ∀ x y, π x ≠ s → π y ≠ s → π x = π y → x = y)
    (ρ : CylinderCover → CylinderCover) (hρ : ∀ q, Φ (ρ q) = q)
    (q : CylinderCover) (hq : cylinderCoverProjection q ≠ s) (hfix : Φ q = q) : ρ q = q := by
  exact cover_contraction_injective_away_from_value π Φ s hproj htrans hinj
    (by rw [hρ]; exact hq) ((hρ q).trans hfix.symm)

end GraphMinor.GM06
