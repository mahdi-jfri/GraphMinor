module

public import GraphMinor.GM06.Section5CutInitialGap
public import GraphMinor.GM06.Section5CoverDisc
import GraphMinor.GM06.Section5RegionPoint

/-!
# A point of the lifted gap in the selected region

The midpoint of the lifted initial gap is exactly the seed defining
the following cover region. Properness excludes the drawing at its
projection, the prescribed initial dual point. Thus this midpoint
belongs to that lifted region. It supplies the incidence point for
the added gap edge in the one-path proof of VI (5.1), page 129.
-/

public section
namespace GraphMinor.GM06
open Set Topology Real GraphMinor.Surface

/-- An interior point of the lifted initial gap lies in the selected
cover region: its midpoint is the defining seed. -/
theorem exists_cut_initial_gap_point_in_coverRegion
    {G : Drawing ClosedCylinder} (hG : IsCylinderSection5Drawing 1 G)
    {D : Set (ℝ × ℝ)} (g : Curve D)
    (hgcoord : ∀ t, (g t).1 = (1, 2 * (1 + (t : ℝ)) * π)) :
    ∃ t ∈ Ioo (0 : unitInterval) 1,
      planeToCylinderCover (g t).1 ∈ cylinderCoverRegion 1 G 0 := by
  let t : unitInterval := ⟨1 / 2, by constructor <;> norm_num⟩
  let b : CylinderCover := (⟨1, by norm_num⟩,
    (2 * (((0 : Fin 1).val + 1 : ℕ) : ℝ) + 1) * π / (1 : ℕ))
  have ht : t ∈ Ioo (0 : unitInterval) 1 := by
    constructor
    · change (0 : ℝ) < 1 / 2
      norm_num
    · change (1 / 2 : ℝ) < 1
      norm_num
  have hgb : planeToCylinderCover (g t).1 = b := by
    rw [hgcoord]
    apply Prod.ext
    · apply Subtype.ext
      change max 1 (min 2 (1 : ℝ)) = 1
      norm_num
    · change 2 * (1 + (t : ℝ)) * π =
        (2 * (((0 : Fin 1).val + 1 : ℕ) : ℝ) + 1) * π / (1 : ℕ)
      norm_num [t]
  refine ⟨t, ht, ?_⟩
  rw [hgb]
  unfold cylinderCoverRegion
  apply mem_connectedComponentIn
  exact ⟨mem_univ _, cylinderN1Point_not_mem_U hG 0⟩

end GraphMinor.GM06
