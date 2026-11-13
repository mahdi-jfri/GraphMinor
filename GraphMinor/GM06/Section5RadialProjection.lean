module

public import GraphMinor.GM06.Defs
import Mathlib.Topology.Covering.Basic
import Mathlib.Topology.Constructions.SumProd
import Mathlib.Analysis.SpecialFunctions.Complex.Circle

/-!
# Projection from radial-angular coordinates

The angular cover in VI Section 5, pages 128–129, projects (r, a)
to the cylinder point with radius r and angle exp(a). We extend this
map to the whole plane by clamping the radius to [1, 2]. On the open
radial strip this is the usual open covering map. The extension lets
us use continuity and compactness for closed strip discs.
-/

public section

namespace GraphMinor.GM06

open Set Topology GraphMinor.Surface

/-- The angular projection, extended off the radial strip by clamping
the radius. On the radial strip the radius is unchanged. -/
@[expose] noncomputable def radialCylinderProjection (p : ℝ × ℝ) : ClosedCylinder :=
  ⟨(max 1 (min 2 p.1), Circle.exp p.2),
    ⟨⟨le_max_left _ _, max_le (by norm_num) (min_le_left _ _)⟩, mem_univ _⟩⟩

/-- The extended angular projection is continuous. -/
theorem continuous_radialCylinderProjection : Continuous radialCylinderProjection :=
  ((continuous_const.max (continuous_const.min continuous_fst)).prodMk
    (Circle.exp.continuous.comp continuous_snd)).subtype_mk _

/-- Projection preserves the radial coordinate throughout the strip. -/
theorem radialCylinderProjection_fst {p : ℝ × ℝ} (hp : 1 ≤ p.1 ∧ p.1 ≤ 2) :
    (radialCylinderProjection p).1.1 = p.1 := by
  change max 1 (min 2 p.1) = p.1
  rw [min_eq_right hp.2, max_eq_right hp.1]

/-- Angular projection takes an open subset of the open radial strip
to an open subset of the cylinder. -/
theorem isOpen_image_radialCylinderProjection
    {U : Set (ℝ × ℝ)} (hU : IsOpen U)
    (hstrip : U ⊆ {p : ℝ × ℝ | 1 < p.1 ∧ p.1 < 2}) :
    IsOpen (radialCylinderProjection '' U) := by
  have hopen := (IsOpenMap.id.prodMap Circle.isCoveringMap_exp.isOpenMap) U hU
  have heq : radialCylinderProjection '' U =
      Subtype.val ⁻¹' ((Prod.map id Circle.exp) '' U) := by
    ext x
    constructor
    · rintro ⟨p, hp, rfl⟩
      refine ⟨p, hp, ?_⟩
      apply Prod.ext
      · exact (radialCylinderProjection_fst ⟨(hstrip hp).1.le, (hstrip hp).2.le⟩).symm
      · rfl
    · rintro ⟨p, hp, he⟩
      refine ⟨p, hp, ?_⟩
      apply Subtype.ext
      apply Prod.ext
      · exact (radialCylinderProjection_fst ⟨(hstrip hp).1.le, (hstrip hp).2.le⟩).trans
          (congrArg Prod.fst he)
      · change Circle.exp p.2 = x.1.2
        exact congrArg Prod.snd he
  rw [heq]
  exact hopen.preimage continuous_subtype_val

end GraphMinor.GM06
