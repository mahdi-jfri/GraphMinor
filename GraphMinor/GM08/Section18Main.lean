module

public import GraphMinor.GM08.Section18Universes
public import GraphMinor.GM08.Section18X2Cut
public import GraphMinor.GM08.Section18CutStep

/-!
# VIII (18.3) and (6.1)

The `X₂` case of the cut counts holds (`x2CutCountStatement`). By
`theorem_18_3_of_X2` it gives (18.3), and by `theorem_6_1_of_183` (18.3) gives
(6.1).
-/

@[expose] public section

namespace GraphMinor.GM08

universe u v w

/-- The lift counts of (18.2) for every schism type and every surface. -/
theorem cutCountStatement : CutCountStatement.{w} :=
  cutCountStatement_of_X2 x2CutCountStatement

/-- The cut step of (18.3). -/
theorem cutStepStatement : CutStepStatement.{u, w} :=
  cutStepStatement_of_cutCount cutCountStatement

/-- **VIII (18.3)**, page 286: for any integers `h, k ≥ 0`, `𝒞(h, k)` is
well-rooted. -/
theorem theorem_18_3_proof : Theorem183Statement.{u, v, w} :=
  theorem_18_3_of_X2 x2CutCountStatement

/-- **VIII (6.1)**, page 263: if `𝒜` is a class of grafts with bounded index,
and some surface embeds `𝒜`, then `𝒜` is well-rooted. -/
theorem theorem_6_1_proof : Theorem61Statement.{u, v, w} :=
  theorem_6_1_of_183 theorem_18_3_proof

end GraphMinor.GM08
