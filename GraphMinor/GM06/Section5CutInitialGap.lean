module

public import GraphMinor.GM06.Section5CutStripSurface
public import GraphMinor.GM06.Section5BoundaryGap
import GraphMinor.GM06.Section5GapEdge
import Mathlib.Analysis.Convex.PathConnected

/-!
# The initial gap on the one-path cut disc

In the cut disc, the initial cuff gap is an injective boundary arc
between the two copies of the initial vertex. Its projection is the
full initial cuff gap of the cylinder. This arc supplies the added
boundary edge excluded from the region walk in VI (5.1), page 129.
-/

public section
namespace GraphMinor.GM06
open Set Topology Real GraphMinor.Surface

/-- The initial gap lifts to an injective boundary arc in the cut disc,
even though its two ends project to the same cylinder vertex. -/
theorem exists_single_strip_initial_gap_curve
    {G : Drawing ClosedCylinder} (L : CylinderLinkage 1 G)
    (hG : IsCylinderSection5Drawing 1 G) {D : Set (ℝ × ℝ)}
    (hBd : discBd D = liftedStripBoundary hG.1 L 1) :
    ∃ g : Curve D, (∀ t, (g t).1 = (1, 2 * (1 + (t : ℝ)) * π)) ∧
      Function.Injective g ∧ range g ⊆ bd D ∧
      ∀ t, radialCylinderProjection (g t).1 = initialCuffGapCurve 1 0 t := by
  have hb (t : unitInterval) : (1, 2 * (1 + (t : ℝ)) * π) ∈ discBd D := by
    rw [hBd]
    apply Or.inl
    apply Or.inr
    refine ⟨mem_singleton 1, ?_⟩
    rw [(liftedLinkageCurve_props_raw hG.1 L 1).2.2.2.1,
      (liftedLinkageCurve_props_raw hG.1 L (1 + 1)).2.2.2.1]
    norm_num only [Int.cast_one, Int.cast_add, Nat.cast_one, div_one]
    constructor <;> nlinarith only [t.2.1, t.2.2, pi_pos]
  let g : Curve D :=
    ⟨fun t => ⟨(1, 2 * (1 + (t : ℝ)) * π), discBd_subset D (hb t)⟩, by fun_prop⟩
  refine ⟨g, fun _ => rfl, ?_, ?_, ?_⟩
  · intro s t h
    have he := congrArg (fun p : D => p.1.2) h
    apply Subtype.ext
    change 2 * (1 + (s : ℝ)) * π = 2 * (1 + (t : ℝ)) * π at he
    nlinarith only [he, pi_pos]
  · rintro _ ⟨t, rfl⟩
    obtain ⟨q, hq, heq⟩ := hb t
    exact (Subtype.ext heq : q = g t) ▸ hq
  · intro t
    apply Subtype.ext
    apply Prod.ext
    · change max 1 (min 2 (1 : ℝ)) = 1
      norm_num
    · change Circle.exp (2 * (1 + (t : ℝ)) * π) =
        Circle.exp (2 * (((0 + 1 : ℕ) : ℝ) + (t : ℝ)) * π / (1 : ℕ))
      norm_num

end GraphMinor.GM06
