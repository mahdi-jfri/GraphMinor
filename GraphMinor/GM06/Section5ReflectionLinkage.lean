module

public import GraphMinor.GM06.Section5ReflectionDrawing
import GraphMinor.GM06.Section5ReflectionBoundary
import GraphMinor.GM06.Section5PathImage
import GraphMinor.GM11.Walks

/-!
# Reflecting linkages and feasible winding numbers

For the orientation reversal in VI (5.10), page 134, reflect each
path and its curve, and relabel by the induced involution of the
initial cuff vertices. Exact image vertices and edges preserve the
path property and disjointness. Every curve winding changes sign,
so feasibility is reversed from theta to minus theta.
-/

public section
namespace GraphMinor.GM06
open Set Topology GraphMinor.Surface

/-- Reflect every linkage path and relabel its prescribed initial vertex. -/
noncomputable def section5ReflectedLinkage {k : ℕ} {G : Drawing ClosedCylinder}
    (hk : 0 < k) (L : CylinderLinkage k G) : CylinderLinkage k (section5ReflectedDrawing k G) where
  pathDrawing i := section5ReflectedDrawing k (L.pathDrawing (section5ReflectionIndex hk i))
  curve i := section5ReflectedCurve k (L.curve (section5ReflectionIndex hk i))
  isSubdrawing i := by
    refine ⟨section5ReflectedDrawing_isSubdrawing (L.isSubdrawing _).1, ?_⟩
    rw [section5ReflectedDrawing_U, section5ReflectedDrawing_U]
    exact image_mono (L.isSubdrawing _).2
  isPath i := by
    let π : C(ClosedCylinder, ClosedCylinder) := ⟨section5CylinderReflection k, (section5CylinderReflection k).continuous⟩
    have hh := isPathDrawing_image_of_injOn_pointSet (L.isPath (section5ReflectionIndex hk i)) π
      (section5CylinderReflection k).injective.injOn
      (section5ReflectedDrawing_U k _) (section5ReflectedDrawing_V k _) (section5ReflectedDrawing_E k _)
    change IsPathDrawing _ (section5CylinderReflection k (cylinderM1Point k (section5ReflectionIndex hk i))) _ at hh
    rw [section5CylinderReflection_M1 hk, section5ReflectionIndex_involutive hk] at hh
    exact hh
  curve_parametrizes i := by
    refine ⟨(section5CylinderReflection k).injective.comp (L.curve_parametrizes _).1, ?_, ?_, rfl⟩
    · rw [section5ReflectedDrawing_U, ← (L.curve_parametrizes (section5ReflectionIndex hk i)).2.1,
        ← range_comp]
      rfl
    · change section5CylinderReflection k (L.curve (section5ReflectionIndex hk i) 0) = _
      rw [(L.curve_parametrizes _).2.2.1, section5CylinderReflection_M1 hk,
        section5ReflectionIndex_involutive hk]
  curve_one_mem i := by
    obtain ⟨j, hj⟩ := L.curve_one_mem (section5ReflectionIndex hk i)
    exact ⟨section5ReflectionIndex hk j, (section5CylinderReflection_M2 hk j).symm.trans
      (congrArg (section5CylinderReflection k) hj)⟩
  pairwise_disjoint := by
    intro i j hij
    have hσ : section5ReflectionIndex hk i ≠ section5ReflectionIndex hk j :=
      (section5ReflectionIndex_involutive hk).injective.ne hij
    rw [section5ReflectedDrawing_U, section5ReflectedDrawing_U]
    apply disjoint_left.mpr
    rintro x ⟨a, ha, rfl⟩ ⟨b, hb, he⟩
    have hba : b = a := (section5CylinderReflection k).injective he
    exact disjoint_left.mp (L.pairwise_disjoint hσ) ha (hba ▸ hb)

/-- The reflected linkage has the negative of the old winding. -/
theorem hasTheta_section5ReflectedLinkage
    {k : ℕ} {G : Drawing ClosedCylinder} (hk : 0 < k) (L : CylinderLinkage k G)
    {θ : ℝ} (hθ : L.HasTheta θ) : (section5ReflectedLinkage hk L).HasTheta (-θ) := by
  intro i
  change windingNumber (section5ReflectedCurve k (L.curve (section5ReflectionIndex hk i))) = -θ
  rw [windingNumber_section5ReflectedCurve, hθ]

/-- Reflection carries every feasible winding to its negative. -/
theorem isThetaFeasible_reflected_of_feasible
    {k : ℕ} {G : Drawing ClosedCylinder} (hk : 0 < k) {θ : ℝ}
    (hθ : IsThetaFeasible k G θ) : IsThetaFeasible k (section5ReflectedDrawing k G) (-θ) := by
  obtain ⟨L, hL⟩ := hθ
  exact ⟨section5ReflectedLinkage hk L, hasTheta_section5ReflectedLinkage hk L hL⟩

/-- Feasibility is equivalent to feasibility of the negative winding
in the drawing with reversed plane orientation. -/
theorem isThetaFeasible_reflected_iff
    {k : ℕ} {G : Drawing ClosedCylinder} (hk : 0 < k) (θ : ℝ) :
    IsThetaFeasible k (section5ReflectedDrawing k G) (-θ) ↔ IsThetaFeasible k G θ := by
  refine ⟨?_, isThetaFeasible_reflected_of_feasible hk⟩
  intro hh
  have hback := isThetaFeasible_reflected_of_feasible hk hh
  rwa [section5ReflectedDrawing_involutive, neg_neg] at hback

end GraphMinor.GM06
