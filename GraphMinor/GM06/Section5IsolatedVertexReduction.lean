module

public import GraphMinor.GM06.Defs
import GraphMinor.GM06.Section5FinitePointAvoidance
import GraphMinor.GM06.Section5SeparationGeometry
import GraphMinor.GM06.Section4
import GraphMinor.GM11.Walks

/-!
# Reduction 2 when the discarded side has no edges

For VI (5.5), page 130, the isolated discarded vertices lie off
the retained drawing and the cuffs. Finite-point avoidance supplies
a retained helix missing all of them. It is then normal in the old
drawing and has exactly the same vertex times and potential there.
-/

public section
namespace GraphMinor.GM06
open Set GraphMinor.Surface

/-- The edgeless discarded-side case of VI (5.5), Reduction 2.
The finite-point detours are constructed from the actual separation. -/
theorem theorem_5_5_red2_of_discarded_edgeless
    {k : ℕ} {G G₁ G₂ : Drawing ClosedCylinder}
    (hG : IsCylinderSection5Drawing k G) (hG₁ : IsCylinderSection5Drawing k G₁)
    (hsep : IsGraphSeparation G.toGraph G₁.toGraph G₂.toGraph)
    (hE : G₂.E = ∅) (f : Curve ClosedCylinder) (hf : IsHelix k G₁ f) :
    ∃ g : Curve ClosedCylinder, IsHelix k G g ∧ curvePhi k G g ≤ curvePhi k G₁ f := by
  let A := G₂.V \ G₁.V
  have h₂ : G₂.IsSubdrawing G := ⟨hsep.2.1.vertexSet_mono, hsep.2.1.edgeSet_mono⟩
  have h₁ : G₁.IsSubdrawing G := ⟨hsep.1.vertexSet_mono, hsep.1.edgeSet_mono⟩
  have hAU : Disjoint A G₁.U := by
    apply disjoint_left.mpr
    rintro x ⟨hx₂, hxn⟩ hx₁
    exact hxn (vertex_mem_of_mem_subdrawing_point_set h₁ hx₁ (h₂.1 hx₂))
  have hAb : Disjoint A (bd ClosedCylinder) := by
    apply disjoint_left.mpr
    rintro x ⟨hx₂, hxn⟩ hxb
    have hxM : x ∈ cylinderM1 k ∪ cylinderM2 k := hG.2.2 ▸ ⟨h₂.1 hx₂, hxb⟩
    exact hxn ((hG₁.2.2.symm ▸ hxM).1)
  obtain ⟨g, hg, hgA, hφ⟩ := exists_helix_avoiding_finite_points
    (G₂.finite_V.sdiff (t := G₁.V)) hAU hAb f hf
  have hU₂ : G₂.U = G₂.V := by
    rw [G₂.U_eq, hE]
    simp
  have hU := (point_sets_of_graph_separation hsep).1
  have hnormal : IsNormalCurve G g := by
    rintro x ⟨hxg, hx⟩
    rcases hU ▸ hx with hx₁ | hx₂
    · exact h₁.1 (hg.1 ⟨hxg, hx₁⟩)
    · rw [hU₂] at hx₂
      exact h₂.1 hx₂
  have hhits : curveVertexHits G g = curveVertexHits G₁ g := by
    ext t
    constructor
    · intro ht
      have hv : g t ∈ G₁.V ∪ G₂.V := by
        rw [show G₁.V ∪ G₂.V = G.V from hsep.2.2.1]
        exact ht
      rcases hv with ht₁ | ht₂
      · exact ht₁
      · by_contra ht₁
        exact disjoint_left.mp hgA (mem_range_self t) ⟨ht₂, ht₁⟩
    · exact fun ht => h₁.1 ht
  have hgOld : IsHelix k G g :=
    ⟨hnormal, hg.2.1, hg.2.2.1, hhits.symm ▸ hg.2.2.2⟩
  refine ⟨g, hgOld, ?_⟩
  have heq : curvePhi k G g = curvePhi k G₁ g := by simp only [curvePhi, curveL, hhits]
  exact heq.le.trans hφ

end GraphMinor.GM06
