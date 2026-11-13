module

public import GraphMinor.GM06.Defs
import GraphMinor.GM06.Section5ContractionCurveLift
import GraphMinor.GM06.Section5Red

/-!
# Helices avoiding the exceptional value of a contraction

For Reduction 3 in VI (5.5), page 130, a helix missing the contracted
vertex pulls back with exactly the same vertex hits. The boundary-fixed
contraction homotopy preserves its winding, so its potential is unchanged.
-/

public section
namespace GraphMinor.GM06
open Set GraphMinor.Surface

/-- The part of the contraction case of VI (5.5) in which the helix
avoids the exceptional value. All data refer to the actual contraction. -/
theorem exists_helix_lift_avoiding_contraction
    {k : ℕ} {G G' : Drawing ClosedCylinder}
    (π : C(ClosedCylinder, ClosedCylinder)) (s : ClosedCylinder)
    (H : C(unitInterval × ClosedCylinder, ClosedCylinder))
    (hH0 : ∀ p, H (0, p) = p) (hH1 : ∀ p, H (1, p) = π p)
    (hHbd : ∀ p ∈ bd ClosedCylinder, ∀ t, H (t, p) = p)
    (hinj : ∀ x y, π x ≠ s → π y ≠ s → π x = π y → x = y)
    (hsurj : ∀ z, z ≠ s → ∃ x, π x = z)
    (hU : G'.U = π '' G.U) (hV : G'.V = π '' G.V)
    (f : Curve ClosedCylinder) (hf : IsHelix k G' f)
    (havoid : ∀ t, f t ≠ s) :
    ∃ g : Curve ClosedCylinder, IsHelix k G g ∧ curvePhi k G g = curvePhi k G' f := by
  obtain ⟨g, hg⟩ := exists_curve_lift_avoiding_contraction π s hinj hsurj f havoid
  have hfix (p) (hp : p ∈ bd ClosedCylinder) : π p = p :=
    (hH1 p).symm.trans (hHbd p hp 1)
  have hf0 : f 0 ∈ bd ClosedCylinder := by
    obtain ⟨i, hi⟩ := hf.2.1
    rw [← hi, bd_closedCylinder]
    exact Or.inl rfl
  have hf1 : f 1 ∈ bd ClosedCylinder := by
    obtain ⟨i, hi⟩ := hf.2.2.1
    rw [← hi, bd_closedCylinder]
    exact Or.inr rfl
  have he0 : g 0 = f 0 := hinj _ _ ((hg 0) ▸ havoid 0)
    (by rw [hfix _ hf0]; exact havoid 0) ((hg 0).trans (hfix _ hf0).symm)
  have he1 : g 1 = f 1 := hinj _ _ ((hg 1) ▸ havoid 1)
    (by rw [hfix _ hf1]; exact havoid 1) ((hg 1).trans (hfix _ hf1).symm)
  have hvertex (t) : g t ∈ G.V ↔ f t ∈ G'.V := by
    rw [hV]
    constructor
    · intro ht
      exact ⟨g t, ht, hg t⟩
    · rintro ⟨x, hx, hxf⟩
      have he : g t = x := hinj _ _ ((hg t) ▸ havoid t)
        (hxf ▸ havoid t) ((hg t).trans hxf.symm)
      exact he.symm ▸ hx
  have hnormal : IsNormalCurve G g := by
    rintro x ⟨⟨t, rfl⟩, ht⟩
    apply (hvertex t).2
    apply hf.1
    exact ⟨mem_range_self t, hU ▸ ⟨g t, ht, hg t⟩⟩
  have hhits : curveVertexHits G g = curveVertexHits G' f := by
    ext t
    exact hvertex t
  have hhom := curvesHomotopic_comp_pi_map hH0 hH1 hHbd
    (he0 ▸ hf0) (he1 ▸ hf1)
  have hcomp : π.comp g = f := by
    apply ContinuousMap.ext
    intro t
    exact hg t
  have hwind : windingNumber g = windingNumber f := by
    rw [← hcomp]
    exact windingNumber_eq_of_homotopic hhom
  refine ⟨g, ⟨hnormal, he0 ▸ hf.2.1, he1 ▸ hf.2.2.1, hhits ▸ hf.2.2.2⟩, ?_⟩
  simp only [curvePhi, curveL, hwind, hhits]

/-- Reduction 3 of VI (5.5) when the helix misses every prescribed
initial vertex, and hence misses the vertex of this contraction. -/
theorem theorem_5_5_red3_of_avoids_initial_vertices
    {k : ℕ} {G G' : Drawing ClosedCylinder}
    (L : CylinderLinkage k G) (L' : CylinderLinkage k G')
    (hRed : Section5Reduction3Step k G L G' L')
    (f : Curve ClosedCylinder) (hf : IsHelix k G' f)
    (havoid : ∀ i : Fin k, ∀ t, f t ≠ cylinderM1Point k i) :
    ∃ g : Curve ClosedCylinder, IsHelix k G g ∧ curvePhi k G g ≤ curvePhi k G' f := by
  rcases hRed with ⟨i, e, v, π, H, _, _, _, _, _, _,
    hH0, hH1, hHbd, hfibre, _, hinj, hsurj, _, hU, hV, _, _, _⟩
  have hoff (x : ClosedCylinder) (hx : π x ≠ cylinderM1Point k i) :
      x ∉ closure e := by
    rw [← hfibre]
    exact hx
  have hi : ∀ x y, π x ≠ cylinderM1Point k i →
      π y ≠ cylinderM1Point k i → π x = π y → x = y := by
    intro x y hx hy hxy
    exact hinj x (hoff x hx) y (hoff y hy) hxy
  have hs : ∀ z, z ≠ cylinderM1Point k i → ∃ x, π x = z := by
    intro z hz
    obtain ⟨x, _, hx⟩ := hsurj z hz
    exact ⟨x, hx⟩
  obtain ⟨g, hg, hφ⟩ := exists_helix_lift_avoiding_contraction π
    (cylinderM1Point k i) H hH0 hH1 hHbd hi hs hU hV f hf (havoid i)
  exact ⟨g, hg, hφ.le⟩

end GraphMinor.GM06
