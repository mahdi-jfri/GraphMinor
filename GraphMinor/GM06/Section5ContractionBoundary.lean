module

public import GraphMinor.GM06.Defs
import GraphMinor.GM06.Section5Red

/-!
# Boundary conditions after contracting an initial edge

For Reduction 3 of VI, page 129, the collapse fixes the boundary.
Outside its single collapsed fiber it is injective, so no other
interior point can acquire a boundary image. The image drawing is
therefore proper and has the same boundary vertices.
-/

public section
namespace GraphMinor.GM06
open Set GraphMinor.Surface

/-- A boundary-fixing collapse of an initial edge preserves the
standing drawing assumptions of Section 5. -/
theorem isCylinderSection5Drawing_of_initial_edge_collapse
    {k : ℕ} {G G' : Drawing ClosedCylinder} {i : Fin k}
    (hG : IsCylinderSection5Drawing k G)
    {a : Set ClosedCylinder} {v : ClosedCylinder}
    (hl : G.toGraph.IsLink a (cylinderM1Point k i) v)
    (π : C(ClosedCylinder, ClosedCylinder))
    (hfiber : π ⁻¹' {cylinderM1Point k i} = closure a)
    (hi : InjOn π (closure a)ᶜ)
    (hbd : ∀ x ∈ bd ClosedCylinder, π x = x)
    (hU : G'.U = π '' G.U) (hV : G'.V = π '' G.V) :
    IsCylinderSection5Drawing k G' := by
  have hπcl : ∀ x ∈ closure a, π x = cylinderM1Point k i := by
    intro x hx
    have hxpre : x ∈ π ⁻¹' {cylinderM1Point k i} := by rw [hfiber]; exact hx
    exact hxpre
  have hpoint : ∀ y ∈ G'.U ∩ bd ClosedCylinder, y ∈ G.V := by
    rintro y ⟨hyU, hybd⟩
    by_cases hys : y = cylinderM1Point k i
    · exact hys.symm ▸ hl.2.1
    · rw [hU] at hyU
      obtain ⟨x, hxG, hxy⟩ := hyU
      have hxnot : x ∉ closure a := fun hx => hys (hxy.symm.trans (hπcl x hx))
      have hynot : y ∉ closure a := fun hy => hys ((hbd y hybd).symm.trans (hπcl y hy))
      have hxeq : x = y := hi hxnot hynot (hxy.trans (hbd y hybd).symm)
      exact hG.2.1 ⟨hybd, hxeq ▸ hxG⟩
  refine ⟨hG.1, ?_, ?_⟩
  · intro y hy
    rw [hV]
    exact ⟨y, hpoint y ⟨hy.2, hy.1⟩, hbd y hy.1⟩
  · apply subset_antisymm
    · rintro y ⟨hyV, hybd⟩
      rw [← hG.2.2]
      exact ⟨hpoint y ⟨G'.V_subset_U hyV, hybd⟩, hybd⟩
    · intro y hy
      rw [← hG.2.2] at hy
      refine ⟨?_, hy.2⟩
      rw [hV]
      exact ⟨y, hy.1, hbd y hy.2⟩

end GraphMinor.GM06
