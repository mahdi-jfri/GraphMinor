module

public import GraphMinor.GM06.Defs
import GraphMinor.GM06.Section5HelixDiscDetour
import GraphMinor.GM06.Section4
import GraphMinor.Surface.DiscMerge
import GraphMinor.Surface.PlaneDisc

/-!
# Avoiding finitely many discarded vertices

The isolated-vertex part of Reduction 2 in VI (5.5), page 130,
needs a helix missing a finite set off the retained drawing and the
cuffs. Put each point inside a small disc disjoint from that drawing,
the cuffs, and the points already avoided. The disc detour preserves
potential, and its range bound keeps the earlier avoidance intact.
-/

public section
namespace GraphMinor.GM06
open Set Topology Metric GraphMinor.Surface

private theorem exists_small_disc_in_open
    {a : ClosedCylinder} (ha : IsInteriorPoint a)
    {W : Set ClosedCylinder} (hW : IsOpen W) (haW : a ∈ W) :
    ∃ D : Set ClosedCylinder, IsClosedDisc D ∧ a ∈ discInt D ∧ D ⊆ W := by
  obtain ⟨U, h, j, c, hUW, hj0⟩ := ha.exists_ballChart hW haW (R := 2) (by norm_num)
  have hsub : closedBall (0 : ℂ) 1 ⊆ ball 0 2 := closedBall_subset_ball (by norm_num)
  obtain ⟨hD, hbd⟩ := c.image_disc isClosedDisc_closedBall.1 hsub
  refine ⟨j '' closedBall (0 : ℂ) 1, hD, ⟨?_, ?_⟩, ?_⟩
  · exact ⟨0, by simp, hj0⟩
  · rw [hbd, isClosedDisc_closedBall.2]
    rintro ⟨z, hz, he⟩
    have hz1 : ‖z‖ = 1 := mem_sphere_zero_iff_norm.mp hz
    have hz0 : z = 0 := c.hg.injOn
      (hsub (mem_closedBall_zero_iff.mpr hz1.le))
      (by simp) (he.trans hj0.symm)
    simp [hz0] at hz1
  · rintro _ ⟨z, hz, rfl⟩
    exact hUW (c.gm (hsub hz))

/-- A finite set away from the retained drawing and the cuffs can
be avoided by a helix with no greater potential. -/
theorem exists_helix_avoiding_finite_points
    {k : ℕ} {G : Drawing ClosedCylinder}
    {A : Set ClosedCylinder} (hA : A.Finite)
    (hAU : Disjoint A G.U) (hAb : Disjoint A (bd ClosedCylinder))
    (f : Curve ClosedCylinder) (hf : IsHelix k G f) :
    ∃ g : Curve ClosedCylinder, IsHelix k G g ∧ Disjoint (range g) A ∧
      curvePhi k G g ≤ curvePhi k G f := by
  classical
  induction A, hA using Set.Finite.induction_on generalizing f with
  | empty => exact ⟨f, hf, disjoint_empty _, le_rfl⟩
  | @insert a A ha hA ih =>
    have hAU' : Disjoint A G.U := hAU.mono_left (subset_insert _ _)
    have hAb' : Disjoint A (bd ClosedCylinder) := hAb.mono_left (subset_insert _ _)
    obtain ⟨g, hg, hgA, hφg⟩ := ih hAU' hAb' f hf
    have haU : a ∉ G.U := disjoint_left.mp hAU (Or.inl rfl)
    have hab : a ∉ bd ClosedCylinder := disjoint_left.mp hAb (Or.inl rfl)
    have haint : IsInteriorPoint a := by by_contra h; exact hab h
    let W : Set ClosedCylinder := (G.U ∪ bd ClosedCylinder ∪ A)ᶜ
    have hW : IsOpen W := (G.isClosed_U.union (isClosed_bd ClosedCylinder) |>.union hA.isClosed).isOpen_compl
    have haW : a ∈ W := by
      rintro ((h | h) | h)
      · exact haU h
      · exact hab h
      · exact ha h
    obtain ⟨D, hD, haD, hDW⟩ := exists_small_disc_in_open haint hW haW
    have hDU : Disjoint D G.U := disjoint_left.mpr (fun x hx hu => hDW hx (Or.inl (Or.inl hu)))
    have hDb : Disjoint D (bd ClosedCylinder) :=
      disjoint_left.mpr (fun x hx hb => hDW hx (Or.inl (Or.inr hb)))
    obtain ⟨u, hu, huD, hφu, hur⟩ := exists_helix_avoiding_disc g hg hD hDU hDb
    refine ⟨u, hu, ?_, hφu.trans hφg⟩
    apply disjoint_left.mpr
    intro x hxu hxA
    rcases hxA with rfl | hxA
    · exact disjoint_left.mp huD hxu haD
    · rcases hur hxu with hxg | hxD
      · exact disjoint_left.mp hgA hxg hxA
      · exact hDW hxD (Or.inr hxA)

end GraphMinor.GM06
