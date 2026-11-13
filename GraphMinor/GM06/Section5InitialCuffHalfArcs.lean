module

public import GraphMinor.GM06.Section5
public import GraphMinor.Surface.DiscGrow

/-!
# The two angular halves of the initial cuff

For the side test in VI (5.7), page 133, split the initial cuff
at its initial point and the opposite circle point. One half runs
towards decreasing angle and the other towards increasing angle.
The circle's two-arc parametrizations give injectivity, the exact
common ends, and coverage of the cuff, also when it has one vertex.
-/

public section
namespace GraphMinor.GM06
open Set Topology Real GraphMinor.Surface unitInterval

/-- The initial cuff has two arcs with explicit decreasing and
increasing angular parametrizations from any chosen initial angle. -/
theorem exists_initial_cuff_half_arcs (θ : ℝ) :
    ∃ g h : I → ClosedCylinder, IsTwoArcs g h ∧
      g 0 = cylinderPoint 1 (by norm_num) θ ∧ range g ∪ range h = cylinderCuff1 ∧
      (∀ t : I, g t = cylinderPoint 1 (by norm_num) (θ - π * (t : ℝ))) ∧
      ∀ t : I, h t = cylinderPoint 1 (by norm_num) (θ + π * (t : ℝ)) := by
  let j : Circle → ClosedCylinder := fun w => ⟨(1, w), by norm_num, trivial⟩
  have hjc : Continuous j := by fun_prop
  have hji : Function.Injective j := by
    intro w z hwz
    exact congrArg (fun p : ClosedCylinder => p.1.2) hwz
  obtain ⟨a, b, hab, ha, hb, hcover⟩ := circle_two_arcs' (Circle.exp θ)
    (θ := π) ⟨pi_pos, by linarith only [pi_pos]⟩
  let g : I → ClosedCylinder := j ∘ b
  let h : I → ClosedCylinder := j ∘ a
  have hgh : IsTwoArcs g h := by
    refine ⟨⟨hjc.comp hab.arc_right.1, hji.comp hab.arc_right.2⟩,
      ⟨hjc.comp hab.arc_left.1, hji.comp hab.arc_left.2⟩,
      congrArg j hab.zero.symm, congrArg j hab.one.symm, ?_⟩
    intro r s hrs
    rcases hab.meet s r (hji hrs).symm with h0 | h1
    · exact Or.inl ⟨h0.2, h0.1⟩
    · exact Or.inr ⟨h1.2, h1.1⟩
  have hg (t : I) : g t = cylinderPoint 1 (by norm_num) (θ - π * (t : ℝ)) := by
    change j (b t) = _
    rw [hb]
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · change Circle.exp θ * Circle.exp (2 * π - (t : ℝ) * (2 * π - π)) =
        Circle.exp (θ - π * (t : ℝ))
      rw [← Circle.exp_add]
      have hh : θ + (2 * π - (t : ℝ) * (2 * π - π)) = (θ - π * (t : ℝ)) + 2 * π := by ring
      rw [hh, Circle.exp_add, Circle.exp_two_pi, mul_one]
  have hh (t : I) : h t = cylinderPoint 1 (by norm_num) (θ + π * (t : ℝ)) := by
    change j (a t) = _
    rw [ha]
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · change Circle.exp θ * Circle.exp ((t : ℝ) * π) = Circle.exp (θ + π * (t : ℝ))
      rw [← Circle.exp_add]
      congr 1
      ring
  have hjrange : range j = cylinderCuff1 := by
    ext p
    constructor
    · rintro ⟨w, rfl⟩
      rfl
    · intro hp
      refine ⟨p.1.2, ?_⟩
      apply Subtype.ext
      exact Prod.ext hp.symm rfl
  have hghcover : range g ∪ range h = cylinderCuff1 := by
    calc
      range g ∪ range h = j '' (range b ∪ range a) := by
        rw [image_union, ← range_comp, ← range_comp]
      _ = j '' univ := by rw [union_comm, hcover]
      _ = cylinderCuff1 := by rw [image_univ, hjrange]
  refine ⟨g, h, hgh, ?_, hghcover, hg, hh⟩
  rw [hg]
  simp only [Icc.coe_zero, mul_zero, sub_zero]

end GraphMinor.GM06
