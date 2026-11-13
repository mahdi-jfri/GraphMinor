module

public import GraphMinor.GM06.Section5CoverSides

/-!
# The one-turn counterexample is excluded by clockwise incidence

Take the one-path linkage along angle zero and the extra edge that
winds once positively while its radius increases from 1 to 2. In the
preceding cover component, every angle lies strictly between 0 and 2π.
The lift of that extra edge in this component approaches angle zero
at radius 1, rather than the chosen initial lift at angle 2π. Hence
it cannot satisfy the corrected Reduction 1 condition.
-/

public section
namespace GraphMinor.GM06
open Set Topology Real GraphMinor.Surface

/-- The cover strip of the radial one-path linkage has its angles
strictly between zero and one full turn. -/
theorem angle_bounds_cylinderCoverStrip_radial
    {G : Drawing ClosedCylinder} (L : CylinderLinkage 1 G)
    (hP : (⋃ j, (L.pathDrawing j).U) = {x | x.1.2 = 1})
    {p : CylinderCover} (hp : p ∈ cylinderCoverStrip L 0) :
    0 < p.2 ∧ p.2 < 2 * π := by
  let C := cylinderCoverStrip L 0
  have hoff {q : CylinderCover} (hq : q ∈ C) : Circle.exp q.2 ≠ 1 := by
    have h := (connectedComponentIn_subset _ _ hq).2
    rw [hP] at h
    exact h
  have hpi : Circle.exp π ≠ 1 := by
    intro h
    have he := Circle.exp_injOn_Ico (a := 0) (b := 2 * π) (by linarith only [pi_pos])
      (show π ∈ Ico (0 : ℝ) (2 * π) from ⟨pi_pos.le, by linarith only [pi_pos]⟩)
      (show (0 : ℝ) ∈ Ico (0 : ℝ) (2 * π) from ⟨le_rfl, by linarith only [pi_pos]⟩)
      (by simpa only [Circle.exp_zero] using h)
    exact pi_ne_zero he
  have hb : (⟨1, by norm_num⟩, π) ∈ C := by
    dsimp only [C, cylinderCoverStrip]
    norm_num only [Int.cast_zero, zero_mul, zero_add, one_mul, Nat.cast_one, div_one]
    apply mem_connectedComponentIn
    refine ⟨mem_univ _, ?_⟩
    rw [hP]
    exact hpi
  have hc : IsPreconnected (Prod.snd '' C) :=
    isPreconnected_connectedComponentIn.image Prod.snd continuous_snd.continuousOn
  have hp' : p.2 ∈ Prod.snd '' C := mem_image_of_mem _ hp
  have hb' : π ∈ Prod.snd '' C := ⟨_, hb, rfl⟩
  constructor
  · by_contra hn
    obtain ⟨q, hq, hq0⟩ := hc.ordConnected.out hp' hb'
      (show (0 : ℝ) ∈ Icc p.2 π from ⟨le_of_not_gt hn, pi_pos.le⟩)
    exact hoff hq (hq0 ▸ Circle.exp_zero)
  · by_contra hn
    obtain ⟨q, hq, hq2⟩ := hc.ordConnected.out hb' hp'
      (show 2 * π ∈ Icc π p.2 from ⟨by linarith only [pi_pos], le_of_not_gt hn⟩)
    exact hoff hq (hq2 ▸ Circle.exp_two_pi)

/-- The positive one-turn edge in the counterexample to the printed
Reduction 1 is not a clockwise initial edge for the radial linkage.
The displayed equation describes the actual edge, with its ends omitted. -/
theorem not_isClockwiseInitialEdge_positive_turn
    {G : Drawing ClosedCylinder} (L : CylinderLinkage 1 G)
    (hP : (⋃ j, (L.pathDrawing j).U) = {x | x.1.2 = 1})
    {e : Set ClosedCylinder}
    (he : e = {x | 1 < x.1.1 ∧ x.1.1 < 2 ∧
      x.1.2 = Circle.exp (2 * π * (x.1.1 - 1))}) :
    ¬ IsClockwiseInitialEdge L 0 e := by
  rintro ⟨A, _, hA, hs, hsub⟩
  let T : Set CylinderCover := {p | p.2 = 2 * π * (p.1.1 - 1)}
  have hT : IsClosed T := isClosed_eq continuous_snd
    (continuous_const.mul ((continuous_subtype_val.comp continuous_fst).sub continuous_const))
  have hAT : A ⊆ T := by
    intro p hp
    have hpE : cylinderCoverProjection p ∈ e := hA ▸ mem_image_of_mem _ hp
    rw [he] at hpE
    have hb := angle_bounds_cylinderCoverStrip_radial L hP (hsub hp)
    change 1 < p.1.1 ∧ p.1.1 < 2 ∧
      Circle.exp p.2 = Circle.exp (2 * π * (p.1.1 - 1)) at hpE
    have ht : 0 < 2 * π * (p.1.1 - 1) ∧ 2 * π * (p.1.1 - 1) < 2 * π := by
      constructor <;> nlinarith only [pi_pos, hpE.1, hpE.2.1]
    exact Circle.exp_injOn_Ico (a := 0) (b := 2 * π) (by linarith only [pi_pos])
      ⟨hb.1.le, hb.2⟩ ⟨ht.1.le, ht.2⟩ hpE.2.2
  have hbad := (closure_minimal hAT hT) hs
  norm_num [T, cylinderInitialLift] at hbad

/-- The positive-turn edge cannot be deleted by the corrected Reduction 1.
This applies to any target drawing omitting that edge, so in particular
it rules out the deletion in the recorded counterexample to (5.5). -/
theorem not_section5Reduction1Step_positive_turn
    {G G' : Drawing ClosedCylinder} (L : CylinderLinkage 1 G)
    (L' : CylinderLinkage 1 G')
    (hP : (⋃ j, (L.pathDrawing j).U) = {x | x.1.2 = 1})
    {e : Set ClosedCylinder} (heG : e ∈ G.E) (heNew : e ∉ G'.E)
    (he : e = {x | 1 < x.1.1 ∧ x.1.1 < 2 ∧
      x.1.2 = Circle.exp (2 * π * (x.1.1 - 1))}) :
    ¬ Section5Reduction1Step 1 G L G' L' := by
  rintro ⟨i, d, hd, hside, _, hE, _⟩
  have hed : e = d := by
    by_contra hne
    apply heNew
    rw [hE]
    exact ⟨heG, by simpa only [mem_singleton_iff] using hne⟩
  have hi : i = 0 := Subsingleton.elim _ _
  rw [hi, ← hed] at hside
  exact not_isClockwiseInitialEdge_positive_turn L hP he hside

end GraphMinor.GM06
