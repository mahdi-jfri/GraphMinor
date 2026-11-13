module

public import GraphMinor.GM08.Section9RoundTame

/-!
# Ring replacement with finitely many protected points

The finite-crossing replacement for VIII (9.1) must preserve the enclosed
edges and must introduce no drawing vertices. Choose one point on each edge
and include the drawing vertices among the protected points. A thin annulus
around the old round ring misses every protected point off that ring.
Replacing the ring within this annulus then preserves the side of every
protected point off the ring.
-/

public section

namespace GraphMinor.GM08

open Set Surface Topology Complex Metric

local notation "𝕀" => unitInterval

/-- Around a given radius, a finite set of points admits an arbitrarily
thin annulus in which its only points have that radius. -/
theorem exists_annulus_avoiding_finite_points {Z : Set ℂ} (hZ : Z.Finite)
    {a r b : ℝ} (_ha : 0 ≤ a) (har : a < r) (hrb : r < b) :
    ∃ α β : ℝ, a < α ∧ α < r ∧ r < β ∧ β < b ∧
      ∀ z ∈ Z, α < ‖z‖ → ‖z‖ < β → ‖z‖ = r := by
  let B : Set ℝ := norm '' (Z \ sphere 0 r)
  have hB : B.Finite := (hZ.sdiff).image norm
  have hrB : r ∉ B := by
    rintro ⟨z, hz, heq⟩
    exact hz.2 (mem_sphere_zero_iff_norm.mpr heq)
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hB.isClosed.isOpen_compl r hrB
  let δ := min (ε / 2) (min ((r - a) / 2) ((b - r) / 2))
  have hδ : 0 < δ := lt_min (by linarith) (lt_min (by linarith) (by linarith))
  have hδε : δ < ε := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hδa : δ ≤ (r - a) / 2 := (min_le_right _ _).trans (min_le_left _ _)
  have hδb : δ ≤ (b - r) / 2 := (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨r - δ, r + δ, by linarith, by linarith, by linarith, by linarith, ?_⟩
  intro z hz hlow hupp
  by_contra hne
  have hzB : ‖z‖ ∈ B := ⟨z, ⟨hz, fun hs => hne (mem_sphere_zero_iff_norm.mp hs)⟩, rfl⟩
  have hclose : ‖z‖ ∈ ball r ε := by
    rw [mem_ball, Real.dist_eq, abs_lt]
    constructor <;> linarith
  exact hball hclose hzB

/-- A round ring has a finite-crossing replacement that preserves the side
of every protected point off the old ring, and passes through no protected
point not already on that ring. This is the pointwise control needed to
preserve enclosed drawing edges in the foundation step of VIII (9.1). -/
theorem exists_tame_round_ring_preserving_points
    (G : List (𝕀 → ℂ)) (hG : ∀ γ ∈ G, IsArcMap γ) {Z : Set ℂ} (hZ : Z.Finite)
    {a r b ρ : ℝ} (ha : 0 ≤ a) (har : a < r) (hrb : r < b) (hρ : 0 < ρ)
    (hfree : ∀ z ∈ ball (r : ℂ) ρ, ∀ γ ∈ G, z ∉ range γ) :
    ∃ P E : Set ℂ, IsOArc P ∧ FinConn (P \ ⋃ γ ∈ G, range γ) ∧
      P ⊆ sphere 0 r ∪ ⋃ γ ∈ G, range γ ∧ IsClosedDisc E ∧ discBd E = P ∧
      closedBall 0 a ⊆ E ∧ E ⊆ ball 0 b ∧
      P ∩ Z ⊆ sphere 0 r ∧
      ∀ z ∈ Z, ‖z‖ ≠ r → (z ∈ E ↔ ‖z‖ < r) := by
  obtain ⟨α, β, haα, hαr, hrβ, hβb, havoid⟩ :=
    exists_annulus_avoiding_finite_points hZ ha har hrb
  obtain ⟨P, E, hP, htame, hsub, hdis, hE, hbd, hin, hout⟩ :=
    exists_tame_round_ring G hG (le_trans ha haα.le) hαr
      (lt_of_le_of_lt ha har) hrβ hρ hfree
  have hPE : P ⊆ E := hbd ▸ discBd_subset E
  have hinside : ∀ z ∈ Z, ‖z‖ < r → z ∈ E := by
    intro z hz hzr
    apply hin
    apply mem_closedBall_zero_iff.mpr
    by_contra hnot
    have hαz : α < ‖z‖ := lt_of_not_ge hnot
    exact hzr.ne (havoid z hz hαz (lt_trans hzr hrβ))
  have houtside : ∀ z ∈ Z, r < ‖z‖ → z ∉ E := by
    intro z hz hzr hzE
    have hzβ : ‖z‖ < β := mem_ball_zero_iff.mp (hout hzE)
    have heq := havoid z hz (lt_trans hαr hzr) hzβ
    exact hzr.ne' heq
  refine ⟨P, E, hP, htame, hsub, hE, hbd,
    (closedBall_subset_closedBall haα.le).trans hin,
    hout.trans (ball_subset_ball hβb.le), ?_, ?_⟩
  · rintro z ⟨hzP, hzZ⟩
    apply mem_sphere_zero_iff_norm.mpr
    apply havoid z hzZ
    · by_contra hnot
      exact Set.disjoint_left.mp hdis hzP (mem_closedBall_zero_iff.mpr (le_of_not_gt hnot))
    · exact mem_ball_zero_iff.mp (hout (hPE hzP))
  · intro z hz hne
    constructor
    · intro hzE
      by_contra hnot
      exact houtside z hz (lt_of_le_of_ne (le_of_not_gt hnot) (Ne.symm hne)) hzE
    · exact hinside z hz

end GraphMinor.GM08
