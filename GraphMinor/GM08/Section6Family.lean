module

public import GraphMinor.Surface.DiscGrow
import GraphMinor.Surface.Cuffs
import GraphMinor.GM08.Section6Plane
import GraphMinor.GM08.Section6Chord
import GraphMinor.GM08.Section6Parameters

/-!
# The family of excursion enlargements and removed intervals

For VIII (6.2), page 264, this file chooses the enlargement for every
outside component, retains the common exterior arc, and parametrizes each
removed part on the complementary old boundary arc. The endpoint pairs
of the two parametrizations agree.
-/

public section

namespace GraphMinor.GM08

open Set Topology Metric Surface

local notation "𝕀" => unitInterval

private theorem plane_point (x : ℂ) : IsManifoldPoint x := by
  obtain ⟨e⟩ := exists_homeomorph_ball x one_pos
  exact (show IsInteriorPoint x from
    ⟨ball x 1, isOpen_ball, mem_ball_self one_pos, ⟨e⟩⟩).isManifoldPoint

/-- Choose all excursion enlargements together with their removed
parameter intervals on one common embedded old boundary arc. No
finiteness condition is imposed on the excursion index set. -/
theorem exists_plane_excursion_parameter_family {D F : Set ℂ} (hD : IsClosedDisc D)
    (hF : IsOArc F) (hinter : (discBd D ∩ F).Nontrivial)
    (hDu : D ⊆ closedBall 0 1) (hFu : F ⊆ closedBall 0 1)
    (hnot : ¬ D ⊆ closedInner F) :
    let I := {J : Set ℂ // J ∈ componentsIn (F \ D)}
    ∃ q f : 𝕀 → ℂ, ∃ p : ℂ,
      IsTwoArcs q f ∧ range q ∪ range f = discBd D ∧
      Disjoint (q '' Ioo (0 : 𝕀) 1) F ∧ p ∈ q '' Ioo (0 : 𝕀) 1 ∧
      p ∈ closure (connectedComponentIn ((D ∪ closedInner F)ᶜ) (2 : ℂ)) ∧
      ∃ (R : I → Set ℂ) (ℓ a b : I → 𝕀 → ℂ) (s t : I → 𝕀), ∀ J,
        IsArcMap (ℓ J) ∧ range (ℓ J) ⊆ F ∧ ℓ J '' Ioo (0 : 𝕀) 1 = J.1 ∧
        range (ℓ J) = closure J.1 ∧ IsClosedDisc (R J) ∧ D ⊆ R J ∧
        R J ⊆ closedBall 0 1 ∧ IsTwoArcs (a J) (b J) ∧
        a J 0 = ℓ J 0 ∧ a J 1 = ℓ J 1 ∧ range (a J) ∪ range (b J) = discBd D ∧
        discBd (R J) = range (a J) ∪ range (ℓ J) ∧ s J < t J ∧
        discInt (R J) ∩ discBd D = f '' Ioo (s J) (t J) ∧
        closure (discInt (R J) ∩ discBd D) = f '' Icc (s J) (t J) ∧
        ({f (s J), f (t J)} : Set ℂ) = {ℓ J 0, ℓ J 1} := by
  classical
  dsimp only
  let I := {J : Set ℂ // J ∈ componentsIn (F \ D)}
  obtain ⟨q, f, p, hqf, hqfr, hqF, hpq, hpcl, hcommon⟩ :=
    exists_common_retained_plane_arc hD hF hinter hDu hFu hnot
  have hinterD : (F ∩ D).Nontrivial := by
    obtain ⟨x, hx, y, hy, hxy⟩ := hinter
    exact ⟨x, ⟨hx.2, discBd_subset D hx.1⟩, y,
      ⟨hy.2, discBd_subset D hy.1⟩, hxy⟩
  choose ℓ R a b hℓ hℓF hℓo hℓr hR hDR hab ha0 ha1 har hRb using
    fun J : I => exists_plane_excursion_enlargement hD hF hinterD J.2
  have haD : ∀ J, range (a J) ⊆ D := fun J =>
    (har J ▸ subset_union_left).trans (discBd_subset D)
  have hRu : ∀ J, R J ⊆ closedBall 0 1 := by
    intro J
    apply plane_disc_subset_unitBall_of_boundary_subset (hR J)
    rw [hRb J]
    exact union_subset ((haD J).trans hDu) ((hℓF J).trans hFu)
  have hmeet : ∀ J r, ℓ J r ∈ D → r = 0 ∨ r = 1 := by
    intro J r hrD
    by_cases hr0 : r = 0
    · exact Or.inl hr0
    by_cases hr1 : r = 1
    · exact Or.inr hr1
    have hr : r ∈ Ioo (0 : 𝕀) 1 :=
      ⟨lt_of_le_of_ne (unitInterval.nonneg r) (Ne.symm hr0),
        lt_of_le_of_ne (unitInterval.le_one r) hr1⟩
    have hrJ : ℓ J r ∈ J.1 := hℓo J ▸ ⟨r, hr, rfl⟩
    rcases J.2 with ⟨x, hx, he⟩
    rw [← he] at hrJ
    exact False.elim ((connectedComponentIn_subset (F \ D) x hrJ).2 hrD)
  have hqR : ∀ J, range q ⊆ discBd (R J) := fun J => hcommon (R J) (a J) (b J) (ℓ J)
    (hR J) (hDR J) (hRu J) (hab J) (har J) (hRb J) (hℓF J) (ha0 J) (ha1 J)
  choose s t hst hP hPcl using fun J => exists_parameters_for_removed_boundary_arc
    plane_point (hR J) (hDR J) hqf hqfr (hab J) (har J) (hRb J)
    (ha0 J) (ha1 J) (hmeet J) (hqR J)
  have hend : ∀ J, ({f (s J), f (t J)} : Set ℂ) = {ℓ J 0, ℓ J 1} := by
    intro J
    have hremoved := removed_arc_eq_old_boundary_inside (hDR J) (hab J) (har J)
      (hRb J) (ha0 J) (ha1 J) (hmeet J)
    have he := endpoints_eq_of_same_open_arc hqf.2 (hab J).2 (hst J)
      ((hP J).symm.trans hremoved)
    simpa only [(hab J).3, (hab J).4, ha0 J, ha1 J] using he
  refine ⟨q, f, p, hqf, hqfr, hqF, hpq, hpcl, R, ℓ, a, b, s, t, ?_⟩
  intro J
  exact ⟨hℓ J, hℓF J, hℓo J, hℓr J, hR J, hDR J, hRu J,
    hab J, ha0 J, ha1 J, har J, hRb J, hst J, hP J, hPcl J, hend J⟩

end GraphMinor.GM08
