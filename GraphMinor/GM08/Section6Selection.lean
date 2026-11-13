module

public import GraphMinor.Surface.DiscGrow
import GraphMinor.Surface.Cuffs
import GraphMinor.GM08.Section6Components
import GraphMinor.GM08.Section6Excursions
import GraphMinor.GM08.Section6Parameters
import GraphMinor.GM08.Section6Chord
import GraphMinor.GM08.Section6ExcursionArcs
import GraphMinor.GM08.Section6Plane

/-!
# Selecting maximal excursion enlargements

For VIII (6.2), page 264, a disc containing one excursion enlargement
must contain its removed interval on the old boundary. The two endpoints
of that interval belong to the excursion closure. The null-family bound
therefore makes each container set finite and gives maximal enlargements.
-/

public section

namespace GraphMinor.GM08

open Set Topology Metric Surface

local notation "𝕀" => unitInterval

private theorem plane_point (x : ℂ) : IsManifoldPoint x := by
  obtain ⟨e⟩ := exists_homeomorph_ball x one_pos
  exact (show IsInteriorPoint x from
    ⟨ball x 1, isOpen_ball, mem_ball_self one_pos, ⟨e⟩⟩).isManifoldPoint

/-- Excursion enlargements with their removed parameter intervals have
finite container sets and maximal members. The size bound follows from
their endpoints in the corresponding excursion closures. -/
theorem excursion_enlargements_have_finite_containers_and_maxima
    {F D : Set ℂ} (hF : IsOArc F) {f : 𝕀 → ℂ} (hf : IsArcMap f)
    (R : {J : Set ℂ // J ∈ componentsIn (F \ D)} → Set ℂ)
    (s t : {J : Set ℂ // J ∈ componentsIn (F \ D)} → 𝕀)
    (hR : ∀ J, IsClosedDisc (R J)) (hst : ∀ J, s J < t J)
    (hP : ∀ J, discInt (R J) ∩ discBd D = f '' Ioo (s J) (t J))
    (hs : ∀ J, f (s J) ∈ closure J.1) (ht : ∀ J, f (t J) ∈ closure J.1) :
    (∀ i, {j | R i ⊆ R j}.Finite) ∧
      ∀ i, ∃ j, R i ⊆ R j ∧ ∀ k, R j ⊆ R k → R k = R j := by
  have hfinite : ∀ ε > 0, {J | ε ≤ (t J).1 - (s J).1}.Finite := fun ε hε =>
    finite_large_parameter_spans_of_excursion_endpoints hF D hf s t hs ht hε
  have hmono : ∀ i j, R i ⊆ R j →
      Ioo (s i).1 (t i).1 ⊆ Ioo (s j).1 (t j).1 := fun i j hij =>
    removed_parameter_intervals_mono plane_point (hR i) hij hf (hP i) (hP j)
  exact ⟨fun i => finite_containers_of_interval_witnesses R
      (fun J => (s J).1) (fun J => (t J).1) hst hfinite hmono i,
    fun i => exists_maximal_region_of_interval_witnesses R
      (fun J => (s J).1) (fun J => (t J).1) hst hfinite hmono i⟩

/-- Actual excursion enlargements are nested or remove disjoint parts of
the old boundary. Thus distinct maximal enlargements have disjoint removed
intervals, as required in the gluing step of VIII (6.2). -/
theorem plane_excursion_enlargements_nested_or_removed_disjoint
    {F D : Set ℂ} (hD : IsClosedDisc D)
    (R : {J : Set ℂ // J ∈ componentsIn (F \ D)} → Set ℂ)
    (ℓ a b : {J : Set ℂ // J ∈ componentsIn (F \ D)} → 𝕀 → ℂ)
    (hR : ∀ J, IsClosedDisc (R J)) (hDR : ∀ J, D ⊆ R J)
    (hRu : ∀ J, R J ⊆ closedBall 0 1)
    (hℓ : ∀ J, IsArcMap (ℓ J)) (hℓo : ∀ J, ℓ J '' Ioo (0 : 𝕀) 1 = J.1)
    (hab : ∀ J, IsTwoArcs (a J) (b J))
    (ha0 : ∀ J, a J 0 = ℓ J 0) (ha1 : ∀ J, a J 1 = ℓ J 1)
    (har : ∀ J, range (a J) ∪ range (b J) = discBd D)
    (hRb : ∀ J, discBd (R J) = range (a J) ∪ range (ℓ J)) :
    ∀ i j, R i ⊆ R j ∨ R j ⊆ R i ∨
      Disjoint (discBd D ∩ discInt (R i)) (discBd D ∩ discInt (R j)) := by
  have haD : ∀ J, range (a J) ⊆ D := fun J =>
    (har J ▸ subset_union_left).trans (discBd_subset D)
  have hℓ0 : ∀ J, ℓ J 0 ∈ D := fun J => ha0 J ▸ haD J ⟨0, rfl⟩
  have hℓ1 : ∀ J, ℓ J 1 ∈ D := fun J => ha1 J ▸ haD J ⟨1, rfl⟩
  have houtside : ∀ J r, r ∈ Ioo (0 : 𝕀) 1 → ℓ J r ∉ D := by
    intro J r hr
    have hxJ : ℓ J r ∈ J.1 := hℓo J ▸ ⟨r, hr, rfl⟩
    rcases J.2 with ⟨x, hx, he⟩
    rw [← he] at hxJ
    exact (connectedComponentIn_subset (F \ D) x hxJ).2
  have hmeet : ∀ J r, ℓ J r ∈ D → r = 0 ∨ r = 1 := by
    intro J r hrD
    by_cases hr0 : r = 0
    · exact Or.inl hr0
    by_cases hr1 : r = 1
    · exact Or.inr hr1
    exact False.elim (houtside J r
      ⟨lt_of_le_of_ne (unitInterval.nonneg r) (Ne.symm hr0),
        lt_of_le_of_ne (unitInterval.le_one r) hr1⟩ hrD)
  have hbdsub : ∀ J, discBd (R J) ⊆ D ∪ range (ℓ J) := by
    intro J
    rw [hRb J]
    exact union_subset_union (haD J) subset_rfl
  have hz : (2 : ℂ) ∉ closedBall 0 1 := by norm_num [mem_closedBall, dist_eq_norm]
  intro i j
  by_cases hij : i = j
  · subst j
    exact Or.inl subset_rfl
  have hji : j.1 ≠ i.1 := fun he => hij (Subtype.ext he.symm)
  have hdis := open_excursion_disjoint_complete_other j.2 i.2 hji
    (hℓo j) (hℓo i) (hℓ0 i) (hℓ1 i)
  exact chord_discs_nested_or_removed_arcs_disjoint plane_point hD (hR i) (hR j)
    (hDR i) (hDR j) (hab i).1.isLineWithEnds
    (old_new_boundary_inter_eq_kept_arc (har i) (hRb i) (ha0 i) (ha1 i) (hmeet i))
    (plane_disc_boundary_subset_closure_compl hD) (hbdsub i) (hbdsub j)
    (hℓ j) (hℓ0 j) (hℓ1 j) (houtside j) hdis (plane_disc_complement_preconnected (hR i))
    (fun h => hz (hRu i h)) (fun h => hz (hRu j h))

end GraphMinor.GM08
