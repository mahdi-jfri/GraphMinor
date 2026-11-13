module

public import GraphMinor.Surface.DiscGrow
import GraphMinor.Surface.Cuffs
import GraphMinor.GM08.Section6Maximal
import GraphMinor.GM08.Section6ArcGluing
import GraphMinor.GM08.Section6Plane
import GraphMinor.GM08.Section6PlaneSide
import GraphMinor.GM08.Section6Chord

/-!
# Covering two plane curves by their outer boundary

This is the plane construction for VIII (6.2), page 264, with both curves
in the unit ball. The maximal outside excursions replace disjoint intervals
of the first boundary. Their null images give an embedded complementary
arc. The retained arc fixes the common exterior and hence enclosure of the
old disc. Every maximal enlargement is then enclosed, so the second curve
is enclosed as well.
-/

public section

namespace GraphMinor.GM08

open Set Topology Metric Surface

local notation "𝕀" => unitInterval

private theorem plane_point (x : ℂ) : IsManifoldPoint x := by
  obtain ⟨e⟩ := exists_homeomorph_ball x one_pos
  exact (show IsInteriorPoint x from
    ⟨ball x 1, isOpen_ball, mem_ball_self one_pos, ⟨e⟩⟩).isManifoldPoint

/-- The unrestricted plane covering step for VIII (6.2), for curves in the
unit ball. There is no finiteness hypothesis on their crossings. -/
theorem exists_plane_disc_cover_unit {D F : Set ℂ} (hD : IsClosedDisc D)
    (hF : IsOArc F) (hinter : (discBd D ∩ F).Nontrivial)
    (hDu : D ⊆ closedBall 0 1) (hFu : F ⊆ closedBall 0 1) :
    ∃ E : Set ℂ, IsClosedDisc E ∧ D ⊆ E ∧ F ⊆ E ∧
      discBd E ⊆ discBd D ∪ F ∧ E ⊆ closedBall 0 1 := by
  by_cases hsub : D ⊆ closedInner F
  · obtain ⟨hE, hEb⟩ := isClosedDisc_closedInner hF
    refine ⟨closedInner F, hE, hsub, ?_, ?_, closedInner_subset_closedBall hF hFu⟩
    · intro x hxF
      apply discBd_subset (closedInner F)
      rwa [hEb]
    · rw [hEb]
      exact subset_union_right
  obtain ⟨q, f, p, hqf, hqfr, hpq, hpcl, K, ℓ, R, s, t, hℓ, hst, hintervals,
    h0, h1, hℓF, hℓD, hpair, hsmall, hR, hDR, hRu, hRb, hcover⟩ :=
    exists_maximal_plane_excursions hD hF hinter hDu hFu hsub
  have hqD : range q ⊆ discBd D := hqfr ▸ subset_union_left
  have hfD : range f ⊆ discBd D := hqfr ▸ subset_union_right
  have havoidf : ∀ i, Disjoint (ℓ i '' Ioo (0 : 𝕀) 1) (range f) := by
    intro i
    exact Set.disjoint_left.mpr (fun _ hx hy => hℓD i hx (discBd_subset D (hfD hy)))
  have havoidq : ∀ i, Disjoint (ℓ i '' Ioo (0 : 𝕀) 1) (range q) := by
    intro i
    exact Set.disjoint_left.mpr (fun _ hx hy => hℓD i hx (discBd_subset D (hqD hy)))
  obtain ⟨g, hg, hg0, hg1, hℓg, hopen⟩ := exists_arc_gluing_disjoint_excursions
    hqf.2 s t hst hintervals ℓ hℓ h0 h1 havoidf hpair hsmall
  have hqg : IsTwoArcs q g := two_arcs_of_glued_excursions hqf hg hg0 hg1 ℓ hopen havoidq
  have hP : IsOArc (range q ∪ range g) :=
    oArc_of_two_arcs hqg.1 hqg.2 hqg.3.symm hqg.4.symm hqg.5
  let E := closedInner (range q ∪ range g)
  have hE : IsClosedDisc E := (isClosedDisc_closedInner hP).1
  have hEb : discBd E = range q ∪ range g := (isClosedDisc_closedInner hP).2
  have hgdesc : range g ⊆ discBd D ∪ ⋃ i, ℓ i '' Ioo (0 : 𝕀) 1 := by
    rintro _ ⟨u, rfl⟩
    by_cases hu0 : u = 0
    · subst u
      exact Or.inl (hg0 ▸ hfD ⟨0, rfl⟩)
    by_cases hu1 : u = 1
    · subst u
      exact Or.inl (hg1 ▸ hfD ⟨1, rfl⟩)
    have hu : u ∈ Ioo (0 : 𝕀) 1 :=
      ⟨lt_of_le_of_ne (unitInterval.nonneg u) (Ne.symm hu0),
        lt_of_le_of_ne (unitInterval.le_one u) hu1⟩
    rcases hopen ⟨u, hu, rfl⟩ with hfu | hexc
    · exact Or.inl (hfD ((image_subset_range _ _) hfu))
    · exact Or.inr hexc
  have hdesc : discBd E ⊆ discBd D ∪ ⋃ i, ℓ i '' Ioo (0 : 𝕀) 1 := by
    rw [hEb]
    exact union_subset (hqD.trans subset_union_left) hgdesc
  have hbd : discBd E ⊆ discBd D ∪ F := by
    intro x hx
    rcases hdesc hx with hxD | hxexc
    · exact Or.inl hxD
    · obtain ⟨i, hi⟩ := mem_iUnion.mp hxexc
      exact Or.inr (hℓF i ((image_subset_range _ _) hi))
  have hbdDF : discBd E ⊆ D ∪ F := hbd.trans
    (union_subset_union (discBd_subset D) subset_rfl)
  have hEu : E ⊆ closedBall 0 1 := plane_disc_subset_unitBall_of_boundary_subset hE
    (hbdDF.trans (union_subset hDu hFu))
  have hpcommon : p ∈ closure ((D ∪ E)ᶜ) :=
    access_point_common_exterior_of_boundary_subset hF hDu hFu hE hEu hbdDF hpcl
  have hdis : Disjoint (discInt D) (discBd E) := by
    apply Set.disjoint_left.mpr
    intro x hxD hxE
    rcases hdesc hxE with hxold | hxexc
    · exact hxD.2 hxold
    · obtain ⟨i, hi⟩ := mem_iUnion.mp hxexc
      exact hℓD i hi hxD.1
  have hDE : D ⊆ E := plane_disc_subset_of_shared_arc_and_common_exterior
    hD hE hqf hqg hqfr.symm hEb hpq hpcommon hdis
  have hz : (2 : ℂ) ∉ closedBall 0 1 := by norm_num [mem_closedBall, dist_eq_norm]
  have hRE : ∀ i, R i ⊆ E := by
    intro i
    have hℓE : range (ℓ i) ⊆ E := (hℓg i).trans
      ((hEb ▸ subset_union_right).trans (discBd_subset E))
    apply disc_subset_of_boundary_subset_and_connected_compl plane_point (hR i)
      (plane_disc_complement_preconnected hE)
      ((hRb i).trans (union_subset hDE hℓE))
      (fun h => hz (hRu i h)) (fun h => hz (hEu h))
  have hFE : F ⊆ E := by
    intro x hx
    rcases hcover hx with hxD | hxR
    · exact hDE hxD
    · obtain ⟨i, hi⟩ := mem_iUnion.mp hxR
      exact hRE i hi
  exact ⟨E, hE, hDE, hFE, hbd, hEu⟩

end GraphMinor.GM08
