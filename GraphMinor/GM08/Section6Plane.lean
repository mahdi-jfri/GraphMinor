module

public import GraphMinor.Surface.DiscGrow
import GraphMinor.Surface.DiscMerge
import GraphMinor.Surface.Cuffs
import GraphMinor.GM08.Section6Chord
import GraphMinor.GM08.Section6ExcursionArcs
import GraphMinor.GM08.Section6Exterior
import GraphMinor.GM08.Section6Excursions

/-!
# Excursion enlargements in the plane

The sphere in VIII (6.2), page 264, can be cut at the specified exterior
point and put in plane coordinates. Each outside component then gives a
closed disc enlargement of the first disc. This file constructs that
enlargement with its exact boundary and the complete excursion arc.
-/

public section

namespace GraphMinor.GM08

open Set Topology Metric Surface

local notation "𝕀" => unitInterval

private theorem plane_manifold_point (x : ℂ) : IsManifoldPoint x := by
  obtain ⟨e⟩ := exists_homeomorph_ball x one_pos
  have h : IsInteriorPoint x := ⟨ball x 1, isOpen_ball, mem_ball_self one_pos, ⟨e⟩⟩
  exact h.isManifoldPoint

/-- Each outside component in the plane yields an enlargement of the first
disc. Its new boundary is a retained old arc together with the complete
excursion, and its removed old arc has the same endpoints. -/
theorem exists_plane_excursion_enlargement {D F : Set ℂ} (hD : IsClosedDisc D)
    (hF : IsOArc F) (hinter : (F ∩ D).Nontrivial)
    {J : Set ℂ} (hJ : J ∈ componentsIn (F \ D)) :
    ∃ ℓ : 𝕀 → ℂ, ∃ E : Set ℂ, ∃ a b : 𝕀 → ℂ,
      IsArcMap ℓ ∧ range ℓ ⊆ F ∧ ℓ '' Ioo (0 : 𝕀) 1 = J ∧ range ℓ = closure J ∧
      IsClosedDisc E ∧ D ⊆ E ∧ IsTwoArcs a b ∧ a 0 = ℓ 0 ∧ a 1 = ℓ 1 ∧
      range a ∪ range b = discBd D ∧ discBd E = range a ∪ range ℓ := by
  obtain ⟨ℓ, hℓ, hℓ0, hℓ1, hℓopen, hℓrange⟩ :=
    exists_arc_for_excursion_component plane_manifold_point hD hF hinter hJ
  have hJF : J ⊆ F := by
    rcases hJ with ⟨x, hx, rfl⟩
    exact (connectedComponentIn_subset (F \ D) x).trans sdiff_subset
  have hℓF : range ℓ ⊆ F := hℓrange ▸ closure_minimal hJF hF.isCompact.isClosed
  have hmeet : ∀ r, ℓ r ∈ D → r = 0 ∨ r = 1 := by
    intro r hrD
    by_cases hr0 : r = 0
    · exact Or.inl hr0
    by_cases hr1 : r = 1
    · exact Or.inr hr1
    have hr : r ∈ Ioo (0 : 𝕀) 1 :=
      ⟨lt_of_le_of_ne (unitInterval.nonneg r) (Ne.symm hr0),
        lt_of_le_of_ne (unitInterval.le_one r) hr1⟩
    have hrJ : ℓ r ∈ J := hℓopen ▸ ⟨r, hr, rfl⟩
    rcases hJ with ⟨x, hx, rfl⟩
    exact False.elim ((connectedComponentIn_subset (F \ D) x hrJ).2 hrD)
  have H : ∀ P : Set ℂ, P ⊆ univ → IsOArc P →
      ∃ E : Set ℂ, E ⊆ univ ∧ IsClosedDisc E ∧ discBd E = P := by
    intro P _ hP
    exact ⟨closedInner P, subset_univ _, (isClosedDisc_closedInner hP).1,
      (isClosedDisc_closedInner hP).2⟩
  obtain ⟨E, a, b, _, hE, hDE, hab, ha0, ha1, hr, hEb⟩ :=
    exists_disc_of_chord_exact_boundary plane_manifold_point (subset_univ D) hD H
      hℓ (subset_univ (range ℓ)) hℓ0 hℓ1 hmeet
  exact ⟨ℓ, E, a, b, hℓ, hℓF, hℓopen, hℓrange, hE, hDE, hab, ha0, ha1, hr, hEb⟩

/-- A plane disc with boundary in the closed unit ball lies entirely in
that ball. This bounds all excursion enlargements by the same compact set. -/
theorem plane_disc_subset_unitBall_of_boundary_subset {E : Set ℂ} (hE : IsClosedDisc E)
    (hbd : discBd E ⊆ closedBall 0 1) : E ⊆ closedBall 0 1 := by
  rw [eq_closedInner_of_discBd hE.isOArc_discBd hE rfl]
  exact closedInner_subset_closedBall hE.isOArc_discBd hbd

private theorem plane_disc_compl_eq_outer {E : Set ℂ} (hE : IsClosedDisc E) :
    Eᶜ = outer (discBd E) := by
  have heq := eq_closedInner_of_discBd hE.isOArc_discBd hE rfl
  nth_rw 1 [heq]
  ext z
  simp only [closedInner, Surface.inner, outer, mem_compl_iff, mem_union, mem_ofPred_eq]
  tauto

/-- The exterior of a closed plane disc is connected. -/
theorem plane_disc_complement_preconnected {E : Set ℂ} (hE : IsClosedDisc E) :
    IsPreconnected Eᶜ := by
  obtain ⟨φ⟩ := hE.isOArc_discBd
  rw [plane_disc_compl_eq_outer hE]
  exact (isJordanParts φ).isConnected_outer.isPreconnected

/-- Every boundary point of a plane disc can be approached from outside.
This is the exterior-side condition in the comparison of excursion lobes. -/
theorem plane_disc_boundary_subset_closure_compl {E : Set ℂ} (hE : IsClosedDisc E) :
    discBd E ⊆ closure Eᶜ := by
  obtain ⟨φ⟩ := hE.isOArc_discBd
  rw [plane_disc_compl_eq_outer hE, (isJordanParts φ).closure_outer]
  exact subset_union_right

/-- Unless the second closed domain already contains the first disc, there
is an old boundary point outside the second curve retained by every bounded
excursion enlargement. The point `2` lies outside the common unit-ball
bound and fixes the exterior component for all these enlargements. -/
theorem exists_common_retained_plane_point {D F : Set ℂ} (hD : IsClosedDisc D)
    (hF : IsOArc F) (hDu : D ⊆ closedBall 0 1) (hFu : F ⊆ closedBall 0 1)
    (hnot : ¬ D ⊆ closedInner F) :
    ∃ p ∈ discBd D \ F,
      p ∈ closure (connectedComponentIn ((D ∪ closedInner F)ᶜ) (2 : ℂ)) ∧
      ∀ E : Set ℂ, IsClosedDisc E → D ⊆ E →
      discBd E ⊆ D ∪ F → E ⊆ closedBall 0 1 → p ∈ discBd E := by
  let B := closedInner F
  have hB : IsClosedDisc B := (isClosedDisc_closedInner hF).1
  have hBb : discBd B = F := (isClosedDisc_closedInner hF).2
  have hFB : F ⊆ B := hBb ▸ discBd_subset B
  have hBu : B ⊆ closedBall 0 1 := closedInner_subset_closedBall hF hFu
  have hz : (2 : ℂ) ∉ closedBall 0 1 := by norm_num [mem_closedBall, dist_eq_norm]
  have hzD : (2 : ℂ) ∉ D := fun h => hz (hDu h)
  have hzB : (2 : ℂ) ∉ B := fun h => hz (hBu h)
  obtain ⟨p, hp, hpcl⟩ := exists_exterior_access_point plane_manifold_point hD hB
    (plane_disc_complement_preconnected hB) hzD hzB (not_subset.mp hnot)
  refine ⟨p, ⟨hp.1, fun h => hp.2 (hFB h)⟩, hpcl, ?_⟩
  intro E hE hDE hEb hEu
  exact exterior_access_point_on_enlarged_boundary plane_manifold_point hE hDE
    (hEb.trans (union_subset_union_right D hFB))
    (fun h => h.elim hzD hzB) (fun h => hz (hEu h)) (discBd_subset D hp.1) hpcl

/-- The exterior access point lies in a whole old boundary arc retained by
every excursion enlargement. The complementary embedded arc therefore
provides one common interval on which to perform all replacements. -/
theorem exists_common_retained_plane_arc {D F : Set ℂ} (hD : IsClosedDisc D)
    (hF : IsOArc F) (hinter : (discBd D ∩ F).Nontrivial)
    (hDu : D ⊆ closedBall 0 1) (hFu : F ⊆ closedBall 0 1)
    (hnot : ¬ D ⊆ closedInner F) :
    ∃ q f : 𝕀 → ℂ, ∃ p : ℂ, IsTwoArcs q f ∧ range q ∪ range f = discBd D ∧
      Disjoint (q '' Ioo (0 : 𝕀) 1) F ∧ p ∈ q '' Ioo (0 : 𝕀) 1 ∧
      p ∈ closure (connectedComponentIn ((D ∪ closedInner F)ᶜ) (2 : ℂ)) ∧
      ∀ (E : Set ℂ) (a b ℓ : 𝕀 → ℂ), IsClosedDisc E → D ⊆ E →
        E ⊆ closedBall 0 1 → IsTwoArcs a b →
        range a ∪ range b = discBd D → discBd E = range a ∪ range ℓ →
        range ℓ ⊆ F → a 0 = ℓ 0 → a 1 = ℓ 1 → range q ⊆ discBd E := by
  obtain ⟨p, hp, hpcl, hpoint⟩ := exists_common_retained_plane_point hD hF hDu hFu hnot
  obtain ⟨q, f, hqf, hqfr, hpq, hqF⟩ :=
    exists_arc_around_point_avoiding_closed_set hD.isOArc_discBd
      hF.isCompact.isClosed hinter hp.1 hp.2
  refine ⟨q, f, p, hqf, hqfr, hqF, hpq, hpcl, ?_⟩
  intro E a b ℓ hE hDE hEu hab hr hEb hℓF ha0 ha1
  have haD : range a ⊆ D := (hr ▸ subset_union_left).trans (discBd_subset D)
  have hEsub : discBd E ⊆ D ∪ F := by
    rw [hEb]
    exact union_subset_union haD hℓF
  have hpE : p ∈ discBd E := hpoint E hE hDE hEsub hEu
  have hpa : p ∈ range a := by
    rw [hEb] at hpE
    exact hpE.resolve_right (fun h => hp.2 (hℓF h))
  have ha0F : a 0 ∈ F := hℓF ⟨0, ha0.symm⟩
  have ha1F : a 1 ∈ F := hℓF ⟨1, ha1.symm⟩
  have hqa : range q ⊆ range a := range_subset_arc_of_open_arc_avoids_endpoints
    hab hqf.1.1 (fun x hx => hr.symm ▸ hqfr ▸ Or.inl hx)
    (fun h => Set.disjoint_left.mp hqF h ha0F)
    (fun h => Set.disjoint_left.mp hqF h ha1F) ⟨p, hpq, hpa⟩
  exact hqa.trans (hEb ▸ subset_union_left)

/-- The original exterior access remains outside the glued disc when its
boundary stays in the old disc together with the second curve. This gives
the common-exterior hypothesis for the retained-arc enclosure comparison. -/
theorem access_point_common_exterior_of_boundary_subset {D F E : Set ℂ}
    (hF : IsOArc F) (hDu : D ⊆ closedBall 0 1) (hFu : F ⊆ closedBall 0 1)
    (hE : IsClosedDisc E) (hEu : E ⊆ closedBall 0 1)
    (hEb : discBd E ⊆ D ∪ F) {p : ℂ}
    (hpcl : p ∈ closure (connectedComponentIn ((D ∪ closedInner F)ᶜ) (2 : ℂ))) :
    p ∈ closure ((D ∪ E)ᶜ) := by
  let B := closedInner F
  let K := connectedComponentIn ((D ∪ B)ᶜ) (2 : ℂ)
  have hB := (isClosedDisc_closedInner hF).1
  have hBb := (isClosedDisc_closedInner hF).2
  have hFB : F ⊆ B := hBb ▸ discBd_subset B
  have hBu : B ⊆ closedBall 0 1 := closedInner_subset_closedBall hF hFu
  have hz : (2 : ℂ) ∉ closedBall 0 1 := by norm_num [mem_closedBall, dist_eq_norm]
  have hzU : (2 : ℂ) ∈ (D ∪ B)ᶜ :=
    fun h => h.elim (fun hD => hz (hDu hD)) (fun hB => hz (hBu hB))
  have hKbd : Disjoint K (discBd E) := by
    apply Set.disjoint_left.mpr
    intro x hx hxb
    have hxU := connectedComponentIn_subset ((D ∪ B)ᶜ) (2 : ℂ) hx
    rcases hEb hxb with hD | hF
    · exact hxU (Or.inl hD)
    · exact hxU (Or.inr (hFB hF))
  have hKE : Disjoint K E := by
    rcases hE.side plane_manifold_point isPreconnected_connectedComponentIn hKbd with hin | hout
    · exact False.elim (hz (hEu (hin (mem_connectedComponentIn hzU)).1))
    · exact hout
  have hKsub : K ⊆ (D ∪ E)ᶜ := by
    intro x hx hDE
    rcases hDE with hxD | hxE
    · exact connectedComponentIn_subset ((D ∪ B)ᶜ) (2 : ℂ) hx (Or.inl hxD)
    · exact Set.disjoint_left.mp hKE hx hxE
  exact closure_mono hKsub hpcl

end GraphMinor.GM08
