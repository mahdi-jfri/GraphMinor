module

public import GraphMinor.GM06.Defs
import GraphMinor.Surface.DiscGrow
import GraphMinor.Surface.PlaneDisc
import GraphMinor.Surface.Jordan

/-!
# Uniqueness of a disc incident with the surface boundary

The enclosed portion in Graph Minors VI, Section 4, page 124, is determined
by its boundary. Two discs with the same boundary either have the same inside,
or together give an embedded sphere. The latter case cannot contain a point
of the surface boundary, by invariance of domain.
-/

public section

namespace GraphMinor.GM06

open Set Topology Metric GraphMinor.Surface OnePoint

universe u

private theorem interiorPoint_of_sphere_embedding
    {S : Type u} [TopologicalSpace S] (hS : IsSurface S)
    {T : OnePoint EuclideanPlane → S} (hc : Continuous T) (hi : Function.Injective T)
    (p : OnePoint EuclideanPlane) : IsInteriorPoint (T p) := by
  let : T2Space S := hS.2.1
  obtain ⟨q, hq⟩ : ∃ q : OnePoint EuclideanPlane, q ≠ p := by
    by_cases hp : p = ∞
    · exact ⟨sph 0, hp ▸ sph_ne_infty 0⟩
    · exact ⟨∞, Ne.symm hp⟩
  obtain ⟨H, hH⟩ := exists_homeomorph_onePoint q
  let ρ : ℂ → S := fun z => T (H.symm (sph z))
  have hρc : Continuous ρ := hc.comp (H.symm.continuous.comp isOpenEmbedding_sph.continuous)
  have hρi : Function.Injective ρ := fun z w he =>
    isOpenEmbedding_sph.injective (H.symm.injective (hi he))
  obtain ⟨z, hz⟩ : ∃ z : ℂ, H p = sph z := by
    rcases eq_infty_or_sph (H p) with he | he
    · exact False.elim (hq (H.injective (hH.trans he.symm)))
    · exact he
  have hρz : ρ z = T p := by
    change T (H.symm (sph z)) = T p
    rw [← hz, H.symm_apply_apply]
  have hopen : IsOpen (ρ '' ball z 1) := isOpen_image_of_manifold isOpen_ball
    hρc.continuousOn hρi.injOn (fun _ _ => hS.2.2 _)
  rw [← hρz]
  exact isInteriorPoint_of_injOn (isCompact_closedBall z 1) hρc.continuousOn hρi.injOn
    ball_subset_closedBall isOpen_ball hopen (mem_ball_self zero_lt_one)

/-- A closed disc whose boundary contains a surface boundary point is the only
closed disc with that boundary. This supplies uniqueness of the enclosed
portion in Graph Minors VI, Section 4, page 124. -/
theorem disc_eq_of_discBd_eq_of_mem_bd
    {S : Type u} [TopologicalSpace S] (hS : IsSurface S)
    {D E : Set S} (hD : IsClosedDisc D) (hE : IsClosedDisc E)
    (hbd : discBd D = discBd E) {x : S} (hx : x ∈ discBd D) (hxb : x ∈ bd S) : D = E := by
  let : T2Space S := hS.2.1
  have hDU : discInt D ∪ discBd D = D := sdiff_union_of_subset (discBd_subset D)
  have hEU : discInt E ∪ discBd E = E := sdiff_union_of_subset (discBd_subset E)
  by_cases hmeet : (discInt D ∩ discInt E).Nonempty
  · have hDE : discInt D ⊆ discInt E := by
      apply subset_of_side hD.isPreconnected_discInt (hE.isOpen_discInt hS.2.2)
        (by rw [hEU]; exact hE.isClosed) ?_ hmeet
      exact disjoint_left.mpr (fun y hy hyE => hy.2 (hbd.symm ▸ hyE))
    have hED : discInt E ⊆ discInt D := by
      apply subset_of_side hE.isPreconnected_discInt (hD.isOpen_discInt hS.2.2)
        (by rw [hDU]; exact hD.isClosed) ?_ (by rwa [inter_comm])
      exact disjoint_left.mpr (fun y hy hyD => hy.2 (hbd ▸ hyD))
    rw [← hDU, ← hEU, Subset.antisymm hDE hED, hbd]
  · have hm : D ∩ E = discBd D := by
      apply Subset.antisymm
      · rintro y ⟨hyD, hyE⟩
        by_cases hyBD : y ∈ discBd D
        · exact hyBD
        by_cases hyBE : y ∈ discBd E
        · exact hbd.symm ▸ hyBE
        exact False.elim (hmeet ⟨y, ⟨hyD, hyBD⟩, ⟨hyE, hyBE⟩⟩)
      · intro y hy
        exact ⟨discBd_subset D hy, discBd_subset E (hbd ▸ hy)⟩
    obtain ⟨T, hc, hi, hr⟩ := exists_sphere_map hD hE hbd hm
    have hxR : x ∈ range T := by rw [hr]; exact Or.inl (discBd_subset D hx)
    obtain ⟨p, hp⟩ := hxR
    exact False.elim (hxb (hp ▸ interiorPoint_of_sphere_embedding hS hc hi p))

/-- The enclosed portion for a fixed path in Graph Minors VI, Section 4,
page 124, is unique because its boundary meets the surface boundary. -/
theorem isEnclosedDisc_unique
    {S : Type u} [TopologicalSpace S] {P : Drawing S} {A D E : Set S} {s : S}
    (hS : IsSurface S) (hsb : s ∈ bd S) (hsP : s ∈ P.U)
    (hD : IsEnclosedDisc P A D) (hE : IsEnclosedDisc P A E) : D = E := by
  have hsD : s ∈ discBd D := by rw [hD.2.2]; exact Or.inl hsP
  exact disc_eq_of_discBd_eq_of_mem_bd hS hD.1 hE.1
    (hD.2.2.trans hE.2.2.symm) hsD hsb

end GraphMinor.GM06
