module

public import GraphMinor.GM06.Defs
import GraphMinor.Surface.EdgeLens
public import GraphMinor.Surface.DiscGrow
import GraphMinor.GM11.PerimeterPull

/-!
# A curve just inside a boundary arc

For the curve choice in VI (5.3), take a thin lens around a boundary
arc, away from the closed set to be avoided and the rest of the
disc boundary. One side of the lens lies inside the disc. Its path
between the arc ends avoids the closed set. A complementary boundary
arc and the one-point compactification reduce the plane case to the
closed-surface lens theorem.
-/

public section
namespace GraphMinor.GM06
open Set Topology GraphMinor.Surface
private theorem exists_path_inside_disc_beside_boundary_arc {S : Type} [TopologicalSpace S] [T2Space S] (hS : IsClosedSurface S)
    {D : Set S} (hD : IsClosedDisc D) (a b : Curve S) (ha : Function.Injective a)
    (haD : range a ⊆ discBd D) (hcover : discBd D ⊆ range a ∪ range b)
    (hmeet : range a ∩ range b ⊆ {a 0, a 1})
    {Z : Set S} (hZ : IsClosed Z) (hAZ : range a ∩ Z ⊆ {a 0, a 1}) :
    ∃ p : Path (a 0) (a 1), range p ⊆ D ∧
      ∀ t : unitInterval, 0 < t → t < 1 → p t ∈ discInt D \ Z := by
  have hman : ∀ x : S, IsManifoldPoint x := fun x => (hS.2.2 x).isManifoldPoint
  have hline : IsLineWithEnds (range a) (a 0) (a 1) := by
    let e : unitInterval ≃ₜ range a := Continuous.homeoOfEquivCompactToT2
      (f := Equiv.ofInjective a ha) a.continuous.rangeFactorization
    exact ⟨e, rfl, rfl⟩
  have hne : a 0 ≠ a 1 := fun h => zero_ne_one (ha h)
  have hZ' : IsClosed (Z ∪ range b) := hZ.union (isCompact_range b.continuous).isClosed
  have hmeet : range a ∩ (Z ∪ range b) ⊆ {a 0, a 1} := by
    rintro x ⟨hx, hz | hb⟩
    · exact hAZ ⟨hx, hz⟩
    · exact hmeet ⟨hx, hb⟩
  obtain ⟨E, A, B, hE, hLE, hEZ, h0, h1, hEL, hEeq,
    hA, hB, hAn, hBn, hAL, hBL, hLA, hLB, hpA, hpB, _⟩ :=
    exists_edge_lens_sides hS hline hne hZ' hmeet
  let mid : unitInterval := ⟨1 / 2, by constructor <;> norm_num⟩
  have hwL : a mid ∈ range a := mem_range_self mid
  have hwnot : a mid ∉ ({a 0, a 1} : Set S) := by
    intro hh
    rcases hh with hh | hh
    · have he := congrArg Subtype.val (ha hh)
      norm_num [mid] at he
    · have he := congrArg Subtype.val (ha hh)
      norm_num [mid] at he
  have hwE : a mid ∈ discInt E := ⟨hLE hwL, fun hb => hwnot (hEL ⟨hb, hwL⟩)⟩
  have hwcl : a mid ∈ closure (discInt D) := hD.subset_closure_discInt (discBd_subset D (haD hwL))
  obtain ⟨z, hzE, hzD⟩ := mem_closure_iff.mp hwcl (discInt E) (hE.isOpen_discInt hman) hwE
  have hzL : z ∉ range a := fun hz => hzD.2 (haD hz)
  have hzAB : z ∈ A ∨ z ∈ B := (show z ∈ A ∪ B ∪ range a from hEeq ▸ hzE.1).resolve_right hzL
  have chooseSide (C : Set S) (hC : IsPreconnected C) (hCE : C ⊆ E)
      (hCL : Disjoint C (range a)) (hzC : z ∈ C)
      (hpC : ∃ p : Path (a 0) (a 1), range p ⊆ E ∧
        ∀ t : unitInterval, 0 < t → t < 1 → p t ∈ C) :
      ∃ p : Path (a 0) (a 1), range p ⊆ D ∧
        ∀ t : unitInterval, 0 < t → t < 1 → p t ∈ discInt D \ Z := by
    have hCbd : Disjoint C (discBd D) := by
      refine disjoint_left.mpr ?_
      intro x hxC hxBd
      rcases hcover hxBd with hxa | hxb
      · exact disjoint_left.mp hCL hxC hxa
      · have hxends := hEZ ⟨hCE hxC, Or.inr hxb⟩
        have hxL : x ∈ range a := by
          rcases hxends with rfl | hx
          · exact mem_range_self 0
          · rw [mem_singleton_iff] at hx
            rw [hx]
            exact mem_range_self 1
        exact disjoint_left.mp hCL hxC hxL
    have hCD : C ⊆ discInt D := by
      rcases hD.side hman hC hCbd with h | h
      · exact h
      · exact False.elim (disjoint_left.mp h hzC hzD.1)
    obtain ⟨p, hpE, hpC⟩ := hpC
    refine ⟨p, ?_, ?_⟩
    · rintro _ ⟨t, rfl⟩
      by_cases ht0 : t = 0
      · rw [ht0, Path.source]
        exact discBd_subset D (haD (mem_range_self 0))
      · by_cases ht1 : t = 1
        · rw [ht1, Path.target]
          exact discBd_subset D (haD (mem_range_self 1))
        · exact (hCD (hpC t (unitInterval.pos_iff_ne_zero.mpr ht0)
            (unitInterval.lt_one_iff_ne_one.mpr ht1))).1
    · intro t ht0 ht1
      have htC := hpC t ht0 ht1
      refine ⟨hCD htC, ?_⟩
      intro htZ
      have htends := hEZ ⟨hpE (mem_range_self t), Or.inl htZ⟩
      have htL : p t ∈ range a := by
        rcases htends with he | he
        · rw [he]
          exact mem_range_self 0
        · rw [mem_singleton_iff] at he
          rw [he]
          exact mem_range_self 1
      exact disjoint_left.mp hCL htC htL
  rcases hzAB with hzA | hzB
  · exact chooseSide A hA (fun x hx => hEeq.symm ▸ Or.inl (Or.inl hx)) hAL hzA hpA
  · exact chooseSide B hB (fun x hx => hEeq.symm ▸ Or.inl (Or.inr hx)) hBL hzB hpB
end GraphMinor.GM06

namespace GraphMinor.GM06
open Set Topology GraphMinor.Surface Metric
private theorem exists_complementary_boundary_curve {S : Type} [TopologicalSpace S] [T2Space S] {D : Set S}
    (hD : IsClosedDisc D) (a : Curve S) (ha : Function.Injective a)
    (haD : range a ⊆ discBd D) :
    ∃ b : Curve S, discBd D ⊆ range a ∪ range b ∧
      range a ∩ range b ⊆ {a 0, a 1} := by
  obtain ⟨h, g, c⟩ := hD.exists_isChart
  have haD' : range a ⊆ D := haD.trans (discBd_subset D)
  let ac : unitInterval → ℂ := h ∘ a
  have hac : IsArcMap ac :=
    ⟨c.hc.comp_continuous a.continuous (fun t => haD' (mem_range_self t)),
      fun t t' ht => ha (c.gh.injOn (haD' (mem_range_self t)) (haD' (mem_range_self t')) ht)⟩
  have hacF : range ac ⊆ sphere (0 : ℂ) 1 := by
    rintro _ ⟨t, rfl⟩
    rw [← c.bd]
    exact mem_image_of_mem h (haD (mem_range_self t))
  obtain ⟨φ⟩ := oArc_sphere
  obtain ⟨bc, hbc, hb0, hb1, hu, hm⟩ := exists_other_arc φ hac hacF
  have hbF : range bc ⊆ sphere (0 : ℂ) 1 := hu ▸ subset_union_right
  have hbD : ∀ t, bc t ∈ closedBall (0 : ℂ) 1 := fun t => sphere_subset_closedBall (hbF (mem_range_self t))
  let b : Curve S := ⟨g ∘ bc, c.gc.comp_continuous hbc.1 hbD⟩
  refine ⟨b, ?_, ?_⟩
  · intro x hx
    have hxD := discBd_subset D hx
    have hxF : h x ∈ sphere (0 : ℂ) 1 := c.bd ▸ mem_image_of_mem h hx
    rw [← hu] at hxF
    rcases hxF with ⟨t, ht⟩ | ⟨t, ht⟩
    · refine Or.inl ⟨t, ?_⟩
      exact c.gh.injOn (haD' (mem_range_self t)) hxD ht
    · refine Or.inr ⟨t, ?_⟩
      change g (bc t) = x
      rw [ht, c.gh hxD]
  · rintro x ⟨⟨s, hs⟩, ⟨t, ht⟩⟩
    have he : ac s = bc t := by
      change h (a s) = bc t
      rw [hs, ← c.hg (hbD t)]
      exact congrArg h ht.symm
    rcases hm s t he with ⟨hs0, _⟩ | ⟨hs1, _⟩
    · exact Or.inl (hs0 ▸ hs.symm)
    · exact Or.inr (hs1 ▸ hs.symm)
end GraphMinor.GM06

namespace GraphMinor.GM06
open Set Topology GraphMinor.Surface
/-- A curve beside a boundary arc, inside the disc and off a closed
set meeting the arc only at its ends. This supplies the curve choice
in VI (5.3), pages 132–133, also when the strip projection identifies
its two linkage boundaries. -/
theorem exists_path_inside_plane_disc_beside_boundary_arc
    {S : Type} [TopologicalSpace S] [T2Space S] (e : S ≃ₜ EuclideanPlane) {D : Set S} (hD : IsClosedDisc D)
    (a : Curve S) (ha : Function.Injective a)
    (haD : range a ⊆ discBd D) {Z : Set S}
    (hZ : IsClosed Z) (hAZ : range a ∩ Z ⊆ {a 0, a 1}) :
    ∃ p : Path (a 0) (a 1), range p ⊆ D ∧
      ∀ t : unitInterval, 0 < t → t < 1 → p t ∈ discInt D \ Z := by
  classical
  obtain ⟨b, hcover, hmeet⟩ := exists_complementary_boundary_curve hD a ha haD
  let j : S → OnePoint EuclideanPlane := fun x => e x
  have hj : Continuous j := OnePoint.isOpenEmbedding_coe.continuous.comp e.continuous
  have hji : Function.Injective j := OnePoint.coe_injective.comp e.injective
  obtain ⟨hD', hBd'⟩ := hD.image_injOn hj.continuousOn hji.injOn
  let a' : Curve (OnePoint EuclideanPlane) := ⟨j ∘ a, hj.comp a.continuous⟩
  let b' : Curve (OnePoint EuclideanPlane) := ⟨j ∘ b, hj.comp b.continuous⟩
  have ha' : Function.Injective a' := hji.comp ha
  have haD' : range a' ⊆ discBd (j '' D) := by
    rintro _ ⟨t, rfl⟩
    rw [hBd']
    exact mem_image_of_mem j (haD (mem_range_self t))
  have hcover' : discBd (j '' D) ⊆ range a' ∪ range b' := by
    rw [hBd']
    rintro _ ⟨x, hx, rfl⟩
    rcases hcover hx with ⟨t, rfl⟩ | ⟨t, rfl⟩
    · exact Or.inl (mem_range_self t)
    · exact Or.inr (mem_range_self t)
  have hmeet' : range a' ∩ range b' ⊆ {a' 0, a' 1} := by
    rintro x ⟨⟨s, hs⟩, ⟨t, ht⟩⟩
    have he : a s = b t := hji (hs.trans ht.symm)
    have hends := hmeet ⟨mem_range_self s, ⟨t, he.symm⟩⟩
    rcases hends with he0 | he1
    · exact Or.inl (hs.symm.trans (congrArg j he0))
    · exact Or.inr (hs.symm.trans (congrArg j he1))
  have hZ' : IsClosed (j '' (Z ∩ D)) := ((hD.isCompact.inter_left hZ).image hj).isClosed
  have hAZ' : range a' ∩ (j '' (Z ∩ D)) ⊆ {a' 0, a' 1} := by
    rintro x ⟨⟨t, ht⟩, ⟨y, hy, hyx⟩⟩
    have hty : a t = y := hji (ht.trans hyx.symm)
    have hends := hAZ ⟨mem_range_self t, hty.symm ▸ hy.1⟩
    rcases hends with he0 | he1
    · exact Or.inl (ht.symm.trans (congrArg j he0))
    · exact Or.inr (ht.symm.trans (congrArg j he1))
  have hsph : IsSphere (OnePoint EuclideanPlane) := ⟨Homeomorph.refl _⟩
  have hS := GM11.IsSphere.isClosedSurface hsph
  obtain ⟨p, hpD, hpinside⟩ := exists_path_inside_disc_beside_boundary_arc hS.1 hD' a' b' ha'
    haD' hcover' hmeet' hZ' hAZ'
  have him : ∀ t, ∃ x ∈ D, j x = p t := fun t => hpD (mem_range_self t)
  choose g hgD hg using him
  have hgc : Continuous g := (OnePoint.isOpenEmbedding_coe.isEmbedding.comp e.isEmbedding).continuous_iff.mpr (by
    change Continuous (j ∘ g)
    have he : j ∘ g = p := funext hg
    rw [he]
    exact p.continuous)
  have hg0 : g 0 = a 0 := hji ((hg 0).trans p.source)
  have hg1 : g 1 = a 1 := hji ((hg 1).trans p.target)
  let q : Path (a 0) (a 1) := ⟨⟨g, hgc⟩, hg0, hg1⟩
  refine ⟨q, ?_, ?_⟩
  · rintro _ ⟨t, rfl⟩
    exact hgD t
  · intro t ht0 ht1
    have hpt := hpinside t ht0 ht1
    refine ⟨⟨hgD t, ?_⟩, ?_⟩
    · intro hbd
      apply hpt.1.2
      rw [hBd']
      exact ⟨g t, hbd, hg t⟩
    · intro hz
      apply hpt.2
      exact ⟨g t, ⟨hz, hgD t⟩, hg t⟩
end GraphMinor.GM06
