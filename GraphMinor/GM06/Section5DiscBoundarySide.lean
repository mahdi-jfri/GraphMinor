module

public import GraphMinor.Surface.Defs
import GraphMinor.Surface.DiscArcs
import GraphMinor.Surface.DiscGrow

/-!
# The side of a disc cross-cut beside a prescribed boundary arc

For the full boundary-contact assertion in VI (5.1), page 129,
choose the side of the region path that contains the initial cuff
gap. In a chart of the strip disc, a prescribed boundary arc has a
complementary arc on the circle. Together with the cross-cut these
form a theta curve. Its chosen closed side pulls back to a disc,
and that side minus the cut is a component of the original disc
minus the cut.
-/

public section
namespace GraphMinor.GM06
open Set Topology Metric GraphMinor.Surface
universe u

/-- A boundary arc and a cross-cut with the same ends bound a closed
side of the disc. Removing the cut from that side gives one component
of the disc minus the cut. -/
theorem exists_disc_side_of_boundary_arc
    {S : Type u} [TopologicalSpace S] [T2Space S] {D : Set S}
    (hD : IsClosedDisc D) (a e : Curve S)
    (ha : Function.Injective a) (he : Function.Injective e)
    (haD : range a ⊆ discBd D) (heD : range e ⊆ D)
    (h0 : a 0 = e 0) (h1 : a 1 = e 1)
    (heBd : range e ∩ discBd D = {e 0, e 1}) :
    ∃ Δ : Set S, IsClosedDisc Δ ∧ Δ ⊆ D ∧
      discBd Δ = range a ∪ range e ∧ (Δ \ range e) ∈ componentsIn (D \ range e) := by
  obtain ⟨h, g, c⟩ := hD.exists_isChart
  have haD' : range a ⊆ D := haD.trans (discBd_subset D)
  have hinj := c.gh.injOn
  let ac : unitInterval → ℂ := h ∘ a
  let ec : unitInterval → ℂ := h ∘ e
  have hac : IsArcMap ac :=
    ⟨c.hc.comp_continuous a.continuous (fun t => haD' (mem_range_self t)),
      fun t t' ht => ha (hinj (haD' (mem_range_self t)) (haD' (mem_range_self t')) ht)⟩
  have hec : IsArcMap ec :=
    ⟨c.hc.comp_continuous e.continuous (fun t => heD (mem_range_self t)),
      fun t t' ht => he (hinj (heD (mem_range_self t)) (heD (mem_range_self t')) ht)⟩
  have hacSphere : range ac ⊆ sphere (0 : ℂ) 1 := by
    rintro z ⟨t, rfl⟩
    rw [← c.bd]
    exact mem_image_of_mem h (haD (mem_range_self t))
  have hac0 : ac 0 = ec 0 := congrArg h h0
  have hac1 : ac 1 = ec 1 := congrArg h h1
  have hinside : ∀ t : unitInterval, t ≠ 0 → t ≠ 1 → ec t ∈ inner (sphere (0 : ℂ) 1) := by
    intro t ht0 ht1
    rw [inner_sphere, mem_ball_zero_iff]
    refine lt_of_le_of_ne (mem_closedBall_zero_iff.mp (c.hm (heD (mem_range_self t)))) ?_
    intro hn
    have hz : ec t ∈ sphere (0 : ℂ) 1 := mem_sphere_zero_iff_norm.mpr hn
    rw [← c.bd] at hz
    obtain ⟨x, hx, hxe⟩ := hz
    have hxt : x = e t := hinj (discBd_subset D hx) (heD (mem_range_self t)) hxe
    have htBd : e t ∈ range e ∩ discBd D := ⟨mem_range_self t, hxt ▸ hx⟩
    rw [heBd] at htBd
    rcases htBd with hte0 | hte1
    · exact ht0 (he hte0)
    · exact ht1 (he (mem_singleton_iff.mp hte1))
  obtain ⟨φ⟩ := oArc_sphere
  obtain ⟨b, hb, hb0, hb1, hu, hm⟩ := exists_other_arc φ hac hacSphere
  have cut : IsCut (sphere (0 : ℂ) 1) ac b ec := {
    arc_a := hac
    arc_b := hb
    arc_e := hec
    a_zero := hac0
    a_one := hac1
    b_zero := hb0.trans hac0
    b_one := hb1.trans hac1
    ne := fun h => zero_ne_one (hec.2 h)
    union := hu
    meet := hm
    inside := hinside }
  have J := isJordanParts φ
  have hsideSub := (cut.closedInner_facts J).2.1
  rw [closedInner_sphere] at hsideSub
  obtain ⟨hside, hsideBd⟩ := isClosedDisc_closedInner cut.oArc_side
  obtain ⟨hΔ, hΔbd⟩ := c.disc_g hsideSub hside
  let Δ := g '' closedInner (side ac ec)
  have hacRange : range ac = h '' range a := range_comp h a
  have hecRange : range ec = h '' range e := range_comp h e
  have hga : g '' range ac = range a := by rw [hacRange]; exact c.g_h haD'
  have hge : g '' range ec = range e := by rw [hecRange]; exact c.g_h heD
  have hecSub : range ec ⊆ closedBall (0 : ℂ) 1 := by rw [hecRange]; exact c.image_subset heD
  have hpart : (closedInner (side ac ec) \ range ec) ∈
      componentsIn (closedBall (0 : ℂ) 1 \ range ec) := by
    rw [← closedInner_sphere, (cut.components J).2.1]
    exact Or.inl rfl
  have hdiff : D \ range e = g '' (closedBall (0 : ℂ) 1 \ range ec) := by
    rw [c.g_sdiff Subset.rfl hecSub, c.g_closedBall, hge]
  have hΔdiff : g '' (closedInner (side ac ec) \ range ec) = Δ \ range e := by
    rw [c.g_sdiff hsideSub hecSub, hge]
  refine ⟨Δ, hΔ, c.g_subset hsideSub, ?_, ?_⟩
  · change discBd (g '' closedInner (side ac ec)) = _
    rw [hΔbd, hsideBd, side, image_union, hga, hge]
  · rw [hdiff, c.components_g sdiff_subset, ← hΔdiff]
    exact mem_image_of_mem (image g) hpart

end GraphMinor.GM06
