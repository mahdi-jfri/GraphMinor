module

public import GraphMinor.GM04.CellChords
import GraphMinor.GM06.Section2Dual
import GraphMinor.GM12.Section4ChordGeometry
import GraphMinor.Surface.DiscArcs
import GraphMinor.Surface.ArcTools

/-!
# Noncrossing lines in a closed disc

For the drawing step of IV (9.2), page 254, put a cell in unit-disc
coordinates. Straight chords give lines with the prescribed ends. Their
interiors miss the boundary, and noncrossing pairs give disjoint lines.
-/

public section

namespace GraphMinor.GM04

open Set Surface Metric Topology

universe u

private theorem line_image {S : Type u} [TopologicalSpace S] [T2Space S]
    {Z : Set ℂ} {a b : ℂ} (hl : IsLineWithEnds Z a b) {g : ℂ → S}
    (hc : ContinuousOn g Z) (hi : InjOn g Z) :
    IsLineWithEnds (g '' Z) (g a) (g b) := by
  obtain ⟨f, h0, h1⟩ := hl
  let e : unitInterval → S := fun t ↦ g (f t).val
  have hec : Continuous e := hc.comp_continuous
    (continuous_subtype_val.comp f.continuous) (fun t ↦ (f t).property)
  have hei : Function.Injective e := fun x y he ↦
    f.injective (Subtype.ext (hi (f x).property (f y).property he))
  have hr : range e = g '' Z := by
    ext y
    constructor
    · rintro ⟨t, rfl⟩
      exact ⟨_, (f t).property, rfl⟩
    · rintro ⟨z, hz, rfl⟩
      exact ⟨f.symm ⟨z, hz⟩, by simp [e]⟩
  refine ⟨hec.isClosedEmbedding hei |>.isEmbedding.toHomeomorph.trans (Homeomorph.setCongr hr), ?_, ?_⟩
  · change e 0 = g a
    simp only [e, h0]
  · change e 1 = g b
    simp only [e, h1]

private noncomputable def chartBoundaryMap {S : Type u} [TopologicalSpace S]
    {D : Set S} {h : S → ℂ} {g : ℂ → S} (c : IsChart D h g) : Circle → discBd D :=
  fun z ↦ ⟨g z, c.g_sphere ▸ mem_image_of_mem g (by simp)⟩

private theorem chartBoundaryMap_bijective {S : Type u} [TopologicalSpace S]
    {D : Set S} {h : S → ℂ} {g : ℂ → S} (c : IsChart D h g) :
    Function.Bijective (chartBoundaryMap c) := by
  constructor
  · intro x y hxy
    apply Subtype.ext
    exact c.injOn (by simp) (by simp) (congrArg Subtype.val hxy)
  · intro x
    have hx : x.val ∈ g '' sphere (0 : ℂ) 1 := by rw [c.g_sphere]; exact x.property
    obtain ⟨z, hz, hzx⟩ := hx
    let z' : Circle := ⟨z, hz⟩
    exact ⟨z', Subtype.ext hzx⟩

private theorem chartBoundaryMap_continuous {S : Type u} [TopologicalSpace S]
    {D : Set S} {h : S → ℂ} {g : ℂ → S} (c : IsChart D h g) :
    Continuous (chartBoundaryMap c) := by
  apply Continuous.subtype_mk
  exact c.gc.comp_continuous continuous_subtype_val (fun z ↦ by simp)

/-- A closed disc has a simultaneous choice of chords: each joins its
prescribed boundary points, meets the boundary only in those points, and
chords with distinct noncrossing ends are disjoint. This is the cellwise
construction in the proof of IV (9.2), page 254. -/
theorem exists_disc_pairing_lines {S : Type u} [TopologicalSpace S] [T2Space S]
    {D : Set S} (hD : IsClosedDisc D) :
    ∃ L : S → S → Set S,
      (∀ a ∈ discBd D, ∀ b ∈ discBd D, a ≠ b →
        IsLineWithEnds (L a b) a b ∧ L a b ⊆ D ∧ L a b ∩ discBd D = {a, b}) ∧
      (∀ a ∈ discBd D, ∀ c ∈ discBd D, ∀ b ∈ discBd D, ∀ d ∈ discBd D,
        a ≠ c → b ≠ d → a ≠ b → a ≠ d → c ≠ b → c ≠ d →
        ¬ GM06.CrossesOn (discBd D) a c b d → Disjoint (L a c) (L b d)) := by
  classical
  obtain ⟨h, g, c⟩ := hD.exists_isChart
  let φ : Circle ≃ₜ discBd D := (chartBoundaryMap_continuous c).homeoOfEquivCompactToT2
    (f := Equiv.ofBijective (chartBoundaryMap c) (chartBoundaryMap_bijective c))
  have hφ (z : Circle) : GM06.oArcMap φ z = g z := rfl
  have hsphere {x : S} (hx : x ∈ discBd D) : h x ∈ sphere (0 : ℂ) 1 :=
    c.bd ▸ mem_image_of_mem h hx
  have hpoint (x : S) (hx : x ∈ discBd D) : g (h x) = x := c.gh (discBd_subset D hx)
  let L : S → S → Set S := fun a b ↦ g '' segment ℝ (h a) (h b)
  have hgeom {a b : S} (ha : a ∈ discBd D) (hb : b ∈ discBd D) (hab : a ≠ b) :=
    GM12.unit_chord_geometry (mem_sphere_zero_iff_norm.mp (hsphere ha))
      (mem_sphere_zero_iff_norm.mp (hsphere hb))
      (show h a ≠ h b from fun he ↦ hab ((hpoint a ha).symm.trans ((congrArg g he).trans (hpoint b hb))))
  refine ⟨L, ?_, ?_⟩
  · intro a ha b hb hab
    have hg := hgeom ha hb hab
    refine ⟨?_, c.g_subset hg.2.1, ?_⟩
    · have hl := line_image hg.1 (c.gc.mono hg.2.1) (c.injOn.mono hg.2.1)
      rwa [hpoint a ha, hpoint b hb] at hl
    · change g '' segment ℝ (h a) (h b) ∩ discBd D = _
      rw [← c.g_sphere, ← c.g_inter hg.2.1 sphere_subset_closedBall, hg.2.2,
        Set.image_pair, hpoint a ha, hpoint b hb]
  · intro a ha cc hc b hb d hd hac hbd hab had hcb hcd hnc
    let ac : Circle := ⟨h a, hsphere ha⟩
    let ccc : Circle := ⟨h cc, hsphere hc⟩
    let bc : Circle := ⟨h b, hsphere hb⟩
    let dc : Circle := ⟨h d, hsphere hd⟩
    have hne {x y : S} (hx : x ∈ discBd D) (hy : y ∈ discBd D) (hne : x ≠ y) :
        h x ≠ h y := fun he ↦ hne ((hpoint x hx).symm.trans ((congrArg g he).trans (hpoint y hy)))
    have hnot : ¬ GM06.CrossesOn (univ : Set Circle) ac ccc bc dc := by
      intro hcr
      have hcr' := (GM06.crossesOn_oArcMap_iff φ).mpr hcr
      simp only [hφ] at hcr'
      exact hnc (by simpa only [ac, ccc, bc, dc, hpoint a ha, hpoint cc hc,
                    hpoint b hb, hpoint d hd] using hcr')
    have hdis := unit_chords_disjoint_of_not_crosses
      (fun he ↦ hne ha hc hac (congrArg Subtype.val he))
      (fun he ↦ hne hb hd hbd (congrArg Subtype.val he))
      (fun he ↦ hne ha hb hab (congrArg Subtype.val he))
      (fun he ↦ hne ha hd had (congrArg Subtype.val he))
      (fun he ↦ hne hc hb hcb (congrArg Subtype.val he))
      (fun he ↦ hne hc hd hcd (congrArg Subtype.val he)) hnot
    apply Set.disjoint_left.mpr
    rintro z ⟨x, hx, hxz⟩ ⟨y, hy, hyz⟩
    have hxy : x = y := c.injOn ((hgeom ha hc hac).2.1 hx)
      ((hgeom hb hd hbd).2.1 hy) (hxz.trans hyz.symm)
    exact Set.disjoint_left.mp hdis hx (hxy.symm ▸ hy)

end GraphMinor.GM04
