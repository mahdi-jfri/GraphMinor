module

public import GraphMinor.GM08.Section18CircleTouch
import GraphMinor.GM08.Section18X2Disc
import GraphMinor.GM08.Section18CutBoundary
import GraphMinor.GM08.Section6Loop
import GraphMinor.GM08.Section18PinchedSides
import GraphMinor.GM08.Section18DiscPiece
import GraphMinor.GM12.Section4ChordGeometry
import GraphMinor.GM12.Section3CircleInclusion
import GraphMinor.GM07.CuffCells
import GraphMinor.GM07.CutBounds
import GraphMinor.GM07.CapMap
import GraphMinor.Surface.DiscArcs
import GraphMinor.Surface.DiscUnion
import GraphMinor.Surface.DiscGrow
import GraphMinor.Surface.ArcTools
import GraphMinor.Surface.CutLift
import GraphMinor.Surface.CutComp
import GraphMinor.Surface.SurfaceGraph

/-!
# The pinched disc

This file proves `PinchedDiscStatement`, the last open case of (18.2).

Let `Z` be a circle that meets `bd(Σ)` only at `p`, and let `C` be the cuff
through `p`. Cut along `Z`. Suppose the cut surface has a piece `D` that is a
closed disc, holds two points `q₁, q₂` over `p`, and holds one point over each
other point of `Z`. We show that `Z` is planar once `C` is capped.

First we find the boundary circle of `D`. It is the union of two lines from
`q₁` to `q₂`: a line `L` whose image holds `Z`, and a line `L'` whose image
lies in `C` (`exists_pinched_disc_bd`).

Then we cut `D` by a chord from a point `r` inside `L'` to a point `w` inside
`L`. This splits `D` into two closed discs `D₁ ∋ q₁` and `D₂ ∋ q₂`
(`Surface.disc_iArc`). The cut map is one to one on each of them. Cap `C` with
a disc `Δ`. The image of `D₁` meets `Δ` in the image of the part of `L'` from
`q₁` to `r`, so their union is a closed disc (`Surface.disc_union`). The image
of `D₂` meets this disc in the image of the chord and the part of `L'` from `r`
to `q₂`, so the union of all three is again a closed disc. It holds the image
of `Z`. So `Z` is planar after `C` is capped.
-/

@[expose] public section

namespace GraphMinor.GM08

open Set Topology GraphMinor.Surface GraphMinor.GM11

universe w

section lines

variable {X : Type w} [TopologicalSpace X]

/-- A line without its two ends is connected. -/
theorem isPreconnected_line_sdiff_pair {L : Set X} {u v : X} (h : IsLineWithEnds L u v) :
    IsPreconnected (L \ {u, v}) := by
  obtain ⟨a, ha, hL, h0, h1⟩ := h.exists_arc
  have hY : L \ {u, v} = (a ∘ projIcc (0 : ℝ) 1 zero_le_one) '' Ioo 0 1 := by
    ext x
    constructor
    · rintro ⟨hx, hxuv⟩
      rw [← hL] at hx
      obtain ⟨s, rfl⟩ := hx
      refine ⟨s.1, ⟨lt_of_le_of_ne s.2.1 fun he => hxuv (Or.inl ?_),
        lt_of_le_of_ne s.2.2 fun he => hxuv (Or.inr ?_)⟩, ?_⟩
      · rw [← h0]
        exact congrArg a (Subtype.ext he.symm)
      · rw [← h1]
        exact congrArg a (Subtype.ext he)
      · simp
    · rintro ⟨t, ht, rfl⟩
      refine ⟨hL ▸ mem_range_self _, ?_⟩
      rintro (he | he)
      · rw [← h0] at he
        have := congrArg Subtype.val (ha.2 he)
        simp [projIcc_of_mem _ ⟨ht.1.le, ht.2.le⟩] at this
        exact ht.1.ne' this
      · rw [← h1] at he
        have := congrArg Subtype.val (ha.2 he)
        simp [projIcc_of_mem _ ⟨ht.1.le, ht.2.le⟩] at this
        exact ht.2.ne this
  rw [hY]
  exact isPreconnected_Ioo.image _ (ha.1.comp continuous_projIcc).continuousOn

/-- A line without its far end is connected. -/
theorem isPreconnected_line_sdiff_right {L : Set X} {u v : X} (h : IsLineWithEnds L u v) :
    IsPreconnected (L \ {v}) := by
  obtain ⟨a, ha, hL, h0, h1⟩ := h.exists_arc
  have hY : L \ {v} = (a ∘ projIcc (0 : ℝ) 1 zero_le_one) '' Ico 0 1 := by
    ext x
    constructor
    · rintro ⟨hx, hxv⟩
      rw [← hL] at hx
      obtain ⟨s, rfl⟩ := hx
      refine ⟨s.1, ⟨s.2.1, lt_of_le_of_ne s.2.2 fun he => hxv ?_⟩, ?_⟩
      · rw [← h1]
        exact congrArg a (Subtype.ext he)
      · simp
    · rintro ⟨t, ht, rfl⟩
      refine ⟨hL ▸ mem_range_self _, fun he => ?_⟩
      rw [mem_singleton_iff, ← h1] at he
      have := congrArg Subtype.val (ha.2 he)
      simp [projIcc_of_mem _ ⟨ht.1, ht.2.le⟩] at this
      exact ht.2.ne this
  rw [hY]
  exact isPreconnected_Ico.image _ (ha.1.comp continuous_projIcc).continuousOn

/-- A line has a point other than its ends. -/
theorem exists_mem_line_ne {L : Set X} {u v : X} (h : IsLineWithEnds L u v) :
    ∃ x ∈ L, x ≠ u ∧ x ≠ v := by
  obtain ⟨f, h0, h1⟩ := h
  have hh : (1 / 2 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨by norm_num, by norm_num⟩
  refine ⟨f ⟨1 / 2, hh⟩, (f _).2, fun he => ?_, fun he => ?_⟩
  · have := f.injective (Subtype.ext (he.trans h0.symm))
    have h' := congrArg Subtype.val this
    norm_num at h'
  · have := f.injective (Subtype.ext (he.trans h1.symm))
    have h' := congrArg Subtype.val this
    norm_num at h'

/-- **A chord of a closed disc.** Two different points of the boundary of a
closed disc are the ends of a line in the disc that meets the boundary only at
its ends. In a chart it is a straight chord of the unit disc. -/
theorem exists_chord [T2Space X] {D : Set X} (hD : IsClosedDisc D) {r w : X}
    (hr : r ∈ discBd D) (hw : w ∈ discBd D) (hrw : r ≠ w) :
    ∃ γ, IsLineWithEnds γ r w ∧ γ ⊆ D ∧ γ ∩ discBd D = {r, w} := by
  obtain ⟨h, g, c⟩ := hD.exists_isChart
  have hhr : h r ∈ Metric.sphere (0 : ℂ) 1 := c.bd ▸ mem_image_of_mem h hr
  have hhw : h w ∈ Metric.sphere (0 : ℂ) 1 := c.bd ▸ mem_image_of_mem h hw
  have hgr : g (h r) = r := c.gh (Surface.discBd_subset D hr)
  have hgw : g (h w) = w := c.gh (Surface.discBd_subset D hw)
  have hne : h r ≠ h w := fun e => hrw (by rw [← hgr, e, hgw])
  obtain ⟨hl, hsub, hint⟩ := GM12.unit_chord_geometry (mem_sphere_zero_iff_norm.mp hhr)
    (mem_sphere_zero_iff_norm.mp hhw) hne
  refine ⟨g '' segment ℝ (h r) (h w), ?_, c.g_subset hsub, ?_⟩
  · have := GM07.isLineWithEnds_image hl (c.gc.mono hsub) (c.injOn.mono hsub)
    rwa [hgr, hgw] at this
  · rw [← c.g_sphere, ← c.g_inter hsub Metric.sphere_subset_closedBall, hint, image_pair, hgr,
      hgw]

end lines

section disc

variable {S T : Type w} [TopologicalSpace S] [TopologicalSpace T]

/-- The cut map is one to one on a part `E` of the disc piece that holds at
most one point over `p`. Off `Z` the cut map is one to one. A point of `Z`
other than `p` has two points over it, one outside `D`, so it has only one in
`D`. -/
theorem injOn_of_pinched {Z : Set S} {p : S} {ρ : T → S} {D E : Set T}
    (hρ : GM19.IsCutMap ρ Z) (hρ2 : ∀ z ∈ Z, z ≠ p → (ρ ⁻¹' {z}).ncard = 2)
    (hsides : ∀ z ∈ Z, z ≠ p → (∃ w ∈ D, ρ w = z) ∧ (∃ w ∈ Dᶜ, ρ w = z))
    (hED : E ⊆ D) (hEp : (E ∩ ρ ⁻¹' {p}).Subsingleton) : InjOn ρ E := by
  intro a ha b hb hab
  by_cases hZ : ρ a ∈ Z
  · by_cases hp : ρ a = p
    · exact hEp ⟨ha, hp⟩ ⟨hb, show ρ b = p from hab ▸ hp⟩
    · obtain ⟨w', hw, hwz⟩ := (hsides _ hZ hp).2
      have hs := subsingleton_of_two (hρ.2.2.2.1 _) (hρ2 _ hZ hp) hwz hw
      exact hs ⟨rfl, hED ha⟩ ⟨show ρ b = ρ a from hab.symm, hED hb⟩
  · exact hρ.2.2.1 hZ (show ρ b ∈ Zᶜ from hab ▸ hZ) hab

/-- **The boundary of the pinched disc.** The boundary circle of the disc
piece `D` is the union of two lines `L` and `L'` from `q₁` to `q₂`, the two
points of `D` over `p`. The image of `L` holds `Z`, and the image of `L'` lies
in the cuff through `p`. Inside `L'` no point lies over `Z`, and every point of
`D` over that cuff lies in `L'`. -/
theorem exists_pinched_disc_bd (hS : IsSurface S) (hT : IsSurface T) {Z : Set S} {p : S}
    {ρ : T → S} {D : Set T} (hZ : IsOArc Z) (hZp : Z ∩ bd S = {p}) (hρ : GM19.IsCutMap ρ Z)
    (hρ2 : ∀ z ∈ Z, z ≠ p → (ρ ⁻¹' {z}).ncard = 2) (hD : IsClopen D) (hDdisc : IsClosedDisc D)
    (hD2 : (D ∩ ρ ⁻¹' {p}).ncard = 2)
    (hsides : ∀ z ∈ Z, z ≠ p → (∃ w ∈ D, ρ w = z) ∧ (∃ w ∈ Dᶜ, ρ w = z)) :
    ∃ q₁ q₂ : T, ∃ L L' : Set T, q₁ ≠ q₂ ∧ D ∩ ρ ⁻¹' {p} = {q₁, q₂} ∧
      IsLineWithEnds L q₁ q₂ ∧ IsLineWithEnds L' q₁ q₂ ∧ L ∪ L' = discBd D ∧
      L ∩ L' = {q₁, q₂} ∧ Z ⊆ ρ '' L ∧ ρ '' L' ⊆ connectedComponentIn (bd S) p ∧
      (∀ x ∈ L', ρ x ∈ Z → x = q₁ ∨ x = q₂) ∧
      D ∩ ρ ⁻¹' connectedComponentIn (bd S) p ⊆ L' := by
  have : T2Space S := hS.2.1
  have : T2Space T := hT.2.1
  have : CompactSpace T := hT.1
  have hZc : IsClosed Z := hZ.isCompact.isClosed
  have hcut := isCutAlongSet_of_cutMap hS hT hZc hρ
  have hbdT : ρ ⁻¹' (bd S ∪ Z) = bd T := hcut.preimage_bd
  have hB : discBd D = D ∩ bd T := by
    ext z
    constructor
    · rintro ⟨z', hz', rfl⟩
      exact ⟨z'.2, (mem_bd_sub hD.isOpen).mp hz'⟩
    · rintro ⟨hzD, hzb⟩
      exact ⟨⟨z, hzD⟩, (mem_bd_sub hD.isOpen).mpr hzb, rfl⟩
  have hBO : IsOArc (discBd D) := hDdisc.isOArc_discBd
  have hpZb : p ∈ Z ∩ bd S := hZp.symm ▸ rfl
  have hZbd : ∀ z ∈ Z, z ∈ bd S → z = p := fun z hz hzb =>
    (hZp ▸ ⟨hz, hzb⟩ : z ∈ ({p} : Set S))
  have hliftbd : ∀ x, ρ x ∈ Z → x ∈ bd T := fun x hx => hbdT ▸ Or.inr hx
  obtain ⟨q₁, q₂, hq, hDq⟩ := ncard_eq_two.mp hD2
  have hq₁ : q₁ ∈ D ∩ ρ ⁻¹' {p} := hDq ▸ mem_insert _ _
  have hq₂ : q₂ ∈ D ∩ ρ ⁻¹' {p} := hDq ▸ mem_insert_of_mem _ rfl
  have hp' : ∀ x ∈ D, ρ x = p → x = q₁ ∨ x = q₂ := fun x hx hxp => by
    have : x ∈ D ∩ ρ ⁻¹' {p} := ⟨hx, hxp⟩
    rw [hDq] at this
    exact this
  have hρq₁ : ρ q₁ = p := hq₁.2
  have hρq₂ : ρ q₂ = p := hq₂.2
  have hq₁B : q₁ ∈ discBd D := hB ▸ ⟨hq₁.1, hliftbd _ (hρq₁ ▸ hpZb.1)⟩
  have hq₂B : q₂ ∈ discBd D := hB ▸ ⟨hq₂.1, hliftbd _ (hρq₂ ▸ hpZb.1)⟩
  have hBD : discBd D ⊆ D := Surface.discBd_subset D
  -- every point of `Z` other than `p` has one point over it in `D`, on the boundary
  have hlift : ∀ z ∈ Z, z ≠ p → ∃ y ∈ discBd D, ρ y = z ∧ y ≠ q₁ ∧ y ≠ q₂ := by
    intro z hz hzp
    obtain ⟨y, hyD, hyz⟩ := (hsides z hz hzp).1
    refine ⟨y, hB ▸ ⟨hyD, hliftbd _ (hyz ▸ hz)⟩, hyz, fun h => hzp ?_, fun h => hzp ?_⟩
    · rw [← hyz, h, hρq₁]
    · rw [← hyz, h, hρq₂]
  have huniq : ∀ z ∈ Z, z ≠ p → ∀ a ∈ D, ∀ b ∈ D, ρ a = z → ρ b = z → a = b := by
    intro z hz hzp a ha b hb hza hzb
    obtain ⟨w', hw, hwz⟩ := (hsides z hz hzp).2
    exact subsingleton_of_two (hρ.2.2.2.1 _) (hρ2 _ hz hzp) hwz hw ⟨hza, ha⟩ ⟨hzb, hb⟩
  have hinj : InjOn ρ (D \ {q₂}) := injOn_of_pinched hρ hρ2 hsides sdiff_subset
    fun a ha b hb => by
      rcases hp' a ha.1.1 ha.2, hp' b hb.1.1 hb.2 with ⟨ha' | ha', hb' | hb'⟩
      all_goals first
        | exact ha'.trans hb'.symm
        | exact absurd ha' ha.1.2
        | exact absurd hb' hb.1.2
  -- a point of the boundary other than `q₁, q₂` lies over `Z` or over `bd S`, not both
  have hoff : ∀ x ∈ discBd D, x ≠ q₁ → x ≠ q₂ → ρ x ≠ p := fun x hx h1 h2 hxp => by
    rcases hp' x (hBD hx) hxp with h | h
    · exact h1 h
    · exact h2 h
  -- a line of the boundary lies over `Z` or over `bd S`, away from its ends
  have hside : ∀ P : Set T, IsLineWithEnds P q₁ q₂ → P ⊆ discBd D →
      P \ {q₁, q₂} ⊆ ρ ⁻¹' Z ∨ P \ {q₁, q₂} ⊆ ρ ⁻¹' bd S := by
    intro P hP hPB
    refine isPreconnected_iff_subset_of_disjoint_closed.mp (isPreconnected_line_sdiff_pair hP) _ _
      (hZc.preimage hρ.1) ((isClosed_bd S).preimage hρ.1) ?_ ?_
    · rintro x ⟨hxP, -⟩
      have : x ∈ bd T := (hB ▸ hPB hxP : x ∈ D ∩ bd T).2
      rw [← hbdT] at this
      exact this.symm
    · ext x
      simp only [mem_inter_iff, mem_empty_iff_false, iff_false, not_and]
      rintro ⟨hxP, hxq⟩ hxZ hxb
      refine hoff x (hPB hxP) (fun h => hxq (Or.inl h)) (fun h => hxq (Or.inr h)) ?_
      exact hZbd _ hxZ hxb
  -- a line of the boundary that lies over `Z` maps onto `Z`
  have himg : ∀ P : Set T, IsLineWithEnds P q₁ q₂ → P ⊆ discBd D →
      P \ {q₁, q₂} ⊆ ρ ⁻¹' Z → ρ '' P = Z := by
    intro P hP hPB hPZ
    obtain ⟨a, ha, hPa, h0, h1⟩ := hP.exists_arc
    let g : ℝ → S := ρ ∘ a ∘ projIcc (0 : ℝ) 1 zero_le_one
    have hg : Continuous g := hρ.1.comp (ha.1.comp continuous_projIcc)
    have hends : g 0 = g 1 := by
      simp only [g, Function.comp_apply, projIcc_left, projIcc_right]
      exact ((congrArg ρ h0).trans hρq₁).trans ((congrArg ρ h1).trans hρq₂).symm
    have hginj : InjOn g (Ico 0 1) := by
      intro s hs t ht hst
      have hs' : s ∈ Icc (0 : ℝ) 1 := ⟨hs.1, hs.2.le⟩
      have ht' : t ∈ Icc (0 : ℝ) 1 := ⟨ht.1, ht.2.le⟩
      have hmem : ∀ u ∈ Ico (0 : ℝ) 1, a (projIcc 0 1 zero_le_one u) ∈ D \ {q₂} := by
        intro u hu
        refine ⟨hBD (hPB (hPa ▸ mem_range_self _)), fun he => ?_⟩
        rw [← h1] at he
        have := congrArg Subtype.val (ha.2 he)
        simp [projIcc_of_mem _ ⟨hu.1, hu.2.le⟩] at this
        exact hu.2.ne this
      have := ha.2 (hinj (hmem s hs) (hmem t ht) hst)
      have := congrArg Subtype.val this
      simpa [projIcc_of_mem _ hs', projIcc_of_mem _ ht'] using this
    have hO := isOArc_image_of_simple_loop hg hends hginj
    have himage : g '' Icc 0 1 = ρ '' P := by
      rw [← hPa]
      ext x
      constructor
      · rintro ⟨s, -, rfl⟩
        exact ⟨_, mem_range_self _, rfl⟩
      · rintro ⟨_, ⟨t, rfl⟩, rfl⟩
        refine ⟨t.1, t.2, ?_⟩
        simp [g]
    rw [himage] at hO
    refine GM12.oArc_eq_of_subset hO hZ ?_
    rintro _ ⟨x, hx, rfl⟩
    by_cases hxq : x ∈ ({q₁, q₂} : Set T)
    · rcases hxq with rfl | rfl
      · exact hρq₁ ▸ hpZb.1
      · exact hρq₂ ▸ hpZb.1
    · exact hPZ ⟨hx, hxq⟩
  obtain ⟨z₀, hz₀Z, hz₀p⟩ := hZ.exists_ne p
  -- the main case, for a line `P` over `Z` and a line `Q` over `bd S`
  have key : ∀ P Q : Set T, IsLineWithEnds P q₁ q₂ → IsLineWithEnds Q q₁ q₂ →
      P ∪ Q = discBd D → P ∩ Q = {q₁, q₂} → P \ {q₁, q₂} ⊆ ρ ⁻¹' Z →
      Q \ {q₁, q₂} ⊆ ρ ⁻¹' bd S →
      Z ⊆ ρ '' P ∧ ρ '' Q ⊆ connectedComponentIn (bd S) p ∧
      (∀ x ∈ Q, ρ x ∈ Z → x = q₁ ∨ x = q₂) ∧
      D ∩ ρ ⁻¹' connectedComponentIn (bd S) p ⊆ Q := by
    intro P Q hP hQ hPQ hPQi hPZ hQb
    have hQZ : ∀ x ∈ Q, ρ x ∈ Z → x = q₁ ∨ x = q₂ := by
      intro x hx hxZ
      by_contra hxq
      have hxq' : x ∉ ({q₁, q₂} : Set T) := hxq
      exact hoff x (hPQ ▸ Or.inr hx) (fun h => hxq (Or.inl h)) (fun h => hxq (Or.inr h))
        (hZbd _ hxZ (hQb ⟨hx, hxq'⟩))
    refine ⟨fun z hz => ?_, ?_, hQZ, ?_⟩
    · by_cases hzp : z = p
      · exact ⟨q₁, hP.left_mem, hzp ▸ hρq₁⟩
      obtain ⟨y, hyB, hyz, hy1, hy2⟩ := hlift z hz hzp
      rw [← hPQ] at hyB
      rcases hyB with hy | hy
      · exact ⟨y, hy, hyz⟩
      · rcases hQZ y hy (hyz ▸ hz) with h | h
        · exact absurd h hy1
        · exact absurd h hy2
    · refine ((line_isPreconnected hQ).image ρ hρ.1.continuousOn).subset_connectedComponentIn
        ⟨q₁, hQ.left_mem, hρq₁⟩ ?_
      rintro _ ⟨x, hx, rfl⟩
      by_cases hxq : x ∈ ({q₁, q₂} : Set T)
      · rcases hxq with rfl | rfl
        · exact hρq₁ ▸ hpZb.2
        · exact hρq₂ ▸ hpZb.2
      · exact hQb ⟨hx, hxq⟩
    · rintro x ⟨hxD, hxC⟩
      have hxb : ρ x ∈ bd S := connectedComponentIn_subset _ _ hxC
      have hxB : x ∈ discBd D := hB ▸ ⟨hxD, hbdT ▸ Or.inl hxb⟩
      rw [← hPQ] at hxB
      rcases hxB with hx | hx
      · by_cases hxq : x ∈ ({q₁, q₂} : Set T)
        · rcases hxq with rfl | rfl
          · exact hQ.left_mem
          · exact hQ.right_mem
        · exfalso
          refine hoff x (hPQ ▸ Or.inl hx) (fun h => hxq (Or.inl h)) (fun h => hxq (Or.inr h)) ?_
          exact hZbd _ (hPZ ⟨hx, hxq⟩) hxb
      · exact hx
  obtain ⟨L, L', hL, hL', hLL, hLi⟩ := hBO.lines hq₁B hq₂B hq
  have hLB : L ⊆ discBd D := hLL ▸ subset_union_left
  have hL'B : L' ⊆ discBd D := hLL ▸ subset_union_right
  rcases hside L hL hLB with hLZ | hLb <;> rcases hside L' hL' hL'B with hL'Z | hL'b
  · -- both lines lie over `Z`: then `z₀` has two points over it in `D`
    exfalso
    obtain ⟨y, hy, hyz⟩ := (himg L hL hLB hLZ).symm ▸ hz₀Z
    obtain ⟨y', hy', hyz'⟩ := (himg L' hL' hL'B hL'Z).symm ▸ hz₀Z
    have hyy : y = y' := huniq z₀ hz₀Z hz₀p y (hBD (hLB hy)) y' (hBD (hL'B hy')) hyz hyz'
    have : y ∈ L ∩ L' := ⟨hy, hyy ▸ hy'⟩
    rw [hLi] at this
    rcases this with rfl | rfl
    · exact hz₀p (hyz.symm.trans hρq₁)
    · exact hz₀p (hyz.symm.trans hρq₂)
  · obtain ⟨h1, h2, h3, h4⟩ := key L L' hL hL' hLL hLi hLZ hL'b
    exact ⟨q₁, q₂, L, L', hq, hDq, hL, hL', hLL, hLi, h1, h2, h3, h4⟩
  · obtain ⟨h1, h2, h3, h4⟩ := key L' L hL' hL (union_comm L L' ▸ hLL) (inter_comm L L' ▸ hLi)
      hL'Z hLb
    exact ⟨q₁, q₂, L', L, hq, hDq, hL', hL, union_comm L L' ▸ hLL, inter_comm L L' ▸ hLi, h1, h2,
      h3, h4⟩
  · -- both lines lie over `bd S`: then `z₀` has no point over it on the boundary of `D`
    exfalso
    obtain ⟨y, hyB, hyz, hy1, hy2⟩ := hlift z₀ hz₀Z hz₀p
    have hyq : y ∉ ({q₁, q₂} : Set T) := by
      rintro (h | h)
      · exact hy1 h
      · exact hy2 h
    rw [← hLL] at hyB
    have hyb : ρ y ∈ bd S := by
      rcases hyB with hy | hy
      · exact hLb ⟨hy, hyq⟩
      · exact hL'b ⟨hy, hyq⟩
    exact hz₀p (hZbd _ (hyz ▸ hz₀Z) hyb ▸ hyz.symm)

/-- **The pinched disc.** If the disc piece of the pinched cut holds two
points over the touched point `p`, then `Z` is planar once the cuff through
`p` is capped, so `Z` is near-planar. -/
theorem pinchedDiscStatement : PinchedDiscStatement.{w} := by
  intro S T _ _ _ hS hT Z p ρ D hZ hZp hρ _ hρ2 hD hDdisc _ hD2 _ hsides
  have : T2Space S := hS.2.1
  have : T2Space T := hT.2.1
  obtain ⟨q₁, q₂, L, L', hq, hDq, hL, hL', hLL, hLi, hZL, hL'C, hL'Z, hDC⟩ :=
    exists_pinched_disc_bd hS hT hZ hZp hρ hρ2 hD hDdisc hD2 hsides
  set C := connectedComponentIn (bd S) p with hCdef
  have hpZb : p ∈ Z ∩ bd S := hZp.symm ▸ rfl
  have hC : IsCuff C := ⟨p, hpZb.2, rfl⟩
  obtain ⟨S', tS', j, Δ, hc, -⟩ := GM07.exists_cappedCuff hS hC
  have : T2Space S' := hc.isSurface.2.1
  refine Or.inr ⟨C, hC, GM07.isPlanarInCappedCuff_of_cap hS hc ?_⟩
  have hjinj : Function.Injective j := hc.isEmbedding.injective
  have hθc : Continuous (j ∘ ρ) := hc.isEmbedding.continuous.comp hρ.1
  -- points over `C` go into the cap, and only they do
  have hCΔ : ∀ x, ρ x ∈ C → j (ρ x) ∈ discBd Δ := fun x hx => hc.discBd_eq ▸ ⟨ρ x, hx, rfl⟩
  have hΔC : ∀ x, j (ρ x) ∈ Δ → ρ x ∈ C := fun x hx => by
    have : j (ρ x) ∈ range j ∩ Δ := ⟨mem_range_self _, hx⟩
    rw [hc.inter_eq] at this
    obtain ⟨c, hcC, hcx⟩ := this
    exact hjinj hcx ▸ hcC
  have hΔsub : discBd Δ ⊆ Δ := Surface.discBd_subset Δ
  -- the basic facts about the boundary circle `B` of `D`
  have hBD : discBd D ⊆ D := Surface.discBd_subset D
  have hLB : L ⊆ discBd D := hLL ▸ subset_union_left
  have hL'B : L' ⊆ discBd D := hLL ▸ subset_union_right
  have hq₁ : q₁ ∈ D ∩ ρ ⁻¹' {p} := hDq ▸ mem_insert _ _
  have hq₂ : q₂ ∈ D ∩ ρ ⁻¹' {p} := hDq ▸ mem_insert_of_mem _ rfl
  have hρq₁ : ρ q₁ = p := hq₁.2
  have hρq₂ : ρ q₂ = p := hq₂.2
  have hp' : ∀ x ∈ D, ρ x = p → x = q₁ ∨ x = q₂ := fun x hx hxp => by
    have : x ∈ D ∩ ρ ⁻¹' {p} := ⟨hx, hxp⟩
    rw [hDq] at this
    exact this
  have hinj : InjOn ρ (D \ {q₂}) := injOn_of_pinched hρ hρ2 hsides sdiff_subset
    fun a ha b hb => by
      rcases hp' a ha.1.1 ha.2, hp' b hb.1.1 hb.2 with ⟨ha' | ha', hb' | hb'⟩
      all_goals first
        | exact ha'.trans hb'.symm
        | exact absurd ha' ha.1.2
        | exact absurd hb' hb.1.2
  have hLL' : ∀ x ∈ L, x ∈ L' → x = q₁ ∨ x = q₂ := fun x hx hx' => by
    have : x ∈ L ∩ L' := ⟨hx, hx'⟩
    rw [hLi] at this
    exact this
  -- the ends of the chord: `r` inside `L'` and `w` inside `L`
  obtain ⟨r, hrL', hr1, hr2⟩ := exists_mem_line_ne hL'
  obtain ⟨w', hwL, hw1, hw2⟩ := exists_mem_line_ne hL
  have hrL : r ∉ L := fun h => (hLL' r h hrL').elim hr1 hr2
  have hwL' : w' ∉ L' := fun h => (hLL' w' hwL h).elim hw1 hw2
  have hrw : r ≠ w' := fun h => hrL (h ▸ hwL)
  obtain ⟨M₁, M₂, hM₁, hM₂, hM, hMi⟩ := hL'.split hrL' hr1 hr2
  obtain ⟨N₁, N₂, hN₁, hN₂, hN, hNi⟩ := hL.split hwL hw1 hw2
  have hM₁L' : M₁ ⊆ L' := hM ▸ subset_union_left
  have hM₂L' : M₂ ⊆ L' := hM ▸ subset_union_right
  have hN₁L : N₁ ⊆ L := hN ▸ subset_union_left
  have hN₂L : N₂ ⊆ L := hN ▸ subset_union_right
  obtain ⟨γ, hγ, hγD, hγB⟩ := exists_chord hDdisc (hL'B hrL') (hLB hwL) hrw
  have hγB' : ∀ x ∈ γ, x ∈ discBd D → x = r ∨ x = w' := fun x hx hxB => by
    have : x ∈ γ ∩ discBd D := ⟨hx, hxB⟩
    rw [hγB] at this
    exact this
  have hrγ : r ∈ γ := hγ.left_mem
  -- the two parts of the boundary without `r, w`
  set F := discBd D \ {r, w'} with hFdef
  set K₁ := connectedComponentIn F q₁
  set K₂ := connectedComponentIn F q₂
  have hq₁F : q₁ ∈ F := ⟨hL'B hL'.left_mem, by
    rintro (h | h)
    · exact hr1 h.symm
    · exact hw1 h.symm⟩
  have hq₂F : q₂ ∈ F := ⟨hL'B hL'.right_mem, by
    rintro (h | h)
    · exact hr2 h.symm
    · exact hw2 h.symm⟩
  have hsubK : ∀ {P : Set T} {a b : T}, IsLineWithEnds P a b → P ⊆ discBd D → a ∈ F →
      (∀ x ∈ P, (x = r ∨ x = w') → x = b) → P \ {b} ⊆ connectedComponentIn F a := by
    intro P a b hP hPB haF hPb
    refine (isPreconnected_line_sdiff_right hP).subset_connectedComponentIn
      ⟨hP.left_mem, hP.ne'⟩ ?_
    rintro x ⟨hxP, hxb⟩
    exact ⟨hPB hxP, fun h => hxb (hPb x hxP h)⟩
  have hK₁M : M₁ \ {r} ⊆ K₁ := hsubK hM₁ (hM₁L'.trans hL'B) hq₁F fun x hx h =>
    h.elim id fun h' => absurd (h' ▸ hM₁L' hx) hwL'
  have hK₁N : N₁ \ {w'} ⊆ K₁ := hsubK hN₁ (hN₁L.trans hLB) hq₁F fun x hx h =>
    h.elim (fun h' => absurd (h' ▸ hN₁L hx) hrL) id
  have hK₂M : M₂ \ {r} ⊆ K₂ := hsubK hM₂.symm (hM₂L'.trans hL'B) hq₂F fun x hx h =>
    h.elim id fun h' => absurd (h' ▸ hM₂L' hx) hwL'
  have hK₂N : N₂ \ {w'} ⊆ K₂ := hsubK hN₂.symm (hN₂L.trans hLB) hq₂F fun x hx h =>
    h.elim (fun h' => absurd (h' ▸ hN₂L hx) hrL) id
  have hcover : F ⊆ K₁ ∪ K₂ := by
    rintro x ⟨hxB, hxrw⟩
    have hxr : x ≠ r := fun h => hxrw (Or.inl h)
    have hxw : x ≠ w' := fun h => hxrw (Or.inr h)
    rw [← hLL, ← hM, ← hN] at hxB
    rcases hxB with (hx | hx) | (hx | hx)
    · exact Or.inl (hK₁N ⟨hx, hxw⟩)
    · exact Or.inr (hK₂N ⟨hx, hxw⟩)
    · exact Or.inl (hK₁M ⟨hx, hxr⟩)
    · exact Or.inr (hK₂M ⟨hx, hxr⟩)
  -- split `D` by the chord, and name the two discs so that `D₁` holds `K₁`
  obtain ⟨A₁, A₂, Δ₁, Δ₂, hA, hcomp, hΔ₁, hΔ₂, hΔU, hΔI, hbd₁, hbd₂, -⟩ :=
    disc_iArc D γ r w' hDdisc hγD hrw hγ hγB
  have hcompK : ∀ x ∈ F, connectedComponentIn F x = K₁ ∨ connectedComponentIn F x = K₂ := by
    intro x hx
    rcases hcover hx with h | h
    · exact Or.inl (connectedComponentIn_eq h).symm
    · exact Or.inr (connectedComponentIn_eq h).symm
  have hKA : ∀ K ∈ componentsIn F, K = A₁ ∨ K = A₂ := fun K hK => by
    rw [hcomp] at hK
    exact hK
  have hA' : ∀ A ∈ componentsIn F, A = K₁ ∨ A = K₂ := by
    rintro A ⟨x, hx, rfl⟩
    exact hcompK x hx
  have hK₁c : K₁ ∈ componentsIn F := ⟨q₁, hq₁F, rfl⟩
  have hK₂c : K₂ ∈ componentsIn F := ⟨q₂, hq₂F, rfl⟩
  have hA₁c : A₁ ∈ componentsIn F := hcomp ▸ mem_insert _ _
  have hA₂c : A₂ ∈ componentsIn F := hcomp ▸ mem_insert_of_mem _ rfl
  obtain ⟨E₁, E₂, hE₁, hE₂, hEU, hEI, hbdE₁, hbdE₂⟩ : ∃ E₁ E₂ : Set T,
      IsClosedDisc E₁ ∧ IsClosedDisc E₂ ∧ E₁ ∪ E₂ = D ∧ E₁ ∩ E₂ = γ ∧
      discBd E₁ = K₁ ∪ γ ∧ discBd E₂ = K₂ ∪ γ := by
    rcases hKA K₁ hK₁c with h1 | h1 <;> rcases hKA K₂ hK₂c with h2 | h2
    · exfalso
      rcases hA' A₂ hA₂c with h | h
      · exact hA (h1.symm.trans h.symm)
      · exact hA (h2.symm.trans h.symm)
    · exact ⟨Δ₁, Δ₂, hΔ₁, hΔ₂, hΔU, hΔI, h1 ▸ hbd₁, h2 ▸ hbd₂⟩
    · exact ⟨Δ₂, Δ₁, hΔ₂, hΔ₁, union_comm Δ₁ Δ₂ ▸ hΔU, inter_comm Δ₁ Δ₂ ▸ hΔI, h1 ▸ hbd₂,
        h2 ▸ hbd₁⟩
    · exfalso
      rcases hA' A₁ hA₁c with h | h
      · exact hA (h.trans h1)
      · exact hA (h.trans h2)
  -- facts about the two discs
  have hE₁D : E₁ ⊆ D := hEU ▸ subset_union_left
  have hE₂D : E₂ ⊆ D := hEU ▸ subset_union_right
  have hbE₁ : discBd E₁ ⊆ E₁ := Surface.discBd_subset E₁
  have hbE₂ : discBd E₂ ⊆ E₂ := Surface.discBd_subset E₂
  have hγE₁ : γ ⊆ discBd E₁ := hbdE₁ ▸ subset_union_right
  have hγE₂ : γ ⊆ discBd E₂ := hbdE₂ ▸ subset_union_right
  have hK₁E₁ : K₁ ⊆ discBd E₁ := hbdE₁ ▸ subset_union_left
  have hK₂E₂ : K₂ ⊆ discBd E₂ := hbdE₂ ▸ subset_union_left
  have hKF₁ : K₁ ⊆ F := connectedComponentIn_subset _ _
  have hKF₂ : K₂ ⊆ F := connectedComponentIn_subset _ _
  have hM₁E₁ : M₁ ⊆ discBd E₁ := fun x hx => by
    by_cases hxr : x = r
    · exact hγE₁ (hxr ▸ hrγ)
    · exact hK₁E₁ (hK₁M ⟨hx, hxr⟩)
  have hM₂E₂ : M₂ ⊆ discBd E₂ := fun x hx => by
    by_cases hxr : x = r
    · exact hγE₂ (hxr ▸ hrγ)
    · exact hK₂E₂ (hK₂M ⟨hx, hxr⟩)
  -- a point of `F` in both discs is impossible
  have hFboth : ∀ x ∈ F, x ∈ E₁ → x ∈ E₂ → False := fun x hxF h1 h2 => by
    have hxγ : x ∈ γ := hEI ▸ ⟨h1, h2⟩
    exact hxF.2 (hγB' x hxγ hxF.1)
  have hK₂E₁ : ∀ x ∈ K₂, x ∉ E₁ := fun x hx h => hFboth x (hKF₂ hx) h (hbE₂ (hK₂E₂ hx))
  have hK₁E₂ : ∀ x ∈ K₁, x ∉ E₂ := fun x hx h => hFboth x (hKF₁ hx) (hbE₁ (hK₁E₁ hx)) h
  have hq₂E₁ : q₂ ∉ E₁ := hK₂E₁ q₂ (mem_connectedComponentIn hq₂F)
  have hq₁E₂ : q₁ ∉ E₂ := hK₁E₂ q₁ (mem_connectedComponentIn hq₁F)
  have hE₁L' : ∀ x ∈ E₁, x ∈ L' → x ∈ M₁ := fun x hx hxL' => by
    rw [← hM] at hxL'
    rcases hxL' with h | h
    · exact h
    · by_cases hxr : x = r
      · exact hxr ▸ hM₁.right_mem
      · exact absurd hx (hK₂E₁ x (hK₂M ⟨h, hxr⟩))
  have hE₂L' : ∀ x ∈ E₂, x ∈ L' → x ∈ M₂ := fun x hx hxL' => by
    rw [← hM] at hxL'
    rcases hxL' with h | h
    · by_cases hxr : x = r
      · exact hxr ▸ hM₂.left_mem
      · exact absurd hx (hK₁E₂ x (hK₁M ⟨h, hxr⟩))
    · exact h
  -- the cut map is one to one on each disc
  have hinj₁ : InjOn ρ E₁ := hinj.mono fun x hx =>
    (⟨hE₁D hx, fun h => hq₂E₁ (mem_singleton_iff.mp h ▸ hx)⟩ : x ∈ D \ {q₂})
  have hinj₂ : InjOn ρ E₂ := injOn_of_pinched hρ hρ2 hsides hE₂D fun a ha b hb => by
    rcases hp' a (hE₂D ha.1) ha.2 with rfl | rfl <;>
      rcases hp' b (hE₂D hb.1) hb.2 with rfl | rfl
    all_goals first | rfl | exact absurd ha.1 hq₁E₂ | exact absurd hb.1 hq₁E₂
  have hθ₁ : InjOn (j ∘ ρ) E₁ := hjinj.comp_injOn hinj₁
  have hθ₂ : InjOn (j ∘ ρ) E₂ := hjinj.comp_injOn hinj₂
  obtain ⟨hG₁, hbG₁⟩ := isClosedDisc_image_of_injOn hθc hE₁ hθ₁
  obtain ⟨hG₂, hbG₂⟩ := isClosedDisc_image_of_injOn hθc hE₂ hθ₂
  -- first union: the image of `E₁` and the cap meet in the image of `M₁`
  have hℓ₁ : IsLineWithEnds ((j ∘ ρ) '' M₁) (j p) (j (ρ r)) := by
    have := GM07.isLineWithEnds_image hM₁ hθc.continuousOn
      (hθ₁.mono (hM₁E₁.trans hbE₁))
    simpa [hρq₁] using this
  have hI₁ : (j ∘ ρ) '' E₁ ∩ Δ = (j ∘ ρ) '' M₁ := by
    ext y
    constructor
    · rintro ⟨⟨x, hx, rfl⟩, hyΔ⟩
      have hxC := hΔC x hyΔ
      exact ⟨x, hE₁L' x hx (hDC ⟨hE₁D hx, hxC⟩), rfl⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨⟨x, hbE₁ (hM₁E₁ hx), rfl⟩,
        hΔsub (hCΔ x (hL'C ⟨x, hM₁L' hx, rfl⟩))⟩
  obtain ⟨hH₁, hbH₁⟩ := disc_union _ _ _ _ _ hG₁ hc.isClosedDisc hℓ₁ hI₁
    (hbG₁ ▸ image_mono hM₁E₁)
    (by rintro _ ⟨x, hx, rfl⟩; exact hCΔ x (hL'C ⟨x, hM₁L' hx, rfl⟩))
  -- second union: the image of `E₂` meets that disc in the image of `γ ∪ M₂`
  have hγM₂ : γ ∩ M₂ = {r} := by
    ext x
    constructor
    · rintro ⟨hxγ, hxM⟩
      rcases hγB' x hxγ (hL'B (hM₂L' hxM)) with h | h
      · exact h
      · exact absurd (h ▸ hM₂L' hxM) hwL'
    · rintro rfl
      exact ⟨hrγ, hM₂.left_mem⟩
  have hγM₂l : IsLineWithEnds (γ ∪ M₂) w' q₂ := hγ.symm.union hM₂ hγM₂
  have hγM₂E₂ : γ ∪ M₂ ⊆ discBd E₂ := union_subset hγE₂ hM₂E₂
  have hℓ₂ : IsLineWithEnds ((j ∘ ρ) '' (γ ∪ M₂)) (j (ρ w')) (j p) := by
    have := GM07.isLineWithEnds_image hγM₂l hθc.continuousOn (hθ₂.mono (hγM₂E₂.trans hbE₂))
    simpa [hρq₂] using this
  have hI₂ : ((j ∘ ρ) '' E₁ ∪ Δ) ∩ (j ∘ ρ) '' E₂ = (j ∘ ρ) '' (γ ∪ M₂) := by
    ext y
    constructor
    · rintro ⟨hy1 | hy1, ⟨x, hx, rfl⟩⟩
      · obtain ⟨x', hx', hxx⟩ := hy1
        have hρx : ρ x' = ρ x := hjinj hxx
        by_cases hxq : x = q₂
        · exact ⟨x, Or.inr (hxq ▸ hM₂.right_mem), rfl⟩
        · have : x' = x := hinj ⟨hE₁D hx', fun h => hq₂E₁ (h ▸ hx')⟩
            ⟨hE₂D hx, hxq⟩ hρx
          exact ⟨x, Or.inl (hEI ▸ ⟨this ▸ hx', hx⟩), rfl⟩
      · exact ⟨x, Or.inr (hE₂L' x hx (hDC ⟨hE₂D hx, hΔC x hy1⟩)), rfl⟩
    · rintro ⟨x, hx, rfl⟩
      refine ⟨?_, x, hbE₂ (hγM₂E₂ hx), rfl⟩
      rcases hx with hx | hx
      · exact Or.inl ⟨x, hbE₁ (hγE₁ hx), rfl⟩
      · exact Or.inr (hΔsub (hCΔ x (hL'C ⟨x, hM₂L' hx, rfl⟩)))
  have hℓ₂H₁ : (j ∘ ρ) '' (γ ∪ M₂) ⊆ discBd ((j ∘ ρ) '' E₁ ∪ Δ) := by
    rw [hbH₁, hbG₁, hc.discBd_eq]
    rintro _ ⟨x, hx, rfl⟩
    refine ⟨?_, ?_⟩
    · rcases hx with hx | hx
      · exact Or.inl ⟨x, hγE₁ hx, rfl⟩
      · exact Or.inr ⟨ρ x, hL'C ⟨x, hM₂L' hx, rfl⟩, rfl⟩
    · rintro ⟨⟨x'', hx'', hxx⟩, hne⟩
      have hρx : ρ x'' = ρ x := hjinj hxx
      have hxD : x ∈ D := hE₂D (hbE₂ (hγM₂E₂ hx))
      have hx''D : x'' ∈ D := hBD (hL'B (hM₁L' hx''))
      have hρxp : ρ x ≠ p := fun h => hne (Or.inl (by simp [h]))
      have hxq : x ≠ q₂ := fun h => hρxp (h ▸ hρq₂)
      have hx''q : x'' ≠ q₂ := fun h => hρxp (hρx ▸ h ▸ hρq₂)
      have hxx' : x'' = x := hinj ⟨hx''D, hx''q⟩ ⟨hxD, hxq⟩ hρx
      subst hxx'
      have hxr : x'' ≠ r := fun h => hne (Or.inr (by simp [h]))
      rcases hx with hx | hx
      · rcases hγB' x'' hx (hL'B (hM₁L' hx'')) with h | h
        · exact hxr h
        · exact hwL' (h ▸ hM₁L' hx'')
      · have : x'' ∈ M₁ ∩ M₂ := ⟨hx'', hx⟩
        rw [hMi] at this
        exact hxr this
  obtain ⟨hH, -⟩ := disc_union _ _ _ _ _ hH₁ hG₂ hℓ₂ hI₂ hℓ₂H₁ (hbG₂ ▸ image_mono hγM₂E₂)
  refine ⟨_, hH, ?_⟩
  rintro _ ⟨z, hz, rfl⟩
  obtain ⟨x, hx, rfl⟩ := hZL hz
  have hxD : x ∈ D := hBD (hLB hx)
  rw [← hEU] at hxD
  rcases hxD with h | h
  · exact Or.inl (Or.inl ⟨x, h, rfl⟩)
  · exact Or.inr ⟨x, h, rfl⟩
end disc

/-- **VIII (18.2)**, page 286, with no hypothesis: cutting a connected surface
that is not a sphere, disc or cylinder along a schism lowers `g`. -/
theorem theorem_18_2_proof : Theorem182Statement.{w} :=
  theorem182Statement_of_pinchedDisc pinchedDiscStatement

end GraphMinor.GM08
