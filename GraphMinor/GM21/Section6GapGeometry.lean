module

public import GraphMinor.GM21.Section6ClaimThree
public import GraphMinor.GM21.Section6Restrict
import GraphMinor.GM21.Section6Supports

/-!
# Graph Minors XXI, (6.3), claim (4): a support that holds both ends of the line

Claim (4) of the proof of (6.3) (page 29 of the preprint) cuts `Σ` along a proper line `F`
with ends `a, b` in one cuff `C`. When a support `F_j*` holds both `a` and `b`, the paper's sentence
"there is a presentation of $G_i$ in $\Sigma_i$ of depth $\le q$ and defect $\le r + 1$" needs care:
on one side `F_j*` is cut in two (see the correction to the proof of (6.3) in
`corrections/GM21.md`). This file finds the two pieces.

Write the cuff `C` by angles, with `a, b` at the angles `x < y < x + 2π`. The open arc `M°` of
angles in `(x, y)` and the open arc of angles in `(y, x + 2π)` are connected and miss `F`, so each
lies on one side. They lie on different sides, since no side contains the whole cuff
(`ClaimThree.false_of_cuff_subset_side`). This is `arcs_on_sides`. If `F_j*` is the arc of angles
`[t₀, t₁]` with `t₀ ≤ x < y ≤ t₁`, then on the side of `M°` the support `F_j*` meets the side in the
arc `[x, y]` (`inter_side_eq_of_mid_subset`), and on the other side in the two arcs `[t₀, x]` and
`[y, t₁]` (`inter_side_eq_of_mid_disjoint`).
-/

@[expose] public section

namespace GraphMinor
namespace GM21
namespace Gap

open Set Topology GraphMinor.Surface GraphMinor.GM21.Side GraphMinor.GM19

variable {S : Type*} [TopologicalSpace S] [T2Space S] {Γ : Surface.Drawing S} {S₁ S₂ F : Set S} {a b : S}

omit [T2Space S] in
/-- A cuff lies in `bd(Σ)`. -/
theorem cuff_subset_bd {C : Set S} (hC : C ∈ cuffs S) : C ⊆ bd S := fun z hz => by
  rw [← sUnion_cuffs (S := S)]
  exact ⟨C, hC, hz⟩

omit [T2Space S] in
/-- An open arc of the cuff `C` whose angles miss those of `a` and `b` misses `F`. -/
theorem image_Ioo_disjoint_line (h : IsSideOfLine Γ S₁ S₂ F a b) {C : Set S} (hC : C ∈ cuffs S)
    (f : Circle ≃ₜ C) {x y s t : ℝ} (hxy : x < y) (hy : y < x + 2 * Real.pi)
    (hab : ({cuffPoint f x, cuffPoint f y} : Set S) = {a, b}) (hs : x ≤ s) (ht : t ≤ x + 2 * Real.pi)
    (hxst : x ∉ Ioo s t) (hyst : y ∉ Ioo s t) :
    Disjoint (cuffPoint f '' Ioo s t) F := by
  rw [Set.disjoint_left]
  rintro _ ⟨τ, hτ, rfl⟩ hτF
  have hbd : cuffPoint f τ ∈ F ∩ bd S := ⟨hτF, cuff_subset_bd hC (GM17.cuffPoint_mem f τ)⟩
  rw [h.inter_bd, ← hab] at hbd
  have hτD : τ ∈ Ico x (x + 2 * Real.pi) := ⟨hs.trans hτ.1.le, hτ.2.trans_le ht⟩
  rcases hbd with hτx | hτy
  · have := GM17.cuffPoint_injOn_Ico f x hτD ⟨le_rfl, by linarith [Real.pi_pos]⟩ hτx
    subst this
    exact hxst hτ
  · have := GM17.cuffPoint_injOn_Ico f x hτD ⟨hxy.le, hy⟩ hτy
    subst this
    exact hyst hτ

omit [T2Space S] in
/-- An open arc of angles `(s, t)` is connected. -/
theorem isPreconnected_image_Ioo {C : Set S} (f : Circle ≃ₜ C) (s t : ℝ) :
    IsPreconnected (cuffPoint f '' Ioo s t) :=
  isPreconnected_Ioo.image _ (GM17.cuffPoint_continuous f).continuousOn

/-- **The two arcs of the cuff lie on different sides.** Let `a, b` be the points of the cuff `C`
at angles `x < y < x + 2π`. Either the arc of angles `(x, y)` lies in `S₁` and the arc of angles
`(y, x + 2π)` misses `S₁`, or the other way round. -/
theorem arcs_on_sides (hS : IsSurface S) (h : IsSideOfLine Γ S₁ S₂ F a b) {C : Set S}
    (hC : C ∈ cuffs S) (haC : a ∈ C) (f : Circle ≃ₜ C) {x y : ℝ} (hxy : x < y)
    (hy : y < x + 2 * Real.pi) (hab : ({cuffPoint f x, cuffPoint f y} : Set S) = {a, b}) :
    (cuffPoint f '' Ioo x y ⊆ S₁ ∧ Disjoint (cuffPoint f '' Ioo y (x + 2 * Real.pi)) S₁) ∨
      (Disjoint (cuffPoint f '' Ioo x y) S₁ ∧ cuffPoint f '' Ioo y (x + 2 * Real.pi) ⊆ S₁) := by
  have hc₁ := h.isClosed_left
  have hc₂ := h.isClosed_right
  have hpi := Real.pi_pos
  have hM := Side.subset_or_disjoint_side hc₁ hc₂ h.union_eq h.inter_eq
    (isPreconnected_image_Ioo f x y)
    (image_Ioo_disjoint_line h hC f hxy hy hab le_rfl (by linarith) (fun h' => h'.1.false)
      (fun h' => h'.2.false))
  have hO := Side.subset_or_disjoint_side hc₁ hc₂ h.union_eq h.inter_eq
    (isPreconnected_image_Ioo f y (x + 2 * Real.pi))
    (image_Ioo_disjoint_line h hC f hxy hy hab hxy.le le_rfl (fun h' => by linarith [h'.1])
      (fun h' => h'.1.false))
  -- The points of `C` are the two ends and the points of the two arcs.
  have hcover : ∀ z ∈ C, z ∈ ({a, b} : Set S) ∨ z ∈ cuffPoint f '' Ioo x y ∨
      z ∈ cuffPoint f '' Ioo y (x + 2 * Real.pi) := by
    intro z hz
    obtain ⟨τ, hτ, rfl⟩ := GM17.exists_cuffPoint_mem_Ico f x hz
    rcases hτ.1.lt_or_eq with hxτ | rfl
    · rcases lt_trichotomy τ y with hτy | rfl | hyτ
      · exact Or.inr (Or.inl ⟨τ, ⟨hxτ, hτy⟩, rfl⟩)
      · exact Or.inl (hab ▸ Or.inr rfl)
      · exact Or.inr (Or.inr ⟨τ, ⟨hyτ, hτ.2⟩, rfl⟩)
    · exact Or.inl (hab ▸ Or.inl rfl)
  have habF : ({a, b} : Set S) ⊆ F := by
    rintro z (rfl | rfl)
    · exact h.proper.1.left_mem
    · exact h.proper.1.right_mem
  have hsub₂ : ∀ {X : Set S}, Disjoint X S₁ → X ⊆ S₂ := fun hX =>
    subset_two_of_disjoint h.union_eq hX
  rcases hM with hM | hM <;> rcases hO with hO | hO
  · exfalso
    refine ClaimThree.false_of_cuff_subset_side hS h.surface_left h.surface_right h.union_eq
      h.inter_eq h.proper hC haC fun z hz => ?_
    rcases hcover z hz with hz | hz | hz
    · exact h.line_subset_left (habF hz)
    · exact hM hz
    · exact hO hz
  · exact Or.inl ⟨hM, hO⟩
  · exact Or.inr ⟨hM, hO⟩
  · exfalso
    refine ClaimThree.false_of_cuff_subset_side hS h.surface_right h.surface_left
      (by rw [union_comm, h.union_eq]) (by rw [inter_comm, h.inter_eq]) h.proper hC haC
      fun z hz => ?_
    rcases hcover z hz with hz | hz | hz
    · exact h.line_subset_right (habF hz)
    · exact hsub₂ hM hz
    · exact hsub₂ hO hz

omit [T2Space S] in
/-- **The side of the middle arc.** If `F_j* = f([t₀, t₁])` with `t₀ ≤ x < y ≤ t₁ < t₀ + 2π`, the
ends of `F` at the angles `x, y`, and the arc of angles `(y, x + 2π)` misses `S₁`, then
`F_j* ∩ S₁ = f([x, y])`. -/
theorem inter_side_eq_of_mid_subset (h : IsSideOfLine Γ S₁ S₂ F a b) {C : Set S}
    (f : Circle ≃ₜ C) {t₀ t₁ x y : ℝ} (ht₀ : t₀ ≤ x) (hxy : x < y) (ht₁ : y ≤ t₁)
    (hlt : t₁ < t₀ + 2 * Real.pi)
    (hab : ({cuffPoint f x, cuffPoint f y} : Set S) = {a, b})
    (hO : Disjoint (cuffPoint f '' Ioo y (x + 2 * Real.pi)) S₁) (hM : cuffPoint f '' Ioo x y ⊆ S₁) :
    cuffPoint f '' Icc t₀ t₁ ∩ S₁ = cuffPoint f '' Icc x y := by
  have hpi := Real.pi_pos
  have hend : ∀ {τ : ℝ}, τ = x ∨ τ = y → cuffPoint f τ ∈ S₁ := by
    rintro τ (rfl | rfl)
    · exact h.line_subset_left (by
        have : cuffPoint f τ ∈ ({a, b} : Set S) := hab ▸ Or.inl rfl
        rcases this with h' | h' <;> rw [h']
        exacts [h.proper.1.left_mem, h.proper.1.right_mem])
    · exact h.line_subset_left (by
        have : cuffPoint f τ ∈ ({a, b} : Set S) := hab ▸ Or.inr rfl
        rcases this with h' | h' <;> rw [h']
        exacts [h.proper.1.left_mem, h.proper.1.right_mem])
  ext z
  constructor
  · rintro ⟨⟨τ, hτ, rfl⟩, hτS⟩
    by_cases hτx : τ < x
    · exfalso
      refine disjoint_left.mp hO ⟨τ + 2 * Real.pi, ⟨by linarith [hτ.1], by linarith⟩, ?_⟩ hτS
      exact GM17.cuffPoint_add_two_pi f τ
    by_cases hτy : y < τ
    · exact absurd hτS (disjoint_left.mp hO ⟨τ, ⟨hτy, by linarith [hτ.2]⟩, rfl⟩)
    exact ⟨τ, ⟨not_lt.mp hτx, not_lt.mp hτy⟩, rfl⟩
  · rintro ⟨τ, hτ, rfl⟩
    refine ⟨⟨τ, ⟨ht₀.trans hτ.1, hτ.2.trans ht₁⟩, rfl⟩, ?_⟩
    rcases hτ.1.lt_or_eq with hxτ | hxτ
    · rcases hτ.2.lt_or_eq with hτy | hτy
      · exact hM ⟨τ, ⟨hxτ, hτy⟩, rfl⟩
      · exact hend (Or.inr hτy)
    · exact hend (Or.inl hxτ.symm)

omit [T2Space S] in
/-- **The side of the outer arc.** If `F_j* = f([t₀, t₁])` with `t₀ ≤ x < y ≤ t₁ < t₀ + 2π`, the
ends of `F` at the angles `x, y`, and the arc of angles `(x, y)` misses `S₁` while the arc of angles
`(y, x + 2π)` lies in `S₁`, then `F_j* ∩ S₁ = f([t₀, x]) ∪ f([y, t₁])`. -/
theorem inter_side_eq_of_mid_disjoint (h : IsSideOfLine Γ S₁ S₂ F a b) {C : Set S}
    (f : Circle ≃ₜ C) {t₀ t₁ x y : ℝ} (ht₀ : t₀ ≤ x) (hxy : x < y) (ht₁ : y ≤ t₁)
    (hlt : t₁ < t₀ + 2 * Real.pi)
    (hab : ({cuffPoint f x, cuffPoint f y} : Set S) = {a, b})
    (hM : Disjoint (cuffPoint f '' Ioo x y) S₁) (hO : cuffPoint f '' Ioo y (x + 2 * Real.pi) ⊆ S₁) :
    cuffPoint f '' Icc t₀ t₁ ∩ S₁ = cuffPoint f '' Icc t₀ x ∪ cuffPoint f '' Icc y t₁ := by
  have hpi := Real.pi_pos
  have hend : ∀ {τ : ℝ}, τ = x ∨ τ = y → cuffPoint f τ ∈ S₁ := by
    rintro τ (rfl | rfl)
    · exact h.line_subset_left (by
        have : cuffPoint f τ ∈ ({a, b} : Set S) := hab ▸ Or.inl rfl
        rcases this with h' | h' <;> rw [h']
        exacts [h.proper.1.left_mem, h.proper.1.right_mem])
    · exact h.line_subset_left (by
        have : cuffPoint f τ ∈ ({a, b} : Set S) := hab ▸ Or.inr rfl
        rcases this with h' | h' <;> rw [h']
        exacts [h.proper.1.left_mem, h.proper.1.right_mem])
  ext z
  constructor
  · rintro ⟨⟨τ, hτ, rfl⟩, hτS⟩
    by_cases hτx : τ ≤ x
    · exact Or.inl ⟨τ, ⟨hτ.1, hτx⟩, rfl⟩
    by_cases hτy : y ≤ τ
    · exact Or.inr ⟨τ, ⟨hτy, hτ.2⟩, rfl⟩
    exact absurd hτS (disjoint_left.mp hM ⟨τ, ⟨not_le.mp hτx, not_le.mp hτy⟩, rfl⟩)
  · rintro (⟨τ, hτ, rfl⟩ | ⟨τ, hτ, rfl⟩)
    · refine ⟨⟨τ, ⟨hτ.1, hτ.2.trans (hxy.le.trans ht₁)⟩, rfl⟩, ?_⟩
      rcases hτ.2.lt_or_eq with hτx | hτx
      · rw [← GM17.cuffPoint_add_two_pi f τ]
        exact hO ⟨τ + 2 * Real.pi, ⟨by linarith [hτ.1], by linarith⟩, rfl⟩
      · exact hend (Or.inl hτx)
    · refine ⟨⟨τ, ⟨ht₀.trans (hxy.le.trans hτ.1), hτ.2⟩, rfl⟩, ?_⟩
      rcases hτ.1.lt_or_eq with hyτ | hyτ
      · exact hO ⟨τ, ⟨hyτ, by linarith [hτ.2]⟩, rfl⟩
      · exact hend (Or.inr hyτ.symm)

end Gap
end GM21
end GraphMinor
