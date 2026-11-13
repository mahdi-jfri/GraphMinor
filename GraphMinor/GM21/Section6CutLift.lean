module

public import GraphMinor.GM21.Section6CutLine
public import GraphMinor.GM07.CutStages
import GraphMinor.GM21.CuffSpaces
import GraphMinor.GM07.PullForest
import GraphMinor.GM11.RadialChord
import GraphMinor.Surface.Cuffs
import GraphMinor.GM17.CutSide

/-!
# Graph Minors XXI, (6.3), claim (2): lifting lines to the cut surface

Claim (2) of the proof of (6.3) (page 28 of the preprint) cuts `Σ` along a proper line `F`
with ends `a, b` and moves the supports of the presentation to the cut surface `Σ'`. A support
that holds `a` is cut at `a` into two supports: "Let $F_1^*$ have ends $u_1, u_2$, and let
$I_i \subseteq F_1^*$ be the support with ends $u_1, a$." The print's $u_1$ is a misprint for $u_i$,
and Lean uses $u_i$ (see the correction to the proof of (6.3) in `corrections/GM21.md`). In `Σ'` the
two pieces `I_1, I_2` must
end at the two different points over `a`. The paper uses this without comment. This file proves it.

* `lift A` is the closure of the lift `ψ⁻¹(A \ F)` of a set `A`. A line `A` that meets `F` only in
  its ends lifts to a line, which `ψ` maps one to one onto `A` (`isLineWithEnds_lift`).
* In an `O`-arc, no point is a common end of three lines that pairwise meet in finitely many points
  (`not_three_lines_oArc`): two of them leave the point in the same direction around the circle.
* Two lines `A₁, A₂ ⊆ bd(Σ)` with the common end `a`, that meet in finitely many points and meet `F`
  only in their ends, lift to lines with different ends over `a` (`lift_end_ne`). Otherwise the two
  lifts and the lift of `F` that ends at the same point would be three lines of one cuff of `Σ'`
  with a common end.
-/

@[expose] public section

namespace GraphMinor
namespace GM21
namespace CutLine

open Set Function Topology GraphMinor.Surface GraphMinor.GM17 GraphMinor.GM19

/-! ## Three lines in an `O`-arc -/

section ThreeLines

variable {S : Type*} [TopologicalSpace S]

/-- A line of an `O`-arc with one end at angle `t` is the arc of angles `[t, s]` or `[s, t + 2π]`
for the angle `s` of its other end. -/
theorem exists_angle_of_line [T2Space S] {Θ : Set S} (f : Circle ≃ₜ Θ) {t : ℝ} {q : S} {L : Set S}
    (hL : IsLineWithEnds L (cuffPoint f t) q) (hs : L ⊆ Θ) :
    ∃ s, t < s ∧ s < t + 2 * Real.pi ∧
      (L = cuffPoint f '' Icc t s ∨ L = cuffPoint f '' Icc s (t + 2 * Real.pi)) := by
  obtain ⟨s, hs₁, rfl⟩ := exists_cuffPoint_mem_Ico f t (hs hL.right_mem)
  have hts : t ≠ s := fun h => hL.ne' (by rw [h])
  have hlt : t < s := lt_of_le_of_ne hs₁.1 hts
  obtain ⟨L', hL', hu, hi⟩ := oarc_split_univ (⟨f⟩ : IsOArc Θ) hL hs
  obtain ⟨-, h | h⟩ := circle_lines_univ f hlt hs₁.2 hL hL' hu hi
  · exact ⟨s, hlt, hs₁.2, Or.inl h.1⟩
  · exact ⟨s, hlt, hs₁.2, Or.inr h.1⟩

/-- An arc of angles of positive length has infinitely many points. -/
theorem infinite_cuffPoint_Icc {Θ : Set S} (f : Circle ≃ₜ Θ) {x y : ℝ} (hxy : x < y)
    (hy : y < x + 2 * Real.pi) : (cuffPoint f '' Icc x y).Infinite :=
  (Set.Icc_infinite hxy).image ((cuffPoint_injOn_Ico f x).mono fun _ hu =>
    show _ ∈ Ico x (x + 2 * Real.pi) from ⟨hu.1, hu.2.trans_lt hy⟩)

/-- **No point of an `O`-arc is a common end of three lines that pairwise meet in finitely many
points.** -/
theorem not_three_lines_oArc [T2Space S] {Θ : Set S} (hΘ : IsOArc Θ) {p q₁ q₂ q₃ : S}
    {L₁ L₂ L₃ : Set S} (h₁ : IsLineWithEnds L₁ p q₁) (h₂ : IsLineWithEnds L₂ p q₂)
    (h₃ : IsLineWithEnds L₃ p q₃) (hs₁ : L₁ ⊆ Θ) (hs₂ : L₂ ⊆ Θ) (hs₃ : L₃ ⊆ Θ)
    (h₁₂ : (L₁ ∩ L₂).Finite) (h₁₃ : (L₁ ∩ L₃).Finite) (h₂₃ : (L₂ ∩ L₃).Finite) : False := by
  obtain ⟨f⟩ := hΘ
  obtain ⟨t, -, rfl⟩ := exists_cuffPoint_mem_Ico f 0 (hs₁ h₁.left_mem)
  have hpi := Real.pi_pos
  -- Two lines that leave `p` in the same direction meet in infinitely many points.
  have hright : ∀ {s s' : ℝ}, t < s → s < t + 2 * Real.pi → t < s' →
      (cuffPoint f '' Icc t s ∩ cuffPoint f '' Icc t s').Infinite := fun {s s'} hs hs2 hs' => by
    refine (infinite_cuffPoint_Icc f (lt_min hs hs') (by
      linarith [min_le_left s s'])).mono ?_
    rintro _ ⟨u, hu, rfl⟩
    exact ⟨⟨u, ⟨hu.1, hu.2.trans (min_le_left _ _)⟩, rfl⟩,
      ⟨u, ⟨hu.1, hu.2.trans (min_le_right _ _)⟩, rfl⟩⟩
  have hleft : ∀ {s s' : ℝ}, t < s → s < t + 2 * Real.pi → s' < t + 2 * Real.pi →
      (cuffPoint f '' Icc s (t + 2 * Real.pi) ∩
        cuffPoint f '' Icc s' (t + 2 * Real.pi)).Infinite := fun {s s'} hs hs2 hs' => by
    refine (infinite_cuffPoint_Icc f (max_lt hs2 hs') (by
      linarith [le_max_left s s'])).mono ?_
    rintro _ ⟨u, hu, rfl⟩
    exact ⟨⟨u, ⟨(le_max_left _ _).trans hu.1, hu.2⟩, rfl⟩,
      ⟨u, ⟨(le_max_right _ _).trans hu.1, hu.2⟩, rfl⟩⟩
  obtain ⟨s₁, ht₁, ht₁', e₁ | e₁⟩ := exists_angle_of_line f h₁ hs₁ <;>
  obtain ⟨s₂, ht₂, ht₂', e₂ | e₂⟩ := exists_angle_of_line f h₂ hs₂ <;>
  obtain ⟨s₃, ht₃, ht₃', e₃ | e₃⟩ := exists_angle_of_line f h₃ hs₃ <;>
  subst e₁ e₂ e₃
  · exact hright ht₁ ht₁' ht₂ h₁₂
  · exact hright ht₁ ht₁' ht₂ h₁₂
  · exact hright ht₁ ht₁' ht₃ h₁₃
  · exact hleft ht₂ ht₂' ht₃' h₂₃
  · exact hright ht₂ ht₂' ht₃ h₂₃
  · exact hleft ht₁ ht₁' ht₃' h₁₃
  · exact hleft ht₁ ht₁' ht₂' h₁₂
  · exact hleft ht₁ ht₁' ht₂' h₁₂

end ThreeLines

/-! ## Lifts of lines -/

variable {S S' : Type} [TopologicalSpace S] [TopologicalSpace S']

/-- The lift of a set `A ⊆ Σ` to the cut surface: the closure of `ψ⁻¹(A \ F)`. -/
def lift (ψ : S' → S) (F A : Set S) : Set S' :=
  closure (ψ ⁻¹' (A \ F))

section Lift

variable {ψ : S' → S} {F : Set S} {a b : S} {X Y : Set S'} {a₁ b₁ a₂ b₂ : S'}

namespace IsLineCut

variable (h : IsLineCut ψ F a b X Y a₁ b₁ a₂ b₂)
include h

theorem compactSpace : CompactSpace S' := h.surface.1

theorem t2Space : T2Space S' := h.surface.2.1

theorem isCutMap : IsCutMap ψ F := IsCutting.isCutMap h.cutting

theorem continuous : Continuous ψ := h.cutting.1

/-- Off `F`, `ψ` is one to one. -/
theorem injOn_compl : InjOn ψ (ψ ⁻¹' Fᶜ) := h.cutting.2.2.1

/-- The lift of `F` lies in the boundary of `Σ'`. -/
theorem preimage_subset_bd : ψ ⁻¹' F ⊆ bd S' := h.cutting.2.2.2.2

/-- Every fibre of `ψ` is finite. -/
theorem finite_fiber (x : S) : (ψ ⁻¹' {x}).Finite := h.isCutMap.2.2.2.1 x

/-- The preimage of a finite set is finite. -/
theorem finite_preimage {A : Set S} (hA : A.Finite) : (ψ ⁻¹' A).Finite :=
  Set.Finite.preimage' hA fun x _ => h.finite_fiber x

/-- The two points over a point of `F`: one in `X` and one in `Y`. -/
theorem preimage_singleton {x : S} (hx : x ∈ F) {x₁ x₂ : S'} (hx₁ : x₁ ∈ X) (hx₂ : x₂ ∈ Y)
    (h₁ : ψ x₁ = x) (h₂ : ψ x₂ = x) : ψ ⁻¹' {x} = {x₁, x₂} := by
  ext z
  simp only [mem_preimage, mem_singleton_iff, mem_insert_iff]
  constructor
  · intro hz
    have hzF : z ∈ ψ ⁻¹' F := by rw [mem_preimage, hz]; exact hx
    rcases (h.union ▸ hzF : z ∈ X ∪ Y) with hzX | hzY
    · exact Or.inl (h.bijX.injOn hzX hx₁ (hz.trans h₁.symm))
    · exact Or.inr (h.bijY.injOn hzY hx₂ (hz.trans h₂.symm))
  · rintro (rfl | rfl)
    · exact h₁
    · exact h₂

theorem a₁_mem : a₁ ∈ X := h.lineX.left_mem
theorem b₁_mem : b₁ ∈ X := h.lineX.right_mem
theorem a₂_mem : a₂ ∈ Y := h.lineY.left_mem
theorem b₂_mem : b₂ ∈ Y := h.lineY.right_mem

omit h in
theorem a_mem (hF : IsProperLineInSurface F a b) : a ∈ F := hF.1.left_mem
omit h in
theorem b_mem (hF : IsProperLineInSurface F a b) : b ∈ F := hF.1.right_mem

/-- The points over `a` are `a₁` and `a₂`. -/
theorem preimage_a (hF : IsProperLineInSurface F a b) : ψ ⁻¹' {a} = {a₁, a₂} :=
  h.preimage_singleton (a_mem hF) h.a₁_mem h.a₂_mem h.map_a₁ h.map_a₂

/-- The points over `b` are `b₁` and `b₂`. -/
theorem preimage_b (hF : IsProperLineInSurface F a b) : ψ ⁻¹' {b} = {b₁, b₂} :=
  h.preimage_singleton (b_mem hF) h.b₁_mem h.b₂_mem h.map_b₁ h.map_b₂

theorem a₁_ne_a₂ : a₁ ≠ a₂ := fun he => disjoint_left.mp h.disjoint h.a₁_mem (he ▸ h.a₂_mem)

theorem b₁_ne_b₂ : b₁ ≠ b₂ := fun he => disjoint_left.mp h.disjoint h.b₁_mem (he ▸ h.b₂_mem)

/-- `ψ` undoes a cut along `F` in the sense of Graph Minors VII (`IsCutAlongSet`). -/
theorem isCutAlongSet (hS : IsSurface S) (hF : IsProperLineInSurface F a b) :
    GM07.IsCutAlongSet F ψ :=
  have : T2Space S := hS.2.1
  GM07.IsCutAlongSet.of_isCutting h.surface hS hF.1.isCompact.isClosed h.cutting

/-- The boundary of `Σ'` is the set over `bd(Σ) ∪ F`. -/
theorem bd_eq (hS : IsSurface S) (hF : IsProperLineInSurface F a b) :
    bd S' = ψ ⁻¹' (bd S ∪ F) :=
  ((h.isCutAlongSet hS hF).preimage_bd).symm

/-- The lift of a set off `F` is a set off the lift of `F`. -/
theorem lift_subset_preimage (hS : IsSurface S) {A : Set S} (hA : IsClosed A) :
    lift ψ F A ⊆ ψ ⁻¹' A := by
  have : T2Space S := hS.2.1
  exact closure_minimal (fun z hz => hz.1) (hA.preimage h.continuous)

/-- The lift of a part of `bd(Σ)` lies in `bd(Σ')`. -/
theorem lift_subset_bd (hS : IsSurface S) (hF : IsProperLineInSurface F a b) {A : Set S}
    (hA : A ⊆ bd S) : lift ψ F A ⊆ bd S' :=
  closure_minimal (fun _ hz => (h.bd_eq hS hF).symm ▸ Or.inl (hA hz.1)) (isClosed_bd S')

/-- **A line that meets `F` only in its ends lifts to a line**, mapped one to one onto it. -/
theorem isLineWithEnds_lift (hS : IsSurface S) {A : Set S} {u v : S} (hne : u ≠ v)
    (hA : IsLineWithEnds A u v) (hAF : A ∩ F ⊆ {u, v}) :
    ∃ u' v' : S', IsLineWithEnds (lift ψ F A) u' v' ∧ ψ u' = u ∧ ψ v' = v ∧
      ψ '' lift ψ F A = A ∧ InjOn ψ (lift ψ F A) := by
  have : CompactSpace S' := h.compactSpace
  have : T2Space S' := h.t2Space
  have : T2Space S := hS.2.1
  have hFc : IsClosed F :=
    (h.bijX.image_eq ▸ h.lineX.isCompact.image h.continuous : IsCompact F).isClosed
  obtain ⟨L, u', v', hL, hu, hv, him, hinj, hmem⟩ :=
    GM07.exists_lift_closed_edge h.isCutMap hFc hne hA hAF
  have hLeq : lift ψ F A = L := by
    apply subset_antisymm
    · refine closure_minimal (fun z hz => ?_) hL.isCompact.isClosed
      by_cases hzuv : ψ z ∈ ({u, v} : Set S)
      · have hzF : ψ z ∉ F := hz.2
        rcases hzuv with hzu | hzv
        · have := h.injOn_compl (show z ∈ ψ ⁻¹' Fᶜ from hzF)
            (show u' ∈ ψ ⁻¹' Fᶜ by rw [mem_preimage, hu, ← hzu]; exact hzF) (hzu.trans hu.symm)
          exact this ▸ hL.left_mem
        · have := h.injOn_compl (show z ∈ ψ ⁻¹' Fᶜ from hzF)
            (show v' ∈ ψ ⁻¹' Fᶜ by rw [mem_preimage, hv, ← hzv]; exact hzF) (hzv.trans hv.symm)
          exact this ▸ hL.right_mem
      · exact hmem z ⟨hz.1, hzuv⟩
    · rw [← GM11.closure_sdiff_pair hL]
      refine closure_mono fun z hz => ⟨?_, ?_⟩
      · rw [← him] at *
        exact mem_image_of_mem ψ hz.1
      · intro hzF
        have hzA : ψ z ∈ A := him ▸ mem_image_of_mem ψ hz.1
        rcases hAF ⟨hzA, hzF⟩ with hzu | hzv
        · exact hz.2 (Or.inl (hinj hz.1 hL.left_mem (hzu.trans hu.symm)))
        · exact hz.2 (Or.inr (hinj hz.1 hL.right_mem (hzv.trans hv.symm)))
  rw [hLeq]
  exact ⟨u', v', hL, hu, hv, him, hinj⟩

/-- **Two boundary lines at `a` lift to lines with different ends over `a`.** Let `A₁, A₂ ⊆ bd(Σ)`
be lines with the common end `a`, meeting in finitely many points, and meeting `F` only in their
ends. If their lifts had the same point `e` over `a`, then the lifts and the lift of `F` that ends at
`e` (`X` or `Y`) would be three lines of the cuff of `Σ'` at `e`, with the common end `e` and
pairwise finite intersections. This is impossible by `not_three_lines_oArc`. -/
theorem lift_end_ne (hS : IsSurface S) (hF : IsProperLineInSurface F a b) {A₁ A₂ : Set S}
    {v₁ v₂ : S} (hA₁ : IsLineWithEnds A₁ a v₁) (hA₂ : IsLineWithEnds A₂ a v₂) (hne₁ : a ≠ v₁)
    (hne₂ : a ≠ v₂) (hb₁ : A₁ ⊆ bd S) (hb₂ : A₂ ⊆ bd S) (hF₁ : A₁ ∩ F ⊆ {a, v₁})
    (hF₂ : A₂ ∩ F ⊆ {a, v₂}) (hfin : (A₁ ∩ A₂).Finite) {e₁ e₂ : S'}
    (he₁ : e₁ ∈ lift ψ F A₁) (he₂ : e₂ ∈ lift ψ F A₂) (hψ₁ : ψ e₁ = a) (hψ₂ : ψ e₂ = a) :
    e₁ ≠ e₂ := by
  have : T2Space S' := h.t2Space
  have : T2Space S := hS.2.1
  obtain ⟨u₁, w₁, hL₁, hu₁, -, -, hinj₁⟩ := h.isLineWithEnds_lift hS hne₁ hA₁ hF₁
  obtain ⟨u₂, w₂, hL₂, hu₂, -, -, hinj₂⟩ := h.isLineWithEnds_lift hS hne₂ hA₂ hF₂
  have he₁u : e₁ = u₁ := hinj₁ he₁ hL₁.left_mem (hψ₁.trans hu₁.symm)
  have he₂u : e₂ = u₂ := hinj₂ he₂ hL₂.left_mem (hψ₂.trans hu₂.symm)
  subst he₁u he₂u
  intro hee
  subst hee
  -- The lift of `F` that ends at `e₁`.
  have hZ : ∃ Z : Set S', ∃ z : S', IsLineWithEnds Z e₁ z ∧ Z ⊆ ψ ⁻¹' F := by
    have hmem : e₁ ∈ ψ ⁻¹' {a} := hψ₁
    rw [h.preimage_a hF] at hmem
    rcases hmem with rfl | rfl
    · exact ⟨X, b₁, h.lineX, fun z hz => h.union ▸ Or.inl hz⟩
    · exact ⟨Y, b₂, h.lineY, fun z hz => h.union ▸ Or.inr hz⟩
  obtain ⟨Z, z, hZl, hZF⟩ := hZ
  have hAc₁ : IsClosed A₁ := hA₁.isCompact.isClosed
  have hAc₂ : IsClosed A₂ := hA₂.isCompact.isClosed
  have hbd₁ := h.lift_subset_bd hS hF hb₁
  have hbd₂ := h.lift_subset_bd hS hF hb₂
  have hbdZ : Z ⊆ bd S' := hZF.trans h.preimage_subset_bd
  have he₁bd : e₁ ∈ bd S' := hbdZ hZl.left_mem
  have hΘ : IsOArc (connectedComponentIn (bd S') e₁) :=
    (cuff_statement S' h.surface).2.2 _ ⟨e₁, he₁bd, rfl⟩
  have hsub : ∀ {L : Set S'} {w : S'}, IsLineWithEnds L e₁ w → L ⊆ bd S' →
      L ⊆ connectedComponentIn (bd S') e₁ := fun {L w} hL hLb =>
    (GM17.isPreconnected_line hL).subset_connectedComponentIn hL.left_mem hLb
  refine not_three_lines_oArc hΘ hZl hL₁ hL₂ (hsub hZl hbdZ) (hsub hL₁ hbd₁) (hsub hL₂ hbd₂)
    ?_ ?_ ?_
  · refine (h.finite_preimage (A := ({a, v₁} : Set S)) (toFinite _)).subset ?_
    rintro y ⟨hyZ, hyL⟩
    exact hF₁ ⟨h.lift_subset_preimage hS hAc₁ hyL, hZF hyZ⟩
  · refine (h.finite_preimage (A := ({a, v₂} : Set S)) (toFinite _)).subset ?_
    rintro y ⟨hyZ, hyL⟩
    exact hF₂ ⟨h.lift_subset_preimage hS hAc₂ hyL, hZF hyZ⟩
  · refine (h.finite_preimage hfin).subset ?_
    rintro y ⟨hy₁, hy₂⟩
    exact ⟨h.lift_subset_preimage hS hAc₁ hy₁, h.lift_subset_preimage hS hAc₂ hy₂⟩

end IsLineCut

end Lift

end CutLine
end GM21
end GraphMinor
