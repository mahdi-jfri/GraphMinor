module

public import GraphMinor.GM08.Section15Lemma4
public import GraphMinor.GM11.PaintingCells

/-!
# Graph Minors VIII, printed (15.1): bridges between equal end sets

This file serves Lemma 2 of the proof of the printed (15.1) in `Section15PrintedFinal.lean`. Lemma 2
says that a bridge of a tube whose two ends meet the drawing in the same vertex set has at most
two attachments.

Three attachments would give a drawing of $K_{3,3}$ in the sphere. We use this idea in the capped
sphere, where the two
ends of the tube bound two closed discs `D₁`, `D₂` with disjoint interiors. A bridge gives a
connected set `Y` outside both discs, and its attachments lie in the closure of `Y` and on both
disc boundaries. Three attachments are impossible (`false_of_three_attachments`).
-/

@[expose] public section

namespace GraphMinor.GM08

open Set Topology GraphMinor.Surface

local notation "𝕀" => unitInterval

/-- A closed disc `X` inside a closed disc `D` of a closed surface meets the boundary of `D` only
on its own boundary: an interior point of `X` is an interior point of `D`. -/
theorem inter_discBd_subset_discBd {T : Type} [TopologicalSpace T] (hT : IsClosedSurface T)
    {X D : Set T} (hX : IsClosedDisc X) (hD : IsClosedDisc D) (hXD : X ⊆ D) :
    X ∩ discBd D ⊆ discBd X := by
  rintro x ⟨hxX, hxD⟩
  by_contra hx
  have h1 : x ∈ interior X := by
    rw [GM11.interior_eq_sdiff_discBd hT hX]
    exact ⟨hxX, hx⟩
  have h2 : x ∈ interior D := interior_mono hXD h1
  rw [GM11.interior_eq_sdiff_discBd hT hD] at h2
  exact h2.2 hxD

/-- Two arcs `f₁`, `f₂` from `a` to `b` that meet only at their ends form a circle. Remove one
inner point of each arc. Then no preconnected part of the rest holds both `a` and `b`: the rest
splits into the part near `a` and the part near `b`, and these are closed in the rest and
disjoint. -/
theorem false_of_preconnected_theta {T : Type*} [TopologicalSpace T] [T2Space T]
    {f₁ f₂ : 𝕀 → T} (h₁ : IsArcMap f₁) (h₂ : IsArcMap f₂) (h0 : f₂ 0 = f₁ 0)
    (h1 : f₂ 1 = f₁ 1) (hmeet : range f₁ ∩ range f₂ ⊆ {f₁ 0, f₁ 1}) {s : 𝕀} (hs0 : s ≠ 0)
    (hs1 : s ≠ 1) {C : Set T} (hC : IsPreconnected C)
    (hCsub : C ⊆ (range f₁ ∪ range f₂) \ {f₁ s, f₂ s}) (ha : f₁ 0 ∈ C) (hb : f₁ 1 ∈ C) :
    False := by
  set Ka : Set T := f₁ '' Icc 0 s ∪ f₂ '' Icc 0 s with hKa
  set Kb : Set T := f₁ '' Icc s 1 ∪ f₂ '' Icc s 1 with hKb
  have hKac : IsClosed Ka :=
    ((isCompact_Icc.image h₁.1).isClosed).union ((isCompact_Icc.image h₂.1).isClosed)
  have hKbc : IsClosed Kb :=
    ((isCompact_Icc.image h₁.1).isClosed).union ((isCompact_Icc.image h₂.1).isClosed)
  -- a point of both arcs is an end
  have hmid : ∀ t t' : 𝕀, f₁ t = f₂ t' → (t = 0 ∧ t' = 0) ∨ (t = 1 ∧ t' = 1) := by
    intro t t' he
    rcases hmeet ⟨⟨t, rfl⟩, ⟨t', he.symm⟩⟩ with h | h
    · left
      refine ⟨h₁.2 h, h₂.2 ?_⟩
      rw [← he, h, h0]
    · right
      refine ⟨h₁.2 h, h₂.2 ?_⟩
      rw [← he, h, h1]
  have hsub : C ⊆ Ka ∪ Kb := by
    intro x hx
    rcases (hCsub hx).1 with ⟨t, rfl⟩ | ⟨t, rfl⟩
    · rcases le_total t s with h | h
      · exact .inl (.inl ⟨t, ⟨unitInterval.nonneg', h⟩, rfl⟩)
      · exact .inr (.inl ⟨t, ⟨h, unitInterval.le_one'⟩, rfl⟩)
    · rcases le_total t s with h | h
      · exact .inl (.inr ⟨t, ⟨unitInterval.nonneg', h⟩, rfl⟩)
      · exact .inr (.inr ⟨t, ⟨h, unitInterval.le_one'⟩, rfl⟩)
  have hcap : C ∩ (Ka ∩ Kb) = ∅ := by
    refine eq_empty_iff_forall_notMem.mpr fun x ⟨hxC, hxa, hxb⟩ => (hCsub hxC).2 ?_
    rcases hxa with ⟨t, ht, rfl⟩ | ⟨t, ht, rfl⟩ <;>
      rcases hxb with ⟨t', ht', he⟩ | ⟨t', ht', he⟩
    · have := h₁.2 he
      subst this
      exact .inl (by rw [le_antisymm ht.2 ht'.1])
    · rcases hmid t t' he.symm with ⟨-, h⟩ | ⟨h, -⟩
      · exact absurd (le_antisymm (h ▸ ht'.1) unitInterval.nonneg') hs0
      · exact absurd (le_antisymm unitInterval.le_one' (h ▸ ht.2)) hs1
    · rcases hmid t' t he with ⟨h, -⟩ | ⟨-, h⟩
      · exact absurd (le_antisymm (h ▸ ht'.1) unitInterval.nonneg') hs0
      · exact absurd (le_antisymm unitInterval.le_one' (h ▸ ht.2)) hs1
    · have := h₂.2 he
      subst this
      exact .inr (by rw [le_antisymm ht.2 ht'.1]; rfl)
  rcases isPreconnected_iff_subset_of_disjoint_closed.mp hC Ka Kb hKac hKbc hsub hcap with h | h
  · rcases h hb with ⟨t, ht, he⟩ | ⟨t, ht, he⟩
    · exact hs1 (le_antisymm unitInterval.le_one' (h₁.2 he ▸ ht.2))
    · exact hs1 (le_antisymm unitInterval.le_one' (h₂.2 (he.trans h1.symm) ▸ ht.2))
  · rcases h ha with ⟨t, ht, he⟩ | ⟨t, ht, he⟩
    · exact hs0 (le_antisymm (h₁.2 he ▸ ht.1) unitInterval.nonneg')
    · exact hs0 (le_antisymm (h₂.2 (he.trans h0.symm) ▸ ht.1) unitInterval.nonneg')

/-- A chord `ℓ` from `a` to `b` cuts a closed disc `D` into two closed discs. For a third point
`c` of the boundary, one of them has `c` and all of `ℓ` on its boundary, and stays connected
when `ℓ` is removed (`Surface.disc_iArc`). -/
theorem exists_half_disc {T : Type*} [TopologicalSpace T] {D ℓ : Set T} {a b c : T}
    (hD : IsClosedDisc D) (hℓ : IsLineWithEnds ℓ a b) (hℓD : ℓ ⊆ D) (hab : a ≠ b)
    (hmeet : ℓ ∩ discBd D = {a, b}) (hc : c ∈ discBd D) (hca : c ≠ a) (hcb : c ≠ b) :
    ∃ X, IsClosedDisc X ∧ X ⊆ D ∧ c ∈ discBd X ∧ ℓ ⊆ discBd X ∧ IsPreconnected (X \ ℓ) := by
  obtain ⟨A₁, A₂, Δ₁, Δ₂, -, hcomp, hΔ₁, hΔ₂, hU, -, hb₁, hb₂, hcompDL⟩ :=
    disc_iArc D ℓ a b hD hℓD hab hℓ hmeet
  have hc' : c ∈ discBd D \ {a, b} := ⟨hc, by rintro (h | h); exacts [hca h, hcb h]⟩
  rw [← union_eq_of_componentsIn_eq_pair hcomp] at hc'
  have hpre₁ : IsPreconnected (Δ₁ \ ℓ) :=
    (isPreconnected_and_subset_of_mem_componentsIn (by rw [hcompDL]; exact .inl rfl)).1
  have hpre₂ : IsPreconnected (Δ₂ \ ℓ) :=
    (isPreconnected_and_subset_of_mem_componentsIn (by rw [hcompDL]; exact .inr rfl)).1
  rcases hc' with h | h
  · exact ⟨Δ₁, hΔ₁, hU ▸ subset_union_left, hb₁ ▸ .inl h, hb₁ ▸ subset_union_right, hpre₁⟩
  · exact ⟨Δ₂, hΔ₂, hU ▸ subset_union_right, hb₂ ▸ .inl h, hb₂ ▸ subset_union_right, hpre₂⟩

/-- **Three attachments are impossible.** In a sphere, let `D₁`, `D₂` be closed discs with
disjoint interiors, and let `Y` be a connected set outside both. Then at most two points of
`bd D₁ ∩ bd D₂` lie in the closure of `Y`.

Suppose `a`, `b`, `c` do. Chords `ℓ₁ ⊆ D₁`, `ℓ₂ ⊆ D₂` from `a` to `b` form a circle `Θ`, and
`Y` lies on one side `P` of it. The chord `ℓ₁` cuts `D₁` into two halves; the half `X₁` with
`c` on its boundary lies in `P`, since it is connected off `ℓ₁` and holds `c`. The same holds for
a half `X₂` of `D₂`. Chords from `c` to inner points `t₁ ∈ ℓ₁` and `t₂ ∈ ℓ₂` inside `X₁` and `X₂`
form a chord `Λ` of `P`. It cuts `P` into two halves, and `Y` lies in one of them. So `a` and `b`
both lie on the arc of `Θ` cut off by `t₁` and `t₂` on that side, which is impossible since `a`
and `b` are separated on `Θ` by `t₁` and `t₂` (`false_of_preconnected_theta`). -/
theorem false_of_three_attachments {T : Type} [TopologicalSpace T] (hT : IsClosedSurface T)
    (hsph : IsSphere T) {D₁ D₂ : Set T} (hD₁ : IsClosedDisc D₁) (hD₂ : IsClosedDisc D₂)
    (h12 : Disjoint (discInt D₁) D₂) (h21 : Disjoint D₁ (discInt D₂))
    {Y : Set T} (hY : IsPreconnected Y) (hYD : Disjoint Y (D₁ ∪ D₂)) {a b c : T}
    (ha₁ : a ∈ discBd D₁) (ha₂ : a ∈ discBd D₂) (hb₁ : b ∈ discBd D₁) (hb₂ : b ∈ discBd D₂)
    (hc₁ : c ∈ discBd D₁) (hc₂ : c ∈ discBd D₂) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (haY : a ∈ closure Y) (hbY : b ∈ closure Y) (hcY : c ∈ closure Y) : False := by
  have : T2Space T := hT.2.1
  have hD12 : D₁ ∩ D₂ ⊆ discBd D₁ := fun z ⟨z1, z2⟩ => by
    by_contra hz
    exact disjoint_left.mp h12 ⟨z1, hz⟩ z2
  have hD21 : D₁ ∩ D₂ ⊆ discBd D₂ := fun z ⟨z1, z2⟩ => by
    by_contra hz
    exact disjoint_left.mp h21 z1 ⟨z2, hz⟩
  have hYne : Y.Nonempty := closure_nonempty_iff.mp ⟨a, haY⟩
  -- the circle `Θ`
  obtain ⟨ℓ₁, hℓ₁, hℓ₁D, hℓ₁b⟩ := GM07.exists_chord_any hD₁ ha₁ hb₁ hab
  obtain ⟨ℓ₂, hℓ₂, hℓ₂D, hℓ₂b⟩ := GM07.exists_chord_any hD₂ ha₂ hb₂ hab
  have hℓ12 : ℓ₁ ∩ ℓ₂ ⊆ {a, b} := fun z ⟨z1, z2⟩ => by
    rw [← hℓ₁b]
    exact ⟨z1, hD12 ⟨hℓ₁D z1, hℓ₂D z2⟩⟩
  have hab₁ : ({a, b} : Set T) ⊆ ℓ₁ := by
    rintro z (rfl | rfl)
    exacts [hℓ₁.left_mem, hℓ₁.right_mem]
  have hab₂ : ({a, b} : Set T) ⊆ ℓ₂ := by
    rintro z (rfl | rfl)
    exacts [hℓ₂.left_mem, hℓ₂.right_mem]
  set Θ := ℓ₁ ∪ ℓ₂ with hΘdef
  have hΘ : IsOArc Θ := GM11.isOArc_union hℓ₁ hℓ₂ hℓ12
  have hΘD : Θ ⊆ D₁ ∪ D₂ := union_subset_union hℓ₁D hℓ₂D
  have hYΘ : Y ⊆ univ \ Θ := fun y hy => ⟨trivial, fun h => disjoint_left.mp hYD hy (hΘD h)⟩
  obtain ⟨P, P', hP, hPb, hcomp, hPI, hYP⟩ : ∃ P P' : Set T, IsClosedDisc P ∧ discBd P = Θ ∧
      componentsIn (univ \ Θ) = {P \ Θ, P' \ Θ} ∧ P ∩ P' = Θ ∧ Y ⊆ P \ Θ := by
    obtain ⟨Δ, Δ', -, hΔ, hΔ', hb, hb', -, hI, hcomp, -⟩ := sphere_disc T hsph Θ hΘ
    rcases subset_or_subset_of_componentsIn_eq_pair hcomp hY hYne hYΘ with h | h
    · exact ⟨Δ, Δ', hΔ, hb, hcomp, hI, h⟩
    · exact ⟨Δ', Δ, hΔ', hb', by rw [hcomp, pair_comm], by rw [inter_comm, hI], h⟩
  have hYP' : closure Y ⊆ P := closure_minimal (hYP.trans sdiff_subset) hP.isClosed
  have hΘP : Θ ⊆ P := hPb ▸ discBd_subset P
  -- `c` is off `Θ` and inside `P`
  have hcℓ₁ : c ∉ ℓ₁ := fun h => by
    have : c ∈ ℓ₁ ∩ discBd D₁ := ⟨h, hc₁⟩
    rw [hℓ₁b] at this
    rcases this with h' | h'
    exacts [hac h'.symm, hbc h'.symm]
  have hcℓ₂ : c ∉ ℓ₂ := fun h => by
    have : c ∈ ℓ₂ ∩ discBd D₂ := ⟨h, hc₂⟩
    rw [hℓ₂b] at this
    rcases this with h' | h'
    exacts [hac h'.symm, hbc h'.symm]
  have hcP : c ∈ P \ Θ := ⟨hYP' hcY, by rintro (h | h); exacts [hcℓ₁ h, hcℓ₂ h]⟩
  -- a half disc holding `c` lies in `P`
  have hhalf : ∀ X ℓ : Set T, IsPreconnected (X \ ℓ) → X \ ℓ ⊆ univ \ Θ → ℓ ⊆ Θ →
      c ∈ X \ ℓ → X ⊆ P := by
    intro X ℓ hX hXΘ hℓΘ hcX z hz
    by_cases hzℓ : z ∈ ℓ
    · exact hΘP (hℓΘ hzℓ)
    rcases subset_or_subset_of_componentsIn_eq_pair hcomp hX ⟨c, hcX⟩ hXΘ with h | h
    · exact (h ⟨hz, hzℓ⟩).1
    · have hc' : c ∈ P ∩ P' := ⟨hcP.1, (h hcX).1⟩
      rw [hPI] at hc'
      exact absurd hc' hcP.2
  obtain ⟨X₁, hX₁, hX₁D, hcX₁, hℓX₁, hpre₁⟩ :=
    exists_half_disc hD₁ hℓ₁ hℓ₁D hab hℓ₁b hc₁ hac.symm hbc.symm
  obtain ⟨X₂, hX₂, hX₂D, hcX₂, hℓX₂, hpre₂⟩ :=
    exists_half_disc hD₂ hℓ₂ hℓ₂D hab hℓ₂b hc₂ hac.symm hbc.symm
  have hX₁P : X₁ ⊆ P := by
    refine hhalf X₁ ℓ₁ hpre₁ ?_ subset_union_left ⟨discBd_subset X₁ hcX₁, hcℓ₁⟩
    rintro z ⟨hz, hzℓ⟩
    refine ⟨trivial, ?_⟩
    rintro (h | h)
    · exact hzℓ h
    · have : z ∈ ℓ₂ ∩ discBd D₂ := ⟨h, hD21 ⟨hX₁D hz, hℓ₂D h⟩⟩
      rw [hℓ₂b] at this
      exact hzℓ (hab₁ this)
  have hX₂P : X₂ ⊆ P := by
    refine hhalf X₂ ℓ₂ hpre₂ ?_ subset_union_right ⟨discBd_subset X₂ hcX₂, hcℓ₂⟩
    rintro z ⟨hz, hzℓ⟩
    refine ⟨trivial, ?_⟩
    rintro (h | h)
    · have : z ∈ ℓ₁ ∩ discBd D₁ := ⟨h, hD12 ⟨hℓ₁D h, hX₂D hz⟩⟩
      rw [hℓ₁b] at this
      exact hzℓ (hab₂ this)
    · exact hzℓ h
  -- inner points `t₁`, `t₂`
  obtain ⟨f₁, hf₁, hr₁, hf₁0, hf₁1⟩ := hℓ₁.exists_arc
  obtain ⟨f₂, hf₂, hr₂, hf₂0, hf₂1⟩ := hℓ₂.exists_arc
  set s : 𝕀 := ⟨1 / 2, by norm_num, by norm_num⟩ with hsdef
  have hs0 : s ≠ 0 := fun h => by
    have := congrArg Subtype.val h
    norm_num [hsdef] at this
  have hs1 : s ≠ 1 := fun h => by
    have := congrArg Subtype.val h
    norm_num [hsdef] at this
  set t₁ := f₁ s with ht₁def
  set t₂ := f₂ s with ht₂def
  have ht₁ℓ : t₁ ∈ ℓ₁ := hr₁ ▸ mem_range_self s
  have ht₂ℓ : t₂ ∈ ℓ₂ := hr₂ ▸ mem_range_self s
  have ht₁a : t₁ ≠ a := fun h => hs0 (hf₁.2 (h.trans hf₁0.symm))
  have ht₁b : t₁ ≠ b := fun h => hs1 (hf₁.2 (h.trans hf₁1.symm))
  have ht₂a : t₂ ≠ a := fun h => hs0 (hf₂.2 (h.trans hf₂0.symm))
  have ht₂b : t₂ ≠ b := fun h => hs1 (hf₂.2 (h.trans hf₂1.symm))
  have ht₁D₂ : t₁ ∉ D₂ := fun h => by
    have : t₁ ∈ ℓ₁ ∩ discBd D₁ := ⟨ht₁ℓ, hD12 ⟨hℓ₁D ht₁ℓ, h⟩⟩
    rw [hℓ₁b] at this
    rcases this with h' | h'
    exacts [ht₁a h', ht₁b h']
  have ht₂D₁ : t₂ ∉ D₁ := fun h => by
    have : t₂ ∈ ℓ₂ ∩ discBd D₂ := ⟨ht₂ℓ, hD21 ⟨h, hℓ₂D ht₂ℓ⟩⟩
    rw [hℓ₂b] at this
    rcases this with h' | h'
    exacts [ht₂a h', ht₂b h']
  -- the chord `Λ` of `P`
  obtain ⟨m₁, hm₁, hm₁X, hm₁b⟩ := GM07.exists_chord_any hX₁ hcX₁ (hℓX₁ ht₁ℓ)
    (fun h => hcℓ₁ (h ▸ ht₁ℓ))
  obtain ⟨m₂, hm₂, hm₂X, hm₂b⟩ := GM07.exists_chord_any hX₂ hcX₂ (hℓX₂ ht₂ℓ)
    (fun h => hcℓ₂ (h ▸ ht₂ℓ))
  have hm12 : m₁ ∩ m₂ = {c} := by
    refine Subset.antisymm (fun z ⟨z1, z2⟩ => ?_) ?_
    · have hz1 : z ∈ discBd D₁ := hD12 ⟨hX₁D (hm₁X z1), hX₂D (hm₂X z2)⟩
      have hzX : z ∈ discBd X₁ := inter_discBd_subset_discBd hT hX₁ hD₁ hX₁D ⟨hm₁X z1, hz1⟩
      have : z ∈ m₁ ∩ discBd X₁ := ⟨z1, hzX⟩
      rw [hm₁b] at this
      rcases this with h | h
      · exact h
      · exact absurd (h ▸ hX₂D (hm₂X z2)) ht₁D₂
    · rintro z rfl
      exact ⟨hm₁.left_mem, hm₂.left_mem⟩
  have hΛ : IsLineWithEnds (m₁ ∪ m₂) t₁ t₂ := hm₁.symm.union hm₂ hm12
  set Λ := m₁ ∪ m₂ with hΛdef
  have hΛP : Λ ⊆ P := union_subset ((hm₁X).trans hX₁P) ((hm₂X).trans hX₂P)
  have hΛΘ : Λ ∩ discBd P = {t₁, t₂} := by
    rw [hPb]
    refine Subset.antisymm ?_ ?_
    · rintro z ⟨hzΛ | hzΛ, hzΘ⟩
      · have hzℓ : z ∈ ℓ₁ := by
          rcases hzΘ with h | h
          · exact h
          · have : z ∈ ℓ₂ ∩ discBd D₂ := ⟨h, hD21 ⟨hX₁D (hm₁X hzΛ), hℓ₂D h⟩⟩
            rw [hℓ₂b] at this
            exact hab₁ this
        have : z ∈ m₁ ∩ discBd X₁ := ⟨hzΛ, hℓX₁ hzℓ⟩
        rw [hm₁b] at this
        rcases this with h | h
        · exact absurd (h ▸ hzℓ) hcℓ₁
        · exact .inl h
      · have hzℓ : z ∈ ℓ₂ := by
          rcases hzΘ with h | h
          · have : z ∈ ℓ₁ ∩ discBd D₁ := ⟨h, hD12 ⟨hℓ₁D h, hX₂D (hm₂X hzΛ)⟩⟩
            rw [hℓ₁b] at this
            exact hab₂ this
          · exact h
        have : z ∈ m₂ ∩ discBd X₂ := ⟨hzΛ, hℓX₂ hzℓ⟩
        rw [hm₂b] at this
        rcases this with h | h
        · exact absurd (h ▸ hzℓ) hcℓ₂
        · exact .inr h
    · rintro z (rfl | rfl)
      · exact ⟨.inl hm₁.right_mem, .inl ht₁ℓ⟩
      · exact ⟨.inr hm₂.right_mem, .inr ht₂ℓ⟩
  have ht12 : t₁ ≠ t₂ := fun h => ht₂D₁ (h ▸ hX₁D (hm₁X hm₁.right_mem))
  obtain ⟨C₁, C₂, P₁, P₂, -, hcompC, hP₁, hP₂, hPU, -, hbP₁, hbP₂, hcompΛ⟩ :=
    disc_iArc P Λ t₁ t₂ hP hΛP ht12 hΛ hΛΘ
  have hYΛ : Y ⊆ P \ Λ := fun y hy =>
    ⟨(hYP hy).1, fun h => disjoint_left.mp hYD hy (union_subset_union (hm₁X.trans hX₁D)
      (hm₂X.trans hX₂D) h)⟩
  -- the end of the argument, on either side of `Λ`
  have hfin : ∀ Pi Ci : Set T, IsClosedDisc Pi → Pi ⊆ P → discBd Pi = Ci ∪ Λ →
      Ci ∈ componentsIn (discBd P \ {t₁, t₂}) → Y ⊆ Pi → False := by
    intro Pi Ci hPi hPiP hbPi hCi hYPi
    have hYPi' : closure Y ⊆ Pi := closure_minimal hYPi hPi.isClosed
    have hmemC : ∀ x, x ∈ closure Y → x ∈ Θ → x ≠ t₁ → x ≠ t₂ → x ∈ Ci := by
      intro x hxY hxΘ hx1 hx2
      have hxb : x ∈ discBd Pi :=
        inter_discBd_subset_discBd hT hPi hP hPiP ⟨hYPi' hxY, hPb ▸ hxΘ⟩
      rw [hbPi] at hxb
      rcases hxb with h | h
      · exact h
      · have : x ∈ Λ ∩ discBd P := ⟨h, hPb ▸ hxΘ⟩
        rw [hΛΘ] at this
        rcases this with h' | h'
        exacts [absurd h' hx1, absurd h' hx2]
    have haC := hmemC a haY (.inl hℓ₁.left_mem) ht₁a.symm ht₂a.symm
    have hbC := hmemC b hbY (.inl hℓ₁.right_mem) ht₁b.symm ht₂b.symm
    obtain ⟨hCpre, hCsub⟩ := isPreconnected_and_subset_of_mem_componentsIn hCi
    refine false_of_preconnected_theta hf₂ hf₁ (hf₁0.trans hf₂0.symm) (hf₁1.trans hf₂1.symm)
      ?_ hs0 hs1 hCpre ?_ (by rw [hf₂0]; exact haC) (by rw [hf₂1]; exact hbC)
    · rw [hr₁, hr₂, hf₂0, hf₂1, inter_comm]
      exact hℓ12
    · rw [hr₁, hr₂, union_comm, ← hΘdef, ← hPb, pair_comm]
      exact hCsub
  rcases subset_or_subset_of_componentsIn_eq_pair hcompΛ hY hYne hYΛ with h | h
  · exact hfin P₁ C₁ hP₁ (hPU ▸ subset_union_left) hbP₁ (by rw [hcompC]; exact .inl rfl)
      (h.trans sdiff_subset)
  · exact hfin P₂ C₂ hP₂ (hPU ▸ subset_union_right) hbP₂ (by rw [hcompC]; exact .inr rfl)
      (h.trans sdiff_subset)

end GraphMinor.GM08
