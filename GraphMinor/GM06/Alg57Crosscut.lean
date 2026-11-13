module

public import GraphMinor.Surface.CrossCut

/-!
# Crosscuts of a disc

This is Lemma 2 of our proof of VI (5.7) (outlined in `Alg57Algorithm.lean`), in the plane. A Jordan
curve `F = A₁ ∪ A₂` bounds a disc, and an arc `c` joins the common ends `p, q` of `A₁` and `A₂`
through the inside of `F`. The theta curve lemma `IsTheta.inner_sdiff` cuts the inside of `F`
along `c` into the insides of `A₁ ∪ c` and `A₂ ∪ c`, the two sides of `c`.

Here we prove the two facts that the later lemmas use.
* The closure of the side of `A₁` meets `F` exactly in `A₁` (`IsTheta.closure_inner_inter₁`).
* A connected set inside `F` that misses `c` lies in one side
  (`IsTheta.subset_inner_or_subset_inner`). If its closure meets a point of `A₁` off `A₂`, it lies
  in the side of `A₁` (`IsTheta.subset_inner₁_of_mem_closure`), so its closure meets `F` only in
  `A₁` (`IsTheta.closure_inter_subset₁`).
-/

@[expose] public section

namespace GraphMinor.Surface.IsTheta

open Set Topology

variable {F F₁ F₂ A₁ A₂ c : Set ℂ} {p q : ℂ}

/-- A point of the crosscut on `F` is one of its two ends, because the open crosscut lies inside
`F`. -/
theorem mem_ends_of_mem_inter (h : IsTheta F F₁ F₂ A₁ A₂ c p q) {z : ℂ} (hzc : z ∈ c)
    (hzF : z ∈ F) : z = p ∨ z = q := by
  by_contra hz
  push Not at hz
  exact (h.inside ⟨hzc, by rintro (rfl | h'); exacts [hz.1 rfl, hz.2 h']⟩).1 hzF

/-- **Lemma 2.** The closure of the side of `A₁` meets the boundary `F` exactly in `A₁`, when the
two ends lie on `A₁`. -/
theorem closure_inner_inter₁ (h : IsTheta F F₁ F₂ A₁ A₂ c p q) (hp : p ∈ A₁) (hq : q ∈ A₁) :
    closure (inner F₁) ∩ F = A₁ := by
  rw [h.parts₁.closure_inner]
  ext z
  constructor
  · rintro ⟨hz | hz, hzF⟩
    · exact absurd hzF (Set.disjoint_left.mp h.inner_disjoint_F hz)
    · rw [h.eq₁] at hz
      rcases hz with hz | hz
      · exact hz
      · rcases h.mem_ends_of_mem_inter hz hzF with rfl | rfl
        exacts [hp, hq]
  · intro hz
    exact ⟨Or.inr (h.eq₁ ▸ Or.inl hz), h.eq ▸ Or.inl hz⟩

/-- **Lemma 2**, for the other side. -/
theorem closure_inner_inter₂ (h : IsTheta F F₁ F₂ A₁ A₂ c p q) (hp : p ∈ A₂) (hq : q ∈ A₂) :
    closure (inner F₂) ∩ F = A₂ :=
  h.symm.closure_inner_inter₁ hp hq

/-- A connected set inside `F` that misses the crosscut lies in one side. The two sides are open
and disjoint (`IsTheta.disjoint_inner`), and they cover the inside of `F` off the crosscut
(`IsTheta.inner_sdiff`). -/
theorem subset_inner_or_subset_inner (h : IsTheta F F₁ F₂ A₁ A₂ c p q) {C : Set ℂ}
    (hC : IsPreconnected C) (hCF : C ⊆ inner F) (hCc : Disjoint C c) :
    C ⊆ inner F₁ ∨ C ⊆ inner F₂ := by
  have hsub : C ⊆ inner F₁ ∪ inner F₂ := by
    rw [← h.inner_sdiff]
    exact fun z hz => ⟨hCF hz, Set.disjoint_left.mp hCc hz⟩
  rcases C.eq_empty_or_nonempty with rfl | ⟨z, hz⟩
  · exact Or.inl (empty_subset _)
  rcases hsub hz with hz1 | hz2
  · exact Or.inl (hC.subset_left_of_subset_union h.parts₁.isOpen_inner h.parts₂.isOpen_inner
      h.disjoint_inner hsub ⟨z, hz, hz1⟩)
  · exact Or.inr (hC.subset_right_of_subset_union h.parts₁.isOpen_inner h.parts₂.isOpen_inner
      h.disjoint_inner hsub ⟨z, hz, hz2⟩)

/-- A connected set inside `F` that misses the crosscut, with a limit point on `A₁` off `A₂`,
lies in the side of `A₁`. Otherwise it lies in the other side, whose closure meets `F` only in
`A₂` (`IsTheta.closure_inner_inter₂`). -/
theorem subset_inner₁_of_mem_closure (h : IsTheta F F₁ F₂ A₁ A₂ c p q) (hp : p ∈ A₂)
    (hq : q ∈ A₂) {C : Set ℂ} (hC : IsPreconnected C) (hCF : C ⊆ inner F) (hCc : Disjoint C c)
    {z : ℂ} (hzC : z ∈ closure C) (hzA₁ : z ∈ A₁) (hzA₂ : z ∉ A₂) : C ⊆ inner F₁ := by
  refine (h.subset_inner_or_subset_inner hC hCF hCc).resolve_right fun h2 => hzA₂ ?_
  rw [← h.closure_inner_inter₂ hp hq]
  exact ⟨closure_mono h2 hzC, h.eq ▸ Or.inl hzA₁⟩

/-- **Lemma 2, as used.** A connected set inside `F` that misses the crosscut, with a limit point
on `A₁` off `A₂`, has its closure meeting `F` only in `A₁`. -/
theorem closure_inter_subset₁ (h : IsTheta F F₁ F₂ A₁ A₂ c p q) (hp₁ : p ∈ A₁) (hq₁ : q ∈ A₁)
    (hp₂ : p ∈ A₂) (hq₂ : q ∈ A₂) {C : Set ℂ} (hC : IsPreconnected C) (hCF : C ⊆ inner F)
    (hCc : Disjoint C c) {z : ℂ} (hzC : z ∈ closure C) (hzA₁ : z ∈ A₁) (hzA₂ : z ∉ A₂) :
    closure C ∩ F ⊆ A₁ := by
  rw [← h.closure_inner_inter₁ hp₁ hq₁]
  exact inter_subset_inter_left _
    (closure_mono (h.subset_inner₁_of_mem_closure hp₂ hq₂ hC hCF hCc hzC hzA₁ hzA₂))

end GraphMinor.Surface.IsTheta
