module

public import GraphMinor.Surface.CutTree
import GraphMinor.GM06.Alg57Crosscut
public import GraphMinor.GM06.Section5StripDisc
import GraphMinor.GM06.Section5LiftedPaths
import GraphMinor.Surface.PlaneDisc

/-!
# Lemma 2 in the lifted strip disc

Lemma 2 of our proof of VI (5.7) (outlined in `Alg57Algorithm.lean`) says that a crosscut of a
closed disc cuts it into two sides, and the closure of each side meets the boundary only in its own
boundary arc. For one linkage path (`k = 1`) our proof uses it in the closed disc `D` between the
chosen lift `L₁` of the path and the next lift `U₁`, which is the one-turn translate.

We first prove a form in the complex plane (`closure_inter_subset_of_crosscut`): a Jordan curve
`F` is the union of two closed sets `A'` and `A''` meeting only at the two ends of a crosscut; a
connected set inside `F` missing the crosscut, with a limit point on `A'` away from the ends, has
its closure meeting `F` only in `A'`. The proof uses the two arcs of `F` from `exists_isCut`: each
of them, without its ends, is connected, so it lies in `A'` or in `A''`.

Then we apply it to the disc `D` between two consecutive lifts (`closure_inter_lift_le`). If the
crosscut runs from `L₁(α)` to `U₁(β)`, then `A'` is the part of the boundary through the inner
cuff: `L₁[0, α]`, the inner cuff interval and `U₁[0, β]`. A connected set in the open disc,
missing the crosscut, with a limit point on the open inner cuff interval, has its closure meeting
`L₁` only in `L₁[0, α]`.
-/

@[expose] public section

namespace GraphMinor.GM06

open Set Topology Real GraphMinor.Surface

local notation "𝕀" => unitInterval

/-- An arc between the two ends of a crosscut, without its ends, lies in one of two closed sets
that cover it and meet only at those ends. -/
theorem arc_interior_subset_or (f : 𝕀 → ℂ) (hf : IsArcMap f) {A' A'' : Set ℂ}
    (hA' : IsClosed A') (hA'' : IsClosed A'') (hcov : range f ⊆ A' ∪ A'')
    (hI : A' ∩ A'' ⊆ {f 0, f 1}) :
    (∀ s : 𝕀, s ≠ 0 → s ≠ 1 → f s ∈ A') ∨ (∀ s : 𝕀, s ≠ 0 → s ≠ 1 → f s ∈ A'') := by
  let g : ℝ → ℂ := fun r => f (projIcc 0 1 zero_le_one r)
  have hg : Continuous g := hf.1.comp continuous_projIcc
  have hS : IsPreconnected (g '' Ioo 0 1) := isPreconnected_Ioo.image g hg.continuousOn
  have hmem : ∀ s : 𝕀, s ≠ 0 → s ≠ 1 → f s ∈ g '' Ioo 0 1 := by
    intro s h0 h1
    refine ⟨s.1, ⟨unitInterval.pos_iff_ne_zero.mpr h0, unitInterval.lt_one_iff_ne_one.mpr h1⟩, ?_⟩
    simp only [g, projIcc_val]
  have hsub : g '' Ioo 0 1 ⊆ A' ∪ A'' := by
    rintro _ ⟨r, -, rfl⟩
    exact hcov (mem_range_self _)
  have hends : g '' Ioo 0 1 ∩ (A' ∩ A'') = ∅ := by
    refine eq_empty_iff_forall_notMem.mpr ?_
    rintro _ ⟨⟨r, hr, rfl⟩, hz⟩
    have hz' := hI hz
    have hr0 : projIcc (0 : ℝ) 1 zero_le_one r ≠ 0 := by
      intro h
      have := congrArg Subtype.val h
      rw [projIcc_of_mem _ ⟨hr.1.le, hr.2.le⟩] at this
      exact hr.1.ne' this
    have hr1 : projIcc (0 : ℝ) 1 zero_le_one r ≠ 1 := by
      intro h
      have := congrArg Subtype.val h
      rw [projIcc_of_mem _ ⟨hr.1.le, hr.2.le⟩] at this
      exact hr.2.ne this
    rcases hz' with h | h
    · exact hr0 (hf.2 h)
    · exact hr1 (hf.2 (mem_singleton_iff.mp h))
  rcases isPreconnected_iff_subset_of_disjoint_closed.mp hS A' A'' hA' hA'' hsub hends with h | h
  · exact Or.inl fun s h0 h1 => h (hmem s h0 h1)
  · exact Or.inr fun s h0 h1 => h (hmem s h0 h1)

/-- **Lemma 2, in the plane.** Let the Jordan curve `F` be the union of two closed sets `A'` and
`A''` that meet only at the ends of a crosscut `e`, both ends in `A'`. A connected set inside `F`
that misses `e`, with a limit point `z` on `A'` other than the ends, has its closure meeting `F`
only in `A'`. -/
theorem closure_inter_subset_of_crosscut {F : Set ℂ} (φ : Circle ≃ₜ F) {e : 𝕀 → ℂ}
    (he : IsArcMap e) (hne : e 0 ≠ e 1) (h0 : e 0 ∈ F) (h1 : e 1 ∈ F)
    (hin : ∀ t, t ≠ 0 → t ≠ 1 → e t ∈ inner F)
    {A' A'' : Set ℂ} (hA' : IsClosed A') (hA'' : IsClosed A'') (hU : A' ∪ A'' = F)
    (hI : A' ∩ A'' ⊆ {e 0, e 1}) (he0 : e 0 ∈ A') (he1 : e 1 ∈ A')
    {C : Set ℂ} (hC : IsPreconnected C) (hCF : C ⊆ inner F) (hCe : Disjoint C (range e))
    {z : ℂ} (hzC : z ∈ closure C) (hzA : z ∈ A') (hz : z ∉ ({e 0, e 1} : Set ℂ)) :
    closure C ∩ F ⊆ A' := by
  have J := isJordanParts φ
  obtain ⟨a, b, hcut⟩ := exists_isCut φ he hne h0 h1 hin
  have hzA'' : z ∉ A'' := fun h => hz (hI ⟨hzA, h⟩)
  -- the arc through `z` lies in `A'`
  have key : ∀ (c d : 𝕀 → ℂ), IsCut F c d e → z ∈ range c → closure C ∩ F ⊆ A' := by
    intro c d hcd hzc
    obtain ⟨s, rfl⟩ := hzc
    have hs0 : s ≠ 0 := fun h => hz (Or.inl (by rw [h, hcd.a_zero]))
    have hs1 : s ≠ 1 := fun h => hz (Or.inr (by rw [h, hcd.a_one]; rfl))
    have hcov : range c ⊆ A' ∪ A'' := by
      rintro _ ⟨t, rfl⟩
      rw [hU]; exact hcd.a_mem t
    have hI' : A' ∩ A'' ⊆ {c 0, c 1} := by rw [hcd.a_zero, hcd.a_one]; exact hI
    have hcA : range c ⊆ A' := by
      rcases arc_interior_subset_or c hcd.arc_a hA' hA'' hcov hI' with h | h
      · rintro _ ⟨t, rfl⟩
        by_cases ht0 : t = 0
        · rw [ht0, hcd.a_zero]; exact he0
        by_cases ht1 : t = 1
        · rw [ht1, hcd.a_one]; exact he1
        exact h t ht0 ht1
      · exact absurd (h s hs0 hs1) hzA''
    have hzd : c s ∉ range d := by
      rintro ⟨t, ht⟩
      rcases hcd.meet s t ht.symm with ⟨h, -⟩ | ⟨h, -⟩
      · exact hs0 h
      · exact hs1 h
    have hθ := hcd.isTheta J
    exact (hθ.closure_inter_subset₁ ⟨0, hcd.a_zero⟩ ⟨1, hcd.a_one⟩ ⟨0, hcd.b_zero⟩ ⟨1, hcd.b_one⟩
      hC hCF hCe hzC (mem_range_self s) hzd).trans hcA
  have hzF : z ∈ F := hU ▸ Or.inl hzA
  rw [← hcut.union] at hzF
  rcases hzF with hza | hzb
  · exact key a b hcut hza
  · exact key b a hcut.symm hzb

section Lift

variable {k : ℕ} {G : Drawing ClosedCylinder}

/-- A lifted linkage curve has radius one only at its start. -/
theorem liftedLinkageCurve_eq_zero_of_radius_one (L : CylinderLinkage k G)
    (hG : IsCylinderSection5Drawing k G) (m : ℤ) {t : 𝕀}
    (ht : (liftedLinkageCurve hG.1 L m t).1 = 1) : t = 0 := by
  by_contra h0
  by_cases h1 : t = 1
  · have h2 := (liftedLinkageCurve_props_raw hG.1 L m).2.2.1
    rw [h1, h2] at ht
    norm_num at ht
  · have := liftedLinkageCurve_interior_radius L hG m
      ⟨unitInterval.pos_iff_ne_zero.mpr h0, unitInterval.lt_one_iff_ne_one.mpr h1⟩
    linarith [this.1]

/-- A lifted linkage curve has radius two only at its end. -/
theorem liftedLinkageCurve_eq_one_of_radius_two (L : CylinderLinkage k G)
    (hG : IsCylinderSection5Drawing k G) (m : ℤ) {t : 𝕀}
    (ht : (liftedLinkageCurve hG.1 L m t).1 = 2) : t = 1 := by
  by_contra h1
  by_cases h0 : t = 0
  · have h2 := (liftedLinkageCurve_props_raw hG.1 L m).2.1
    rw [h0, h2] at ht
    norm_num at ht
  · have := liftedLinkageCurve_interior_radius L hG m
      ⟨unitInterval.pos_iff_ne_zero.mpr h0, unitInterval.lt_one_iff_ne_one.mpr h1⟩
    linarith [this.2]

/-- The start of a lifted linkage curve is the point `(1, 2mπ/k)`. -/
theorem liftedLinkageCurve_zero_eq (L : CylinderLinkage k G) (hk : 0 < k) (m : ℤ) :
    liftedLinkageCurve hk L m 0 = (1, (liftedLinkageCurve hk L m 0).2) :=
  Prod.ext (liftedLinkageCurve_props_raw hk L m).2.1 rfl

/-- The part of the strip boundary through the inner cuff, from `L(α)` to `U(β)`. -/
def innerBoundaryPart (hk : 0 < k) (L : CylinderLinkage k G) (m : ℤ) (α β : 𝕀) : Set (ℝ × ℝ) :=
  liftedLinkageCurve hk L m '' Icc 0 α ∪
    ({1} ×ˢ Icc (liftedLinkageCurve hk L m 0).2 (liftedLinkageCurve hk L (m + 1) 0).2) ∪
    liftedLinkageCurve hk L (m + 1) '' Icc 0 β

/-- The part of the strip boundary through the outer cuff, from `L(α)` to `U(β)`. -/
def outerBoundaryPart (hk : 0 < k) (L : CylinderLinkage k G) (m : ℤ) (α β : 𝕀) : Set (ℝ × ℝ) :=
  liftedLinkageCurve hk L m '' Icc α 1 ∪
    ({2} ×ˢ Icc (liftedLinkageCurve hk L m 1).2 (liftedLinkageCurve hk L (m + 1) 1).2) ∪
    liftedLinkageCurve hk L (m + 1) '' Icc β 1

theorem isCompact_innerBoundaryPart (hk : 0 < k) (L : CylinderLinkage k G) (m : ℤ) (α β : 𝕀) :
    IsCompact (innerBoundaryPart hk L m α β) :=
  ((isClosed_Icc.isCompact.image (liftedLinkageCurve hk L m).continuous).union
    (isCompact_singleton.prod isCompact_Icc)).union
    (isClosed_Icc.isCompact.image (liftedLinkageCurve hk L (m + 1)).continuous)

theorem isCompact_outerBoundaryPart (hk : 0 < k) (L : CylinderLinkage k G) (m : ℤ) (α β : 𝕀) :
    IsCompact (outerBoundaryPart hk L m α β) :=
  ((isClosed_Icc.isCompact.image (liftedLinkageCurve hk L m).continuous).union
    (isCompact_singleton.prod isCompact_Icc)).union
    (isClosed_Icc.isCompact.image (liftedLinkageCurve hk L (m + 1)).continuous)

theorem range_eq_Icc_union (f : 𝕀 → ℝ × ℝ) (α : 𝕀) : range f = f '' Icc 0 α ∪ f '' Icc α 1 := by
  rw [← image_union, ← image_univ]
  congr 1
  ext t
  simp only [mem_univ, mem_union, mem_Icc, true_iff]
  rcases le_total t α with h | h
  · exact Or.inl ⟨unitInterval.nonneg' , h⟩
  · exact Or.inr ⟨h, unitInterval.le_one'⟩

/-- The two parts make up the strip boundary. -/
theorem innerBoundaryPart_union (hk : 0 < k) (L : CylinderLinkage k G) (m : ℤ) (α β : 𝕀) :
    innerBoundaryPart hk L m α β ∪ outerBoundaryPart hk L m α β = liftedStripBoundary hk L m := by
  rw [liftedStripBoundary, innerBoundaryPart, outerBoundaryPart,
    range_eq_Icc_union (liftedLinkageCurve hk L m) α,
    range_eq_Icc_union (liftedLinkageCurve hk L (m + 1)) β]
  ext p
  simp only [mem_union]
  tauto

/-- The two parts meet only at `L(α)` and `U(β)`. -/
theorem innerBoundaryPart_inter (L : CylinderLinkage k G) (hG : IsCylinderSection5Drawing k G)
    (m : ℤ) (α β : 𝕀) :
    innerBoundaryPart hG.1 L m α β ∩ outerBoundaryPart hG.1 L m α β ⊆
      {liftedLinkageCurve hG.1 L m α, liftedLinkageCurve hG.1 L (m + 1) β} := by
  set Γ := liftedLinkageCurve hG.1 L m
  set Γ' := liftedLinkageCurve hG.1 L (m + 1)
  have hinj := (isArcMap_liftedLinkageCurve hG.1 L m).2
  have hinj' := (isArcMap_liftedLinkageCurve hG.1 L (m + 1)).2
  have hdis := disjoint_range_liftedLinkageCurve hG.1 L (show m ≠ m + 1 by omega)
  have hr1 := fun t => liftedLinkageCurve_eq_zero_of_radius_one L hG m (t := t)
  have hr1' := fun t => liftedLinkageCurve_eq_zero_of_radius_one L hG (m + 1) (t := t)
  have hr2 := fun t => liftedLinkageCurve_eq_one_of_radius_two L hG m (t := t)
  have hr2' := fun t => liftedLinkageCurve_eq_one_of_radius_two L hG (m + 1) (t := t)
  have hcross : ∀ s t, Γ s ≠ Γ' t := fun s t h =>
    disjoint_left.mp hdis (mem_range_self s) (h ▸ mem_range_self t)
  rintro p ⟨(⟨hp | hp⟩ | hp), (⟨hq | hq⟩ | hq)⟩
  · obtain ⟨s, hs, rfl⟩ := hp
    obtain ⟨s', hs', hss⟩ := hq
    have := hinj hss
    subst this
    exact Or.inl (by rw [le_antisymm hs.2 hs'.1])
  · obtain ⟨s, hs, rfl⟩ := hp
    have h1 := hr2 _ (by simpa using hq.1)
    subst h1
    exact Or.inl (by rw [le_antisymm hs.2 unitInterval.le_one'])
  · obtain ⟨s, hs, rfl⟩ := hp
    obtain ⟨t, -, ht⟩ := hq
    exact absurd ht.symm (hcross s t)
  · obtain ⟨s', hs', rfl⟩ := hq
    have h0 := hr1 _ (by simpa using hp.1)
    subst h0
    exact Or.inl (by rw [le_antisymm hs'.1 unitInterval.nonneg'])
  · have h1 : p.1 = 1 := by simpa using hp.1
    have h2 : p.1 = 2 := by simpa using hq.1
    rw [h1] at h2; norm_num at h2
  · obtain ⟨t, ht, rfl⟩ := hq
    have h0 := hr1' _ (by simpa using hp.1)
    subst h0
    exact Or.inr (by rw [le_antisymm ht.1 unitInterval.nonneg']; rfl)
  · obtain ⟨t, -, rfl⟩ := hp
    obtain ⟨s, -, hs⟩ := hq
    exact absurd hs (hcross s t)
  · obtain ⟨t, ht, rfl⟩ := hp
    have h1 := hr2' _ (by simpa using hq.1)
    subst h1
    exact Or.inr (by rw [le_antisymm ht.2 unitInterval.le_one']; rfl)
  · obtain ⟨t, ht, rfl⟩ := hp
    obtain ⟨t', ht', htt⟩ := hq
    have := hinj' htt
    subst this
    exact Or.inr (by rw [le_antisymm ht.2 ht'.1]; rfl)

/-- **Lemma 2 in the lifted strip disc.** Let `D` be the closed disc bounded by the lifts `Γ = L`
and `Γ' = U` of index `m` and `m + 1` and the two cuff intervals, and let `c` be a crosscut of `D`
from `Γ α` to `Γ' β`. A connected set `C` in the open disc that misses `c`, with a limit point on
the open inner cuff interval, has its closure meeting `Γ` only in `Γ [0, α]`. -/
theorem le_of_mem_closure_of_crosscut (L : CylinderLinkage k G)
    (hG : IsCylinderSection5Drawing k G) (m : ℤ)
    {D : Set (ℝ × ℝ)} (hD : IsClosedDisc D) (hBd : discBd D = liftedStripBoundary hG.1 L m)
    {c : 𝕀 → ℝ × ℝ} (hc : IsArcMap c) {α β : 𝕀} (hc0 : c 0 = liftedLinkageCurve hG.1 L m α)
    (hc1 : c 1 = liftedLinkageCurve hG.1 L (m + 1) β)
    (hcin : ∀ t, t ≠ 0 → t ≠ 1 → c t ∈ D \ discBd D)
    {C : Set (ℝ × ℝ)} (hC : IsPreconnected C) (hCD : C ⊆ D \ discBd D)
    (hCc : Disjoint C (range c)) {y : ℝ}
    (hy : (liftedLinkageCurve hG.1 L m 0).2 < y ∧ y < (liftedLinkageCurve hG.1 L (m + 1) 0).2)
    (hyC : ((1 : ℝ), y) ∈ closure C) {t : 𝕀}
    (ht : liftedLinkageCurve hG.1 L m t ∈ closure C) : t ≤ α := by
  set Γ := liftedLinkageCurve hG.1 L m
  set Γ' := liftedLinkageCurve hG.1 L (m + 1)
  let E : ℝ × ℝ ≃ₜ ℂ := Complex.equivRealProdCLM.symm.toHomeomorph
  obtain ⟨hDC, hbC⟩ := hD.image (f := E) (f' := E.symm) E.continuous.continuousOn
    E.symm.continuous.continuousOn (fun x _ => E.symm_apply_apply x)
  obtain ⟨φ⟩ := hDC.isOArc_discBd
  have hcl := eq_closedInner_of_discBd ⟨φ⟩ hDC rfl
  have hinner : ∀ x ∈ D \ discBd D, E x ∈ inner (discBd (E '' D)) := by
    intro x hx
    have hxD : E x ∈ E '' D := mem_image_of_mem E hx.1
    rw [hcl] at hxD
    rcases hxD with h | h
    · exact h
    · rw [hbC] at h
      obtain ⟨x', hx', hxx⟩ := h
      exact absurd (E.injective hxx ▸ hx') hx.2
  have hbd : ∀ x ∈ liftedStripBoundary hG.1 L m, E x ∈ discBd (E '' D) := by
    intro x hx
    rw [hbC, hBd]
    exact mem_image_of_mem E hx
  have hdis := disjoint_range_liftedLinkageCurve hG.1 L (show m ≠ m + 1 by omega)
  have hL : ∀ s, Γ s ∈ liftedStripBoundary hG.1 L m := fun s =>
    Or.inl (Or.inl (Or.inl (mem_range_self s)))
  have hU : ∀ s, Γ' s ∈ liftedStripBoundary hG.1 L m := fun s =>
    Or.inl (Or.inl (Or.inr (mem_range_self s)))
  have hne : c 0 ≠ c 1 := by
    rw [hc0, hc1]
    intro h
    exact disjoint_left.mp hdis (mem_range_self α) (h ▸ mem_range_self β)
  have he : IsArcMap (E ∘ c) := ⟨E.continuous.comp hc.1, E.injective.comp hc.2⟩
  have hz : ((1 : ℝ), y) ∈ innerBoundaryPart hG.1 L m α β :=
    Or.inl (Or.inr ⟨rfl, hy.1.le, hy.2.le⟩)
  have hzne : E ((1 : ℝ), y) ∉ ({(E ∘ c) 0, (E ∘ c) 1} : Set ℂ) := by
    rintro (h | h)
    · have h' := E.injective h
      rw [hc0] at h'
      have h0 := liftedLinkageCurve_eq_zero_of_radius_one L hG m (t := α)
        (by rw [← h'])
      have h2 : (Γ α).2 = y := by rw [← h']
      rw [h0] at h2
      exact hy.1.ne h2
    · have h' := E.injective (mem_singleton_iff.mp h)
      rw [hc1] at h'
      have h0 := liftedLinkageCurve_eq_zero_of_radius_one L hG (m + 1) (t := β)
        (by rw [← h'])
      have h2 : (Γ' β).2 = y := by rw [← h']
      rw [h0] at h2
      exact hy.2.ne' h2
  have key := closure_inter_subset_of_crosscut φ he (fun h => hne (E.injective h))
    (by rw [Function.comp_apply, hc0]; exact hbd _ (hL α))
    (by rw [Function.comp_apply, hc1]; exact hbd _ (hU β))
    (fun t h0 h1 => hinner _ (hcin t h0 h1))
    ((isCompact_innerBoundaryPart hG.1 L m α β).image E.continuous).isClosed
    ((isCompact_outerBoundaryPart hG.1 L m α β).image E.continuous).isClosed
    (by rw [← image_union, innerBoundaryPart_union, hbC, hBd])
    (by
      rw [← image_inter E.injective]
      rintro _ ⟨x, hx, rfl⟩
      rcases innerBoundaryPart_inter L hG m α β hx with h | h
      · left; rw [Function.comp_apply, hc0, h]
      · right; rw [Function.comp_apply, hc1, mem_singleton_iff.mp h]; rfl)
    (by rw [Function.comp_apply, hc0]; exact mem_image_of_mem E (Or.inl (Or.inl
      ⟨α, ⟨unitInterval.nonneg', le_rfl⟩, rfl⟩)))
    (by rw [Function.comp_apply, hc1]; exact mem_image_of_mem E (Or.inr
      ⟨β, ⟨unitInterval.nonneg', le_rfl⟩, rfl⟩))
    (hC.image E E.continuous.continuousOn)
    (by rintro _ ⟨x, hx, rfl⟩; exact hinner x (hCD hx))
    (by
      rw [range_comp]
      exact (disjoint_image_iff E.injective).mpr hCc)
    (by rw [← E.image_closure]; exact mem_image_of_mem E hyC)
    (mem_image_of_mem E hz) hzne
  have hmem : E (Γ t) ∈ closure (E '' C) ∩ discBd (E '' D) :=
    ⟨by rw [← E.image_closure]; exact mem_image_of_mem E ht, hbd _ (hL t)⟩
  obtain ⟨x, hx, hxe⟩ := key hmem
  have hxt : x = Γ t := E.injective hxe
  subst hxt
  rcases hx with (h | h) | h
  · obtain ⟨s, hs, hst⟩ := h
    rw [← (isArcMap_liftedLinkageCurve hG.1 L m).2 hst]
    exact hs.2
  · have h0 := liftedLinkageCurve_eq_zero_of_radius_one L hG m (t := t) (by simpa using h.1)
    rw [h0]; exact unitInterval.nonneg'
  · obtain ⟨s, -, hs⟩ := h
    exact (disjoint_left.mp hdis (mem_range_self t) (hs ▸ mem_range_self s)).elim

end Lift

end GraphMinor.GM06
