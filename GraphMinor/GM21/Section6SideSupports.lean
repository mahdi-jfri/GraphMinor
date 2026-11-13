module

public import GraphMinor.GM21.Section6Side
public import GraphMinor.GM21.Section6Supports
import GraphMinor.GM12.Section3SubspaceArcs
import GraphMinor.GM17.CuffOrder

/-!
# Graph Minors XXI, Section 6: supports on one side of a line

Let `Σ₁` be a side of a proper line `F` whose ends `a, b` are vertices of `Γ` and whose other points
miss `U(Γ)` (see `Section6Side.lean`). This file compares the supports of `Γ` in `Σ` with the
supports of `Γ ∩ Σ₁` in `Σ₁`.

* A support of `Γ ∩ Σ₁` in `Σ₁` that lies in `bd(Σ)` is a support of `Γ` in `Σ`
  (`supportHasEnds_image`), and a support of `Γ` in `Σ` that lies in `Σ₁` is a support of
  `Γ ∩ Σ₁` in `Σ₁` (`supportHasEnds_preimage`).
* If a vertex lies between two spaces in a support `K` of `Γ ∩ Σ₁` inside `bd(Σ)`, it lies between
  them in `K` read in `Σ` (`liesBetweenInSupport_image`), and so in every support of `Γ` in `Σ` that
  contains `K` (`liesBetweenInSupport_mono`). The last step reads all supports of one cuff as
  intervals of angles.
-/

@[expose] public section

namespace GraphMinor
namespace GM21
namespace Side

open Set Topology Function GraphMinor.Surface GraphMinor.GM19 GraphMinor.GM17
  GraphMinor.GM21.Supports

universe w

variable {S : Type w} [TopologicalSpace S] {Γ : Surface.Drawing S}

/-- If `(α, β) ⊆ [c, d]` and `α < β`, then `c ≤ α` and `β ≤ d`. -/
theorem le_and_le_of_Ioo_subset_Icc {α β c d : ℝ} (hαβ : α < β) (h : Ioo α β ⊆ Icc c d) :
    c ≤ α ∧ β ≤ d := by
  constructor
  · by_contra hlt
    push Not at hlt
    have hx := h (show (α + min c β) / 2 ∈ Ioo α β from
      ⟨by linarith [lt_min hlt hαβ], by linarith [min_le_right c β]⟩)
    linarith [hx.1, min_le_left c β]
  · by_contra hlt
    push Not at hlt
    have hx := h (show (max d α + β) / 2 ∈ Ioo α β from
      ⟨by linarith [max_lt hlt hαβ, le_max_right d α], by linarith [max_lt hlt hαβ]⟩)
    linarith [hx.2, le_max_left d α, max_lt hlt hαβ]

/-- If `u` lies between `s₁` and `s₂` in `F`, it lies between `s₂` and `s₁`. -/
theorem liesBetweenInSupport_symm {F s₁ s₂ : Set S} {u : S}
    (h : LiesBetweenInSupport Γ F s₁ s₂ u) : LiesBetweenInSupport Γ F s₂ s₁ u := by
  obtain ⟨hu, hs₁, hs₂, hs₁F, hs₂F, I₁, I₂, hI₁, hI₂, hun, hint, hsI₁, hsI₂⟩ := h
  exact ⟨hu, hs₂, hs₁, hs₂F, hs₁F, I₂, I₁, hI₂, hI₁, by rw [union_comm]; exact hun,
    by rw [inter_comm]; exact hint, hsI₂, hsI₁⟩

/-- **Betweenness in a larger support.** If `u` lies between the spaces `s₁, s₂` in a support `K`,
and `K` lies in a support `F'`, then `u` lies between `s₁` and `s₂` in `F'`. We read `F'` as an
interval `[t₀, t₁]` of angles on its cuff. The supports `I₁, I₂` with `I₁ ∪ I₂ = K` and
`I₁ ∩ I₂ = {u}` are intervals meeting only at the angle `γ` of `u`, so one of them ends at `γ`
and the other starts there; the spaces lie on the two sides of `γ`. -/
theorem liesBetweenInSupport_mono (hS : IsSurface S)
    (hge2 : ∀ C ∈ cuffs S, 2 ≤ (Γ.V ∩ C).ncard) {K F' s₁ s₂ : Set S} {u : S}
    (hF' : IsSupportOfDrawing Γ F') (hKF : K ⊆ F') (h : LiesBetweenInSupport Γ K s₁ s₂ u) :
    LiesBetweenInSupport Γ F' s₁ s₂ u := by
  obtain ⟨⟨huK, huV⟩, hs₁, hs₂, hs₁K, hs₂K, I₁, I₂, ⟨a₁, b₁, hI₁⟩, ⟨a₂, b₂, hI₂⟩, hun, hinter,
    hsI₁, hsI₂⟩ := h
  obtain ⟨e₀, e₁, hFe⟩ := hF'
  obtain ⟨C, hC, hFC⟩ := exists_cuff_of_supportHasEnds hFe
  set f := cuffHomeo hS hC
  obtain ⟨t₀, -, t₁, ⟨hle, hlt⟩, hends, hFeq, -⟩ := support_eq_cuffPoint_Icc hS hC f hFe hFC
  have hFends := ends_mem_of_supportHasEnds hFe
  have ht₀V : cuffPoint f t₀ ∈ Γ.V := by
    rcases hends with ⟨h, -⟩ | ⟨h, -⟩ <;> rw [h]
    · exact hFends.2.2.1.1
    · exact hFends.2.2.2.1.1
  have ht₁V : cuffPoint f t₁ ∈ Γ.V := by
    rcases hends with ⟨-, h⟩ | ⟨-, h⟩ <;> rw [h]
    · exact hFends.2.2.2.1.1
    · exact hFends.2.2.1.1
  have hI₁F : I₁ ⊆ F' := (subset_union_left.trans hun.le).trans hKF
  have hI₂F : I₂ ⊆ F' := (subset_union_right.trans hun.le).trans hKF
  obtain ⟨c₁, d₁, hc₁, hcd₁, hd₁, -, hI₁eq⟩ :=
    subsupport_eq_cuffPoint_Icc hS hC f hle hlt hFeq hI₁F hI₁
  obtain ⟨c₂, d₂, hc₂, hcd₂, hd₂, -, hI₂eq⟩ :=
    subsupport_eq_cuffPoint_Icc hS hC f hle hlt hFeq hI₂F hI₂
  obtain ⟨α₁, β₁, hα₁, hαβ₁, hβ₁, -, -, -, hs₁eq, -⟩ :=
    space_in_support_eq_Ioo hS hge2 hC f hle hlt ⟨ht₀V, cuffPoint_mem f t₀⟩ hFeq hs₁
      (hs₁K.trans hKF)
  obtain ⟨α₂, β₂, hα₂, hαβ₂, hβ₂, -, -, -, hs₂eq, -⟩ :=
    space_in_support_eq_Ioo hS hge2 hC f hle hlt ⟨ht₀V, cuffPoint_mem f t₀⟩ hFeq hs₂
      (hs₂K.trans hKF)
  set D := Ico t₀ (t₀ + 2 * Real.pi)
  have hinj : InjOn (cuffPoint f) D := cuffPoint_injOn_Ico f t₀
  have hIccD : ∀ {c d : ℝ}, t₀ ≤ c → d ≤ t₁ → Icc c d ⊆ D := fun hc hd x hx =>
    ⟨hc.trans hx.1, (hx.2.trans hd).trans_lt hlt⟩
  have hIooD : ∀ {c d : ℝ}, t₀ ≤ c → d ≤ t₁ → Ioo c d ⊆ D := fun hc hd =>
    Ioo_subset_Icc_self.trans (hIccD hc hd)
  -- The spaces lie in the intervals of `I₁` and `I₂`.
  have h₁ : Ioo α₁ β₁ ⊆ Icc c₁ d₁ := by
    rw [← hinj.image_subset_image_iff (hIooD hα₁ hβ₁) (hIccD hc₁ hd₁), ← hs₁eq, ← hI₁eq]
    exact hsI₁
  have h₂ : Ioo α₂ β₂ ⊆ Icc c₂ d₂ := by
    rw [← hinj.image_subset_image_iff (hIooD hα₂ hβ₂) (hIccD hc₂ hd₂), ← hs₂eq, ← hI₂eq]
    exact hsI₂
  replace h₁ := le_and_le_of_Ioo_subset_Icc hαβ₁ h₁
  replace h₂ := le_and_le_of_Ioo_subset_Icc hαβ₂ h₂
  -- The angle `γ` of `u`.
  have huI₁ : u ∈ I₁ := (hinter.symm ▸ mem_singleton u : u ∈ I₁ ∩ I₂).1
  have huI₂ : u ∈ I₂ := (hinter.symm ▸ mem_singleton u : u ∈ I₁ ∩ I₂).2
  rw [hI₁eq] at huI₁
  obtain ⟨γ, hγ₁, rfl⟩ := huI₁
  rw [hI₂eq] at huI₂
  obtain ⟨γ', hγ₂, hγγ'⟩ := huI₂
  have hγeq : γ' = γ := hinj (hIccD hc₂ hd₂ hγ₂) (hIccD hc₁ hd₁ hγ₁) hγγ'
  subst hγeq
  have honly : ∀ x ∈ Icc c₁ d₁, x ∈ Icc c₂ d₂ → x = γ' := by
    intro x hx₁ hx₂
    have hmem : cuffPoint f x ∈ I₁ ∩ I₂ := by
      rw [hI₁eq, hI₂eq]
      exact ⟨⟨x, hx₁, rfl⟩, ⟨x, hx₂, rfl⟩⟩
    rw [hinter, mem_singleton_iff] at hmem
    exact hinj (hIccD hc₁ hd₁ hx₁) (hIccD hc₁ hd₁ hγ₁) hmem
  -- One interval ends at `γ'` and the other starts there.
  have hc : c₁ = γ' ∨ c₂ = γ' := by
    by_contra hne
    push Not at hne
    have hc₁γ : c₁ < γ' := lt_of_le_of_ne hγ₁.1 hne.1
    have hc₂γ : c₂ < γ' := lt_of_le_of_ne hγ₂.1 hne.2
    set x := (max c₁ c₂ + γ') / 2
    have hx := honly x ⟨by simp only [x]; linarith [le_max_left c₁ c₂, max_lt hc₁γ hc₂γ],
      by simp only [x]; linarith [hγ₁.2, max_lt hc₁γ hc₂γ]⟩
      ⟨by simp only [x]; linarith [le_max_right c₁ c₂, max_lt hc₁γ hc₂γ],
      by simp only [x]; linarith [hγ₂.2, max_lt hc₁γ hc₂γ]⟩
    simp only [x] at hx
    linarith [max_lt hc₁γ hc₂γ]
  have hd : d₁ = γ' ∨ d₂ = γ' := by
    by_contra hne
    push Not at hne
    have hd₁γ : γ' < d₁ := lt_of_le_of_ne hγ₁.2 (Ne.symm hne.1)
    have hd₂γ : γ' < d₂ := lt_of_le_of_ne hγ₂.2 (Ne.symm hne.2)
    set x := (min d₁ d₂ + γ') / 2
    have hx := honly x ⟨by simp only [x]; linarith [hγ₁.1, lt_min hd₁γ hd₂γ],
      by simp only [x]; linarith [min_le_left d₁ d₂, lt_min hd₁γ hd₂γ]⟩
      ⟨by simp only [x]; linarith [hγ₂.1, lt_min hd₁γ hd₂γ],
      by simp only [x]; linarith [min_le_right d₁ d₂, lt_min hd₁γ hd₂γ]⟩
    simp only [x] at hx
    linarith [lt_min hd₁γ hd₂γ]
  rcases hc with hc | hc <;> rcases hd with hd | hd
  · linarith [h₁.1, h₁.2]
  · exact liesBetweenInSupport_symm (liesBetweenInSupport_of_angles hS hC f hlt ht₀V ht₁V hFeq
      hs₂ hs₁ hα₂ hαβ₂ (by linarith [h₂.2]) (by linarith [h₁.1]) hαβ₁ hβ₁ hs₂eq hs₁eq huV)
  · exact liesBetweenInSupport_of_angles hS hC f hlt ht₀V ht₁V hFeq hs₁ hs₂ hα₁ hαβ₁
      (by linarith [h₁.2]) (by linarith [h₂.1]) hαβ₂ hβ₂ hs₁eq hs₂eq huV
  · linarith [h₂.1, h₂.2]

variable {S₁ S₂ F : Set S} {a b : S}

/-- A support of `Γ ∩ S₁` in `S₁` that lies in `bd(S)` is, in `S`, a support of `Γ` with the same
ends. -/
theorem supportHasEnds_image [T2Space S] (h₁ : IsClosed S₁) {I : Set S₁} {u v : S₁}
    (hI : SupportHasEnds (sideDrawing Γ h₁) I u v) (hIbd : I ⊆ Subtype.val ⁻¹' bd S) :
    SupportHasEnds Γ (Subtype.val '' I) u.1 v.1 := by
  rcases hI with ⟨w, ⟨hwV, -⟩, hIw, huw, hvw⟩ | ⟨-, huv, ⟨huV, -⟩, ⟨hvV, -⟩, hline⟩
  · rw [sideDrawing_V] at hwV
    rw [huw, hvw]
    exact Or.inl ⟨w.1, ⟨hwV, hIbd (hIw ▸ rfl)⟩, by rw [hIw, image_singleton], rfl, rfl⟩
  · rw [sideDrawing_V] at huV hvV
    refine Or.inr ⟨image_subset_iff.mpr hIbd, fun h => huv (Subtype.ext h),
      ⟨huV, hIbd hline.left_mem⟩, ⟨hvV, hIbd hline.right_mem⟩,
      GM12.isLineWithEnds_subtype_image hline⟩

/-- A support of `Γ` in `S` that lies in a side `S₁` is, read in `S₁`, a support of `Γ ∩ S₁` with
the same ends. -/
theorem supportHasEnds_preimage [T2Space S] (hS : IsSurface S) (hS₁ : IsSurface S₁) (hS₂ : IsSurface S₂)
    (hun : S₁ ∪ S₂ = univ) (hint : S₁ ∩ S₂ = F) (hF : IsLineWithEnds F a b)
    (h₁ : IsClosed S₁) {K : Set S} {u v : S₁} (hK : SupportHasEnds Γ K u.1 v.1)
    (hKS₁ : K ⊆ S₁) :
    SupportHasEnds (sideDrawing Γ h₁) (Subtype.val ⁻¹' K) u v := by
  have hbd : ∀ x : S₁, x.1 ∈ bd S → x ∈ bd S₁ := fun x hx =>
    (mem_bd_side_iff' hS hS₁ hS₂ hun hint hF).mpr (Or.inr hx)
  rcases hK with ⟨w, ⟨hwV, hwbd⟩, hKw, huw, hvw⟩ | ⟨hKbd, huv, ⟨huV, hubd⟩, ⟨hvV, hvbd⟩, hline⟩
  · have huv : u = v := Subtype.ext (huw.trans hvw.symm)
    subst huv hKw
    have hu : u.1 ∈ Γ.V ∧ u.1 ∈ bd S := by rw [huw]; exact ⟨hwV, hwbd⟩
    refine Or.inl ⟨u, ⟨?_, hbd u hu.2⟩, ?_, rfl, rfl⟩
    · rw [sideDrawing_V]
      exact hu.1
    · ext x
      simp only [mem_preimage, mem_singleton_iff, ← huw, Subtype.ext_iff]
  · refine Or.inr ⟨fun x hx => hbd x (hKbd hx), fun h => huv (congrArg Subtype.val h),
      ⟨?_, hbd u hubd⟩, ⟨?_, hbd v hvbd⟩, GM12.isLineWithEnds_subtype_preimage hKS₁ hline⟩
    · rw [sideDrawing_V]; exact huV
    · rw [sideDrawing_V]; exact hvV

/-- If `u` lies between the spaces `s₁, s₂` in a support `K` of `Γ ∩ S₁` that lies in `bd(S)`,
then in `S` the point `u` lies between the spaces `val '' s₁` and `val '' s₂` of `Γ` in the support
`val '' K`. -/
theorem liesBetweenInSupport_image [T2Space S] (hS : IsSurface S) (h₁ : IsClosed S₁) (h₂ : IsClosed S₂)
    (hun : S₁ ∪ S₂ = univ) (hint : S₁ ∩ S₂ = F) (hFcl : IsClosed F)
    (hFbd : F ∩ bd S = {a, b}) (haV : a ∈ Γ.V) (hbV : b ∈ Γ.V) {K s₁ s₂ : Set S₁} {u : S₁}
    (h : LiesBetweenInSupport (sideDrawing Γ h₁) K s₁ s₂ u) (hKbd : K ⊆ Subtype.val ⁻¹' bd S) :
    LiesBetweenInSupport Γ (Subtype.val '' K) (Subtype.val '' s₁) (Subtype.val '' s₂) u.1 := by
  obtain ⟨⟨huK, huV⟩, hs₁, hs₂, hs₁K, hs₂K, I₁, I₂, ⟨a₁, b₁, hI₁⟩, ⟨a₂, b₂, hI₂⟩, hunion, hinter,
    hsI₁, hsI₂⟩ := h
  rw [sideDrawing_V] at huV
  have hI₁K : I₁ ⊆ K := hunion ▸ subset_union_left
  have hI₂K : I₂ ⊆ K := hunion ▸ subset_union_right
  refine ⟨⟨⟨u, huK, rfl⟩, huV⟩,
    image_mem_drawingSpaces hS h₁ h₂ hun hint hFcl hFbd haV hbV hs₁ (hs₁K.trans hKbd),
    image_mem_drawingSpaces hS h₁ h₂ hun hint hFcl hFbd haV hbV hs₂ (hs₂K.trans hKbd),
    image_mono hs₁K, image_mono hs₂K, Subtype.val '' I₁, Subtype.val '' I₂,
    ⟨_, _, supportHasEnds_image h₁ hI₁ (hI₁K.trans hKbd)⟩,
    ⟨_, _, supportHasEnds_image h₁ hI₂ (hI₂K.trans hKbd)⟩, ?_, ?_, image_mono hsI₁,
    image_mono hsI₂⟩
  · rw [← image_union, hunion]
  · rw [← image_inter Subtype.val_injective, hinter, image_singleton]

end Side
end GM21
end GraphMinor
