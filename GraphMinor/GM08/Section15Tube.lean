module

public import GraphMinor.GM08.Section15Defs
public import GraphMinor.GM12.Section3HomeoWalks
public import Mathlib.Data.ENat.Lattice

/-!
# Graph Minors VIII, Section 15: Tubes, Framings, Width, Length, and $\mathcal{A}(k, r, s)$

This file formalizes tubes, sub-tubes, width, length, framings, tubular grafts, the classes
$\mathcal{G}(r, k)$ (`tubularClass`) and $\mathcal{A}(k, r, s)$ (`classA`), and their invariance
under homeomorphisms of cylinders and isomorphisms of grafts (Robertson and Seymour,
*Graph Minors. VIII. A Kuratowski Theorem for General Surfaces*, J. Combin. Theory Ser. B **48**
(1990), 255–288, Section 15, pages 280–282).
-/

@[expose] public section

namespace GraphMinor.GM08

open Set Function Topology Classical Graph GraphMinor.Surface GraphMinor.GM11

universe u v u' v' w w'

/-! ## 1. Small arcs on hoops and subdrawings on $\Sigma(F_1, F_2)$ -/

section SubArcAndInterSet

variable {S : Type w} [TopologicalSpace S]

/-- Reversing the ends of a `[0, 1]`-arc via `t ↦ 1 - t`. -/
theorem IsLineWithEnds.symm {I : Set S} {u v : S} (h : IsLineWithEnds I u v) :
    IsLineWithEnds I v u := by
  obtain ⟨f, h0, h1⟩ := h
  let rev : unitInterval ≃ₜ unitInterval :=
    { toFun := fun t => unitInterval.symm t
      invFun := fun t => unitInterval.symm t
      left_inv := fun t => by simp
      right_inv := fun t => by simp
      continuous_toFun := unitInterval.continuous_symm
      continuous_invFun := unitInterval.continuous_symm }
  refine ⟨rev.trans f, ?_, ?_⟩
  · simpa [rev] using h1
  · simpa [rev] using h0

/-- Extracting a sub-`[0, 1]`-arc of `I` on `[t₁, t₂]` (`t₁ < t₂` in `unitInterval`). -/
theorem subArc_of_lt [T2Space S] {f : unitInterval → S} (hf_cont : Continuous f)
    (hf_inj : Injective f) {t₁ t₂ : unitInterval} (hlt : t₁ < t₂) :
    IsLineWithEnds (f '' Icc t₁ t₂) (f t₁) (f t₂) := by
  have hgap : (0 : ℝ) < (t₂ : ℝ) - t₁ := sub_pos.mpr hlt
  let r : unitInterval → unitInterval := fun σ =>
    ⟨t₁ + σ * ((t₂ : ℝ) - t₁), by
      have h3 := mul_nonneg σ.2.1 hgap.le
      have h4 := mul_le_of_le_one_left hgap.le σ.2.2
      exact ⟨by linarith [t₁.2.1], by linarith [t₂.2.2]⟩⟩
  have hrc : Continuous r := Continuous.subtype_mk (by fun_prop) _
  have hrinj : Injective r := fun σ₁ σ₂ heq => by
    have hval := congrArg Subtype.val heq
    dsimp [r] at hval
    have hmul : (σ₁ : ℝ) * ((t₂ : ℝ) - t₁) = (σ₂ : ℝ) * ((t₂ : ℝ) - t₁) := by linarith
    exact Subtype.ext (mul_right_cancel₀ hgap.ne' hmul)
  have hrange : range (f ∘ r) = f '' Icc t₁ t₂ := by
    ext x
    constructor
    · rintro ⟨σ, rfl⟩
      refine ⟨r σ, ⟨?_, ?_⟩, rfl⟩
      · change (t₁ : ℝ) ≤ t₁ + σ * ((t₂ : ℝ) - t₁)
        linarith [mul_nonneg σ.2.1 hgap.le]
      · change (t₁ : ℝ) + σ * ((t₂ : ℝ) - t₁) ≤ t₂
        linarith [mul_le_of_le_one_left hgap.le σ.2.2]
    · rintro ⟨t, ⟨ht1, ht2⟩, rfl⟩
      let σ : unitInterval := ⟨((t : ℝ) - t₁) / ((t₂ : ℝ) - t₁),
        div_nonneg (sub_nonneg.mpr ht1) hgap.le,
        (div_le_one hgap).mpr (sub_le_sub_right (Subtype.coe_le_coe.mpr ht2) _)⟩
      refine ⟨σ, congrArg f (Subtype.ext ?_)⟩
      change (t₁ : ℝ) + ((t : ℝ) - t₁) / ((t₂ : ℝ) - t₁) * ((t₂ : ℝ) - t₁) = t
      rw [div_mul_cancel₀ _ hgap.ne']
      ring
  have hemb : IsEmbedding (f ∘ r) := (hf_cont.comp hrc).isClosedEmbedding (hf_inj.comp hrinj)
    |>.isEmbedding
  let eI : unitInterval ≃ₜ f '' Icc t₁ t₂ :=
    (Homeomorph.Set.univ unitInterval).symm.trans
      ((hemb.homeomorphImage univ).trans (Homeomorph.setCongr (image_univ.trans hrange)))
  refine ⟨eI, ?_, ?_⟩
  · change f (r 0) = f t₁
    congr 1; apply Subtype.ext; simp [r]
  · change f (r 1) = f t₂
    congr 1; apply Subtype.ext; simp [r]

/-- On any hoop `F` in a T2 space `S`, given `w ∈ F` and a finite set `B ⊆ S`, there is a
`[0, 1]`-arc `I ⊆ F` with ends `u ∈ F` and `w` such that `I ∩ B ⊆ {w}`. -/
theorem IsHoop.exists_subArc_avoiding [T2Space S] {F : Set S} (hF : IsHoop F) {w : S}
    (hw : w ∈ F) {B : Set S} (hB : B.Finite) :
    ∃ (I : Set S) (u : S), I ⊆ F ∧ u ∈ F ∧ IsLineWithEnds I u w ∧ I ∩ B ⊆ {w} := by
  obtain ⟨φ⟩ := hF.1
  let c₀ : Circle := φ.symm ⟨w, hw⟩
  have hφc₀ : (φ c₀).1 = w := by simp [c₀]
  have hinj : Injective (fun c : Circle => (φ c).1) := Subtype.val_injective.comp φ.injective
  have hKfin : ((fun c : Circle => (φ c).1) ⁻¹' (B \ {w})).Finite :=
    hB.sdiff.preimage hinj.injOn
  have hKopen : IsOpen (((fun c : Circle => (φ c).1) ⁻¹' (B \ {w}))ᶜ) :=
    hKfin.isClosed.isOpen_compl
  have hc₀_mem : c₀ ∈ (((fun c : Circle => (φ c).1) ⁻¹' (B \ {w}))ᶜ) := by
    simp [hφc₀]
  let g : ℝ → Circle := fun t => c₀ * Circle.exp t
  have hg_cont : Continuous g := continuous_const.mul Circle.exp.continuous
  have h0_mem : (0 : ℝ) ∈ g ⁻¹' (((fun c : Circle => (φ c).1) ⁻¹' (B \ {w}))ᶜ) := by
    simpa [g] using hc₀_mem
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp (hKopen.preimage hg_cont) 0 h0_mem
  let δ : ℝ := min (ε / 2) (Real.pi / 2)
  have hδ_pos : 0 < δ := lt_min (half_pos hε) (half_pos Real.pi_pos)
  have hδ_lt_ε : δ < ε := lt_of_le_of_lt (min_le_left _ _) (half_lt_self hε)
  have hδ_lt_pi : δ < Real.pi := lt_of_le_of_lt (min_le_right _ _) (half_lt_self Real.pi_pos)
  let ψ : unitInterval → S := fun t => (φ (g (δ * (1 - t.1)))).1
  have hψ_cont : Continuous ψ :=
    continuous_subtype_val.comp (φ.continuous.comp (hg_cont.comp
      (continuous_const.mul (continuous_const.sub continuous_subtype_val))))
  have hψ_inj : Injective ψ := by
    intro t₁ t₂ heq
    have hge := hinj heq
    have hexp : Circle.exp (δ * (1 - t₁.1)) = Circle.exp (δ * (1 - t₂.1)) :=
      mul_left_cancel hge
    have hexp1 : Circle.exp (δ * (t₂.1 - t₁.1)) = 1 := by
      have hmul : Circle.exp (δ * (1 - t₁.1)) * (Circle.exp (δ * (1 - t₂.1)))⁻¹ = 1 :=
        mul_inv_eq_one.mpr hexp
      rw [← Circle.exp_neg, ← Circle.exp_add] at hmul
      convert hmul using 2
      ring
    obtain ⟨n, hn⟩ := Circle.exp_eq_one.mp hexp1
    have hdiff_le : |t₂.1 - t₁.1| ≤ 1 := by
      rw [abs_sub_le_iff]
      exact ⟨by linarith [t₁.2.1, t₂.2.2], by linarith [t₂.2.1, t₁.2.2]⟩
    have habs : |δ * (t₂.1 - t₁.1)| < Real.pi := by
      rw [abs_mul, abs_of_pos hδ_pos]
      calc δ * |t₂.1 - t₁.1| ≤ δ * 1 := mul_le_mul_of_nonneg_left hdiff_le hδ_pos.le
        _ = δ := mul_one δ
        _ < Real.pi := hδ_lt_pi
    have hn0 : n = 0 := by
      by_contra hn0
      have h1 : (1 : ℝ) ≤ |(n : ℝ)| := by exact_mod_cast Int.one_le_abs hn0
      have h2pi : 2 * Real.pi ≤ |(n : ℝ) * (2 * Real.pi)| := by
        rw [abs_mul, abs_of_pos (mul_pos zero_lt_two Real.pi_pos)]
        nlinarith [Real.pi_pos]
      rw [← hn] at h2pi
      linarith [Real.pi_pos]
    have hsub0 : δ * (t₂.1 - t₁.1) = 0 := by simpa [hn0] using hn
    have ht : t₁.1 = t₂.1 := by
      rcases mul_eq_zero.mp hsub0 with h0 | h0
      · linarith
      · linarith
    exact Subtype.ext ht
  have hψ_emb : IsEmbedding ψ := hψ_cont.isClosedEmbedding hψ_inj |>.isEmbedding
  let eI : unitInterval ≃ₜ range ψ :=
    (Homeomorph.Set.univ unitInterval).symm.trans
      ((hψ_emb.homeomorphImage univ).trans (Homeomorph.setCongr image_univ))
  refine ⟨range ψ, ψ 0, ?_, (φ (g (δ * (1 - 0)))).2, ⟨eI, rfl, ?_⟩, ?_⟩
  · rintro _ ⟨t, rfl⟩
    exact (φ _).2
  · change ψ 1 = w
    simp [ψ, g, hφc₀]
  · rintro x ⟨⟨t, rfl⟩, hxB⟩
    by_contra hxw
    have ht_dist : dist (δ * (1 - t.1)) 0 < ε := by
      rw [Real.dist_eq, sub_zero, abs_of_nonneg (mul_nonneg hδ_pos.le (sub_nonneg.mpr t.2.2))]
      calc δ * (1 - t.1) ≤ δ * 1 :=
          mul_le_mul_of_nonneg_left (by linarith [t.2.1]) hδ_pos.le
        _ = δ := mul_one δ
        _ < ε := hδ_lt_ε
    exact hball ht_dist ⟨hxB, hxw⟩

/-- For a closed subset `X ⊆ S`, `(Γ.interSet X).V = Γ.V ∩ X`. -/
theorem interSet_V_of_isClosed [T1Space S] (Γ : Drawing S) {X : Set S} (hX : IsClosed X) :
    (Γ.interSet X).V = Γ.V ∩ X := by
  apply Subset.antisymm
  · rintro x (hx | hx)
    · exact ⟨hx.2, hx.1.2⟩
    · obtain ⟨e, he, hxe⟩ := mem_iUnion₂.mp hx
      exact ⟨hxe.2, closure_minimal he.1.2 hX hxe.1⟩
  · intro x hx
    exact Or.inl ⟨hx, hx.1⟩

theorem interSet_E [T1Space S] (Γ : Drawing S) (X : Set S) :
    (Γ.interSet X).E = {e ∈ Γ.E | e ⊆ X} := by
  rw [Drawing.interSet, Γ.span_E]
  ext e
  exact ⟨fun ⟨⟨he, hs⟩, _⟩ => ⟨he, hs⟩, fun ⟨he, hs⟩ => ⟨⟨he, hs⟩, he⟩⟩

theorem interSet_U_subset_of_isClosed [T1Space S] (Γ : Drawing S) {X : Set S} (hX : IsClosed X) :
    (Γ.interSet X).U ⊆ Γ.U ∩ X := by
  have hV := interSet_V_of_isClosed Γ hX
  rintro x (hx | hx)
  · have hx' : x ∈ Γ.V ∩ X := hV ▸ hx
    exact ⟨Γ.V_subset_U hx'.1, hx'.2⟩
  · obtain ⟨e, he, hxe⟩ := mem_iUnion₂.mp hx
    exact ⟨Γ.closure_subset_U he.2 hxe, closure_minimal he.1.2 hX hxe⟩

theorem interSet_isNormal_of_isClosed [T1Space S] (Γ : Drawing S) {X Z : Set S} (hX : IsClosed X)
    (hZ : Z ⊆ X) (hN : Γ.IsNormal Z) : (Γ.interSet X).IsNormal Z := by
  rw [Drawing.IsNormal, interSet_V_of_isClosed Γ hX]
  rintro x ⟨hxZ, hxU⟩
  have hxUX := interSet_U_subset_of_isClosed Γ hX hxU
  exact ⟨hN ⟨hxZ, hxUX.1⟩, hZ hxZ⟩

theorem interSet_interSet_of_isClosed [T1Space S] (Γ : Drawing S) {X Y : Set S}
    (hX : IsClosed X) (hY : IsClosed Y) (hYX : Y ⊆ X) :
    (Γ.interSet X).interSet Y = Γ.interSet Y := by
  apply Drawing.ext_of_V_E
  · rw [interSet_V_of_isClosed _ hY, interSet_V_of_isClosed _ hX, interSet_V_of_isClosed _ hY,
      inter_assoc, inter_eq_self_of_subset_right hYX]
  · rw [interSet_E, interSet_E, interSet_E]
    ext e
    exact ⟨fun ⟨⟨he, _⟩, heY⟩ => ⟨he, heY⟩, fun ⟨he, heY⟩ => ⟨⟨he, heY.trans hYX⟩, heY⟩⟩

theorem interSet_eq_self_of_U_subset [T1Space S] (Γ : Drawing S) {X : Set S} (h : Γ.U ⊆ X) :
    Γ.interSet X = Γ := by
  apply Drawing.ext_of_V_E
  · apply Subset.antisymm (Γ.spanV_subset _ _)
    intro x hx
    exact Or.inl ⟨⟨hx, h (Γ.V_subset_U hx)⟩, hx⟩
  · rw [interSet_E]
    ext e
    exact ⟨fun he => he.1, fun he => ⟨he, fun x hx => h (he.2.1 hx).1⟩⟩

theorem interSet_isLink_iff_of_isClosed [T1Space S] (Γ : Drawing S) {X : Set S} (hX : IsClosed X)
    {e : Set S} {x y : S} :
    (Γ.interSet X).toGraph.IsLink e x y ↔ e ⊆ X ∧ Γ.toGraph.IsLink e x y := by
  change (e ∈ (Γ.interSet X).E ∧ x ∈ (Γ.interSet X).V ∧ y ∈ (Γ.interSet X).V ∧
      closure e ∩ (Γ.interSet X).V = {x, y}) ↔
    e ⊆ X ∧ e ∈ Γ.E ∧ x ∈ Γ.V ∧ y ∈ Γ.V ∧ closure e ∩ Γ.V = {x, y}
  rw [interSet_E, interSet_V_of_isClosed Γ hX]
  constructor
  · rintro ⟨⟨he, heX⟩, ⟨hxV, _⟩, ⟨hyV, _⟩, hcl⟩
    have hclX : closure e ∩ (Γ.V ∩ X) = closure e ∩ Γ.V := by
      ext z
      exact ⟨fun ⟨h1, h2, _⟩ => ⟨h1, h2⟩, fun ⟨h1, h2⟩ => ⟨h1, h2, closure_minimal heX hX h1⟩⟩
    exact ⟨heX, he, hxV, hyV, hclX ▸ hcl⟩
  · rintro ⟨heX, he, hxV, hyV, hcl⟩
    have hclX : closure e ∩ (Γ.V ∩ X) = closure e ∩ Γ.V := by
      ext z
      exact ⟨fun ⟨h1, h2, _⟩ => ⟨h1, h2⟩, fun ⟨h1, h2⟩ => ⟨h1, h2, closure_minimal heX hX h1⟩⟩
    have hxX : x ∈ X := by
      have : x ∈ closure e ∩ Γ.V := hcl ▸ mem_insert x {y}
      exact closure_minimal heX hX this.1
    have hyX : y ∈ X := by
      have : y ∈ closure e ∩ Γ.V := hcl ▸ mem_insert_of_mem x rfl
      exact closure_minimal heX hX this.1
    exact ⟨⟨he, heX⟩, ⟨hxV, hxX⟩, ⟨hyV, hyX⟩, hclX.trans hcl⟩

/-- If `H` is a `Γ`-normal hoop in `Σ(F₁, F₂)` (with `cap.disc₁ F₁ ⊆ cap.disc₁ H ⊆ cap.disc₁ F₂`),
every edge `e ∈ Γ.E` contained in `Σ(F₁, F₂)` lies either in `Σ(F₁, H)` or in `Σ(H, F₂)`, and
never in both. -/
theorem CylinderSphereCap.edge_subset_left_or_right (cap : CylinderSphereCap S) (hS : IsCylinder S)
    (Γ : Drawing S) {F₁ H F₂ e : Set S} (hF₁ : IsHoop F₁) (hH : IsHoop H) (hF₂ : IsHoop F₂)
    (hle1 : cap.disc₁ hS.1 hF₁ ⊆ cap.disc₁ hS.1 hH)
    (hle2 : cap.disc₁ hS.1 hH ⊆ cap.disc₁ hS.1 hF₂)
    (hNH : Γ.IsNormal H) (he : e ∈ Γ.E) (he_sub : e ⊆ cylinderBetween F₁ F₂) :
    (e ⊆ cylinderBetween F₁ H ∧ ¬ e ⊆ cylinderBetween H F₂) ∨
      (e ⊆ cylinderBetween H F₂ ∧ ¬ e ⊆ cylinderBetween F₁ H) := by
  have he_dis_H : Disjoint e H := by
    refine disjoint_left.mpr fun x hxe hxH => ?_
    exact (he.2.1 hxe).2 (hNH ⟨hxH, (he.2.1 hxe).1⟩)
  have hnot_both : ¬ (e ⊆ cylinderBetween F₁ H ∧ e ⊆ cylinderBetween H F₂) := by
    rintro ⟨h1, h2⟩
    obtain ⟨x, hxe⟩ := he.2.1 |> fun _ => he.1
    have hxH : x ∈ H := cap.cylinderBetween_inter hS hF₁ hH hF₂ hle1 hle2 ▸ ⟨h1 hxe, h2 hxe⟩
    exact disjoint_left.mp he_dis_H hxe hxH
  have he_cov : e ⊆ cap.side₁ hS.1 hH ∪ cap.side₂ hS.1 hH := by
    rw [cap.side₁_union_side₂ hS.1 hH]
    exact fun x hxe => ⟨mem_univ x, disjoint_left.mp he_dis_H hxe⟩
  have he_prec : IsPreconnected e := he.2.2.1.isConnected.isPreconnected
  have hsub_or : e ⊆ cap.side₁ hS.1 hH ∨ e ⊆ cap.side₂ hS.1 hH := by
    by_cases hne1 : (e ∩ cap.side₁ hS.1 hH).Nonempty
    · left
      intro x hxe
      rcases he_cov hxe with hx1 | hx2
      · exact hx1
      · obtain ⟨y, _, hy1, hy2⟩ := he_prec _ _ (cap.isOpen_side₁ hS.1 hH)
          (cap.isOpen_side₂ hS.1 hH) he_cov hne1 ⟨x, hxe, hx2⟩
        exact absurd hy2 (disjoint_left.mp (cap.disjoint_side₁_side₂ hS.1 hH) hy1)
    · right
      intro x hxe
      exact (he_cov hxe).resolve_left (fun hx1 => hne1 ⟨x, hxe, hx1⟩)
  rw [cap.cylinderBetween_eq_of_disc₁_subset hS hF₁ hF₂ (hle1.trans hle2)] at he_sub
  rcases hsub_or with h1 | h2
  · left
    have hsubL : e ⊆ cylinderBetween F₁ H := by
      rw [cap.cylinderBetween_eq_of_disc₁_subset hS hF₁ hH hle1]
      intro x hxe
      exact ⟨(cap.side₁_eq_preimage_diff hS.1 hH ▸ h1 hxe).1, (he_sub hxe).2⟩
    exact ⟨hsubL, fun hsubR => hnot_both ⟨hsubL, hsubR⟩⟩
  · right
    have hsubR : e ⊆ cylinderBetween H F₂ := by
      rw [cap.cylinderBetween_eq_of_disc₁_subset hS hH hF₂ hle2]
      intro x hxe
      exact ⟨(he_sub hxe).1, (cap.side₂_eq_preimage_diff hS.1 hH ▸ h2 hxe).1⟩
    exact ⟨hsubR, fun hsubL => hnot_both ⟨hsubL, hsubR⟩⟩

/-- When `cap.disc₁ F₁ ⊆ cap.disc₁ F₂`, `cap.disc₁ F₁ ∩ cap.disc₂ F₂ = cap.j '' (F₁ ∩ F₂)`. -/
theorem CylinderSphereCap.disc₁_inter_disc₂_eq_image_inter (cap : CylinderSphereCap S)
    (hS : IsSurface S) {F₁ F₂ : Set S} (hF₁ : IsHoop F₁) (hF₂ : IsHoop F₂)
    (hle : cap.disc₁ hS hF₁ ⊆ cap.disc₁ hS hF₂) :
    cap.disc₁ hS hF₁ ∩ cap.disc₂ hS hF₂ = cap.j '' (F₁ ∩ F₂) := by
  obtain ⟨hE₁, -, hbE₁, -, -, -, -, -⟩ := cap.disc₁_disc₂_spec hS hF₁
  obtain ⟨-, -, -, hbG₂, -, hcapG, -, -⟩ := cap.disc₁_disc₂_spec hS hF₂
  apply Subset.antisymm
  · rintro z ⟨hz1, hz2⟩
    have hzF₂ : z ∈ cap.j '' F₂ := hcapG ▸ ⟨hle hz1, hz2⟩
    obtain ⟨x, hx₂, rfl⟩ := hzF₂
    have hx₁ : x ∈ F₁ := by
      by_contra hnx₁
      have hzIntE : cap.j x ∈ discInt (cap.disc₁ hS hF₁) :=
        ⟨hz1, hbE₁ ▸ fun ⟨y, hy, he⟩ => hnx₁ (cap.inj he ▸ hy)⟩
      have hzIntG : cap.j x ∈ discInt (cap.disc₁ hS hF₂) :=
        discInt_mono cap.isManifoldPoint_Z hE₁ hle hzIntE
      exact hzIntG.2 ((cap.disc₁_disc₂_spec hS hF₂).2.2.1 ▸ mem_image_of_mem _ hx₂)
    exact ⟨x, ⟨hx₁, hx₂⟩, rfl⟩
  · rintro _ ⟨x, ⟨hx₁, hx₂⟩, rfl⟩
    exact ⟨Surface.discBd_subset _ (hbE₁ ▸ mem_image_of_mem _ hx₁),
      Surface.discBd_subset _ (hbG₂ ▸ mem_image_of_mem _ hx₂)⟩

end SubArcAndInterSet

/-! ## 2. Tubes, Sub-tubes, Width, and Length -/

/-- A *tube* in a cylinder $\Sigma$ is a triple $(\Gamma, F_1, F_2)$, where $\Gamma$ is a drawing
in $\Sigma$ and $F_1, F_2$ are $\Gamma$-normal laminar hoops such that
$U(\Gamma) \subseteq \Sigma(F_1, F_2)$.
Graph Minors VIII, Section 15 (page 280):
"A tube in a cylinder $\Sigma$ is a triple $(\Gamma, F_1, F_2)$, where $\Gamma$ is a drawing in
$\Sigma$ and $F_1$, $F_2$ are $\Gamma$-normal laminar hoops such that
$U(\Gamma) \subseteq \Sigma(F_1, F_2)$." -/
structure Tube (S : Type w) [TopologicalSpace S] where
  /-- The drawing $\Gamma$ in $\Sigma$. -/
  Γ : Drawing S
  /-- The first bounding hoop $F_1$. -/
  F₁ : Set S
  /-- The second bounding hoop $F_2$. -/
  F₂ : Set S
  /-- $\Sigma$ is a cylinder. -/
  isCylinder : IsCylinder S
  /-- $F_1, F_2$ are laminar hoops in $\Sigma$. -/
  laminar : AreLaminarHoops F₁ F₂
  /-- $F_1$ is $\Gamma$-normal. -/
  isNormal_F₁ : Γ.IsNormal F₁
  /-- $F_2$ is $\Gamma$-normal. -/
  isNormal_F₂ : Γ.IsNormal F₂
  /-- $U(\Gamma) \subseteq \Sigma(F_1, F_2)$. -/
  U_subset : Γ.U ⊆ cylinderBetween F₁ F₂

namespace Tube

section Basic

variable {S : Type w} [TopologicalSpace S] (τ : Tube S)

theorem isHoop_F₁ : IsHoop τ.F₁ := τ.laminar.2.1

theorem isHoop_F₂ : IsHoop τ.F₂ := τ.laminar.2.2.1

theorem t2Space (τ : Tube S) : T2Space S := τ.isCylinder.1.2.1

/-- Reversing the two bounding hoops $F_1, F_2$ of a tube. -/
def symm (τ : Tube S) : Tube S where
  Γ := τ.Γ
  F₁ := τ.F₂
  F₂ := τ.F₁
  isCylinder := τ.isCylinder
  laminar := τ.laminar.symm
  isNormal_F₁ := τ.isNormal_F₂
  isNormal_F₂ := τ.isNormal_F₁
  U_subset := cylinderBetween_comm τ.F₁ τ.F₂ ▸ τ.U_subset

/-- The sub-tube $(\Gamma \cap \Sigma(F_1', F_2'), F_1', F_2')$ cut out by $\Gamma$-normal laminar
hoops $F_1', F_2' \subseteq \Sigma(F_1, F_2)$.
Graph Minors VIII, Section 15 (pages 280–281). -/
def subTube (τ : Tube S) {F₁' F₂' : Set S} (hlam : AreLaminarHoops F₁' F₂')
    (hN₁ : τ.Γ.IsNormal F₁') (hN₂ : τ.Γ.IsNormal F₂') : Tube S :=
  letI : T2Space S := τ.t2Space
  have hcl : IsClosed (cylinderBetween F₁' F₂') := isClosed_cylinderBetween hlam
  { Γ := τ.Γ.interSet (cylinderBetween F₁' F₂')
    F₁ := F₁'
    F₂ := F₂'
    isCylinder := τ.isCylinder
    laminar := hlam
    isNormal_F₁ := interSet_isNormal_of_isClosed τ.Γ hcl (subset_cylinderBetween_left hlam) hN₁
    isNormal_F₂ := interSet_isNormal_of_isClosed τ.Γ hcl (subset_cylinderBetween_right hlam) hN₂
    U_subset := (interSet_U_subset_of_isClosed τ.Γ hcl).trans inter_subset_right }

/-- A $\Gamma$-normal hoop $F \subseteq \Sigma(F_1, F_2)$ is *cut-trivial* in a tube
$\tau = (\Gamma, F_1, F_2)$ if either $U(\Gamma) \subseteq \Sigma(F, F_2)$ and
$F \cap V(\Gamma) = F_1 \cap V(\Gamma)$, or $U(\Gamma) \subseteq \Sigma(F_1, F)$ and
$F \cap V(\Gamma) = F_2 \cap V(\Gamma)$.
These side conditions are extra requirements relative to the exceptional equalities in
the width definition of Graph Minors VIII, Section 15, page 280. -/
def IsCutTrivial (τ : Tube S) (F : Set S) : Prop :=
  (τ.Γ.U ⊆ cylinderBetween F τ.F₂ ∧ F ∩ τ.Γ.V = τ.F₁ ∩ τ.Γ.V) ∨
    (τ.Γ.U ⊆ cylinderBetween τ.F₁ F ∧ F ∩ τ.Γ.V = τ.F₂ ∩ τ.Γ.V)

theorem isCutTrivial_F₁ (τ : Tube S) : τ.IsCutTrivial τ.F₁ :=
  Or.inl ⟨τ.U_subset, rfl⟩

theorem isCutTrivial_F₂ (τ : Tube S) : τ.IsCutTrivial τ.F₂ :=
  Or.inr ⟨τ.U_subset, rfl⟩

theorem isCutTrivial_symm {F : Set S} : τ.symm.IsCutTrivial F ↔ τ.IsCutTrivial F := by
  simp only [IsCutTrivial, symm, cylinderBetween_comm]
  exact Or.comm

/-- A side-qualified width of a tube $(\Gamma, F_1, F_2)$ (taking values in $\mathbb{N}_\infty$).
Graph Minors VIII, Section 15 (page 280):
"The width of a tube $(\Gamma, F_1, F_2)$ is the largest value of $r$ such that for every
$\Gamma$-normal hoop $F \subseteq \Sigma(F_1, F_2)$, either $F \cap V(\Gamma) = F_1 \cap V(\Gamma)$,
or $F \cap V(\Gamma) = F_2 \cap V(\Gamma)$, or $|F \cap V(\Gamma)| \ge r$. If there is no such
number $r$, we say its width is infinite."
The definition below also imposes the side conditions in `IsCutTrivial` on each exceptional
equality. Those side conditions are absent from the printed definition. -/
noncomputable def width (τ : Tube S) : ℕ∞ :=
  sSup {r : ℕ∞ | ∀ F : Set S, IsHoop F → τ.Γ.IsNormal F → F ⊆ cylinderBetween τ.F₁ τ.F₂ →
    τ.IsCutTrivial F ∨ r ≤ ((F ∩ τ.Γ.V).ncard : ℕ∞)}

theorem le_width_iff {r : ℕ∞} :
    r ≤ τ.width ↔
      ∀ F : Set S, IsHoop F → τ.Γ.IsNormal F → F ⊆ cylinderBetween τ.F₁ τ.F₂ →
        τ.IsCutTrivial F ∨ r ≤ ((F ∩ τ.Γ.V).ncard : ℕ∞) := by
  constructor
  · intro hr F hF hNF hsub
    by_cases hct : τ.IsCutTrivial F
    · exact Or.inl hct
    · right
      refine hr.trans (sSup_le fun x hx => ?_)
      exact (hx F hF hNF hsub).resolve_left hct
  · exact fun h => le_sSup h

theorem width_symm : τ.symm.width = τ.width := by
  apply le_antisymm
  · rw [le_width_iff]
    intro F hF hNF hsub
    rw [← isCutTrivial_symm]
    exact (le_width_iff τ.symm).mp le_rfl F hF hNF (cylinderBetween_comm τ.F₁ τ.F₂ ▸ hsub)
  · rw [le_width_iff]
    intro F hF hNF hsub
    rw [isCutTrivial_symm]
    exact (le_width_iff τ).mp le_rfl F hF hNF (cylinderBetween_comm τ.F₂ τ.F₁ ▸ hsub)

/-- Every tube `τ = (Γ, F₁, F₂)` admits at least one `Γ`-normal `[0, 1]`-arc
`I ⊆ Σ(F₁, F₂)` with one end in `F₁` and the other in `F₂`. -/
theorem exists_normal_line (τ : Tube S) :
    ∃ (I : Set S) (u v : S),
      IsLineWithEnds I u v ∧ u ∈ τ.F₁ ∧ v ∈ τ.F₂ ∧ τ.Γ.IsNormal I ∧
        I ⊆ cylinderBetween τ.F₁ τ.F₂ := by
  have : T2Space S := τ.t2Space
  have : CompactSpace S := τ.isCylinder.1.1
  have : Nonempty S := τ.isCylinder.nonempty
  by_cases hne : (τ.F₁ ∩ τ.F₂).Nonempty
  · obtain ⟨w, hw₁, hw₂⟩ := hne
    obtain ⟨I, u, hIF, huF, hline, -⟩ :=
      τ.isHoop_F₁.exists_subArc_avoiding hw₁ τ.Γ.finite_V
    refine ⟨I, u, w, hline, huF, hw₂, fun x ⟨hxI, hxU⟩ => τ.isNormal_F₁ ⟨hIF hxI, hxU⟩,
      hIF.trans (subset_cylinderBetween_left τ.laminar)⟩
  · have hdisF : Disjoint τ.F₁ τ.F₂ :=
      disjoint_iff_inter_eq_empty.mpr (not_nonempty_iff_eq_empty.mp hne)
    obtain ⟨cap⟩ := CylinderSphereCap.exists_of_isCylinder τ.isCylinder
    have : T2Space cap.Z := cap.t2Space_Z
    wlog hle : cap.disc₁ τ.isCylinder.1 τ.isHoop_F₁ ⊆ cap.disc₁ τ.isCylinder.1 τ.isHoop_F₂
      generalizing τ
    · have hge := ((cap.areLaminarHoops_iff τ.isCylinder τ.isHoop_F₁ τ.isHoop_F₂).mp
        τ.laminar).resolve_left hle
      obtain ⟨I, u, v, hl, hu, hv, hN, hsub⟩ :=
        this τ.symm (by simpa [symm, inter_comm] using hne) hdisF.symm hge
      exact ⟨I, v, u, hl.symm, hv, hu, hN, cylinderBetween_comm τ.F₂ τ.F₁ ▸ hsub⟩
    set E₁ := cap.disc₁ τ.isCylinder.1 τ.isHoop_F₁
    set E₂ := cap.disc₂ τ.isCylinder.1 τ.isHoop_F₁
    set G₁ := cap.disc₁ τ.isCylinder.1 τ.isHoop_F₂
    set G₂ := cap.disc₂ τ.isCylinder.1 τ.isHoop_F₂
    obtain ⟨hE₁, hE₂, hbE₁, hbE₂, _, _, hD₁E, _⟩ :=
      cap.disc₁_disc₂_spec τ.isCylinder.1 τ.isHoop_F₁
    obtain ⟨hG₁, hG₂, hbG₁, hbG₂, _, _, _, hD₂G⟩ :=
      cap.disc₁_disc₂_spec τ.isCylinder.1 τ.isHoop_F₂
    have hdisEG : Disjoint E₁ G₂ := by
      rw [disjoint_iff_inter_eq_empty,
        cap.disc₁_inter_disc₂_eq_image_inter τ.isCylinder.1 τ.isHoop_F₁ τ.isHoop_F₂ hle,
        disjoint_iff_inter_eq_empty.mp hdisF, image_empty]
    obtain ⟨ΓZ, hm⟩ := GM07.exists_image_matched cap.isClosedEmbedding τ.Γ
    have hUZ : ΓZ.U = cap.j '' τ.Γ.U := by simpa using hm.image_U.symm
    have hVZ : ΓZ.V = cap.j '' τ.Γ.V := by simpa using hm.image_V.symm
    have hUsubZ : ΓZ.U ⊆ G₁ ∩ E₂ := by
      rw [hUZ]
      rintro _ ⟨x, hxU, rfl⟩
      have hx := τ.U_subset hxU
      rwa [cap.cylinderBetween_eq_of_disc₁_subset τ.isCylinder τ.isHoop_F₁ τ.isHoop_F₂ hle] at hx
    obtain ⟨p, hp⟩ := cap.isClosedDisc_D₁.nonempty_discInt
    obtain ⟨a, ha⟩ := cap.isClosedDisc_D₂.nonempty_discInt
    have hpr : p ∉ range cap.j := fun hr => disjoint_left.mp cap.disjoint_range_discInt_D₁ hr hp
    have har : a ∉ range cap.j := fun hr => disjoint_left.mp cap.disjoint_range_discInt_D₂ hr ha
    have hpU : p ∈ univ \ ΓZ.U := ⟨mem_univ _, fun h => hpr (hUZ ▸ h |> image_subset_range _ _)⟩
    have haU : a ∈ univ \ ΓZ.U := ⟨mem_univ _, fun h => har (hUZ ▸ h |> image_subset_range _ _)⟩
    let r₀ := connectedComponentIn (univ \ ΓZ.U) p
    let r₂ := connectedComponentIn (univ \ ΓZ.U) a
    have hr₀ : r₀ ∈ ΓZ.R := ⟨p, hpU, rfl⟩
    have hr₂ : r₂ ∈ ΓZ.R := ⟨a, haU, rfl⟩
    have hlayer : ∃ t ≤ ΓZ.V.ncard, r₂ ∈ GM07.regLayer ΓZ r₀ t := by
      by_contra hno
      push Not at hno
      have hfar : ∀ t < ΓZ.V.ncard + 1, r₂ ∉ GM07.regLayer ΓZ r₀ t :=
        fun t ht => hno t (Nat.lt_succ_iff.mp ht)
      obtain ⟨C, _, hC, hdisC⟩ := GM07.exists_region_nest cap.isClosedSurface cap.isSphere
        hr₀ hr₂ (mem_connectedComponentIn hpU) (mem_connectedComponentIn haU) hfar
      have hneV : ∀ i : Fin (ΓZ.V.ncard + 1), ((C i).V ∩ ΓZ.V).Nonempty := by
        intro i
        obtain ⟨u₀, W, _, _, hCV, _⟩ := (hC i).1
        have hu₀ : u₀ ∈ (C i).V := hCV ▸ W.start_mem_support
        exact ⟨u₀, hu₀, (hC i).2.1.1 hu₀⟩
      choose f hf using hneV
      have hfinj : Injective f := by
        intro i j hij
        by_contra hne_ij
        have hlt_or : i < j ∨ j < i := lt_or_gt_of_ne hne_ij
        rcases hlt_or with hlt | hlt
        · exact disjoint_left.mp (hdisC i j hlt).1 (hf i).1 (hij ▸ (hf j).1)
        · exact disjoint_left.mp (hdisC j i hlt).1 (hf j).1 (hij.symm ▸ (hf i).1)
      have hcard : ΓZ.V.ncard + 1 ≤ ΓZ.V.ncard := by
        have hsubf : range f ⊆ ΓZ.V := by rintro _ ⟨i, rfl⟩; exact (hf i).2
        have h1 : (range f).ncard ≤ ΓZ.V.ncard := ncard_le_ncard hsubf ΓZ.finite_V
        rw [ncard_range_of_injective hfinj, Nat.card_fin] at h1
        exact h1
      omega
    obtain ⟨t, _, ht⟩ := hlayer
    obtain ⟨LZ, uZ, vZ, hlZ, huZ, hvZ, hNZ, hdis1, hdis2, -⟩ :=
      GM07.exists_cross_line cap.isClosedSurface hE₁ hG₂ hdisEG hr₀
        (mem_connectedComponentIn hpU) (hD₁E hp.1)
        (mem_connectedComponentIn haU) (hD₂G ha.1) ht
    obtain ⟨u, hu₁, rfl⟩ := hbE₁ ▸ huZ
    obtain ⟨v, hv₂, rfl⟩ := hbG₂ ▸ hvZ
    have hLZ_range : LZ ⊆ range cap.j := by
      refine cap.subset_range_of_disjoint_discInts ?_ ?_
      · exact hdis1.mono_right (discInt_mono cap.isManifoldPoint_Z cap.isClosedDisc_D₁ hD₁E)
      · exact hdis2.mono_right (discInt_mono cap.isManifoldPoint_Z cap.isClosedDisc_D₂ hD₂G)
    have hlineS : IsLineWithEnds (cap.j ⁻¹' LZ) u v :=
      GM07.pull_line cap.isClosedEmbedding.isEmbedding hlZ hLZ_range
    refine ⟨cap.j ⁻¹' LZ, u, v, hlineS, hu₁, hv₂, ?_, ?_⟩
    · intro x ⟨hxL, hxU⟩
      have hjV : cap.j x ∈ ΓZ.V := hNZ ⟨hxL, hUZ ▸ mem_image_of_mem _ hxU⟩
      rw [hVZ] at hjV
      obtain ⟨y, hy, he⟩ := hjV
      exact cap.inj he ▸ hy
    · rw [cap.cylinderBetween_eq_of_disc₁_subset τ.isCylinder τ.isHoop_F₁ τ.isHoop_F₂ hle]
      intro x hxL
      refine ⟨?_, ?_⟩
      · rcases ((cap.disc₁_disc₂_spec τ.isCylinder.1 τ.isHoop_F₂).2.2.2.2.1 ▸
            mem_univ (cap.j x) : cap.j x ∈ G₁ ∪ G₂) with h1 | h2
        · exact h1
        · by_cases hb : cap.j x ∈ discBd G₂
          · exact Surface.discBd_subset _ (hbG₁ ▸ hbG₂ ▸ hb)
          · exact absurd ⟨h2, hb⟩ (disjoint_left.mp hdis2 hxL)
      · rcases ((cap.disc₁_disc₂_spec τ.isCylinder.1 τ.isHoop_F₁).2.2.2.2.1 ▸
            mem_univ (cap.j x) : cap.j x ∈ E₁ ∪ E₂) with h1 | h2
        · by_cases hb : cap.j x ∈ discBd E₁
          · exact Surface.discBd_subset _ (hbE₂ ▸ hbE₁ ▸ hb)
          · exact absurd ⟨h1, hb⟩ (disjoint_left.mp hdis1 hxL)
        · exact h2

/-- The *length* of a tube $(\Gamma, F_1, F_2)$.
Graph Minors VIII, Section 15 (page 280):
"The length of a tube $(\Gamma, F_1, F_2)$ is the largest value of $s$ such that
$|I \cap V(\Gamma)| \ge s$ for every $\Gamma$-normal $[0, 1]$-arc $I$ with one end in $F_1$ and the
other in $F_2$." -/
noncomputable def length (τ : Tube S) : ℕ :=
  sSup {s : ℕ | ∀ (I : Set S) (u v : S),
    IsLineWithEnds I u v → u ∈ τ.F₁ → v ∈ τ.F₂ → τ.Γ.IsNormal I → s ≤ (I ∩ τ.Γ.V).ncard}

private theorem bddAbove_length_set (τ : Tube S) :
    BddAbove {s : ℕ | ∀ (I : Set S) (u v : S),
      IsLineWithEnds I u v → u ∈ τ.F₁ → v ∈ τ.F₂ → τ.Γ.IsNormal I → s ≤ (I ∩ τ.Γ.V).ncard} := by
  obtain ⟨I, u, v, hl, hu, hv, hN, -⟩ := τ.exists_normal_line
  refine ⟨τ.Γ.V.ncard, fun s hs => ?_⟩
  exact (hs I u v hl hu hv hN).trans (ncard_le_ncard inter_subset_right τ.Γ.finite_V)

theorem le_length_iff {s : ℕ} :
    s ≤ τ.length ↔
      ∀ (I : Set S) (u v : S),
        IsLineWithEnds I u v → u ∈ τ.F₁ → v ∈ τ.F₂ → τ.Γ.IsNormal I → s ≤ (I ∩ τ.Γ.V).ncard := by
  have h0 : (0 : ℕ) ∈ {s : ℕ | ∀ (I : Set S) (u v : S),
      IsLineWithEnds I u v → u ∈ τ.F₁ → v ∈ τ.F₂ → τ.Γ.IsNormal I → s ≤ (I ∩ τ.Γ.V).ncard} :=
    fun _ _ _ _ _ _ _ => Nat.zero_le _
  constructor
  · intro hs I u v hl hu hv hN
    exact hs.trans (csSup_le ⟨0, h0⟩ fun r hr => hr I u v hl hu hv hN)
  · exact fun h => le_csSup (bddAbove_length_set τ) h

theorem length_symm : τ.symm.length = τ.length := by
  apply le_antisymm
  · rw [le_length_iff]
    intro I u v hl hu hv hN
    exact (le_length_iff τ.symm).mp le_rfl I v u hl.symm hv hu hN
  · rw [le_length_iff]
    intro I u v hl hu hv hN
    exact (le_length_iff τ).mp le_rfl I v u hl.symm hv hu hN

/-- If `2 ≤ τ.length`, then `τ.F₁` and `τ.F₂` are disjoint. -/
theorem disjoint_of_two_le_length (h : 2 ≤ τ.length) : Disjoint τ.F₁ τ.F₂ := by
  have : T2Space S := τ.t2Space
  by_contra hndis
  obtain ⟨w, hw₁, hw₂⟩ := not_disjoint_iff.mp hndis
  obtain ⟨I, u, hIF, huF, hline, hIB⟩ := τ.isHoop_F₁.exists_subArc_avoiding hw₁ τ.Γ.finite_V
  have hN : τ.Γ.IsNormal I := fun x ⟨hxI, hxU⟩ => τ.isNormal_F₁ ⟨hIF hxI, hxU⟩
  have h2 : 2 ≤ (I ∩ τ.Γ.V).ncard := (le_length_iff τ).mp h I u w hline huF hw₂ hN
  have h1 : (I ∩ τ.Γ.V).ncard ≤ 1 :=
    (ncard_le_ncard hIB (finite_singleton w)).trans (by simp)
  omega

/-- Testing `s ≤ τ.length` against all `Γ`-normal `[0, 1]`-arcs in `S` from `F₁` to `F₂` is
equivalent to testing only those contained in `Σ(F₁, F₂)`. -/
theorem le_length_iff_sub_cylinderBetween {s : ℕ} :
    s ≤ τ.length ↔
      ∀ (I : Set S) (u v : S),
        IsLineWithEnds I u v → u ∈ τ.F₁ → v ∈ τ.F₂ → τ.Γ.IsNormal I →
          I ⊆ cylinderBetween τ.F₁ τ.F₂ → s ≤ (I ∩ τ.Γ.V).ncard := by
  rw [le_length_iff]
  constructor
  · intro h I u v hl hu hv hN _
    exact h I u v hl hu hv hN
  · intro hsub I u v hl hu hv hN
    have : T2Space S := τ.t2Space
    by_cases hhit : (I ∩ (τ.F₁ ∩ τ.F₂)).Nonempty
    · obtain ⟨w, hwI, hw₁, hw₂⟩ := hhit
      obtain ⟨I', u', hI'F, hu'F, hline', hI'V⟩ :=
        τ.isHoop_F₁.exists_subArc_avoiding hw₁ τ.Γ.finite_V
      have hN' : τ.Γ.IsNormal I' := fun x ⟨hxI', hxU⟩ => τ.isNormal_F₁ ⟨hI'F hxI', hxU⟩
      have hsub' : I' ⊆ cylinderBetween τ.F₁ τ.F₂ :=
        hI'F.trans (subset_cylinderBetween_left τ.laminar)
      have hsI' : s ≤ (I' ∩ τ.Γ.V).ncard := hsub I' u' w hline' hu'F hw₂ hN' hsub'
      have hI'_le_I : I' ∩ τ.Γ.V ⊆ I ∩ τ.Γ.V := by
        intro x hx
        have hxw : x = w := mem_singleton_iff.mp (hI'V hx)
        exact ⟨hxw ▸ hwI, hx.2⟩
      exact hsI'.trans (ncard_le_ncard hI'_le_I (τ.Γ.finite_V.subset inter_subset_right))
    · obtain ⟨cap⟩ := CylinderSphereCap.exists_of_isCylinder τ.isCylinder
      have : T2Space cap.Z := cap.t2Space_Z
      wlog hle : cap.disc₁ τ.isCylinder.1 τ.isHoop_F₁ ⊆ cap.disc₁ τ.isCylinder.1 τ.isHoop_F₂
        generalizing τ u v
      · have hge := ((cap.areLaminarHoops_iff τ.isCylinder τ.isHoop_F₁ τ.isHoop_F₂).mp
          τ.laminar).resolve_left hle
        refine this τ.symm ?_ v u hl.symm hv hu hN (by simpa [symm, inter_comm] using hhit) hge
        intro I' a b hl' ha hb hN' hsub'
        exact hsub I' b a hl'.symm hb ha hN' (cylinderBetween_comm τ.F₂ τ.F₁ ▸ hsub')
      set E₁ := cap.disc₁ τ.isCylinder.1 τ.isHoop_F₁
      set E₂ := cap.disc₂ τ.isCylinder.1 τ.isHoop_F₁
      set G₁ := cap.disc₁ τ.isCylinder.1 τ.isHoop_F₂
      set G₂ := cap.disc₂ τ.isCylinder.1 τ.isHoop_F₂
      obtain ⟨hE₁, hE₂, hbE₁, _, hcupE, hcapE, _, _⟩ :=
        cap.disc₁_disc₂_spec τ.isCylinder.1 τ.isHoop_F₁
      obtain ⟨hG₁, hG₂, _, hbG₂, hcupG, hcapG, _, _⟩ :=
        cap.disc₁_disc₂_spec τ.isCylinder.1 τ.isHoop_F₂
      obtain ⟨f₀, hf0, hf1⟩ := hl
      let f : unitInterval → S := fun t => (f₀ t).1
      have hf_cont : Continuous f := continuous_subtype_val.comp f₀.continuous
      have hf_inj : Injective f := Subtype.val_injective.comp f₀.injective
      have hfz_cont : Continuous (cap.j ∘ f) := cap.isClosedEmbedding.continuous.comp hf_cont
      have hno_EG : ∀ t : unitInterval, ¬ (cap.j (f t) ∈ E₁ ∧ cap.j (f t) ∈ G₂) := by
        rintro t ⟨he1, hg2⟩
        have hz : cap.j (f t) ∈ cap.j '' (τ.F₁ ∩ τ.F₂) := by
          rw [← cap.disc₁_inter_disc₂_eq_image_inter τ.isCylinder.1 τ.isHoop_F₁ τ.isHoop_F₂ hle]
          exact ⟨he1, hg2⟩
        obtain ⟨x, hxF, hxeq⟩ := hz
        exact hhit ⟨f t, (f₀ t).2, cap.inj hxeq ▸ hxF⟩
      have hcG₂ : IsCompact ((cap.j ∘ f) ⁻¹' G₂) :=
        (hG₂.isCompact.isClosed.preimage hfz_cont).isCompact
      have h1_mem : (1 : unitInterval) ∈ (cap.j ∘ f) ⁻¹' G₂ := by
        change cap.j (f₀ 1).1 ∈ G₂
        rw [hf1]
        exact Surface.discBd_subset _ (hbG₂ ▸ mem_image_of_mem _ hv)
      obtain ⟨t₂, ht₂G, hlow₂⟩ := hcG₂.exists_isLeast ⟨1, h1_mem⟩
      have hcE₁ : IsCompact (Iic t₂ ∩ (cap.j ∘ f) ⁻¹' E₁) :=
        (isClosed_Iic.inter (hE₁.isCompact.isClosed.preimage hfz_cont)).isCompact
      have h0_mem : (0 : unitInterval) ∈ Iic t₂ ∩ (cap.j ∘ f) ⁻¹' E₁ := by
        refine ⟨unitInterval.nonneg t₂, ?_⟩
        change cap.j (f₀ 0).1 ∈ E₁
        rw [hf0]
        exact Surface.discBd_subset _ (hbE₁ ▸ mem_image_of_mem _ hu)
      obtain ⟨t₁, ⟨ht₁_le, ht₁E⟩, hhigh₁⟩ := hcE₁.exists_isGreatest ⟨0, h0_mem⟩
      have ht₁_lt_t₂ : t₁ < t₂ :=
        lt_of_le_of_ne ht₁_le fun heq => hno_EG t₁ ⟨ht₁E, heq ▸ ht₂G⟩
      have hmid_E₂ : ∀ t : unitInterval, t₁ < t → t < t₂ → cap.j (f t) ∈ E₂ := by
        intro t ht1 ht2
        rcases (hcupE ▸ mem_univ (cap.j (f t)) : cap.j (f t) ∈ E₁ ∪ E₂) with h1 | h2
        · exact absurd (hhigh₁ ⟨ht2.le, h1⟩) (not_le.mpr ht1)
        · exact h2
      have hmid_G₁ : ∀ t : unitInterval, t₁ < t → t < t₂ → cap.j (f t) ∈ G₁ := by
        intro t _ ht2
        rcases (hcupG ▸ mem_univ (cap.j (f t)) : cap.j (f t) ∈ G₁ ∪ G₂) with h1 | h2
        · exact h1
        · exact absurd (hlow₂ h2) (not_le.mpr ht2)
      have ht₁_E₂ : cap.j (f t₁) ∈ E₂ := by
        have ht₁_cl : t₁ ∈ closure (Ioo t₁ t₂) := by
          have hcl_val : (t₁ : ℝ) ∈ closure (Ioo (t₁ : ℝ) (t₂ : ℝ)) := by
            rw [closure_Ioo (Subtype.coe_ne_coe.mpr ht₁_lt_t₂.ne)]
            exact left_mem_Icc.mpr ht₁_lt_t₂.le
          rw [mem_closure_iff]
          intro U hU ht₁U
          obtain ⟨V, hV, rfl⟩ := isOpen_induced_iff.mp hU
          obtain ⟨r, hrV, hr1, hr2⟩ := mem_closure_iff.mp hcl_val V hV ht₁U
          have hrI : r ∈ Icc (0 : ℝ) 1 := ⟨le_trans t₁.2.1 hr1.le, le_trans hr2.le t₂.2.2⟩
          exact ⟨⟨r, hrI⟩, hrV, hr1, hr2⟩
        exact closure_minimal
          (by rintro _ ⟨t, ⟨h1, h2⟩, rfl⟩; exact hmid_E₂ t h1 h2)
          hE₂.isCompact.isClosed
          (image_closure_subset_closure_image hfz_cont ⟨t₁, ht₁_cl, rfl⟩)
      have ht₂_G₁ : cap.j (f t₂) ∈ G₁ := by
        have ht₂_cl : t₂ ∈ closure (Ioo t₁ t₂) := by
          have hcl_val : (t₂ : ℝ) ∈ closure (Ioo (t₁ : ℝ) (t₂ : ℝ)) := by
            rw [closure_Ioo (Subtype.coe_ne_coe.mpr ht₁_lt_t₂.ne)]
            exact right_mem_Icc.mpr ht₁_lt_t₂.le
          rw [mem_closure_iff]
          intro U hU ht₂U
          obtain ⟨V, hV, rfl⟩ := isOpen_induced_iff.mp hU
          obtain ⟨r, hrV, hr1, hr2⟩ := mem_closure_iff.mp hcl_val V hV ht₂U
          have hrI : r ∈ Icc (0 : ℝ) 1 := ⟨le_trans t₁.2.1 hr1.le, le_trans hr2.le t₂.2.2⟩
          exact ⟨⟨r, hrI⟩, hrV, hr1, hr2⟩
        exact closure_minimal
          (by rintro _ ⟨t, ⟨h1, h2⟩, rfl⟩; exact hmid_G₁ t h1 h2)
          hG₁.isCompact.isClosed
          (image_closure_subset_closure_image hfz_cont ⟨t₂, ht₂_cl, rfl⟩)
      have hu' : f t₁ ∈ τ.F₁ := by
        have : cap.j (f t₁) ∈ cap.j '' τ.F₁ := hcapE ▸ ⟨ht₁E, ht₁_E₂⟩
        obtain ⟨x, hx, he⟩ := this
        exact cap.inj he ▸ hx
      have hv' : f t₂ ∈ τ.F₂ := by
        have : cap.j (f t₂) ∈ cap.j '' τ.F₂ := hcapG ▸ ⟨ht₂_G₁, ht₂G⟩
        obtain ⟨x, hx, he⟩ := this
        exact cap.inj he ▸ hx
      let I' := f '' Icc t₁ t₂
      have hI'_sub_I : I' ⊆ I := by
        rintro _ ⟨t, _, rfl⟩
        exact (f₀ t).2
      have hI'_cyl : I' ⊆ cylinderBetween τ.F₁ τ.F₂ := by
        rw [cap.cylinderBetween_eq_of_disc₁_subset τ.isCylinder τ.isHoop_F₁ τ.isHoop_F₂ hle]
        rintro _ ⟨t, ⟨ht1, ht2⟩, rfl⟩
        rcases eq_or_lt_of_le ht1 with rfl | hlt1
        · exact ⟨hle ht₁E, ht₁_E₂⟩
        · rcases eq_or_lt_of_le ht2 with rfl | hlt2
          · exact ⟨ht₂_G₁, ((cap.disc₂_subset_iff_disc₁_subset τ.isCylinder.1
              τ.isHoop_F₁ τ.isHoop_F₂).mpr hle) ht₂G⟩
          · exact ⟨hmid_G₁ t hlt1 hlt2, hmid_E₂ t hlt1 hlt2⟩
      have hline' : IsLineWithEnds I' (f t₁) (f t₂) := subArc_of_lt hf_cont hf_inj ht₁_lt_t₂
      have hN' : τ.Γ.IsNormal I' := fun x ⟨hxI', hxU⟩ => hN ⟨hI'_sub_I hxI', hxU⟩
      exact (hsub I' (f t₁) (f t₂) hline' hu' hv' hN' hI'_cyl).trans
        (ncard_le_ncard (inter_subset_inter_left _ hI'_sub_I)
          (τ.Γ.finite_V.subset inter_subset_right))

theorem length_lt_iff {s : ℕ} :
    τ.length < s ↔
      ∃ (I : Set S) (u v : S),
        IsLineWithEnds I u v ∧ u ∈ τ.F₁ ∧ v ∈ τ.F₂ ∧ τ.Γ.IsNormal I ∧
          I ⊆ cylinderBetween τ.F₁ τ.F₂ ∧ (I ∩ τ.Γ.V).ncard < s := by
  rw [← not_le, le_length_iff_sub_cylinderBetween]
  push Not
  rfl

/-- Transporting a tube across a homeomorphism `e : S ≃ₜ S'`. -/
def mapHomeomorph {S' : Type w'} [TopologicalSpace S'] (e : S ≃ₜ S') (τ : Tube S) : Tube S' where
  Γ := GM07.mapDrawingHomeo e τ.Γ
  F₁ := e '' τ.F₁
  F₂ := e '' τ.F₂
  isCylinder := τ.isCylinder.congr e
  laminar := (AreLaminarHoops.image_homeomorph e).mpr τ.laminar
  isNormal_F₁ := by
    rintro _ ⟨⟨x, hxF, rfl⟩, ⟨y, hyU, hye⟩⟩
    exact ⟨x, τ.isNormal_F₁ ⟨hxF, e.injective hye ▸ hyU⟩, rfl⟩
  isNormal_F₂ := by
    rintro _ ⟨⟨x, hxF, rfl⟩, ⟨y, hyU, hye⟩⟩
    exact ⟨x, τ.isNormal_F₂ ⟨hxF, e.injective hye ▸ hyU⟩, rfl⟩
  U_subset := by
    rw [← image_cylinderBetween_homeomorph]
    exact image_mono τ.U_subset

theorem isCutTrivial_mapHomeomorph {S' : Type w'} [TopologicalSpace S'] (e : S ≃ₜ S')
    {F : Set S} : (τ.mapHomeomorph e).IsCutTrivial (e '' F) ↔ τ.IsCutTrivial F := by
  simp only [IsCutTrivial, mapHomeomorph, GM07.mapDrawingHomeo, ← image_cylinderBetween_homeomorph,
    ← image_inter e.injective, image_subset_image_iff e.injective, e.injective.image_injective.eq_iff]

private theorem width_le_mapHomeomorph {A : Type*} {B : Type*} [TopologicalSpace A]
    [TopologicalSpace B] (f : A ≃ₜ B) (σ : Tube A) : σ.width ≤ (σ.mapHomeomorph f).width := by
  rw [le_width_iff]
  intro F' hF' hN' hsub'
  have hpre : f '' (f.symm '' F') = F' := f.image_symm_image F'
  have hF : IsHoop (f.symm '' F') := by
    rw [← IsHoop.image_homeomorph f, hpre]
    exact hF'
  have hN : σ.Γ.IsNormal (f.symm '' F') := by
    rintro x ⟨hxF, hxU⟩
    have : f x ∈ F' ∩ (σ.mapHomeomorph f).Γ.U := ⟨hpre ▸ ⟨x, hxF, rfl⟩, ⟨x, hxU, rfl⟩⟩
    obtain ⟨y, hyV, he⟩ := hN' this
    exact f.injective he.symm ▸ hyV
  have hsub : f.symm '' F' ⊆ cylinderBetween σ.F₁ σ.F₂ := by
    rw [← image_subset_image_iff f.injective, hpre, image_cylinderBetween_homeomorph]
    exact hsub'
  have hcard : ((F' ∩ (σ.mapHomeomorph f).Γ.V).ncard : ℕ∞) =
      ((f.symm '' F' ∩ σ.Γ.V).ncard : ℕ∞) := by
    congr 1
    have : F' ∩ f '' σ.Γ.V = f '' (f.symm '' F' ∩ σ.Γ.V) := by
      rw [image_inter f.injective, hpre]
    change (F' ∩ f '' σ.Γ.V).ncard = _
    rw [this, ncard_image_of_injective _ f.injective]
  rcases (le_width_iff σ).mp le_rfl (f.symm '' F') hF hN hsub with hct | hle
  · left
    rw [← hpre, isCutTrivial_mapHomeomorph]
    exact hct
  · exact Or.inr (hcard ▸ hle)

theorem width_mapHomeomorph {S' : Type w'} [TopologicalSpace S'] (e : S ≃ₜ S') :
    (τ.mapHomeomorph e).width = τ.width := by
  apply le_antisymm _ (width_le_mapHomeomorph e τ)
  have hsymm := width_le_mapHomeomorph e.symm (τ.mapHomeomorph e)
  have heq : ((τ.mapHomeomorph e).mapHomeomorph e.symm).width = τ.width := by
    have hΓ : GM07.mapDrawingHomeo e.symm (GM07.mapDrawingHomeo e τ.Γ) = τ.Γ :=
      GM12.mapDrawingHomeo_symm e τ.Γ
    have h1 : e.symm '' (e '' τ.F₁) = τ.F₁ := e.symm_image_image τ.F₁
    have h2 : e.symm '' (e '' τ.F₂) = τ.F₂ := e.symm_image_image τ.F₂
    have hT : (τ.mapHomeomorph e).mapHomeomorph e.symm = τ := by
      cases τ
      simp only [mapHomeomorph, Tube.mk.injEq]
      exact ⟨hΓ, h1, h2⟩
    rw [hT]
  exact hsymm.trans_eq heq

private theorem length_le_mapHomeomorph {A : Type*} {B : Type*} [TopologicalSpace A]
    [TopologicalSpace B] (f : A ≃ₜ B) (σ : Tube A) : σ.length ≤ (σ.mapHomeomorph f).length := by
  have : T2Space A := σ.isCylinder.1.2.1
  have : T2Space B := (σ.isCylinder.congr f).1.2.1
  rw [le_length_iff]
  intro I' u' v' hl' hu' hv' hN'
  have hpre : f '' (f.symm '' I') = I' := f.image_symm_image I'
  have hl : IsLineWithEnds (f.symm '' I') (f.symm u') (f.symm v') :=
    GM07.image_line f.symm.isEmbedding hl'
  obtain ⟨u, hu, rfl⟩ := hu'
  obtain ⟨v, hv, rfl⟩ := hv'
  rw [f.symm_apply_apply, f.symm_apply_apply] at hl
  have hN : σ.Γ.IsNormal (f.symm '' I') := by
    rintro x ⟨hxI, hxU⟩
    have : f x ∈ I' ∩ (σ.mapHomeomorph f).Γ.U := ⟨hpre ▸ ⟨x, hxI, rfl⟩, ⟨x, hxU, rfl⟩⟩
    obtain ⟨y, hyV, he⟩ := hN' this
    exact f.injective he.symm ▸ hyV
  have hcard : (I' ∩ (σ.mapHomeomorph f).Γ.V).ncard = (f.symm '' I' ∩ σ.Γ.V).ncard := by
    have : I' ∩ f '' σ.Γ.V = f '' (f.symm '' I' ∩ σ.Γ.V) := by
      rw [image_inter f.injective, hpre]
    change (I' ∩ f '' σ.Γ.V).ncard = _
    rw [this, ncard_image_of_injective _ f.injective]
  exact hcard ▸ (le_length_iff σ).mp le_rfl (f.symm '' I') u v hl hu hv hN

theorem length_mapHomeomorph {S' : Type w'} [TopologicalSpace S'] (e : S ≃ₜ S') :
    (τ.mapHomeomorph e).length = τ.length := by
  apply le_antisymm _ (length_le_mapHomeomorph e τ)
  have hsymm := length_le_mapHomeomorph e.symm (τ.mapHomeomorph e)
  have hT : (τ.mapHomeomorph e).mapHomeomorph e.symm = τ := by
    have hΓ := GM12.mapDrawingHomeo_symm e τ.Γ
    have h1 := e.symm_image_image τ.F₁
    have h2 := e.symm_image_image τ.F₂
    cases τ
    simp only [mapHomeomorph, Tube.mk.injEq]
    exact ⟨hΓ, h1, h2⟩
  exact hsymm.trans_eq (congrArg Tube.length hT)

end Basic

/-! ## 3. Framings of Grafts -/

/-- Explicit framing witness between a tube `τ = (Γ, F₁, F₂)` and a graft `X = (G, T)`.
Graph Minors VIII, Section 15 (page 280):
"If $(\Gamma, F_1, F_2)$ is a tube, and $(G, T)$ is a graft, we say that $(\Gamma, F_1, F_2)$ is a
*framing* of $(G, T)$ if there is a bijection $\alpha$ from $V(G)$ to $V(\Gamma)$ and a bijection
$\beta$ from $E(G)$ to the set of edges of $\Gamma$, such that
(i) for $v \in V(G)$ and $e \in E(G)$, $v$ is incident with $e$ if and only if
$\alpha(v) \in \beta(e)$
(ii) for $v \in V(G)$, $\alpha(v) \in F_1 \cup F_2$ if and only if $v \in T$."
(Note: in (i), $\alpha(v) \in \overline{\beta(e)}$, since in a drawing $V(\Gamma)$ and edges
$e \in E(\Gamma)$ are disjoint and incidence is $v \in \bar{e}$; see `isFraming_iff_exists_bijections`.) -/
structure Framing {S : Type w} [TopologicalSpace S] {α : Type u} {β : Type v}
    (τ : Tube S) (X : Graft α β) where
  /-- Graph isomorphism between `X.G` and `τ.Γ.toGraph`. -/
  iso : Iso X.G τ.Γ.toGraph
  /-- Root vertices correspond to vertices drawn in `F₁ ∪ F₂`. -/
  mem_F_iff : ∀ v : V(X.G), (iso.vertexEquiv v).1 ∈ τ.F₁ ∪ τ.F₂ ↔ v.1 ∈ X.T

/-- A tube `τ` is a *framing* of a graft `X` if `τ.Framing X` is nonempty. -/
def IsFraming {S : Type w} [TopologicalSpace S] {α : Type u} {β : Type v}
    (τ : Tube S) (X : Graft α β) : Prop :=
  Nonempty (τ.Framing X)

/-- Equivalence between `τ.IsFraming X` and the paper's incidence-preserving bijections
`α : V(G) ≃ V(Γ)` and `β : E(G) ≃ E(Γ)`. -/
theorem isFraming_iff_exists_bijections {S : Type w} [TopologicalSpace S]
    {α : Type u} {β : Type v} (τ : Tube S) (X : Graft α β) :
    τ.IsFraming X ↔
      ∃ (α_eq : V(X.G) ≃ τ.Γ.V) (β_eq : E(X.G) ≃ τ.Γ.E),
        (∀ (v : V(X.G)) (e : E(X.G)), X.G.Inc e.1 v.1 ↔ (α_eq v).1 ∈ closure (β_eq e).1) ∧
        (∀ v : V(X.G), (α_eq v).1 ∈ τ.F₁ ∪ τ.F₂ ↔ v.1 ∈ X.T) := by
  constructor
  · rintro ⟨⟨iso, hF⟩⟩
    refine ⟨iso.vertexEquiv, iso.edgeEquiv, fun v e => ?_, hF⟩
    constructor
    · rintro ⟨w, hlink⟩
      have hw : w ∈ V(X.G) := hlink.right_mem
      have hlink' := (iso.isLink_iff e v ⟨w, hw⟩).mp hlink
      have hmem : (iso.vertexEquiv v).1 ∈ closure (iso.edgeEquiv e).1 ∩ τ.Γ.V :=
        hlink'.2.2.2 ▸ mem_insert _ _
      exact hmem.1
    · intro hcl
      have hmem : (iso.vertexEquiv v).1 ∈ closure (iso.edgeEquiv e).1 ∩ τ.Γ.V :=
        ⟨hcl, (iso.vertexEquiv v).2⟩
      obtain ⟨x', y', hl'⟩ := τ.Γ.toGraph.edge_mem_iff_exists_isLink _ |>.mp (iso.edgeEquiv e).2
      let x₀ := iso.vertexEquiv.symm ⟨x', hl'.2.1⟩
      let y₀ := iso.vertexEquiv.symm ⟨y', hl'.2.2.1⟩
      have hl₀ : X.G.IsLink e.1 x₀.1 y₀.1 := by
        rw [iso.isLink_iff e x₀ y₀]
        simpa [x₀, y₀] using hl'
      rw [hl'.2.2.2] at hmem
      rcases mem_insert_iff.mp hmem with hvx | hvy
      · have hv_eq : v = x₀ := iso.vertexEquiv.injective (Subtype.ext (hvx.trans (by simp [x₀])))
        exact hv_eq ▸ ⟨y₀.1, hl₀⟩
      · have hv_eq : v = y₀ := iso.vertexEquiv.injective
          (Subtype.ext ((mem_singleton_iff.mp hvy).trans (by simp [y₀])))
        exact hv_eq ▸ ⟨x₀.1, hl₀.symm⟩
  · rintro ⟨α_eq, β_eq, hinc, hF⟩
    refine ⟨⟨{ vertexEquiv := α_eq, edgeEquiv := β_eq, isLink_iff := fun e x y => ?_ }, hF⟩⟩
    have hcl_eq : closure (β_eq e).1 ∩ τ.Γ.V =
        (fun w : V(X.G) => (α_eq w).1) '' {w : V(X.G) | X.G.Inc e.1 w.1} := by
      ext z
      constructor
      · rintro ⟨hzcl, hzV⟩
        let w := α_eq.symm ⟨z, hzV⟩
        have hw_eq : (α_eq w).1 = z := congrArg Subtype.val (α_eq.apply_symm_apply ⟨z, hzV⟩)
        exact ⟨w, (hinc w e).mpr (hw_eq ▸ hzcl), hw_eq⟩
      · rintro ⟨w, hwinc, rfl⟩
        exact ⟨(hinc w e).mp hwinc, (α_eq w).2⟩
    constructor
    · intro hl
      refine ⟨(β_eq e).2, (α_eq x).2, (α_eq y).2, ?_⟩
      change closure (β_eq e).1 ∩ τ.Γ.V = {(α_eq x).1, (α_eq y).1}
      rw [hcl_eq]
      have hset : {w : V(X.G) | X.G.Inc e.1 w.1} = {x, y} := by
        ext w
        simp only [mem_ofPred_eq, mem_insert_iff, mem_singleton_iff]
        constructor
        · rintro ⟨z, hwz⟩
          exact (X.G.eq_or_eq_of_isLink_of_isLink hwz hl).imp Subtype.ext Subtype.ext
        · rintro (rfl | rfl)
          · exact ⟨y.1, hl⟩
          · exact ⟨x.1, hl.symm⟩
      rw [hset, image_pair]
    · rintro ⟨_, _, _, hpair⟩
      change closure (β_eq e).1 ∩ τ.Γ.V = {(α_eq x).1, (α_eq y).1} at hpair
      rw [hcl_eq] at hpair
      have hinj : Injective (fun w : V(X.G) => (α_eq w).1) :=
        Subtype.val_injective.comp α_eq.injective
      have hset : {w : V(X.G) | X.G.Inc e.1 w.1} = {x, y} := by
        apply hinj.image_injective
        rwa [image_pair]
      obtain ⟨u, v, huv⟩ := X.G.edge_mem_iff_exists_isLink e.1 |>.mp e.2
      let u₀ : V(X.G) := ⟨u, huv.left_mem⟩
      let v₀ : V(X.G) := ⟨v, huv.right_mem⟩
      have hu₀ : u₀ ∈ ({x, y} : Set V(X.G)) := hset ▸ (⟨v, huv⟩ : X.G.Inc e.1 u₀.1)
      have hv₀ : v₀ ∈ ({x, y} : Set V(X.G)) := hset ▸ (⟨u, huv.symm⟩ : X.G.Inc e.1 v₀.1)
      have hx₀ : x ∈ {w : V(X.G) | X.G.Inc e.1 w.1} := hset.symm ▸ mem_insert x {y}
      have hy₀ : y ∈ {w : V(X.G) | X.G.Inc e.1 w.1} := hset.symm ▸ mem_insert_of_mem x rfl
      obtain ⟨zx, hzx⟩ := hx₀
      obtain ⟨zy, hzy⟩ := hy₀
      have hx_uv : x.1 = u ∨ x.1 = v := X.G.eq_or_eq_of_isLink_of_isLink hzx huv
      have hy_uv : y.1 = u ∨ y.1 = v := X.G.eq_or_eq_of_isLink_of_isLink hzy huv
      by_cases hxy : x.1 = y.1
      · have hxy_sub : x = y := Subtype.ext hxy
        have hu_eq : u = x.1 := by
          rcases mem_insert_iff.mp hu₀ with h | h
          · exact congrArg Subtype.val h
          · exact congrArg Subtype.val (mem_singleton_iff.mp h |>.trans hxy_sub.symm)
        have hv_eq : v = x.1 := by
          rcases mem_insert_iff.mp hv₀ with h | h
          · exact congrArg Subtype.val h
          · exact congrArg Subtype.val (mem_singleton_iff.mp h |>.trans hxy_sub.symm)
        rw [hu_eq, hv_eq] at huv
        rwa [← hxy]
      · rcases hx_uv with hxu | hxv <;> rcases hy_uv with hyu | hyv
        · exact absurd (hxu.trans hyu.symm) hxy
        · rwa [hxu, hyv]
        · rw [hxv, hyu]
          exact huv.symm
        · exact absurd (hxv.trans hyv.symm) hxy

/-- Transporting a framing across a cylinder homeomorphism `e : S ≃ₜ S'`. -/
def Framing.mapHomeomorph {S : Type w} {S' : Type w'} [TopologicalSpace S] [TopologicalSpace S']
    {α : Type u} {β : Type v} {τ : Tube S} {X : Graft α β}
    (e : S ≃ₜ S') (fr : τ.Framing X) : (τ.mapHomeomorph e).Framing X where
  iso :=
    { vertexEquiv := fr.iso.vertexEquiv.trans
        { toFun := fun v => ⟨e v.1, ⟨v.1, v.2, rfl⟩⟩
          invFun := fun w => ⟨e.symm w.1, by
            obtain ⟨x, hx, hxe⟩ := w.2
            change e.symm w.1 ∈ τ.Γ.V
            rw [← hxe, e.symm_apply_apply]
            exact hx⟩
          left_inv := fun v => Subtype.ext (e.symm_apply_apply v.1)
          right_inv := fun w => Subtype.ext (e.apply_symm_apply w.1) }
      edgeEquiv := fr.iso.edgeEquiv.trans
        { toFun := fun ed => ⟨e '' ed.1, by
            change e '' ed.1 ∈ (GM07.mapDrawingHomeo e τ.Γ).E
            rw [GM12.mapDrawingHomeo_edges]
            exact ⟨ed.1, ed.2, rfl⟩⟩
          invFun := fun fd => ⟨e.symm '' fd.1, by
            have hfd : fd.1 ∈ (GM07.mapDrawingHomeo e τ.Γ).E := fd.2
            rw [GM12.mapDrawingHomeo_edges] at hfd
            obtain ⟨ed, hed, h_eq⟩ := hfd
            change e.symm '' fd.1 ∈ τ.Γ.E
            have hsymm : e.symm '' fd.1 = ed := by
              rw [← h_eq, image_image]
              simp [e.symm_apply_apply]
            rwa [hsymm]⟩
          left_inv := fun ed => Subtype.ext (show e.symm '' (e '' ed.1) = ed.1 by
            rw [image_image]; simp [e.symm_apply_apply])
          right_inv := fun fd => Subtype.ext (show e '' (e.symm '' fd.1) = fd.1 by
            rw [image_image]; simp [e.apply_symm_apply]) }
      isLink_iff := fun ed x y => by
        rw [fr.iso.isLink_iff ed x y]
        change τ.Γ.toGraph.IsLink _ _ _ ↔ (GM07.mapDrawingHomeo e τ.Γ).toGraph.IsLink _ _ _
        constructor
        · exact GM12.isLink_mapDrawingHomeo e τ.Γ
        · intro hl
          have hl' := GM12.isLink_mapDrawingHomeo e.symm (GM07.mapDrawingHomeo e τ.Γ) hl
          rw [GM12.mapDrawingHomeo_symm] at hl'
          simpa [image_image, e.symm_apply_apply] using hl' }
  mem_F_iff := fun v => by
    change e (fr.iso.vertexEquiv v).1 ∈ e '' τ.F₁ ∪ e '' τ.F₂ ↔ v.1 ∈ X.T
    rw [← image_union, e.injective.mem_set_image]
    exact fr.mem_F_iff v

theorem IsFraming.mapHomeomorph {S : Type w} {S' : Type w'} [TopologicalSpace S]
    [TopologicalSpace S'] {α : Type u} {β : Type v} {τ : Tube S} {X : Graft α β}
    (e : S ≃ₜ S') (h : τ.IsFraming X) : (τ.mapHomeomorph e).IsFraming X :=
  h.map (Framing.mapHomeomorph e)

theorem IsFraming.symm {S : Type w} [TopologicalSpace S] {α : Type u} {β : Type v}
    {τ : Tube S} {X : Graft α β} (h : τ.IsFraming X) : τ.symm.IsFraming X := by
  obtain ⟨⟨iso, hF⟩⟩ := h
  exact ⟨⟨iso, fun v => by rw [union_comm]; exact hF v⟩⟩

/-- Transporting a framing along a graft isomorphism `IsGraftIso Y X`. -/
theorem IsFraming.of_isGraftIso {S : Type w} [TopologicalSpace S]
    {α : Type u} {β : Type v} {α' : Type u'} {β' : Type v'}
    {τ : Tube S} {Y : Graft α' β'} {X : Graft α β}
    (hfr : τ.IsFraming Y) (hiso : IsGraftIso Y X) : τ.IsFraming X := by
  obtain ⟨⟨isoY, hFY⟩⟩ := hfr
  obtain ⟨φ, hφ⟩ := hiso
  refine ⟨⟨{
    vertexEquiv := φ.vertexEquiv.symm.trans isoY.vertexEquiv
    edgeEquiv := φ.edgeEquiv.symm.trans isoY.edgeEquiv
    isLink_iff := fun e x y => by
      have hl1 := φ.isLink_iff (φ.edgeEquiv.symm e) (φ.vertexEquiv.symm x) (φ.vertexEquiv.symm y)
      rw [φ.edgeEquiv.apply_symm_apply, φ.vertexEquiv.apply_symm_apply,
        φ.vertexEquiv.apply_symm_apply] at hl1
      exact hl1.symm.trans (isoY.isLink_iff _ _ _) }, fun v => ?_⟩⟩
  change (isoY.vertexEquiv (φ.vertexEquiv.symm v)).1 ∈ τ.F₁ ∪ τ.F₂ ↔ v.1 ∈ X.T
  rw [hFY (φ.vertexEquiv.symm v), hφ (φ.vertexEquiv.symm v), φ.vertexEquiv.apply_symm_apply]

end Tube

/-! ## 4. Tubular Grafts, Width, Length, $\mathcal{G}(r, k)$, and $\mathcal{A}(k, r, s)$ -/

/-- A graft $(G, T)$ is *tubular* if it has a framing on a cylinder $\Sigma$.
(Since every cylinder is homeomorphic to `SurfaceModel 0 0 2 : Type 0`, quantifying over cylinders
in `Type 0` is equivalent to quantifying over cylinders in any universe `Type w`; see
`IsTubularGraft.of_framing`.)
Graph Minors VIII, Section 15 (page 280):
"If $(G, T)$ has a framing, we say $(G, T)$ is *tubular*." -/
def IsTubularGraft {α : Type u} {β : Type v} (X : Graft α β) : Prop :=
  ∃ (S : Type) (_ : TopologicalSpace S) (τ : Tube S), τ.IsFraming X

/-- Any framing `τ : Tube S` in an arbitrary universe `Type w` witnesses `IsTubularGraft X` by
transporting along a homeomorphism `S ≃ₜ SurfaceModel 0 0 2`. -/
theorem IsTubularGraft.of_framing {S : Type w} [TopologicalSpace S] {α : Type u} {β : Type v}
    {τ : Tube S} {X : Graft α β} (h : τ.IsFraming X) : IsTubularGraft X := by
  obtain ⟨e⟩ := τ.isCylinder.2
  exact ⟨SurfaceModel 0 0 2, inferInstance, τ.mapHomeomorph e, h.mapHomeomorph e⟩

/-- The *width* of a tubular graft $(G, T)$: the maximum width of all its framings (in $\mathbb{N}_\infty$).
Graph Minors VIII, Section 15 (page 280):
"If $(G, T)$ is a tubular graft, its *width* is the maximum width of all its framings and its
*length* is the minimum length of all its framings." -/
noncomputable def tubularWidth {α : Type u} {β : Type v} (X : Graft α β) : ℕ∞ :=
  sSup {w₀ : ℕ∞ | ∃ (S : Type) (_ : TopologicalSpace S) (τ : Tube S),
    τ.IsFraming X ∧ τ.width = w₀}

/-- The *length* of a tubular graft $(G, T)$: the minimum length of all its framings.
Graph Minors VIII, Section 15 (page 280). -/
noncomputable def tubularLength {α : Type u} {β : Type v} (X : Graft α β) : ℕ :=
  sInf {l₀ : ℕ | ∃ (S : Type) (_ : TopologicalSpace S) (τ : Tube S),
    τ.IsFraming X ∧ τ.length = l₀}

theorem le_tubularWidth_of_framing {S : Type w} [TopologicalSpace S] {α : Type u} {β : Type v}
    {τ : Tube S} {X : Graft α β} (h : τ.IsFraming X) : τ.width ≤ tubularWidth X := by
  obtain ⟨e⟩ := τ.isCylinder.2
  refine le_sSup ⟨SurfaceModel 0 0 2, inferInstance, τ.mapHomeomorph e, h.mapHomeomorph e, ?_⟩
  exact τ.width_mapHomeomorph e

theorem tubularLength_le_of_framing {S : Type w} [TopologicalSpace S] {α : Type u} {β : Type v}
    {τ : Tube S} {X : Graft α β} (h : τ.IsFraming X) : tubularLength X ≤ τ.length := by
  obtain ⟨e⟩ := τ.isCylinder.2
  refine Nat.sInf_le ⟨SurfaceModel 0 0 2, inferInstance, τ.mapHomeomorph e, h.mapHomeomorph e, ?_⟩
  exact τ.length_mapHomeomorph e

/-- If `X` is tubular and `tubularWidth X = (r : ℕ∞)`, there is a framing `τ` of `X` attaining
`τ.width = (r : ℕ∞)`. -/
theorem IsTubularGraft.exists_framing_of_tubularWidth_eq {α : Type u} {β : Type v}
    {X : Graft α β} (htub : IsTubularGraft X) {r : ℕ} (hw : tubularWidth X = (r : ℕ∞)) :
    ∃ (S : Type) (_ : TopologicalSpace S) (τ : Tube S),
      τ.IsFraming X ∧ τ.width = (r : ℕ∞) := by
  let W : Set ℕ∞ := {w₀ : ℕ∞ | ∃ (S : Type) (_ : TopologicalSpace S) (τ : Tube S),
    τ.IsFraming X ∧ τ.width = w₀}
  have hW_sub : W ⊆ Iic (r : ℕ∞) := fun w₀ hw₀ => (le_sSup hw₀).trans_eq hw
  let M : Set ℕ := {m : ℕ | (m : ℕ∞) ∈ W}
  obtain ⟨S₀, ts₀, τ₀, hfr₀⟩ := htub
  have h0_le : τ₀.width ≤ (r : ℕ∞) := hW_sub ⟨S₀, ts₀, τ₀, hfr₀, rfl⟩
  have h0_ne_top : τ₀.width ≠ ⊤ := ne_top_of_le_ne_top (ENat.natCast_ne_top r) h0_le
  have hM_ne : M.Nonempty :=
    ⟨τ₀.width.toNat, S₀, ts₀, τ₀, hfr₀, (ENat.natCast_toNat h0_ne_top).symm⟩
  have hM_bdd : BddAbove M :=
    ⟨r, fun m hm => Nat.cast_le (α := ℕ∞).mp (hW_sub hm)⟩
  have hmem : sSup M ∈ M := Nat.sSup_mem hM_ne hM_bdd
  have heq_r : sSup M = r := by
    apply le_antisymm (csSup_le hM_ne fun m hm => Nat.cast_le (α := ℕ∞).mp (hW_sub hm))
    have hr_le : (r : ℕ∞) ≤ ((sSup M : ℕ) : ℕ∞) := by
      rw [← hw]
      refine sSup_le fun w₀ hw₀ => ?_
      have hw₀_top : w₀ ≠ ⊤ := ne_top_of_le_ne_top (ENat.natCast_ne_top r) (hW_sub hw₀)
      have hw₀_eq : ((w₀.toNat : ℕ) : ℕ∞) = w₀ := ENat.natCast_toNat hw₀_top
      rw [← hw₀_eq]
      exact Nat.cast_le.mpr (le_csSup hM_bdd (hw₀_eq.symm ▸ hw₀))
    exact Nat.cast_le.mp hr_le
  exact heq_r ▸ hmem

/-- Every tubular graft `X` has a framing attaining `τ.length = tubularLength X`. -/
theorem IsTubularGraft.exists_framing_tubularLength {α : Type u} {β : Type v}
    {X : Graft α β} (htub : IsTubularGraft X) :
    ∃ (S : Type) (_ : TopologicalSpace S) (τ : Tube S),
      τ.IsFraming X ∧ τ.length = tubularLength X := by
  obtain ⟨S₀, ts₀, τ₀, hfr₀⟩ := htub
  exact Nat.sInf_mem
    (s := {l₀ : ℕ | ∃ (S : Type) (_ : TopologicalSpace S) (τ : Tube S),
      τ.IsFraming X ∧ τ.length = l₀})
    ⟨τ₀.length, S₀, ts₀, τ₀, hfr₀, rfl⟩

/-- The class $\mathcal{G}(r, k)$ of all tubular grafts of width $\ge r$ and index $\le k$.
Graph Minors VIII, Section 15, proof of (15.2) (page 281):
"Let $\mathcal{G}(t, u)$ be the class of all tubular grafts of width $\ge t$ and index $\le u$." -/
def tubularClass {α : Type u} {β : Type v} (r k : ℕ) : Set (Graft α β) :=
  {X : Graft α β | IsTubularGraft X ∧ (r : ℕ∞) ≤ tubularWidth X ∧ X.index ≤ k}

/-- Condition on a tube `τ = (Γ, F₁, F₂)` that there do not exist `Γ`-normal laminar hoops
`F₁', F₂' ⊆ Σ(F₁, F₂)` such that `(Γ ∩ Σ(F₁', F₂'), F₁', F₂')` has width `≥ r` and length `≥ s`.
Graph Minors VIII, Section 15 (page 281). -/
def Tube.HasNoSubTubeOf {S : Type w} [TopologicalSpace S] (τ : Tube S) (r s : ℕ) : Prop :=
  ¬ ∃ (F₁' F₂' : Set S) (hlam : AreLaminarHoops F₁' F₂')
      (_ : F₁' ⊆ cylinderBetween τ.F₁ τ.F₂) (_ : F₂' ⊆ cylinderBetween τ.F₁ τ.F₂)
      (hN₁ : τ.Γ.IsNormal F₁') (hN₂ : τ.Γ.IsNormal F₂'),
      (r : ℕ∞) ≤ (τ.subTube hlam hN₁ hN₂).width ∧ s ≤ (τ.subTube hlam hN₁ hN₂).length

private theorem hasNoSubTubeOf_of_mapHomeomorph {A : Type*} {B : Type*}
    [TopologicalSpace A] [TopologicalSpace B] (f : A ≃ₜ B) (σ : Tube A) {r s : ℕ}
    (hno : (σ.mapHomeomorph f).HasNoSubTubeOf r s) : σ.HasNoSubTubeOf r s := by
  rintro ⟨F₁', F₂', hlam, h1, h2, hN1, hN2, hw, hl⟩
  have : T2Space A := σ.isCylinder.1.2.1
  have : T2Space B := (σ.isCylinder.congr f).1.2.1
  have hlam' : AreLaminarHoops (f '' F₁') (f '' F₂') :=
    (AreLaminarHoops.image_homeomorph f).mpr hlam
  have h1' : f '' F₁' ⊆ cylinderBetween (f '' σ.F₁) (f '' σ.F₂) := by
    rw [← image_cylinderBetween_homeomorph]
    exact image_mono h1
  have h2' : f '' F₂' ⊆ cylinderBetween (f '' σ.F₁) (f '' σ.F₂) := by
    rw [← image_cylinderBetween_homeomorph]
    exact image_mono h2
  have hN1' : (σ.mapHomeomorph f).Γ.IsNormal (f '' F₁') := by
    rintro _ ⟨⟨x, hx, rfl⟩, ⟨y, hy, hye⟩⟩
    exact ⟨x, hN1 ⟨hx, f.injective hye ▸ hy⟩, rfl⟩
  have hN2' : (σ.mapHomeomorph f).Γ.IsNormal (f '' F₂') := by
    rintro _ ⟨⟨x, hx, rfl⟩, ⟨y, hy, hye⟩⟩
    exact ⟨x, hN2 ⟨hx, f.injective hye ▸ hy⟩, rfl⟩
  have hsub_eq : (σ.mapHomeomorph f).subTube hlam' hN1' hN2' =
      (σ.subTube hlam hN1 hN2).mapHomeomorph f := by
    have hclA : IsClosed (cylinderBetween F₁' F₂') := isClosed_cylinderBetween hlam
    have hclB : IsClosed (cylinderBetween (f '' F₁') (f '' F₂')) := isClosed_cylinderBetween hlam'
    have hΓ : (GM07.mapDrawingHomeo f σ.Γ).interSet (cylinderBetween (f '' F₁') (f '' F₂')) =
        GM07.mapDrawingHomeo f (σ.Γ.interSet (cylinderBetween F₁' F₂')) := by
      rw [← image_cylinderBetween_homeomorph]
      apply Drawing.ext_of_V_E
      · rw [interSet_V_of_isClosed _ (image_cylinderBetween_homeomorph f F₁' F₂' ▸ hclB)]
        change f '' σ.Γ.V ∩ f '' cylinderBetween F₁' F₂' =
          f '' (σ.Γ.interSet (cylinderBetween F₁' F₂')).V
        rw [interSet_V_of_isClosed _ hclA, image_inter f.injective]
      · rw [interSet_E, GM12.mapDrawingHomeo_edges, GM12.mapDrawingHomeo_edges, interSet_E]
        ext ed
        constructor
        · rintro ⟨⟨e₀, he₀, rfl⟩, hsube⟩
          exact ⟨e₀, ⟨he₀, (image_subset_image_iff f.injective).mp hsube⟩, rfl⟩
        · rintro ⟨e₀, ⟨he₀, hsube⟩, rfl⟩
          exact ⟨⟨e₀, he₀, rfl⟩, image_mono hsube⟩
    dsimp only [Tube.subTube, Tube.mapHomeomorph]
    congr 1
  refine hno ⟨f '' F₁', f '' F₂', hlam', h1', h2', hN1', hN2', ?_, ?_⟩
  · rw [hsub_eq, Tube.width_mapHomeomorph]
    exact hw
  · rw [hsub_eq, Tube.length_mapHomeomorph]
    exact hl

theorem Tube.hasNoSubTubeOf_mapHomeomorph {S : Type w} {S' : Type w'}
    [TopologicalSpace S] [TopologicalSpace S'] (e : S ≃ₜ S') (τ : Tube S) (r s : ℕ) :
    (τ.mapHomeomorph e).HasNoSubTubeOf r s ↔ τ.HasNoSubTubeOf r s := by
  refine ⟨hasNoSubTubeOf_of_mapHomeomorph e τ, fun h => ?_⟩
  have hT : (τ.mapHomeomorph e).mapHomeomorph e.symm = τ := by
    have hΓ := GM12.mapDrawingHomeo_symm e τ.Γ
    have h1 := e.symm_image_image τ.F₁
    have h2 := e.symm_image_image τ.F₂
    cases τ
    simp only [Tube.mapHomeomorph, Tube.mk.injEq]
    exact ⟨hΓ, h1, h2⟩
  exact hasNoSubTubeOf_of_mapHomeomorph e.symm (τ.mapHomeomorph e) (hT.symm ▸ h)

/-- The class $\mathcal{A}(k, r, s)$ of tubular grafts of index $\le k$ having a framing with no
$(r, s)$-sub-tube.
Graph Minors VIII, Section 15 (page 281):
"Let $\mathcal{A}(k, r, s)$ denote the class of all tubular grafts with index $\le k$ which have a
framing $(\Gamma, F_1, F_2)$ in a cylinder $\Sigma$, such that there do not exist $\Gamma$-normal
laminar hoops $F_1', F_2' \subseteq \Sigma(F_1, F_2)$ such that $(\Gamma', F_1', F_2')$ has width
$\ge r$ and length $\ge s$, where $\Gamma'$ is the intersection of $\Gamma$ and
$\Sigma(F_1', F_2')$." -/
def classA {α : Type u} {β : Type v} (k r s : ℕ) : Set (Graft α β) :=
  {X : Graft α β | X.index ≤ k ∧
    ∃ (S : Type) (_ : TopologicalSpace S) (τ : Tube S), τ.IsFraming X ∧ τ.HasNoSubTubeOf r s}

theorem mem_classA_of_framing {S : Type w} [TopologicalSpace S] {α : Type u} {β : Type v}
    {k r s : ℕ} {X : Graft α β} {τ : Tube S} (hk : X.index ≤ k) (hfr : τ.IsFraming X)
    (hno : τ.HasNoSubTubeOf r s) : X ∈ classA k r s := by
  obtain ⟨e⟩ := τ.isCylinder.2
  exact ⟨hk, SurfaceModel 0 0 2, inferInstance, τ.mapHomeomorph e, hfr.mapHomeomorph e,
    (τ.hasNoSubTubeOf_mapHomeomorph e r s).mpr hno⟩

/-! ## 5. Isomorphism Invariance of `tubularClass` and `classA` -/

theorem IsGraftIso.symm_iso {α : Type u} {β : Type v} {α' : Type u'} {β' : Type v'}
    {Y : Graft α' β'} {X : Graft α β} (h : IsGraftIso Y X) : IsGraftIso X Y := by
  obtain ⟨φ, hφ⟩ := h
  refine ⟨{
    vertexEquiv := φ.vertexEquiv.symm
    edgeEquiv := φ.edgeEquiv.symm
    isLink_iff := fun e x y => by
      have hl1 := φ.isLink_iff (φ.edgeEquiv.symm e) (φ.vertexEquiv.symm x) (φ.vertexEquiv.symm y)
      rw [φ.edgeEquiv.apply_symm_apply, φ.vertexEquiv.apply_symm_apply,
        φ.vertexEquiv.apply_symm_apply] at hl1
      exact hl1.symm }, fun v => ?_⟩
  have hv := hφ (φ.vertexEquiv.symm v)
  rw [φ.vertexEquiv.apply_symm_apply] at hv
  exact hv.symm

theorem Graft.index_eq_of_isGraftIso {α : Type u} {β : Type v} {α' : Type u'} {β' : Type v'}
    {Y : Graft α' β'} {X : Graft α β} (h : IsGraftIso Y X) : Y.index = X.index := by
  obtain ⟨φ, hφ⟩ := h
  let eT : Y.T ≃ X.T :=
    { toFun := fun u => ⟨(φ.vertexEquiv ⟨u.1, Y.T_subset u.2⟩).1,
        (hφ ⟨u.1, Y.T_subset u.2⟩).mp u.2⟩
      invFun := fun v => ⟨(φ.vertexEquiv.symm ⟨v.1, X.T_subset v.2⟩).1,
        (hφ (φ.vertexEquiv.symm ⟨v.1, X.T_subset v.2⟩)).mpr (by
          rw [φ.vertexEquiv.apply_symm_apply]; exact v.2)⟩
      left_inv := fun u => Subtype.ext
        (show (φ.vertexEquiv.symm (φ.vertexEquiv ⟨u.1, Y.T_subset u.2⟩)).1 = u.1 from
          congrArg Subtype.val (φ.vertexEquiv.symm_apply_apply ⟨u.1, Y.T_subset u.2⟩))
      right_inv := fun v => Subtype.ext
        (show (φ.vertexEquiv (φ.vertexEquiv.symm ⟨v.1, X.T_subset v.2⟩)).1 = v.1 from
          congrArg Subtype.val (φ.vertexEquiv.apply_symm_apply ⟨v.1, X.T_subset v.2⟩)) }
  rw [Graft.index, Graft.index, ← Nat.card_coe_set_eq, ← Nat.card_coe_set_eq]
  exact Nat.card_congr eT

theorem IsTubularGraft.of_isGraftIso {α : Type u} {β : Type v} {α' : Type u'} {β' : Type v'}
    {Y : Graft α' β'} {X : Graft α β} (hY : IsTubularGraft Y) (hiso : IsGraftIso Y X) :
    IsTubularGraft X := by
  obtain ⟨S, ts, τ, hfr⟩ := hY
  exact ⟨S, ts, τ, hfr.of_isGraftIso hiso⟩

theorem tubularWidth_eq_of_isGraftIso {α : Type u} {β : Type v} {α' : Type u'} {β' : Type v'}
    {Y : Graft α' β'} {X : Graft α β} (hiso : IsGraftIso Y X) :
    tubularWidth Y = tubularWidth X := by
  have heq : {w₀ : ℕ∞ | ∃ (S : Type) (_ : TopologicalSpace S) (τ : Tube S),
      τ.IsFraming Y ∧ τ.width = w₀} =
    {w₀ : ℕ∞ | ∃ (S : Type) (_ : TopologicalSpace S) (τ : Tube S),
      τ.IsFraming X ∧ τ.width = w₀} := by
    ext w₀
    exact ⟨fun ⟨S, ts, τ, hfr, hw⟩ => ⟨S, ts, τ, hfr.of_isGraftIso hiso, hw⟩,
      fun ⟨S, ts, τ, hfr, hw⟩ => ⟨S, ts, τ, hfr.of_isGraftIso hiso.symm_iso, hw⟩⟩
  simp only [tubularWidth, heq]

theorem tubularLength_eq_of_isGraftIso {α : Type u} {β : Type v} {α' : Type u'} {β' : Type v'}
    {Y : Graft α' β'} {X : Graft α β} (hiso : IsGraftIso Y X) :
    tubularLength Y = tubularLength X := by
  have heq : {l₀ : ℕ | ∃ (S : Type) (_ : TopologicalSpace S) (τ : Tube S),
      τ.IsFraming Y ∧ τ.length = l₀} =
    {l₀ : ℕ | ∃ (S : Type) (_ : TopologicalSpace S) (τ : Tube S),
      τ.IsFraming X ∧ τ.length = l₀} := by
    ext l₀
    exact ⟨fun ⟨S, ts, τ, hfr, hl⟩ => ⟨S, ts, τ, hfr.of_isGraftIso hiso, hl⟩,
      fun ⟨S, ts, τ, hfr, hl⟩ => ⟨S, ts, τ, hfr.of_isGraftIso hiso.symm_iso, hl⟩⟩
  simp only [tubularLength, heq]

theorem isoGraftClass_tubularClass_eq {α : Type u} {β : Type v} (r k : ℕ) :
    isoGraftClass (tubularClass (α := α) (β := β) r k) = tubularClass r k := by
  apply Subset.antisymm
  · rintro X ⟨Y, ⟨htub, hw, hk⟩, hiso⟩
    exact ⟨htub.of_isGraftIso hiso, tubularWidth_eq_of_isGraftIso hiso ▸ hw,
      Graft.index_eq_of_isGraftIso hiso ▸ hk⟩
  · intro X hX
    exact ⟨X, hX, ⟨Iso.mk (Equiv.refl _) (Equiv.refl _) (fun _ _ _ => Iff.rfl), fun _ => Iff.rfl⟩⟩

theorem isoGraftClass_classA_eq {α : Type u} {β : Type v} (k r s : ℕ) :
    isoGraftClass (classA (α := α) (β := β) k r s) = classA k r s := by
  apply Subset.antisymm
  · rintro X ⟨Y, ⟨hk, S, ts, τ, hfr, hno⟩, hiso⟩
    exact ⟨Graft.index_eq_of_isGraftIso hiso ▸ hk, S, ts, τ, hfr.of_isGraftIso hiso, hno⟩
  · intro X hX
    exact ⟨X, hX, ⟨Iso.mk (Equiv.refl _) (Equiv.refl _) (fun _ _ _ => Iff.rfl), fun _ => Iff.rfl⟩⟩

end GraphMinor.GM08
