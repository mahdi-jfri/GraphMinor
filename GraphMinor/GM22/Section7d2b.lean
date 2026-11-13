module

public import GraphMinor.GM22.Section7d2a
public import GraphMinor.GM11.ArcDrawings
public import GraphMinor.GM11.RadialTwoCell
public import GraphMinor.GM11.Walks
public import GraphMinor.GM11.Section6
public import GraphMinor.GM11.PaintingRegions
public import GraphMinor.Surface.DiscArcs

/-!
# Graph Minors XXII – Section 7.4 (Part 2b): Disc Chords, 2-Cell Gluing, and Line Drawings

This file provides the topological and drawing lemmas used in the proof of **Claim (2)** of
**Theorem 7.4** from Robertson and Seymour, *Graph Minors. XXII. Irrelevant vertices in linkage
problems*, J. Combin. Theory Ser. B **102** (2012), 530–563 (page 553):

- `exists_chord_in_closedDisc`: any two distinct points in a closed disc `E` are joined by a line
  `I ⊆ E` whose interior `I \ {s₁, s₂}` lies in `E \ subBd E`.
- `disc_iArc_split_subdiscs`: cutting a closed disc `D` along a proper `I`-arc `L` yields two
  closed subdiscs `E₁, E₂ ⊆ D` with `E_i \ subBd E_i ⊆ (D \ subBd D) \ L` such that any subset
  `K ⊆ D` with `IsPreconnected (K \ L)` lies in `E₁` or `E₂`.
- `isPreconnected_U_of_isTwoCell` and `isTwoCell_of_subdrawing_of_isPreconnected_U`: adding a
  connected piece meeting a 2-cell drawing in a closed connected surface preserves `IsTwoCell`.
- `exists_drawing_of_simpleWalk_on_line`: drawing a simple walk of length `≥ 1` along a line `I`
  by updating `ιV` and `ιE` via permutations on the internal vertices and edges.
-/

@[expose] public section

namespace GraphMinor.GM22

open Classical Set Function Topology Metric unitInterval Graph Hypergraph
open GraphMinor GraphMinor.Surface GraphMinor.GM09 GraphMinor.GM11 GraphMinor.GM12 GraphMinor.GM14

universe w u v

variable {S : Type w} [TopologicalSpace S] [T2Space S]
variable {α : Type u} {β : Type v}

/-! ## 1. Chords in a Closed Disc and Proper `I`-Arc Splitting -/

/-- For distinct `z₁, z₂ ∈ closedBall (0 : ℂ) 1` and `t ∈ Ioo (0 : ℝ) 1`, the convex combination
`(1 - t) • z₁ + t • z₂` lies strictly inside `ball (0 : ℂ) 1`. -/
private theorem convex_combo_mem_ball {z₁ z₂ : ℂ} (hz₁ : z₁ ∈ closedBall (0 : ℂ) 1)
    (hz₂ : z₂ ∈ closedBall (0 : ℂ) 1) (hne : z₁ ≠ z₂) {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) :
    (1 - t : ℝ) • z₁ + (t : ℝ) • z₂ ∈ ball (0 : ℂ) 1 := by
  rw [mem_closedBall_zero_iff] at hz₁ hz₂
  rw [mem_ball_zero_iff]
  have hsq₁ : z₁.re ^ 2 + z₁.im ^ 2 ≤ 1 := by
    have := mul_self_le_mul_self (norm_nonneg z₁) hz₁
    rwa [← sq, ← Complex.normSq_eq_norm_sq, Complex.normSq_apply, ← sq, ← sq, mul_one] at this
  have hsq₂ : z₂.re ^ 2 + z₂.im ^ 2 ≤ 1 := by
    have := mul_self_le_mul_self (norm_nonneg z₂) hz₂
    rwa [← sq, ← Complex.normSq_eq_norm_sq, Complex.normSq_apply, ← sq, ← sq, mul_one] at this
  have hdiff_pos : 0 < (z₁.re - z₂.re) ^ 2 + (z₁.im - z₂.im) ^ 2 := by
    by_contra hle
    have hre : z₁.re - z₂.re = 0 := by nlinarith [sq_nonneg (z₁.re - z₂.re), sq_nonneg (z₁.im - z₂.im)]
    have him : z₁.im - z₂.im = 0 := by nlinarith [sq_nonneg (z₁.re - z₂.re), sq_nonneg (z₁.im - z₂.im)]
    exact hne (Complex.ext (sub_eq_zero.mp hre) (sub_eq_zero.mp him))
  let w : ℂ := (1 - t : ℝ) • z₁ + (t : ℝ) • z₂
  have hw_re : w.re = (1 - t) * z₁.re + t * z₂.re := by simp [w]
  have hw_im : w.im = (1 - t) * z₁.im + t * z₂.im := by simp [w]
  have hid : w.re ^ 2 + w.im ^ 2 =
      (1 - t) * (z₁.re ^ 2 + z₁.im ^ 2) + t * (z₂.re ^ 2 + z₂.im ^ 2) -
        t * (1 - t) * ((z₁.re - z₂.re) ^ 2 + (z₁.im - z₂.im) ^ 2) := by
    rw [hw_re, hw_im]
    ring
  have hlt1 : w.re ^ 2 + w.im ^ 2 < 1 := by
    have ht_prod : 0 < t * (1 - t) * ((z₁.re - z₂.re) ^ 2 + (z₁.im - z₂.im) ^ 2) :=
      mul_pos (mul_pos ht0 (by linarith)) hdiff_pos
    nlinarith
  refine not_le.mp fun hge => ?_
  have hge' := Complex.one_le_normSq_iff.mpr hge
  rw [Complex.normSq_apply, ← sq, ← sq] at hge'
  linarith

/-- In any closed disc `E ⊆ S` (`IsClosedDisc E`), any two distinct points `s₁, s₂ ∈ E` are joined
by a line `L_arc ⊆ E` with ends `s₁, s₂` such that `L_arc \ {s₁, s₂} ⊆ E \ discBd E`. -/
theorem exists_chord_in_closedDisc {E : Set S} (hE : IsClosedDisc E)
    {s₁ s₂ : S} (hs₁ : s₁ ∈ E) (hs₂ : s₂ ∈ E) (hne : s₁ ≠ s₂) :
    ∃ L_arc : Set S, IsLineWithEnds L_arc s₁ s₂ ∧ L_arc ⊆ E ∧ L_arc \ {s₁, s₂} ⊆ E \ discBd E := by
  obtain ⟨h, g, c⟩ := hE.exists_isChart
  let z₁ := h s₁
  let z₂ := h s₂
  have hz₁ : z₁ ∈ closedBall (0 : ℂ) 1 := c.hm hs₁
  have hz₂ : z₂ ∈ closedBall (0 : ℂ) 1 := c.hm hs₂
  have hz_ne : z₁ ≠ z₂ := fun heq => hne (c.gh.injOn hs₁ hs₂ heq)
  let seg : I → ℂ := fun t => (1 - (t : ℝ)) • z₁ + (t : ℝ) • z₂
  have hseg_cont : Continuous seg := by fun_prop
  have hseg_mem : ∀ t : I, seg t ∈ closedBall (0 : ℂ) 1 := fun t =>
    convex_closedBall (0 : ℂ) 1 hz₁ hz₂ (sub_nonneg.mpr t.2.2) t.2.1 (by ring)
  have hseg_inj : Function.Injective seg := by
    intro t₁ t₂ heq
    have hdiff : ((t₁ : ℝ) - (t₂ : ℝ)) • (z₂ - z₁) = 0 := by
      have h1 : ((t₁ : ℝ) - (t₂ : ℝ)) • (z₂ - z₁) = seg t₁ - seg t₂ := by
        apply Complex.ext <;> simp [seg] <;> ring
      rw [h1, sub_eq_zero.mpr heq]
    rcases smul_eq_zero.mp hdiff with ht | hz
    · exact Subtype.ext (sub_eq_zero.mp ht)
    · exact (hz_ne (sub_eq_zero.mp hz).symm).elim
  let γ : I → S := fun t => g (seg t)
  have hγ_cont : Continuous γ := c.gc.comp_continuous hseg_cont hseg_mem
  have hγ_inj : Function.Injective γ := fun t₁ t₂ heq =>
    hseg_inj (c.injOn (hseg_mem t₁) (hseg_mem t₂) heq)
  have hγ0 : γ 0 = s₁ := by
    change g ((1 - (0 : ℝ)) • z₁ + (0 : ℝ) • z₂) = s₁
    simp [z₁, c.gh hs₁]
  have hγ1 : γ 1 = s₂ := by
    change g ((1 - (1 : ℝ)) • z₁ + (1 : ℝ) • z₂) = s₂
    simp [z₂, c.gh hs₂]
  have hLine : IsLineWithEnds (range γ) s₁ s₂ := by
    have hL := GM11.isLine_range hγ_cont hγ_inj
    rwa [hγ0, hγ1] at hL
  refine ⟨range γ, hLine, ?_, ?_⟩
  · rintro _ ⟨t, rfl⟩
    exact c.gm (hseg_mem t)
  · rintro _ ⟨⟨t, rfl⟩, hnot_end⟩
    have ht0 : (0 : ℝ) < t.1 := by
      refine lt_of_le_of_ne t.2.1 fun h0 => hnot_end (Or.inl ?_)
      have ht_eq : t = 0 := Subtype.ext h0.symm
      rw [ht_eq, hγ0]
    have ht1 : (t : ℝ) < 1 := by
      refine lt_of_le_of_ne t.2.2 fun h1 => hnot_end (Or.inr ?_)
      have ht_eq : t = 1 := Subtype.ext h1
      rw [ht_eq, hγ1]
      rfl
    have hball : seg t ∈ ball (0 : ℂ) 1 := convex_combo_mem_ball hz₁ hz₂ hz_ne ht0 ht1
    refine ⟨c.gm (hseg_mem t), ?_⟩
    rw [← c.g_sphere]
    rintro ⟨w, hw_sph, hw_eq⟩
    have hw_seg : w = seg t := c.injOn (sphere_subset_closedBall hw_sph) (hseg_mem t) hw_eq
    rw [hw_seg] at hw_sph
    have h1 : ‖seg t‖ = 1 := mem_sphere_zero_iff_norm.mp hw_sph
    have h2 : ‖seg t‖ < 1 := mem_ball_zero_iff.mp hball
    linarith

omit [T2Space S] in
/-- Cutting a closed disc `D` along a proper `I`-arc `L` (`IsLineWithEnds L a b` with `L ⊆ D` and
`L ∩ discBd D = {a, b}`) yields two closed discs `E₁, E₂` such that:
1. `E₁ ∪ E₂ = D` and `E₁ ∩ E₂ = L`,
2. `E₁ \ discBd E₁ ⊆ (D \ discBd D) \ L` and `E₂ \ discBd E₂ ⊆ (D \ discBd D) \ L`,
3. `(E₁ ∩ discBd D) ∪ L = discBd E₁` and `(E₂ ∩ discBd D) ∪ L = discBd E₂`, and
4. any subset `K ⊆ D` with `IsPreconnected (K \ L)` satisfies `K ⊆ E₁ ∨ K ⊆ E₂`. -/
theorem disc_iArc_split_subdiscs {D L : Set S} {a b : S} (hD : IsClosedDisc D)
    (hL : IsLineWithEnds L a b) (hLD : L ⊆ D) (hab : a ≠ b) (hmeet : L ∩ discBd D = {a, b}) :
    ∃ E₁ E₂ : Set S,
      IsClosedDisc E₁ ∧ IsClosedDisc E₂ ∧
      E₁ ∪ E₂ = D ∧ E₁ ∩ E₂ = L ∧
      E₁ \ discBd E₁ ⊆ (D \ discBd D) \ L ∧
      E₂ \ discBd E₂ ⊆ (D \ discBd D) \ L ∧
      discBd E₁ ⊆ discBd D ∪ L ∧ discBd E₂ ⊆ discBd D ∪ L ∧
      (∀ K : Set S, K ⊆ D → IsPreconnected (K \ L) → K ⊆ E₁ ∨ K ⊆ E₂) := by
  obtain ⟨C₁, C₂, E₁, E₂, _, hcomp_bd, hE₁, hE₂, hU, hI, hb₁, hb₂, hcomp_DL⟩ :=
    disc_iArc D L a b hD hLD hab hL hmeet
  have hC₁_sub : C₁ ⊆ discBd D \ {a, b} := by
    have hmem : C₁ ∈ componentsIn (discBd D \ {a, b}) := by rw [hcomp_bd]; simp
    rcases hmem with ⟨x, hx, rfl⟩
    exact connectedComponentIn_subset _ _
  have hC₂_sub : C₂ ⊆ discBd D \ {a, b} := by
    have hmem : C₂ ∈ componentsIn (discBd D \ {a, b}) := by rw [hcomp_bd]; simp
    rcases hmem with ⟨x, hx, rfl⟩
    exact connectedComponentIn_subset _ _
  have hbd_cov : discBd D \ {a, b} ⊆ C₁ ∪ C₂ := by
    intro x hx
    have hmem : connectedComponentIn (discBd D \ {a, b}) x ∈ ({C₁, C₂} : Set (Set S)) :=
      hcomp_bd ▸ ⟨x, hx, rfl⟩
    have hx_cc : x ∈ connectedComponentIn (discBd D \ {a, b}) x := mem_connectedComponentIn hx
    rcases hmem with h1 | h2
    · exact Or.inl (h1 ▸ hx_cc)
    · exact Or.inr ((mem_singleton_iff.mp h2) ▸ hx_cc)
  have hab_L : ({a, b} : Set S) ⊆ L := by
    intro x hx
    exact (hmeet.symm ▸ hx).1
  have hE₁_int : E₁ \ discBd E₁ ⊆ (D \ discBd D) \ L := by
    rintro x ⟨hxE₁, hx_not_bd₁⟩
    have hx_not_L : x ∉ L := fun hxL => hx_not_bd₁ (hb₁ ▸ Or.inr hxL)
    refine ⟨⟨hU ▸ Or.inl hxE₁, ?_⟩, hx_not_L⟩
    intro hx_bdD
    have hx_not_ab : x ∉ ({a, b} : Set S) := fun hxab => hx_not_L (hab_L hxab)
    rcases hbd_cov ⟨hx_bdD, hx_not_ab⟩ with hxC₁ | hxC₂
    · exact hx_not_bd₁ (hb₁ ▸ Or.inl hxC₁)
    · have hxE₂ : x ∈ E₂ := Surface.discBd_subset E₂ (hb₂ ▸ Or.inl hxC₂)
      exact hx_not_L (hI ▸ ⟨hxE₁, hxE₂⟩)
  have hE₂_int : E₂ \ discBd E₂ ⊆ (D \ discBd D) \ L := by
    rintro x ⟨hxE₂, hx_not_bd₂⟩
    have hx_not_L : x ∉ L := fun hxL => hx_not_bd₂ (hb₂ ▸ Or.inr hxL)
    refine ⟨⟨hU ▸ Or.inr hxE₂, ?_⟩, hx_not_L⟩
    intro hx_bdD
    have hx_not_ab : x ∉ ({a, b} : Set S) := fun hxab => hx_not_L (hab_L hxab)
    rcases hbd_cov ⟨hx_bdD, hx_not_ab⟩ with hxC₁ | hxC₂
    · have hxE₁ : x ∈ E₁ := Surface.discBd_subset E₁ (hb₁ ▸ Or.inl hxC₁)
      exact hx_not_L (hI ▸ ⟨hxE₁, hxE₂⟩)
    · exact hx_not_bd₂ (hb₂ ▸ Or.inl hxC₂)
  refine ⟨E₁, E₂, hE₁, hE₂, hU, hI, hE₁_int, hE₂_int,
    hb₁ ▸ union_subset_union_left L (hC₁_sub.trans sdiff_subset),
    hb₂ ▸ union_subset_union_left L (hC₂_sub.trans sdiff_subset), ?_⟩
  intro K hKD hK_pre
  by_cases hKL_ne : (K \ L).Nonempty
  · obtain ⟨x₀, hx₀⟩ := hKL_ne
    have hx₀_DL : x₀ ∈ D \ L := ⟨hKD hx₀.1, hx₀.2⟩
    have hcc_sub : K \ L ⊆ connectedComponentIn (D \ L) x₀ :=
      hK_pre.subset_connectedComponentIn hx₀ (sdiff_subset_sdiff_left hKD)
    have hcc_mem : connectedComponentIn (D \ L) x₀ ∈ ({E₁ \ L, E₂ \ L} : Set (Set S)) :=
      hcomp_DL ▸ ⟨x₀, hx₀_DL, rfl⟩
    rcases hcc_mem with h1 | h2
    · left
      intro x hxK
      by_cases hxL : x ∈ L
      · exact (hI ▸ hxL).1
      · exact ((h1 ▸ hcc_sub) ⟨hxK, hxL⟩).1
    · right
      intro x hxK
      by_cases hxL : x ∈ L
      · exact (hI ▸ hxL).2
      · exact (((mem_singleton_iff.mp h2) ▸ hcc_sub) ⟨hxK, hxL⟩).1
  · left
    intro x hxK
    have hxL : x ∈ L := by_contra fun hxL => hKL_ne ⟨x, hxK, hxL⟩
    exact (hI ▸ hxL).1

omit [T2Space S] in
/-- Removing one endpoint from a line `IsLineWithEnds L a b` yields a preconnected set. -/
theorem IsLineWithEnds.isPreconnected_diff_left {L : Set S} {a b : S}
    (hL : IsLineWithEnds L a b) : IsPreconnected (L \ {a}) := by
  obtain ⟨f, hf0, _⟩ := hL
  have hEq : L \ {a} = (fun t : I => (f t).1) '' Ioi (0 : I) := by
    ext x
    constructor
    · rintro ⟨hxL, hxa⟩
      refine ⟨f.symm ⟨x, hxL⟩, ?_, by simp⟩
      refine unitInterval.pos_iff_ne_zero.mpr fun h0 => hxa ?_
      have := congrArg (fun t => (f t).1) h0
      simpa [hf0] using this
    · rintro ⟨t, ht, rfl⟩
      refine ⟨(f t).2, fun hxa => ?_⟩
      have ht0 : t = 0 := f.injective (Subtype.ext (hxa.trans hf0.symm))
      exact ne_of_gt ht (congrArg Subtype.val ht0)
  rw [hEq]
  exact isPreconnected_Ioi.image _ (continuous_subtype_val.comp f.continuous).continuousOn

omit [T2Space S] in
/-- Removing the second endpoint from a line `IsLineWithEnds L a b` yields a preconnected set. -/
theorem IsLineWithEnds.isPreconnected_diff_right {L : Set S} {a b : S}
    (hL : IsLineWithEnds L a b) : IsPreconnected (L \ {b}) :=
  IsLineWithEnds.isPreconnected_diff_left (GM11.IsLineWithEnds.symm hL)

/-! ## 2. 2-Cell Preservation under Connected Extensions -/

/-- The point set `Γ.U` of a 2-cell drawing `Γ` in a connected closed surface `S` is
preconnected. -/
theorem isPreconnected_U_of_isTwoCell [ConnectedSpace S] (hS : IsClosedSurface S)
    {Γ : Drawing S} (h2cell : Γ.IsTwoCell) : IsPreconnected Γ.U := by
  apply isPreconnected_closed_iff.mpr
  intro C₁ C₂ hc₁ hc₂ hcover hne₁ hne₂
  by_contra hn
  have hdis : Disjoint (Γ.U ∩ C₁) (Γ.U ∩ C₂) :=
    disjoint_left.mpr fun x hx hy => hn ⟨x, hx.1, hx.2, hy.2⟩
  have heq : (Γ.U ∩ C₁) ∪ (Γ.U ∩ C₂) = Γ.U := by
    refine Subset.antisymm (union_subset inter_subset_left inter_subset_left) fun x hx => ?_
    exact (hcover hx).elim (fun h => Or.inl ⟨hx, h⟩) (fun h => Or.inr ⟨hx, h⟩)
  have hempty := GM11.eq_empty_of_split hS h2cell.2 (Γ.isClosed_U.inter hc₁)
    (Γ.isClosed_U.inter hc₂) hdis heq hne₁
  exact hne₂.ne_empty hempty

/-- If `Γ` is a 2-cell drawing in a connected closed surface `S` with `Γ.V.Nonempty`,
`Γ.IsSubdrawing Γ'`, and `IsPreconnected Γ'.U`, then `Γ'` is also a 2-cell drawing. -/
theorem isTwoCell_of_subdrawing_of_isPreconnected_U [ConnectedSpace S] (hS : IsClosedSurface S)
    {Γ Γ' : Drawing S} (h2cell : Γ.IsTwoCell) (hV : Γ.V.Nonempty) (hsub : Γ.IsSubdrawing Γ')
    (hU'_pre : IsPreconnected Γ'.U) : Γ'.IsTwoCell := by
  have : LocallyConnectedSpace S := IsClosedSurface.locallyConnectedSpace hS
  have hman : ∀ x : S, IsManifoldPoint x := fun x => (hS.2.2 x).isManifoldPoint
  obtain ⟨v₀, hv₀⟩ := hV
  have hv₀U : v₀ ∈ Γ.U := Γ.V_subset_U hv₀
  have hv₀U' : v₀ ∈ Γ'.U := hsub.U_subset hv₀U
  refine ⟨inferInstance, fun q hq => ?_⟩
  obtain ⟨y₀, hy₀q⟩ := GM11.region_nonempty hq
  have hy₀_notU : y₀ ∉ Γ.U := fun h => GM11.region_subset hq hy₀q (hsub.U_subset h)
  obtain ⟨r, hr, hy₀r⟩ := GM11.exists_region_of_notMem hy₀_notU
  have hqr : q ⊆ r := by
    have hdis : Disjoint q Γ.U :=
      disjoint_left.mpr fun x hxq hxU => GM11.region_subset hq hxq (hsub.U_subset hxU)
    exact GM11.subset_region hr (GM11.region_isPreconnected hq) hdis hy₀q hy₀r
  have hrd : IsOpenDisc r := h2cell.2 r hr
  have hq_ne_univ : q ≠ univ := fun hun => GM11.region_subset hq (hun ▸ mem_univ v₀) hv₀U'
  refine GM11.isOpenDisc_of_bound hS (GM11.region_isOpen hq)
    ⟨⟨y₀, hy₀q⟩, GM11.region_isPreconnected hq⟩ hq_ne_univ fun F hFq hF => ?_
  obtain ⟨Δ, hΔr, hΔ, hb⟩ := GM11.exists_disc_in_openDisc hrd hF (hFq.trans hqr)
  have hFU' : Disjoint Γ'.U (discBd Δ) := by
    rw [hb]
    exact disjoint_right.mpr fun x hxF hxU' => GM11.region_subset hq (hFq hxF) hxU'
  have hv₀_notΔ : v₀ ∉ Δ := fun h => GM11.region_subset hr (hΔr h) hv₀U
  have hΔU' : Disjoint Δ Γ'.U :=
    (GM11.disjoint_disc_of_outside hman hΔ hU'_pre hFU' hv₀U' hv₀_notΔ).symm
  obtain ⟨z, hzF⟩ := GM14.IsOArc.nonempty hF
  have hzΔ : z ∈ Δ := Surface.discBd_subset Δ (hb.symm ▸ hzF)
  have hΔ_pre : IsPreconnected Δ := GM14.IsClosedDisc.isPreconnected hΔ
  exact ⟨Δ, GM11.subset_region hq hΔ_pre hΔU' hzΔ (hFq hzF), hΔ, hb⟩

/-! ## 3. Lifting Simple Walks between `toEmbeddedGraph` and `toGraph` -/

omit [T2Space S] in
/-- Any walk in `H.toEmbeddedGraph ιV ιE` from `ιV a` to `ιV b` lifts to a walk in `H.toGraph`
from `a` to `b` with the corresponding support and edges. -/
theorem exists_walk_toGraph_of_toEmbeddedGraph {H : Drawing S} {ιV : S ↪ α} {ιE : Set S ↪ β}
    {a b : S} (W : GraphWalk (H.toEmbeddedGraph ιV ιE) (ιV a) (ιV b)) :
    ∃ W₀ : GraphWalk H.toGraph a b,
      W.support = W₀.support.map ιV ∧ W.edges = W₀.edges.map ιE := by
  generalize hx : ιV a = x, hy : ιV b = y at W
  induction W generalizing a b with
  | nil h =>
    subst hx
    have hab : a = b := ιV.injective hy.symm
    subst hab
    rcases h with ⟨a', ha', ha'_eq⟩
    obtain rfl : a' = a := ιV.injective ha'_eq
    exact ⟨.nil ha', rfl, rfl⟩
  | @cons u v w e hlink rest ih =>
    subst hx
    obtain ⟨e₀, x₀, y₀, hlink₀, he₀, hx₀, hy₀⟩ := id hlink
    have hx₀_eq : x₀ = a := ιV.injective hx₀
    subst hx₀_eq
    obtain ⟨W_rest, hsupp, hedges⟩ := ih hy₀ hy
    refine ⟨.cons hlink₀ W_rest, ?_, ?_⟩
    · rw [GraphWalk.support_cons, GraphWalk.support_cons, List.map_cons, hsupp]
    · rw [GraphWalk.edges_cons, GraphWalk.edges_cons, List.map_cons, hedges, he₀]

/-! ## 4. Drawing a Simple Walk along a Line -/

/-- A single-edge simple walk `GraphWalk.cons hlink (.nil _)` drawn on a line `L_arc` with ends
`s₁, s₂` via `lineDrawing`. -/
private theorem lineDrawing_toEmbeddedGraph_eq_walkSubgraph
    {G : Graph α β} {ιV : S ↪ α} {ιE : Set S ↪ β}
    {s₁ s₂ : S} {L_arc : Set S} (hI : IsLineWithEnds L_arc s₁ s₂) (hs₁₂ : s₁ ≠ s₂)
    {e₀ : β} (hlink : G.IsLink e₀ (ιV s₁) (ιV s₂))
    (hιE : ιE (L_arc \ {s₁, s₂}) = e₀) :
    (GM11.lineDrawing hI hs₁₂).toEmbeddedGraph ιV ιE =
      walkSubgraph (GraphWalk.cons hlink (.nil hlink.right_mem)) := by
  let M := GM11.lineDrawing hI hs₁₂
  let W : GraphWalk G (ιV s₁) (ιV s₂) := .cons hlink (.nil hlink.right_mem)
  have hME : M.E = {L_arc \ {s₁, s₂}} := GM11.lineDrawing_E hI hs₁₂
  have hMV : M.V = {s₁, s₂} := rfl
  have hle₁ : M.toEmbeddedGraph ιV ιE ≤ G := by
    refine ⟨?_, ?_⟩
    · rintro x ⟨s, hs, rfl⟩
      rcases hs with rfl | rfl
      · exact hlink.left_mem
      · exact hlink.right_mem
    · rintro e x y ⟨e_S, a, b, hLM, rfl, rfl, rfl⟩
      have he_S : e_S = L_arc \ {s₁, s₂} := by
        have := hLM.1
        rwa [hME, mem_singleton_iff] at this
      subst he_S
      rw [hιE]
      have hab : ({a, b} : Set S) = {s₁, s₂} := by
        have hcl : closure (L_arc \ {s₁, s₂}) ∩ M.V = {s₁, s₂} := by
          rw [GM11.closure_sdiff_pair hI, hMV]
          exact inter_eq_right.mpr M.V_subset_U
        exact hLM.2.2.2.symm.trans hcl
      rcases Set.pair_eq_pair_iff.mp hab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact hlink
      · exact hlink.symm
  have hle₂ : walkSubgraph W ≤ G := walkSubgraph_le W
  refine (Compatible.of_le_le hle₁ hle₂).ext ?_ ?_
  · ext x
    rw [vertexSet_walkSubgraph]
    change x ∈ ιV '' {s₁, s₂} ↔ x ∈ W.support
    simp [W, GraphWalk.support_cons]
  · ext e
    rw [edgeSet_walkSubgraph]
    change e ∈ ιE '' M.E ↔ e ∈ W.edges
    rw [hME, image_singleton, hιE]
    simp [W, GraphWalk.edges_cons]

omit [T2Space S] in
/-- Given two glued drawings `M₁, M₂`, `(M₁.glue M₂ hmeet).toEmbeddedGraph ιV ιE` is the
`graphUnion` of their embedded graphs when `M₁.E` and `M₂.E` are disjoint. -/
theorem glue_toEmbeddedGraph_eq_graphUnion {M₁ M₂ : Drawing S}
    (hmeet : M₁.U ∩ M₂.U ⊆ M₁.V ∩ M₂.V) (hE_disj : Disjoint M₁.E M₂.E)
    (ιV : S ↪ α) (ιE : Set S ↪ β) :
    (M₁.glue M₂ hmeet).toEmbeddedGraph ιV ιE =
      graphUnion (M₁.toEmbeddedGraph ιV ιE) (M₂.toEmbeddedGraph ιV ιE) := by
  have hsub₁ : M₁.IsSubdrawing (M₁.glue M₂ hmeet) :=
    ⟨subset_union_left, by rw [Drawing.glue_E]; exact subset_union_left⟩
  have hsub₂ : M₂.IsSubdrawing (M₁.glue M₂ hmeet) :=
    ⟨subset_union_right, by rw [Drawing.glue_E]; exact subset_union_right⟩
  have hV_eq : V((M₁.glue M₂ hmeet).toEmbeddedGraph ιV ιE) =
      V(graphUnion (M₁.toEmbeddedGraph ιV ιE) (M₂.toEmbeddedGraph ιV ιE)) :=
    image_union _ _ _
  ext x y e
  · exact Set.ext_iff.mp hV_eq x
  · constructor
    · rintro ⟨e₀, x₀, y₀, hL, rfl, rfl, rfl⟩
      have he₀ : e₀ ∈ M₁.E ∪ M₂.E := by
        have := hL.1
        rwa [Drawing.glue_E] at this
      rcases he₀ with he₁ | he₂
      · exact Or.inl ⟨e₀, x₀, y₀, (hsub₁.isLink_iff he₁).mpr hL, rfl, rfl, rfl⟩
      · refine Or.inr ⟨?_, e₀, x₀, y₀, (hsub₂.isLink_iff he₂).mpr hL, rfl, rfl, rfl⟩
        rintro ⟨e₁, he₁, he_eq⟩
        obtain rfl : e₁ = e₀ := ιE.injective he_eq
        exact disjoint_left.mp hE_disj he₁ he₂
    · rintro (⟨e₀, x₀, y₀, hL₁, rfl, rfl, rfl⟩ | ⟨_, e₀, x₀, y₀, hL₂, rfl, rfl, rfl⟩)
      · exact ⟨e₀, x₀, y₀, (hsub₁.isLink_iff hL₁.1).mp hL₁, rfl, rfl, rfl⟩
      · exact ⟨e₀, x₀, y₀, (hsub₂.isLink_iff hL₂.1).mp hL₂, rfl, rfl, rfl⟩

private theorem cast_walk_eq {G : Graph α β} {u₁ u₂ v₁ v₂ : α} (hu : u₁ = u₂) (hv : v₁ = v₂)
    (W : GraphWalk G u₁ v₁) :
    ∃ W' : GraphWalk G u₂ v₂, W'.support = W.support ∧ W'.edges = W.edges := by
  subst hu hv
  exact ⟨W, rfl, rfl⟩

set_option maxHeartbeats 400000 in
/-- Given a simple walk `W : GraphWalk G (ιV s₁) (ιV s₂)` of length `≥ 1` and a line `L_arc` with
ends `s₁ ≠ s₂`, we can draw `walkSubgraph W` on `L_arc` via a drawing `M : Drawing S` and updated
embeddings `ιV' : S ↪ α` and `ιE' : Set S ↪ β` obtained by permuting only points in
`L_arc \ {s₁, s₂}` with internal vertices of `W`, and nonempty subsets of `L_arc \ {s₁, s₂}` with
edges of `W`. -/
theorem exists_drawing_of_simpleWalk_on_line (n : ℕ) :
    ∀ {G : Graph α β} {ιV : S ↪ α} {ιE : Set S ↪ β} {s₁ s₂ : S} {L_arc : Set S},
      IsLineWithEnds L_arc s₁ s₂ → s₁ ≠ s₂ →
      ∀ (W : GraphWalk G (ιV s₁) (ιV s₂)), W.IsSimple →
      W.length = n + 1 →
      ∃ (M : Drawing S) (ιV' : S ↪ α) (ιE' : Set S ↪ β),
        M.U = L_arc ∧ s₁ ∈ M.V ∧ s₂ ∈ M.V ∧ M.E.Nonempty ∧
        M.toEmbeddedGraph ιV' ιE' = walkSubgraph W ∧
        (∀ x : S, x ∉ L_arc \ {s₁, s₂} →
          ιV x ∉ {u ∈ W.support | u ≠ ιV s₁ ∧ u ≠ ιV s₂} → ιV' x = ιV x) ∧
        (∀ e : Set S, ¬ (e.Nonempty ∧ e ⊆ L_arc \ {s₁, s₂}) →
          ιE e ∉ {e' | e' ∈ W.edges} → ιE' e = ιE e) := by
  induction n with
  | zero =>
    intro G ιV ιE s₁ s₂ L_arc hI hs₁₂ W hW hlen
    generalize hx₁ : ιV s₁ = x₁, hx₂ : ιV s₂ = x₂ at W
    cases W with
    | nil _ => simp [GraphWalk.length] at hlen
    | @cons _ u_mid _ e₀ hlink rest =>
      cases rest with
      | cons _ _ => simp [GraphWalk.length] at hlen
      | nil _ =>
        subst hx₁ hx₂
        let M := GM11.lineDrawing hI hs₁₂
        let e_S := L_arc \ {s₁, s₂}
        let ιE' := ιE.trans (Equiv.swap (ιE e_S) e₀).toEmbedding
        have he_S_ne : e_S.Nonempty := (GM11.isPathConnected_sdiff_pair hI).nonempty
        have hME : M.E = {e_S} := GM11.lineDrawing_E hI hs₁₂
        have hιE'_eS : ιE' e_S = e₀ := by simp [ιE']
        refine ⟨M, ιV, ιE', rfl, Or.inl rfl, Or.inr rfl, hME ▸ singleton_nonempty e_S,
          lineDrawing_toEmbeddedGraph_eq_walkSubgraph hI hs₁₂ hlink hιE'_eS,
          fun _ _ _ => rfl, ?_⟩
        intro e he_not he_not_W
        have he_ne_eS : e ≠ e_S := fun h => he_not (h ▸ ⟨he_S_ne, Subset.rfl⟩)
        have h1 : ιE e ≠ ιE e_S := fun h => he_ne_eS (ιE.injective h)
        have h2 : ιE e ≠ e₀ := fun h => he_not_W (by simp [h, GraphWalk.edges_cons])
        exact Equiv.swap_apply_of_ne_of_ne h1 h2
  | succ n ih =>
    intro G ιV ιE s₁ s₂ L_arc hI hs₁₂ W hW hlen
    generalize hx₁ : ιV s₁ = x₁, hx₂ : ιV s₂ = x₂ at W
    cases W with
    | nil _ => simp [GraphWalk.length] at hlen
    | @cons _ u_mid _ e₀ hlink rest =>
      subst hx₁ hx₂
      have hlen_rest : rest.length = n + 1 := by
        simpa [GraphWalk.length_cons] using hlen
      obtain ⟨f, hf0, hf1⟩ := id hI
      let g : unitInterval → S := fun t => (f t).1
      have hgc : Continuous g := continuous_subtype_val.comp f.continuous
      have hgi : Function.Injective g := Subtype.val_injective.comp f.injective
      have hrange : range g = L_arc := by
        ext z
        exact ⟨by rintro ⟨t, rfl⟩; exact (f t).2, fun hz => ⟨f.symm ⟨z, hz⟩, by simp [g]⟩⟩
      let τ : unitInterval := ⟨1 / 2, by norm_num, by norm_num⟩
      have hτ0 : (0 : unitInterval) < τ := Subtype.mk_lt_mk.mpr (by norm_num)
      have hτ1 : τ < (1 : unitInterval) := Subtype.mk_lt_mk.mpr (by norm_num)
      let s_mid := g τ
      have hs_mid_in : s_mid ∈ L_arc \ {s₁, s₂} := by
        refine ⟨(f τ).2, ?_⟩
        rintro (h | h)
        · exact hτ0.ne' (hgi (h.trans hf0.symm))
        · exact hτ1.ne (hgi (h.trans hf1.symm))
      have hs₁_mid : s₁ ≠ s_mid := fun h => hs_mid_in.2 (Or.inl h.symm)
      have hs_mid₂ : s_mid ≠ s₂ := fun h => hs_mid_in.2 (Or.inr h)
      let I₁ := g '' Icc 0 τ
      let I₂ := g '' Icc τ 1
      have hI₁ : IsLineWithEnds I₁ s₁ s_mid := by
        have := GM11.isLine_piece hgc hgi hτ0
        rwa [show g 0 = s₁ from hf0] at this
      have hI₂ : IsLineWithEnds I₂ s_mid s₂ := by
        have := GM11.isLine_piece hgc hgi hτ1
        rwa [show g 1 = s₂ from hf1] at this
      have hI₁₂_union : I₁ ∪ I₂ = L_arc := by
        rw [← image_union, ← hrange, ← image_univ]
        congr 1
        ext t
        simp only [mem_union, mem_Icc, mem_univ, iff_true]
        rcases le_total t τ with h | h
        · exact Or.inl ⟨t.2.1, h⟩
        · exact Or.inr ⟨h, t.2.2⟩
      have hI₁₂_inter : I₁ ∩ I₂ = {s_mid} := by
        ext z
        constructor
        · rintro ⟨⟨t₁, ht₁, rfl⟩, ⟨t₂, ht₂, ht_eq⟩⟩
          have ht₁₂ : t₁ = t₂ := (hgi ht_eq).symm
          subst ht₁₂
          have ht₁τ : t₁ = τ := le_antisymm ht₁.2 ht₂.1
          subst ht₁τ
          rfl
        · rintro rfl
          exact ⟨⟨τ, ⟨hτ0.le, le_rfl⟩, rfl⟩, ⟨τ, ⟨le_rfl, hτ1.le⟩, rfl⟩⟩
      have hI₁_int_sub : I₁ \ {s₁, s_mid} ⊆ L_arc \ {s₁, s₂} := by
        rintro z ⟨⟨t, ht, rfl⟩, hnot⟩
        refine ⟨(f t).2, ?_⟩
        rintro (h | h)
        · exact hnot (Or.inl h)
        · have ht1 : t = 1 := hgi (h.trans hf1.symm)
          exact absurd ht.2 (by rw [ht1]; exact not_le.mpr hτ1)
      have hI₂_int_sub : I₂ \ {s_mid, s₂} ⊆ L_arc \ {s₁, s₂} := by
        rintro z ⟨⟨t, ht, rfl⟩, hnot⟩
        refine ⟨(f t).2, ?_⟩
        rintro (h | h)
        · have ht0 : t = 0 := hgi (h.trans hf0.symm)
          exact absurd ht.1 (by rw [ht0]; exact not_le.mpr hτ0)
        · exact hnot (Or.inr h)
      have hnd_cons := List.nodup_cons.mp hW
      have hrest_simple : rest.IsSimple := hnd_cons.2
      have hu_mid_ne_s₁ : u_mid ≠ ιV s₁ := fun h => hnd_cons.1 (h ▸ rest.start_mem_support)
      have hu_mid_ne_s₂ : u_mid ≠ ιV s₂ := by
        intro h
        subst h
        cases rest with
        | nil _ => simp [GraphWalk.length] at hlen_rest
        | cons _ r => exact (List.nodup_cons.mp hrest_simple).1 r.end_mem_support
      let ιV₁ := ιV.trans (Equiv.swap (ιV s_mid) u_mid).toEmbedding
      let e_S₁ := I₁ \ {s₁, s_mid}
      let ιE₁ := ιE.trans (Equiv.swap (ιE e_S₁) e₀).toEmbedding
      have hιV₁_mid : ιV₁ s_mid = u_mid := by simp [ιV₁]
      have hιV₁_s₁ : ιV₁ s₁ = ιV s₁ :=
        Equiv.swap_apply_of_ne_of_ne (fun h => hs₁_mid (ιV.injective h)) hu_mid_ne_s₁.symm
      have hιV₁_s₂ : ιV₁ s₂ = ιV s₂ :=
        Equiv.swap_apply_of_ne_of_ne (fun h => hs_mid₂.symm (ιV.injective h)) hu_mid_ne_s₂.symm
      have hιE₁_eS₁ : ιE₁ e_S₁ = e₀ := by simp [ιE₁]
      obtain ⟨rest', hrest'_supp, hrest'_edges⟩ :=
        cast_walk_eq hιV₁_mid.symm hιV₁_s₂.symm rest
      have hrest'_simple : rest'.IsSimple := by
        unfold GraphWalk.IsSimple; rw [hrest'_supp]; exact hrest_simple
      have hrest'_len : rest'.length = n + 1 := by
        unfold GraphWalk.length; rw [hrest'_edges]; exact hlen_rest
      obtain ⟨M₂, ιV', ιE', hM₂U, hs_mid_M₂, hs₂_M₂, _, hM₂_emb, hιV'_eq, hιE'_eq⟩ :=
        ih hI₂ hs_mid₂ rest' hrest'_simple hrest'_len
      let M₁ := GM11.lineDrawing hI₁ hs₁_mid
      have hmeet : M₁.U ∩ M₂.U ⊆ M₁.V ∩ M₂.V := by
        change I₁ ∩ M₂.U ⊆ {s₁, s_mid} ∩ M₂.V
        rw [hM₂U, hI₁₂_inter, singleton_subset_iff]
        exact ⟨Or.inr rfl, hs_mid_M₂⟩
      have he_S₁_ne : e_S₁.Nonempty := (GM11.isPathConnected_sdiff_pair hI₁).nonempty
      have hM₁E : M₁.E = {e_S₁} := GM11.lineDrawing_E hI₁ hs₁_mid
      have hE_disj : Disjoint M₁.E M₂.E := by
        rw [hM₁E, disjoint_singleton_left]
        intro he_S₁_M₂
        obtain ⟨z, hz⟩ := he_S₁_ne
        have hz_I₂ : z ∈ I₂ := hM₂U ▸ (he_S₁_M₂.2.1 hz).1
        have hz_inter : z ∈ I₁ ∩ I₂ := ⟨hz.1, hz_I₂⟩
        rw [hI₁₂_inter, mem_singleton_iff] at hz_inter
        exact hz.2 (Or.inr hz_inter)
      have hιV'_s₁ : ιV' s₁ = ιV s₁ := by
        have hs₁_not_I₂ : s₁ ∉ I₂ \ {s_mid, s₂} := fun h => by
          have : s₁ ∈ I₁ ∩ I₂ := ⟨⟨0, ⟨le_rfl, hτ0.le⟩, hf0⟩, h.1⟩
          rw [hI₁₂_inter, mem_singleton_iff] at this
          exact hs₁_mid this
        have hs₁_not_supp : ιV₁ s₁ ∉ {u ∈ rest'.support | u ≠ ιV₁ s_mid ∧ u ≠ ιV₁ s₂} := by
          rw [hιV₁_s₁, hrest'_supp]
          intro h
          exact hnd_cons.1 h.1
        exact (hιV'_eq s₁ hs₁_not_I₂ hs₁_not_supp).trans hιV₁_s₁
      have hιV'_mid : ιV' s_mid = u_mid := by
        have hmid_not_I₂ : s_mid ∉ I₂ \ {s_mid, s₂} := fun h => h.2 (Or.inl rfl)
        have hmid_not_supp : ιV₁ s_mid ∉ {u ∈ rest'.support | u ≠ ιV₁ s_mid ∧ u ≠ ιV₁ s₂} :=
          fun h => h.2.1 rfl
        exact (hιV'_eq s_mid hmid_not_I₂ hmid_not_supp).trans hιV₁_mid
      have hιE'_eS₁ : ιE' e_S₁ = e₀ := by
        have heS₁_not_I₂ : ¬ (e_S₁.Nonempty ∧ e_S₁ ⊆ I₂ \ {s_mid, s₂}) := by
          rintro ⟨_, hsub⟩
          obtain ⟨z, hz⟩ := he_S₁_ne
          have : z ∈ I₁ ∩ I₂ := ⟨hz.1, (hsub hz).1⟩
          rw [hI₁₂_inter, mem_singleton_iff] at this
          exact hz.2 (Or.inr this)
        have he₀_not_rest : ιE₁ e_S₁ ∉ {e' | e' ∈ rest'.edges} := by
          rw [hιE₁_eS₁, hrest'_edges]
          exact (List.nodup_cons.mp hW.edges_nodup).1
        exact (hιE'_eq e_S₁ heS₁_not_I₂ he₀_not_rest).trans hιE₁_eS₁
      have hM₁_emb : M₁.toEmbeddedGraph ιV' ιE' =
          walkSubgraph (GraphWalk.cons hlink (.nil hlink.right_mem)) := by
        have hlink' : G.IsLink e₀ (ιV' s₁) (ιV' s_mid) := by
          rwa [hιV'_s₁, hιV'_mid]
        have h := lineDrawing_toEmbeddedGraph_eq_walkSubgraph hI₁ hs₁_mid hlink' hιE'_eS₁
        refine h.trans ?_
        refine (Compatible.of_le_le (walkSubgraph_le _) (walkSubgraph_le _)).ext ?_ ?_
        · ext x; simp [GraphWalk.support_cons, hιV'_s₁, hιV'_mid]
        · ext e; simp [GraphWalk.edges_cons]
      have hwalk_rest_eq : walkSubgraph rest' = walkSubgraph rest := by
        refine (Compatible.of_le_le (walkSubgraph_le _) (walkSubgraph_le _)).ext ?_ ?_
        · ext x; simp [vertexSet_walkSubgraph, hrest'_supp]
        · ext e; simp [edgeSet_walkSubgraph, hrest'_edges]
      have hunion_walk : graphUnion
          (walkSubgraph (GraphWalk.cons hlink (.nil hlink.right_mem))) (walkSubgraph rest) =
          walkSubgraph (GraphWalk.cons hlink rest) := by
        refine (Compatible.of_le_le
          (graphUnion_le (walkSubgraph_le _) (walkSubgraph_le _)) (walkSubgraph_le _)).ext ?_ ?_
        · ext x
          rw [vertexSet_graphUnion, vertexSet_walkSubgraph, vertexSet_walkSubgraph,
            vertexSet_walkSubgraph]
          simp only [GraphWalk.support_cons, GraphWalk.support_nil, List.mem_cons,
            List.not_mem_nil, or_false, mem_union, mem_ofPred_eq]
          constructor
          · rintro ((rfl | rfl) | hx)
            · exact Or.inl rfl
            · exact Or.inr rest.start_mem_support
            · exact Or.inr hx
          · rintro (rfl | hx)
            · exact Or.inl (Or.inl rfl)
            · exact Or.inr hx
        · ext e
          rw [edgeSet_graphUnion, edgeSet_walkSubgraph, edgeSet_walkSubgraph, edgeSet_walkSubgraph]
          simp [GraphWalk.edges_cons]
      refine ⟨M₁.glue M₂ hmeet, ιV', ιE', ?_, Or.inl (Or.inl rfl), Or.inr hs₂_M₂, ?_, ?_, ?_, ?_⟩
      · change I₁ ∪ M₂.U = L_arc
        rw [hM₂U, hI₁₂_union]
      · rw [Drawing.glue_E]
        exact ⟨e_S₁, Or.inl (hM₁E ▸ mem_singleton e_S₁)⟩
      · rw [glue_toEmbeddedGraph_eq_graphUnion hmeet hE_disj, hM₁_emb, hM₂_emb, hwalk_rest_eq,
          hunion_walk]
      · intro x hx_not_I hx_not_W
        have hx_not_I₂ : x ∉ I₂ \ {s_mid, s₂} := fun h => hx_not_I (hI₂_int_sub h)
        have hx_ne_mid : x ≠ s_mid := fun h => hx_not_I (h ▸ hs_mid_in)
        have hιVx_ne_umid : ιV x ≠ u_mid := fun h =>
          hx_not_W ⟨by simp [h, GraphWalk.support_cons, rest.start_mem_support],
            h ▸ hu_mid_ne_s₁, h ▸ hu_mid_ne_s₂⟩
        have hιV₁_x : ιV₁ x = ιV x :=
          Equiv.swap_apply_of_ne_of_ne (fun h => hx_ne_mid (ιV.injective h)) hιVx_ne_umid
        have hx_not_rest : ιV₁ x ∉ {u ∈ rest'.support | u ≠ ιV₁ s_mid ∧ u ≠ ιV₁ s₂} := by
          rw [hιV₁_x, hrest'_supp, hιV₁_mid, hιV₁_s₂]
          rintro ⟨hu_rest, _, hu_ne_s₂⟩
          have hu_ne_s₁ : ιV x ≠ ιV s₁ := fun h => hnd_cons.1 (h ▸ hu_rest)
          exact hx_not_W ⟨List.mem_cons_of_mem _ hu_rest, hu_ne_s₁, hu_ne_s₂⟩
        exact (hιV'_eq x hx_not_I₂ hx_not_rest).trans hιV₁_x
      · intro e he_not_I he_not_W
        have he_not_I₂ : ¬ (e.Nonempty ∧ e ⊆ I₂ \ {s_mid, s₂}) :=
          fun ⟨hne, hsub⟩ => he_not_I ⟨hne, hsub.trans hI₂_int_sub⟩
        have he_ne_eS₁ : e ≠ e_S₁ :=
          fun h => he_not_I (h ▸ ⟨he_S₁_ne, hI₁_int_sub⟩)
        have hιEe_ne_e₀ : ιE e ≠ e₀ :=
          fun h => he_not_W (by simp [h, GraphWalk.edges_cons])
        have hιE₁_e : ιE₁ e = ιE e :=
          Equiv.swap_apply_of_ne_of_ne (fun h => he_ne_eS₁ (ιE.injective h)) hιEe_ne_e₀
        have he_not_rest : ιE₁ e ∉ {e' | e' ∈ rest'.edges} := by
          rw [hιE₁_e, hrest'_edges]
          intro h
          exact he_not_W (List.mem_cons_of_mem _ h)
        exact (hιE'_eq e he_not_I₂ he_not_rest).trans hιE₁_e

end GraphMinor.GM22
