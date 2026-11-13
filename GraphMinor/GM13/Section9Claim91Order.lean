module

public import GraphMinor.GM13.Section7Four
public import GraphMinor.GM14.Defs
public import GraphMinor.GM12.Section2CirclePeriod

/-!
# Graph Minors XIII, (9.1): Cyclic Order on Subwall Perimeter Circuits and Topological Routing

This file proves two topological ingredients for the proof of **(9.1)** (page 98):
1. `isPreconnected_sdiff_interior_union_frontier`: routing a preconnected set `Y₀` around the
   interior of a closed set `K` via its preconnected frontier `frontier K`.
2. `occurInCircuitOrder_of_pairsCrossOn` and `pairsCrossOn_frontier_fig1EnclosedSet`: four points
   whose opposite pairs cross on an `O`-arc `C.U` occur in cyclic order (`OccurInCircuitOrder`)
   along `C`, and in particular the four attachment points `(1, 2)`, `(1, h - 2)`, `(2h, h - 2)`,
   `(2h, 2)` occur in cyclic order around the boundary circuit of `fig1EnclosedSet h` for every
   even `h ≥ 6`.
-/

@[expose] public section

namespace GraphMinor.GM13

open Set Function Topology
open GraphMinor
open GraphMinor.Surface
open GraphMinor.GM12
open GraphMinor.GM14

universe u

/-! ## 1. Routing a Preconnected Set Around the Interior of a Closed Set -/

/-- If `Y₀` is preconnected, `K` is closed with `frontier K` preconnected, and `Y₀` meets `K`,
then `(Y₀ \ interior K) ∪ frontier K` is preconnected. -/
theorem isPreconnected_sdiff_interior_union_frontier {X : Type*} [TopologicalSpace X]
    {Y₀ K : Set X} (hY₀ : IsPreconnected Y₀) (hK : IsClosed K)
    (hfr : IsPreconnected (frontier K)) (hmeet : (Y₀ ∩ K).Nonempty) :
    IsPreconnected ((Y₀ \ interior K) ∪ frontier K) := by
  have key : ∀ u v : Set X, IsOpen u → IsOpen v →
      (Y₀ \ interior K) ∪ frontier K ⊆ u ∪ v →
      (((Y₀ \ interior K) ∪ frontier K) ∩ (u ∩ v) = ∅) →
      frontier K ⊆ u → (Y₀ \ interior K) ∪ frontier K ⊆ u := by
    intro u v hu hv hcov hdisj hfru
    let u' : Set X := u ∪ interior K
    let v' : Set X := v ∩ Kᶜ
    have hu' : IsOpen u' := hu.union isOpen_interior
    have hv' : IsOpen v' := hv.inter hK.isOpen_compl
    have hcov' : Y₀ ⊆ u' ∪ v' := by
      intro y hy
      by_cases hyInt : y ∈ interior K
      · exact Or.inl (Or.inr hyInt)
      · have hyL : y ∈ (Y₀ \ interior K) ∪ frontier K := Or.inl ⟨hy, hyInt⟩
        rcases hcov hyL with hyu | hyv
        · exact Or.inl (Or.inl hyu)
        · by_cases hyK : y ∈ K
          · have hyFr : y ∈ frontier K := ⟨subset_closure hyK, hyInt⟩
            have hyu : y ∈ u := hfru hyFr
            have : y ∈ ((Y₀ \ interior K) ∪ frontier K) ∩ (u ∩ v) := ⟨Or.inr hyFr, hyu, hyv⟩
            rw [hdisj] at this
            exact this.elim
          · exact Or.inr ⟨hyv, hyK⟩
    have hdisj' : Y₀ ∩ (u' ∩ v') = ∅ := by
      ext y
      simp only [mem_inter_iff, mem_empty_iff_false, iff_false, not_and]
      intro hyY₀ hyu' ⟨hyv, hyK⟩
      have hyInt : y ∉ interior K := fun h => hyK (interior_subset h)
      have hyu : y ∈ u := hyu'.resolve_right hyInt
      have : y ∈ ((Y₀ \ interior K) ∪ frontier K) ∩ (u ∩ v) :=
        ⟨Or.inl ⟨hyY₀, hyInt⟩, hyu, hyv⟩
      rw [hdisj] at this
      exact this
    rcases isPreconnected_iff_subset_of_disjoint.mp hY₀ u' v' hu' hv' hcov' hdisj' with hsub | hsub
    · refine union_subset ?_ hfru
      intro y ⟨hyY₀, hyInt⟩
      exact (hsub hyY₀).resolve_right hyInt
    · exfalso
      obtain ⟨z, hzY₀, hzK⟩ := hmeet
      exact (hsub hzY₀).2 hzK
  rw [isPreconnected_iff_subset_of_disjoint]
  intro u v hu hv hcov hdisj
  have hfr_cov : frontier K ⊆ u ∪ v := subset_union_right.trans hcov
  have hfr_disj : frontier K ∩ (u ∩ v) = ∅ :=
    subset_empty_iff.mp ((inter_subset_inter_left _ subset_union_right).trans hdisj.subset)
  rcases isPreconnected_iff_subset_of_disjoint.mp hfr u v hu hv hfr_cov hfr_disj with hfru | hfrv
  · exact Or.inl (key u v hu hv hcov hdisj hfru)
  · refine Or.inr (key v u hv hu (by rwa [union_comm v u]) ?_ hfrv)
    rwa [inter_comm v u]

/-- Given a finite family `D : ι → Set X` of pairwise disjoint closed sets with preconnected
frontiers, any preconnected set `Y₀ ⊆ X` can be routed around all `interior (D c)` (`c ∈ S`)
to form a preconnected set `Y` satisfying:
- `Y ⊆ Y₀ ∪ ⋃ c ∈ S, frontier (D c)`,
- `∀ c ∈ S, Disjoint Y (interior (D c))`,
- `∀ p ∈ Y₀, (∀ c ∈ S, p ∉ interior (D c)) → p ∈ Y`. -/
theorem exists_preconnected_routeFinset {X : Type*} [TopologicalSpace X] {ι : Type*} [DecidableEq ι]
    (S : Finset ι) (D : ι → Set X)
    (hClosed : ∀ c ∈ S, IsClosed (D c))
    (hFr : ∀ c ∈ S, IsPreconnected (frontier (D c)))
    (hDisj : ∀ c₁ ∈ S, ∀ c₂ ∈ S, c₁ ≠ c₂ → Disjoint (D c₁) (D c₂))
    {Y₀ : Set X} (hY₀ : IsPreconnected Y₀) :
    ∃ Y : Set X,
      IsPreconnected Y ∧
      Y ⊆ Y₀ ∪ (⋃ c ∈ S, frontier (D c)) ∧
      (∀ c ∈ S, Disjoint Y (interior (D c))) ∧
      (∀ p ∈ Y₀, (∀ c ∈ S, p ∉ interior (D c)) → p ∈ Y) := by
  induction S using Finset.induction_on with
  | empty =>
    refine ⟨Y₀, hY₀, by simp, fun c hc => (Finset.notMem_empty c hc).elim, fun p hp _ => hp⟩
  | @insert a S' ha ih =>
    have hClosed' : ∀ c ∈ S', IsClosed (D c) :=
      fun c hc => hClosed c (Finset.mem_insert_of_mem hc)
    have hFr' : ∀ c ∈ S', IsPreconnected (frontier (D c)) :=
      fun c hc => hFr c (Finset.mem_insert_of_mem hc)
    have hDisj' : ∀ c₁ ∈ S', ∀ c₂ ∈ S', c₁ ≠ c₂ → Disjoint (D c₁) (D c₂) :=
      fun c₁ hc₁ c₂ hc₂ hne =>
        hDisj c₁ (Finset.mem_insert_of_mem hc₁) c₂ (Finset.mem_insert_of_mem hc₂) hne
    obtain ⟨Y', hY'_pre, hY'_sub, hY'_disj, hY'_mem⟩ := ih hClosed' hFr' hDisj'
    by_cases hmeet : (Y' ∩ D a).Nonempty
    · let Y := (Y' \ interior (D a)) ∪ frontier (D a)
      have ha_mem : a ∈ insert a S' := Finset.mem_insert_self a S'
      have hY_pre : IsPreconnected Y :=
        isPreconnected_sdiff_interior_union_frontier hY'_pre (hClosed a ha_mem) (hFr a ha_mem) hmeet
      refine ⟨Y, hY_pre, ?_, ?_, ?_⟩
      · intro z hz
        rcases hz with ⟨hzY', -⟩ | hzFr
        · rcases hY'_sub hzY' with hzY₀ | hzU
          · exact Or.inl hzY₀
          · obtain ⟨c, hc, hzc⟩ := mem_iUnion₂.mp hzU
            exact Or.inr (mem_iUnion₂.mpr ⟨c, Finset.mem_insert_of_mem hc, hzc⟩)
        · exact Or.inr (mem_iUnion₂.mpr ⟨a, ha_mem, hzFr⟩)
      · intro c hc
        rcases Finset.mem_insert.mp hc with rfl | hc'
        · rw [Set.disjoint_left]
          rintro z (⟨-, hnot⟩ | ⟨-, hnot⟩) hint
          · exact hnot hint
          · exact hnot hint
        · rw [Set.disjoint_left]
          rintro z (⟨hzY', -⟩ | hzFr) hint
          · exact Set.disjoint_left.mp (hY'_disj c hc') hzY' hint
          · have hDa : z ∈ D a := (hClosed a ha_mem).frontier_subset hzFr
            have hDc : z ∈ D c := interior_subset hint
            have hne : a ≠ c := fun h => ha (h ▸ hc')
            exact Set.disjoint_left.mp
              (hDisj a ha_mem c (Finset.mem_insert_of_mem hc') hne) hDa hDc
      · intro p hp hp_not
        refine Or.inl ⟨hY'_mem p hp (fun c hc => hp_not c (Finset.mem_insert_of_mem hc)), ?_⟩
        exact hp_not a ha_mem
    · refine ⟨Y', hY'_pre, ?_, ?_, ?_⟩
      · intro z hz
        rcases hY'_sub hz with hzY₀ | hzU
        · exact Or.inl hzY₀
        · obtain ⟨c, hc, hzc⟩ := mem_iUnion₂.mp hzU
          exact Or.inr (mem_iUnion₂.mpr ⟨c, Finset.mem_insert_of_mem hc, hzc⟩)
      · intro c hc
        rcases Finset.mem_insert.mp hc with rfl | hc'
        · rw [Set.disjoint_left]
          intro z hzY' hint
          exact hmeet ⟨z, hzY', interior_subset hint⟩
        · exact hY'_disj c hc'
      · intro p hp hp_not
        exact hY'_mem p hp (fun c hc => hp_not c (Finset.mem_insert_of_mem hc))

/-! ## 2. `OccurInCircuitOrder` from `PairsCrossOn` -/

/-- Transporting `PairsCrossOn` along a topological embedding. -/
theorem PairsCrossOn.image_of_isEmbedding {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {f : X → Y} (hf : Topology.IsEmbedding f) {K : Set X} {a c b d : X}
    (h : PairsCrossOn K a c b d) :
    PairsCrossOn (f '' K) (f a) (f c) (f b) (f d) := by
  rcases h with ⟨ha, hb, hc, hd, hac, hbd, hab, had, hcb, hcd, hcomp⟩
  refine ⟨mem_image_of_mem f ha, mem_image_of_mem f hb, mem_image_of_mem f hc,
    mem_image_of_mem f hd, hf.injective.ne hac, hf.injective.ne hbd, hf.injective.ne hab,
    hf.injective.ne had, hf.injective.ne hcb, hf.injective.ne hcd, ?_⟩
  intro heq
  let C_Y := connectedComponentIn (f '' K \ {f a, f c}) (f b)
  let Z := f ⁻¹' C_Y
  have hCY_sub : C_Y ⊆ f '' K \ {f a, f c} := connectedComponentIn_subset _ _
  have hZ_sub : Z ⊆ K \ {a, c} := by
    intro x hx
    obtain ⟨⟨x', hx'K, hfx'⟩, hnot⟩ := hCY_sub hx
    rw [hf.injective hfx'] at hx'K
    refine ⟨hx'K, ?_⟩
    rintro (rfl | rfl)
    · exact hnot (Or.inl rfl)
    · exact hnot (Or.inr rfl)
  have hfZ : f '' Z = C_Y := by
    refine Subset.antisymm (image_preimage_subset f C_Y) ?_
    intro y hy
    obtain ⟨⟨x, _, rfl⟩, -⟩ := hCY_sub hy
    exact ⟨x, hy, rfl⟩
  have hZ_pre : IsPreconnected Z := by
    rw [← hf.isInducing.isPreconnected_image, hfZ]
    exact isPreconnected_connectedComponentIn
  have hb_mem : f b ∈ f '' K \ {f a, f c} := by
    refine ⟨mem_image_of_mem f hb, ?_⟩
    rintro (h | h)
    · exact hab (hf.injective h).symm
    · exact hcb (hf.injective h).symm
  have hd_mem : f d ∈ f '' K \ {f a, f c} := by
    refine ⟨mem_image_of_mem f hd, ?_⟩
    rintro (h | h)
    · exact had (hf.injective h).symm
    · exact hcd (hf.injective h).symm
  have hbZ : b ∈ Z := mem_connectedComponentIn hb_mem
  have hdZ : d ∈ Z := by
    change f d ∈ connectedComponentIn (f '' K \ {f a, f c}) (f b)
    rw [heq]
    exact mem_connectedComponentIn hd_mem
  have hd_comp : d ∈ connectedComponentIn (K \ {a, c}) b :=
    hZ_pre.subset_connectedComponentIn hbZ hZ_sub hdZ
  exact hcomp (connectedComponentIn_eq hd_comp)

/-- Every point `z ≠ 1` on `Circle` is `Circle.exp θ` for a unique `θ ∈ Ioo 0 (2 * Real.pi)`. -/
private lemma exists_angle_mem_Ioo {z : Circle} (hz : z ≠ 1) :
    ∃ θ ∈ Ioo (0 : ℝ) (2 * Real.pi), Circle.exp θ = z := by
  obtain ⟨s, hs, hsz⟩ := (circle_parameter_bijOn 0).surjOn (mem_univ z)
  rw [zero_add] at hs
  have hs0 : s ≠ 0 := by
    rintro rfl
    apply hz
    dsimp only at hsz
    rw [← hsz, mul_zero, Circle.exp_zero]
  have hs_pos : 0 < s := lt_of_le_of_ne hs.1 hs0.symm
  refine ⟨2 * Real.pi * s, ⟨mul_pos Real.two_pi_pos hs_pos, ?_⟩, hsz⟩
  simpa using mul_lt_mul_of_pos_left hs.2 Real.two_pi_pos

/-- Injectivity of `Circle.exp` on `Ico 0 (2 * Real.pi)`. -/
private lemma circle_exp_injOn_Ico_two_pi :
    InjOn Circle.exp (Ico (0 : ℝ) (2 * Real.pi)) := by
  simpa using Circle.exp_injOn_Ico (a := (0 : ℝ)) (b := 2 * Real.pi) (by linarith)

/-- If `C.U` is an `O`-arc and `PairsCrossOn C.U a c b d`, then `[a, b, c, d].Nodup` and
`OccurInCircuitOrder C a b c d`. -/
theorem occurInCircuitOrder_of_pairsCrossOn {S : Type*} [TopologicalSpace S]
    {C : Drawing S} (hO : IsOArc C.U) {a b c d : S}
    (hcross : PairsCrossOn C.U a c b d) :
    ([a, b, c, d]).Nodup ∧ OccurInCircuitOrder C a b c d := by
  rcases hcross with ⟨ha, hb, hc, hd, hac, hbd, hab, had, hcb, hcd, hcomp⟩
  have hnodup : ([a, b, c, d]).Nodup := by
    simp [List.nodup_cons, hab, hac, had, hcb.symm, hbd, hcd]
  refine ⟨hnodup, ?_⟩
  rcases hO with ⟨φ₀⟩
  let za : Circle := φ₀.symm ⟨a, ha⟩
  let φ₁ : Circle ≃ₜ C.U := (Homeomorph.mulLeft za).trans φ₀
  have hφ₁_one : (φ₁ 1).1 = a := by
    change (φ₀ (za * 1)).1 = a
    rw [mul_one, Homeomorph.apply_symm_apply]
  have hφ₁_zero : (φ₁ (Circle.exp 0)).1 = a := by
    rw [Circle.exp_zero, hφ₁_one]
  have hne_one : ∀ {x : S} (hx : x ∈ C.U), x ≠ a → φ₁.symm ⟨x, hx⟩ ≠ 1 := by
    intro x hx hxa h1
    apply hxa
    have : φ₁ (φ₁.symm ⟨x, hx⟩) = φ₁ 1 := congrArg φ₁ h1
    rw [Homeomorph.apply_symm_apply] at this
    exact (congrArg Subtype.val this).trans hφ₁_one
  obtain ⟨tb, htb, htb_eq⟩ := exists_angle_mem_Ioo (hne_one hb hab.symm)
  obtain ⟨tc, htc, htc_eq⟩ := exists_angle_mem_Ioo (hne_one hc hac.symm)
  obtain ⟨td, htd, htd_eq⟩ := exists_angle_mem_Ioo (hne_one hd had.symm)
  have hφ₁_tb : (φ₁ (Circle.exp tb)).1 = b := by
    rw [htb_eq, Homeomorph.apply_symm_apply]
  have hφ₁_tc : (φ₁ (Circle.exp tc)).1 = c := by
    rw [htc_eq, Homeomorph.apply_symm_apply]
  have hφ₁_td : (φ₁ (Circle.exp td)).1 = d := by
    rw [htd_eq, Homeomorph.apply_symm_apply]
  have hbc_t : tb ≠ tc := by
    intro h
    apply hcb.symm
    rw [← hφ₁_tb, ← hφ₁_tc, h]
  have hdc_t : td ≠ tc := by
    intro h
    apply hcd.symm
    rw [← hφ₁_td, ← hφ₁_tc, h]
  have hbd_t : tb ≠ td := by
    intro h
    apply hbd
    rw [← hφ₁_tb, ← hφ₁_td, h]
  -- Two points in the same open arc `(0, tc)` or `(tc, 2π)` lie in the same component of `C.U \ {a, c}`
  have hnot_same_arc : ∀ {u v : ℝ},
      Ioo u v ⊆ Ioo (0 : ℝ) (2 * Real.pi) →
      (∀ t ∈ Ioo u v, t ≠ tc) →
      tb ∈ Ioo u v → td ∈ Ioo u v → False := by
    intro u v huv hnot_tc htb_uv htd_uv
    let f : ℝ → S := fun t => (φ₁ (Circle.exp t)).1
    have hf_cont : Continuous f :=
      continuous_subtype_val.comp (φ₁.continuous.comp Circle.exp.continuous)
    let A := f '' Ioo u v
    have hA_pre : IsPreconnected A := isPreconnected_Ioo.image f hf_cont.continuousOn
    have hA_sub : A ⊆ C.U \ {a, c} := by
      rintro _ ⟨t, ht, rfl⟩
      have ht_Ioo := huv ht
      refine ⟨(φ₁ (Circle.exp t)).2, ?_⟩
      rintro (hfa | hfc)
      · have h1 : φ₁ (Circle.exp t) = φ₁ (Circle.exp 0) := Subtype.ext (hfa.trans hφ₁_zero.symm)
        have h2 := circle_exp_injOn_Ico_two_pi ⟨ht_Ioo.1.le, ht_Ioo.2⟩ ⟨le_rfl, Real.two_pi_pos⟩
          (φ₁.injective h1)
        linarith [ht_Ioo.1]
      · have h1 : φ₁ (Circle.exp t) = φ₁ (Circle.exp tc) := Subtype.ext (hfc.trans hφ₁_tc.symm)
        have h2 := circle_exp_injOn_Ico_two_pi ⟨ht_Ioo.1.le, ht_Ioo.2⟩ ⟨htc.1.le, htc.2⟩
          (φ₁.injective h1)
        exact hnot_tc t ht h2
    have hbA : b ∈ A := ⟨tb, htb_uv, hφ₁_tb⟩
    have hdA : d ∈ A := ⟨td, htd_uv, hφ₁_td⟩
    have hd_comp : d ∈ connectedComponentIn (C.U \ {a, c}) b :=
      hA_pre.subset_connectedComponentIn hbA hA_sub hdA
    exact hcomp (connectedComponentIn_eq hd_comp)
  rcases lt_or_gt_of_ne hbc_t with htb_lt_tc | htc_lt_tb
  · rcases lt_or_gt_of_ne hdc_t with htd_lt_tc | htc_lt_td
    · exfalso
      exact hnot_same_arc (Ioo_subset_Ioo le_rfl htc.2.le) (fun t ht => ne_of_lt ht.2)
        ⟨htb.1, htb_lt_tc⟩ ⟨htd.1, htd_lt_tc⟩
    · exact ⟨φ₁, 0, tb, tc, td, le_rfl, htb.1, htb_lt_tc, htc_lt_td, htd.2,
        hφ₁_zero, hφ₁_tb, hφ₁_tc, hφ₁_td⟩
  · rcases lt_or_gt_of_ne hdc_t with htd_lt_tc | htc_lt_td
    · -- Reverse orientation of `Circle` via `Homeomorph.inv Circle`
      let φ₂ : Circle ≃ₜ C.U := (Homeomorph.inv Circle).trans φ₁
      have hexp_sub : ∀ t : ℝ, (Circle.exp (2 * Real.pi - t))⁻¹ = Circle.exp t := by
        intro t
        rw [← Circle.exp_neg, neg_sub, Circle.periodic_exp.sub_eq]
      refine ⟨φ₂, 0, 2 * Real.pi - tb, 2 * Real.pi - tc, 2 * Real.pi - td,
        le_rfl, by linarith [htb.2], by linarith, by linarith, by linarith [htd.1], ?_, ?_, ?_, ?_⟩
      · change (φ₁ (Circle.exp 0)⁻¹).1 = a
        rw [Circle.exp_zero, inv_one, hφ₁_one]
      · change (φ₁ (Circle.exp (2 * Real.pi - tb))⁻¹).1 = b
        rw [hexp_sub, hφ₁_tb]
      · change (φ₁ (Circle.exp (2 * Real.pi - tc))⁻¹).1 = c
        rw [hexp_sub, hφ₁_tc]
      · change (φ₁ (Circle.exp (2 * Real.pi - td))⁻¹).1 = d
        rw [hexp_sub, hφ₁_td]
    · exfalso
      exact hnot_same_arc (Ioo_subset_Ioo htc.1.le le_rfl) (fun t ht => ne_of_gt ht.1)
        ⟨htc_lt_tb, htb.2⟩ ⟨htc_lt_td, htd.2⟩

/-! ## 3. `PairsCrossOn` on `frontier (fig1EnclosedSet h)` -/

/-- `fig1EnclosedSet h` is a closed set in `ℝ × ℝ`. -/
theorem isClosed_fig1EnclosedSet (h : ℕ) : IsClosed (fig1EnclosedSet h) := by
  unfold fig1EnclosedSet GM16.rectangleStack
  exact (Set.finite_lt_nat h).isClosed_biUnion fun k _ => isClosed_Icc.prod isClosed_Icc

/-- Every rectangle `[1, 2h] × [k, k + 1]` for `k < h` lies in `fig1EnclosedSet h`. -/
lemma rect_subset_fig1EnclosedSet {h : ℕ} :
    Icc (1 : ℝ) (2 * (h : ℝ)) ×ˢ Icc (0 : ℝ) (h : ℝ) ⊆ fig1EnclosedSet h := by
  rcases eq_or_ne h 0 with rfl | hh0
  · rintro ⟨x, y⟩ ⟨⟨hx1, hx2⟩, _⟩
    norm_num at hx2
    linarith
  rintro ⟨x, y⟩ ⟨⟨hx1, hx2⟩, ⟨hy1, hy2⟩⟩
  let k := min ⌊y⌋₊ (h - 1)
  have hk_lt : k < h := lt_of_le_of_lt (min_le_right _ _) (Nat.sub_lt (Nat.pos_of_ne_zero hh0) zero_lt_one)
  refine mem_iUnion₂.mpr ⟨k, hk_lt, ⟨?_, ?_⟩, ?_⟩
  · exact (fig1RowLeft_bounds k).2.trans hx1
  · have h0 : 0 ≤ fig1RowLeft k := (fig1RowLeft_bounds k).1
    unfold fig1RowRight
    linarith
  · rcases le_or_gt ⌊y⌋₊ (h - 1) with hle | hgt
    · have hk_eq : k = ⌊y⌋₊ := min_eq_left hle
      rw [hk_eq]
      exact ⟨Nat.floor_le hy1, (Nat.lt_floor_add_one y).le⟩
    · have hk_eq : k = h - 1 := min_eq_right hgt.le
      have hy_lo : ((h - 1 : ℕ) : ℝ) ≤ y :=
        (by exact_mod_cast hgt.le : ((h - 1 : ℕ) : ℝ) ≤ (⌊y⌋₊ : ℝ)).trans (Nat.floor_le hy1)
      have hh1 : ((h - 1 : ℕ) : ℝ) + 1 = (h : ℝ) := by
        have : (h - 1) + 1 = h := Nat.sub_add_cancel (Nat.pos_of_ne_zero hh0)
        have h1 : (((h - 1) + 1 : ℕ) : ℝ) = (h : ℝ) := by exact_mod_cast this
        push_cast at h1
        linarith
      rw [hk_eq]
      exact ⟨hy_lo, by linarith⟩

/-- The open rectangle `(1, 2h) × (0, h)` lies in `interior (fig1EnclosedSet h)`. -/
lemma open_rect_subset_interior_fig1EnclosedSet (h : ℕ) :
    Ioo (1 : ℝ) (2 * (h : ℝ)) ×ˢ Ioo (0 : ℝ) (h : ℝ) ⊆ interior (fig1EnclosedSet h) := by
  have h1 : Ioo (1 : ℝ) (2 * (h : ℝ)) ×ˢ Ioo (0 : ℝ) (h : ℝ) =
      interior (Icc (1 : ℝ) (2 * (h : ℝ)) ×ˢ Icc (0 : ℝ) (h : ℝ)) := by
    rw [interior_prod_eq, interior_Icc, interior_Icc]
  rw [h1]
  exact interior_mono rect_subset_fig1EnclosedSet

/-- If `(x, y) ∈ fig1EnclosedSet h` and `k < y < k + 1` for a natural number `k`, then `(x, y)`
can only belong to row `k` of `fig1EnclosedSet h`, so `fig1RowLeft k ≤ x ≤ fig1RowRight h k`. -/
lemma row_bounds_of_mem_fig1EnclosedSet {h k : ℕ} {x y : ℝ}
    (hmem : (x, y) ∈ fig1EnclosedSet h) (hy1 : (k : ℝ) < y) (hy2 : y < (k : ℝ) + 1) :
    fig1RowLeft k ≤ x ∧ x ≤ fig1RowRight h k := by
  obtain ⟨m, hm, ⟨hx1, hx2⟩, ⟨hmy1, hmy2⟩⟩ := mem_iUnion₂.mp hmem
  have hmk : m = k := by
    have h1 : (m : ℝ) < (k : ℝ) + 1 := lt_of_le_of_lt hmy1 hy2
    have h2 : (k : ℝ) < (m : ℝ) + 1 := lt_of_lt_of_le hy1 hmy2
    have h1' : m < k + 1 := by exact_mod_cast h1
    have h2' : k < m + 1 := by exact_mod_cast h2
    omega
  subst hmk
  exact ⟨hx1, hx2⟩

/-- For even `h ≥ 6`, the four attachment points `(1, 2)`, `(2h, h - 2)`, `(1, h - 2)`, `(2h, 2)`
lie on `frontier (fig1EnclosedSet h)` and cross on `frontier (fig1EnclosedSet h)`. -/
theorem pairsCrossOn_frontier_fig1EnclosedSet {h : ℕ} (h6 : 6 ≤ h) (heven : Even h) :
    PairsCrossOn (frontier (fig1EnclosedSet h))
      ((1 : ℝ), (2 : ℝ)) (2 * (h : ℝ), (h : ℝ) - 2)
      ((1 : ℝ), (h : ℝ) - 2) (2 * (h : ℝ), (2 : ℝ)) := by
  have hh_real : (6 : ℝ) ≤ (h : ℝ) := by exact_mod_cast h6
  let pa : ℝ × ℝ := (1, 2)
  let pc : ℝ × ℝ := (2 * (h : ℝ), (h : ℝ) - 2)
  let pb : ℝ × ℝ := (1, (h : ℝ) - 2)
  let pd : ℝ × ℝ := (2 * (h : ℝ), 2)
  have hpa_cl : pa ∈ closure (fig1EnclosedSet h) :=
    subset_closure (rect_subset_fig1EnclosedSet ⟨⟨le_rfl, by linarith⟩, ⟨by linarith, by linarith⟩⟩)
  have hpc_cl : pc ∈ closure (fig1EnclosedSet h) :=
    subset_closure (rect_subset_fig1EnclosedSet ⟨⟨by linarith, le_rfl⟩, ⟨by linarith, by linarith⟩⟩)
  have hpb_cl : pb ∈ closure (fig1EnclosedSet h) :=
    subset_closure (rect_subset_fig1EnclosedSet ⟨⟨le_rfl, by linarith⟩, ⟨by linarith, by linarith⟩⟩)
  have hpd_cl : pd ∈ closure (fig1EnclosedSet h) :=
    subset_closure (rect_subset_fig1EnclosedSet ⟨⟨by linarith, le_rfl⟩, ⟨by linarith, by linarith⟩⟩)
  -- Helper to show a point is not in `interior (fig1EnclosedSet h)` by exhibiting a sequence/point in every ball
  have hnot_int_left : ∀ (k : ℕ), Even k → ¬ ((1 : ℝ), (k : ℝ)) ∈ interior (fig1EnclosedSet h) := by
    intro k hk hint
    rw [mem_interior_iff_mem_nhds, Metric.mem_nhds_iff] at hint
    obtain ⟨ε, hε, hball⟩ := hint
    let δ := min (ε / 2) (1 / 2)
    have hδ_pos : 0 < δ := lt_min (by linarith) (by norm_num)
    have hδ_le : δ ≤ 1 / 2 := min_le_right _ _
    have hδ_lt_ε : δ < ε := lt_of_le_of_lt (min_le_left _ _) (by linarith)
    let z : ℝ × ℝ := (1 - δ, (k : ℝ) + δ)
    have hz_ball : z ∈ Metric.ball ((1 : ℝ), (k : ℝ)) ε := by
      rw [Metric.mem_ball, Prod.dist_eq]
      refine max_lt ?_ ?_
      · simp [z, abs_of_pos hδ_pos, hδ_lt_ε]
      · simp [z, abs_of_pos hδ_pos, hδ_lt_ε]
    have hbounds := row_bounds_of_mem_fig1EnclosedSet (hball hz_ball) (k := k)
      (by linarith) (by linarith)
    have hleft : fig1RowLeft k = 1 := by simp [fig1RowLeft, hk]
    linarith [hbounds.1]
  have hnot_int_right : ∀ (k : ℕ), ¬ Even k →
      ¬ (2 * (h : ℝ), (k : ℝ) + 1) ∈ interior (fig1EnclosedSet h) := by
    intro k hk hint
    rw [mem_interior_iff_mem_nhds, Metric.mem_nhds_iff] at hint
    obtain ⟨ε, hε, hball⟩ := hint
    let δ := min (ε / 2) (1 / 2)
    have hδ_pos : 0 < δ := lt_min (by linarith) (by norm_num)
    have hδ_le : δ ≤ 1 / 2 := min_le_right _ _
    have hδ_lt_ε : δ < ε := lt_of_le_of_lt (min_le_left _ _) (by linarith)
    let z : ℝ × ℝ := (2 * (h : ℝ) + δ, (k : ℝ) + 1 - δ)
    have hz_ball : z ∈ Metric.ball (2 * (h : ℝ), (k : ℝ) + 1) ε := by
      rw [Metric.mem_ball, Prod.dist_eq]
      refine max_lt ?_ ?_
      · simp [z, abs_of_pos hδ_pos, hδ_lt_ε]
      · simp [z, abs_of_pos hδ_pos, hδ_lt_ε]
    have hbounds := row_bounds_of_mem_fig1EnclosedSet (hball hz_ball) (k := k)
      (by linarith) (by linarith)
    have hright : fig1RowRight h k = 2 * (h : ℝ) := by
      unfold fig1RowRight fig1RowLeft
      rw [ite_eq_right_iff.mpr fun h => (hk h).elim, add_zero]
    linarith [hbounds.2]
  have hpa_fr : pa ∈ frontier (fig1EnclosedSet h) :=
    ⟨hpa_cl, by simpa [pa] using hnot_int_left 2 ⟨1, rfl⟩⟩
  have hpb_fr : pb ∈ frontier (fig1EnclosedSet h) := by
    refine ⟨hpb_cl, ?_⟩
    have hev_h2 : Even (h - 2) := by
      rcases heven with ⟨m, rfl⟩
      exact ⟨m - 1, by omega⟩
    have hcast : ((h - 2 : ℕ) : ℝ) = (h : ℝ) - 2 := by
      have : (h - 2) + 2 = h := Nat.sub_add_cancel (by omega)
      have h1 : (((h - 2) + 2 : ℕ) : ℝ) = (h : ℝ) := by exact_mod_cast this
      push_cast at h1
      linarith
    simpa [pb, hcast] using hnot_int_left (h - 2) hev_h2
  have hpc_fr : pc ∈ frontier (fig1EnclosedSet h) := by
    refine ⟨hpc_cl, ?_⟩
    have hodd_h3 : ¬ Even (h - 3) := by
      rcases heven with ⟨m, rfl⟩
      rw [Nat.even_iff]
      omega
    have hcast : ((h - 3 : ℕ) : ℝ) + 1 = (h : ℝ) - 2 := by
      have : (h - 3) + 3 = h := Nat.sub_add_cancel (by omega)
      have h1 : (((h - 3) + 3 : ℕ) : ℝ) = (h : ℝ) := by exact_mod_cast this
      push_cast at h1
      linarith
    simpa [pc, hcast] using hnot_int_right (h - 3) hodd_h3
  have hpd_fr : pd ∈ frontier (fig1EnclosedSet h) := by
    refine ⟨hpd_cl, ?_⟩
    have h1 := hnot_int_right 1 (by decide)
    norm_num at h1
    exact h1
  refine ⟨hpa_fr, hpb_fr, hpc_fr, hpd_fr, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro h; have := congrArg Prod.fst h; dsimp [pa, pc] at this; linarith
  · intro h; have := congrArg Prod.fst h; dsimp [pb, pd] at this; linarith
  · intro h; have := congrArg Prod.snd h; dsimp [pa, pb] at this; linarith
  · intro h; have := congrArg Prod.fst h; dsimp [pa, pd] at this; linarith
  · intro h; have := congrArg Prod.fst h; dsimp [pc, pb] at this; linarith
  · intro h; have := congrArg Prod.snd h; dsimp [pc, pd] at this; linarith
  · -- Separation of `pb` and `pd` in `frontier (fig1EnclosedSet h) \ {pa, pc}` via `G`
    let G : ℝ × ℝ → ℝ := fun z =>
      (2 * (h : ℝ) - 1) * ((z.1 - 1) + 2 * (z.2 - 2)) -
        (4 * (h : ℝ) - 9) * max 0 (min (2 * (h : ℝ) - 1) (z.1 - 1))
    have hG_cont : Continuous G := by fun_prop
    have hG_pb : 0 < G pb := by
      dsimp [G, pb]
      rw [sub_self, min_eq_right (by linarith), max_self, mul_zero, sub_zero]
      nlinarith
    have hG_pd : G pd < 0 := by
      dsimp [G, pd]
      rw [show 2 * (h : ℝ) - 1 = 2 * (h : ℝ) - 1 from rfl, min_self,
        max_eq_right (by linarith)]
      nlinarith
    have hG_ne_zero : ∀ z ∈ frontier (fig1EnclosedSet h) \ {pa, pc}, G z ≠ 0 := by
      rintro ⟨x, y⟩ ⟨hz_fr, hz_not_ac⟩ hG0
      have hz_mem : (x, y) ∈ fig1EnclosedSet h :=
        (isClosed_fig1EnclosedSet h).closure_eq ▸ hz_fr.1
      obtain ⟨k, hk_lt, ⟨hx_lo, hx_hi⟩, ⟨hy_lo, hy_hi⟩⟩ := mem_iUnion₂.mp hz_mem
      dsimp only at hx_lo hx_hi hy_lo hy_hi
      have hk_le : (k : ℝ) + 1 ≤ (h : ℝ) := by exact_mod_cast hk_lt
      have hleft_bds := fig1RowLeft_bounds k
      have hy_0h : 0 ≤ y ∧ y ≤ (h : ℝ) := ⟨(Nat.cast_nonneg k).trans hy_lo, hy_hi.trans hk_le⟩
      have hnot_open : ¬ (1 < x ∧ x < 2 * (h : ℝ) ∧ 0 < y ∧ y < (h : ℝ)) := by
        rintro ⟨hx1, hx2, hy1, hy2⟩
        exact hz_fr.2 (open_rect_subset_interior_fig1EnclosedSet h ⟨⟨hx1, hx2⟩, ⟨hy1, hy2⟩⟩)
      rcases le_or_gt x 1 with hx1 | hx1
      · -- Case 1: `x ≤ 1`
        have hmax0 : max (0 : ℝ) (min (2 * (h : ℝ) - 1) (x - 1)) = 0 :=
          max_eq_left (min_le_of_right_le (by linarith))
        dsimp [G] at hG0
        rw [hmax0, mul_zero, sub_zero] at hG0
        have hxy5 : x + 2 * y = 5 := by nlinarith
        have hk2 : k = 0 ∨ k = 1 ∨ k = 2 ∨ 3 ≤ k := by omega
        rcases hk2 with rfl | rfl | rfl | hk3
        · simp at hy_hi; linarith [hleft_bds.1]
        · norm_num at hy_hi
          have hy2 : y = 2 := by linarith [hleft_bds.1]
          have hx_eq : x = 1 := by linarith
          exact hz_not_ac (Or.inl (Prod.ext hx_eq hy2))
        · have hl2 : fig1RowLeft 2 = 1 := by simp [fig1RowLeft]
          rw [hl2] at hx_lo
          norm_num at hy_lo
          have hx_eq : x = 1 := by linarith
          have hy2 : y = 2 := by linarith
          exact hz_not_ac (Or.inl (Prod.ext hx_eq hy2))
        · have hk3_r : (3 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk3
          linarith [hleft_bds.1]
      · rcases le_or_gt (2 * (h : ℝ)) x with hx2 | hx2
        · -- Case 2: `x ≥ 2h`
          have hmax1 : max (0 : ℝ) (min (2 * (h : ℝ) - 1) (x - 1)) = 2 * (h : ℝ) - 1 := by
            rw [min_eq_left (by linarith), max_eq_right (by linarith)]
          dsimp [G] at hG0
          rw [hmax1] at hG0
          have hxy : (x - 2 * (h : ℝ)) + 2 * (y - ((h : ℝ) - 2)) = 0 := by nlinarith
          have hx_up : x ≤ 2 * (h : ℝ) + 1 := by
            unfold fig1RowRight at hx_hi
            linarith [hleft_bds.2]
          have hkh : k + 4 ≤ h ∨ k = h - 3 ∨ k = h - 2 ∨ k = h - 1 := by omega
          rcases hkh with hk4 | rfl | rfl | rfl
          · have hk4_r : (k : ℝ) + 4 ≤ (h : ℝ) := by exact_mod_cast hk4
            linarith
          · have hodd : ¬ Even (h - 3) := by
              rcases heven with ⟨m, rfl⟩; rw [Nat.even_iff]; omega
            have hr_eq : fig1RowRight h (h - 3) = 2 * (h : ℝ) := by
              unfold fig1RowRight fig1RowLeft
              rw [ite_eq_right_iff.mpr fun h => (hodd h).elim, add_zero]
            rw [hr_eq] at hx_hi
            have hk_r : ((h - 3 : ℕ) : ℝ) + 1 = (h : ℝ) - 2 := by
              have : (h - 3) + 3 = h := Nat.sub_add_cancel (by omega)
              have h1 : (((h - 3) + 3 : ℕ) : ℝ) = (h : ℝ) := by exact_mod_cast this
              push_cast at h1; linarith
            have hx_eq : x = 2 * (h : ℝ) := by linarith
            have hy_eq : y = (h : ℝ) - 2 := by linarith
            exact hz_not_ac (Or.inr (Prod.ext hx_eq hy_eq))
          · have hk_r : ((h - 2 : ℕ) : ℝ) = (h : ℝ) - 2 := by
              have : (h - 2) + 2 = h := Nat.sub_add_cancel (by omega)
              have h1 : (((h - 2) + 2 : ℕ) : ℝ) = (h : ℝ) := by exact_mod_cast this
              push_cast at h1; linarith
            have hx_eq : x = 2 * (h : ℝ) := by linarith
            have hy_eq : y = (h : ℝ) - 2 := by linarith
            exact hz_not_ac (Or.inr (Prod.ext hx_eq hy_eq))
          · have hk_r : ((h - 1 : ℕ) : ℝ) = (h : ℝ) - 1 := by
              have : (h - 1) + 1 = h := Nat.sub_add_cancel (by omega)
              have h1 : (((h - 1) + 1 : ℕ) : ℝ) = (h : ℝ) := by exact_mod_cast this
              push_cast at h1; linarith
            linarith
        · -- Case 3: `1 < x < 2h`, so `y = 0` or `y = h`
          have hmax_mid : max (0 : ℝ) (min (2 * (h : ℝ) - 1) (x - 1)) = x - 1 := by
            rw [min_eq_right (by linarith), max_eq_right (by linarith)]
          dsimp [G] at hG0
          rw [hmax_mid] at hG0
          have hy_eq : y = 0 ∨ y = (h : ℝ) := by
            by_contra hne
            push Not at hne
            exact hnot_open ⟨hx1, hx2, lt_of_le_of_ne hy_0h.1 hne.1.symm,
              lt_of_le_of_ne hy_0h.2 hne.2⟩
          rcases hy_eq with rfl | rfl <;> nlinarith
    -- Now conclude `connectedComponentIn ... pb ≠ connectedComponentIn ... pd`
    intro heq
    let S_sub := frontier (fig1EnclosedSet h) \ {pa, pc}
    let C_b := connectedComponentIn S_sub pb
    have hCb_pre : IsPreconnected C_b := isPreconnected_connectedComponentIn
    have hCb_sub : C_b ⊆ S_sub := connectedComponentIn_subset _ _
    let U_pos : Set (ℝ × ℝ) := {z | 0 < G z}
    let U_neg : Set (ℝ × ℝ) := {z | G z < 0}
    have hU_pos : IsOpen U_pos := isOpen_lt continuous_const hG_cont
    have hU_neg : IsOpen U_neg := isOpen_lt hG_cont continuous_const
    have hcov : C_b ⊆ U_pos ∪ U_neg := by
      intro z hz
      rcases lt_or_gt_of_ne (hG_ne_zero z (hCb_sub hz)) with hlt | hgt
      · exact Or.inr hlt
      · exact Or.inl hgt
    have hdisj : C_b ∩ (U_pos ∩ U_neg) = ∅ := by
      ext z
      simp only [mem_inter_iff, mem_empty_iff_false, iff_false, not_and, U_pos, U_neg, mem_ofPred_eq]
      intro _ h1 h2
      linarith
    have hpb_mem : pb ∈ S_sub := by
      refine ⟨hpb_fr, ?_⟩
      rintro (h | h)
      · have := congrArg Prod.snd h; dsimp [pb, pa] at this; linarith
      · have := congrArg Prod.fst h; dsimp [pb, pc] at this; linarith
    have hpd_mem : pd ∈ S_sub := by
      refine ⟨hpd_fr, ?_⟩
      rintro (h | h)
      · have := congrArg Prod.fst h; dsimp [pd, pa] at this; linarith
      · have := congrArg Prod.snd h; dsimp [pd, pc] at this; linarith
    have hpb_Cb : pb ∈ C_b := mem_connectedComponentIn hpb_mem
    have hpd_Cb : pd ∈ C_b := by
      change pd ∈ connectedComponentIn S_sub pb
      rw [heq]
      exact mem_connectedComponentIn hpd_mem
    rcases isPreconnected_iff_subset_of_disjoint.mp hCb_pre U_pos U_neg hU_pos hU_neg hcov hdisj with hsub | hsub
    · have : 0 < G pd := hsub hpd_Cb
      linarith
    · have : G pb < 0 := hsub hpb_Cb
      linarith

/-- For an open embedding `f : ℝ × ℝ → S` into a T2 space `S` and `h ≥ 1`,
`frontier (f '' fig1EnclosedSet h) = f '' frontier (fig1EnclosedSet h)`. -/
theorem frontier_image_fig1EnclosedSet {S : Type*} [TopologicalSpace S] [T2Space S]
    (hS : IsClosedSurface S) {f : (ℝ × ℝ) → S} (hf : Topology.IsOpenEmbedding f)
    {h : ℕ} (hh : 1 ≤ h) :
    frontier (f '' fig1EnclosedSet h) = f '' frontier (fig1EnclosedSet h) := by
  have hDisc := isClosedDisc_image_fig1EnclosedSet hS hf.isEmbedding hh
  have hcl_img : closure (f '' fig1EnclosedSet h) = f '' closure (fig1EnclosedSet h) := by
    rw [hDisc.isClosed.closure_eq, (isClosed_fig1EnclosedSet h).closure_eq]
  have hint_img : interior (f '' fig1EnclosedSet h) = f '' interior (fig1EnclosedSet h) := by
    refine Subset.antisymm ?_ (interior_maximal (image_mono interior_subset)
      (hf.isOpenMap _ isOpen_interior))
    intro y hy
    obtain ⟨x, _, rfl⟩ := interior_subset hy
    refine ⟨x, ?_, rfl⟩
    have hU : f ⁻¹' interior (f '' fig1EnclosedSet h) ⊆ fig1EnclosedSet h := by
      intro z hz
      have hfz : f z ∈ f '' fig1EnclosedSet h := interior_subset hz
      obtain ⟨z', hz', hzz'⟩ := hfz
      rwa [← hf.injective hzz']
    exact interior_maximal hU (isOpen_interior.preimage hf.continuous) hy
  rw [frontier, frontier, hcl_img, hint_img, Set.image_sdiff hf.injective]

/-- Every point of `fig1EnclosedSet h` lies in `[0, 2h + 1] × [0, h]`. -/
theorem fig1EnclosedSet_subset_Icc (h : ℕ) :
    fig1EnclosedSet h ⊆ Icc (0 : ℝ) (2 * (h : ℝ) + 1) ×ˢ Icc (0 : ℝ) (h : ℝ) := by
  rintro ⟨x, y⟩ hz
  obtain ⟨k, hk_lt, ⟨hx_lo, hx_hi⟩, ⟨hy_lo, hy_hi⟩⟩ := mem_iUnion₂.mp hz
  dsimp only at hx_lo hx_hi hy_lo hy_hi
  have hk_le : (k : ℝ) + 1 ≤ (h : ℝ) := by exact_mod_cast hk_lt
  have hleft_bds := fig1RowLeft_bounds k
  have hk0 : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
  unfold fig1RowRight at hx_hi
  exact ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩

/-- For even `k` and `x ≤ 1`, `(x, k) ∉ interior (fig1EnclosedSet h)`. -/
theorem not_mem_interior_fig1EnclosedSet_of_even_le_one {h k : ℕ} (hk : Even k)
    {x : ℝ} (hx : x ≤ 1) :
    (x, (k : ℝ)) ∉ interior (fig1EnclosedSet h) := by
  intro hint
  rw [mem_interior_iff_mem_nhds, Metric.mem_nhds_iff] at hint
  obtain ⟨ε, hε, hball⟩ := hint
  let δ := min (ε / 2) (1 / 2)
  have hδ_pos : 0 < δ := lt_min (by linarith) (by norm_num)
  have hδ_le : δ ≤ 1 / 2 := min_le_right _ _
  have hδ_lt_ε : δ < ε := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  let z : ℝ × ℝ := (x - δ, (k : ℝ) + δ)
  have hz_ball : z ∈ Metric.ball (x, (k : ℝ)) ε := by
    rw [Metric.mem_ball, Prod.dist_eq]
    refine max_lt ?_ ?_
    · simp [z, abs_of_pos hδ_pos, hδ_lt_ε]
    · simp [z, abs_of_pos hδ_pos, hδ_lt_ε]
  have hbounds := row_bounds_of_mem_fig1EnclosedSet (hball hz_ball) (k := k)
    (by linarith) (by linarith)
  have hleft : fig1RowLeft k = 1 := by simp [fig1RowLeft, hk]
  linarith [hbounds.1]

/-- For odd `k` (`¬ Even k`) and `2h ≤ x`, `(x, k + 1) ∉ interior (fig1EnclosedSet h)`. -/
theorem not_mem_interior_fig1EnclosedSet_of_odd_ge_two_mul {h k : ℕ} (hk : ¬ Even k)
    {x : ℝ} (hx : 2 * (h : ℝ) ≤ x) :
    (x, (k : ℝ) + 1) ∉ interior (fig1EnclosedSet h) := by
  intro hint
  rw [mem_interior_iff_mem_nhds, Metric.mem_nhds_iff] at hint
  obtain ⟨ε, hε, hball⟩ := hint
  let δ := min (ε / 2) (1 / 2)
  have hδ_pos : 0 < δ := lt_min (by linarith) (by norm_num)
  have hδ_le : δ ≤ 1 / 2 := min_le_right _ _
  have hδ_lt_ε : δ < ε := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  let z : ℝ × ℝ := (x + δ, (k : ℝ) + 1 - δ)
  have hz_ball : z ∈ Metric.ball (x, (k : ℝ) + 1) ε := by
    rw [Metric.mem_ball, Prod.dist_eq]
    refine max_lt ?_ ?_
    · simp [z, abs_of_pos hδ_pos, hδ_lt_ε]
    · simp [z, abs_of_pos hδ_pos, hδ_lt_ε]
  have hbounds := row_bounds_of_mem_fig1EnclosedSet (hball hz_ball) (k := k)
    (by linarith) (by linarith)
  have hright : fig1RowRight h k = 2 * (h : ℝ) := by
    unfold fig1RowRight fig1RowLeft
    rw [ite_eq_right_iff.mpr fun h => (hk h).elim, add_zero]
  linarith [hbounds.2]

/-- The real plane translation `(x, y) ↦ (x + i, y + j)` as a homeomorphism of `ℝ × ℝ`. -/
def wallShiftRealHomeomorph (i j : ℕ) : (ℝ × ℝ) ≃ₜ (ℝ × ℝ) :=
  Homeomorph.addRight ((i : ℝ), (j : ℝ))

@[simp]
lemma wallShiftRealHomeomorph_apply (i j : ℕ) (z : ℝ × ℝ) :
    wallShiftRealHomeomorph i j z = (z.1 + (i : ℝ), z.2 + (j : ℝ)) :=
  rfl

/-- For `m ≥ 1`, `4m ≤ i`, and `2m ≤ j`, the shifted enclosed set of height `h` at `(i, j)` lies
strictly inside the interior of the shifted enclosed set of height `h + 4m` at
`(i - 4m, j - 2m)`. -/
theorem fig1EnclosedSet_shift_subset_interior {i j h m : ℕ}
    (hm : 1 ≤ m) (hi : 4 * m ≤ i) (hj : 2 * m ≤ j) :
    wallShiftRealHomeomorph i j '' fig1EnclosedSet h ⊆
      interior (wallShiftRealHomeomorph (i - 4 * m) (j - 2 * m) '' fig1EnclosedSet (h + 4 * m)) := by
  rw [← (wallShiftRealHomeomorph (i - 4 * m) (j - 2 * m)).image_interior]
  rintro _ ⟨⟨x, y⟩, hxy, rfl⟩
  obtain ⟨⟨hx0, hx1⟩, ⟨hy0, hy1⟩⟩ := fig1EnclosedSet_subset_Icc h hxy
  have hm_r : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hi_cast : ((i - 4 * m : ℕ) : ℝ) + 4 * (m : ℝ) = (i : ℝ) := by
    have : (i - 4 * m) + 4 * m = i := Nat.sub_add_cancel hi
    have h1 : (((i - 4 * m) + 4 * m : ℕ) : ℝ) = (i : ℝ) := by exact_mod_cast this
    push_cast at h1
    linarith
  have hj_cast : ((j - 2 * m : ℕ) : ℝ) + 2 * (m : ℝ) = (j : ℝ) := by
    have : (j - 2 * m) + 2 * m = j := Nat.sub_add_cancel hj
    have h1 : (((j - 2 * m) + 2 * m : ℕ) : ℝ) = (j : ℝ) := by exact_mod_cast this
    push_cast at h1
    linarith
  refine ⟨(x + 4 * (m : ℝ), y + 2 * (m : ℝ)), ?_, ?_⟩
  · apply open_rect_subset_interior_fig1EnclosedSet (h + 4 * m)
    push_cast
    exact ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩
  · ext <;> dsimp <;> linarith

end GraphMinor.GM13
