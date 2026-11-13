module

public import GraphMinor.LRPlanarity.Statements

/-!
# Exact Aggregation of New Fork Constraints (Part II)

This module proves `ForkAggregationStatement` from
`GraphMinor/LRPlanarity/Statements.lean`, following Part II
("Exact aggregation of new fork constraints") of
`docs/planarity/planarity_test.tex`.
-/

@[expose] public section
namespace GraphMinor.LRPlanarity

open Classical

/-- Every strict return of `e` has target depth strictly below `T.depth e.1`. -/
theorem Forest.returns_depth_lt {N : ℕ} (T : Forest N) (G : SimpleGraph (Fin N))
    (e b : Arc N) (hb : b ∈ T.returns G e) :
    T.depth b.2 < T.depth e.1 := by
  rcases hb with ⟨hbe, ⟨_, rfl⟩ | ⟨_, _, hlt⟩⟩
  · exact hbe.2.2.1
  · exact hlt

/-- The lowpoint `T.low G e` is a lower bound on the target depth of every return in `T.returns G e`. -/
theorem Forest.low_le_depth_of_mem_returns {N : ℕ} (T : Forest N) (G : SimpleGraph (Fin N))
    (e b : Arc N) (hb : b ∈ T.returns G e) :
    T.low G e ≤ T.depth b.2 := by
  unfold Forest.low
  apply Finset.min'_le
  refine Finset.mem_insert.mpr (Or.inr ?_)
  exact Finset.mem_image.mpr ⟨b, Finset.mem_filter.mpr ⟨Finset.mem_univ b, hb⟩, rfl⟩

/-- When `T.returns G e` is nonempty, its lowpoint `T.low G e` is achieved by some return in `T.returns G e`. -/
theorem Forest.exists_mem_returns_depth_eq_low {N : ℕ} (T : Forest N) (G : SimpleGraph (Fin N))
    (e : Arc N) (hne : (T.returns G e).Nonempty) :
    ∃ b ∈ T.returns G e, T.depth b.2 = T.low G e := by
  obtain ⟨b₁, hb₁⟩ := hne
  have hlow_lt : T.low G e < T.depth e.1 :=
    lt_of_le_of_lt (T.low_le_depth_of_mem_returns G e b₁ hb₁) (T.returns_depth_lt G e b₁ hb₁)
  have hmem : T.low G e ∈ insert (T.depth e.1)
      ((Finset.univ.filter (fun b => b ∈ T.returns G e)).image (fun b => T.depth b.2)) := by
    unfold Forest.low
    exact Finset.min'_mem _ _
  rcases Finset.mem_insert.mp hmem with heq | hmem_img
  · omega
  · obtain ⟨b₀, hb₀, hd₀⟩ := Finset.mem_image.mp hmem_img
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hb₀
    exact ⟨b₀, hb₀, hd₀⟩

/-- Ordering by `T.key` implies ordering by `T.low`. -/
theorem Forest.low_le_of_key_le {N : ℕ} (T : Forest N) (G : SimpleGraph (Fin N))
    (e f : Arc N) (hkey : T.key G e ≤ T.key G f) :
    T.low G e ≤ T.low G f := by
  unfold Forest.key at hkey
  have he : (T.thick G e).toNat ≤ 1 := Bool.toNat_le _
  have hf : (T.thick G f).toNat ≤ 1 := Bool.toNat_le _
  omega

/-- At equal lowpoints, ordering by `T.key` preserves the `thick` bit. -/
theorem Forest.thick_of_key_le_of_low_eq {N : ℕ} (T : Forest N) (G : SimpleGraph (Fin N))
    (e f : Arc N) (hkey : T.key G e ≤ T.key G f) (hlow : T.low G e = T.low G f)
    (hthick : T.thick G e = true) :
    T.thick G f = true := by
  unfold Forest.key at hkey
  rw [hlow, hthick] at hkey
  cases hf : T.thick G f
  · rw [hf] at hkey
    simp at hkey
  · rfl

/-- If `T.low G f₁ ≤ T.low G f₂`, then `T.forkSet G e f₂ ⊆ T.forkSet G e f₁`. -/
theorem Forest.forkSet_mono_right {N : ℕ} (T : Forest N) (G : SimpleGraph (Fin N))
    (e f₁ f₂ : Arc N) (hlow : T.low G f₁ ≤ T.low G f₂) :
    T.forkSet G e f₂ ⊆ T.forkSet G e f₁ := by
  rintro b ⟨hb, hlt⟩
  exact ⟨hb, lt_of_le_of_lt hlow hlt⟩

/-- Part II ("Exact aggregation of new fork constraints"): "If M_j is nonempty, then N_j is
nonempty. Indeed, if low(e_j)<b, every return of e_i belongs to N_j. If low(e_j)=b, then a
nonempty M_j means that e_j is chordal, and the order forces e_i to be chordal too, so e_i has a
return strictly above b." -/
theorem Forest.forkSet_new_nonempty_of_forkSet_old_nonempty {N : ℕ}
    (T : Forest N) (G : SimpleGraph (Fin N)) (e new : Arc N)
    (hkey : T.key G e ≤ T.key G new)
    (hne_e : (T.returns G e).Nonempty) (hne_new : (T.returns G new).Nonempty)
    (hm : (T.forkSet G e new).Nonempty) :
    (T.forkSet G new e).Nonempty := by
  have hlow_le : T.low G e ≤ T.low G new := T.low_le_of_key_le G e new hkey
  rcases lt_or_eq_of_le hlow_le with hlow_lt | hlow_eq
  · obtain ⟨b, hb⟩ := hne_new
    exact ⟨b, hb, lt_of_lt_of_le hlow_lt (T.low_le_depth_of_mem_returns G new b hb)⟩
  · obtain ⟨c, hc_ret, hc_gt⟩ := hm
    obtain ⟨c₀, hc₀_ret, hc₀_eq⟩ := T.exists_mem_returns_depth_eq_low G e hne_e
    have hthick_e : T.thick G e = true := by
      unfold Forest.thick
      rw [@decide_eq_true_eq _ (Classical.propDecidable _)]
      refine ⟨c₀, hc₀_ret, c, hc_ret, ?_⟩
      omega
    have hthick_new : T.thick G new = true :=
      T.thick_of_key_le_of_low_eq G e new hkey hlow_eq hthick_e
    unfold Forest.thick at hthick_new
    rw [@decide_eq_true_eq _ (Classical.propDecidable _)] at hthick_new
    obtain ⟨b₁, hb₁, b₂, hb₂, hne_d⟩ := hthick_new
    have hd₁ : T.low G new ≤ T.depth b₁.2 := T.low_le_depth_of_mem_returns G new b₁ hb₁
    have hd₂ : T.low G new ≤ T.depth b₂.2 := T.low_le_depth_of_mem_returns G new b₂ hb₂
    rcases lt_or_gt_of_ne hne_d with hlt | hlt
    · exact ⟨b₂, hb₂, by omega⟩
    · exact ⟨b₁, hb₁, by omega⟩

theorem Color.eq_of_ne_of_ne {c c₁ c₂ : Color} (h1 : c ≠ c₁) (h2 : c ≠ c₂) : c₁ = c₂ := by
  cases c <;> cases c₁ <;> cases c₂ <;> first | rfl | contradiction

/-- Part II, exact aggregation of new fork constraints: in key order, all new
primitive constraints reduce to two monochromatic classes with opposite colors. -/
theorem forkAggregationStatement : ForkAggregationStatement := by
  intro N G T _ color v first rest new branches _hnodup hbranches hpair B U
  have hpair_cons : (first :: (rest ++ [new])).Pairwise (fun e f => T.key G e ≤ T.key G f) :=
    hpair
  rw [List.pairwise_cons] at hpair_cons
  have hfirst_key : ∀ e ∈ first :: rest, T.key G first ≤ T.key G e := by
    intro e he
    rcases List.mem_cons.mp he with rfl | he_rest
    · exact le_rfl
    · exact hpair_cons.1 e (List.mem_append_left [new] he_rest)
  have hnew_key : ∀ e ∈ first :: rest, T.key G e ≤ T.key G new := by
    intro e he
    have hp_app : ((first :: rest) ++ [new]).Pairwise (fun e f => T.key G e ≤ T.key G f) := hpair
    rw [List.pairwise_append] at hp_app
    exact hp_app.2.2 e he new (List.mem_singleton_self new)
  have hne_new : (T.returns G new).Nonempty :=
    (hbranches new (by simp [branches])).2
  have hne_old : ∀ e ∈ first :: rest, (T.returns G e).Nonempty := by
    intro e he
    exact (hbranches e (List.mem_append_left [new] he)).2
  have hN_sub_B : ∀ e ∈ first :: rest, T.forkSet G new e ⊆ B := by
    intro e he
    exact T.forkSet_mono_right G new first e (T.low_le_of_key_le G first e (hfirst_key e he))
  have hM_sub_U : ∀ e ∈ first :: rest, T.forkSet G e new ⊆ U := by
    intro e he b hb
    exact ⟨e, he, hb.1, hb.2⟩
  have hN_nonempty : ∀ e ∈ first :: rest,
      (T.forkSet G e new).Nonempty → (T.forkSet G new e).Nonempty := by
    intro e he hm
    exact T.forkSet_new_nonempty_of_forkSet_old_nonempty G e new
      (hnew_key e he) (hne_old e he) hne_new hm
  have hU_imp_B : U.Nonempty → B.Nonempty := by
    rintro ⟨c, e, he, hc_ret, hc_gt⟩
    obtain ⟨b, hb⟩ := hN_nonempty e he ⟨c, hc_ret, hc_gt⟩
    exact ⟨b, hN_sub_B e he hb⟩
  refine ⟨⟨?_, ?_⟩, hU_imp_B⟩
  · intro hforks
    have hB_mono : Monochromatic color B :=
      (hforks first List.mem_cons_self).2.1
    have hBU_opp : ∀ b ∈ B, ∀ c ∈ U, color b ≠ color c := by
      rintro b hb c ⟨e, he, hc_ret, hc_gt⟩
      have hc_M : c ∈ T.forkSet G e new := ⟨hc_ret, hc_gt⟩
      obtain ⟨b₀, hb₀⟩ := hN_nonempty e he ⟨c, hc_M⟩
      have hb₀_B : b₀ ∈ B := hN_sub_B e he hb₀
      have hbb₀ : color b = color b₀ := hB_mono b hb b₀ hb₀_B
      have hcb₀ : color c ≠ color b₀ := (hforks e he).2.2 c hc_M b₀ hb₀
      rw [hbb₀]
      exact Ne.symm hcb₀
    have hU_mono : Monochromatic color U := by
      intro c₁ hc₁ c₂ hc₂
      obtain ⟨b, hb⟩ := hU_imp_B ⟨c₁, hc₁⟩
      exact Color.eq_of_ne_of_ne (hBU_opp b hb c₁ hc₁) (hBU_opp b hb c₂ hc₂)
    exact ⟨hB_mono, hU_mono, hBU_opp⟩
  · rintro ⟨hB_mono, hU_mono, hBU_opp⟩ e he
    refine ⟨?_, ?_, ?_⟩
    · intro c₁ hc₁ c₂ hc₂
      exact hU_mono c₁ (hM_sub_U e he hc₁) c₂ (hM_sub_U e he hc₂)
    · intro b₁ hb₁ b₂ hb₂
      exact hB_mono b₁ (hN_sub_B e he hb₁) b₂ (hN_sub_B e he hb₂)
    · intro c hc b hb
      exact Ne.symm (hBU_opp b (hN_sub_B e he hb) c (hM_sub_U e he hc))

end GraphMinor.LRPlanarity
