module

public import GraphMinor.Compute.SpecsCrossingReduction
import GraphMinor.Compute.CrossingTopCoreProved

/-! The proved crossing extractor supplies the program used in the reduction
to Shiloach's two-paths specification. -/

public section
namespace GraphMinor.Compute.Crossing
open SimpleGraph GraphMinor.HP25 GraphMinor.Compute.TwoPaths

/-- **Shiloach's statement from the crossing extractor.** -/
theorem shiloach80Statement_of_crossingExtractor :
    Shiloach80Statement := by
  obtain ⟨P, C, c_w, hC, hcw, hP⟩ := crossingExtractor_of 51 52 53 43 45 46 200 40 170 200
    ⟨by decide, by simp⟩ (by decide) (by decide) (by decide)
  refine ⟨redProg P, 5 * C + 2000, 8 * c_w + 200, by omega, by omega, ?_⟩
  intro N G _ lists s₁ t₁ s₂ t₂ h₁ h₂ h₃ h₄ h₅ h₆ w hw s hadj hent h30 h31 h32 h33 h34
  set M := G.edgeFinset.card with hM
  set K₀ := (N + 1) * (M + N + 1) with hK₀
  have hNK : N + 1 ≤ K₀ := Nat.le_mul_of_pos_right _ (by omega)
  have hMK : M + N + 1 ≤ K₀ := Nat.le_mul_of_pos_left _ (by omega)
  have hNNK : N * N ≤ K₀ := Nat.mul_le_mul (by omega) (by omega)
  have hbig : ∀ V, V ≤ 100 * (K₀ + 1) → V < 2 ^ w := fun V hV =>
    lt_two_pow_of_le_mul hV ((wordSize_mono_left (by omega) _).trans hw)
  have hw1 : 1 < 2 ^ w := hbig 1 (by omega)
  have hN : N < 2 ^ w := hbig N (by omega)
  have hn4 : 4 * N + 4 < 2 ^ w := hbig _ (by omega)
  have hNN : N * N < 2 ^ w := hbig _ (by omega)
  have htot : totalAdjEntries lists = 2 * M := totalAdjEntries_eq_two_mul_card_edgeFinset hadj.2
  -- 1. `N` into register `40`.
  set u₂ := s.setReg 40 N with hu₂
  have hx₂ : Exec w (.assign 40 (.reg 30)) s u₂ (1 + 1) := .assign (reg_eval h30 hN)
  -- 2. The set of all vertices.
  obtain ⟨u₃, t₃, hx₃, ht₃, hY₃, ha₃, hr₃⟩ := initUnivBitSetProg_exec (n := N) aY 40 149
    (by decide) hw1 hN (s := u₂) (by simp [u₂])
  have h40₃ : u₃.regs 40 = N := by rw [hr₃ 40 (by decide)]; simp [u₂]
  -- 3. The capacity `N²`.
  set u₄ := u₃.setReg 148 (N * N) with hu₄
  have hx₄ : Exec w (.assign 148 (.op .mul (.reg 40) (.reg 40))) u₃ u₄ (1 + 1 + 1 + 1) :=
    .assign (op_eval (reg_eval h40₃ hN) (reg_eval h40₃ hN)
      (by simp [BinOp.eval, BinOp.raw, checkWord, hNN]))
  have hr₄ : ∀ r : ℕ, r ≠ 148 → r ≠ 149 → r ≠ 40 → u₄.regs r = s.regs r := fun r h1 h2 h3 => by
    rw [hu₄, State.setReg_regs_ne _ _ h1, hr₃ r h2, hu₂, State.setReg_regs_ne _ _ h3]
  have ha₄ : ∀ x : ℕ, x ≠ aY → u₄.arrs x = s.arrs x := fun x hx => by
    rw [hu₄, State.setReg_arrs, ha₃ x hx]; rfl
  have hadj₄ : IsAdjList G 30 31 32 lists u₄ :=
    hadj.of_arrs_eq (ha₄ 30 (by decide)) (ha₄ 31 (by decide)) (ha₄ 32 (by decide))
  -- 4. The lists of `G` in `40`–`42`.
  have hcapb : 2 * (edgesInSet G Finset.univ).card ≤ N * N := by
    rw [← totalAdjEntries_restrictListFamily hadj.2 Finset.univ]
    have hfam := isAdjListFamily_restrictListFamily hadj.2 Finset.univ
    unfold totalAdjEntries
    have := Finset.sum_le_card_nsmul Finset.univ
      (fun u => (restrictListFamily Finset.univ lists u).length) N (fun u _ => (hfam u).2.2.1)
    simpa using this
  obtain ⟨u₅, t₅, hx₅, ht₅, hadj₅, hlen₅, -, ha₅, hr₅⟩ := restrictGraphProg_exec G lists
    Finset.univ (N * N) 30 31 32 aY 40 41 42 40 148 141 142 143 144 145 146 147
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) hw1 hN hNN hcapb (s := u₄) hadj₄
    (by rw [ha₄ 32 (by decide)]; exact hent)
    (hY₃.of_arr_eq (by simp [u₄])) (by rw [hu₄, State.setReg_regs_ne _ _ (by decide)]; exact h40₃)
    (by simp [u₄])
  rw [restrictGraph_univ] at hadj₅
  set L₁ := restrictListFamily Finset.univ lists with hL₁
  have htot₁ : totalAdjEntries L₁ = 2 * M := totalAdjEntries_eq_two_mul_card_edgeFinset hadj₅.2
  have hr₅' : ∀ r : ℕ, r < 141 → r ≠ 40 → u₅.regs r = s.regs r := fun r hr h40 => by
    rw [hr₅ r (by rintro rfl; exact absurd hr (by decide)) (by rintro rfl; exact absurd hr (by decide)) (by rintro rfl; exact absurd hr (by decide)) (by rintro rfl; exact absurd hr (by decide)) (by rintro rfl; exact absurd hr (by decide)) (by rintro rfl; exact absurd hr (by decide)) (by rintro rfl; exact absurd hr (by decide)),
      hr₄ r (by rintro rfl; exact absurd hr (by decide)) (by rintro rfl; exact absurd hr (by decide)) h40]
  have h40₅ : u₅.regs 40 = N := by
    rw [hr₅ 40 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide), hu₄, State.setReg_regs_ne _ _ (by decide)]; exact h40₃
  -- 5. The new edges of the frame.
  obtain ⟨F₀, hF₀⟩ : ∃ F, F = pairsList (newFramePairs G s₁ s₂ t₁ t₂) := ⟨_, rfl⟩
  have hF8 : F₀.length ≤ 8 := by
    rw [hF₀, length_pairsList]
    have : (newFramePairs G s₁ s₂ t₁ t₂).length ≤ 4 := by
      simp only [newFramePairs]
      exact (List.length_filter_le _ _).trans (by simp [framePairs])
    omega
  obtain ⟨u₆, t₆, hx₆, ht₆, hk₆, hF₆⟩ := frameEdgesProg_exec hw1 hn4 hadj₅
    (by rw [hlen₅]; exact hNN) s₁ t₁ s₂ t₂ (by rw [hr₅' 31 (by decide) (by decide)]; exact h31)
    (by rw [hr₅' 32 (by decide) (by decide)]; exact h32)
    (by rw [hr₅' 33 (by decide) (by decide)]; exact h33)
    (by rw [hr₅' 34 (by decide) (by decide)]; exact h34)
  rw [← hF₀] at hF₆
  have hadj₆ : IsAdjList G aStart aEnd aEnt L₁ u₆ :=
    hadj₅.of_arrs_eq (hk₆.2 _ (by decide)) (hk₆.2 _ (by decide)) (hk₆.2 _ (by decide))
  have hent₆ : (u₆.arrs aEnt).length = N * N := by rw [hk₆.2 _ (by decide)]; exact hlen₅
  have h40₆ : u₆.regs 40 = N := by
    rw [hk₆.1 40 (by simp [frameEdgesRegs])]; exact h40₅
  -- 6. The lists of `G` plus the frame in `51`–`53`.
  have hnew : IsNewEdgeList G [s₁, s₂, t₁, t₂] (u₆.arrs aF) := by
    rw [hF₆, hF₀]; exact isNewEdgeList_frame h₁ h₂ h₃ h₄ h₅ h₆
  obtain ⟨u₇, t₇, hx₇, ht₇, hk₇, hadj₇, hlen₇⟩ := unionProg_exec hadj₆ hnew h40₆ hn4
    (by rw [hent₆]; exact hNN) (by rw [hF₆]; omega) (by rw [hF₆, htot₁]; exact hbig _ (by
      have : N * F₀.length ≤ N * 8 := Nat.mul_le_mul_left _ hF8
      omega))
  rw [hF₆] at ht₇ hadj₇ hlen₇
  rw [htot₁] at ht₇ hlen₇
  have hGeq : G ⊔ pairGraph N F₀ = G ⊔ frameGraph s₁ s₂ t₁ t₂ := by
    rw [hF₀, sup_pairGraph_frame]
  rw [hGeq] at hadj₇
  set G' := G ⊔ frameGraph s₁ s₂ t₁ t₂ with hG'
  -- 7. The cycle.
  have hreg₇ : ∀ r : ℕ, r < 40 → u₇.regs r = s.regs r := fun r hr => by
    rw [hk₇.1 r (notMem_of_lt (b := 40) (by decide) hr),
      hk₆.1 r (notMem_of_lt (b := 40) (by decide) hr), hr₅' r (by omega) (by rintro rfl; omega)]
  have hv : ∀ v : Fin N, v.1 < 2 ^ w := fun v => by have := v.2; omega
  set c₀ := u₇.setArr aCyc (List.replicate 4 0) with hc₀
  set c₁ := c₀.writeArr aCyc 0 s₁.1 with hc₁'
  set c₂ := c₁.writeArr aCyc 1 s₂.1 with hc₂'
  set c₃ := c₂.writeArr aCyc 2 t₁.1 with hc₃'
  set c₄ := c₃.writeArr aCyc 3 t₂.1 with hc₄'
  have hcyc : Exec w cycWrite u₇ c₄ ((1 + 4) + ((1 + 1 + 1) + ((1 + 1 + 1) + ((1 + 1 + 1) +
      (1 + 1 + 1))))) :=
    .seq (.alloc (const_eval' (by omega)))
      (.seq (.write (const_eval' (by omega)) (reg_eval (by simp [c₀, hreg₇ 31 (by omega), h31])
        (hv s₁)) (by simp [c₀]))
      (.seq (.write (const_eval' (by omega)) (reg_eval (by simp [c₁, c₀, hreg₇ 33 (by omega), h33])
        (hv s₂)) (by simp [c₁, c₀]))
      (.seq (.write (const_eval' (by omega)) (reg_eval (by simp [c₂, c₁, c₀,
        hreg₇ 32 (by omega), h32]) (hv t₁)) (by simp [c₂, c₁, c₀]))
      (.write (const_eval' (by omega)) (reg_eval (by simp [c₃, c₂, c₁, c₀,
        hreg₇ 34 (by omega), h34]) (hv t₂)) (by simp [c₃, c₂, c₁, c₀])))))
  have hcyc₄ : c₄.arrs aCyc = [s₁, s₂, t₁, t₂].map Fin.val := by
    simp [c₄, c₃, c₂, c₁, c₀, List.replicate_succ]
  have hcl₄ : ∀ x : ℕ, x ≠ aCyc → c₄.arrs x = u₇.arrs x := fun x hx => by
    simp [c₄, c₃, c₂, c₁, c₀, State.writeArr_arrs_ne _ _ _ hx, State.setArr_arrs_ne _ _ hx]
  have hcr₄ : c₄.regs = u₇.regs := rfl
  -- 8. The extractor.
  let _ : DecidableRel G'.Adj := Classical.decRel _
  have hE' : 2 * G'.edgeSet.ncard ≤ 2 * M + N * F₀.length := by
    have h := totalAdjEntries_eq_two_mul_card_edgeFinset (G := G') hadj₇.2
    have : totalAdjEntries (unionList L₁ F₀) ≤ totalAdjEntries L₁ + N * F₀.length := by
      have := sum_unionList_le L₁ F₀
      rwa [pre_n] at this
    rw [ncard_edgeSet_eq, ← h]
    omega
  have hNF : N * F₀.length ≤ N * 8 := Nat.mul_le_mul_left _ hF8
  have hE'K : G'.edgeSet.ncard + N + 1 ≤ 5 * (M + N + 1) := by omega
  have hP5 : (N + 1) * (G'.edgeSet.ncard + N + 1) ≤ 5 * K₀ := by
    rw [hK₀, Nat.mul_left_comm]; exact Nat.mul_le_mul_left _ hE'K
  have hwP : wordSize c_w ((N + 1) * (G'.edgeSet.ncard + N + 1)) ≤ w :=
    (wordSize_le_of_le_mul' (K := 5) (by omega)).trans
      ((wordSize_mono_left (by omega) _).trans hw)
  obtain ⟨sP, tP, hxP, htP, hkP, hout⟩ := hP N G' (unionList L₁ F₀) [s₁, s₂, t₁, t₂] w c₄ hwP
    (hadj₇.of_arrs_eq (by rw [hcl₄ _ (by decide)]) (by rw [hcl₄ _ (by decide)])
      (by rw [hcl₄ _ (by decide)]))
    (by rw [hcl₄ _ (by decide), hlen₇]; exact hbig _ (by omega))
    (by rw [hcr₄, hk₇.1 40 (by simp [uRegs])]; exact h40₆) hcyc₄
    (frame_isCycleList h₁ h₂ h₃ h₄ h₅ h₆)
  -- 9. The output.
  have hlowP : ∀ r : ℕ, r < 30 → sP.regs r = s.regs r := fun r hr => by
    rw [hkP.1 r (by omega) (notMem_of_lt (b := 170) (by decide) (by omega)), hcr₄,
      hreg₇ r (by omega)]
  have hlowPa : ∀ x : ℕ, x < 33 → sP.arrs x = s.arrs x := fun x hx => by
    rw [hkP.2 x (by omega) (notMem_of_lt (b := 45) (by decide) (by omega)),
      hcl₄ x (by rintro rfl; exact absurd hx (by decide)), hk₇.2 x (notMem_of_lt (b := 51) (by decide) (by omega)),
      hk₆.2 x (notMem_of_lt (b := 47) (by decide) (by omega)),
      ha₅ x (by rintro rfl; omega) (by rintro rfl; omega) (by rintro rfl; omega),
      ha₄ x (by rintro rfl; exact absurd hx (by decide))]
  have hlen_le : ∀ {a b : Fin N} (Q : G'.Walk a b), Q.IsPath → Q.support.length ≤ N := by
    intro a b Q hQ
    simpa using hQ.support_nodup.length_le_card
  rcases hout with ⟨h1, a, b, c, d, Q, R, hcr, hQ, hR⟩ | ⟨h0, hnc⟩
  · -- The answer `1`.
    obtain ⟨P₁, P₂, hP₁, hP₂, hd, hs₁, hs₂⟩ := exists_paths_of_isCrossing h₁ h₂ h₃ h₄ h₅ hcr
    have hQl := hlen_le Q hcr.2.1.1
    have hRl := hlen_le R hcr.2.2.1.1
    set o₁ := sP.setReg 35 1 with ho₁
    have hxo₁ : Exec w (.assign 35 (.reg 170)) sP o₁ (1 + 1) := .assign (reg_eval h1 hw1)
    have hvals : ∀ (L : List (Fin N)), ∀ x ∈ L.map Fin.val, x < 2 ^ w := fun L x hx => by
      obtain ⟨v, -, rfl⟩ := List.mem_map.1 hx; exact hv v
    obtain ⟨o₂, t₈, hx₈, ht₈, hk₈, hd₈⟩ := copyProg_exec (dst := 33) (src := 45) (by decide)
      (Q.support.map Fin.val) o₁ hw1 (by rw [List.length_map]; omega) (hvals _) (by rw [ho₁]; exact hQ)
    obtain ⟨o₃, t₉, hx₉, ht₉, hk₉, hd₉⟩ := copyProg_exec (dst := 34) (src := 46) (by decide)
      (R.support.map Fin.val) o₂ hw1 (by rw [List.length_map]; omega) (hvals _)
      (by rw [hk₈.2 46 (by simp), ho₁]; exact hR)
    have hcond : (Expr.op .eq (.reg 170) (.const 1)).eval w o₁ = some 1 := by
      simp [Expr.eval, ho₁, h1, BinOp.eval, BinOp.raw, checkWord, hw1]
    have hxout : Exec w redOutProg sP o₃ ((1 + 1) + ((Expr.op .eq (.reg 170) (.const 1)).cost +
        (t₈ + t₉))) :=
      .seq hxo₁ (.ite_true hcond (by decide) (.seq hx₈ hx₉))
    refine ⟨o₃, _, Exec.seq hx₂ (Exec.seq hx₃ (Exec.seq hx₄ (Exec.seq hx₅ (Exec.seq hx₆
      (Exec.seq hx₇ (Exec.seq hcyc (Exec.seq hxP hxout))))))), ?_, ?_, ?_, Or.inl ⟨?_, P₁, P₂,
      hP₁, hP₂, hd, ?_, ?_⟩⟩
    · have hCt : C * (N + 1) * (G'.edgeSet.ncard + N + 1) ≤ 5 * (C * K₀) :=
        calc C * (N + 1) * (G'.edgeSet.ncard + N + 1)
            = C * ((N + 1) * (G'.edgeSet.ncard + N + 1)) := by ring
          _ ≤ C * (5 * K₀) := Nat.mul_le_mul_left _ hP5
          _ = 5 * (C * K₀) := by ring
      have hK : (5 * C + 2000) * (N + 1) * (M + N + 1) = 5 * (C * K₀) + 2000 * K₀ := by
        rw [hK₀]; ring
      rw [htot] at ht₅
      try simp only [List.length_map] at *
      rw [hK]
      simp only [Expr.cost]
      omega
    · intro r hr
      have hr' : (r : ℕ) < 30 := hr
      rw [hk₉.1 r (notMem_of_lt (b := 98) (by decide) (lt_of_lt_of_le hr' (by decide))),
        hk₈.1 r (notMem_of_lt (b := 98) (by decide) (lt_of_lt_of_le hr' (by decide))), ho₁,
        State.setReg_regs_ne _ _ (by rintro rfl; exact absurd hr' (by decide)), hlowP r hr']
    · intro x hx
      have hx' : (x : ℕ) < 33 := hx
      rw [hk₉.2 x (notMem_of_lt (b := 34) (by decide) (lt_of_lt_of_le hx' (by decide))),
        hk₈.2 x (notMem_of_lt (b := 33) (by decide) hx'), ho₁, State.setReg_arrs,
        hlowPa x hx']
    · rw [hk₉.1 35 (by decide), hk₈.1 35 (by decide), ho₁]; simp
    · rw [hk₉.2 33 (by simp), hd₈, ← hs₁]; simp
    · rw [hd₉, ← hs₂]; simp
  · -- The answer `0`.
    set o₁ := sP.setReg 35 0 with ho₁
    have hxo₁ : Exec w (.assign 35 (.reg 170)) sP o₁ (1 + 1) := .assign (reg_eval h0 (by omega))
    have hcond : (Expr.op .eq (.reg 170) (.const 1)).eval w o₁ = some 0 := by
      simp [Expr.eval, ho₁, h0, BinOp.eval, BinOp.raw, checkWord, hw1]
    have hxout : Exec w redOutProg sP o₁ ((1 + 1) + ((Expr.op .eq (.reg 170) (.const 1)).cost +
        1)) :=
      .seq hxo₁ (.ite_false hcond (.skip o₁))
    refine ⟨o₁, _, Exec.seq hx₂ (Exec.seq hx₃ (Exec.seq hx₄ (Exec.seq hx₅ (Exec.seq hx₆
      (Exec.seq hx₇ (Exec.seq hcyc (Exec.seq hxP hxout))))))), ?_, ?_, ?_, Or.inr ⟨?_, ?_⟩⟩
    · have hCt : C * (N + 1) * (G'.edgeSet.ncard + N + 1) ≤ 5 * (C * K₀) :=
        calc C * (N + 1) * (G'.edgeSet.ncard + N + 1)
            = C * ((N + 1) * (G'.edgeSet.ncard + N + 1)) := by ring
          _ ≤ C * (5 * K₀) := Nat.mul_le_mul_left _ hP5
          _ = 5 * (C * K₀) := by ring
      have hK : (5 * C + 2000) * (N + 1) * (M + N + 1) = 5 * (C * K₀) + 2000 * K₀ := by
        rw [hK₀]; ring
      rw [htot] at ht₅
      try simp only [List.length_map] at *
      rw [hK]
      simp only [Expr.cost]
      omega
    · intro r hr
      have hr' : (r : ℕ) < 30 := hr
      rw [ho₁, State.setReg_regs_ne _ _ (by rintro rfl; exact absurd hr' (by decide)), hlowP r hr']
    · intro x hx
      have hx' : (x : ℕ) < 33 := hx
      rw [ho₁, State.setReg_arrs, hlowPa x hx']
    · simp [ho₁]
    · intro P₁ P₂ hP₁ hP₂ hd
      exact hnc ⟨_, _, _, _, _, _, isCrossing_of_paths hP₁ hP₂ hd⟩

end GraphMinor.Compute.Crossing
