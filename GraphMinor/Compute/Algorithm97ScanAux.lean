module

public import GraphMinor.Compute.Algorithm97Aux

/-!
# Graph Minors XIII, Algorithm (9.7): Dividing Subwall Scan with Shiloach's Two-Paths Algorithm

This module implements and verifies Step (3) of **Algorithm (9.7)** (`alg97ScanSubwallsProg`):
1. `testDisjointBitSetsProg`: tests whether two `Finset (Fin n)` bitsets are disjoint in $O(n)$
   time.
2. `appendLenPrefixedArrProg`: appends `(s.arrs a_src).length :: s.arrs a_src` to `a_dst` in
   $O(|a_{\mathrm{dst}}| + |a_{\mathrm{src}}|)$ time.
3. `alg97ScanSubwallsProg`: iterates over the `t` canonical subwalls `W_sub a` (`a : Fin t`); for
   each dividing subwall `a ∈ I`, computes its compass in `G' = (G \ X) ∪ W`, restricts `G'` to
   `(W_sub a).compassFinset`, and runs Shiloach's two-paths algorithm (`shiloachProg`) on the four
   corners `(c0, c2)` and `(c1, c3)` to either collect a crossed subwall in `arr 24` or (when
   disjoint from `X`) collect a flat subwall in `arr 25`.
4. Proves the pigeonhole counting lemma showing that after scanning all `t` subwalls, either `k₂`
   crossed subwalls have been collected in `arr 24` or `s` flat subwalls disjoint from `X` have
   been collected in `arr 25`.
-/

@[expose] public section

namespace GraphMinor.Compute

open SimpleGraph Classical

/-! ### Section 1: Testing Disjointness of Two Bitsets (`testDisjointBitSetsProg`) -/

/-- Inner loop body for `testDisjointBitSetsProg`: reads `a_A[r_u]` and `a_B[r_u]`; if both are
nonzero, sets `r_res := 0`. -/
def testDisjointBitSetsStep (a_A a_B : Arr) (r_u r_a r_b r_res : Reg) : Cmd :=
  .seq (.assign r_a (.read a_A (.reg r_u)))
    (.seq (.assign r_b (.read a_B (.reg r_u)))
      (.ite (.op .mul (.reg r_a) (.reg r_b))
        (.assign r_res (.const 0))
        .skip))

/-- Test whether `IsBitSet A a_A` and `IsBitSet B a_B` are disjoint on `Fin n` (`n = s.regs r_n`),
setting `s'.regs r_res = if Disjoint A B then 1 else 0` in $O(n)$ steps. -/
def testDisjointBitSetsProg (a_A a_B : Arr) (r_n r_u r_a r_b r_res : Reg) : Cmd :=
  .seq (.assign r_res (.const 1))
    (.seq (.assign r_u (.const 0))
      (forUp r_u (.reg r_n) (testDisjointBitSetsStep a_A a_B r_u r_a r_b r_res)))

/-- Concrete instantiation of `testDisjointBitSetsProg` for `(9.7)`:
tests `Disjoint (W_sub a).vertexFinset X` with `IsBitSet (W_sub a).vertexFinset 27` and
`IsBitSet X 17`, `reg 1 = n`, scratch registers `3, 4, 5`, and output in `reg 10`. -/
def testDisjointInstProg : Cmd :=
  testDisjointBitSetsProg 27 17 1 3 4 5 10

theorem testDisjointInstProg_exec {w n : ℕ} (A B : Finset (Fin n))
    (hw1 : 1 < 2 ^ w) (hn_w : n < 2 ^ w)
    {s : State}
    (hA : IsBitSet A 27 s)
    (hB : IsBitSet B 17 s)
    (hr1 : s.regs 1 = n) :
    ∃ s' t,
      Exec w testDisjointInstProg s s' t ∧
      t ≤ 7 + 19 * n ∧
      s'.regs 10 = (if Disjoint A B then 1 else 0) ∧
      (∀ a : Arr, s'.arrs a = s.arrs a) ∧
      (∀ r : ℕ, (r < 3 ∨ 5 < r) → r ≠ 10 → s'.regs r = s.regs r) := by
  have h0_w : 0 < 2 ^ w := by omega
  let s₁ := s.setReg 10 1
  have hex₁ : Exec w (.assign 10 (.const 1)) s s₁ 2 :=
    .assign (by simp [Expr.eval, checkWord, hw1])
  let s₂ := s₁.setReg 3 0
  have hex₂ : Exec w (.assign 3 (.const 0)) s₁ s₂ 2 :=
    .assign (by simp [Expr.eval, checkWord, h0_w])
  let prefixDisj (i : ℕ) : Prop :=
    ∀ u : Fin n, u.1 < i → ¬ (u ∈ A ∧ u ∈ B)
  let Inv (i : ℕ) (st : State) : Prop :=
    st.regs 1 = n ∧
    st.regs 3 = i ∧
    st.regs 10 = (if prefixDisj i then 1 else 0) ∧
    IsBitSet A 27 st ∧
    IsBitSet B 17 st ∧
    (∀ a : Arr, st.arrs a = s.arrs a) ∧
    (∀ r : ℕ, (r < 3 ∨ 5 < r) → r ≠ 10 → st.regs r = s.regs r)
  have hloop :
      ⦃Inv 0⦄[w]
        forUp 3 (.reg 1) (testDisjointBitSetsStep 27 17 3 4 5 10)
      ⦃Inv n⦄ ≤
        fun _ => ((Expr.reg 1).cost + 2) + n * ((Expr.reg 1).cost + 6 + 12) := by
    apply Triple.forUp_const Inv n 12 hw1 hn_w
    · intro i _ st ⟨hr1_i, hr3_i, _⟩
      exact ⟨hr3_i, by rw [Expr.eval, hr1_i]; simp [checkWord, hn_w]⟩
    · intro i hi st ⟨hr1_i, hr3_i, hr10_i, hA_i, hB_i, harr_i, hreg_i⟩
      have hi_w : i < 2 ^ w := by omega
      let u : Fin n := ⟨i, hi⟩
      obtain ⟨hA_len, hA_le, hA_mem⟩ := hA_i
      obtain ⟨hB_len, hB_le, hB_mem⟩ := hB_i
      have hu_A : i < (st.arrs 27).length := by rw [hA_len]; exact hi
      have hu_B : i < (st.arrs 17).length := by rw [hB_len]; exact hi
      let a_val := (st.arrs 27)[i]'hu_A
      let b_val := (st.arrs 17)[i]'hu_B
      have ha_le : a_val ≤ 1 := hA_le u
      have hb_le : b_val ≤ 1 := hB_le u
      have ha_w : a_val < 2 ^ w := by omega
      have hb_w : b_val < 2 ^ w := by omega
      let st₁ := st.setReg 4 a_val
      have hex_s1 : Exec w (.assign 4 (.read 27 (.reg 3))) st st₁ 3 :=
        .assign (by simp [Expr.eval, checkWord, hr3_i, hi_w, hu_A, a_val, ha_w])
      let st₂ := st₁.setReg 5 b_val
      have hex_s2 : Exec w (.assign 5 (.read 17 (.reg 3))) st₁ st₂ 3 :=
        .assign (by simp [st₁, Expr.eval, checkWord, hr3_i, hi_w, hu_B, b_val, hb_w])
      let prod_val := a_val * b_val
      have hprod_le : prod_val ≤ 1 := by
        dsimp [prod_val]
        have : a_val * b_val ≤ 1 * 1 := Nat.mul_le_mul ha_le hb_le
        omega
      have hprod_w : prod_val < 2 ^ w := by omega
      have hprod_iff : prod_val ≠ 0 ↔ (u ∈ A ∧ u ∈ B) := by
        have hAu := hA_mem u
        have hBu := hB_mem u
        change a_val ≠ 0 ↔ u ∈ A at hAu
        change b_val ≠ 0 ↔ u ∈ B at hBu
        dsimp [prod_val]
        by_cases h1 : u ∈ A <;> by_cases h2 : u ∈ B
        · have ha1 : a_val = 1 := by have := hAu.mpr h1; omega
          have hb1 : b_val = 1 := by have := hBu.mpr h2; omega
          simp [h1, h2, ha1, hb1]
        · have hb0 : b_val = 0 := not_ne_iff.mp (hBu.not.mpr h2)
          simp [h1, h2, hb0]
        · have ha0 : a_val = 0 := not_ne_iff.mp (hAu.not.mpr h1)
          simp [h1, h2, ha0]
        · have ha0 : a_val = 0 := not_ne_iff.mp (hAu.not.mpr h1)
          simp [h1, h2, ha0]
      by_cases hprod0 : prod_val = 0
      · have hnot_both : ¬ (u ∈ A ∧ u ∈ B) := fun h => hprod_iff.mpr h hprod0
        have hpref_iff : prefixDisj (i + 1) ↔ prefixDisj i := by
          constructor
          · intro h u' hu'
            exact h u' (by omega)
          · intro h u' hu'
            rcases Nat.lt_succ_iff_lt_or_eq.mp hu' with hlt | heq
            · exact h u' hlt
            · have hu'_eq : u' = u := Fin.ext heq
              subst hu'_eq
              exact hnot_both
        have hex_s3 :
            Exec w (.ite (.op .mul (.reg 4) (.reg 5)) (.assign 10 (.const 0)) .skip) st₂ st₂ 4 :=
          .ite_false
            (by
              simp [st₂, st₁, Expr.eval, BinOp.eval, BinOp.raw, checkWord,
                ha_w, hb_w, show a_val * b_val = prod_val from rfl, hprod0, h0_w])
            (.skip st₂)
        refine ⟨st₂, 3 + (3 + 4), .seq hex_s1 (.seq hex_s2 hex_s3), by dsimp only; omega, ?_, hr3_i⟩
        refine ⟨by simp [st₂, st₁, hr1_i],
          by simp [st₂, st₁],
          by simp [st₂, st₁, hr10_i, hpref_iff],
          ⟨by simpa [st₂, st₁] using hA_len,
            fun x => by simpa [st₂, st₁] using hA_le x,
            fun x => by simpa [st₂, st₁] using hA_mem x⟩,
          ⟨by simpa [st₂, st₁] using hB_len,
            fun x => by simpa [st₂, st₁] using hB_le x,
            fun x => by simpa [st₂, st₁] using hB_mem x⟩,
          fun a => by simp [st₂, st₁, harr_i a],
          fun r hr h10 => by
            have hr3 : (r : Reg) ≠ 3 := by omega
            have hr4 : (r : Reg) ≠ 4 := by omega
            have hr5 : (r : Reg) ≠ 5 := by omega
            simp [st₂, st₁, State.setReg, hr3, hr4, hr5, hreg_i r hr h10]⟩
      · have hboth : u ∈ A ∧ u ∈ B := hprod_iff.mp hprod0
        have hnot_pref : ¬ prefixDisj (i + 1) := fun h => h u (by dsimp [u]; omega) hboth
        let st₃ := st₂.setReg 10 0
        have hex_s3 :
            Exec w (.ite (.op .mul (.reg 4) (.reg 5)) (.assign 10 (.const 0)) .skip) st₂ st₃ 5 :=
          .ite_true
            (by
              simp [st₂, st₁, Expr.eval, BinOp.eval, BinOp.raw, checkWord,
                ha_w, hb_w, show a_val * b_val = prod_val from rfl, hprod_w])
            hprod0
            (.assign (by simp [Expr.eval, checkWord, h0_w]))
        refine ⟨st₃, 3 + (3 + 5), .seq hex_s1 (.seq hex_s2 hex_s3), by dsimp only; omega, ?_, hr3_i⟩
        refine ⟨by simp [st₃, st₂, st₁, hr1_i],
          by simp [st₃, st₂, st₁],
          by simp [st₃, State.setReg, hnot_pref],
          ⟨by simpa [st₃, st₂, st₁] using hA_len,
            fun x => by simpa [st₃, st₂, st₁] using hA_le x,
            fun x => by simpa [st₃, st₂, st₁] using hA_mem x⟩,
          ⟨by simpa [st₃, st₂, st₁] using hB_len,
            fun x => by simpa [st₃, st₂, st₁] using hB_le x,
            fun x => by simpa [st₃, st₂, st₁] using hB_mem x⟩,
          fun a => by simp [st₃, st₂, st₁, harr_i a],
          fun r hr h10 => by
            have hr3 : (r : Reg) ≠ 3 := by omega
            have hr4 : (r : Reg) ≠ 4 := by omega
            have hr5 : (r : Reg) ≠ 5 := by omega
            have hr10 : (r : Reg) ≠ 10 := by omega
            simp [st₃, st₂, st₁, State.setReg, hr3, hr4, hr5, hr10, hreg_i r hr h10]⟩
  have hpref0 : prefixDisj 0 := fun u hu => by omega
  have hinv₀ : Inv 0 s₂ := by
    refine ⟨by simp [s₂, s₁, hr1],
      by simp [s₂],
      by simp [s₂, s₁, hpref0],
      hA.of_arr_eq (by simp [s₂, s₁]),
      hB.of_arr_eq (by simp [s₂, s₁]),
      fun a => by simp [s₂, s₁],
      fun r hr h10 => by
        have hr3 : (r : Reg) ≠ 3 := by omega
        have hr10' : (r : Reg) ≠ 10 := by omega
        simp [s₂, s₁, State.setReg, hr3, hr10']⟩
  rcases hloop s₂ hinv₀ with ⟨s₃, t₃, hex₃, ht₃, _, _, hr10_3, _, _, harr₃, hreg₃⟩
  dsimp [Expr.cost] at ht₃
  have hpref_n_iff : prefixDisj n ↔ Disjoint A B := by
    unfold prefixDisj
    rw [Finset.disjoint_left]
    exact ⟨fun h u huA huB => h u u.2 ⟨huA, huB⟩, fun h u _ ⟨huA, huB⟩ => h huA huB⟩
  refine ⟨s₃, 2 + (2 + t₃), .seq hex₁ (.seq hex₂ hex₃), by omega,
    by simpa [hpref_n_iff] using hr10_3,
    harr₃, hreg₃⟩

/-! ### Section 2: Appending a Length-Prefixed Array (`appendLenPrefixedArrProg`) -/

/-- Append `(s.arrs a_src).length :: s.arrs a_src` to `a_dst` using scratch arrays `a_one, a_tmp`
and scratch registers `r_len1, r_len2, r_sc`. -/
def appendLenPrefixedArrProg (a_dst a_src a_one a_tmp : Arr) (r_len1 r_len2 r_sc : Reg) : Cmd :=
  .seq (.alloc a_one (.const 1))
    (.seq (.write a_one (.const 0) (.len a_src))
      (.seq (.assign r_len1 (.len a_dst))
        (.seq (.assign r_len2 (.const 1))
          (.seq (appendArrProg a_dst a_one a_tmp r_len1 r_len2 r_sc)
            (.seq (.assign r_len1 (.len a_dst))
              (.seq (.assign r_len2 (.len a_src))
                (appendArrProg a_dst a_src a_tmp r_len1 r_len2 r_sc)))))))

theorem appendLenPrefixedArrProg_exec {w : ℕ}
    (a_dst a_src a_one a_tmp : ℕ) (r_len1 r_len2 r_sc : ℕ)
    (hne_ds : a_dst ≠ a_src) (hne_do : a_dst ≠ a_one) (hne_dt : a_dst ≠ a_tmp)
    (hne_so : a_src ≠ a_one) (hne_st : a_src ≠ a_tmp) (hne_ot : a_one ≠ a_tmp)
    (hr12 : r_len1 < r_len2) (hr2s : r_len2 < r_sc)
    (L₁ L₂ : List ℕ)
    (hL₁_w : ∀ x ∈ L₁, x < 2 ^ w) (hL₂_w : ∀ x ∈ L₂, x < 2 ^ w)
    (hw1 : 1 < 2 ^ w)
    (htot_w : L₁.length + 1 + L₂.length < 2 ^ w)
    {s : State}
    (hdst : s.arrs a_dst = L₁)
    (hsrc : s.arrs a_src = L₂) :
    ∃ s' t,
      Exec w (appendLenPrefixedArrProg a_dst a_src a_one a_tmp r_len1 r_len2 r_sc) s s' t ∧
      t ≤ 137 + 68 * L₁.length + 18 * L₂.length ∧
      s'.arrs a_dst = L₁ ++ (L₂.length :: L₂) ∧
      (∀ a : Arr, a ≠ a_dst → a ≠ a_one → a ≠ a_tmp → s'.arrs a = s.arrs a) ∧
      (∀ r : ℕ, (r < r_sc ∨ r_sc + 3 < r) → r ≠ r_len1 → r ≠ r_len2 → s'.regs r = s.regs r) := by
  have h0_w : 0 < 2 ^ w := by omega
  have hlen1_w : L₁.length < 2 ^ w := by omega
  have hlen2_w : L₂.length < 2 ^ w := by omega
  have hlen11_w : L₁.length + 1 < 2 ^ w := by omega
  -- 1. alloc a_one (.const 1)
  let s₁ := s.setArr a_one (List.replicate 1 0)
  have hex₁ : Exec w (.alloc a_one (.const 1)) s s₁ (1 + 1) :=
    .alloc (by simp [Expr.eval, checkWord, hw1])
  -- 2. write a_one (.const 0) (.len a_src)
  let s₂ := s₁.writeArr a_one 0 L₂.length
  have hex₂ : Exec w (.write a_one (.const 0) (.len a_src)) s₁ s₂ 3 :=
    .write (by simp [Expr.eval, checkWord, h0_w])
      (by simp [s₁, State.setArr_arrs_ne _ _ hne_so, Expr.eval, checkWord, hsrc, hlen2_w])
      (by simp [s₁])
  have hone₂ : s₂.arrs a_one = [L₂.length] := by simp [s₂, s₁]
  have hdst₂ : s₂.arrs a_dst = L₁ := by
    simp [s₂, s₁, State.writeArr_arrs_ne _ _ _ hne_do, State.setArr_arrs_ne _ _ hne_do, hdst]
  -- 3. assign r_len1 (.len a_dst)
  let s₃ := s₂.setReg r_len1 L₁.length
  have hex₃ : Exec w (.assign r_len1 (.len a_dst)) s₂ s₃ 2 :=
    .assign (by simp [Expr.eval, checkWord, hdst₂, hlen1_w])
  -- 4. assign r_len2 (.const 1)
  let s₄ := s₃.setReg r_len2 1
  have hex₄ : Exec w (.assign r_len2 (.const 1)) s₃ s₄ 2 :=
    .assign (by simp [Expr.eval, checkWord, hw1])
  have hr1_4 : s₄.regs r_len1 = L₁.length := by
    have hne : (r_len1 : Reg) ≠ r_len2 := by omega
    simp [s₄, s₃, State.setReg_regs_ne _ _ hne]
  -- 5. appendArrProg a_dst a_one a_tmp r_len1 r_len2 r_sc
  have hone_w : ∀ x ∈ [L₂.length], x < 2 ^ w := by simp [hlen2_w]
  rcases appendArrProg_exec a_dst a_one a_tmp r_len1 r_len2 r_sc
      hne_do hne_dt hne_ot (by omega) (by omega) hr2s L₁ [L₂.length]
      hL₁_w hone_w hw1 (by simpa using hlen11_w) (s := s₄)
      hdst₂ hone₂ hr1_4 (by simp [s₄]) with
    ⟨s₅, t₅, hex₅, ht₅, hdst₅, _, harr₅, hreg₅⟩
  have hsrc₅ : s₅.arrs a_src = L₂ := by
    rw [harr₅ a_src hne_ds.symm hne_st]
    simp [s₄, s₃, s₂, s₁, State.writeArr_arrs_ne _ _ _ hne_so, State.setArr_arrs_ne _ _ hne_so, hsrc]
  -- 6. assign r_len1 (.len a_dst)
  let s₆ := s₅.setReg r_len1 (L₁ ++ [L₂.length]).length
  have hex₆ : Exec w (.assign r_len1 (.len a_dst)) s₅ s₆ 2 :=
    .assign (by simp [Expr.eval, checkWord, hdst₅, hlen11_w])
  -- 7. assign r_len2 (.len a_src)
  let s₇ := s₆.setReg r_len2 L₂.length
  have hex₇ : Exec w (.assign r_len2 (.len a_src)) s₆ s₇ 2 :=
    .assign (by simp [s₆, Expr.eval, checkWord, hsrc₅, hlen2_w])
  have hr1_7 : s₇.regs r_len1 = (L₁ ++ [L₂.length]).length := by
    have hne : (r_len1 : Reg) ≠ r_len2 := by omega
    simp [s₇, s₆, State.setReg_regs_ne _ _ hne]
  -- 8. appendArrProg a_dst a_src a_tmp r_len1 r_len2 r_sc
  have hL₁_one_w : ∀ x ∈ L₁ ++ [L₂.length], x < 2 ^ w := by
    intro x hx
    rcases List.mem_append.mp hx with hx1 | hx2
    · exact hL₁_w x hx1
    · exact hone_w x hx2
  rcases appendArrProg_exec a_dst a_src a_tmp r_len1 r_len2 r_sc
      hne_ds hne_dt hne_st (by omega) (by omega) hr2s (L₁ ++ [L₂.length]) L₂
      hL₁_one_w hL₂_w hw1 (by simpa [List.length_append] using htot_w) (s := s₇)
      hdst₅ hsrc₅ hr1_7 (by simp [s₇]) with
    ⟨s₈, t₈, hex₈, ht₈, hdst₈, _, harr₈, hreg₈⟩
  rw [List.append_assoc, List.singleton_append] at hdst₈
  simp only [List.length_append, List.length_singleton] at ht₅ ht₈
  refine ⟨s₈, (1 + 1) + (3 + (2 + (2 + (t₅ + (2 + (2 + t₈)))))),
    .seq hex₁ (.seq hex₂ (.seq hex₃ (.seq hex₄ (.seq hex₅ (.seq hex₆ (.seq hex₇ hex₈)))))),
    by omega, hdst₈,
    fun a ha_d ha_o ha_t => by
      rw [harr₈ a ha_d ha_t]
      simp only [s₇, s₆, State.setReg_arrs]
      rw [harr₅ a ha_d ha_t]
      simp [s₄, s₃, s₂, s₁, State.writeArr_arrs_ne _ _ _ ha_o, State.setArr_arrs_ne _ _ ha_o],
    fun r hrs hr1 hr2 => by
      rw [hreg₈ r hrs hr1]
      simp only [s₇, s₆, State.setReg_regs_ne _ _ hr2, State.setReg_regs_ne _ _ hr1]
      rw [hreg₅ r hrs hr1]
      simp [s₄, s₃, s₂, s₁, State.setReg_regs_ne _ _ hr2, State.setReg_regs_ne _ _ hr1]⟩

/-! ### Section 3: Subwall Scan Step and Loop (`alg97ScanSubwallsProg`) -/

/-- Upper bound on the encoding length of a single crossed subwall block
`W_sub.encList ++ (P₁.length :: P₁.map Fin.val) ++ (P₂.length :: P₂.map Fin.val)`. -/
def maxCrossedBlockLen (h n : ℕ) : ℕ :=
  maxWallEncLen h n + 2 * n + 2

theorem maxCrossedBlockLen_pos (h n : ℕ) : 1 ≤ maxCrossedBlockLen h n := by
  unfold maxCrossedBlockLen maxWallEncLen; omega

/-- Extend a finite sequence `f : Fin m → α` by appending `last : α` at index `m`. -/
def snocFin {α : Type*} {m : ℕ} (f : Fin m → α) (last : α) (i : Fin (m + 1)) : α :=
  if h : i.1 < m then f ⟨i.1, h⟩ else last

@[simp]
theorem snocFin_lt {α : Type*} {m : ℕ} (f : Fin m → α) (last : α) (i : Fin (m + 1))
    (h : i.1 < m) :
    snocFin f last i = f ⟨i.1, h⟩ := by
  simp [snocFin, h]

@[simp]
theorem snocFin_last {α : Type*} {m : ℕ} (f : Fin m → α) (last : α) :
    snocFin f last ⟨m, Nat.lt_succ_self m⟩ = last := by
  simp [snocFin]

theorem map_finRange_snocFin {α : Type*} {m : ℕ} (f : Fin m → α) (last : α) :
    (List.finRange (m + 1)).map (snocFin f last) = (List.finRange m).map f ++ [last] := by
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    rw [List.length_map, List.length_finRange] at h1
    simp only [List.getElem_map, List.getElem_finRange, Fin.cast_mk]
    by_cases hi : i < m
    · rw [snocFin_lt f last ⟨i, by omega⟩ hi,
        List.getElem_append_left (by simp [hi])]
      simp
    · have hi_eq : i = m := by omega
      subst hi_eq
      rw [snocFin_last, List.getElem_append_right (by simp)]
      simp

theorem flatMap_finRange_snocFin {α β : Type*} {m : ℕ} (f : Fin m → α) (last : α)
    (g : α → List β) :
    (List.finRange (m + 1)).flatMap (fun a => g (snocFin f last a)) =
      (List.finRange m).flatMap (fun a => g (f a)) ++ g last := by
  have h1 : (List.finRange (m + 1)).flatMap (fun a => g (snocFin f last a)) =
      ((List.finRange (m + 1)).map (snocFin f last)).flatMap g := by
    rw [List.flatMap_map]
  have h2 : (List.finRange m).flatMap (fun a => g (f a)) =
      ((List.finRange m).map f).flatMap g := by
    rw [List.flatMap_map]
  rw [h1, h2, map_finRange_snocFin, List.flatMap_append, List.flatMap_singleton]

theorem flatMap_finRange_snocFin₂ {α₁ α₂ β : Type*} {m : ℕ}
    (f₁ : Fin m → α₁) (last₁ : α₁) (f₂ : Fin m → α₂) (last₂ : α₂) (g : α₁ → α₂ → List β) :
    (List.finRange (m + 1)).flatMap (fun a => g (snocFin f₁ last₁ a) (snocFin f₂ last₂ a)) =
      (List.finRange m).flatMap (fun a => g (f₁ a) (f₂ a)) ++ g last₁ last₂ := by
  have hpair : ∀ a : Fin (m + 1),
      g (snocFin f₁ last₁ a) (snocFin f₂ last₂ a) =
        (fun p : α₁ × α₂ => g p.1 p.2) (snocFin (fun i => (f₁ i, f₂ i)) (last₁, last₂) a) := by
    intro a
    by_cases ha : a.1 < m <;> simp [snocFin, ha]
  simp only [hpair]
  exact flatMap_finRange_snocFin (fun i => (f₁ i, f₂ i)) (last₁, last₂) (fun p => g p.1 p.2)

theorem strictMono_snocFin {m t j : ℕ} {idx : Fin m → Fin t} {j_fin : Fin t}
    (hmono : StrictMono idx) (hlt : ∀ a : Fin m, (idx a).1 < j) (hj : j_fin.1 = j) :
    StrictMono (snocFin idx j_fin) ∧ ∀ a : Fin (m + 1), (snocFin idx j_fin a).1 < j + 1 := by
  refine ⟨?_, ?_⟩
  · intro a b hab
    by_cases hb : b.1 < m
    · have ha : a.1 < m := Nat.lt_trans hab hb
      rw [snocFin_lt idx j_fin a ha, snocFin_lt idx j_fin b hb]
      exact hmono hab
    · have hb_eq : b = ⟨m, Nat.lt_succ_self m⟩ := by ext; simp; omega
      have ha : a.1 < m := by omega
      subst hb_eq
      rw [snocFin_lt idx j_fin a ha, snocFin_last]
      change (idx ⟨a.1, ha⟩).1 < j_fin.1
      rw [hj]
      exact hlt ⟨a.1, ha⟩
  · intro a
    by_cases ha : a.1 < m
    · rw [snocFin_lt idx j_fin a ha]
      have := hlt ⟨a.1, ha⟩
      omega
    · have ha_eq : a = ⟨m, Nat.lt_succ_self m⟩ := by ext; simp; omega
      subst ha_eq
      rw [snocFin_last, hj]
      omega

/-- Subwall indices `idx < j` belonging to `I : Finset (Fin t)`. -/
def divSetIndicesUpTo {t : ℕ} (I : Finset (Fin t)) (j : ℕ) : List (Fin t) :=
  ((List.finRange t).take j).filter (fun idx => decide (idx ∈ I))

@[simp]
theorem divSetIndicesUpTo_zero {t : ℕ} (I : Finset (Fin t)) :
    divSetIndicesUpTo I 0 = [] := by
  simp [divSetIndicesUpTo]

theorem divSetIndicesUpTo_succ_of_mem {t : ℕ} (I : Finset (Fin t)) {j : ℕ} (hj : j < t)
    (hmem : (⟨j, hj⟩ : Fin t) ∈ I) :
    divSetIndicesUpTo I (j + 1) = divSetIndicesUpTo I j ++ [⟨j, hj⟩] := by
  unfold divSetIndicesUpTo
  have hj_len : j < (List.finRange t).length := by simp [hj]
  rw [take_add_one_eq_append_getElem (List.finRange t) j hj_len,
    List.getElem_finRange, List.filter_append, List.filter_singleton]
  simp [hmem]

theorem divSetIndicesUpTo_succ_of_not_mem {t : ℕ} (I : Finset (Fin t)) {j : ℕ} (hj : j < t)
    (hnot : (⟨j, hj⟩ : Fin t) ∉ I) :
    divSetIndicesUpTo I (j + 1) = divSetIndicesUpTo I j := by
  unfold divSetIndicesUpTo
  have hj_len : j < (List.finRange t).length := by simp [hj]
  rw [take_add_one_eq_append_getElem (List.finRange t) j hj_len,
    List.getElem_finRange, List.filter_append, List.filter_singleton]
  simp [hnot]

theorem length_divSetIndicesUpTo_full {t : ℕ} (I : Finset (Fin t)) :
    (divSetIndicesUpTo I t).length = I.card := by
  unfold divSetIndicesUpTo
  have htake : (List.finRange t).take t = List.finRange t := List.take_of_length_le (by simp)
  rw [htake]
  let L := (List.finRange t).filter (fun idx => decide (idx ∈ I))
  have hnodup : L.Nodup := (List.nodup_finRange t).filter _
  have hlen : L.length = L.toFinset.card := (List.toFinset_card_of_nodup hnodup).symm
  have hset : L.toFinset = I := by
    ext x
    simp [L]
  change L.length = I.card
  rw [hlen, hset]

/-- Subwall indices `idx < j` whose vertex set `(W_sub idx).vertexFinset` intersects `X`. -/
def hitXIndicesUpTo {n t h : ℕ} {G : MultiDigraph n}
    (W_sub : Fin t → WallOfHeight h G) (X : Finset (Fin n)) (j : ℕ) : List (Fin t) :=
  ((List.finRange t).take j).filter (fun idx => !decide (Disjoint (W_sub idx).vertexFinset X))

@[simp]
theorem hitXIndicesUpTo_zero {n t h : ℕ} {G : MultiDigraph n}
    (W_sub : Fin t → WallOfHeight h G) (X : Finset (Fin n)) :
    hitXIndicesUpTo W_sub X 0 = [] := by
  simp [hitXIndicesUpTo]

theorem hitXIndicesUpTo_succ_of_disjoint {n t h : ℕ} {G : MultiDigraph n}
    (W_sub : Fin t → WallOfHeight h G) (X : Finset (Fin n)) {j : ℕ} (hj : j < t)
    (hdisj : Disjoint (W_sub ⟨j, hj⟩).vertexFinset X) :
    hitXIndicesUpTo W_sub X (j + 1) = hitXIndicesUpTo W_sub X j := by
  unfold hitXIndicesUpTo
  have hj_len : j < (List.finRange t).length := by simp [hj]
  rw [take_add_one_eq_append_getElem (List.finRange t) j hj_len,
    List.getElem_finRange, List.filter_append, List.filter_singleton]
  simp [hdisj]

theorem hitXIndicesUpTo_succ_of_not_disjoint {n t h : ℕ} {G : MultiDigraph n}
    (W_sub : Fin t → WallOfHeight h G) (X : Finset (Fin n)) {j : ℕ} (hj : j < t)
    (hndisj : ¬ Disjoint (W_sub ⟨j, hj⟩).vertexFinset X) :
    hitXIndicesUpTo W_sub X (j + 1) = hitXIndicesUpTo W_sub X j ++ [⟨j, hj⟩] := by
  unfold hitXIndicesUpTo
  have hj_len : j < (List.finRange t).length := by simp [hj]
  rw [take_add_one_eq_append_getElem (List.finRange t) j hj_len,
    List.getElem_finRange, List.filter_append, List.filter_singleton]
  simp [hndisj]

theorem length_hitXIndicesUpTo_mono {n t h : ℕ} {G : MultiDigraph n}
    (W_sub : Fin t → WallOfHeight h G) (X : Finset (Fin n)) {j : ℕ} (hj : j < t) :
    (hitXIndicesUpTo W_sub X j).length ≤ (hitXIndicesUpTo W_sub X (j + 1)).length := by
  by_cases hdisj : Disjoint (W_sub ⟨j, hj⟩).vertexFinset X
  · rw [hitXIndicesUpTo_succ_of_disjoint W_sub X hj hdisj]
  · rw [hitXIndicesUpTo_succ_of_not_disjoint W_sub X hj hdisj, List.length_append]
    omega

/-- If the subwalls `W_sub j` (`j : Fin t`) are pairwise vertex-disjoint, then at most `X.card`
of them can have non-empty intersection with `X` (GM XIII (9.6), page 103). -/
theorem length_hitXIndicesUpTo_le_card {n t h : ℕ} {G : MultiDigraph n}
    {W_sub : Fin t → WallOfHeight h G} (X : Finset (Fin n))
    (hdisj : ∀ j₁ j₂ : Fin t, j₁ ≠ j₂ →
      Disjoint (W_sub j₁).vertexFinset (W_sub j₂).vertexFinset) :
    (hitXIndicesUpTo W_sub X t).length ≤ X.card := by
  have htake : (List.finRange t).take t = List.finRange t := List.take_of_length_le (by simp)
  unfold hitXIndicesUpTo
  rw [htake]
  let L := (List.finRange t).filter (fun idx => !decide (Disjoint (W_sub idx).vertexFinset X))
  have hnodup : L.Nodup := (List.nodup_finRange t).filter _
  let S := L.toFinset
  have hlen : L.length = S.card := (List.toFinset_card_of_nodup hnodup).symm
  have hcard_le_sum : S.card ≤ ∑ idx ∈ S, ((W_sub idx).vertexFinset ∩ X).card := by
    rw [Finset.card_eq_sum_ones]
    apply Finset.sum_le_sum
    intro idx hidx
    have hmem : idx ∈ L := List.mem_toFinset.mp hidx
    rw [List.mem_filter] at hmem
    have hnd := hmem.2
    simp only [Bool.not_eq_true', decide_eq_false_iff_not] at hnd
    rcases Finset.not_disjoint_iff.mp hnd with ⟨u, huV, huX⟩
    exact Finset.card_pos.mpr ⟨u, Finset.mem_inter.mpr ⟨huV, huX⟩⟩
  have hbiUnion_card :
      (∑ idx ∈ S, ((W_sub idx).vertexFinset ∩ X).card) =
        (S.biUnion (fun idx : Fin t => (W_sub idx).vertexFinset ∩ X)).card := by
    symm
    apply Finset.card_biUnion
    intro j₁ _ j₂ _ hne
    exact Disjoint.mono Finset.inter_subset_left Finset.inter_subset_left (hdisj j₁ j₂ hne)
  have hsub_X :
      S.biUnion (fun idx : Fin t => (W_sub idx).vertexFinset ∩ X) ⊆ X :=
    Finset.biUnion_subset.mpr (fun _ _ => Finset.inter_subset_right)
  have hcard_le : (S.biUnion (fun idx : Fin t => (W_sub idx).vertexFinset ∩ X)).card ≤ X.card :=
    Finset.card_le_card hsub_X
  change L.length ≤ X.card
  omega

/-- Data recorded for a crossed subwall `W' : WallOfHeight h G'`: the two cross paths
`P₁, P₂ : List (Fin n)` inside `W'.compassFinset`. -/
structure CrossedSubwallData {n h : ℕ} (h2 : 2 ≤ h) {G' : MultiDigraph n}
    (W' : WallOfHeight h G') where
  /-- First path of the cross over `W'`. -/
  P₁ : List (Fin n)
  /-- Second path of the cross over `W'`. -/
  P₂ : List (Fin n)
  /-- `(P₁, P₂)` is a cross over `W'` in `G'`. -/
  hcr : W'.IsCrossOverWall h2 P₁ P₂
  /-- Every vertex of `P₁` lies in `W'.compassFinset`. -/
  hmem₁ : ∀ v ∈ P₁, v ∈ W'.compassFinset
  /-- Every vertex of `P₂` lies in `W'.compassFinset`. -/
  hmem₂ : ∀ v ∈ P₂, v ∈ W'.compassFinset

/-- Encoding of `W'` together with the two length-prefixed cross paths `P₁` and `P₂`, matching
the per-subwall block of `encAlg91In`. -/
def crossedSubwallBlock {n h : ℕ} {G' : MultiDigraph n}
    (W' : WallOfHeight h G') (P₁ P₂ : List (Fin n)) : List ℕ :=
  W'.encList ++ (P₁.length :: P₁.map Fin.val) ++ (P₂.length :: P₂.map Fin.val)

theorem length_nodup_fin_le {n : ℕ} {L : List (Fin n)} (hnd : L.Nodup) :
    L.length ≤ n := by
  simpa [Fintype.card_fin] using hnd.length_le_card

theorem length_crossedSubwallBlock_le {n h : ℕ} {h2 : 2 ≤ h} {G' : MultiDigraph n}
    {W' : WallOfHeight h G'} (hW' : W'.IsValid) (C : CrossedSubwallData h2 W') :
    (crossedSubwallBlock W' C.P₁ C.P₂).length ≤ maxCrossedBlockLen h n := by
  have h1 : W'.encList.length ≤ maxWallEncLen h n := by
    have ha := Alg91.length_encList_le_of_isValid hW'
    have hb := length_elemWallEdges_le h
    unfold maxWallEncLen; omega
  have h2 := length_nodup_fin_le C.hcr.nodup₁
  have h3 := length_nodup_fin_le C.hcr.nodup₂
  unfold crossedSubwallBlock maxCrossedBlockLen
  simp only [List.length_append, List.length_cons, List.length_map]
  omega

theorem all_lt_crossedSubwallBlock {n h w : ℕ} {h2 : 2 ≤ h} {G' : MultiDigraph n}
    {W' : WallOfHeight h G'} (hW' : W'.IsValid) (C : CrossedSubwallData h2 W')
    (hh_w : h < 2 ^ w) (hc2_w : 3 + 2 * elemWallNumVerts h < 2 ^ w) (hn1_w : n + 1 < 2 ^ w) :
    ∀ x ∈ crossedSubwallBlock W' C.P₁ C.P₂, x < 2 ^ w := by
  have hn_w : n < 2 ^ w := by omega
  have hW_w := all_lt_encList_of_isValid W' hW' le_rfl hh_w hc2_w hn_w
  have hP₁_len : C.P₁.length ≤ n := length_nodup_fin_le C.hcr.nodup₁
  have hP₂_len : C.P₂.length ≤ n := length_nodup_fin_le C.hcr.nodup₂
  intro x hx
  unfold crossedSubwallBlock at hx
  simp only [List.append_assoc, List.mem_append, List.mem_cons, List.mem_map] at hx
  rcases hx with hW | (rfl | ⟨v, _, rfl⟩) | (rfl | ⟨v, _, rfl⟩)
  · exact hW_w x hW
  · omega
  · exact Nat.lt_trans v.2 hn_w
  · omega
  · exact Nat.lt_trans v.2 hn_w

/-- Load the four corner vertices `(c0, c2, c1, c3)` of `W_sub : WallOfHeight h G'` from `arr 26`
(`= W_sub.encList`) into registers `31, 32, 33, 34`, and set `reg 30 := reg 1` (`= n`). -/
def loadShiloachInputsProg (h : ℕ) (h2 : 2 ≤ h) : Cmd :=
  .seq (.assign 30 (.reg 1))
    (.seq (.assign 31 (.read 26 (.const (3 + (elemWallCornerIdx h2 0).1))))
      (.seq (.assign 32 (.read 26 (.const (3 + (elemWallCornerIdx h2 2).1))))
        (.seq (.assign 33 (.read 26 (.const (3 + (elemWallCornerIdx h2 1).1))))
          (.assign 34 (.read 26 (.const (3 + (elemWallCornerIdx h2 3).1)))))))

theorem loadShiloachInputsProg_exec {w h n : ℕ} (h2 : 2 ≤ h)
    {G' : MultiDigraph n} (W_sub : WallOfHeight h G')
    (hn_w : n < 2 ^ w) (hc_w : 3 + elemWallNumVerts h < 2 ^ w)
    {s : State}
    (harr26 : s.arrs 26 = W_sub.encList)
    (hr1 : s.regs 1 = n) :
    ∃ s' t,
      Exec w (loadShiloachInputsProg h h2) s s' t ∧
      t ≤ 14 ∧
      s'.regs 30 = n ∧
      s'.regs 31 = (W_sub.cornerVert h2 0).1 ∧
      s'.regs 32 = (W_sub.cornerVert h2 2).1 ∧
      s'.regs 33 = (W_sub.cornerVert h2 1).1 ∧
      s'.regs 34 = (W_sub.cornerVert h2 3).1 ∧
      (∀ a : Arr, s'.arrs a = s.arrs a) ∧
      (∀ r : ℕ, r < 30 ∨ 34 < r → s'.regs r = s.regs r) := by
  have hread_c : ∀ c : Fin 4,
      ∃ (hl : 3 + (elemWallCornerIdx h2 c).1 < (s.arrs 26).length),
      (s.arrs 26)[3 + (elemWallCornerIdx h2 c).1]'hl = (W_sub.cornerVert h2 c).1 := by
    intro c
    have h := readBranchVert_at_off W_sub (elemWallCornerIdx h2 c) [] []
      (by simpa using harr26)
    simpa [WallOfHeight.cornerVert] using h
  obtain ⟨hl0, hr0⟩ := hread_c 0
  obtain ⟨hl1, hr1_c⟩ := hread_c 1
  obtain ⟨hl2, hr2⟩ := hread_c 2
  obtain ⟨hl3, hr3⟩ := hread_c 3
  have hc0_w : 3 + (elemWallCornerIdx h2 0).1 < 2 ^ w := by have := (elemWallCornerIdx h2 0).2; omega
  have hc1_w : 3 + (elemWallCornerIdx h2 1).1 < 2 ^ w := by have := (elemWallCornerIdx h2 1).2; omega
  have hc2_w : 3 + (elemWallCornerIdx h2 2).1 < 2 ^ w := by have := (elemWallCornerIdx h2 2).2; omega
  have hc3_w : 3 + (elemWallCornerIdx h2 3).1 < 2 ^ w := by have := (elemWallCornerIdx h2 3).2; omega
  have hv0_w : (W_sub.cornerVert h2 0).1 < 2 ^ w := Nat.lt_trans (W_sub.cornerVert h2 0).2 hn_w
  have hv1_w : (W_sub.cornerVert h2 1).1 < 2 ^ w := Nat.lt_trans (W_sub.cornerVert h2 1).2 hn_w
  have hv2_w : (W_sub.cornerVert h2 2).1 < 2 ^ w := Nat.lt_trans (W_sub.cornerVert h2 2).2 hn_w
  have hv3_w : (W_sub.cornerVert h2 3).1 < 2 ^ w := Nat.lt_trans (W_sub.cornerVert h2 3).2 hn_w
  let s₁ := s.setReg 30 n
  have hex₁ : Exec w (.assign 30 (.reg 1)) s s₁ 2 :=
    .assign (by simp [Expr.eval, checkWord, hr1, hn_w])
  let s₂ := s₁.setReg 31 (W_sub.cornerVert h2 0).1
  have hex₂ : Exec w (.assign 31 (.read 26 (.const (3 + (elemWallCornerIdx h2 0).1)))) s₁ s₂ 3 :=
    .assign (by simp [s₁, Expr.eval, checkWord, hc0_w, hl0, hr0, hv0_w])
  let s₃ := s₂.setReg 32 (W_sub.cornerVert h2 2).1
  have hex₃ : Exec w (.assign 32 (.read 26 (.const (3 + (elemWallCornerIdx h2 2).1)))) s₂ s₃ 3 :=
    .assign (by simp [s₂, s₁, Expr.eval, checkWord, hc2_w, hl2, hr2, hv2_w])
  let s₄ := s₃.setReg 33 (W_sub.cornerVert h2 1).1
  have hex₄ : Exec w (.assign 33 (.read 26 (.const (3 + (elemWallCornerIdx h2 1).1)))) s₃ s₄ 3 :=
    .assign (by simp [s₃, s₂, s₁, Expr.eval, checkWord, hc1_w, hl1, hr1_c, hv1_w])
  let s₅ := s₄.setReg 34 (W_sub.cornerVert h2 3).1
  have hex₅ : Exec w (.assign 34 (.read 26 (.const (3 + (elemWallCornerIdx h2 3).1)))) s₄ s₅ 3 :=
    .assign (by simp [s₄, s₃, s₂, s₁, Expr.eval, checkWord, hc3_w, hl3, hr3, hv3_w])
  refine ⟨s₅, 2 + (3 + (3 + (3 + 3))),
    .seq hex₁ (.seq hex₂ (.seq hex₃ (.seq hex₄ hex₅))),
    by omega,
    by simp [s₅, s₄, s₃, s₂, s₁],
    by simp [s₅, s₄, s₃, s₂],
    by simp [s₅, s₄, s₃],
    by simp [s₅, s₄],
    by simp [s₅],
    fun _ => rfl,
    fun r hr => by
      have h30 : (r : Reg) ≠ 30 := by omega
      have h31 : (r : Reg) ≠ 31 := by omega
      have h32 : (r : Reg) ≠ 32 := by omega
      have h33 : (r : Reg) ≠ 33 := by omega
      have h34 : (r : Reg) ≠ 34 := by omega
      simp [s₅, s₄, s₃, s₂, s₁, State.setReg, h30, h31, h32, h33, h34]⟩

/-- Append the crossed subwall block `arr 26 ++ (len(arr 33) :: arr 33) ++ (len(arr 34) :: arr 34)`
to `arr 24` and increment `reg 11`. -/
def recordCrossedSubwallProg : Cmd :=
  .seq (.assign 3 (.len 24))
    (.seq (.assign 4 (.len 26))
      (.seq (appendArrProg 24 26 29 3 4 5)
        (.seq (appendLenPrefixedArrProg 24 33 28 29 3 4 5)
          (.seq (appendLenPrefixedArrProg 24 34 28 29 3 4 5)
            (.assign 11 (.op .add (.reg 11) (.const 1)))))))

theorem recordCrossedSubwallProg_exec {w h n : ℕ}
    {G' : MultiDigraph n} (W_sub : WallOfHeight h G')
    (L_prev P₁_vals P₂_vals : List ℕ) (c_cnt : ℕ)
    (hprev_w : ∀ x ∈ L_prev, x < 2 ^ w)
    (hW_w : ∀ x ∈ W_sub.encList, x < 2 ^ w)
    (hP₁_w : ∀ x ∈ P₁_vals, x < 2 ^ w)
    (hP₂_w : ∀ x ∈ P₂_vals, x < 2 ^ w)
    (hw1 : 1 < 2 ^ w)
    (htot_w : L_prev.length + W_sub.encList.length + (P₁_vals.length + 1) + (P₂_vals.length + 1) < 2 ^ w)
    (hc_cnt_w : c_cnt + 1 < 2 ^ w)
    {s : State}
    (harr24 : s.arrs 24 = L_prev)
    (harr26 : s.arrs 26 = W_sub.encList)
    (harr33 : s.arrs 33 = P₁_vals)
    (harr34 : s.arrs 34 = P₂_vals)
    (hr11 : s.regs 11 = c_cnt) :
    ∃ s' t,
      Exec w recordCrossedSubwallProg s s' t ∧
      t ≤ 386 + 170 * L_prev.length + 154 * W_sub.encList.length +
        86 * P₁_vals.length + 18 * P₂_vals.length ∧
      s'.arrs 24 = L_prev ++
        (W_sub.encList ++ (P₁_vals.length :: P₁_vals) ++ (P₂_vals.length :: P₂_vals)) ∧
      s'.regs 11 = c_cnt + 1 ∧
      (∀ a : Arr, a ≠ 24 → a ≠ 28 → a ≠ 29 → s'.arrs a = s.arrs a) ∧
      (∀ r : ℕ, (r < 3 ∨ 8 < r) → r ≠ 11 → s'.regs r = s.regs r) := by
  have hlen_prev_w : L_prev.length < 2 ^ w := by omega
  have hlen_W_w : W_sub.encList.length < 2 ^ w := by omega
  have hlen_P₁_w : P₁_vals.length < 2 ^ w := by omega
  have hlen1_w : L_prev.length + W_sub.encList.length < 2 ^ w := by omega
  have hlen2_w : (L_prev ++ W_sub.encList).length + 1 + P₁_vals.length < 2 ^ w := by
    simp [List.length_append]; omega
  have hlen3_w :
      (L_prev ++ W_sub.encList ++ (P₁_vals.length :: P₁_vals)).length + 1 + P₂_vals.length < 2 ^ w := by
    simp [List.length_append]; omega
  -- 1. assign 3 (.len 24)
  let s₁ := s.setReg 3 L_prev.length
  have hex₁ : Exec w (.assign 3 (.len 24)) s s₁ 2 :=
    .assign (by simp [Expr.eval, checkWord, harr24, hlen_prev_w])
  -- 2. assign 4 (.len 26)
  let s₂ := s₁.setReg 4 W_sub.encList.length
  have hex₂ : Exec w (.assign 4 (.len 26)) s₁ s₂ 2 :=
    .assign (by simp [s₁, Expr.eval, checkWord, harr26, hlen_W_w])
  -- 3. appendArrProg 24 26 29 3 4 5
  rcases appendArrProg_exec 24 26 29 3 4 5
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      L_prev W_sub.encList hprev_w hW_w hw1 hlen1_w (s := s₂)
      harr24 harr26 (by simp [s₂, s₁]) (by simp [s₂]) with
    ⟨s₃, t₃, hex₃, ht₃, harr24_3, _, harr₃, hreg₃⟩
  -- 4. appendLenPrefixedArrProg 24 33 28 29 3 4 5
  have harr33_3 : s₃.arrs 33 = P₁_vals := by
    rw [harr₃ 33 (by decide) (by decide)]; exact harr33
  have hprev_W_w : ∀ x ∈ L_prev ++ W_sub.encList, x < 2 ^ w := by
    intro x hx
    rcases List.mem_append.mp hx with hx1 | hx2
    · exact hprev_w x hx1
    · exact hW_w x hx2
  rcases appendLenPrefixedArrProg_exec 24 33 28 29 3 4 5
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (L_prev ++ W_sub.encList) P₁_vals hprev_W_w hP₁_w hw1 hlen2_w (s := s₃)
      harr24_3 harr33_3 with
    ⟨s₄, t₄, hex₄, ht₄, harr24_4, harr₄, hreg₄⟩
  -- 5. appendLenPrefixedArrProg 24 34 28 29 3 4 5
  have harr34_4 : s₄.arrs 34 = P₂_vals := by
    rw [harr₄ 34 (by decide) (by decide) (by decide), harr₃ 34 (by decide) (by decide)]
    exact harr34
  have hprev_W_P₁_w : ∀ x ∈ L_prev ++ W_sub.encList ++ (P₁_vals.length :: P₁_vals), x < 2 ^ w := by
    intro x hx
    rcases List.mem_append.mp hx with hx1 | hx2
    · exact hprev_W_w x hx1
    · rcases List.mem_cons.mp hx2 with rfl | hx3
      · exact hlen_P₁_w
      · exact hP₁_w x hx3
  rcases appendLenPrefixedArrProg_exec 24 34 28 29 3 4 5
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide)
      (L_prev ++ W_sub.encList ++ (P₁_vals.length :: P₁_vals)) P₂_vals
      hprev_W_P₁_w hP₂_w hw1 hlen3_w (s := s₄)
      harr24_4 harr34_4 with
    ⟨s₅, t₅, hex₅, ht₅, harr24_5, harr₅, hreg₅⟩
  -- 6. assign 11 (reg 11 + 1)
  have hr11_5 : s₅.regs 11 = c_cnt := by
    rw [hreg₅ 11 (Or.inr (by decide)) (by decide) (by decide),
      hreg₄ 11 (Or.inr (by decide)) (by decide) (by decide),
      hreg₃ 11 (Or.inr (by decide)) (by decide)]
    simp [s₂, s₁, hr11]
  have hc_w : c_cnt < 2 ^ w := by omega
  let s₆ := s₅.setReg 11 (c_cnt + 1)
  have hex₆ : Exec w (.assign 11 (.op .add (.reg 11) (.const 1))) s₅ s₆ 4 :=
    .assign (by simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr11_5, hc_w, hw1, hc_cnt_w])
  simp only [List.length_append, List.length_cons] at ht₄ ht₅
  refine ⟨s₆, 2 + (2 + (t₃ + (t₄ + (t₅ + 4)))),
    .seq hex₁ (.seq hex₂ (.seq hex₃ (.seq hex₄ (.seq hex₅ hex₆)))),
    by omega,
    by simpa [s₆, List.append_assoc] using harr24_5,
    by simp [s₆],
    fun a ha24 ha28 ha29 => by
      simp only [s₆, State.setReg_arrs]
      rw [harr₅ a ha24 ha28 ha29, harr₄ a ha24 ha28 ha29, harr₃ a ha24 ha29]
      simp [s₂, s₁],
    fun r hr h11 => by
      have hr3 : r ≠ 3 := by omega
      have hr4 : r ≠ 4 := by omega
      have hr58 : r < 5 ∨ 5 + 3 < r := by omega
      simp only [s₆, State.setReg_regs_ne _ _ h11]
      rw [hreg₅ r hr58 hr3 hr4, hreg₄ r hr58 hr3 hr4, hreg₃ r hr58 hr3]
      simp [s₂, s₁, State.setReg, hr3, hr4]⟩

/-- Append the flat dividing subwall encoding `arr 26` to `arr 25` and increment `reg 12`. -/
def recordFlatSubwallProg : Cmd :=
  .seq (.assign 3 (.len 25))
    (.seq (.assign 4 (.len 26))
      (.seq (appendArrProg 25 26 29 3 4 5)
        (.assign 12 (.op .add (.reg 12) (.const 1)))))

theorem recordFlatSubwallProg_exec {w h n : ℕ}
    {G' : MultiDigraph n} (W_sub : WallOfHeight h G')
    (L_prev : List ℕ) (f_cnt : ℕ)
    (hprev_w : ∀ x ∈ L_prev, x < 2 ^ w)
    (hW_w : ∀ x ∈ W_sub.encList, x < 2 ^ w)
    (hw1 : 1 < 2 ^ w)
    (htot_w : L_prev.length + W_sub.encList.length < 2 ^ w)
    (hf_cnt_w : f_cnt + 1 < 2 ^ w)
    {s : State}
    (harr25 : s.arrs 25 = L_prev)
    (harr26 : s.arrs 26 = W_sub.encList)
    (hr12 : s.regs 12 = f_cnt) :
    ∃ s' t,
      Exec w recordFlatSubwallProg s s' t ∧
      t ≤ 44 + 34 * L_prev.length + 18 * W_sub.encList.length ∧
      s'.arrs 25 = L_prev ++ W_sub.encList ∧
      s'.regs 12 = f_cnt + 1 ∧
      (∀ a : Arr, a ≠ 25 → a ≠ 29 → s'.arrs a = s.arrs a) ∧
      (∀ r : ℕ, (r < 3 ∨ 8 < r) → r ≠ 12 → s'.regs r = s.regs r) := by
  have hlen_prev_w : L_prev.length < 2 ^ w := by omega
  have hlen_W_w : W_sub.encList.length < 2 ^ w := by omega
  let s₁ := s.setReg 3 L_prev.length
  have hex₁ : Exec w (.assign 3 (.len 25)) s s₁ 2 :=
    .assign (by simp [Expr.eval, checkWord, harr25, hlen_prev_w])
  let s₂ := s₁.setReg 4 W_sub.encList.length
  have hex₂ : Exec w (.assign 4 (.len 26)) s₁ s₂ 2 :=
    .assign (by simp [s₁, Expr.eval, checkWord, harr26, hlen_W_w])
  rcases appendArrProg_exec 25 26 29 3 4 5
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      L_prev W_sub.encList hprev_w hW_w hw1 htot_w (s := s₂)
      harr25 harr26 (by simp [s₂, s₁]) (by simp [s₂]) with
    ⟨s₃, t₃, hex₃, ht₃, harr25_3, _, harr₃, hreg₃⟩
  have hr12_3 : s₃.regs 12 = f_cnt := by
    rw [hreg₃ 12 (Or.inr (by decide)) (by decide)]
    simp [s₂, s₁, hr12]
  have hf_w : f_cnt < 2 ^ w := by omega
  let s₄ := s₃.setReg 12 (f_cnt + 1)
  have hex₄ : Exec w (.assign 12 (.op .add (.reg 12) (.const 1))) s₃ s₄ 4 :=
    .assign (by simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr12_3, hf_w, hw1, hf_cnt_w])
  refine ⟨s₄, 2 + (2 + (t₃ + 4)),
    .seq hex₁ (.seq hex₂ (.seq hex₃ hex₄)),
    by omega,
    by simpa [s₄] using harr25_3,
    by simp [s₄],
    fun a ha25 ha29 => by
      simp only [s₄, State.setReg_arrs]
      rw [harr₃ a ha25 ha29]
      simp [s₂, s₁],
    fun r hr h12 => by
      have hr3 : r ≠ 3 := by omega
      have hr4 : r ≠ 4 := by omega
      have hr58 : r < 5 ∨ 5 + 3 < r := by omega
      simp only [s₄, State.setReg_regs_ne _ _ h12]
      rw [hreg₃ r hr58 hr3]
      simp [s₂, s₁, State.setReg, hr3, hr4]⟩

/-- Compute the compass of `W_sub`, restrict `G'` (`arrs 20..22`) to `W_sub.compassFinset`
(`arr 33`) into `arrs 30..32`, load the four corners `(c0, c2, c1, c3)` of `W_sub` from `arr 26`
into `regs 31..34`, and run `shiloachProg`. -/
def runShiloachOnCompassProg (h : ℕ) (h2 : 2 ≤ h) (shiloachProg : Cmd) : Cmd :=
  .seq testDividingAndCompassProg
    (.seq (restrictGraphProg 20 21 22 33 30 31 32 1 2 3 4 5 6 7 8 9)
      (.seq (loadShiloachInputsProg h h2)
        shiloachProg))

theorem runShiloachOnCompassProg_exec {w n h h_W cap C_sh c_sh : ℕ}
    {shiloachProg : Cmd}
    (hShiloachProg :
      ∀ (N : ℕ) (G : SimpleGraph (Fin N)) [DecidableRel G.Adj]
        (lists : Fin N → List ℕ) (s₁ t₁ s₂ t₂ : Fin N),
        s₁ ≠ t₁ → s₁ ≠ s₂ → s₁ ≠ t₂ → t₁ ≠ s₂ → t₁ ≠ t₂ → s₂ ≠ t₂ →
        ∀ (w : ℕ), wordSize c_sh ((N + 1) * (G.edgeFinset.card + N + 1)) ≤ w →
        ∀ (s : State),
          IsAdjList G 30 31 32 lists s →
          (s.arrs 32).length < 2 ^ w →
          s.regs 30 = N →
          s.regs 31 = s₁.1 →
          s.regs 32 = t₁.1 →
          s.regs 33 = s₂.1 →
          s.regs 34 = t₂.1 →
          ∃ (s' : State) (t : ℕ),
            Exec w shiloachProg s s' t ∧
            t ≤ C_sh * (N + 1) * (G.edgeFinset.card + N + 1) ∧
            (∀ r < 30, s'.regs r = s.regs r) ∧
            (∀ a < 33, s'.arrs a = s.arrs a) ∧
            ((s'.regs 35 = 1 ∧
                ∃ (P₁ : G.Walk s₁ t₁) (P₂ : G.Walk s₂ t₂),
                  P₁.IsPath ∧ P₂.IsPath ∧
                  List.Disjoint P₁.support P₂.support ∧
                  s'.arrs 33 = P₁.support.map Fin.val ∧
                  s'.arrs 34 = P₂.support.map Fin.val) ∨
              (s'.regs 35 = 0 ∧
                ∀ (P₁ : G.Walk s₁ t₁) (P₂ : G.Walk s₂ t₂),
                  P₁.IsPath → P₂.IsPath → ¬ List.Disjoint P₁.support P₂.support)))
    (G' : MultiDigraph n) (lists' : Fin n → List ℕ)
    (W : WallOfHeight h_W G') (W_sub : WallOfHeight h G')
    (h2 : 2 ≤ h) (he : Even h) (h2_W : 2 ≤ h_W) (he_W : Even h_W)
    (hW : W.IsValid) (hsub : W_sub.IsSubwallOf W)
    (hw2 : 2 < 2 ^ w) (hn_w : n < 2 ^ w)
    (hc_w : 3 + elemWallNumVerts h < 2 ^ w)
    (hcap_w : cap < 2 ^ w)
    (hcap_bound : totalAdjEntries lists' ≤ cap)
    (hw_sh : wordSize c_sh ((n + 1) * (G'.toSimpleGraph.edgeFinset.card + n + 1)) ≤ w)
    {s : State}
    (hadj : IsAdjList G'.toSimpleGraph 20 21 22 lists' s)
    (hent_w : (s.arrs 22).length < 2 ^ w)
    (hHV : IsBitSet W.vertexFinset 11 s)
    (hHjV : IsBitSet W_sub.vertexFinset 27 s)
    (hperim : IsBitSet W_sub.perimeterFinset 28 s)
    (harr26 : s.arrs 26 = W_sub.encList)
    (hr1 : s.regs 1 = n)
    (hr2 : s.regs 2 = cap)
    (hr14 : s.regs 14 = (W_sub.seedVert h2).1) :
    ∃ s' t,
      Exec w (runShiloachOnCompassProg h h2 shiloachProg) s s' t ∧
      t ≤ 75 + 143 * n + 2 * cap + 76 * totalAdjEntries lists' +
        C_sh * (n + 1) * (G'.toSimpleGraph.edgeFinset.card + n + 1) ∧
      (∀ a : ℕ, a < 29 → s'.arrs a = s.arrs a) ∧
      (∀ r : ℕ, r < 3 ∨ (10 < r ∧ r < 30) → s'.regs r = s.regs r) ∧
      ((s'.regs 35 = 1 ∧
          ∃ C : CrossedSubwallData h2 W_sub,
            s'.arrs 33 = C.P₁.map Fin.val ∧
            s'.arrs 34 = C.P₂.map Fin.val) ∨
        (s'.regs 35 = 0 ∧ W_sub.IsFlatWall h2)) := by
  have hw1 : 1 < 2 ^ w := by omega
  have hW_sub : W_sub.IsValid := W.isValid_of_isSubwallOf hW hsub
  -- 1. testDividingAndCompassProg
  rcases testDividingAndCompassWall_exec G' lists' W W_sub
      h2_W he_W hW hsub cap hw2 hn_w hcap_w hcap_bound
      hadj hent_w hHV hHjV hperim hr1 hr2 hr14 with
    ⟨s₁, t₁, hex₁, ht₁, hcomp₁, _, harr₁, hreg₁⟩
  -- 2. restrictGraphProg 20 21 22 33 30 31 32 1 2 3 4 5 6 7 8 9
  let Y := W_sub.compassFinset
  have htot_Y_le : totalAdjEntries (restrictListFamily Y lists') ≤ totalAdjEntries lists' := by
    unfold totalAdjEntries restrictListFamily restrictList
    apply Finset.sum_le_sum
    intro u _
    exact restrictListUpTo_length_le Y u (lists' u) (lists' u).length
  have hcards_le : 2 * (edgesInSet G'.toSimpleGraph Y).card ≤ cap := by
    rw [← totalAdjEntries_restrictListFamily hadj.2 Y]
    exact le_trans htot_Y_le hcap_bound
  have hadj₁ : IsAdjList G'.toSimpleGraph 20 21 22 lists' s₁ :=
    hadj.of_arrs_eq
      (harr₁ 20 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
      (harr₁ 21 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
      (harr₁ 22 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
  have hent₁_w : (s₁.arrs 22).length < 2 ^ w := by
    rw [harr₁ 22 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
    exact hent_w
  rcases restrictGraphProg_exec G'.toSimpleGraph lists' Y cap
      20 21 22 33 30 31 32 1 2 3 4 5 6 7 8 9
      (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide)
      hw1 hn_w hcap_w hcards_le
      hadj₁ hent₁_w hcomp₁
      (by rw [hreg₁ 1 (Or.inl (by decide)), hr1])
      (by rw [hreg₁ 2 (Or.inl (by decide)), hr2]) with
    ⟨s₂, t₂, hex₂, ht₂, hadj_Y₂, hent_Y₂, _, harr₂, hreg₂⟩
  -- 3. loadShiloachInputsProg h h2
  have harr26_2 : s₂.arrs 26 = W_sub.encList := by
    rw [harr₂ 26 (by decide) (by decide) (by decide),
      harr₁ 26 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
      harr26]
  have hr1_2 : s₂.regs 1 = n := by
    rw [hreg₂ 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
      hreg₁ 1 (Or.inl (by decide)), hr1]
  rcases loadShiloachInputsProg_exec h2 W_sub hn_w hc_w harr26_2 hr1_2 with
    ⟨s₃, t₃, hex₃, ht₃, hr30_3, hr31_3, hr32_3, hr33_3, hr34_3, harr₃, hreg₃⟩
  -- 4. shiloachProg
  have hadj_Y₃ : IsAdjList (restrictGraph G'.toSimpleGraph Y) 30 31 32
      (restrictListFamily Y lists') s₃ :=
    hadj_Y₂.of_arrs_eq (harr₃ 30) (harr₃ 31) (harr₃ 32)
  have hent_Y₃_w : (s₃.arrs 32).length < 2 ^ w := by
    rw [harr₃ 32, hent_Y₂]; exact hcap_w
  have he_le : (restrictGraph G'.toSimpleGraph Y).edgeFinset.card ≤
      G'.toSimpleGraph.edgeFinset.card := by
    rw [card_edgeFinset_restrictGraph]
    exact card_edgesInSet_le_card_edgeFinset G'.toSimpleGraph Y
  have hw_sh_Y : wordSize c_sh
      ((n + 1) * ((restrictGraph G'.toSimpleGraph Y).edgeFinset.card + n + 1)) ≤ w := by
    refine le_trans (wordSize_mono_right c_sh ?_) hw_sh
    exact Nat.mul_le_mul_left (n + 1) (by omega)
  have hne02 : W_sub.cornerVert h2 0 ≠ W_sub.cornerVert h2 2 :=
    W_sub.cornerVert_ne_of_ne h2 hW_sub (by decide)
  have hne01 : W_sub.cornerVert h2 0 ≠ W_sub.cornerVert h2 1 :=
    W_sub.cornerVert_ne_of_ne h2 hW_sub (by decide)
  have hne03 : W_sub.cornerVert h2 0 ≠ W_sub.cornerVert h2 3 :=
    W_sub.cornerVert_ne_of_ne h2 hW_sub (by decide)
  have hne21 : W_sub.cornerVert h2 2 ≠ W_sub.cornerVert h2 1 :=
    W_sub.cornerVert_ne_of_ne h2 hW_sub (by decide)
  have hne23 : W_sub.cornerVert h2 2 ≠ W_sub.cornerVert h2 3 :=
    W_sub.cornerVert_ne_of_ne h2 hW_sub (by decide)
  have hne13 : W_sub.cornerVert h2 1 ≠ W_sub.cornerVert h2 3 :=
    W_sub.cornerVert_ne_of_ne h2 hW_sub (by decide)
  rcases hShiloachProg n (restrictGraph G'.toSimpleGraph Y) (restrictListFamily Y lists')
      (W_sub.cornerVert h2 0) (W_sub.cornerVert h2 2)
      (W_sub.cornerVert h2 1) (W_sub.cornerVert h2 3)
      hne02 hne01 hne03 hne21 hne23 hne13
      w hw_sh_Y s₃ hadj_Y₃ hent_Y₃_w hr30_3 hr31_3 hr32_3 hr33_3 hr34_3 with
    ⟨s₄, t₄, hex₄, ht₄, hreg₄, harr₄, hout₄⟩
  have ht₄_b : t₄ ≤ C_sh * (n + 1) * (G'.toSimpleGraph.edgeFinset.card + n + 1) := by
    refine le_trans ht₄ ?_
    exact Nat.mul_le_mul_left (C_sh * (n + 1)) (by omega)
  refine ⟨s₄, t₁ + (t₂ + (t₃ + t₄)),
    .seq hex₁ (.seq hex₂ (.seq hex₃ hex₄)),
    by omega,
    fun a ha => by
      rw [harr₄ a (by change (a : ℕ) < 33; omega), harr₃ a,
        harr₂ a (ne_arr_of_ne (by omega)) (ne_arr_of_ne (by omega)) (ne_arr_of_ne (by omega)),
        harr₁ a (ne_arr_of_ne (by omega)) (ne_arr_of_ne (by omega)) (ne_arr_of_ne (by omega))
          (ne_arr_of_ne (by omega)) (ne_arr_of_ne (by omega)) (ne_arr_of_ne (by omega))
          (ne_arr_of_ne (by omega))],
    fun r hr => by
      have hr30 : r < 30 := by omega
      rw [hreg₄ r hr30, hreg₃ r (Or.inl hr30)]
      have hr3 : r ≠ 3 := by omega
      have hr4 : r ≠ 4 := by omega
      have hr5 : r ≠ 5 := by omega
      have hr6 : r ≠ 6 := by omega
      have hr7 : r ≠ 7 := by omega
      have hr8 : r ≠ 8 := by omega
      have hr9 : r ≠ 9 := by omega
      rw [hreg₂ r hr3 hr4 hr5 hr6 hr7 hr8 hr9, hreg₁ r (by omega)],
    ?_⟩
  rcases hout₄ with ⟨hr35_4, P₁, P₂, hP₁, hP₂, hdisj, harr33_4, harr34_4⟩ | ⟨hr35_4, hno⟩
  · left
    obtain ⟨hcr, hmem₁, hmem₂⟩ :=
      W_sub.isCrossOverWall_of_restrictGraph_paths h2 he hW_sub hP₁ hP₂ hdisj
    exact ⟨hr35_4, ⟨P₁.support, P₂.support, hcr, hmem₁, hmem₂⟩, harr33_4, harr34_4⟩
  · right
    exact ⟨hr35_4, W_sub.isFlatWall_of_no_restrictGraph_paths h2 hW_sub hno⟩


end GraphMinor.Compute
