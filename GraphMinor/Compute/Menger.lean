module

public import GraphMinor.Compute.MengerAugment

/-!
# End-to-End Menger Disjoint Paths Algorithm in the Word RAM Model

This file completes the Word RAM implementation and verification of Menger's vertex-disjoint
`A`–`B` paths algorithm (`disjointPaths_computesInTime`), joining:
1. Flat input parsing (`parseGraphProg` and `readSliceProg`) from `inArr` in `O(n + m)` time.
2. Up to `k` augmenting rounds (`mengerLoopRegProg`), each running residual BFS and either
   augmenting the `A`–`B` path system (`augmentTraceRegProg`) or terminating early when no
   `b ∈ B` is reachable in the residual graph.
3. Output serialization to `outArr` (`writePathSystemOutProg` / `writeResCutOutProg`) and pure
   decoding (`decDisjointPathsOut`) into either `k` pairwise vertex-disjoint simple `A`–`B` paths
   in `G` or an `A`–`B` vertex separator of size `< k`.
-/

@[expose] public section

namespace GraphMinor.Compute

/-! ### Section 1: Initializing the Empty Path System (`initPathSystemRegProg`) -/

/-- Initialize `(a_used, a_pred, a_succ) = (a_base, a_base + 1, a_base + 2)` to represent the empty
path system (`used = 0`, `pred = n`, `succ = n`). -/
def initPathSystemRegBody (a_base : Arr) (r_base : Reg) : Cmd :=
  .seq (.write (a_base + 1) (.reg (r_base + 3)) (.reg (r_base + 12)))
    (.write (a_base + 2) (.reg (r_base + 3)) (.reg (r_base + 12)))

def initPathSystemRegProg (a_base : Arr) (r_base : Reg) : Cmd :=
  .seq (.alloc a_base (.reg (r_base + 12)))
    (.seq (.alloc (a_base + 1) (.reg (r_base + 12)))
      (.seq (.alloc (a_base + 2) (.reg (r_base + 12)))
        (.seq (.assign (r_base + 3) (.const 0))
          (forUp (r_base + 3) (.reg (r_base + 12)) (initPathSystemRegBody a_base r_base)))))

theorem initPathSystemRegLoop_exec {w n k_goal : ℕ} (a_base r_base : ℕ)
    (hw : 1 < 2 ^ w) (hn_w : n < 2 ^ w)
    (rem k : ℕ) (hrem : k + rem = n) {s : State}
    (hconst : ConstRegs n k_goal r_base s)
    (hused : s.arrs a_base = List.replicate n 0)
    (hpred : s.arrs (a_base + 1) = List.replicate k n ++ List.replicate (n - k) 0)
    (hsucc : s.arrs (a_base + 2) = List.replicate k n ++ List.replicate (n - k) 0)
    (hrk : s.regs (r_base + 3) = k) :
    ∃ s' t,
      Exec w (forUp (r_base + 3) (.reg (r_base + 12)) (initPathSystemRegBody a_base r_base)) s s' t ∧
      t ≤ 3 + 13 * rem ∧
      ConstRegs n k_goal r_base s' ∧
      s'.arrs a_base = List.replicate n 0 ∧
      s'.arrs (a_base + 1) = List.replicate n n ∧
      s'.arrs (a_base + 2) = List.replicate n n ∧
      (∀ a < a_base, s'.arrs a = s.arrs a) ∧
      (∀ r ≥ r_base + 12, s'.regs r = s.regs r) := by
  have h0_w : 0 < 2 ^ w := by omega
  induction rem generalizing k s with
  | zero =>
    have hk_eq : k = n := by omega
    rw [hk_eq] at hrk hpred hsucc
    have hcond : (Expr.op .lt (.reg (r_base + 3)) (.reg (r_base + 12))).eval w s = some 0 := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hrk, hconst.1, hn_w, h0_w]
    refine ⟨s, 3, .while_false hcond, by omega, hconst, hused, ?_, ?_,
      fun _ _ => rfl, fun _ _ => rfl⟩
    · simpa using hpred
    · simpa using hsucc
  | succ rem ih =>
    have hk_lt : k < n := by omega
    have hk_w : k < 2 ^ w := by omega
    have hcond : (Expr.op .lt (.reg (r_base + 3)) (.reg (r_base + 12))).eval w s = some 1 := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hrk, hconst.1, hk_w, hn_w, hk_lt, hw]
    have hpred_len : (s.arrs (a_base + 1)).length = n := by
      rw [hpred, List.length_append, List.length_replicate, List.length_replicate]; omega
    have hsucc_len : (s.arrs (a_base + 2)).length = n := by
      rw [hsucc, List.length_append, List.length_replicate, List.length_replicate]; omega
    let s₁ := s.writeArr (a_base + 1) k n
    have hex₁ : Exec w (.write (a_base + 1) (.reg (r_base + 3)) (.reg (r_base + 12))) s s₁ 3 :=
      .write (by simp [Expr.eval, checkWord, hrk, hk_w])
        (by simp [Expr.eval, checkWord, hconst.1, hn_w]) (by rw [hpred_len]; exact hk_lt)
    let s₂ := s₁.writeArr (a_base + 2) k n
    have hex₂ : Exec w (.write (a_base + 2) (.reg (r_base + 3)) (.reg (r_base + 12))) s₁ s₂ 3 :=
      .write (by simp [s₁, Expr.eval, checkWord, hrk, hk_w])
        (by simp [s₁, Expr.eval, checkWord, hconst.1, hn_w])
        (by simp [s₁, hsucc_len, hk_lt])
    let s₃ := s₂.setReg (r_base + 3) (k + 1)
    have hex_inc : Exec w (.assign (r_base + 3) (.op .add (.reg (r_base + 3)) (.const 1))) s₂ s₃ 4 :=
      .assign (by
        simp [s₂, s₁, Expr.eval, BinOp.eval, BinOp.raw, checkWord, hrk, hk_w, hw,
          show k + 1 < 2 ^ w by omega])
    have hrep_step : (List.replicate k n ++ List.replicate (n - k) 0).set k n =
        List.replicate (k + 1) n ++ List.replicate (n - (k + 1)) 0 := by
      rw [List.set_append_right _ _ (by simp)]
      have hsub0 : k - (List.replicate k n).length = 0 := by simp
      have hrep : n - k = (n - (k + 1)) + 1 := by omega
      rw [hsub0, hrep, List.replicate_succ, List.set_cons_zero]
      rw [List.replicate_add, List.replicate_one, List.append_assoc, List.singleton_append]
    have hpred₃ : s₃.arrs (a_base + 1) =
        List.replicate (k + 1) n ++ List.replicate (n - (k + 1)) 0 := by
      simp [s₃, s₂, s₁, hpred, hrep_step]
    have hsucc₃ : s₃.arrs (a_base + 2) =
        List.replicate (k + 1) n ++ List.replicate (n - (k + 1)) 0 := by
      simp [s₃, s₂, s₁, hsucc, hrep_step]
    have hused₃ : s₃.arrs a_base = List.replicate n 0 := by
      simp [s₃, s₂, s₁, hused]
    have hreg₃ : ∀ r ≥ r_base + 12, s₃.regs r = s.regs r := by
      intro r hr
      simp [s₃, s₂, s₁, State.setReg, show (r : Reg) ≠ r_base + 3 by omega]
    have hconst₃ : ConstRegs n k_goal r_base s₃ :=
      hconst.of_regs_eq (hreg₃ _ (by omega)) (hreg₃ _ (by omega)) (hreg₃ _ (by omega))
    rcases ih (k + 1) (by omega) hconst₃ hused₃ hpred₃ hsucc₃ (by simp [s₃]) with
      ⟨s₄, t₄, hex₄, ht₄, hconst₄, hused₄, hpred₄, hsucc₄, harr₄, hreg₄⟩
    refine ⟨s₄, 3 + ((3 + 3) + 4) + t₄,
      .while_true hcond (by omega) (.seq (.seq hex₁ hex₂) hex_inc) hex₄,
      by omega, hconst₄, hused₄, hpred₄, hsucc₄,
      fun a ha => by
        rw [harr₄ a ha]
        have hne2 : (a : Arr) ≠ a_base + 2 := by omega
        have hne1 : (a : Arr) ≠ a_base + 1 := by omega
        simp [s₃, s₂, s₁, hne2, hne1],
      fun r hr => by rw [hreg₄ r hr, hreg₃ r hr]⟩

theorem initPathSystemRegProg_exec {w n k_goal : ℕ} (G : SimpleGraph (Fin n))
    (A B : Finset (Fin n)) (a_base r_base : ℕ)
    (hw : 1 < 2 ^ w) (hn_w : n < 2 ^ w)
    {s : State}
    (hconst : ConstRegs n k_goal r_base s) :
    ∃ s' t,
      Exec w (initPathSystemRegProg a_base r_base) s s' t ∧
      t ≤ 16 * n + 10 ∧
      ConstRegs n k_goal r_base s' ∧
      PathSystemState G A B a_base (fun _ => 0) (fun _ => n) (fun _ => n) s' ∧
      (pathStarts (n := n) (fun _ => 0) (fun _ => n)).card = 0 ∧
      (∀ a < a_base, s'.arrs a = s.arrs a) ∧
      (∀ r ≥ r_base + 12, s'.regs r = s.regs r) := by
  have h0_w : 0 < 2 ^ w := by omega
  have heval_n : (Expr.reg (r_base + 12)).eval w s = some n := by
    simp [Expr.eval, checkWord, hconst.1, hn_w]
  let s₁ := s.setArr a_base (List.replicate n 0)
  have hex₁ : Exec w (.alloc a_base (.reg (r_base + 12))) s s₁ (1 + n) := .alloc heval_n
  let s₂ := s₁.setArr (a_base + 1) (List.replicate n 0)
  have hex₂ : Exec w (.alloc (a_base + 1) (.reg (r_base + 12))) s₁ s₂ (1 + n) :=
    .alloc (by simp [s₁, Expr.eval, checkWord, hconst.1, hn_w])
  let s₃ := s₂.setArr (a_base + 2) (List.replicate n 0)
  have hex₃ : Exec w (.alloc (a_base + 2) (.reg (r_base + 12))) s₂ s₃ (1 + n) :=
    .alloc (by simp [s₂, s₁, Expr.eval, checkWord, hconst.1, hn_w])
  let s₄ := s₃.setReg (r_base + 3) 0
  have hex₄ : Exec w (.assign (r_base + 3) (.const 0)) s₃ s₄ 2 :=
    .assign (by simp [Expr.eval, checkWord, h0_w])
  have hreg₄ : ∀ r ≥ r_base + 12, s₄.regs r = s.regs r := by
    intro r hr
    simp [s₄, s₃, s₂, s₁, State.setReg, show (r : Reg) ≠ r_base + 3 by omega]
  have hconst₄ : ConstRegs n k_goal r_base s₄ :=
    hconst.of_regs_eq (hreg₄ _ (by omega)) (hreg₄ _ (by omega)) (hreg₄ _ (by omega))
  have hused₄ : s₄.arrs a_base = List.replicate n 0 := by
    simp [s₄, s₃, s₂, s₁]
  have hpred₄ : s₄.arrs (a_base + 1) = List.replicate 0 n ++ List.replicate (n - 0) 0 := by
    simp [s₄, s₃, s₂]
  have hsucc₄ : s₄.arrs (a_base + 2) = List.replicate 0 n ++ List.replicate (n - 0) 0 := by
    simp [s₄, s₃]
  rcases initPathSystemRegLoop_exec a_base r_base hw hn_w n 0 (by omega)
      hconst₄ hused₄ hpred₄ hsucc₄ (by simp [s₄]) with
    ⟨s₅, t₅, hex₅, ht₅, hconst₅, hused₅, hpred₅, hsucc₅, harr₅, hreg₅⟩
  have harrs₅ : IsPathSystemArrs (n := n) a_base (fun _ => 0) (fun _ => n) (fun _ => n) s₅ := by
    refine ⟨by simp [hused₅], by simp [hpred₅], by simp [hsucc₅],
      fun u => by simp [hused₅], fun u => by simp [hpred₅], fun u => by simp [hsucc₅]⟩
  have hstarts0 : pathStarts (n := n) (fun _ => 0) (fun _ => n) = ∅ := by
    ext u
    simp
  refine ⟨s₅, (1 + n) + ((1 + n) + ((1 + n) + (2 + t₅))),
    .seq hex₁ (.seq hex₂ (.seq hex₃ (.seq hex₄ hex₅))),
    by omega, hconst₅, ⟨IsValidPathSystem.empty G A B, harrs₅⟩,
    by simp [hstarts0],
    fun a ha => by
      rw [harr₅ a ha]
      have hne2 : (a : Arr) ≠ a_base + 2 := by omega
      have hne1 : (a : Arr) ≠ a_base + 1 := by omega
      have hne0 : (a : Arr) ≠ a_base := by omega
      simp [s₄, s₃, s₂, s₁, hne2, hne1, hne0],
    fun r hr => by rw [hreg₅ r hr, hreg₄ r hr]⟩

/-! ### Section 2: Outer Augmentation Loop (`mengerLoopRegProg`) -/

/-- Predicate stating that `s.arrs a_vis` is the `0`/`1` visited indicator array of length `2 * n`
for `items : List ℕ`. -/
def IsResVisArr (n : ℕ) (a_vis : Arr) (items : List ℕ) (s : State) : Prop :=
  ∃ (hvis_len : (s.arrs a_vis).length = 2 * n),
    ∀ x : ℕ, (hx : x < 2 * n) →
      (((s.arrs a_vis)[x]'(by rw [hvis_len]; exact hx) ≠ 0 ↔ x ∈ items) ∧
        (s.arrs a_vis)[x]'(by rw [hvis_len]; exact hx) ≤ 1)

theorem IsResVisArr.of_arr_eq {n : ℕ} {a_vis : Arr} {items : List ℕ} {s s' : State}
    (h : IsResVisArr n a_vis items s) (heq : s'.arrs a_vis = s.arrs a_vis) :
    IsResVisArr n a_vis items s' := by
  rcases h with ⟨hlen, hiff⟩
  exact ⟨by rw [heq, hlen], fun x hx => by simp only [heq]; exact hiff x hx⟩

/-- Single round of Menger augmentation inside the `while r_round < k_goal` loop:
1. Allocates `a_q = a_base + 5` of size `2 * n` and seeds residual BFS from `A` (`initSourcesRegProg`).
2. Runs residual BFS (`resBfsLoopRegProg`).
3. Searches for a reached target `b ∈ B` (`findTargetRegProg`).
4. If `r_base + 11 < r_base + 12` (`r_targ < n`), augments the path system (`augmentTraceRegProg`)
   and increments `r_base + 15` (`r_round := r_round + 1`); otherwise sets `r_base + 16 := 0`
   (`r_ok := 0`) and `r_base + 15 := r_base + 14` (`r_round := k_goal`) to exit the loop. -/
def augmentRoundRegBody (a_start a_end a_entries a_A a_B a_base : Arr) (r_base : Reg) : Cmd :=
  .seq (.alloc (a_base + 5) (.reg (r_base + 13)))
    (.seq (initSourcesRegProg a_A a_base r_base)
      (.seq (resBfsLoopRegProg a_start a_end a_entries a_base r_base)
        (.seq (findTargetRegProg a_B a_base r_base)
          (.ite (.op .lt (.reg (r_base + 11)) (.reg (r_base + 12)))
            (.seq (augmentTraceRegProg a_A a_base r_base)
              (.assign (r_base + 15) (.op .add (.reg (r_base + 15)) (.const 1))))
            (.seq (.assign (r_base + 16) (.const 0))
              (.assign (r_base + 15) (.reg (r_base + 14))))))))

/-- Outer loop running at most `k_goal` augmenting rounds. -/
def mengerLoopRegProg (a_start a_end a_entries a_A a_B a_base : Arr) (r_base : Reg) : Cmd :=
  .while (.op .lt (.reg (r_base + 15)) (.reg (r_base + 14)))
    (augmentRoundRegBody a_start a_end a_entries a_A a_B a_base r_base)

theorem mengerLoopRegProg_exec {w n k_goal : ℕ} (G : SimpleGraph (Fin n))
    (lists : Fin n → List ℕ) (A B : Finset (Fin n))
    (a_start a_end a_entries a_A a_B a_base : ℕ) (r_base : ℕ)
    (ha_st : a_start < a_base) (ha_en : a_end < a_base) (ha_ent : a_entries < a_base)
    (ha_A : a_A < a_base) (ha_B : a_B < a_base)
    (hw : 1 < 2 ^ w) (h2n_w : 2 * n < 2 ^ w) (hk_w : k_goal < 2 ^ w)
    (rem round : ℕ) (hrem : round + rem = k_goal)
    {used pred succ : Fin n → ℕ} {s : State}
    (hconst : ConstRegs n k_goal r_base s)
    (hadj : IsAdjList G a_start a_end a_entries lists s)
    (hent_w : (s.arrs a_entries).length < 2 ^ w)
    (hA_bit : IsBitSet A a_A s)
    (hB_bit : IsBitSet B a_B s)
    (hsys : PathSystemState G A B a_base used pred succ s)
    (hcard : (pathStarts used pred).card = round)
    (hr_round : s.regs (r_base + 15) = round)
    (hr_ok : s.regs (r_base + 16) = 1) :
    ∃ s' t,
      Exec w (mengerLoopRegProg a_start a_end a_entries a_A a_B a_base r_base) s s' t ∧
      t ≤ 3 + rem * (65 + 264 * n + 31 * totalAdjEntries lists) ∧
      ConstRegs n k_goal r_base s' ∧
      (∀ a < a_base, s'.arrs a = s.arrs a) ∧
      (∀ r ≥ r_base + 17, s'.regs r = s.regs r) ∧
      ((s'.regs (r_base + 16) = 1 ∧
        ∃ used' pred' succ',
          PathSystemState G A B a_base used' pred' succ' s' ∧
          (pathStarts used' pred').card = k_goal) ∨
       (s'.regs (r_base + 16) = 0 ∧
        ∃ used' pred' succ' items,
          PathSystemState G A B a_base used' pred' succ' s' ∧
          (pathStarts used' pred').card < k_goal ∧
          IsResVisArr n (a_base + 3) items s' ∧
          ResParentInv G A used' pred' succ' (a_base + 4) items s' ∧
          IsResPopClosed G used' pred' succ' items items.length ∧
          (∀ a ∈ A, a.1 ∈ items) ∧
          (∀ b ∈ B, b.1 + n ∉ items))) := by
  have h0_w : 0 < 2 ^ w := by omega
  have hn_w : n < 2 ^ w := by omega
  induction rem generalizing round used pred succ s with
  | zero =>
    have hround_eq : round = k_goal := by omega
    subst hround_eq
    have hcond : (Expr.op .lt (.reg (r_base + 15)) (.reg (r_base + 14))).eval w s = some 0 := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr_round, hconst.2.2, hk_w, h0_w]
    exact ⟨s, 3, .while_false hcond, by omega, hconst, fun _ _ => rfl, fun _ _ => rfl,
      Or.inl ⟨hr_ok, used, pred, succ, hsys, hcard⟩⟩
  | succ rem ih =>
    have hround_lt : round < k_goal := by omega
    have hround_w : round < 2 ^ w := by omega
    have hcond : (Expr.op .lt (.reg (r_base + 15)) (.reg (r_base + 14))).eval w s = some 1 := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr_round, hconst.2.2,
        hround_w, hk_w, hround_lt, hw]
    -- 0. alloc (a_base + 5) (.reg (r_base + 13))
    let s₀ := s.setArr (a_base + 5) (List.replicate (2 * n) 0)
    have hex₀ : Exec w (.alloc (a_base + 5) (.reg (r_base + 13))) s s₀ (1 + 2 * n) :=
      .alloc (by simp [Expr.eval, checkWord, hconst.2.1, h2n_w])
    have harr₀_lt : ∀ a < a_base + 3, s₀.arrs a = s.arrs a := by
      intro a ha
      have hne5 : (a : Arr) ≠ a_base + 5 := by omega
      simp [s₀, hne5]
    have hconst₀ : ConstRegs n k_goal r_base s₀ := hconst.of_regs_eq rfl rfl rfl
    have hA_bit₀ : IsBitSet A a_A s₀ := hA_bit.of_arr_eq (harr₀_lt a_A (by omega))
    have hsys₀ : PathSystemState G A B a_base used pred succ s₀ :=
      hsys.of_arrs_eq (harr₀_lt a_base (by omega))
        (harr₀_lt (a_base + 1) (by omega)) (harr₀_lt (a_base + 2) (by omega))
    -- 1. initSourcesRegProg
    rcases initSourcesRegProg_exec G A B used pred succ a_A a_base r_base ha_A hw h2n_w
        hconst₀ hA_bit₀ (by simp [s₀]) hsys₀ with
      ⟨s₁, t₁, items₀, hex₁, ht₁, hconst₁, hsys₁, hq₁, hpar₁, hinit₁, harr₁, hreg₁⟩
    have hadj₁ : IsAdjList G a_start a_end a_entries lists s₁ :=
      hadj.of_arrs_eq
        (by rw [harr₁ a_start (by omega), harr₀_lt a_start (by omega)])
        (by rw [harr₁ a_end (by omega), harr₀_lt a_end (by omega)])
        (by rw [harr₁ a_entries (by omega), harr₀_lt a_entries (by omega)])
    have hent₁ : (s₁.arrs a_entries).length < 2 ^ w := by
      rw [harr₁ a_entries (by omega), harr₀_lt a_entries (by omega)]; exact hent_w
    -- 2. resBfsLoopRegProg
    rcases resBfsLoopRegProg_exec G lists A B used pred succ a_start a_end a_entries a_base r_base
        (by omega) (by omega) (by omega) hw h2n_w
        hconst₁ hadj₁ hent₁ hsys₁ hq₁ hpar₁ (IsResPopClosed.zero G used pred succ items₀) hinit₁ with
      ⟨s₂, t₂, items, hex₂, ht₂, hconst₂, _, hsys₂, hq₂, hpar₂, hclosed₂, hinit₂, harr₂, hreg₂⟩
    have hsum_res := sum_resNodeWeight_le_univ lists (Finset.univ \ listFinset (2 * n) (items₀.take 0))
    have hB_bit₂ : IsBitSet B a_B s₂ :=
      hB_bit.of_arr_eq (by rw [harr₂ a_B (by omega), harr₁ a_B (by omega), harr₀_lt a_B (by omega)])
    -- 3. findTargetRegProg
    rcases findTargetRegProg_exec B a_B a_base r_base hw h2n_w hconst₂ hB_bit₂ hq₂ with
      ⟨s₃, t₃, hex₃, ht₃, hconst₃, htarg_le₃, htarg_sound₃, htarg_comp₃, harr₃, hreg₃⟩
    have hsys₃ : PathSystemState G A B a_base used pred succ s₃ :=
      hsys₂.of_arrs_eq (harr₃ a_base) (harr₃ (a_base + 1)) (harr₃ (a_base + 2))
    have hpar₃ : ResParentInv G A used pred succ (a_base + 4) items s₃ :=
      hpar₂.of_arrs_eq (harr₃ (a_base + 4))
    have hvis₃ : IsResVisArr n (a_base + 3) items s₃ :=
      IsResVisArr.of_arr_eq ⟨hq₂.2.2.2.1, hq₂.2.2.2.2.2.1⟩ (harr₃ (a_base + 3))
    have hA_bit₃ : IsBitSet A a_A s₃ :=
      hA_bit.of_arr_eq (by rw [harr₃ a_A, harr₂ a_A (by omega), harr₁ a_A (by omega), harr₀_lt a_A (by omega)])
    have harr₃_lt : ∀ a < a_base, s₃.arrs a = s.arrs a := by
      intro a ha
      rw [harr₃ a, harr₂ a (by omega), harr₁ a (by omega), harr₀_lt a (by omega)]
    have hreg₃_ge : ∀ r ≥ r_base + 12, s₃.regs r = s.regs r := by
      intro r hr
      rw [hreg₃ r (by omega) (by omega), hreg₂ r (by omega), hreg₁ r (by omega)]
      rfl
    -- 4. Branch on r_base + 11 < r_base + 12
    by_cases hlt11 : s₃.regs (r_base + 11) < n
    · -- Target found: augment and continue
      let b₀ : Fin n := ⟨s₃.regs (r_base + 11), hlt11⟩
      have hr_targ : s₃.regs (r_base + 11) = b₀.1 := rfl
      rcases htarg_sound₃ b₀ rfl with ⟨hb₀_B, hb₀_mem⟩
      have hb₀_lt : b₀.1 < n := b₀.2
      have hb₀_w : b₀.1 < 2 ^ w := by omega
      have hcond_ite : (Expr.op .lt (.reg (r_base + 11)) (.reg (r_base + 12))).eval w s₃ = some 1 := by
        simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr_targ, hconst₃.1, hb₀_w, hn_w, hb₀_lt, hw]
      have hlen_le : items.length ≤ 2 * n := hq₂.1.2.1
      rcases augmentTraceRegProg_exec G A B used pred succ a_A a_base r_base ha_A hw h2n_w
          hconst₃ hA_bit₃ hpar₃ hsys₃ hr_targ hb₀_B hb₀_mem hlen_le with
        ⟨s₄, t₄, used', pred', succ', hex₄, ht₄, hconst₄, hsys₄, hcard₄, harr₄, hreg₄⟩
      have hr_round₄ : s₄.regs (r_base + 15) = round := by
        rw [hreg₄ _ (by omega), hreg₃_ge _ (by omega), hr_round]
      have hr_ok₄ : s₄.regs (r_base + 16) = 1 := by
        rw [hreg₄ _ (by omega), hreg₃_ge _ (by omega), hr_ok]
      let s₅ := s₄.setReg (r_base + 15) (round + 1)
      have hex_inc : Exec w (.assign (r_base + 15) (.op .add (.reg (r_base + 15)) (.const 1)))
          s₄ s₅ 4 :=
        .assign (by
          simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr_round₄, hround_w, hw,
            show round + 1 < 2 ^ w by omega])
      have hex_ite : Exec w (.ite (.op .lt (.reg (r_base + 11)) (.reg (r_base + 12)))
          (.seq (augmentTraceRegProg a_A a_base r_base)
            (.assign (r_base + 15) (.op .add (.reg (r_base + 15)) (.const 1))))
          (.seq (.assign (r_base + 16) (.const 0))
            (.assign (r_base + 15) (.reg (r_base + 14))))) s₃ s₅ (3 + (t₄ + 4)) :=
        .ite_true hcond_ite (by omega) (.seq hex₄ hex_inc)
      have hex_body : Exec w (augmentRoundRegBody a_start a_end a_entries a_A a_B a_base r_base)
          s s₅ ((1 + 2 * n) + (t₁ + (t₂ + (t₃ + (3 + (t₄ + 4)))))) :=
        .seq hex₀ (.seq hex₁ (.seq hex₂ (.seq hex₃ hex_ite)))
      have harr₅_lt : ∀ a < a_base, s₅.arrs a = s.arrs a := by
        intro a ha
        simp [s₅, harr₄ a ha, harr₃_lt a ha]
      have hconst₅ : ConstRegs n k_goal r_base s₅ :=
        hconst₄.of_regs_eq
          (by simp [s₅, State.setReg])
          (by simp [s₅, State.setReg])
          (by simp [s₅, State.setReg])
      have hadj₅ : IsAdjList G a_start a_end a_entries lists s₅ :=
        hadj.of_arrs_eq (harr₅_lt a_start ha_st) (harr₅_lt a_end ha_en) (harr₅_lt a_entries ha_ent)
      have hent₅ : (s₅.arrs a_entries).length < 2 ^ w := by
        rw [harr₅_lt a_entries ha_ent]; exact hent_w
      have hA_bit₅ : IsBitSet A a_A s₅ := hA_bit.of_arr_eq (harr₅_lt a_A ha_A)
      have hB_bit₅ : IsBitSet B a_B s₅ := hB_bit.of_arr_eq (harr₅_lt a_B ha_B)
      have hsys₅ : PathSystemState G A B a_base used' pred' succ' s₅ :=
        ⟨hsys₄.1, hsys₄.2.setReg _ _⟩
      rcases ih (round + 1) (by omega) hconst₅ hadj₅ hent₅ hA_bit₅ hB_bit₅ hsys₅
          (by rw [hcard₄, hcard]) (by simp [s₅])
          (by simp [s₅, State.setReg, hr_ok₄]) with
        ⟨s', t_rem, hex_rem, ht_rem, hconst', harr', hreg', hres'⟩
      have hstep_bound :
          3 + ((1 + 2 * n) + (t₁ + (t₂ + (t₃ + (3 + (t₄ + 4)))))) ≤
            65 + 264 * n + 31 * totalAdjEntries lists := by
        omega
      have hmul : (rem + 1) * (65 + 264 * n + 31 * totalAdjEntries lists) =
          (65 + 264 * n + 31 * totalAdjEntries lists) +
            rem * (65 + 264 * n + 31 * totalAdjEntries lists) := by
        rw [Nat.add_mul, Nat.one_mul, Nat.add_comm]
      refine ⟨s', 3 + ((1 + 2 * n) + (t₁ + (t₂ + (t₃ + (3 + (t₄ + 4)))))) + t_rem,
        .while_true hcond (by omega) hex_body hex_rem,
        by omega, hconst',
        fun a ha => by rw [harr' a ha, harr₅_lt a ha],
        fun r hr => by
          rw [hreg' r hr]
          simp [s₅, State.setReg, show (r : Reg) ≠ r_base + 15 by omega,
            hreg₄ r (by omega), hreg₃_ge r (by omega)],
        hres'⟩
    · -- No target found: record ok := 0, round := k_goal, and exit immediately
      have hr_targ_n : s₃.regs (r_base + 11) = n := by omega
      have hnoB : ∀ b ∈ B, b.1 + n ∉ items := htarg_comp₃ hr_targ_n
      have hcond_ite : (Expr.op .lt (.reg (r_base + 11)) (.reg (r_base + 12))).eval w s₃ = some 0 := by
        simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr_targ_n, hconst₃.1, hn_w, h0_w]
      let s₄ := s₃.setReg (r_base + 16) 0
      have hex_ok0 : Exec w (.assign (r_base + 16) (.const 0)) s₃ s₄ 2 :=
        .assign (by simp [Expr.eval, checkWord, h0_w])
      let s₅ := s₄.setReg (r_base + 15) k_goal
      have hex_rk : Exec w (.assign (r_base + 15) (.reg (r_base + 14))) s₄ s₅ 2 :=
        .assign (by
          simp [s₄, State.setReg, Expr.eval, checkWord, hconst₃.2.2, hk_w])
      have hex_ite : Exec w (.ite (.op .lt (.reg (r_base + 11)) (.reg (r_base + 12)))
          (.seq (augmentTraceRegProg a_A a_base r_base)
            (.assign (r_base + 15) (.op .add (.reg (r_base + 15)) (.const 1))))
          (.seq (.assign (r_base + 16) (.const 0))
            (.assign (r_base + 15) (.reg (r_base + 14))))) s₃ s₅ (3 + (2 + 2)) :=
        .ite_false hcond_ite (.seq hex_ok0 hex_rk)
      have hex_body : Exec w (augmentRoundRegBody a_start a_end a_entries a_A a_B a_base r_base)
          s s₅ ((1 + 2 * n) + (t₁ + (t₂ + (t₃ + (3 + (2 + 2)))))) :=
        .seq hex₀ (.seq hex₁ (.seq hex₂ (.seq hex₃ hex_ite)))
      have hconst₅ : ConstRegs n k_goal r_base s₅ :=
        hconst₃.of_regs_eq
          (by simp [s₅, s₄, State.setReg])
          (by simp [s₅, s₄, State.setReg])
          (by simp [s₅, s₄, State.setReg])
      have hr15_₅ : s₅.regs (r_base + 15) = k_goal := by simp [s₅]
      have hcond_end : (Expr.op .lt (.reg (r_base + 15)) (.reg (r_base + 14))).eval w s₅ = some 0 := by
        simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr15_₅, hconst₅.2.2, hk_w, h0_w]
      have hex_end : Exec w (mengerLoopRegProg a_start a_end a_entries a_A a_B a_base r_base)
          s₅ s₅ 3 := .while_false hcond_end
      have hstep_bound :
          3 + ((1 + 2 * n) + (t₁ + (t₂ + (t₃ + (3 + (2 + 2)))))) ≤
            65 + 264 * n + 31 * totalAdjEntries lists := by
        omega
      have hmul_ge : 65 + 264 * n + 31 * totalAdjEntries lists ≤
          (rem + 1) * (65 + 264 * n + 31 * totalAdjEntries lists) :=
        Nat.le_mul_of_pos_left _ (by omega)
      refine ⟨s₅, 3 + ((1 + 2 * n) + (t₁ + (t₂ + (t₃ + (3 + (2 + 2)))))) + 3,
        .while_true hcond (by omega) hex_body hex_end,
        by omega, hconst₅,
        fun a ha => by simp [s₅, s₄, harr₃_lt a ha],
        fun r hr => by
          simp [s₅, s₄, State.setReg,
            show (r : Reg) ≠ r_base + 15 by omega,
            show (r : Reg) ≠ r_base + 16 by omega,
            hreg₃_ge r (by omega)],
        Or.inr ⟨by simp [s₅, s₄, State.setReg],
          used, pred, succ, items,
          ⟨hsys₃.1, (hsys₃.2.setReg _ _).setReg _ _⟩,
          by omega, hvis₃.of_arr_eq (s' := s₅) rfl, hpar₃.of_arrs_eq (s' := s₅) rfl, hclosed₂,
          hinit₂, hnoB⟩⟩

/-! ### Section 3: Writing Output to `outArr` (`mengerOutputRegProg`) -/

/-- Copy array `a_src` of length `n` (`r_base + 12`) into `outArr` starting at offset `r_base + 8`,
using loop register `r_base + 3` and scratch register `r_base + 7`. -/
def copyToOutBody (a_src : Arr) (r_base : Reg) : Cmd :=
  .seq (.assign (r_base + 7) (.read a_src (.reg (r_base + 3))))
    (.write outArr (.op .add (.reg (r_base + 8)) (.reg (r_base + 3))) (.reg (r_base + 7)))

def copyToOutProg (a_src : Arr) (e_off : Expr) (r_base : Reg) : Cmd :=
  .seq (.assign (r_base + 8) e_off)
    (.seq (.assign (r_base + 3) (.const 0))
      (forUp (r_base + 3) (.reg (r_base + 12)) (copyToOutBody a_src r_base)))

theorem copyToOutLoop_exec {w n k_goal : ℕ} (off a_src : ℕ) (r_base : ℕ)
    (hne_out : (outArr : Arr) ≠ a_src)
    (pre mid suf : List ℕ)
    (hpre : pre.length = off) (hmid : mid.length = n)
    (hmid_w : ∀ x ∈ mid, x < 2 ^ w)
    (hw : 1 < 2 ^ w) (hoff_n_w : off + n < 2 ^ w)
    (rem k : ℕ) (hrem : k + rem = n) {s : State}
    (hconst : ConstRegs n k_goal r_base s)
    (hsrc : s.arrs a_src = mid)
    (hout : s.arrs outArr = pre ++ mid.take k ++ List.replicate (n - k) 0 ++ suf)
    (hroff : s.regs (r_base + 8) = off)
    (hrk : s.regs (r_base + 3) = k) :
    ∃ s' t,
      Exec w (forUp (r_base + 3) (.reg (r_base + 12)) (copyToOutBody a_src r_base)) s s' t ∧
      t ≤ 3 + 15 * rem ∧
      ConstRegs n k_goal r_base s' ∧
      s'.arrs outArr = pre ++ mid ++ suf ∧
      (∀ a : ℕ, a ≠ outArr → s'.arrs a = s.arrs a) ∧
      (∀ r ≥ r_base + 12, s'.regs r = s.regs r) := by
  have h0_w : 0 < 2 ^ w := by omega
  have hn_w : n < 2 ^ w := by omega
  induction rem generalizing k s with
  | zero =>
    have hk_eq : k = n := by omega
    rw [hk_eq] at hrk hout
    have hcond : (Expr.op .lt (.reg (r_base + 3)) (.reg (r_base + 12))).eval w s = some 0 := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hrk, hconst.1, hn_w, h0_w]
    have htake : mid.take n = mid := List.take_of_length_le (by omega)
    refine ⟨s, 3, .while_false hcond, by omega, hconst, ?_, fun _ _ => rfl, fun _ _ => rfl⟩
    simpa [htake] using hout
  | succ rem ih =>
    have hk_lt : k < n := by omega
    have hk_w : k < 2 ^ w := by omega
    have hoff_w : off < 2 ^ w := by omega
    have hoff_k_w : off + k < 2 ^ w := by omega
    have hcond : (Expr.op .lt (.reg (r_base + 3)) (.reg (r_base + 12))).eval w s = some 1 := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hrk, hconst.1, hk_w, hn_w, hk_lt, hw]
    have hk_mid : k < mid.length := by omega
    let val := mid[k]'hk_mid
    have hval_w : val < 2 ^ w := hmid_w val (List.getElem_mem hk_mid)
    have hk_src : k < (s.arrs a_src).length := by rw [hsrc]; exact hk_mid
    have hget_src : (s.arrs a_src)[k]'hk_src = val := by simp [val, hsrc]
    let s₁ := s.setReg (r_base + 7) val
    have hex₁ : Exec w (.assign (r_base + 7) (.read a_src (.reg (r_base + 3)))) s s₁ 3 :=
      .assign (by simp [Expr.eval, checkWord, hrk, hk_w, hk_src, hget_src, hval_w])
    have hout_len : off + k < (s₁.arrs outArr).length := by
      simp [s₁, hout, hpre, hmid]; omega
    let s₂ := s₁.writeArr outArr (off + k) val
    have hex₂ : Exec w (.write outArr (.op .add (.reg (r_base + 8)) (.reg (r_base + 3)))
        (.reg (r_base + 7))) s₁ s₂ 5 :=
      .write
        (by simp [s₁, State.setReg, Expr.eval, BinOp.eval, BinOp.raw, checkWord,
          hroff, hrk, hoff_w, hk_w, hoff_k_w])
        (by simp [s₁, State.setReg, Expr.eval, checkWord, hval_w])
        hout_len
    let s₃ := s₂.setReg (r_base + 3) (k + 1)
    have hex_inc : Exec w (.assign (r_base + 3) (.op .add (.reg (r_base + 3)) (.const 1))) s₂ s₃ 4 :=
      .assign (by
        simp [s₂, s₁, State.setReg, Expr.eval, BinOp.eval, BinOp.raw, checkWord,
          hrk, hk_w, hw, show k + 1 < 2 ^ w by omega])
    have hout₃ : s₃.arrs outArr =
        pre ++ mid.take (k + 1) ++ List.replicate (n - (k + 1)) 0 ++ suf := by
      simp only [s₃, s₂, s₁, State.setReg_arrs, State.writeArr_arrs_self, hout]
      have hlen_pre_take : (pre ++ mid.take k).length = off + k := by
        rw [List.length_append, hpre, List.length_take]; omega
      rw [List.append_assoc (pre ++ mid.take k), List.set_append_right _ _ (by omega)]
      have hsub0 : off + k - (pre ++ mid.take k).length = 0 := by omega
      have hrep : n - k = (n - (k + 1)) + 1 := by omega
      rw [hsub0, hrep, List.replicate_succ, List.cons_append, List.set_cons_zero]
      rw [take_add_one_eq_append_getElem mid k hk_mid]
      simp only [val, List.append_assoc, List.cons_append, List.nil_append]
    have hreg₃ : ∀ r ≥ r_base + 12, s₃.regs r = s.regs r := by
      intro r hr
      simp [s₃, s₂, s₁, State.setReg,
        show (r : Reg) ≠ r_base + 3 by omega, show (r : Reg) ≠ r_base + 7 by omega]
    have hconst₃ : ConstRegs n k_goal r_base s₃ :=
      hconst.of_regs_eq (hreg₃ _ (by omega)) (hreg₃ _ (by omega)) (hreg₃ _ (by omega))
    rcases ih (k + 1) (by omega) hconst₃
        (by simp [s₃, s₂, s₁, State.writeArr_arrs_ne _ _ _ hne_out.symm, hsrc])
        hout₃
        (by simp [s₃, s₂, s₁, State.setReg, hroff])
        (by simp [s₃]) with
      ⟨s₄, t₄, hex₄, ht₄, hconst₄, hout₄, harr₄, hreg₄⟩
    refine ⟨s₄, 3 + ((3 + 5) + 4) + t₄,
      .while_true hcond (by omega) (.seq (.seq hex₁ hex₂) hex_inc) hex₄,
      by omega, hconst₄, hout₄,
      fun a ha => by
        rw [harr₄ a ha]
        simp [s₃, s₂, s₁, show (a : Arr) ≠ outArr from ha],
      fun r hr => by rw [hreg₄ r hr, hreg₃ r hr]⟩

theorem copyToOutProg_exec {w n k_goal : ℕ} (off a_src : ℕ) (e_off : Expr) (r_base : ℕ)
    (hne_out : (outArr : Arr) ≠ a_src)
    (pre mid suf : List ℕ)
    (hpre : pre.length = off) (hmid : mid.length = n)
    (hmid_w : ∀ x ∈ mid, x < 2 ^ w)
    (hw : 1 < 2 ^ w) (hoff_n_w : off + n < 2 ^ w) {s : State}
    (hconst : ConstRegs n k_goal r_base s)
    (he_off : e_off.eval w s = some off)
    (hsrc : s.arrs a_src = mid)
    (hout : s.arrs outArr = pre ++ List.replicate n 0 ++ suf) :
    ∃ s' t,
      Exec w (copyToOutProg a_src e_off r_base) s s' t ∧
      t ≤ 15 * n + 6 + e_off.cost ∧
      ConstRegs n k_goal r_base s' ∧
      s'.arrs outArr = pre ++ mid ++ suf ∧
      (∀ a : ℕ, a ≠ outArr → s'.arrs a = s.arrs a) ∧
      (∀ r ≥ r_base + 12, s'.regs r = s.regs r) := by
  have h0_w : 0 < 2 ^ w := by omega
  let s₁ := s.setReg (r_base + 8) off
  have hex₁ : Exec w (.assign (r_base + 8) e_off) s s₁ (e_off.cost + 1) := .assign he_off
  let s₂ := s₁.setReg (r_base + 3) 0
  have hex₂ : Exec w (.assign (r_base + 3) (.const 0)) s₁ s₂ 2 :=
    .assign (by simp [Expr.eval, checkWord, h0_w])
  have hreg₂ : ∀ r ≥ r_base + 12, s₂.regs r = s.regs r := by
    intro r hr
    simp [s₂, s₁, State.setReg,
      show (r : Reg) ≠ r_base + 3 by omega, show (r : Reg) ≠ r_base + 8 by omega]
  have hconst₂ : ConstRegs n k_goal r_base s₂ :=
    hconst.of_regs_eq (hreg₂ _ (by omega)) (hreg₂ _ (by omega)) (hreg₂ _ (by omega))
  rcases copyToOutLoop_exec off a_src r_base hne_out pre mid suf hpre hmid hmid_w hw hoff_n_w n 0
      (by omega) hconst₂ (by simp [s₂, s₁, hsrc]) (by simpa [s₂, s₁] using hout)
      (by simp [s₂, s₁, State.setReg]) (by simp [s₂]) with
    ⟨s₃, t₃, hex₃, ht₃, hconst₃, hout₃, harr₃, hreg₃⟩
  refine ⟨s₃, (e_off.cost + 1) + (2 + t₃), .seq hex₁ (.seq hex₂ hex₃),
    by omega, hconst₃, hout₃, harr₃,
    fun r hr => by rw [hreg₃ r hr, hreg₂ r hr]⟩

/-- Write `[1] ++ s.arrs a_base ++ s.arrs (a_base + 1) ++ s.arrs (a_base + 2)` to `outArr`. -/
def writePathSystemOutProg (a_base : Arr) (r_base : Reg) : Cmd :=
  .seq (.alloc outArr (.op .add (.const 1) (.op .add (.reg (r_base + 12)) (.reg (r_base + 13)))))
    (.seq (.write outArr (.const 0) (.const 1))
      (.seq (copyToOutProg a_base (.const 1) r_base)
        (.seq (copyToOutProg (a_base + 1) (.op .add (.const 1) (.reg (r_base + 12))) r_base)
          (copyToOutProg (a_base + 2) (.op .add (.const 1) (.reg (r_base + 13))) r_base))))

theorem writePathSystemOutProg_exec {w n k_goal : ℕ} (G : SimpleGraph (Fin n))
    (A B : Finset (Fin n)) (used pred succ : Fin n → ℕ) (a_base r_base : ℕ)
    (ha_out : outArr < a_base)
    (hw : 1 < 2 ^ w) (h3n1_w : 1 + 3 * n < 2 ^ w) {s : State}
    (hconst : ConstRegs n k_goal r_base s)
    (hsys : PathSystemState G A B a_base used pred succ s) :
    ∃ s' t,
      Exec w (writePathSystemOutProg a_base r_base) s s' t ∧
      t ≤ 48 * n + 35 ∧
      s'.arrs outArr = [1] ++ s.arrs a_base ++ s.arrs (a_base + 1) ++ s.arrs (a_base + 2) := by
  have h0_w : 0 < 2 ^ w := by omega
  have hn_w : n < 2 ^ w := by omega
  have h2n_w : 2 * n < 2 ^ w := by omega
  have h3n_w : n + 2 * n < 2 ^ w := by omega
  have h13n_w : 1 + (n + 2 * n) < 2 ^ w := by omega
  have heval_len :
      (Expr.op .add (.const 1) (.op .add (.reg (r_base + 12)) (.reg (r_base + 13)))).eval w s =
        some (1 + (n + 2 * n)) := by
    simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hconst.1, hconst.2.1,
      hw, hn_w, h2n_w, h3n_w, h13n_w]
  let s₁ := s.setArr outArr (List.replicate (1 + (n + 2 * n)) 0)
  have hex₁ : Exec w (.alloc outArr
      (.op .add (.const 1) (.op .add (.reg (r_base + 12)) (.reg (r_base + 13)))))
      s s₁ (5 + (1 + (n + 2 * n))) := .alloc heval_len
  let s₂ := s₁.writeArr outArr 0 1
  have hex₂ : Exec w (.write outArr (.const 0) (.const 1)) s₁ s₂ 3 :=
    .write (by simp [Expr.eval, checkWord, h0_w]) (by simp [Expr.eval, checkWord, hw])
      (by simp [s₁])
  have hout₂ : s₂.arrs outArr = [1] ++ List.replicate n 0 ++ List.replicate (2 * n) 0 := by
    have hrep : List.replicate (1 + (n + 2 * n)) 0 =
        0 :: (List.replicate n 0 ++ List.replicate (2 * n) 0) := by
      rw [Nat.add_comm 1, List.replicate_succ, List.replicate_add]
    simp [s₂, s₁, hrep]
  have hconst₂ : ConstRegs n k_goal r_base s₂ := hconst.of_regs_eq rfl rfl rfl
  have harr₂ : ∀ a : Arr, a ≠ outArr → s₂.arrs a = s.arrs a := by
    intro a ha
    simp [s₂, s₁, State.writeArr_arrs_ne _ _ _ ha, State.setArr_arrs_ne _ _ ha]
  rcases hsys.2 with ⟨hu_len, hp_len, hs_len, hu_eq, hp_eq, hs_eq⟩
  have hused_w : ∀ x ∈ s.arrs a_base, x < 2 ^ w := by
    intro x hx
    rcases List.mem_iff_getElem.mp hx with ⟨i, hi, rfl⟩
    have hi_n : i < n := by simpa [hu_len] using hi
    have hle := hsys.1.used_le ⟨i, hi_n⟩
    have heq := hu_eq ⟨i, hi_n⟩
    dsimp at heq
    omega
  have hpred_w : ∀ x ∈ s.arrs (a_base + 1), x < 2 ^ w := by
    intro x hx
    rcases List.mem_iff_getElem.mp hx with ⟨i, hi, rfl⟩
    have hi_n : i < n := by simpa [hp_len] using hi
    have hle := hsys.1.pred_le ⟨i, hi_n⟩
    have heq := hp_eq ⟨i, hi_n⟩
    dsimp at heq
    omega
  have hsucc_w : ∀ x ∈ s.arrs (a_base + 2), x < 2 ^ w := by
    intro x hx
    rcases List.mem_iff_getElem.mp hx with ⟨i, hi, rfl⟩
    have hi_n : i < n := by simpa [hs_len] using hi
    have hle := hsys.1.succ_le ⟨i, hi_n⟩
    have heq := hs_eq ⟨i, hi_n⟩
    dsimp at heq
    omega
  have hne_out0 : (outArr : Arr) ≠ a_base := ne_of_lt ha_out
  have hne_out1 : (outArr : Arr) ≠ a_base + 1 := ne_of_lt (Nat.lt_trans ha_out (by omega))
  have hne_out2 : (outArr : Arr) ≠ a_base + 2 := ne_of_lt (Nat.lt_trans ha_out (by omega))
  -- Copy a_base to offset 1
  rcases copyToOutProg_exec 1 a_base (.const 1) r_base hne_out0
      [1] (s.arrs a_base) (List.replicate (2 * n) 0)
      (by simp) hu_len hused_w hw (by omega) hconst₂
      (by simp [Expr.eval, checkWord, hw])
      (harr₂ a_base hne_out0.symm)
      hout₂ with
    ⟨s₃, t₃, hex₃, ht₃, hconst₃, hout₃, harr₃, _⟩
  dsimp [Expr.cost] at ht₃
  -- Copy a_base + 1 to offset 1 + n
  have hout₃' : s₃.arrs outArr =
      ([1] ++ s.arrs a_base) ++ List.replicate n 0 ++ List.replicate n 0 := by
    have h2n : 2 * n = n + n := Nat.two_mul n
    rw [hout₃, h2n, List.replicate_add]
    simp [List.append_assoc]
  rcases copyToOutProg_exec (1 + n) (a_base + 1)
      (.op .add (.const 1) (.reg (r_base + 12))) r_base hne_out1
      ([1] ++ s.arrs a_base) (s.arrs (a_base + 1)) (List.replicate n 0)
      (by simp [hu_len]; omega) hp_len hpred_w hw (by omega) hconst₃
      (by simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hconst₃.1, hw, hn_w,
        show 1 + n < 2 ^ w by omega])
      (by rw [harr₃ (a_base + 1) hne_out1.symm, harr₂ (a_base + 1) hne_out1.symm])
      hout₃' with
    ⟨s₄, t₄, hex₄, ht₄, hconst₄, hout₄, harr₄, _⟩
  dsimp [Expr.cost] at ht₄
  -- Copy a_base + 2 to offset 1 + 2 * n
  have hout₄' : s₄.arrs outArr =
      ([1] ++ s.arrs a_base ++ s.arrs (a_base + 1)) ++ List.replicate n 0 ++ [] := by
    simp [hout₄]
  rcases copyToOutProg_exec (1 + 2 * n) (a_base + 2)
      (.op .add (.const 1) (.reg (r_base + 13))) r_base hne_out2
      ([1] ++ s.arrs a_base ++ s.arrs (a_base + 1)) (s.arrs (a_base + 2)) []
      (by simp [hu_len, hp_len]; omega) hs_len hsucc_w hw (by omega) hconst₄
      (by simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hconst₄.2.1, hw, h2n_w,
        show 1 + 2 * n < 2 ^ w by omega])
      (by rw [harr₄ (a_base + 2) hne_out2.symm, harr₃ (a_base + 2) hne_out2.symm, harr₂ (a_base + 2) hne_out2.symm])
      hout₄' with
    ⟨s₅, t₅, hex₅, ht₅, _, hout₅, _, _⟩
  dsimp [Expr.cost] at ht₅
  refine ⟨s₅, (5 + (1 + (n + 2 * n))) + (3 + (t₃ + (t₄ + t₅))),
    .seq hex₁ (.seq hex₂ (.seq hex₃ (.seq hex₄ hex₅))),
    by omega, by simpa using hout₅⟩

/-- Loop body for writing `0 :: bitSetList (resCut n items)` to `outArr`. -/
def writeResCutOutBody (a_base : Arr) (r_base : Reg) : Cmd :=
  .seq (.assign (r_base + 7) (.read (a_base + 3) (.reg (r_base + 3))))
    (.seq (.assign (r_base + 8)
        (.read (a_base + 3) (.op .add (.reg (r_base + 3)) (.reg (r_base + 12)))))
      (.ite (.reg (r_base + 7))
        (.ite (.reg (r_base + 8))
          .skip
          (.write outArr (.op .add (.const 1) (.reg (r_base + 3))) (.const 1)))
        .skip))

def writeResCutOutProg (a_base : Arr) (r_base : Reg) : Cmd :=
  .seq (.alloc outArr (.op .add (.const 1) (.reg (r_base + 12))))
    (.seq (.assign (r_base + 3) (.const 0))
      (forUp (r_base + 3) (.reg (r_base + 12)) (writeResCutOutBody a_base r_base)))

theorem writeResCutOutLoop_exec {w n k_goal : ℕ} (a_base r_base : ℕ)
    (ha_out : outArr < a_base)
    (hw : 1 < 2 ^ w) (h2n_w : 2 * n < 2 ^ w)
    (rem k : ℕ) (hrem : k + rem = n) {items : List ℕ} {s : State}
    (hconst : ConstRegs n k_goal r_base s)
    (hvis : IsResVisArr n (a_base + 3) items s)
    (hout : s.arrs outArr = [0] ++ (bitSetList (resCut n items)).take k ++ List.replicate (n - k) 0)
    (hrk : s.regs (r_base + 3) = k) :
    ∃ s' t,
      Exec w (forUp (r_base + 3) (.reg (r_base + 12)) (writeResCutOutBody a_base r_base)) s s' t ∧
      t ≤ 3 + 22 * rem ∧
      s'.arrs outArr = 0 :: bitSetList (resCut n items) := by
  have h0_w : 0 < 2 ^ w := by omega
  have hn_w : n < 2 ^ w := by omega
  induction rem generalizing k s with
  | zero =>
    have hk_eq : k = n := by omega
    rw [hk_eq] at hrk hout
    have hcond : (Expr.op .lt (.reg (r_base + 3)) (.reg (r_base + 12))).eval w s = some 0 := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hrk, hconst.1, hn_w, h0_w]
    have htake : (bitSetList (resCut n items)).take n = bitSetList (resCut n items) :=
      List.take_of_length_le (by simp)
    refine ⟨s, 3, .while_false hcond, by omega, ?_⟩
    rw [htake, Nat.sub_self, List.replicate_zero, List.append_nil] at hout
    exact hout
  | succ rem ih =>
    have hk_lt : k < n := by omega
    have hk_w : k < 2 ^ w := by omega
    have hkn_lt : k + n < 2 * n := by omega
    have hkn_w : k + n < 2 ^ w := by omega
    have h1k_w : 1 + k < 2 ^ w := by omega
    have hcond : (Expr.op .lt (.reg (r_base + 3)) (.reg (r_base + 12))).eval w s = some 1 := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hrk, hconst.1, hk_w, hn_w, hk_lt, hw]
    have hvis_len : (s.arrs (a_base + 3)).length = 2 * n := hvis.1
    have hk_vis : k < (s.arrs (a_base + 3)).length := by rw [hvis_len]; omega
    let vin := (s.arrs (a_base + 3))[k]'hk_vis
    have hvin_props := hvis.2 k (by omega)
    have hvin_le : vin ≤ 1 := hvin_props.2
    have hvin_w : vin < 2 ^ w := by omega
    let s₁ := s.setReg (r_base + 7) vin
    have hex₁ : Exec w (.assign (r_base + 7) (.read (a_base + 3) (.reg (r_base + 3)))) s s₁ 3 :=
      .assign (by simp [Expr.eval, checkWord, hrk, hk_w, hk_vis, vin, hvin_w])
    have hkn_vis : k + n < (s.arrs (a_base + 3)).length := by rw [hvis_len]; exact hkn_lt
    let vout := (s.arrs (a_base + 3))[k + n]'hkn_vis
    have hvout_props := hvis.2 (k + n) hkn_lt
    have hvout_le : vout ≤ 1 := hvout_props.2
    have hvout_w : vout < 2 ^ w := by omega
    let s₂ := s₁.setReg (r_base + 8) vout
    have hex₂ : Exec w (.assign (r_base + 8)
        (.read (a_base + 3) (.op .add (.reg (r_base + 3)) (.reg (r_base + 12))))) s₁ s₂ 5 :=
      .assign (by
        simp [s₁, State.setReg, Expr.eval, BinOp.eval, BinOp.raw, checkWord,
          hrk, hconst.1, hk_w, hn_w, hkn_w, hkn_vis, vout, hvout_w])
    let uk : Fin n := ⟨k, hk_lt⟩
    have hbit_len : k < (bitSetList (resCut n items)).length := by simp [hk_lt]
    have hbit_k : (bitSetList (resCut n items))[k]'hbit_len =
        if uk ∈ resCut n items then 1 else 0 := getElem_bitSetList (resCut n items) k hk_lt
    have hne_out3 : (outArr : Arr) ≠ a_base + 3 := ne_of_lt (Nat.lt_trans ha_out (by omega))
    have hite_step : ∃ s₃ t_ite,
        Exec w (.ite (.reg (r_base + 7))
          (.ite (.reg (r_base + 8))
            .skip
            (.write outArr (.op .add (.const 1) (.reg (r_base + 3))) (.const 1)))
          .skip) s₂ s₃ t_ite ∧
        t_ite ≤ 7 ∧
        s₃.arrs outArr =
          [0] ++ (bitSetList (resCut n items)).take (k + 1) ++ List.replicate (n - (k + 1)) 0 ∧
        s₃.arrs (a_base + 3) = s.arrs (a_base + 3) ∧
        s₃.regs (r_base + 3) = k ∧
        (∀ r ≥ r_base + 12, s₃.regs r = s.regs r) := by
      have htake_zero : (bitSetList (resCut n items))[k]'hbit_len = 0 →
          [0] ++ (bitSetList (resCut n items)).take k ++ List.replicate (n - k) 0 =
          [0] ++ (bitSetList (resCut n items)).take (k + 1) ++ List.replicate (n - (k + 1)) 0 := by
        intro h0
        rw [take_add_one_eq_append_getElem _ k hbit_len, h0]
        have hrep : n - k = 1 + (n - (k + 1)) := by omega
        rw [hrep, List.replicate_add, List.replicate_one]
        simp [List.append_assoc]
      have hreg_s₂ : ∀ r, r ≠ r_base + 7 → r ≠ r_base + 8 → s₂.regs r = s.regs r := by
        intro r hr7 hr8
        simp [s₂, s₁, State.setReg, hr7, hr8]
      by_cases hvin : vin ≠ 0
      · have hk_in : k ∈ items := hvin_props.1.mp hvin
        have hcond7 : (Expr.reg (r_base + 7)).eval w s₂ = some vin := by
          simp [s₂, s₁, State.setReg, Expr.eval, checkWord, hvin_w]
        by_cases hvout : vout ≠ 0
        · have hkn_in : k + n ∈ items := hvout_props.1.mp hvout
          have huk_not : uk ∉ resCut n items := by
            rw [mem_resCut]
            intro h
            exact h.2 hkn_in
          have hcond8 : (Expr.reg (r_base + 8)).eval w s₂ = some vout := by
            simp [s₂, State.setReg, Expr.eval, checkWord, hvout_w]
          refine ⟨s₂, 1 + 2, .ite_true hcond7 hvin (.ite_true hcond8 hvout (.skip s₂)),
            by omega, ?_, rfl,
            hreg_s₂ (r_base + 3) (by omega) (by omega) ▸ hrk,
            fun r hr => hreg_s₂ r (by omega) (by omega)⟩
          rw [show s₂.arrs outArr = s.arrs outArr from rfl, hout]
          exact htake_zero (by rw [hbit_k]; simp [huk_not])
        · have hvout0 : vout = 0 := by omega
          have hkn_not : k + n ∉ items := fun h => hvout (hvout_props.1.mpr h)
          have huk_mem : uk ∈ resCut n items := (mem_resCut uk).mpr ⟨hk_in, hkn_not⟩
          have hcond8 : (Expr.reg (r_base + 8)).eval w s₂ = some 0 := by
            simp [s₂, State.setReg, Expr.eval, checkWord, hvout0, h0_w]
          have hout_len₂ : 1 + k < (s₂.arrs outArr).length := by
            have : (s.arrs outArr).length = 1 + n := by
              rw [hout, List.length_append, List.length_append, List.length_singleton,
                List.length_take, length_bitSetList, List.length_replicate]
              omega
            simp [s₂, s₁, this, hk_lt]
          let s₃ := s₂.writeArr outArr (1 + k) 1
          have hex_w : Exec w (.write outArr (.op .add (.const 1) (.reg (r_base + 3))) (.const 1))
              s₂ s₃ 5 :=
            .write
              (by simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord,
                hreg_s₂ (r_base + 3) (by omega) (by omega), hrk, hw, hk_w, h1k_w])
              (by simp [Expr.eval, checkWord, hw])
              hout_len₂
          refine ⟨s₃, 1 + (1 + 5), .ite_true hcond7 hvin (.ite_false hcond8 hex_w),
            by omega, ?_,
            by simp [s₃, s₂, s₁, hne_out3.symm],
            by simp [s₃, hreg_s₂ (r_base + 3) (by omega) (by omega), hrk],
            fun r hr => by simp [s₃, hreg_s₂ r (by omega) (by omega)]⟩
          simp only [s₃, s₂, s₁, State.writeArr_arrs_self, State.setReg_arrs, hout]
          have hlen_pre : ([0] ++ (bitSetList (resCut n items)).take k).length = 1 + k := by
            rw [List.length_append, List.length_singleton, List.length_take, length_bitSetList]
            omega
          rw [List.set_append_right _ _ (by omega)]
          have hsub0 : 1 + k - ([0] ++ (bitSetList (resCut n items)).take k).length = 0 := by omega
          have hrep : n - k = (n - (k + 1)) + 1 := by omega
          rw [hsub0, hrep, List.replicate_succ, List.set_cons_zero]
          rw [take_add_one_eq_append_getElem _ k hbit_len, hbit_k]
          simp [huk_mem, List.append_assoc]
      · have hvin0 : vin = 0 := by omega
        have hk_not : k ∉ items := fun h => hvin (hvin_props.1.mpr h)
        have huk_not : uk ∉ resCut n items := by
          rw [mem_resCut]
          intro h
          exact hk_not h.1
        have hcond7 : (Expr.reg (r_base + 7)).eval w s₂ = some 0 := by
          simp [s₂, s₁, State.setReg, Expr.eval, checkWord, hvin0, h0_w]
        refine ⟨s₂, 2, .ite_false hcond7 (.skip s₂), by omega, ?_, rfl,
          hreg_s₂ (r_base + 3) (by omega) (by omega) ▸ hrk,
          fun r hr => hreg_s₂ r (by omega) (by omega)⟩
        rw [show s₂.arrs outArr = s.arrs outArr from rfl, hout]
        exact htake_zero (by rw [hbit_k]; simp [huk_not])
    rcases hite_step with
      ⟨s₃, t_ite, hex_ite, ht_ite, hout₃, harr3₃, hrk₃, hreg₃⟩
    let s₄ := s₃.setReg (r_base + 3) (k + 1)
    have hex_inc : Exec w (.assign (r_base + 3) (.op .add (.reg (r_base + 3)) (.const 1))) s₃ s₄ 4 :=
      .assign (by
        simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hrk₃, hk_w, hw,
          show k + 1 < 2 ^ w by omega])
    have hreg₄ : ∀ r ≥ r_base + 12, s₄.regs r = s.regs r := by
      intro r hr
      simp [s₄, State.setReg, show (r : Reg) ≠ r_base + 3 by omega, hreg₃ r hr]
    have hconst₄ : ConstRegs n k_goal r_base s₄ :=
      hconst.of_regs_eq (hreg₄ _ (by omega)) (hreg₄ _ (by omega)) (hreg₄ _ (by omega))
    have hvis₄ : IsResVisArr n (a_base + 3) items s₄ :=
      hvis.of_arr_eq (by simp [s₄, harr3₃])
    rcases ih (k + 1) (by omega) hconst₄ hvis₄ (by simpa [s₄] using hout₃) (by simp [s₄]) with
      ⟨s₅, t₅, hex₅, ht₅, hout₅⟩
    refine ⟨s₅, 3 + ((3 + (5 + t_ite)) + 4) + t₅,
      .while_true hcond (by omega) (.seq (.seq hex₁ (.seq hex₂ hex_ite)) hex_inc) hex₅,
      by omega, hout₅⟩

theorem writeResCutOutProg_exec {w n k_goal : ℕ} (a_base r_base : ℕ)
    (ha_out : outArr < a_base)
    (hw : 1 < 2 ^ w) (h2n_w : 2 * n < 2 ^ w) (h1n_w : 1 + n < 2 ^ w)
    {items : List ℕ} {s : State}
    (hconst : ConstRegs n k_goal r_base s)
    (hvis : IsResVisArr n (a_base + 3) items s) :
    ∃ s' t,
      Exec w (writeResCutOutProg a_base r_base) s s' t ∧
      t ≤ 23 * n + 10 ∧
      s'.arrs outArr = 0 :: bitSetList (resCut n items) := by
  have h0_w : 0 < 2 ^ w := by omega
  have hn_w : n < 2 ^ w := by omega
  have hne_out3 : (outArr : Arr) ≠ a_base + 3 := ne_of_lt (Nat.lt_trans ha_out (by omega))
  let s₁ := s.setArr outArr (List.replicate (1 + n) 0)
  have hex₁ : Exec w (.alloc outArr (.op .add (.const 1) (.reg (r_base + 12))))
      s s₁ (3 + (1 + n)) :=
    .alloc (by simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hconst.1, hw, hn_w, h1n_w])
  let s₂ := s₁.setReg (r_base + 3) 0
  have hex₂ : Exec w (.assign (r_base + 3) (.const 0)) s₁ s₂ 2 :=
    .assign (by simp [Expr.eval, checkWord, h0_w])
  have hconst₂ : ConstRegs n k_goal r_base s₂ :=
    hconst.of_regs_eq
      (by simp [s₂, s₁, State.setReg])
      (by simp [s₂, s₁, State.setReg])
      (by simp [s₂, s₁, State.setReg])
  have hvis₂ : IsResVisArr n (a_base + 3) items s₂ :=
    hvis.of_arr_eq (by simp [s₂, s₁, hne_out3.symm])
  have hout₂ : s₂.arrs outArr =
      [0] ++ (bitSetList (resCut n items)).take 0 ++ List.replicate (n - 0) 0 := by
    have hrep : List.replicate (1 + n) 0 = [0] ++ List.replicate n 0 := by
      rw [Nat.add_comm 1, List.replicate_succ]; rfl
    simp [s₂, s₁, hrep]
  rcases writeResCutOutLoop_exec a_base r_base ha_out hw h2n_w n 0 (by omega)
      hconst₂ hvis₂ hout₂ (by simp [s₂]) with
    ⟨s₃, t₃, hex₃, ht₃, hout₃⟩
  refine ⟨s₃, (3 + (1 + n)) + (2 + t₃), .seq hex₁ (.seq hex₂ hex₃), by omega, hout₃⟩

/-- Dispatch output serialization based on `r_base + 16` (`r_ok`). -/
def mengerOutputRegProg (a_base : Arr) (r_base : Reg) : Cmd :=
  .ite (.reg (r_base + 16))
    (writePathSystemOutProg a_base r_base)
    (writeResCutOutProg a_base r_base)

/-! ### Section 4: Pure Decoder and End-to-End `disjointPaths_computesInTime` -/

/-- Problem input for the vertex-disjoint `A`–`B` paths algorithm: a simple graph
`G : SimpleGraph (Fin n)` with `DecidableRel G.Adj`, vertex subsets `A, B : Finset (Fin n)`, and
target path count `k : ℕ`. -/
structure DisjointPathsInput where
  /-- Number of vertices. -/
  n : ℕ
  /-- The input simple graph on `Fin n`. -/
  G : SimpleGraph (Fin n)
  /-- Decidability of adjacency in `G`. -/
  [decAdj : DecidableRel G.Adj]
  /-- Source vertex subset `A ⊆ V(G)`. -/
  A : Finset (Fin n)
  /-- Target vertex subset `B ⊆ V(G)`. -/
  B : Finset (Fin n)
  /-- Target number of vertex-disjoint `A`–`B` paths. -/
  k : ℕ

attribute [instance] DisjointPathsInput.decAdj

/-- Problem size for `DisjointPathsInput`: `(k + 1) * (n + m + 1)`, where `m = G.edgeFinset.card`.
For `k ≥ 1` and `n + m ≥ 1`, this is within a constant factor of `k * (n + m)`, while remaining
positive when `k = 0` or `n = 0` so that the initial `O(n + m)` input parsing and the word-size
bound `k, n, m < 2 ^ w` hold uniformly for all inputs. -/
def disjointPathsSize (x : DisjointPathsInput) : ℕ :=
  (x.k + 1) * (x.n + x.G.edgeFinset.card + 1)

/-- Flat input encoding of `(G, A, B, k)` in `inArr`:
`encGraph G ++ bitSetList A ++ bitSetList B ++ [k]`. -/
def encDisjointPathsIn (x : DisjointPathsInput) : List ℕ :=
  encGraph x.G ++ bitSetList x.A ++ bitSetList x.B ++ [x.k]

/-- Output type of the disjoint paths problem on `x : DisjointPathsInput`:
either a family of `x.k` `A`–`B` walks in `x.G`, or a vertex subset `C ⊆ V(x.G)`. -/
abbrev DisjointPathsOutput (x : DisjointPathsInput) : Type :=
  (Fin x.k → ABWalk x.G x.A x.B) ⊕ Finset (Fin x.n)

/-- Validity predicate on a decoded `DisjointPathsOutput x`:
- `Sum.inl P`: the `x.k` `A`–`B` walks `P i` (each a walk of `x.G` with `(P i).start ∈ x.A` and
  `(P i).finish ∈ x.B`) are simple paths (`(P i).walk.IsPath`) and pairwise vertex-disjoint
  (`PairwiseVertexDisjoint P`).
- `Sum.inr C`: `C` has size `< x.k` and meets every `A`–`B` walk in `x.G`
  (`IsABSeparator x.G x.A x.B C`). -/
def IsValidDisjointPathsOutput (x : DisjointPathsInput) (res : DisjointPathsOutput x) : Prop :=
  match res with
  | .inl P => PairwiseVertexDisjoint P ∧ ∀ i : Fin x.k, (P i).walk.IsPath
  | .inr C => C.card < x.k ∧ IsABSeparator x.G x.A x.B C

/-- Decode the `used`, `pred`, and `succ` functions on `Fin n` from an `outArr` list of the form
`[1] ++ usedList ++ predList ++ succList`. -/
def decUsed (n : ℕ) (out : List ℕ) (u : Fin n) : ℕ :=
  out.getD (1 + u.1) 0

def decPred (n : ℕ) (out : List ℕ) (u : Fin n) : ℕ :=
  out.getD (1 + n + u.1) n

def decSucc (n : ℕ) (out : List ℕ) (u : Fin n) : ℕ :=
  out.getD (1 + 2 * n + u.1) n

/-- Pure decoder from `outArr : List ℕ` into `DisjointPathsOutput x`:
- If `out.head? = some 1` and the encoded `(used, pred, succ)` arrays form a valid `A`–`B` path
  system of cardinality `x.k`, extracts the `x.k` vertex-disjoint simple `A`–`B` paths via
  `extractDisjointPaths`.
- Otherwise decodes `out.tail` as a vertex subset `finsetOfBitList x.n out.tail`. -/
noncomputable def decDisjointPathsOut (x : DisjointPathsInput) (out : List ℕ) :
    DisjointPathsOutput x :=
  open Classical in
  if out.head? = some 1 then
    if h : IsValidPathSystem x.G x.A x.B (decUsed x.n out) (decPred x.n out) (decSucc x.n out) ∧
        (pathStarts (decUsed x.n out) (decPred x.n out)).card = x.k then
      .inl (extractDisjointPaths h.1 h.2)
    else
      .inr ∅
  else
    .inr (finsetOfBitList x.n out.tail)

theorem decUsed_pred_succ_eq_of_isPathSystemArrs {n : ℕ} {used pred succ : Fin n → ℕ}
    {a_base : ℕ} {s : State}
    (harrs : IsPathSystemArrs a_base used pred succ s) :
    let out := [1] ++ s.arrs a_base ++ s.arrs (a_base + 1) ++ s.arrs (a_base + 2)
    decUsed n out = used ∧ decPred n out = pred ∧ decSucc n out = succ := by
  intro out
  rcases harrs with ⟨hu_len, hp_len, hs_len, hu_eq, hp_eq, hs_eq⟩
  refine ⟨funext fun u => ?_, funext fun u => ?_, funext fun u => ?_⟩
  · dsimp [decUsed, out]
    have hlt : 1 + u.1 < out.length := by simp [out, hu_len, hp_len, hs_len]; omega
    change (out[1 + u.1]?.getD 0) = used u
    rw [List.getElem?_eq_getElem hlt, Option.getD_some]
    have hout_eq : out = [1] ++ (s.arrs a_base ++ (s.arrs (a_base + 1) ++ s.arrs (a_base + 2))) := by
      simp [out, List.append_assoc]
    simp only [hout_eq]
    rw [List.getElem_append_right (by simp)]
    rw [List.getElem_append_left (by simp [hu_len])]
    have hsub : 1 + u.1 - ([1] : List ℕ).length = u.1 := by simp
    simp only [hsub]
    exact hu_eq u
  · dsimp [decPred, out]
    have hlt : 1 + n + u.1 < out.length := by simp [out, hu_len, hp_len, hs_len]; omega
    change (out[1 + n + u.1]?.getD n) = pred u
    rw [List.getElem?_eq_getElem hlt, Option.getD_some]
    have hout_eq : out = ([1] ++ s.arrs a_base) ++ (s.arrs (a_base + 1) ++ s.arrs (a_base + 2)) := by
      simp [out, List.append_assoc]
    simp only [hout_eq]
    rw [List.getElem_append_right (by simp [hu_len]; omega)]
    rw [List.getElem_append_left (by simp [hu_len, hp_len]; omega)]
    have hsub : 1 + n + u.1 - ([1] ++ s.arrs a_base).length = u.1 := by simp [hu_len]; omega
    simp only [hsub]
    exact hp_eq u
  · dsimp [decSucc, out]
    have hlt : 1 + 2 * n + u.1 < out.length := by simp [out, hu_len, hp_len, hs_len]; omega
    change (out[1 + 2 * n + u.1]?.getD n) = succ u
    rw [List.getElem?_eq_getElem hlt, Option.getD_some]
    simp only [out]
    rw [List.getElem_append_right (by simp [hu_len, hp_len]; omega)]
    have hsub : 1 + 2 * n + u.1 - ([1] ++ s.arrs a_base ++ s.arrs (a_base + 1)).length = u.1 := by
      simp [hu_len, hp_len]; omega
    simp only [hsub]
    exact hs_eq u

theorem isValidDisjointPathsOutput_of_pathSystem (x : DisjointPathsInput)
    {used pred succ : Fin x.n → ℕ} {a_base : ℕ} {s : State}
    (hsys : PathSystemState x.G x.A x.B a_base used pred succ s)
    (hcard : (pathStarts used pred).card = x.k)
    {out : List ℕ}
    (hout : out = [1] ++ s.arrs a_base ++ s.arrs (a_base + 1) ++ s.arrs (a_base + 2)) :
    IsValidDisjointPathsOutput x (decDisjointPathsOut x out) := by
  rcases decUsed_pred_succ_eq_of_isPathSystemArrs hsys.2 with ⟨hU, hP, hS⟩
  have hhead : out.head? = some 1 := by simp [hout]
  have hcond : IsValidPathSystem x.G x.A x.B (decUsed x.n out) (decPred x.n out) (decSucc x.n out) ∧
      (pathStarts (decUsed x.n out) (decPred x.n out)).card = x.k := by
    rw [← hout] at hU hP hS
    rw [hU, hP, hS]
    exact ⟨hsys.1, hcard⟩
  unfold decDisjointPathsOut
  simp only [hhead, ↓reduceIte, hcond, IsValidDisjointPathsOutput]
  exact extractDisjointPaths_sound hcond.1 hcond.2

theorem isValidDisjointPathsOutput_of_resCut (x : DisjointPathsInput)
    {used pred succ : Fin x.n → ℕ} {items : List ℕ}
    (hsys : IsValidPathSystem x.G x.A x.B used pred succ)
    (hcard_lt : (pathStarts used pred).card < x.k)
    (hreach : ∀ z : Fin (2 * x.n), z.1 ∈ items →
      ResReachable (ResidualAdj x.G used pred succ) {z | ∃ a ∈ x.A, z = inNode a} z)
    (hclosed : IsResPopClosed x.G used pred succ items items.length)
    (hinit : ∀ a ∈ x.A, a.1 ∈ items)
    (hnoB : ∀ b ∈ x.B, b.1 + x.n ∉ items)
    {out : List ℕ}
    (hout : out = 0 :: bitSetList (resCut x.n items)) :
    IsValidDisjointPathsOutput x (decDisjointPathsOut x out) := by
  have hhead : out.head? ≠ some 1 := by simp [hout]
  have htail : finsetOfBitList x.n out.tail = resCut x.n items := by
    simp [hout]
  unfold decDisjointPathsOut
  simp only [hhead, ↓reduceIte, htail, IsValidDisjointPathsOutput]
  have hclosed_all := hclosed.to_closed
  exact ⟨Nat.lt_of_le_of_lt (card_resCut_le_card_pathStarts hsys hclosed_all) hcard_lt,
    isABSeparator_resCut hsys hinit hclosed_all hreach hnoB⟩

/-- Fixed end-to-end Word RAM program for Menger's vertex-disjoint `A`–`B` paths theorem
(`disjointPaths_computesInTime`):
1. Parses `G` from `inArr` into CSR arrays `(a_start = 3, a_end = 4, a_entries = 5)` using `a_deg = 2`
   and registers `0..6` (`r_0 := n`, `r_1 := m`).
2. Copies `bitSetList A` into `a_A = 6` and `bitSetList B` into `a_B = 7` via `readSliceProg`.
3. Sets up `ConstRegs n k 2` (`r_14 := n`, `r_15 := 2 * n`, `r_16 := k`) and initializes
   `r_17 := 0` (`round := 0`), `r_18 := 1` (`ok := 1`).
4. Initializes the empty path system in `(a_used = 8, a_pred = 9, a_succ = 10)` via
   `initPathSystemRegProg 8 2`.
5. Runs `mengerLoopRegProg 3 4 5 6 7 8 2` for up to `k` rounds (using residual BFS arrays
   `a_vis = 11`, `a_parent = 12`, `a_q = 13`).
6. Writes the output to `outArr = 1` via `mengerOutputRegProg 8 2`. -/
def disjointPathsEndToEndProg : Cmd :=
  .seq (parseGraphProg 2 3 4 5 0)
    (.seq (readSliceProg inArr (.op .add (.const 2) (.op .mul (.const 2) (.reg 1))) 6 (.reg 0) 2)
      (.seq (readSliceProg inArr
          (.op .add (.op .add (.const 2) (.op .mul (.const 2) (.reg 1))) (.reg 0)) 7 (.reg 0) 2)
        (.seq (.assign 14 (.reg 0))
          (.seq (.assign 15 (.op .mul (.const 2) (.reg 0)))
            (.seq (.assign 16 (.read inArr
                (.op .add (.op .add (.const 2) (.op .mul (.const 2) (.reg 1))) (.reg 15))))
              (.seq (.assign 17 (.const 0))
                (.seq (.assign 18 (.const 1))
                  (.seq (initPathSystemRegProg 8 2)
                    (.seq (mengerLoopRegProg 3 4 5 6 7 8 2)
                      (mengerOutputRegProg 8 2))))))))))

theorem inArr_getElem_k {n : ℕ} (edges : List (Fin n × Fin n)) (A B : Finset (Fin n)) (k_val : ℕ)
    {arr : List ℕ}
    (harr : arr = [n, edges.length] ++ flatEdges edges ++ bitSetList A ++ bitSetList B ++ [k_val]) :
    ∃ (hidx : 2 + 2 * edges.length + 2 * n < arr.length),
      arr[2 + 2 * edges.length + 2 * n]'hidx = k_val := by
  have hlen : 2 + 2 * edges.length + 2 * n < arr.length := by
    simp [harr, length_flatEdges]; omega
  refine ⟨hlen, ?_⟩
  simp only [harr]
  rw [List.getElem_append_right (by simp [length_flatEdges]; omega)]
  have hsub : 2 + 2 * edges.length + 2 * n -
      ([n, edges.length] ++ flatEdges edges ++ bitSetList A ++ bitSetList B).length = 0 := by
    simp [length_flatEdges]; omega
  simp only [hsub, List.getElem_cons_zero]

/-- End-to-end `O(k(n + m))` Word RAM complexity theorem for Menger's vertex-disjoint `A`–`B` paths
algorithm (`disjointPathsEndToEndProg`):
on any input `x = (G, A, B, k)`, running `disjointPathsEndToEndProg` from any state with
`s.arrs inArr = encDisjointPathsIn x` terminates in `O((k + 1)(n + m + 1))` steps and writes an
output list to `outArr` whose decoding `decDisjointPathsOut x (s'.arrs outArr)` is either `k`
pairwise vertex-disjoint simple `A`–`B` paths in `G` or an `A`–`B` vertex separator of size `< k`. -/
theorem disjointPaths_computesInTime :
    ComputesArrRelInTime disjointPathsSize encDisjointPathsIn
      (fun x out => IsValidDisjointPathsOutput x (decDisjointPathsOut x out))
      disjointPathsEndToEndProg (fun s => s) := by
  unfold ComputesArrRelInTime ComputesRelInTime
  refine ⟨450, 3, by omega, by omega, fun x s₀ hs₀ => ?_⟩
  let edges := edgeListOf x.G
  have hedges : IsSimpleEdgeList x.G edges := isSimpleEdgeList_edgeListOf x.G
  have hm_eq : edges.length = x.G.edgeFinset.card := length_edgeListOf_eq_card_edgeFinset x.G
  have htot_eq : totalAdjEntries (edgeNeighbors edges) = 2 * edges.length :=
    totalAdjEntries_edgeNeighbors edges hedges.1
  set S := disjointPathsSize x
  let w := wordSize 3 S
  have hS_eq : S = (x.k + 1) * (x.n + edges.length + 1) := by simp [S, disjointPathsSize, hm_eq]
  have hnm_le_S : x.n + edges.length + 1 ≤ S := by
    rw [hS_eq]
    exact Nat.le_mul_of_pos_left _ (by omega)
  have hk_le_S : x.k + 1 ≤ S := by
    rw [hS_eq]
    exact Nat.le_mul_of_pos_right _ (by omega)
  have hpow3 : (S + 2) ^ 3 < 2 ^ w := pow_lt_two_pow_wordSize (c := 3) (by omega) S
  have h4S : 4 * (S + 2) ≤ (S + 2) ^ 3 := by
    have h1 : 4 ≤ (S + 2) ^ 2 := by
      calc 4 = 2 ^ 2 := rfl
        _ ≤ (S + 2) ^ 2 := Nat.pow_le_pow_left (by omega) 2
    have h2 : 4 * (S + 2) ≤ (S + 2) * (S + 2) ^ 2 := by
      simpa [Nat.mul_comm] using Nat.mul_le_mul_left (S + 2) h1
    simpa [Nat.pow_succ, Nat.mul_comm] using h2
  have hw_bound : 4 * (S + 2) < 2 ^ w := Nat.lt_of_le_of_lt h4S hpow3
  have h0_w : 0 < 2 ^ w := by omega
  have hw : 1 < 2 ^ w := by omega
  have hw2 : 2 < 2 ^ w := by omega
  have hn_w : x.n < 2 ^ w := by omega
  have h2n_w : 2 * x.n < 2 ^ w := by omega
  have h1n_w : 1 + x.n < 2 ^ w := by omega
  have h3n1_w : 1 + 3 * x.n < 2 ^ w := by omega
  have hm_w : edges.length < 2 ^ w := by omega
  have h2m_w : 2 * edges.length < 2 ^ w := by omega
  have hm2_w : 2 + 2 * edges.length < 2 ^ w := by omega
  have hm2n_w : 2 + 2 * edges.length + x.n < 2 ^ w := by omega
  have hm22n_w : 2 + 2 * edges.length + 2 * x.n < 2 ^ w := by omega
  have hk_w : x.k < 2 ^ w := by omega
  let extra := bitSetList x.A ++ bitSetList x.B ++ [x.k]
  have hin₀ : s₀.arrs inArr = [x.n, edges.length] ++ flatEdges edges ++ extra := by
    simpa [encDisjointPathsIn, encGraph, edges, extra, List.append_assoc] using hs₀
  -- 1. parseGraphProg 2 3 4 5 0
  rcases Triple.parseGraphProg_spec (w := w) x.G edges extra 2 3 4 5 0 hedges
      (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      hw2 hn_w hm2_w s₀ hin₀ with
    ⟨s₁, t₁, hex₁, ht₁, hin₁, hrn₁, hrm₁, hadj₁, hent₁, _⟩
  dsimp only at ht₁
  -- 2. readSliceProg for A into array 6
  have hin₁_A : s₁.arrs inArr =
      ([x.n, edges.length] ++ flatEdges edges) ++ bitSetList x.A ++ (bitSetList x.B ++ [x.k]) := by
    simpa [extra, List.append_assoc] using hin₁
  have hbitA_w : ∀ v ∈ bitSetList x.A, v < 2 ^ w := by
    intro v hv
    rcases List.mem_iff_getElem.mp hv with ⟨i, hi, rfl⟩
    have := getElem_bitSetList_le_one x.A i hi
    omega
  rcases readSliceProg_exec (w := w) (off := 2 + 2 * edges.length) inArr 6
      (.op .add (.const 2) (.op .mul (.const 2) (.reg 1))) 0 2
      (by decide) (by omega)
      ([x.n, edges.length] ++ flatEdges edges) (bitSetList x.A) (bitSetList x.B ++ [x.k])
      (by simp [length_flatEdges]; omega) (length_bitSetList x.A) hbitA_w hw hm2n_w
      (by simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hrm₁, hw2, hm_w, h2m_w, hm2_w])
      hin₁_A hrn₁ with
    ⟨s₂, t₂, hex₂, ht₂, harr6₂, harr_ne₂, hreg_lt₂⟩
  dsimp [Expr.cost] at ht₂
  -- 3. readSliceProg for B into array 7
  have hrn₂ : s₂.regs 0 = x.n := by rw [hreg_lt₂ 0 (by omega), hrn₁]
  have hrm₂ : s₂.regs 1 = edges.length := by rw [hreg_lt₂ 1 (by omega), hrm₁]
  have hin₂_B : s₂.arrs inArr =
      ([x.n, edges.length] ++ flatEdges edges ++ bitSetList x.A) ++ bitSetList x.B ++ [x.k] := by
    rw [harr_ne₂ inArr (by decide)]
    simpa [extra, List.append_assoc] using hin₁
  have hbitB_w : ∀ v ∈ bitSetList x.B, v < 2 ^ w := by
    intro v hv
    rcases List.mem_iff_getElem.mp hv with ⟨i, hi, rfl⟩
    have := getElem_bitSetList_le_one x.B i hi
    omega
  rcases readSliceProg_exec (w := w) (off := 2 + 2 * edges.length + x.n) inArr 7
      (.op .add (.op .add (.const 2) (.op .mul (.const 2) (.reg 1))) (.reg 0)) 0 2
      (by decide) (by omega)
      ([x.n, edges.length] ++ flatEdges edges ++ bitSetList x.A) (bitSetList x.B) [x.k]
      (by simp [length_flatEdges]; omega) (length_bitSetList x.B) hbitB_w hw (by omega)
      (by simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hrm₂, hrn₂,
        hw2, hm_w, h2m_w, hm2_w, hn_w, hm2n_w])
      hin₂_B hrn₂ with
    ⟨s₃, t₃, hex₃, ht₃, harr7₃, harr_ne₃, hreg_lt₃⟩
  dsimp [Expr.cost] at ht₃
  have hrn₃ : s₃.regs 0 = x.n := by rw [hreg_lt₃ 0 (by omega), hrn₂]
  have hrm₃ : s₃.regs 1 = edges.length := by rw [hreg_lt₃ 1 (by omega), hrm₂]
  have hin₃ : s₃.arrs inArr =
      [x.n, edges.length] ++ flatEdges edges ++ bitSetList x.A ++ bitSetList x.B ++ [x.k] := by
    rw [harr_ne₃ inArr (by decide), hin₂_B]
  -- 4. Set r_14 := n, r_15 := 2 * n, r_16 := k, r_17 := 0, r_18 := 1
  let s₄ := s₃.setReg 14 x.n
  have hex₄ : Exec w (.assign 14 (.reg 0)) s₃ s₄ 2 :=
    .assign (by simp [Expr.eval, checkWord, hrn₃, hn_w])
  let s₅ := s₄.setReg 15 (2 * x.n)
  have hex₅ : Exec w (.assign 15 (.op .mul (.const 2) (.reg 0))) s₄ s₅ 4 :=
    .assign (by
      simp [s₄, State.setReg, Expr.eval, BinOp.eval, BinOp.raw, checkWord,
        hrn₃, hw2, hn_w, h2n_w])
  obtain ⟨hlen_k, hget_k⟩ := inArr_getElem_k edges x.A x.B x.k hin₃
  let s₆ := s₅.setReg 16 x.k
  have hex₆ : Exec w (.assign 16 (.read inArr
      (.op .add (.op .add (.const 2) (.op .mul (.const 2) (.reg 1))) (.reg 15)))) s₅ s₆ 9 :=
    .assign (by
      simp [s₅, s₄, State.setReg, Expr.eval, BinOp.eval, BinOp.raw, checkWord,
        hrm₃, hw2, hm_w, h2m_w, hm2_w, h2n_w, hm22n_w, hlen_k, hget_k, hk_w])
  let s₇ := s₆.setReg 17 0
  have hex₇ : Exec w (.assign 17 (.const 0)) s₆ s₇ 2 :=
    .assign (by simp [Expr.eval, checkWord, h0_w])
  let s₈ := s₇.setReg 18 1
  have hex₈ : Exec w (.assign 18 (.const 1)) s₇ s₈ 2 :=
    .assign (by simp [Expr.eval, checkWord, hw])
  have hconst₈ : ConstRegs x.n x.k 2 s₈ := by
    refine ⟨by simp [s₈, s₇, s₆, s₅, s₄, State.setReg],
      by simp [s₈, s₇, s₆, s₅, State.setReg],
      by simp [s₈, s₇, s₆, State.setReg]⟩
  -- 5. initPathSystemRegProg 8 2
  rcases initPathSystemRegProg_exec (w := w) x.G x.A x.B 8 2 hw hn_w hconst₈ with
    ⟨s₉, t₉, hex₉, ht₉, hconst₉, hsys₉, hcard₉, harr₉, hreg₉⟩
  have harr9_lt8 : ∀ a : ℕ, a < 8 → s₉.arrs a = s₃.arrs a := by
    intro a ha
    rw [harr₉ a ha]
    rfl
  have hadj₉ : IsAdjList x.G 3 4 5 (edgeNeighbors edges) s₉ := by
    apply hadj₁.of_arrs_eq
    · rw [harr9_lt8 3 (by omega), harr_ne₃ 3 (by decide), harr_ne₂ 3 (by decide)]
    · rw [harr9_lt8 4 (by omega), harr_ne₃ 4 (by decide), harr_ne₂ 4 (by decide)]
    · rw [harr9_lt8 5 (by omega), harr_ne₃ 5 (by decide), harr_ne₂ 5 (by decide)]
  have hent₉ : (s₉.arrs 5).length < 2 ^ w := by
    rw [harr9_lt8 5 (by omega), harr_ne₃ 5 (by decide), harr_ne₂ 5 (by decide), hent₁]
    exact h2m_w
  have hA_bit₉ : IsBitSet x.A 6 s₉ := by
    apply IsBitSet.of_bitSetList
    rw [harr9_lt8 6 (by omega), harr_ne₃ 6 (by decide), harr6₂]
  have hB_bit₉ : IsBitSet x.B 7 s₉ := by
    apply IsBitSet.of_bitSetList
    rw [harr9_lt8 7 (by omega), harr7₃]
  have hr17_₉ : s₉.regs 17 = 0 := by
    rw [hreg₉ 17 (by omega)]
    simp [s₈, s₇, State.setReg]
  have hr18_₉ : s₉.regs 18 = 1 := by
    rw [hreg₉ 18 (by omega)]
    simp [s₈, State.setReg]
  -- 6. mengerLoopRegProg 3 4 5 6 7 8 2
  rcases mengerLoopRegProg_exec (w := w) x.G (edgeNeighbors edges) x.A x.B
      3 4 5 6 7 8 2 (by omega) (by omega) (by omega) (by omega) (by omega)
      hw h2n_w hk_w x.k 0 (by omega)
      hconst₉ hadj₉ hent₉ hA_bit₉ hB_bit₉ hsys₉ hcard₉ hr17_₉ hr18_₉ with
    ⟨s₁₀, t₁₀, hex₁₀, ht₁₀, hconst₁₀, _, _, hres₁₀⟩
  -- 7. mengerOutputRegProg 8 2
  rcases hres₁₀ with ⟨hok1, used', pred', succ', hsys₁₀, hcard₁₀⟩ |
      ⟨hok0, used', pred', succ', items, hsys₁₀, hcard_lt₁₀, hvis₁₀, hpar₁₀, hclosed₁₀, hinit₁₀, hnoB₁₀⟩
  · have hcond_out : (Expr.reg 18).eval w s₁₀ = some 1 := by
      simp [Expr.eval, checkWord, hok1, hw]
    rcases writePathSystemOutProg_exec (w := w) x.G x.A x.B used' pred' succ' 8 2
        (by decide) hw h3n1_w hconst₁₀ hsys₁₀ with
      ⟨s₁₁, t₁₁, hex₁₁, ht₁₁, hout₁₁⟩
    have hex_out : Exec w (mengerOutputRegProg 8 2) s₁₀ s₁₁ (1 + t₁₁) :=
      .ite_true hcond_out (by omega) hex₁₁
    have hvalid := isValidDisjointPathsOutput_of_pathSystem x hsys₁₀ hcard₁₀ hout₁₁
    have htime :
        t₁ + (t₂ + (t₃ + (2 + (4 + (9 + (2 + (2 + (t₉ + (t₁₀ + (1 + t₁₁)))))))))) ≤ 450 * S := by
      have htot_le : totalAdjEntries (edgeNeighbors edges) = 2 * edges.length := htot_eq
      have hloop_le :
          x.k * (65 + 264 * x.n + 31 * totalAdjEntries (edgeNeighbors edges)) ≤
            x.k * (264 * (x.n + edges.length + 1)) := by
        rw [htot_le]
        apply Nat.mul_le_mul_left
        omega
      have hk_le : x.k * (x.n + edges.length + 1) ≤ S := by
        rw [hS_eq, Nat.add_mul, Nat.one_mul]
        omega
      have hk_nm_le : x.k * (264 * (x.n + edges.length + 1)) ≤ 264 * S := by
        rw [Nat.mul_left_comm x.k 264]
        omega
      omega
    exact ⟨s₁₁, _,
      .seq hex₁ (.seq hex₂ (.seq hex₃ (.seq hex₄ (.seq hex₅
        (.seq hex₆ (.seq hex₇ (.seq hex₈ (.seq hex₉ (.seq hex₁₀ hex_out))))))))),
      htime, hvalid⟩
  · have hcond_out : (Expr.reg 18).eval w s₁₀ = some 0 := by
      simp [Expr.eval, checkWord, hok0, h0_w]
    rcases writeResCutOutProg_exec (w := w) 8 2 (by decide) hw h2n_w h1n_w hconst₁₀ hvis₁₀ with
      ⟨s₁₁, t₁₁, hex₁₁, ht₁₁, hout₁₁⟩
    have hex_out : Exec w (mengerOutputRegProg 8 2) s₁₀ s₁₁ (1 + t₁₁) :=
      .ite_false hcond_out hex₁₁
    have hvalid := isValidDisjointPathsOutput_of_resCut x hsys₁₀.1 hcard_lt₁₀
      hpar₁₀.2.1 hclosed₁₀ hinit₁₀ hnoB₁₀ hout₁₁
    have htime :
        t₁ + (t₂ + (t₃ + (2 + (4 + (9 + (2 + (2 + (t₉ + (t₁₀ + (1 + t₁₁)))))))))) ≤ 450 * S := by
      have htot_le : totalAdjEntries (edgeNeighbors edges) = 2 * edges.length := htot_eq
      have hloop_le :
          x.k * (65 + 264 * x.n + 31 * totalAdjEntries (edgeNeighbors edges)) ≤
            x.k * (264 * (x.n + edges.length + 1)) := by
        rw [htot_le]
        apply Nat.mul_le_mul_left
        omega
      have hk_le : x.k * (x.n + edges.length + 1) ≤ S := by
        rw [hS_eq, Nat.add_mul, Nat.one_mul]
        omega
      have hk_nm_le : x.k * (264 * (x.n + edges.length + 1)) ≤ 264 * S := by
        rw [Nat.mul_left_comm x.k 264]
        omega
      omega
    exact ⟨s₁₁, _,
      .seq hex₁ (.seq hex₂ (.seq hex₃ (.seq hex₄ (.seq hex₅
        (.seq hex₆ (.seq hex₇ (.seq hex₈ (.seq hex₉ (.seq hex₁₀ hex_out))))))))),
      htime, hvalid⟩

end GraphMinor.Compute
