module

public import GraphMinor.Compute.Case3StepsSelfFlagBody
import GraphMinor.Compute.Case3StepsFlagBuffer

/-!
# Scanning a block of self-label flags

The program compares each source label with its offset index and writes the
result into a preallocated destination block. A completed-prefix invariant
proves the exact output, including the unchanged surrounding data. The two
blocks of the selected-group mask use this same linear scan.
-/

@[expose] public section

namespace GraphMinor.Compute

/-- Scan labels into a destination block whose offset is held in `r_off`. -/
def case3SelfFlagsProg (a_src a_dst r_len r_off r_i : ℕ) : Cmd :=
  .seq (.assign r_i (.const 0))
    (forUp r_i (.reg r_len) (case3SelfFlagBody a_src a_dst r_off r_i))

private theorem selfFlagsLoop_exec {w : ℕ} (labels pre suf : List ℕ) (off : ℕ)
    (hpre : pre.length = off) (a_src a_dst r_len r_off r_i : ℕ)
    (ha : a_src ≠ a_dst) (hni : r_len ≠ r_i) (hoi : r_off ≠ r_i)
    (hw : 1 < 2 ^ w) (hsize : off + labels.length < 2 ^ w)
    (hwords : ∀ z ∈ labels, z < 2 ^ w) (rem k : ℕ) (hrem : k + rem = labels.length)
    {s : State} (hsrc : s.arrs a_src = labels)
    (hbuf : s.arrs a_dst = pre ++ (case3SelfFlagList labels off).take k ++
      List.replicate (labels.length - k) 0 ++ suf)
    (hrn : s.regs r_len = labels.length) (hroff : s.regs r_off = off) (hri : s.regs r_i = k) :
    ∃ s' t, Exec w (forUp r_i (.reg r_len) (case3SelfFlagBody a_src a_dst r_off r_i)) s s' t ∧
      t ≤ 3 + 17 * rem ∧ s'.arrs a_dst = pre ++ case3SelfFlagList labels off ++ suf := by
  have h0 : 0 < 2 ^ w := by omega
  have hnw : labels.length < 2 ^ w := by omega
  induction rem generalizing k s with
  | zero =>
    have hk : k = labels.length := by omega
    have hc : (Expr.op .lt (.reg r_i) (.reg r_len)).eval w s = some 0 := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hri, hrn, hk, hnw, h0]
    refine ⟨s, 3, .while_false hc, by omega, ?_⟩
    have ht : (case3SelfFlagList labels off).take labels.length = case3SelfFlagList labels off :=
      List.take_of_length_le (by rw [case3SelfFlagList_length])
    simpa only [hk, ht, Nat.sub_self, List.replicate_zero, List.append_nil] using hbuf
  | succ rem ih =>
    have hk : k < labels.length := by omega
    have hkw : k < 2 ^ w := by omega
    have hkpw : k + 1 < 2 ^ w := by omega
    have hc : (Expr.op .lt (.reg r_i) (.reg r_len)).eval w s = some 1 := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hri, hrn, hk, hkw, hnw, hw]
    have hdlen : off + labels.length ≤ (s.arrs a_dst).length := by
      rw [hbuf]
      simp only [List.length_append, List.length_take, case3SelfFlagList_length,
        List.length_replicate, hpre, Nat.min_eq_left hk.le]
      omega
    let sB := s.writeArr a_dst (off + k) (if labels[k] = off + k then 1 else 0)
    let sC := sB.setReg r_i (k + 1)
    have hexB : Exec w (case3SelfFlagBody a_src a_dst r_off r_i) s sB 10 :=
      case3SelfFlagBody_exec labels off k hk a_src a_dst r_off r_i hw hsize hwords hsrc hdlen hroff hri
    have hexC : Exec w (.assign r_i (.op .add (.reg r_i) (.const 1))) sB sC 4 :=
      .assign (by simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, sB, hri, hkw, hw, hkpw])
    have hsrcC : sC.arrs a_src = labels := by
      simp only [sC, sB, State.setReg_arrs, State.writeArr_arrs_ne _ _ _ ha, hsrc]
    have hbufC : sC.arrs a_dst = pre ++ (case3SelfFlagList labels off).take (k + 1) ++
        List.replicate (labels.length - (k + 1)) 0 ++ suf := by
      simp only [sC, sB, State.setReg_arrs, State.writeArr_arrs_self]
      rw [hbuf]
      have hs := case3FlagBuffer_set pre (case3SelfFlagList labels off) suf k
        (by rw [case3SelfFlagList_length]; exact hk)
      simpa only [case3SelfFlagList_length, hpre, getElem_case3SelfFlagList labels off k hk] using hs
    obtain ⟨s', t, hex, ht, hdst⟩ := ih (k + 1) (by omega) hsrcC hbufC
      (by simp only [sC, sB, State.setReg_regs_ne _ _ hni, State.writeArr_regs, hrn])
      (by simp only [sC, sB, State.setReg_regs_ne _ _ hoi, State.writeArr_regs, hroff])
      (State.setReg_regs_self ..)
    exact ⟨s', 3 + (10 + 4) + t, .while_true hc (by decide) (.seq hexB hexC) hex, by omega, hdst⟩

/-- A block of self-label flags is written in `17 len + 5` steps. Only the
destination array and loop register change. -/
theorem case3SelfFlagsProg_exec {w : ℕ} (labels pre suf : List ℕ) (off : ℕ)
    (hpre : pre.length = off) (a_src a_dst r_len r_off r_i : ℕ)
    (ha : a_src ≠ a_dst) (hni : r_len ≠ r_i) (hoi : r_off ≠ r_i)
    (hw : 1 < 2 ^ w) (hsize : off + labels.length < 2 ^ w)
    (hwords : ∀ z ∈ labels, z < 2 ^ w) {s : State}
    (hsrc : s.arrs a_src = labels)
    (hbuf : s.arrs a_dst = pre ++ List.replicate labels.length 0 ++ suf)
    (hrn : s.regs r_len = labels.length) (hroff : s.regs r_off = off) :
    ∃ s' t, Exec w (case3SelfFlagsProg a_src a_dst r_len r_off r_i) s s' t ∧
      t ≤ 17 * labels.length + 5 ∧ s'.arrs a_dst = pre ++ case3SelfFlagList labels off ++ suf ∧
      (∀ a, a ≠ a_dst → s'.arrs a = s.arrs a) ∧
      (∀ r, r ≠ r_i → s'.regs r = s.regs r) := by
  have h0 : 0 < 2 ^ w := by omega
  let s₁ := s.setReg r_i 0
  have hex₁ : Exec w (.assign r_i (.const 0)) s s₁ 2 :=
    .assign (by simp only [Expr.eval, checkWord, h0, ↓reduceIte])
  obtain ⟨s₂, t₂, hex₂, ht₂, hdst₂⟩ := selfFlagsLoop_exec labels pre suf off hpre
    a_src a_dst r_len r_off r_i ha hni hoi hw hsize hwords labels.length 0 (by omega) (s := s₁)
    hsrc (by simpa only [s₁, State.setReg_arrs, List.take_zero, List.append_nil, Nat.sub_zero] using hbuf)
    (by simp only [s₁, State.setReg_regs_ne _ _ hni, hrn])
    (by simp only [s₁, State.setReg_regs_ne _ _ hoi, hroff]) (State.setReg_regs_self ..)
  have hex : Exec w (case3SelfFlagsProg a_src a_dst r_len r_off r_i) s s₂ (2 + t₂) := .seq hex₁ hex₂
  refine ⟨s₂, 2 + t₂, hex, by omega, hdst₂, ?_, ?_⟩
  · intro a ha'
    exact hex.arrs_eq_of_not_mem_writtenArrs (by
      simp [case3SelfFlagsProg, case3SelfFlagBody, forUp, Cmd.writtenArrs, ha'])
  · intro r hr
    exact hex.regs_eq_of_not_mem_writtenRegs (by
      simp [case3SelfFlagsProg, case3SelfFlagBody, forUp, Cmd.writtenRegs, hr])

end GraphMinor.Compute
