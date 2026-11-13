module

public import GraphMinor.Compute.Case3StepsRecordOwnerBody
import GraphMinor.Compute.Case3StepsRewriteBuffer
import Mathlib.Data.List.GetD

/-!
# Recording the first containing member for all vertices

For one member bitset, the scan replaces missing owner entries by its label.
Previously assigned entries survive. A completed-prefix invariant proves the
exact owner array after the scan, using linear time and one loop register.
-/

@[expose] public section

namespace GraphMinor.Compute

/-- Replace just the missing owners of vertices present in the current member. -/
noncomputable def case3RecordOwnerList {n : ℕ} (S : Finset (Fin n))
    (old : List ℕ) (label missing : ℕ) : List ℕ := by
  classical
  exact List.ofFn (fun u : Fin n =>
    if u ∈ S ∧ old.getD u.1 0 = missing then label else old.getD u.1 0)

/-- Scan all vertices, retaining owners assigned by earlier members. -/
def case3RecordOwnerProg (a_set a_owner r_n r_i r_group r_missing : ℕ) : Cmd :=
  .seq (.assign r_i (.const 0))
    (forUp r_i (.reg r_n) (case3RecordOwnerBody a_set a_owner r_i r_group r_missing))

private theorem recordOwnerLoop_exec {w n : ℕ} (S : Finset (Fin n))
    (old : List ℕ) (label missing : ℕ) (hlen : old.length = n)
    (a_set a_owner r_n r_i r_group r_missing : ℕ) (ha : a_set ≠ a_owner)
    (hni : r_n ≠ r_i) (hgi : r_group ≠ r_i) (hmi : r_missing ≠ r_i)
    (hw : 1 < 2 ^ w) (hn : n < 2 ^ w) (hlabel : label < 2 ^ w)
    (hmissing : missing < 2 ^ w) (hwords : ∀ z ∈ old, z < 2 ^ w)
    (rem k : ℕ) (hrem : k + rem = n) {s : State}
    (hset : IsBitSet S a_set s)
    (hbuf : s.arrs a_owner = (case3RecordOwnerList S old label missing).take k ++ old.drop k)
    (hrn : s.regs r_n = n) (hri : s.regs r_i = k)
    (hrg : s.regs r_group = label) (hrm : s.regs r_missing = missing) :
    ∃ s' t, Exec w (forUp r_i (.reg r_n)
      (case3RecordOwnerBody a_set a_owner r_i r_group r_missing)) s s' t ∧
      t ≤ 3 + 19 * rem ∧ s'.arrs a_owner = case3RecordOwnerList S old label missing := by
  classical
  have h0 : 0 < 2 ^ w := by omega
  have hnewlen : (case3RecordOwnerList S old label missing).length = n := by
    simp only [case3RecordOwnerList, List.length_ofFn]
  induction rem generalizing k s with
  | zero =>
    have hk : k = n := by omega
    have hc : (Expr.op .lt (.reg r_i) (.reg r_n)).eval w s = some 0 := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hri, hrn, hk, hn, h0]
    refine ⟨s, 3, .while_false hc, by omega, ?_⟩
    have ht : (case3RecordOwnerList S old label missing).take n =
        case3RecordOwnerList S old label missing := List.take_of_length_le (by omega)
    have hd : old.drop n = [] := List.drop_eq_nil_of_le (by omega)
    simpa only [hk, ht, hd, List.append_nil] using hbuf
  | succ rem ih =>
    have hk : k < n := by omega
    have hkw : k < 2 ^ w := hk.trans hn
    have hkpw : k + 1 < 2 ^ w := (by omega : k + 1 ≤ n).trans_lt hn
    have hc : (Expr.op .lt (.reg r_i) (.reg r_n)).eval w s = some 1 := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hri, hrn, hk, hkw, hn, hw]
    have hold : old.getD k 0 < 2 ^ w := by
      rw [List.getD_eq_getElem _ 0 (by omega)]
      exact hwords _ (List.getElem_mem (by omega))
    have hcur : (s.arrs a_owner).getD k 0 = old.getD k 0 := by
      rw [hbuf]
      exact case3RewriteBuffer_getD old _ k (by omega)
    have hcurlen : (s.arrs a_owner).length = n := by
      rw [hbuf, List.length_append, List.length_take, List.length_drop, hnewlen, hlen,
        Nat.min_eq_left hk.le]
      omega
    obtain ⟨tB, hexB, htB⟩ := case3RecordOwnerBody_exec S a_set a_owner r_i r_group r_missing
      k (old.getD k 0) label missing hk hw hn hold hlabel hmissing hset hcurlen hcur hri hrg hrm
    let value := if (⟨k, hk⟩ : Fin n) ∈ S ∧ old.getD k 0 = missing then label else old.getD k 0
    let sB := s.writeArr a_owner k value
    let sC := sB.setReg r_i (k + 1)
    have hexC : Exec w (.assign r_i (.op .add (.reg r_i) (.const 1))) sB sC 4 :=
      .assign (by simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, sB, hri, hkw, hw, hkpw])
    have hbufC : sC.arrs a_owner =
        (case3RecordOwnerList S old label missing).take (k + 1) ++ old.drop (k + 1) := by
      simp only [sC, sB, State.setReg_arrs, State.writeArr_arrs_self]
      rw [hbuf]
      have hs := case3RewriteBuffer_set old (case3RecordOwnerList S old label missing)
        (by omega) k (by omega)
      simpa only [case3RecordOwnerList, List.getElem_ofFn, value] using hs
    obtain ⟨s', t, hex, ht, hdst⟩ := ih (k + 1) (by omega) (s := sC)
      (hset.of_arr_eq (State.writeArr_arrs_ne _ _ _ ha)) hbufC
      (by simp only [sC, sB, State.setReg_regs_ne _ _ hni, State.writeArr_regs, hrn])
      (State.setReg_regs_self ..)
      (by simp only [sC, sB, State.setReg_regs_ne _ _ hgi, State.writeArr_regs, hrg])
      (by simp only [sC, sB, State.setReg_regs_ne _ _ hmi, State.writeArr_regs, hrm])
    exact ⟨s', 3 + (tB + 4) + t, .while_true hc (by decide) (.seq hexB hexC) hex,
      by omega, hdst⟩

/-- One member updates the loop-owner table in at most `19 n + 5` steps. -/
theorem case3RecordOwnerProg_exec {w n : ℕ} (S : Finset (Fin n))
    (old : List ℕ) (label missing : ℕ) (hlen : old.length = n)
    (a_set a_owner r_n r_i r_group r_missing : ℕ) (ha : a_set ≠ a_owner)
    (hni : r_n ≠ r_i) (hgi : r_group ≠ r_i) (hmi : r_missing ≠ r_i)
    (hw : 1 < 2 ^ w) (hn : n < 2 ^ w) (hlabel : label < 2 ^ w)
    (hmissing : missing < 2 ^ w) (hwords : ∀ z ∈ old, z < 2 ^ w)
    {s : State} (hset : IsBitSet S a_set s) (hbuf : s.arrs a_owner = old)
    (hrn : s.regs r_n = n) (hrg : s.regs r_group = label) (hrm : s.regs r_missing = missing) :
    ∃ s' t, Exec w (case3RecordOwnerProg a_set a_owner r_n r_i r_group r_missing) s s' t ∧
      t ≤ 19 * n + 5 ∧ s'.arrs a_owner = case3RecordOwnerList S old label missing ∧
      (∀ a, a ≠ a_owner → s'.arrs a = s.arrs a) ∧
      (∀ r, r ≠ r_i → s'.regs r = s.regs r) := by
  have h0 : 0 < 2 ^ w := by omega
  let s₁ := s.setReg r_i 0
  have hex₁ : Exec w (.assign r_i (.const 0)) s s₁ 2 :=
    .assign (by simp only [Expr.eval, checkWord, h0, ↓reduceIte])
  obtain ⟨s₂, t₂, hex₂, ht₂, hdst₂⟩ := recordOwnerLoop_exec S old label missing hlen
    a_set a_owner r_n r_i r_group r_missing ha hni hgi hmi hw hn hlabel hmissing hwords
    n 0 (by omega) (s := s₁) hset
    (by simp only [s₁, State.setReg_arrs, List.take_zero, List.drop_zero, List.nil_append, hbuf])
    (by rw [State.setReg_regs_ne _ _ hni]; exact hrn) (State.setReg_regs_self ..)
    (by rw [State.setReg_regs_ne _ _ hgi]; exact hrg)
    (by rw [State.setReg_regs_ne _ _ hmi]; exact hrm)
  have hex := Exec.seq hex₁ hex₂
  refine ⟨s₂, 2 + t₂, hex, by omega, hdst₂, ?_, ?_⟩
  · intro a ha'
    exact hex.arrs_eq_of_not_mem_writtenArrs (by
      simp [case3RecordOwnerProg, case3RecordOwnerBody, forUp, Cmd.writtenArrs, ha'])
  · intro r hr
    exact hex.regs_eq_of_not_mem_writtenRegs (by
      simp [case3RecordOwnerProg, case3RecordOwnerBody, forUp, Cmd.writtenRegs, hr])

end GraphMinor.Compute
