module

public import GraphMinor.Compute.Case3StepsFindBoundaryBody

/-!
# Finding the first component with a given boundary

The scan keeps the vertex count as a sentinel until it encounters a matching
outside component. It then retains that first seed. This supplies a common
representative for equal attachment keys and detects core-edge boundaries
that need a separate member.
-/

@[expose] public section

namespace GraphMinor.Compute

/-- Find the least outside seed matching the target boundary key. -/
def case3FindBoundaryProg (a_Z a_keys a_target r_n r_i r_res : ℕ) : Cmd :=
  .seq (.assign r_res (.reg r_n))
    (.seq (.assign r_i (.const 0))
      (forUp r_i (.reg r_n) (case3FindBoundaryBody a_Z a_keys a_target r_n r_i r_res)))

private theorem findBoundaryLoop_exec {w : ℕ} (x : Alg81Input)
    (d : Alg86DivisionOutput x) (hd : IsValidAlg86DivisionOutput x d)
    (bd : Finset (Fin x.n)) (hbd : bd.card ≤ 3)
    (a_Z a_keys a_target r_n r_i r_res : ℕ)
    (hni : r_n ≠ r_i) (hnr : r_n ≠ r_res) (hir : r_i ≠ r_res)
    (hw : 4 < 2 ^ w) (hn : x.n + 1 < 2 ^ w) (hkeys : x.n * 4 < 2 ^ w)
    (rem k r : ℕ) (hrem : k + rem = x.n) (hrr : r ≤ x.n)
    (hnone : r = x.n → ∀ v : Fin x.n, v.1 < k →
      ¬ (v ∉ d.core.Z ∧ case3AttachmentRowSet x d.core.Z v = bd))
    (hfound : ∀ h : r < x.n,
      (((⟨r, h⟩ : Fin x.n) ∉ d.core.Z ∧ case3AttachmentRowSet x d.core.Z ⟨r, h⟩ = bd) ∧
        ∀ v : Fin x.n, v.1 < r → ¬ (v ∉ d.core.Z ∧ case3AttachmentRowSet x d.core.Z v = bd)) ∧ r < k)
    {s : State} (hZ : IsBitSet d.core.Z a_Z s)
    (htab : s.arrs a_keys = case3AttachmentKeys x d.core.Z)
    (htarget : s.arrs a_target = case3BoundaryKey bd)
    (hrn : s.regs r_n = x.n) (hri : s.regs r_i = k) (hrres : s.regs r_res = r) :
    ∃ s' t, Exec w (forUp r_i (.reg r_n)
        (case3FindBoundaryBody a_Z a_keys a_target r_n r_i r_res)) s s' t ∧
      t ≤ 3 + 56 * rem ∧ s'.regs r_res =
        case3FirstIndex (fun v => v ∉ d.core.Z ∧ case3AttachmentRowSet x d.core.Z v = bd) := by
  classical
  have h0 : 0 < 2 ^ w := by omega
  have h1 : 1 < 2 ^ w := by omega
  have hnw : x.n < 2 ^ w := by omega
  induction rem generalizing k r s with
  | zero =>
    have hk : k = x.n := by omega
    have hc : (Expr.op .lt (.reg r_i) (.reg r_n)).eval w s = some 0 := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hri, hrn, hk, hnw, h0]
    refine ⟨s, 3, .while_false hc, by omega, ?_⟩
    rw [hrres]
    exact case3FirstIndex_unique _ r hrr
      (fun heq v => hnone heq v (by rw [hk]; exact v.2)) (fun h => (hfound h).1)
  | succ rem ih =>
    have hk : k < x.n := by omega
    have hkw : k < 2 ^ w := by omega
    have hkpw : k + 1 < 2 ^ w := by omega
    have hc : (Expr.op .lt (.reg r_i) (.reg r_n)).eval w s = some 1 := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hri, hrn, hk, hkw, hnw, h1]
    obtain ⟨sB, tB, hexB, htB, hresB, harrB, hregB⟩ :=
      case3FindBoundaryBody_exec x d hd bd hbd a_Z a_keys a_target r_n r_i r_res
        hw hnw hkeys k r hk hrr hZ htab htarget hrn hri hrres
    let r' := if r = x.n ∧ (⟨k, hk⟩ : Fin x.n) ∉ d.core.Z ∧
      case3AttachmentRowSet x d.core.Z ⟨k, hk⟩ = bd then k else r
    have hnext := case3FirstIndex_scan_step
      (fun v => v ∉ d.core.Z ∧ case3AttachmentRowSet x d.core.Z v = bd) k r hk hrr hnone hfound
    let sC := sB.setReg r_i (k + 1)
    have hriB : sB.regs r_i = k := (hregB r_i hir).trans hri
    have hexC : Exec w (.assign r_i (.op .add (.reg r_i) (.const 1))) sB sC 4 :=
      .assign (by simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hriB, hkw, h1, hkpw])
    obtain ⟨s', t, hex, ht, hdst⟩ := ih (k + 1) r' (by omega)
      (by simpa only [r'] using hnext.1)
      (by simpa only [r'] using hnext.2.1)
      (by simpa only [r'] using hnext.2.2)
      (s := sC) (hZ.of_arr_eq (harrB a_Z))
      ((harrB a_keys).trans htab) ((harrB a_target).trans htarget)
      (by rw [State.setReg_regs_ne _ _ hni, hregB r_n hnr, hrn])
      (State.setReg_regs_self ..)
      (by rw [State.setReg_regs_ne _ _ hir.symm]; exact hresB)
    exact ⟨s', 3 + (tB + 4) + t, .while_true hc (by decide) (.seq hexB hexC) hex, by omega, hdst⟩

/-- A boundary representative is found in at most `56 n + 7` steps. The
search changes no arrays and only its index and result registers. -/
theorem case3FindBoundaryProg_exec {w : ℕ} (x : Alg81Input)
    (d : Alg86DivisionOutput x) (hd : IsValidAlg86DivisionOutput x d)
    (bd : Finset (Fin x.n)) (hbd : bd.card ≤ 3)
    (a_Z a_keys a_target r_n r_i r_res : ℕ)
    (hni : r_n ≠ r_i) (hnr : r_n ≠ r_res) (hir : r_i ≠ r_res)
    (hw : 4 < 2 ^ w) (hn : x.n + 1 < 2 ^ w) (hkeys : x.n * 4 < 2 ^ w)
    {s : State} (hZ : IsBitSet d.core.Z a_Z s)
    (htab : s.arrs a_keys = case3AttachmentKeys x d.core.Z)
    (htarget : s.arrs a_target = case3BoundaryKey bd) (hrn : s.regs r_n = x.n) :
    ∃ s' t, Exec w (case3FindBoundaryProg a_Z a_keys a_target r_n r_i r_res) s s' t ∧
      t ≤ 56 * x.n + 7 ∧ s'.regs r_res =
        case3FirstIndex (fun v => v ∉ d.core.Z ∧ case3AttachmentRowSet x d.core.Z v = bd) ∧
      (∀ a, s'.arrs a = s.arrs a) ∧
      (∀ r, r ≠ r_i → r ≠ r_res → s'.regs r = s.regs r) := by
  have h0 : 0 < 2 ^ w := by omega
  have hnw : x.n < 2 ^ w := by omega
  let s₁ := s.setReg r_res x.n
  let s₂ := s₁.setReg r_i 0
  have hex₁ : Exec w (.assign r_res (.reg r_n)) s s₁ 2 :=
    .assign (by simp only [Expr.eval, checkWord, hrn, hnw, ↓reduceIte])
  have hex₂ : Exec w (.assign r_i (.const 0)) s₁ s₂ 2 :=
    .assign (by simp only [Expr.eval, checkWord, h0, ↓reduceIte])
  obtain ⟨s₃, t₃, hex₃, ht₃, hres₃⟩ := findBoundaryLoop_exec x d hd bd hbd
    a_Z a_keys a_target r_n r_i r_res hni hnr hir hw hn hkeys x.n 0 x.n
    (by omega) le_rfl (fun _ _ hlt => by omega) (fun h => by omega) (s := s₂)
    (hZ.of_arr_eq rfl) htab htarget
    (by simp only [s₂, s₁, State.setReg_regs_ne _ _ hni, State.setReg_regs_ne _ _ hnr, hrn])
    (State.setReg_regs_self ..)
    (by simp only [s₂, s₁, State.setReg_regs_ne _ _ hir.symm, State.setReg_regs_self])
  have hex : Exec w (case3FindBoundaryProg a_Z a_keys a_target r_n r_i r_res) s s₃ (2 + (2 + t₃)) :=
    .seq hex₁ (.seq hex₂ hex₃)
  refine ⟨s₃, 2 + (2 + t₃), hex, by omega, hres₃, ?_, ?_⟩
  · intro a
    exact hex.arrs_eq_of_not_mem_writtenArrs (by
      simp [case3FindBoundaryProg, case3FindBoundaryBody, forUp, Cmd.writtenArrs])
  · intro r hi hr
    exact hex.regs_eq_of_not_mem_writtenRegs (by
      simp [case3FindBoundaryProg, case3FindBoundaryBody, forUp, Cmd.writtenRegs, hi, hr])

end GraphMinor.Compute
