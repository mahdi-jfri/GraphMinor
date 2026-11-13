module

public import GraphMinor.Compute.Case3StepsLoopOwnerBody
public import GraphMinor.Compute.Algorithm33Multigraph

/-!
# Computing all loop-owner labels

The program initializes one missing owner per vertex, then scans the selected
member labels in order. Each selected member records its still-unassigned
vertices. The result is the exact first-containing-member table in time
proportional to the vertex count times the candidate count. This supplies
the loop choice when restoring the multigraph in XIII (9.9), step 5, p. 105.
-/

@[expose] public section

namespace GraphMinor.Compute

local macro "romega" : tactic => `(tactic| ((try dsimp only [Reg, Arr] at *); omega))

/-- Initialize missing owners and visit all selected groups in numeric order. -/
def case3LoopOwnersProg : Cmd :=
  .seq (fillArrProg 33 14 52 63)
    (.seq (.assign 54 (.const 0)) (forUp 54 (.reg 52) case3LoopOwnerBody))

private theorem loopOwnersLoop_exec {w : ℕ} (x : Alg81Input)
    (d : Alg86DivisionOutput x) (hd : IsValidAlg86DivisionOutput x d)
    (hw : 4 < 2 ^ w) (hn : x.n + 1 < 2 ^ w) (hkeys : x.n * 4 < 2 ^ w)
    (hm : 2 + 2 * (case3InputEdges x).length < 2 ^ w)
    (hsize : x.n + (case3InputEdges x).length < 2 ^ w)
    (rem k : ℕ) (hrem : k + rem = x.n + (case3InputEdges x).length) {s : State}
    (hin : s.arrs 16 = encGraph x.G) (hZ : IsBitSet d.core.Z 10 s)
    (htab : s.arrs 26 = case3AttachmentKeys x d.core.Z)
    (hreps : s.arrs 27 = case3ComponentRepList x d.core.Z)
    (hmask : IsBitSet (case3GroupLabelSet x d.core.Z) 29 s)
    (hrn : s.regs 14 = x.n) (hrL : s.regs 52 = x.n + (case3InputEdges x).length)
    (hri : s.regs 54 = k) (howners : s.arrs 33 = case3LoopOwnerPrefix x d.core.Z k) :
    ∃ s' t, Exec w (forUp 54 (.reg 52) case3LoopOwnerBody) s s' t ∧
      t ≤ 3 + rem * (77 * x.n + 111) ∧
      s'.arrs 33 = case3LoopOwnerPrefix x d.core.Z (x.n + (case3InputEdges x).length) ∧
      (∀ a, a ≠ 25 → a ≠ 30 → a ≠ 33 → s'.arrs a = s.arrs a) ∧
      (∀ r, r < 13 ∨ r = 14 ∨ r = 17 ∨ r = 52 ∨ 64 ≤ r → s'.regs r = s.regs r) := by
  have h0 : 0 < 2 ^ w := by omega
  have h1 : 1 < 2 ^ w := by omega
  induction rem generalizing k s with
  | zero =>
    have hk : k = x.n + (case3InputEdges x).length := by omega
    have hc : (Expr.op .lt (.reg 54) (.reg 52)).eval w s = some 0 := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hri, hrL, hk, hsize, h0]
    exact ⟨s, 3, .while_false hc, by omega, hk ▸ howners,
      fun _ _ _ _ => rfl, fun _ _ => rfl⟩
  | succ rem ih =>
    have hk : k < x.n + (case3InputEdges x).length := by omega
    have hkw : k < 2 ^ w := hk.trans hsize
    have hkpw : k + 1 < 2 ^ w := (by omega : k + 1 ≤ x.n + (case3InputEdges x).length).trans_lt hsize
    have hc : (Expr.op .lt (.reg 54) (.reg 52)).eval w s = some 1 := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hri, hrL, hk, hkw, hsize, h1]
    let q : Fin (x.n + (case3InputEdges x).length) := ⟨k, hk⟩
    let i := (case3GroupLabelEquiv x).symm q
    have hlabel : case3RawIndexLabel x i = k := by
      rw [← case3GroupLabelEquiv_val]
      exact congrArg Fin.val ((case3GroupLabelEquiv x).apply_symm_apply q)
    obtain ⟨sB, tB, hexB, htB, hownersB, harrB, hregB⟩ :=
      case3LoopOwnerBody_exec x d hd i hw hn hkeys hm hsize hin hZ htab hreps hmask hrn
        (by rw [hlabel]; exact hri) hrL (by rw [hlabel]; exact howners)
    let sC := sB.setReg 54 (k + 1)
    have hexC : Exec w (.assign 54 (.op .add (.reg 54) (.const 1))) sB sC 4 :=
      .assign (by simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord,
        hregB 54 (by decide), hri, hkw, h1, hkpw])
    obtain ⟨s', t, hex, ht, hdst, harr, hreg⟩ := ih (k + 1) (by omega) (s := sC)
      ((harrB 16 (by decide) (by decide) (by decide)).trans hin)
      (hZ.of_arr_eq (harrB 10 (by decide) (by decide) (by decide)))
      ((harrB 26 (by decide) (by decide) (by decide)).trans htab)
      ((harrB 27 (by decide) (by decide) (by decide)).trans hreps)
      (hmask.of_arr_eq (harrB 29 (by decide) (by decide) (by decide)))
      (by rw [State.setReg_regs_ne _ _ (by decide), hregB 14 (by decide)]; exact hrn)
      (by rw [State.setReg_regs_ne _ _ (by decide), hregB 52 (by decide)]; exact hrL)
      (State.setReg_regs_self ..) (by simpa only [sC, State.setReg_arrs, hlabel] using hownersB)
    refine ⟨s', 3 + (tB + 4) + t, .while_true hc (by decide) (.seq hexB hexC) hex,
      by rw [Nat.succ_mul]; omega, hdst, ?_, ?_⟩
    · intro a h25 h30 h33
      exact (harr a h25 h30 h33).trans (harrB a h25 h30 h33)
    · intro r hr
      rw [hreg r hr, State.setReg_regs_ne _ _ (by romega)]
      exact hregB r (by romega)

/-- The complete loop-owner table is computed with one vertex scan per
candidate and no work proportional to expanded edge multiplicities. -/
theorem case3LoopOwnersProg_exec {w : ℕ} (x : Alg81Input)
    (d : Alg86DivisionOutput x) (hd : IsValidAlg86DivisionOutput x d)
    (hw : 4 < 2 ^ w) (hn : x.n + 1 < 2 ^ w) (hkeys : x.n * 4 < 2 ^ w)
    (hm : 2 + 2 * (case3InputEdges x).length < 2 ^ w)
    (hsize : x.n + (case3InputEdges x).length < 2 ^ w) {s : State}
    (hin : s.arrs 16 = encGraph x.G) (hZ : IsBitSet d.core.Z 10 s)
    (htab : s.arrs 26 = case3AttachmentKeys x d.core.Z)
    (hreps : s.arrs 27 = case3ComponentRepList x d.core.Z)
    (hmask : IsBitSet (case3GroupLabelSet x d.core.Z) 29 s)
    (hrn : s.regs 14 = x.n) (hrL : s.regs 52 = x.n + (case3InputEdges x).length) :
    ∃ s' t, Exec w case3LoopOwnersProg s s' t ∧
      t ≤ 11 * x.n + 11 + (x.n + (case3InputEdges x).length) * (77 * x.n + 111) ∧
      s'.arrs 33 = List.ofFn (case3OrderedLoopLabel x d.core.Z) ∧
      (∀ a, a ≠ 25 → a ≠ 30 → a ≠ 33 → s'.arrs a = s.arrs a) ∧
      (∀ r, r < 13 ∨ r = 14 ∨ r = 17 ∨ r = 52 ∨ 64 ≤ r → s'.regs r = s.regs r) := by
  have h0 : 0 < 2 ^ w := by omega
  obtain ⟨s₁, t₁, hex₁, ht₁, hfill₁, harr₁, hreg₁⟩ :=
    fillArrProg_exec 33 14 52 63 (by decide) (by decide) (by omega) (by omega) hsize hrn hrL
  let s₂ := s₁.setReg 54 0
  have hex₂ : Exec w (.assign 54 (.const 0)) s₁ s₂ 2 :=
    .assign (by simp only [Expr.eval, checkWord, h0, ↓reduceIte])
  obtain ⟨s₃, t₃, hex₃, ht₃, hdst₃, harr₃, hreg₃⟩ := loopOwnersLoop_exec x d hd
    hw hn hkeys hm hsize (x.n + (case3InputEdges x).length) 0 (by omega) (s := s₂)
    ((harr₁ 16 (by decide)).trans hin) (hZ.of_arr_eq (harr₁ 10 (by decide)))
    ((harr₁ 26 (by decide)).trans htab) ((harr₁ 27 (by decide)).trans hreps)
    (hmask.of_arr_eq (harr₁ 29 (by decide)))
    (by rw [State.setReg_regs_ne _ _ (by decide), hreg₁ 14 (by decide)]; exact hrn)
    (by rw [State.setReg_regs_ne _ _ (by decide), hreg₁ 52 (by decide)]; exact hrL)
    (State.setReg_regs_self ..)
    (hfill₁.trans (case3LoopOwnerPrefix_zero x d.core.Z).symm)
  refine ⟨s₃, t₁ + (2 + t₃), .seq hex₁ (.seq hex₂ hex₃), by omega,
    hdst₃.trans (case3LoopOwnerPrefix_done x d.core.Z), ?_, ?_⟩
  · intro a h25 h30 h33
    exact (harr₃ a h25 h30 h33).trans (harr₁ a h33)
  · intro r hr
    rw [hreg₃ r hr, State.setReg_regs_ne _ _ (by romega)]
    exact hreg₁ r (by romega)

end GraphMinor.Compute
