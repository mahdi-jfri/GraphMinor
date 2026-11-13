module

public import GraphMinor.Compute.Case3StepsComponentRowProg

/-!
# Computing the component table

The loop writes the outside-component row of each vertex in order. The
unwritten suffix remains zero, while the written prefix is the list of rows
already computed. This supplies the component searches in XIII (9.9),
step (5), page 104.
-/

@[expose] public section

namespace GraphMinor.Compute

local macro "romega" : tactic => `(tactic| ((try dsimp only [Reg, Arr] at *); omega))

/-- Allocate the square table and fill it in vertex order. -/
def case3ComponentTableProg (a_Z a_mat a_off r_base : ℕ) : Cmd :=
  .seq (.alloc a_mat (.op .mul (.reg r_base) (.reg r_base)))
    (.seq (.assign (r_base + 1) (.const 0))
      (forUp (r_base + 1) (.reg r_base)
        (case3ComponentRowProg a_Z a_mat a_off r_base)))

private theorem componentTableLoop_exec {w : ℕ} (x : Alg81Input)
    (Z : Finset (Fin x.n)) (lists : Fin x.n → List ℕ)
    (a_Z a_mat a_off r_base : ℕ)
    (haZ : a_Z < a_off) (haM : a_mat < a_off) (haZM : a_Z ≠ a_mat)
    (hw : 1 < 2 ^ w) (hn : x.n + 1 < 2 ^ w) (hsq : x.n * x.n < 2 ^ w)
    (rem k : ℕ) (hrem : k + rem = x.n) {s : State}
    (hZ : s.arrs a_Z = bitSetList Z)
    (hmat : s.arrs a_mat =
      (((List.finRange x.n).take k).flatMap (case3ComponentRow x Z)) ++
        List.replicate ((x.n - k) * x.n) 0)
    (hadj : IsAdjList (restrictGraph x.G (Finset.univ \ Z))
      (36 + a_off) (37 + a_off) (38 + a_off) lists s)
    (hent : (s.arrs (38 + a_off)).length < 2 ^ w)
    (hrn : s.regs r_base = x.n) (hrk : s.regs (r_base + 1) = k) :
    ∃ s' t,
      Exec w (forUp (r_base + 1) (.reg r_base)
        (case3ComponentRowProg a_Z a_mat a_off r_base)) s s' t ∧
      t ≤ 3 + rem * (38 * x.n + 26 * totalAdjEntries lists + 47) ∧
      s'.arrs a_mat = case3ComponentRows x Z ∧
      s'.regs r_base = x.n ∧
      (∀ a, a ≠ a_mat → a ≠ 31 + a_off → a ≠ 32 + a_off → s'.arrs a = s.arrs a) ∧
      (∀ r < r_base, s'.regs r = s.regs r) := by
  have h0 : 0 < 2 ^ w := by omega
  have hnw : x.n < 2 ^ w := by omega
  induction rem generalizing k s with
  | zero =>
    have hk : k = x.n := by omega
    have hc : (Expr.op .lt (.reg (r_base + 1)) (.reg r_base)).eval w s = some 0 := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hrk, hrn, hk, hnw, h0]
    refine ⟨s, 3, .while_false hc, by simp, ?_, hrn, fun _ _ _ _ => rfl, fun _ _ => rfl⟩
    simpa only [hk, case3ComponentRows_storage_done] using hmat
  | succ rem ih =>
    have hk : k < x.n := by omega
    have hkw : k < 2 ^ w := by omega
    have hkpw : k + 1 < 2 ^ w := by omega
    have hc : (Expr.op .lt (.reg (r_base + 1)) (.reg r_base)).eval w s = some 1 := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hrk, hrn, hk, hnw, hkw, hw]
    obtain ⟨sB, tB, hexB, htB, hmatB, hrnB, hrkB, harrB, hregB⟩ :=
      case3ComponentRowProg_exec x Z lists a_Z a_mat a_off r_base haZ haM haZM hw hn hsq
        k hk _ _ (case3ComponentRows_prefix_length x Z k (Nat.le_of_lt hk))
        hZ (hmat.trans (case3ComponentRows_storage_succ x Z k hk)) hadj hent hrn hrk
    let sC := sB.setReg (r_base + 1) (k + 1)
    have hexC : Exec w (.assign (r_base + 1) (.op .add (.reg (r_base + 1)) (.const 1)))
        sB sC 4 := .assign (by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hrkB, hkw, hw, hkpw])
    have harrC : ∀ a, a ≠ a_mat → a ≠ 31 + a_off → a ≠ 32 + a_off →
        sC.arrs a = s.arrs a := by
      intro a hM h31 h32
      exact harrB a hM h31 h32
    have hZC : sC.arrs a_Z = bitSetList Z := by
      rw [harrC a_Z haZM (by omega) (by omega), hZ]
    have hmatC : sC.arrs a_mat =
        (((List.finRange x.n).take (k + 1)).flatMap (case3ComponentRow x Z)) ++
          List.replicate ((x.n - (k + 1)) * x.n) 0 := by
      rw [case3ComponentRows_prefix_succ x Z k hk, List.append_assoc]
      simpa only [sC, State.setReg_arrs, List.append_assoc] using hmatB
    have hadjC : IsAdjList (restrictGraph x.G (Finset.univ \ Z))
        (36 + a_off) (37 + a_off) (38 + a_off) lists sC :=
      hadj.of_arrs_eq (harrC _ (by omega) (by omega) (by omega))
        (harrC _ (by omega) (by omega) (by omega))
        (harrC _ (by omega) (by omega) (by omega))
    obtain ⟨s', t, hex, ht, hdst, hrn', harr, hreg⟩ := ih (k + 1) (by omega) hZC hmatC hadjC
      (by rw [harrC _ (by omega) (by omega) (by omega)]; exact hent)
      (by simpa only [sC, State.setReg_regs_ne _ _ (show r_base ≠ r_base + 1 by omega)] using hrnB)
      (State.setReg_regs_self ..)
    refine ⟨s', 3 + (tB + 4) + t, .while_true hc (by decide) (.seq hexB hexC) hex,
      ?_, hdst, hrn', ?_, ?_⟩
    · rw [Nat.succ_mul]
      omega
    · intro a hM h31 h32
      exact (harr a hM h31 h32).trans (harrC a hM h31 h32)
    · intro r hr
      rw [hreg r hr]
      change (sB.setReg (r_base + 1) (k + 1)).regs r = s.regs r
      rw [State.setReg_regs_ne _ _ (by romega)]
      exact hregB r hr

/-- All outside-component rows can be computed in quadratic vertex work plus
one adjacency scan per seed. Only the table and the search arrays change. -/
theorem case3ComponentTableProg_exec {w : ℕ} (x : Alg81Input)
    (Z : Finset (Fin x.n)) (lists : Fin x.n → List ℕ)
    (a_Z a_mat a_off r_base : ℕ)
    (haZ : a_Z < a_off) (haM : a_mat < a_off) (haZM : a_Z ≠ a_mat)
    (hw : 1 < 2 ^ w) (hn : x.n + 1 < 2 ^ w) (hsq : x.n * x.n < 2 ^ w)
    {s : State} (hZ : s.arrs a_Z = bitSetList Z)
    (hadj : IsAdjList (restrictGraph x.G (Finset.univ \ Z))
      (36 + a_off) (37 + a_off) (38 + a_off) lists s)
    (hent : (s.arrs (38 + a_off)).length < 2 ^ w)
    (hrn : s.regs r_base = x.n) :
    ∃ s' t, Exec w (case3ComponentTableProg a_Z a_mat a_off r_base) s s' t ∧
      t ≤ x.n * x.n + x.n * (38 * x.n + 26 * totalAdjEntries lists + 47) + 8 ∧
      s'.arrs a_mat = case3ComponentRows x Z ∧ s'.regs r_base = x.n ∧
      (∀ a, a ≠ a_mat → a ≠ 31 + a_off → a ≠ 32 + a_off → s'.arrs a = s.arrs a) ∧
      (∀ r < r_base, s'.regs r = s.regs r) := by
  have hnw : x.n < 2 ^ w := by omega
  have h0 : 0 < 2 ^ w := by omega
  let s₁ := s.setArr a_mat (List.replicate (x.n * x.n) 0)
  let s₂ := s₁.setReg (r_base + 1) 0
  have hex₁ : Exec w (.alloc a_mat (.op .mul (.reg r_base) (.reg r_base)))
      s s₁ (3 + x.n * x.n) := .alloc (by
    simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hrn, hnw, hsq])
  have hex₂ : Exec w (.assign (r_base + 1) (.const 0)) s₁ s₂ 2 :=
    .assign (by simp [Expr.eval, checkWord, h0])
  have harr₂ : ∀ a, a ≠ a_mat → s₂.arrs a = s.arrs a := by
    intro a ha
    exact State.setArr_arrs_ne _ _ ha
  obtain ⟨s', t, hex, ht, hdst, hrn', harr, hreg⟩ :=
    componentTableLoop_exec x Z lists a_Z a_mat a_off r_base haZ haM haZM hw hn hsq
      x.n 0 (by omega) (s := s₂)
      (by rw [harr₂ a_Z haZM]; exact hZ)
      (by simp [s₂, s₁, State.setReg_arrs, State.setArr_arrs_self])
      (hadj.of_arrs_eq (harr₂ _ (by omega)) (harr₂ _ (by omega)) (harr₂ _ (by omega)))
      (by rw [harr₂ _ (by omega)]; exact hent)
      (by simpa only [s₂, s₁, State.setReg_regs_ne _ _ (show r_base ≠ r_base + 1 by omega),
        State.setArr_regs] using hrn)
      (State.setReg_regs_self ..)
  refine ⟨s', 3 + x.n * x.n + (2 + t), .seq hex₁ (.seq hex₂ hex),
    by omega, hdst, hrn', ?_, ?_⟩
  · intro a hM h31 h32
    exact (harr a hM h31 h32).trans (harr₂ a hM)
  · intro r hr
    rw [hreg r hr]
    change (s₁.setReg (r_base + 1) 0).regs r = s.regs r
    rw [State.setReg_regs_ne _ _ (show r ≠ r_base + 1 by omega)]
    rfl

end GraphMinor.Compute
