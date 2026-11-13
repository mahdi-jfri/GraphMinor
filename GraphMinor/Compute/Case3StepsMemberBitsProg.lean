module

public import GraphMinor.Compute.Case3StepsMemberVertexExpr

/-!
# Writing the vertices of one selected member

The program scans all compact vertices and evaluates the boundary-or-component
membership test. A prefix invariant records its normalized indicator bits.
The result is exactly the vertex set of the selected merged member.
-/

@[expose] public section

namespace GraphMinor.Compute

/-- Write the selected member's vertex bitset into array 30. -/
def case3MemberBitsProg : Cmd :=
  .seq (.alloc 30 (.reg 14))
    (.seq (.assign 60 (.const 0))
      (forUp 60 (.reg 14) (.write 30 (.reg 60) (case3MemberVertexExpr 10 25 27 60 54))))

private theorem memberBitsLoop_exec {w : ℕ} (x : Alg81Input) (Z : Finset (Fin x.n))
    (i : Case3SelectedGroup x Z) (hbd : (case3GroupBoundary x Z i.1).card ≤ 3)
    (hw : 4 < 2 ^ w) (hn : x.n + 1 < 2 ^ w)
    (hsize : x.n + (case3InputEdges x).length < 2 ^ w)
    (rem k : ℕ) (hrem : k + rem = x.n) {s : State}
    (hZ : IsBitSet Z 10 s) (hkey : s.arrs 25 = case3BoundaryKey (case3GroupBoundary x Z i.1))
    (hreps : s.arrs 27 = case3ComponentRepList x Z)
    (hrn : s.regs 14 = x.n) (hrg : s.regs 54 = case3RawIndexLabel x i.1)
    (hri : s.regs 60 = k) (hlen : (s.arrs 30).length = x.n)
    (hbits : ∀ j : Fin x.n, (s.arrs 30).getD j.1 0 =
      if j.1 < k then (if j ∈ (case3SelectedMember x Z i).verts then 1 else 0) else 0) :
    ∃ s' t, Exec w (forUp 60 (.reg 14)
        (.write 30 (.reg 60) (case3MemberVertexExpr 10 25 27 60 54))) s s' t ∧
      t ≤ 3 + 57 * rem ∧ s'.arrs 30 = bitSetList (case3SelectedMember x Z i).verts := by
  have h0 : 0 < 2 ^ w := by omega
  have h1 : 1 < 2 ^ w := by omega
  have hnw : x.n < 2 ^ w := by omega
  induction rem generalizing k s with
  | zero =>
    have hk : k = x.n := by omega
    have hc : (Expr.op .lt (.reg 60) (.reg 14)).eval w s = some 0 := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hri, hrn, hk, hnw, h0]
    refine ⟨s, 3, .while_false hc, by omega, ?_⟩
    apply List.ext_getElem (by rw [hlen, length_bitSetList])
    intro j hj hj'
    have hjn : j < x.n := by rw [← hlen]; exact hj
    have hb := hbits ⟨j, hjn⟩
    rw [List.getD_eq_getElem _ 0 hj] at hb
    rw [getElem_bitSetList _ j hjn]
    simpa only [hk, hjn, ↓reduceIte] using hb
  | succ rem ih =>
    have hk : k < x.n := by omega
    have hkw : k < 2 ^ w := by omega
    have hkpw : k + 1 < 2 ^ w := by omega
    have hc : (Expr.op .lt (.reg 60) (.reg 14)).eval w s = some 1 := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hri, hrn, hk, hkw, hnw, h1]
    let sB := s.writeArr 30 k (if (⟨k, hk⟩ : Fin x.n) ∈ (case3SelectedMember x Z i).verts then 1 else 0)
    let sC := sB.setReg 60 (k + 1)
    have hexB : Exec w (.write 30 (.reg 60) (case3MemberVertexExpr 10 25 27 60 54)) s sB 50 :=
      .write (by simp only [Expr.eval, checkWord, hri, hkw, ↓reduceIte])
        (case3MemberVertexExpr_eval x Z i hbd ⟨k, hk⟩ 10 25 27 60 54 hw hnw hsize hZ hkey hreps hri hrg)
        (by rw [hlen]; exact hk)
    have hexC : Exec w (.assign 60 (.op .add (.reg 60) (.const 1))) sB sC 4 :=
      .assign (by simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, sB, hri, hkw, h1, hkpw])
    have harrC : ∀ a, a ≠ 30 → sC.arrs a = s.arrs a := by
      intro a ha
      simp only [sC, sB, State.setReg_arrs, State.writeArr_arrs_ne _ _ _ ha]
    have hlenC : (sC.arrs 30).length = x.n := by
      simp only [sC, sB, State.setReg_arrs, State.writeArr_arrs_self, List.length_set, hlen]
    have hbitsC : ∀ j : Fin x.n, (sC.arrs 30).getD j.1 0 =
        if j.1 < k + 1 then (if j ∈ (case3SelectedMember x Z i).verts then 1 else 0) else 0 := by
      intro j
      have hj : j.1 < (s.arrs 30).length := by rw [hlen]; exact j.2
      simp only [sC, sB, State.setReg_arrs, State.writeArr_arrs_self]
      rw [List.getD_eq_getElem _ 0 (by rw [List.length_set]; exact hj), List.getElem_set]
      by_cases hkj : k = j.1
      · simp only [hkj, ↓reduceIte, Nat.lt_add_one]
      · simp only [hkj, ↓reduceIte]
        have hb := hbits j
        rw [List.getD_eq_getElem _ 0 hj] at hb
        rw [hb]
        have htest : j.1 < k + 1 ↔ j.1 < k := by omega
        simp only [htest]
    obtain ⟨s', t, hex, ht, hdst⟩ := ih (k + 1) (by omega) (s := sC)
      (hZ.of_arr_eq (harrC 10 (by decide))) ((harrC 25 (by decide)).trans hkey)
      ((harrC 27 (by decide)).trans hreps)
      (by simp only [sC, sB, State.setReg_regs_ne _ _ (show (14 : ℕ) ≠ 60 by decide), State.writeArr_regs, hrn])
      (by simp only [sC, sB, State.setReg_regs_ne _ _ (show (54 : ℕ) ≠ 60 by decide), State.writeArr_regs, hrg])
      (State.setReg_regs_self ..) hlenC hbitsC
    exact ⟨s', 3 + (50 + 4) + t, .while_true hc (by decide) (.seq hexB hexC) hex, by omega, hdst⟩

/-- The exact vertex bitset of a selected merged member is computed in at
most `58 n + 6` steps. Only array 30 and register 60 change. -/
theorem case3MemberBitsProg_exec {w : ℕ} (x : Alg81Input)
    (d : Alg86DivisionOutput x) (hd : IsValidAlg86DivisionOutput x d)
    (i : Case3SelectedGroup x d.core.Z) (hw : 4 < 2 ^ w) (hn : x.n + 1 < 2 ^ w)
    (hsize : x.n + (case3InputEdges x).length < 2 ^ w) {s : State}
    (hZ : IsBitSet d.core.Z 10 s)
    (hkey : s.arrs 25 = case3BoundaryKey (case3GroupBoundary x d.core.Z i.1))
    (hreps : s.arrs 27 = case3ComponentRepList x d.core.Z)
    (hrn : s.regs 14 = x.n) (hrg : s.regs 54 = case3RawIndexLabel x i.1) :
    ∃ s' t, Exec w case3MemberBitsProg s s' t ∧ t ≤ 58 * x.n + 6 ∧
      s'.arrs 30 = bitSetList (case3SelectedMember x d.core.Z i).verts ∧
      (∀ a, a ≠ 30 → s'.arrs a = s.arrs a) ∧
      (∀ r, r ≠ 60 → s'.regs r = s.regs r) := by
  have hnw : x.n < 2 ^ w := by omega
  have h0 : 0 < 2 ^ w := by omega
  let s₁ := s.setArr 30 (List.replicate x.n 0)
  let s₂ := s₁.setReg 60 0
  have hex₁ : Exec w (.alloc 30 (.reg 14)) s s₁ (1 + x.n) :=
    .alloc (by simp only [Expr.eval, checkWord, hrn, hnw, ↓reduceIte])
  have hex₂ : Exec w (.assign 60 (.const 0)) s₁ s₂ 2 :=
    .assign (by simp only [Expr.eval, checkWord, h0, ↓reduceIte])
  obtain ⟨s₃, t₃, hex₃, ht₃, hdst₃⟩ := memberBitsLoop_exec x d.core.Z i
    (case3GroupBoundary_card_le_three x d hd i.1) hw hn hsize x.n 0 (by omega) (s := s₂)
    (hZ.of_arr_eq (State.setArr_arrs_ne s (List.replicate x.n 0) (show (10 : ℕ) ≠ 30 by decide)))
    (by simpa only [s₂, s₁, State.setReg_arrs, State.setArr_arrs_ne _ _ (show (25 : ℕ) ≠ 30 by decide)] using hkey)
    (by simpa only [s₂, s₁, State.setReg_arrs, State.setArr_arrs_ne _ _ (show (27 : ℕ) ≠ 30 by decide)] using hreps)
    (by simp only [s₂, s₁, State.setReg_regs_ne _ _ (show (14 : ℕ) ≠ 60 by decide), State.setArr_regs, hrn])
    (by simp only [s₂, s₁, State.setReg_regs_ne _ _ (show (54 : ℕ) ≠ 60 by decide), State.setArr_regs, hrg])
    (State.setReg_regs_self ..)
    (by simp only [s₂, s₁, State.setReg_arrs, State.setArr_arrs_self, List.length_replicate])
    (fun j => by simp only [s₂, s₁, State.setReg_arrs, State.setArr_arrs_self,
      Nat.not_lt_zero, ↓reduceIte, List.getD_replicate 0 j.2])
  have hex : Exec w case3MemberBitsProg s s₃ (1 + x.n + (2 + t₃)) := .seq hex₁ (.seq hex₂ hex₃)
  refine ⟨s₃, 1 + x.n + (2 + t₃), hex, by omega, hdst₃, ?_, ?_⟩
  · intro a ha
    exact hex.arrs_eq_of_not_mem_writtenArrs (by simp [case3MemberBitsProg, forUp, Cmd.writtenArrs, ha])
  · intro r hr
    exact hex.regs_eq_of_not_mem_writtenRegs (by simp [case3MemberBitsProg, forUp, Cmd.writtenRegs, hr])

end GraphMinor.Compute
