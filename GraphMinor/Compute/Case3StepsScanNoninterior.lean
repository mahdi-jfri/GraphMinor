module

public import GraphMinor.Compute.Case3StepsMemberScanBody

/-!
# Skipping noninterior selected members

Construct the selected member and test it against the entire perimeter.
A member that meets the perimeter is not passed to (7.2). Its iteration
preserves the record buffer, all three persistent counters, and the routing
tables, then advances the numeric candidate index.
-/

public section

namespace GraphMinor.Compute

/-- A selected noninterior member is skipped after the full perimeter test. -/
theorem case3MemberScanBody_noninterior_exec {w h : ℕ} (P72 : Cmd) (x : Alg81Input) (D : MultiDigraph x.n)
    (d : Alg86DivisionOutput x) (hd : IsValidAlg86DivisionOutput x d)
    (i : Case3SelectedGroup x d.core.Z)
    (hw : 4 < 2 ^ w) (hn : x.n + 1 < 2 ^ w) (hkeys : x.n * 4 < 2 ^ w)
    (hm : 2 + 2 * (case3InputEdges x).length < 2 ^ w)
    (hsize : x.n + (case3InputEdges x).length < 2 ^ w)
    (he : D.numEdges < 2 ^ w) (hA : 2 + 3 * D.numActivePairs < 2 ^ w) {s : State}
    (hD : s.arrs 3 = D.enc) (hin : s.arrs 16 = encGraph x.G) (hZ : IsBitSet d.core.Z 10 s)
    (htab : s.arrs 26 = case3AttachmentKeys x d.core.Z)
    (hreps : s.arrs 27 = case3ComponentRepList x d.core.Z)
    (hheads : s.arrs 35 = case3BucketHeads (case3ActivePairOwner x D d.core.Z)
      (x.n + (case3InputEdges x).length) 0)
    (hnext : s.arrs 36 = case3BucketNext (case3ActivePairOwner x D d.core.Z) 0)
    (hcounts : s.arrs 37 = case3BucketCounts (case3ActivePairOwner x D d.core.Z)
      (x.n + (case3InputEdges x).length) 0)
    (hrn : s.regs 14 = x.n) (hrg : s.regs 54 = case3RawIndexLabel x i.1)
    (P : Finset (Fin x.n)) (hP : IsBitSet P 20 s)
    (hnon : ¬ Disjoint (case3SelectedMember x d.core.Z i).verts P)
    (hmask : s.arrs 29 = bitSetList (case3GroupLabelSet x d.core.Z)) :
    ∃ s' t, Exec w (case3MemberScanBody h P72) s s' t ∧
      t ≤ 97 * x.n + 83 * (case3RoutedMember x D d.core.Z (case3RawIndexLabel x i.1)).numActivePairs + 146 ∧
      s'.regs 54 = case3RawIndexLabel x i.1 + 1 ∧
      (∀ a, a ≠ 25 → a ≠ 30 → a ≠ 31 → a ≠ 39 → s'.arrs a = s.arrs a) ∧
      (∀ r < 13, s'.regs r = s.regs r) ∧ s'.regs 52 = s.regs 52 ∧ s'.regs 14 = s.regs 14 := by
  obtain ⟨s₁, t₁, hex₁, ht₁, _, hverts, _, _, _, harr₁, hreg₁⟩ :=
    case3MemberEncodingProg_exec x D d hd i hw hn hkeys hm hsize he hA
      hD hin hZ htab hreps hheads hnext hcounts hrn hrg
  obtain ⟨s₂, t₂, hex₂, ht₂, htest, harr₂, hreg₂⟩ :=
    case3InteriorProg_exec (w := w) (s := s₁) (case3SelectedMember x d.core.Z i).verts P (by omega) (by omega)
      (IsBitSet.of_bitSetList _ _ _ hverts)
      (hP.of_arr_eq (harr₁ 20 (by decide) (by decide) (by decide) (by decide)))
      ((hreg₁ 14 (by decide)).trans hrn)
  have hzero : s₂.regs 100 = 0 := by simpa only [hnon, ↓reduceIte] using htest
  have h0 := Nat.two_pow_pos w
  have hcond : (Expr.reg 100).eval w s₂ = some 0 := by
    simp only [Expr.eval, checkWord, hzero, h0, ↓reduceIte]
  have hmasktest := case3MemberMask_eval (w := w) (s := s) (case3GroupLabelSet x d.core.Z)
    (case3GroupLabelEquiv x i.1) (by omega) hsize hmask
    (by rw [case3GroupLabelEquiv_val]; exact hrg)
  rw [ite_eq_left ((mem_case3GroupLabelSet x d.core.Z i.1).mpr i.2)] at hmasktest
  have h54 : s₂.regs 54 = case3RawIndexLabel x i.1 :=
    (hreg₂ 54 (by decide)).trans ((hreg₁ 54 (by decide)).trans hrg)
  have hiw : case3RawIndexLabel x i.1 < 2 ^ w := (case3RawIndexLabel_lt x i.1).trans hsize
  have hi1 : case3RawIndexLabel x i.1 + 1 < 2 ^ w :=
    lt_of_le_of_lt (case3RawIndexLabel_lt x i.1) hsize
  let s₃ := s₂.setReg 54 (case3RawIndexLabel x i.1 + 1)
  have hex₃ : Exec w (.assign 54 (.op .add (.reg 54) (.const 1))) s₂ s₃ 4 :=
    .assign (by simp only [Expr.eval, checkWord, h54, hiw, show 1 < 2 ^ w by omega,
      BinOp.eval, BinOp.raw, hi1, ↓reduceIte])
  refine ⟨s₃, (2 + (t₁ + (t₂ + (1 + 1)))) + 4,
    .seq (.ite_true hmasktest (by decide) (.seq hex₁ (.seq hex₂ (.ite_false hcond (.skip s₂)))))
      hex₃, by omega, State.setReg_regs_self .., ?_, ?_, ?_, ?_⟩
  · intro a h25 h30 h31 h39
    exact (harr₂ a).trans (harr₁ a h25 h30 h31 h39)
  · intro r hr
    dsimp only [Reg] at hr
    rw [State.setReg_regs_ne _ _ (by dsimp only [Reg]; omega),
      hreg₂ r (by dsimp only [Reg]; omega)]
    exact hreg₁ r (Or.inl hr)
  · rw [State.setReg_regs_ne _ _ (show (52 : Reg) ≠ 54 by decide), hreg₂ 52 (by decide)]
    exact hreg₁ 52 (by decide)

  · rw [State.setReg_regs_ne _ _ (show (14 : Reg) ≠ 54 by decide), hreg₂ 14 (by decide)]
    exact hreg₁ 14 (by decide)

end GraphMinor.Compute
