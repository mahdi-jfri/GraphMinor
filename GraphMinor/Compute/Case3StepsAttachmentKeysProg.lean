module

public import GraphMinor.Compute.Case3StepsStoreAttachmentKey

/-!
# Computing every attachment key

The program visits seeds in vertex order. Each iteration computes its
attachment set and stores the four-word boundary key. The loop keeps the
component table, core bitset, and graph adjacency lists for later seeds.
-/

@[expose] public section

namespace GraphMinor.Compute

local macro "romega" : tactic => `(tactic| ((try dsimp only [Reg, Arr] at *); omega))

/-- Store the attachment key of every seed in array 26. -/
def case3AttachmentKeysProg : Cmd :=
  .seq (.alloc 26 (.op .mul (.reg 14) (.const 4)))
    (.seq (.assign 13 (.const 4))
      (.seq (.assign 15 (.const 0)) (forUp 15 (.reg 14) case3StoreAttachmentKeyProg)))

private theorem attachmentKeysLoop_exec {w : ℕ} (x : Alg81Input)
    (d : Alg86DivisionOutput x) (hd : IsValidAlg86DivisionOutput x d)
    (lists : Fin x.n → List ℕ)
    (hw : 4 < 2 ^ w) (hn : x.n + 1 < 2 ^ w) (hsq : x.n * x.n < 2 ^ w)
    (hkeys : x.n * 4 < 2 ^ w) (rem k : ℕ) (hrem : k + rem = x.n)
    {s : State} (hmat : s.arrs 12 = case3ComponentRows x d.core.Z)
    (hZ : IsBitSet d.core.Z 10 s)
    (hadj : IsAdjList x.G 19 20 21 lists s) (hent : (s.arrs 21).length < 2 ^ w)
    (htab : s.arrs 26 = (((List.finRange x.n).take k).flatMap
      (fun u => case3BoundaryKey (case3AttachmentRowSet x d.core.Z u))) ++
        List.replicate ((x.n - k) * 4) 0)
    (hrn : s.regs 14 = x.n) (hrk : s.regs 15 = k) (hr4 : s.regs 13 = 4) :
    ∃ s' t, Exec w (forUp 15 (.reg 14) case3StoreAttachmentKeyProg) s s' t ∧
      t ≤ 3 + rem * (76 * x.n + 19 * totalAdjEntries lists + 125) ∧
      s'.arrs 26 = case3AttachmentKeys x d.core.Z ∧
      (∀ a, a ≠ 22 → a ≠ 23 → a ≠ 24 → a ≠ 25 → a ≠ 26 → s'.arrs a = s.arrs a) ∧
      (∀ r < 13, s'.regs r = s.regs r) := by
  have h0 : 0 < 2 ^ w := by omega
  have h1 : 1 < 2 ^ w := by omega
  have hnw : x.n < 2 ^ w := by omega
  induction rem generalizing k s with
  | zero =>
    have hk : k = x.n := by omega
    have hc : (Expr.op .lt (.reg 15) (.reg 14)).eval w s = some 0 := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hrk, hrn, hk, hnw, h0]
    refine ⟨s, 3, .while_false hc, by simp, ?_, fun _ _ _ _ _ _ => rfl, fun _ _ => rfl⟩
    simpa only [hk, case3AttachmentKeys_storage_done] using htab
  | succ rem ih =>
    have hk : k < x.n := by omega
    have hkw : k < 2 ^ w := by omega
    have hkpw : k + 1 < 2 ^ w := by omega
    have hc : (Expr.op .lt (.reg 15) (.reg 14)).eval w s = some 1 := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hrk, hrn, hk, hkw, hnw, h1]
    obtain ⟨sB, tB, hexB, htB, htabB, harrB, hregB⟩ :=
      case3StoreAttachmentKeyProg_exec x d hd ⟨k, hk⟩ lists hw hn hsq hkeys _ _
        (case3AttachmentKeys_prefix_length x d hd k hk.le) hmat hZ hadj hent
        (htab.trans (case3AttachmentKeys_storage_succ x d.core.Z k hk)) hrn hrk hr4
    let sC := sB.setReg 15 (k + 1)
    have hexC : Exec w (.assign 15 (.op .add (.reg 15) (.const 1))) sB sC 4 :=
      .assign (by simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord,
        hregB 15 (by decide), hrk, hkw, h1, hkpw])
    have harrC : ∀ a, a ≠ 22 → a ≠ 23 → a ≠ 24 → a ≠ 25 → a ≠ 26 →
        sC.arrs a = s.arrs a := harrB
    have hmatC : sC.arrs 12 = case3ComponentRows x d.core.Z := by
      rw [harrC 12 (by decide) (by decide) (by decide) (by decide) (by decide), hmat]
    have htabC : sC.arrs 26 = (((List.finRange x.n).take (k + 1)).flatMap
        (fun u => case3BoundaryKey (case3AttachmentRowSet x d.core.Z u))) ++
          List.replicate ((x.n - (k + 1)) * 4) 0 := by
      rw [case3AttachmentKeys_prefix_succ x d.core.Z k hk, List.append_assoc]
      simpa only [sC, State.setReg_arrs, List.append_assoc] using htabB
    obtain ⟨s', t, hex, ht, hdst, harr, hreg⟩ := ih (k + 1) (by omega) (s := sC) hmatC
      (hZ.of_arr_eq (harrC _ (by decide) (by decide) (by decide) (by decide) (by decide)))
      (hadj.of_arrs_eq
        (harrC _ (by decide) (by decide) (by decide) (by decide) (by decide))
        (harrC _ (by decide) (by decide) (by decide) (by decide) (by decide))
        (harrC _ (by decide) (by decide) (by decide) (by decide) (by decide)))
      (by rw [harrC _ (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hent)
      htabC
      (by rw [State.setReg_regs_ne _ _ (show (14 : ℕ) ≠ 15 by decide), hregB 14 (by decide), hrn])
      (State.setReg_regs_self ..)
      (by rw [State.setReg_regs_ne _ _ (show (13 : ℕ) ≠ 15 by decide), hregB 13 (by decide), hr4])
    refine ⟨s', 3 + (tB + 4) + t, .while_true hc (by decide) (.seq hexB hexC) hex, ?_, hdst, ?_, ?_⟩
    · rw [Nat.succ_mul]
      omega
    · intro a h22 h23 h24 h25 h26
      exact (harr a h22 h23 h24 h25 h26).trans (harrC a h22 h23 h24 h25 h26)
    · intro r hr
      rw [hreg r hr]
      change (sB.setReg 15 (k + 1)).regs r = s.regs r
      rw [State.setReg_regs_ne _ _ (show r ≠ 15 by romega)]
      exact hregB r (by romega)

/-- The whole key table costs vertex count times linear vertex and adjacency
work. Arrays outside 22 through 26 and registers below 13 are preserved. -/
theorem case3AttachmentKeysProg_exec {w : ℕ} (x : Alg81Input)
    (d : Alg86DivisionOutput x) (hd : IsValidAlg86DivisionOutput x d)
    (lists : Fin x.n → List ℕ)
    (hw : 4 < 2 ^ w) (hn : x.n + 1 < 2 ^ w) (hsq : x.n * x.n < 2 ^ w)
    (hkeys : x.n * 4 < 2 ^ w) {s : State}
    (hmat : s.arrs 12 = case3ComponentRows x d.core.Z) (hZ : IsBitSet d.core.Z 10 s)
    (hadj : IsAdjList x.G 19 20 21 lists s) (hent : (s.arrs 21).length < 2 ^ w)
    (hrn : s.regs 14 = x.n) :
    ∃ s' t, Exec w case3AttachmentKeysProg s s' t ∧
      t ≤ x.n * 4 + x.n * (76 * x.n + 19 * totalAdjEntries lists + 125) + 10 ∧
      s'.arrs 26 = case3AttachmentKeys x d.core.Z ∧
      (∀ a, a ≠ 22 → a ≠ 23 → a ≠ 24 → a ≠ 25 → a ≠ 26 → s'.arrs a = s.arrs a) ∧
      (∀ r < 13, s'.regs r = s.regs r) := by
  have hnw : x.n < 2 ^ w := by omega
  have h0 : 0 < 2 ^ w := by omega
  let s₁ := s.setArr 26 (List.replicate (x.n * 4) 0)
  let s₂ := s₁.setReg 13 4
  let s₃ := s₂.setReg 15 0
  have hex₁ : Exec w (.alloc 26 (.op .mul (.reg 14) (.const 4))) s s₁ (3 + x.n * 4) :=
    .alloc (by simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hrn, hnw, hw, hkeys])
  have hex₂ : Exec w (.assign 13 (.const 4)) s₁ s₂ 2 :=
    .assign (by simp only [Expr.eval, checkWord, hw, ↓reduceIte])
  have hex₃ : Exec w (.assign 15 (.const 0)) s₂ s₃ 2 :=
    .assign (by simp only [Expr.eval, checkWord, h0, ↓reduceIte])
  have harr₃ : ∀ a, a ≠ 26 → s₃.arrs a = s.arrs a := fun _ ha => State.setArr_arrs_ne _ _ ha
  obtain ⟨s₄, t₄, hex₄, ht₄, hdst₄, harr₄, hreg₄⟩ :=
    attachmentKeysLoop_exec x d hd lists hw hn hsq hkeys x.n 0 (by omega) (s := s₃)
      (by rw [harr₃ _ (by decide)]; exact hmat)
      (hZ.of_arr_eq (harr₃ _ (by decide)))
      (hadj.of_arrs_eq (harr₃ _ (by decide)) (harr₃ _ (by decide)) (harr₃ _ (by decide)))
      (by rw [harr₃ _ (by decide)]; exact hent)
      (by simp [s₃, s₂, s₁, State.setReg_arrs, State.setArr_arrs_self])
      (by simp [s₃, s₂, s₁, State.setReg, State.setArr_regs, hrn])
      (State.setReg_regs_self ..)
      (by simp [s₃, s₂, State.setReg])
  refine ⟨s₄, 3 + x.n * 4 + (2 + (2 + t₄)), .seq hex₁ (.seq hex₂ (.seq hex₃ hex₄)),
    by omega, hdst₄, ?_, ?_⟩
  · intro a h22 h23 h24 h25 h26
    exact (harr₄ a h22 h23 h24 h25 h26).trans (harr₃ a h26)
  · intro r hr
    rw [hreg₄ r hr]
    simp only [s₃, s₂, s₁, State.setReg_regs_ne _ _ (show r ≠ 15 by romega),
      State.setReg_regs_ne _ _ (show r ≠ 13 by romega), State.setArr_regs]

/-- The key-table program can follow the shifted core computation directly.
All arrays below offset 22, including the retained graph and core, survive. -/
theorem case3AttachmentKeysProg_shift_exec {w : ℕ} (x : Alg81Input)
    (d : Alg86DivisionOutput x) (hd : IsValidAlg86DivisionOutput x d)
    (lists : Fin x.n → List ℕ) (a_base r_base : ℕ)
    (hw : 4 < 2 ^ w) (hn : x.n + 1 < 2 ^ w) (hsq : x.n * x.n < 2 ^ w)
    (hkeys : x.n * 4 < 2 ^ w) {s : State}
    (hmat : s.arrs (12 + a_base) = case3ComponentRows x d.core.Z)
    (hZ : s.arrs (10 + a_base) = bitSetList d.core.Z)
    (hadj : IsAdjList x.G (19 + a_base) (20 + a_base) (21 + a_base) lists s)
    (hent : (s.arrs (21 + a_base)).length < 2 ^ w)
    (hrn : s.regs (14 + r_base) = x.n) :
    ∃ s' t, Exec w (case3AttachmentKeysProg.shift a_base r_base) s s' t ∧
      t ≤ x.n * 4 + x.n * (76 * x.n + 19 * totalAdjEntries lists + 125) + 10 ∧
      s'.arrs (26 + a_base) = case3AttachmentKeys x d.core.Z ∧
      (∀ a < a_base + 22, s'.arrs a = s.arrs a) ∧
      (∀ r < r_base, s'.regs r = s.regs r) := by
  have hadjSub : IsAdjList x.G 19 20 21 lists (s.unshift a_base r_base) := by
    simpa only [IsAdjList, IsListFamily, IsListAt, State.unshift_arrs] using hadj
  obtain ⟨s_sub, t, hex, ht, hdst, harr, _⟩ :=
    case3AttachmentKeysProg_exec x d hd lists hw hn hsq hkeys (s := s.unshift a_base r_base)
      hmat (IsBitSet.of_bitSetList _ _ _ hZ) hadjSub hent hrn
  refine ⟨s.applyShifted a_base r_base s_sub, t, Exec.shift_from a_base r_base hex,
    ht, ?_, ?_, ?_⟩
  · rw [State.applyShifted_arrs_add, hdst]
  · intro a ha
    by_cases hab : a_base ≤ a
    · change (if a_base ≤ a then s_sub.arrs (a - a_base) else s.arrs a) = _
      simp only [hab, ↓reduceIte]
      rw [harr (a - a_base) (by romega) (by romega) (by romega) (by romega) (by romega),
        State.unshift_arrs, Nat.sub_add_cancel hab]
    · exact State.applyShifted_arrs_lt a_base r_base s s_sub (by omega)
  · intro r hr
    exact State.applyShifted_regs_lt a_base r_base s s_sub hr

end GraphMinor.Compute
