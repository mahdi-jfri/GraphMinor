module

public import GraphMinor.Compute.Case3StepsGroups
public import GraphMinor.Compute.Case3StepsExtractKeyProg
public import GraphMinor.Compute.Case3StepsReadCoreEdgeProg
public import GraphMinor.Compute.Case3StepsPairKeyProg

/-!
# Preparing the boundary key of one member candidate

A component candidate reads its stored attachment key. A core-edge candidate
reads its endpoints and writes their pair key. Both paths use constant work
and preserve the outer member index and traversal counts.
-/

@[expose] public section

namespace GraphMinor.Compute

/-- Prepare the boundary key of group register 54 in array 25. -/
def case3GroupKeyProg : Cmd :=
  .seq (.assign 13 (.const 4))
    (.ite (.op .lt (.reg 54) (.reg 14))
      (.seq (.assign 15 (.reg 54)) case3ExtractKeyProg)
      (.seq (.assign 18 (.op .sub (.reg 54) (.reg 14)))
        (.seq case3ReadCoreEdgeProg (case3PairKeyProg 25 42 43))))

private theorem groupKey_preserves (r : ℕ)
    (hr : r < 13 ∨ r = 14 ∨ r = 17 ∨ r = 52 ∨ r = 54 ∨ 60 ≤ r) :
    r ≠ 13 ∧ r ≠ 15 ∧ r ≠ 18 ∧ (r < 36 ∨ 40 ≤ r) ∧ r ≠ 42 ∧ r ≠ 43 ∧ r ≠ 44 := by omega

/-- Every candidate's exact boundary key is prepared in at most 91 steps.
The graph, representative arrays, selected-group mask, counts, and outer
member label survive. -/
theorem case3GroupKeyProg_exec {w : ℕ} (x : Alg81Input)
    (d : Alg86DivisionOutput x) (hd : IsValidAlg86DivisionOutput x d) (i : Case3RawIndex x)
    (hw : 4 < 2 ^ w) (hn : x.n + 1 < 2 ^ w) (hkeys : x.n * 4 < 2 ^ w)
    (hm : 2 + 2 * (case3InputEdges x).length < 2 ^ w)
    (hsize : x.n + (case3InputEdges x).length < 2 ^ w) {s : State}
    (hin : s.arrs 16 = encGraph x.G) (htab : s.arrs 26 = case3AttachmentKeys x d.core.Z)
    (hrn : s.regs 14 = x.n) (hri : s.regs 54 = case3RawIndexLabel x i) :
    ∃ s' t, Exec w case3GroupKeyProg s s' t ∧ t ≤ 91 ∧
      s'.arrs 25 = case3BoundaryKey (case3GroupBoundary x d.core.Z i) ∧
      (∀ a, a ≠ 25 → s'.arrs a = s.arrs a) ∧
      (∀ r, r < 13 ∨ r = 14 ∨ r = 17 ∨ r = 52 ∨ r = 54 ∨ 60 ≤ r → s'.regs r = s.regs r) := by
  have hnw : x.n < 2 ^ w := by omega
  have h0 : 0 < 2 ^ w := by omega
  have h1 : 1 < 2 ^ w := by omega
  have hgw : case3RawIndexLabel x i < 2 ^ w := (case3RawIndexLabel_lt x i).trans hsize
  let s₀ := s.setReg 13 4
  have hex₀ : Exec w (.assign 13 (.const 4)) s s₀ 2 :=
    .assign (by simp only [Expr.eval, checkWord, hw, ↓reduceIte])
  have hrn₀ : s₀.regs 14 = x.n := by
    rw [State.setReg_regs_ne _ _ (show (14 : ℕ) ≠ 13 by decide)]
    exact hrn
  have hri₀ : s₀.regs 54 = case3RawIndexLabel x i := by
    rw [State.setReg_regs_ne _ _ (show (54 : ℕ) ≠ 13 by decide)]
    exact hri
  cases i with
  | inl u =>
    simp only [case3RawIndexLabel] at hri₀ hgw
    have hc : (Expr.op .lt (.reg 54) (.reg 14)).eval w s₀ = some 1 := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hri₀, hrn₀, hgw, hnw, u.2, h1]
    let s₁ := s₀.setReg 15 u.1
    have hex₁ : Exec w (.assign 15 (.reg 54)) s₀ s₁ 2 :=
      .assign (by simp only [Expr.eval, checkWord, hri₀, hgw, ↓reduceIte])
    obtain ⟨s₂, t₂, hex₂, ht₂, hkey₂, harr₂, hreg₂⟩ :=
      case3ExtractKeyProg_exec x d hd u hw hnw hkeys (s := s₁)
        (by simpa only [s₁, s₀, State.setReg_arrs] using htab)
        (State.setReg_regs_self ..)
        (by simp only [s₁, s₀, State.setReg_regs_ne _ _ (show (13 : ℕ) ≠ 15 by decide),
          State.setReg_regs_self])
    refine ⟨s₂, 2 + (3 + (2 + t₂)), .seq hex₀ (.ite_true (t := 2 + t₂) hc (by decide) (.seq hex₁ hex₂)),
      by omega, hkey₂, ?_, ?_⟩
    · intro a ha
      simpa only [s₁, s₀, State.setReg_arrs] using harr₂ a ha
    · intro r hr
      obtain ⟨h13, h15, _, hcopy, _, _, _⟩ := groupKey_preserves r hr
      rw [hreg₂ r hcopy, State.setReg_regs_ne _ _ h15, State.setReg_regs_ne _ _ h13]
  | inr j =>
    simp only [case3RawIndexLabel] at hri₀ hgw
    have hc : (Expr.op .lt (.reg 54) (.reg 14)).eval w s₀ = some 0 := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hri₀, hrn₀, hgw, hnw, h0]
    have hjw : j.1 < 2 ^ w := by have := j.2; omega
    let s₁ := s₀.setReg 18 j.1
    have hex₁ : Exec w (.assign 18 (.op .sub (.reg 54) (.reg 14))) s₀ s₁ 4 :=
      .assign (by simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord,
        hri₀, hrn₀, hgw, hnw, hjw])
    obtain ⟨s₂, t₂, hex₂, ht₂, hru₂, hrv₂, harr₂, hreg₂⟩ :=
      case3ReadCoreEdgeProg_exec x j (by omega) hnw hm (s := s₁)
        (by simpa only [s₁, s₀, State.setReg_arrs] using hin) (State.setReg_regs_self ..)
    obtain ⟨s₃, hex₃, hkey₃, harr₃, hreg₃⟩ :=
      case3PairKeyProg_exec _ _ (case3InputEdges_get_spec x j).1 25 42 43 hw hnw hru₂ hrv₂
    refine ⟨s₃, 2 + (3 + (4 + (t₂ + 14))), .seq hex₀
      (.ite_false (t := 4 + (t₂ + 14)) hc (.seq hex₁ (.seq hex₂ hex₃))),
      by omega, hkey₃, ?_, ?_⟩
    · intro a ha
      simpa only [s₁, s₀, State.setReg_arrs] using (harr₃ a ha).trans (harr₂ a)
    · intro r hr
      obtain ⟨h13, _, h18, _, h42, h43, h44⟩ := groupKey_preserves r hr
      rw [hreg₃ r, hreg₂ r h42 h43 h44,
        State.setReg_regs_ne _ _ h18, State.setReg_regs_ne _ _ h13]

end GraphMinor.Compute
