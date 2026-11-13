module

public import GraphMinor.Compute.GM06Alg34Regions

/-!
# Reading the disc input header

The RAM reads the vertex, edge, and region counts from the input itself.
It then skips the two endpoint words per edge. The resulting stream begins
at the region boundaries. The program initializes its cursor and makes no
assumption about the initial scratch registers.
-/

@[expose] public section
namespace GraphMinor.Compute

/-- Read counts into registers 100–102 and advance cursor 103 past the
endpoint section of input array 0. -/
def gm06ReadHeaderProg : Cmd :=
  .seq (.assign 103 (.const 0))
    (.seq (readStreamWordProg 0 103 100)
      (.seq (readStreamWordProg 0 103 101)
        (.seq (readStreamWordProg 0 103 102)
          (.assign 103 (.op .add (.reg 103) (.op .mul (.const 2) (.reg 101)))))))

/-- The header program reads the three supplied counts and locates the
region section in at most 32 RAM steps. Only registers 100–103 change. -/
theorem gm06ReadHeaderProg_exec {w n m r : ℕ} (ends tail : List ℕ)
    (hlen : ends.length = 2 * m) (hw : 3 < 2 ^ w)
    (hn : n < 2 ^ w) (hm : m < 2 ^ w) (hr : r < 2 ^ w)
    (hend : 3 + ends.length < 2 ^ w) {s : State}
    (harr : s.arrs 0 = [n, m, r] ++ ends ++ tail) :
    ∃ s' t, Exec w gm06ReadHeaderProg s s' t ∧ t ≤ 32 ∧
      s'.regs 100 = n ∧ s'.regs 101 = m ∧ s'.regs 102 = r ∧
      s'.regs 103 = 3 + 2 * m ∧ AtStream 0 (3 + 2 * m) tail s' ∧
      (∀ a, s'.arrs a = s.arrs a) ∧
      (∀ q : ℕ, q ≠ 100 → q ≠ 101 → q ≠ 102 → q ≠ 103 → s'.regs q = s.regs q) := by
  have h0 : 0 < 2 ^ w := by omega
  have h1 : 1 < 2 ^ w := by omega
  have h2 : 2 < 2 ^ w := by omega
  let s₀ := s.setReg 103 0
  have hex₀ : Exec w (.assign 103 (.const 0)) s s₀ 2 :=
    .assign (by simp [Expr.eval, checkWord, h0])
  have hstream₀ : AtStream 0 0 (n :: m :: r :: (ends ++ tail)) s₀ := ⟨[], rfl, harr⟩
  obtain ⟨s₁, t₁, hex₁, ht₁, hn₁, hpos₁, hstream₁, harr₁, hreg₁⟩ :=
    readStreamWordProg_exec 103 100 (by decide) h1 (by omega) hn hstream₀
      (State.setReg_regs_self _ _ _)
  obtain ⟨s₂, t₂, hex₂, ht₂, hm₂, hpos₂, hstream₂, harr₂, hreg₂⟩ :=
    readStreamWordProg_exec 103 101 (by decide) h1 (by omega) hm hstream₁ hpos₁
  obtain ⟨s₃, t₃, hex₃, ht₃, hr₃, hpos₃, hstream₃, harr₃, hreg₃⟩ :=
    readStreamWordProg_exec 103 102 (by decide) h1 (by omega) hr hstream₂ hpos₂
  have hn₃ : s₃.regs 100 = n := by
    rw [hreg₃ 100 (by decide) (by decide), hreg₂ 100 (by decide) (by decide), hn₁]
  have hm₃ : s₃.regs 101 = m := by
    rw [hreg₃ 101 (by decide) (by decide), hm₂]
  have hout : 3 + 2 * m < 2 ^ w := by omega
  have hmul : 2 * m < 2 ^ w := by omega
  have heval : (Expr.op .add (.reg 103) (.op .mul (.const 2) (.reg 101))).eval w s₃ =
      some (3 + 2 * m) := by
    simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hpos₃, hm₃, hm, h2, hw, hmul, hout]
  let s₄ := s₃.setReg 103 (3 + 2 * m)
  have hex₄ : Exec w (.assign 103 (.op .add (.reg 103)
      (.op .mul (.const 2) (.reg 101)))) s₃ s₄ 6 := .assign heval
  have hstream₄ : AtStream 0 (3 + 2 * m) tail s₄ := by
    have hs := hstream₃.append_advance (mid := ends)
    rw [hlen] at hs
    exact hs.of_arr_eq rfl
  refine ⟨s₄, 2 + (t₁ + (t₂ + (t₃ + 6))),
    .seq hex₀ (.seq hex₁ (.seq hex₂ (.seq hex₃ hex₄))), by omega,
    ?_, ?_, ?_, by simp [s₄], hstream₄, ?_, ?_⟩
  · simpa only [s₄, State.setReg_regs_ne _ _ (by decide : 100 ≠ 103)] using hn₃
  · simpa only [s₄, State.setReg_regs_ne _ _ (by decide : 101 ≠ 103)] using hm₃
  · simpa only [s₄, State.setReg_regs_ne _ _ (by decide : 102 ≠ 103)] using hr₃
  · intro a
    exact (harr₃ a).trans ((harr₂ a).trans (harr₁ a))
  · intro q hq100 hq101 hq102 hq103
    change (s₃.setReg 103 (3 + 2 * m)).regs q = s.regs q
    rw [State.setReg_regs_ne _ _ hq103, hreg₃ q hq103 hq102,
      hreg₂ q hq103 hq101, hreg₁ q hq103 hq100]
    exact State.setReg_regs_ne _ _ hq103

end GraphMinor.Compute
