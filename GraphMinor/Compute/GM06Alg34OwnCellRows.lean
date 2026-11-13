module

public import GraphMinor.Compute.GM06Alg34StartClosureRow

/-!
# The closure rows of supplied vertices

A vertex cell's closure contains only itself. Mark consecutive diagonal
entries using the verified row starter. The counted loop also provides
an exact finite update for a range of such rows and preserves all input
arrays except the closure matrix.
-/

@[expose] public section
namespace GraphMinor.Compute

/-- Exact diagonal updates for a consecutive range of own-cell closure rows. -/
def gm06OwnCellRows (N : ℕ) : ℕ → ℕ → List ℕ → List ℕ
  | _, 0, dst => dst
  | i, k + 1, dst => gm06OwnCellRows N (i + 1) k (dst.set (N * i + i) 1)

/-- The diagonal-row update preserves the matrix allocation. -/
theorem gm06OwnCellRows_length (N i k : ℕ) (dst : List ℕ) :
    (gm06OwnCellRows N i k dst).length = dst.length := by
  induction k generalizing i dst with
  | zero => rfl
  | succ k ih => rw [gm06OwnCellRows, ih, List.length_set]

/-- Mark consecutive own-cell rows counted in register 175, starting at register 171. -/
def gm06OwnCellRowsLoopProg : Cmd :=
  .while (.reg 175) (.seq gm06StartClosureRowProg
    (.seq (.assign 171 (.op .add (.reg 171) (.const 1)))
      (.assign 175 (.op .sub (.reg 175) (.const 1)))))

/-- The counted own-cell row scan makes exactly its diagonal updates
in at most twenty-four steps per vertex plus the final test. -/
theorem gm06OwnCellRowsLoopProg_exec {w N i k : ℕ}
    (hw : 1 < 2 ^ w) (hN : N < 2 ^ w) (hsquare : N * N < 2 ^ w)
    (hfit : i + k ≤ N) {s : State} (hNr : s.regs 170 = N)
    (hir : s.regs 171 = i) (hc : s.regs 175 = k) (hcap : (s.arrs 12).length = N * N) :
    ∃ s' t, Exec w gm06OwnCellRowsLoopProg s s' t ∧ t ≤ 24 * k + 1 ∧
      s'.arrs 12 = gm06OwnCellRows N i k (s.arrs 12) ∧
      s'.regs 171 = i + k ∧ s'.regs 175 = 0 ∧
      (∀ a : ℕ, a ≠ 12 → s'.arrs a = s.arrs a) ∧
      (∀ q : ℕ, q ≠ 109 → q ≠ 171 → q ≠ 173 → q ≠ 174 → q ≠ 175 →
        s'.regs q = s.regs q) := by
  induction k generalizing i s with
  | zero =>
    have he : (Expr.reg 175).eval w s = some 0 := by
      simp [Expr.eval, checkWord, hc, Nat.zero_lt_of_lt hw]
    exact ⟨s, 1, .while_false he, by omega, rfl, by simpa using hir, hc,
      fun _ _ => rfl, fun _ _ _ _ _ _ => rfl⟩
  | succ k ih =>
    have hi : i < N := by omega
    have hiw := hi.trans hN
    have hi1w : i + 1 < 2 ^ w := by omega
    have hkw : k < 2 ^ w := by omega
    have hk1w : k + 1 < 2 ^ w := by omega
    obtain ⟨s₁, he₁, hbuf₁, _, _, _, ha₁, hr₁⟩ :=
      gm06StartClosureRowProg_exec hw hN hi hsquare hNr hir hcap
    have hi₁ : s₁.regs 171 = i :=
      (hr₁ 171 (by decide) (by decide) (by decide)).trans hir
    have hc₁ : s₁.regs 175 = k + 1 :=
      (hr₁ 175 (by decide) (by decide) (by decide)).trans hc
    have hN₁ : s₁.regs 170 = N :=
      (hr₁ 170 (by decide) (by decide) (by decide)).trans hNr
    let s₂ := s₁.setReg 171 (i + 1)
    have he₂ : Exec w (.assign 171 (.op .add (.reg 171) (.const 1))) s₁ s₂ 4 :=
      .assign (by simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hi₁, hiw, hi1w, hw])
    let s₃ := s₂.setReg 175 k
    have he₃ : Exec w (.assign 175 (.op .sub (.reg 175) (.const 1))) s₂ s₃ 4 :=
      .assign (by simp [s₂, Expr.eval, BinOp.eval, BinOp.raw, checkWord, hc₁, hkw, hk1w, hw])
    have hcap₃ : (s₃.arrs 12).length = N * N := by
      change (s₁.arrs 12).length = _
      rw [hbuf₁, List.length_set, hcap]
    obtain ⟨s₄, t₄, he₄, ht₄, hbuf₄, hi₄, hc₄, ha₄, hr₄⟩ :=
      ih (i := i + 1) (s := s₃) (by omega) (by simp [s₃, s₂, hN₁])
        (by simp [s₃, s₂]) (by simp [s₃]) hcap₃
    have hecond : (Expr.reg 175).eval w s = some (k + 1) := by
      simp [Expr.eval, checkWord, hc, hk1w]
    have hex : Exec w gm06OwnCellRowsLoopProg s s₄ (1 + (15 + (4 + 4)) + t₄) :=
      .while_true hecond (by omega) (.seq he₁ (.seq he₂ he₃)) he₄
    refine ⟨s₄, _, hex, by omega, ?_, by omega, hc₄, ?_, ?_⟩
    · rw [hbuf₄]
      change gm06OwnCellRows N (i + 1) k (s₁.arrs 12) = _
      rw [hbuf₁]
      rfl
    · intro a ha
      exact (ha₄ a ha).trans (ha₁ a ha)
    · intro q hqv hqi hqr hqs hqn
      rw [hr₄ q hqv hqi hqr hqs hqn]
      change (s₂.setReg 175 k).regs q = _
      rw [State.setReg_regs_ne _ _ hqn, State.setReg_regs_ne _ _ hqi]
      exact hr₁ q hqv hqr hqs

/-- Initialize the vertex closure-row scan from the supplied vertex count. -/
def gm06VertexRowsProg : Cmd :=
  .seq (.assign 171 (.const 0)) (.seq (.assign 175 (.reg 100)) gm06OwnCellRowsLoopProg)

/-- The header-driven vertex pass marks exactly the supplied vertices’
own-cell closure rows, with linear work and preserved input arrays. -/
theorem gm06VertexRowsProg_exec {w N n : ℕ}
    (hw : 1 < 2 ^ w) (hN : N < 2 ^ w) (hsquare : N * N < 2 ^ w) (hfit : n ≤ N)
    {s : State} (hNr : s.regs 170 = N) (hnr : s.regs 100 = n)
    (hcap : (s.arrs 12).length = N * N) :
    ∃ s' t, Exec w gm06VertexRowsProg s s' t ∧ t ≤ 24 * n + 5 ∧
      s'.arrs 12 = gm06OwnCellRows N 0 n (s.arrs 12) ∧ s'.regs 171 = n ∧
      (∀ a : ℕ, a ≠ 12 → s'.arrs a = s.arrs a) ∧
      (∀ q : ℕ, q ≠ 109 → q ≠ 171 → q ≠ 173 → q ≠ 174 → q ≠ 175 →
        s'.regs q = s.regs q) := by
  have hn : n < 2 ^ w := hfit.trans_lt hN
  let s₁ := s.setReg 171 0
  have he₁ : Exec w (.assign 171 (.const 0)) s s₁ 2 :=
    .assign (by simp [Expr.eval, checkWord, Nat.zero_lt_of_lt hw])
  let s₂ := s₁.setReg 175 n
  have he₂ : Exec w (.assign 175 (.reg 100)) s₁ s₂ 2 :=
    .assign (by simp [s₁, Expr.eval, checkWord, hnr, hn])
  obtain ⟨s₃, t₃, he₃, ht₃, hbuf₃, hi₃, _, ha₃, hr₃⟩ :=
    gm06OwnCellRowsLoopProg_exec (s := s₂) (i := 0) (k := n) hw hN hsquare
      (by simpa using hfit) (by simp [s₂, s₁, hNr]) (by simp [s₂, s₁])
      (by simp [s₂]) hcap
  have hex : Exec w gm06VertexRowsProg s s₃ (2 + (2 + t₃)) := .seq he₁ (.seq he₂ he₃)
  refine ⟨s₃, _, hex, by omega, hbuf₃, by simpa using hi₃, ha₃, ?_⟩
  intro q hqv hqi hqr hqs hqn
  rw [hr₃ q hqv hqi hqr hqs hqn]
  change (s₁.setReg 175 n).regs q = _
  rw [State.setReg_regs_ne _ _ hqn, State.setReg_regs_ne _ _ hqi]

end GraphMinor.Compute
