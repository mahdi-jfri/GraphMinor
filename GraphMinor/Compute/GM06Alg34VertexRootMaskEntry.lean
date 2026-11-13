module

public import GraphMinor.Compute.GM06Alg34VertexRootQuery

/-!
# Writing one canonical component-root flag

Run the root query for a supplied vertex label and write its exact bit
into the root-mask allocation. The query's scratch arrays may change,
but the input, masks, closure table, and CSR graph remain fixed.
-/

@[expose] public section
namespace GraphMinor.Compute

/-- Query source 187 and write its canonical root bit into mask 36. -/
def gm06VertexRootMaskEntryProg : Cmd :=
  .seq gm06VertexRootQueryProg (.write 36 (.reg 187) (.reg 200))

/-- The canonical root bit at one vertex source is written within a
quadratic bound while preserving the source and graph representation. -/
theorem gm06VertexRootMaskEntryProg_exec {w : ℕ} (x : GM06DrawingData) 
    (a : Fin x.n) (hw : 1 < 2 ^ w) (hN : x.n < 2 ^ w)
    (hsquare : x.n * x.n < 2 ^ w) {s : State}
    (hsize : s.regs 4 = x.n) (hsource : s.regs 187 = a.val)
    (hlists : IsAdjList x.vertexGraph 30 31 32 (adjListOf x.vertexGraph) s)
    (hlen : (s.arrs 32).length = x.n * x.n)
    (hcap : (s.arrs 36).length = x.n) :
    ∃ s' t, Exec w gm06VertexRootMaskEntryProg s s' t ∧
      t ≤ 26 * (x.n * x.n) + 46 * x.n + 73 ∧
      s'.arrs 36 = (s.arrs 36).set a.val (if x.isComponentRoot a then 1 else 0) ∧
      (∀ k : ℕ, k ≠ 33 → k ≠ 34 → k ≠ 35 → k ≠ 36 → s'.arrs k = s.arrs k) ∧
      (∀ q : ℕ, q < 190 ∨ 201 ≤ q → s'.regs q = s.regs q) := by
  obtain ⟨s₁, t, hex, ht, hbit, _, harr, hreg⟩ :=
    gm06VertexRootQueryProg_exec x a hw hN hsquare hsize hsource hlists hlen
  have ha₁ : s₁.regs 187 = a.val := (hreg _ (Or.inl (by decide))).trans hsource
  have haeval : (Expr.reg 187).eval w s₁ = some a.val := by
    simp [Expr.eval, checkWord, ha₁, a.isLt.trans hN]
  have hval : (Expr.reg 200).eval w s₁ = some (if x.isComponentRoot a then 1 else 0) := by
    cases hr : x.isComponentRoot a <;>
      simp [Expr.eval, checkWord, hbit, hr, hw, Nat.zero_lt_of_lt hw]
  let s₂ := s₁.writeArr 36 a.val (if x.isComponentRoot a then 1 else 0)
  have hwrite : Exec w (.write 36 (.reg 187) (.reg 200)) s₁ s₂ 3 :=
    .write haeval hval (by rw [harr 36 (by decide) (by decide) (by decide), hcap]; exact a.isLt)
  refine ⟨s₂, t + 3, Exec.seq hex hwrite, by omega, ?_, ?_, hreg⟩
  · simp only [s₂, State.writeArr_arrs_self, harr 36 (by decide) (by decide) (by decide)]
  · intro k hk₁ hk₂ hk₃ hk₄
    exact (State.writeArr_arrs_ne _ _ _ hk₄).trans (harr k hk₁ hk₂ hk₃)

end GraphMinor.Compute
