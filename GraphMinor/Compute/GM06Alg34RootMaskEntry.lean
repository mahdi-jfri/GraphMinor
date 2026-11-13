module

public import GraphMinor.Compute.GM06Alg34RootQuery

/-!
# Writing one canonical region-root flag

Run the root query for a supplied packed label and write its exact bit
into the root-mask allocation. The query's scratch arrays may change,
but the input, masks, closure table, and CSR graph remain fixed.
-/

@[expose] public section
namespace GraphMinor.Compute

/-- Query source 187 and write its canonical root bit into mask 36. -/
def gm06RootMaskEntryProg : Cmd :=
  .seq gm06RootQueryProg (.write 36 (.reg 187) (.reg 200))

/-- The canonical root bit at one packed source is written within a
quadratic bound while preserving the source and graph representation. -/
theorem gm06RootMaskEntryProg_exec {w : ℕ} (x : GM06DrawingData) (vs : List (Fin x.n))
    (a : Fin x.cellCount) (hw : 1 < 2 ^ w) (hN : x.cellCount < 2 ^ w)
    (hsquare : x.cellCount * x.cellCount < 2 ^ w) {s : State}
    (hsize : s.regs 4 = x.cellCount) (hsource : s.regs 187 = a.val)
    (hn : s.regs 100 = x.n) (hm : s.regs 101 = x.ends.length)
    (hv : s.arrs 4 = gm06VertexMask vs) (he : s.arrs 6 = gm06EdgeMask x vs)
    (hlists : IsAdjList (x.complementGraph vs) 30 31 32 (adjListOf (x.complementGraph vs)) s)
    (hlen : (s.arrs 32).length = x.cellCount * x.cellCount)
    (hcap : (s.arrs 36).length = x.cellCount) :
    ∃ s' t, Exec w gm06RootMaskEntryProg s s' t ∧
      t ≤ 26 * (x.cellCount * x.cellCount) + 46 * x.cellCount + 73 ∧
      s'.arrs 36 = (s.arrs 36).set a.val (if x.isRegionRoot vs a then 1 else 0) ∧
      (∀ k : ℕ, k ≠ 33 → k ≠ 34 → k ≠ 35 → k ≠ 36 → s'.arrs k = s.arrs k) ∧
      (∀ q : ℕ, q < 190 ∨ 201 ≤ q → s'.regs q = s.regs q) := by
  obtain ⟨s₁, t, hex, ht, hbit, _, harr, hreg⟩ :=
    gm06RootQueryProg_exec x vs a hw hN hsquare hsize hsource hn hm hv he hlists hlen
  have ha₁ : s₁.regs 187 = a.val := (hreg _ (Or.inl (by decide))).trans hsource
  have haeval : (Expr.reg 187).eval w s₁ = some a.val := by
    simp [Expr.eval, checkWord, ha₁, a.isLt.trans hN]
  have hval : (Expr.reg 200).eval w s₁ = some (if x.isRegionRoot vs a then 1 else 0) := by
    cases hr : x.isRegionRoot vs a <;>
      simp [Expr.eval, checkWord, hbit, hr, hw, Nat.zero_lt_of_lt hw]
  let s₂ := s₁.writeArr 36 a.val (if x.isRegionRoot vs a then 1 else 0)
  have hwrite : Exec w (.write 36 (.reg 187) (.reg 200)) s₁ s₂ 3 :=
    .write haeval hval (by rw [harr 36 (by decide) (by decide) (by decide), hcap]; exact a.isLt)
  refine ⟨s₂, t + 3, Exec.seq hex hwrite, by omega, ?_, ?_, hreg⟩
  · simp only [s₂, State.writeArr_arrs_self, harr 36 (by decide) (by decide) (by decide)]
  · intro k hk₁ hk₂ hk₃ hk₄
    exact (State.writeArr_arrs_ne _ _ _ hk₄).trans (harr k hk₁ hk₂ hk₃)

end GraphMinor.Compute
