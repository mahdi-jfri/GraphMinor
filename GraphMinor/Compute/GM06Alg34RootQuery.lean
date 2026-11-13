module

public import GraphMinor.Compute.GM06Alg34RootTestExpr

/-!
# A complete RAM test for one canonical region root

Search the complement graph from the source, compute prefix counts of
the component marks, and read the source's active flag. The final
expression tests inactivity and zero smaller-label count. The BFS
marks remain available for computing that region's boundary.
-/

@[expose] public section
namespace GraphMinor.Compute

/-- Test source register 187 for being a region root, returning its bit
in register 200 while keeping its component marks in array 33. -/
def gm06RootQueryProg : Cmd :=
  .seq gm06ComplementBfsProg
    (.seq gm06ReachRanksProg
      (.seq (gm06ActiveCellReadProg 187 199) (.assign 200 gm06RootTestExpr)))

/-- The root query computes the exact canonical root bit and component
marks in quadratic time, preserving the input, masks, and CSR lists. -/
theorem gm06RootQueryProg_exec {w : ℕ} (x : GM06DrawingData) (vs : List (Fin x.n))
    (a : Fin x.cellCount) (hw : 1 < 2 ^ w) (hN : x.cellCount < 2 ^ w)
    (hsquare : x.cellCount * x.cellCount < 2 ^ w) {s : State}
    (hsize : s.regs 4 = x.cellCount) (hsource : s.regs 187 = a.val)
    (hn : s.regs 100 = x.n) (hm : s.regs 101 = x.ends.length)
    (hv : s.arrs 4 = gm06VertexMask vs) (he : s.arrs 6 = gm06EdgeMask x vs)
    (hlists : IsAdjList (x.complementGraph vs) 30 31 32 (adjListOf (x.complementGraph vs)) s)
    (hlen : (s.arrs 32).length = x.cellCount * x.cellCount) :
    ∃ s' t, Exec w gm06RootQueryProg s s' t ∧
      t ≤ 26 * (x.cellCount * x.cellCount) + 46 * x.cellCount + 70 ∧
      s'.regs 200 = (if x.isRegionRoot vs a then 1 else 0) ∧
      s'.arrs 33 = gm06ComplementReachData x vs a ∧
      (∀ k : ℕ, k ≠ 33 → k ≠ 34 → k ≠ 35 → s'.arrs k = s.arrs k) ∧
      (∀ q : ℕ, q < 190 ∨ 201 ≤ q → s'.regs q = s.regs q) := by
  obtain ⟨s₁, t₁, hex₁, ht₁, hmarks, harr₁, hreg₁⟩ :=
    gm06ComplementBfsProg_exec x vs a hw hN hsquare hsize hsource hlists hlen
  obtain ⟨s₂, t₂, hex₂, ht₂, hranks, harr₂, hreg₂⟩ :=
    gm06ReachRanksProg_exec x vs a hw hN hmarks
  have hsource₂ : s₂.regs 187 = a.val :=
    (hreg₂ _ (by decide) (by decide)).trans ((hreg₁ _ (Or.inl (by decide))).trans hsource)
  have hn₂ : s₂.regs 100 = x.n :=
    (hreg₂ _ (by decide) (by decide)).trans ((hreg₁ _ (Or.inl (by decide))).trans hn)
  have hm₂ : s₂.regs 101 = x.ends.length :=
    (hreg₂ _ (by decide) (by decide)).trans ((hreg₁ _ (Or.inl (by decide))).trans hm)
  have hv₂ : s₂.arrs 4 = gm06VertexMask vs :=
    (harr₂ _ (by decide)).trans ((harr₁ _ (by decide) (by decide)).trans hv)
  have he₂ : s₂.arrs 6 = gm06EdgeMask x vs :=
    (harr₂ _ (by decide)).trans ((harr₁ _ (by decide) (by decide)).trans he)
  let active : ℕ := if x.activeCell vs (x.cellNumbering.symm a) then 1 else 0
  let s₃ := s₂.setReg 199 active
  obtain ⟨t₃, hex₃, ht₃⟩ := gm06ActiveCellReadProg_exec x vs (x.cellNumbering.symm a)
    187 199 hw hN hn₂ hm₂ (by simpa only [Equiv.apply_symm_apply] using hsource₂) hv₂ he₂
  have hex₃' : Exec w (gm06ActiveCellReadProg 187 199) s₂ s₃ t₃ := hex₃
  have htest : gm06RootTestExpr.eval w s₃ = some (if x.isRegionRoot vs a then 1 else 0) :=
    gm06RootTestExpr_eval x vs a hw hN (by simpa [s₃] using hsource₂)
      (by simp [s₃, active]) hranks
  let s₄ := s₃.setReg 200 (if x.isRegionRoot vs a then 1 else 0)
  have hex₄ : Exec w (.assign 200 gm06RootTestExpr) s₃ s₄ 9 := .assign htest
  refine ⟨s₄, t₁ + (t₂ + (t₃ + 9)),
    Exec.seq hex₁ (Exec.seq hex₂ (Exec.seq hex₃' hex₄)), by omega, ?_, ?_, ?_, ?_⟩
  · simp [s₄]
  · exact (harr₂ 33 (by decide)).trans hmarks
  · intro k hk₁ hk₂ hk₃
    exact (harr₂ k hk₃).trans (harr₁ k hk₁ hk₂)
  · intro q hq
    have hq₁ : q ≠ 197 := by omega
    have hq₂ : q ≠ 198 := by omega
    have hq₃ : q ≠ 199 := by omega
    have hq₄ : q ≠ 200 := by omega
    simp only [s₄, s₃, State.setReg, Function.update_of_ne hq₃, Function.update_of_ne hq₄]
    exact (hreg₂ q hq₁ hq₂).trans (hreg₁ q (by omega))

end GraphMinor.Compute
