module

public import GraphMinor.Compute.GM06Alg34RegionOutputLoop
import GraphMinor.Compute.GM06Alg34RowEnumeration

/-!
# Writing the complete induced region section

Start the source label at zero, read the supplied cell count into the
remaining-label counter, and emit root-selected records in increasing
order. The output is exactly the induced drawing's region section.
All source arrays and the computed new region count remain available.
-/

@[expose] public section
namespace GraphMinor.Compute

/-- Append the complete recomputed region section to payload buffer 10. -/
def gm06RegionOutputProg : Cmd :=
  .seq (.assign 187 (.const 0)) (.seq (.assign 188 (.reg 4)) gm06RegionOutputLoopProg)

/-- The full region-output program appends exactly the induced payload's
region section in polynomial time, including an empty cell range. -/
theorem gm06RegionOutputProg_exec {w cap : ℕ} (x : GM06DrawingData)
    (vs : List (Fin x.n)) (pfx : List ℕ) (hw : 1 < 2 ^ w)
    (hN : x.cellCount < 2 ^ w) (hsquare : x.cellCount * x.cellCount < 2 ^ w)
    (hout : pfx.length + (x.cellCount + 1) * (2 + x.n + x.ends.length) < 2 ^ w) {s : State}
    (hrootMask : s.arrs 36 = gm06RootMask x vs)
    (hmat : s.arrs 12 = gm06ClosureMatrixData x) (hc : s.regs 170 = x.cellCount)
    (hvertexMask : s.arrs 4 = gm06VertexMask vs) (hvertexRanks : s.arrs 5 = gm06VertexRanks vs)
    (hedgeMask : s.arrs 6 = gm06EdgeMask x vs) (hedgeRanks : s.arrs 7 = gm06EdgeRanks x vs)
    (hsize : s.regs 4 = x.cellCount) (hn : s.regs 100 = x.n) (hm : s.regs 101 = x.ends.length)
    (hlists : IsAdjList (x.complementGraph vs) 30 31 32 (adjListOf (x.complementGraph vs)) s)
    (hlen : (s.arrs 32).length = x.cellCount * x.cellCount)
    (hbuf : IsPrefixBuffer 10 pfx ((x.inducedData vs).regionWords.length + cap) s)
    (hcursor : s.regs 143 = pfx.length) :
    ∃ s' t, Exec w gm06RegionOutputProg s s' t ∧
      t ≤ (26 * (x.cellCount * x.cellCount) + 23 * x.cellCount +
        (18 * x.cellCount + 72) * (x.n + x.ends.length) + 99) * x.cellCount + 5 ∧
      IsPrefixBuffer 10 (pfx ++ (x.inducedData vs).regionWords) cap s' ∧
      s'.regs 143 = (pfx ++ (x.inducedData vs).regionWords).length ∧
      (∀ j : ℕ, j ≠ 9 → j ≠ 10 → j ≠ 11 → j ≠ 33 → j ≠ 34 → s'.arrs j = s.arrs j) ∧
      (∀ q : ℕ, (q < 190 ∨ q = 203) → q ≠ 0 → q ≠ 105 → q ≠ 142 → q ≠ 143 →
        q ≠ 187 → q ≠ 188 → s'.regs q = s.regs q) := by
  let s₁ := s.setReg 187 0
  let s₂ := s₁.setReg 188 x.cellCount
  have hex₁ : Exec w (.assign 187 (.const 0)) s s₁ 2 :=
    .assign (by simp [Expr.eval, checkWord, Nat.zero_lt_of_lt hw])
  have hex₂ : Exec w (.assign 188 (.reg 4)) s₁ s₂ 2 :=
    .assign (by simp [s₁, Expr.eval, checkWord, hsize, hN])
  have hlists₂ : IsAdjList (x.complementGraph vs) 30 31 32 (adjListOf (x.complementGraph vs)) s₂ :=
    hlists.of_arrs_eq rfl rfl rfl
  have hbuf₂ := hbuf.of_arr_eq (s' := s₂) (show s₂.arrs 10 = s.arrs 10 from rfl)
  obtain ⟨s₃, t, hex₃, ht, hbuf₃, hcursor₃, _, _, harr, hreg⟩ :=
    gm06RegionOutputLoopProg_exec x vs (List.finRange x.cellCount) pfx hw hN hsquare
      (i := 0) (by simp)
      (by simpa only [List.length_finRange] using (gm06Range_eq_finRange x.cellCount).symm)
      (by simpa only [List.length_finRange] using hout) (s := s₂) hrootMask hmat
      (by simpa [s₂, s₁] using hc) hvertexMask hvertexRanks hedgeMask hedgeRanks
      (by simpa [s₂, s₁] using hsize) (by simp [s₂, s₁]) (by simp [s₂])
      (by simpa [s₂, s₁] using hn) (by simpa [s₂, s₁] using hm) hlists₂ hlen
      (by simpa only [gm06Induced_regionWords_eq_root_scan] using hbuf₂)
      (by simpa [s₂, s₁] using hcursor)
  refine ⟨s₃, 2 + (2 + t), Exec.seq hex₁ (Exec.seq hex₂ hex₃), ?_, ?_, ?_, harr, ?_⟩
  · simp only [List.length_finRange] at ht
    omega
  · simpa only [← gm06Induced_regionWords_eq_root_scan] using hbuf₃
  · simpa only [← gm06Induced_regionWords_eq_root_scan] using hcursor₃
  · intro q hq hq₁ hq₂ hq₃ hq₄ hq₅ hq₆
    exact (hreg q hq hq₁ hq₂ hq₃ hq₄ hq₅ hq₆).trans (by simp [s₂, s₁, hq₅, hq₆])

end GraphMinor.Compute
