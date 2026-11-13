module

public import GraphMinor.Compute.GM06Alg34AppendBoundaryList
public import GraphMinor.Compute.GM06Alg34BoundaryWordLabels

/-!
# Writing a new region's vertex boundary field

Set the vertex-cell offset to zero and append the vertex specialization
of the computed boundary list. Its length and labels are exactly the
vertex field of the induced region boundary. The output cursor advances
past that field while the drawing and component tables remain fixed.
-/

@[expose] public section
namespace GraphMinor.Compute

/-- Append the length-prefixed new vertex boundary to payload buffer 10. -/
def gm06AppendBoundaryVertexProg : Cmd :=
  .seq (.assign 208 (.const 0)) (gm06AppendBoundaryListProg 4 5 100)

/-- The new region's complete vertex boundary field is written exactly,
with a quadratic bound in the original cell and vertex counts. -/
theorem gm06AppendBoundaryVertexProg_exec {w cap : ℕ} (x : GM06DrawingData)
    (vs : List (Fin x.n)) (a : Fin x.cellCount) (pfx : List ℕ) (hw : 1 < 2 ^ w)
    (hN : x.cellCount < 2 ^ w) (hsquare : x.cellCount * x.cellCount < 2 ^ w)
    (ha : x.activeCell vs (x.cellNumbering.symm a) = false)
    (hout : pfx.length + 1 + x.n < 2 ^ w) {s : State}
    (hmarks : s.arrs 33 = gm06ComplementReachData x vs a)
    (hmat : s.arrs 12 = gm06ClosureMatrixData x) (hc : s.regs 170 = x.cellCount)
    (hmask : s.arrs 4 = gm06VertexMask vs) (hranks : s.arrs 5 = gm06VertexRanks vs)
    (hcount : s.regs 100 = x.n)
    (hbuf : IsPrefixBuffer 10 pfx (1 + (x.inducedRegionBoundary vs a).vertices.length + cap) s)
    (hcursor : s.regs 143 = pfx.length) :
    ∃ s' t, Exec w gm06AppendBoundaryVertexProg s s' t ∧
      t ≤ (18 * x.cellCount + 72) * x.n + 31 ∧
      IsPrefixBuffer 10 (pfx ++ GM06DrawingData.listWords
        (((x.inducedRegionBoundary vs a).vertices).map Fin.val)) cap s' ∧
      s'.regs 143 = (pfx ++ GM06DrawingData.listWords
        (((x.inducedRegionBoundary vs a).vertices).map Fin.val)).length ∧
      (∀ j : ℕ, j ≠ 9 → j ≠ 10 → j ≠ 11 → s'.arrs j = s.arrs j) ∧
      (∀ q : ℕ, q < 210 → q ≠ 0 → q ≠ 105 → q ≠ 142 → q ≠ 143 → q ≠ 204 → q ≠ 205 → q ≠ 206 →
        q ≠ 207 → q ≠ 208 → q ≠ 209 → s'.regs q = s.regs q) := by
  have hfit : 0 + x.n ≤ x.cellCount := by dsimp only [GM06DrawingData.cellCount]; omega
  have hn : x.n < 2 ^ w := (by omega : x.n ≤ x.cellCount).trans_lt hN
  let s₁ := s.setReg 208 0
  have hex₁ : Exec w (.assign 208 (.const 0)) s s₁ 2 :=
    .assign (by simp [Expr.eval, checkWord, Nat.zero_lt_of_lt hw])
  have hlabel : ∀ v : Fin x.n, decide (v ∈ vs) = true →
      ((gm06VertexMask vs).take v.val).sum < 2 ^ w := by
    intro v _
    exact (((List.take_sublist v.val (gm06VertexMask vs)).sum_le_sum
      (fun _ _ => Nat.zero_le _)).trans (gm06VertexMask_sum_le vs)).trans_lt hn
  have hbuf₁ := hbuf.of_arr_eq (s' := s₁) (show s₁.arrs 10 = s.arrs 10 from rfl)
  obtain ⟨s₂, t, hex₂, ht, hbuf₂, hcursor₂, harr, hreg⟩ :=
    gm06AppendBoundaryListProg_exec x vs a 4 5 100 (fun v => decide (v ∈ vs))
      (fun v => ((gm06VertexMask vs).take v.val).sum) pfx (by decide) (by decide)
      hw hN hsquare hfit hlabel ha hout (s := s₁) hmarks hmat (by simpa [s₁] using hc)
      (by simpa only [gm06VertexMask, decide_eq_true_eq, s₁, State.setReg] using hmask) hranks
      (by simpa [s₁] using hcount) (by simp [s₁])
      (by simpa only [gm06BoundaryVertexWords_eq, List.length_map] using hbuf₁)
      (by simpa [s₁] using hcursor)
  refine ⟨s₂, 2 + t, Exec.seq hex₁ hex₂, by omega, ?_, ?_, harr, ?_⟩
  · simpa only [gm06BoundaryVertexWords_eq] using hbuf₂
  · simpa only [gm06BoundaryVertexWords_eq] using hcursor₂
  · intro q hq hq₁ hq₂ hq₃ hq₄ hq₅ hq₆ hq₇ hq₈ hq₉ hq₁₀
    exact (hreg q hq hq₁ hq₂ hq₃ hq₄ hq₅ hq₆ hq₇ hq₈ hq₁₀).trans (by simp [s₁, hq₉])

end GraphMinor.Compute
