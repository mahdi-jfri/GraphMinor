module

public import GraphMinor.Compute.GM06Alg34BoundaryListProg
public import GraphMinor.Compute.GM06Alg34BoundaryWordLabels

/-!
# Computing the vertex boundary list of a new region

Use offset zero, the vertex survival mask, and the vertex rank table
in the common boundary-list program. The resulting exact word array
is the vertex list of the induced region boundary, in its specified
finite order. Only the boundary scratch arrays and registers change.
-/

@[expose] public section
namespace GraphMinor.Compute

/-- Compute the new region's vertex boundary labels in exact array 11. -/
def gm06BoundaryVertexListProg : Cmd :=
  .seq (.assign 208 (.const 0)) (gm06BoundaryListProg 4 5 100)

/-- The vertex specialization returns precisely the induced boundary's
vertex labels in at most `(18 * N + 55) * oldVertices + 19` steps. -/
theorem gm06BoundaryVertexListProg_exec {w : ℕ} (x : GM06DrawingData)
    (vs : List (Fin x.n)) (a : Fin x.cellCount) (hw : 1 < 2 ^ w)
    (hN : x.cellCount < 2 ^ w) (hsquare : x.cellCount * x.cellCount < 2 ^ w)
    (ha : x.activeCell vs (x.cellNumbering.symm a) = false) {s : State}
    (hmarks : s.arrs 33 = gm06ComplementReachData x vs a)
    (hmat : s.arrs 12 = gm06ClosureMatrixData x) (hc : s.regs 170 = x.cellCount)
    (hmask : s.arrs 4 = gm06VertexMask vs) (hranks : s.arrs 5 = gm06VertexRanks vs)
    (hcount : s.regs 100 = x.n) :
    ∃ s' t, Exec w gm06BoundaryVertexListProg s s' t ∧
      t ≤ (18 * x.cellCount + 55) * x.n + 19 ∧
      s'.arrs 11 = ((x.inducedRegionBoundary vs a).vertices).map Fin.val ∧
      s'.regs 142 = (x.inducedRegionBoundary vs a).vertices.length ∧
      (∀ j : ℕ, j ≠ 9 → j ≠ 11 → s'.arrs j = s.arrs j) ∧
      (∀ q : ℕ, q < 210 → q ≠ 0 → q ≠ 105 → q ≠ 142 → q ≠ 204 → q ≠ 205 → q ≠ 206 →
        q ≠ 207 → q ≠ 208 → q ≠ 209 → s'.regs q = s.regs q) := by
  have hfit : 0 + x.n ≤ x.cellCount := by
    dsimp only [GM06DrawingData.cellCount]; omega
  have hn : x.n < 2 ^ w := (by omega : x.n ≤ x.cellCount).trans_lt hN
  let s₁ := s.setReg 208 0
  have hex₁ : Exec w (.assign 208 (.const 0)) s s₁ 2 :=
    .assign (by simp [Expr.eval, checkWord, Nat.zero_lt_of_lt hw])
  have hlabel : ∀ v : Fin x.n, decide (v ∈ vs) = true →
      ((gm06VertexMask vs).take v.val).sum < 2 ^ w := by
    intro v _
    exact (((List.take_sublist v.val (gm06VertexMask vs)).sum_le_sum
      (fun _ _ => Nat.zero_le _)).trans (gm06VertexMask_sum_le vs)).trans_lt hn
  obtain ⟨s₂, t, hex₂, ht, hout, htotal, harr, hreg⟩ :=
    gm06BoundaryListProg_exec x vs a 4 5 100 (fun v => decide (v ∈ vs))
      (fun v => ((gm06VertexMask vs).take v.val).sum) (by decide) (by decide)
      hw hN hsquare hfit hlabel ha (s := s₁) hmarks hmat (by simpa [s₁] using hc)
      (by simpa only [gm06VertexMask, decide_eq_true_eq, s₁, State.setReg] using hmask) hranks
      (by simpa [s₁] using hcount) (by simp [s₁])
  refine ⟨s₂, 2 + t, Exec.seq hex₁ hex₂, by omega,
    hout.trans (gm06BoundaryVertexWords_eq x vs a hfit), ?_, harr, ?_⟩
  · simpa only [gm06BoundaryVertexWords_eq, List.length_map] using htotal
  · intro q hq hq₁ hq₂ hq₃ hq₄ hq₅ hq₆ hq₇ hq₈ hq₉
    exact (hreg q hq hq₁ hq₂ hq₃ hq₄ hq₅ hq₆ hq₇ hq₉).trans (by simp [s₁, hq₈])

end GraphMinor.Compute
