module

public import GraphMinor.Compute.GM06Alg34BoundaryListProg
public import GraphMinor.Compute.GM06Alg34BoundaryWordLabels

/-!
# Computing the edge boundary list of a new region

Use the old vertex count as offset, the edge survival mask, and the edge rank table
in the common boundary-list program. The resulting exact word array
is the edge list of the induced region boundary, in its specified
finite order. Only the boundary scratch arrays and registers change.
-/

@[expose] public section
namespace GraphMinor.Compute

/-- Compute the new region's vertex boundary labels in exact array 11. -/
def gm06BoundaryEdgeListProg : Cmd :=
  .seq (.assign 208 (.reg 100)) (gm06BoundaryListProg 6 7 101)

/-- The edge specialization returns precisely the induced boundary's
edge labels in at most `(18 * N + 55) * oldEdges + 19` steps. -/
theorem gm06BoundaryEdgeListProg_exec {w : ℕ} (x : GM06DrawingData)
    (vs : List (Fin x.n)) (a : Fin x.cellCount) (hw : 1 < 2 ^ w)
    (hN : x.cellCount < 2 ^ w) (hsquare : x.cellCount * x.cellCount < 2 ^ w)
    (ha : x.activeCell vs (x.cellNumbering.symm a) = false) {s : State}
    (hmarks : s.arrs 33 = gm06ComplementReachData x vs a)
    (hmat : s.arrs 12 = gm06ClosureMatrixData x) (hc : s.regs 170 = x.cellCount)
    (hmask : s.arrs 6 = gm06EdgeMask x vs) (hranks : s.arrs 7 = gm06EdgeRanks x vs)
    (hvertices : s.regs 100 = x.n) (hcount : s.regs 101 = x.ends.length) :
    ∃ s' t, Exec w gm06BoundaryEdgeListProg s s' t ∧
      t ≤ (18 * x.cellCount + 55) * x.ends.length + 19 ∧
      s'.arrs 11 = ((x.inducedRegionBoundary vs a).edges).map Fin.val ∧
      s'.regs 142 = (x.inducedRegionBoundary vs a).edges.length ∧
      (∀ j : ℕ, j ≠ 9 → j ≠ 11 → s'.arrs j = s.arrs j) ∧
      (∀ q : ℕ, q < 210 → q ≠ 0 → q ≠ 105 → q ≠ 142 → q ≠ 204 → q ≠ 205 → q ≠ 206 →
        q ≠ 207 → q ≠ 208 → q ≠ 209 → s'.regs q = s.regs q) := by
  have hfit : x.n + x.ends.length ≤ x.cellCount := by
    dsimp only [GM06DrawingData.cellCount]; omega
  have hm : x.ends.length < 2 ^ w := (by omega : x.ends.length ≤ x.cellCount).trans_lt hN
  have hn : x.n < 2 ^ w := (by omega : x.n ≤ x.cellCount).trans_lt hN
  let s₁ := s.setReg 208 x.n
  have hex₁ : Exec w (.assign 208 (.reg 100)) s s₁ 2 :=
    .assign (by simp [Expr.eval, checkWord, hvertices, hn])
  have hlabel : ∀ v : Fin x.ends.length, x.activeCell vs (.inr (.inl v)) = true →
      ((gm06EdgeMask x vs).take v.val).sum < 2 ^ w := by
    intro v _
    exact (((List.take_sublist v.val (gm06EdgeMask x vs)).sum_le_sum
      (fun _ _ => Nat.zero_le _)).trans (gm06EdgeMask_sum_le x vs)).trans_lt hm
  obtain ⟨s₂, t, hex₂, ht, hout, htotal, harr, hreg⟩ :=
    gm06BoundaryListProg_exec x vs a 6 7 101 (fun v => x.activeCell vs (.inr (.inl v)))
      (fun v => ((gm06EdgeMask x vs).take v.val).sum) (by decide) (by decide)
      hw hN hsquare hfit hlabel ha (s := s₁) hmarks hmat (by simpa [s₁] using hc)
      (by simpa only [gm06EdgeMask, s₁, State.setReg] using hmask) hranks
      (by simpa [s₁] using hcount) (by simp [s₁])
  refine ⟨s₂, 2 + t, Exec.seq hex₁ hex₂, by omega,
    hout.trans (gm06BoundaryEdgeWords_eq x vs a hfit), ?_, harr, ?_⟩
  · simpa only [gm06BoundaryEdgeWords_eq, List.length_map] using htotal
  · intro q hq hq₁ hq₂ hq₃ hq₄ hq₅ hq₆ hq₇ hq₈ hq₉
    exact (hreg q hq hq₁ hq₂ hq₃ hq₄ hq₅ hq₆ hq₇ hq₉).trans (by simp [s₁, hq₈])

end GraphMinor.Compute
