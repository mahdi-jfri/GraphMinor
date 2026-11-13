module

public import GraphMinor.Compute.CrossingOpsBfsRoot

/-!
# Choosing roots from the active vertices

Subtracting the discovered mark from the active mark tests whether a vertex needs a
new component search. Inactive vertices and previously discovered vertices are skipped.
-/

@[expose] public section

namespace GraphMinor.Compute.Crossing

open GraphMinor.Crossing

/-- Start a component exactly when the vertex in `R` is active and unmarked. -/
def bfsChooseRoot (A R : ℕ) : Cmd :=
  .ite (.op .sub (.read (A + 6) (.reg R)) (.read (A + 3) (.reg R)))
    (bfsRootRun A R) .skip

/-- Testing a possible root preserves the completed history and discovers that vertex
when it belongs to the active set. The cost is paid by nineteen steps and new scans. -/
theorem bfsChooseRoot_exec {w N : ℕ} (A R : ℕ) {G : SimpleGraph (Fin N)}
    (S : Finset (Fin N)) (nbrs : Fin N → List (Fin N)) (hG : HP25.IsSupportedOn G (↑S))
    (hnd : ∀ v, (nbrs v).Nodup) (hn : ∀ u v, v ∈ nbrs u ↔ G.Adj u v)
    (hN : N < 2 ^ w) (hw : 1 < 2 ^ w)
    {items : List (Fin N)} {edges : List (Fin N × Fin N)} {s : State}
    (v : Fin N) (htrace : BfsScanTrace G (↑S) items items.length edges)
    (hl : ∀ u, ∃ st en, IsListAt A (A + 1) (A + 2) u.val st en ((nbrs u).map Fin.val) s ∧ en < 2 ^ w)
    (hq : IsQueueHistory (A + 5) (R + 2) (R + 3) N (items.map Fin.val) items.length s)
    (hvis : s.arrs (A + 3) = bfsMarks items) (hpar : IsBfsParentsAt (A + 4) edges s)
    (hactive : s.arrs (A + 6) = List.ofFn (fun u : Fin N => if u ∈ S then 1 else 0))
    (hr : s.regs R = v.val) :
    ∃ s' t items' edges', Exec w (bfsChooseRoot A R) s s' t ∧
      t + bfsScannedWork nbrs items items.length ≤ 19 + bfsScannedWork nbrs items' items'.length ∧
      BfsScanTrace G (↑S) items' items'.length edges' ∧ items <+: items' ∧
      (v ∈ S → v ∈ items') ∧
      IsQueueHistory (A + 5) (R + 2) (R + 3) N (items'.map Fin.val) items'.length s' ∧
      s'.arrs (A + 3) = bfsMarks items' ∧ IsBfsParentsAt (A + 4) edges' s' ∧
      (∀ a, a ≠ A + 3 → a ≠ A + 4 → a ≠ A + 5 → s'.arrs a = s.arrs a) ∧
      (∀ r, r ≠ R + 2 → r ≠ R + 3 → r ≠ R + 4 → r ≠ R + 5 → r ≠ R + 6 →
        r ≠ R + 7 → r ≠ R + 8 → s'.regs r = s.regs r) := by
  classical
  have hc : (Expr.op .sub (.read (A + 6) (.reg R)) (.read (A + 3) (.reg R))).eval w s =
      some ((if v ∈ S then 1 else 0) - (if v ∈ items then 1 else 0)) := by
    have hvw := v.isLt.trans hN
    by_cases hs : v ∈ S <;> by_cases hi : v ∈ items <;>
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr, hvw, hactive, hvis, bfsMarks,
        v.isLt, hs, hi, hw, show 0 < 2 ^ w by omega]
  by_cases hroot : v ∈ S ∧ v ∉ items
  · have hc1 : (Expr.op .sub (.read (A + 6) (.reg R)) (.read (A + 3) (.reg R))).eval w s = some 1 := by
      simpa only [hroot.1, hroot.2, ite_true, ite_false, Nat.sub_zero] using hc
    obtain ⟨s', t, items', edges', he, ht, htr, hpre, hq', hv', hp', ha, hr'⟩ :=
      bfsRootRun_exec A R nbrs hG hnd hn hN hw v htrace hroot.1 hroot.2 hl hq hvis hpar hr
    refine ⟨s', 5 + t, items', edges', .ite_true hc1 (by decide) he, by omega, htr,
      (items.prefix_append [v]).trans hpre, ?_, hq', hv', hp', ha, hr'⟩
    intro _
    exact hpre.sublist.subset (by simp)
  · have hzero : (if v ∈ S then 1 else 0) - (if v ∈ items then 1 else 0) = 0 := by
      by_cases hs : v ∈ S <;> by_cases hi : v ∈ items <;> simp_all
    have hc0 : (Expr.op .sub (.read (A + 6) (.reg R)) (.read (A + 3) (.reg R))).eval w s = some 0 := by
      simpa only [hzero] using hc
    refine ⟨s, 6, items, edges, .ite_false hc0 (.skip s), by omega, htrace,
      ⟨[], by simp⟩, ?_, hq, hvis, hpar, fun _ _ _ _ => rfl, fun _ _ _ _ _ _ _ _ => rfl⟩
    intro hs
    by_contra hi
    exact hroot ⟨hs, hi⟩

end GraphMinor.Compute.Crossing
