module

public import GraphMinor.Compute.CrossingOpsBfsWork

/-!
# Draining the BFS forest queue

Each iteration scans one previously unscanned vertex. The head therefore supplies a
termination measure, and the sum of charges on the scanned prefix pays for all iterations.
-/

@[expose] public section

namespace GraphMinor.Compute.Crossing

open GraphMinor.Crossing

/-- Scan vertices until the discovery queue is empty. -/
def bfsForestLoop (A R : ℕ) : Cmd :=
  .while (.op .lt (.reg (R + 2)) (.reg (R + 3))) (bfsForestStep A R)

/-- Draining the queue extends the history and returns an empty queue. The increase
in scanned work pays for all iterations, with three steps for the final condition test. -/
theorem bfsForestLoop_exec {w N : ℕ} (A R : ℕ) {G : SimpleGraph (Fin N)} {T : Set (Fin N)}
    (nbrs : Fin N → List (Fin N)) (hG : HP25.IsSupportedOn G T)
    (hnd : ∀ v, (nbrs v).Nodup) (hn : ∀ u v, v ∈ nbrs u ↔ G.Adj u v)
    (hN : N < 2 ^ w) (hw : 1 < 2 ^ w)
    {items : List (Fin N)} {head : ℕ} {edges : List (Fin N × Fin N)} {s : State}
    (htrace : BfsScanTrace G T items head edges)
    (hl : ∀ u, ∃ st en, IsListAt A (A + 1) (A + 2) u.val st en ((nbrs u).map Fin.val) s ∧ en < 2 ^ w)
    (hq : IsQueueHistory (A + 5) (R + 2) (R + 3) N (items.map Fin.val) head s)
    (hvis : s.arrs (A + 3) = bfsMarks items) (hpar : IsBfsParentsAt (A + 4) edges s) :
    ∃ s' t items' edges', Exec w (bfsForestLoop A R) s s' t ∧
      t + bfsScannedWork nbrs items head ≤ 3 + bfsScannedWork nbrs items' items'.length ∧
      BfsScanTrace G T items' items'.length edges' ∧ items <+: items' ∧
      IsQueueHistory (A + 5) (R + 2) (R + 3) N (items'.map Fin.val) items'.length s' ∧
      s'.arrs (A + 3) = bfsMarks items' ∧ IsBfsParentsAt (A + 4) edges' s' ∧
      (∀ a, a ≠ A + 3 → a ≠ A + 4 → a ≠ A + 5 → s'.arrs a = s.arrs a) ∧
      (∀ r, r ≠ R + 2 → r ≠ R + 3 → r ≠ R + 4 → r ≠ R + 5 → r ≠ R + 6 →
        r ≠ R + 7 → r ≠ R + 8 → s'.regs r = s.regs r) := by
  classical
  generalize hm : N - head = m
  induction m using Nat.strong_induction_on generalizing items head edges s with
  | _ m ih =>
    have hlen : items.length ≤ N := by simpa only [List.length_map] using hq.2.1
    have hhead := htrace.head_le
    have hrhead := hq.2.2.1
    have hrtail : s.regs (R + 3) = items.length := by simpa only [List.length_map] using hq.2.2.2.1
    have htailword : items.length < 2 ^ w := hlen.trans_lt hN
    have hheadword : head < 2 ^ w := hhead.trans_lt htailword
    by_cases pending : head < items.length
    · have hc : (Expr.op .lt (.reg (R + 2)) (.reg (R + 3))).eval w s = some 1 := by
        simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hrhead, hrtail,
          hheadword, htailword, pending, hw]
      obtain ⟨st, en, hlist, hen⟩ := hl items[head]
      obtain ⟨s1, t1, he1, ht1, htr1, hq1, hv1, hp1, ha1, hr1⟩ :=
        bfsForestStep_exec A R htrace pending hG hlist (hnd _) (hn _) hq hvis hpar hN hen hw
      have hl1 : ∀ u, ∃ st en, IsListAt A (A + 1) (A + 2) u.val st en
          ((nbrs u).map Fin.val) s1 ∧ en < 2 ^ w := by
        intro u
        obtain ⟨st, en, hh, hw'⟩ := hl u
        exact ⟨st, en, hh.of_arrs_eq (ha1 _ (by omega) (by omega) (by omega))
          (ha1 _ (by omega) (by omega) (by omega))
          (ha1 _ (by omega) (by omega) (by omega)), hw'⟩
      have hdec : N - (head + 1) < m := by omega
      obtain ⟨s2, t2, items2, edges2, he2, ht2, htr2, hprefix, hq2, hv2, hp2, ha2, hr2⟩ :=
        ih (N - (head + 1)) hdec htr1 hl1 hq1 hv1 hp1 rfl
      have hwork := bfsScannedWork_scan nbrs items
        ((nbrs items[head]).filter (fun v => v ∉ items)) pending
      refine ⟨s2, 3 + t1 + t2, items2, edges2,
        .while_true hc (by omega) he1 he2, by omega, htr2,
        (items.prefix_append _).trans hprefix, hq2, hv2, hp2, ?_, ?_⟩
      · intro a h3 h4 h5
        exact (ha2 a h3 h4 h5).trans (ha1 a h3 h4 h5)
      · intro r h2 h3 h4 h5 h6 h7 h8
        exact (hr2 r h2 h3 h4 h5 h6 h7 h8).trans (hr1 r h2 h3 h4 h5 h6 h7 h8)
    · have heq : head = items.length := by omega
      have hc : (Expr.op .lt (.reg (R + 2)) (.reg (R + 3))).eval w s = some 0 := by
        simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hrhead, hrtail,
          hheadword, htailword, pending, show 0 < 2 ^ w by omega]
      refine ⟨s, 3, items, edges, .while_false hc, ?_, ?_, ?_, ?_, hvis, hpar,
        fun _ _ _ _ => rfl, fun _ _ _ _ _ _ _ _ => rfl⟩
      · simp only [heq]; omega
      · simpa only [heq] using htrace
      · exact ⟨[], by simp⟩
      · simpa only [heq] using hq

end GraphMinor.Compute.Crossing
