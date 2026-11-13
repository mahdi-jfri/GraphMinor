module

public import GraphMinor.Compute.CrossingOpsBfsLoop

/-!
# Starting a new BFS component

When the queue is empty, an unmarked vertex can start the next component. The program
marks and queues this root without assigning a parent, then drains its component queue.
-/

@[expose] public section

namespace GraphMinor.Compute.Crossing

open GraphMinor.Crossing

/-- Add the root in `R` to the discovery queue without adding a parent edge. -/
def bfsRootPush (A R : ℕ) : Cmd :=
  .seq (.write (A + 3) (.reg R) (.const 1)) (queuePush (A + 5) (R + 3) (.reg R))

/-- Starting a component implements a root transition of the discovery history. -/
theorem bfsRootPush_exec {w N : ℕ} (A R : ℕ) {G : SimpleGraph (Fin N)} {T : Set (Fin N)}
    {items : List (Fin N)} {edges : List (Fin N × Fin N)} {s : State}
    (v : Fin N) (htrace : BfsScanTrace G T items items.length edges)
    (hmem : v ∈ T) (hfresh : v ∉ items)
    (hq : IsQueueHistory (A + 5) (R + 2) (R + 3) N (items.map Fin.val) items.length s)
    (hvis : s.arrs (A + 3) = bfsMarks items) (hpar : IsBfsParentsAt (A + 4) edges s)
    (hr : s.regs R = v.val) (hN : N < 2 ^ w) (hw : 1 < 2 ^ w) :
    ∃ s' t, Exec w (bfsRootPush A R) s s' t ∧ t ≤ 10 ∧
      BfsScanTrace G T (items ++ [v]) items.length edges ∧
      IsQueueHistory (A + 5) (R + 2) (R + 3) N ((items ++ [v]).map Fin.val) items.length s' ∧
      s'.arrs (A + 3) = bfsMarks (items ++ [v]) ∧ IsBfsParentsAt (A + 4) edges s' ∧
      (∀ a, a ≠ A + 3 → a ≠ A + 5 → s'.arrs a = s.arrs a) ∧
      (∀ r, r ≠ R + 3 → s'.regs r = s.regs r) := by
  let s1 := s.writeArr (A + 3) v.val 1
  have he1 : Exec w (.write (A + 3) (.reg R) (.const 1)) s s1 3 :=
    .write (eval_reg hr (v.isLt.trans hN)) (eval_const hw) (by simp [hvis, bfsMarks])
  have hq1 := hq.of_eq (s' := s1) (by simp [s1, State.writeArr_arrs_ne]) rfl rfl
  have hlen : (items.map Fin.val).length < N := by
    have hc := (List.nodup_cons.mpr ⟨hfresh, htrace.nodup⟩).length_le_card
    simp only [List.length_cons, Fintype.card_fin] at hc
    simpa only [List.length_map] using (show items.length < N by omega)
  obtain ⟨s2, t2, he2, ht2, hq2⟩ := Triple.queuePush_spec (w := w)
    (A + 5) (R + 2) (R + 3) (.reg R) N (items.map Fin.val) items.length v.val
    (by omega) hw hN hlen s1 ⟨hq1, eval_reg (by simpa [s1] using hr) (v.isLt.trans hN)⟩
  have ha2 : ∀ a, a ≠ A + 5 → s2.arrs a = s1.arrs a := fun a h5 =>
    he2.arrs_eq_of_not_mem_writtenArrs (by simp [queuePush, Cmd.writtenArrs, h5])
  refine ⟨s2, 3 + t2, .seq he1 he2, by simp only [Expr.cost] at ht2; omega,
    htrace.root rfl v hmem hfresh, by simpa only [List.map_append, List.map_singleton] using hq2,
    ?_, hpar.of_arrs_eq ?_, ?_, ?_⟩
  · rw [ha2 _ (by omega)]
    simpa only [s1, State.writeArr_arrs_self, hvis] using bfsMarks_set items v
  · rw [ha2 _ (by omega)]; simp [s1, State.writeArr_arrs_ne]
  · intro a h3 h5
    rw [ha2 a h5]; simp [s1, State.writeArr_arrs_ne, h3]
  · intro r h3
    exact (he2.regs_eq_of_not_mem_writtenRegs (by simp [queuePush, Cmd.writtenRegs, h3])).trans rfl

/-- Mark and queue the root, then scan its entire component. -/
def bfsRootRun (A R : ℕ) : Cmd := .seq (bfsRootPush A R) (bfsForestLoop A R)

/-- Running an unmarked root returns an empty queue and a history containing the root.
Its cost is at most thirteen plus the increase in scanned work. -/
theorem bfsRootRun_exec {w N : ℕ} (A R : ℕ) {G : SimpleGraph (Fin N)} {T : Set (Fin N)}
    (nbrs : Fin N → List (Fin N)) (hG : HP25.IsSupportedOn G T)
    (hnd : ∀ v, (nbrs v).Nodup) (hn : ∀ u v, v ∈ nbrs u ↔ G.Adj u v)
    (hN : N < 2 ^ w) (hw : 1 < 2 ^ w)
    {items : List (Fin N)} {edges : List (Fin N × Fin N)} {s : State}
    (v : Fin N) (htrace : BfsScanTrace G T items items.length edges)
    (hmem : v ∈ T) (hfresh : v ∉ items)
    (hl : ∀ u, ∃ st en, IsListAt A (A + 1) (A + 2) u.val st en ((nbrs u).map Fin.val) s ∧ en < 2 ^ w)
    (hq : IsQueueHistory (A + 5) (R + 2) (R + 3) N (items.map Fin.val) items.length s)
    (hvis : s.arrs (A + 3) = bfsMarks items) (hpar : IsBfsParentsAt (A + 4) edges s)
    (hr : s.regs R = v.val) :
    ∃ s' t items' edges', Exec w (bfsRootRun A R) s s' t ∧
      t + bfsScannedWork nbrs items items.length ≤ 13 + bfsScannedWork nbrs items' items'.length ∧
      BfsScanTrace G T items' items'.length edges' ∧ (items ++ [v]) <+: items' ∧
      IsQueueHistory (A + 5) (R + 2) (R + 3) N (items'.map Fin.val) items'.length s' ∧
      s'.arrs (A + 3) = bfsMarks items' ∧ IsBfsParentsAt (A + 4) edges' s' ∧
      (∀ a, a ≠ A + 3 → a ≠ A + 4 → a ≠ A + 5 → s'.arrs a = s.arrs a) ∧
      (∀ r, r ≠ R + 2 → r ≠ R + 3 → r ≠ R + 4 → r ≠ R + 5 → r ≠ R + 6 →
        r ≠ R + 7 → r ≠ R + 8 → s'.regs r = s.regs r) := by
  obtain ⟨s1, t1, he1, ht1, htr1, hq1, hv1, hp1, ha1, hr1⟩ :=
    bfsRootPush_exec A R v htrace hmem hfresh hq hvis hpar hr hN hw
  have hl1 : ∀ u, ∃ st en, IsListAt A (A + 1) (A + 2) u.val st en
      ((nbrs u).map Fin.val) s1 ∧ en < 2 ^ w := by
    intro u
    obtain ⟨st, en, hh, hw'⟩ := hl u
    exact ⟨st, en, hh.of_arrs_eq (ha1 _ (by omega) (by omega))
      (ha1 _ (by omega) (by omega)) (ha1 _ (by omega) (by omega)), hw'⟩
  obtain ⟨s2, t2, items2, edges2, he2, ht2, htr2, hpre2, hq2, hv2, hp2, ha2, hr2⟩ :=
    bfsForestLoop_exec A R nbrs hG hnd hn hN hw htr1 hl1 hq1 hv1 hp1
  have hwork : bfsScannedWork nbrs (items ++ [v]) items.length =
      bfsScannedWork nbrs items items.length := by
    simp only [bfsScannedWork, List.take_append_of_le_length (Nat.le_refl _)]
  refine ⟨s2, t1 + t2, items2, edges2, .seq he1 he2, by omega, htr2, hpre2,
    hq2, hv2, hp2, ?_, ?_⟩
  · intro a h3 h4 h5
    exact (ha2 a h3 h4 h5).trans (ha1 a h3 h5)
  · intro r h2 h3 h4 h5 h6 h7 h8
    exact (hr2 r h2 h3 h4 h5 h6 h7 h8).trans (hr1 r h3)

end GraphMinor.Compute.Crossing
