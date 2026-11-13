module

public import GraphMinor.Compute.CrossingOpsBfsScan

/-!
# One queue iteration of the BFS forest program

The program pops a vertex and then scans its adjacency list. The discovery history
advances by one scan, while the queue, marks, and parent words keep their exact meanings.
-/

@[expose] public section

namespace GraphMinor.Compute.Crossing

open GraphMinor.Crossing

/-- Pop one vertex and discover its unmarked neighbours. -/
def bfsForestStep (A R : ℕ) : Cmd :=
  .seq (queuePop (A + 5) (R + 2) (R + 4)) (bfsScanProg A R)

/-- A queue iteration implements one scan transition and takes linear time in the
popped vertex's adjacency-list length. -/
theorem bfsForestStep_exec {w N : ℕ} (A R : ℕ) {G : SimpleGraph (Fin N)} {T : Set (Fin N)}
    {items nbrs : List (Fin N)} {head : ℕ} {edges : List (Fin N × Fin N)} {s : State}
    {st en : ℕ} (htrace : BfsScanTrace G T items head edges) (pending : head < items.length)
    (hG : HP25.IsSupportedOn G T)
    (hl : IsListAt A (A + 1) (A + 2) items[head].val st en (nbrs.map Fin.val) s)
    (hnd : nbrs.Nodup) (hn : ∀ v, v ∈ nbrs ↔ G.Adj items[head] v)
    (hq : IsQueueHistory (A + 5) (R + 2) (R + 3) N (items.map Fin.val) head s)
    (hvis : s.arrs (A + 3) = bfsMarks items) (hpar : IsBfsParentsAt (A + 4) edges s)
    (hN : N < 2 ^ w) (hen : en < 2 ^ w) (hw : 1 < 2 ^ w) :
    let fresh := nbrs.filter (fun v => v ∉ items)
    ∃ s' t, Exec w (bfsForestStep A R) s s' t ∧ t ≤ 16 + 27 * nbrs.length ∧
      BfsScanTrace G T (items ++ fresh) (head + 1)
        (edges ++ fresh.map (fun v => (items[head], v))) ∧
      IsQueueHistory (A + 5) (R + 2) (R + 3) N ((items ++ fresh).map Fin.val) (head + 1) s' ∧
      s'.arrs (A + 3) = bfsMarks (items ++ fresh) ∧
      IsBfsParentsAt (A + 4) (edges ++ fresh.map (fun v => (items[head], v))) s' ∧
      (∀ a, a ≠ A + 3 → a ≠ A + 4 → a ≠ A + 5 → s'.arrs a = s.arrs a) ∧
      (∀ r, r ≠ R + 2 → r ≠ R + 3 → r ≠ R + 4 → r ≠ R + 5 → r ≠ R + 6 →
        r ≠ R + 7 → r ≠ R + 8 → s'.regs r = s.regs r) := by
  have hpending : head < (items.map Fin.val).length := by simpa using pending
  have hval : (items.map Fin.val)[head] < 2 ^ w := by
    simpa only [List.getElem_map] using items[head].isLt.trans hN
  obtain ⟨s1, t1, he1, ht1, hq1, hu1⟩ := Triple.queuePop_spec (w := w)
    (A + 5) (R + 2) (R + 3) (R + 4) N (items.map Fin.val) head
    (by omega) (by omega) (by omega) hw hN hpending hval s hq
  have ha1 : ∀ a, s1.arrs a = s.arrs a := fun a =>
    he1.arrs_eq_of_not_mem_writtenArrs (by simp [queuePop, Cmd.writtenArrs])
  obtain ⟨s2, t2, he2, ht2, htr2, hq2, hv2, hp2, ha2, hr2⟩ :=
    bfsScanProg_exec A R htrace pending hG
      (hl.of_arrs_eq (ha1 _) (ha1 _) (ha1 _)) hnd hn hq1
      ((ha1 _).trans hvis) (hpar.of_arrs_eq (ha1 _))
      (by simpa only [List.getElem_map] using hu1) hN hen hw
  refine ⟨s2, t1 + t2, .seq he1 he2, by dsimp at ht1; omega,
    htr2, hq2, hv2, hp2, ?_, ?_⟩
  · intro a h3 h4 h5
    exact (ha2 a h3 h4 h5).trans (ha1 a)
  · intro r h2 h3 h4 h5 h6 h7 h8
    exact (hr2 r h3 h5 h6 h7 h8).trans
      (he1.regs_eq_of_not_mem_writtenRegs (by simp [queuePop, Cmd.writtenRegs, h2, h4]))

end GraphMinor.Compute.Crossing
