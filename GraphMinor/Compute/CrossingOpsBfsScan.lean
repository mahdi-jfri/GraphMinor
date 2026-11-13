module

public import GraphMinor.Compute.CrossingOpsBfsFresh

/-!
# Scanning one BFS adjacency list

The program scans a vertex's adjacency list and discovers every unmarked neighbour.
The invariant records exactly the newly discovered prefix and its parent edges. This yields
one scan transition of the BFS history, with time proportional to the old list length.
-/

@[expose] public section

namespace GraphMinor.Compute.Crossing

open GraphMinor.Crossing

/-- Scan the list of the vertex in `R+4`. Arrays `A+3,A+4,A+5` hold marks, parents, and queue. -/
def bfsScanProg (A R : ℕ) : Cmd :=
  forList A (A + 1) (A + 2) (R + 4) (R + 5) (R + 6) (R + 7)
    (tryPushReg (A + 3) (A + 4) (A + 5) (R + 3) (R + 8) (R + 7) (R + 4))

/-- Scanning an adjacency list discovers exactly its previously unmarked vertices and
records the corresponding parent edges. The queue head has already been advanced by the pop. -/
theorem bfsScanProg_exec {w N : ℕ} (A R : ℕ) {G : SimpleGraph (Fin N)} {T : Set (Fin N)}
    {items nbrs : List (Fin N)} {head : ℕ} {edges : List (Fin N × Fin N)} {s : State}
    {st en : ℕ} (htrace : BfsScanTrace G T items head edges) (pending : head < items.length)
    (hG : HP25.IsSupportedOn G T)
    (hl : IsListAt A (A + 1) (A + 2) items[head].val st en (nbrs.map Fin.val) s)
    (hnd : nbrs.Nodup) (hn : ∀ v, v ∈ nbrs ↔ G.Adj items[head] v)
    (hq : IsQueueHistory (A + 5) (R + 2) (R + 3) N (items.map Fin.val) (head + 1) s)
    (hvis : s.arrs (A + 3) = bfsMarks items) (hpar : IsBfsParentsAt (A + 4) edges s)
    (hu : s.regs (R + 4) = items[head].val)
    (hN : N < 2 ^ w) (hen : en < 2 ^ w) (hw : 1 < 2 ^ w) :
    let fresh := nbrs.filter (fun v => v ∉ items)
    ∃ s' t, Exec w (bfsScanProg A R) s s' t ∧ t ≤ 9 + 27 * nbrs.length ∧
      BfsScanTrace G T (items ++ fresh) (head + 1)
        (edges ++ fresh.map (fun v => (items[head], v))) ∧
      IsQueueHistory (A + 5) (R + 2) (R + 3) N ((items ++ fresh).map Fin.val) (head + 1) s' ∧
      s'.arrs (A + 3) = bfsMarks (items ++ fresh) ∧
      IsBfsParentsAt (A + 4) (edges ++ fresh.map (fun v => (items[head], v))) s' ∧
      (∀ a, a ≠ A + 3 → a ≠ A + 4 → a ≠ A + 5 → s'.arrs a = s.arrs a) ∧
      (∀ r, r ≠ R + 3 → r ≠ R + 5 → r ≠ R + 6 → r ≠ R + 7 → r ≠ R + 8 →
        s'.regs r = s.regs r) := by
  classical
  let current (j : ℕ) := items ++ bfsFresh items nbrs j
  let parents (j : ℕ) := edges ++ (bfsFresh items nbrs j).map (fun v => (items[head], v))
  let I : ℕ → State → Prop := fun j z =>
    IsQueueHistory (A + 5) (R + 2) (R + 3) N ((current j).map Fin.val) (head + 1) z ∧
    z.arrs (A + 3) = bfsMarks (current j) ∧ IsBfsParentsAt (A + 4) (parents j) z ∧
    z.regs (R + 4) = items[head].val ∧
    (∀ a, a ≠ A + 3 → a ≠ A + 4 → a ≠ A + 5 → z.arrs a = s.arrs a)
  have hmove : ∀ j z z', I j z → z'.arrs = z.arrs →
      (∀ r, r ≠ R + 5 → r ≠ R + 6 → r ≠ R + 7 → z'.regs r = z.regs r) → I j z' := by
    intro j z z' h ha hr
    refine ⟨h.1.of_eq (congrFun ha _) (hr _ (by omega) (by omega) (by omega))
      (hr _ (by omega) (by omega) (by omega)), ?_, ?_, ?_, ?_⟩
    · rw [ha]; exact h.2.1
    · exact h.2.2.1.of_arrs_eq (congrFun ha _)
    · exact (hr _ (by omega) (by omega) (by omega)).trans h.2.2.2.1
    · intro a h3 h4 h5; rw [ha]; exact h.2.2.2.2 a h3 h4 h5
  have hI0 : I 0 s := by
    simpa only [I, current, parents, bfsFresh, List.take_zero, List.filter_nil,
      List.append_nil, List.map_nil] using
      (show IsQueueHistory (A + 5) (R + 2) (R + 3) N (items.map Fin.val) (head + 1) s ∧
        s.arrs (A + 3) = bfsMarks items ∧ IsBfsParentsAt (A + 4) edges s ∧
        s.regs (R + 4) = items[head].val ∧
        (∀ a, a ≠ A + 3 → a ≠ A + 4 → a ≠ A + 5 → s.arrs a = s.arrs a) from
          ⟨hq, hvis, hpar, hu, fun _ _ _ _ => rfl⟩)
  obtain ⟨s', t, hex, ht, hI⟩ := forList_exec (w := w) A (A + 1) (A + 2) (R + 4)
    (R + 5) (R + 6) (R + 7)
    (tryPushReg (A + 3) (A + 4) (A + 5) (R + 3) (R + 8) (R + 7) (R + 4))
    items[head].val st en (nbrs.map Fin.val) I 17 (by omega) (by omega) hw hen
    (items[head].isLt.trans hN) hl hu
    (hmove 0 s _ hI0 rfl (fun r h5 h6 _ => by simp [State.setReg_regs, h5, h6]))
    (fun j hj z h => by
      have ha := h.2.2.2.2 (A + 2) (by omega) (by omega) (by omega)
      rw [ha]
      obtain ⟨-, -, hlen, hdiff, -, -, -, hget⟩ := hl
      exact ⟨by omega, hget j hj⟩)
    (fun x hx => by
      obtain ⟨v, -, rfl⟩ := List.mem_map.mp hx
      exact v.isLt.trans hN)
    (fun j hj z h hri hrhi => by
      have hj' : j < nbrs.length := by simpa only [List.length_map] using hj
      let v := nbrs[j]
      let z0 := z.setReg (R + 7) v.val
      have h0 : I j z0 := hmove j z z0 h rfl
        (fun r _ _ h7 => by simp [z0, State.setReg_regs, h7])
      have hvreg : z0.regs (R + 7) = v.val := by simp [z0]
      have hchild : ∀ p c, (p, c) ∈ parents j → c ∈ current j :=
        bfsFresh_edge_child items nbrs edges items[head] j (fun p c he => (htrace.edge_endpoints p c he).2.1)
      obtain ⟨z1, t1, he1, ht1, hq1, hvis1, hpar1, ha1, hr1⟩ := tryPushReg_forest_parents_exec
        (w := w) (A + 3) (A + 4) (A + 5) R v items[head] (by omega) (by omega) (by omega)
        h0.2.1 h0.2.2.1 h0.1 (bfsFresh_nodup items nbrs htrace.nodup hnd j) hvreg h0.2.2.2.1
        (fun hv q he => hv (hchild q v he)) hN hw
      have hvm : v ∈ current j ↔ v ∈ items := bfsFresh_next_mem_iff items nbrs hnd hj'
      have hiStep : current j ++ (if v ∈ current j then [] else [v]) = current (j + 1) := by
        simp only [hvm]
        dsimp only [current]
        rw [bfsFresh_succ items nbrs hj']
        simp only [List.append_assoc, v]
      have hpStep : parents j ++ (if v ∈ current j then [] else [(items[head], v)]) = parents (j + 1) := by
        simp only [hvm]
        dsimp only [parents]
        rw [bfsFresh_succ items nbrs hj', List.map_append]
        by_cases hv : v ∈ items <;> simp [hv, v, List.append_assoc] at hv ⊢
      have hI1 : I (j + 1) z1 := by
        refine ⟨?_, ?_, ?_, ?_, ?_⟩
        · simpa only [hiStep] using hq1
        · simpa only [hiStep] using hvis1
        · simpa only [hpStep] using hpar1
        · exact (hr1 (R + 4) (by omega) (by omega)).trans h0.2.2.2.1
        · intro a h3 h4 h5
          exact (ha1 a h3 h4 h5).trans (h0.2.2.2.2 a h3 h4 h5)
      refine ⟨z1, t1, ?_, ht1, ?_, ?_, ?_⟩
      · simpa only [z0, v, List.getElem_map] using he1
      · simpa only [z0, State.setReg_regs_ne _ _ (show R + 5 ≠ R + 7 by omega)] using
          (hr1 (R + 5) (by omega) (by omega)).trans (by simpa [z0] using hri)
      · simpa only [z0, State.setReg_regs_ne _ _ (show R + 6 ≠ R + 7 by omega)] using
          (hr1 (R + 6) (by omega) (by omega)).trans (by simpa [z0] using hrhi)
      · exact hmove (j + 1) z1 _ hI1 rfl
          (fun r h5 _ _ => by simp [State.setReg_regs, h5]))
  let fresh := nbrs.filter (fun v => v ∉ items)
  have hc : current (nbrs.map Fin.val).length = items ++ fresh := by
    simp [current, bfsFresh, fresh]
  have hp : parents (nbrs.map Fin.val).length = edges ++ fresh.map (fun v => (items[head], v)) := by
    simp [parents, bfsFresh, fresh]
  have htr : BfsScanTrace G T (items ++ fresh) (head + 1)
      (edges ++ fresh.map (fun v => (items[head], v))) := by
    apply htrace.scan pending fresh (hnd.filter _)
    intro v
    simp only [fresh, List.mem_filter, decide_eq_true_eq, hn]
    constructor
    · rintro ⟨hvadj, hvnot⟩
      exact ⟨hvadj, hG hvadj.symm, hvnot⟩
    · rintro ⟨hvadj, -, hvnot⟩
      exact ⟨hvadj, hvnot⟩
  refine ⟨s', t, hex, by simpa only [List.length_map, Nat.mul_comm] using ht, htr,
    by simpa only [hc] using hI.1, by simpa only [hc] using hI.2.1,
    by simpa only [hp] using hI.2.2.1, hI.2.2.2.2, ?_⟩
  intro r h3 h5 h6 h7 h8
  exact hex.regs_eq_of_not_mem_writtenRegs (by
    simp [bfsScanProg, forList, forUp, tryPushReg, queuePush, Cmd.writtenRegs, h3, h5, h6, h7, h8])

end GraphMinor.Compute.Crossing
