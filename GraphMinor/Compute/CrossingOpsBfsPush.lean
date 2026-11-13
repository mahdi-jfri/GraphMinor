module

public import GraphMinor.Compute.DisjointPaths
public import GraphMinor.Compute.CrossingOpsBfsParents
public import GraphMinor.Compute.CrossingOpsBasic

/-!
# Discovering a vertex and recording its BFS parent

The residual-search library already provides `tryPushReg`: it marks an unvisited vertex,
stores a parent, and appends the vertex to a queue. This file verifies that command for
an ordinary BFS forest, with an arbitrary number of vertices and a persistent queue history.
-/

@[expose] public section

namespace GraphMinor.Compute.Crossing

/-- The zero-one array of vertices already in the queue history. -/
def bfsMarks {N : ℕ} (items : List (Fin N)) : List ℕ :=
  List.ofFn (fun v : Fin N => if v ∈ items then 1 else 0)

/-- Marking a vertex adds it to the discovered set. -/
theorem bfsMarks_set {N : ℕ} (items : List (Fin N)) (v : Fin N) :
    (bfsMarks items).set v.val 1 = bfsMarks (items ++ [v]) := by
  classical
  apply List.ext_getElem (by simp [bfsMarks])
  intro i hi hi'
  simp only [bfsMarks, List.length_ofFn] at hi hi'
  simp only [bfsMarks, List.getElem_set, List.getElem_ofFn, List.mem_append, List.mem_singleton]
  by_cases hv : v.val = i
  · have heq : (⟨i, hi'⟩ : Fin N) = v := Fin.ext hv.symm
    simp [hv, heq]
  · have heq : (⟨i, hi'⟩ : Fin N) ≠ v := fun e => hv (congrArg Fin.val e).symm
    simp [hv, heq]

/-- The BFS discovery command appends an unmarked vertex, writes its parent, and preserves
all other arrays. It takes at most seventeen steps, including the membership test. -/
theorem tryPushReg_forest_exec {w N : ℕ} (a_vis a_par a_q R : ℕ)
    {items : List (Fin N)} {head : ℕ} {s : State} (v p : Fin N)
    (hvp : a_vis ≠ a_par) (hvq : a_vis ≠ a_q) (hpq : a_par ≠ a_q)
    (hvis : s.arrs a_vis = bfsMarks items) (hpar : (s.arrs a_par).length = N)
    (hq : IsQueueHistory a_q (R + 2) (R + 3) N (items.map Fin.val) head s)
    (hnd : items.Nodup) (hv : s.regs (R + 7) = v.val) (hp : s.regs (R + 4) = p.val)
    (hN : N < 2 ^ w) (hw : 1 < 2 ^ w) :
    ∃ s' t, Exec w (tryPushReg a_vis a_par a_q (R + 3) (R + 8) (R + 7) (R + 4)) s s' t ∧
      t ≤ 17 ∧
      IsQueueHistory a_q (R + 2) (R + 3) N
        ((items ++ if v ∈ items then [] else [v]).map Fin.val) head s' ∧
      s'.arrs a_vis = bfsMarks (items ++ if v ∈ items then [] else [v]) ∧
      s'.arrs a_par = (if v ∈ items then s.arrs a_par else (s.arrs a_par).set v.val p.val) ∧
      (∀ a, a ≠ a_vis → a ≠ a_par → a ≠ a_q → s'.arrs a = s.arrs a) ∧
      (∀ r, r ≠ R + 3 → r ≠ R + 8 → s'.regs r = s.regs r) := by
  classical
  have hvlen : v.val < (s.arrs a_vis).length := by simp [hvis, bfsMarks]
  have hvval : (s.arrs a_vis)[v.val] = if v ∈ items then 1 else 0 := by simp [hvis, bfsMarks]
  have hread : (Expr.read a_vis (.reg (R + 7))).eval w s = some (if v ∈ items then 1 else 0) := by
    have := eval_read (w := w) (a := a_vis) (eval_reg hv (v.isLt.trans hN)) hvlen
      (by rw [hvval]; split <;> omega)
    simpa only [hvval] using this
  let mark := if v ∈ items then 1 else 0
  let s0 := s.setReg (R + 8) mark
  have hex0 : Exec w (.assign (R + 8) (.read a_vis (.reg (R + 7)))) s s0 3 := .assign hread
  have hrun : ∃ s' t, Exec w (tryPushReg a_vis a_par a_q (R + 3) (R + 8) (R + 7) (R + 4)) s s' t ∧
      t ≤ 17 ∧
      IsQueueHistory a_q (R + 2) (R + 3) N
        ((items ++ if v ∈ items then [] else [v]).map Fin.val) head s' ∧
      s'.arrs a_vis = bfsMarks (items ++ if v ∈ items then [] else [v]) ∧
      s'.arrs a_par = (if v ∈ items then s.arrs a_par else (s.arrs a_par).set v.val p.val) := by
    by_cases hvm : v ∈ items
    · have he : (Expr.reg (R + 8)).eval w s0 = some 1 :=
        eval_reg (by simp [s0, mark, hvm]) hw
      refine ⟨s0, 5, .seq hex0 (.ite_true he (by decide) (.skip s0)), by omega, ?_, ?_, ?_⟩
      · simpa [hvm] using hq.of_eq (s' := s0) rfl (by simp [s0]) (by simp [s0])
      · simpa [hvm, s0] using hvis
      · simp [hvm, s0]
    · let s1 := s0.writeArr a_vis v.val 1
      let s2 := s1.writeArr a_par v.val p.val
      have hex1 : Exec w (.write a_vis (.reg (R + 7)) (.const 1)) s0 s1 3 :=
        .write (eval_reg (by simp [s0, hv]) (v.isLt.trans hN)) (eval_const hw)
          (by simpa [s0] using hvlen)
      have hex2 : Exec w (.write a_par (.reg (R + 7)) (.reg (R + 4))) s1 s2 3 :=
        .write (eval_reg (by simp [s1, s0, hv]) (v.isLt.trans hN))
          (eval_reg (by simp [s1, s0, hp]) (p.isLt.trans hN))
          (by simp [s1, s0, State.writeArr_arrs_ne _ _ _ (Ne.symm hvp), hpar])
      have hq2 : IsQueueHistory a_q (R + 2) (R + 3) N (items.map Fin.val) head s2 :=
        hq.of_eq (by simp [s2, s1, s0, State.writeArr_arrs_ne _ _ _ (Ne.symm hvq),
          State.writeArr_arrs_ne _ _ _ (Ne.symm hpq)]) (by simp [s2, s1, s0]) (by simp [s2, s1, s0])
      have hlen : (items.map Fin.val).length < N := by
        have hc := (List.nodup_cons.mpr ⟨hvm, hnd⟩).length_le_card
        simp only [List.length_cons, Fintype.card_fin] at hc
        simp only [List.length_map]
        omega
      obtain ⟨s3, t3, hex3, ht3, hq3⟩ := Triple.queuePush_spec (w := w) a_q (R + 2) (R + 3)
        (.reg (R + 7)) N (items.map Fin.val) head v.val (by omega) hw hN hlen s2
        ⟨hq2, eval_reg (by simp [s2, s1, s0, hv]) (v.isLt.trans hN)⟩
      have he : (Expr.reg (R + 8)).eval w s0 = some 0 :=
        eval_reg (by simp [s0, mark, hvm]) (by omega)
      refine ⟨s3, 3 + (1 + (3 + (3 + t3))), .seq hex0 (.ite_false he (.seq hex1 (.seq hex2 hex3))),
        by simp only [Expr.cost] at ht3; omega, ?_, ?_, ?_⟩
      · simpa [hvm] using hq3
      · rw [hex3.arrs_eq_of_not_mem_writtenArrs (a := a_vis) (by
          simp [queuePush, Cmd.writtenArrs, hvq])]
        simp only [s2, State.writeArr_arrs_ne _ _ _ hvp, s1, State.writeArr_arrs_self,
          s0, State.setReg_arrs, hvis, bfsMarks_set]
        simp [hvm]
      · rw [hex3.arrs_eq_of_not_mem_writtenArrs (a := a_par) (by
          simp [queuePush, Cmd.writtenArrs, hpq])]
        simp [s2, s1, s0, State.writeArr_arrs_ne _ _ _ (Ne.symm hvp), hvm]
  obtain ⟨s', t, hex, ht, hq', hvis', hpar'⟩ := hrun
  refine ⟨s', t, hex, ht, hq', hvis', hpar', ?_, ?_⟩
  · intro a ha1 ha2 ha3
    exact hex.arrs_eq_of_not_mem_writtenArrs (by simp [tryPushReg, queuePush, Cmd.writtenArrs, ha1, ha2, ha3])
  · intro r hr3 hr8
    exact hex.regs_eq_of_not_mem_writtenRegs (by simp [tryPushReg, queuePush, Cmd.writtenRegs, hr3, hr8])

end GraphMinor.Compute.Crossing
