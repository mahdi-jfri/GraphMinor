module

public import GraphMinor.Compute.CrossingOpsReplCopy

/-!
# Allocating and completing the replacement record

The record buffer is allocated from the input list sizes and the number of old adjacency
entries. The body encoder fills it, and the final prefix copy produces the exact-size array
used by the record-append routine. All sizes are read from memory.
-/

@[expose] public section

namespace GraphMinor.Compute.Crossing

open GraphMinor.Crossing

/-- Capacity for the two list fields, at most two words per old adjacency entry, and headers. -/
def replCapacityExpr (a_bd a_rep A : ℕ) : Expr :=
  .op .add (.op .add (.len a_bd) (.len a_rep))
    (.op .add (.op .mul (.const 2) (.len (A + 2))) (.const 5))

/-- Write the replacement encoding into `A+7`, using `A+4` as a buffer. -/
def replEncodeProg (a_bd a_rep A R : ℕ) : Cmd :=
  .seq (.alloc (A + 4) (replCapacityExpr a_bd a_rep A))
    (.seq (.assign (R + 4) (.const 0))
      (.seq (replRecordBodyProg a_bd a_rep (A + 11) A (A + 1) (A + 2) (A + 10) (A + 4) R)
        (finishReplRecordProg (A + 4) (A + 7) R)))

/-- The encoder constructs the replacement record in linear time. The input arrays store
its boundary and component, the union array and marks, and the old adjacency lists. -/
theorem replEncodeProg_exec {w N : ℕ} (a_bd a_rep A R : ℕ)
    {r : ReplRecord (Fin N)} {D : List (Fin N)} {lists : Fin N → List ℕ}
    {B Rp : List (Fin N)} {s : State}
    (hbd : a_bd < A) (hrep : a_rep < A) (hN : s.regs (R + 8) = N)
    (hB : s.arrs a_bd = B.map Fin.val) (hR : s.arrs a_rep = Rp.map Fin.val)
    (hRB : s.arrs (A + 11) = Rp.map Fin.val ++ B.map Fin.val)
    (hmark : s.arrs (A + 10) = setAt (List.replicate N 0) (Rp.map Fin.val ++ B.map Fin.val) 1)
    (hadj : IsAdjList r.graph A (A + 1) (A + 2) lists s)
    (hentries : (s.arrs (A + 2)).length = 2 * r.graph.edgeSet.ncard)
    (hv : r.IsValid D) (hBn : B.Nodup) (hBm : ∀ y, y ∈ B ↔ y ∈ r.boundary)
    (hRn : Rp.Nodup) (hRm : ∀ y, y ∈ Rp ↔ y ∈ r.rep)
    (hw : 10 * (N + r.graph.edgeSet.ncard + 1) < 2 ^ w) :
    ∃ s' t, Exec w (replEncodeProg a_bd a_rep A R) s s' t ∧
      t ≤ 200 * (N + r.graph.edgeSet.ncard + 1) ∧
      s'.arrs (A + 7) = replRecordWords lists (B.map Fin.val) (Rp.map Fin.val) ∧
      IsRecordEnc (CrossRecord.repl r) (s'.arrs (A + 7)) ∧
      (∀ a, a ≠ A + 4 → a ≠ A + 7 → s'.arrs a = s.arrs a) := by
  classical
  let bd := B.map Fin.val
  let rep := Rp.map Fin.val
  let words := replRecordWords lists bd rep
  let cap := bd.length + rep.length + 2 * (s.arrs (A + 2)).length + 5
  have hdisj : ∀ y ∈ Rp, y ∉ B := by
    intro y hy hB'
    exact (hv.2.2.2.1 ((hBm y).mp hB')).2 (hv.2.2.2.2.2.1 ((hRm y).mp hy))
  have hnd : (rep ++ bd).Nodup := by
    rw [← List.map_append]
    exact (List.Nodup.append hRn hBn hdisj).map Fin.val_injective
  have hlt : ∀ x ∈ rep ++ bd, x < N := by
    simpa only [List.map_append] using vals_lt (Rp ++ B)
  have hlen : bd.length + rep.length ≤ N := by
    have := length_le_of_nodup_lt hnd hlt
    simp only [List.length_append] at this
    omega
  have hpair := length_flatMap_pairsOf_le hadj.2 (rb := rep ++ bd) hnd hlt
  have hwordlen : words.length = bd.length + rep.length +
      ((rep ++ bd).flatMap (pairsOf lists (rep ++ bd))).length + 5 := by
    simp only [words, replRecordWords, replHead, withLength, List.length_append,
      List.length_cons, List.length_nil]
    omega
  have hwordcap : words.length ≤ cap := by rw [hwordlen]; dsimp only [cap]; omega
  have hcap : cap ≤ N + 4 * r.graph.edgeSet.ncard + 5 := by dsimp only [cap]; omega
  have hsum : (Expr.op .add (.len a_bd) (.len a_rep)).eval w s =
      some (bd.length + rep.length) :=
    eval_add (eval_len hB (by change bd.length < 2 ^ w; omega))
      (eval_len hR (by change rep.length < 2 ^ w; omega)) (by omega)
  have hmul : (Expr.op .mul (.const 2) (.len (A + 2))).eval w s =
      some (2 * (s.arrs (A + 2)).length) :=
    eval_mul (eval_const (w := w) (c := 2) (by omega))
      (eval_len (a := A + 2) rfl (by omega)) (by omega)
  have htail : (Expr.op .add (.op .mul (.const 2) (.len (A + 2))) (.const 5)).eval w s =
      some (2 * (s.arrs (A + 2)).length + 5) :=
    eval_add hmul (eval_const (by omega)) (by omega)
  have heval : (replCapacityExpr a_bd a_rep A).eval w s = some cap := by
    have hv := eval_add hsum htail (show bd.length + rep.length +
      (2 * (s.arrs (A + 2)).length + 5) < 2 ^ w by omega)
    simpa only [replCapacityExpr, cap, Nat.add_assoc] using hv
  let s0 := s.setArr (A + 4) (List.replicate cap 0)
  have hex0 : Exec w (.alloc (A + 4) (replCapacityExpr a_bd a_rep A)) s s0 (9 + cap) :=
    .alloc heval
  let s1 := s0.setReg (R + 4) 0
  have hex1 : Exec w (.assign (R + 4) (.const 0)) s0 s1 2 := .assign (eval_const (w := w) (by omega))
  have ha1 : ∀ a, a ≠ A + 4 → s1.arrs a = s.arrs a := fun a ha => by
    simp [s1, s0, State.setArr_arrs, ha]
  have hb1 : IsBuf (A + 4) (R + 4) [] cap s1 := by simp [IsBuf, s1, s0]
  obtain ⟨s2, t2, hex2, ht2, hb2, ha2⟩ := replRecordBodyProg_exec (w := w) (bd := bd) (rep := rep)
    a_bd a_rep (A + 11) A (A + 1) (A + 2) (A + 10) (A + 4) R
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    ((ha1 a_bd (by omega)).trans hB) ((ha1 a_rep (by omega)).trans hR)
    ((ha1 (A + 11) (by omega)).trans hRB) hnd hlt
    (hadj.of_arrs_eq (ha1 A (by omega)) (ha1 (A + 1) (by omega)) (ha1 (A + 2) (by omega)))
    ((ha1 (A + 10) (by omega)).trans hmark) hb1 (by dsimp only [cap]; omega)
    (by rw [ha1 (A + 2) (by omega)]; omega)
  have hN2 : s2.regs (R + 8) = N := by
    rw [hex2.regs_eq_of_not_mem_writtenRegs (by
      simp [replRecordBodyProg, replHeaderProg, emitFieldProg, emitArrayProg,
        emitPairsProg, emitPairListProg, emitMarkedPairProg, emitPairProg, patchPairCountProg,
        emitLengthProg, emitProg, forArrProg, forList, forUp, Cmd.writtenRegs])]
    simpa [s1, s0] using hN
  have henc : IsRecordEnc (CrossRecord.repl r) words :=
    isRecordEnc_replRecordWords hadj.2 hv B Rp hBn hBm hRn hRm
  obtain ⟨s3, t3, hex3, ht3, harr3, ha3, hr3⟩ := finishReplRecordProg_exec (w := w) (words := words)
    (A + 4) (A + 7) R (by omega) hN2 hb2 henc (by omega)
  refine ⟨s3, (9 + cap) + (2 + (t2 + t3)), .seq hex0 (.seq hex1 (.seq hex2 hex3)),
    by omega, harr3, by rw [harr3]; exact henc, ?_⟩
  intro a h4 h7
  exact (ha3 a h7).trans ((ha2 a h4).trans (ha1 a h4))

end GraphMinor.Compute.Crossing
