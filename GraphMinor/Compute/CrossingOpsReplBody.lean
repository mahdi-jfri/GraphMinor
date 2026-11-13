module

public import GraphMinor.Compute.CrossingOpsReplBoundary
public import GraphMinor.Compute.CrossingOpsReplFilter

/-!
# The new adjacency list of one vertex

A deleted vertex has an empty list. At every other vertex, the program copies undeleted old
neighbours. At a boundary vertex it then adds the missing clique neighbours. The boundary
has at most three entries, so the cost is linear in the old adjacency-list length.
-/

@[expose] public section

namespace GraphMinor.Compute.Crossing

/-- Rebuild one list. The deletion marks are in `A+3`, boundary marks in `A+9`, and
output buffer in `A+4`. Register `R` holds the vertex. -/
def replBody (a_bd A R : ℕ) : Cmd :=
  .ite (.read (A + 3) (.reg R)) .skip
    (.seq (emitSurvivingListProg A (A + 1) (A + 2) (A + 3) (A + 4) R)
      (.ite (.read (A + 9) (.reg R))
        (emitBoundaryProg a_bd A (A + 1) (A + 2) (A + 4) R) .skip))

/-- The body emits `replList`, preserving the old lists and all arrays except its buffer. -/
theorem replBody_exec {w N : ℕ} (a_bd A R : ℕ)
    {G : SimpleGraph (Fin N)} {lists : Fin N → List ℕ} {dl bl pre : List ℕ}
    {s : State} {k x : ℕ}
    (hbd : a_bd < A) (hadj : IsAdjList G A (A + 1) (A + 2) lists s)
    (hbl : s.arrs a_bd = bl) (hsmall : bl.length ≤ 3)
    (hblnd : bl.Nodup) (hblt : ∀ y ∈ bl, y < N)
    (hdel : s.arrs (A + 3) = setAt (List.replicate N 0) dl 1)
    (hboundary : s.arrs (A + 9) = setAt (List.replicate N 0) bl 1)
    (hx : s.regs R = x) (hxN : x < N)
    (hb : IsBuf (A + 4) (R + 4) pre k s) (hk : (replList lists dl bl x).length ≤ k)
    (hw : N + (s.arrs (A + 2)).length + pre.length + k + 2 < 2 ^ w) :
    ∃ s' t, Exec w (replBody a_bd A R) s s' t ∧ t ≤ 120 + 65 * (listOf lists x).length ∧
      IsBuf (A + 4) (R + 4) (pre ++ replList lists dl bl x)
        (k - (replList lists dl bl x).length) s' ∧
      (∀ a, a ≠ A + 4 → s'.arrs a = s.arrs a) ∧
      (∀ r, r ≠ R + 1 → r ≠ R + 2 → r ≠ R + 3 → r ≠ R + 4 →
        r ≠ R + 5 → r ≠ R + 6 → r ≠ R + 7 → r ≠ R + 9 → s'.regs r = s.regs r) := by
  classical
  have htest := eval_membershipMark (w := w) (A + 3) R hdel hx hxN (by omega) (by omega)
  have hrun : ∃ s' t, Exec w (replBody a_bd A R) s s' t ∧
      t ≤ 120 + 65 * (listOf lists x).length ∧
      IsBuf (A + 4) (R + 4) (pre ++ replList lists dl bl x)
        (k - (replList lists dl bl x).length) s' := by
    by_cases hxd : x ∈ dl
    · have hv : (Expr.read (A + 3) (.reg R)).eval w s = some 1 := by simpa [hxd] using htest
      refine ⟨s, 3, .ite_true hv (by decide) (.skip s), by omega, ?_⟩
      simpa [replList, hxd] using hb
    · have hv : (Expr.read (A + 3) (.reg R)).eval w s = some 0 := by simpa [hxd] using htest
      obtain ⟨st, en, hl, hen⟩ := exists_isListAt hadj hxN
      have hlt := listOf_lt hadj.2 x
      have hsurv : ((listOf lists x).filter (fun y => y ∉ dl)).length ≤ k := by
        calc
          _ ≤ (replList lists dl bl x).length := by simp [replList, hxd]
          _ ≤ k := hk
      obtain ⟨s1, t1, hex1, ht1, hb1, ha1, hr1⟩ := emitSurvivingListProg_exec (w := w)
        A (A + 1) (A + 2) (A + 3) (A + 4) R (by omega) (by omega) hl hx hdel hb hsurv
        hlt (by omega) (by omega) (by omega) (by omega)
      have hx1 : s1.regs R = x := (hr1 R (by omega) (by omega) (by omega) (by omega)).trans hx
      have htest1 := eval_membershipMark (w := w) (A + 9) R ((ha1 (A + 9) (by omega)).trans hboundary)
        hx1 hxN (by omega) (by omega)
      have htail : ∃ s2 t2,
          Exec w (.ite (.read (A + 9) (.reg R))
            (emitBoundaryProg a_bd A (A + 1) (A + 2) (A + 4) R) .skip) s1 s2 t2 ∧
          t2 ≤ 105 + 45 * (listOf lists x).length ∧
          IsBuf (A + 4) (R + 4) (pre ++ replList lists dl bl x)
            (k - (replList lists dl bl x).length) s2 := by
        by_cases hxb : x ∈ bl
        · have hv1 : (Expr.read (A + 9) (.reg R)).eval w s1 = some 1 := by
            simpa [hxb] using htest1
          obtain ⟨s2, t2, hex2, ht2, hb2, -, -⟩ := emitBoundaryProg_exec (w := w)
            a_bd A (A + 1) (A + 2) (A + 4) R (by omega) (by omega) (by omega) (by omega)
            ((ha1 a_bd (by omega)).trans hbl) hsmall
            (hl.of_arrs_eq (ha1 A (by omega)) (ha1 (A + 1) (by omega)) (ha1 (A + 2) (by omega)))
            hx1 hb1 (by
              have hk' := hk
              simp only [replList, hxd, ite_false, hxb, ite_true, List.length_append] at hk'
              omega)
            (fun y hy => (hblt y hy).trans (by omega))
            (by have := length_le_of_nodup_lt hblnd hblt; omega)
            (fun y hy => (hlt y hy).trans (by omega)) (by omega) (by omega)
            (by simp only [List.length_append]; omega)
          refine ⟨s2, 2 + t2, .ite_true hv1 (by decide) hex2, by omega, ?_⟩
          simpa only [replList, hxd, ite_false, hxb, ite_true, List.append_assoc,
            List.length_append, Nat.sub_sub] using hb2
        · have hv1 : (Expr.read (A + 9) (.reg R)).eval w s1 = some 0 := by
            simpa [hxb] using htest1
          refine ⟨s1, 3, .ite_false hv1 (.skip s1), by omega, ?_⟩
          simpa [replList, hxd, hxb] using hb1
      obtain ⟨s2, t2, hex2, ht2, hb2⟩ := htail
      exact ⟨s2, 2 + (t1 + t2), .ite_false hv (.seq hex1 hex2), by omega, hb2⟩
  obtain ⟨s', t, hex, ht, hb'⟩ := hrun
  refine ⟨s', t, hex, ht, hb', ?_, ?_⟩
  · intro a ha
    exact hex.arrs_eq_of_not_mem_writtenArrs (by
      simp [replBody, emitSurvivingListProg, emitUnmarkedProg, emitBoundaryProg,
        emitMissingNeighbourProg, findNeighbourProg, forArrProg, forList, forUp,
        emitProg, Cmd.writtenArrs, ha])
  · intro r h1 h2 h3 h4 h5 h6 h7 h9
    exact hex.regs_eq_of_not_mem_writtenRegs (by
      simp [replBody, emitSurvivingListProg, emitUnmarkedProg, emitBoundaryProg,
        emitMissingNeighbourProg, findNeighbourProg, forArrProg, forList, forUp,
        emitProg, Cmd.writtenRegs, h1, h2, h3, h4, h5, h6, h7, h9])

end GraphMinor.Compute.Crossing
