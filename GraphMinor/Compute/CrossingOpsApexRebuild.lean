module

public import GraphMinor.Compute.CrossingOpsApexLoop

/-!
# Allocating the numerical apex graph

The program allocates the two offset arrays and a buffer with two extra entries for
each cycle vertex. It packs the apex lists and copies the used prefix to the entries
array. Both vertex counts and all list lengths come from registers or memory.
-/

@[expose] public section

namespace GraphMinor.Compute.Crossing

/-- Allocate and pack the apex graph. The old and new counts are in `R+9` and `R+8`. -/
def apexRebuildProg (a_D A B R : ℕ) : Cmd :=
  .seq (.alloc B (.reg (R + 8)))
    (.seq (.alloc (B + 1) (.reg (R + 8)))
      (.seq (.alloc (B + 3) (.op .add (.len (A + 2)) (.op .mul (.const 2) (.len a_D))))
        (.seq (.assign (R + 4) (.const 0))
          (.seq (.assign R (.const 0))
            (.seq (apexVertexLoop a_D A B R)
              (.seq (.assign (R + 14) (.reg (R + 4)))
                (.seq (.assign (R + 11) (.reg (R + 8)))
                  (copyMinNProg (B + 3) (B + 2) (R + 11) (R + 12) (R + 14)))))))))

/-- The apex rebuilding command produces exact CSR arrays and keeps the source arrays.
The cycle mark array and both vertex-count registers are its prepared inputs. -/
theorem apexRebuildProg_exec {w N : ℕ} (a_D A B R : ℕ)
    {G : SimpleGraph (Fin N)} {lists : Fin N → List ℕ} {D : List (Fin N)} {s : State}
    (hDA : a_D < A) (hAB : A + 7 ≤ B)
    (hadj : IsAdjList G A (A + 1) (A + 2) lists s)
    (hentries : (s.arrs (A + 2)).length = 2 * G.edgeSet.ncard)
    (hD : s.arrs a_D = D.map Fin.val) (hDnd : D.Nodup)
    (hm : s.arrs (A + 3) = setAt (List.replicate N 0) (D.map Fin.val) 1)
    (hN : s.regs (R + 8) = N + 1) (hNold : s.regs (R + 9) = N)
    (hw : 5 * (N + G.edgeSet.ncard + 1) < 2 ^ w) :
    ∃ s' t, Exec w (apexRebuildProg a_D A B R) s s' t ∧
      t ≤ 200 * (N + G.edgeSet.ncard + 1) ∧
      IsAdjList (apexFinGraph G D) B (B + 1) (B + 2) (fun u => apexList lists D u.val) s' ∧
      (s'.arrs (B + 2)).length = 2 * (apexFinGraph G D).edgeSet.ncard ∧
      (∀ a, a ≠ B → a ≠ B + 1 → a ≠ B + 2 → a ≠ B + 3 → s'.arrs a = s.arrs a) := by
  let L := apexList lists D
  let cap := (s.arrs (A + 2)).length + 2 * D.length
  have hDlen : D.length ≤ N := by simpa using hDnd.length_le_card
  have hcapEq : cap = 2 * G.edgeSet.ncard + 2 * D.length := by simp [cap, hentries]
  have hcap : (flatUpTo L (N + 1)).length = cap := by
    simpa only [hcapEq] using length_flatUpTo_apexList hadj.2 D hDnd
  have hfam := isAdjListFamily_apexList hadj.2 D hDnd
  let s1 := s.setArr B (List.replicate (N + 1) 0)
  let s2 := s1.setArr (B + 1) (List.replicate (N + 1) 0)
  let s3 := s2.setArr (B + 3) (List.replicate cap 0)
  let s4 := s3.setReg (R + 4) 0
  let s5 := s4.setReg R 0
  have he1 : Exec w (.alloc B (.reg (R + 8))) s s1 (1 + (N + 1)) := .alloc (eval_reg hN (by omega))
  have he2 : Exec w (.alloc (B + 1) (.reg (R + 8))) s1 s2 (1 + (N + 1)) :=
    .alloc (eval_reg (by simpa [s1] using hN) (by omega))
  have ha2 : ∀ a, a < B → s2.arrs a = s.arrs a := by
    intro a ha
    simp [s2, s1, State.setArr_arrs, show a ≠ B by omega, show a ≠ B + 1 by omega]
  have hvalD : (Expr.len a_D).eval w s2 = some D.length := by
    simpa only [ha2 a_D (by omega), hD, List.length_map] using
      eval_len (ha2 a_D (by omega)) (show (s.arrs a_D).length < 2 ^ w by simp [hD]; omega)
  have hmul := eval_mul (eval_const (w := w) (s := s2) (c := 2) (by omega)) hvalD
    (show 2 * D.length < 2 ^ w by omega)
  have hval := eval_add (eval_len (ha2 (A + 2) (by omega)) (by omega)) hmul
    (show (s.arrs (A + 2)).length + 2 * D.length < 2 ^ w by omega)
  have he3 : Exec w (.alloc (B + 3) (.op .add (.len (A + 2)) (.op .mul (.const 2) (.len a_D))))
      s2 s3 (5 + cap) := .alloc hval
  have he4 : Exec w (.assign (R + 4) (.const 0)) s3 s4 2 := .assign (eval_const (by omega))
  have he5 : Exec w (.assign R (.const 0)) s4 s5 2 := .assign (eval_const (by omega))
  have ha5 : ∀ a, a < B → s5.arrs a = s.arrs a := by
    intro a ha
    simp [s5, s4, s3, s2, s1, State.setArr_arrs, show a ≠ B by omega,
      show a ≠ B + 1 by omega, show a ≠ B + 3 by omega]
  obtain ⟨s6, t6, he6, ht6, hb6, hst6, hen6, hN6⟩ := apexVertexLoop_exec (w := w)
    a_D A B R hDA hAB (hadj.of_arrs_eq (ha5 _ (by omega)) (ha5 _ (by omega)) (ha5 _ (by omega)))
    ((ha5 _ (by omega)).trans hD) hDnd ((ha5 _ (by omega)).trans hm)
    (by simp [s5]) (by simpa [s5, s4, s3, s2, s1] using hN)
    (by simpa [s5, s4, s3, s2, s1] using hNold)
    (by simp [s5, s4, s3, s2, s1, State.setArr_arrs, show B ≠ B + 1 by omega,
      show B ≠ B + 3 by omega])
    (by simp [s5, s4, s3, s2, State.setArr_arrs, show B + 1 ≠ B + 3 by omega])
    (by simp [IsBuf, s5, s4, s3]) hcap.le
    (by rw [ha5 _ (by omega)]; omega)
  let cnt := (flatUpTo L (N + 1)).length
  let s7 := s6.setReg (R + 14) cnt
  let s8 := s7.setReg (R + 11) (N + 1)
  have he7 : Exec w (.assign (R + 14) (.reg (R + 4))) s6 s7 2 :=
    .assign (eval_reg hb6.2 (by omega))
  have he8 : Exec w (.assign (R + 11) (.reg (R + 8))) s7 s8 2 :=
    .assign (eval_reg (by simpa [s7] using hN6) (by omega))
  obtain ⟨s9, t9, he9, ht9, harr9, ha9, hr9⟩ := copyMinNProg_exec (w := w)
    (B + 3) (B + 2) (R + 11) (R + 12) (R + 14) (by omega) (by omega) (by omega) (by omega)
    (s := s8) (B := N + 1) (n := cnt) (by simp [s8]) (by omega) (by omega)
    (by simp [s8, s7]) (by omega) (by simp [s8, s7, hb6.1, cnt, L])
  have hst9 : s9.arrs B = (List.range (N + 1)).map (fun x => (flatUpTo L x).length) :=
    (ha9 _ (by omega)).trans (by simpa [s8, s7] using hst6)
  have hen9 : s9.arrs (B + 1) = (List.range (N + 1)).map (fun x => (flatUpTo L (x + 1)).length) :=
    (ha9 _ (by omega)).trans (by simpa [s8, s7] using hen6)
  have hent9 : s9.arrs (B + 2) = flatUpTo L (N + 1) := by
    rw [harr9]
    simp only [s8, s7, State.setReg_arrs, hb6.1]
    rw [List.take_left' (show cnt = (flatUpTo L (N + 1)).length from rfl)]
    exact map_min_of_le (fun x hx => (lt_of_mem_flatUpTo hfam x hx).le)
  have hex := Exec.seq he1 (.seq he2 (.seq he3 (.seq he4 (.seq he5
    (.seq he6 (.seq he7 (.seq he8 he9)))))))
  refine ⟨s9, _, hex, by omega, ⟨isListFamily_flatUpTo hst9 hen9 hent9, hfam⟩, ?_, ?_⟩
  · rw [hent9]
    exact length_flatUpTo_eq hfam
  · intro a h0 h1 h2 h3
    exact hex.arrs_eq_of_not_mem_writtenArrs (by
      simp [apexRebuildProg, apexVertexLoop, vertexLoopProg, apexBody, filterListProg,
        forList, forUp, emitWhenProg, emitArrayProg, forArrProg, emitProg,
        copyMinNProg, Cmd.writtenArrs, h0, h1, h2, h3])

end GraphMinor.Compute.Crossing
