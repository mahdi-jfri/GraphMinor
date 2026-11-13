module

public import GraphMinor.Compute.CrossingOpsResidualLoop

/-!
# Allocating and packing the residual graph

The program allocates fresh offset arrays and a buffer no longer than the old entries
array. After filtering the lists, it copies their used prefix to the new entries array.
The old graph and its parent words remain available for later edge-retention tests.
-/

@[expose] public section

namespace GraphMinor.Compute.Crossing

/-- Allocate and pack the graph after deleting the parent forest. Register `R+8` holds `N`. -/
def residualRebuildProg (A B R : ℕ) : Cmd :=
  .seq (.alloc B (.reg (R + 8)))
    (.seq (.alloc (B + 1) (.reg (R + 8)))
      (.seq (.alloc (B + 3) (.len (A + 2)))
        (.seq (.assign (R + 4) (.const 0))
          (.seq (.assign R (.const 0))
            (.seq (residualVertexLoop A B R)
              (.seq (.assign (R + 14) (.reg (R + 4)))
                (.seq (.assign (R + 11) (.reg (R + 8)))
                  (copyMinNProg (B + 3) (B + 2) (R + 11) (R + 12) (R + 14)))))))))

/-- Rebuilding the residual graph takes linear time, stores its exact CSR layout, and
preserves the input arrays. -/
theorem residualRebuildProg_exec {w N : ℕ} (A B R : ℕ)
    {G : SimpleGraph (Fin N)} {lists : Fin N → List ℕ}
    {edges : List (Fin N × Fin N)} {s : State}
    (hAB : A + 5 ≤ B) (hadj : IsAdjList G A (A + 1) (A + 2) lists s)
    (hp : IsBfsParentsAt (A + 4) edges s)
    (hentries : (s.arrs (A + 2)).length = 2 * G.edgeSet.ncard)
    (hN : s.regs (R + 8) = N) (hw : N + 2 * G.edgeSet.ncard + 2 < 2 ^ w) :
    ∃ s' t, Exec w (residualRebuildProg A B R) s s' t ∧
      t ≤ 30 + 24 * N + 92 * G.edgeSet.ncard ∧
      IsAdjList (G \ bfsDiscoveryForest edges) B (B + 1) (B + 2)
        (fun u => residualList lists edges u.val) s' ∧
      (s'.arrs (B + 2)).length = 2 * (G \ bfsDiscoveryForest edges).edgeSet.ncard ∧
      (∀ a, a ≠ B → a ≠ B + 1 → a ≠ B + 2 → a ≠ B + 3 → s'.arrs a = s.arrs a) := by
  let L := residualList lists edges
  let cap := (s.arrs (A + 2)).length
  have hcap : (flatUpTo L N).length ≤ cap := by
    simpa only [cap, hentries] using length_flatUpTo_residualList_le hadj.2 edges
  have hcapEq : cap = 2 * G.edgeSet.ncard := hentries
  have hfam := isAdjListFamily_residualList hadj.2 edges
  let s1 := s.setArr B (List.replicate N 0)
  let s2 := s1.setArr (B + 1) (List.replicate N 0)
  let s3 := s2.setArr (B + 3) (List.replicate cap 0)
  let s4 := s3.setReg (R + 4) 0
  let s5 := s4.setReg R 0
  have he1 : Exec w (.alloc B (.reg (R + 8))) s s1 (1 + N) := .alloc (eval_reg hN (by omega))
  have he2 : Exec w (.alloc (B + 1) (.reg (R + 8))) s1 s2 (1 + N) :=
    .alloc (eval_reg (by simpa [s1] using hN) (by omega))
  have ha2 : s2.arrs (A + 2) = s.arrs (A + 2) := by
    simp [s2, s1, State.setArr_arrs, show A + 2 ≠ B by omega, show A + 2 ≠ B + 1 by omega]
  have he3 : Exec w (.alloc (B + 3) (.len (A + 2))) s2 s3 (1 + cap) :=
    .alloc (eval_len ha2 (by omega))
  have he4 : Exec w (.assign (R + 4) (.const 0)) s3 s4 2 := .assign (eval_const (by omega))
  have he5 : Exec w (.assign R (.const 0)) s4 s5 2 := .assign (eval_const (by omega))
  have ha5 : ∀ a, a ≠ B → a ≠ B + 1 → a ≠ B + 3 → s5.arrs a = s.arrs a := by
    intro a h0 h1 h3
    simp [s5, s4, s3, s2, s1, State.setArr_arrs, h0, h1, h3]
  obtain ⟨s6, t6, he6, ht6, hb6, hst6, hen6, hN6⟩ := residualVertexLoop_exec (w := w) A B R hAB
    (hadj.of_arrs_eq (ha5 _ (by omega) (by omega) (by omega))
      (ha5 _ (by omega) (by omega) (by omega)) (ha5 _ (by omega) (by omega) (by omega)))
    (hp.of_arrs_eq (ha5 _ (by omega) (by omega) (by omega)))
    (by rw [ha5 _ (by omega) (by omega) (by omega)])
    (by simp [s5]) (by simpa [s5, s4, s3, s2, s1] using hN)
    (by simp [s5, s4, s3, s2, s1, State.setArr_arrs, show B ≠ B + 1 by omega,
      show B ≠ B + 3 by omega])
    (by simp [s5, s4, s3, s2, State.setArr_arrs, show B + 1 ≠ B + 3 by omega])
    (by simp [IsBuf, s5, s4, s3]) hcap (by omega)
  let cnt := (flatUpTo L N).length
  let s7 := s6.setReg (R + 14) cnt
  let s8 := s7.setReg (R + 11) N
  have he7 : Exec w (.assign (R + 14) (.reg (R + 4))) s6 s7 2 :=
    .assign (eval_reg hb6.2 (by omega))
  have he8 : Exec w (.assign (R + 11) (.reg (R + 8))) s7 s8 2 :=
    .assign (eval_reg (by simpa [s7] using hN6) (by omega))
  obtain ⟨s9, t9, he9, ht9, harr9, ha9, hr9⟩ := copyMinNProg_exec (w := w)
    (B + 3) (B + 2) (R + 11) (R + 12) (R + 14) (by omega) (by omega) (by omega) (by omega)
    (s := s8) (B := N) (n := cnt) (by simp [s8]) (by omega) (by omega)
    (by simp [s8, s7]) (by omega) (by simp [s8, s7, hb6.1, cnt, L])
  have hst9 : s9.arrs B = (List.range N).map (fun x => (flatUpTo L x).length) :=
    (ha9 _ (by omega)).trans (by simpa [s8, s7] using hst6)
  have hen9 : s9.arrs (B + 1) = (List.range N).map (fun x => (flatUpTo L (x + 1)).length) :=
    (ha9 _ (by omega)).trans (by simpa [s8, s7] using hen6)
  have hent9 : s9.arrs (B + 2) = flatUpTo L N := by
    rw [harr9]
    simp only [s8, s7, State.setReg_arrs, hb6.1]
    rw [List.take_left' (show cnt = (flatUpTo L N).length from rfl)]
    exact map_min_of_le (fun x hx => (lt_of_mem_flatUpTo hfam x hx).le)
  have hex := Exec.seq he1 (.seq he2 (.seq he3 (.seq he4 (.seq he5
    (.seq he6 (.seq he7 (.seq he8 he9)))))))
  refine ⟨s9, _, hex, by omega, ⟨isListFamily_flatUpTo hst9 hen9 hent9, hfam⟩, ?_, ?_⟩
  · rw [hent9]
    exact length_flatUpTo_eq hfam
  · intro a h0 h1 h2 h3
    exact hex.arrs_eq_of_not_mem_writtenArrs (by
      simp [residualRebuildProg, residualVertexLoop, vertexLoopProg, filterListProg,
        forList, forUp, emitWhenProg, emitProg, copyMinNProg, Cmd.writtenArrs, h0, h1, h2, h3])

end GraphMinor.Compute.Crossing
