module

public import GraphMinor.Compute.CrossingOpsReplLoop

/-!
# Allocating and storing the replacement adjacency lists

The rebuilding phase allocates start and end arrays and a buffer large enough for the
old entries and three additional neighbours per vertex. It runs the vertex loop and
copies the used prefix to the new entries array.
-/

@[expose] public section

namespace GraphMinor.Compute.Crossing

/-- Allocate and rebuild the replacement's adjacency-list arrays. -/
def replRebuildProg (a_bd a_st a_en a_ent A R : ℕ) : Cmd :=
  .seq (.alloc a_st (.reg (R + 8)))
    (.seq (.alloc a_en (.reg (R + 8)))
      (.seq (.alloc (A + 4) (.op .add (.len (A + 2)) (.op .mul (.const 3) (.reg (R + 8)))))
        (.seq (.assign (R + 4) (.const 0))
          (.seq (.assign R (.const 0))
            (.seq (vertexLoopProg R (R + 8) (R + 4) a_st a_en (replBody a_bd A R))
              (.seq (.assign (R + 14) (.reg (R + 4)))
                (.seq (.assign (R + 11) (.reg (R + 8)))
                  (copyMinNProg (A + 4) a_ent (R + 11) (R + 12) (R + 14)))))))))

/-- The rebuilding phase stores the packed lists and their offsets. Its family hypothesis
identifies the graph represented by those lists and supplies the bound on their entries. -/
theorem replRebuildProg_exec {w N : ℕ} (a_bd a_st a_en a_ent A R : ℕ)
    {G H : SimpleGraph (Fin N)} {lists : Fin N → List ℕ} {dl bl : List ℕ} {s : State}
    (hbd : a_bd < A) (hst : a_st < A) (hen : a_en < A) (hent : a_ent < A)
    (hse : a_st ≠ a_en) (hste : a_st ≠ a_ent) (hene : a_en ≠ a_ent)
    (hbs : a_bd ≠ a_st) (hbe : a_bd ≠ a_en)
    (hadj : IsAdjList G A (A + 1) (A + 2) lists s)
    (hentries : (s.arrs (A + 2)).length = 2 * G.edgeSet.ncard)
    (hbl : s.arrs a_bd = bl) (hsmall : bl.length ≤ 3)
    (hblnd : bl.Nodup) (hblt : ∀ y ∈ bl, y < N)
    (hdel : s.arrs (A + 3) = setAt (List.replicate N 0) dl 1)
    (hboundary : s.arrs (A + 9) = setAt (List.replicate N 0) bl 1)
    (hN : s.regs (R + 8) = N)
    (hfam : IsAdjListFamily H (fun x => replList lists dl bl x))
    (hw : 10 * (N + G.edgeSet.ncard + 1) < 2 ^ w) :
    ∃ s' t, Exec w (replRebuildProg a_bd a_st a_en a_ent A R) s s' t ∧
      t ≤ 300 * (N + G.edgeSet.ncard + 1) ∧
      s'.arrs a_st = (List.range N).map (fun x => (flatUpTo (replList lists dl bl) x).length) ∧
      s'.arrs a_en = (List.range N).map (fun x => (flatUpTo (replList lists dl bl) (x + 1)).length) ∧
      s'.arrs a_ent = flatUpTo (replList lists dl bl) N := by
  let L := replList lists dl bl
  let cap := (s.arrs (A + 2)).length + 3 * N
  have hcap : (flatUpTo L N).length ≤ cap := by
    have := length_flatUpTo_replList_linear hadj.2 dl bl hblnd hblt hsmall
    dsimp only [cap, L]
    omega
  have hcapEq : cap = 2 * G.edgeSet.ncard + 3 * N := by dsimp only [cap]; rw [hentries]
  let s1 := s.setArr a_st (List.replicate N 0)
  let s2 := s1.setArr a_en (List.replicate N 0)
  let s3 := s2.setArr (A + 4) (List.replicate cap 0)
  let s4 := s3.setReg (R + 4) 0
  let s5 := s4.setReg R 0
  have hex1 : Exec w (.alloc a_st (.reg (R + 8))) s s1 (1 + N) := .alloc (eval_reg hN (by omega))
  have hex2 : Exec w (.alloc a_en (.reg (R + 8))) s1 s2 (1 + N) :=
    .alloc (eval_reg (by simpa [s1] using hN) (by omega))
  have hm : (Expr.op .mul (.const 3) (.reg (R + 8))).eval w s2 = some (3 * N) :=
    eval_mul (eval_const (w := w) (by omega)) (eval_reg (by simpa [s2, s1] using hN) (by omega)) (by omega)
  have hlen2 : s2.arrs (A + 2) = s.arrs (A + 2) := by
    simp [s2, s1, State.setArr_arrs, show A + 2 ≠ a_st by omega, show A + 2 ≠ a_en by omega]
  have heval : (Expr.op .add (.len (A + 2)) (.op .mul (.const 3) (.reg (R + 8)))).eval w s2 =
      some cap := eval_add (eval_len hlen2 (by omega)) hm (by omega)
  have hex3 : Exec w (.alloc (A + 4)
      (.op .add (.len (A + 2)) (.op .mul (.const 3) (.reg (R + 8))))) s2 s3 (5 + cap) := .alloc heval
  have hex4 : Exec w (.assign (R + 4) (.const 0)) s3 s4 2 := .assign (eval_const (by omega))
  have hex5 : Exec w (.assign R (.const 0)) s4 s5 2 := .assign (eval_const (by omega))
  have ha5 : ∀ a, a ≠ a_st → a ≠ a_en → a ≠ A + 4 → s5.arrs a = s.arrs a := by
    intro a h1 h2 h3
    simp [s5, s4, s3, s2, s1, State.setArr_arrs, h1, h2, h3]
  obtain ⟨s6, t6, hex6, ht6, hb6, hst6, hen6, hN6⟩ := replVertexLoop_exec (w := w)
    a_bd a_st a_en A R hbd hst hen hse hbs hbe
    (hadj.of_arrs_eq (ha5 A (by omega) (by omega) (by omega))
      (ha5 (A + 1) (by omega) (by omega) (by omega))
      (ha5 (A + 2) (by omega) (by omega) (by omega)))
    ((ha5 a_bd hbs hbe (by omega)).trans hbl) hsmall hblnd hblt
    ((ha5 (A + 3) (by omega) (by omega) (by omega)).trans hdel)
    ((ha5 (A + 9) (by omega) (by omega) (by omega)).trans hboundary)
    (by simp [s5]) (by simpa [s5, s4, s3, s2, s1] using hN)
    (by simp [s5, s4, s3, s2, s1, State.setArr_arrs, hse, show a_st ≠ A + 4 by omega])
    (by simp [s5, s4, s3, s2, State.setArr_arrs, show a_en ≠ A + 4 by omega])
    (by simp [IsBuf, s5, s4, s3]) hcap
    (by rw [ha5 (A + 2) (by omega) (by omega) (by omega)]; omega)
  let cnt := (flatUpTo L N).length
  let s7 := s6.setReg (R + 14) cnt
  let s8 := s7.setReg (R + 11) N
  have hex7 : Exec w (.assign (R + 14) (.reg (R + 4))) s6 s7 2 :=
    .assign (eval_reg hb6.2 (by omega))
  have hex8 : Exec w (.assign (R + 11) (.reg (R + 8))) s7 s8 2 :=
    .assign (eval_reg (by simpa [s7] using hN6) (by omega))
  obtain ⟨s9, t9, hex9, ht9, harr9, ha9, hr9⟩ := copyMinNProg_exec (w := w)
    (A + 4) a_ent (R + 11) (R + 12) (R + 14) (by omega) (by omega) (by omega) (by omega)
    (s := s8) (B := N) (n := cnt) (by simp [s8]) (by omega) (by omega)
    (by simp [s8, s7]) (by omega) (by simp [s8, s7, hb6.1, cnt, L])
  refine ⟨s9, _,
    .seq hex1 (.seq hex2 (.seq hex3 (.seq hex4 (.seq hex5 (.seq hex6 (.seq hex7 (.seq hex8 hex9))))))),
    by omega, ?_, ?_, ?_⟩
  · simpa [s8, s7] using (ha9 a_st hste).trans (show s8.arrs a_st = _ by simpa [s8, s7] using hst6)
  · simpa [s8, s7] using (ha9 a_en hene).trans (show s8.arrs a_en = _ by simpa [s8, s7] using hen6)
  · rw [harr9]
    simp only [s8, s7, State.setReg_arrs, hb6.1]
    rw [List.take_left' (show cnt = (flatUpTo L N).length from rfl)]
    exact map_min_of_le (fun x hx => (lt_of_mem_flatUpTo hfam x hx).le)

end GraphMinor.Compute.Crossing
