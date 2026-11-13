module

public import GraphMinor.Compute.CrossingOpsSubgraphLoop

/-!
# Allocating and rebuilding an encoded subgraph

The command allocates new offsets and an old-size entries buffer, filters all lists,
and copies the used prefix into a packed entries array. Its time is linear when the
read-only edge test has fixed cost.
-/

@[expose] public section

namespace GraphMinor.Compute.Crossing

/-- Allocate and pack a subgraph using a read-only edge test. Register `R+8` holds `N`. -/
def subgraphRebuildProg (a_s a_e a_ent B R : ℕ) (test : Expr) : Cmd :=
  .seq (.alloc B (.reg (R + 8)))
    (.seq (.alloc (B + 1) (.reg (R + 8)))
      (.seq (.alloc (B + 3) (.len a_ent))
        (.seq (.assign (R + 4) (.const 0))
          (.seq (.assign R (.const 0))
            (.seq (subgraphVertexLoop a_s a_e a_ent B R test)
              (.seq (.assign (R + 14) (.reg (R + 4)))
                (.seq (.assign (R + 11) (.reg (R + 8)))
                  (copyMinNProg (B + 3) (B + 2) (R + 11) (R + 12) (R + 14)))))))))

/-- A read-only test with the specified adjacency values builds an exact CSR encoding
of the subgraph. The test is verified separately from the storage and loop mechanics. -/
theorem subgraphRebuildProg_exec {w N : ℕ} (a_s a_e a_ent B R : ℕ) (test : Expr)
    {G H : SimpleGraph (Fin N)} [DecidableRel H.Adj] {lists : Fin N → List ℕ} {s : State}
    (hs : a_s < B) (he : a_e < B) (hent : a_ent < B)
    (hadj : IsAdjList G a_s a_e a_ent lists s) (hHG : H ≤ G)
    (hentries : (s.arrs a_ent).length = 2 * G.edgeSet.ncard)
    (hN : s.regs (R + 8) = N) (hw : N + 4 * G.edgeSet.ncard + 2 < 2 ^ w)
    (htest : ∀ z (u v : Fin N), (∀ a, a < B → z.arrs a = s.arrs a) →
      z.regs (R + 15) = s.regs (R + 15) → z.regs (R + 16) = s.regs (R + 16) →
      z.regs R = u.val → z.regs (R + 3) = v.val → G.Adj u v →
      test.eval w z = some (if H.Adj u v then 1 else 0)) :
    ∃ s' t, Exec w (subgraphRebuildProg a_s a_e a_ent B R test) s s' t ∧
      t ≤ 30 + 24 * N + (66 + 2 * test.cost) * G.edgeSet.ncard ∧
      IsAdjList H B (B + 1) (B + 2) (fun u => graphFilterList lists H u.val) s' ∧
      (s'.arrs (B + 2)).length = 2 * H.edgeSet.ncard ∧
      (∀ a, a < B → s'.arrs a = s.arrs a) ∧
      s'.regs (R + 15) = s.regs (R + 15) ∧ s'.regs (R + 16) = s.regs (R + 16) := by
  let L := graphFilterList lists H
  let cap := (s.arrs a_ent).length
  have hcapEq : cap = 2 * G.edgeSet.ncard := hentries
  have hcap : (flatUpTo L N).length ≤ cap := by
    simpa only [hcapEq] using length_flatUpTo_graphFilterList_le (H := H) hadj.2
  have hfam := isAdjListFamily_graphFilterList hadj.2 hHG
  let s1 := s.setArr B (List.replicate N 0)
  let s2 := s1.setArr (B + 1) (List.replicate N 0)
  let s3 := s2.setArr (B + 3) (List.replicate cap 0)
  let s4 := s3.setReg (R + 4) 0
  let s5 := s4.setReg R 0
  have he1 : Exec w (.alloc B (.reg (R + 8))) s s1 (1 + N) := .alloc (eval_reg hN (by omega))
  have he2 : Exec w (.alloc (B + 1) (.reg (R + 8))) s1 s2 (1 + N) :=
    .alloc (eval_reg (by simpa [s1] using hN) (by omega))
  have ha5 : ∀ a, a < B → s5.arrs a = s.arrs a := by
    intro a hh
    simp [s5, s4, s3, s2, s1, State.setArr_arrs, show a ≠ B by omega,
      show a ≠ B + 1 by omega, show a ≠ B + 3 by omega]
  have he3 : Exec w (.alloc (B + 3) (.len a_ent)) s2 s3 (1 + cap) :=
    .alloc (eval_len (show s2.arrs a_ent = s.arrs a_ent from by
      simp [s2, s1, State.setArr_arrs, show a_ent ≠ B by omega, show a_ent ≠ B + 1 by omega]) (by omega))
  have he4 : Exec w (.assign (R + 4) (.const 0)) s3 s4 2 := .assign (eval_const (by omega))
  have he5 : Exec w (.assign R (.const 0)) s4 s5 2 := .assign (eval_const (by omega))
  obtain ⟨s6, t6, he6, ht6, hb6, hst6, hen6, hN6, ha6, h156, h166⟩ :=
    subgraphVertexLoop_exec (w := w) a_s a_e a_ent B R test hs he hent
      (hadj.of_arrs_eq (ha5 _ hs) (ha5 _ he) (ha5 _ hent)) hHG
      (by simp [s5]) (by simpa [s5, s4, s3, s2, s1] using hN)
      (by simp [s5, s4, s3, s2, s1, State.setArr_arrs, show B ≠ B + 1 by omega,
        show B ≠ B + 3 by omega])
      (by simp [s5, s4, s3, s2, State.setArr_arrs, show B + 1 ≠ B + 3 by omega])
      (by simp [IsBuf, s5, s4, s3]) hcap (by rw [ha5 _ hent]; omega)
      (fun z u v ha h15 h16 hxr hyr had => htest z u v
        (fun a hh => (ha a hh).trans (ha5 a hh))
        (h15.trans (by simp [s5, s4, s3, s2, s1]))
        (h16.trans (by simp [s5, s4, s3, s2, s1])) hxr hyr had)
  let cnt := (flatUpTo L N).length
  let s7 := s6.setReg (R + 14) cnt
  let s8 := s7.setReg (R + 11) N
  have he7 : Exec w (.assign (R + 14) (.reg (R + 4))) s6 s7 2 := .assign (eval_reg hb6.2 (by omega))
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
  have hex := Exec.seq he1 (.seq he2 (.seq he3 (.seq he4 (.seq he5 (.seq he6 (.seq he7 (.seq he8 he9)))))))
  have hcost : (17 + test.cost) * (2 * G.edgeSet.ncard) + 32 * G.edgeSet.ncard =
      (66 + 2 * test.cost) * G.edgeSet.ncard := by ring
  refine ⟨s9, _, hex, by omega, ⟨isListFamily_flatUpTo hst9 hen9 hent9, hfam⟩, ?_, ?_, ?_, ?_⟩
  · rw [hent9]; exact length_flatUpTo_eq hfam
  · intro a hh
    exact (ha9 a (by omega)).trans ((ha6 a hh).trans (ha5 a hh))
  · exact (hr9 _ (by omega)).trans (by simpa [s8, s7, s5, s4, s3, s2, s1] using h156)
  · exact (hr9 _ (by omega)).trans (by simpa [s8, s7, s5, s4, s3, s2, s1] using h166)

end GraphMinor.Compute.Crossing
