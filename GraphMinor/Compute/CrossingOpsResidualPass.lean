module

public import GraphMinor.Compute.CrossingOpsResidualRebuild
public import GraphMinor.Compute.CrossingOpsBfsEncoded

/-!
# Preparing the next forest search

The residual pass reads the size, rebuilds the graph after removing the computed forest,
and copies the active marks. It keeps the old CSR arrays and parent words, which are
needed to decide later whether an original edge belongs to any selected forest.
-/

@[expose] public section

namespace GraphMinor.Compute.Crossing

open GraphMinor.Crossing

/-- Store the residual graph and its active marks at the next block of ten arrays. -/
def residualPassProg (A R : ℕ) : Cmd :=
  .seq (.assign (R + 8) (.len (A + 6)))
    (.seq (residualRebuildProg A (A + 10) R)
      (.seq (.assign (R + 11) (.const 1))
        (copyMinProg (A + 6) (A + 16) (R + 11) (R + 12) (R + 14))))

/-- The residual pass produces a valid input for the next BFS search and preserves
all arrays below its output block. -/
theorem residualPassProg_exec {w N : ℕ} (A R : ℕ) {G : SimpleGraph (Fin N)}
    (S : Finset (Fin N)) {lists : Fin N → List ℕ} {edges : List (Fin N × Fin N)} {s : State}
    (hadj : IsAdjList G A (A + 1) (A + 2) lists s)
    (hp : IsBfsParentsAt (A + 4) edges s)
    (hentries : (s.arrs (A + 2)).length = 2 * G.edgeSet.ncard)
    (hactive : s.arrs (A + 6) = List.ofFn (fun u : Fin N => if u ∈ S then 1 else 0))
    (hw : N + 2 * G.edgeSet.ncard + 2 < 2 ^ w) :
    ∃ s' t, Exec w (residualPassProg A R) s s' t ∧
      t ≤ 50 + 40 * N + 100 * G.edgeSet.ncard ∧
      IsAdjList (G \ bfsDiscoveryForest edges) (A + 10) (A + 11) (A + 12)
        (fun u => residualList lists edges u.val) s' ∧
      (s'.arrs (A + 12)).length = 2 * (G \ bfsDiscoveryForest edges).edgeSet.ncard ∧
      s'.arrs (A + 16) = List.ofFn (fun u : Fin N => if u ∈ S then 1 else 0) ∧
      (∀ a, a < A + 10 → s'.arrs a = s.arrs a) ∧
      (∀ r, r < R ∨ R + 15 ≤ r → s'.regs r = s.regs r) := by
  let s1 := s.setReg (R + 8) N
  have he1 : Exec w (.assign (R + 8) (.len (A + 6))) s s1 2 :=
    .assign (by simp [Expr.eval, checkWord, hactive, show N < 2 ^ w by omega])
  obtain ⟨s2, t2, he2, ht2, hadj2, hent2, ha2⟩ := residualRebuildProg_exec (w := w)
    A (A + 10) R (s := s1) (by omega) hadj hp hentries (by simp [s1]) hw
  have hal2 : s2.arrs (A + 6) = List.ofFn (fun u : Fin N => if u ∈ S then 1 else 0) :=
    (ha2 _ (by omega) (by omega) (by omega) (by omega)).trans hactive
  let s3 := s2.setReg (R + 11) 1
  have he3 : Exec w (.assign (R + 11) (.const 1)) s2 s3 2 := .assign (eval_const (by omega))
  obtain ⟨s4, t4, he4, ht4, harr4, ha4, hr4⟩ := copyMinProg_exec (w := w)
    (A + 6) (A + 16) (R + 11) (R + 12) (R + 14)
    (by omega) (by omega) (by omega) (by omega)
    (s := s3) (B := 1) (by simp [s3]) (by omega) (by omega) (by simp [s3, hal2]; omega)
  have hal4 : s4.arrs (A + 16) = List.ofFn (fun u : Fin N => if u ∈ S then 1 else 0) := by
    rw [harr4]
    simp only [s3, State.setReg_arrs, hal2, List.map_ofFn]
    congr 1
    funext u
    by_cases hu : u ∈ S <;> simp [hu]
  have hex := Exec.seq he1 (.seq he2 (.seq he3 he4))
  refine ⟨s4, _, hex, ?_, ?_, ?_, hal4, ?_, ?_⟩
  · simp only [s3, State.setReg_arrs, hal2, List.length_ofFn] at ht4
    omega
  · exact hadj2.of_arrs_eq (ha4 _ (by omega)) (ha4 _ (by omega)) (ha4 _ (by omega))
  · rw [ha4 _ (by omega)]; exact hent2
  · intro a ha
    exact (ha4 a (by omega)).trans (ha2 a (by omega) (by omega) (by omega) (by omega))
  · intro r hh
    have h0 : r ≠ R := by omega
    have h1 : r ≠ R + 1 := by omega
    have h2 : r ≠ R + 2 := by omega
    have h3 : r ≠ R + 3 := by omega
    have h4 : r ≠ R + 4 := by omega
    have h8 : r ≠ R + 8 := by omega
    have h11 : r ≠ R + 11 := by omega
    have h12 : r ≠ R + 12 := by omega
    have h14 : r ≠ R + 14 := by omega
    exact hex.regs_eq_of_not_mem_writtenRegs (by
      simp [residualPassProg, residualRebuildProg, residualVertexLoop, vertexLoopProg,
        filterListProg, forList, forUp, emitWhenProg, emitProg, copyMinNProg,
        copyMinProg, Cmd.writtenRegs, h0, h1, h2, h3, h4, h8, h11, h12, h14])

end GraphMinor.Compute.Crossing
