module

public import GraphMinor.Compute.CrossingOpsLocateLoop
public import GraphMinor.Compute.CrossingOpsBoundaryMarks
public import GraphMinor.Compute.CrossingOpsEdgePrefix

/-!
# Selecting a prescribed prefix of original edges

The command locates the final chosen edge row, marks its chosen neighbours, and saves
the row index for later membership tests. The selected edges form the prefix set of
Section 7.2, represented by one index and a mark array.
-/

@[expose] public section

namespace GraphMinor.Compute.Crossing

/-- Choose the edge quota in `R+5`. The old size is in `R+8`; save the cutoff in `R+15`. -/
def selectEdgesProg (a_s a_e a_ent B R : ℕ) : Cmd :=
  .seq (.assign R (.const 0))
    (.seq (locateEdgeRowLoop a_s a_e a_ent R)
      (.seq (boundaryMarksProg a_s a_e a_ent B R) (.assign (R + 15) (.reg R))))

/-- A positive feasible quota is selected in linear time. The saved cutoff and marks
represent exactly the final row of the prefix, and the prefix has the required cardinality. -/
theorem selectEdgesProg_exec {w N : ℕ} (a_s a_e a_ent B R : ℕ)
    {G : SimpleGraph (Fin N)} {lists : Fin N → List ℕ} {s : State} {k : ℕ}
    (hs : a_s < B) (he : a_e < B) (hent : a_ent < B)
    (hadj : IsAdjList G a_s a_e a_ent lists s) (hNpos : 0 < N)
    (hN : s.regs (R + 8) = N) (hk : s.regs (R + 5) = k)
    (hkpos : 0 < k) (hkbound : k ≤ G.edgeSet.ncard)
    (hw : N + (s.arrs a_ent).length + k + 2 < 2 ^ w) :
    ∃ (s' : State) (t : ℕ) (cut : Fin N) (q : ℕ),
      Exec w (selectEdgesProg a_s a_e a_ent B R) s s' t ∧ t ≤ 100 * (N + G.edgeSet.ncard + 1) ∧
      s'.regs (R + 15) = cut.val ∧ s'.arrs (B + 2) =
        setAt (List.replicate N 0) (edgeBoundaryList lists cut q) 1 ∧
      (edgeRowsBefore lists cut.val).length + q = k ∧ q ≤ (edgeRow lists cut).length ∧
      edgePrefixSet lists k ⊆ G.edgeSet ∧ (edgePrefixSet lists k).Finite ∧
      (edgePrefixSet lists k).ncard = k ∧
      (∀ a, a < B → s'.arrs a = s.arrs a) := by
  let s0 := s.setReg R 0
  have he0 : Exec w (.assign R (.const 0)) s s0 2 := .assign (eval_const (by omega))
  obtain ⟨s1, t1, cut, q, he1, ht1, hcut1, hq1, h61, htarget, hrow, ha1, hr1⟩ :=
    locateEdgeRowLoop_exec (w := w) a_s a_e a_ent R (s := s0) hadj hNpos (by simp [s0])
      (by simpa [s0] using hk) hkpos (by simp [edgeRowsBefore]) hkbound hw
  have hN1 : s1.regs (R + 8) = N :=
    (hr1 _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)).trans
      (by simpa [s0] using hN)
  have hadj1 := hadj.of_arrs_eq (ha1 a_s) (ha1 a_e) (ha1 a_ent)
  obtain ⟨st, en, hl⟩ := hadj1.1.2.2 cut
  obtain ⟨s2, t2, he2, ht2, hm2, hcut2, ha2⟩ := boundaryMarksProg_exec (w := w)
    a_s a_e a_ent B R hs he hent hl hcut1 cut.isLt hN1 h61
    (by simpa only [edgeRow_length hadj.2 cut] using hrow)
    (hadj.2 cut).2.2.1 (hadj.2 cut).1 (by rw [ha1 a_ent]; exact (by dsimp [s0]; omega))
  let s3 := s2.setReg (R + 15) cut.val
  have he3 : Exec w (.assign (R + 15) (.reg R)) s2 s3 2 :=
    .assign (eval_reg hcut2 (by have := cut.isLt; omega))
  have hspec := edgePrefixSet_spec hadj.2 k hkbound
  refine ⟨s3, _, cut, q, .seq he0 (.seq he1 (.seq he2 he3)), ?_, by simp [s3], hm2,
    htarget, hrow, hspec.1, hspec.2.1, hspec.2.2, ?_⟩
  · simp only [flatUpTo_zero, List.length_nil, Nat.mul_zero, Nat.add_zero, Nat.sub_zero] at ht1
    omega
  · intro a hh
    exact (ha2 a hh).trans (ha1 a)

end GraphMinor.Compute.Crossing
