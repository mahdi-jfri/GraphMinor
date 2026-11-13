module

public import GraphMinor.Compute.PlanarityRamKeep
import GraphMinor.Compute.PlanarityRamWord
public import GraphMinor.Compute.SpecsPlanarity

/-!
# The Word RAM left-right test from its solver phase

The fixed program counts adjacency entries, performs the explicit-frame
DFS, builds the global bucket order, allocates the solver arenas, and
calls the solver. Search and sorting are proved here. The solver phase is
the sole hypothesis. The logarithmic word constant absorbs its fixed
word bound, and the handshaking identity gives linear time in graph size.
-/

@[expose] public section
namespace GraphMinor.Compute

open PlanarityRam LRPlanarity

/-- The phases of Part V run once in their prescribed order. -/
def PlanarityRam.testProg (solver : Cmd) : Cmd :=
  .seq depthFirstSearchProg
    (.seq bucketSortProg (.seq (allocateFields solverFields) solver))

private theorem assembly_time (N M E C t1 t2 t3 t4 : ℕ) (hM : M = 2 * E)
    (h1 : t1 ≤ 800 * (E + N + 1)) (h2 : t2 ≤ 150 * (N + M + 1))
    (h3 : t3 ≤ 118 * (N + M + 1)) (h4 : t4 ≤ C * (N + M + 1)) :
    t1 + (t2 + (t3 + t4)) ≤ (1337 + 2 * C) * (E + N + 1) := by
  have hsize : N + M + 1 ≤ 2 * (E + N + 1) := by omega
  have hC := Nat.mul_le_mul_left C hsize
  have h4' : t4 ≤ 2 * (C * (E + N + 1)) := by
    calc
      t4 ≤ C * (2 * (E + N + 1)) := h4.trans hC
      _ = 2 * (C * (E + N + 1)) := by rw [← Nat.mul_assoc, Nat.mul_comm C 2, Nat.mul_assoc]
  simp only [Nat.add_mul, Nat.mul_assoc]
  omega

/-- Part V of the planarity note: the complete fixed RAM program computes
`lrTest` in linear time, assuming exactly the separately specified solver
phase. Search, bucket order, allocation, word bounds, and preservation of
the protected input fields are all proved in the preceding modules. -/
theorem lrPlanarityRamStatement_of (hSolve : PlanarityRamSolveClaim) : LRPlanarityRamStatement := by
  obtain ⟨solver, C, K, hsolver⟩ := hSolve
  refine ⟨testProg solver, 1337 + 2 * C, 2 * K + 6, by omega, by omega, ?_⟩
  intro N G inst lists w hw s hadj hentries hN
  let M := totalAdjEntries lists
  have hM : M = 2 * G.edgeFinset.card := totalAdjEntries_eq_two_mul_card_edgeFinset hadj.2
  obtain ⟨hwordDFS, hword, hwordSolver⟩ := assembly_word_bounds K G.edgeFinset.card N M w hM hw
  obtain ⟨search, s1, t1, hsearch, hx1, ht1, hs1, hb, hm, hpost, hpostlen, hpostvalid,
    hframes, hN1, hM1⟩ := depthFirstSearchProg_refines N G lists w s hwordDFS hadj hentries hN
  obtain ⟨s2, t2, hx2, ht2, hs2, hout⟩ := bucketSortProg_refines search s1 hs1 hb hm hN1 hM1 hword
  have hheaders := bucketSortProg_headers hx2
  obtain ⟨hx3, ht3⟩ := allocateSolver_exec N M w s2 (hheaders.1.trans hN1) (hheaders.2.trans hM1) hword
  let s3 := allocatedState N M solverFields s2
  have hs3 : SearchAt N M s3 search := hs2.allocate_solver
  have hout3 : OutgoingAt N s3 (bucketOrder N search.edges) := hout.allocate_solver
  obtain ⟨s4, t4, hx4, ht4, hr4, ha4, hresult⟩ :=
    hsolver N M w search s3 hwordSolver hs3 hb hpost hpostvalid hout3 (allocatedSolver_arenasAt N M s2)
  have hp1 := depthFirstSearchProg_preserves hx1
  have hp2 := bucketSortProg_preserves hx2
  have hp3 := allocatedState_preserves N M solverFields s2
  refine ⟨s4, t1 + (t2 + (allocationTime N M solverFields + t4)),
    Exec.seq hx1 (Exec.seq hx2 (Exec.seq hx3 hx4)),
    assembly_time N M G.edgeFinset.card C _ _ _ _ hM ht1 ht2 ht3 ht4, ?_, ?_, ?_⟩
  · intro r hr
    exact (hr4 r hr).trans ((hp3.1 r).trans ((hp2.1 r hr).trans (hp1.1 r hr)))
  · intro a ha
    exact (ha4 a ha).trans ((hp3.2 a ha).trans ((hp2.2 a ha).trans (hp1.2 a ha)))
  · simpa only [lrTest, hsearch] using hresult

end GraphMinor.Compute
