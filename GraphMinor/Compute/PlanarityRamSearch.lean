module

public import GraphMinor.Compute.PlanarityRamRootsLoop

/-!
# Linear-time RAM depth-first search

Preparation counts incidences and allocates the search arenas once. The
root-loop theorem accounts for all scans and vertex completions together.
The functional root-scan equation then identifies the final arrays with
`depthFirstSearch`, whose final reversal is already represented by the
array's chronological completion order.
-/

@[expose] public section
namespace GraphMinor.Compute.PlanarityRam

open LRPlanarity

/-- The complete fixed DFS program computes `depthFirstSearch` in linear
time. Its only hypotheses are the input adjacency encoding and calling
convention, the entries-array word bound, and logarithmic word size. -/
theorem depthFirstSearchProg_refines (N : ℕ) (G : SimpleGraph (Fin N)) [DecidableRel G.Adj]
    (lists : Fin N → List ℕ) (w : ℕ) (s : State)
    (hw : wordSize 2 (G.edgeFinset.card + N + 1) ≤ w)
    (hadj : IsAdjList G 30 31 32 lists s) (hentries : (s.arrs 32).length < 2 ^ w)
    (hN : s.regs 30 = N) :
    ∃ search s' t,
      depthFirstSearch (List.ofFn lists).toArray = some search ∧
      Exec w depthFirstSearchProg s s' t ∧ t ≤ 800 * (G.edgeFinset.card + N + 1) ∧
      SearchAt N (totalAdjEntries lists) s' search ∧ SearchBounded N search ∧
      search.edges.size ≤ totalAdjEntries lists ∧ search.postorder.Nodup ∧
      search.postorder.length ≤ N ∧ (∀ v ∈ search.postorder, v < N) ∧ FramesAt N s' [] ∧
      s'.regs 30 = N ∧ s'.regs 36 = totalAdjEntries lists := by
  let M := totalAdjEntries lists
  have hMCard : M = 2 * G.edgeFinset.card := totalAdjEntries_eq_two_mul_card_edgeFinset hadj.2
  have hcap0 := preparation_word_bound (G.edgeFinset.card + N + 1) w hw
  have hcap : 2 * (N + M + 2) < 2 ^ w := by omega
  obtain ⟨s1, t1, hx1, ht1, h1, hf1, hM1, hr1, ha1⟩ :=
    prepareSearchProg_exec N G lists w s hw hadj hentries hN
  have hN1 : s1.regs 30 = N := by
    apply Eq.trans (hx1.regs_eq_of_not_mem_writtenRegs ?_) hN
    simp [prepareSearchProg, countEntriesProg, initializeSearchProg, allocateFields,
      searchFields, forUp, Cmd.writtenRegs]
  let s2 := s1.setReg 40 0
  have hN2 : s2.regs 30 = N := by simpa [s2] using hN1
  have hroot2 : s2.regs 40 = 0 := by simp [s2]
  have hDfs1 : DfsSearchAt N M s1 (initialSearch N) := h1
  have h2 : DfsSearchAt N M s2 (initialSearch N) := hDfs1.setReg 40 0 (by decide) (by decide)
  have hf2 : FramesAt N s2 [] := hf1.setReg 40 0 (by decide)
  have hb2 := SearchBounded.initial N
  have hs2 : FrameInvariant (List.ofFn lists).toArray (initialSearch N) [] := by
    simpa only [List.size_toArray, List.length_ofFn] using FrameInvariant.initial (List.ofFn lists).toArray
  have hbudget2 : (initialSearch N).edges.size +
      searchWork (List.ofFn lists).toArray 0 (initialSearch N) [] ≤ M := by
    rw [initial_searchWork]
    simp [initialSearch, M]
  have hwork2 : searchWork (List.ofFn lists).toArray 1 (initialSearch N) [] ≤ M + N := by
    rw [initial_searchWork]
    simp [M]
  have hadj1 := hadj.of_arrs_eq (ha1 30 (by decide)) (ha1 31 (by decide)) (ha1 32 (by decide))
  have hadj2 : IsAdjList G 30 31 32 lists s2 := hadj1.of_arrs_eq rfl rfl rfl
  have hentries2 : (s2.arrs 32).length < 2 ^ w := by
    change (s1.arrs 32).length < 2 ^ w
    rw [ha1 32 (by decide)]
    exact hentries
  have hx2 : Exec w (.assign 40 (.const 0)) s1 s2 2 :=
    Exec.assign (e := .const 0) (checkWord_of_lt (by omega))
  obtain ⟨result, s3, t3, hresult, hx3, ht3, hf3, h3, hb3, hs3, hwork3, hbudget3, hN3, hroot3⟩ :=
    searchRootsProg_refines 0 (initialSearch N) s2 (Nat.zero_le _) hN2 hroot2 hadj2 h2 hf2 hb2 hs2
      hbudget2 hwork2 hcap hentries2
  have hrootResult : searchRoots (List.ofFn lists).toArray (M + N + 1) (List.range N) (initialSearch N) =
      some result := by
    simpa only [Nat.sub_zero, ← List.range_eq_range'] using hresult
  have hsearch : depthFirstSearch (List.ofFn lists).toArray = some (reversePostorder result) := by
    rw [depthFirstSearch_eq_searchRoots, adjacency_fold_eq_total]
    simp only [List.size_toArray, List.length_ofFn]
    rw [hrootResult]
    rfl
  have ht3' : t3 ≤ 25 * N + 201 * (M + N) + 3 := by
    simp only [Nat.sub_zero, initial_searchWork, Nat.mul_one] at ht3
    change t3 ≤ 25 * N + 201 * ((M + N) - searchWork (List.ofFn lists).toArray 1 result []) + 3 at ht3
    omega
  have hM3 : s3.regs 36 = totalAdjEntries lists := by
    apply Eq.trans (hx3.regs_eq_of_not_mem_writtenRegs (r := 36) ?_)
      (show s2.regs 36 = totalAdjEntries lists by simpa [s2] using hM1)
    simp [forUp, searchRootProg, startRootProg, searchComponentProg, searchFrameStepProg,
      loadFrameProg, completeFrameProg, popFrameProg, appendPostorderProg, finishIncomingProg,
      finishEdgeProg, finishKeyProg, parentPairProg, insertPairProg, insertLowProg,
      scanNeighborProg, advanceFrameProg, visitedNeighborProg, backEdgeProg, treeChildProg,
      addEdgeProg, storeEdgeProg, discoverChildProg, pushFrameProg, Cmd.writtenRegs]
  have hpostNodup : result.postorder.Nodup := by simpa [ownedVertices] using hs3.2.1
  have hpostLength : result.postorder.length ≤ N := by
    simpa [ownedVertices] using hs3.capacity
  refine ⟨reversePostorder result, s3, t1 + (2 + t3), hsearch,
    Exec.seq hx1 (Exec.seq hx2 hx3), by omega, h3, ?_, ?_, ?_, ?_, ?_, hf3, hN3, hM3⟩
  · change SearchBounded N result
    exact hb3
  · exact Nat.le_trans (Nat.le_add_right _ _) hbudget3
  · simpa [reversePostorder] using hpostNodup
  · simpa [reversePostorder] using hpostLength
  · intro v hv
    have hh := hs3.2.2.1 v (by simpa [ownedVertices, reversePostorder] using hv)
    simpa only [List.size_toArray, List.length_ofFn] using hh

end GraphMinor.Compute.PlanarityRam
