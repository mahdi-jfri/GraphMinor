module

public import GraphMinor.Compute.GM06CutComponents
public import GraphMinor.Compute.GM06BfsPath
import GraphMinor.Compute.TwoPathsSearchWalk

/-!
# Runtime single-component search for the cut graph

Section 9 of our proof of VI (5.7) (outlined in `GraphMinor/GM06/Alg57Algorithm.lean`) computes the
component reached from an inner cuff edge. Run the verified queue
search with all vertices free and its sole source read from the
current cuff endpoint. The parent invariant proves soundness and
the empty-queue invariant proves completeness. The program computes
its own initial labels and source list and returns the exact dense
component membership bits. Its graph input is only adjacency arrays.
-/

@[expose] public section
namespace GraphMinor.Compute
open TwoPaths SimpleGraph

/-- Exact dense component membership in a finite decidable graph. -/
def gm06ComponentBits {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (root : Fin n) : List ℕ :=
  List.ofFn (fun v => if G.Reachable root v then 1 else 0)

/-- For a completed all-free one-source queue search, membership in
the queue history is exactly reachability from that source. -/
theorem gm06Search_component_mem {n : ℕ} (G : SimpleGraph (Fin n))
    (root : Fin n) (s₀ sf : State) (items : List ℕ)
    (hs : SInv G (fun _ => 0) [root.val] s₀ items items.length sf) :
    ∀ v : Fin n, v.val ∈ items ↔ G.Reachable root v := by
  intro v
  constructor
  · intro hv
    obtain ⟨p, _, hp⟩ := hs.par
    obtain ⟨r, walk, _, hr, _, _, _⟩ := exists_walk_of_parentOK hp items.length v hv
      (List.idxOf_lt_length_of_mem hv)
    have heq : r = root := Fin.ext (by simpa only [List.mem_singleton] using hr)
    subst r
    exact walk.reachable
  · rintro ⟨p⟩
    exact hs.mem_of_walk (by simp) p (fun _ _ => rfl)

/-- The labels of a completed one-source search are exactly its
finite component bits. This includes the source itself. -/
theorem gm06Search_component_bits {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (root : Fin n) (s₀ sf : State) (items : List ℕ)
    (hs : SInv G (fun _ => 0) [root.val] s₀ items items.length sf) :
    sf.arrs 60 = gm06ComponentBits G root := by
  rw [hs.lab]
  unfold gm06ComponentBits
  congr 1
  funext v
  by_cases hr : G.Reachable root v
  · have hm := (gm06Search_component_mem G root s₀ sf items hs v).mpr hr
    simp only [hm, hr, ↓reduceIte]
  · have hm : v.val ∉ items := mt (gm06Search_component_mem G root s₀ sf items hs v).mp hr
    simp only [hm, hr, ↓reduceIte]

/-- Initialize all-free labels and the actual cuff-endpoint source,
then run the relocated full queue search. CSR arrays are 620--622,
vertex count is register 620, and the current root is register 644. -/
def gm06ComponentSearchProg : Cmd :=
  .seq (.alloc 630 (.reg 620))
    (.seq (.alloc 633 (.const 1))
      (.seq (.write 633 (.const 0) (.reg 644))
        (renameCmd gm06BfsRename (TwoPaths.searchProg 40 41 42))))

/-- The component program computes exact membership bits in linear
graph time. No allowed-set, initial labels or source array is supplied. -/
theorem gm06ComponentSearchProg_exec {w n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (lists : Fin n → List ℕ) (root : Fin n) (s : State)
    (hw : 4 < 2 ^ w) (hn : n < 2 ^ w)
    (hN : s.regs 620 = n) (hroot : s.regs 644 = root.val)
    (hadj : IsAdjList G 620 621 622 lists s) (hentries : (s.arrs 622).length < 2 ^ w) :
    ∃ sf t, Exec w gm06ComponentSearchProg s sf t ∧
      t ≤ 60 + 22 * n + 29 * totalAdjEntries lists ∧
      Keeps (List.range' 630 11) [630, 631, 632, 633] s sf ∧
      sf.arrs 630 = gm06ComponentBits G root := by
  have hw1 : 1 < 2 ^ w := by omega
  let s₀ := s.setArr 630 (List.replicate n 0)
  let s₁ := s₀.setArr 633 [0]
  let s₂ := s₁.writeArr 633 0 root.val
  have he₀ : Exec w (.alloc 630 (.reg 620)) s s₀ (1 + n) :=
    .alloc (GraphMinor.Compute.Crossing.eval_reg hN hn)
  have he₁ : Exec w (.alloc 633 (.const 1)) s₀ s₁ 2 :=
    .alloc (GraphMinor.Compute.Crossing.eval_const hw1)
  have he₂ : Exec w (.write 633 (.const 0) (.reg 644)) s₁ s₂ 3 :=
    .write (GraphMinor.Compute.Crossing.eval_const (Nat.two_pow_pos w))
      (GraphMinor.Compute.Crossing.eval_reg (by simpa [s₁, s₀] using hroot) (root.isLt.trans hn))
      (by simp [s₁])
  have hkInit : Keeps (List.range' 630 11) [630, 631, 632, 633] s s₂ :=
    (((Keeps.refl _ _ s).setArr (by simp) _).setArr (by simp) _).writeArr (by simp) _ _
  have hAdjInit := hadj.of_arrs_eq (hkInit.2 620 (by decide)) (hkInit.2 621 (by decide)) (hkInit.2 622 (by decide))
  let sr := renameState gm06BfsRename s₂
  have hAdjR : IsAdjList G 40 41 42 lists sr := by
    simpa [IsAdjList, IsListFamily, IsListAt, sr, renameState, gm06BfsRename] using hAdjInit
  obtain ⟨sm, tm, items, hem, htm, hs⟩ := TwoPaths.searchProg_exec G lists 40 41 42
    (by decide) (by decide) (by decide) (fun _ => 0) (fun _ => by decide) [root.val]
    (fun x hx => by
      have he : x = root.val := by simpa only [List.mem_singleton] using hx
      simpa only [he] using root.isLt) sr hAdjR
    (by simpa [sr, renameState, gm06BfsRename] using (hkInit.2 622 (by decide) ▸ hentries))
    (by simpa [sr, renameState, gm06BfsRename] using (hkInit.1 620 (by simp [List.mem_range'_1])).trans hN)
    hw hn (by simpa using hw1)
    (by simp [sr, renameState, gm06BfsRename, s₂, s₁, s₀, State.writeArr, List.ofFn_const, aLab])
    (by simp [sr, renameState, gm06BfsRename, s₂, s₁, State.writeArr, aSrc])
  have hinv : renameState gm06BfsRename sr = s₂ := by
    ext x <;> simp [sr, renameState, gm06BfsRename_involutive x]
  let sf := renameState gm06BfsRename sm
  have hef : Exec w (renameCmd gm06BfsRename (TwoPaths.searchProg 40 41 42)) s₂ sf tm := by
    rw [← hinv]
    exact exec_renameCmd gm06BfsRename_involutive hem
  have hkSearch : Keeps (List.range' 630 11) [630, 631, 632, 633] s₂ sf := by
    constructor
    · intro r hr
      have hnot : gm06BfsRename r < 60 ∨ 71 ≤ gm06BfsRename r := by
        simp only [List.mem_range'_1] at hr
        unfold gm06BfsRename
        split_ifs <;> omega
      change sm.regs (gm06BfsRename r) = s₂.regs r
      rw [hs.frame.1 _ hnot]
      exact congrArg s₂.regs (gm06BfsRename_involutive r)
    · intro a ha
      have hnot : gm06BfsRename a ≠ 60 ∧ gm06BfsRename a ≠ 61 ∧ gm06BfsRename a ≠ 62 := by
        simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at ha
        unfold gm06BfsRename
        split_ifs <;> omega
      change sm.arrs (gm06BfsRename a) = s₂.arrs a
      rw [hs.frame.2 _ hnot.1 hnot.2.1 hnot.2.2]
      exact congrArg s₂.arrs (gm06BfsRename_involutive a)
  refine ⟨sf, (1 + n) + (2 + (3 + tm)), .seq he₀ (.seq he₁ (.seq he₂ hef)), ?_,
    hkInit.trans hkSearch (fun _ h => h) (fun _ h => h), ?_⟩
  · simp only [List.length_singleton] at htm
    omega
  · exact gm06Search_component_bits G root sr sm items hs

end GraphMinor.Compute
