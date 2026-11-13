module

public import GraphMinor.Compute.SpecsPlanarity
public import GraphMinor.LRPlanarity.Statements

/-!
# Assemble the conditional planarity test

Part V, Section 3 of `docs/planarity/planarity_test.tex` combines the search, constraint
solver, weak-alignment lemma and two geometric implications. This file checks that
those mathematical statements fit the fixed Word RAM calling convention. The six
inputs to the theorem are explicit proof obligations. The theorem does not close
any of them.
-/

public section
namespace GraphMinor.LRPlanarity

/-- Part V, Section 3: derive the cited Boolean planarity specification from
RAM execution, search correctness, the exact solver, weak alignment, geometric
sufficiency, and geometric necessity. Each of these six claims is a hypothesis. -/
theorem planarityTestStatement_of
    (hRam : Compute.LRPlanarityRamStatement)
    (hSearch : SearchStatement)
    (hSolver : SolverStatement)
    (hAlignment : WeakAlignmentStatement)
    (hSuff : SufficiencyStatement)
    (hNec : NecessityStatement) : Compute.PlanarityTestStatement := by
  obtain ⟨prog, C, c_w, hC, hc_w, hRun⟩ := hRam
  refine ⟨prog, C, c_w, hC, hc_w, ?_⟩
  intro N G inst lists w hw s hInput hLength hN
  obtain ⟨search, hSearchEq, hDFS⟩ := hSearch N G lists hInput.2
  have hSolve := hSolver N G lists search hInput.2 hSearchEq
  have hCorrect : lrTest lists = true ↔ Nonempty (HP25.PlaneEmbedding G Set.univ) := by
    constructor
    · intro hAccept
      obtain ⟨color, hFork, hAligned⟩ := hSolve.mp hAccept
      exact hSuff N G (search.forest N) color hDFS hFork hAligned
    · intro hPlane
      obtain ⟨color, hFork, hAligned⟩ :=
        (hAlignment N G (search.forest N) hDFS).mp
          (hNec N G (search.forest N) hDFS hPlane)
      exact hSolve.mpr ⟨color, hFork, hAligned⟩
  obtain ⟨s', t, hExec, hTime, hRegs, hArrs, hOut⟩ :=
    hRun N G lists w hw s hInput hLength hN
  refine ⟨s', t, hExec, hTime, hRegs, hArrs, ?_⟩
  cases hb : lrTest lists with
  | false =>
    refine Or.inr ⟨?_, ?_⟩
    · simpa only [hb, Bool.toNat_false] using hOut
    · exact ⟨fun drawing => by
        have h := hCorrect.mpr ⟨drawing⟩
        simp only [hb, Bool.false_eq_true] at h⟩
  | true =>
    exact Or.inl ⟨by simpa only [hb, Bool.toNat_true] using hOut, hCorrect.mp hb⟩

end GraphMinor.LRPlanarity
