module

public import GraphMinor.Compute.GM02NumericTerminalPairs
public import GraphMinor.Compute.GM02ActiveTerminalList
public import GraphMinor.GM02.TerminationGraph

/-!
# The active terminal scan produces the canonical matching encoding

Every active original pattern position has one enumerated active edge,
and conversely. Thus its fixed numeric pair is exactly a prescribed
termination pair. The increasing pair orientation rules out swapping
its endpoints. Membership and strict pair order then identify the
active-position list with the canonical matching edge list.
-/

public section
namespace GraphMinor.Compute
open Graph Set GraphMinor.GM02 Classical

/-- Numeric prescribed pairs are precisely the fixed pairs of active original pattern positions. -/
theorem gm02FullPortTermination_mem_pairs (x : GM02TopologicalInput) (gflags hflags : List ℕ)
    (code K : ℕ) (hK : x.edges.length ≤ K) {k : ℕ}
    (edge : Fin k ≃ E(gm02ActiveGraph x.H hflags))
    (hvalid : gm02PortAssignmentValid x gflags hflags (gm02PortAssignmentOfCode x code))
    (p : Sym2 (Fin (gm02FullPortSize x K))) :
    p ∈ (gm02FullPortTermination x gflags hflags code K hK edge hvalid).pairs ↔
      ∃ f : Fin x.edges.length, hflags[f.val]? = some 1 ∧
        s((gm02PatternTerminalPair x K hK f).1, (gm02PatternTerminalPair x K hK f).2) = p := by
  rw [gm02FullPortTermination_pairs_indexed]
  constructor
  · intro hp
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.1 hp
    exact ⟨gm02ActivePatternIndex x hflags (edge i), gm02ActivePatternIndex_flag x hflags (edge i), rfl⟩
  · rintro ⟨f, hflag, hp⟩
    refine Finset.mem_image.2 ⟨edge.symm (gm02ActivePatternEdge x hflags f hflag), Finset.mem_univ _, ?_⟩
    rw [Equiv.apply_symm_apply, gm02ActivePatternIndex_edge]
    exact hp

/-- The active-position list has exactly the increasing adjacent pairs of the termination matching. -/
theorem gm02ActiveTerminalList_mem_pairGraph (x : GM02TopologicalInput) (gflags hflags : List ℕ)
    (code K : ℕ) (hK : x.edges.length ≤ K) {k : ℕ}
    (edge : Fin k ≃ E(gm02ActiveGraph x.H hflags))
    (hvalid : gm02PortAssignmentValid x gflags hflags (gm02PortAssignmentOfCode x code))
    (p : Fin (gm02FullPortSize x K) × Fin (gm02FullPortSize x K)) :
    p ∈ gm02ActiveTerminalList x hflags K hK ↔ p.1.val < p.2.val ∧
      (gm02FullPortTermination x gflags hflags code K hK edge hvalid).pairGraph.Adj p.1 p.2 := by
  rw [gm02ActiveTerminalList, List.mem_map]
  simp only [gm02ActivePatternPositions_mem]
  constructor
  · rintro ⟨f, hflag, rfl⟩
    refine ⟨gm02PatternTerminalPair_increasing x K hK f, ?_⟩
    apply (Termination.pairGraph_adj_iff _).2
    exact (gm02FullPortTermination_mem_pairs x gflags hflags code K hK edge hvalid _).2 ⟨f, hflag, rfl⟩
  · rintro ⟨hpinc, hpadj⟩
    obtain ⟨f, hflag, hp⟩ := (gm02FullPortTermination_mem_pairs x gflags hflags code K hK edge hvalid _).1
      ((Termination.pairGraph_adj_iff _).1 hpadj)
    rcases Sym2.eq_iff.1 hp with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
    · exact ⟨f, hflag, Prod.ext h₁ h₂⟩
    · have hinc := gm02PatternTerminalPair_increasing x K hK f
      have hv₁ := congrArg Fin.val h₁
      have hv₂ := congrArg Fin.val h₂
      omega

/-- Scanning active supplied positions gives exactly the canonical terminal matching edge list. -/
theorem gm02ActiveTerminalList_eq_edgeListOf (x : GM02TopologicalInput) (gflags hflags : List ℕ)
    (code K : ℕ) (hK : x.edges.length ≤ K) {k : ℕ}
    (edge : Fin k ≃ E(gm02ActiveGraph x.H hflags))
    (hvalid : gm02PortAssignmentValid x gflags hflags (gm02PortAssignmentOfCode x code)) :
    gm02ActiveTerminalList x hflags K hK =
      edgeListOf (gm02FullPortTermination x gflags hflags code K hK edge hvalid).pairGraph := by
  exact gm02EdgeListOf_eq_of_pairwise_rank _ _ (gm02ActiveTerminalList_pairwise_rank x hflags K hK)
    (gm02ActiveTerminalList_mem_pairGraph x gflags hflags code K hK edge hvalid)

end GraphMinor.Compute
