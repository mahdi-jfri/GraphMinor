module

public import GraphMinor.GM06.Defs
import GraphMinor.GM06.Section4
import GraphMinor.GM06.Section4BothCuffs
import GraphMinor.GM06.Section4MinimumBase
import GraphMinor.GM06.Section4EmptyBase

/-!
# Graph Minors VI (4.2), claim (2)

If every component meets both cuffs, each is interval-based on both.
Otherwise choose a component meeting only one cuff and use the minimum
interval argument to obtain a cuff base. Excluding Reduction 1 gives
at least two vertices there, so the chosen component is bad. Its base
on the missed cuff is empty. These are the two cases of the paper's
proof on page 126.
-/

public section

namespace GraphMinor.GM06

open Set GraphMinor.Surface

private theorem cylinderCuffs_disjoint : Disjoint cylinderCuff1 cylinderCuff2 := by
  refine disjoint_left.mpr ?_
  intro x hx1 hx2
  change x.1.1 = 1 at hx1
  change x.1.1 = 2 at hx2
  linarith only [hx1, hx2]

/-- Graph Minors VI (4.2), claim (2), page 126:
"If some component of $H$ is bad, there is a bad component of $H$ which is interval-based on both cuffs of $\Sigma$."
The hypotheses are the forest setting and the exclusion of Reduction 1
used at the start of the proof of (4.2). -/
theorem lemma_4_2_claim_2
    {G H : Drawing ClosedCylinder} (hH : H.IsProper)
    (hforest : IsGraphForest H.toGraph)
    (hbd : H.V ∩ bd ClosedCylinder = G.V ∩ bd ClosedCylinder)
    (hno : ¬ Section4Reduction1Applies G H)
    (hbad : ∃ K : Graph ClosedCylinder (Set ClosedCylinder),
      IsGraphComponent K H.toGraph ∧ IsBadComponent K) :
    ∃ K : Graph ClosedCylinder (Set ClosedCylinder), IsGraphComponent K H.toGraph ∧
      IsBadComponent K ∧ ∀ C ∈ cuffs ClosedCylinder, IsIntervalBasedOn H K C := by
  classical
  by_cases hall : ∀ K : Graph ClosedCylinder (Set ClosedCylinder), IsGraphComponent K H.toGraph →
      (Graph.vertexSet K ∩ cylinderCuff1).Nonempty ∧
      (Graph.vertexSet K ∩ cylinderCuff2).Nonempty
  · obtain ⟨K, hK, hbadK⟩ := hbad
    exact ⟨K, hK, hbadK, fun C hC =>
      isIntervalBasedOn_of_all_components_meet_both_cuffs hforest hall hK hC⟩
  · obtain ⟨K, hcounter⟩ := not_forall.mp hall
    obtain ⟨hK, hmiss⟩ := not_imp.mp hcounter
    have hone : ∃ C ∈ cuffs ClosedCylinder, Graph.vertexSet K ∩ bd ClosedCylinder ⊆ C := by
      by_cases h1 : (Graph.vertexSet K ∩ cylinderCuff1).Nonempty
      · have h2 : ¬ (Graph.vertexSet K ∩ cylinderCuff2).Nonempty := fun h2 => hmiss ⟨h1, h2⟩
        refine ⟨cylinderCuff1, ?_, ?_⟩
        · rw [cuffs_closedCylinder]; exact Or.inl rfl
        · intro x hx
          have hxb : x ∈ cylinderCuff1 ∪ cylinderCuff2 := bd_closedCylinder ▸ hx.2
          rcases hxb with hx1 | hx2
          · exact hx1
          · exact (h2 ⟨x, hx.1, hx2⟩).elim
      · refine ⟨cylinderCuff2, ?_, ?_⟩
        · rw [cuffs_closedCylinder]; exact Or.inr rfl
        · intro x hx
          have hxb : x ∈ cylinderCuff1 ∪ cylinderCuff2 := bd_closedCylinder ▸ hx.2
          rcases hxb with hx1 | hx2
          · exact (h1 ⟨x, hx.1, hx1⟩).elim
          · exact hx2
    obtain ⟨C, hC, hKC⟩ := hone
    obtain ⟨L, A, hbase, hLC, hcard⟩ := exists_cuffBase_of_component_on_one_cuff
      hH hforest hbd hno hC ⟨K, hK, hKC⟩
    have hL : IsGraphComponent L H.toGraph := hbase.2.1
    have hbadL : IsBadComponent L := ⟨C, hC, (by decide : 1 < 2).trans_le hcard⟩
    refine ⟨L, hL, hbadL, ?_⟩
    intro D hD
    by_cases hDC : D = C
    · subst D
      exact ⟨A, hbase⟩
    · have hCcases : C = cylinderCuff1 ∨ C = cylinderCuff2 := by
        rw [cuffs_closedCylinder] at hC; exact hC
      have hDcases : D = cylinderCuff1 ∨ D = cylinderCuff2 := by
        rw [cuffs_closedCylinder] at hD; exact hD
      have hCD : Disjoint C D := by
        rcases hCcases with rfl | rfl <;> rcases hDcases with rfl | rfl
        · exact (hDC rfl).elim
        · exact cylinderCuffs_disjoint
        · exact cylinderCuffs_disjoint.symm
        · exact (hDC rfl).elim
      have hDbd : D ⊆ bd ClosedCylinder := by
        obtain ⟨o, _, rfl⟩ := hD
        exact connectedComponentIn_subset _ o
      have hLD : Disjoint (Graph.vertexSet L) D := by
        refine disjoint_left.mpr ?_
        intro x hxL hxD
        exact disjoint_left.mp hCD (hLC ⟨hxL, hDbd hxD⟩) hxD
      exact isIntervalBasedOn_of_component_disjoint_cuff hL hD hLD

end GraphMinor.GM06
