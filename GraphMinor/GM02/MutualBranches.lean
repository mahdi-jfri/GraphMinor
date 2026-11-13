module

public import GraphMinor.GM02.BranchRegions
import GraphMinor.GM10.TreeWidthBasic

/-!
# Two chosen branches face one another

Case 2 of II (2.5), page 312, chooses one branch at every tree node.
Choose the first edge into each branch. A finite tree has fewer edges
than vertices, so two choices give the same edge. Those two nodes are
its ends, and their chosen branches point toward each other.
-/

public section
namespace GraphMinor.GM02
open SimpleGraph Set Classical
universe w

/-- The edge-count argument in II (2.5), Case 2, page 312. For any choice
of a branch at each node of a finite tree, two adjacent nodes choose
branches containing one another. -/
theorem exists_mutual_branches {ι : Type w} [Fintype ι] {T : SimpleGraph ι}
    (hT : T.IsTree) (B : ∀ i, BranchAt T i) :
    ∃ j j', T.Adj j j' ∧ j' ∈ branchVertices (B j) ∧ j ∈ branchVertices (B j') := by
  choose f hfadj hfbranch using fun i => exists_adj_mem_branch hT i (B i)
  let g : ι → T.edgeSet := fun i => ⟨s(i, f i), (SimpleGraph.mem_edgeSet _).2 (hfadj i)⟩
  have hcard : Fintype.card T.edgeSet < Fintype.card ι := by
    have hc := hT.card_edgeFinset
    rw [SimpleGraph.edgeFinset_card] at hc
    omega
  have hpair : ∃ j j', j ≠ j' ∧ g j = g j' := by
    by_contra hn
    have hinj : Function.Injective g := by
      intro j j' heq
      by_contra hne
      exact hn ⟨j, j', hne, heq⟩
    have hc := Fintype.card_le_of_injective g hinj
    omega
  obtain ⟨j, j', hne, heq⟩ := hpair
  have hedge : s(j, f j) = s(j', f j') := congrArg Subtype.val heq
  rcases Sym2.eq_iff.1 hedge with ⟨h, _⟩ | ⟨h1, h2⟩
  · exact (hne h).elim
  · refine ⟨j, j', ?_, ?_, ?_⟩
    · rw [← h2]
      exact hfadj j
    · rw [← h2]
      exact hfbranch j
    · rw [h1]
      exact hfbranch j'

end GraphMinor.GM02
