module

public import GraphMinor.Compute.GM06Alg34VertexComponents

/-!
# Detecting a division block across components

A block meets two components exactly when it contains two labels that
are not reachable from each other. Scan the supplied block lists for
such a pair. The rejection proof applies VI (3.3)(iii) to the two
components through those labels.
-/

@[expose] public section
namespace GraphMinor.Compute.GM06DrawingData

open Set Surface GM06

/-- Test whether one supplied block meets distinct graph components,
as in Graph Minors VI (3.3)(iii), page 121. -/
def isSplitBlock (x : GM06DrawingData) (L : List (Fin x.n)) : Bool :=
  L.any fun a => L.any fun b => decide (¬ x.vertexGraph.Reachable a b)

/-- Test the supplied division for a block meeting two components. -/
def hasSplitBlock (x : GM06DrawingData) : Bool := x.division.any x.isSplitBlock

/-- A successful block test supplies two unreachable labels of that block. -/
theorem isSplitBlock_iff (x : GM06DrawingData) (L : List (Fin x.n)) :
    x.isSplitBlock L = true ↔
      ∃ a ∈ L, ∃ b ∈ L, ¬ x.vertexGraph.Reachable a b := by
  simp only [isSplitBlock, List.any_eq_true, decide_eq_true_eq]

/-- A successful division test supplies its block and two unreachable labels. -/
theorem hasSplitBlock_iff (x : GM06DrawingData) :
    x.hasSplitBlock = true ↔
      ∃ L ∈ x.division, ∃ a ∈ L, ∃ b ∈ L, ¬ x.vertexGraph.Reachable a b := by
  simp only [hasSplitBlock, List.any_eq_true, x.isSplitBlock_iff]

/-- The rejection test is sound by Graph Minors VI (3.3)(iii), applied
to the components through the two supplied unreachable labels. -/
theorem not_feasible_of_hasSplitBlock (x : GM06DrawingData)
    (hs : x.hasSplitBlock = true) : ¬ IsFeasible x.graph x.divisionSet := by
  obtain ⟨L, hL, a, ha, b, hb, hab⟩ := (x.hasSplitBlock_iff).mp hs
  have hCa := isGraphComponent_compOf (show a ∈ x.graph.vertexSet from trivial)
  have hCb := isGraphComponent_compOf (show b ∈ x.graph.vertexSet from trivial)
  have hne : compOf x.graph a ≠ compOf x.graph b := by
    intro heq
    have hmem := self_mem_reachSet (show b ∈ x.graph.vertexSet from trivial)
    change b ∈ (compOf x.graph b).vertexSet at hmem
    rw [← heq] at hmem
    exact hab ((x.vertexGraph_reachable_iff a b).mpr hmem.2)
  exact theorem_3_3_iii x.graph x.divisionSet (block L)
    (compOf x.graph a) (compOf x.graph b) ⟨L, hL, rfl⟩ hCa hCb hne
    ⟨a, ha, self_mem_reachSet trivial⟩ ⟨b, hb, self_mem_reachSet trivial⟩

/-- For a nonempty block, testing reachability from its first label
suffices to detect every pair lying in different components. -/
theorem isSplitBlock_cons (x : GM06DrawingData) (a : Fin x.n)
    (L : List (Fin x.n)) :
    x.isSplitBlock (a :: L) = !L.all (fun b => decide (x.vertexGraph.Reachable a b)) := by
  have heq : x.isSplitBlock (a :: L) = true ↔
      ∃ b ∈ L, ¬ x.vertexGraph.Reachable a b := by
    rw [x.isSplitBlock_iff]
    constructor
    · rintro ⟨b, hb, c, hc, hbc⟩
      by_contra hn
      have hall : ∀ b ∈ a :: L, x.vertexGraph.Reachable a b := by
        intro b hb
        rcases List.mem_cons.mp hb with rfl | hb
        · exact .refl _
        · exact Classical.byContradiction (fun h => hn ⟨b, hb, h⟩)
      exact hbc ((hall b hb).symm.trans (hall c hc))
    · rintro ⟨b, hb, hab⟩
      exact ⟨a, List.mem_cons_self, b, List.mem_cons_of_mem a hb, hab⟩
  apply Bool.eq_iff_iff.mpr
  rw [heq]
  simp only [Bool.not_eq_true', List.all_eq_false, decide_eq_true_eq]

end GraphMinor.Compute.GM06DrawingData
