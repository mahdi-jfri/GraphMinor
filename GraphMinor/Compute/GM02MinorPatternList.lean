module

public import GraphMinor.Compute.GM02EdgeListInput
public import GraphMinor.GM02.TopologicalContainment
import GraphMinor.GM02.TopologicalPatternsNatEdges
import GraphMinor.Compute.GM02FiniteEdgeListPresentation

/-!
# Fixed edge-list patterns for the minor algorithm

Use the finite family proved in II (4.8), now on ordinary host edge
names. Number each fixed pattern once and keep its edge-list code.
The resulting fixed list tests minor containment by the isomorphic
topological-containment programs of (4.7).
-/

public section
namespace GraphMinor.Compute
open Graph Set GraphMinor.GM02 Classical

/-- The finite family of (4.8) has a fixed list of ordinary edge-list presentations. -/
theorem exists_gm02MinorPatternList {A B : Type*} (H : Graph A B)
    (hV : V(H).Finite) (hE : E(H).Finite) :
    ∃ ps : List GM02EdgeListInput, ∀ G : GM02EdgeListInput,
      IsIsoMinor H G.graph ↔ ∃ J ∈ ps, ∃ L : Graph ℕ ℕ,
        TopologicallyContains G.graph L ∧ Nonempty (Iso J.graph L) := by
  obtain ⟨F, hF, hp⟩ := exists_topologicalPatterns_nat_edges H hV hE
  choose code hCode using fun J : F => exists_gm02EdgeListPresentation J.val
    (hF J.val J.property).1 (hF J.val J.property).2
  let ps := F.attach.toList.map code
  refine ⟨ps, ?_⟩
  intro G
  have hpg := hp G.graph G.finite_vertices G.finite_edges
  constructor
  · intro hm
    obtain ⟨J, hJ, L, ht, ⟨ψ⟩⟩ := hpg.1 hm
    obtain ⟨φ⟩ := hCode ⟨J, hJ⟩
    refine ⟨code ⟨J, hJ⟩, List.mem_map.2 ⟨⟨J, hJ⟩, ?_, rfl⟩, L, ht, ⟨φ.symm.trans ψ⟩⟩
    exact Finset.mem_toList.2 (Finset.mem_attach _ _)
  · rintro ⟨J, hJ, L, ht, ⟨ψ⟩⟩
    obtain ⟨j, _, rfl⟩ := List.mem_map.1 hJ
    obtain ⟨φ⟩ := hCode j
    exact hpg.2 ⟨j.val, j.property, L, ht, ⟨φ.trans ψ⟩⟩

end GraphMinor.Compute
