module

public import GraphMinor.GM06.Defs
import GraphMinor.GM11.Walks

/-!
# A walk avoiding a vertex lies in a connected punctured set

Join the closures of successive drawing edges along a walk. Each
closure is connected and meets the next piece at their common end.
If the support avoids a fixed drawing vertex, no edge closure can
contain that vertex, since its only drawing vertices are its ends.
This turns the cut-disc walk construction into the connected subsets
needed in the one-path proof of VI (5.1), page 129.
-/

public section
namespace GraphMinor.GM06
open Set Topology GraphMinor.Surface
universe u

/-- A graph walk avoiding a drawing vertex joins its ends in a
connected subset of the drawing with that vertex removed. -/
theorem exists_connected_subset_of_walk_avoiding_vertex
    {S : Type u} [TopologicalSpace S] [T2Space S] {F : Drawing S}
    {s : S} (hs : s ∈ F.V) {a b : S} (W : GraphWalk F.toGraph a b)
    (havoid : ∀ z ∈ W.support, z ≠ s) :
    ∃ Y ⊆ F.U \ {s}, a ∈ Y ∧ b ∈ Y ∧ IsConnected Y := by
  revert havoid
  induction W with
  | nil ha =>
    intro hn
    refine ⟨{_}, ?_, rfl, rfl, isConnected_singleton⟩
    intro z hz
    have hza := mem_singleton_iff.mp hz
    subst z
    exact ⟨F.V_subset_U ha, hn _ (List.mem_singleton_self _)⟩
  | @cons a v b e hl W ih =>
    intro hn
    obtain ⟨Y, hY, hvY, hbY, hcY⟩ := ih (fun z hz => hn z (List.mem_cons_of_mem a hz))
    have han : a ≠ s := hn a List.mem_cons_self
    have hvn : v ≠ s := hn v (List.mem_cons_of_mem a W.start_mem_support)
    have haE : a ∈ closure e :=
      (show a ∈ closure e ∩ F.V from hl.2.2.2.symm ▸ mem_insert _ {v}).1
    have hvE : v ∈ closure e :=
      (show v ∈ closure e ∩ F.V from hl.2.2.2.symm ▸ mem_insert_of_mem a rfl).1
    have heX : closure e ⊆ F.U \ {s} := by
      intro z hz
      refine ⟨F.closure_subset_U hl.1 hz, ?_⟩
      intro hzs
      have hsE : s ∈ closure e ∩ F.V := ⟨(mem_singleton_iff.mp hzs) ▸ hz, hs⟩
      rw [hl.2.2.2] at hsE
      rcases hsE with hsa | hsv
      · exact han hsa.symm
      · exact hvn (mem_singleton_iff.mp hsv).symm
    have hcE : IsConnected (closure e) := hl.1.2.2.1.isConnected.closure
    refine ⟨closure e ∪ Y, union_subset heX hY, Or.inl haE, Or.inr hbY, ?_⟩
    exact hcE.union ⟨v, hvE, hvY⟩ hcY

end GraphMinor.GM06
