module

public import GraphMinor.Compute.GM02FilterSide
public import GraphMinor.GM02.FeasibilityVertices
public import Mathlib.Combinatorics.Graph.Delete

/-!
# Graph meaning of the recursive edge-filter output

The edge-filter condition keeps both endpoints in the selected vertex
side and removes edges assigned to the first side. Its simple graph is
exactly the path shadow of the corresponding induced graph with those
edges deleted. This connects the executable filter with the canonical
edge-disjoint separation used by II's crossing-scheme recursion.
-/

public section
namespace GraphMinor.Compute
open Graph Set SimpleGraph Classical GraphMinor.GM02

private theorem induced_simple_edge_iff {n : ℕ} (F : SimpleGraph (Fin n))
    (S : Set (Fin n)) (u v : Fin n) :
    s(u, v) ∈ E((Graph.ofSimpleGraph F).induce S) ↔ F.Adj u v ∧ u ∈ S ∧ v ∈ S := by
  constructor
  · rintro ⟨a, b, hab, ha, hb⟩
    have hp : s(u, v) = s(a, b) := hab.1
    have hadj : F.Adj a b := (SimpleGraph.mem_edgeSet _).1 (hp ▸ hab.2)
    rcases Sym2.eq_iff.1 hp with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact ⟨hadj, ha, hb⟩
    · exact ⟨hadj.symm, hb, ha⟩
  · rintro ⟨hadj, hu, hv⟩
    exact ⟨u, v, ⟨rfl, (SimpleGraph.mem_edgeSet _).2 hadj⟩, hu, hv⟩

/-- The filtered simple graph represents the canonical side with edges
inside `A` removed and actual vertex set `B`. -/
theorem gm02FilteredSide_pathGraph {n : ℕ} (F : SimpleGraph (Fin n))
    (A B : Finset (Fin n)) :
    pathGraph (((Graph.ofSimpleGraph F).induce (B : Set (Fin n))).deleteEdges
      E((Graph.ofSimpleGraph F).induce (A : Set (Fin n)))) = gm02FilteredSide F A B := by
  ext u v
  constructor
  · rintro ⟨⟨e, he⟩, hne⟩
    change ((Graph.ofSimpleGraph F).induce (B : Set (Fin n))).IsLink e u v ∧
      e ∉ E((Graph.ofSimpleGraph F).induce (A : Set (Fin n))) at he
    rw [Graph.induce_isLink] at he
    have hep : e = s(u, v) := he.1.1.1
    have hf : F.Adj u v := (SimpleGraph.mem_edgeSet _).1 (hep ▸ he.1.1.2)
    refine ⟨hf, ?_⟩
    simp only [keepCoreEdge, decide_eq_true_eq, Finset.mem_inter]
    refine ⟨he.1.2.1, he.1.2.2, ?_⟩
    intro hh
    apply he.2
    rw [hep, induced_simple_edge_iff]
    exact ⟨hf, hh.1.1, hh.2.1⟩
  · rintro ⟨hf, hk⟩
    simp only [keepCoreEdge, decide_eq_true_eq, Finset.mem_inter] at hk
    refine ⟨⟨s(u, v), ?_⟩, F.ne_of_adj hf⟩
    change ((Graph.ofSimpleGraph F).induce (B : Set (Fin n))).IsLink s(u, v) u v ∧
      s(u, v) ∉ E((Graph.ofSimpleGraph F).induce (A : Set (Fin n)))
    constructor
    · rw [Graph.induce_isLink]
      exact ⟨⟨rfl, (SimpleGraph.mem_edgeSet _).2 hf⟩, hk.1, hk.2.1⟩
    · rw [induced_simple_edge_iff]
      rintro ⟨_, hu, hv⟩
      exact hk.2.2 ⟨⟨hu, hk.1⟩, ⟨hv, hk.2.1⟩⟩

end GraphMinor.Compute
