module

public import GraphMinor.Compute.Case3StepsSelectedVertices

/-!
# Edge tests for selected merged members

An edge with an endpoint outside the core belongs to the group of that
endpoint. An edge with both endpoints in the core belongs to the group
whose boundary is its endpoint pair. These are the two raw edge types in
Graph Minors XIII, (8.6), p. 96, used by (9.9), step 5, p. 105.
-/

public section

namespace GraphMinor.Compute

/-- Outside vertices of a selected member are precisely its grouped components. -/
theorem case3SelectedMember_outside_iff (x : Alg81Input) (Z : Finset (Fin x.n))
    (i : Case3SelectedGroup x Z) (u : Fin x.n) (hu : u ∉ Z) :
    u ∈ outsideOfBoundary x Z (case3GroupBoundary x Z i.1) ↔
      u ∈ (case3SelectedMember x Z i).verts := by
  rw [case3SelectedMember_verts, Finset.mem_union]
  have hb : u ∉ case3GroupBoundary x Z i.1 :=
    fun h => hu (case3GroupBoundary_subset_core x Z i h)
  simp only [hb, or_false]

/-- For an edge leaving the core, the outside endpoint alone determines its group. -/
theorem case3SelectedMember_adj_outside_iff (x : Alg81Input) (Z : Finset (Fin x.n))
    (i : Case3SelectedGroup x Z) (u v : Fin x.n) (hu : u ∉ Z)
    (hadj : x.G.Adj u v) :
    (case3SelectedMember x Z i).graph.Adj u v ↔
      case3ComponentRepresentative x Z u = case3RawIndexLabel x i.1 := by
  rw [← case3SelectedMember_mem_outside_iff x Z i u hu,
    ← case3SelectedMember_outside_iff x Z i u hu]
  change (x.G.Adj u v ∧
    ((u ∈ outsideOfBoundary x Z (case3GroupBoundary x Z i.1) ∨
      v ∈ outsideOfBoundary x Z (case3GroupBoundary x Z i.1)) ∨
      (u ∈ Z ∧ v ∈ Z ∧ case3GroupBoundary x Z i.1 = {u, v}))) ↔ _
  constructor
  · rintro ⟨_, (h | h) | h⟩
    · exact h
    · exact outsideOfBoundary_closed h hu hadj.symm
    · exact False.elim (hu h.1)
  · intro h
    exact ⟨hadj, Or.inl (Or.inl h)⟩

/-- For an edge inside the core, the boundary pair alone determines its group. -/
theorem case3SelectedMember_adj_core_iff (x : Alg81Input) (Z : Finset (Fin x.n))
    (i : Case3SelectedGroup x Z) (u v : Fin x.n) (hu : u ∈ Z) (hv : v ∈ Z)
    (hadj : x.G.Adj u v) :
    (case3SelectedMember x Z i).graph.Adj u v ↔
      case3GroupBoundary x Z i.1 = {u, v} := by
  have hout (z : Fin x.n) (hz : z ∈ Z) :
      z ∉ outsideOfBoundary x Z (case3GroupBoundary x Z i.1) := by
    intro h
    have hdis := outsideOfBoundary_disjoint_Z x Z (case3GroupBoundary x Z i.1)
    exact Finset.disjoint_left.mp hdis h hz
  change (x.G.Adj u v ∧
    ((u ∈ outsideOfBoundary x Z (case3GroupBoundary x Z i.1) ∨
      v ∈ outsideOfBoundary x Z (case3GroupBoundary x Z i.1)) ∨
      (u ∈ Z ∧ v ∈ Z ∧ case3GroupBoundary x Z i.1 = {u, v}))) ↔ _
  simp only [hadj, true_and, hout u hu, hout v hv, false_or, hu, hv]

end GraphMinor.Compute
