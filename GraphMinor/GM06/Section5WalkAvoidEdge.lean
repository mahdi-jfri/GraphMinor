module

public import GraphMinor.GM06.Defs
public import GraphMinor.GM11.Walks
import GraphMinor.GM06.Section5WalkSubpaths
import Mathlib.Data.List.Count

/-!
# Following a region boundary without a cuff edge

In the boundary argument of VI (5.1), page 129, the added cuff edge
must be left out when extracting Qᵢ. An edge used at most once by a
closed walk can be avoided between any two vertices of that walk.
For a vertex, split the walk there and choose the prefix or the
reversed suffix. They cannot both use that edge. Joining two such
walks and removing repetitions gives the required path.
-/

public section

namespace GraphMinor.GM06

open Set GraphMinor.Surface

universe u v

private theorem exists_walk_to_support_avoiding_edge
    {α : Type u} {β : Type v} [DecidableEq β] {G : Graph α β} {s x : α}
    (W : GraphWalk G s s) (e : β) (hcount : W.edges.count e ≤ 1) (hx : x ∈ W.support) :
    ∃ R : GraphWalk G s x, e ∉ R.edges ∧ R.support ⊆ W.support ∧ R.edges ⊆ W.edges := by
  obtain ⟨A, B, hW⟩ := W.exists_append_of_mem hx
  by_cases heA : e ∈ A.edges
  · have heB : e ∉ B.edges := by
      intro heB
      have hA : 0 < A.edges.count e := List.count_pos_iff.mpr heA
      have hB : 0 < B.edges.count e := List.count_pos_iff.mpr heB
      rw [hW, GraphWalk.edges_append, List.count_append] at hcount
      omega
    refine ⟨B.reverse, ?_, ?_, ?_⟩
    · simpa only [GraphWalk.edges_reverse, List.mem_reverse] using heB
    · intro y hy
      rw [GraphWalk.support_reverse, List.mem_reverse] at hy
      rw [hW, GraphWalk.mem_support_append]
      exact Or.inr hy
    · intro f hf
      rw [GraphWalk.edges_reverse, List.mem_reverse] at hf
      rw [hW, GraphWalk.edges_append, List.mem_append]
      exact Or.inr hf
  · refine ⟨A, heA, ?_, ?_⟩
    · intro y hy
      rw [hW, GraphWalk.mem_support_append]
      exact Or.inl hy
    · intro f hf
      rw [hW, GraphWalk.edges_append, List.mem_append]
      exact Or.inl hf

/-- Any two distinct vertices of a closed boundary walk are joined
along that walk while avoiding an edge occurring at most once. -/
theorem exists_subpath_avoiding_edge_of_closed_walk
    {S : Type u} [TopologicalSpace S] [T1Space S] (G : Drawing S)
    {s a b : S} (W : GraphWalk G.toGraph s s) (e : Set S)
    [DecidableEq (Set S)] (hcount : W.edges.count e ≤ 1)
    (ha : a ∈ W.support) (hb : b ∈ W.support) (hab : a ≠ b) :
    ∃ P : Drawing S, IsSubpathOf G P a b ∧
      P.V ⊆ {x | x ∈ W.support} ∧ P.E ⊆ {f | f ∈ W.edges} ∧ e ∉ P.E := by
  obtain ⟨A, heA, hVA, hEA⟩ := exists_walk_to_support_avoiding_edge W e hcount ha
  obtain ⟨B, heB, hVB, hEB⟩ := exists_walk_to_support_avoiding_edge W e hcount hb
  let R := A.reverse.append B
  have hVR : R.support ⊆ W.support := by
    intro x hx
    rw [GraphWalk.mem_support_append, GraphWalk.support_reverse, List.mem_reverse] at hx
    exact hx.elim (hVA ·) (hVB ·)
  have hER : R.edges ⊆ W.edges := by
    intro f hf
    rw [GraphWalk.edges_append, List.mem_append, GraphWalk.edges_reverse, List.mem_reverse] at hf
    exact hf.elim (hEA ·) (hEB ·)
  have heR : e ∉ R.edges := by
    rw [GraphWalk.edges_append, List.mem_append, GraphWalk.edges_reverse, List.mem_reverse]
    exact fun h => h.elim heA heB
  obtain ⟨P, hP, hPV, hPE⟩ := exists_subpath_of_walk_support G R
    R.start_mem_support R.end_mem_support hab
  exact ⟨P, hP, fun _ hx => hVR (hPV hx), fun _ hf => hER (hPE hf), fun he => heR (hPE he)⟩

end GraphMinor.GM06
