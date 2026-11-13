module

public import GraphMinor.Compute.GM06Alg34InteriorComponent
public import GraphMinor.Compute.GM06Alg34SingletonFind

/-!
# Nonempty boundary and edge bounds at a stuck finite state

If no interior component is found in a nonempty graph, a supplied cuff
contains a vertex. If a division has a vertex but has no singleton,
there are at least two supplied vertices. Connectedness then gives an
adjacency and hence an edge label. These facts justify the dual step's
progress bounds from the finite search results.
-/

public section
namespace GraphMinor.Compute.GM06DrawingData

open Set GM06

/-- A nonempty finite input with no interior component has a supplied cuff vertex. -/
theorem cuff_vertex_of_no_interior (x : GM06DrawingData) (hn : 0 < x.n)
    (hfind : x.findInteriorComponent = none) :
    ∃ L ∈ x.cuffs, ∃ b, b ∈ L := by
  let a : Fin x.n := ⟨0, hn⟩
  have hnot := (List.find?_eq_none.mp hfind) a (List.mem_finRange a)
  have ha : x.isInteriorComponent a = false := by
    cases hh : x.isInteriorComponent a with
    | false => rfl
    | true => exact False.elim (hnot hh)
  have hAny : x.cuffs.any (fun L => L.any (fun b => decide (x.vertexGraph.Reachable a b))) = true := by
    cases hb : x.cuffs.any (fun L => L.any (fun b => decide (x.vertexGraph.Reachable a b))) <;>
      simp_all [isInteriorComponent]
  obtain ⟨L, hL, hLL⟩ := List.any_eq_true.mp hAny
  obtain ⟨b, hb, _⟩ := List.any_eq_true.mp hLL
  exact ⟨L, hL, b, hb⟩

/-- A nonempty division union with no singleton requires at least two vertex labels. -/
theorem two_le_n_of_no_singleton (x : GM06DrawingData)
    (hne : (divisionUnion x.divisionSet).Nonempty)
    (hfind : gm06FindSingleton x.division = none) : 2 ≤ x.n := by
  obtain ⟨a, A, hA, ha⟩ := hne
  by_contra hn
  have hEq : ∀ b : Fin x.n, b = a := by
    intro b
    apply Fin.ext
    have hb := b.isLt
    have ha' := a.isLt
    omega
  have hAs : A = {a} := by
    ext b
    constructor
    · intro _
      exact hEq b
    · intro hb
      rcases hb with rfl
      exact ha
  have hno := (gm06FindSingleton_eq_none_iff x.division).mp hfind a
  exact hno (hAs ▸ hA)

/-- A preconnected endpoint graph with a nonempty nonsingleton division has an edge. -/
theorem edges_pos_of_no_singleton (x : GM06DrawingData)
    (hc : x.vertexGraph.Preconnected) (hne : (divisionUnion x.divisionSet).Nonempty)
    (hfind : gm06FindSingleton x.division = none) : 0 < x.ends.length := by
  have hn := x.two_le_n_of_no_singleton hne hfind
  haveI : Nontrivial (Fin x.n) := Fin.nontrivial_iff_two_le.mpr hn
  let a : Fin x.n := ⟨0, by omega⟩
  obtain ⟨b, _, e, _⟩ := hc.exists_adj_of_nontrivial a
  have he := e.isLt
  omega

end GraphMinor.Compute.GM06DrawingData
