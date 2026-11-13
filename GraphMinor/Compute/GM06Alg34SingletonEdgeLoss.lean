module

public import GraphMinor.Compute.GM06Alg34SingletonBounds
public import GraphMinor.Compute.GM06Alg34WorkWeight

/-!
# Edge loss when a connected drawing loses a vertex

Every vertex of a connected graph with an edge has an incident edge.
Deleting that vertex removes its edge label from the retained edge
list, so the edge count strictly decreases. This supplies the edge
loss needed to charge a dual transition followed by singleton deletion.
-/

public section
namespace GraphMinor.Compute.GM06DrawingData

private theorem filter_length_lt {α : Type*} (L : List α) (p : α → Bool)
    (a : α) (ha : a ∈ L) (hp : p a = false) : (L.filter p).length < L.length := by
  induction L with
  | nil => simp only [List.not_mem_nil] at ha
  | cons b L ih =>
    rcases List.mem_cons.mp ha with rfl | ha
    · simp only [List.filter_cons, hp, Bool.false_eq_true, ↓reduceIte, List.length_cons]
      exact Nat.lt_succ_of_le (List.length_filter_le _ _)
    · have ht := ih ha
      cases hb : p b
      · simpa only [List.filter_cons, hb, Bool.false_eq_true, ↓reduceIte, List.length_cons]
          using Nat.lt_succ_of_lt ht
      · simpa only [List.filter_cons, hb, ↓reduceIte, List.length_cons]
          using Nat.succ_lt_succ ht

/-- An incident edge is removed by singleton vertex deletion. -/
theorem singletonData_edges_lt_of_incident (x : GM06DrawingData) (v : Fin x.n)
    (e : Fin x.ends.length) (he : v = x.ends[e].1 ∨ v = x.ends[e].2) :
    (x.singletonData v).ends.length < x.ends.length := by
  have hnot : e ∉ x.activeEdges (x.singletonSurvivors v) := by
    intro hh
    have hh' := (x.mem_activeEdges_iff _ e).mp hh
    rcases he with he | he
    · exact ((x.mem_singletonSurvivors_iff v _).mp hh'.1) he.symm
    · exact ((x.mem_singletonSurvivors_iff v _).mp hh'.2) he.symm
  have hp : x.activeCell (x.singletonSurvivors v) (.inr (.inl e)) = false := by
    cases hb : x.activeCell (x.singletonSurvivors v) (.inr (.inl e))
    · rfl
    · exact False.elim (hnot (List.mem_filter.mpr ⟨List.mem_finRange _, hb⟩))
  rw [singletonData, x.inducedData_ends_length]
  exact (filter_length_lt (List.finRange x.ends.length) _ e (List.mem_finRange _) hp).trans_eq
    (List.length_finRange)

/-- A connected finite endpoint graph with an edge has an edge incident with every vertex. -/
theorem exists_incident_of_preconnected (x : GM06DrawingData)
    (hc : x.vertexGraph.Preconnected) (hE : 0 < x.ends.length) (v : Fin x.n) :
    ∃ e : Fin x.ends.length, v = x.ends[e].1 ∨ v = x.ends[e].2 := by
  by_cases hn : 2 ≤ x.n
  · haveI : Nontrivial (Fin x.n) := Fin.nontrivial_iff_two_le.mpr hn
    obtain ⟨u, hu⟩ := hc.exists_adj_of_nontrivial v
    obtain ⟨_, e, he⟩ := hu
    exact ⟨e, he.elim (fun hh => Or.inl hh.1) (fun hh => Or.inr hh.1)⟩
  · let e : Fin x.ends.length := ⟨0, hE⟩
    refine ⟨e, Or.inl ?_⟩
    apply Fin.ext
    have hv := v.isLt
    have he := x.ends[e].1.isLt
    omega

/-- Singleton deletion in a connected finite graph with an edge strictly loses edges. -/
theorem singletonData_edges_lt_of_preconnected (x : GM06DrawingData)
    (hc : x.vertexGraph.Preconnected) (hE : 0 < x.ends.length) (v : Fin x.n) :
    (x.singletonData v).ends.length < x.ends.length := by
  obtain ⟨e, he⟩ := x.exists_incident_of_preconnected hc hE v
  exact x.singletonData_edges_lt_of_incident v e he

/-- Ordinary singleton deletion strictly lowers the queue weight. -/
theorem singletonData_workWeight_lt (C : ℕ) (x : GM06DrawingData) (v : Fin x.n) :
    (x.singletonData v).workWeight C < x.workWeight C := by
  apply x.workWeight_lt_of_mass C _ (by have hv := v.isLt; omega)
  exact x.workMass_lt_of_vertices C _ (gm06SingletonData_n_lt x v) (gm06SingletonData_edges_le x v)

end GraphMinor.Compute.GM06DrawingData
