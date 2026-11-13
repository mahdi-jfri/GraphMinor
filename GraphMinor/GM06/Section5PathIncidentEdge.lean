module

public import GraphMinor.GM06.Defs
import GraphMinor.GM06.Section5EndpointObstruction
import GraphMinor.GM11.Walks

/-!
# Covering path vertices by edge endpoints

The linkage-mask scan for VI (5.7), page 133, marks endpoints of
the supplied path edges. Every vertex of a path with distinct ends
is such an endpoint. Prove this directly along its tracing walk,
including the last vertex, to justify the computed vertex mask.
-/

public section
namespace GraphMinor.GM06
open Set GraphMinor.Surface

private theorem support_incident_or_singleton {α β : Type*} {G : Graph α β}
    {s t : α} (W : GraphWalk G s t) {a : α} (ha : a ∈ W.support) :
    (∃ e ∈ W.edges, ∃ b, G.IsLink e a b) ∨ (W.edges = [] ∧ a = s) := by
  induction W with
  | nil hv =>
    exact Or.inr ⟨rfl, List.mem_singleton.mp ha⟩
  | @cons s v t e hl T ih =>
    rcases List.mem_cons.mp ha with rfl | ha
    · exact Or.inl ⟨e, List.mem_cons_self, v, hl⟩
    · rcases ih ha with ⟨f, hf, b, hfb⟩ | ⟨_, rfl⟩
      · exact Or.inl ⟨f, List.mem_cons_of_mem e hf, b, hfb⟩
      · exact Or.inl ⟨e, List.mem_cons_self, s, hl.symm⟩

/-- Every vertex of a nondegenerate path drawing is incident with a path edge. -/
theorem isPathDrawing_exists_incident_edge
    {S : Type*} [TopologicalSpace S] {P : Drawing S} {s t a : S}
    (hP : IsPathDrawing P s t) (ha : a ∈ P.V) :
    ∃ e ∈ P.E, ∃ b, P.toGraph.IsLink e a b := by
  have hst := isPathDrawing_start_ne_end hP
  obtain ⟨W, _, hV, hE⟩ := hP.1
  have haW : a ∈ W.support := by simpa only [hV, mem_ofPred_eq] using ha
  rcases support_incident_or_singleton W haW with ⟨e, he, b, hl⟩ | ⟨hzero, _⟩
  · exact ⟨e, hE ▸ he, b, hl⟩
  · cases W with
    | nil _ => exact False.elim (hst rfl)
    | cons _ _ => simp at hzero

end GraphMinor.GM06
