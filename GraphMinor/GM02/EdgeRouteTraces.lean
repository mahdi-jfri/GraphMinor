module

public import GraphMinor.GM02.EdgeRouteTraceStep
import GraphMinor.GM02.Section4Suppression

/-!
# Edge-labelled traces of a suppression sequence

Start with the one-edge walk of every host edge. At each suppression,
glue the two removed edges' traces and retain the others. Induction on
the sequence gives traces for the final edges, with disjoint interiors
and disjoint host-edge sets. Indexing by actual edges also covers an
empty graph without requiring an arbitrary vertex or edge name.
-/

public section
namespace GraphMinor.GM02
open Graph Set Classical Surface Relation
universe u v

/-- Every edge of a suppressed graph has a nonempty edge-labelled host trace, with disjoint interiors and edge sets. -/
theorem exists_edgeRoute_traces {α : Type u} {β : Type v} {K L : Graph α β}
    (h : ReflTransGen IsSuppression K L) :
    ∃ R : E(L) → EdgeRoute K,
      (∀ f, L.IsLink f.val (R f).start (R f).finish ∧
        (R f).walk.support = (R f).start :: ((R f).inner ++ [(R f).finish]) ∧
        (R f).inner.Nodup ∧ (∀ y ∈ (R f).inner, y ∈ V(K) \ V(L)) ∧
        (R f).walk.edges.Nodup ∧ (R f).walk.edges ≠ []) ∧
      ∀ f g, f ≠ g →
        Disjoint {y | y ∈ (R f).inner} {y | y ∈ (R g).inner} ∧
        Disjoint {e | e ∈ (R f).walk.edges} {e | e ∈ (R g).walk.edges} := by
  induction h with
  | refl =>
    choose a b hab using (fun f : E(K) => K.exists_isLink_of_mem_edgeSet f.property)
    let R : E(K) → EdgeRoute K := fun f =>
      ⟨a f, b f, [], .cons (hab f) (.nil (hab f).right_mem)⟩
    refine ⟨R, ?_, ?_⟩
    · intro f
      refine ⟨hab f, rfl, List.nodup_nil, ?_, ?_, ?_⟩
      · intro y hy
        exact (List.not_mem_nil hy).elim
      · exact List.nodup_singleton _
      · exact List.cons_ne_nil _ _
    · intro f g hfg
      constructor
      · rw [Set.disjoint_left]
        intro y hy
        exact (List.not_mem_nil hy).elim
      · rw [Set.disjoint_left]
        intro e hef heg
        change e ∈ [f.val] at hef
        change e ∈ [g.val] at heg
        have hef' := List.mem_singleton.1 hef
        have heg' := List.mem_singleton.1 heg
        exact hfg (Subtype.ext (hef'.symm.trans heg'))
  | @tail M L hKM hstep ih =>
    obtain ⟨R, hR, hDis⟩ := ih
    obtain ⟨d, rfl⟩ := hstep
    exact exists_edgeRoute_trace_step R (vertexSet_subset_of_reflTransGen hKM) hR hDis d

end GraphMinor.GM02
