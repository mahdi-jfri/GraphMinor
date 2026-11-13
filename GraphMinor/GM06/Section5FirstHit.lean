module

public import GraphMinor.GM06.Defs
import GraphMinor.GM06.Section5Red
import GraphMinor.GM06.Section4PathTools
import GraphMinor.GM06.Section4Overlap
import GraphMinor.GM11.Walks

/-!
# Stopping a path at its first contact

The proof of VI (5.1), page 129, follows a region boundary until it
first meets the next linkage path. A simple graph walk has a prefix
whose only vertex in a specified target set is its last vertex.
For subdrawings, the vertex condition also excludes shared edge
interiors, since the starting vertex is outside the target drawing.
-/

public section

namespace GraphMinor.GM06

open Set GraphMinor.Surface GraphMinor.GM11

universe u v

/-- A simple walk has a simple prefix ending at its first vertex in
a target set. Its other vertices miss that set. -/
theorem exists_first_hit_walk
    {α : Type u} {β : Type v} {G : Graph α β} {s t : α} {B : Set α}
    (W : GraphWalk G s t) :
    W.IsSimple → s ∉ B → t ∈ B →
    ∃ x ∈ B, ∃ R : GraphWalk G s x, R.IsSimple ∧
      (∀ y ∈ R.support, y ∈ W.support) ∧
      (∀ e ∈ R.edges, e ∈ W.edges) ∧
      (∀ y ∈ R.support, y ∈ B → y = x) := by
  classical
  induction W with
  | nil hv =>
    intro _ hs ht
    exact False.elim (hs ht)
  | @cons s a t e hl W ih =>
    intro hW hs ht
    by_cases ha : a ∈ B
    · have hsa : s ≠ a := fun he => hs (he.symm ▸ ha)
      refine ⟨a, ha, GraphWalk.cons hl (GraphWalk.nil hl.right_mem), ?_, ?_, ?_, ?_⟩
      · change ([s, a] : List α).Nodup
        exact List.nodup_cons.mpr ⟨by simpa only [List.mem_singleton] using hsa,
          List.nodup_singleton a⟩
      · intro y hy
        change y ∈ [s, a] at hy
        rcases List.mem_cons.mp hy with rfl | hy
        · exact List.mem_cons_self
        · have heq := List.mem_singleton.mp hy
          subst y
          exact List.mem_cons_of_mem s W.start_mem_support
      · intro f hf
        change f ∈ [e] at hf
        exact List.mem_cons.mpr (Or.inl (List.mem_singleton.mp hf))
      · intro y hy hyB
        change y ∈ [s, a] at hy
        rcases List.mem_cons.mp hy with rfl | hy
        · exact False.elim (hs hyB)
        · exact List.mem_singleton.mp hy
    · obtain ⟨x, hx, R, hR, hV, hE, hB⟩ := ih (List.nodup_cons.mp hW).2 ha ht
      refine ⟨x, hx, GraphWalk.cons hl R, ?_, ?_, ?_, ?_⟩
      · exact List.nodup_cons.mpr
          ⟨fun h => (List.nodup_cons.mp hW).1 (hV s h), hR⟩
      · intro y hy
        rcases List.mem_cons.mp hy with he | hy
        · exact List.mem_cons.mpr (Or.inl he)
        · exact List.mem_cons_of_mem s (hV y hy)
      · intro f hf
        rcases List.mem_cons.mp hf with he | hf
        · exact List.mem_cons.mpr (Or.inl he)
        · exact List.mem_cons_of_mem e (hE f hf)
      · intro y hy hyB
        rcases List.mem_cons.mp hy with rfl | hy
        · exact False.elim (hs hyB)
        · exact hB y hy hyB

/-- Stop a path drawing the first time its graph walk reaches a given
vertex set, as in VI (5.1), page 129. -/
theorem exists_subpath_to_vertex_set
    {S : Type u} [TopologicalSpace S] [T1Space S]
    {Q : Drawing S} {s t : S} {B : Set S}
    (hQ : IsPathDrawing Q s t) (hs : s ∉ B) (ht : t ∈ B) :
    ∃ x ∈ B, ∃ P : Drawing S,
      IsSubpathOf Q P s x ∧ P.V ∩ B ⊆ {x} := by
  obtain ⟨W, hW, _, _⟩ := hQ.1
  obtain ⟨x, hx, R, hR, _, _, hB⟩ := exists_first_hit_walk W hW hs ht
  have hsub := walkDrawing_isSubdrawing Q R
  have hsx : s ≠ x := fun he => hs (he.symm ▸ hx)
  refine ⟨x, hx, walkDrawing Q R,
    ⟨hsub, hsub.U_subset, isPathDrawing_walkDrawing_of_isSimple Q hR hsx⟩, ?_⟩
  intro y hy
  have hyR : y ∈ R.support := by
    simpa only [walkDrawing_V, mem_ofPred_eq] using hy.1
  exact mem_singleton_iff.mpr (hB y hyR hy.2)

/-- The prefix to the first target vertex meets the target drawing
only at that vertex. This supplies the point-set version of the first
contact used in VI (5.1), page 129. -/
theorem exists_subpath_first_contact
    {S : Type u} [TopologicalSpace S] [T2Space S]
    {G Q D : Drawing S} {s t : S}
    (hQG : Q.IsSubdrawing G) (hDG : D.IsSubdrawing G)
    (hQ : IsPathDrawing Q s t) (hs : s ∉ D.U) (ht : t ∈ D.V) :
    ∃ x ∈ D.V, ∃ P : Drawing S,
      IsSubpathOf Q P s x ∧ P.U ∩ D.U ⊆ {x} := by
  have hsV : s ∉ D.V := fun h => hs (D.V_subset_U h)
  obtain ⟨x, hx, P, hP, hPV⟩ := exists_subpath_to_vertex_set hQ hsV ht
  have hPG : P.IsSubdrawing G := ⟨hP.1.1.trans hQG.1, hP.1.2.trans hQG.2⟩
  have hstart : s ∈ P.U := P.V_subset_U (isPathDrawing_end_vertices hP.2.2).1
  have hmeet : (P.U ∩ ({s} : Set S)).Nonempty := ⟨s, hstart, mem_singleton s⟩
  have hDX : Disjoint D.U ({s} : Set S) := disjoint_singleton_right.mpr hs
  have hinter := path_intersection_subset_ends_of_vertices hPG hDG hP.2.2
    (fun y hy => mem_insert_of_mem s (hPV hy)) hmeet hDX
  refine ⟨x, hx, P, hP, ?_⟩
  intro y hy
  rcases hinter hy with he | he
  · exact False.elim (hs (he ▸ hy.2))
  · exact he

end GraphMinor.GM06
