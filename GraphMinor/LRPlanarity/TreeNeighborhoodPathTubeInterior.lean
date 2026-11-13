module

public import GraphMinor.LRPlanarity.TreeNeighborhoodPathTube
public import GraphMinor.HP25.Embedding

/-!
# Interior containment along a subdivided tree edge

Part IV, Section 7b of the planarity note leaves the drawn tree image
unchanged when it is subdivided at bends. The image of a walk is the union
of the drawn lines of its darts. Each such line is interior to its two
vertex polygons and strip. All those pieces belong to the tube together
with its two endpoint polygons, so the whole original edge is interior.
-/

public section
namespace GraphMinor.LRPlanarity

open Set SimpleGraph

/-- A walk image is exactly the union of its drawn edge images. -/
theorem walk_pathImage_eq_dart_union {V : Type*} {G : SimpleGraph V}
    (drawing : HP25.PlaneEmbedding G univ) {u v : V} (w : G.Walk u v) :
    drawing.pathImage w.support = ⋃ e ∈ w.darts, drawing.line e.fst e.snd := by
  induction w with
  | nil => simp
  | @cons u v t h q ih =>
    rw [Walk.support_cons, ← q.cons_tail_support, drawing.pathImage_cons_cons,
      q.cons_tail_support, ih]
    ext x
    simp [Walk.darts_cons]

/-- The support of a nonempty walk consists of its first vertex, its
internal vertices, and its last vertex. -/
theorem walk_support_endpoint_decomposition {V : Type*} {G : SimpleGraph V}
    {u v : V} (w : G.Walk u v) (hnil : ¬w.Nil) :
    w.support = u :: (w.support.tail.dropLast ++ [v]) := by
  cases w with
  | nil => exact (hnil Walk.Nil.nil).elim
  | cons h q =>
    simp only [Walk.support_cons, List.tail_cons]
    congr 1
    symm
    simpa only [q.getLast_support] using List.dropLast_append_getLast q.support_ne_nil

/-- Every vertex of a nonempty simple walk lies on its geometric image. -/
theorem path_vertex_mem_pathImage {V : Type*} {G : SimpleGraph V}
    (drawing : HP25.PlaneEmbedding G univ) {u v : V} (w : G.Walk u v)
    (hw : w.IsPath) (hnil : ¬w.Nil) {z : V} (hz : z ∈ w.support) :
    drawing.pt z ∈ drawing.pathImage w.support := by
  have h2 : 2 ≤ w.support.length := by
    cases w with
    | nil => exact (hnil Walk.Nil.nil).elim
    | cons h q => simp [Walk.length_support]
  exact drawing.pt_mem_pathImage (HP25.PlaneEmbedding.isPathList_support hw (fun _ _ => mem_univ _)) h2 hz

/-- Part IV, Section 7b: local edge-interior containment implies interior
containment of the full original path in its tube and endpoint polygons. -/
theorem walk_pathImage_subset_interior_cells {V : Type*} {G : SimpleGraph V}
    (drawing : HP25.PlaneEmbedding G univ) (P : V → Set ℂ) (R : V → V → Set ℂ)
    (hlocal : ∀ u v, G.Adj u v → drawing.line u v ⊆ interior (P u ∪ R u v ∪ P v))
    {u v : V} (w : G.Walk u v) (hnil : ¬w.Nil) :
    drawing.pathImage w.support ⊆ interior (P u ∪ walkTube P R w ∪ P v) := by
  have hPsub : ∀ z ∈ w.support, P z ⊆ P u ∪ walkTube P R w ∪ P v := by
    intro z hz x hx
    rw [walk_support_endpoint_decomposition w hnil] at hz
    simp only [List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at hz
    rcases hz with he | hmid | he
    · subst z
      exact Or.inl (Or.inl hx)
    · exact Or.inl (Or.inr ((mem_walkTube_iff P R w x).mpr (Or.inr ⟨z, hmid, hx⟩)))
    · subst z
      exact Or.inr hx
  rw [walk_pathImage_eq_dart_union]
  intro x hx
  obtain ⟨e, he'⟩ := mem_iUnion.mp hx
  obtain ⟨he, hxe⟩ := mem_iUnion.mp he'
  obtain ⟨hfst, hsnd⟩ := walk_dart_ends_mem_support w he
  apply interior_mono (union_subset (union_subset (hPsub e.fst hfst) ?_)
    (hPsub e.snd hsnd)) (hlocal e.fst e.snd e.adj hxe)
  intro y hy
  exact Or.inl (Or.inr ((mem_walkTube_iff P R w y).mpr (Or.inl ⟨e, he, hy⟩)))

end GraphMinor.LRPlanarity
