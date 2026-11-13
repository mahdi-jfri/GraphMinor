module

public import GraphMinor.GM16.Defs
import GraphMinor.GM09.Basic

/-!
# The graph retained by a location

The location in XVI (1.3), page 51, removes all the edges of each
society. We describe the edges that remain in the core and prove that
none remain when the left sides cover every edge. This lets the torso
edges be assigned to the separators that contain their ends.
-/

public section
namespace GraphMinor.GM16
open Set Graph GM06 GM09 GM14
universe u v

/-- The core is a subgraph of the original graph. -/
theorem graphLocationCore_le {α : Type u} {β : Type v}
    (G : Graph α β) (ℒ : Set (Graph α β × Graph α β)) :
    graphLocationCore G ℒ ≤ G :=
  restrict_le.trans (G.induce_le (fun _ h => h.1))

/-- An edge remains in the core exactly when it belongs to every
right side. Membership in those sides also puts its ends in the core. -/
theorem edgeSet_graphLocationCore {α : Type u} {β : Type v}
    {G : Graph α β} {ℒ : Set (Graph α β × Graph α β)}
    (h : IsGraphLocation G ℒ) :
    E(graphLocationCore G ℒ) = {e ∈ E(G) | ∀ p ∈ ℒ, e ∈ E(p.2)} := by
  ext e
  change e ∈ E(G.induce _) ∩ {e ∈ E(G) | ∀ p ∈ ℒ, e ∈ E(p.2)} ↔ _
  refine ⟨fun he => he.2, fun he => ⟨?_, he⟩⟩
  obtain ⟨x, y, hxy⟩ := G.exists_isLink_of_mem_edgeSet he.1
  refine ⟨x, y, hxy, ⟨hxy.left_mem, ?_⟩, ⟨hxy.right_mem, ?_⟩⟩
  · intro p hp
    exact (((h.isSeparation hp).2.1.isLink_iff (he.2 p hp)).mpr hxy).left_mem
  · intro p hp
    exact (((h.isSeparation hp).2.1.isLink_iff (he.2 p hp)).mpr hxy).right_mem

/-- If the left sides cover every edge, the core has no edges.
This is used for both the local ring locations and their assembly in
XVI (1.3), page 51. -/
theorem IsGraphLocation.edgeSet_core_eq_empty {α : Type u} {β : Type v}
    {G : Graph α β} {ℒ : Set (Graph α β × Graph α β)}
    (h : IsGraphLocation G ℒ)
    (hcover : ∀ e ∈ E(G), ∃ p ∈ ℒ, e ∈ E(p.1)) :
    E(graphLocationCore G ℒ) = ∅ := by
  rw [edgeSet_graphLocationCore h]
  apply eq_empty_iff_forall_notMem.mpr
  rintro e ⟨heG, heAll⟩
  obtain ⟨p, hp, heLeft⟩ := hcover e heG
  exact disjoint_left.mp (h.isSeparation hp).2.2.2.2 heLeft (heAll p hp)

/-- The separator sets of a location lie in its core, so its design
is a finite graph design whenever the original graph is finite. -/
theorem IsGraphLocation.isGraphDesign {α : Type u} {β : Type v}
    {G : Graph α β} {ℒ : Set (Graph α β × Graph α β)}
    (h : IsGraphLocation G ℒ) (hV : V(G).Finite) (hE : E(G).Finite) :
    IsGraphDesign (graphLocationDesign G ℒ) := by
  have hle := graphLocationCore_le G ℒ
  refine ⟨hV.subset hle.vertexSet_mono, hE.subset hle.edgeSet_mono, ?_⟩
  rintro X ⟨p, hp, rfl⟩ x ⟨hxA, hxB⟩
  change x ∈ V(G) ∧ ∀ q ∈ ℒ, x ∈ V(q.2)
  refine ⟨(h.isSeparation hp).1.vertexSet_mono hxA, ?_⟩
  intro q hq
  by_cases hpq : p = q
  · exact hpq ▸ hxB
  · exact (h.left_le_right hp hq hpq).vertexSet_mono hxA

/-- If the left sides cover every vertex, every retained core vertex
belongs to one of the design sets. -/
theorem location_core_vertex_mem_design_set {α : Type u} {β : Type v}
    {G : Graph α β} {ℒ : Set (Graph α β × Graph α β)}
    (hCover : ∀ x ∈ V(G), ∃ p ∈ ℒ, x ∈ V(p.1))
    {x : α} (hx : x ∈ V(graphLocationCore G ℒ)) :
    ∃ X ∈ (graphLocationDesign G ℒ).2, x ∈ X := by
  have hxG := (graphLocationCore_le G ℒ).vertexSet_mono hx
  obtain ⟨p, hp, hxA⟩ := hCover x hxG
  exact ⟨V(p.1) ∩ V(p.2), mem_image_of_mem _ hp, hxA, hx.2 p hp⟩

end GraphMinor.GM16
