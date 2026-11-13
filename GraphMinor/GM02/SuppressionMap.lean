module

public import GraphMinor.GM02.SuppressionMinor

/-!
# Mapping walks through a suppression

Contract the first edge by sending the removed vertex to its first other
end. A first-edge step becomes stationary, a second-edge step uses the
replacement edge, and every other edge step stays unchanged. Thus walks
in connected branch subgraphs map to walks after suppression, without
using any forbidden representing edges when the replacement edge is fresh
with respect to those edges.
-/

@[expose] public section

namespace GraphMinor.GM02

open Graph Set Classical Relation

universe u v

variable {α : Type u} {β : Type v} {G : Graph α β}

/-- The vertex map for contracting the first edge of a suppression. -/
noncomputable def suppressionVertexMap (d : SuppressionData G) (x : α) : α :=
  if x = d.vertex then d.left else x

/-- The edge used after suppression: the second old edge is replaced by
its new edge, and all other old edges keep their names. The first edge
will only be used in stationary steps. -/
noncomputable def suppressionForwardEdgeMap (d : SuppressionData G) (e : β) : β :=
  if e = d.second then d.fresh else e

/-- The first edge is contracted to a stationary step. -/
theorem SuppressionData.vertexMap_first (d : SuppressionData G) {a b : α}
    (hab : G.IsLink d.first a b) :
    suppressionVertexMap d a = suppressionVertexMap d b := by
  have heq := hab.isLink_iff_sym2_eq.1 d.first_link
  rcases Sym2.eq_iff.1 heq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    simp only [suppressionVertexMap, d.vertex_ne_left.symm, ↓reduceIte]

/-- The vertex map takes original vertices to surviving vertices. -/
theorem SuppressionData.vertexMap_mem (d : SuppressionData G) {x : α}
    (hx : x ∈ V(G)) : suppressionVertexMap d x ∈ V(d.result) := by
  by_cases h : x = d.vertex
  · simp only [suppressionVertexMap, h, ↓reduceIte]
    exact ⟨d.first_link.right_mem, d.vertex_ne_left.symm⟩
  · simp only [suppressionVertexMap, h, ↓reduceIte]
    exact ⟨hx, h⟩

/-- Every original edge maps to either a stationary step or an edge of the
suppressed graph. This formula also permits the replacement to be a loop. -/
theorem SuppressionData.map_link (d : SuppressionData G) {e : β} {a b : α}
    (hab : G.IsLink e a b) :
    suppressionVertexMap d a = suppressionVertexMap d b ∨
      d.result.IsLink (suppressionForwardEdgeMap d e)
        (suppressionVertexMap d a) (suppressionVertexMap d b) := by
  by_cases he1 : e = d.first
  · subst e
    exact Or.inl (d.vertexMap_first hab)
  · right
    by_cases he2 : e = d.second
    · subst e
      have heq := hab.isLink_iff_sym2_eq.1 d.second_link
      rcases Sym2.eq_iff.1 heq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · simp only [suppressionForwardEdgeMap, suppressionVertexMap,
          d.vertex_ne_right.symm, ↓reduceIte]
        exact Or.inr ⟨rfl, Or.inl ⟨rfl, rfl⟩⟩
      · simp only [suppressionForwardEdgeMap, suppressionVertexMap,
          d.vertex_ne_right.symm, ↓reduceIte]
        exact Or.inr ⟨rfl, Or.inr ⟨rfl, rfl⟩⟩
    · have ha : a ≠ d.vertex := fun h => d.retained_not_inc he1 he2 (h ▸ hab.inc_left)
      have hb : b ≠ d.vertex := fun h => d.retained_not_inc he1 he2 (h ▸ hab.inc_right)
      simp only [suppressionForwardEdgeMap, suppressionVertexMap, he2, ha, hb, ↓reduceIte]
      exact Or.inl ⟨hab, he1, he2⟩

/-- Avoiding a set of representing edges is preserved by the forward edge
map if the replacement edge is not in that set. -/
theorem SuppressionData.forwardEdgeMap_notMem (d : SuppressionData G)
    {F : Set β} (hfresh : d.fresh ∉ F) {e : β} (he : e ∉ F) :
    suppressionForwardEdgeMap d e ∉ F := by
  by_cases h : e = d.second <;>
    simp only [suppressionForwardEdgeMap, h, ↓reduceIte]
  · exact hfresh
  · exact he

/-- A connected subgraph maps to a connected induced subgraph after
suppression, with any forbidden representing edges still deleted. -/
theorem SuppressionData.connected_image (d : SuppressionData G)
    {F : Set β} (hfresh : d.fresh ∉ F) {K : Graph α β}
    (hKG : K ≤ G.deleteEdges F) (hK : GraphConnected K) :
    GraphConnected ((d.result.deleteEdges F).induce (suppressionVertexMap d '' V(K))) := by
  let L := (d.result.deleteEdges F).induce (suppressionVertexMap d '' V(K))
  have hmap : ∀ {a b}, K.Adj a b →
      ReflTransGen L.Adj (suppressionVertexMap d a) (suppressionVertexMap d b) := by
    rintro a b ⟨e, hab⟩
    have hG := hKG.isLink_mono hab
    have hlink : G.IsLink e a b := hG.1
    have hnot : e ∉ F := hG.2
    rcases d.map_link hlink with heq | hstep
    · rw [heq]
    · exact ReflTransGen.single ⟨suppressionForwardEdgeMap d e,
        ⟨⟨hstep, d.forwardEdgeMap_notMem hfresh hnot⟩,
          ⟨a, hab.left_mem, rfl⟩, ⟨b, hab.right_mem, rfl⟩⟩⟩
  have hwalk : ∀ {a b}, ReflTransGen K.Adj a b →
      ReflTransGen L.Adj (suppressionVertexMap d a) (suppressionVertexMap d b) := by
    intro a b h
    induction h with
    | refl => exact ReflTransGen.refl
    | tail _ hstep ih => exact ih.trans (hmap hstep)
  obtain ⟨a, ha⟩ := hK.1
  refine ⟨⟨suppressionVertexMap d a, a, ha, rfl⟩, ?_⟩
  rintro x ⟨a, ha, rfl⟩ y ⟨b, hb, rfl⟩
  exact hwalk (hK.2 a ha b hb)

end GraphMinor.GM02
