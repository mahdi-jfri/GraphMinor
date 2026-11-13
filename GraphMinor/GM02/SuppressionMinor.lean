module

public import GraphMinor.GM02.TopologicalContainment

/-!
# The branch sets for suppression

A suppression contracts its first edge. The branch set at the first other
end contains that end and the removed vertex, and all other branch sets are
singletons. The replacement edge is represented by the second original
edge. These sets and edges preserve incidence, including when suppression
creates a loop.
-/

@[expose] public section

namespace GraphMinor.GM02

open Graph Set

universe u v

variable {α : Type u} {β : Type v} {G : Graph α β}

/-- The branch sets when the first edge of a suppression is contracted. -/
def suppressionBranchSet (d : SuppressionData G) (z : α) : Set α :=
  {x | x = z ∨ (z = d.left ∧ x = d.vertex)}

open Classical in
/-- The new edge is represented by the second old edge. All retained edges
represent themselves. -/
noncomputable def suppressionEdgeMap (d : SuppressionData G) (e : β) : β :=
  if e = d.fresh then d.second else e

/-- Each surviving vertex lies in its own branch set. -/
theorem SuppressionData.mem_branchSet_self (d : SuppressionData G) (z : α) :
    z ∈ suppressionBranchSet d z := Or.inl rfl

/-- The branch sets contain only original vertices. -/
theorem SuppressionData.branchSet_subset (d : SuppressionData G) {z : α}
    (hz : z ∈ V(d.result)) : suppressionBranchSet d z ⊆ V(G) := by
  rintro x (rfl | ⟨_, rfl⟩)
  · exact hz.1
  · exact d.first_link.left_mem

/-- Distinct surviving vertices have disjoint branch sets. -/
theorem SuppressionData.branchSet_disjoint (d : SuppressionData G)
    {a b : α} (ha : a ∈ V(d.result)) (hb : b ∈ V(d.result)) (hab : a ≠ b) :
    Disjoint (suppressionBranchSet d a) (suppressionBranchSet d b) := by
  apply Set.disjoint_left.2
  rintro x (hxa | ⟨ha', hx⟩) (hxb | ⟨hb', hx'⟩)
  · exact hab (hxa.symm.trans hxb)
  · exact ha.2 (hxa.symm.trans hx')
  · exact hb.2 (hxb.symm.trans hx)
  · exact hab (ha'.trans hb'.symm)

/-- The second edge has only its two specified ends. -/
theorem SuppressionData.second_inc_iff (d : SuppressionData G) (x : α) :
    G.Inc d.second x ↔ x = d.vertex ∨ x = d.right := by
  constructor
  · exact fun hx => hx.eq_or_eq_of_isLink d.second_link
  · rintro (rfl | rfl)
    · exact d.second_link.inc_left
    · exact d.second_link.inc_right

/-- Every retained edge avoids the removed vertex. -/
theorem SuppressionData.retained_not_inc (d : SuppressionData G)
    {e : β} (h1 : e ≠ d.first) (h2 : e ≠ d.second) : ¬ G.Inc e d.vertex :=
  fun h => (d.incident e h).elim h1 h2

/-- An edge of the suppressed graph is either its new edge or a retained
original edge, with the two removed edges excluded. -/
theorem SuppressionData.edge_cases (d : SuppressionData G) {e : β}
    (he : e ∈ E(d.result)) :
    e = d.fresh ∨ (e ∈ E(G) ∧ e ≠ d.first ∧ e ≠ d.second) := by
  rcases he with ⟨he, hnot⟩ | hf
  · exact Or.inr ⟨he, fun h => hnot (Or.inl h), fun h => hnot (Or.inr h)⟩
  · exact Or.inl hf

/-- The branch sets and edge map for contraction of the first edge preserve
incidence between every surviving vertex and every resulting edge. -/
theorem SuppressionData.model_incidence (d : SuppressionData G)
    {z : α} (hz : z ∈ V(d.result)) {e : β} (he : e ∈ E(d.result)) :
    d.result.Inc e z ↔
      ∃ x ∈ suppressionBranchSet d z, G.Inc (suppressionEdgeMap d e) x := by
  classical
  rcases d.edge_cases he with rfl | ⟨heG, h1, h2⟩
  · have hmap : suppressionEdgeMap d d.fresh = d.second := by
      simp only [suppressionEdgeMap, ↓reduceIte]
    rw [hmap]
    constructor
    · intro hinc
      rcases (d.inc_iff d.fresh z).1 hinc with ⟨_, hleft | hright⟩ | ⟨h, h1, h2⟩
      · exact ⟨d.vertex, Or.inr ⟨hleft, rfl⟩, d.second_link.inc_left⟩
      · exact ⟨z, Or.inl rfl, hright ▸ d.second_link.inc_right⟩
      · exact (d.retained_not_fresh h.edge_mem h1 h2 rfl).elim
    · rintro ⟨x, hx, hinc⟩
      rcases hx with rfl | ⟨hzleft, rfl⟩
      · rcases (d.second_inc_iff x).1 hinc with hxv | hxr
        · exact (hz.2 hxv).elim
        · exact (d.inc_iff _ _).2 (Or.inl ⟨rfl, Or.inr hxr⟩)
      · exact (d.inc_iff _ _).2 (Or.inl ⟨rfl, Or.inl hzleft⟩)
  · have hef := d.retained_not_fresh heG h1 h2
    have hmap : suppressionEdgeMap d e = e := by
      simp only [suppressionEdgeMap, hef, ↓reduceIte]
    rw [hmap]
    constructor
    · intro hinc
      rcases (d.inc_iff e z).1 hinc with ⟨h, _⟩ | ⟨hinc, _, _⟩
      · exact (hef h).elim
      · exact ⟨z, Or.inl rfl, hinc⟩
    · rintro ⟨x, hx, hinc⟩
      rcases hx with rfl | ⟨_, rfl⟩
      · exact (d.inc_iff _ _).2 (Or.inr ⟨hinc, h1, h2⟩)
      · exact (d.retained_not_inc h1 h2 hinc).elim

/-- The selected old edge lies in the original graph. -/
theorem SuppressionData.edgeMap_mem (d : SuppressionData G) {e : β}
    (he : e ∈ E(d.result)) : suppressionEdgeMap d e ∈ E(G) := by
  classical
  rcases d.edge_cases he with rfl | ⟨heG, h1, h2⟩
  · simpa only [suppressionEdgeMap, ↓reduceIte] using d.second_link.edge_mem
  · simpa only [suppressionEdgeMap, d.retained_not_fresh heG h1 h2, ↓reduceIte] using heG

/-- Different resulting edges are represented by different old edges. -/
theorem SuppressionData.edgeMap_injOn (d : SuppressionData G) :
    Set.InjOn (suppressionEdgeMap d) E(d.result) := by
  classical
  intro a ha b hb hab
  rcases d.edge_cases ha with rfl | ⟨haG, ha1, ha2⟩ <;>
    rcases d.edge_cases hb with rfl | ⟨hbG, hb1, hb2⟩
  · rfl
  · have hbf := d.retained_not_fresh hbG hb1 hb2
    have h : d.second = b := by
      simpa only [suppressionEdgeMap, hbf, ↓reduceIte] using hab
    exact (hb2 h.symm).elim
  · have haf := d.retained_not_fresh haG ha1 ha2
    have h : a = d.second := by
      simpa only [suppressionEdgeMap, haf, ↓reduceIte] using hab
    exact (ha2 h).elim
  · have haf := d.retained_not_fresh haG ha1 ha2
    have hbf := d.retained_not_fresh hbG hb1 hb2
    simpa only [suppressionEdgeMap, haf, hbf, ↓reduceIte] using hab

/-- Each end of a selected original edge belongs to a surviving vertex's
branch set. The removed vertex belongs to the first other end's branch set. -/
theorem SuppressionData.edgeMap_ends_covered (d : SuppressionData G)
    {e : β} (he : e ∈ E(d.result)) {x : α}
    (hx : G.Inc (suppressionEdgeMap d e) x) :
    ∃ z ∈ V(d.result), x ∈ suppressionBranchSet d z := by
  classical
  rcases d.edge_cases he with rfl | ⟨heG, h1, h2⟩
  · have hinc : G.Inc d.second x := by
      simpa only [suppressionEdgeMap, ↓reduceIte] using hx
    rcases (d.second_inc_iff x).1 hinc with rfl | rfl
    · exact ⟨d.left, ⟨d.first_link.right_mem, d.vertex_ne_left.symm⟩,
        Or.inr ⟨rfl, rfl⟩⟩
    · exact ⟨d.right, ⟨d.second_link.right_mem, d.vertex_ne_right.symm⟩,
        Or.inl rfl⟩
  · have hinc : G.Inc e x := by
      simpa only [suppressionEdgeMap, d.retained_not_fresh heG h1 h2, ↓reduceIte] using hx
    refine ⟨x, ⟨hinc.vertex_mem, ?_⟩, Or.inl rfl⟩
    intro h
    exact d.retained_not_inc h1 h2 (h ▸ hinc)

private theorem loop_iff_all_inc_eq (F : Graph α β) {e : β} (he : e ∈ E(F)) (z : α) :
    F.IsLoopAt e z ↔ ∀ x, F.Inc e x → x = z := by
  constructor
  · intro h x hx
    exact (h.eq_of_inc hx).symm
  · intro h
    obtain ⟨a, b, hab⟩ := Graph.exists_isLink_of_mem_edgeSet he
    change F.IsLink e z z
    simpa only [h a hab.inc_left, h b hab.inc_right] using hab

/-- The branch sets and edge map also preserve loops. -/
theorem SuppressionData.model_loops (d : SuppressionData G)
    {z : α} (hz : z ∈ V(d.result)) {e : β} (he : e ∈ E(d.result)) :
    d.result.IsLoopAt e z ↔
      ∀ x, G.Inc (suppressionEdgeMap d e) x → x ∈ suppressionBranchSet d z := by
  constructor
  · intro hloop x hx
    obtain ⟨a, ha, hxa⟩ := d.edgeMap_ends_covered he hx
    have hinc := (d.model_incidence ha he).2 ⟨x, hxa, hx⟩
    have heq : a = z := (hloop.eq_of_inc hinc).symm
    exact heq ▸ hxa
  · intro hends
    apply (loop_iff_all_inc_eq d.result he z).2
    intro a ha
    have haV := ha.vertex_mem
    obtain ⟨x, hx, hxe⟩ := (d.model_incidence haV he).1 ha
    by_contra haz
    exact Set.disjoint_left.1 (d.branchSet_disjoint haV hz haz) hx (hends x hxe)

/-- The first old edge is available to connect the nonsingleton branch set:
it represents no resulting edge. -/
theorem SuppressionData.first_notMem_edgeMap (d : SuppressionData G) :
    d.first ∉ suppressionEdgeMap d '' E(d.result) := by
  classical
  rintro ⟨e, he, heq⟩
  rcases d.edge_cases he with rfl | ⟨heG, h1, h2⟩
  · have h : d.second = d.first := by
      simpa only [suppressionEdgeMap, ↓reduceIte] using heq
    exact d.first_ne_second h.symm
  · have h : e = d.first := by
      simpa only [suppressionEdgeMap, d.retained_not_fresh heG h1 h2, ↓reduceIte] using heq
    exact h1 h

/-- Every branch set is connected using edges other than those that
represent resulting edges. The only nonsingleton branch uses the first edge. -/
theorem SuppressionData.branchSet_connected (d : SuppressionData G) {z : α}
    (hz : z ∈ V(d.result)) :
    ∃ K ≤ G.deleteEdges (suppressionEdgeMap d '' E(d.result)),
      V(K) = suppressionBranchSet d z ∧ GraphConnected K := by
  classical
  by_cases hzl : z = d.left
  · subst z
    let K : Graph α β := Graph.banana d.vertex d.left {d.first}
    have hKG : K ≤ G.deleteEdges (suppressionEdgeMap d '' E(d.result)) := by
      constructor
      · rintro a (rfl | rfl)
        · exact d.first_link.left_mem
        · exact d.first_link.right_mem
      · intro e a b hab
        rcases hab with ⟨rfl, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩
        · exact ⟨d.first_link, d.first_notMem_edgeMap⟩
        · exact ⟨d.first_link.symm, d.first_notMem_edgeMap⟩
    refine ⟨K, hKG, ?_, ?_⟩
    · ext a
      change (a = d.vertex ∨ a = d.left) ↔ (a = d.left ∨ (d.left = d.left ∧ a = d.vertex))
      simp only [true_and, or_comm]
    · refine ⟨⟨d.vertex, Or.inl rfl⟩, ?_⟩
      rintro a (rfl | rfl) b (rfl | rfl)
      · exact Relation.ReflTransGen.refl
      · exact Relation.ReflTransGen.single ⟨d.first, ⟨rfl, Or.inl ⟨rfl, rfl⟩⟩⟩
      · exact Relation.ReflTransGen.single ⟨d.first, ⟨rfl, Or.inr ⟨rfl, rfl⟩⟩⟩
      · exact Relation.ReflTransGen.refl
  · let K : Graph α β := Graph.noEdge {z} β
    have hKG : K ≤ G.deleteEdges (suppressionEdgeMap d '' E(d.result)) := by
      constructor
      · intro a ha
        change a = z at ha
        rw [ha]
        exact hz.1
      · intro e a b hab
        exact hab.elim
    refine ⟨K, hKG, ?_, ?_⟩
    · ext a
      change a = z ↔ (a = z ∨ (z = d.left ∧ a = d.vertex))
      simp only [hzl, false_and, or_false]
    · refine ⟨⟨z, rfl⟩, ?_⟩
      intro a ha b hb
      change a = z at ha
      change b = z at hb
      have hab : a = b := ha.trans hb.symm
      rw [hab]

/-- Contracting the first edge gives a minor model of the suppressed graph.
This includes the case where the second edge becomes a loop. -/
theorem SuppressionData.minorModel (d : SuppressionData G) :
    IsMinorModel d.result G (suppressionBranchSet d) (suppressionEdgeMap d) where
  vertex_nonempty z _ := ⟨z, d.mem_branchSet_self z⟩
  vertex_subset _ hz := d.branchSet_subset hz
  edge_mem _ he := d.edgeMap_mem he
  vertex_disjoint _ ha _ hb hab := d.branchSet_disjoint ha hb hab
  edge_injOn := d.edgeMap_injOn
  inc_iff _ hz _ he := d.model_incidence hz he
  isLoopAt_iff _ hz _ he := d.model_loops hz he
  connected _ hz := d.branchSet_connected hz

/-- Suppression gives an isomorphic minor, as observed in II, Section 4,
page 318. Its model contracts exactly the first incident edge. -/
theorem SuppressionData.isIsoMinor (d : SuppressionData G)
    (hV : V(G).Finite) (hE : E(G).Finite) : IsIsoMinor d.result G := by
  have hfinite := d.result_finite hV hE
  exact isIsoMinor_of_isMinorModel d.result G hfinite.1 hfinite.2 hV hE _ _ d.minorModel

/-- A graph obtained by repeated suppressions of a subgraph is an
isomorphic minor, as observed in II, Section 4, page 318. -/
theorem TopologicallyContains.isIsoMinor {H : Graph α β}
    (h : TopologicallyContains G H) (hV : V(G).Finite) (hE : E(G).Finite) :
    IsIsoMinor H G := by
  obtain ⟨K, hK, L, hs, φ, hφ⟩ := h
  have hVK := hV.subset hK.vertexSet_mono
  have hEK := hE.subset hK.edgeSet_mono
  have hchain : V(L).Finite ∧ E(L).Finite ∧ IsIsoMinor L K := by
    clear hφ φ
    induction hs with
    | refl => exact ⟨hVK, hEK, IsIsoMinor.refl K⟩
    | tail _ hstep ih =>
      obtain ⟨d, rfl⟩ := hstep
      have hfinite := d.result_finite ih.1 ih.2.1
      exact ⟨hfinite.1, hfinite.2, (d.isIsoMinor ih.1 ih.2.1).trans ih.2.2⟩
  have hKG : IsIsoMinor K G := by
    obtain ⟨K', hK', C, hC, hφ⟩ := IsIsoMinor.refl K
    exact ⟨K', hK'.trans hK, C, hC, hφ⟩
  exact (φ.isIsoMinor_left hchain.2.2).trans hKG

end GraphMinor.GM02
