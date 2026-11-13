module

public import GraphMinor.Minor.Basic
import Mathlib.Data.Set.Card

/-!
# Suppression and topological containment in Graph Minors II

Section 4 defines suppression at a vertex incident with exactly two distinct
non-loop edges. Delete that vertex and replace those two edges by one fresh
edge between their other ends. The other ends may coincide, so the new edge
may be a loop. Repeated suppression of a subgraph is topological containment.
-/

@[expose] public section

namespace GraphMinor.GM02

open Graph Set Relation

universe u v

variable {α : Type u} {β : Type v}

/-- Graph Minors II, Section 4, page 318: the data for suppressing a vertex
incident with only two edges, neither a loop. The fresh edge joins the other
ends of these edges. The two other ends are allowed to coincide. -/
structure SuppressionData (G : Graph α β) where
  /-- Vertex to remove. -/
  vertex : α
  /-- Other end of the first edge. -/
  left : α
  /-- Other end of the second edge. -/
  right : α
  /-- First incident edge. -/
  first : β
  /-- Second incident edge. -/
  second : β
  /-- New replacement edge. -/
  fresh : β
  /-- The two incident edges are distinct. -/
  first_ne_second : first ≠ second
  /-- The first edge joins the removed vertex to its other end. -/
  first_link : G.IsLink first vertex left
  /-- The second edge joins the removed vertex to its other end. -/
  second_link : G.IsLink second vertex right
  /-- The first edge is not a loop. -/
  vertex_ne_left : vertex ≠ left
  /-- The second edge is not a loop. -/
  vertex_ne_right : vertex ≠ right
  /-- No other edge is incident with the removed vertex. -/
  incident : ∀ e, G.Inc e vertex → e = first ∨ e = second
  /-- The replacement edge has a name not used by any retained edge. -/
  fresh_notMem : fresh ∉ E(G) \ {first, second}

/-- The result of suppression, Graph Minors II, Section 4, page 318:
"The result of suppressing $v$ is the graph obtained from $G$ by deleting
$v$ and adding a new edge with ends $v_1, v_2$." -/
def SuppressionData.result {G : Graph α β} (d : SuppressionData G) : Graph α β where
  vertexSet := V(G) \ {d.vertex}
  edgeSet := (E(G) \ {d.first, d.second}) ∪ {d.fresh}
  IsLink e a b :=
    (G.IsLink e a b ∧ e ≠ d.first ∧ e ≠ d.second) ∨
      (e = d.fresh ∧ ((a = d.left ∧ b = d.right) ∨ (a = d.right ∧ b = d.left)))
  isLink_symm := by
    intro e _
    refine ⟨?_⟩
    intro a b h
    rcases h with ⟨h, h1, h2⟩ | ⟨rfl, h | h⟩
    · exact Or.inl ⟨h.symm, h1, h2⟩
    · exact Or.inr ⟨rfl, Or.inr ⟨h.2, h.1⟩⟩
    · exact Or.inr ⟨rfl, Or.inl ⟨h.2, h.1⟩⟩
  eq_or_eq_of_isLink_of_isLink := by
    intro e a b c f h h'
    rcases h with ⟨hab, h1, h2⟩ | ⟨he, h⟩
    · rcases h' with ⟨hcf, _, _⟩ | ⟨he, _⟩
      · exact hab.left_eq_or_eq hcf
      · exact (d.fresh_notMem (he ▸ ⟨hab.edge_mem, fun h => h.elim h1 h2⟩)).elim
    · rcases h' with ⟨hcf, h1, h2⟩ | ⟨_, h'⟩
      · exact (d.fresh_notMem (he ▸ ⟨hcf.edge_mem, fun h => h.elim h1 h2⟩)).elim
      · rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
          rcases h' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact Or.inl rfl
        · exact Or.inr rfl
        · exact Or.inr rfl
        · exact Or.inl rfl
  edge_mem_iff_exists_isLink := by
    intro e
    constructor
    · rintro (⟨he, hnot⟩ | rfl)
      · obtain ⟨a, b, hab⟩ := Graph.exists_isLink_of_mem_edgeSet he
        refine ⟨a, b, Or.inl ⟨hab, ?_, ?_⟩⟩ <;> intro heq <;> apply hnot
        · exact Or.inl heq
        · exact Or.inr heq
      · exact ⟨d.left, d.right, Or.inr ⟨rfl, Or.inl ⟨rfl, rfl⟩⟩⟩
    · rintro ⟨a, b, ⟨hab, h1, h2⟩ | ⟨rfl, _⟩⟩
      · exact Or.inl ⟨hab.edge_mem, fun h => h.elim h1 h2⟩
      · exact Or.inr rfl
  left_mem_of_isLink := by
    intro e a b h
    rcases h with ⟨hab, h1, h2⟩ | ⟨_, ⟨rfl, _⟩ | ⟨rfl, _⟩⟩
    · refine ⟨hab.left_mem, ?_⟩
      intro heq
      have hinc : G.Inc e d.vertex := heq ▸ hab.inc_left
      exact (d.incident e hinc).elim h1 h2
    · exact ⟨d.first_link.right_mem, d.vertex_ne_left.symm⟩
    · exact ⟨d.second_link.right_mem, d.vertex_ne_right.symm⟩

/-- One suppression as defined in II, Section 4, page 318. -/
def IsSuppression (G H : Graph α β) : Prop :=
  ∃ d : SuppressionData G, H = d.result

/-- Graph Minors II, Section 4, page 318:
"We say that $G$ topologically contains $H$ if $H$ can be obtained from a
subgraph of $G$ by repeated suppression."

The identification of the result with `H` fixes its vertices. Edge names
may change, as when the paper deletes different named loops in (4.3). -/
def TopologicallyContains (G H : Graph α β) : Prop :=
  ∃ K ≤ G, ∃ L, ReflTransGen IsSuppression K L ∧
    ∃ φ : Iso H L, ∀ v : V(H), (φ.vertexEquiv v).val = v.val

/-- Suppression removes one vertex and introduces no vertex. -/
theorem IsSuppression.vertexSet_subset {G H : Graph α β} (h : IsSuppression G H) :
    V(H) ⊆ V(G) := by
  obtain ⟨d, rfl⟩ := h
  exact sdiff_subset

/-- The retained edges are exactly the old edges other than the two removed
edges. In particular, the fresh edge cannot also be a retained edge. -/
theorem SuppressionData.retained_not_fresh {G : Graph α β} (d : SuppressionData G)
    {e : β} (he : e ∈ E(G)) (h1 : e ≠ d.first) (h2 : e ≠ d.second) :
    e ≠ d.fresh := by
  intro h
  exact d.fresh_notMem (h ▸ ⟨he, fun h => h.elim h1 h2⟩)

/-- The new edge has exactly the specified ends, including when it is a loop. -/
theorem SuppressionData.fresh_isLink_iff {G : Graph α β} (d : SuppressionData G)
    (a b : α) :
    d.result.IsLink d.fresh a b ↔
      (a = d.left ∧ b = d.right) ∨ (a = d.right ∧ b = d.left) := by
  constructor
  · rintro (⟨hab, h1, h2⟩ | ⟨_, hab⟩)
    · exact (d.retained_not_fresh hab.edge_mem h1 h2 rfl).elim
    · exact hab
  · intro hab
    exact Or.inr ⟨rfl, hab⟩

/-- A retained edge has its original ends after suppression. -/
theorem SuppressionData.retained_isLink_iff {G : Graph α β} (d : SuppressionData G)
    {e : β} (he : e ≠ d.fresh) (a b : α) :
    d.result.IsLink e a b ↔ G.IsLink e a b ∧ e ≠ d.first ∧ e ≠ d.second := by
  constructor
  · rintro (h | ⟨hf, _⟩)
    · exact h
    · exact (he hf).elim
  · exact Or.inl

/-- Incidence after suppression distinguishes the new edge from retained
edges. The new edge may have only one end if its two specified ends agree. -/
theorem SuppressionData.inc_iff {G : Graph α β} (d : SuppressionData G)
    (e : β) (a : α) :
    d.result.Inc e a ↔
      (e = d.fresh ∧ (a = d.left ∨ a = d.right)) ∨
      (G.Inc e a ∧ e ≠ d.first ∧ e ≠ d.second) := by
  constructor
  · rintro ⟨b, ⟨hab, h1, h2⟩ | ⟨he, hab | hab⟩⟩
    · exact Or.inr ⟨hab.inc_left, h1, h2⟩
    · exact Or.inl ⟨he, Or.inl hab.1⟩
    · exact Or.inl ⟨he, Or.inr hab.1⟩
  · rintro (⟨rfl, rfl | rfl⟩ | ⟨⟨b, hab⟩, h1, h2⟩)
    · exact ⟨d.right, Or.inr ⟨rfl, Or.inl ⟨rfl, rfl⟩⟩⟩
    · exact ⟨d.left, Or.inr ⟨rfl, Or.inr ⟨rfl, rfl⟩⟩⟩
    · exact ⟨b, Or.inl ⟨hab, h1, h2⟩⟩

/-- Suppression of a finite graph leaves finitely many vertices and edges. -/
theorem SuppressionData.result_finite {G : Graph α β} (d : SuppressionData G)
    (hV : V(G).Finite) (hE : E(G).Finite) :
    V(d.result).Finite ∧ E(d.result).Finite :=
  ⟨hV.sdiff, hE.sdiff.union (Set.finite_singleton _)⟩

/-- A suppression decreases the vertex count by exactly one. -/
theorem SuppressionData.ncard_vertexSet {G : Graph α β} (d : SuppressionData G)
    (hV : V(G).Finite) : V(d.result).ncard + 1 = V(G).ncard :=
  Set.ncard_sdiff_singleton_add_one d.first_link.left_mem hV

/-- A subgraph is topologically contained using no suppressions. -/
theorem topologicallyContains_of_le {G H : Graph α β} (h : H ≤ G) :
    TopologicallyContains G H :=
  ⟨H, h, H, ReflTransGen.refl,
    ⟨Equiv.refl _, Equiv.refl _, fun _ _ _ => Iff.rfl⟩, fun _ => rfl⟩

/-- Topological containment can be viewed in any larger ambient graph. -/
theorem TopologicallyContains.mono {G G' H : Graph α β}
    (h : TopologicallyContains G H) (hGG' : G ≤ G') : TopologicallyContains G' H := by
  obtain ⟨K, hK, L, hs, φ, hφ⟩ := h
  exact ⟨K, hK.trans hGG', L, hs, φ, hφ⟩

/-- Every vertex of a topologically contained graph is an original vertex,
as observed in II, Section 4, page 318. -/
theorem TopologicallyContains.vertexSet_subset {G H : Graph α β}
    (h : TopologicallyContains G H) : V(H) ⊆ V(G) := by
  obtain ⟨K, hK, L, hs, φ, hφ⟩ := h
  have hsub : V(L) ⊆ V(K) := by
    clear φ hφ
    induction hs with
    | refl => exact Subset.refl _
    | tail _ hstep ih => exact hstep.vertexSet_subset.trans ih
  intro v hv
  have hvL : v ∈ V(L) := by
    have hmem := (φ.vertexEquiv ⟨v, hv⟩).property
    change (φ.vertexEquiv ⟨v, hv⟩).val ∈ V(L) at hmem
    simpa only [hφ] using hmem
  exact hK.vertexSet_mono (hsub hvL)

end GraphMinor.GM02
