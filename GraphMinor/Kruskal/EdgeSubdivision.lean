module

public import GraphMinor.Kruskal.TopologicalTransport

/-!
# Constructing a single edge subdivision

Graph Minors IV, Section 1, page 229 replaces an edge by two edges in series.
We construct that graph explicitly and prove that fresh vertex and edge
names give a step of `GM04.IsEdgeSubdivision`. The construction also permits
a loop as the edge being replaced.
-/

@[expose] public section

namespace GraphMinor.Kruskal

open Graph Set

/-- Replace `e` with links from `u` to `a` and from `a` to `v`, using the
new names `f` and `g`. Distinct edge names keep their ends unambiguous. -/
noncomputable def subdivideEdge {α β : Type*} (G : Graph α β)
    (e : β) (u v a : α) (f g : β) (hlink : G.IsLink e u v) (_hfg : f ≠ g) :
    Graph α β := by
  classical
  exact {
    vertexSet := insert a V(G)
    edgeSet := insert f (insert g (E(G) \ {e}))
    IsLink := fun d x y ↦
      if d = f then (x = u ∧ y = a) ∨ (x = a ∧ y = u)
      else if d = g then (x = a ∧ y = v) ∨ (x = v ∧ y = a)
      else d ≠ e ∧ G.IsLink d x y
    isLink_symm := by
      intro d hd
      constructor
      intro x y h
      split_ifs at h ⊢ <;> first
        | exact h.elim (fun h ↦ Or.inr h.symm) (fun h ↦ Or.inl h.symm)
        | exact ⟨h.1, h.2.symm⟩
    eq_or_eq_of_isLink_of_isLink := by
      intro d x y z w h₁ h₂
      split_ifs at h₁ h₂
      · rcases h₁ with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
          rcases h₂ with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp
      · rcases h₁ with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
          rcases h₂ with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp
      · exact h₁.2.left_eq_or_eq h₂.2
    edge_mem_iff_exists_isLink := by
      intro d
      by_cases hdf : d = f
      · subst d
        simp only [mem_insert_iff, true_or, ↓reduceIte]
        exact ⟨fun _ ↦ ⟨u, a, Or.inl ⟨rfl, rfl⟩⟩, fun _ ↦ trivial⟩
      · by_cases hdg : d = g
        · subst d
          simp only [hdf, ↓reduceIte, mem_insert_iff, true_or, or_true]
          exact ⟨fun _ ↦ ⟨a, v, Or.inl ⟨rfl, rfl⟩⟩, fun _ ↦ trivial⟩
        · simp only [hdf, hdg, ↓reduceIte, mem_insert_iff, false_or,
            mem_sdiff, mem_singleton_iff]
          constructor
          · rintro ⟨hd, hde⟩
            obtain ⟨x, y, hxy⟩ := G.exists_isLink_of_mem_edgeSet hd
            exact ⟨x, y, hde, hxy⟩
          · rintro ⟨x, y, hde, hxy⟩
            exact ⟨hxy.edge_mem, hde⟩
    left_mem_of_isLink := by
      intro d x y h
      split_ifs at h
      · rcases h with ⟨rfl, _⟩ | ⟨rfl, _⟩
        · exact mem_insert_of_mem _ hlink.left_mem
        · exact mem_insert _ _
      · rcases h with ⟨rfl, _⟩ | ⟨rfl, _⟩
        · exact mem_insert _ _
        · exact mem_insert_of_mem _ hlink.right_mem
      · exact mem_insert_of_mem _ h.2.left_mem }

/-- With fresh names, the explicit edge replacement is a subdivision step
in the sense of Graph Minors IV. -/
theorem isEdgeSubdivision_subdivideEdge {α β : Type*} (G : Graph α β)
    (e : β) (u v a : α) (f g : β) (hlink : G.IsLink e u v)
    (ha : a ∉ V(G)) (hf : f ∉ E(G)) (hg : g ∉ E(G)) (hfg : f ≠ g) :
    GM04.IsEdgeSubdivision G (subdivideEdge G e u v a f g hlink hfg) := by
  classical
  refine ⟨e, u, v, a, f, g, hlink, ha, hf, hg, hfg, rfl, rfl, ?_⟩
  intro d x y
  change (if d = f then _ else if d = g then _ else _) ↔ _
  by_cases hdf : d = f
  · subst d
    have hfalse : ¬ G.IsLink f x y := fun h ↦ hf h.edge_mem
    simp only [↓reduceIte, hfg, false_and, or_false, hfalse, and_false, false_or,
      true_and]
  · by_cases hdg : d = g
    · subst d
      have hfalse : ¬ G.IsLink g x y := fun h ↦ hg h.edge_mem
      simp only [hdf, ↓reduceIte, false_and, false_or, hfalse, and_false, true_and]
    · simp only [hdf, hdg, ↓reduceIte, false_and, or_false]

/-- Edge and vertex finiteness are preserved by one subdivision. -/
theorem subdivideEdge_finite {α β : Type*} (G : Graph α β)
    (e : β) (u v a : α) (f g : β) (hlink : G.IsLink e u v) (hfg : f ≠ g)
    (hV : V(G).Finite) (hE : E(G).Finite) :
    V(subdivideEdge G e u v a f g hlink hfg).Finite ∧
      E(subdivideEdge G e u v a f g hlink hfg).Finite :=
  ⟨hV.insert _, (hE.sdiff.insert _).insert _⟩

end GraphMinor.Kruskal
