module

public import GraphMinor.GM13.Defs

/-!
# Transport of graphs along injective relabellings

Algorithm (9.9) of Graph Minors XIII (page 104) works on a sequence of graphs `G_1, G_2, …`, each
a subgraph of the input graph `G`. The program stores `G_i` renumbered on `Fin v_i`, with a map
`orig` back to the labels of `G`. So every fact proved about `G_i` in its own labels must be
carried back to the labels of `G`. This file gives the basic tool for that.

For embeddings `f : α ↪ α'` of vertex labels and `g : β ↪ β'` of edge labels, `relabelGraph f g G`
is the graph `G` with every vertex `x` renamed `f x` and every edge `e` renamed `g e`. It is
isomorphic to `G` (`relabelGraphIso`). We show that renaming commutes with the operations used in
Section 9 of Graph Minors XIII (subgraphs, induced subgraphs, restrictions, deletion of vertices,
unions of families of subgraphs), and that it carries walks, paths and `H`-paths in both
directions. A subgraph of a renamed graph is itself a renamed subgraph (`relabelGraph_comapGraph`),
which gives the backward direction of each statement.

Walls, compasses, flat walls, dividing subwalls, wall societies, rural divisions and
branch-decompositions are treated in `Algorithm99TransportWall.lean` and
`Algorithm99TransportSociety.lean`.
-/

@[expose] public section

namespace GraphMinor.Transport

open Graph Function Set GraphMinor.Surface GraphMinor.GM09 GraphMinor.GM14

universe u u' v v'

variable {α : Type u} {α' : Type u'} {β : Type v} {β' : Type v'}

/-! ### Renaming a graph -/

/-- The graph `G` with each vertex `x` renamed `f x` and each edge `e` renamed `g e`. -/
def relabelGraph (f : α ↪ α') (g : β ↪ β') (G : Graph α β) : Graph α' β' where
  vertexSet := f '' V(G)
  IsLink e' x' y' := ∃ e x y, G.IsLink e x y ∧ g e = e' ∧ f x = x' ∧ f y = y'
  edgeSet := g '' E(G)
  isLink_symm := by
    rintro _ -
    exact ⟨fun _ _ ⟨e, x, y, h, he, hx, hy⟩ => ⟨e, y, x, h.symm, he, hy, hx⟩⟩
  eq_or_eq_of_isLink_of_isLink := by
    rintro _ _ _ _ _ ⟨e, x, y, h, rfl, rfl, rfl⟩ ⟨e₂, v, w, h₂, he, rfl, rfl⟩
    obtain rfl := g.injective he
    rcases h.left_eq_or_eq h₂ with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr rfl
  edge_mem_iff_exists_isLink := by
    intro e'
    constructor
    · rintro ⟨e, he, rfl⟩
      obtain ⟨x, y, h⟩ := G.exists_isLink_of_mem_edgeSet he
      exact ⟨f x, f y, e, x, y, h, rfl, rfl, rfl⟩
    · rintro ⟨_, _, e, x, y, h, rfl, -, -⟩
      exact ⟨e, h.edge_mem, rfl⟩
  left_mem_of_isLink := by
    rintro _ _ _ ⟨e, x, y, h, -, rfl, -⟩
    exact ⟨x, h.left_mem, rfl⟩

variable (f : α ↪ α') (g : β ↪ β') {G H P : Graph α β}

@[simp]
theorem vertexSet_relabelGraph : V(relabelGraph f g G) = f '' V(G) := rfl

@[simp]
theorem edgeSet_relabelGraph : E(relabelGraph f g G) = g '' E(G) := rfl

theorem relabelGraph_isLink {e' : β'} {x' y' : α'} :
    (relabelGraph f g G).IsLink e' x' y' ↔
      ∃ e x y, G.IsLink e x y ∧ g e = e' ∧ f x = x' ∧ f y = y' := Iff.rfl

@[simp]
theorem relabelGraph_isLink_apply {e : β} {x y : α} :
    (relabelGraph f g G).IsLink (g e) (f x) (f y) ↔ G.IsLink e x y := by
  refine ⟨?_, fun h => ⟨e, x, y, h, rfl, rfl, rfl⟩⟩
  rintro ⟨e₀, x₀, y₀, h, he, hx, hy⟩
  rw [g.injective he, f.injective hx, f.injective hy] at h
  exact h

@[simp]
theorem mem_vertexSet_relabelGraph_apply {x : α} : f x ∈ V(relabelGraph f g G) ↔ x ∈ V(G) :=
  f.injective.mem_set_image

@[simp]
theorem mem_edgeSet_relabelGraph_apply {e : β} : g e ∈ E(relabelGraph f g G) ↔ e ∈ E(G) :=
  g.injective.mem_set_image

/-- Every link of a renamed graph is the renaming of a link. -/
theorem exists_eq_of_relabelGraph_isLink {e' : β'} {x' y' : α'}
    (h : (relabelGraph f g G).IsLink e' x' y') :
    ∃ e x y, G.IsLink e x y ∧ g e = e' ∧ f x = x' ∧ f y = y' := h

theorem relabelGraph_inc_apply {e : β} {x : α} :
    (relabelGraph f g G).Inc (g e) (f x) ↔ G.Inc e x := by
  constructor
  · rintro ⟨y', hy'⟩
    obtain ⟨e₀, x₀, y₀, h, he, hx, rfl⟩ := hy'
    rw [g.injective he, f.injective hx] at h
    exact ⟨y₀, h⟩
  · rintro ⟨y, hy⟩
    exact ⟨f y, (relabelGraph_isLink_apply f g).2 hy⟩

theorem relabelGraph_mono (h : H ≤ G) : relabelGraph f g H ≤ relabelGraph f g G where
  vertexSet_mono := Set.image_mono h.vertexSet_mono
  isLink_mono := by
    rintro _ _ _ ⟨e, x, y, hl, rfl, rfl, rfl⟩
    exact ⟨e, x, y, hl.mono h, rfl, rfl, rfl⟩

@[simp]
theorem relabelGraph_le_relabelGraph_iff : relabelGraph f g H ≤ relabelGraph f g G ↔ H ≤ G := by
  refine ⟨fun h => ?_, relabelGraph_mono f g⟩
  refine ⟨fun x hx => ?_, fun e x y hl => ?_⟩
  · exact (mem_vertexSet_relabelGraph_apply f g).1 (h.vertexSet_mono ⟨x, hx, rfl⟩)
  · exact (relabelGraph_isLink_apply f g).1 (h.isLink_mono ((relabelGraph_isLink_apply f g).2 hl))

theorem relabelGraph_injective : Injective (fun G : Graph α β => relabelGraph f g G) := by
  intro H G h
  have h' : relabelGraph f g H = relabelGraph f g G := h
  exact le_antisymm ((relabelGraph_le_relabelGraph_iff f g).1 h'.le)
    ((relabelGraph_le_relabelGraph_iff f g).1 h'.ge)

@[simp]
theorem relabelGraph_inj : relabelGraph f g H = relabelGraph f g G ↔ H = G :=
  (relabelGraph_injective f g).eq_iff

/-! ### Pulling a subgraph back -/

/-- The graph on `α, β` whose renaming is `P`, when `P` is a subgraph of a renamed graph
(`relabelGraph_comapGraph`): a vertex `x` is kept if `f x ∈ V(P)`, and `e` links `x, y` if `g e`
links `f x, f y` in `P`. -/
def comapGraph (P : Graph α' β') : Graph α β where
  vertexSet := f ⁻¹' V(P)
  IsLink e x y := P.IsLink (g e) (f x) (f y)
  isLink_symm := by
    rintro _ -
    exact ⟨fun _ _ h => h.symm⟩
  eq_or_eq_of_isLink_of_isLink := by
    intro e x y v w h₁ h₂
    rcases h₁.left_eq_or_eq h₂ with h | h
    · exact Or.inl (f.injective h)
    · exact Or.inr (f.injective h)
  left_mem_of_isLink := by
    intro e x y h
    exact h.left_mem

@[simp]
theorem comapGraph_isLink {P : Graph α' β'} {e : β} {x y : α} :
    (comapGraph f g P).IsLink e x y ↔ P.IsLink (g e) (f x) (f y) := Iff.rfl

@[simp]
theorem vertexSet_comapGraph {P : Graph α' β'} : V(comapGraph f g P) = f ⁻¹' V(P) := rfl

/-- A subgraph of a renamed graph is the renaming of its pull-back. -/
theorem relabelGraph_comapGraph {P : Graph α' β'} (hP : P ≤ relabelGraph f g G) :
    relabelGraph f g (comapGraph f g P) = P := by
  refine Graph.ext ?_ ?_
  · ext x'
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact hx
    · intro hx
      obtain ⟨x, -, rfl⟩ := hP.vertexSet_mono hx
      exact ⟨x, hx, rfl⟩
  · intro e' x' y'
    constructor
    · rintro ⟨e, x, y, hl, rfl, rfl, rfl⟩
      exact hl
    · intro hl
      obtain ⟨e, x, y, -, rfl, rfl, rfl⟩ := hl.mono hP
      exact ⟨e, x, y, hl, rfl, rfl, rfl⟩

theorem comapGraph_le {P : Graph α' β'} (hP : P ≤ relabelGraph f g G) :
    comapGraph f g P ≤ G := by
  rw [← relabelGraph_le_relabelGraph_iff f g, relabelGraph_comapGraph f g hP]
  exact hP

@[simp]
theorem comapGraph_relabelGraph : comapGraph f g (relabelGraph f g G) = G :=
  (relabelGraph_injective f g) (relabelGraph_comapGraph f g le_rfl)

/-- Every subgraph of `relabelGraph f g G` is `relabelGraph f g P` for a subgraph `P ≤ G`. -/
theorem exists_eq_relabelGraph_of_le {P' : Graph α' β'} (hP : P' ≤ relabelGraph f g G) :
    ∃ P ≤ G, relabelGraph f g P = P' :=
  ⟨comapGraph f g P', comapGraph_le f g hP, relabelGraph_comapGraph f g hP⟩

/-! ### Renaming commutes with the graph operations of the papers -/

theorem relabelGraph_induce (X : Set α) :
    relabelGraph f g (G.induce X) = (relabelGraph f g G).induce (f '' X) := by
  refine Graph.ext rfl ?_
  intro e' x' y'
  constructor
  · rintro ⟨e, x, y, ⟨hl, hx, hy⟩, rfl, rfl, rfl⟩
    exact ⟨⟨e, x, y, hl, rfl, rfl, rfl⟩, ⟨x, hx, rfl⟩, ⟨y, hy, rfl⟩⟩
  · rintro ⟨⟨e, x, y, hl, rfl, rfl, rfl⟩, hx, hy⟩
    exact ⟨e, x, y, ⟨hl, f.injective.mem_set_image.1 hx, f.injective.mem_set_image.1 hy⟩,
      rfl, rfl, rfl⟩

theorem relabelGraph_restrict (E₀ : Set β) :
    relabelGraph f g (G.restrict E₀) = (relabelGraph f g G).restrict (g '' E₀) := by
  refine Graph.ext rfl ?_
  intro e' x' y'
  constructor
  · rintro ⟨e, x, y, ⟨he, hl⟩, rfl, rfl, rfl⟩
    exact ⟨⟨e, he, rfl⟩, e, x, y, hl, rfl, rfl, rfl⟩
  · rintro ⟨he, e, x, y, hl, rfl, rfl, rfl⟩
    exact ⟨e, x, y, ⟨g.injective.mem_set_image.1 he, hl⟩, rfl, rfl, rfl⟩

theorem relabelGraph_deleteVertices (X : Set α) :
    relabelGraph f g (GM09.deleteVertices G X) =
      GM09.deleteVertices (relabelGraph f g G) (f '' X) := by
  unfold GM09.deleteVertices
  rw [relabelGraph_induce, vertexSet_relabelGraph, Set.image_sdiff f.injective]

theorem relabelGraph_subgraphSUnion (Ps : Set (Graph α β)) :
    relabelGraph f g (subgraphSUnion G Ps) =
      subgraphSUnion (relabelGraph f g G) (relabelGraph f g '' Ps) := by
  unfold subgraphSUnion
  rw [relabelGraph_restrict, relabelGraph_induce, Set.image_iUnion₂, Set.image_iUnion₂]
  simp only [Set.biUnion_image, vertexSet_relabelGraph, edgeSet_relabelGraph]

theorem relabelGraph_subgraphUnion (G₁ G₂ : Graph α β) :
    relabelGraph f g (subgraphUnion G G₁ G₂) =
      subgraphUnion (relabelGraph f g G) (relabelGraph f g G₁) (relabelGraph f g G₂) := by
  unfold subgraphUnion
  rw [relabelGraph_restrict, relabelGraph_induce, Set.image_union, Set.image_union]
  rfl

theorem relabelGraph_subgraphInter (G₁ G₂ : Graph α β) :
    relabelGraph f g (subgraphInter G G₁ G₂) =
      subgraphInter (relabelGraph f g G) (relabelGraph f g G₁) (relabelGraph f g G₂) := by
  unfold subgraphInter
  rw [relabelGraph_restrict, relabelGraph_induce, Set.image_inter f.injective,
    Set.image_inter g.injective]
  rfl

/-! ### The renaming is an isomorphism -/

/-- `G` is isomorphic to its renaming, by `x ↦ f x` and `e ↦ g e`. -/
noncomputable def relabelGraphIso (G : Graph α β) : GraphMinor.Iso G (relabelGraph f g G) where
  vertexEquiv := Equiv.Set.image f V(G) f.injective
  edgeEquiv := Equiv.Set.image g E(G) g.injective
  isLink_iff _ _ _ := (relabelGraph_isLink_apply f g).symm

@[simp]
theorem relabelGraphIso_vertexEquiv_apply (x : V(G)) :
    ((relabelGraphIso f g G).vertexEquiv x).1 = f x.1 := rfl

@[simp]
theorem relabelGraphIso_edgeEquiv_apply (e : E(G)) :
    ((relabelGraphIso f g G).edgeEquiv e).1 = g e.1 := rfl

/-! ### Walks and paths -/

/-- The renaming of a walk. -/
def relabelWalk : {u w : α} → GraphWalk G u w → GraphWalk (relabelGraph f g G) (f u) (f w)
  | _, _, .nil hv => .nil ⟨_, hv, rfl⟩
  | _, _, .cons hlink rest => .cons ((relabelGraph_isLink_apply f g).2 hlink) (relabelWalk rest)

@[simp]
theorem support_relabelWalk {u w : α} (W : GraphWalk G u w) :
    (relabelWalk f g W).support = W.support.map f := by
  induction W with
  | nil hv => rfl
  | cons hlink rest ih => simp [relabelWalk, GraphWalk.support, ih]

@[simp]
theorem edges_relabelWalk {u w : α} (W : GraphWalk G u w) :
    (relabelWalk f g W).edges = W.edges.map g := by
  induction W with
  | nil hv => rfl
  | cons hlink rest ih => simp [relabelWalk, GraphWalk.edges, ih]

/-- A walk of a renamed graph that starts at `f u` is the renaming of a walk of `G`. -/
theorem exists_walk_of_relabelWalk {u : α} {w' : α'}
    (W' : GraphWalk (relabelGraph f g G) (f u) w') :
    ∃ w, f w = w' ∧ ∃ W : GraphWalk G u w,
      W.support.map f = W'.support ∧ W.edges.map g = W'.edges := by
  suffices key : ∀ {u' w' : α'} (W' : GraphWalk (relabelGraph f g G) u' w') (u : α), f u = u' →
      ∃ w, f w = w' ∧ ∃ W : GraphWalk G u w,
        W.support.map f = W'.support ∧ W.edges.map g = W'.edges from key W' u rfl
  intro u' w' W'
  induction W' with
  | nil hv =>
    intro u hu
    subst hu
    exact ⟨u, rfl, .nil ((mem_vertexSet_relabelGraph_apply f g).1 hv), rfl, rfl⟩
  | cons hlink rest ih =>
    intro u hu
    subst hu
    obtain ⟨e, x, y, hl, rfl, hx, rfl⟩ := hlink
    obtain rfl := f.injective hx
    obtain ⟨w, hw, W, hs, he⟩ := ih y rfl
    exact ⟨w, hw, .cons hl W, by simp [GraphWalk.support, hs],
      by simp [GraphWalk.edges, he]⟩

theorem isSimple_relabelWalk_iff {u w : α} (W : GraphWalk G u w) :
    (relabelWalk f g W).IsSimple ↔ W.IsSimple := by
  unfold GraphWalk.IsSimple
  rw [support_relabelWalk]
  exact List.nodup_map_iff f.injective

theorem isGraphPathWithEnds_relabelGraph {a b : α} (h : IsGraphPathWithEnds G P a b) :
    IsGraphPathWithEnds (relabelGraph f g G) (relabelGraph f g P) (f a) (f b) := by
  obtain ⟨hle, W, hW, hV, hE⟩ := h
  refine ⟨relabelGraph_mono f g hle, relabelWalk f g W, (isSimple_relabelWalk_iff f g W).2 hW,
    ?_, ?_⟩
  · ext x'
    simp only [vertexSet_relabelGraph, hV, support_relabelWalk, List.mem_map]
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨x, hx, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨x, hx, rfl⟩
  · ext e'
    simp only [edgeSet_relabelGraph, hE, edges_relabelWalk, List.mem_map]
    constructor
    · rintro ⟨e, he, rfl⟩
      exact ⟨e, he, rfl⟩
    · rintro ⟨e, he, rfl⟩
      exact ⟨e, he, rfl⟩

theorem isGraphPathWithEnds_of_relabelGraph {a b : α}
    (h : IsGraphPathWithEnds (relabelGraph f g G) (relabelGraph f g P) (f a) (f b)) :
    IsGraphPathWithEnds G P a b := by
  obtain ⟨hle, W', hW', hV, hE⟩ := h
  obtain ⟨w, hw, W, hs, he⟩ := exists_walk_of_relabelWalk f g W'
  obtain rfl := f.injective hw
  refine ⟨(relabelGraph_le_relabelGraph_iff f g).1 hle, W, ?_, ?_, ?_⟩
  · unfold GraphWalk.IsSimple
    rw [← List.nodup_map_iff f.injective, hs]
    exact hW'
  · ext x
    have hx := congrArg (f x ∈ ·) hV
    simp only [vertexSet_relabelGraph, f.injective.mem_set_image, eq_iff_iff] at hx
    rw [hx, ← hs]
    exact List.mem_map_of_injective f.injective
  · ext e
    have he' := congrArg (g e ∈ ·) hE
    simp only [edgeSet_relabelGraph, g.injective.mem_set_image, eq_iff_iff] at he'
    rw [he', ← he]
    exact List.mem_map_of_injective g.injective

@[simp]
theorem isGraphPathWithEnds_relabelGraph_iff {a b : α} :
    IsGraphPathWithEnds (relabelGraph f g G) (relabelGraph f g P) (f a) (f b) ↔
      IsGraphPathWithEnds G P a b :=
  ⟨isGraphPathWithEnds_of_relabelGraph f g, isGraphPathWithEnds_relabelGraph f g⟩

private theorem end_mem_support {G' : Graph α' β'} {u w : α'} (W : GraphWalk G' u w) :
    w ∈ W.support := by
  induction W with
  | nil hv => simp [GraphWalk.support]
  | cons hlink rest ih => simp [GraphWalk.support, ih]

/-- A path of a renamed graph is the renaming of a path, with renamed ends. -/
theorem exists_of_isGraphPathWithEnds_relabelGraph {P' : Graph α' β'} {a' b' : α'}
    (h : IsGraphPathWithEnds (relabelGraph f g G) P' a' b') :
    ∃ P a b, relabelGraph f g P = P' ∧ f a = a' ∧ f b = b' ∧ IsGraphPathWithEnds G P a b := by
  obtain ⟨P, -, rfl⟩ := exists_eq_relabelGraph_of_le f g h.1
  have ha : a' ∈ V(relabelGraph f g P) := by
    obtain ⟨-, W, -, hV, -⟩ := h
    rw [hV]
    cases W <;> simp [GraphWalk.support]
  have hb : b' ∈ V(relabelGraph f g P) := by
    obtain ⟨-, W, -, hV, -⟩ := h
    rw [hV]
    exact end_mem_support W
  obtain ⟨a, -, rfl⟩ := ha
  obtain ⟨b, -, rfl⟩ := hb
  exact ⟨P, a, b, rfl, rfl, rfl, (isGraphPathWithEnds_relabelGraph_iff f g).1 h⟩

@[simp]
theorem isHPathWithEnds_relabelGraph_iff {a b : α} :
    IsHPathWithEnds (relabelGraph f g G) (relabelGraph f g H) (relabelGraph f g P) (f a) (f b) ↔
      IsHPathWithEnds G H P a b := by
  unfold IsHPathWithEnds
  simp only [relabelGraph_le_relabelGraph_iff, isGraphPathWithEnds_relabelGraph_iff,
    f.injective.ne_iff, f.injective.mem_set_image, vertexSet_relabelGraph,
    edgeSet_relabelGraph]
  rw [← Set.image_inter f.injective, Set.disjoint_image_iff g.injective]
  have : ({f a, f b} : Set α') = f '' {a, b} := by simp [Set.image_insert_eq]
  rw [this, (Set.image_injective.2 f.injective).eq_iff]

end GraphMinor.Transport
