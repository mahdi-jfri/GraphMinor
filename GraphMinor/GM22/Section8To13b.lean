module

public import GraphMinor.GM22.Section8To13a

import GraphMinor.GM22.GM21Proved

/-!
# Graph Minors XXII, Section 8 to XIII (10.2) (Part b): Type-Embedding Bridge for Theorem 8.3

In `GM13.GM13Theorem102Statement`, the vertex and edge types `α : Type u` and `β : Type v` are
arbitrary (possibly finite), whereas `Hypotheses83` in Graph Minors XXII requires embeddings
`ιV : S ↪ α'` and `ιE : Set S ↪ β'` from the surface `S` into the vertex and edge types.

Given a graph `K : Graph α β` and a surface drawing `Γ_draw : GraphDrawing K S`, we embed `α` into
`α' := α ⊕ ULift.{u} S` and `β` into `β' := β ⊕ ULift.{v} (Set S)` via `Sum.inl`, and define
`graphDrawingEmbV Γ_draw : S ↪ α'` and `graphDrawingEmbE Γ_draw : Set S ↪ β'` using `Γ_draw.iso` on
`Γ.V` and `Γ.E` and `Sum.inr ∘ ULift.up` on their complements. This yields
`Hypotheses83InGraph` and `theorem_8_3_in_graph`, which formulate and prove Theorem 8.3 directly
over `(α, β)` for a `GraphDrawing K S`.
-/

@[expose] public section

namespace GraphMinor.GM22

open Classical Set Function Topology Graph Hypergraph
open GraphMinor GraphMinor.Surface GraphMinor.GM06 GraphMinor.GM09 GraphMinor.GM11
open GraphMinor.GM13 GraphMinor.GM14

universe w u v u₁ v₁

variable {S : Type w} [TopologicalSpace S]
variable {α : Type u} {β : Type v} {α' : Type u₁} {β' : Type v₁}

/-! ## 1. Functoriality of `mapGraphEmb` along Injections `fV : α ↪ α'` and `fE : β ↪ β'` -/

/-- Push forward a graph `K : Graph α β` along embeddings `fV : α ↪ α'` and `fE : β ↪ β'`. -/
def mapGraphEmb (fV : α ↪ α') (fE : β ↪ β') (K : Graph α β) : Graph α' β' where
  vertexSet := fV '' V(K)
  edgeSet := fE '' E(K)
  IsLink e' x' y' := ∃ e x y, K.IsLink e x y ∧ fE e = e' ∧ fV x = x' ∧ fV y = y'
  isLink_symm _ _ := ⟨fun _ _ ⟨e, x, y, h, he, hx, hy⟩ => ⟨e, y, x, h.symm, he, hy, hx⟩⟩
  eq_or_eq_of_isLink_of_isLink := by
    rintro _ _ _ _ _ ⟨e₁, x₁, y₁, h₁, rfl, rfl, rfl⟩ ⟨e₂, x₂, y₂, h₂, he, rfl, rfl⟩
    obtain rfl : e₁ = e₂ := fE.injective he.symm
    obtain rfl | rfl := h₁.left_eq_or_eq h₂ <;> simp
  edge_mem_iff_exists_isLink e' := by
    constructor
    · rintro ⟨e, he, rfl⟩
      obtain ⟨x, y, hlink⟩ := K.exists_isLink_of_mem_edgeSet he
      exact ⟨fV x, fV y, e, x, y, hlink, rfl, rfl, rfl⟩
    · rintro ⟨_, _, e, x, y, hlink, rfl, rfl, rfl⟩
      exact ⟨e, hlink.edge_mem, rfl⟩
  left_mem_of_isLink := by
    rintro _ _ _ ⟨e, x, y, hlink, rfl, rfl, rfl⟩
    exact ⟨x, hlink.left_mem, rfl⟩

@[simp]
theorem vertexSet_mapGraphEmb (fV : α ↪ α') (fE : β ↪ β') (K : Graph α β) :
    V(mapGraphEmb fV fE K) = fV '' V(K) := rfl

@[simp]
theorem edgeSet_mapGraphEmb (fV : α ↪ α') (fE : β ↪ β') (K : Graph α β) :
    E(mapGraphEmb fV fE K) = fE '' E(K) := rfl

@[simp]
theorem mapGraphEmb_isLink_iff (fV : α ↪ α') (fE : β ↪ β') (K : Graph α β)
    (e : β) (x y : α) :
    (mapGraphEmb fV fE K).IsLink (fE e) (fV x) (fV y) ↔ K.IsLink e x y := by
  constructor
  · rintro ⟨e₀, x₀, y₀, hlink, he, hx, hy⟩
    obtain rfl := fE.injective he
    obtain rfl := fV.injective hx
    obtain rfl := fV.injective hy
    exact hlink
  · intro hlink
    exact ⟨e, x, y, hlink, rfl, rfl, rfl⟩

theorem mapGraphEmb_injective (fV : α ↪ α') (fE : β ↪ β') :
    Function.Injective (mapGraphEmb fV fE) := by
  intro K₁ K₂ h
  refine Graph.ext ?_ fun e x y => ?_
  · exact fV.injective.image_injective (congrArg Graph.vertexSet h)
  · rw [← mapGraphEmb_isLink_iff fV fE K₁, ← mapGraphEmb_isLink_iff fV fE K₂, h]

@[simp]
theorem mapGraphEmb_le_iff (fV : α ↪ α') (fE : β ↪ β') {K₁ K₂ : Graph α β} :
    mapGraphEmb fV fE K₁ ≤ mapGraphEmb fV fE K₂ ↔ K₁ ≤ K₂ := by
  constructor
  · rintro ⟨hV, hL⟩
    refine ⟨?_, fun e x y hlink => ?_⟩
    · intro x hx
      obtain ⟨x₀, hx₀, heq⟩ := hV ⟨x, hx, rfl⟩
      exact fV.injective heq ▸ hx₀
    · rw [← mapGraphEmb_isLink_iff fV fE K₂]
      exact hL ((mapGraphEmb_isLink_iff fV fE K₁ e x y).mpr hlink)
  · rintro ⟨hV, hL⟩
    refine ⟨image_mono hV, ?_⟩
    rintro _ _ _ ⟨e, x, y, hlink, rfl, rfl, rfl⟩
    exact ⟨e, x, y, hL hlink, rfl, rfl, rfl⟩

theorem mapGraphEmb_deleteVerts (fV : α ↪ α') (fE : β ↪ β') (K : Graph α β) (X : Set α) :
    mapGraphEmb fV fE (K.deleteVerts X) = (mapGraphEmb fV fE K).deleteVerts (fV '' X) := by
  refine Graph.ext ?_ fun e' x' y' => ?_
  · simp [Set.image_sdiff fV.injective]
  · simp only [mapGraphEmb, Graph.deleteVerts_isLink, mem_image]
    constructor
    · rintro ⟨e, x, y, ⟨hlink, hx, hy⟩, rfl, rfl, rfl⟩
      refine ⟨⟨e, x, y, hlink, rfl, rfl, rfl⟩, ?_, ?_⟩
      · rintro ⟨z, hz, hzx⟩; exact hx (fV.injective hzx ▸ hz)
      · rintro ⟨z, hz, hzy⟩; exact hy (fV.injective hzy ▸ hz)
    · rintro ⟨⟨e, x, y, hlink, rfl, rfl, rfl⟩, hx, hy⟩
      refine ⟨e, x, y, ⟨hlink, ?_, ?_⟩, rfl, rfl, rfl⟩
      · intro hxX; exact hx ⟨x, hxX, rfl⟩
      · intro hyX; exact hy ⟨y, hyX, rfl⟩

theorem mapGraphEmb_induce (fV : α ↪ α') (fE : β ↪ β') (K : Graph α β) (X : Set α) :
    mapGraphEmb fV fE (K.induce X) = (mapGraphEmb fV fE K).induce (fV '' X) := by
  refine Graph.ext rfl fun e' x' y' => ?_
  simp only [mapGraphEmb, Graph.induce_isLink, mem_image]
  constructor
  · rintro ⟨e, x, y, ⟨hlink, hx, hy⟩, rfl, rfl, rfl⟩
    exact ⟨⟨e, x, y, hlink, rfl, rfl, rfl⟩, ⟨x, hx, rfl⟩, ⟨y, hy, rfl⟩⟩
  · rintro ⟨⟨e, x, y, hlink, rfl, rfl, rfl⟩, ⟨x₀, hx₀, hx⟩, ⟨y₀, hy₀, hy⟩⟩
    obtain rfl := fV.injective hx
    obtain rfl := fV.injective hy
    exact ⟨e, x₀, y₀, ⟨hlink, hx₀, hy₀⟩, rfl, rfl, rfl⟩

theorem mapGraphEmb_subgraphSUnion (fV : α ↪ α') (fE : β ↪ β') {K : Graph α β}
    {𝒜 : Set (Graph α β)} (hle : ∀ A ∈ 𝒜, A ≤ K) :
    mapGraphEmb fV fE (subgraphSUnion K 𝒜) =
      subgraphSUnion (mapGraphEmb fV fE K) (mapGraphEmb fV fE '' 𝒜) := by
  have hle' : ∀ A' ∈ mapGraphEmb fV fE '' 𝒜, A' ≤ mapGraphEmb fV fE K := by
    rintro _ ⟨A, hA, rfl⟩
    exact (mapGraphEmb_le_iff fV fE).mpr (hle A hA)
  have h1 : mapGraphEmb fV fE (subgraphSUnion K 𝒜) ≤ mapGraphEmb fV fE K :=
    (mapGraphEmb_le_iff fV fE).mpr (subgraphSUnion_le hle)
  have h2 : subgraphSUnion (mapGraphEmb fV fE K) (mapGraphEmb fV fE '' 𝒜) ≤ mapGraphEmb fV fE K :=
    subgraphSUnion_le hle'
  refine (Compatible.of_le_le h1 h2).ext ?_ ?_
  · rw [vertexSet_mapGraphEmb, vertexSet_subgraphSUnion, vertexSet_subgraphSUnion]
    ext x'
    simp only [mem_image, mem_iUnion, exists_prop]
    aesop
  · rw [edgeSet_mapGraphEmb, edgeSet_subgraphSUnion hle, edgeSet_subgraphSUnion hle']
    ext e'
    simp only [mem_image, mem_iUnion, exists_prop]
    aesop

/-- Pull back a subgraph `K' ≤ mapGraphEmb fV fE A` to a subgraph of `A`. -/
def unmapSubgraphEmb (fV : α ↪ α') (fE : β ↪ β') (A : Graph α β) (K' : Graph α' β') :
    Graph α β where
  vertexSet := V(A) ∩ fV ⁻¹' V(K')
  edgeSet := {e | ∃ x y, A.IsLink e x y ∧ K'.IsLink (fE e) (fV x) (fV y)}
  IsLink e x y := A.IsLink e x y ∧ K'.IsLink (fE e) (fV x) (fV y)
  isLink_symm _ _ := ⟨fun _ _ ⟨hA, hK⟩ => ⟨hA.symm, hK.symm⟩⟩
  eq_or_eq_of_isLink_of_isLink _ _ _ _ _ h₁ h₂ := h₁.1.left_eq_or_eq h₂.1
  edge_mem_iff_exists_isLink _ := Iff.rfl
  left_mem_of_isLink _ _ _ h := ⟨h.1.left_mem, h.2.left_mem⟩

theorem unmapSubgraphEmb_le (fV : α ↪ α') (fE : β ↪ β') (A : Graph α β) (K' : Graph α' β') :
    unmapSubgraphEmb fV fE A K' ≤ A :=
  ⟨inter_subset_left, fun _ _ _ h => h.1⟩

theorem mapGraphEmb_unmapSubgraphEmb (fV : α ↪ α') (fE : β ↪ β') {A : Graph α β}
    {K' : Graph α' β'} (hle : K' ≤ mapGraphEmb fV fE A) :
    mapGraphEmb fV fE (unmapSubgraphEmb fV fE A K') = K' := by
  refine Graph.ext ?_ fun e' x' y' => ?_
  · apply Subset.antisymm
    · rintro _ ⟨x, ⟨_, hxK'⟩, rfl⟩
      exact hxK'
    · intro x' hx'
      obtain ⟨x, hxA, rfl⟩ := hle.vertexSet_mono hx'
      exact ⟨x, ⟨hxA, hx'⟩, rfl⟩
  · constructor
    · rintro ⟨e, x, y, ⟨_, hlinkK'⟩, rfl, rfl, rfl⟩
      exact hlinkK'
    · intro hlinkK'
      obtain ⟨e, x, y, hlinkA, rfl, rfl, rfl⟩ := hle.2 hlinkK'
      exact ⟨e, x, y, ⟨hlinkA, hlinkK'⟩, rfl, rfl, rfl⟩

/-! ## 2. Walks, Paths, Components, and Divisions under `mapGraphEmb` -/

/-- Push forward a walk along `(fV, fE)`. -/
def mapGraphWalkEmb (fV : α ↪ α') (fE : β ↪ β') {K : Graph α β} :
    ∀ {u v : α}, GraphWalk K u v → GraphWalk (mapGraphEmb fV fE K) (fV u) (fV v)
  | _, _, .nil hu => .nil ⟨_, hu, rfl⟩
  | _, _, .cons hlink rest =>
    .cons ((mapGraphEmb_isLink_iff fV fE K _ _ _).mpr hlink) (mapGraphWalkEmb fV fE rest)

@[simp]
theorem support_mapGraphWalkEmb (fV : α ↪ α') (fE : β ↪ β') {K : Graph α β}
    {u v : α} (W : GraphWalk K u v) :
    (mapGraphWalkEmb fV fE W).support = W.support.map fV := by
  induction W with
  | nil _ => rfl
  | cons _ rest ih => simp [mapGraphWalkEmb, GraphWalk.support, ih]

@[simp]
theorem edges_mapGraphWalkEmb (fV : α ↪ α') (fE : β ↪ β') {K : Graph α β}
    {u v : α} (W : GraphWalk K u v) :
    (mapGraphWalkEmb fV fE W).edges = W.edges.map fE := by
  induction W with
  | nil _ => rfl
  | cons _ rest ih => simp [mapGraphWalkEmb, GraphWalk.edges, ih]

/-- Pull back a walk from `mapGraphEmb fV fE K` to `K`. -/
noncomputable def unmapGraphWalkEmb (fV : α ↪ α') (fE : β ↪ β') {K : Graph α β} :
    ∀ {u' v' : α'} (_ : GraphWalk (mapGraphEmb fV fE K) u' v')
      (u v : α) (_ : fV u = u') (_ : fV v = v'), GraphWalk K u v
  | _, _, .nil hu', u, v, hu, hv => by
    obtain rfl : u = v := fV.injective (hu.trans hv.symm)
    have huK : u ∈ V(K) := by
      rcases hu' with ⟨x, hx, hfx⟩
      exact fV.injective (hfx.trans hu.symm) ▸ hx
    exact .nil huK
  | _, _, @GraphWalk.cons _ _ _ _ w' _ e' hlink' rest', u, v, hu, hv => by
    have hex : ∃ w e, K.IsLink e u w ∧ fV w = w' ∧ fE e = e' := by
      rcases hlink' with ⟨e₀, x₀, y₀, hl, rfl, hx₀, rfl⟩
      obtain rfl : x₀ = u := fV.injective (hx₀.trans hu.symm)
      exact ⟨y₀, e₀, hl, rfl, rfl⟩
    let w := Classical.choose hex
    let e := Classical.choose (Classical.choose_spec hex)
    have hspec := Classical.choose_spec (Classical.choose_spec hex)
    exact .cons hspec.1 (unmapGraphWalkEmb fV fE rest' w v hspec.2.1 hv)

theorem nonempty_graphWalk_mapGraphEmb_iff (fV : α ↪ α') (fE : β ↪ β') (K : Graph α β)
    (u v : α) :
    Nonempty (GraphWalk (mapGraphEmb fV fE K) (fV u) (fV v)) ↔ Nonempty (GraphWalk K u v) :=
  ⟨fun ⟨W'⟩ => ⟨unmapGraphWalkEmb fV fE W' u v rfl rfl⟩,
   fun ⟨W⟩ => ⟨mapGraphWalkEmb fV fE W⟩⟩

theorem isGraphConnected_mapGraphEmb_iff (fV : α ↪ α') (fE : β ↪ β') (K : Graph α β) :
    IsGraphConnected (mapGraphEmb fV fE K) ↔ IsGraphConnected K := by
  constructor
  · rintro ⟨⟨_, ⟨v₀, hv₀, rfl⟩⟩, hconn⟩
    refine ⟨⟨v₀, hv₀⟩, fun u hu v hv => ?_⟩
    exact (nonempty_graphWalk_mapGraphEmb_iff fV fE K u v).mp
      (hconn (fV u) ⟨u, hu, rfl⟩ (fV v) ⟨v, hv, rfl⟩)
  · rintro ⟨⟨v₀, hv₀⟩, hconn⟩
    refine ⟨⟨fV v₀, v₀, hv₀, rfl⟩, ?_⟩
    rintro _ ⟨u, hu, rfl⟩ _ ⟨v, hv, rfl⟩
    exact (nonempty_graphWalk_mapGraphEmb_iff fV fE K u v).mpr (hconn u hu v hv)

theorem isGraphPathWithEnds_mapGraphEmb (fV : α ↪ α') (fE : β ↪ β') {K P : Graph α β}
    {u v : α} (hP : IsGraphPathWithEnds K P u v) :
    IsGraphPathWithEnds (mapGraphEmb fV fE K) (mapGraphEmb fV fE P) (fV u) (fV v) := by
  obtain ⟨hle, W, hsimp, hV, hE⟩ := hP
  refine ⟨(mapGraphEmb_le_iff fV fE).mpr hle, mapGraphWalkEmb fV fE W, ?_, ?_, ?_⟩
  · change (mapGraphWalkEmb fV fE W).support.Nodup
    rw [support_mapGraphWalkEmb]
    exact hsimp.map fV.injective
  · rw [vertexSet_mapGraphEmb, support_mapGraphWalkEmb, hV]
    ext x'
    simp
  · rw [edgeSet_mapGraphEmb, edges_mapGraphWalkEmb, hE]
    ext e'
    simp

theorem support_unmapGraphWalkEmb (fV : α ↪ α') (fE : β ↪ β') {K : Graph α β} :
    ∀ {u' v' : α'} (W' : GraphWalk (mapGraphEmb fV fE K) u' v')
      (u v : α) (hu : fV u = u') (hv : fV v = v'),
      (unmapGraphWalkEmb fV fE W' u v hu hv).support.map fV = W'.support
  | _, _, .nil _, u, v, hu, hv => by
    obtain rfl : u = v := fV.injective (hu.trans hv.symm)
    simp [unmapGraphWalkEmb, GraphWalk.support, hu]
  | _, _, @GraphWalk.cons _ _ _ _ w' _ e' hlink' rest', u, v, hu, hv => by
    have hex : ∃ w e, K.IsLink e u w ∧ fV w = w' ∧ fE e = e' := by
      rcases hlink' with ⟨e₀, x₀, y₀, hl, rfl, hx₀, rfl⟩
      obtain rfl : x₀ = u := fV.injective (hx₀.trans hu.symm)
      exact ⟨y₀, e₀, hl, rfl, rfl⟩
    have hspec := Classical.choose_spec (Classical.choose_spec hex)
    simp only [unmapGraphWalkEmb, GraphWalk.support, List.map_cons, hu,
      support_unmapGraphWalkEmb fV fE rest' _ v hspec.2.1 hv]

theorem edges_unmapGraphWalkEmb (fV : α ↪ α') (fE : β ↪ β') {K : Graph α β} :
    ∀ {u' v' : α'} (W' : GraphWalk (mapGraphEmb fV fE K) u' v')
      (u v : α) (hu : fV u = u') (hv : fV v = v'),
      (unmapGraphWalkEmb fV fE W' u v hu hv).edges.map fE = W'.edges
  | _, _, .nil _, u, v, hu, hv => by
    obtain rfl : u = v := fV.injective (hu.trans hv.symm)
    simp [unmapGraphWalkEmb, GraphWalk.edges]
  | _, _, @GraphWalk.cons _ _ _ _ w' _ e' hlink' rest', u, v, hu, hv => by
    have hex : ∃ w e, K.IsLink e u w ∧ fV w = w' ∧ fE e = e' := by
      rcases hlink' with ⟨e₀, x₀, y₀, hl, rfl, hx₀, rfl⟩
      obtain rfl : x₀ = u := fV.injective (hx₀.trans hu.symm)
      exact ⟨y₀, e₀, hl, rfl, rfl⟩
    have hspec := Classical.choose_spec (Classical.choose_spec hex)
    simp only [unmapGraphWalkEmb, GraphWalk.edges, List.map_cons, hspec.2.2,
      edges_unmapGraphWalkEmb fV fE rest' _ v hspec.2.1 hv]

theorem end_mem_support_of_graphWalk {K : Graph α β} {u v : α} (W : GraphWalk K u v) :
    v ∈ W.support := by
  induction W with
  | nil _ => simp [GraphWalk.support]
  | cons _ _ ih => exact List.mem_cons_of_mem _ ih

theorem pathInternalVerts_mapGraphEmb (fV : α ↪ α') (fE : β ↪ β') {K P : Graph α β}
    {u v : α} (_ : IsGraphPathWithEnds K P u v) :
    pathInternalVerts (mapGraphEmb fV fE K) (mapGraphEmb fV fE P) =
      fV '' pathInternalVerts K P := by
  ext w'
  change (w' ∈ V(mapGraphEmb fV fE P) ∧
      ¬ ∃ z', IsGraphPathWithEnds (mapGraphEmb fV fE K) (mapGraphEmb fV fE P) w' z') ↔
    ∃ w, (w ∈ V(P) ∧ ¬ ∃ z, IsGraphPathWithEnds K P w z) ∧ fV w = w'
  constructor
  · rintro ⟨⟨w, hwP, rfl⟩, hnot⟩
    exact ⟨w, ⟨hwP, fun ⟨z, hwz⟩ => hnot ⟨fV z, isGraphPathWithEnds_mapGraphEmb fV fE hwz⟩⟩, rfl⟩
  · rintro ⟨w, ⟨hwP, hnot⟩, rfl⟩
    refine ⟨⟨w, hwP, rfl⟩, fun ⟨z', hle', W', hsimp', hV', hE'⟩ => ?_⟩
    have hz'_mem : z' ∈ V(mapGraphEmb fV fE P) := by
      rw [hV']
      exact end_mem_support_of_graphWalk W'
    obtain ⟨z, _, hfz⟩ := hz'_mem
    let W := unmapGraphWalkEmb fV fE W' w z rfl hfz
    have hsupp := support_unmapGraphWalkEmb fV fE W' w z rfl hfz
    have hedges := edges_unmapGraphWalkEmb fV fE W' w z rfl hfz
    apply hnot
    refine ⟨z, (mapGraphEmb_le_iff fV fE).mp hle', W, ?_, ?_, ?_⟩
    · change W.support.Nodup
      exact List.Nodup.of_map fV (by rw [hsupp]; exact hsimp')
    · ext x
      rw [← fV.injective.mem_set_image, ← vertexSet_mapGraphEmb, hV', ← hsupp]
      simp [W]
    · ext e
      rw [← fE.injective.mem_set_image, ← edgeSet_mapGraphEmb, hE', ← hedges]
      simp [W]

/-- For any graph `L` and vertex set `Y`, the union of vertex sets of components of `L` meeting
`Y` is the set of vertices of `L` reachable in `L` from `Y ∩ V(L)`. -/
theorem biUnion_graphComponents_inter_nonempty_eq (L : Graph α β) (Y : Set α) :
    (⋃ C ∈ {C ∈ graphComponents L | (V(C) ∩ Y).Nonempty}, V(C)) =
      {v ∈ V(L) | ∃ y ∈ Y ∩ V(L), Nonempty (GraphWalk L y v)} := by
  ext v
  simp only [mem_iUnion, exists_prop, mem_ofPred, mem_inter_iff]
  constructor
  · rintro ⟨C, ⟨hC_comp, y, hyC, hyY⟩, hvC⟩
    have hyL : y ∈ V(L) := hC_comp.1.vertexSet_mono hyC
    have hvL : v ∈ V(L) := hC_comp.1.vertexSet_mono hvC
    obtain ⟨W⟩ := hC_comp.2.1.2 y hyC v hvC
    exact ⟨hvL, y, ⟨hyY, hyL⟩, ⟨W.mono hC_comp.1⟩⟩
  · rintro ⟨hvL, y, ⟨hyY, hyL⟩, ⟨W⟩⟩
    refine ⟨GM09.reachableComponent L y,
      ⟨GM09.isGraphComponent_reachableComponent hyL,
        y, GM09.self_mem_reachableComponent hyL, hyY⟩, ?_⟩
    rw [GM09.vertexSet_reachableComponent]
    exact ⟨hvL, ⟨W⟩⟩

theorem biUnion_graphComponents_mapGraphEmb (fV : α ↪ α') (fE : β ↪ β')
    (L : Graph α β) (Y : Set α) :
    (⋃ C' ∈ {C' ∈ graphComponents (mapGraphEmb fV fE L) | (V(C') ∩ (fV '' Y)).Nonempty}, V(C')) =
      fV '' (⋃ C ∈ {C ∈ graphComponents L | (V(C) ∩ Y).Nonempty}, V(C)) := by
  rw [biUnion_graphComponents_inter_nonempty_eq, biUnion_graphComponents_inter_nonempty_eq]
  ext v'
  simp only [vertexSet_mapGraphEmb, mem_ofPred, mem_image, mem_inter_iff]
  constructor
  · rintro ⟨⟨v, hvL, rfl⟩, _, ⟨⟨y, hyY, rfl⟩, ⟨y₀, hy₀L, hy₀⟩⟩, ⟨W'⟩⟩
    obtain rfl := (fV.injective hy₀).symm
    refine ⟨v, ⟨hvL, y, ⟨hyY, hy₀L⟩,
      (nonempty_graphWalk_mapGraphEmb_iff fV fE L y v).mp ⟨W'⟩⟩, rfl⟩
  · rintro ⟨v, ⟨hvL, y, ⟨hyY, hyL⟩, hW⟩, rfl⟩
    exact ⟨⟨v, hvL, rfl⟩, fV y, ⟨⟨y, hyY, rfl⟩, ⟨y, hyL, rfl⟩⟩,
      (nonempty_graphWalk_mapGraphEmb_iff fV fE L y v).mpr hW⟩

theorem isZDivision_mapGraphEmb (fV : α ↪ α') (fE : β ↪ β') {J : Graph α β} {Z : Set α}
    {𝒜 : Set (Graph α β)} (hdiv : IsZDivision J Z 𝒜) :
    IsZDivision (mapGraphEmb fV fE J) (fV '' Z) (mapGraphEmb fV fE '' 𝒜) := by
  obtain ⟨hfin, hle, hsUnion, hdisj⟩ := hdiv
  refine ⟨hfin.image _, ?_, ?_, ?_⟩
  · rintro _ ⟨A, hA, rfl⟩
    exact (mapGraphEmb_le_iff fV fE).mpr (hle A hA)
  · rw [← mapGraphEmb_subgraphSUnion fV fE hle, hsUnion]
  · rintro _ ⟨A₁, hA₁, rfl⟩ _ ⟨A₂, hA₂, rfl⟩ hne
    have hA_ne : A₁ ≠ A₂ := fun h => hne (by rw [h])
    obtain ⟨hE, hV⟩ := hdisj A₁ hA₁ A₂ hA₂ hA_ne
    refine ⟨?_, ?_⟩
    · rw [edgeSet_mapGraphEmb, edgeSet_mapGraphEmb]
      exact Set.disjoint_image_of_injective fE.injective hE
    · rw [vertexSet_mapGraphEmb, vertexSet_mapGraphEmb, ← Set.image_inter fV.injective]
      exact image_mono hV

/-! ## 3. Digraphs, Rooted Digraphs, and $\delta$-Folios under `(fV, fE)` -/

/-- Auxiliary head map for `mapDigraphEmb`. -/
noncomputable def mapDigraphHead {α : Type u} {β : Type v} {α' : Type u₁} {β' : Type v₁}
    (fV : α ↪ α') (fE : β ↪ β') (D : Digraph α β) [Nonempty α] (e' : β') : α' :=
  if h : ∃ e ∈ E(D.toGraph), fE e = e' then
    fV (D.head (Classical.choose h))
  else
    fV (Classical.arbitrary α)

/-- Auxiliary tail map for `mapDigraphEmb`. -/
noncomputable def mapDigraphTail {α : Type u} {β : Type v} {α' : Type u₁} {β' : Type v₁}
    (fV : α ↪ α') (fE : β ↪ β') (D : Digraph α β) [Nonempty α] (e' : β') : α' :=
  if h : ∃ e ∈ E(D.toGraph), fE e = e' then
    fV (D.tail (Classical.choose h))
  else
    fV (Classical.arbitrary α)

/-- Push forward a `GM22.Digraph α β` along `(fV : α ↪ α', fE : β ↪ β')`. -/
noncomputable abbrev mapDigraphEmb {α : Type u} {β : Type v} {α' : Type u₁} {β' : Type v₁}
    (fV : α ↪ α') (fE : β ↪ β') (D : Digraph α β) [Nonempty α] :
    Digraph α' β' where
  toGraph := mapGraphEmb fV fE D.toGraph
  head := mapDigraphHead fV fE D
  tail := mapDigraphTail fV fE D
  isLink_of_mem := by
    rintro _ ⟨e, he, rfl⟩
    have hex : ∃ e₀ ∈ E(D.toGraph), fE e₀ = fE e := ⟨e, he, rfl⟩
    have heq : Classical.choose hex = e := fE.injective (Classical.choose_spec hex).2
    simp only [mapDigraphHead, mapDigraphTail, hex, ↓reduceDIte, heq]
    exact (mapGraphEmb_isLink_iff fV fE D.toGraph e (D.tail e) (D.head e)).mpr
      (D.isLink_of_mem e he)

@[simp]
theorem toGraph_mapDigraphEmb {α : Type u} {β : Type v} {α' : Type u₁} {β' : Type v₁}
    (fV : α ↪ α') (fE : β ↪ β') (D : Digraph α β) [Nonempty α] :
    (mapDigraphEmb fV fE D).toGraph = mapGraphEmb fV fE D.toGraph := rfl

theorem head_mapDigraphEmb {α : Type u} {β : Type v} {α' : Type u₁} {β' : Type v₁}
    (fV : α ↪ α') (fE : β ↪ β') (D : Digraph α β) [Nonempty α]
    {e : β} (he : e ∈ E(D.toGraph)) :
    (mapDigraphEmb fV fE D).head (fE e) = fV (D.head e) := by
  have hex : ∃ e₀ ∈ E(D.toGraph), fE e₀ = fE e := ⟨e, he, rfl⟩
  have heq : Classical.choose hex = e := fE.injective (Classical.choose_spec hex).2
  change mapDigraphHead fV fE D (fE e) = _
  simp only [mapDigraphHead, hex, ↓reduceDIte, heq]

theorem tail_mapDigraphEmb {α : Type u} {β : Type v} {α' : Type u₁} {β' : Type v₁}
    (fV : α ↪ α') (fE : β ↪ β') (D : Digraph α β) [Nonempty α]
    {e : β} (he : e ∈ E(D.toGraph)) :
    (mapDigraphEmb fV fE D).tail (fE e) = fV (D.tail e) := by
  have hex : ∃ e₀ ∈ E(D.toGraph), fE e₀ = fE e := ⟨e, he, rfl⟩
  have heq : Classical.choose hex = e := fE.injective (Classical.choose_spec hex).2
  change mapDigraphTail fV fE D (fE e) = _
  simp only [mapDigraphTail, hex, ↓reduceDIte, heq]

/-- Push forward a `GM22.RootedDigraph α β q` along `(fV : α ↪ α', fE : β ↪ β')`. -/
noncomputable abbrev mapRootedDigraphEmb {α : Type u} {β : Type v} {α' : Type u₁} {β' : Type v₁}
    {q : ℕ} (fV : α ↪ α') (fE : β ↪ β') (R : RootedDigraph α β q) [Nonempty α] :
    RootedDigraph α' β' q where
  G := mapDigraphEmb fV fE R.G
  roots := fV ∘ R.roots
  roots_mem i := ⟨R.roots i, R.roots_mem i, rfl⟩

/-- `HasRootedDigraphModel` is invariant under `mapDigraphEmb fV fE` on `subRootedDigraph`. -/
theorem hasRootedDigraphModel_subRootedDigraph_mapDigraphEmb_iff
    {α : Type u} {β : Type v} {α' : Type u₁} {β' : Type v₁} {q : ℕ}
    (fV : α ↪ α') (fE : β ↪ β') [Nonempty α] [Nonempty β]
    (D : Digraph α β) (A : Graph α β) (hA : A ≤ D.toGraph)
    (π : Fin q → α) (hπ : ∀ i : Fin q, π i ∈ V(A))
    (hA' : mapGraphEmb fV fE A ≤ (mapDigraphEmb fV fE D).toGraph)
    (hπ' : ∀ i : Fin q, (fV ∘ π) i ∈ V(mapGraphEmb fV fE A))
    {αH βH : Type*} (R_H : RootedDigraph αH βH q) :
    HasRootedDigraphModel
      (subRootedDigraph (mapDigraphEmb fV fE D) (mapGraphEmb fV fE A) hA' (fV ∘ π) hπ') R_H ↔
    HasRootedDigraphModel (subRootedDigraph D A hA π hπ) R_H := by
  constructor
  · rintro ⟨φV', φE', hM'⟩
    let φV (v : αH) : Graph α β := unmapSubgraphEmb fV fE A (φV' v)
    have hφV_map : ∀ v ∈ V(R_H.G.toGraph), mapGraphEmb fV fE (φV v) = φV' v :=
      fun v hv => mapGraphEmb_unmapSubgraphEmb fV fE (hM'.subgraph_of_mem v hv)
    have hexE : ∀ e, e ∈ E(R_H.G.toGraph) → ∃ b ∈ E(A), fE b = φE' e :=
      fun e he => hM'.edge_mem e he
    let φE (e : βH) : β :=
      if he : e ∈ E(R_H.G.toGraph) then Classical.choose (hexE e he) else Classical.arbitrary β
    have hφE_mem : ∀ e (he : e ∈ E(R_H.G.toGraph)), φE e ∈ E(A) := by
      intro e he
      simp only [φE, he, ↓reduceDIte]
      exact (Classical.choose_spec (hexE e he)).1
    have hφE_eq : ∀ e (he : e ∈ E(R_H.G.toGraph)), fE (φE e) = φE' e := by
      intro e he
      simp only [φE, he, ↓reduceDIte]
      exact (Classical.choose_spec (hexE e he)).2
    refine ⟨φV, φE, ?_⟩
    exact
      { subgraph_of_mem := fun v _ => unmapSubgraphEmb_le fV fE A (φV' v)
        connected_of_mem := fun v hv => by
          rw [← isGraphConnected_mapGraphEmb_iff fV fE, hφV_map v hv]
          exact hM'.connected_of_mem v hv
        disjoint_V := fun u hu v hv hne => by
          obtain ⟨hdV, hdE⟩ := hM'.disjoint_V u hu v hv hne
          rw [← hφV_map u hu, ← hφV_map v hv, vertexSet_mapGraphEmb, vertexSet_mapGraphEmb] at hdV
          rw [← hφV_map u hu, ← hφV_map v hv, edgeSet_mapGraphEmb, edgeSet_mapGraphEmb] at hdE
          exact ⟨hdV.of_image, hdE.of_image⟩
        root_mem := fun i => by
          have hr := hM'.root_mem i
          rw [← hφV_map (R_H.roots i) (R_H.roots_mem i), vertexSet_mapGraphEmb] at hr
          obtain ⟨x, hx, heq⟩ := hr
          obtain rfl : x = π i := fV.injective heq
          exact hx
        edge_mem := fun e he => hφE_mem e he
        injOn_E := fun e₁ he₁ e₂ he₂ heq =>
          hM'.injOn_E he₁ he₂ (by rw [← hφE_eq e₁ he₁, ← hφE_eq e₂ he₂, heq])
        edge_not_mem_φV := fun e he v hv hmem => by
          apply hM'.edge_not_mem_φV e he v hv
          rw [← hφE_eq e he, ← hφV_map v hv]
          exact ⟨φE e, hmem, rfl⟩
        head_mem := fun e he => by
          have hh := hM'.head_mem e he
          have hhV : R_H.G.head e ∈ V(R_H.G.toGraph) := (R_H.G.isLink_of_mem e he).right_mem
          have heD : φE e ∈ E(D.toGraph) := hA.edgeSet_mono (hφE_mem e he)
          change (mapDigraphEmb fV fE D).head (φE' e) ∈ V(φV' (R_H.G.head e)) at hh
          rw [← hφE_eq e he, head_mapDigraphEmb fV fE D heD, ← hφV_map _ hhV,
              vertexSet_mapGraphEmb] at hh
          obtain ⟨x, hx, heq⟩ := hh
          obtain rfl : x = D.head (φE e) := fV.injective heq
          exact hx
        tail_mem := fun e he => by
          have ht := hM'.tail_mem e he
          have htV : R_H.G.tail e ∈ V(R_H.G.toGraph) := (R_H.G.isLink_of_mem e he).left_mem
          have heD : φE e ∈ E(D.toGraph) := hA.edgeSet_mono (hφE_mem e he)
          change (mapDigraphEmb fV fE D).tail (φE' e) ∈ V(φV' (R_H.G.tail e)) at ht
          rw [← hφE_eq e he, tail_mapDigraphEmb fV fE D heD, ← hφV_map _ htV,
              vertexSet_mapGraphEmb] at ht
          obtain ⟨x, hx, heq⟩ := ht
          obtain rfl : x = D.tail (φE e) := fV.injective heq
          exact hx }
  · rintro ⟨φV, φE, hM⟩
    refine ⟨fun v => mapGraphEmb fV fE (φV v), fE ∘ φE, ?_⟩
    exact
      { subgraph_of_mem := fun v hv => (mapGraphEmb_le_iff fV fE).mpr (hM.subgraph_of_mem v hv)
        connected_of_mem := fun v hv =>
          (isGraphConnected_mapGraphEmb_iff fV fE _).mpr (hM.connected_of_mem v hv)
        disjoint_V := fun u hu v hv hne => by
          obtain ⟨hdV, hdE⟩ := hM.disjoint_V u hu v hv hne
          exact ⟨Set.disjoint_image_of_injective fV.injective hdV,
            Set.disjoint_image_of_injective fE.injective hdE⟩
        root_mem := fun i => ⟨π i, hM.root_mem i, rfl⟩
        edge_mem := fun e he => ⟨φE e, hM.edge_mem e he, rfl⟩
        injOn_E := fun e₁ he₁ e₂ he₂ heq => hM.injOn_E he₁ he₂ (fE.injective heq)
        edge_not_mem_φV := fun e he v hv ⟨b, hb, heq⟩ =>
          hM.edge_not_mem_φV e he v hv (fE.injective heq ▸ hb)
        head_mem := fun e he => by
          have heD : φE e ∈ E(D.toGraph) := hA.edgeSet_mono (hM.edge_mem e he)
          change (mapDigraphEmb fV fE D).head (fE (φE e)) ∈ _
          rw [head_mapDigraphEmb fV fE D heD]
          exact ⟨D.head (φE e), hM.head_mem e he, rfl⟩
        tail_mem := fun e he => by
          have heD : φE e ∈ E(D.toGraph) := hA.edgeSet_mono (hM.edge_mem e he)
          change (mapDigraphEmb fV fE D).tail (fE (φE e)) ∈ _
          rw [tail_mapDigraphEmb fV fE D heD]
          exact ⟨D.tail (φE e), hM.tail_mem e he, rfl⟩ }

theorem hasSameDeltaFolio_subRootedDigraph_mapDigraphEmb_iff [Nonempty α] [Nonempty β]
    {q₁ q₂ δ : ℕ} (fV : α ↪ α') (fE : β ↪ β')
    (D₁ D₂ : Digraph α β) (A₁ A₂ : Graph α β)
    (hA₁ : A₁ ≤ D₁.toGraph) (hA₂ : A₂ ≤ D₂.toGraph)
    (π₁ : Fin q₁ → α) (hπ₁ : ∀ i : Fin q₁, π₁ i ∈ V(A₁))
    (π₂ : Fin q₂ → α) (hπ₂ : ∀ i : Fin q₂, π₂ i ∈ V(A₂))
    (hA₁' : mapGraphEmb fV fE A₁ ≤ (mapDigraphEmb fV fE D₁).toGraph)
    (hA₂' : mapGraphEmb fV fE A₂ ≤ (mapDigraphEmb fV fE D₂).toGraph)
    (hπ₁' : ∀ i : Fin q₁, (fV ∘ π₁) i ∈ V(mapGraphEmb fV fE A₁))
    (hπ₂' : ∀ i : Fin q₂, (fV ∘ π₂) i ∈ V(mapGraphEmb fV fE A₂))
    (hq : q₁ = q₂) :
    q₁ = q₂ →
      ∀ (hR : q₁ = q₂),
      (HasSameDeltaFolio
        (subRootedDigraph (mapDigraphEmb fV fE D₁) (mapGraphEmb fV fE A₁) hA₁' (fV ∘ π₁) hπ₁')
        (hR ▸ subRootedDigraph (mapDigraphEmb fV fE D₂) (mapGraphEmb fV fE A₂) hA₂' (fV ∘ π₂) hπ₂') δ ↔
      HasSameDeltaFolio
        (subRootedDigraph D₁ A₁ hA₁ π₁ hπ₁)
        (hR ▸ subRootedDigraph D₂ A₂ hA₂ π₂ hπ₂) δ) := by
  subst hq
  intro _ _
  constructor
  · intro h αH βH R_H hDet
    rw [← hasRootedDigraphModel_subRootedDigraph_mapDigraphEmb_iff fV fE D₁ A₁ hA₁ π₁ hπ₁ hA₁' hπ₁',
        ← hasRootedDigraphModel_subRootedDigraph_mapDigraphEmb_iff fV fE D₂ A₂ hA₂ π₂ hπ₂ hA₂' hπ₂']
    exact h R_H hDet
  · intro h αH βH R_H hDet
    rw [hasRootedDigraphModel_subRootedDigraph_mapDigraphEmb_iff fV fE D₁ A₁ hA₁ π₁ hπ₁ hA₁' hπ₁',
        hasRootedDigraphModel_subRootedDigraph_mapDigraphEmb_iff fV fE D₂ A₂ hA₂ π₂ hπ₂ hA₂' hπ₂']
    exact h R_H hDet

/-! ## 4. Canonical Embeddings `graphDrawingEmbV` and `graphDrawingEmbE` for a `GraphDrawing` -/

/-- Given a `GraphDrawing K S`, map each vertex `s ∈ Γ_draw.drawing.V` to its corresponding vertex
in `V(K)` (and points outside `Γ_draw.drawing.V` to an arbitrary element of `α`). -/
noncomputable def drawingVertToGraph [Nonempty α] {K : Graph α β}
    (Γ_draw : GraphDrawing K S) (s : S) : α :=
  if hs : s ∈ Γ_draw.drawing.V then
    (Γ_draw.iso.vertexEquiv.symm ⟨s, hs⟩).1
  else
    Classical.arbitrary α

theorem drawingVertToGraph_apply_vertexEquiv [Nonempty α] {K : Graph α β}
    (Γ_draw : GraphDrawing K S) (x : V(K)) :
    drawingVertToGraph Γ_draw (Γ_draw.iso.vertexEquiv x).1 = x.1 := by
  have hs : (Γ_draw.iso.vertexEquiv x).1 ∈ Γ_draw.drawing.V := (Γ_draw.iso.vertexEquiv x).2
  simp only [drawingVertToGraph, hs, ↓reduceDIte]
  exact congrArg Subtype.val (Γ_draw.iso.vertexEquiv.symm_apply_apply x)

theorem vertexEquiv_drawingVertToGraph [Nonempty α] {K : Graph α β}
    (Γ_draw : GraphDrawing K S) {s : S} (hs : s ∈ Γ_draw.drawing.V) :
    ∃ hmem : drawingVertToGraph Γ_draw s ∈ V(K),
      (Γ_draw.iso.vertexEquiv ⟨drawingVertToGraph Γ_draw s, hmem⟩).1 = s := by
  simp only [drawingVertToGraph, hs, ↓reduceDIte]
  exact ⟨(Γ_draw.iso.vertexEquiv.symm ⟨s, hs⟩).2,
    congrArg Subtype.val (Γ_draw.iso.vertexEquiv.apply_symm_apply ⟨s, hs⟩)⟩

theorem injOn_drawingVertToGraph [Nonempty α] {K : Graph α β}
    (Γ_draw : GraphDrawing K S) :
    InjOn (drawingVertToGraph Γ_draw) Γ_draw.drawing.V := by
  intro s₁ hs₁ s₂ hs₂ heq
  obtain ⟨h₁, heq₁⟩ := vertexEquiv_drawingVertToGraph Γ_draw hs₁
  obtain ⟨h₂, heq₂⟩ := vertexEquiv_drawingVertToGraph Γ_draw hs₂
  rw [← heq₁, ← heq₂]
  exact congrArg (Subtype.val ∘ Γ_draw.iso.vertexEquiv) (Subtype.ext heq)

theorem image_drawingVertToGraph_V [Nonempty α] {K : Graph α β}
    (Γ_draw : GraphDrawing K S) :
    drawingVertToGraph Γ_draw '' Γ_draw.drawing.V = V(K) := by
  ext v
  constructor
  · rintro ⟨s, hs, rfl⟩
    obtain ⟨hmem, _⟩ := vertexEquiv_drawingVertToGraph Γ_draw hs
    exact hmem
  · intro hv
    exact ⟨(Γ_draw.iso.vertexEquiv ⟨v, hv⟩).1, (Γ_draw.iso.vertexEquiv ⟨v, hv⟩).2,
      drawingVertToGraph_apply_vertexEquiv Γ_draw ⟨v, hv⟩⟩

/-- Canonical vertex embedding `S ↪ α ⊕ ULift.{u} S` associated to `Γ_draw : GraphDrawing K S`. -/
noncomputable def graphDrawingEmbV {K : Graph α β} (Γ_draw : GraphDrawing K S) :
    S ↪ α ⊕ ULift.{u} S where
  toFun s :=
    if hs : s ∈ Γ_draw.drawing.V then
      Sum.inl (Γ_draw.iso.vertexEquiv.symm ⟨s, hs⟩).1
    else
      Sum.inr (ULift.up s)
  inj' := by
    intro s₁ s₂ heq
    by_cases hs₁ : s₁ ∈ Γ_draw.drawing.V <;> by_cases hs₂ : s₂ ∈ Γ_draw.drawing.V <;>
      simp [hs₁, hs₂] at heq
    · have hsub : Γ_draw.iso.vertexEquiv.symm ⟨s₁, hs₁⟩ = Γ_draw.iso.vertexEquiv.symm ⟨s₂, hs₂⟩ :=
        Subtype.ext heq
      exact congrArg Subtype.val (Γ_draw.iso.vertexEquiv.symm.injective hsub)
    · exact heq

/-- Canonical edge embedding `Set S ↪ β ⊕ ULift.{v} (Set S)` associated to `Γ_draw : GraphDrawing K S`. -/
noncomputable def graphDrawingEmbE {K : Graph α β} (Γ_draw : GraphDrawing K S) :
    Set S ↪ β ⊕ ULift.{v} (Set S) where
  toFun e :=
    if he : e ∈ Γ_draw.drawing.E then
      Sum.inl (Γ_draw.iso.edgeEquiv.symm ⟨e, he⟩).1
    else
      Sum.inr (ULift.up e)
  inj' := by
    intro e₁ e₂ heq
    by_cases he₁ : e₁ ∈ Γ_draw.drawing.E <;> by_cases he₂ : e₂ ∈ Γ_draw.drawing.E <;>
      simp [he₁, he₂] at heq
    · have hsub : Γ_draw.iso.edgeEquiv.symm ⟨e₁, he₁⟩ = Γ_draw.iso.edgeEquiv.symm ⟨e₂, he₂⟩ :=
        Subtype.ext heq
      exact congrArg Subtype.val (Γ_draw.iso.edgeEquiv.symm.injective hsub)
    · exact heq

theorem graphDrawingEmbV_of_mem_V [Nonempty α] {K : Graph α β}
    (Γ_draw : GraphDrawing K S) {s : S} (hs : s ∈ Γ_draw.drawing.V) :
    graphDrawingEmbV Γ_draw s = Sum.inl (drawingVertToGraph Γ_draw s) := by
  simp [graphDrawingEmbV, drawingVertToGraph, hs]

theorem image_graphDrawingEmbV_subset_V [Nonempty α] {K : Graph α β}
    (Γ_draw : GraphDrawing K S) {Y : Set S} (hY : Y ⊆ Γ_draw.drawing.V) :
    graphDrawingEmbV Γ_draw '' Y =
      (Function.Embedding.inl : α ↪ α ⊕ ULift.{u} S) '' (drawingVertToGraph Γ_draw '' Y) := by
  ext x'
  simp only [mem_image, Function.Embedding.inl_apply]
  constructor
  · rintro ⟨s, hsY, rfl⟩
    rw [graphDrawingEmbV_of_mem_V Γ_draw (hY hsY)]
    exact ⟨drawingVertToGraph Γ_draw s, ⟨s, hsY, rfl⟩, rfl⟩
  · rintro ⟨_, ⟨s, hsY, rfl⟩, rfl⟩
    refine ⟨s, hsY, ?_⟩
    exact graphDrawingEmbV_of_mem_V Γ_draw (hY hsY)

/-- Under `graphDrawingEmbV Γ_draw` and `graphDrawingEmbE Γ_draw`, the embedded graph of
`Γ_draw.drawing` is `mapGraphEmb Embedding.inl Embedding.inl K`. -/
theorem toEmbeddedGraph_graphDrawingEmb_eq {K : Graph α β} (Γ_draw : GraphDrawing K S) :
    Γ_draw.drawing.toEmbeddedGraph (graphDrawingEmbV Γ_draw) (graphDrawingEmbE Γ_draw) =
      mapGraphEmb Function.Embedding.inl Function.Embedding.inl K := by
  refine Graph.ext ?_ fun e' x' y' => ?_
  · ext x'
    simp only [Drawing.toEmbeddedGraph, vertexSet_mapGraphEmb, mem_image,
      Function.Embedding.inl_apply]
    constructor
    · rintro ⟨s, hs, rfl⟩
      simp only [graphDrawingEmbV, Function.Embedding.coeFn_mk, hs, ↓reduceDIte, Sum.inl.injEq]
      exact ⟨(Γ_draw.iso.vertexEquiv.symm ⟨s, hs⟩).1,
        (Γ_draw.iso.vertexEquiv.symm ⟨s, hs⟩).2, rfl⟩
    · rintro ⟨v, hv, rfl⟩
      let s := (Γ_draw.iso.vertexEquiv ⟨v, hv⟩).1
      have hs : s ∈ Γ_draw.drawing.V := (Γ_draw.iso.vertexEquiv ⟨v, hv⟩).2
      refine ⟨s, hs, ?_⟩
      simp only [graphDrawingEmbV, Function.Embedding.coeFn_mk, hs, ↓reduceDIte]
      exact congrArg Sum.inl (congrArg Subtype.val (Γ_draw.iso.vertexEquiv.symm_apply_apply ⟨v, hv⟩))
  · simp only [Drawing.toEmbeddedGraph, mapGraphEmb, Function.Embedding.inl_apply]
    constructor
    · rintro ⟨e₀, x₀, y₀, hlink, rfl, rfl, rfl⟩
      have he₀ : e₀ ∈ Γ_draw.drawing.E := hlink.edge_mem
      have hx₀ : x₀ ∈ Γ_draw.drawing.V := hlink.left_mem
      have hy₀ : y₀ ∈ Γ_draw.drawing.V := hlink.right_mem
      let e := Γ_draw.iso.edgeEquiv.symm ⟨e₀, he₀⟩
      let x := Γ_draw.iso.vertexEquiv.symm ⟨x₀, hx₀⟩
      let y := Γ_draw.iso.vertexEquiv.symm ⟨y₀, hy₀⟩
      have hlinkK : K.IsLink e.1 x.1 y.1 := by
        rw [Γ_draw.iso.isLink_iff e x y]
        simpa [e, x, y] using hlink
      refine ⟨e.1, x.1, y.1, hlinkK, ?_, ?_, ?_⟩
      · simp only [graphDrawingEmbE, Function.Embedding.coeFn_mk, he₀, ↓reduceDIte]; rfl
      · simp only [graphDrawingEmbV, Function.Embedding.coeFn_mk, hx₀, ↓reduceDIte]; rfl
      · simp only [graphDrawingEmbV, Function.Embedding.coeFn_mk, hy₀, ↓reduceDIte]; rfl
    · rintro ⟨e, x, y, hlinkK, rfl, rfl, rfl⟩
      have he : e ∈ E(K) := hlinkK.edge_mem
      have hx : x ∈ V(K) := hlinkK.left_mem
      have hy : y ∈ V(K) := hlinkK.right_mem
      let e₀ := Γ_draw.iso.edgeEquiv ⟨e, he⟩
      let x₀ := Γ_draw.iso.vertexEquiv ⟨x, hx⟩
      let y₀ := Γ_draw.iso.vertexEquiv ⟨y, hy⟩
      have he₀ : e₀.1 ∈ Γ_draw.drawing.E := e₀.2
      have hx₀ : x₀.1 ∈ Γ_draw.drawing.V := x₀.2
      have hy₀ : y₀.1 ∈ Γ_draw.drawing.V := y₀.2
      have hlink : Γ_draw.drawing.toGraph.IsLink e₀.1 x₀.1 y₀.1 :=
        (Γ_draw.iso.isLink_iff ⟨e, he⟩ ⟨x, hx⟩ ⟨y, hy⟩).mp hlinkK
      refine ⟨e₀.1, x₀.1, y₀.1, hlink, ?_, ?_, ?_⟩
      · simp only [graphDrawingEmbE, Function.Embedding.coeFn_mk, he₀, ↓reduceDIte]
        exact congrArg Sum.inl (congrArg Subtype.val (Γ_draw.iso.edgeEquiv.symm_apply_apply ⟨e, he⟩))
      · simp only [graphDrawingEmbV, Function.Embedding.coeFn_mk, hx₀, ↓reduceDIte]
        exact congrArg Sum.inl (congrArg Subtype.val (Γ_draw.iso.vertexEquiv.symm_apply_apply ⟨x, hx⟩))
      · simp only [graphDrawingEmbV, Function.Embedding.coeFn_mk, hy₀, ↓reduceDIte]
        exact congrArg Sum.inl (congrArg Subtype.val (Γ_draw.iso.vertexEquiv.symm_apply_apply ⟨y, hy⟩))

/-! ## 5. Disc Drawing of `divisionIncidenceGraph` and `Hypotheses83InGraph` -/

/-- Condition (x) of Theorem 8.3 formulated directly over `(α, β)` using a map `ν : S → α` on
`PiSet`. -/
def HasDiscDrawingWithBoundaryOrderInGraph {S : Type w} [TopologicalSpace S]
    {α : Type u} {β : Type v}
    (ν : S → α) (C₀ : Drawing S) (PiSet : Set S) (Z : Set α) (𝒜 : Set (Graph α β)) : Prop :=
  ∃ (D_disc : Set EuclideanPlane) (gd : GraphDrawing (divisionIncidenceGraph Z 𝒜) EuclideanPlane)
    (φ_C : Circle ≃ₜ C₀.U) (φ_D : Circle ≃ₜ subBd D_disc),
    IsClosedDisc D_disc ∧ gd.drawing.U ⊆ D_disc ∧
    (∀ p : S, p ∈ PiSet →
      ∃ hp : Sum.inl (ν p) ∈ V(divisionIncidenceGraph Z 𝒜),
        (gd.iso.vertexEquiv ⟨Sum.inl (ν p), hp⟩).1 ∈ subBd D_disc) ∧
    (∀ v : V(divisionIncidenceGraph Z 𝒜),
      (gd.iso.vertexEquiv v).1 ∈ subBd D_disc ↔ ∃ p ∈ PiSet, v.1 = Sum.inl (ν p)) ∧
    ∀ (t₁ t₂ t₃ t₄ : ℝ) (p₁ p₂ p₃ p₄ : S),
      0 ≤ t₁ → t₁ < t₂ → t₂ < t₃ → t₃ < t₄ → t₄ < 2 * Real.pi →
      PiSet = {p₁, p₂, p₃, p₄} →
      (φ_C (Circle.exp t₁)).1 = p₁ → (φ_C (Circle.exp t₂)).1 = p₂ →
      (φ_C (Circle.exp t₃)).1 = p₃ → (φ_C (Circle.exp t₄)).1 = p₄ →
      ∃ (s₁ s₂ s₃ s₄ : ℝ) (hp₁ : Sum.inl (ν p₁) ∈ V(divisionIncidenceGraph Z 𝒜))
        (hp₂ : Sum.inl (ν p₂) ∈ V(divisionIncidenceGraph Z 𝒜))
        (hp₃ : Sum.inl (ν p₃) ∈ V(divisionIncidenceGraph Z 𝒜))
        (hp₄ : Sum.inl (ν p₄) ∈ V(divisionIncidenceGraph Z 𝒜)),
        0 ≤ s₁ ∧ s₁ < s₂ ∧ s₂ < s₃ ∧ s₃ < s₄ ∧ s₄ < 2 * Real.pi ∧
        (φ_D (Circle.exp s₁)).1 = (gd.iso.vertexEquiv ⟨Sum.inl (ν p₁), hp₁⟩).1 ∧
        (φ_D (Circle.exp s₂)).1 = (gd.iso.vertexEquiv ⟨Sum.inl (ν p₂), hp₂⟩).1 ∧
        (φ_D (Circle.exp s₃)).1 = (gd.iso.vertexEquiv ⟨Sum.inl (ν p₃), hp₃⟩).1 ∧
        (φ_D (Circle.exp s₄)).1 = (gd.iso.vertexEquiv ⟨Sum.inl (ν p₄), hp₄⟩).1

/-- Isomorphism between `divisionIncidenceGraph (fV '' Z) (mapGraphEmb fV fE '' 𝒜)` and
`divisionIncidenceGraph Z 𝒜`. -/
noncomputable def divisionIncidenceGraphIso (fV : α ↪ α') (fE : β ↪ β')
    (Z : Set α) (𝒜 : Set (Graph α β)) :
    Iso (divisionIncidenceGraph (fV '' Z) (mapGraphEmb fV fE '' 𝒜))
      (divisionIncidenceGraph Z 𝒜) := by
  let G₁ := divisionIncidenceGraph (fV '' Z) (mapGraphEmb fV fE '' 𝒜)
  let G₂ := divisionIncidenceGraph Z 𝒜
  have hv_fwd : ∀ x : α ⊕ Graph α β, x ∈ V(G₂) →
      Sum.map fV (mapGraphEmb fV fE) x ∈ V(G₁) := by
    rintro (z | A) (⟨z₀, hz₀, h⟩ | ⟨A₀, hA₀, h⟩)
    · obtain rfl := Sum.inl.inj h
      exact Or.inl ⟨fV z₀, ⟨z₀, hz₀, rfl⟩, rfl⟩
    · cases h
    · cases h
    · obtain rfl := Sum.inr.inj h
      exact Or.inr ⟨mapGraphEmb fV fE A₀, ⟨A₀, hA₀, rfl⟩, rfl⟩
  have hv_inj : Function.Injective (Sum.map fV (mapGraphEmb fV fE)) :=
    Sum.map_injective.mpr ⟨fV.injective, mapGraphEmb_injective fV fE⟩
  have hv_surj : ∀ y ∈ V(G₁), ∃ x ∈ V(G₂), Sum.map fV (mapGraphEmb fV fE) x = y := by
    rintro _ (⟨_, ⟨z, hz, rfl⟩, rfl⟩ | ⟨_, ⟨A, hA, rfl⟩, rfl⟩)
    · exact ⟨Sum.inl z, Or.inl ⟨z, hz, rfl⟩, rfl⟩
    · exact ⟨Sum.inr A, Or.inr ⟨A, hA, rfl⟩, rfl⟩
  let eV : V(G₂) ≃ V(G₁) :=
    Equiv.ofBijective (fun x => ⟨Sum.map fV (mapGraphEmb fV fE) x.1, hv_fwd x.1 x.2⟩)
      ⟨fun x₁ x₂ h => Subtype.ext (hv_inj (congrArg Subtype.val h)),
       fun y => by
         obtain ⟨x, hx, heq⟩ := hv_surj y.1 y.2
         exact ⟨⟨x, hx⟩, Subtype.ext heq⟩⟩
  have he_fwd : ∀ p : α × Graph α β, p ∈ E(G₂) →
      Prod.map fV (mapGraphEmb fV fE) p ∈ E(G₁) := by
    rintro ⟨z, A⟩ ⟨hz, hA, hzA⟩
    exact ⟨⟨z, hz, rfl⟩, ⟨A, hA, rfl⟩, ⟨z, hzA, rfl⟩⟩
  have he_inj : Function.Injective (Prod.map fV (mapGraphEmb fV fE)) :=
    fun ⟨z₁, A₁⟩ ⟨z₂, A₂⟩ h =>
      Prod.ext (fV.injective (congrArg Prod.fst h))
        (mapGraphEmb_injective fV fE (congrArg Prod.snd h))
  have he_surj : ∀ q ∈ E(G₁), ∃ p ∈ E(G₂), Prod.map fV (mapGraphEmb fV fE) p = q := by
    rintro ⟨_, _⟩ ⟨⟨z, hz, rfl⟩, ⟨A, hA, rfl⟩, ⟨z₀, hz₀A, hz₀⟩⟩
    obtain rfl := (fV.injective hz₀).symm
    exact ⟨(z, A), ⟨hz, hA, hz₀A⟩, rfl⟩
  let eE : E(G₂) ≃ E(G₁) :=
    Equiv.ofBijective (fun p => ⟨Prod.map fV (mapGraphEmb fV fE) p.1, he_fwd p.1 p.2⟩)
      ⟨fun p₁ p₂ h => Subtype.ext (he_inj (congrArg Subtype.val h)),
       fun q => by
         obtain ⟨p, hp, heq⟩ := he_surj q.1 q.2
         exact ⟨⟨p, hp⟩, Subtype.ext heq⟩⟩
  refine
    { vertexEquiv := eV.symm
      edgeEquiv := eE.symm
      isLink_iff := fun q u v => ?_ }
  obtain ⟨p, rfl⟩ := Equiv.surjective eE q
  obtain ⟨x, rfl⟩ := Equiv.surjective eV u
  obtain ⟨y, rfl⟩ := Equiv.surjective eV v
  simp only [Equiv.symm_apply_apply]
  rcases p with ⟨⟨z, A⟩, hz, hA, hzA⟩
  change G₁.IsLink (fV z, mapGraphEmb fV fE A)
    (Sum.map fV (mapGraphEmb fV fE) x.1) (Sum.map fV (mapGraphEmb fV fE) y.1) ↔
    G₂.IsLink (z, A) x.1 y.1
  dsimp [G₁, G₂, divisionIncidenceGraph]
  constructor
  · rintro ⟨_, _, _, ⟨hx, hy⟩ | ⟨hx, hy⟩⟩
    · refine ⟨hz, hA, hzA, Or.inl ⟨?_, ?_⟩⟩
      · exact hv_inj (hx.trans rfl)
      · exact hv_inj (hy.trans rfl)
    · refine ⟨hz, hA, hzA, Or.inr ⟨?_, ?_⟩⟩
      · exact hv_inj (hx.trans rfl)
      · exact hv_inj (hy.trans rfl)
  · rintro ⟨_, _, _, ⟨hx, hy⟩ | ⟨hx, hy⟩⟩
    · refine ⟨⟨z, hz, rfl⟩, ⟨A, hA, rfl⟩, ⟨z, hzA, rfl⟩, Or.inl ⟨?_, ?_⟩⟩
      · rw [hx]; rfl
      · rw [hy]; rfl
    · refine ⟨⟨z, hz, rfl⟩, ⟨A, hA, rfl⟩, ⟨z, hzA, rfl⟩, Or.inr ⟨?_, ?_⟩⟩
      · rw [hx]; rfl
      · rw [hy]; rfl

@[simp]
theorem divisionIncidenceGraphIso_vertexEquiv_inl (fV : α ↪ α') (fE : β ↪ β')
    (Z : Set α) (𝒜 : Set (Graph α β)) (z : α)
    (hz' : Sum.inl (fV z) ∈ V(divisionIncidenceGraph (fV '' Z) (mapGraphEmb fV fE '' 𝒜)))
    (hz : Sum.inl z ∈ V(divisionIncidenceGraph Z 𝒜)) :
    (divisionIncidenceGraphIso fV fE Z 𝒜).vertexEquiv ⟨Sum.inl (fV z), hz'⟩ =
      ⟨Sum.inl z, hz⟩ := by
  apply (divisionIncidenceGraphIso fV fE Z 𝒜).vertexEquiv.symm.injective
  rw [Equiv.symm_apply_apply]
  rfl

theorem hasDiscDrawingWithBoundaryOrder_of_inGraph (fV : α ↪ α') (fE : β ↪ β')
    {ιV : S ↪ α'} {ν : S → α} {C₀ : Drawing S} {PiSet : Set S}
    {Z : Set α} {𝒜 : Set (Graph α β)}
    (hPi : ∀ p ∈ PiSet, ιV p = fV (ν p))
    (h : HasDiscDrawingWithBoundaryOrderInGraph ν C₀ PiSet Z 𝒜) :
    HasDiscDrawingWithBoundaryOrder ιV C₀ PiSet (fV '' Z) (mapGraphEmb fV fE '' 𝒜) := by
  obtain ⟨D_disc, gd, φ_C, φ_D, hD, hU, hPi_bd, hbd_iff, hord⟩ := h
  let iso₀ := divisionIncidenceGraphIso fV fE Z 𝒜
  let gd' : GraphDrawing (divisionIncidenceGraph (fV '' Z) (mapGraphEmb fV fE '' 𝒜))
      EuclideanPlane :=
    { drawing := gd.drawing
      iso :=
        { vertexEquiv := iso₀.vertexEquiv.trans gd.iso.vertexEquiv
          edgeEquiv := iso₀.edgeEquiv.trans gd.iso.edgeEquiv
          isLink_iff := fun e x y =>
            (iso₀.isLink_iff e x y).trans
              (gd.iso.isLink_iff (iso₀.edgeEquiv e) (iso₀.vertexEquiv x) (iso₀.vertexEquiv y)) } }
  have hmem_iff : ∀ z : α,
      Sum.inl (fV z) ∈ V(divisionIncidenceGraph (fV '' Z) (mapGraphEmb fV fE '' 𝒜)) ↔
        Sum.inl z ∈ V(divisionIncidenceGraph Z 𝒜) := by
    intro z
    change Sum.inl (fV z) ∈ (Sum.inl '' (fV '' Z) ∪ Sum.inr '' (mapGraphEmb fV fE '' 𝒜)) ↔
      Sum.inl z ∈ (Sum.inl '' Z ∪ Sum.inr '' 𝒜)
    simp only [mem_union, mem_image, Sum.inl.injEq, reduceCtorEq, and_false, exists_false, or_false]
    constructor
    · rintro ⟨_, ⟨z₀, hz₀, rfl⟩, h⟩
      exact ⟨z₀, hz₀, fV.injective h⟩
    · rintro ⟨z₀, hz₀, rfl⟩
      exact ⟨fV z₀, ⟨z₀, hz₀, rfl⟩, rfl⟩
  refine ⟨D_disc, gd', φ_C, φ_D, hD, hU, ?_, ?_, ?_⟩
  · intro p hp
    obtain ⟨hp₀, hp_bd⟩ := hPi_bd p hp
    have hp' : Sum.inl (ιV p) ∈ V(divisionIncidenceGraph (fV '' Z) (mapGraphEmb fV fE '' 𝒜)) := by
      rw [hPi p hp, hmem_iff]
      exact hp₀
    refine ⟨hp', ?_⟩
    have hsub : (⟨Sum.inl (ιV p), hp'⟩ :
        V(divisionIncidenceGraph (fV '' Z) (mapGraphEmb fV fE '' 𝒜))) =
        ⟨Sum.inl (fV (ν p)), (hmem_iff (ν p)).mpr hp₀⟩ :=
      Subtype.ext (congrArg Sum.inl (hPi p hp))
    change (gd.iso.vertexEquiv (iso₀.vertexEquiv ⟨Sum.inl (ιV p), hp'⟩)).1 ∈ subBd D_disc
    rw [hsub, divisionIncidenceGraphIso_vertexEquiv_inl]
    exact hp_bd
  · intro v'
    change (gd.iso.vertexEquiv (iso₀.vertexEquiv v')).1 ∈ subBd D_disc ↔ _
    rw [hbd_iff (iso₀.vertexEquiv v')]
    constructor
    · rintro ⟨p, hp, heq⟩
      refine ⟨p, hp, ?_⟩
      have h1 : v' = iso₀.vertexEquiv.symm (iso₀.vertexEquiv v') :=
        (iso₀.vertexEquiv.symm_apply_apply v').symm
      have h2 : (iso₀.vertexEquiv.symm (iso₀.vertexEquiv v')).1 =
          Sum.map fV (mapGraphEmb fV fE) (iso₀.vertexEquiv v').1 := rfl
      rw [h1, h2, heq, hPi p hp]
      rfl
    · rintro ⟨p, hp, heq⟩
      have hp' : Sum.inl (fV (ν p)) ∈
          V(divisionIncidenceGraph (fV '' Z) (mapGraphEmb fV fE '' 𝒜)) := by
        rw [← hPi p hp, ← heq]
        exact v'.2
      have hp₀ : Sum.inl (ν p) ∈ V(divisionIncidenceGraph Z 𝒜) := (hmem_iff (ν p)).mp hp'
      have hv' : v' = ⟨Sum.inl (fV (ν p)), hp'⟩ :=
        Subtype.ext (heq.trans (congrArg Sum.inl (hPi p hp)))
      refine ⟨p, hp, ?_⟩
      rw [hv', divisionIncidenceGraphIso_vertexEquiv_inl fV fE Z 𝒜 (ν p) hp' hp₀]
  · intro t₁ t₂ t₃ t₄ p₁ p₂ p₃ p₄ ht₁ ht₂ ht₃ ht₄ ht₅ hPi_eq hc₁ hc₂ hc₃ hc₄
    obtain ⟨s₁, s₂, s₃, s₄, hp₁, hp₂, hp₃, hp₄, hs₁, hs₂, hs₃, hs₄, hs₅, hd₁, hd₂, hd₃, hd₄⟩ :=
      hord t₁ t₂ t₃ t₄ p₁ p₂ p₃ p₄ ht₁ ht₂ ht₃ ht₄ ht₅ hPi_eq hc₁ hc₂ hc₃ hc₄
    have hp₁_mem : p₁ ∈ PiSet := hPi_eq ▸ by simp
    have hp₂_mem : p₂ ∈ PiSet := hPi_eq ▸ by simp
    have hp₃_mem : p₃ ∈ PiSet := hPi_eq ▸ by simp
    have hp₄_mem : p₄ ∈ PiSet := hPi_eq ▸ by simp
    have hp₁' : Sum.inl (ιV p₁) ∈ V(divisionIncidenceGraph (fV '' Z) (mapGraphEmb fV fE '' 𝒜)) := by
      rw [hPi p₁ hp₁_mem, hmem_iff]; exact hp₁
    have hp₂' : Sum.inl (ιV p₂) ∈ V(divisionIncidenceGraph (fV '' Z) (mapGraphEmb fV fE '' 𝒜)) := by
      rw [hPi p₂ hp₂_mem, hmem_iff]; exact hp₂
    have hp₃' : Sum.inl (ιV p₃) ∈ V(divisionIncidenceGraph (fV '' Z) (mapGraphEmb fV fE '' 𝒜)) := by
      rw [hPi p₃ hp₃_mem, hmem_iff]; exact hp₃
    have hp₄' : Sum.inl (ιV p₄) ∈ V(divisionIncidenceGraph (fV '' Z) (mapGraphEmb fV fE '' 𝒜)) := by
      rw [hPi p₄ hp₄_mem, hmem_iff]; exact hp₄
    refine ⟨s₁, s₂, s₃, s₄, hp₁', hp₂', hp₃', hp₄', hs₁, hs₂, hs₃, hs₄, hs₅, ?_, ?_, ?_, ?_⟩
    · have hsub : (⟨Sum.inl (ιV p₁), hp₁'⟩ :
          V(divisionIncidenceGraph (fV '' Z) (mapGraphEmb fV fE '' 𝒜))) =
          ⟨Sum.inl (fV (ν p₁)), (hmem_iff (ν p₁)).mpr hp₁⟩ :=
        Subtype.ext (congrArg Sum.inl (hPi p₁ hp₁_mem))
      change (φ_D (Circle.exp s₁)).1 =
        (gd.iso.vertexEquiv (iso₀.vertexEquiv ⟨Sum.inl (ιV p₁), hp₁'⟩)).1
      rw [hsub, divisionIncidenceGraphIso_vertexEquiv_inl]
      exact hd₁
    · have hsub : (⟨Sum.inl (ιV p₂), hp₂'⟩ :
          V(divisionIncidenceGraph (fV '' Z) (mapGraphEmb fV fE '' 𝒜))) =
          ⟨Sum.inl (fV (ν p₂)), (hmem_iff (ν p₂)).mpr hp₂⟩ :=
        Subtype.ext (congrArg Sum.inl (hPi p₂ hp₂_mem))
      change (φ_D (Circle.exp s₂)).1 =
        (gd.iso.vertexEquiv (iso₀.vertexEquiv ⟨Sum.inl (ιV p₂), hp₂'⟩)).1
      rw [hsub, divisionIncidenceGraphIso_vertexEquiv_inl]
      exact hd₂
    · have hsub : (⟨Sum.inl (ιV p₃), hp₃'⟩ :
          V(divisionIncidenceGraph (fV '' Z) (mapGraphEmb fV fE '' 𝒜))) =
          ⟨Sum.inl (fV (ν p₃)), (hmem_iff (ν p₃)).mpr hp₃⟩ :=
        Subtype.ext (congrArg Sum.inl (hPi p₃ hp₃_mem))
      change (φ_D (Circle.exp s₃)).1 =
        (gd.iso.vertexEquiv (iso₀.vertexEquiv ⟨Sum.inl (ιV p₃), hp₃'⟩)).1
      rw [hsub, divisionIncidenceGraphIso_vertexEquiv_inl]
      exact hd₃
    · have hsub : (⟨Sum.inl (ιV p₄), hp₄'⟩ :
          V(divisionIncidenceGraph (fV '' Z) (mapGraphEmb fV fE '' 𝒜))) =
          ⟨Sum.inl (fV (ν p₄)), (hmem_iff (ν p₄)).mpr hp₄⟩ :=
        Subtype.ext (congrArg Sum.inl (hPi p₄ hp₄_mem))
      change (φ_D (Circle.exp s₄)).1 =
        (gd.iso.vertexEquiv (iso₀.vertexEquiv ⟨Sum.inl (ιV p₄), hp₄'⟩)).1
      rw [hsub, divisionIncidenceGraphIso_vertexEquiv_inl]
      exact hd₄

/-- Formulation of `Hypotheses83` over `(α, β)` for a subgraph `K ≤ R_G.G.toGraph.deleteVerts W`
with a surface drawing `Γ_draw : GraphDrawing K S`, avoiding any requirement of an injection
`S ↪ α` or `Set S ↪ β`. -/
structure Hypotheses83InGraph [T2Space S] [Nonempty α] (q δ h θ : ℕ)
    (R_G : RootedDigraph α β q) (W : Set α)
    (K : Graph α β) (Γ_draw : GraphDrawing K S)
    (C₀ : Drawing S) (r₀ : Set S) (orient : GM19.SurfaceOrientation S)
    (PiSet : Set S)
    (ord : ℕ) (T : Set (Hypergraph S (Set S) × Hypergraph S (Set S)))
    (d : Set S → Set S → ℕ)
    (J : Graph α β) (Z : Set α) (𝒜 : Set (Graph α β))
    (πLen : Graph α β → ℕ) (πA : ∀ A : Graph α β, Fin (πLen A) → α)
    (vA : Graph α β → S) (D_disc : Set S) (v_star : S) : Prop where
  /-- $V(G)$ is finite. -/
  finite_V : V(R_G.G.toGraph).Finite
  /-- $E(G)$ is finite. -/
  finite_E : E(R_G.G.toGraph).Finite
  /-- $W \subseteq V(G)$ and $\omega$ is an ordering of $W$. -/
  ordering_W : W ⊆ V(R_G.G.toGraph) ∧ IsOrderingOf W R_G.roots
  /-- $K \subseteq G \setminus W$. -/
  K_le : K ≤ R_G.G.toGraph.deleteVerts W
  /-- (i) $\Sigma$ is a sphere and $\Gamma$ is a subdivision of a simple 3-connected graph. -/
  hyp_i : IsSphere S ∧ IsSubdivisionOfSimpleThreeConnected Γ_draw.drawing.toGraph
  /-- (ii) $C_0$ is a circuit of $\Gamma$, and $U(C_0)$ bounds a region $r_0$ of $\Gamma$. -/
  hyp_ii : C₀.IsSubdrawing Γ_draw.drawing ∧ C₀.IsCircuit ∧ r₀ ∈ Γ_draw.drawing.R ∧ subBd r₀ = C₀.U
  /-- (iii) $\Pi \subseteq V(C_0)$ with $|\Pi| = 4$. -/
  hyp_iii : PiSet ⊆ C₀.V ∧ PiSet.ncard = 4
  /-- (iv) $\mathcal{T}$ is a respectful tangle in $\Gamma$ of order `ord ≥ θ` with metric $d$, and
  there is no $(A, B) \in \mathcal{T}$ with order $\le 3$ such that $\Pi \subseteq V(A)$. -/
  hyp_iv : θ ≤ ord ∧ HasTangleMetric Γ_draw.drawing ord T d ∧
    ∀ A B : Hypergraph S (Set S), (A, B) ∈ T → separationOrder A B ≤ 3 → ¬ (PiSet ⊆ A.vertexSet)
  /-- (v) $J \subseteq G$ has vertex set the union of $W$, $V(K)$, and the vertex sets of all
  components of $G \setminus (V(C_0) \cup W)$ which meet $V(K)$, and edge set all edges of $G$
  with both ends in $V(J)$. -/
  hyp_v : J ≤ R_G.G.toGraph ∧
    J = R_G.G.toGraph.induce
      (W ∪ V(K) ∪
        ⋃ C ∈ {C ∈ graphComponents
          (R_G.G.toGraph.deleteVerts ((drawingVertToGraph Γ_draw '' C₀.V) ∪ W)) |
          (V(C) ∩ V(K)).Nonempty}, V(C))
  /-- (vi) $Z \subseteq V(J) \setminus W$ with $\Pi \subseteq Z$, and $\mathcal{A}$ is a
  $(Z \cup W)$-division of $J$, such that $W \subseteq V(A)$ for all $A \in \mathcal{A}$. -/
  hyp_vi : Z ⊆ V(J) \ W ∧ drawingVertToGraph Γ_draw '' PiSet ⊆ Z ∧
    IsZDivision J (Z ∪ W) 𝒜 ∧ ∀ A ∈ 𝒜, W ⊆ V(A)
  /-- (vii) For each $A \in \mathcal{A}$, $Z \cap V(A) = \bar{\pi}(A)$, $|\bar{\pi}(A)| \le 3$, and
  $\pi(A)$ is a linear order of $\bar{\pi}(A)$. -/
  hyp_vii : ∀ A ∈ 𝒜, πLen A ≤ 3 ∧ IsOrderingOf (Z ∩ V(A)) (πA A)
  /-- (viii) For each $A \in \mathcal{A}$, there are $|\bar{\pi}(A)|$ mutually vertex-disjoint
  paths of $J \setminus W$ between $\bar{\pi}(A)$ and $\Pi$, preserving clockwise order when
  $|\bar{\pi}(A)| = 3$. -/
  hyp_viii : ∀ A ∈ 𝒜,
    ∃ (P : Fin (πLen A) → Graph α β) (t : Fin (πLen A) → S),
      (∀ i : Fin (πLen A), t i ∈ PiSet ∧
        IsGraphPathWithEnds (J.deleteVerts W) (P i) (πA A i) (drawingVertToGraph Γ_draw (t i))) ∧
      Pairwise (fun i j : Fin (πLen A) => Disjoint V(P i) V(P j)) ∧
      (∀ h3 : πLen A = 3,
        orient.pos (Set.univ \ r₀) (t ⟨0, by omega⟩) (t ⟨1, by omega⟩) (t ⟨2, by omega⟩))
  /-- (ix) For each $A \in \mathcal{A}$, if $u, v \in \bar{\pi}(A)$ there is a path of
  $A \setminus W$ between $u$ and $v$ with no internal vertex in $\bar{\pi}(A)$. -/
  hyp_ix : ∀ A ∈ 𝒜, ∀ u ∈ Z ∩ V(A), ∀ v ∈ Z ∩ V(A),
    ∃ P : Graph α β, IsGraphPathWithEnds (A.deleteVerts W) P u v ∧
      Disjoint (pathInternalVerts (A.deleteVerts W) P) (Z ∩ V(A))
  /-- (x) The bipartite incidence graph $G'$ on $Z \cup \mathcal{A}$ can be drawn in a closed disc
  with $\Pi$ in the boundary in the order of $U(C_0)$. -/
  hyp_x : HasDiscDrawingWithBoundaryOrderInGraph (drawingVertToGraph Γ_draw) C₀ PiSet Z 𝒜
  /-- (xi) For each $A \in \mathcal{A}$, $v(A) \in V(\Gamma)$ and there is a path of $G \setminus W$
  between $v(A)$ and a vertex of $\bar{\pi}(A)$ with no vertex in $V(K)$ except $v(A)$. -/
  hyp_xi : ∀ A ∈ 𝒜, vA A ∈ Γ_draw.drawing.V ∧
    ∃ u ∈ Z ∩ V(A), ∃ P : Graph α β,
      IsGraphPathWithEnds (R_G.G.toGraph.deleteVerts W) P (drawingVertToGraph Γ_draw (vA A)) u ∧
      V(P) ∩ V(K) = {drawingVertToGraph Γ_draw (vA A)}
  /-- (xii) $D \subseteq \Sigma$ is a closed disc with $\operatorname{bd}(D) \subseteq U(\Gamma)$
  including the region $r_0$ of $\Gamma$ bounded by $U(C_0)$. -/
  hyp_xii : IsClosedDisc D_disc ∧ subBd D_disc ⊆ Γ_draw.drawing.U ∧ r₀ ⊆ D_disc
  /-- (xiii) Homogeneity condition outside $D$. -/
  hyp_xiii : ∀ (A : Graph α β) (hA : A ∈ 𝒜), vA A ∈ Set.univ \ D_disc →
    ∀ v ∈ Γ_draw.drawing.V \ D_disc,
      subsetTangleDist Γ_draw.drawing ord d {v} D_disc ≤ h ∨
        ∃ (A' : Graph α β) (hA' : A' ∈ 𝒜),
          subsetTangleDist Γ_draw.drawing ord d {v} {vA A'} ≤ h ∧
          ∃ hlen : πLen A' = πLen A,
            HasSameDeltaFolio
              (subRootedDigraph R_G.G A' ((hyp_vi.2.2.1.2.1 A' hA').trans hyp_v.1)
                (seqConcat (πA A' ∘ Fin.cast hlen.symm) R_G.roots)
                (seqConcat_mem
                  (fun j => ((hyp_vii A' hA').2.2.subset ⟨Fin.cast hlen.symm j, rfl⟩).2)
                  (fun j => hyp_vi.2.2.2 A' hA' (ordering_W.2.2.subset ⟨j, rfl⟩))))
              (subRootedDigraph R_G.G A ((hyp_vi.2.2.1.2.1 A hA).trans hyp_v.1)
                (seqConcat (πA A) R_G.roots)
                (seqConcat_mem
                  (fun j => ((hyp_vii A hA).2.2.subset ⟨j, rfl⟩).2)
                  (fun j => hyp_vi.2.2.2 A hA (ordering_W.2.2.subset ⟨j, rfl⟩))))
              δ
  /-- (xiv) $v^* \in V(\Gamma) \setminus D$ and $d(v^*, D) \ge \theta$. -/
  hyp_xiv : v_star ∈ Γ_draw.drawing.V \ D_disc ∧
    θ ≤ subsetTangleDist Γ_draw.drawing ord d {v_star} D_disc

theorem Hypotheses83InGraph.roots_mem_deleteVerts_v_star [T2Space S] [Nonempty α]
    {q δ h θ : ℕ} {R_G : RootedDigraph α β q} {W : Set α}
    {K : Graph α β} {Γ_draw : GraphDrawing K S}
    {C₀ : Drawing S} {r₀ : Set S} {orient : GM19.SurfaceOrientation S}
    {PiSet : Set S}
    {ord : ℕ} {T : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    {d : Set S → Set S → ℕ}
    {J : Graph α β} {Z : Set α} {𝒜 : Set (Graph α β)}
    {πLen : Graph α β → ℕ} {πA : ∀ A : Graph α β, Fin (πLen A) → α}
    {vA : Graph α β → S} {D_disc : Set S} {v_star : S}
    (h83 : Hypotheses83InGraph q δ h θ R_G W K Γ_draw C₀ r₀ orient PiSet ord T d J Z 𝒜
      πLen πA vA D_disc v_star) (i : Fin q) :
    R_G.roots i ∈ V(R_G.G.toGraph.deleteVerts {drawingVertToGraph Γ_draw v_star}) := by
  rw [Graph.vertexSet_deleteVerts]
  refine ⟨R_G.roots_mem i, ?_⟩
  rw [mem_singleton_iff]
  intro heq
  have hv_K : drawingVertToGraph Γ_draw v_star ∈ V(K) :=
    (vertexEquiv_drawingVertToGraph Γ_draw h83.hyp_xiv.1.1).1
  have hv_del : drawingVertToGraph Γ_draw v_star ∈ V(R_G.G.toGraph) \ W :=
    R_G.G.toGraph.vertexSet_deleteVerts W ▸ h83.K_le.vertexSet_mono hv_K
  exact hv_del.2 (heq ▸ h83.ordering_W.2.2 ▸ mem_range_self i)

private theorem πA_congr_eq {πLen : Graph α β → ℕ} {πA : ∀ A : Graph α β, Fin (πLen A) → α}
    {B₁ B₂ : Graph α β} (hB : B₁ = B₂) (i : Fin (πLen B₁)) :
    πA B₁ i = πA B₂ (Fin.cast (congrArg πLen hB) i) := by
  subst hB; rfl

/-- **Theorem 8.3 for a `GraphDrawing K S` over arbitrary `(α, β)`.** -/
theorem theorem_8_3_in_graph  (q δ h : ℕ) :
    ∃ θ : ℕ, h ≤ θ ∧ 4 ≤ θ ∧
      ∀ {S : Type} [TopologicalSpace S] [T2Space S]
        {α : Type u} {β : Type v} [Nonempty α] [Nonempty β]
        (R_G : RootedDigraph α β q) (W : Set α)
        (K : Graph α β) (Γ_draw : GraphDrawing K S)
        (C₀ : Drawing S) (r₀ : Set S) (orient : GM19.SurfaceOrientation S)
        (PiSet : Set S)
        (ord : ℕ) (T : Set (Hypergraph S (Set S) × Hypergraph S (Set S)))
        (d : Set S → Set S → ℕ)
        (J : Graph α β) (Z : Set α) (𝒜 : Set (Graph α β))
        (πLen : Graph α β → ℕ) (πA : ∀ A : Graph α β, Fin (πLen A) → α)
        (vA : Graph α β → S) (D_disc : Set S) (v_star : S)
        (h83 : Hypotheses83InGraph q δ h θ R_G W K Γ_draw C₀ r₀ orient PiSet ord T d J Z 𝒜
          πLen πA vA D_disc v_star),
        HasSameDeltaFolio
          (subRootedDigraph R_G.G
            (R_G.G.toGraph.deleteVerts {drawingVertToGraph Γ_draw v_star})
            Graph.deleteVerts_le R_G.roots h83.roots_mem_deleteVerts_v_star)
          R_G δ := by
  obtain ⟨θ, hhθ, h4θ, hθ_spec⟩ := theorem_8_3_proof.{0, u, v} q δ h
  refine ⟨θ, hhθ, h4θ, ?_⟩
  intro S _ _ α β _ _ R_G W K Γ_draw C₀ r₀ orient PiSet ord T d J Z 𝒜 πLen πA vA D_disc v_star h83
  let α' : Type u := α ⊕ ULift.{u} S
  let β' : Type v := β ⊕ ULift.{v} (Set S)
  let fV : α ↪ α' := Function.Embedding.inl
  let fE : β ↪ β' := Function.Embedding.inl
  let ιV : S ↪ α' := graphDrawingEmbV Γ_draw
  let ιE : Set S ↪ β' := graphDrawingEmbE Γ_draw
  let R_G' : RootedDigraph α' β' q := mapRootedDigraphEmb fV fE R_G
  let W' : Set α' := fV '' W
  let J' : Graph α' β' := mapGraphEmb fV fE J
  let Z' : Set α' := fV '' Z
  let 𝒜' : Set (Graph α' β') := mapGraphEmb fV fE '' 𝒜
  let unmapA (A' : Graph α' β') : Graph α β := unmapSubgraphEmb fV fE R_G.G.toGraph A'
  have hunmapA_eq : ∀ A ∈ 𝒜, unmapA (mapGraphEmb fV fE A) = A := by
    intro A hA
    have hA_le_G : A ≤ R_G.G.toGraph := (h83.hyp_vi.2.2.1.2.1 A hA).trans h83.hyp_v.1
    apply mapGraphEmb_injective fV fE
    exact mapGraphEmb_unmapSubgraphEmb fV fE ((mapGraphEmb_le_iff fV fE).mpr hA_le_G)
  let πLen' (A' : Graph α' β') : ℕ := πLen (unmapA A')
  let πA' (A' : Graph α' β') : Fin (πLen' A') → α' := fV ∘ πA (unmapA A')
  let vA' (A' : Graph α' β') : S := vA (unmapA A')
  have hιV_V : ιV '' Γ_draw.drawing.V = fV '' V(K) := by
    rw [image_graphDrawingEmbV_subset_V Γ_draw Subset.rfl, image_drawingVertToGraph_V]
  have hC₀_sub_V : C₀.V ⊆ Γ_draw.drawing.V := h83.hyp_ii.1.1
  have hιV_C₀V : ιV '' C₀.V = fV '' (drawingVertToGraph Γ_draw '' C₀.V) :=
    image_graphDrawingEmbV_subset_V Γ_draw hC₀_sub_V
  have hPi_sub_V : PiSet ⊆ Γ_draw.drawing.V := h83.hyp_iii.1.trans hC₀_sub_V
  have hιV_Pi : ιV '' PiSet = fV '' (drawingVertToGraph Γ_draw '' PiSet) :=
    image_graphDrawingEmbV_subset_V Γ_draw hPi_sub_V
  have h_ord' : W' ⊆ V(R_G'.G.toGraph) ∧ IsOrderingOf W' R_G'.roots :=
    ⟨image_mono h83.ordering_W.1,
      ⟨fV.injective.comp h83.ordering_W.2.1, by
        rw [Set.range_comp, h83.ordering_W.2.2]⟩⟩
  have h_Γ_le' : Γ_draw.drawing.toEmbeddedGraph ιV ιE ≤ R_G'.G.toGraph.deleteVerts W' := by
    change (Γ_draw.drawing.toEmbeddedGraph ιV ιE) ≤ (mapGraphEmb fV fE R_G.G.toGraph).deleteVerts (fV '' W)
    rw [toEmbeddedGraph_graphDrawingEmb_eq, ← mapGraphEmb_deleteVerts]
    exact (mapGraphEmb_le_iff fV fE).mpr h83.K_le
  have h_v' : J' ≤ R_G'.G.toGraph ∧
      J' = R_G'.G.toGraph.induce
        (W' ∪ (ιV '' Γ_draw.drawing.V) ∪
          ⋃ C' ∈ {C' ∈ graphComponents (R_G'.G.toGraph.deleteVerts ((ιV '' C₀.V) ∪ W')) |
            (V(C') ∩ (ιV '' Γ_draw.drawing.V)).Nonempty}, V(C')) := by
    refine ⟨(mapGraphEmb_le_iff fV fE).mpr h83.hyp_v.1, ?_⟩
    change mapGraphEmb fV fE J =
      (mapGraphEmb fV fE R_G.G.toGraph).induce
        ((fV '' W) ∪ (ιV '' Γ_draw.drawing.V) ∪
          ⋃ C' ∈ {C' ∈ graphComponents
            ((mapGraphEmb fV fE R_G.G.toGraph).deleteVerts ((ιV '' C₀.V) ∪ (fV '' W))) |
            (V(C') ∩ (ιV '' Γ_draw.drawing.V)).Nonempty}, V(C'))
    rw [hιV_V, hιV_C₀V, ← Set.image_union, ← Set.image_union, ← mapGraphEmb_deleteVerts,
        biUnion_graphComponents_mapGraphEmb, ← Set.image_union, ← mapGraphEmb_induce,
        ← h83.hyp_v.2]
  have h_vi' : Z' ⊆ V(J') \ W' ∧ ιV '' PiSet ⊆ Z' ∧ IsZDivision J' (Z' ∪ W') 𝒜' ∧
      ∀ A' ∈ 𝒜', W' ⊆ V(A') := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [vertexSet_mapGraphEmb, ← Set.image_sdiff fV.injective]
      exact image_mono h83.hyp_vi.1
    · rw [hιV_Pi]
      exact image_mono h83.hyp_vi.2.1
    · rw [← Set.image_union]
      exact isZDivision_mapGraphEmb fV fE h83.hyp_vi.2.2.1
    · rintro _ ⟨A, hA, rfl⟩
      exact image_mono (h83.hyp_vi.2.2.2 A hA)
  have h_vii' : ∀ A' ∈ 𝒜', πLen' A' ≤ 3 ∧ IsOrderingOf (Z' ∩ V(A')) (πA' A') := by
    rintro _ ⟨A, hA, rfl⟩
    dsimp only [πLen', πA']
    rw [hunmapA_eq A hA]
    obtain ⟨hlen, hinj, hrange⟩ := h83.hyp_vii A hA
    refine ⟨hlen, fV.injective.comp hinj, ?_⟩
    rw [Set.range_comp, hrange, vertexSet_mapGraphEmb, Set.image_inter fV.injective]
  have h_viii' : ∀ A' ∈ 𝒜',
      ∃ (P : Fin (πLen' A') → Graph α' β') (t : Fin (πLen' A') → S),
        (∀ i : Fin (πLen' A'), t i ∈ PiSet ∧
          IsGraphPathWithEnds (J'.deleteVerts W') (P i) (πA' A' i) (ιV (t i))) ∧
        Pairwise (fun i j : Fin (πLen' A') => Disjoint V(P i) V(P j)) ∧
        (∀ h3 : πLen' A' = 3,
          orient.pos (Set.univ \ r₀) (t ⟨0, by omega⟩) (t ⟨1, by omega⟩) (t ⟨2, by omega⟩)) := by
    rintro _ ⟨A, hA, rfl⟩
    have h1 : unmapA (mapGraphEmb fV fE A) = A := hunmapA_eq A hA
    have hcast : πLen' (mapGraphEmb fV fE A) = πLen A := congrArg πLen h1
    obtain ⟨P, t, htP, hdisj, hcw⟩ := h83.hyp_viii A hA
    refine ⟨fun i => mapGraphEmb fV fE (P (Fin.cast hcast i)),
      fun i => t (Fin.cast hcast i), ?_, ?_, ?_⟩
    · intro i
      obtain ⟨hti, hPi⟩ := htP (Fin.cast hcast i)
      refine ⟨hti, ?_⟩
      have hti_V : t (Fin.cast hcast i) ∈ Γ_draw.drawing.V := hPi_sub_V hti
      have hιV_ti :
          ιV (t (Fin.cast hcast i)) =
            fV (drawingVertToGraph Γ_draw (t (Fin.cast hcast i))) :=
        graphDrawingEmbV_of_mem_V Γ_draw hti_V
      rw [hιV_ti]
      have hπ_eq : πA' (mapGraphEmb fV fE A) i = fV (πA A (Fin.cast hcast i)) :=
        congrArg fV (πA_congr_eq h1 i)
      rw [hπ_eq]
      change IsGraphPathWithEnds ((mapGraphEmb fV fE J).deleteVerts (fV '' W))
        (mapGraphEmb fV fE (P (Fin.cast hcast i)))
        (fV (πA A (Fin.cast hcast i)))
        (fV (drawingVertToGraph Γ_draw (t (Fin.cast hcast i))))
      rw [← mapGraphEmb_deleteVerts]
      exact isGraphPathWithEnds_mapGraphEmb fV fE hPi
    · intro i j hij
      have hij' : Fin.cast hcast i ≠ Fin.cast hcast j := fun h => hij (Fin.ext (by simpa using congrArg Fin.val h))
      exact Set.disjoint_image_of_injective fV.injective (hdisj hij')
    · intro h3
      exact hcw (hcast.symm.trans h3)
  have h_ix' : ∀ A' ∈ 𝒜', ∀ u' ∈ Z' ∩ V(A'), ∀ v' ∈ Z' ∩ V(A'),
      ∃ P' : Graph α' β', IsGraphPathWithEnds (A'.deleteVerts W') P' u' v' ∧
        Disjoint (pathInternalVerts (A'.deleteVerts W') P') (Z' ∩ V(A')) := by
    rintro _ ⟨A, hA, rfl⟩ _ ⟨⟨u, huZ, rfl⟩, ⟨u₀, hu₀A, hu₀⟩⟩
      _ ⟨⟨v, hvZ, rfl⟩, ⟨v₀, hv₀A, hv₀⟩⟩
    obtain rfl := (fV.injective hu₀).symm
    obtain rfl := (fV.injective hv₀).symm
    obtain ⟨P, hP, hdisj⟩ := h83.hyp_ix A hA u ⟨huZ, hu₀A⟩ v ⟨hvZ, hv₀A⟩
    refine ⟨mapGraphEmb fV fE P, ?_, ?_⟩
    · change IsGraphPathWithEnds ((mapGraphEmb fV fE A).deleteVerts (fV '' W))
        (mapGraphEmb fV fE P) (fV u) (fV v)
      rw [← mapGraphEmb_deleteVerts]
      exact isGraphPathWithEnds_mapGraphEmb fV fE hP
    · change Disjoint
        (pathInternalVerts ((mapGraphEmb fV fE A).deleteVerts (fV '' W))
          (mapGraphEmb fV fE P))
        ((fV '' Z) ∩ V(mapGraphEmb fV fE A))
      rw [← mapGraphEmb_deleteVerts, pathInternalVerts_mapGraphEmb fV fE hP,
          vertexSet_mapGraphEmb, ← Set.image_inter fV.injective]
      exact Set.disjoint_image_of_injective fV.injective hdisj
  have h_xi' : ∀ A' ∈ 𝒜', vA' A' ∈ Γ_draw.drawing.V ∧
      ∃ u' ∈ Z' ∩ V(A'), ∃ P' : Graph α' β',
        IsGraphPathWithEnds (R_G'.G.toGraph.deleteVerts W') P' (ιV (vA' A')) u' ∧
        V(P') ∩ (ιV '' Γ_draw.drawing.V) = {ιV (vA' A')} := by
    rintro _ ⟨A, hA, rfl⟩
    dsimp only [vA']
    rw [hunmapA_eq A hA]
    obtain ⟨hvA_V, u, ⟨huZ, huA⟩, P, hP, hinter⟩ := h83.hyp_xi A hA
    refine ⟨hvA_V, fV u, ⟨⟨u, huZ, rfl⟩, ⟨u, huA, rfl⟩⟩, mapGraphEmb fV fE P, ?_, ?_⟩
    · have hιV_vA : ιV (vA A) = fV (drawingVertToGraph Γ_draw (vA A)) :=
        graphDrawingEmbV_of_mem_V Γ_draw hvA_V
      rw [hιV_vA]
      change IsGraphPathWithEnds ((mapGraphEmb fV fE R_G.G.toGraph).deleteVerts (fV '' W))
        (mapGraphEmb fV fE P) (fV (drawingVertToGraph Γ_draw (vA A))) (fV u)
      rw [← mapGraphEmb_deleteVerts]
      exact isGraphPathWithEnds_mapGraphEmb fV fE hP
    · have hιV_vA : ιV (vA A) = fV (drawingVertToGraph Γ_draw (vA A)) :=
        graphDrawingEmbV_of_mem_V Γ_draw hvA_V
      rw [hιV_vA, hιV_V, vertexSet_mapGraphEmb, ← Set.image_inter fV.injective, hinter,
          Set.image_singleton]
  have h_xiii' : ∀ (A_sub : Graph α' β') (hA_sub : A_sub ∈ 𝒜'),
      vA' A_sub ∈ Set.univ \ D_disc → ∀ v ∈ Γ_draw.drawing.V \ D_disc,
      subsetTangleDist Γ_draw.drawing ord d {v} D_disc ≤ h ∨
        ∃ (A₁_sub : Graph α' β') (hA₁_sub : A₁_sub ∈ 𝒜'),
          subsetTangleDist Γ_draw.drawing ord d {v} {vA' A₁_sub} ≤ h ∧
          ∃ hlen : πLen' A₁_sub = πLen' A_sub,
            HasSameDeltaFolio
              (subRootedDigraph R_G'.G A₁_sub ((h_vi'.2.2.1.2.1 A₁_sub hA₁_sub).trans h_v'.1)
                (seqConcat (πA' A₁_sub ∘ Fin.cast hlen.symm) R_G'.roots)
                (seqConcat_mem
                  (fun j => ((h_vii' A₁_sub hA₁_sub).2.2.subset ⟨Fin.cast hlen.symm j, rfl⟩).2)
                  (fun j => h_vi'.2.2.2 A₁_sub hA₁_sub (h_ord'.2.2.subset ⟨j, rfl⟩))))
              (subRootedDigraph R_G'.G A_sub ((h_vi'.2.2.1.2.1 A_sub hA_sub).trans h_v'.1)
                (seqConcat (πA' A_sub) R_G'.roots)
                (seqConcat_mem
                  (fun j => ((h_vii' A_sub hA_sub).2.2.subset ⟨j, rfl⟩).2)
                  (fun j => h_vi'.2.2.2 A_sub hA_sub (h_ord'.2.2.subset ⟨j, rfl⟩))))
              δ := by
    rintro _ ⟨A, hA, rfl⟩ hvA_out v hv_out
    dsimp only [vA'] at hvA_out
    rw [hunmapA_eq A hA] at hvA_out
    rcases h83.hyp_xiii A hA hvA_out v hv_out with hd_le | ⟨A₁, hA₁, hd_v, hlen, hfolio⟩
    · exact Or.inl hd_le
    · right
      refine ⟨mapGraphEmb fV fE A₁, ⟨A₁, hA₁, rfl⟩, ?_, ?_⟩
      · dsimp only [vA']
        rw [hunmapA_eq A₁ hA₁]
        exact hd_v
      · have hlen' : πLen' (mapGraphEmb fV fE A₁) = πLen' (mapGraphEmb fV fE A) := by
          dsimp only [πLen']
          rw [hunmapA_eq A₁ hA₁, hunmapA_eq A hA]
          exact hlen
        refine ⟨hlen', ?_⟩
        intro αH βH R_H hDet
        have hA₁_le : A₁ ≤ R_G.G.toGraph := (h83.hyp_vi.2.2.1.2.1 A₁ hA₁).trans h83.hyp_v.1
        have hA_le : A ≤ R_G.G.toGraph := (h83.hyp_vi.2.2.1.2.1 A hA).trans h83.hyp_v.1
        have hA₁'_le : mapGraphEmb fV fE A₁ ≤ (mapDigraphEmb fV fE R_G.G).toGraph :=
          (mapGraphEmb_le_iff fV fE).mpr hA₁_le
        have hA'_le : mapGraphEmb fV fE A ≤ (mapDigraphEmb fV fE R_G.G).toGraph :=
          (mapGraphEmb_le_iff fV fE).mpr hA_le
        let roots₁ := seqConcat (πA A₁ ∘ Fin.cast hlen.symm) R_G.roots
        let roots₂ := seqConcat (πA A) R_G.roots
        have hroots₁ : ∀ j, roots₁ j ∈ V(A₁) :=
          seqConcat_mem
            (fun j => ((h83.hyp_vii A₁ hA₁).2.2.subset ⟨Fin.cast hlen.symm j, rfl⟩).2)
            (fun j => h83.hyp_vi.2.2.2 A₁ hA₁ (h83.ordering_W.2.2.subset ⟨j, rfl⟩))
        have hroots₂ : ∀ j, roots₂ j ∈ V(A) :=
          seqConcat_mem
            (fun j => ((h83.hyp_vii A hA).2.2.subset ⟨j, rfl⟩).2)
            (fun j => h83.hyp_vi.2.2.2 A hA (h83.ordering_W.2.2.subset ⟨j, rfl⟩))
        have hroots₁' : ∀ j, (fV ∘ roots₁) j ∈ V(mapGraphEmb fV fE A₁) :=
          fun j => ⟨roots₁ j, hroots₁ j, rfl⟩
        have hroots₂' : ∀ j, (fV ∘ roots₂) j ∈ V(mapGraphEmb fV fE A) :=
          fun j => ⟨roots₂ j, hroots₂ j, rfl⟩
        have hcast_eq : πLen' (mapGraphEmb fV fE A) = πLen A :=
          congrArg πLen (hunmapA_eq A hA)
        have hcast_eq_q : πLen' (mapGraphEmb fV fE A) + q = πLen A + q :=
          congrArg (· + q) hcast_eq
        have hseq₁ :
            ∀ k : Fin (πLen' (mapGraphEmb fV fE A) + q),
              seqConcat (πA' (mapGraphEmb fV fE A₁) ∘ Fin.cast hlen'.symm) R_G'.roots k =
                (fV ∘ roots₁) (Fin.cast hcast_eq_q k) := by
          intro k
          refine Fin.addCases (fun i => ?_) (fun j => ?_) k
          · dsimp only [roots₁, seqConcat, πA', Function.comp_apply]
            rw [Fin.append_left]
            have h1 : unmapA (mapGraphEmb fV fE A₁) = A₁ := hunmapA_eq A₁ hA₁
            have hcast_i :
                Fin.cast hcast_eq_q (Fin.castAdd q i) =
                  Fin.castAdd q (Fin.cast hcast_eq i) := by
              ext; rfl
            rw [hcast_i, Fin.append_left]
            dsimp only [Function.comp_apply]
            have hπ₁ := congrArg fV (πA_congr_eq (πA := πA) h1 (Fin.cast hlen'.symm i))
            rw [hπ₁]
            congr 2
          · dsimp only [roots₁, seqConcat, R_G', mapRootedDigraphEmb, Function.comp_apply]
            rw [Fin.append_right]
            have hcast_j :
                Fin.cast hcast_eq_q (Fin.natAdd (πLen' (mapGraphEmb fV fE A)) j) =
                  Fin.natAdd (πLen A) j := by
              ext; dsimp [Fin.cast, Fin.natAdd]; omega
            rw [hcast_j, Fin.append_right]
            rfl
        have hseq₂ :
            ∀ k : Fin (πLen' (mapGraphEmb fV fE A) + q),
              seqConcat (πA' (mapGraphEmb fV fE A)) R_G'.roots k =
                (fV ∘ roots₂) (Fin.cast hcast_eq_q k) := by
          intro k
          refine Fin.addCases (fun i => ?_) (fun j => ?_) k
          · dsimp only [roots₂, seqConcat, πA', Function.comp_apply]
            rw [Fin.append_left]
            have h1 : unmapA (mapGraphEmb fV fE A) = A := hunmapA_eq A hA
            have hcast_i :
                Fin.cast hcast_eq_q (Fin.castAdd q i) =
                  Fin.castAdd q (Fin.cast hcast_eq i) := by
              ext; rfl
            rw [hcast_i, Fin.append_left]
            exact congrArg fV (πA_congr_eq (πA := πA) h1 i)
          · dsimp only [roots₂, seqConcat, R_G', mapRootedDigraphEmb, Function.comp_apply]
            rw [Fin.append_right]
            have hcast_j :
                Fin.cast hcast_eq_q (Fin.natAdd (πLen' (mapGraphEmb fV fE A)) j) =
                  Fin.natAdd (πLen A) j := by
              ext; dsimp [Fin.cast, Fin.natAdd]; omega
            rw [hcast_j, Fin.append_right]
            rfl
        have hfolio' :
            HasSameDeltaFolio
              (subRootedDigraph R_G'.G (mapGraphEmb fV fE A₁) hA₁'_le
                (fV ∘ roots₁) hroots₁')
              (subRootedDigraph R_G'.G (mapGraphEmb fV fE A) hA'_le
                (fV ∘ roots₂) hroots₂') δ := by
          intro αH₀ βH₀ R_H₀ hDet₀
          exact (hasRootedDigraphModel_subRootedDigraph_mapDigraphEmb_iff fV fE R_G.G A₁
              hA₁_le roots₁ hroots₁ hA₁'_le hroots₁' R_H₀).trans
            ((hfolio R_H₀ hDet₀).trans
              (hasRootedDigraphModel_subRootedDigraph_mapDigraphEmb_iff fV fE R_G.G A
                hA_le roots₂ hroots₂ hA'_le hroots₂' R_H₀).symm)
        exact hasSameDeltaFolio_subRootedDigraph_cast hA₁'_le hA'_le hA₁'_le hA'_le
          hcast_eq _ _ _ _ hseq₁ hseq₂
          (fun k => by rw [hseq₁ k]; exact hroots₁' _)
          (fun k => by rw [hseq₂ k]; exact hroots₂' _)
          hroots₁' hroots₂' hfolio' R_H hDet
  have h83' : Hypotheses83 q δ h θ ιV ιE R_G' W' Γ_draw.drawing C₀ r₀ orient PiSet ord T d
      J' Z' 𝒜' πLen' πA' vA' D_disc v_star :=
    { finite_V := h83.finite_V.image fV
      finite_E := h83.finite_E.image fE
      ordering_W := h_ord'
      Γ_le := h_Γ_le'
      hyp_i := h83.hyp_i
      hyp_ii := h83.hyp_ii
      hyp_iii := h83.hyp_iii
      hyp_iv := h83.hyp_iv
      hyp_v := h_v'
      hyp_vi := h_vi'
      hyp_vii := h_vii'
      hyp_viii := h_viii'
      hyp_ix := h_ix'
      hyp_x := hasDiscDrawingWithBoundaryOrder_of_inGraph fV fE
        (fun p hp => graphDrawingEmbV_of_mem_V Γ_draw (hPi_sub_V hp)) h83.hyp_x
      hyp_xi := h_xi'
      hyp_xii := h83.hyp_xii
      hyp_xiii := h_xiii'
      hyp_xiv := h83.hyp_xiv }
  intro αH βH R_H hDet
  have hfolio' := hθ_spec ιV ιE R_G' W' Γ_draw.drawing C₀ r₀ orient PiSet ord T d
    J' Z' 𝒜' πLen' πA' vA' D_disc v_star h83' R_H hDet
  have hv_star_eq : ιV v_star = fV (drawingVertToGraph Γ_draw v_star) :=
    graphDrawingEmbV_of_mem_V Γ_draw h83.hyp_xiv.1.1
  have hdel_eq :
      R_G'.G.toGraph.deleteVerts {ιV v_star} =
        mapGraphEmb fV fE (R_G.G.toGraph.deleteVerts {drawingVertToGraph Γ_draw v_star}) := by
    rw [hv_star_eq, mapGraphEmb_deleteVerts, Set.image_singleton]
  have hdel'_le :
      mapGraphEmb fV fE (R_G.G.toGraph.deleteVerts {drawingVertToGraph Γ_draw v_star}) ≤
        (mapDigraphEmb fV fE R_G.G).toGraph :=
    hdel_eq ▸ Graph.deleteVerts_le
  have hroots_del' :
      ∀ i : Fin q,
        (fV ∘ R_G.roots) i ∈
          V(mapGraphEmb fV fE (R_G.G.toGraph.deleteVerts {drawingVertToGraph Γ_draw v_star})) :=
    fun i => ⟨R_G.roots i, h83.roots_mem_deleteVerts_v_star i, rfl⟩
  have hsub_eq :
      subRootedDigraph R_G'.G (R_G'.G.toGraph.deleteVerts {ιV v_star}) Graph.deleteVerts_le
        R_G'.roots h83'.roots_mem_deleteVerts_v_star =
      subRootedDigraph R_G'.G
        (mapGraphEmb fV fE (R_G.G.toGraph.deleteVerts {drawingVertToGraph Γ_draw v_star}))
        hdel'_le (fV ∘ R_G.roots) hroots_del' := by
    simp only [subRootedDigraph, Digraph.ofSubgraph, hdel_eq, R_G']
  have h1 :=
    hasRootedDigraphModel_subRootedDigraph_mapDigraphEmb_iff fV fE R_G.G
      (R_G.G.toGraph.deleteVerts {drawingVertToGraph Γ_draw v_star}) Graph.deleteVerts_le
      R_G.roots h83.roots_mem_deleteVerts_v_star hdel'_le hroots_del' R_H
  have h2 :=
    hasRootedDigraphModel_subRootedDigraph_mapDigraphEmb_iff fV fE R_G.G
      R_G.G.toGraph le_rfl R_G.roots R_G.roots_mem le_rfl R_G'.roots_mem R_H
  have hR_G_eq : subRootedDigraph R_G.G R_G.G.toGraph le_rfl R_G.roots R_G.roots_mem = R_G := by
    cases R_G; rfl
  have hR_G'_eq :
      subRootedDigraph R_G'.G (mapGraphEmb fV fE R_G.G.toGraph) le_rfl (fV ∘ R_G.roots)
        R_G'.roots_mem = R_G' := by
    simp only [subRootedDigraph, Digraph.ofSubgraph, R_G', mapRootedDigraphEmb, mapDigraphEmb]
  rw [← h1, ← hsub_eq, ← hR_G_eq, ← h2, hR_G'_eq]
  exact hfolio'

end GraphMinor.GM22
