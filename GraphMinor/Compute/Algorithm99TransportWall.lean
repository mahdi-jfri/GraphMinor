module

public import GraphMinor.Compute.Algorithm99Transport

/-!
# Transport of walls, compasses and flat walls along injective relabellings

Section 9 of Graph Minors XIII (pages 97–104) speaks of walls in a graph, their subwalls, the
compass of a wall, crosses over a wall, flat walls and dividing subwalls. Algorithm (9.9) proves
these facts for the renumbered graph `G_i` and needs them in the labels of `G`. Here we show that
each of these notions is unchanged when vertices and edges are renamed along embeddings
`f : α ↪ α'` and `g : β ↪ β'`.

`relabelWall f g W` is the wall `W` with its graph, its base graph and its subdivision paths
renamed. Its corners, perimeter and inside vertices are the renamed ones of `W`. The main results
are `wallCompass_relabelGraph` (the compass of the renamed wall is the renamed compass),
`isFlatWallIn_relabelGraph_iff`, `isSubwallOf_relabelWall_iff` and
`isDividingSubwall_relabelGraph_iff`. The proofs only unfold the definitions and use the transport
of walks and paths of `Algorithm99Transport.lean`, in both directions: for the statements with a
negation (flatness, dividing), a cross or an `H`-path in the renamed graph is pulled back.
-/

@[expose] public section

namespace GraphMinor.Transport

open Graph Function Set GraphMinor.Surface GraphMinor.GM09 GraphMinor.GM14 GraphMinor.GM13

universe u u' v v'

variable {α : Type u} {α' : Type u'} {β : Type v} {β' : Type v'}
variable (f : α ↪ α') (g : β ↪ β')

/-- The renaming of a family of graphs indexed by edges: the graph at `g e` is the renaming of the
graph at `e`, and the graph at an edge name outside the range of `g` is empty. -/
noncomputable def relabelEdgeFamily (P : β → Graph α β) (e' : β') : Graph α' β' :=
  open Classical in
  if h : e' ∈ Set.range g then relabelGraph f g (P h.choose) else ⊥

@[simp]
theorem relabelEdgeFamily_apply (P : β → Graph α β) (e : β) :
    relabelEdgeFamily f g P (g e) = relabelGraph f g (P e) := by
  have h : g e ∈ Set.range g := ⟨e, rfl⟩
  unfold relabelEdgeFamily
  simp only [h, ↓reduceDIte]
  congr 2
  exact g.injective h.choose_spec

theorem relabelEdgeFamily_injective : Injective (relabelEdgeFamily (α := α) f g) := by
  intro P Q h
  funext e
  have := congrFun h (g e)
  rw [relabelEdgeFamily_apply, relabelEdgeFamily_apply] at this
  exact relabelGraph_injective f g this

/-- The wall `W` with its vertices renamed along `f` and its edges renamed along `g`. -/
noncomputable def relabelWall (W : Wall α β) : Wall α' β' where
  graph := relabelGraph f g W.graph
  height := W.height
  two_le_height := W.two_le_height
  even_height := W.even_height
  baseGraph := relabelGraph f g W.baseGraph
  baseIso :=
    { vertexEquiv := W.baseIso.vertexEquiv.trans (Equiv.Set.image f _ f.injective)
      edgeEquiv := W.baseIso.edgeEquiv.trans (Equiv.Set.image g _ g.injective)
      isLink_iff := fun e x y =>
        (W.baseIso.isLink_iff e x y).trans (relabelGraph_isLink_apply f g).symm }
  subdivisionPaths := relabelEdgeFamily f g W.subdivisionPaths
  base_verts_subset := Set.image_mono W.base_verts_subset
  path_of_edge := by
    rintro _ ⟨e, he, rfl⟩
    obtain ⟨u, w, hl, hP, hne, hint⟩ := W.path_of_edge e he
    refine ⟨f u, f w, (relabelGraph_isLink_apply f g).2 hl, ?_, ?_, ?_⟩
    · rw [relabelEdgeFamily_apply]
      exact isGraphPathWithEnds_relabelGraph f g hP
    · rw [relabelEdgeFamily_apply, edgeSet_relabelGraph]
      exact hne.image g
    · rw [relabelEdgeFamily_apply, vertexSet_relabelGraph, vertexSet_relabelGraph,
        ← Set.image_inter f.injective, hint, Set.image_pair]
  paths_disjoint := by
    rintro _ ⟨e₁, he₁, rfl⟩ _ ⟨e₂, he₂, rfl⟩ hne
    have hne' : e₁ ≠ e₂ := fun h => hne (h ▸ rfl)
    obtain ⟨hE, hV⟩ := W.paths_disjoint e₁ he₁ e₂ he₂ hne'
    rw [relabelEdgeFamily_apply, relabelEdgeFamily_apply]
    refine ⟨?_, ?_⟩
    · simpa [edgeSet_relabelGraph] using (Set.disjoint_image_iff g.injective).2 hE
    · simp only [vertexSet_relabelGraph]
      rw [← Set.image_inter f.injective]
      exact Set.image_mono hV
  vertexSet_eq := by
    simp only [vertexSet_relabelGraph, edgeSet_relabelGraph, Set.biUnion_image,
      relabelEdgeFamily_apply]
    rw [W.vertexSet_eq, Set.image_union, Set.image_iUnion₂]
  edgeSet_eq := by
    simp only [edgeSet_relabelGraph, Set.biUnion_image, relabelEdgeFamily_apply]
    rw [W.edgeSet_eq, Set.image_iUnion₂]

variable (W W' : Wall α β)

@[simp] theorem relabelWall_graph : (relabelWall f g W).graph = relabelGraph f g W.graph := rfl

@[simp] theorem relabelWall_height : (relabelWall f g W).height = W.height := rfl

@[simp] theorem relabelWall_baseGraph :
    (relabelWall f g W).baseGraph = relabelGraph f g W.baseGraph := rfl

@[simp] theorem relabelWall_subdivisionPaths_apply (e : β) :
    (relabelWall f g W).subdivisionPaths (g e) = relabelGraph f g (W.subdivisionPaths e) :=
  relabelEdgeFamily_apply f g _ e

@[simp]
theorem relabelWall_baseIso_vertexEquiv (p : V(elementaryWall W.height)) :
    ((relabelWall f g W).baseIso.vertexEquiv p).1 = f (W.baseIso.vertexEquiv p).1 := rfl

@[simp]
theorem relabelWall_baseIso_edgeEquiv (e : E(elementaryWall W.height)) :
    ((relabelWall f g W).baseIso.edgeEquiv e).1 = g (W.baseIso.edgeEquiv e).1 := rfl

@[simp]
theorem relabelWall_branchVertex (p : ℕ × ℕ) (hp : p ∈ elementaryWallVerts W.height) :
    (relabelWall f g W).branchVertex p hp = f (W.branchVertex p hp) := rfl

@[simp]
theorem relabelWall_corner (k : Fin 4) : (relabelWall f g W).corner k = f (W.corner k) := rfl

theorem relabelWall_corners : (relabelWall f g W).corners = f '' W.corners := by
  unfold Wall.corners
  rw [← Set.range_comp]
  rfl

@[simp]
theorem relabelWall_middleVertex₁ : (relabelWall f g W).middleVertex₁ = f W.middleVertex₁ := rfl

@[simp]
theorem relabelWall_middleVertex₂ : (relabelWall f g W).middleVertex₂ = f W.middleVertex₂ := rfl

theorem relabelWall_perimeter :
    (relabelWall f g W).perimeter = relabelGraph f g W.perimeter := by
  unfold Wall.perimeter
  rw [relabelGraph_subgraphSUnion]
  congr 1
  ext P'
  constructor
  · rintro ⟨e₀, he₀, rfl⟩
    refine ⟨W.subdivisionPaths (W.baseIso.edgeEquiv ⟨e₀, _⟩).1, ⟨e₀, he₀, rfl⟩, ?_⟩
    change _ = relabelEdgeFamily f g W.subdivisionPaths (g _)
    rw [relabelEdgeFamily_apply]
    rfl
  · rintro ⟨P, ⟨e₀, he₀, rfl⟩, rfl⟩
    refine ⟨e₀, he₀, ?_⟩
    change _ = relabelEdgeFamily f g W.subdivisionPaths (g _)
    rw [relabelEdgeFamily_apply]
    rfl

theorem relabelWall_insideVerts : (relabelWall f g W).insideVerts = f '' W.insideVerts := by
  unfold Wall.insideVerts
  rw [relabelWall_perimeter, relabelWall_graph, vertexSet_relabelGraph, vertexSet_relabelGraph,
    Set.image_sdiff f.injective]

variable {G : Graph α β}

@[simp]
theorem isWallIn_relabelGraph_iff :
    IsWallIn (relabelGraph f g G) (relabelWall f g W) ↔ IsWallIn G W :=
  relabelGraph_le_relabelGraph_iff f g

/-! ### Compasses -/

theorem wallCompassVerts_relabelGraph :
    wallCompassVerts (relabelGraph f g G) (relabelWall f g W) = f '' wallCompassVerts G W := by
  unfold wallCompassVerts
  rw [relabelWall_perimeter, relabelWall_insideVerts, vertexSet_relabelGraph,
    vertexSet_relabelGraph, ← relabelGraph_deleteVertices, Set.image_union]
  congr 1
  ext v'
  constructor
  · rintro ⟨⟨⟨v, hv, rfl⟩, hvC⟩, u', ⟨u, hu, rfl⟩, ⟨W'⟩⟩
    obtain ⟨w, hw, W₀, -, -⟩ := exists_walk_of_relabelWalk f g W'
    rw [f.injective hw] at W₀
    exact ⟨v, ⟨⟨hv, fun h => hvC ⟨v, h, rfl⟩⟩, u, hu, ⟨W₀⟩⟩, rfl⟩
  · rintro ⟨v, ⟨⟨hv, hvC⟩, u, hu, ⟨W₀⟩⟩, rfl⟩
    exact ⟨⟨⟨v, hv, rfl⟩, fun h => hvC (f.injective.mem_set_image.1 h)⟩, f u, ⟨u, hu, rfl⟩,
      ⟨relabelWalk f g W₀⟩⟩

/-- The compass of the renamed wall in the renamed graph is the renamed compass. -/
theorem wallCompass_relabelGraph :
    wallCompass (relabelGraph f g G) (relabelWall f g W) = relabelGraph f g (wallCompass G W) := by
  unfold wallCompass
  rw [wallCompassVerts_relabelGraph, relabelGraph_induce]

/-! ### Crosses and flat walls -/

@[simp]
theorem isCrossOverWall_relabelGraph_iff {P Q : Graph α β} :
    IsCrossOverWall (relabelGraph f g G) (relabelWall f g W) (relabelGraph f g P)
        (relabelGraph f g Q) ↔ IsCrossOverWall G W P Q := by
  unfold IsCrossOverWall
  simp only [vertexSet_relabelGraph, relabelWall_corner, isGraphPathWithEnds_relabelGraph_iff,
    Set.disjoint_image_iff f.injective]

/-- A cross over the renamed wall in a renamed graph is the renaming of a cross. -/
theorem exists_of_isCrossOverWall_relabelGraph {P' Q' : Graph α' β'}
    (h : IsCrossOverWall (relabelGraph f g G) (relabelWall f g W) P' Q') :
    ∃ P Q, relabelGraph f g P = P' ∧ relabelGraph f g Q = Q' ∧ IsCrossOverWall G W P Q := by
  obtain ⟨P, -, rfl⟩ := exists_eq_relabelGraph_of_le f g h.2.1.1
  obtain ⟨Q, -, rfl⟩ := exists_eq_relabelGraph_of_le f g h.2.2.1
  exact ⟨P, Q, rfl, rfl, (isCrossOverWall_relabelGraph_iff f g W).1 h⟩

/-- A wall is flat in `G` if and only if its renaming is flat in the renamed graph. -/
@[simp]
theorem isFlatWallIn_relabelGraph_iff :
    IsFlatWallIn (relabelGraph f g G) (relabelWall f g W) ↔ IsFlatWallIn G W := by
  unfold IsFlatWallIn
  rw [relabelWall_graph, relabelGraph_le_relabelGraph_iff, wallCompass_relabelGraph]
  refine and_congr_right fun _ => not_congr ?_
  constructor
  · rintro ⟨P', Q', h⟩
    obtain ⟨P, Q, -, -, hc⟩ := exists_of_isCrossOverWall_relabelGraph f g W h
    exact ⟨P, Q, hc⟩
  · rintro ⟨P, Q, hc⟩
    exact ⟨_, _, (isCrossOverWall_relabelGraph_iff f g W).2 hc⟩

/-! ### Subwalls and dividing subwalls -/

/-- `W'` is a subwall of `W` if and only if the renamed `W'` is a subwall of the renamed `W`. -/
@[simp]
theorem isSubwallOf_relabelWall_iff :
    (relabelWall f g W').IsSubwallOf (relabelWall f g W) ↔ W'.IsSubwallOf W := by
  have hbase : ∀ S : Set (elementaryWallVerts W.height),
      (fun p : elementaryWallVerts (relabelWall f g W).height =>
          ((relabelWall f g W).baseIso.vertexEquiv p).1) '' S =
        f '' ((fun p : elementaryWallVerts W.height => (W.baseIso.vertexEquiv p).1) '' S) := by
    intro S
    rw [Set.image_image]
    rfl
  constructor
  · rintro ⟨hle, i, j, hi, hj, hi', hj', hbv, hsp, hbg⟩
    refine ⟨hle, i, j, hi, hj, hi', hj', fun p hp' hp => f.injective (hbv p hp' hp),
      relabelEdgeFamily_injective f g hsp, ?_⟩
    have hbg' : relabelGraph f g W'.baseGraph = relabelGraph f g (W.baseGraph.induce
        ((fun p : elementaryWallVerts W.height => (W.baseIso.vertexEquiv p).1) ''
          {p : elementaryWallVerts W.height |
            ∃ q ∈ elementaryWallVerts W'.height, p.1 = wallShift i j q})) := by
      rw [relabelGraph_induce, ← hbase]
      exact hbg
    exact relabelGraph_injective f g hbg'
  · rintro ⟨hle, i, j, hi, hj, hi', hj', hbv, hsp, hbg⟩
    refine ⟨hle, i, j, hi, hj, hi', hj', fun p hp' hp => ?_, ?_, ?_⟩
    · exact congrArg f (hbv p hp' hp)
    · change relabelEdgeFamily f g W'.subdivisionPaths = relabelEdgeFamily f g W.subdivisionPaths
      rw [hsp]
    · have e1 := hbase {p : elementaryWallVerts W.height |
        ∃ q ∈ elementaryWallVerts W'.height, p.1 = wallShift i j q}
      change relabelGraph f g W'.baseGraph = (relabelGraph f g W.baseGraph).induce
        ((fun p : elementaryWallVerts W.height => ((relabelWall f g W).baseIso.vertexEquiv p).1) ''
          {p : elementaryWallVerts W.height |
            ∃ q ∈ elementaryWallVerts W'.height, p.1 = wallShift i j q})
      refine Eq.trans ?_ (congrArg (relabelGraph f g W.baseGraph).induce e1).symm
      rw [← relabelGraph_induce, hbg]

/-- `W'` is a dividing subwall of `W` in `G` if and only if the renamed `W'` is a dividing subwall
of the renamed `W` in the renamed graph. -/
@[simp]
theorem isDividingSubwall_relabelGraph_iff :
    IsDividingSubwall (relabelGraph f g G) (relabelWall f g W) (relabelWall f g W') ↔
      IsDividingSubwall G W W' := by
  unfold IsDividingSubwall
  rw [isSubwallOf_relabelWall_iff]
  refine and_congr_right fun _ => ?_
  rw [relabelWall_insideVerts, relabelWall_graph, relabelWall_graph, vertexSet_relabelGraph,
    vertexSet_relabelGraph, ← Set.image_sdiff f.injective]
  constructor
  · intro h P a b hP hab
    exact h _ _ _ ((isHPathWithEnds_relabelGraph_iff f g).2 hP)
      ⟨⟨a, hab.1, rfl⟩, ⟨b, hab.2, rfl⟩⟩
  · intro h P' a' b' hP' hab
    obtain ⟨P, a, b, rfl, rfl, rfl, -⟩ := exists_of_isGraphPathWithEnds_relabelGraph f g hP'.2.1
    exact h P a b ((isHPathWithEnds_relabelGraph_iff f g).1 hP')
      ⟨f.injective.mem_set_image.1 hab.1, f.injective.mem_set_image.1 hab.2⟩

end GraphMinor.Transport
