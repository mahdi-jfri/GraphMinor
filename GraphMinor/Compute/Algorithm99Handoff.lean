module

public import GraphMinor.Compute.Algorithm99Case3Claim
import GraphMinor.Compute.Algorithm97Aux

/-!
# From the output of (9.7) to the input of steps (5) to (7) of (9.9)

Algorithm (9.7) of Graph Minors XIII (page 103) returns walls `H^1, …, H^s` of `G_i` that are
flat and dividing in `G' = (G_i \ X) ∪ H_i` (`WallOfHeight.wallUnionMultiDigraph G_i X H_i`).
Steps (5) to (7) of (9.9) (`Case3StepsClaim`) take instead a wall that is flat in
`D_del = G' \ X` (`G'.deleteVertices X`), together with its compass there. This file proves that
the two views agree.

The reason is (9.5) in the following form. Let `W` be one of the `H^a`, disjoint from `X`, with
compass `K` in `G'`. A vertex of `X` is joined in `G'` only by edges of `H_i`. So if a walk of `K`
that starts inside `W` reached `X`, its first vertex in `X` would be a vertex of `H_i` in `K`. Since
`W` is dividing, every vertex of `H_i` in `K` is a vertex of `W`, and `W` misses `X`. Hence `K`
misses `X` (`disjoint_compassFinset_wallUnion`), every edge of `K` lies in `D_del`, and the compass
of `W` in `D_del` is `K` (`compassFinset_castGraph_deleteVertices_wallUnion`). A cross over `W` in
`D_del` is a cross in `G'`, so `W` is flat in `D_del` (`isFlatWall_castGraph_deleteVertices_wallUnion`).
Finally the compass in `D_del` is also the compass of the GM wall in the graph `delGraph G' X`, in
which the vertices of `X` are removed (`toNatSet_compassFinset_eq_wallCompass_delGraph`).
All four facts are what `Case3StepsClaim` asks of its wall (`handoff_case3StepsClaim_input`).
-/

@[expose] public section

namespace GraphMinor.Compute

open SimpleGraph Graph

/-- In `G \ Z` two vertices are adjacent when they are adjacent in `G` and both lie outside `Z`. -/
theorem MultiDigraph.toSimpleGraph_deleteVertices_adj {n : ℕ} (G : MultiDigraph n)
    (Z : Finset (Fin n)) (u v : Fin n) :
    (G.deleteVertices Z).toSimpleGraph.Adj u v ↔ G.toSimpleGraph.Adj u v ∧ u ∉ Z ∧ v ∉ Z := by
  rw [MultiDigraph.toSimpleGraph_adj, MultiDigraph.toSimpleGraph_adj,
    MultiDigraph.deleteVertices_edgeMult, MultiDigraph.deleteVertices_edgeMult]
  by_cases hu : u ∈ Z <;> by_cases hv : v ∈ Z <;> simp [hu, hv]

/-- Deleting vertices from a digraph and then forgetting directions is deleting them from the
underlying graph. -/
theorem GM13.Digraph.toGraph_deleteVertices {α β : Type*} (G : GM13.Digraph α β) (X : Set α) :
    (G.deleteVertices X).toGraph = GM09.deleteVertices G.toGraph X := by
  refine Graph.ext ?_ fun e x y => ?_
  · ext v
    change v ∈ G.vertexSet ∩ (G.vertexSet \ X) ↔ v ∈ G.vertexSet \ X
    exact ⟨fun hv => hv.2, fun hv => ⟨hv.1, hv⟩⟩
  · simp only [GM13.Digraph.toGraph, GM13.Digraph.deleteVertices, GM13.Digraph.induce,
      GM09.deleteVertices, Graph.induce_isLink, Set.mem_ofPred_eq, Set.mem_sdiff]
    constructor
    · rintro ⟨⟨he, hh, ht⟩, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩
      · exact ⟨⟨he, Or.inl ⟨rfl, rfl⟩⟩, hh, ht⟩
      · exact ⟨⟨he, Or.inr ⟨rfl, rfl⟩⟩, ht, hh⟩
    · rintro ⟨⟨he, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩, hx, hy⟩
      · exact ⟨⟨he, hx, hy⟩, Or.inl ⟨rfl, rfl⟩⟩
      · exact ⟨⟨he, hy, hx⟩, Or.inr ⟨rfl, rfl⟩⟩

namespace WallOfHeight

variable {n h h' : ℕ} {Gi : MultiDigraph n} {X : Finset (Fin n)} {Hi : WallOfHeight h' Gi}
  {W₀ : WallOfHeight h Gi}

/-- A wall of `G_i` that misses `X` is a valid wall of `(G_i \ X) ∪ H_i`. -/
theorem isValid_castGraph_wallUnion (hW₀ : W₀.IsValid) (hdisj : Disjoint W₀.vertexFinset X) :
    (W₀.castGraph (wallUnionMultiDigraph Gi X Hi)).IsValid := by
  apply W₀.isValid_castGraph hW₀
  intro u v hwe
  have hmem := hwe.mem_vertexFinset W₀
  rw [wallUnionMultiDigraph_adj]
  exact ⟨hwe.adj_toSimpleGraph hW₀,
    Or.inl ⟨Finset.disjoint_left.mp hdisj hmem.1, Finset.disjoint_left.mp hdisj hmem.2⟩⟩

/-- A wall of `G_i` that misses `X` is a valid wall of `((G_i \ X) ∪ H_i) \ X`. -/
theorem isValid_castGraph_deleteVertices_wallUnion (hW₀ : W₀.IsValid)
    (hdisj : Disjoint W₀.vertexFinset X) :
    (W₀.castGraph ((wallUnionMultiDigraph Gi X Hi).deleteVertices X)).IsValid := by
  apply W₀.isValid_castGraph hW₀
  intro u v hwe
  have hmem := hwe.mem_vertexFinset W₀
  rw [MultiDigraph.toSimpleGraph_deleteVertices_adj, wallUnionMultiDigraph_adj]
  have hu := Finset.disjoint_left.mp hdisj hmem.1
  have hv := Finset.disjoint_left.mp hdisj hmem.2
  exact ⟨⟨hwe.adj_toSimpleGraph hW₀, Or.inl ⟨hu, hv⟩⟩, hu, hv⟩

/-- The walk step behind the hand-off. Let `W₀` be dividing in `G' = (G_i \ X) ∪ H_i` and miss
`X`. Along a walk of `G'` that avoids the perimeter of `W₀` and starts at a vertex reachable from
the seed of `W₀` (in `G'` and in `G' \ X`) and outside `X`, the end is again outside `X` and
reachable from the seed in `G' \ X`. At each step the new vertex is in the compass of `W₀` in `G'`;
if it were in `X`, the edge to it would be an edge of `H_i` (vertices of `X` meet no other edge of
`G'`), so the new vertex would be a vertex of `H_i` in the compass, hence of `W₀` since `W₀` is
dividing, and `W₀` misses `X`. -/
private theorem reach_aux (hHi : Hi.IsValid) (h2' : 2 ≤ h') (he' : Even h')
    (hW₀ : W₀.IsValid) (h2 : 2 ≤ h) (hdisj : Disjoint W₀.vertexFinset X)
    (hdiv : (Hi.castGraph (wallUnionMultiDigraph Gi X Hi)).IsDividingSubwall
      (W₀.castGraph (wallUnionMultiDigraph Gi X Hi))) :
    ∀ {a b : Fin n},
      (restrictGraph (wallUnionMultiDigraph Gi X Hi).toSimpleGraph
        (Finset.univ \ W₀.perimeterFinset)).Walk a b →
      (restrictGraph (wallUnionMultiDigraph Gi X Hi).toSimpleGraph
        (Finset.univ \ W₀.perimeterFinset)).Reachable (W₀.seedVert h2) a →
      (restrictGraph ((wallUnionMultiDigraph Gi X Hi).deleteVertices X).toSimpleGraph
        (Finset.univ \ W₀.perimeterFinset)).Reachable (W₀.seedVert h2) a →
      a ∉ X →
      (restrictGraph ((wallUnionMultiDigraph Gi X Hi).deleteVertices X).toSimpleGraph
        (Finset.univ \ W₀.perimeterFinset)).Reachable (W₀.seedVert h2) b ∧ b ∉ X := by
  intro a b p
  induction p with
  | nil => exact fun _ hD ha => ⟨hD, ha⟩
  | @cons a c b hadj p ih =>
    intro hG hD ha
    have hW' := isValid_castGraph_wallUnion (Hi := Hi) hW₀ hdisj
    have hHi' := isValid_castGraph_wallUnionMultiDigraph X hHi
    have hGc := hG.trans hadj.reachable
    have hc_comp : c ∈ (W₀.castGraph (wallUnionMultiDigraph Gi X Hi)).compassFinset := by
      rw [compassFinset_eq_reachSet_seedVert _ h2 hW', Finset.mem_union, mem_reachSet]
      exact Or.inr hGc
    have hc : c ∉ X := by
      intro hcX
      have hadj' := ((restrictGraph_adj _ _ _ _).mp hadj).2.2
      rw [wallUnionMultiDigraph_adj] at hadj'
      have hwe : Hi.IsWallEdge a c := by
        rcases hadj'.2 with h | h
        · exact absurd hcX h.2
        · exact h
      have hcV : c ∈ (Hi.castGraph (wallUnionMultiDigraph Gi X Hi)).vertexFinset := by
        rw [castGraph_vertexFinset]
        exact (hwe.mem_vertexFinset Hi).2
      have hcW := WallOfHeight.mem_vertexFinset_of_mem_compassFinset_of_isDividingSubwall
        h2' he' hHi' hdiv hc_comp hcV
      rw [castGraph_vertexFinset] at hcW
      exact Finset.disjoint_left.mp hdisj hcW hcX
    have hadjD : (restrictGraph ((wallUnionMultiDigraph Gi X Hi).deleteVertices X).toSimpleGraph
        (Finset.univ \ W₀.perimeterFinset)).Adj a c := by
      obtain ⟨ha_in, hc_in, hac⟩ := (restrictGraph_adj _ _ _ _).mp hadj
      exact (restrictGraph_adj _ _ _ _).mpr ⟨ha_in, hc_in,
        (MultiDigraph.toSimpleGraph_deleteVertices_adj _ _ _ _).mpr ⟨hac, ha, hc⟩⟩
    exact ih hGc (hD.trans hadjD.reachable) hc

/-- **Graph Minors XIII, (9.5)**, in the form used by step (5) of (9.9): the compass of a dividing
subwall `W₀` of `H_i` in `(G_i \ X) ∪ H_i` misses `X` when `W₀` does. -/
theorem disjoint_compassFinset_wallUnion (hHi : Hi.IsValid) (h2' : 2 ≤ h') (he' : Even h')
    (hW₀ : W₀.IsValid) (h2 : 2 ≤ h) (hdisj : Disjoint W₀.vertexFinset X)
    (hdiv : (Hi.castGraph (wallUnionMultiDigraph Gi X Hi)).IsDividingSubwall
      (W₀.castGraph (wallUnionMultiDigraph Gi X Hi))) :
    Disjoint (W₀.castGraph (wallUnionMultiDigraph Gi X Hi)).compassFinset X := by
  have hW' := isValid_castGraph_wallUnion (Hi := Hi) hW₀ hdisj
  have hseed : W₀.seedVert h2 ∉ X := fun hX =>
    Finset.disjoint_left.mp hdisj
      (Finset.sdiff_subset (seedVert_mem_insideFinset h2 hW₀)) hX
  rw [Finset.disjoint_left]
  intro v hv hvX
  rw [compassFinset_eq_reachSet_seedVert _ h2 hW', Finset.mem_union, mem_reachSet] at hv
  rcases hv with hP | hr
  · exact Finset.disjoint_left.mp hdisj (W₀.perimeterFinset_subset_vertexFinset hP) hvX
  · exact (reach_aux hHi h2' he' hW₀ h2 hdisj hdiv (Classical.choice hr) (Reachable.refl _)
      (Reachable.refl _) hseed).2 hvX

/-- The compass of `W₀` in `((G_i \ X) ∪ H_i) \ X` is its compass in `(G_i \ X) ∪ H_i`. -/
theorem compassFinset_castGraph_deleteVertices_wallUnion (hHi : Hi.IsValid) (h2' : 2 ≤ h')
    (he' : Even h') (hW₀ : W₀.IsValid) (h2 : 2 ≤ h) (hdisj : Disjoint W₀.vertexFinset X)
    (hdiv : (Hi.castGraph (wallUnionMultiDigraph Gi X Hi)).IsDividingSubwall
      (W₀.castGraph (wallUnionMultiDigraph Gi X Hi))) :
    (W₀.castGraph ((wallUnionMultiDigraph Gi X Hi).deleteVertices X)).compassFinset =
      (W₀.castGraph (wallUnionMultiDigraph Gi X Hi)).compassFinset := by
  have hW' := isValid_castGraph_wallUnion (Hi := Hi) hW₀ hdisj
  have hW'' := isValid_castGraph_deleteVertices_wallUnion (Hi := Hi) hW₀ hdisj
  have hseed : W₀.seedVert h2 ∉ X := fun hX =>
    Finset.disjoint_left.mp hdisj
      (Finset.sdiff_subset (seedVert_mem_insideFinset h2 hW₀)) hX
  rw [compassFinset_eq_reachSet_seedVert _ h2 hW', compassFinset_eq_reachSet_seedVert _ h2 hW'']
  simp only [castGraph_perimeterFinset]
  congr 1
  ext v
  simp only [mem_reachSet]
  constructor
  · intro hv
    refine hv.mono ?_
    intro a b hab
    obtain ⟨ha, hb, hadj⟩ := (restrictGraph_adj _ _ _ _).mp hab
    exact (restrictGraph_adj _ _ _ _).mpr
      ⟨ha, hb, MultiDigraph.toSimpleGraph_deleteVertices_le _ X hadj⟩
  · intro hr
    exact (reach_aux hHi h2' he' hW₀ h2 hdisj hdiv (Classical.choice hr) (Reachable.refl _)
      (Reachable.refl _) hseed).1

/-- A wall that is flat in `(G_i \ X) ∪ H_i`, dividing there, and disjoint from `X` is flat in
`((G_i \ X) ∪ H_i) \ X`: its compass is the same (`compassFinset_castGraph_deleteVertices_wallUnion`),
and a cross in the smaller graph is a cross in the larger one. -/
theorem isFlatWall_castGraph_deleteVertices_wallUnion (hHi : Hi.IsValid) (h2' : 2 ≤ h')
    (he' : Even h') (hW₀ : W₀.IsValid) (h2 : 2 ≤ h) (hdisj : Disjoint W₀.vertexFinset X)
    (hdiv : (Hi.castGraph (wallUnionMultiDigraph Gi X Hi)).IsDividingSubwall
      (W₀.castGraph (wallUnionMultiDigraph Gi X Hi)))
    (hflat : (W₀.castGraph (wallUnionMultiDigraph Gi X Hi)).IsFlatWall h2) :
    (W₀.castGraph ((wallUnionMultiDigraph Gi X Hi).deleteVertices X)).IsFlatWall h2 := by
  refine ⟨isValid_castGraph_deleteVertices_wallUnion hW₀ hdisj, ?_⟩
  rintro ⟨P₁, P₂, hcr, hP₁, hP₂⟩
  rw [compassFinset_castGraph_deleteVertices_wallUnion hHi h2' he' hW₀ h2 hdisj hdiv]
    at hP₁ hP₂
  have hle : ∀ u v : Fin n,
      ((wallUnionMultiDigraph Gi X Hi).deleteVertices X).toSimpleGraph.Adj u v →
        (wallUnionMultiDigraph Gi X Hi).toSimpleGraph.Adj u v :=
    fun u v huv => MultiDigraph.toSimpleGraph_deleteVertices_le _ X huv
  refine hflat.2 ⟨P₁, P₂, ?_, hP₁, hP₂⟩
  exact
    { ne_nil₁ := hcr.ne_nil₁
      ne_nil₂ := hcr.ne_nil₂
      nodup₁ := hcr.nodup₁
      nodup₂ := hcr.nodup₂
      isWalk₁ := isSimpleWalkList_of_congr (fun u v _ huv => hle u v huv) hcr.isWalk₁
      isWalk₂ := isSimpleWalkList_of_congr (fun u v _ huv => hle u v huv) hcr.isWalk₂
      head₁ := hcr.head₁
      getLast₁ := hcr.getLast₁
      head₂ := hcr.head₂
      getLast₂ := hcr.getLast₂
      disjoint := hcr.disjoint }

/-- The vertex set of the compass of a wall `W` of `G' \ X` that misses `X` is the vertex set of
the compass of its GM wall in `delGraph G' X`, the graph `G' \ X` with the vertices of `X`
removed. In `G' \ X` the vertices of `X` have no edges, so removing them changes no walk that
starts inside `W`; then `val_compassFinsetAvoid_eq_wallCompassVerts` applies. -/
theorem toNatSet_compassFinset_eq_wallCompass_delGraph {G' : MultiDigraph n}
    (W : WallOfHeight h (G'.deleteVertices X)) (h2 : 2 ≤ h) (he : Even h) (hW : W.IsValid)
    (hdisj : Disjoint W.vertexFinset X) :
    W.compassFinset.toNatSet =
      V(GM13.wallCompass (delGraph G' X) (W.toGMWall h2 he hW)) := by
  have hdisj' : Disjoint X W.vertexFinset := hdisj.symm
  have hA := W.val_compassFinsetAvoid_eq_wallCompassVerts h2 he hW X hdisj'
  have hdel : delGraph G' X =
      GM09.deleteVertices (G'.deleteVertices X).toGMDigraph.toGraph X.toNatSet := by
    unfold delGraph
    exact GM13.Digraph.toGraph_deleteVertices _ _
  have hrestr : restrictGraph (G'.deleteVertices X).toSimpleGraph
        (Finset.univ \ (X ∪ W.perimeterFinset)) =
      restrictGraph (G'.deleteVertices X).toSimpleGraph (Finset.univ \ W.perimeterFinset) := by
    ext u v
    rw [restrictGraph_adj, restrictGraph_adj, MultiDigraph.toSimpleGraph_deleteVertices_adj]
    simp only [Finset.mem_sdiff, Finset.mem_univ, true_and, Finset.mem_union, not_or]
    tauto
  have havoid : W.compassFinsetAvoid X = W.compassFinset := by
    rw [W.compassFinsetAvoid_eq_reachSet_seedVert h2 hW hdisj',
      W.compassFinset_eq_reachSet_seedVert h2 hW, hrestr]
  rw [hdel, ← havoid]
  exact hA

/-- **The hand-off from (9.7) to steps (5) to (7) of (9.9).** Let `W₀` be a wall of `G_i`, missing
`X`, that (9.7) returns: flat and dividing in `G' = (G_i \ X) ∪ H_i`. Then `W₀`, read as a wall of
`G' \ X`, satisfies every hypothesis that `Case3StepsClaim` puts on its wall, and its compass
there is its compass in `G'`, which step (4) computes. -/
theorem handoff_case3StepsClaim_input (hHi : Hi.IsValid) (h2' : 2 ≤ h') (he' : Even h')
    (hW₀ : W₀.IsValid) (h2 : 2 ≤ h) (he : Even h) (hdisj : Disjoint W₀.vertexFinset X)
    (hdiv : (Hi.castGraph (wallUnionMultiDigraph Gi X Hi)).IsDividingSubwall
      (W₀.castGraph (wallUnionMultiDigraph Gi X Hi)))
    (hflat : (W₀.castGraph (wallUnionMultiDigraph Gi X Hi)).IsFlatWall h2) :
    ∃ hW : (W₀.castGraph ((wallUnionMultiDigraph Gi X Hi).deleteVertices X)).IsValid,
      Disjoint (W₀.castGraph ((wallUnionMultiDigraph Gi X Hi).deleteVertices X)).vertexFinset X ∧
      (W₀.castGraph ((wallUnionMultiDigraph Gi X Hi).deleteVertices X)).IsFlatWall h2 ∧
      Disjoint (W₀.castGraph ((wallUnionMultiDigraph Gi X Hi).deleteVertices X)).compassFinset X ∧
      (W₀.castGraph ((wallUnionMultiDigraph Gi X Hi).deleteVertices X)).compassFinset.toNatSet =
        V(GM13.wallCompass (delGraph (wallUnionMultiDigraph Gi X Hi) X)
          ((W₀.castGraph ((wallUnionMultiDigraph Gi X Hi).deleteVertices X)).toGMWall
            h2 he hW)) ∧
      (W₀.castGraph ((wallUnionMultiDigraph Gi X Hi).deleteVertices X)).compassFinset =
        (W₀.castGraph (wallUnionMultiDigraph Gi X Hi)).compassFinset := by
  have hW := isValid_castGraph_deleteVertices_wallUnion (Hi := Hi) hW₀ hdisj
  have heq := compassFinset_castGraph_deleteVertices_wallUnion hHi h2' he' hW₀ h2 hdisj hdiv
  refine ⟨hW, hdisj, isFlatWall_castGraph_deleteVertices_wallUnion hHi h2' he' hW₀ h2 hdisj hdiv
    hflat, ?_, toNatSet_compassFinset_eq_wallCompass_delGraph _ h2 he hW hdisj, heq⟩
  rw [heq]
  exact disjoint_compassFinset_wallUnion hHi h2' he' hW₀ h2 hdisj hdiv

end WallOfHeight

end GraphMinor.Compute
