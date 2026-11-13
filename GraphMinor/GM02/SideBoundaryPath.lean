module

public import GraphMinor.GM02.SidePairGraph
public import GraphMinor.GM02.SideBoundaryVertices

/-!
# Contracted paths in the graph of side pairs

For the forward construction of corrected II (2.9), the endpoint pair of
each maximal side piece is an edge of the union of the new terminations.
The boundary-vertex list therefore gives a path in that graph, joining
the original pair and using only original path vertices.
-/

@[expose] public section
namespace GraphMinor.GM02
open Graph SimpleGraph List Set Classical
universe u v
variable {α : Type u} {β : Type v} {S : Set α} (A : Termination S) (G H : Graph α β)
variable (P : ∀ p : {p // p ∈ A.pairs}, PairPath (pathGraph G) p.val)
variable (hP : ∀ p q, p ≠ q → Disjoint (P p).vertices (P q).vertices)

private theorem support_headD {F : SimpleGraph α} {a b : α} (p : F.Walk a b) (default : α) :
    p.support.headD default = a := by
  cases p <;> rfl

private theorem fullRecord_pair {a b : α} (p : (pathGraph G).Walk a b)
    (r : List (pathGraph G).Dart) (hr : r ∈ sideRuns H p) :
    s((dartFullRecord (separationEdgeColor H) a r).2.headD a,
      (dartFullRecord (separationEdgeColor H) a r).2.getLastD a) =
    s((r.head (coloredRun_ne_nil hr)).fst, (r.getLast (coloredRun_ne_nil hr)).snd) := by
  rw [sideRunWalk_fullRecord p r hr]
  have hfirst : (sideRunWalk p r hr).support.headD a = (r.head (coloredRun_ne_nil hr)).fst := by
    exact support_headD _ a
  have hlast : (sideRunWalk p r hr).support.getLastD a = (r.getLast (coloredRun_ne_nil hr)).snd := by
    simp only [List.getLastD_eq_getLast?, List.getLast?_eq_some_getLast
      (sideRunWalk p r hr).support_ne_nil, Option.getD_some, Walk.getLast_support]
  rw [hfirst, hlast]

/-- Every consecutive edge of a contracted boundary list belongs to the
union of the two side terminations. -/
theorem sideBoundary_edges_mem (p : {p // p ∈ A.pairs}) (e : Sym2 α)
    (he : e ∈ List.zipWith (s(·, ·)) (sideBoundaryVertices H (P p).walk)
      (sideBoundaryVertices H (P p).walk).tail) :
    e ∈ (sidePairGraph A G H P hP).edgeSet := by
  have hzip := chunkEndpointPairs_eq_zip_boundaries (P p).start
    (sideRunRecords H (P p).walk) (sideRunRecords_nonempty (P p).walk)
  change e ∈ List.zipWith (s(·, ·)) (chunkBoundaryVertices (P p).start (sideRunRecords H (P p).walk))
    (chunkBoundaryVertices (P p).start (sideRunRecords H (P p).walk)).tail at he
  rw [← hzip, chunkEndpointPairs_eq_records _ _ (sideRunRecords_nonempty (P p).walk),
    sideRunRecords_restore, List.map_map] at he
  obtain ⟨r, hr, he⟩ := List.mem_map.1 he
  let i : RunPieceIndex A G H P := ⟨p, ⟨r, hr⟩⟩
  apply (sidePairGraph_mem_edgeSet A G H P hP e).2
  refine ⟨i, ?_⟩
  exact (fullRecord_pair G H (P p).walk r hr).symm.trans he

/-- A vertex list whose consecutive pairs are graph edges is a walk chain. -/
theorem chain_of_zip_edges {δ : Type u} {F : SimpleGraph δ} (l : List δ)
    (hmem : ∀ e ∈ List.zipWith (s(·, ·)) l l.tail, e ∈ F.edgeSet) : l.IsChain F.Adj := by
  induction l with
  | nil => exact List.IsChain.nil
  | cons a xs ih =>
    cases xs with
    | nil => exact List.IsChain.singleton a
    | cons b ys =>
      apply List.isChain_cons_cons.2
      constructor
      · exact (SimpleGraph.mem_edgeSet _).1 (hmem s(a, b) (by simp))
      · apply ih
        intro e he
        exact hmem e (List.mem_cons_of_mem _ he)

/-- The contracted boundary list is a path in the graph of side pairs. -/
noncomputable def sideBoundaryPairPath (p : {p // p ∈ A.pairs}) :
    PairPath (sidePairGraph A G H P hP) p.val := by
  let l := sideBoundaryVertices H (P p).walk
  have hn : l ≠ [] := sideBoundaryVertices_nonempty (P p).walk
  have hc : l.IsChain (sidePairGraph A G H P hP).Adj :=
    chain_of_zip_edges l (sideBoundary_edges_mem A G H P hP p)
  let w := Walk.ofSupport l hn hc
  have hs : l.head hn = (P p).start := sideBoundaryVertices_head (P p).walk
  have ht : l.getLast hn = (P p).finish := sideBoundaryVertices_getLast (P p).walk
  refine ⟨(P p).start, (P p).finish, (P p).ends_eq, w.copy hs ht, ?_⟩
  apply Walk.IsPath.mk'
  rw [Walk.support_copy, Walk.support_ofSupport]
  exact sideBoundaryVertices_nodup (P p).walk (P p).isPath

/-- The contracted pair path has exactly the boundary vertex list. -/
theorem sideBoundaryPairPath_support (p : {p // p ∈ A.pairs}) :
    (sideBoundaryPairPath A G H P hP p).walk.support = sideBoundaryVertices H (P p).walk := by
  simp only [sideBoundaryPairPath, Walk.support_copy, Walk.support_ofSupport]

/-- The contracted path's edges list the endpoint pairs of the maximal
runs in their original order. -/
theorem sideBoundaryPairPath_edges_records (p : {p // p ∈ A.pairs}) :
    (sideBoundaryPairPath A G H P hP p).walk.edges = (sideRuns H (P p).walk).map
      (fun r => s((dartFullRecord (separationEdgeColor H) (P p).start r).2.headD (P p).start,
        (dartFullRecord (separationEdgeColor H) (P p).start r).2.getLastD (P p).start)) := by
  rw [Walk.edges_eq_zipWith_support, sideBoundaryPairPath_support]
  exact (chunkEndpointPairs_eq_zip_boundaries (P p).start (sideRunRecords H (P p).walk)
    (sideRunRecords_nonempty (P p).walk)).symm.trans
      ((chunkEndpointPairs_eq_records _ _ (sideRunRecords_nonempty (P p).walk)).trans (by
        rw [sideRunRecords_restore, List.map_map]
        rfl))

/-- A piece pair is recovered from its full dart record. -/
theorem RunPieceIndex.pair_eq_fullRecord (i : RunPieceIndex A G H P) :
    i.pair A G H P =
      s((dartFullRecord (separationEdgeColor H) (P i.1).start i.2.val).2.headD (P i.1).start,
        (dartFullRecord (separationEdgeColor H) (P i.1).start i.2.val).2.getLastD (P i.1).start) :=
  (fullRecord_pair G H (P i.1).walk i.2.val i.2.property).symm

/-- Every original side piece occurs as an edge of its contracted
original-pair path. This gives the edge coverage in condition (iv). -/
theorem sideBoundaryPairPath_piece_edge (i : RunPieceIndex A G H P) :
    i.pair A G H P ∈ (sideBoundaryPairPath A G H P hP i.1).walk.edges := by
  rw [Walk.edges_eq_zipWith_support, sideBoundaryPairPath_support]
  have hzip := chunkEndpointPairs_eq_zip_boundaries (P i.1).start
    (sideRunRecords H (P i.1).walk) (sideRunRecords_nonempty (P i.1).walk)
  change i.pair A G H P ∈ List.zipWith (s(·, ·))
    (chunkBoundaryVertices (P i.1).start (sideRunRecords H (P i.1).walk))
    (chunkBoundaryVertices (P i.1).start (sideRunRecords H (P i.1).walk)).tail
  rw [← hzip, chunkEndpointPairs_eq_records _ _ (sideRunRecords_nonempty (P i.1).walk),
    sideRunRecords_restore, List.map_map]
  exact List.mem_map.2 ⟨i.2.val, i.2.property, fullRecord_pair G H (P i.1).walk _ i.2.property⟩

/-- Every contracted path vertex belongs to the original connecting path. -/
theorem sideBoundaryPairPath_vertices_subset (p : {p // p ∈ A.pairs}) :
    (sideBoundaryPairPath A G H P hP p).vertices ⊆ (P p).vertices := by
  intro a ha
  change a ∈ (sideBoundaryPairPath A G H P hP p).walk.support at ha
  rw [sideBoundaryPairPath_support] at ha
  exact (sideBoundaryVertices_sublist (P p).walk).subset ha

end GraphMinor.GM02
