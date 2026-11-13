module

public import GraphMinor.GM06.Alg511InputRep
public import GraphMinor.Compute.GM06Alg511StoredPathRows
public import GraphMinor.GM06.Alg57InputRep
import GraphMinor.GM11.Walks
import Mathlib.Tactic

/-!
# The computed initial rows encode the retained linkage

The initializer of VI (5.11), page 134, interprets every chosen
finite edge as an actual drawing edge. The successor interface
requires those same choices as ordinary-dart walk encodings.
Transfer a finite labelled walk with its prescribed dart list,
retaining its support and edge sequence. Comparing these with the
already retained linkage walks identifies their path drawings.
Thus the rows materialized from the flow and choice arrays encode
the very same actual linkage. No new edge choice or path-row
coverage choice is used in this interpretation.
-/

public section
namespace GraphMinor.GM06
open GraphMinor.Compute GraphMinor.Surface Set GraphMinor.GM11

private theorem initial_dart_data {x : GM06Alg511Input} {G : Drawing ClosedCylinder}
    (rep : GM06SuccessorGraphRep (x.withLinkage []) G.toGraph)
    {e : Fin rep.pairs.length} {a b : Fin (x.withLinkage []).vertexCount}
    (he : (gm06Alg511LabelGraph rep.pairs).IsLink e a b) :
    ∃ hd : gm06Alg511LabelDart rep.pairs he < 2 * rep.initialTagged.length,
      (rep.initialTagged[gm06Alg511LabelDart rep.pairs he / 2]'(by omega)).2 = 1 ∧
      rep.edgeLabels ⟨gm06Alg511LabelDart rep.pairs he / 2, by omega⟩ = (rep.edge e).val ∧
      rep.vertexLabels (gm06DartTail rep.initialTagged ⟨_, hd⟩) = (rep.vertex a).val ∧
      rep.vertexLabels (gm06DartHead rep.initialTagged ⟨_, hd⟩) = (rep.vertex b).val := by
  classical
  have hlen : rep.initialTagged.length = rep.pairs.length := by
    simp only [GM06SuccessorGraphRep.initialTagged, List.length_map]
  by_cases ha : a = rep.pairs[e.val].1
  · have hb : b = rep.pairs[e.val].2 := by
      rcases he with ⟨_, hb⟩ | ⟨h', hb⟩
      · exact hb
      · exact hb.trans (ha.symm.trans h')
    have hd : gm06Alg511LabelDart rep.pairs he = 2 * e.val := by
      change 2 * e.val + (if a = rep.pairs[e.val].1 then 0 else 1) = _
      rw [ite_eq_left ha, Nat.add_zero]
    have hdiv : 2 * e.val / 2 = e.val := by omega
    have hmod : 2 * e.val % 2 = 0 := by omega
    have hbound : gm06Alg511LabelDart rep.pairs he < 2 * rep.initialTagged.length := by rw [hd, hlen]; omega
    refine ⟨hbound, ?_, ?_, ?_, ?_⟩
    · simp only [hd, GM06SuccessorGraphRep.initialTagged, List.getElem_map]
    · simp only [GM06SuccessorGraphRep.edgeLabels, hd, hdiv]
    · simp only [GM06SuccessorGraphRep.vertexLabels, Function.Embedding.coeFn_mk,
        gm06DartTail, hd, hdiv, hmod, ↓reduceIte,
        GM06SuccessorGraphRep.initialTagged, List.getElem_map, ← ha]
    · simp only [GM06SuccessorGraphRep.vertexLabels, Function.Embedding.coeFn_mk,
        gm06DartHead, hd, hdiv, hmod, ↓reduceIte,
        GM06SuccessorGraphRep.initialTagged, List.getElem_map, ← hb]
  · have hab : a = rep.pairs[e.val].2 ∧ b = rep.pairs[e.val].1 :=
      he.resolve_left (fun h => ha h.1)
    have hd : gm06Alg511LabelDart rep.pairs he = 2 * e.val + 1 := by
      change 2 * e.val + (if a = rep.pairs[e.val].1 then 0 else 1) = _
      rw [ite_eq_right ha]
    have hdiv : (2 * e.val + 1) / 2 = e.val := by omega
    have hmod : ¬ (2 * e.val + 1) % 2 = 0 := by omega
    have hbound : gm06Alg511LabelDart rep.pairs he < 2 * rep.initialTagged.length := by rw [hd, hlen]; omega
    refine ⟨hbound, ?_, ?_, ?_, ?_⟩
    · simp only [hd, hdiv, GM06SuccessorGraphRep.initialTagged, List.getElem_map]
    · simp only [GM06SuccessorGraphRep.edgeLabels, hd, hdiv]
    · simp only [GM06SuccessorGraphRep.vertexLabels, Function.Embedding.coeFn_mk,
        gm06DartTail, hd, hdiv, hmod, ↓reduceIte,
        GM06SuccessorGraphRep.initialTagged, List.getElem_map, ← hab.1]
    · simp only [GM06SuccessorGraphRep.vertexLabels, Function.Embedding.coeFn_mk,
        gm06DartHead, hd, hdiv, hmod, ↓reduceIte,
        GM06SuccessorGraphRep.initialTagged, List.getElem_map, ← hab.2]

/-- A finite labelled walk transfers to an actual walk with exactly
its ordinary-dart encoding, support and edge sequence. -/
theorem alg511_exists_encoded_actual_walk {x : GM06Alg511Input} {G : Drawing ClosedCylinder}
    (rep : GM06SuccessorGraphRep (x.withLinkage []) G.toGraph)
    {a b : Fin (x.withLinkage []).vertexCount} (W : GraphWalk (gm06Alg511LabelGraph rep.pairs) a b) :
    ∃ R : GraphWalk G.toGraph (rep.vertex a).val (rep.vertex b).val,
      R.support = W.support.map (fun j => (rep.vertex j).val) ∧
      R.edges = W.edges.map (fun j => (rep.edge j).val) ∧
      GM06WalkDartEncoding G.toGraph rep.initialTagged rep.vertexLabels rep.edgeLabels R
        (gm06Alg511LabelWalkDarts rep.pairs W) := by
  induction W with
  | nil ha => exact ⟨.nil (rep.vertex _).property, rfl, rfl, .nil _⟩
  | @cons a c b e he W ih =>
    have hl : G.toGraph.IsLink (rep.edge e).val (rep.vertex a).val (rep.vertex c).val := by
      rcases he with ⟨ha, hc⟩ | ⟨ha, hc⟩
      · simpa only [ha, hc] using rep.link e
      · simpa only [ha, hc] using (rep.link e).symm
    obtain ⟨R, hs, hE, henc⟩ := ih
    obtain ⟨hd, hactive, hedge, htail, hhead⟩ := initial_dart_data rep he
    refine ⟨.cons hl R, ?_, ?_, .cons hd hactive hedge htail hhead henc⟩
    · change (rep.vertex a).val :: R.support = (rep.vertex a).val :: W.support.map (fun j => (rep.vertex j).val)
      rw [hs]
    · change (rep.edge e).val :: R.edges = (rep.edge e).val :: W.edges.map (fun j => (rep.edge j).val)
      rw [hE]

/-- Finite labelled walks already retained by the initializer give
the ordinary-row encoding of that same actual linkage. The support
and edge equalities identify each path drawing exactly. -/
theorem alg511_linkage_rows_of_labelled_walks {x : GM06Alg511WindingInput} {G : Drawing ClosedCylinder}
    (rep : GM06Alg511GraphTurnRep x G) (finish : Fin x.drawing.pathCount → Fin x.drawing.vertexCount)
    (W : ∀ i, GraphWalk (gm06Alg511LabelGraph rep.graph.pairs) (rep.source i) (finish i))
    (actual : ∀ i, GraphWalk G.toGraph (rep.graph.vertex (rep.source i)).val (rep.graph.vertex (finish i)).val)
    (L : CylinderLinkage x.drawing.pathCount G)
    (hsimple : ∀ i, (W i).IsSimple)
    (hsupport : ∀ i, (actual i).support = (W i).support.map (fun j => (rep.graph.vertex j).val))
    (hedges : ∀ i, (actual i).edges = (W i).edges.map (fun j => (rep.graph.edge j).val))
    (hpath : ∀ i, L.pathDrawing i = walkDrawing G (actual i))
    (hfinish : ∀ i, L.curve i 1 = (rep.graph.vertex (finish i)).val) :
    GM06LinkageRowsEncoding L rep.graph.initialTagged rep.graph.vertexLabels rep.graph.edgeLabels
      (List.ofFn (fun i => gm06Alg511LabelWalkDarts rep.graph.pairs (W i))) := by
  refine ⟨List.length_ofFn, ?_⟩
  intro i
  rw [List.getElem?_eq_getElem (by rw [List.length_ofFn]; exact i.isLt), Option.getD_some, List.getElem_ofFn]
  obtain ⟨R, hs, hE, henc⟩ := alg511_exists_encoded_actual_walk rep.graph (W i)
  have hR : R.IsSimple := by
    change R.support.Nodup
    rw [hs]
    exact (hsimple i).map (Subtype.val_injective.comp rep.graph.vertex.injective)
  have hdraw : walkDrawing G R = L.pathDrawing i := by
    rw [hpath]
    apply Drawing.ext_of_V_E
    · rw [walkDrawing_V, walkDrawing_V, hs, hsupport]
    · rw [walkDrawing_E, walkDrawing_E, hE, hedges]
  rw [← rep.source_point i, hfinish]
  exact ⟨R, hR, henc, hdraw⟩

/-- The numerically materialized rows of every stored source trace
encode the retained actual linkage, in precisely its original cuff
order and using precisely the computed edge choices. -/
theorem alg511_storedPathRows_encode_linkage {x : GM06Alg511WindingInput} {G : Drawing ClosedCylinder}
    (rep : GM06Alg511GraphTurnRep x G) (out choices : List ℕ)
    (hsys : IsValidPathSystem x.drawing.flowGraph x.drawing.flowInput.A x.drawing.flowInput.B
      (decUsed x.drawing.vertexCount out) (decPred x.drawing.vertexCount out)
      (decSucc x.drawing.vertexCount out))
    (hu : ∀ i, rep.source i ∈ pathStarts (decUsed x.drawing.vertexCount out) (decPred x.drawing.vertexCount out))
    (finish : Fin x.drawing.pathCount → Fin x.drawing.vertexCount)
    (W : ∀ i, GraphWalk (gm06Alg511LabelGraph rep.graph.pairs) (rep.source i) (finish i))
    (actual : ∀ i, GraphWalk G.toGraph (rep.graph.vertex (rep.source i)).val (rep.graph.vertex (finish i)).val)
    (L : CylinderLinkage x.drawing.pathCount G)
    (hsimple : ∀ i, (W i).IsSimple)
    (hsupport : ∀ i, (actual i).support = (W i).support.map (fun j => (rep.graph.vertex j).val))
    (hedges : ∀ i, (actual i).edges = (W i).edges.map (fun j => (rep.graph.edge j).val))
    (hpath : ∀ i, L.pathDrawing i = walkDrawing G (actual i))
    (hfinish : ∀ i, L.curve i 1 = (rep.graph.vertex (finish i)).val)
    (hflow : ∀ i, (W i).support = (abWalkOfStart hsys (rep.source i) (hu i)).walk.support)
    (hdarts : ∀ i, gm06Alg511LabelWalkDarts rep.graph.pairs (W i) =
      gm06Alg511ChosenDarts x.drawing choices (W i).support) :
    GM06LinkageRowsEncoding L rep.graph.initialTagged rep.graph.vertexLabels rep.graph.edgeLabels
      (gm06Alg511StoredPathRows x.drawing out choices (List.ofFn rep.source)) := by
  have heach (i : Fin x.drawing.pathCount) : gm06Alg511StoredPathRow x.drawing out choices (rep.source i).val =
      gm06Alg511LabelWalkDarts rep.graph.pairs (W i) := by
    rw [gm06Alg511StoredPathRow_eq_chosen x.drawing out choices hsys (rep.source i) (hu i), ← hflow, ← hdarts]
  have hrows : gm06Alg511StoredPathRows x.drawing out choices (List.ofFn rep.source) =
      List.ofFn (fun i => gm06Alg511LabelWalkDarts rep.graph.pairs (W i)) := by
    simp only [gm06Alg511StoredPathRows, List.map_ofFn]
    apply congrArg List.ofFn
    funext i
    exact heach i
  rw [hrows]
  exact alg511_linkage_rows_of_labelled_walks rep finish W actual L hsimple hsupport hedges hpath hfinish

end GraphMinor.GM06
