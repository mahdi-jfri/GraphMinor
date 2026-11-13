module

public import GraphMinor.GM06.Alg57CurrentFaceVertices
public import GraphMinor.GM06.Alg57Find4Link
import GraphMinor.GM06.Alg57CutPathKeys

/-!
# The computed boundary path lists

Section 12 of the proof of VI (5.7), page 133, lists the chosen
left boundary path by its copied edges and arrival vertices.
The right boundary is listed by the other copies. The functions
below read these lists directly from original directed path words
and endpoint arrays. Modulo bounds make the functions total. On
actual current inputs each endpoint is already in range, so these
bounds do not change a word. The current walk encoding proves that
the lists trace exactly the original linkage path.
-/

public section
namespace GraphMinor.GM06
open Set GraphMinor.Surface GraphMinor.GM11 GraphMinor.Compute

/-- A bounded left or right copy of an original numeric vertex. -/
@[expose] def gm06CutVertexFin (n : ℕ) (hn : 0 < n) (v : ℕ) (left : Bool) : Fin (2 * n) :=
  ⟨gm06CutVertex (v % n) left, by
    have hv := Nat.mod_lt v hn
    cases left <;> simp only [gm06CutVertex, Bool.not_false, Bool.not_true,
      Bool.toNat_false, Bool.toNat_true] <;> omega⟩

/-- The chosen boundary path as copied edge and arrival labels. -/
@[expose] def gm06CutPathSteps (n : ℕ) (hn : 0 < n) (origins path : List ℕ)
    (left : Bool) : List (ℕ × Fin (2 * n)) :=
  path.map (fun d => (gm06CutDart d (!left).toNat / 2,
    gm06CutVertexFin n hn (origins[gm06DartMate d]?.getD 0) left))

/-- The vertex labels of the chosen boundary path in traversal order. -/
@[expose] def gm06CutPathLabels (n : ℕ) (hn : 0 < n) (origins path : List ℕ)
    (source : ℕ) (left : Bool) : List (Fin (2 * n)) :=
  find4PathLabels (gm06CutVertexFin n hn source left)
    (gm06CutPathSteps n hn origins path left)

/-- On a valid original vertex the bound leaves its copied slot unchanged. -/
theorem cutVertexFin_val {n v : ℕ} (hn : 0 < n) (hv : v < n) (left : Bool) :
    (gm06CutVertexFin n hn v left).val = gm06CutVertex v left := by
  simp only [gm06CutVertexFin, Nat.mod_eq_of_lt hv]

/-- The original edge index is unchanged by either copied edge tag. -/
theorem cutDart_edge_project (d : ℕ) (left : Bool) :
    (gm06CutDart d (!left).toNat / 2) / 2 = d / 2 := by
  have hm := Nat.mod_lt d (by decide : 0 < 2)
  cases left <;> simp only [gm06CutDart, Bool.not_false, Bool.not_true,
    Bool.toNat_false, Bool.toNat_true] <;> omega

namespace GM06CurrentDrawingRep
variable {k : ℕ} {x : GM06SuccessorInput} {G : Drawing ClosedCylinder}
  {L : CylinderLinkage k G} (rep : GM06CurrentDrawingRep x G L)
include rep

/-- The geometric edge at a copied ordinary slot, with an empty
value outside the original ordinary label space. -/
@[expose] def cutEdgePoint (e : ℕ) : Set ClosedCylinder :=
  if h : e / 2 < rep.tagged.length then rep.edge ⟨e / 2, h⟩ else ∅

/-- The two copied vertex labels project to the same original point. -/
theorem cutVertexFin_point (hn : 0 < x.vertexCount) (v : Fin x.vertexCount) (left : Bool) :
    rep.cutVertexPoint (gm06CutVertexFin x.vertexCount hn v.val left) = rep.vertex v := by
  apply congrArg rep.vertex
  apply Fin.ext
  change gm06CutVertex (v.val % x.vertexCount) left / 2 = v.val
  rw [gm06CutVertex_project, Nat.mod_eq_of_lt v.isLt]

/-- Either copied edge label of an ordinary path word names its
original geometric edge. -/
theorem cutEdgePoint_copy {d : ℕ} (hd : d < 2 * rep.tagged.length) (left : Bool) :
    rep.cutEdgePoint (gm06CutDart d (!left).toNat / 2) = rep.edge ⟨d / 2, by omega⟩ := by
  simp only [cutEdgePoint, cutDart_edge_project, show d / 2 < rep.tagged.length by omega, dite_true]

private theorem encoded_edges_eq {s t : ClosedCylinder} (W : GraphWalk G.toGraph s t)
    (path : List ℕ) (henc : GM06WalkDartEncoding G.toGraph rep.tagged rep.vertex rep.edge W path)
    (left : Bool) : W.edges = path.map (fun d => rep.cutEdgePoint (gm06CutDart d (!left).toNat / 2)) := by
  induction henc with
  | nil => rfl
  | @cons a b c e hl R rest d hd hactive hedge htail hhead hrest ih =>
    simp only [GraphWalk.edges_cons, List.map_cons, rep.cutEdgePoint_copy hd left, hedge, ih]

/-- The computed left or right boundary row traces exactly its
actual linkage path, including its ordered vertex and edge lists. -/
theorem computed_encoded_path_walk (hn : 0 < x.vertexCount) (i : Fin k) (left : Bool) :
    let path := x.linkage[i.val]'(by rw [rep.linkage.1]; exact i.isLt)
    ∃ W : GraphWalk G.toGraph (cylinderM1Point k i) (L.curve i 1),
      W.IsSimple ∧ GM06WalkDartEncoding G.toGraph rep.tagged rep.vertex rep.edge W path ∧
      walkDrawing G W = L.pathDrawing i ∧ (L.pathDrawing i).V = {v | v ∈ W.support} ∧
      W.support = (gm06CutPathLabels x.vertexCount hn x.endpoints path
        (rep.source i).val left).map rep.cutVertexPoint ∧
      W.edges = (gm06CutPathSteps x.vertexCount hn x.endpoints path left).map
        (fun st => rep.cutEdgePoint st.1) := by
  dsimp only
  obtain ⟨W, hW, henc, hP⟩ := rep.linkage.path i
  let lab : ℕ → ClosedCylinder := fun v => if h : v < x.vertexCount then
    rep.vertex ⟨v, h⟩ else cylinderPoint 1 (by norm_num) 0
  have hlab (v : Fin x.vertexCount) : lab v.val = rep.vertex v := by
    simp only [lab, v.isLt, dite_true]
  have hheads := walk_encoding_map_origins henc lab hlab true
  rw [← rep.endpoints] at hheads
  simp only [ite_true] at hheads
  have hpoints :
      (gm06CutPathSteps x.vertexCount hn x.endpoints
        (x.linkage[i.val]'(by rw [rep.linkage.1]; exact i.isLt)) left).map
          (fun st => rep.cutVertexPoint st.2) = W.support.tail := by
    rw [gm06CutPathSteps, List.map_map, ← hheads]
    apply List.map_congr_left
    intro d hd
    have hdflat : d ∈ x.linkage.flatten := List.mem_flatten.mpr ⟨_, List.getElem_mem _, hd⟩
    have hv := rep.cut_path_origin_lt true hdflat
    change rep.cutVertexPoint (gm06CutVertexFin x.vertexCount hn
      (x.endpoints[gm06DartMate d]?.getD 0) left) = lab (x.endpoints[gm06DartMate d]?.getD 0)
    have hv' : x.endpoints[gm06DartMate d]?.getD 0 < x.vertexCount := hv
    rw [show lab (x.endpoints[gm06DartMate d]?.getD 0) =
      rep.vertex ⟨x.endpoints[gm06DartMate d]?.getD 0, hv'⟩ by simp only [lab, hv', dite_true]]
    exact rep.cutVertexFin_point hn ⟨_, hv'⟩ left
  have hsupp : W.support =
      (gm06CutPathLabels x.vertexCount hn x.endpoints
        (x.linkage[i.val]'(by rw [rep.linkage.1]; exact i.isLt)) (rep.source i).val left).map
          rep.cutVertexPoint := by
    simp only [gm06CutPathLabels, find4PathLabels, List.map_cons, List.map_map,
      rep.cutVertexFin_point hn (rep.source i) left, rep.source_point]
    simp only [Function.comp_def]
    rw [hpoints]
    exact W.support_eq_cons
  have he : W.edges = (gm06CutPathSteps x.vertexCount hn x.endpoints
      (x.linkage[i.val]'(by rw [rep.linkage.1]; exact i.isLt)) left).map
        (fun st => rep.cutEdgePoint st.1) := by
    simpa only [gm06CutPathSteps, List.map_map, Function.comp_def] using rep.encoded_edges_eq W _ henc left
  exact ⟨W, hW, henc, hP, by rw [← hP, walkDrawing_V], hsupp, he⟩

/-- The computed left or right boundary row traces exactly its
actual linkage path, including its ordered vertex and edge lists. -/
theorem computed_path_walk (hn : 0 < x.vertexCount) (i : Fin k) (left : Bool) :
    let path := x.linkage[i.val]'(by rw [rep.linkage.1]; exact i.isLt)
    ∃ W : GraphWalk (L.pathDrawing i).toGraph (cylinderM1Point k i) (L.curve i 1),
      W.IsSimple ∧ (L.pathDrawing i).V = {v | v ∈ W.support} ∧
      W.support = (gm06CutPathLabels x.vertexCount hn x.endpoints path
        (rep.source i).val left).map rep.cutVertexPoint ∧
      W.edges = (gm06CutPathSteps x.vertexCount hn x.endpoints path left).map
        (fun st => rep.cutEdgePoint st.1) := by
  obtain ⟨W, hW, _, hP, hV, hsupp, he⟩ := rep.computed_encoded_path_walk hn i left
  obtain ⟨W', hs', he'⟩ := (L.isSubdrawing i).1.exists_walk_down W
    (fun v hv => by rw [← hP, walkDrawing_V]; exact hv)
    (fun e he => by rw [← hP, walkDrawing_E]; exact he)
  exact ⟨W', by simpa only [GraphWalk.IsSimple, hs'] using hW,
    hV.trans (by rw [hs']), hs'.trans hsupp, he'.trans he⟩

end GM06CurrentDrawingRep
end GraphMinor.GM06
