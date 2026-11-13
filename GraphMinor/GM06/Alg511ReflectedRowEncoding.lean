module

public import GraphMinor.Compute.GM06Alg511BinaryReflectPaths
public import GraphMinor.GM06.Alg511ReflectedStoredPaths
import Mathlib.Tactic

/-!
# Reflection of any retained ordinary linkage encoding

Reflect each actual walk in an encoded linkage by the cylinder
reflection. Its ordinary directed edge words stay the same, because
vertex and edge labels are interpreted by their reflected geometric
images. Reindex the paths by the reflected cuff permutation. Their
point sets are exactly the reflected linkage path drawings.

This proves the geometric interpretation of the concrete path-row
permutation used in VI (5.11), page 134, for every computed ordinary
linkage table. It does not require retaining a particular flow-path
construction or recomputing any edge turns.
-/

public section
namespace GraphMinor.GM06
open GraphMinor.Compute GraphMinor.Surface GraphMinor.GM11 Set

private theorem reflected_vertex (k : ℕ) {G : Drawing ClosedCylinder} {a : ClosedCylinder}
    (ha : a ∈ G.toGraph.vertexSet) : section5CylinderReflection k a ∈ (section5ReflectedDrawing k G).toGraph.vertexSet := by
  change section5CylinderReflection k a ∈ (section5ReflectedDrawing k G).V
  rw [section5ReflectedDrawing_V]
  exact mem_image_of_mem _ ha

private theorem reflected_link (k : ℕ) {G : Drawing ClosedCylinder}
    {e : Set ClosedCylinder} {a b : ClosedCylinder} (he : G.toGraph.IsLink e a b) :
    (section5ReflectedDrawing k G).toGraph.IsLink (section5CylinderReflection k '' e)
      (section5CylinderReflection k a) (section5CylinderReflection k b) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [section5ReflectedDrawing_E]
    exact ⟨e, he.1, rfl⟩
  · exact reflected_vertex k he.2.1
  · exact reflected_vertex k he.2.2.1
  · rw [← (section5CylinderReflection k).image_closure, section5ReflectedDrawing_V,
      ← Set.image_inter (section5CylinderReflection k).injective, he.2.2.2]
    simp

private noncomputable def reflectedWalk (k : ℕ) {G : Drawing ClosedCylinder} {a b : ClosedCylinder} :
    GraphWalk G.toGraph a b → GraphWalk (section5ReflectedDrawing k G).toGraph
      (section5CylinderReflection k a) (section5CylinderReflection k b)
  | .nil ha => .nil (reflected_vertex k ha)
  | .cons he W => .cons (reflected_link k he) (reflectedWalk k W)

private theorem reflectedWalk_support (k : ℕ) {G : Drawing ClosedCylinder} {a b : ClosedCylinder}
    (W : GraphWalk G.toGraph a b) : (reflectedWalk k W).support = W.support.map (section5CylinderReflection k) := by
  induction W with
  | nil _ => rfl
  | cons _ W ih => simpa only [reflectedWalk, GraphWalk.support_cons, List.map_cons] using congrArg (List.cons _) ih

private theorem reflectedWalk_edges (k : ℕ) {G : Drawing ClosedCylinder} {a b : ClosedCylinder}
    (W : GraphWalk G.toGraph a b) : (reflectedWalk k W).edges = W.edges.map (image (section5CylinderReflection k)) := by
  induction W with
  | nil _ => rfl
  | cons _ W ih => simpa only [reflectedWalk, GraphWalk.edges_cons, List.map_cons] using congrArg (List.cons _) ih

private theorem reflectedWalk_encoding (k : ℕ) {n : ℕ} {G : Drawing ClosedCylinder}
    (tagged : List ((Fin n × Fin n) × ℕ)) (vertex : Fin n → ClosedCylinder)
    (edge : Fin tagged.length → Set ClosedCylinder) {a b : ClosedCylinder}
    (W : GraphWalk G.toGraph a b) (row : List ℕ)
    (h : GM06WalkDartEncoding G.toGraph tagged vertex edge W row) :
    GM06WalkDartEncoding (section5ReflectedDrawing k G).toGraph tagged
      (fun i => section5CylinderReflection k (vertex i))
      (fun j => section5CylinderReflection k '' edge j) (reflectedWalk k W) row := by
  induction h with
  | nil ha => exact .nil (reflected_vertex k ha)
  | cons hd hactive hedge htail hhead hrest ih =>
    exact .cons hd hactive (congrArg (image (section5CylinderReflection k)) hedge)
      (congrArg (section5CylinderReflection k) htail) (congrArg (section5CylinderReflection k) hhead) ih

private theorem reflectedWalk_drawing (k : ℕ) {G : Drawing ClosedCylinder} {a b : ClosedCylinder}
    (W : GraphWalk G.toGraph a b) :
    walkDrawing (section5ReflectedDrawing k G) (reflectedWalk k W) = section5ReflectedDrawing k (walkDrawing G W) := by
  apply Drawing.ext_of_V_E
  · rw [walkDrawing_V, section5ReflectedDrawing_V, walkDrawing_V]
    ext v
    change v ∈ (reflectedWalk k W).support ↔ ∃ u, u ∈ W.support ∧ section5CylinderReflection k u = v
    rw [reflectedWalk_support]
    exact List.mem_map
  · rw [walkDrawing_E, section5ReflectedDrawing_E, walkDrawing_E]
    ext e
    change e ∈ (reflectedWalk k W).edges ↔ ∃ f, f ∈ W.edges ∧ section5CylinderReflection k '' f = e
    rw [reflectedWalk_edges]
    exact List.mem_map

private theorem row_at_reflected_index (rows : List (List ℕ)) {k : ℕ} (hlen : rows.length = k) (i : Fin k) :
    (gm06Alg511ReflectedPathRows rows)[i.val]?.getD [] = rows[(gm06Alg511ReflectFin i).val]?.getD [] := by
  subst k
  have hi : i.val < (gm06Alg511ReflectedPathRows rows).length := by
    rw [gm06Alg511ReflectedPathRows_length]
    exact i.isLt
  rw [List.getElem?_eq_getElem hi, Option.getD_some]
  simp only [gm06Alg511ReflectedPathRows, List.getElem_ofFn,
    List.getElem?_eq_getElem (gm06Alg511ReflectFin i).isLt, Option.getD_some]

private theorem recast_walk {D : Drawing ClosedCylinder} {n : ℕ}
    {tagged : List ((Fin n × Fin n) × ℕ)} {vertex : Fin n → ClosedCylinder}
    {edge : Fin tagged.length → Set ClosedCylinder} {row : List ℕ}
    {a b c d : ClosedCylinder} (W : GraphWalk D.toGraph a b)
    (hs : W.IsSimple) (he : GM06WalkDartEncoding D.toGraph tagged vertex edge W row)
    {P : Drawing ClosedCylinder} (hP : walkDrawing D W = P) (ha : a = c) (hb : b = d) :
    ∃ R : GraphWalk D.toGraph c d, R.IsSimple ∧ GM06WalkDartEncoding D.toGraph tagged vertex edge R row ∧
      walkDrawing D R = P := by
  cases ha
  cases hb
  exact ⟨W, hs, he, hP⟩

/-- Any ordinary linkage encoding, not only a particular flow
materialization, reflects by permuting the source rows and keeping
all their edge words. This is the linkage part of the orientation
reversal in VI (5.11), page 134. -/
theorem alg511_reflected_linkage_rows {x : GM06Alg511WindingInput} {G : Drawing ClosedCylinder}
    (rep : GM06Alg511GraphTurnRep x G) (hk : 0 < x.drawing.pathCount)
    (L : CylinderLinkage x.drawing.pathCount G) (rows : List (List ℕ))
    (hrows : GM06LinkageRowsEncoding L rep.graph.initialTagged rep.graph.vertexLabels rep.graph.edgeLabels rows) :
    GM06LinkageRowsEncoding (alg511ReflectedStoredLinkage hk L)
      (alg511ReflectedInputRep rep hk).graph.initialTagged (alg511ReflectedInputRep rep hk).graph.vertexLabels
      (alg511ReflectedInputRep rep hk).graph.edgeLabels (gm06Alg511ReflectedPathRows rows) := by
  let rp := alg511ReflectedInputRep rep hk
  refine ⟨(gm06Alg511ReflectedPathRows_length rows).trans hrows.1, ?_⟩
  intro i
  rw [row_at_reflected_index rows hrows.1 i]
  let j := gm06Alg511ReflectFin i
  obtain ⟨W, hsimple, hencoding, hpath⟩ := hrows.2 j
  let R := reflectedWalk x.drawing.pathCount W
  have hR : R.IsSimple := by
    change R.support.Nodup
    rw [reflectedWalk_support]
    exact hsimple.map (section5CylinderReflection x.drawing.pathCount).injective
  have henc : GM06WalkDartEncoding (section5ReflectedDrawing x.drawing.pathCount G).toGraph
      rp.graph.initialTagged rp.graph.vertexLabels rp.graph.edgeLabels R (rows[j.val]?.getD []) := by
    exact reflectedWalk_encoding x.drawing.pathCount rep.graph.initialTagged rep.graph.vertexLabels rep.graph.edgeLabels W _ hencoding
  have hdraw : walkDrawing (section5ReflectedDrawing x.drawing.pathCount G) R =
      (alg511ReflectedStoredLinkage hk L).pathDrawing i := by
    change _ = section5ReflectedDrawing x.drawing.pathCount (L.pathDrawing j)
    exact (reflectedWalk_drawing _ W).trans (congrArg (section5ReflectedDrawing x.drawing.pathCount) hpath)
  have hstart : section5CylinderReflection x.drawing.pathCount (cylinderM1Point x.drawing.pathCount j) =
      cylinderM1Point x.drawing.pathCount i := by
    rw [alg511_reflection_M1 hk]
    exact congrArg (cylinderM1Point x.drawing.pathCount) (gm06Alg511ReflectFin_involutive i)
  exact recast_walk R hR henc hdraw hstart rfl

end GraphMinor.GM06
