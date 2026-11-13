module

public import GraphMinor.GM06.Alg511StoredPathEncoding
public import GraphMinor.GM06.Alg511ReflectedInputRep
import GraphMinor.GM06.Section5PathImage
import Mathlib.Tactic

/-!
# The stored initial paths after orientation reversal

In VI (5.11), page 134, reflection retains every original edge
label and reindexes the paths by the reflected cuff order. Make
this action explicit on the retained path drawings and curves.
The new paths are their actual images, and every curve winding
is negated. A finite labelled path still uses the same ordinary
edge words when its vertex and edge labels are interpreted by
the reflected drawing. Hence materializing the reflected cuff
sources gives an encoding of this same reflected linkage.
-/

public section
namespace GraphMinor.GM06
open GraphMinor.Compute GraphMinor.Surface Set GraphMinor.GM11

/-- Reflection of the retained stored paths, indexed by the
computed cuff permutation. The exposed path and curve formulas
allow the ordinary output rows to keep their exact interpretation. -/
@[expose] noncomputable def alg511ReflectedStoredLinkage {k : ℕ} {G : Drawing ClosedCylinder}
    (hk : 0 < k) (L : CylinderLinkage k G) : CylinderLinkage k (section5ReflectedDrawing k G) where
  pathDrawing i := section5ReflectedDrawing k (L.pathDrawing (gm06Alg511ReflectFin i))
  curve i := section5ReflectedCurve k (L.curve (gm06Alg511ReflectFin i))
  isSubdrawing i := by
    refine ⟨section5ReflectedDrawing_isSubdrawing (L.isSubdrawing _).1, ?_⟩
    rw [section5ReflectedDrawing_U, section5ReflectedDrawing_U]
    exact image_mono (L.isSubdrawing _).2
  isPath i := by
    let π : C(ClosedCylinder, ClosedCylinder) :=
      ⟨section5CylinderReflection k, (section5CylinderReflection k).continuous⟩
    have hh := isPathDrawing_image_of_injOn_pointSet (L.isPath (gm06Alg511ReflectFin i)) π
      (section5CylinderReflection k).injective.injOn
      (section5ReflectedDrawing_U k _) (section5ReflectedDrawing_V k _) (section5ReflectedDrawing_E k _)
    change IsPathDrawing _ (section5CylinderReflection k (cylinderM1Point k (gm06Alg511ReflectFin i))) _ at hh
    rw [alg511_reflection_M1 hk, gm06Alg511ReflectFin_involutive] at hh
    exact hh
  curve_parametrizes i := by
    refine ⟨(section5CylinderReflection k).injective.comp (L.curve_parametrizes _).1, ?_, ?_, rfl⟩
    · rw [section5ReflectedDrawing_U, ← (L.curve_parametrizes (gm06Alg511ReflectFin i)).2.1,
        ← range_comp]
      rfl
    · change section5CylinderReflection k (L.curve (gm06Alg511ReflectFin i) 0) = _
      rw [(L.curve_parametrizes _).2.2.1, alg511_reflection_M1 hk, gm06Alg511ReflectFin_involutive]
  curve_one_mem i := by
    obtain ⟨j, hj⟩ := L.curve_one_mem (gm06Alg511ReflectFin i)
    exact ⟨gm06Alg511ReflectFin j,
      (alg511_reflection_M2 hk j).symm.trans (congrArg (section5CylinderReflection k) hj)⟩
  pairwise_disjoint := by
    intro i j hij
    have hσ : gm06Alg511ReflectFin i ≠ gm06Alg511ReflectFin j :=
      (gm06Alg511ReflectFin_involutive).injective.ne hij
    rw [section5ReflectedDrawing_U, section5ReflectedDrawing_U]
    apply disjoint_left.mpr
    rintro p ⟨a, ha, rfl⟩ ⟨b, hb, heq⟩
    have hba : b = a := (section5CylinderReflection k).injective heq
    exact disjoint_left.mp (L.pairwise_disjoint hσ) ha (hba ▸ hb)

/-- The winding of the explicitly retained reflected linkage is
the negative of its original winding, as required in VI (5.11). -/
theorem alg511_reflectedStoredLinkage_hasTheta {k : ℕ} {G : Drawing ClosedCylinder}
    (hk : 0 < k) (L : CylinderLinkage k G) {θ : ℝ} (hθ : L.HasTheta θ) :
    (alg511ReflectedStoredLinkage hk L).HasTheta (-θ) := by
  intro i
  change windingNumber (section5ReflectedCurve k (L.curve (gm06Alg511ReflectFin i))) = -θ
  rw [windingNumber_section5ReflectedCurve, hθ]

private theorem reflected_walkDrawing_eq {k : ℕ} {G : Drawing ClosedCylinder}
    {a b c d : ClosedCylinder} (W : GraphWalk G.toGraph a b)
    (R : GraphWalk (section5ReflectedDrawing k G).toGraph c d)
    (hs : R.support = W.support.map (section5CylinderReflection k))
    (hE : R.edges = W.edges.map (image (section5CylinderReflection k))) :
    walkDrawing (section5ReflectedDrawing k G) R = section5ReflectedDrawing k (walkDrawing G W) := by
  apply Drawing.ext_of_V_E
  · rw [walkDrawing_V, section5ReflectedDrawing_V, walkDrawing_V]
    ext v
    change v ∈ R.support ↔ ∃ u, u ∈ W.support ∧ section5CylinderReflection k u = v
    rw [hs]
    exact List.mem_map
  · rw [walkDrawing_E, section5ReflectedDrawing_E, walkDrawing_E]
    ext e
    change e ∈ R.edges ↔ ∃ f, f ∈ W.edges ∧ section5CylinderReflection k '' f = e
    rw [hE]
    exact List.mem_map

private theorem recast_encoded_walk {D : Drawing ClosedCylinder} {n : ℕ}
    {tagged : List ((Fin n × Fin n) × ℕ)} {vertex : Fin n → ClosedCylinder}
    {edge : Fin tagged.length → Set ClosedCylinder} {row : List ℕ}
    {a b c d : ClosedCylinder} (W : GraphWalk D.toGraph a b)
    (hs : W.IsSimple) (he : GM06WalkDartEncoding D.toGraph tagged vertex edge W row)
    {P : Drawing ClosedCylinder} (hP : walkDrawing D W = P) (ha : a = c) (hb : b = d) :
    ∃ R : GraphWalk D.toGraph c d, R.IsSimple ∧
      GM06WalkDartEncoding D.toGraph tagged vertex edge R row ∧ walkDrawing D R = P := by
  cases ha
  cases hb
  exact ⟨W, hs, he, hP⟩

/-- Reflecting the drawing interpretation and reordering the
finite reference paths gives exactly the ordinary-row encoding
of the reflected retained linkage. No edge words are changed. -/
theorem alg511_reflected_rows_of_labelled_walks {x : GM06Alg511WindingInput} {G : Drawing ClosedCylinder}
    (rep : GM06Alg511GraphTurnRep x G) (hk : 0 < x.drawing.pathCount)
    (finish : Fin x.drawing.pathCount → Fin x.drawing.vertexCount)
    (W : ∀ i, GraphWalk (gm06Alg511LabelGraph rep.graph.pairs) (rep.source i) (finish i))
    (actual : ∀ i, GraphWalk G.toGraph (rep.graph.vertex (rep.source i)).val (rep.graph.vertex (finish i)).val)
    (L : CylinderLinkage x.drawing.pathCount G)
    (hsimple : ∀ i, (W i).IsSimple)
    (hsupport : ∀ i, (actual i).support = (W i).support.map (fun j => (rep.graph.vertex j).val))
    (hedges : ∀ i, (actual i).edges = (W i).edges.map (fun j => (rep.graph.edge j).val))
    (hpath : ∀ i, L.pathDrawing i = walkDrawing G (actual i))
    (hfinish : ∀ i, L.curve i 1 = (rep.graph.vertex (finish i)).val) :
    GM06LinkageRowsEncoding (alg511ReflectedStoredLinkage hk L)
      (alg511ReflectedInputRep rep hk).graph.initialTagged (alg511ReflectedInputRep rep hk).graph.vertexLabels
      (alg511ReflectedInputRep rep hk).graph.edgeLabels
      (List.ofFn (fun i => gm06Alg511LabelWalkDarts rep.graph.pairs (W (gm06Alg511ReflectFin i)))) := by
  let rp := alg511ReflectedInputRep rep hk
  refine ⟨List.length_ofFn, ?_⟩
  intro i
  rw [List.getElem?_eq_getElem (by rw [List.length_ofFn]; exact i.isLt), Option.getD_some, List.getElem_ofFn]
  let j := gm06Alg511ReflectFin i
  obtain ⟨R, hs, hE, henc⟩ := alg511_exists_encoded_actual_walk rp.graph (W j)
  have hR : R.IsSimple := by
    change R.support.Nodup
    rw [hs]
    exact (hsimple j).map (Subtype.val_injective.comp rp.graph.vertex.injective)
  have hsup : R.support = (actual j).support.map (section5CylinderReflection x.drawing.pathCount) := by
    rw [hs, hsupport, List.map_map]
    rfl
  have hEdges : R.edges = (actual j).edges.map (image (section5CylinderReflection x.drawing.pathCount)) := by
    rw [hE, hedges, List.map_map]
    rfl
  have hdraw : walkDrawing (section5ReflectedDrawing x.drawing.pathCount G) R =
      (alg511ReflectedStoredLinkage hk L).pathDrawing i := by
    change _ = section5ReflectedDrawing x.drawing.pathCount (L.pathDrawing j)
    rw [hpath]
    exact reflected_walkDrawing_eq (actual j) R hsup hEdges
  have hf : (alg511ReflectedStoredLinkage hk L).curve i 1 = (rp.graph.vertex (finish j)).val := by
    change section5CylinderReflection x.drawing.pathCount (L.curve j 1) = _
    rw [hfinish]
    rfl
  have hstart : (rp.graph.vertex (rep.source j)).val = cylinderM1Point x.drawing.pathCount i :=
    rp.source_point i
  exact recast_encoded_walk R hR henc hdraw hstart hf.symm

/-- The same numeric materialization, using the reflected cuff
source order, gives the reflected linkage's rows in the successor
interface. The raw flow and choice arrays remain the original ones. -/
theorem alg511_reflected_storedPathRows_encode_linkage
    {x : GM06Alg511WindingInput} {G : Drawing ClosedCylinder}
    (rep : GM06Alg511GraphTurnRep x G) (hk : 0 < x.drawing.pathCount) (out choices : List ℕ)
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
    GM06LinkageRowsEncoding (alg511ReflectedStoredLinkage hk L)
      (alg511ReflectedInputRep rep hk).graph.initialTagged (alg511ReflectedInputRep rep hk).graph.vertexLabels
      (alg511ReflectedInputRep rep hk).graph.edgeLabels
      (gm06Alg511StoredPathRows x.drawing out choices
        (List.ofFn (fun i => rep.source (gm06Alg511ReflectFin i)))) := by
  have heach (i : Fin x.drawing.pathCount) :
      gm06Alg511StoredPathRow x.drawing out choices (rep.source (gm06Alg511ReflectFin i)).val =
        gm06Alg511LabelWalkDarts rep.graph.pairs (W (gm06Alg511ReflectFin i)) := by
    rw [gm06Alg511StoredPathRow_eq_chosen x.drawing out choices hsys _ (hu _), ← hflow, ← hdarts]
  have hrows : gm06Alg511StoredPathRows x.drawing out choices
      (List.ofFn (fun i => rep.source (gm06Alg511ReflectFin i))) =
      List.ofFn (fun i => gm06Alg511LabelWalkDarts rep.graph.pairs (W (gm06Alg511ReflectFin i))) := by
    simp only [gm06Alg511StoredPathRows, List.map_ofFn]
    apply congrArg List.ofFn
    funext i
    exact heach i
  rw [hrows]
  exact alg511_reflected_rows_of_labelled_walks rep hk finish W actual L hsimple hsupport hedges hpath hfinish

end GraphMinor.GM06
