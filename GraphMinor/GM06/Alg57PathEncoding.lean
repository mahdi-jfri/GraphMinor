module

public import GraphMinor.GM06.Alg57InputRep
import GraphMinor.GM11.Walks
import GraphMinor.GM06.Alg57PositiveRotations
import GraphMinor.GM06.Alg511GraphInputExists

/-!
# Supplying the given linkage as ordinary directed rows

For VI (5.7), page 133, the supplied linkage is part of the instance.
Every actual walk can be encoded using the original edge bijection
and either orientation of each endpoint pair. Apply this to the
simple walks of its path drawings. The resulting rows describe
exactly the given linkage. Attaching them to a cuff-augmented graph
input leaves all graph, rotation and cuff fields unchanged.
Positive rotation coverage then supplies such an input for every
Section 5 drawing and given linkage.
-/

public section
namespace GraphMinor.GM06
open GraphMinor.Compute Set GraphMinor.Surface GraphMinor.GM11

/-- Any actual graph walk has an ordinary directed-word encoding
using the input's original edge positions and endpoint orientation. -/
theorem exists_initial_walk_encoding {x : GM06SuccessorInput} {G : Drawing ClosedCylinder}
    (rep : GM06SuccessorGraphRep x G.toGraph) {s t : ClosedCylinder}
    (W : GraphWalk G.toGraph s t) :
    ∃ row : List ℕ, GM06WalkDartEncoding G.toGraph rep.initialTagged rep.vertexLabels rep.edgeLabels W row := by
  induction W with
  | nil hs => exact ⟨[], .nil hs⟩
  | @cons s u t e hl R ih =>
    obtain ⟨row, hrow⟩ := ih
    let j := rep.edge.symm ⟨e, hl.edge_mem⟩
    have hedge : (rep.edge j).val = e := congrArg Subtype.val (rep.edge.apply_symm_apply _)
    have hcanon := rep.link j
    have hj : j.val < rep.initialTagged.length := by
      simpa only [GM06SuccessorGraphRep.initialTagged, List.length_map] using j.isLt
    have htag : rep.initialTagged[j.val]'hj = (rep.pairs[j.val], 1) := by
      simp only [GM06SuccessorGraphRep.initialTagged, List.getElem_map]
    have heq : rep.edgeLabels ⟨j.val, hj⟩ = e := hedge
    rw [hedge] at hcanon
    rcases hl.eq_and_eq_or_eq_and_eq hcanon with ⟨hs, hu⟩ | ⟨hs, hu⟩
    · have hd : 2 * j.val < 2 * rep.initialTagged.length := by omega
      have hdiv : 2 * j.val / 2 = j.val := by omega
      have hmod : 2 * j.val % 2 = 0 := by omega
      refine ⟨2 * j.val :: row, .cons hd ?_ ?_ ?_ ?_ hrow⟩
      · simpa only [hdiv, htag]
      · simpa only [hdiv] using heq
      · simpa only [gm06DartTail, hmod, ite_true, hdiv, htag, GM06SuccessorGraphRep.vertexLabels, Function.Embedding.coeFn_mk] using hs.symm
      · simpa only [gm06DartHead, hmod, ite_true, hdiv, htag, GM06SuccessorGraphRep.vertexLabels, Function.Embedding.coeFn_mk] using hu.symm
    · have hd : 2 * j.val + 1 < 2 * rep.initialTagged.length := by omega
      have hdiv : (2 * j.val + 1) / 2 = j.val := by omega
      have hmod : (2 * j.val + 1) % 2 ≠ 0 := by omega
      refine ⟨(2 * j.val + 1) :: row, .cons hd ?_ ?_ ?_ ?_ hrow⟩
      · simpa only [hdiv, htag]
      · simpa only [hdiv] using heq
      · simpa only [gm06DartTail, hmod, ite_false, hdiv, htag, GM06SuccessorGraphRep.vertexLabels, Function.Embedding.coeFn_mk] using hs.symm
      · simpa only [gm06DartHead, hmod, ite_false, hdiv, htag, GM06SuccessorGraphRep.vertexLabels, Function.Embedding.coeFn_mk] using hu.symm

/-- Every given cylinder linkage has rows encoding its actual
simple path walks, with the same original edge labels. -/
theorem exists_initial_linkage_rows {k : ℕ} {x : GM06SuccessorInput} {G : Drawing ClosedCylinder}
    (rep : GM06SuccessorGraphRep x G.toGraph) (L : CylinderLinkage k G) :
    ∃ rows : List (List ℕ), GM06LinkageRowsEncoding L rep.initialTagged rep.vertexLabels rep.edgeLabels rows := by
  have hex (j : Fin k) : ∃ (row : List ℕ)
      (W : GraphWalk G.toGraph (cylinderM1Point k j) (L.curve j 1)),
      W.IsSimple ∧ GM06WalkDartEncoding G.toGraph rep.initialTagged rep.vertexLabels rep.edgeLabels W row ∧
      walkDrawing G W = L.pathDrawing j := by
    obtain ⟨W, hW, hV, hE⟩ := (L.isPath j).1
    obtain ⟨R, hs, he⟩ := (L.isSubdrawing j).1.exists_walk_up W
    have hsimple : R.IsSimple := by change R.support.Nodup; rw [hs]; exact hW
    obtain ⟨row, hrow⟩ := exists_initial_walk_encoding rep R
    refine ⟨row, R, hsimple, hrow, ?_⟩
    apply Drawing.ext_of_V_E
    · rw [walkDrawing_V, hs, ← hV]
    · rw [walkDrawing_E, he, ← hE]
  choose row W hsimple henc hpath using hex
  refine ⟨List.ofFn row, List.length_ofFn, ?_⟩
  intro j
  rw [List.getElem?_eq_getElem (show j.val < (List.ofFn row).length by
    rw [List.length_ofFn]; exact j.isLt), Option.getD_some, List.getElem_ofFn]
  exact ⟨W j, hsimple j, henc j, hpath j⟩

/-- Supplying the reference paths completes an interpreted
cuff-augmented graph input without changing any drawing field. -/
theorem exists_successor_input_with_reference_rows
    {k : ℕ} {x : GM06SuccessorInput} {G : Drawing ClosedCylinder}
    (rep : GM06SuccessorGraphRep x G.toGraph) (L : CylinderLinkage k G)
    (source target : Fin k → Fin x.vertexCount)
    (hinner : x.innerCuff = List.ofFn (fun i => (source i).val))
    (houter : x.outerCuff = List.ofFn (fun i => (target i).val))
    (hsource : ∀ i, (rep.vertex (source i)).val = cylinderM1Point k i)
    (htarget : ∀ i, (rep.vertex (target i)).val = cylinderM2Point k i)
    (hrot : GM06SuccessorRotationRep k x rep) :
    ∃ y : GM06SuccessorInput, Nonempty (GM06SuccessorInputRep y G L) ∧
      y.vertexCount = x.vertexCount ∧ y.endpoints = x.endpoints ∧ y.rotations = x.rotations ∧
      y.innerCuff = x.innerCuff ∧ y.outerCuff = x.outerCuff := by
  obtain ⟨rows, hrows⟩ := exists_initial_linkage_rows rep L
  let y : GM06SuccessorInput := {x with linkage := rows}
  let graph : GM06SuccessorGraphRep y G.toGraph := {
    vertex := rep.vertex
    pairs := rep.pairs
    endpoints := rep.endpoints
    edge := rep.edge
    link := rep.link }
  have hy : GM06SuccessorInputRep y G L := {
    graph := graph
    source := source
    target := target
    inner := hinner
    outer := houter
    source_point := hsource
    target_point := htarget
    linkage := hrows
    rotations := hrot }
  exact ⟨y, ⟨hy⟩, rfl, rfl, rfl, rfl, rfl⟩

/-- Copy the original graph interpretation after replacing only
the supplied rotation rows. No labels or endpoints change. -/
@[expose] def gm06GraphRepWithRotations {x : GM06SuccessorInput} {G : Drawing ClosedCylinder}
    (rep : GM06SuccessorGraphRep x G.toGraph) (rows : List (List ℕ)) :
    GM06SuccessorGraphRep {x with rotations := rows} G.toGraph where
  vertex := rep.vertex
  pairs := rep.pairs
  endpoints := rep.endpoints
  edge := rep.edge
  link := rep.link

/-- A graph input can be supplied with rotations of both cuff
families in the actual positive plane orientation. -/
theorem exists_successor_rotation_rows {k : ℕ} {x : GM06SuccessorInput} {G : Drawing ClosedCylinder}
    (hG : IsCylinderSection5Drawing k G) (rep : GM06SuccessorGraphRep x G.toGraph) :
    ∃ rows : List (List ℕ), GM06SuccessorRotationRep k {x with rotations := rows}
      (gm06GraphRepWithRotations rep rows) := by
  classical
  obtain ⟨F, edge, γ, _, hGF, hFU, hFV, hγ, hedgeG, hedgeI, hedgeO,
    hends, hγI, hγO, _, _⟩ := alg511_exists_augmented_rotation_rows hG x rep
  have hex (v : Fin x.vertexCount) : ∃ row : List ℕ,
      GM06SuccessorRotationRowRep edge γ (cylinderToSphere (rep.vertex v).val) row := by
    apply exists_successor_positive_rotation_row edge hγ
    · rw [cylinderSphereDrawing_V, hFV]
      exact mem_image_of_mem cylinderToSphere (rep.vertex v).property
    · exact ⟨cylToPlane (rep.vertex v).val, rfl⟩
  choose row hrow using hex
  refine ⟨List.ofFn row, F, edge, γ, hGF, hFU, hFV, hγ, hedgeG, hedgeI, hedgeO,
    hends, hγI, hγO, List.length_ofFn, ?_⟩
  intro v
  simpa only [gm06GraphRepWithRotations, Fin.eta, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem
    (show v.val < (List.ofFn row).length by rw [List.length_ofFn]; exact v.isLt),
    Option.getD_some, List.getElem_ofFn] using hrow v

/-- Every Section 5 drawing and given linkage have an ordinary
region-free input with both positively oriented cuff families.
All choices supply graph data, rotations and the given paths only. -/
theorem exists_successor_input {k : ℕ} {G : Drawing ClosedCylinder}
    (hG : IsCylinderSection5Drawing k G) (L : CylinderLinkage k G) :
    ∃ x : GM06SuccessorInput, Nonempty (GM06SuccessorInputRep x G L) := by
  obtain ⟨x, rep, _, _, _, _, _, source, hsource, _, hinner, target, htarget, houter⟩ :=
    alg511_exists_graph_cuff_input k G hG 0 1
  obtain ⟨rotations, hrot⟩ := exists_successor_rotation_rows hG rep
  obtain ⟨y, hy, _⟩ := exists_successor_input_with_reference_rows
    (gm06GraphRepWithRotations rep rotations) L source target hinner houter hsource htarget hrot
  exact ⟨y, hy⟩

end GraphMinor.GM06
