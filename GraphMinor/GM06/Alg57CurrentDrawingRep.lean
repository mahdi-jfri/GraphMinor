module

public import GraphMinor.GM06.Alg57PersistentRotations
public import GraphMinor.Compute.GM06LinkageRowsEncoding
import GraphMinor.GM06.Alg57RowBounds

/-!
# Interpreting the current arrays of VI (5.7)

The algorithm on page 133 retains the original vertex and edge slots.
Only live slots name the current drawing. The endpoint words and path
rows keep their old labels, and the two cuff families keep their fixed
labels after the original ordinary edge slots. The rotation rows use
positive polar charts, with no ends in a retired vertex slot.

The relation below records these meanings. It contains no assertion
about a reduction, a face orbit, a strip component or a successor
linkage. The initial input gives this relation with all ordinary slots
live, by converting its consecutive edge enumeration to permanent labels.
-/

public section
namespace GraphMinor.GM06
open Set Topology GraphMinor.Surface GraphMinor.GM11 GraphMinor.Compute unitInterval

/-- The current graph, cuff, rotation and path fields in the realization
relation for VI (5.7), page 133. The live vertex and ordinary edge slots
are in bijection with the current vertices and edges. -/
structure GM06CurrentDrawingRep {k : ℕ} (x : GM06SuccessorInput)
    (G : Drawing ClosedCylinder) (L : CylinderLinkage k G) where
  tagged : List ((Fin x.vertexCount × Fin x.vertexCount) × ℕ)
  endpoints : x.endpoints = gm06EndpointWords (tagged.map fun p => (p.1.1.val, p.1.2.val))
  live : Finset (Fin x.vertexCount)
  vertex : Fin x.vertexCount → ClosedCylinder
  vertex_mem : ∀ a ∈ live, vertex a ∈ G.V
  vertex_inj : InjOn vertex (↑live : Set (Fin x.vertexCount))
  vertex_cover : ∀ v ∈ G.V, ∃ a ∈ live, vertex a = v
  edge : Fin tagged.length → Set ClosedCylinder
  edge_inj : InjOn edge {j | tagged[j].2 = 1}
  edge_cover : ∀ e ∈ G.E, ∃ j : Fin tagged.length, tagged[j].2 = 1 ∧ edge j = e
  links : ∀ j : Fin tagged.length, tagged[j].2 = 1 →
    G.toGraph.IsLink (edge j) (vertex tagged[j].1.1) (vertex tagged[j].1.2)
  ends_live : ∀ j : Fin tagged.length, tagged[j].2 = 1 →
    tagged[j].1.1 ∈ live ∧ tagged[j].1.2 ∈ live
  source : Fin k → Fin x.vertexCount
  target : Fin k → Fin x.vertexCount
  inner : x.innerCuff = List.ofFn (fun i => (source i).val)
  outer : x.outerCuff = List.ofFn (fun i => (target i).val)
  source_live : ∀ i, source i ∈ live
  target_live : ∀ i, target i ∈ live
  source_point : ∀ i, vertex (source i) = cylinderM1Point k i
  target_point : ∀ i, vertex (target i) = cylinderM2Point k i
  linkage : GM06LinkageRowsEncoding L tagged vertex edge x.linkage
  cuffed : Drawing ClosedCylinder
  subdrawing : G.IsSubdrawing cuffed
  cuffed_U : cuffed.U = G.U ∪ bd ClosedCylinder
  cuffed_V : cuffed.V = G.V
  label : (cylinderSphereDrawing cuffed).E ↪ ℕ
  par : Set (OnePoint EuclideanPlane) → I → OnePoint EuclideanPlane
  edgePar : EdgePar (cylinderSphereDrawing cuffed) par
  ordinary_labels : ∀ j : Fin tagged.length, tagged[j].2 = 1 →
    ∃ f : (cylinderSphereDrawing cuffed).E,
      f.val = cylinderToSphere '' edge j ∧ label f = j.val
  inner_labels : ∀ i : Fin k, ∃ f : (cylinderSphereDrawing cuffed).E,
    f.val = cylinderToSphere '' (initialCuffGapCurve k i '' Ioo 0 1) ∧
      label f = tagged.length + i.val
  outer_labels : ∀ i : Fin k, ∃ f : (cylinderSphereDrawing cuffed).E,
    f.val = cylinderToSphere '' (alg511OuterCuffGapCurve k i '' Ioo 0 1) ∧
      label f = tagged.length + k + i.val
  ordinary_ends : ∀ j : Fin tagged.length, tagged[j].2 = 1 →
    par (cylinderToSphere '' edge j) 0 = cylinderToSphere (vertex tagged[j].1.1) ∧
      par (cylinderToSphere '' edge j) 1 = cylinderToSphere (vertex tagged[j].1.2)
  inner_par : ∀ i : Fin k, ∀ t : I,
    par (cylinderToSphere '' (initialCuffGapCurve k i '' Ioo 0 1)) t =
      cylinderToSphere (initialCuffGapCurve k i t)
  outer_par : ∀ i : Fin k, ∀ t : I,
    par (cylinderToSphere '' (alg511OuterCuffGapCurve k i '' Ioo 0 1)) t =
      cylinderToSphere (alg511OuterCuffGapCurve k i t)
  rows_length : x.rotations.length = x.vertexCount
  rows : ∀ a : Fin x.vertexCount, a ∈ live →
    GM06PersistentRotationRowRep label par (cylinderToSphere (vertex a))
      (x.rotations.getD a.val [])
  retired_rows : ∀ a : Fin x.vertexCount, a ∉ live → x.rotations.getD a.val [] = []

/-- The original six-field input realizes the current drawing with
all original slots live, the given linkage rows unchanged, and the
initial edge map: the ordinary slot `j` names the `j`-th input edge. -/
theorem GM06SuccessorInputRep.exists_currentDrawingRep_edge
    {k : ℕ} {x : GM06SuccessorInput} {G : Drawing ClosedCylinder}
    {L : CylinderLinkage k G} (rep : GM06SuccessorInputRep x G L) :
    ∃ cur : GM06CurrentDrawingRep x G L,
      cur.tagged = rep.graph.initialTagged ∧ cur.live = Finset.univ ∧
        cur.vertex = rep.graph.vertexLabels ∧ HEq cur.edge rep.graph.edgeLabels ∧
          ∀ (h : cur.tagged.length = rep.graph.initialTagged.length)
            (j : Fin cur.tagged.length), cur.edge j = rep.graph.edgeLabels (Fin.cast h j) := by
  classical
  obtain ⟨F, e, γ, hGF, hFU, hFV, hγ, he, hi, ho, hends, hI, hO, hlen, hrows⟩ :=
    rep.rotations
  have htag (j : Fin rep.graph.initialTagged.length) :
      rep.graph.initialTagged[j] =
        (rep.graph.pairs[j.val]'(by simpa only [GM06SuccessorGraphRep.initialTagged,
          List.length_map] using j.isLt), 1) := by
    exact List.getElem_map (fun p => (p, 1))
  have hVinj : Function.Injective rep.graph.vertexLabels := rep.graph.vertexLabels.injective
  have hEinj : Function.Injective rep.graph.edgeLabels := by
    intro a b hab
    apply Fin.ext
    exact congrArg (fun j : Fin rep.graph.pairs.length => j.val)
      (rep.graph.edge.injective (Subtype.ext hab))
  refine ⟨{
    tagged := rep.graph.initialTagged
    endpoints := ?_
    live := Finset.univ
    vertex := rep.graph.vertexLabels
    vertex_mem := fun a _ => (rep.graph.vertex a).property
    vertex_inj := fun _ _ _ _ h => hVinj h
    vertex_cover := ?_
    edge := rep.graph.edgeLabels
    edge_inj := fun _ _ _ _ h => hEinj h
    edge_cover := ?_
    links := fun j _ => rep.graph.initial_links j
    ends_live := fun _ _ => ⟨Finset.mem_univ _, Finset.mem_univ _⟩
    source := rep.source
    target := rep.target
    inner := rep.inner
    outer := rep.outer
    source_live := fun _ => Finset.mem_univ _
    target_live := fun _ => Finset.mem_univ _
    source_point := rep.source_point
    target_point := rep.target_point
    linkage := rep.linkage
    cuffed := F
    subdrawing := hGF
    cuffed_U := hFU
    cuffed_V := hFV
    label := gm06InputEdgeLabels e
    par := γ
    edgePar := hγ
    ordinary_labels := ?_
    inner_labels := ?_
    outer_labels := ?_
    ordinary_ends := ?_
    inner_par := hI
    outer_par := hO
    rows_length := hlen
    rows := fun a _ => (hrows a).to_persistent
    retired_rows := fun a ha => False.elim (ha (Finset.mem_univ a))
  }, rfl, rfl, rfl, HEq.rfl, fun _ _ => rfl⟩
  · simpa only [GM06SuccessorGraphRep.initialTagged, List.map_map, Function.comp_def]
      using rep.graph.endpoints
  · intro v hv
    obtain ⟨a, ha⟩ := rep.graph.vertex.surjective ⟨v, hv⟩
    exact ⟨a, Finset.mem_univ _, congrArg Subtype.val ha⟩
  · intro f hf
    obtain ⟨j, hj⟩ := rep.graph.edge.surjective ⟨f, hf⟩
    let a : Fin rep.graph.initialTagged.length :=
      ⟨j.val, by simpa only [GM06SuccessorGraphRep.initialTagged, List.length_map] using j.isLt⟩
    refine ⟨a, ?_, ?_⟩
    · simp only [htag]
    · exact congrArg Subtype.val hj
  · intro j _
    let a : Fin rep.graph.pairs.length :=
      ⟨j.val, by simpa only [GM06SuccessorGraphRep.initialTagged, List.length_map] using j.isLt⟩
    refine ⟨e (a.castAdd (k + k)), he a, ?_⟩
    simp only [gm06InputEdgeLabels, Function.Embedding.coeFn_mk, Equiv.symm_apply_apply]
    rfl
  · intro i
    refine ⟨e ((i.castAdd k).natAdd rep.graph.pairs.length), hi i, ?_⟩
    simp only [gm06InputEdgeLabels, Function.Embedding.coeFn_mk, Equiv.symm_apply_apply,
      Fin.val_natAdd, Fin.val_castAdd, GM06SuccessorGraphRep.initialTagged, List.length_map]
  · intro i
    refine ⟨e ((i.natAdd k).natAdd rep.graph.pairs.length), ho i, ?_⟩
    simp only [gm06InputEdgeLabels, Function.Embedding.coeFn_mk, Equiv.symm_apply_apply,
      Fin.val_natAdd, GM06SuccessorGraphRep.initialTagged, List.length_map]
    omega
  · intro j _
    rw [htag]
    exact hends ⟨j.val, by simpa only [GM06SuccessorGraphRep.initialTagged, List.length_map] using j.isLt⟩

/-- The original six-field input realizes the current drawing with
all original slots live and the given linkage rows unchanged. -/
theorem GM06SuccessorInputRep.exists_currentDrawingRep
    {k : ℕ} {x : GM06SuccessorInput} {G : Drawing ClosedCylinder}
    {L : CylinderLinkage k G} (rep : GM06SuccessorInputRep x G L) :
    ∃ cur : GM06CurrentDrawingRep x G L,
      cur.tagged = rep.graph.initialTagged ∧ cur.live = Finset.univ ∧
        cur.vertex = rep.graph.vertexLabels := by
  obtain ⟨cur, ht, hl, hv, -⟩ := rep.exists_currentDrawingRep_edge
  exact ⟨cur, ht, hl, hv⟩

end GraphMinor.GM06
