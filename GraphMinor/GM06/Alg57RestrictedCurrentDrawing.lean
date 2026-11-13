module

public import GraphMinor.GM06.Alg57CurrentDrawingRep
public import GraphMinor.GM06.Alg57RestrictedRotations
public import GraphMinor.Compute.GM06RestrictedLinkageRows
public import GraphMinor.Compute.GM06UndoDrawing
import GraphMinor.GM06.Alg57CurrentEndClassification
import GraphMinor.GM06.Alg511AdjoinCuffs
import GraphMinor.GM06.Alg511CuffEnumeration

/-!
# The current drawing relation after either deletion reduction

In the main loop of VI (5.7), page 133, Reductions 1 and 2 retain
an actual subdrawing and its given linkage. Extend the retained
drawing by the same two cuff families. Its sphere drawing is an
actual subdrawing of the old cuffed drawing. The old curves and
permanent labels therefore restrict to it, and filtering each old
row gives its positive new rotation. The finite live and edge masks
then give the complete updated current relation.
-/

public section
namespace GraphMinor.GM06
open Set Topology GraphMinor.Surface GraphMinor.GM11 GraphMinor.Compute unitInterval

/-- Pruning changes just the rotation field of the six-field input.
Activity and live masks are separate current arrays. -/
@[expose] def gm06RestrictSuccessorInput (x : GM06SuccessorInput) (mask : List ℕ) : GM06SuccessorInput :=
  { x with rotations := gm06PrunedRotationRows (gm06AugmentedActivity mask x.innerCuff.length) x.rotations }

private theorem sphere_subdrawing_of_subdrawing
    {F H : Drawing ClosedCylinder} (h : H.IsSubdrawing F) :
    (cylinderSphereDrawing H).IsSubdrawing (cylinderSphereDrawing F) := by
  constructor
  · rw [cylinderSphereDrawing_V, cylinderSphereDrawing_V]
    exact image_mono h.1
  · rw [cylinderSphereDrawing_E, cylinderSphereDrawing_E]
    exact image_mono h.2

/-- Adjoining the same cuff arcs commutes with passing to a proper
Section 5 subdrawing. All auxiliary edges are retained literally. -/
theorem cuff_subdrawing_of_subdrawing
    {k : ℕ} {G H F F' : Drawing ClosedCylinder}
    (hG : IsCylinderSection5Drawing k G) (hH : IsCylinderSection5Drawing k H)
    (hHG : H.IsSubdrawing G) (hGF : G.IsSubdrawing F) (hHF' : H.IsSubdrawing F')
    (hFU : F.U = G.U ∪ bd ClosedCylinder) (hFV : F.V = G.V)
    (hF'U : F'.U = H.U ∪ bd ClosedCylinder) (hF'V : F'.V = H.V) : F'.IsSubdrawing F := by
  constructor
  · rw [hF'V, hFV]
    exact hHG.1
  · rw [alg511_cuff_edges_eq hH hHF' hF'U hF'V, alg511_cuff_edges_eq hG hGF hFU hFV]
    exact union_subset_union hHG.2 subset_rfl

/-- The retained ordinary mask and a proper subdrawing determine
exactly which permanently labelled augmented ends survive. Both
cuff families remain active, including a one-path cuff loop. -/
theorem GM06CurrentDrawingRep.keep_active_iff_mem_subdrawing
    {k : ℕ} {x : GM06SuccessorInput} {G H : Drawing ClosedCylinder}
    {L : CylinderLinkage k G} (rep : GM06CurrentDrawingRep x G L)
    (hG : IsCylinderSection5Drawing k G) (hH : IsCylinderSection5Drawing k H)
    {F' : Drawing ClosedCylinder} (hHF' : H.IsSubdrawing F')
    (hF'U : F'.U = H.U ∪ bd ClosedCylinder) (hF'V : F'.V = H.V)
    (mask : List ℕ) (hlen : mask.length = rep.tagged.length)
    (hmask : ∀ j : Fin rep.tagged.length,
      mask[j.val]'(hlen.symm ▸ j.isLt) = 1 ↔ rep.tagged[j].2 = 1 ∧ rep.edge j ∈ H.E) :
    ∀ (f : (cylinderSphereDrawing rep.cuffed).E) (bit : Bool),
      gm06KeepActiveDart (gm06AugmentedActivity mask x.innerCuff.length)
        (2 * rep.label f + bit.toNat) = true ↔ f.val ∈ (cylinderSphereDrawing F').E := by
  have hklen : x.innerCuff.length = k := by rw [rep.inner]; exact List.length_ofFn
  have hFE := alg511_cuff_edges_eq hH hHF' hF'U hF'V
  have hmem (e : Set ClosedCylinder) :
      cylinderToSphere '' e ∈ (cylinderSphereDrawing F').E ↔ e ∈ F'.E := by
    rw [cylinderSphereDrawing_E]
    constructor
    · rintro ⟨a, ha, hae⟩
      exact (Set.image_injective.mpr injective_cylinderToSphere) hae ▸ ha
    · exact fun he => mem_image_of_mem (image cylinderToSphere) he
  intro f bit
  rw [hklen]
  rcases rep.edge_cases hG f with ⟨j, hj, hfj⟩ | ⟨i, hfi⟩ | ⟨i, hfi⟩
  · obtain ⟨g, hg, hgl⟩ := rep.ordinary_labels j hj
    have hlab : rep.label f = j.val :=
      (congrArg rep.label (Subtype.ext (hfj.trans hg.symm))).trans hgl
    rw [hlab, hfj, hmem]
    have heG := (rep.links j hj).edge_mem
    have heH : rep.edge j ∈ F'.E ↔ rep.edge j ∈ H.E := by
      rw [hFE]
      constructor
      · rintro (he | he)
        · exact he
        · rcases he with he | he
          · exact False.elim (disjoint_left.mp (alg511_cuff_edge_families_disjoint hG).1 heG he)
          · exact False.elim (disjoint_left.mp (alg511_cuff_edge_families_disjoint hG).2.1 heG he)
      · exact Or.inl
    have hm : mask[j.val]'(hlen.symm ▸ j.isLt) = 1 ↔ rep.edge j ∈ H.E :=
      ⟨fun hh => ((hmask j).mp hh).2, fun hh => (hmask j).mpr ⟨hj, hh⟩⟩
    exact (gm06KeepActiveDart_ordinary mask k ⟨j.val, hlen.symm ▸ j.isLt⟩ bit).trans (hm.trans heH.symm)
  · obtain ⟨g, hg, hgl⟩ := rep.inner_labels i
    have hlab : rep.label f = mask.length + i.val := by
      rw [hlen]
      exact (congrArg rep.label (Subtype.ext (hfi.trans hg.symm))).trans hgl
    have hnew : f.val ∈ (cylinderSphereDrawing F').E := by
      rw [hfi, hmem, hFE]
      exact Or.inr (Or.inl ⟨i, rfl⟩)
    rw [hlab]
    exact iff_of_true (gm06KeepActiveDart_cuff mask k i.val bit (by omega)) hnew
  · obtain ⟨g, hg, hgl⟩ := rep.outer_labels i
    have hlab : rep.label f = mask.length + (k + i.val) := by
      have hh := (congrArg rep.label (Subtype.ext (hfi.trans hg.symm))).trans hgl
      rw [hlen]
      exact hh.trans (Nat.add_assoc _ _ _)
    have hnew : f.val ∈ (cylinderSphereDrawing F').E := by
      rw [hfi, hmem, hFE]
      exact Or.inr (Or.inr ⟨i, rfl⟩)
    rw [hlab]
    exact iff_of_true (gm06KeepActiveDart_cuff mask k (k + i.val) bit (by omega)) hnew

/-- The actual masks and retained linkage construct the full new
current relation after a deletion. All positive rows are the exact
computed filters, and every retired slot has an empty row. -/
theorem GM06CurrentDrawingRep.exists_restricted_currentDrawingRep
    {k : ℕ} {x : GM06SuccessorInput} {G H : Drawing ClosedCylinder}
    {L : CylinderLinkage k G} (rep : GM06CurrentDrawingRep x G L)
    (hG : IsCylinderSection5Drawing k G) (hH : IsCylinderSection5Drawing k H)
    (hHG : H.IsSubdrawing G) (M : CylinderLinkage k H)
    (hpaths : M.pathDrawing = L.pathDrawing) (hcurves : M.curve = L.curve)
    (mask : List ℕ) (hlen : mask.length = rep.tagged.length)
    (hmask : ∀ j : Fin rep.tagged.length,
      mask[j.val]'(hlen.symm ▸ j.isLt) = 1 ↔ rep.tagged[j].2 = 1 ∧ rep.edge j ∈ H.E)
    (A : Finset (Fin x.vertexCount))
    (hA : ∀ a : Fin x.vertexCount, a ∈ A ↔ a ∈ rep.live ∧ rep.vertex a ∈ H.V) :
    ∃ cur : GM06CurrentDrawingRep (gm06RestrictSuccessorInput x mask) H M,
      cur.live = A ∧ cur.vertex = rep.vertex ∧
      cur.tagged = gm06RetagEdges rep.tagged mask ∧
      GM06UndoStep x.vertexCount k ⟨G, rep.tagged, rep.vertex, rep.edge⟩
        ⟨H, cur.tagged, cur.vertex, cur.edge⟩ none := by
  classical
  obtain ⟨F', _, _, hHF', hF'U, hF'V, _⟩ := alg511_exists_drawing_with_cuffs hH
  have hFF := cuff_subdrawing_of_subdrawing hG hH hHG rep.subdrawing hHF'
    rep.cuffed_U rep.cuffed_V hF'U hF'V
  have hS := sphere_subdrawing_of_subdrawing hFF
  let label' := gm06RestrictEdgeLabels hS rep.label
  have hγ' := edgePar_of_subdrawing hS rep.edgePar
  let updated := gm06RetagEdges rep.tagged mask
  let old : Fin updated.length → Fin rep.tagged.length := Fin.cast (gm06RetagEdges_length rep.tagged mask)
  let edge' : Fin updated.length → Set ClosedCylinder := fun j => rep.edge (old j)
  let keep := gm06KeepActiveDart (gm06AugmentedActivity mask x.innerCuff.length)
  have hkeep := rep.keep_active_iff_mem_subdrawing hG hH hHF' hF'U hF'V mask hlen hmask
  have htag (j : Fin updated.length) : updated[j] =
      (rep.tagged[old j].1, mask[j.val]'(by rw [hlen]; exact (old j).isLt)) :=
    gm06RetagEdges_getElem rep.tagged mask hlen (old j).isLt
  have hactive (j : Fin updated.length) (hj : updated[j].2 = 1) :
      rep.tagged[old j].2 = 1 ∧ edge' j ∈ H.E := by
    rw [htag] at hj
    exact (hmask (old j)).mp hj
  have hlinks (j : Fin updated.length) (hj : updated[j].2 = 1) :
      H.toGraph.IsLink (edge' j) (rep.vertex updated[j].1.1) (rep.vertex updated[j].1.2) := by
    have hl := (hHG.isLink_iff (hactive j hj).2).mpr (rep.links (old j) (hactive j hj).1)
    simpa only [htag] using hl
  have hsourceV (j : Fin k) : rep.vertex (rep.source j) ∈ H.V := by
    rw [rep.source_point]
    have hh : cylinderM1Point k j ∈ H.V ∩ bd ClosedCylinder := by
      rw [hH.2.2]
      exact Or.inl ⟨j, rfl⟩
    exact hh.1
  have htargetV (j : Fin k) : rep.vertex (rep.target j) ∈ H.V := by
    rw [rep.target_point]
    have hh : cylinderM2Point k j ∈ H.V ∩ bd ClosedCylinder := by
      rw [hH.2.2]
      exact Or.inr ⟨j, rfl⟩
    exact hh.1
  have hrow (j : Fin x.vertexCount) (hj : j ∈ rep.live) :=
    persistent_rotation_row_of_subdrawing hS rep.label (rep.rows j hj) keep hkeep
  have hnewRow (j : Fin x.vertexCount) :
      (gm06PrunedRotationRows (gm06AugmentedActivity mask x.innerCuff.length) x.rotations).getD j.val [] =
        (x.rotations.getD j.val []).filter keep := by
    rw [List.getD_eq_getElem _ [] (by simpa only [gm06PrunedRotationRows, List.length_map] using (rep.rows_length.symm ▸ j.isLt)),
      List.getD_eq_getElem _ [] (rep.rows_length.symm ▸ j.isLt)]
    simp only [gm06PrunedRotationRows, List.getElem_map]
    rfl
  have hretired (j : Fin x.vertexCount) (hj : j ∉ A) :
      (x.rotations.getD j.val []).filter keep = [] := by
    by_cases hjold : j ∈ rep.live
    · apply List.eq_nil_iff_forall_not_mem.mpr
      intro r hr
      obtain ⟨a, ha⟩ := ((hrow j hjold).2.1 r).mp hr
      have hpV : cylinderToSphere (rep.vertex j) ∈ (cylinderSphereDrawing F').V := by
        rw [← a.property.2]
        exact end_mem_V hγ' a.property.1 a.val.2
      rw [cylinderSphereDrawing_V, hF'V] at hpV
      obtain ⟨v, hv, hvj⟩ := hpV
      exact hj ((hA j).mpr ⟨hjold, injective_cylinderToSphere hvj ▸ hv⟩)
    · rw [rep.retired_rows j hjold]
      rfl
  have hpathRows := gm06LinkageRowsEncoding_restrict L M rep.tagged rep.vertex rep.edge x.linkage
    rep.linkage hHG hpaths hcurves mask hlen
    (fun j hj he => by
      have hjbound : j.val < mask.length := by rw [hlen]; exact j.isLt
      rw [List.getElem?_eq_getElem hjbound, Option.getD_some]
      exact (hmask j).mpr ⟨hj, he⟩)
  let x' : GM06SuccessorInput := { x with
    rotations := gm06PrunedRotationRows (gm06AugmentedActivity mask x.innerCuff.length) x.rotations }
  let cur : GM06CurrentDrawingRep x' H M := {
    tagged := updated
    endpoints := by
      change x.endpoints = gm06EndpointWords _
      rw [rep.endpoints]
      have hh := gm06RetagEdges_endpoints rep.tagged mask
      have hh' := congrArg (List.map (fun p : Fin x.vertexCount × Fin x.vertexCount => (p.1.val, p.2.val))) hh
      simpa only [List.map_map, Function.comp_def, updated] using (congrArg gm06EndpointWords hh').symm
    live := A
    vertex := rep.vertex
    vertex_mem := fun a ha => ((hA a).mp ha).2
    vertex_inj := fun a ha b hb he => rep.vertex_inj ((hA a).mp ha).1 ((hA b).mp hb).1 he
    vertex_cover := fun v hv => by
      obtain ⟨a, ha, hav⟩ := rep.vertex_cover v (hHG.1 hv)
      exact ⟨a, (hA a).mpr ⟨ha, hav.symm ▸ hv⟩, hav⟩
    edge := edge'
    edge_inj := fun j hj l hl he => by
      have hh := rep.edge_inj (hactive j hj).1 (hactive l hl).1 he
      exact Fin.ext (congrArg (fun z : Fin rep.tagged.length => z.val) hh)
    edge_cover := fun e he => by
      obtain ⟨j, hj, hje⟩ := rep.edge_cover e (hHG.2 he)
      let j' : Fin updated.length := Fin.cast (gm06RetagEdges_length rep.tagged mask).symm j
      refine ⟨j', ?_, ?_⟩
      · rw [htag j']
        exact (hmask j).mpr ⟨hj, hje.symm ▸ he⟩
      · simpa only [edge', old, j', Fin.cast_cast, Fin.cast_eq_self] using hje
    links := hlinks
    ends_live := fun j hj => by
      have hold := rep.ends_live (old j) (hactive j hj).1
      constructor
      · apply (hA _).mpr
        have heq := congrArg (fun p : (Fin x.vertexCount × Fin x.vertexCount) × ℕ => p.1.1) (htag j)
        exact ⟨heq.symm ▸ hold.1, (hlinks j hj).left_mem⟩
      · apply (hA _).mpr
        have heq := congrArg (fun p : (Fin x.vertexCount × Fin x.vertexCount) × ℕ => p.1.2) (htag j)
        exact ⟨heq.symm ▸ hold.2, (hlinks j hj).right_mem⟩
    source := rep.source
    target := rep.target
    inner := rep.inner
    outer := rep.outer
    source_live := fun j => (hA _).mpr ⟨rep.source_live j, hsourceV j⟩
    target_live := fun j => (hA _).mpr ⟨rep.target_live j, htargetV j⟩
    source_point := rep.source_point
    target_point := rep.target_point
    linkage := hpathRows
    cuffed := F'
    subdrawing := hHF'
    cuffed_U := hF'U
    cuffed_V := hF'V
    label := label'
    par := rep.par
    edgePar := hγ'
    ordinary_labels := fun j hj => by
      obtain ⟨f, hf, hfl⟩ := rep.ordinary_labels (old j) (hactive j hj).1
      have hmem : f.val ∈ (cylinderSphereDrawing F').E := by
        rw [hf, cylinderSphereDrawing_E]
        exact mem_image_of_mem (image cylinderToSphere) (hHF'.2 (hactive j hj).2)
      exact ⟨⟨f.val, hmem⟩, hf, hfl⟩
    inner_labels := fun j => by
      obtain ⟨f, hf, hfl⟩ := rep.inner_labels j
      have hmem : f.val ∈ (cylinderSphereDrawing F').E := by
        rw [hf, cylinderSphereDrawing_E]
        apply mem_image_of_mem (image cylinderToSphere)
        rw [alg511_cuff_edges_eq hH hHF' hF'U hF'V]
        exact Or.inr (Or.inl ⟨j, rfl⟩)
      refine ⟨⟨f.val, hmem⟩, hf, hfl.trans ?_⟩
      exact congrArg (fun n : ℕ => n + j.val) (gm06RetagEdges_length rep.tagged mask).symm
    outer_labels := fun j => by
      obtain ⟨f, hf, hfl⟩ := rep.outer_labels j
      have hmem : f.val ∈ (cylinderSphereDrawing F').E := by
        rw [hf, cylinderSphereDrawing_E]
        apply mem_image_of_mem (image cylinderToSphere)
        rw [alg511_cuff_edges_eq hH hHF' hF'U hF'V]
        exact Or.inr (Or.inr ⟨j, rfl⟩)
      refine ⟨⟨f.val, hmem⟩, hf, hfl.trans ?_⟩
      exact congrArg (fun n : ℕ => n + k + j.val) (gm06RetagEdges_length rep.tagged mask).symm
    ordinary_ends := fun j hj => by
      have hh := rep.ordinary_ends (old j) (hactive j hj).1
      constructor
      · have heq := congrArg (fun p : (Fin x.vertexCount × Fin x.vertexCount) × ℕ => p.1.1) (htag j)
        exact hh.1.trans (congrArg (fun a => cylinderToSphere (rep.vertex a)) heq.symm)
      · have heq := congrArg (fun p : (Fin x.vertexCount × Fin x.vertexCount) × ℕ => p.1.2) (htag j)
        exact hh.2.trans (congrArg (fun a => cylinderToSphere (rep.vertex a)) heq.symm)
    inner_par := rep.inner_par
    outer_par := rep.outer_par
    rows_length := by
      change (gm06PrunedRotationRows _ x.rotations).length = _
      simp only [gm06PrunedRotationRows, List.length_map]
      exact rep.rows_length
    rows := fun j hj => by
      change GM06PersistentRotationRowRep label' rep.par (cylinderToSphere (rep.vertex j))
        ((gm06PrunedRotationRows (gm06AugmentedActivity mask x.innerCuff.length) x.rotations).getD j.val [])
      rw [hnewRow j]
      exact hrow j ((hA j).mp hj).1
    retired_rows := fun j hj => by
      change (gm06PrunedRotationRows (gm06AugmentedActivity mask x.innerCuff.length) x.rotations).getD j.val [] = []
      rw [hnewRow j]
      exact hretired j hj }
  refine ⟨cur, rfl, rfl, rfl, ?_⟩
  exact .subdrawing hHG rep.tagged rep.vertex rep.edge mask hlen rep.links
    (fun j hj => by
      have hjbound : j.val < mask.length := by rw [hlen]; exact j.isLt
      rw [List.getElem?_eq_getElem hjbound, Option.getD_some] at hj
      exact ((hmask j).mp hj).1)

end GraphMinor.GM06
