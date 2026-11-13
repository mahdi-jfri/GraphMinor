module

public import GraphMinor.GM06.Alg57ContractedRotationRows
public import GraphMinor.Compute.GM06ApplyReduction3Drawing
import GraphMinor.GM06.Section5ContractedCuffs
import GraphMinor.GM06.Section5CollapseChartFibers
import GraphMinor.GM06.Section5ContractedCuffLabels
import GraphMinor.GM11.Walks

/-!
# The current drawing relation after Reduction 3

For Lemmas 8 and 9 of VI (5.7), page 133, use one selected
rectangular collapse for the finite graph, shortened linkage,
positive rotation table, fixed cuffs and inverse record. Extend
that same homotopy over the caps and inherit the permanent labels
and parametrizations of all surviving edges. This constructs the
complete new current drawing relation for the literal finite update.
-/

public section
namespace GraphMinor.GM06
open Set Topology GraphMinor.Surface GraphMinor.GM11 GraphMinor.Compute unitInterval

/-- The six input fields written by the selected contraction. The
cuff rows and original slot counts retain their literal values. -/
@[expose] def gm06ContractSuccessorInput (x : GM06SuccessorInput)
    (a b i first : ℕ) (rest : List ℕ) : GM06SuccessorInput :=
  { x with
    endpoints := x.endpoints.map (fun v => if v = b then a else v)
    rotations := gm06ContractRotationRows x.rotations a b first (gm06DartMate first)
    linkage := x.linkage.set i rest }

/-- The actual selected contraction realizes the entire computed
current input, with the same fixed cuff labels and an actual inverse
record. The new vertex map remains injective on all original slots,
so the same finite update theorem can be used at the next iteration. -/
theorem GM06CurrentDrawingRep.exists_contracted_currentDrawingRep
    {k : ℕ} {x : GM06SuccessorInput} {G : Drawing ClosedCylinder}
    {L : CylinderLinkage k G} (rep : GM06CurrentDrawingRep x G L)
    (hvinj : Function.Injective rep.vertex) (hG : IsCylinderSection5Drawing k G)
    (i : Fin k) (b : Fin x.vertexCount) (first : ℕ) (rest : List ℕ)
    (hrow : x.linkage[i.val]'(by rw [rep.linkage.1]; exact i.isLt) = first :: rest)
    (hfirst : first < 2 * rep.tagged.length)
    (hval : vertexValency G.toGraph (cylinderM1Point k i) = 1)
    (hl : G.toGraph.IsLink (rep.edge ⟨first / 2, by omega⟩)
      (cylinderM1Point k i) (rep.vertex b))
    (hvs : rep.vertex b ≠ cylinderM1Point k i) (hoff : rep.vertex b ∉ cylinderCuff2) :
    ∃ (G' : Drawing ClosedCylinder) (M : CylinderLinkage k G')
      (cur : GM06CurrentDrawingRep
        (gm06ContractSuccessorInput x (rep.source i).val b.val i.val first rest) G' M),
      IsCylinderSection5Drawing k G' ∧ Section5Reduction3Step k G L G' M ∧
      Function.Injective cur.vertex ∧ cur.live = rep.live.erase b ∧
      cur.tagged = gm06ContractTaggedEdges rep.tagged (rep.source i) b (first / 2) ∧
      GM06UndoStep x.vertexCount k ⟨G, rep.tagged, rep.vertex, rep.edge⟩
        ⟨G', cur.tagged, cur.vertex, cur.edge⟩ (some (i.val, first)) := by
  classical
  let vertex : Fin x.vertexCount ↪ ClosedCylinder := ⟨rep.vertex, hvinj⟩
  let d : Fin rep.tagged.length := ⟨first / 2, by omega⟩
  obtain ⟨W, _, henc, hPW⟩ := rep.linkage.path i
  rw [hrow] at henc
  obtain ⟨_, hactive⟩ := henc.active_words first (by simp)
  have hpath : rep.edge d ∈ (L.pathDrawing i).E := by
    rw [← hPW, walkDrawing_E]
    exact (henc.edge_mem_iff _).mpr ⟨first, by simp, hfirst, rfl⟩
  have hb : b ∈ rep.live := by
    obtain ⟨j, hj, hjeq⟩ := rep.vertex_cover _ hl.right_mem
    exact hvinj hjeq ▸ hj
  have hvbd := L.initial_neighbour_not_mem_boundary hG i hpath hl hvs hoff
  obtain ⟨πC, G', M, vertex', hdata, H, D, E, hD, hchart, hout, horigin, hsegment,
      hH0, hH1, hHbd, ηR, hηR, hηRinv, hηRcl⟩ :=
    exists_selected_rectangular_contraction_representation L hG i rep.tagged vertex rep.edge rep.live
      rep.edge_inj rep.links rep.edge_cover rep.vertex_mem rep.vertex_cover
      (rep.source i) b (rep.source_point i) d hactive hval hl hvs hoff
      x.linkage rep.linkage first rest hrow rfl
  dsimp only at hdata
  obtain ⟨hG', hred, hfibreC, hinjC, hUC, hVC, hEC, hnew, hnewV, hsource, hEinj,
    hlinks, hcover, hpaths, hcuffs, hundo⟩ := hdata
  let updated := gm06ContractTaggedEdges rep.tagged (rep.source i) b d.val
  let edge' : Fin updated.length → Set ClosedCylinder := fun j =>
    πC '' rep.edge (Fin.cast (gm06ContractTaggedEdges_length rep.tagged (rep.source i) b d.val) j)
  let old : Fin updated.length → Fin rep.tagged.length :=
    Fin.cast (gm06ContractTaggedEdges_length rep.tagged (rep.source i) b d.val)
  have hbd : ∀ y ∈ bd ClosedCylinder, πC y = y := fun y hy =>
    (hH1 y).symm.trans (hHbd y hy 1)
  have hsurjC : Function.Surjective πC := by
    intro y
    obtain ⟨z, hz⟩ := surjective_of_rectangle_homotopy_in_chart E H hchart hout 1 y
    exact ⟨z, (hH1 z).symm.trans hz⟩
  obtain ⟨F', hGF', hFU', hFV', hFUimage, hFVimage, _⟩ :=
    exists_cuff_augmentation_of_closed_edge_collapse hG' rep.subdrawing rep.cuffed_U rep.cuffed_V
      hl hvs πC hfibreC hinjC hbd hUC hVC
  obtain ⟨π, K, hcomm, hπoff, hK0, hK1, hK, hKout, _⟩ :=
    exists_capped_cylinder_collapse πC H hH0 hH1 hHbd hout
  have hKoff : ∀ y ∉ range cylinderToSphere, ∀ t, K (t, y) = y := by
    intro y hy t
    exact hKout y (fun ⟨z, _, hzy⟩ => hy ⟨z, hzy⟩) t
  have hfixed : ∀ y ∈ cylinderToSphere '' bd ClosedCylinder, π y = y := by
    rintro y ⟨z, hz, rfl⟩
    rw [hcomm, hbd z hz]
  have hlF := (rep.subdrawing.isLink_iff hl.edge_mem).mp hl
  obtain ⟨hfibre, hinj, hsurj, hU, hV, hE, _, _, _, _⟩ :=
    cylinderSphereDrawing_closed_edge_collapse hlF hvs πC hfibreC hinjC hsurjC
      hFUimage hFVimage π hcomm hπoff
  obtain ⟨label', γ', hγ', hlabel, hpar, hinner, houter, hI, hO⟩ :=
    rep.exists_contracted_cuff_data hG hl hvs π hinj hfixed hV hE
  have hsegS : closure (cylinderToSphere '' rep.edge d) = cylinderToSphere ''
      ((fun z => (E z).val) '' {z | z.1.1 = 0 ∧ z.2.1 ≤ 1}) := by
    rw [isClosedEmbedding_cylinderToSphere.closure_image_eq, hsegment]
  have hrows := rep.contracted_rotation_rows hG hG'.2.1 i b hb first rest hrow hfirst hval hl hvs hvbd
    vertex' πC hnew hsource hEC π hcomm hfibre hinj hsurj hfixed hU hV hE hγ' hpar label' hlabel
    E H K hchart hout hK hKoff hK0 hK1 hsegS
  have hupdated (j : Fin updated.length) : updated[j] =
      ((gm06ContractVertexLabel (rep.source i) b rep.tagged[old j].1.1,
        gm06ContractVertexLabel (rep.source i) b rep.tagged[old j].1.2),
        if j.val = d.val then 0 else rep.tagged[old j].2) :=
    gm06ContractTaggedEdges_getElem rep.tagged (rep.source i) b d.val (old j).isLt
  have hactiveOld (j : Fin updated.length) (hj : updated[j].2 = 1) :
      rep.tagged[old j].2 = 1 ∧ j.val ≠ d.val := by
    rw [hupdated] at hj
    by_cases hje : j.val = d.val
    · simp only [hje, ite_true] at hj
      exact False.elim (Nat.zero_ne_one hj)
    · exact ⟨by simpa only [hje, ite_false] using hj, hje⟩
  have hretained (j : Fin updated.length) (hj : updated[j].2 = 1) : rep.edge (old j) ≠ rep.edge d := by
    intro heq
    have hidx := rep.edge_inj (hactiveOld j hj).1 hactive heq
    exact (hactiveOld j hj).2 (congrArg Fin.val hidx)
  have hOldMem (j : Fin updated.length) (hj : updated[j].2 = 1) :
      cylinderToSphere '' rep.edge (old j) ∈ (cylinderSphereDrawing rep.cuffed).E := by
    obtain ⟨f, hf, _⟩ := rep.ordinary_labels (old j) (hactiveOld j hj).1
    exact hf ▸ f.property
  have hRetainedS (j : Fin updated.length) (hj : updated[j].2 = 1) :
      cylinderToSphere '' rep.edge (old j) ≠ cylinderToSphere '' rep.edge d :=
    fun hh => hretained j hj ((Set.image_injective.mpr injective_cylinderToSphere) hh)
  have hImage (j : Fin updated.length) : cylinderToSphere '' edge' j = π '' (cylinderToSphere '' rep.edge (old j)) := by
    change cylinderToSphere '' (πC '' rep.edge (old j)) = _
    rw [image_image, image_image]
    exact image_congr (fun y _ => (hcomm y).symm)
  have hparOrd (j : Fin updated.length) (hj : updated[j].2 = 1) (t : I) :
      γ' (cylinderToSphere '' edge' j) t = π (rep.par (cylinderToSphere '' rep.edge (old j)) t) := by
    rw [hImage, hpar _ (hOldMem j hj) (hRetainedS j hj)]
  have hsourceBd (j : Fin k) : rep.vertex (rep.source j) ∈ bd ClosedCylinder := by
    rw [rep.source_point, bd_closedCylinder]
    exact Or.inl rfl
  have htargetBd (j : Fin k) : rep.vertex (rep.target j) ∈ bd ClosedCylinder := by
    rw [rep.target_point, bd_closedCylinder]
    exact Or.inr rfl
  have hsourceLive (j : Fin k) := (hcuffs _ (rep.source_live j) (hsourceBd j)).1
  have htargetLive (j : Fin k) := (hcuffs _ (rep.target_live j) (htargetBd j)).1
  have hnewPoint (c : Fin x.vertexCount) (hc : c ∈ rep.live) :
      vertex' (gm06ContractVertexLabel (rep.source i) b c) = πC (rep.vertex c) := by
    change vertex' (gm06ContractVertexLabel (rep.source i) b c) = πC (vertex c)
    by_cases hcb : c = b
    · subst c
      have hbcl : rep.vertex b ∈ closure (rep.edge d) :=
        (hl.2.2.2.symm ▸ mem_insert_of_mem _ (mem_singleton _)).1
      have hπb : πC (rep.vertex b) = cylinderM1Point k i :=
        show rep.vertex b ∈ πC ⁻¹' {cylinderM1Point k i} from hfibreC.symm ▸ hbcl
      simp only [gm06ContractVertexLabel, ite_true]
      exact hsource.trans hπb.symm
    · have hcerase : c ∈ rep.live.erase b := Finset.mem_erase.mpr ⟨hcb, hc⟩
      simpa only [gm06ContractVertexLabel, hcb, ite_false] using hnew c hcerase
  let x' := gm06ContractSuccessorInput x (rep.source i).val b.val i.val first rest
  let cur : GM06CurrentDrawingRep x' G' M := {
    tagged := updated
    endpoints := by
      change x.endpoints.map _ = _
      rw [rep.endpoints]
      exact (gm06ContractTaggedEdges_endpointWords rep.tagged (rep.source i) b d.val).symm
    live := rep.live.erase b
    vertex := vertex'
    vertex_mem := fun j hj => hnewV ▸ mem_image_of_mem vertex' hj
    vertex_inj := fun _ _ _ _ hh => vertex'.injective hh
    vertex_cover := fun y hy => by
      have hy' : y ∈ vertex' '' (rep.live.erase b : Set (Fin x.vertexCount)) := by
        rw [← hnewV]
        exact hy
      obtain ⟨a, ha, hay⟩ := hy'
      exact ⟨a, ha, hay⟩
    edge := edge'
    edge_inj := hEinj
    edge_cover := hcover
    links := hlinks
    ends_live := fun j hj => by
      constructor
      · have hleft : vertex' updated[j].1.1 ∈ G'.V := (hlinks j hj).left_mem
        rw [hnewV] at hleft
        obtain ⟨c, hc, heq⟩ := hleft
        exact vertex'.injective heq ▸ hc
      · have hright : vertex' updated[j].1.2 ∈ G'.V := (hlinks j hj).right_mem
        rw [hnewV] at hright
        obtain ⟨c, hc, heq⟩ := hright
        exact vertex'.injective heq ▸ hc
    source := rep.source
    target := rep.target
    inner := rep.inner
    outer := rep.outer
    source_live := hsourceLive
    target_live := htargetLive
    source_point := fun j => (hcuffs _ (rep.source_live j) (hsourceBd j)).2.trans (rep.source_point j)
    target_point := fun j => (hcuffs _ (rep.target_live j) (htargetBd j)).2.trans (rep.target_point j)
    linkage := hpaths
    cuffed := F'
    subdrawing := hGF'
    cuffed_U := hFU'
    cuffed_V := hFV'
    label := label'
    par := γ'
    edgePar := hγ'
    ordinary_labels := fun j hj => by
      let f' : (cylinderSphereDrawing F').E :=
        ⟨π '' (cylinderToSphere '' rep.edge (old j)), hE ▸ mem_image_of_mem (image π) ⟨hOldMem j hj, hRetainedS j hj⟩⟩
      obtain ⟨f, hf, hfl⟩ := rep.ordinary_labels (old j) (hactiveOld j hj).1
      refine ⟨f', (hImage j).symm, ?_⟩
      have hh := hlabel _ (hOldMem j hj) (hRetainedS j hj)
      have heq : (⟨cylinderToSphere '' rep.edge (old j), hOldMem j hj⟩ : (cylinderSphereDrawing rep.cuffed).E) = f :=
        Subtype.ext hf.symm
      exact hh.trans ((congrArg rep.label heq).trans hfl)
    inner_labels := fun j => by
      obtain ⟨f, hf, hfl⟩ := hinner j
      refine ⟨f, hf, hfl.trans ?_⟩
      exact congrArg (fun n : ℕ => n + j.val) (gm06ContractTaggedEdges_length rep.tagged (rep.source i) b d.val).symm
    outer_labels := fun j => by
      obtain ⟨f, hf, hfl⟩ := houter j
      refine ⟨f, hf, hfl.trans ?_⟩
      exact congrArg (fun n : ℕ => n + k + j.val) (gm06ContractTaggedEdges_length rep.tagged (rep.source i) b d.val).symm
    ordinary_ends := fun j hj => by
      have hends := rep.ordinary_ends (old j) (hactiveOld j hj).1
      have hlive := rep.ends_live (old j) (hactiveOld j hj).1
      constructor
      · rw [hparOrd j hj 0, hends.1, hcomm]
        have heq := congrArg (fun p : (Fin x.vertexCount × Fin x.vertexCount) × ℕ => p.1.1) (hupdated j)
        exact congrArg cylinderToSphere ((hnewPoint _ hlive.1).symm.trans (congrArg vertex' heq.symm))
      · rw [hparOrd j hj 1, hends.2, hcomm]
        have heq := congrArg (fun p : (Fin x.vertexCount × Fin x.vertexCount) × ℕ => p.1.2) (hupdated j)
        exact congrArg cylinderToSphere ((hnewPoint _ hlive.2).symm.trans (congrArg vertex' heq.symm))
    inner_par := hI
    outer_par := hO
    rows_length := by
      change (gm06ContractRotationRows _ _ _ _ _).length = _
      rw [gm06ContractRotationRows_length, rep.rows_length]
      rfl
    rows := hrows.1
    retired_rows := hrows.2 }
  exact ⟨G', M, cur, hG', hred, vertex'.injective, rfl, rfl, hundo⟩

end GraphMinor.GM06
