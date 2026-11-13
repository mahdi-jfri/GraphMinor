module

public import GraphMinor.GM13.Section7RealizePic
public import GraphMinor.GM16.EmbeddedLineGraphDrawing
public import GraphMinor.GM14.CylinderParts

/-!
# Graph Minors XIII, (7.3): the new wall is drawn as in Fig. 1

A cell wall `C` of height `h` is *a homeomorphic image of Fig. 1* (`CellWall.IsFig1Homeo`) if a
homeomorphism of the plane maps each cell `m` of the wall of Fig. 1 onto the cells `C.cells m`.
The wall of Fig. 1 itself is one (`CellWall.isFig1Homeo_fig1`), and a step whose rays leave the
kept cells and whose old vertices keep the order of the rows keeps this property
(`CellWall.IsFig1Homeo.transform`): we compose the homeomorphism of the step
(`Shape.Realization.exists_homeo`) with that of `C`.

If a wall `W` is drawn by `Γ` on the cells of such a cell wall, then the drawing of `W` induced by
`Γ` is the image of a drawing of `W` as in Fig. 1 under a homeomorphism of the plane
(`exists_fig1_of_drawnOnCells`). We pull the vertices and the closed edges of `W` back by the
homeomorphism and build a drawing from these lines (`exists_graphDrawing_of_embedded_lines`).
Its branch vertices are at their points and the closed edges of the path of each edge `pq` cover
the segment from `p` to `q`, since this holds for the cells.
-/

@[expose] public section

namespace GraphMinor.GM13

open Set Function Graph GraphMinor GraphMinor.Surface GraphMinor.GM09
open GraphMinor.GM16 (latticePoint)

universe u v

namespace CellWall

variable {h : ℕ}

/-- **A cell wall that is a homeomorphic image of the wall of Fig. 1**: a homeomorphism of the
plane maps each cell `m` of the wall of Fig. 1 onto the cells of `m` in `C`. -/
def IsFig1Homeo (C : CellWall h) : Prop :=
  ∃ ψ : (ℝ × ℝ) ≃ₜ (ℝ × ℝ), ∀ m ∈ fig1WallCells h, ψ '' cellSet {m} = cellSet (C.cells m)

theorem isFig1Homeo_fig1 (hh : 1 ≤ h) (he : Even h) : (fig1 hh he).IsFig1Homeo :=
  ⟨Homeomorph.refl _, fun m _ => by simp [fig1]⟩

theorem cellSet_eq_iUnion (S : Set (ℤ × ℤ)) : cellSet S = ⋃ m ∈ S, cellSet {m} := by
  ext z
  simp [cellSet]

/-- **A good step keeps the cell wall a homeomorphic image of Fig. 1.** The step maps the cell
`m'` of the new wall of Fig. 1 onto the old cells `m` that go to `m'`, and `C` maps these onto
their cells in `C`, whose union is the set of cells of `m'` in the new cell wall. -/
theorem IsFig1Homeo.transform {C : CellWall h} (hC : C.IsFig1Homeo) {h' : ℕ} {τ : Shape h h'}
    (R : τ.Realization) (hh : 2 ≤ h) (he : Even h) (hh' : 1 ≤ h') (he' : Even h')
    (hray : R.RayOK) (hmono : R.RowMono) : (C.transform τ hh' he').IsFig1Homeo := by
  obtain ⟨ψC, hψC⟩ := hC
  have hh2 : 2 ≤ h' := by obtain ⟨k, hk⟩ := he'; omega
  obtain ⟨ψs, hψs⟩ := R.exists_homeo hh he hh2 he' hray hmono
  refine ⟨ψs.trans ψC, fun m' hm' => ?_⟩
  rw [show ((ψs.trans ψC) : ℝ × ℝ → ℝ × ℝ) = ψC ∘ ψs from rfl, image_comp, hψs m' hm',
    cellSet_eq_iUnion, image_iUnion₂]
  change _ = cellSet (C.tCells τ m')
  ext z
  rw [mem_iUnion₂]
  constructor
  · rintro ⟨m, ⟨hm, hown⟩, hz⟩
    rw [hψC m hm] at hz
    exact (C.mem_tCells τ).mpr ⟨m, hm, hown, hz⟩
  · intro hz
    obtain ⟨m, hm, hown, hz⟩ := (C.mem_tCells τ).mp hz
    exact ⟨m, ⟨hm, hown⟩, by rw [hψC m hm]; exact hz⟩

end CellWall

variable {α : Type u} {β : Type v}

/-- The edge set of a wall that is part of a drawn graph is finite, and so is its vertex set:
they are part of those of the drawing. -/
theorem GraphDrawing.finite_V {G : Graph α β} (Γ : GraphDrawing G EuclideanPlane) :
    V(G).Finite := by
  have : Finite V(Γ.drawing.toGraph) :=
    (show V(Γ.drawing.toGraph).Finite from Γ.drawing.finite_V).to_subtype
  exact Set.finite_coe_iff.mp (Finite.of_equiv _ Γ.iso.vertexEquiv.symm)

theorem GraphDrawing.finite_E {G : Graph α β} (Γ : GraphDrawing G EuclideanPlane) :
    E(G).Finite := by
  have : Finite E(Γ.drawing.toGraph) :=
    (show E(Γ.drawing.toGraph).Finite from Γ.drawing.finite_edges).to_subtype
  exact Set.finite_coe_iff.mp (Finite.of_equiv _ Γ.iso.edgeEquiv.symm)

/-- A wall has no loops: each of its edges lies on the path of an edge of the elementary wall. -/
theorem Wall.no_loop (W : Wall α β) (e : β) (v : α) : ¬ W.graph.IsLink e v v := by
  intro hl
  obtain ⟨m, -, hm⟩ := W.exists_mem_elemE hl.edge_mem
  obtain ⟨p, q, hadj, -, hf⟩ := hm
  have hP := W.isGraphPathWithEnds_baseEdge hadj
  exact GM14.IsGraphPathWithEnds.no_loop hP ((hP.1.isLink_iff hf).mpr hl)

/-- **A wall drawn on the cells of a homeomorphic image of Fig. 1 is drawn as in Fig. 1, up to
a homeomorphism.** Let `W` be a wall that is part of a graph drawn by `Γ`, drawn on the cells of
a cell wall `C` that is a homeomorphic image of Fig. 1. Then the drawing of `W` induced by `Γ` is
the image under a homeomorphism `Ψ` of the plane of a drawing `Γ'` of `W` as in Fig. 1, with each
vertex `u` of `W` at `Ψ` of its point in `Γ'`. -/
theorem exists_fig1_of_drawnOnCells {G : Graph α β} {Γ : GraphDrawing G EuclideanPlane}
    {W : Wall α β} (hWG : W.graph ≤ G) {C : CellWall W.height} (hD : DrawnOnCells Γ W C)
    (hC : C.IsFig1Homeo) :
    ∃ (Ψ : EuclideanPlane ≃ₜ EuclideanPlane) (Γ' : GraphDrawing W.graph EuclideanPlane),
      IsFigure1CoordDrawing W Γ' ∧ indU Γ W = Ψ '' Γ'.drawing.U ∧
      ∀ (u : α) (hu : u ∈ V(W.graph)), ptV Γ u = Ψ (Γ'.iso.vertexEquiv ⟨u, hu⟩).1 := by
  classical
  obtain ⟨ψ, hψ⟩ := hC
  let Ψ : EuclideanPlane ≃ₜ EuclideanPlane := fig1PlaneEquiv.symm.trans (ψ.trans fig1PlaneEquiv)
  -- the points of each element are the images under `Ψ` of its points in Fig. 1
  have hΨ : ∀ m ∈ fig1WallCells W.height,
      elemPts Γ W m = Ψ '' (fig1PlaneEquiv '' cellSet {m}) := by
    intro m hm
    rw [hD m hm, ← hψ m hm, image_image, image_image]
    simp [Ψ]
  have hVW : V(W.graph) ⊆ V(G) := hWG.vertexSet_mono
  have hinj : InjOn (ptV Γ) V(W.graph) := (ptV_injOn Γ).mono hVW
  -- the closure of an edge of `W` is the edge and its two ends
  have hcl : ∀ {f x y}, W.graph.IsLink f x y →
      closure (arcE Γ f) = arcE Γ f ∪ {ptV Γ x, ptV Γ y} := fun hl =>
    closure_arcE Γ (hl.mono hWG)
  have hLine : ∀ f ∈ E(W.graph), ∀ x y, W.graph.IsLink f x y →
      IsLineWithEnds (closure (arcE Γ f)) (ptV Γ x) (ptV Γ y) := by
    intro f hf x y hl
    have hl' := hl.mono hWG
    have hxy : x ≠ y := fun e => W.no_loop f x (e ▸ hl)
    have h1 := (Γ.iso.isLink_iff ⟨f, hl'.edge_mem⟩ ⟨x, hl'.left_mem⟩ ⟨y, hl'.right_mem⟩).mp hl'
    obtain ⟨he, -, -, hcap⟩ := h1
    rw [arcE_of_mem Γ hl'.edge_mem, ptV_of_mem Γ hl'.left_mem, ptV_of_mem Γ hl'.right_mem]
    refine GraphMinor.GM11.isLine_closure he ?_ hcap
    intro e
    exact hxy (congrArg Subtype.val (Γ.iso.vertexEquiv.injective (Subtype.ext e)))
  have hVert : ∀ f ∈ E(W.graph), ∀ v ∈ V(W.graph), ptV Γ v ∈ closure (arcE Γ f) →
      W.graph.Inc f v := by
    intro f hf v hv hz
    obtain ⟨x, y, hl⟩ := exists_isLink_of_mem_edgeSet hf
    rw [hcl hl] at hz
    rcases hz with hz | hz | hz
    · exact absurd hz (ptV_not_mem_arcE Γ (hVW hv) f)
    · rw [hinj hv hl.left_mem hz]
      exact ⟨y, hl⟩
    · rw [hinj hv hl.right_mem (mem_singleton_iff.mp hz)]
      exact ⟨x, hl.symm⟩
  have hMeet : ∀ f ∈ E(W.graph), ∀ d ∈ E(W.graph), f ≠ d →
      closure (arcE Γ f) ∩ closure (arcE Γ d) ⊆ ptV Γ '' V(W.graph) := by
    intro f hf d hd hne z hz
    have hfG := hWG.edgeSet_mono hf
    have hdG := hWG.edgeSet_mono hd
    have hne' : arcE Γ f ≠ arcE Γ d := by
      rw [arcE_of_mem Γ hfG, arcE_of_mem Γ hdG]
      intro e
      exact hne (congrArg Subtype.val (Γ.iso.edgeEquiv.injective (Subtype.ext e)))
    have hzV := GraphMinor.GM11.closure_inter_subset_V (arcE_mem_E Γ hfG) (arcE_mem_E Γ hdG)
      hne' hz
    obtain ⟨x, y, hl⟩ := exists_isLink_of_mem_edgeSet hf
    have hz1 := hz.1
    rw [hcl hl] at hz1
    rcases hz1 with hz1 | rfl | hz1
    · rw [arcE_of_mem Γ hfG] at hz1
      have h2 : z ∈ closure (Γ.iso.edgeEquiv ⟨f, hfG⟩).1 \ Γ.drawing.V := by
        rw [Γ.drawing.closure_diff_V (Γ.iso.edgeEquiv ⟨f, hfG⟩).2]
        exact hz1
      exact absurd hzV h2.2
    · exact ⟨x, hl.left_mem, rfl⟩
    · rw [mem_singleton_iff.mp hz1]
      exact ⟨y, hl.right_mem, rfl⟩
  obtain ⟨Γ', -, hv', he'⟩ := GraphMinor.GM16.exists_graphDrawing_of_embedded_lines W.graph
    ((GraphDrawing.finite_V Γ).subset hVW) ((GraphDrawing.finite_E Γ).subset hWG.edgeSet_mono)
    (ptV Γ) hinj (fun f => closure (arcE Γ f)) (fun e v hl => W.no_loop e v hl) hLine hVert
    hMeet Ψ.symm Ψ.symm.isEmbedding
  have hv'' : ∀ (u : α) (hu : u ∈ V(W.graph)), ptV Γ u = Ψ (Γ'.iso.vertexEquiv ⟨u, hu⟩).1 :=
    fun u hu => by rw [hv' ⟨u, hu⟩]; simp
  refine ⟨Ψ, Γ', ⟨fun p hp hW => ?_, fun p q hpq => ?_⟩, ?_, hv''⟩
  · -- the branch vertex of `p` is at the point `p`
    apply Ψ.injective
    rw [← hv'' _ hW]
    have hmem : ptV Γ (W.branchVertex p hp) ∈ elemPts Γ W (vCell p) :=
      Or.inl ⟨_, W.branchVertex_mem_elemV hp, rfl⟩
    rw [hΨ _ (mem_fig1WallCells_vCell W.two_le_height W.even_height hp), cellSet_vCell,
      image_singleton, image_singleton] at hmem
    exact hmem
  · -- the closed edges of the path of `pq` cover the segment from `p` to `q`
    set P := W.subdivisionPaths (W.baseEdge hpq) with hPdef
    have hP := W.isGraphPathWithEnds_baseEdge hpq
    have hPG : IsGraphPathWithEnds G P _ _ := ⟨hP.1.trans hWG, hP.2⟩
    have hunion := iUnion_closure_arcE Γ hPG (W.subdivisionPaths_nonempty hpq)
    have hPV : V(P) ⊆ V(W.graph) := hP.1.vertexSet_mono
    have ha := W.branchVertex_mem_graph p hpq.1
    have hb := W.branchVertex_mem_graph q hpq.2.1
    have hinter := W.vertexSet_baseEdge_inter hpq
    -- the points of the path: the element of `pq` and the two ends
    have hpts : ptV Γ '' V(P) ∪ ⋃ f ∈ E(P), arcE Γ f =
        elemPts Γ W (eCell p q) ∪ {ptV Γ (W.branchVertex p hpq.1),
          ptV Γ (W.branchVertex q hpq.2.1)} := by
      have haP : W.branchVertex p hpq.1 ∈ V(P) := hP.left_mem
      have hbP : W.branchVertex q hpq.2.1 ∈ V(P) := hP.right_mem
      ext z
      simp only [elemPts, mem_union, mem_image, mem_iUnion, exists_prop, mem_insert_iff,
        mem_singleton_iff, W.mem_elemV_eCell hpq, W.mem_elemE_eCell hpq]
      constructor
      · rintro (⟨x, hx, rfl⟩ | ⟨f, hf, hz⟩)
        · by_cases hxB : x ∈ V(W.baseGraph)
          · have : x ∈ V(P) ∩ V(W.baseGraph) := ⟨hx, hxB⟩
            rw [hinter] at this
            rcases this with rfl | rfl
            · exact Or.inr (Or.inl rfl)
            · exact Or.inr (Or.inr rfl)
          · exact Or.inl (Or.inl ⟨x, ⟨hx, hxB⟩, rfl⟩)
        · exact Or.inl (Or.inr ⟨f, hf, hz⟩)
      · rintro ((⟨x, ⟨hx, -⟩, rfl⟩ | ⟨f, hf, hz⟩) | rfl | rfl)
        · exact Or.inl ⟨x, hx, rfl⟩
        · exact Or.inr ⟨f, hf, hz⟩
        · exact Or.inl ⟨_, haP, rfl⟩
        · exact Or.inl ⟨_, hbP, rfl⟩
    have hends : ∀ (r : ℕ × ℕ) (hr : r ∈ elementaryWallVerts W.height),
        ptV Γ (W.branchVertex r hr) = Ψ (fig1PlaneEquiv (latticePoint r)) := by
      intro r hr
      have hmem : ptV Γ (W.branchVertex r hr) ∈ elemPts Γ W (vCell r) :=
        Or.inl ⟨_, W.branchVertex_mem_elemV hr, rfl⟩
      rw [hΨ _ (mem_fig1WallCells_vCell W.two_le_height W.even_height hr), cellSet_vCell,
        image_singleton, image_singleton] at hmem
      exact hmem
    have hseg : ⋃ f ∈ E(P), closure (arcE Γ f) = Ψ '' (fig1PlaneEquiv '' fig1Segment p q) := by
      rw [hunion, hpts, hΨ _ (mem_fig1WallCells_eCell W.two_le_height W.even_height hpq),
        hends p hpq.1, hends q hpq.2.1, fig1Segment_eq_cellSet, fig1SegmentCells_eq hpq,
        ← cellSet_segment_diff hpq]
      have hsub : cellSet {vCell p, eCell p q, vCell q} =
          (cellSet {vCell p, eCell p q, vCell q} \ {latticePoint p, latticePoint q}) ∪
            {latticePoint p, latticePoint q} := by
        have hp' : latticePoint p ∈ cellSet ({vCell p, eCell p q, vCell q} : Set (ℤ × ℤ)) := by
          change cellCode (latticePoint p) ∈ ({vCell p, eCell p q, vCell q} : Set (ℤ × ℤ))
          rw [(cellCode_eq_vCell_iff).mpr rfl]
          exact Or.inl rfl
        have hq' : latticePoint q ∈ cellSet ({vCell p, eCell p q, vCell q} : Set (ℤ × ℤ)) := by
          change cellCode (latticePoint q) ∈ ({vCell p, eCell p q, vCell q} : Set (ℤ × ℤ))
          rw [(cellCode_eq_vCell_iff).mpr rfl]
          exact Or.inr (Or.inr rfl)
        rw [sdiff_union_self, union_eq_left.mpr (insert_subset hp' (singleton_subset_iff.mpr hq'))]
      conv_rhs => rw [hsub, image_union, image_union, image_insert_eq, image_singleton,
        image_insert_eq, image_singleton]
    calc ⋃ (f : E(W.graph)) (_ : f.1 ∈ E(P)), closure (Γ'.iso.edgeEquiv f).1
        = ⋃ f ∈ E(P), Ψ.symm '' closure (arcE Γ f) := by
          ext z
          simp only [mem_iUnion, exists_prop]
          constructor
          · rintro ⟨f, hf, hz⟩
            rw [he' f] at hz
            exact ⟨f.1, hf, hz⟩
          · rintro ⟨f, hf, hz⟩
            refine ⟨⟨f, hP.1.edgeSet_mono hf⟩, hf, ?_⟩
            rw [he']
            exact hz
      _ = Ψ.symm '' (Ψ '' (fig1PlaneEquiv '' fig1Segment p q)) := by
          rw [← hseg, image_iUnion₂]
      _ = fig1PlaneEquiv '' fig1Segment p q := by
          rw [image_image]
          simp
  · -- the drawing of `W` induced by `Γ` is the image of `Γ'`
    rw [GraphMinor.Surface.Drawing.U_eq, image_union, image_iUnion₂]
    ext z
    simp only [indU, mem_union, mem_image, mem_iUnion, exists_prop]
    constructor
    · rintro (⟨x, hx, rfl⟩ | ⟨f, hf, hz⟩)
      · refine Or.inl ⟨(Γ'.iso.vertexEquiv ⟨x, hx⟩).1, (Γ'.iso.vertexEquiv ⟨x, hx⟩).2, ?_⟩
        rw [hv'' x hx]
      · refine Or.inr ⟨(Γ'.iso.edgeEquiv ⟨f, hf⟩).1, (Γ'.iso.edgeEquiv ⟨f, hf⟩).2, ?_⟩
        rw [he']
        exact ⟨Ψ.symm z, mem_image_of_mem _ (subset_closure hz), by simp⟩
    · rintro (⟨y, hy, rfl⟩ | ⟨e, he, w, hw, rfl⟩)
      · obtain ⟨x, hx⟩ := Γ'.iso.vertexEquiv.surjective ⟨y, hy⟩
        have hy' : y = (Γ'.iso.vertexEquiv x).1 := by rw [hx]
        subst hy'
        left
        exact ⟨x.1, x.2, hv'' x.1 x.2⟩
      · obtain ⟨f, hf⟩ := Γ'.iso.edgeEquiv.surjective ⟨e, he⟩
        have he2 : e = (Γ'.iso.edgeEquiv f).1 := by rw [hf]
        subst he2
        change w ∈ closure (Γ'.iso.edgeEquiv f).1 at hw
        rw [he'] at hw
        obtain ⟨w', hw', rfl⟩ := hw
        simp only [Homeomorph.apply_symm_apply]
        obtain ⟨x, y, hl⟩ := exists_isLink_of_mem_edgeSet f.2
        rw [hcl hl] at hw'
        rcases hw' with hw' | rfl | hw'
        · exact Or.inr ⟨f.1, f.2, hw'⟩
        · exact Or.inl ⟨x, hl.left_mem, rfl⟩
        · exact Or.inl ⟨y, hl.right_mem, (mem_singleton_iff.mp hw').symm⟩

end GraphMinor.GM13
