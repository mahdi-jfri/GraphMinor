module

public import GraphMinor.GM06.Alg57TargetBlockData
public import GraphMinor.GM06.Alg57SourceChartOrientation
import GraphMinor.GM06.Alg57CuffFace
import GraphMinor.GM06.Alg511CuffEnumeration
import GraphMinor.GM06.Alg57RowRotation

/-!
# The positive source splice for the selected rectangular collapse

This proves the source-rotation part of Lemma 8 of VI (5.7), page
133, for the actual current drawing and rectangular homotopy.
The old source has three ends. Its two cuff ends survive at their
fixed points, and the other ends of the interior neighbour become
the block between them. The old target row supplies each retained
end and its angular coordinate. The explicit radius quotient and
positive source chart prove the order of that block. The finite
splice therefore has its full positive geometric interpretation,
with the same permanent words, including the two ends of a loop.
-/

public section
namespace GraphMinor.GM06
open Set Metric Topology GraphMinor.Surface GraphMinor.GM11 GraphMinor.Compute unitInterval

/-- Lemma 8 of the implementation of Graph Minors VI (5.7), page
133: the computed source splice is the positive rotation of the
actual rectangular contraction. Its order is derived from the
quotient coordinates and the actual signed cuff curves. -/
theorem GM06CurrentDrawingRep.source_splice_of_rectangular_collapse
    {k : ℕ} {x : GM06SuccessorInput} {G G' : Drawing ClosedCylinder}
    {L : CylinderLinkage k G} (rep : GM06CurrentDrawingRep x G L)
    (hG : IsCylinderSection5Drawing k G) (hG' : G'.IsProper) (i : Fin k)
    {e : Set ClosedCylinder} {v : ClosedCylinder}
    (hval : vertexValency G.toGraph (cylinderM1Point k i) = 1)
    (hl : G.toGraph.IsLink e (cylinderM1Point k i) v)
    (hvs : v ≠ cylinderM1Point k i) (hvbd : v ∉ bd ClosedCylinder)
    (a₀ : halfEdges (cylinderSphereDrawing rep.cuffed) rep.par
      (cylinderToSphere (cylinderM1Point k i)))
    (a₁ : halfEdges (cylinderSphereDrawing rep.cuffed) rep.par (cylinderToSphere v))
    (ha₀ : a₀.val.1 = cylinderToSphere '' e) (ha₁ : a₁.val.1 = cylinderToSphere '' e)
    {ys : List ℕ} (hy : GM06PersistentRotationRowRep rep.label rep.par (cylinderToSphere v) ys)
    (πC : C(ClosedCylinder, ClosedCylinder))
    (hrawE : G'.E = (image πC) '' (G.E \ {e}))
    {Γ' : Drawing (OnePoint EuclideanPlane)}
    (π : C(OnePoint EuclideanPlane, OnePoint EuclideanPlane))
    (hcomm : ∀ y, π (cylinderToSphere y) = cylinderToSphere (πC y))
    (hfibre : π ⁻¹' {cylinderToSphere (cylinderM1Point k i)} = closure (cylinderToSphere '' e))
    (hinj : InjOn π (closure (cylinderToSphere '' e))ᶜ)
    (hfixed : ∀ y ∈ cylinderToSphere '' bd ClosedCylinder, π y = y)
    (hE : Γ'.E = (image π) '' ((cylinderSphereDrawing rep.cuffed).E \ {cylinderToSphere '' e}))
    {γ' : Set (OnePoint EuclideanPlane) → I → OnePoint EuclideanPlane}
    (hγ' : EdgePar Γ' γ')
    (hpar : ∀ f ∈ (cylinderSphereDrawing rep.cuffed).E, f ≠ cylinderToSphere '' e →
      ∀ t, γ' (π '' f) t = π (rep.par f t))
    (label' : Γ'.E ↪ ℕ)
    (hlabel : ∀ f (hf : f ∈ (cylinderSphereDrawing rep.cuffed).E) (hne : f ≠ cylinderToSphere '' e),
      label' ⟨π '' f, hE ▸ mem_image_of_mem (image π) ⟨hf, hne⟩⟩ = rep.label ⟨f, hf⟩)
    {D : Set ClosedCylinder} (E : Section5CollapseRectangle ≃ₜ D)
    (H : C(I × ClosedCylinder, ClosedCylinder))
    (K : C(I × OnePoint EuclideanPlane, OnePoint EuclideanPlane))
    (hchart : ∀ t z, H (t, (E z).val) = (E (section5RectangleCollapseHomotopy (t, z))).val)
    (hout : ∀ y ∉ D, ∀ t, H (t, y) = y)
    (hK : ∀ t y, K (t, cylinderToSphere y) = cylinderToSphere (H (t, y)))
    (hoff : ∀ y ∉ range cylinderToSphere, ∀ t, K (t, y) = y)
    (hK0 : ∀ y, K (0, y) = y) (hK1 : ∀ y, K (1, y) = π y)
    (hsegment : closure (cylinderToSphere '' e) = cylinderToSphere ''
      ((fun z => (E z).val) '' {z | z.1.1 = 0 ∧ z.2.1 ≤ 1})) :
    let xs := x.rotations.getD (rep.source i).val []
    let d := gm06PersistentHalfEdgeLabel rep.label a₀
    GM06PersistentRotationRowRep label' γ' (cylinderToSphere (cylinderM1Point k i))
      (gm06SplicedRotation xs ys (xs.idxOf d) (ys.idxOf (gm06DartMate d))) := by
  classical
  dsimp only
  have hlF := (rep.subdrawing.isLink_iff hl.edge_mem).mp hl
  have hlS := cylinderSphereDrawing_isLink hlF
  have hvsS : cylinderToSphere v ≠ cylinderToSphere (cylinderM1Point k i) :=
    fun hh => hvs (injective_cylinderToSphere hh)
  rw [← gm06PersistentHalfEdgeLabel_mate rep.label a₀ a₁ hvsS.symm (ha₀.trans ha₁.symm)]
  let xs := x.rotations.getD (rep.source i).val []
  let q := ys.idxOf (gm06PersistentHalfEdgeLabel rep.label a₁)
  let p := xs.idxOf (gm06PersistentHalfEdgeLabel rep.label a₀)
  let row := gm06SplicedRotation xs ys p q
  have hx : GM06PersistentRotationRowRep rep.label rep.par
      (cylinderToSphere (cylinderM1Point k i)) xs := by
    have hh := rep.rows (rep.source i) (rep.source_live i)
    simpa only [rep.source_point] using hh
  have hq : q < ys.length := List.idxOf_lt_length_iff.mpr ((hy.2.1 _).mpr ⟨a₁, rfl⟩)
  have hp : p < xs.length := List.idxOf_lt_length_iff.mpr ((hx.2.1 _).mpr ⟨a₀, rfl⟩)
  have hgetq : ys[q] = gm06PersistentHalfEdgeLabel rep.label a₁ := List.getElem_idxOf hq
  have hgetp : xs[p] = gm06PersistentHalfEdgeLabel rep.label a₀ := List.getElem_idxOf hp
  let C := cylinderToSphere '' bd ClosedCylinder
  have hC : IsClosed C := isClosedEmbedding_cylinderToSphere.isClosedMap _ (isClosed_bd ClosedCylinder)
  have hvC : cylinderToSphere v ∉ C := by
    rintro ⟨y, hy, hyv⟩
    exact hvbd (injective_cylinderToSphere hyv ▸ hy)
  obtain ⟨O, hO, hvO, hOC, hmid⟩ :=
    exists_vertex_neighbourhood_avoiding_midpoints rep.edgePar hlS.right_mem hC hvC
  obtain ⟨Φ, z, hpolar, hpositive, hΦO, hzi, hs, hspoke, hlabelold⟩ :=
    hy.exists_small_chart_all rep.edgePar hlS.right_mem ⟨cylToPlane v, rfl⟩ hO hvO
  have hΦC : Disjoint (range Φ) C := disjoint_left.mpr
    (fun y hy => disjoint_left.mp hOC (hΦO hy))
  have hmidΦ (a : halfEdges (cylinderSphereDrawing rep.cuffed) rep.par (cylinderToSphere v)) :
      spoke rep.par a.val 1 ∉ range Φ := fun hh => hmid a (hΦO hh)
  obtain ⟨Ψ, χ, hχ, hΨi, hΨ0, hΨnhd, hΨpos, hquot⟩ :=
    exists_positive_full_chart_of_closed_edge_collapse rep.edgePar hlS hvsS a₁ ha₁ hpolar
      hpositive (z (gm06PersistentHalfEdgeLabel rep.label a₁)) (hspoke a₁)
      E H K hchart hout hK hoff hK0 π hK1 hfibre hinj hsegment
  let tail := ys.drop (q + 1) ++ ys.take q
  let J := {r : ℕ // r ∈ tail}
  let : Finite J := tail.finite_toSet.to_subtype
  let : Fintype J := Fintype.ofFinite J
  obtain ⟨b, a, θ, hai, hb, hbne, hacode, hadata, haspoke, hθ, hray, horder⟩ :=
    exists_retained_target_block_data hlS hvsS π hfibre hinj hE rep.edgePar hpar
      rep.label label' hlabel a₁ ha₁ hy hq hgetq hpolar hs hspoke hmidΦ
  obtain ⟨minus, plus, hmp, hm, hplus, hml, hpl, hpc, hqnorm, hmcurve, hpcurve⟩ := rep.inner_cuff_ends i
  have hbm : a₀ ≠ minus := rep.ordinary_end_ne_inner_end hG a₀ minus hl.edge_mem ha₀
    (finPredCycle i) (congrArg Prod.fst hm)
  have hbp : a₀ ≠ plus := rep.ordinary_end_ne_inner_end hG a₀ plus hl.edge_mem ha₀
    i (congrArg Prod.fst hplus)
  have hmne : minus.val.1 ≠ cylinderToSphere '' e := fun heq => hbm
    (halfedge_eq_of_nonloop_edge rep.edgePar hlS hvsS a₀ minus ha₀ heq)
  have hpne : plus.val.1 ≠ cylinderToSphere '' e := fun heq => hbp
    (halfedge_eq_of_nonloop_edge rep.edgePar hlS hvsS a₀ plus ha₀ heq)
  obtain ⟨η, hη, _, hηspoke, _⟩ :=
    exists_contracted_source_halfedge_equiv hlS hvsS π hfibre hinj hE rep.edgePar hpar
  let minus' := η (.inl ⟨minus, hmne⟩)
  let plus' := η (.inl ⟨plus, hpne⟩)
  have hminuscode : gm06PersistentHalfEdgeLabel label' minus' = gm06PersistentHalfEdgeLabel rep.label minus :=
    permanent_label_of_image_halfedge π hE rep.label label' hlabel minus hmne minus' (hη ⟨minus, hmne⟩)
  have hpluscode : gm06PersistentHalfEdgeLabel label' plus' = gm06PersistentHalfEdgeLabel rep.label plus :=
    permanent_label_of_image_halfedge π hE rep.label label' hlabel plus hpne plus' (hη ⟨plus, hpne⟩)
  have hmp' : minus' ≠ plus' := by
    intro hh
    have heq := congrArg (gm06PersistentHalfEdgeLabel label') hh
    rw [hminuscode, hpluscode] at heq
    exact hmp (gm06PersistentHalfEdgeLabel_injective rep.label heq)
  have holdC (c : halfEdges (cylinderSphereDrawing rep.cuffed) rep.par
      (cylinderToSphere (cylinderM1Point k i))) (j : Fin k) (bit : Bool)
      (hc : c.val = (cylinderToSphere '' (initialCuffGapCurve k j '' Ioo 0 1), bit))
      (t : I) : spoke rep.par c.val t ∈ C := by
    change rep.par c.val.1 (halfPar c.val.2 t) ∈ C
    rw [hc, rep.inner_par]
    exact mem_image_of_mem cylinderToSphere (by
      rw [bd_closedCylinder]
      exact Or.inl ((initialCuffGapCurve_props hG j).2.2.1 (mem_range_self _)))
  have hminusspoke (t : I) : spoke γ' minus'.val t = spoke rep.par minus.val t :=
    (hηspoke ⟨minus, hmne⟩ t).trans (hfixed _ (holdC minus (finPredCycle i) true hm t))
  have hplusspoke (t : I) : spoke γ' plus'.val t = spoke rep.par plus.val t :=
    (hηspoke ⟨plus, hpne⟩ t).trans (hfixed _ (holdC plus i false hplus t))
  have hcuff : range (spoke γ' minus'.val) ⊆ C := by
    rintro y ⟨t, rfl⟩
    rw [hminusspoke]
    exact holdC minus (finPredCycle i) true hm t
  have hsmall (j : J) : j.val < 2 * rep.tagged.length := by
    have hh := rep.ordinary_halfedge_word_lt (b j) (rep.interior_halfedge_ordinary hG hvbd (b j))
    simpa only [hb] using hh
  have hma (j : J) : minus' ≠ a j := by
    intro hh
    have heq := congrArg (gm06PersistentHalfEdgeLabel label') hh
    rw [hminuscode, hml, hacode] at heq
    have hj := hsmall j
    omega
  have hpa (j : J) : plus' ≠ a j := by
    intro hh
    have heq := congrArg (gm06PersistentHalfEdgeLabel label') hh
    rw [hpluscode, hpl, hacode] at heq
    have hj := hsmall j
    omega
  have hordinary (j : J) : ∃ f ∈ G'.E, (a j).val.1 = cylinderToSphere '' f := by
    obtain ⟨l, hlive, hbl⟩ := rep.interior_halfedge_ordinary hG hvbd (b j)
    have hlne : rep.edge l ≠ e := fun hh => hbne j (hbl.trans (congrArg (image cylinderToSphere) hh))
    refine ⟨πC '' rep.edge l, hrawE ▸ mem_image_of_mem (image πC) ⟨(rep.links l hlive).edge_mem, hlne⟩, ?_⟩
    calc
      (a j).val.1 = π '' (cylinderToSphere '' rep.edge l) :=
        (congrArg Prod.fst (hadata j)).trans (congrArg (image π) hbl)
      _ = cylinderToSphere '' (πC '' rep.edge l) := by
        rw [image_image, image_image]
        exact image_congr (fun y _ => hcomm y)
  have hinc := spliced_rotation_source_incidence hlS hvsS π hfibre hinj hE rep.edgePar hpar
    rep.label label' hlabel a₀ a₁ ha₀ ha₁ hx hy
  dsimp only at hinc
  rw [← gm06PersistentHalfEdgeLabel_mate rep.label a₀ a₁ hvsS.symm (ha₀.trans ha₁.symm)] at hinc
  change row.Nodup ∧ (∀ r, r ∈ row ↔ ∃ c, gm06PersistentHalfEdgeLabel label' c = r) at hinc
  have hnedge : gm06PersistentHalfEdgeLabel rep.label minus ≠ gm06PersistentHalfEdgeLabel rep.label a₀ :=
    fun hh => hbm (gm06PersistentHalfEdgeLabel_injective rep.label hh).symm
  have hedgep : gm06PersistentHalfEdgeLabel rep.label a₀ ≠ gm06PersistentHalfEdgeLabel rep.label plus :=
    fun hh => hbp (gm06PersistentHalfEdgeLabel_injective rep.label hh)
  have hsourceforms : xs = [gm06PersistentHalfEdgeLabel rep.label minus,
      gm06PersistentHalfEdgeLabel rep.label a₀, gm06PersistentHalfEdgeLabel rep.label plus] ∨
      xs = [gm06PersistentHalfEdgeLabel rep.label a₀, gm06PersistentHalfEdgeLabel rep.label plus,
        gm06PersistentHalfEdgeLabel rep.label minus] ∨
      xs = [gm06PersistentHalfEdgeLabel rep.label plus, gm06PersistentHalfEdgeLabel rep.label minus,
        gm06PersistentHalfEdgeLabel rep.label a₀] := by
    simpa only [hml, hpl] using rep.initial_source_row_forms hG i hval hl hvs a₀ ha₀
  have hforms := spliced_three_end_source_row_forms hnedge hedgep hsourceforms hp hgetp (ys := ys) (q := q)
  let js : List J := tail.attach
  have htail : js.map (fun j => gm06PersistentHalfEdgeLabel label' (a j)) = tail := by
    simp only [hacode]
    exact (List.attach_map_val (l := tail) (f := id)).trans (List.map_id tail)
  have hforms' : row = gm06PersistentHalfEdgeLabel label' minus' ::
        (js.map (fun j => gm06PersistentHalfEdgeLabel label' (a j)) ++ [gm06PersistentHalfEdgeLabel label' plus']) ∨
      row = js.map (fun j => gm06PersistentHalfEdgeLabel label' (a j)) ++
        [gm06PersistentHalfEdgeLabel label' plus', gm06PersistentHalfEdgeLabel label' minus'] ∨
      row = gm06PersistentHalfEdgeLabel label' plus' :: gm06PersistentHalfEdgeLabel label' minus' ::
        js.map (fun j => gm06PersistentHalfEdgeLabel label' (a j)) := by
    simpa only [htail, hminuscode, hpluscode, tail, row, List.append_assoc] using hforms
  have hjsorder : js.Pairwise (fun j l => θ j.val < θ l.val) := by
    have heq : js.map (fun j : J => j.val) = tail := by
      exact (List.attach_map_val (l := tail) (f := id)).trans (List.map_id tail)
    have hh : (js.map Subtype.val).Pairwise (fun j l => θ j < θ l) := by
      rw [heq]
      exact horder
    exact (List.pairwise_map (f := fun j : J => j.val) (R := fun j l : ℕ => θ j < θ l)).mp hh
  have hpV : cylinderToSphere (cylinderM1Point k i) ∈ Γ'.V := by
    rw [← minus'.property.2]
    exact end_mem_V hγ' minus'.property.1 minus'.val.2
  have hscale : 0 < Real.pi / (k : ℝ) := div_pos Real.pi_pos (Nat.cast_pos.mpr i.pos)
  change GM06PersistentRotationRowRep label' γ' (cylinderToSphere (cylinderM1Point k i)) row
  apply persistent_rotation_row_of_collapsed_source_block hγ' hpV hpc hqnorm hscale hfibre hinj hfixed
    (z (gm06PersistentHalfEdgeLabel rep.label a₁)) hquot hΨi hΨpos hΨ0 hΨnhd hΦC
    minus' plus' hmp' hcuff
    (fun t => (hminusspoke t).trans (hmcurve t)) (fun t => (hplusspoke t).trans (hpcurve t))
    a hai hma hpa hG' hordinary (fun j => spoke rep.par (b j).val) haspoke
    (fun j => θ j.val) (fun j => (hθ j).1) (fun j => (hθ j).2.1)
    (fun j t ht => by rw [← hgetq]; exact hray j t ht) label' hjsorder hinc.1 hinc.2 hforms'

end GraphMinor.GM06
