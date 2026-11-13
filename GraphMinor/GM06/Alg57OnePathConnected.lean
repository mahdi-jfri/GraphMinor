module

public import GraphMinor.GM06.Alg57RotationConnected
import GraphMinor.GM06.Section5PuncturedLinkage
import GraphMinor.GM06.Section5DeletedStartComponents
import GraphMinor.GM06.Section5CapDrawing
import GraphMinor.GM06.Section3Induce
import GraphMinor.GM06.Section4PathTools
import GraphMinor.GM11.Walks

/-!
# Lemma 4 for every `k ≥ 1`

Lemma 4 of our proof of VI (5.7) (outlined in `Alg57Algorithm.lean`) says that when Reduction 2 does
not apply, the cuffed graph `G⁺` is connected. For `k ≥ 2` it follows from the punctured form (the
drawing and cuffs stay connected after deleting `sᵢ`). For `k = 1` the punctured form is false:
deleting `s₁` cuts the inner cuff loose. Here we prove the unpunctured form for every `k ≥ 1`
(`isConnected_drawing_and_cuffs_of_no_reduction2`), and with it the incidence results of Lemma 11 on
`G⁺` for every `k ≥ 1` (`region_incidence_of_no_reduction'`,
`subset_closure_region_iff_of_no_reduction'`).

The proof: the linkage and both cuffs form a connected set, since every path joins the two cuffs.
Every component of `G - s₁` meets the linkage, because Reduction 2 does not apply
(`deleted_start_component_meets_linkage_of_no_reduction2`). Every edge has an end, which joins it to
this set.
-/

public section

namespace GraphMinor.GM06

open Set Topology GraphMinor.Surface GraphMinor.GM11 unitInterval

private theorem connected_of_oArc' {C : Set ClosedCylinder} (hC : IsOArc C) :
    IsConnected C := by
  obtain ⟨e⟩ := hC
  exact isConnected_iff_connectedSpace.mpr (e.surjective.connectedSpace e.continuous)

/-- With at least one path, the linkage and both cuffs form a connected set. -/
theorem isConnected_linkage_and_cuffs {k : ℕ} {G : Drawing ClosedCylinder}
    (L : CylinderLinkage k G) (hk : 0 < k) :
    IsConnected (bd ClosedCylinder ∪ ⋃ j, (L.pathDrawing j).U) := by
  have ht (j : Fin k) : L.curve j 1 ∈ cylinderCuff2 := by
    obtain ⟨n, hn⟩ := L.curve_one_mem j
    rw [← hn]
    rfl
  have hstart (j : Fin k) : cylinderM1Point k j ∈ (L.pathDrawing j).U := by
    rw [← (L.curve_parametrizes j).2.1]
    exact ⟨0, (L.curve_parametrizes j).2.2.1⟩
  have hend (j : Fin k) : L.curve j 1 ∈ (L.pathDrawing j).U := by
    rw [← (L.curve_parametrizes j).2.1]
    exact ⟨1, rfl⟩
  have hp (j : Fin k) : IsConnected (L.pathDrawing j).U := by
    rw [← (L.curve_parametrizes j).2.1]
    exact isConnected_range (L.curve j).continuous
  let D := cylinderCuff2 ∪ ⋃ j, (L.pathDrawing j).U
  have hC2 := connected_of_oArc' isOArc_cylinderCuff2
  obtain ⟨a, ha⟩ := hC2.nonempty
  have hD : IsConnected D := by
    refine ⟨⟨a, Or.inl ha⟩, ?_⟩
    apply isPreconnected_of_forall a
    intro x hx
    rcases hx with hx | hx
    · exact ⟨cylinderCuff2, subset_union_left, ha, hx, hC2.isPreconnected⟩
    · obtain ⟨j, hx⟩ := mem_iUnion.mp hx
      have hj := hC2.union ⟨L.curve j 1, ht j, hend j⟩ (hp j)
      exact ⟨cylinderCuff2 ∪ (L.pathDrawing j).U,
        union_subset_union_right _ (fun y hy => mem_iUnion.mpr ⟨j, hy⟩), Or.inl ha, Or.inr hx,
        hj.isPreconnected⟩
  have hC1 := connected_of_oArc' isOArc_cylinderCuff1
  let j₀ : Fin k := ⟨0, hk⟩
  have hjoin : (D ∩ cylinderCuff1).Nonempty :=
    ⟨cylinderM1Point k j₀, Or.inr (mem_iUnion.mpr ⟨j₀, hstart j₀⟩), rfl⟩
  have hconn := hD.union hjoin hC1
  convert hconn using 1
  rw [bd_closedCylinder]
  ext x
  constructor
  · rintro ((hx | hx) | hx)
    · exact Or.inr hx
    · exact Or.inl (Or.inl hx)
    · exact Or.inl (Or.inr hx)
  · rintro ((hx | hx) | hx)
    · exact Or.inl (Or.inr hx)
    · exact Or.inr hx
    · exact Or.inl (Or.inl hx)

/-- **Lemma 4, every `k ≥ 1`.** If Reduction 2 does not apply, the drawing together with both
cuffs is connected. -/
theorem isConnected_drawing_and_cuffs_of_no_reduction2
    {k : ℕ} {G : Drawing ClosedCylinder} (L : CylinderLinkage k G)
    (hk : 0 < k) (hG : IsCylinderSection5Drawing k G)
    (hno : ∀ (G₁ : Drawing ClosedCylinder) (L₁ : CylinderLinkage k G₁),
      IsCylinderSection5Drawing k G₁ → ¬ Section5Reduction2Step k G L G₁ L₁) :
    IsConnected (bd ClosedCylinder ∪ G.U) := by
  classical
  let i : Fin k := ⟨0, hk⟩
  let s := cylinderM1Point k i
  let X := bd ClosedCylinder ∪ G.U
  let C := bd ClosedCylinder ∪ ⋃ j, (L.pathDrawing j).U
  have hC : IsConnected C := isConnected_linkage_and_cuffs L hk
  have hCX : C ⊆ X := by
    rintro x (hx | hx)
    · exact Or.inl hx
    · obtain ⟨j, hj⟩ := mem_iUnion.mp hx
      exact Or.inr ((L.isSubdrawing j).2 hj)
  obtain ⟨a, ha⟩ := hC.nonempty
  have hsC : s ∈ C := by
    refine Or.inr (mem_iUnion.mpr ⟨i, ?_⟩)
    rw [← (L.curve_parametrizes i).2.1]
    exact ⟨0, (L.curve_parametrizes i).2.2.1⟩
  let H := induceDrawing G (G.V \ {s})
  have hHG : H.IsSubdrawing G := induceDrawing_isSubdrawing G sdiff_subset
  have hHX : H.U ⊆ X := fun x hx => Or.inr (hHG.U_subset hx)
  have hHV : H.V = G.V \ {s} := induceDrawing_V G sdiff_subset
  have hvertex (b : ClosedCylinder) (hb : b ∈ G.V) :
      ∃ Y ⊆ X, a ∈ Y ∧ b ∈ Y ∧ IsConnected Y := by
    by_cases hbs : b = s
    · exact ⟨C, hCX, ha, hbs ▸ hsC, hC⟩
    have hbH : b ∈ H.V := hHV.symm ▸ ⟨hb, hbs⟩
    let K := compOf H.toGraph b
    have hK : IsGraphComponent K H.toGraph := isGraphComponent_compOf hbH
    have hKi : IsGraphComponent K (G.toGraph.induce (G.V \ {s})) := by
      rw [← induceDrawing_toGraph_eq_induce G sdiff_subset]
      exact hK
    obtain ⟨j, z, hzK, hzP⟩ := deleted_start_component_meets_linkage_of_no_reduction2 L hG hno i hKi
    have hKX : compPointSet K ⊆ X := by
      apply subset_trans ?_ hHX
      rw [← biUnion_compPointSet_eq_U H]
      exact fun y hy => mem_iUnion₂.mpr ⟨K, hK, hy⟩
    have hzC : z ∈ C :=
      Or.inr (mem_iUnion.mpr ⟨j, (L.pathDrawing j).V_subset_U hzP⟩)
    exact ⟨C ∪ compPointSet K, union_subset hCX hKX, Or.inl ha,
      Or.inr (Or.inl (self_mem_reachSet hbH)),
      hC.union ⟨z, hzC, Or.inl hzK⟩ (isConnected_compPointSet H hK)⟩
  refine ⟨⟨a, hCX ha⟩, ?_⟩
  apply isPreconnected_of_forall a
  intro x hx
  by_cases hxC : x ∈ C
  · exact ⟨C, hCX, ha, hxC, hC.isPreconnected⟩
  have hxG : x ∈ G.U := hx.resolve_left (fun hb => hxC (Or.inl hb))
  by_cases hxV : x ∈ G.V
  · obtain ⟨Y, hY, haY, hxY, hcY⟩ := hvertex x hxV
    exact ⟨Y, hY, haY, hxY, hcY.isPreconnected⟩
  have hxEdges : x ∈ ⋃ e ∈ G.E, closure e := by
    rw [G.U_eq] at hxG
    exact hxG.resolve_left hxV
  obtain ⟨e, he, hxe⟩ := mem_iUnion₂.mp hxEdges
  obtain ⟨u, v, hl⟩ := G.toGraph.exists_isLink_of_mem_edgeSet he
  have hucl : u ∈ closure e := (hl.2.2.2 ▸ mem_insert u {v} : u ∈ closure e ∩ G.V).1
  obtain ⟨Y, hY, haY, huY, hcY⟩ := hvertex u hl.left_mem
  have heC : IsConnected (closure e) := he.2.2.1.isConnected.closure
  have heX : closure e ⊆ X := fun y hy =>
    Or.inr (G.isClosed_U.closure_subset_iff.mpr (he.2.1.trans sdiff_subset) hy)
  exact ⟨Y ∪ closure e, union_subset hY heX, Or.inl haY, Or.inr hxe,
    (hcY.union ⟨u, huY, hucl⟩ heC).isPreconnected⟩

variable {k : ℕ} {G F : Drawing ClosedCylinder}
  {γ : Set (OnePoint EuclideanPlane) → I → OnePoint EuclideanPlane}
  {R : DartRotation (DrawingDart (cylinderSphereDrawing F))}

/-- When no reduction applies and `k ≥ 1`, the point set of the cuffed drawing in the sphere is
connected. -/
theorem isPreconnected_cylinderSphereDrawing_U_of_no_reduction' (L : CylinderLinkage k G)
    (hk : 0 < k) (hG : IsCylinderSection5Drawing k G) (hno : ¬ Section5AnyReductionApplies k G L)
    (hFU : F.U = G.U ∪ bd ClosedCylinder) : IsPreconnected (cylinderSphereDrawing F).U := by
  rw [cylinderSphereDrawing_U, hFU, union_comm]
  exact ((isConnected_drawing_and_cuffs_of_no_reduction2 L hk hG
    (fun G₁ L₁ hG₁ hRed => hno ⟨G₁, L₁, hG₁, Or.inr (Or.inl hRed)⟩)).image _
    continuous_cylinderToSphere.continuousOn).isPreconnected

/-- **Lemma 11, incidence (10), for every `k ≥ 1`.** `region_incidence_of_no_reduction` without
the hypothesis `k ≥ 2`. -/
theorem region_incidence_of_no_reduction' (L : CylinderLinkage k G) (hk : 0 < k)
    (hG : IsCylinderSection5Drawing k G) (hno : ¬ Section5AnyReductionApplies k G L)
    (hFU : F.U = G.U ∪ bd ClosedCylinder) (hγ : EdgePar (cylinderSphereDrawing F) γ)
    (hR : IsDrawingRotation (cylinderSphereDrawing F) γ R)
    (hccw : IsCcwRotation (cylinderSphereDrawing F) γ R) (i : Fin k)
    (he : cylinderToSphere '' (initialCuffGapCurve k i '' Ioo 0 1) ∈ (cylinderSphereDrawing F).E)
    (hγe : ∀ t, γ (cylinderToSphere '' (initialCuffGapCurve k i '' Ioo 0 1)) t =
      cylinderToSphere (initialCuffGapCurve k i t)) :
    (∀ v : ClosedCylinder, cylinderToSphere v ∈ (cylinderSphereDrawing F).V →
      (v ∈ closure (cylinderRegion k G i) ↔
        ∃ d : DrawingDart (cylinderSphereDrawing F), dartVertex γ d = cylinderToSphere v ∧
          R.faceOf d = R.faceOf (reverseInnerGapDart k i F he))) ∧
    (∀ d : DrawingDart (cylinderSphereDrawing F),
      d.1.1 ⊆ cylinderToSphere '' closure (cylinderRegion k G i) ↔
        R.faceOf d = R.faceOf (reverseInnerGapDart k i F he) ∨
          R.faceOf (R.rev d) = R.faceOf (reverseInnerGapDart k i F he)) := by
  have hU := isPreconnected_cylinderSphereDrawing_U_of_no_reduction' L hk hG hno hFU
  exact region_incidence_of_ccw hG hFU hγ hR hccw (DartRotation.connected_of_isPreconnected_U hγ hR hU)
    (exists_dart_of_isPreconnected_U hγ hU ⟨_, he⟩) i he hγe

/-- `subset_closure_region_iff_of_no_reduction` without the hypothesis `k ≥ 2`. -/
theorem subset_closure_region_iff_of_no_reduction' (L : CylinderLinkage k G) (hk : 0 < k)
    (hG : IsCylinderSection5Drawing k G) (hno : ¬ Section5AnyReductionApplies k G L)
    (hGF : G.IsSubdrawing F)
    (hFU : F.U = G.U ∪ bd ClosedCylinder) (hγ : EdgePar (cylinderSphereDrawing F) γ)
    (hR : IsDrawingRotation (cylinderSphereDrawing F) γ R)
    (hccw : IsCcwRotation (cylinderSphereDrawing F) γ R) (i : Fin k)
    (he : cylinderToSphere '' (initialCuffGapCurve k i '' Ioo 0 1) ∈ (cylinderSphereDrawing F).E)
    (hγe : ∀ t, γ (cylinderToSphere '' (initialCuffGapCurve k i '' Ioo 0 1)) t =
      cylinderToSphere (initialCuffGapCurve k i t))
    {P : Drawing ClosedCylinder} (hP : P.IsSubdrawing G) :
    P.U ⊆ closure (cylinderRegion k G i) ↔
      (∀ v ∈ P.V, ∃ d : DrawingDart (cylinderSphereDrawing F),
        dartVertex γ d = cylinderToSphere v ∧
          R.faceOf d = R.faceOf (reverseInnerGapDart k i F he)) ∧
      (∀ e ∈ P.E, ∃ (b : Bool) (he' : cylinderToSphere '' e ∈ (cylinderSphereDrawing F).E),
        R.faceOf ⟨(cylinderToSphere '' e, b), he'⟩ =
          R.faceOf (reverseInnerGapDart k i F he)) := by
  have hU := isPreconnected_cylinderSphereDrawing_U_of_no_reduction' L hk hG hno hFU
  exact subset_closure_region_iff_of_ccw hG hGF hFU hγ hR hccw
    (DartRotation.connected_of_isPreconnected_U hγ hR hU)
    (exists_dart_of_isPreconnected_U hγ hU ⟨_, he⟩) i he hγe hP

end GraphMinor.GM06
