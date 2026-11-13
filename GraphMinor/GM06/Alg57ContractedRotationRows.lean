module

public import GraphMinor.GM06.Alg57SourceSplice
public import GraphMinor.GM06.Alg57ContractedCuffData
public import GraphMinor.Compute.GM06ContractRotationData

/-!
# The complete rotation table after the selected contraction

For Lemma 8 of VI (5.7), page 133, the finite command splices the
source row, clears the retired neighbour's row and leaves every
other row unchanged. The source splice has the actual positive
order proved in `Alg57SourceSplice`. At every other live vertex,
the capped rectangular homotopy transports its positive chart.
Thus the whole computed table, including empty retired rows, has
its required geometric meaning after the same contraction.
-/

public section
namespace GraphMinor.GM06
open Set Topology GraphMinor.Surface GraphMinor.GM11 GraphMinor.Compute unitInterval

private theorem open_image_off_collapsed_fibre
    {S : Type*} [TopologicalSpace S] [CompactSpace S] [T2Space S]
    (π : C(S, S)) {p : S} {A : Set S} (hfibre : π ⁻¹' {p} = A)
    (hi : InjOn π Aᶜ) (hsurj : Function.Surjective π)
    {O : Set S} (hO : IsOpen O) (hOA : Disjoint O A) : IsOpen (π '' O) := by
  have hq := π.continuous.isClosedMap.isQuotientMap π.continuous hsurj
  rw [← hq.isCoinducing.isOpen_preimage]
  have hpre : π ⁻¹' (π '' O) = O := by
    ext x
    constructor
    · rintro ⟨y, hy, hyx⟩
      have hyA : y ∉ A := disjoint_left.mp hOA hy
      have hxA : x ∉ A := by
        intro hx
        have hxp : π x = p := show x ∈ π ⁻¹' {p} from hfibre.symm ▸ hx
        exact hyA (hfibre ▸ (show y ∈ π ⁻¹' {p} from hyx.trans hxp))
      exact hi hyA hxA hyx ▸ hy
    · exact fun hx => ⟨x, hx, rfl⟩
  rw [hpre]
  exact hO

private theorem contract_rotation_rows_getD
    (rows : List (List ℕ)) (a b d e j : ℕ) (hj : j < rows.length) :
    (gm06ContractRotationRows rows a b d e).getD j [] =
      if b = j then [] else if a = j then
        gm06SplicedRotation (rows.getD a []) (rows.getD b [])
          ((rows.getD a []).idxOf d) ((rows.getD b []).idxOf e)
      else rows.getD j [] := by
  rw [List.getD_eq_getElem _ _ (by rw [gm06ContractRotationRows_length]; exact hj),
    gm06ContractRotationRows_getElem rows a b d e hj, List.getD_eq_getElem _ _ hj]
  rfl

/-- Lemma 8 for the whole finite rotation table: the computed splice
and cleared row, with all other rows retained, interpret the actual
current drawing after the selected rectangular contraction. -/
theorem GM06CurrentDrawingRep.contracted_rotation_rows
    {k : ℕ} {x : GM06SuccessorInput} {G G' : Drawing ClosedCylinder}
    {L : CylinderLinkage k G} (rep : GM06CurrentDrawingRep x G L)
    (hG : IsCylinderSection5Drawing k G) (hG' : G'.IsProper) (i : Fin k)
    (b : Fin x.vertexCount) (hb : b ∈ rep.live)
    (first : ℕ) (rest : List ℕ)
    (hrow : x.linkage[i.val]'(by rw [rep.linkage.1]; exact i.isLt) = first :: rest)
    (hfirst : first < 2 * rep.tagged.length)
    (hval : vertexValency G.toGraph (cylinderM1Point k i) = 1)
    (hl : G.toGraph.IsLink (rep.edge ⟨first / 2, by omega⟩)
      (cylinderM1Point k i) (rep.vertex b))
    (hvs : rep.vertex b ≠ cylinderM1Point k i) (hvbd : rep.vertex b ∉ bd ClosedCylinder)
    (vertex' : Fin x.vertexCount → ClosedCylinder)
    (πC : C(ClosedCylinder, ClosedCylinder))
    (hnew : ∀ j ∈ rep.live.erase b, vertex' j = πC (rep.vertex j))
    (hsource : vertex' (rep.source i) = cylinderM1Point k i)
    (hrawE : G'.E = (image πC) '' (G.E \ {rep.edge ⟨first / 2, by omega⟩}))
    {Γ' : Drawing (OnePoint EuclideanPlane)}
    (π : C(OnePoint EuclideanPlane, OnePoint EuclideanPlane))
    (hcomm : ∀ y, π (cylinderToSphere y) = cylinderToSphere (πC y))
    (hfibre : π ⁻¹' {cylinderToSphere (cylinderM1Point k i)} =
      closure (cylinderToSphere '' rep.edge ⟨first / 2, by omega⟩))
    (hinj : InjOn π (closure (cylinderToSphere '' rep.edge ⟨first / 2, by omega⟩))ᶜ)
    (hsurj : Function.Surjective π)
    (hfixed : ∀ y ∈ cylinderToSphere '' bd ClosedCylinder, π y = y)
    (hU : Γ'.U = π '' (cylinderSphereDrawing rep.cuffed).U)
    (hV : Γ'.V = π '' (cylinderSphereDrawing rep.cuffed).V)
    (hE : Γ'.E = (image π) '' ((cylinderSphereDrawing rep.cuffed).E \
      {cylinderToSphere '' rep.edge ⟨first / 2, by omega⟩}))
    {γ' : Set (OnePoint EuclideanPlane) → I → OnePoint EuclideanPlane}
    (hγ' : EdgePar Γ' γ')
    (hpar : ∀ f ∈ (cylinderSphereDrawing rep.cuffed).E,
      f ≠ cylinderToSphere '' rep.edge ⟨first / 2, by omega⟩ →
      ∀ t, γ' (π '' f) t = π (rep.par f t))
    (label' : Γ'.E ↪ ℕ)
    (hlabel : ∀ f (hf : f ∈ (cylinderSphereDrawing rep.cuffed).E)
      (hne : f ≠ cylinderToSphere '' rep.edge ⟨first / 2, by omega⟩),
      label' ⟨π '' f, hE ▸ mem_image_of_mem (image π) ⟨hf, hne⟩⟩ = rep.label ⟨f, hf⟩)
    {D : Set ClosedCylinder} (E : Section5CollapseRectangle ≃ₜ D)
    (H : C(I × ClosedCylinder, ClosedCylinder))
    (K : C(I × OnePoint EuclideanPlane, OnePoint EuclideanPlane))
    (hchart : ∀ t z, H (t, (E z).val) = (E (section5RectangleCollapseHomotopy (t, z))).val)
    (hout : ∀ y ∉ D, ∀ t, H (t, y) = y)
    (hK : ∀ t y, K (t, cylinderToSphere y) = cylinderToSphere (H (t, y)))
    (hoff : ∀ y ∉ range cylinderToSphere, ∀ t, K (t, y) = y)
    (hK0 : ∀ y, K (0, y) = y) (hK1 : ∀ y, K (1, y) = π y)
    (hsegment : closure (cylinderToSphere '' rep.edge ⟨first / 2, by omega⟩) = cylinderToSphere ''
      ((fun z => (E z).val) '' {z | z.1.1 = 0 ∧ z.2.1 ≤ 1})) :
    let rows := gm06ContractRotationRows x.rotations (rep.source i).val b.val first (gm06DartMate first)
    (∀ j ∈ rep.live.erase b, GM06PersistentRotationRowRep label' γ'
      (cylinderToSphere (vertex' j)) (rows.getD j.val [])) ∧
      ∀ j : Fin x.vertexCount, j ∉ rep.live.erase b → rows.getD j.val [] = [] := by
  classical
  dsimp only
  have hsb : rep.source i ≠ b := by
    intro hh
    exact hvs (hh ▸ rep.source_point i)
  have hsbval : (rep.source i).val ≠ b.val := fun hh => hsb (Fin.ext hh)
  have hread (j : Fin x.vertexCount) := contract_rotation_rows_getD x.rotations
    (rep.source i).val b.val first (gm06DartMate first) j.val (rep.rows_length.symm ▸ j.isLt)
  have hlF := (rep.subdrawing.isLink_iff hl.edge_mem).mp hl
  have hlS := cylinderSphereDrawing_isLink hlF
  have hvsS : cylinderToSphere (rep.vertex b) ≠ cylinderToSphere (cylinderM1Point k i) :=
    fun hh => hvs (injective_cylinderToSphere hh)
  constructor
  · intro j hj
    have hjb : j ≠ b := (Finset.mem_erase.mp hj).1
    have hjbval : b.val ≠ j.val := fun hh => hjb (Fin.ext hh.symm)
    have hjlive := (Finset.mem_erase.mp hj).2
    rw [hread, ite_eq_right hjbval]
    by_cases hjs : rep.source i = j
    · subst j
      rw [ite_eq_left rfl, hsource]
      obtain ⟨a₀, a₁, ha₀, ha₁, hcode₀, hcode₁⟩ :=
        rep.initial_word_halfedges i first rest hrow hfirst hl hvs
      have hy := rep.rows b hb
      have hh := rep.source_splice_of_rectangular_collapse hG hG' i hval hl hvs hvbd
        a₀ a₁ ha₀ ha₁ hy πC hrawE π hcomm hfibre hinj hfixed hE hγ' hpar label' hlabel
        E H K hchart hout hK hoff hK0 hK1 hsegment
      dsimp only at hh
      simpa only [hcode₀] using hh
    · have hjsval : (rep.source i).val ≠ j.val := fun hh => hjs (Fin.ext hh)
      rw [ite_eq_right hjsval]
      have hjoff : rep.vertex j ∉ closure (rep.edge ⟨first / 2, by omega⟩) := by
        intro hjcl
        have hjends : rep.vertex j ∈ ({cylinderM1Point k i, rep.vertex b} : Set ClosedCylinder) :=
          hl.2.2.2 ▸ And.intro hjcl (rep.vertex_mem j hjlive)
        rcases hjends with hstart | hend
        · have heq : j = rep.source i := rep.vertex_inj hjlive (rep.source_live i)
            (hstart.trans (rep.source_point i).symm)
          exact hjs heq.symm
        · exact hjb (rep.vertex_inj hjlive hb (mem_singleton_iff.mp hend))
      have hjoffS : cylinderToSphere (rep.vertex j) ∉
          closure (cylinderToSphere '' rep.edge ⟨first / 2, by omega⟩) := by
        rw [isClosedEmbedding_cylinderToSphere.closure_image_eq]
        rintro ⟨y, hy, hyj⟩
        exact hjoff (injective_cylinderToSphere hyj ▸ hy)
      have hh := persistent_rotation_row_of_capped_rectangle_collapse hlS hvsS π hfibre hinj hsurj
        (fun O hO hOe => open_image_off_collapsed_fibre π hfibre hinj hsurj hO hOe)
        hV hE hU rep.edgePar hpar hjoffS E H K hchart hout hK hoff hK0 hK1 hsegment
        rep.label label' hlabel (rep.rows j hjlive)
      have hpoint : π (cylinderToSphere (rep.vertex j)) = cylinderToSphere (vertex' j) :=
        (hcomm _).trans (congrArg cylinderToSphere (hnew j hj).symm)
      simpa only [hpoint] using hh
  · intro j hj
    rw [hread]
    by_cases hbj : b.val = j.val
    · rw [ite_eq_left hbj]
    · rw [ite_eq_right hbj]
      have hjnot : j ∉ rep.live := fun hjlive =>
        hj (Finset.mem_erase.mpr ⟨fun hh => hbj (congrArg Fin.val hh.symm), hjlive⟩)
      have hsj : (rep.source i).val ≠ j.val := by
        intro hh
        exact hjnot (Fin.ext hh ▸ rep.source_live i)
      rw [ite_eq_right hsj]
      exact rep.retired_rows j hjnot

end GraphMinor.GM06
