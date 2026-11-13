module

public import GraphMinor.GM08.Section17CollarTransport
public import GraphMinor.GM08.Section17CollarDrawing
public import GraphMinor.GM08.Section17Defs
public import GraphMinor.GM08.Section16PrintedDefs
public import GraphMinor.GM08.Section17RootLeaves
import GraphMinor.GM08.Section17CollarOrder
import GraphMinor.GM08.Section17Linked
public import GraphMinor.GM08.Section17Minor
import GraphMinor.GM08.Section17LeafReflect
import GraphMinor.GM08.Section15PuncturedCylinder

/-!
# A linked framing simulates every graft with the same boundary

This is the main step of VIII (17.2). Let `X` and `Y` be drawn in the cylinder
`S` with the same boundary vertices, and let the framing of `X` by the two cuffs
be boundary-linked with large enough width and length. We want VII (9.3), but
its hoops must avoid the boundary, and the hoops given by boundary linking may
touch the cuffs only through vertices. So we add a leaf at every root of both
grafts, and draw the new leaves on spokes in the caps of the capped sphere. The
part `Q` of the sphere left after removing a small disc from each cap is a
larger cylinder. In `Q` the images of the two hoops avoid the boundary, and the
earlier files carry every other condition of VII (9.3) to `Q`. So VII (9.3)
gives a simulation of the root-leaf graft of `Y` in that of `X`, and removing
the leaves gives a simulation of `Y` in `X`.
-/

public section

namespace GraphMinor.GM08

open Set Topology GraphMinor.Surface GraphMinor.GM07 GraphMinor.GM12

universe u v

variable {S : Type} [TopologicalSpace S]

/-- The vertices of the collar drawing on the boundary of the small discs are
the ends of the spokes. -/
theorem CollarWheel.V_inter_discBd_eq {cap : CylinderSphereCap S} {P : Set S}
    (W : CollarWheel cap P) (hP : P ⊆ bd S) {Γ : Drawing S} {H : Drawing cap.Z}
    (hHV : H.V = cap.j '' Γ.V ∪ (fun x => W.q (cap.j x)) '' P) :
    H.V ∩ (discBd W.E₁ ∪ discBd W.E₂) = (fun x => W.q (cap.j x)) '' P := by
  have hr₁ : Disjoint (range cap.j) W.E₁ :=
    cap.disjoint_range_discInt_D₁.mono_right W.E₁_subset
  have hr₂ : Disjoint (range cap.j) W.E₂ :=
    cap.disjoint_range_discInt_D₂.mono_right W.E₂_subset
  rw [hHV, union_inter_distrib_right]
  have h₁ : cap.j '' Γ.V ∩ (discBd W.E₁ ∪ discBd W.E₂) = ∅ := by
    refine eq_empty_iff_forall_notMem.mpr ?_
    rintro _ ⟨⟨x, -, rfl⟩, h | h⟩
    · exact disjoint_left.mp hr₁ ⟨x, rfl⟩ (discBd_subset _ h)
    · exact disjoint_left.mp hr₂ ⟨x, rfl⟩ (discBd_subset _ h)
  rw [h₁, empty_union, inter_eq_left]
  rintro _ ⟨x, hx, rfl⟩
  rcases (cap.bd_eq ▸ hP hx : x ∈ cap.C₁ ∪ cap.C₂) with h | h
  · exact .inl (W.q_mem₁ x hx h)
  · exact .inr (W.q_mem₂ x hx h)

/-- The vertices of the collar drawing on the boundary of one small disc are
the ends of the spokes from the matching cuff. -/
theorem CollarWheel.V_inter_discBd_subset {cap : CylinderSphereCap S} {P : Set S}
    (W : CollarWheel cap P) {Γ : Drawing S} (hP : Γ.V ∩ bd S = P) {H : Drawing cap.Z}
    (hHV : H.V = cap.j '' Γ.V ∪ (fun x => W.q (cap.j x)) '' P)
    {C C' : Set S} {E E' : Set cap.Z} (hbd : bd S = C ∪ C') (hEE' : Disjoint E E')
    (hE : E = W.E₁ ∨ E = W.E₂)
    (hq' : ∀ x ∈ P, x ∈ C' → W.q (cap.j x) ∈ discBd E') :
    H.V ∩ discBd E ⊆ (fun x => W.q (cap.j x)) '' (Γ.V ∩ C) := by
  have hPbd : P ⊆ bd S := hP ▸ inter_subset_right
  rintro z ⟨hzV, hzE⟩
  have hz : z ∈ H.V ∩ (discBd W.E₁ ∪ discBd W.E₂) :=
    ⟨hzV, by rcases hE with rfl | rfl; exacts [.inl hzE, .inr hzE]⟩
  rw [W.V_inter_discBd_eq hPbd hHV] at hz
  obtain ⟨x, hx, rfl⟩ := hz
  have hxV : x ∈ Γ.V := (hP ▸ hx : x ∈ Γ.V ∩ bd S).1
  rcases (hbd ▸ hPbd hx : x ∈ C ∪ C') with h | h
  · exact ⟨x, ⟨hxV, h⟩, rfl⟩
  · exact absurd (discBd_subset _ (hq' x hx h)) (disjoint_left.mp hEE' (discBd_subset _ hzE))

/-- The main step of VIII (17.2), page 284. If `X` and `Y` are drawn in the
cylinder with the same boundary vertices, and the framing of `X` by the two
cuffs is boundary-linked with the width and length below, then `Y` is
simulated in `X`. -/
theorem isGraftSimulatedIn_of_printedBoundaryLinked (hS : IsCylinder S)
    (cap : CylinderSphereCap S) {α : Type u} {β : Type v} {Y X : Graft α β}
    (DY : GraftDrawing Y.G Y.T S) (DX : GraftDrawing X.G X.T S)
    (hbd : DY.drawing.V ∩ bd S = DX.drawing.V ∩ bd S)
    (τ : Tube S) (hτΓ : τ.Γ = DX.drawing) (hτ₁ : τ.F₁ = cap.C₁) (hτ₂ : τ.F₂ = cap.C₂)
    (hlink : τ.IsPrintedBoundaryLinked (cylinderMinorThreshold (rootLeafGraft Y) + 1)
      (max 4 (2 * cylinderMinorThreshold (rootLeafGraft Y)))) :
    IsGraftSimulatedIn Y X := by
  classical
  have : Nonempty S := hS.nonempty
  have : CompactSpace S := hS.compactSpace
  have : T2Space cap.Z := cap.t2Space_Z
  have : ConnectedSpace cap.Z := cap.connectedSpace
  obtain ⟨A, B, hlam, hNA, hNB, hAB, -, -, hBA, -, hcentral, -, -, hsk₁, hsk₂, hline⟩ :=
    τ.exists_minor_linkage_of_printedBoundaryLinked _ hlink
  rw [hτΓ] at hNA hNB hcentral hline
  rw [hτΓ, hτ₁] at hsk₁
  rw [hτΓ, hτ₂] at hsk₂
  rw [hτ₁] at hBA
  have hA : IsHoop A := hlam.2.1
  have hB : IsHoop B := hlam.2.2.1
  -- the hoop `B` is nearer to the first cuff than `A`
  have hle : cap.disc₁ hS.1 hB ⊆ cap.disc₁ hS.1 hA := by
    have h0 : cap.disc₁ hS.1 (cap.isHoop_C₁ hS.1) ⊆ cap.disc₁ hS.1 hA := by
      rw [cap.disc₁_C₁ hS.1]
      exact (cap.disc₁_disc₂_spec hS.1 hA).2.2.2.2.2.2.1
    exact ((cap.hoop_subset_cylinderBetween_iff hS (cap.isHoop_C₁ hS.1) hA hB h0).mp hBA).2
  -- the spokes and the two root-leaf drawings in the larger cylinder `Q`
  set P := DX.drawing.V ∩ bd S with hPdef
  have hPbd : P ⊆ bd S := inter_subset_right
  obtain ⟨W⟩ := cap.exists_collarWheel hPbd
  obtain ⟨HX, hHXQ, gdX, hgdX, hXU, hXV, hXE⟩ := W.exists_collar_graftDrawing DX rfl
  obtain ⟨HY, hHYQ, gdY, hgdY, -, hYV, -⟩ := W.exists_collar_graftDrawing DY hbd
  have hE₁₂ : Disjoint W.E₁ W.E₂ := cap.disjoint_D.mono
    (W.E₁_subset.trans (discInt_subset _)) (W.E₂_subset.trans (discInt_subset _))
  obtain ⟨hQ, hcuffsQ, hneQ, hbdQ⟩ := cylinder_complement_two_discs cap.isClosedSurface
    cap.isSphere W.isClosedDisc_E₁ W.isClosedDisc_E₂ hE₁₂
  have : Nonempty (discComplement (![W.E₁, W.E₂] : Fin 2 → Set cap.Z)) := hQ.nonempty
  obtain ⟨hord, hins, hoffA, hoffB⟩ := cap.collar_order hS hA hB hAB hle
    W.isClosedDisc_E₁ W.isClosedDisc_E₂ W.E₁_subset W.E₂_subset
  apply isGraftSimulatedIn_of_rootLeafGraft
  refine isGraftSimulatedIn_of_cylinder_minor_configuration hQ.1 hQ.2 hcuffsQ hneQ gdY gdX
    ?_ ?_ ?_ hord hins hoffA hoffB ?_ ?_ ?_ ?_
  · -- both drawings meet the boundary of `Q` at the ends of the spokes
    rw [hgdX, hgdY, drawingInSubspace_V, drawingInSubspace_V, hbdQ, ← preimage_inter,
      ← preimage_inter, W.V_inter_discBd_eq hPbd hXV, W.V_inter_discBd_eq hPbd hYV]
  · rw [hgdX]; exact W.isNormal_liftEdge rfl hHXQ hXU hXV hNA
  · rw [hgdX]; exact W.isNormal_liftEdge rfl hHXQ hXU hXV hNB
  · intro F hNF hF hFA hFB
    rw [hgdX] at hNF ⊢
    obtain ⟨L, hL, hNL, hLA, hLB, hcount⟩ :=
      W.exists_line_le_ncard hS hHXQ hXU hXV hA hB hAB hle hNF hF hFA hFB
    exact (hline L hNL hL hLA hLB).trans hcount
  · rw [hgdX]
    exact hcentral.trans (W.maxDisjointPaths_le hHXQ hXV hXE A B)
  · rw [hgdX]
    refine W.ncard_cuff_le rfl hHXQ hXU hXV hXE
      (fun x hx => ⟨hx.1, cap.bd_eq ▸ .inl hx.2⟩)
      (fun x hx => W.q_mem₁ x ⟨hx.1, cap.bd_eq ▸ .inl hx.2⟩ hx.2) ?_ hsk₁
    exact W.V_inter_discBd_subset rfl hXV cap.bd_eq hE₁₂ (.inl rfl) W.q_mem₂
  · rw [hgdX]
    refine W.ncard_cuff_le rfl hHXQ hXU hXV hXE
      (fun x hx => ⟨hx.1, cap.bd_eq ▸ .inr hx.2⟩)
      (fun x hx => W.q_mem₂ x ⟨hx.1, cap.bd_eq ▸ .inr hx.2⟩ hx.2) ?_ hsk₂
    exact W.V_inter_discBd_subset rfl hXV (cap.bd_eq.trans (union_comm _ _)) hE₁₂.symm
      (.inr rfl) W.q_mem₁

end GraphMinor.GM08
