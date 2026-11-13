module

public import GraphMinor.GM08.Section15Tube
import GraphMinor.GM08.Section15Menger
import GraphMinor.GM08.Section15FramingSides
import GraphMinor.GM08.Section15PuncturedCylinder
import GraphMinor.GM08.Section15PuncturedDrawing
import GraphMinor.GM08.Section15FramingDrawing
import GraphMinor.GM08.Section15CappedArc
import GraphMinor.GM08.Section15PuncturedArc
import GraphMinor.GM07.CylinderCap

/-!
# A short framing with all roots on cylinder cuffs

Cap the original cylinder, separate its two empty outer disc sides,
and read the unchanged graph in their cylindrical complement. Exactly
the original framing roots lie on its cuffs. The original short witness
and the empty sides give a bounded normal line between the adjusted
discs, hence a proper short arc between the new cuffs. This is the
geometric construction of the disc graft in VIII (15.4).
-/

public section

namespace GraphMinor.GM08

open Set GraphMinor.Surface

universe u v

/-- A short tubular framing can be drawn with all its graft roots on
the cylinder cuffs and with a proper normal cuff-joining arc meeting
fewer than `s` vertices. This proves the geometric short-tube step
in Graph Minors VIII (15.4), page 282, including touching framing hoops. -/
theorem Tube.Framing.exists_short_cylinder_drawing {S : Type} [TopologicalSpace S]
    {α : Type u} {β : Type v} {τ : Tube S} {X : Graft α β}
    (fr : τ.Framing X) {s : ℕ} (hs : τ.length < s) :
    ∃ (Y : Type) (_ : TopologicalSpace Y), IsCylinder Y ∧
      ∃ (gd : GraftDrawing X.G X.T Y) (C D J : Set Y) (a b : Y),
        C ∈ cuffs Y ∧ D ∈ cuffs Y ∧ C ≠ D ∧ IsLineWithEnds J a b ∧
        a ∈ C ∧ b ∈ D ∧ J ∩ bd Y = {a, b} ∧ gd.drawing.IsNormal J ∧
        (J ∩ gd.drawing.V).ncard < s := by
  classical
  have : T2Space S := τ.t2Space
  have : CompactSpace S := τ.isCylinder.compactSpace
  have : Nonempty S := τ.isCylinder.nonempty
  obtain ⟨I, a, b, hI, ha, hb, hNI, _, hIs⟩ := τ.length_lt_iff.mp hs
  obtain ⟨cap, hle⟩ := CylinderSphereCap.exists_oriented τ.isCylinder
    τ.isHoop_F₁ τ.isHoop_F₂ τ.laminar
  have : T2Space cap.Z := cap.t2Space_Z
  have : ConnectedSpace cap.Z := cap.connectedSpace
  obtain ⟨G, hm⟩ := GM07.exists_image_matched cap.isClosedEmbedding τ.Γ
  have hGU : G.U = cap.j '' τ.Γ.U := by simpa using hm.image_U.symm
  have hGV : G.V = cap.j '' τ.Γ.V := by simpa using hm.image_V.symm
  have image_normal : ∀ A : Set S, τ.Γ.IsNormal A → G.IsNormal (cap.j '' A) := by
    intro A hn
    rintro x ⟨⟨y, hy, rfl⟩, hxG⟩
    rw [hGU] at hxG
    obtain ⟨z, hz, heq⟩ := hxG
    have hyU : y ∈ τ.Γ.U := cap.inj heq ▸ hz
    rw [hGV]
    exact mem_image_of_mem cap.j (hn ⟨hy, hyU⟩)
  let D := cap.disc₁ τ.isCylinder.1 τ.isHoop_F₁
  let R := cap.disc₂ τ.isCylinder.1 τ.isHoop_F₂
  obtain ⟨hD, _, hbD, _, _, _, _, _⟩ := cap.disc₁_disc₂_spec τ.isCylinder.1 τ.isHoop_F₁
  obtain ⟨_, hR, _, hbR, _, hcapR, _, _⟩ := cap.disc₁_disc₂_spec τ.isCylinder.1 τ.isHoop_F₂
  obtain ⟨E, hE, hER, hDE, hoffD, hoffE, hnE, hroots⟩ :=
    τ.exists_separated_framing_sides cap hle G hGU hGV
  have hnD : G.IsNormal (discBd D) := by rw [hbD]; exact image_normal _ τ.isNormal_F₁
  have hnEB : G.IsNormal (discBd E) := fun x hx => hnE ⟨discBd_subset E hx.1, hx.2⟩
  obtain ⟨hcyl, hcuffs, hne, _⟩ := cylinder_complement_two_discs
    cap.isClosedSurface cap.isSphere hD hE hDE
  let P : Fin 2 → Set cap.Z := ![D, E]
  let Q := GM12.discComplement P
  obtain ⟨H, hHU, hHV, hH, hrootQ, i, hiv⟩ := exists_drawing_in_two_disc_complement
    cap.isClosedSurface G hD hE hDE hoffD hoffE hnD hnEB
  obtain ⟨gd, hgd⟩ := exists_graftDrawing_of_framing_image fr cap.isClosedEmbedding.isEmbedding
    hm H hH i Subtype.val_injective hiv (hrootQ.trans hroots)
  have hRoff : Disjoint (discInt R) G.U := by
    refine disjoint_left.mpr ?_
    intro x hx hxG
    rw [hGU] at hxG
    obtain ⟨y, hy, rfl⟩ := hxG
    have hycore := τ.U_subset hy
    rw [cap.cylinderBetween_eq_of_disc₁_subset τ.isCylinder τ.isHoop_F₁ τ.isHoop_F₂ hle] at hycore
    exact hx.2 (hbR.symm ▸ (hcapR ▸ ⟨hycore.1, hx.1⟩))
  have hja : cap.j a ∈ D := discBd_subset _ (hbD ▸ mem_image_of_mem cap.j ha)
  have hjb : cap.j b ∈ R := discBd_subset _ (hbR ▸ mem_image_of_mem cap.j hb)
  obtain ⟨L, x, y, hL, hx, hy, hNL, hLD, hLE, hcount⟩ :=
    exists_normal_line_between_inner_discs cap.isClosedSurface cap.isSphere hD hE hDE
      hD hR subset_rfl hER hoffD hRoff (GM07.image_line cap.isClosedEmbedding.isEmbedding hI)
      hja hjb (image_normal _ hNI)
  have hsmall : (L ∩ G.V).ncard < s := by
    apply hcount.trans_lt
    rw [hGV, ← image_inter cap.inj, ncard_image_of_injective _ cap.inj]
    exact hIs
  obtain ⟨J, u, v, hJ, hu, hv, hJbd, hNJ, hJcount⟩ :=
    exists_proper_arc_in_two_disc_complement cap.isClosedSurface cap.isSphere hD hE hDE
      G H hHU hHV hL hx hy hNL hLD hLE
  let C : Set Q := Subtype.val ⁻¹' discBd D
  let F : Set Q := Subtype.val ⁻¹' discBd E
  have hC : C ∈ cuffs Q := by rw [hcuffs]; exact .inl rfl
  have hF : F ∈ cuffs Q := by rw [hcuffs]; exact .inr rfl
  refine ⟨Q, inferInstance, hcyl, gd, C, F, J, u, v, hC, hF, hne, hJ, hu, hv, hJbd, ?_, ?_⟩
  · rwa [hgd]
  · rw [hgd]
    exact hJcount.trans_lt hsmall

end GraphMinor.GM08
