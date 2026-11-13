module

public import GraphMinor.GM08.Section15Defs
public import GraphMinor.GM08.Section15PuncturedCylinder
public import GraphMinor.GM07.Section9MoveOff
import GraphMinor.GM08.Section15Tube
import GraphMinor.GM07.Section9DiscSphere
import GraphMinor.GM07.Section9Cylinder
import GraphMinor.GM07.Section5a
import GraphMinor.GM12.Section3SubspaceArcs
import GraphMinor.GM12.Section3CapOneDisc
import GraphMinor.GM12.Section3CapComparison
import GraphMinor.GM12.Section3FillOneDisc

/-!
# Two hoops seen in a larger cylinder

In the proof of (17.2) the two hoops `A` and `B` given by boundary linking
may touch the cuffs of the cylinder `S`, while VII (9.3) needs hoops off the
boundary. So we cap `S` to a sphere and remove two smaller discs `E₁, E₂`
from the two caps. What is left is a larger cylinder `Q` that contains the
image of `S` away from its boundary.

This file proves the facts about `Q` that only concern the hoops:
the images of `B` and `A` lie in `Q` in the order required by VII (9.3)(i),
they avoid the boundary of `Q`, and every arc of `Q` from one image to the
other contains the image of an arc of `S` from `A` to `B`.
-/

public section

namespace GraphMinor.GM08

open Set Topology GraphMinor.Surface GraphMinor.GM07 GraphMinor.GM12

variable {S : Type} [TopologicalSpace S]

/-- The first cap disc of a cylinder cap is the side of its first cuff that
contains it. -/
theorem CylinderSphereCap.disc₁_C₁ (cap : CylinderSphereCap S) (hS : IsSurface S) :
    cap.disc₁ hS (cap.isHoop_C₁ hS) = cap.D₁ := by
  obtain ⟨h1, h2, hb1, hb2, -, hcap, hD1, hD2⟩ := cap.disc₁_disc₂_spec hS (cap.isHoop_C₁ hS)
  exact (cap.hoop_discs_unique h1 h2 hb1 hb2 hcap hD1 hD2 cap.isClosedDisc_D₁ h2
    cap.discBd_D₁ hb2 Subset.rfl hD2).1.symm

/-- Facts in the capped sphere about two disjoint hoops `B`, `A` in the order
`C₁, B, A, C₂`. -/
private theorem hoop_pair_facts (cap : CylinderSphereCap S) (hS : IsCylinder S)
    {A B : Set S} (hA : IsHoop A) (hB : IsHoop B) (hAB : Disjoint A B)
    (hle : cap.disc₁ hS.1 hB ⊆ cap.disc₁ hS.1 hA) :
    Disjoint (cap.j '' A) (cap.disc₁ hS.1 hB) ∧
    cap.j '' B ⊆ cap.disc₁ hS.1 hA ∧ Disjoint (cap.j '' B) (cap.j '' A) ∧
    cap.j '' A ⊆ cap.disc₂ hS.1 hB := by
  obtain ⟨-, -, hbB, -, hcupB, hcapB, -, -⟩ := cap.disc₁_disc₂_spec hS.1 hB
  have hside : A \ B ⊆ cap.side₂ hS.1 hB :=
    (cap.subset_side₂_iff_disc₁_subset hS.1 hB hA).mpr hle
  have h1 : Disjoint (cap.j '' A) (cap.disc₁ hS.1 hB) := by
    refine disjoint_left.mpr ?_
    rintro _ ⟨a, ha, rfl⟩ hd
    have haB : a ∉ B := disjoint_left.mp hAB ha
    have h2 := hside ⟨ha, haB⟩
    rw [cap.side₂_eq_preimage_diff] at h2
    have hjB : cap.j a ∈ cap.j '' B := hcapB ▸ ⟨hd, h2.1⟩
    exact h2.2 hjB
  have h2 : cap.j '' B ⊆ cap.disc₁ hS.1 hA :=
    (hbB ▸ discBd_subset _).trans hle
  have h3 : Disjoint (cap.j '' B) (cap.j '' A) := (disjoint_image_iff cap.inj).mpr hAB.symm
  refine ⟨h1, h2, h3, fun z hz => ?_⟩
  have hz' : z ∈ cap.disc₁ hS.1 hB ∪ cap.disc₂ hS.1 hB := hcupB ▸ mem_univ z
  exact hz'.resolve_left (disjoint_left.mp h1 hz)

/-- The disc complement `Q` of two discs `E₁ ⊆ int D₁` and `E₂ ⊆ int D₂` contains
the image of `S`. -/
theorem CylinderSphereCap.range_subset_discComplement (cap : CylinderSphereCap S)
    {E₁ E₂ : Set cap.Z} (hE₁ : IsClosedDisc E₁) (hE₂ : IsClosedDisc E₂)
    (hE₁D : E₁ ⊆ discInt cap.D₁) (hE₂D : E₂ ⊆ discInt cap.D₂) :
    range cap.j ⊆ discComplement (![E₁, E₂] : Fin 2 → Set cap.Z) := by
  have : T2Space cap.Z := cap.t2Space_Z
  have hP : ∀ i, IsClosedDisc ((![E₁, E₂] : Fin 2 → Set cap.Z) i) := by
    intro i; fin_cases i <;> assumption
  have hdis : Pairwise (fun i j => Disjoint ((![E₁, E₂] : Fin 2 → Set cap.Z) i)
      ((![E₁, E₂] : Fin 2 → Set cap.Z) j)) := by
    have hd : Disjoint E₁ E₂ := (cap.disjoint_D.mono (hE₁D.trans (discInt_subset _))
      (hE₂D.trans (discInt_subset _)))
    intro i j hij
    fin_cases i <;> fin_cases j
    · exact (hij rfl).elim
    · exact hd
    · exact hd.symm
    · exact (hij rfl).elim
  rintro _ ⟨x, rfl⟩
  rw [mem_discComplement_iff cap.isClosedSurface _ hP hdis]
  intro i hi
  fin_cases i
  · exact disjoint_left.mp cap.disjoint_range_discInt_D₁ ⟨x, rfl⟩
      ((hE₁D (discInt_subset _ hi)))
  · exact disjoint_left.mp cap.disjoint_range_discInt_D₂ ⟨x, rfl⟩
      ((hE₂D (discInt_subset _ hi)))

/-- **The order of the hoops in the larger cylinder.** Let `B` and `A` be disjoint
hoops of `S` in the order `C₁, B, A, C₂`, and let `Q` be the cap sphere with the
interiors of `E₁ ⊆ int D₁` and `E₂ ⊆ int D₂` removed. Then in `Q`, the images of
`B` and `A` are in the order of VII (9.3)(i), every point of the image of `B` is
inside the image of `A`, and both images avoid the boundary of `Q`. -/
theorem CylinderSphereCap.collar_order (cap : CylinderSphereCap S) (hS : IsCylinder S)
    {A B : Set S} (hA : IsHoop A) (hB : IsHoop B) (hAB : Disjoint A B)
    (hle : cap.disc₁ hS.1 hB ⊆ cap.disc₁ hS.1 hA)
    {E₁ E₂ : Set cap.Z} (hE₁ : IsClosedDisc E₁) (hE₂ : IsClosedDisc E₂)
    (hE₁D : E₁ ⊆ discInt cap.D₁) (hE₂D : E₂ ⊆ discInt cap.D₂) :
    let Q := discComplement (![E₁, E₂] : Fin 2 → Set cap.Z)
    CylinderOArcsInOrder ((Subtype.val : Q → cap.Z) ⁻¹' discBd E₁)
        (liftEdge cap.j Q B) (liftEdge cap.j Q A) ((Subtype.val : Q → cap.Z) ⁻¹' discBd E₂) ∧
      (∀ x ∈ liftEdge cap.j Q B, IsPointInsideSurroundingOArc
        ((Subtype.val : Q → cap.Z) ⁻¹' discBd E₁) (liftEdge cap.j Q A) x) ∧
      Disjoint (liftEdge cap.j Q A) (bd Q) ∧ Disjoint (liftEdge cap.j Q B) (bd Q) := by
  intro Q
  have : T2Space cap.Z := cap.t2Space_Z
  have : ConnectedSpace cap.Z := cap.connectedSpace
  have hj := cap.isClosedEmbedding
  obtain ⟨hAB₁, hBA₁, hBA, hAB₂⟩ := hoop_pair_facts cap hS hA hB hAB hle
  obtain ⟨hdA₁, -, hbA₁, -, -, hcapA, hD₁A, hD₂A⟩ := cap.disc₁_disc₂_spec hS.1 hA
  obtain ⟨hdB₁, -, hbB₁, -, -, hcapB, hD₁B, hD₂B⟩ := cap.disc₁_disc₂_spec hS.1 hB
  let P : Fin 2 → Set cap.Z := ![E₁, E₂]
  have hP : ∀ i, IsClosedDisc (P i) := by intro i; fin_cases i <;> assumption
  have hE₁₂ : Disjoint E₁ E₂ := (cap.disjoint_D.mono (hE₁D.trans (discInt_subset _))
      (hE₂D.trans (discInt_subset _)))
  have hdis : Pairwise (fun i j => Disjoint (P i) (P j)) := by
    intro i j hij
    fin_cases i <;> fin_cases j
    · exact (hij rfl).elim
    · exact hE₁₂
    · exact hE₁₂.symm
    · exact (hij rfl).elim
  have hrange : range cap.j ⊆ Q := cap.range_subset_discComplement hE₁ hE₂ hE₁D hE₂D
  have hE₁r : Disjoint E₁ (range cap.j) :=
    (cap.disjoint_range_discInt_D₁.mono_right hE₁D).symm
  have hE₂r : Disjoint E₂ (range cap.j) :=
    (cap.disjoint_range_discInt_D₂.mono_right hE₂D).symm
  have hjA : cap.j '' A ⊆ range cap.j := image_subset_range _ _
  have hjB : cap.j '' B ⊆ range cap.j := image_subset_range _ _
  obtain ⟨hQ, hcuffs, hne, hbdQ⟩ := cylinder_complement_two_discs
    cap.isClosedSurface cap.isSphere hE₁ hE₂ hE₁₂
  have hQs : IsSurface Q := hQ.1
  have hC₁ : ((Subtype.val : Q → cap.Z) ⁻¹' discBd E₁) ∈ cuffs Q := by
    rw [hcuffs]; exact .inl rfl
  have hC₂ : ((Subtype.val : Q → cap.Z) ⁻¹' discBd E₂) ∈ cuffs Q := by
    rw [hcuffs]; exact .inr rfl
  have hval_emb : IsClosedEmbedding (Subtype.val : Q → cap.Z) :=
    isClosed_closure.isClosedEmbedding_subtypeVal
  have hAQ : cap.j '' A ⊆ Q := hjA.trans hrange
  have hBQ : cap.j '' B ⊆ Q := hjB.trans hrange
  have hOA : IsOArc (liftEdge cap.j Q A) := isOArc_liftEdge hj.isEmbedding hAQ hA.1
  have hOB : IsOArc (liftEdge cap.j Q B) := isOArc_liftEdge hj.isEmbedding hBQ hB.1
  have hvalA : (Subtype.val : Q → cap.Z) '' liftEdge cap.j Q A = cap.j '' A :=
    subtype_image_liftEdge_of_subset hAQ
  have hvalB : (Subtype.val : Q → cap.Z) '' liftEdge cap.j Q B = cap.j '' B :=
    subtype_image_liftEdge_of_subset hBQ
  -- points of the removed discs
  obtain ⟨p₁, hp₁⟩ := hE₁.nonempty_discInt
  obtain ⟨p₂, hp₂⟩ := hE₂.nonempty_discInt
  have hp₁Q : p₁ ∉ range (Subtype.val : Q → cap.Z) := by
    rw [Subtype.range_val, mem_discComplement_iff cap.isClosedSurface P hP hdis]
    intro h
    exact h 0 hp₁
  have hp₂Q : p₂ ∉ range (Subtype.val : Q → cap.Z) := by
    rw [Subtype.range_val, mem_discComplement_iff cap.isClosedSurface P hP hdis]
    intro h
    exact h 1 hp₂
  have hE₁B : E₁ ⊆ cap.disc₁ hS.1 hB := (hE₁D.trans (discInt_subset _)).trans hD₁B
  have hE₁A : E₁ ⊆ cap.disc₁ hS.1 hA := hE₁B.trans hle
  -- a disc side meets `E₂` only in the image of `S`, so not at all
  have hE₂_off : ∀ {F : Set S} (hF : IsHoop F), Disjoint (cap.disc₁ hS.1 hF) E₂ := by
    intro F hF
    obtain ⟨-, -, -, -, -, hcap, -, hD₂⟩ := cap.disc₁_disc₂_spec hS.1 hF
    refine disjoint_left.mpr fun z hz₁ hzE => ?_
    have hz : z ∈ cap.j '' F := hcap ▸ ⟨hz₁, hD₂ ((hE₂D.trans (discInt_subset _)) hzE)⟩
    exact disjoint_left.mp hE₂r hzE (image_subset_range _ _ hz)
  have hp₂A : p₂ ∉ cap.disc₁ hS.1 hA := fun h =>
    disjoint_left.mp (hE₂_off hA) h (discInt_subset _ hp₂)
  have hp₂B : p₂ ∉ cap.disc₁ hS.1 hB := fun h =>
    disjoint_left.mp (hE₂_off hB) h (discInt_subset _ hp₂)
  have hnullA : ¬ IsNullHomotopicOArc (liftEdge cap.j Q A) :=
    not_null_of_separating_u hQs cap.isSphere hval_emb hOA hdA₁ (hbA₁.trans hvalA.symm)
      (hE₁A (discInt_subset _ hp₁)) hp₂A hp₁Q hp₂Q
  have hnullB : ¬ IsNullHomotopicOArc (liftEdge cap.j Q B) :=
    not_null_of_separating_u hQs cap.isSphere hval_emb hOB hdB₁ (hbB₁.trans hvalB.symm)
      (hE₁B (discInt_subset _ hp₁)) hp₂B hp₁Q hp₂Q
  have hplanA : ¬ GM11.IsPlanar (liftEdge cap.j Q A) := fun hp =>
    hnullA ((isPlanar_iff_isNullHomotopicOArc_of_isOArc hQs hOA).mp hp)
  have hplanB : ¬ GM11.IsPlanar (liftEdge cap.j Q B) := fun hp =>
    hnullB ((isPlanar_iff_isNullHomotopicOArc_of_isOArc hQs hOB).mp hp)
  -- cap the first new cuff
  obtain ⟨j_cap, hcap₁, hj_cap_val⟩ :=
    exists_cap_discComplement_cuff cap.isClosedSurface P hP hdis 0
  let T := discComplement (fun k : {k : Fin 2 // k ≠ 0} => P k.val)
  have hsubT : ∀ {F : Set S} (hF : IsHoop F), cap.disc₁ hS.1 hF ⊆ T := by
    intro F hF
    change cap.disc₁ hS.1 hF ⊆ discComplement (fun k : {k : Fin 2 // k ≠ 0} => P k.val)
    rw [discComplement_except_eq_union P hP hdis 0]
    intro z hz
    by_cases hzE : z ∈ E₁
    · exact Or.inr hzE
    · left
      rw [mem_discComplement_iff cap.isClosedSurface P hP hdis]
      intro i
      fin_cases i
      · exact fun h => hzE h.1
      · exact fun h => disjoint_left.mp (hE₂_off hF) hz h.1
  have hjcap : ∀ F : Set S, cap.j '' F ⊆ Q →
      j_cap '' liftEdge cap.j Q F = (Subtype.val : T → cap.Z) ⁻¹' (cap.j '' F) := by
    intro F hFQ
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      rw [mem_preimage, hj_cap_val]
      exact hx
    · intro hy
      have hyQ : y.val ∈ Q := hFQ hy
      exact ⟨⟨y.val, hyQ⟩, hy, Subtype.ext (hj_cap_val ⟨y.val, hyQ⟩)⟩
  obtain ⟨hdAT, hbAT⟩ := isClosedDisc_subtype_preimage (hsubT hA) hdA₁
  obtain ⟨hdBT, hbBT⟩ := isClosedDisc_subtype_preimage (hsubT hB) hdB₁
  rw [hbA₁, ← hjcap A hAQ] at hbAT
  rw [hbB₁, ← hjcap B hBQ] at hbBT
  have hplanA₁ : IsPlanarInCappedCuff ((Subtype.val : Q → cap.Z) ⁻¹' discBd E₁)
      (liftEdge cap.j Q A) :=
    isPlanarInCappedCuff_of_one_cap hQs hcap₁
      ⟨_, hdAT, hbAT ▸ discBd_subset _⟩
  have hplanB₁ : IsPlanarInCappedCuff ((Subtype.val : Q → cap.Z) ⁻¹' discBd E₁)
      (liftEdge cap.j Q B) :=
    isPlanarInCappedCuff_of_one_cap hQs hcap₁
      ⟨_, hdBT, hbBT ▸ discBd_subset _⟩
  have hSurrA : SurroundsCuff (liftEdge cap.j Q A)
      ((Subtype.val : Q → cap.Z) ⁻¹' discBd E₁) := ⟨hC₁, hplanA₁, hplanA⟩
  have hSurrB : SurroundsCuff (liftEdge cap.j Q B)
      ((Subtype.val : Q → cap.Z) ⁻¹' discBd E₁) := ⟨hC₁, hplanB₁, hplanB⟩
  have hinside : ∀ x ∈ liftEdge cap.j Q B, IsPointInsideSurroundingOArc
      ((Subtype.val : Q → cap.Z) ⁻¹' discBd E₁) (liftEdge cap.j Q A) x := by
    intro x hx
    apply isPointInsideSurroundingOArc_of_one_cap hQs hOA hSurrA hcap₁
    have hOAT : IsOArc (j_cap '' liftEdge cap.j Q A) := hbAT ▸ hdAT.isOArc_discBd
    refine ⟨isNullHomotopicOArcIn_of_subset_disc hOAT (subset_univ _) hdAT
      (hbAT ▸ discBd_subset _), _, hdAT, hbAT, ?_, ?_⟩
    · rw [mem_preimage, hj_cap_val]
      exact hBA₁ hx
    · rw [hjcap A hAQ, mem_preimage, hj_cap_val]
      exact disjoint_left.mp hBA hx
  have hoffA : Disjoint (liftEdge cap.j Q A) (bd Q) := by
    rw [hbdQ]
    refine disjoint_left.mpr fun x hx hxb => ?_
    rcases hxb with h | h
    · exact disjoint_left.mp hE₁r (discBd_subset _ h) (hjA hx)
    · exact disjoint_left.mp hE₂r (discBd_subset _ h) (hjA hx)
  have hoffB : Disjoint (liftEdge cap.j Q B) (bd Q) := by
    rw [hbdQ]
    refine disjoint_left.mpr fun x hx hxb => ?_
    rcases hxb with h | h
    · exact disjoint_left.mp hE₁r (discBd_subset _ h) (hjB hx)
    · exact disjoint_left.mp hE₂r (discBd_subset _ h) (hjB hx)
  refine ⟨⟨hC₁, hC₂, hne, hOA, hOB, disjoint_liftEdge cap.inj Q hAB, hnullA, hnullB,
    hSurrB, hSurrA, fun x hx => Or.inr ⟨_, hC₁, hinside x hx⟩⟩, hinside, hoffA, hoffB⟩

/-- On a path from a closed set `X` to a disjoint closed set `Y`, there is a
segment from `X` to `Y` that meets `X` only at its start and `Y` only at its end. -/
theorem exists_segment_between {Z : Type} [TopologicalSpace Z] {g : unitInterval → Z}
    (hg : Continuous g) {X Y : Set Z} (hX : IsClosed X) (hY : IsClosed Y)
    (hXY : Disjoint X Y) {s t : unitInterval} (hst : s < t) (hs : g s ∈ X) (ht : g t ∈ Y) :
    ∃ u v, u < v ∧ g u ∈ X ∧ g v ∈ Y ∧ (∀ w ∈ Ioc u v, g w ∉ X) ∧
      (∀ w ∈ Ico u v, g w ∉ Y) := by
  have hKX : IsCompact (Icc s t ∩ g ⁻¹' X) := (isClosed_Icc.inter (hX.preimage hg)).isCompact
  obtain ⟨u, ⟨⟨hsu, hut⟩, hu⟩, hugr⟩ := hKX.exists_isGreatest ⟨s, ⟨le_rfl, hst.le⟩, hs⟩
  have hKY : IsCompact (Icc u t ∩ g ⁻¹' Y) := (isClosed_Icc.inter (hY.preimage hg)).isCompact
  obtain ⟨v, ⟨⟨huv, hvt⟩, hv⟩, hvle⟩ := hKY.exists_isLeast ⟨t, ⟨hut, le_rfl⟩, ht⟩
  have hne : u ≠ v := fun h => disjoint_left.mp hXY hu (h ▸ hv)
  refine ⟨u, v, lt_of_le_of_ne huv hne, hu, hv, ?_, ?_⟩
  · rintro w ⟨hwu, hwv⟩ hw
    exact absurd (hugr ⟨⟨hsu.trans hwu.le, hwv.trans hvt⟩, hw⟩) (not_le.mpr hwu)
  · rintro w ⟨hwu, hwv⟩ hw
    exact absurd (hvle ⟨⟨hwu, hwv.le.trans hvt⟩, hw⟩) (not_le.mpr hwv)

/-- **Arcs between the two hoops in a larger surface.** Let `Q` be any subset of
the cap sphere, and let `B`, `A` be disjoint hoops in
the order `C₁, B, A, C₂`. Every arc of `Q` that meets the images of both `A` and
`B` contains the image of an arc of `S` that meets both `A` and `B`.
The reason is that a segment of the arc from the image of `A` to the image of `B`
that meets them only at its ends stays between them, and the part of the
sphere between them lies in the image of `S`. -/
theorem CylinderSphereCap.exists_line_of_collar_line (cap : CylinderSphereCap S)
    (hS : IsCylinder S) {A B : Set S} (hA : IsHoop A) (hB : IsHoop B) (hAB : Disjoint A B)
    (hle : cap.disc₁ hS.1 hB ⊆ cap.disc₁ hS.1 hA) {Q : Set cap.Z}
    {F : Set Q} (hF : IsLine F)
    (hFA : (F ∩ liftEdge cap.j Q A).Nonempty) (hFB : (F ∩ liftEdge cap.j Q B).Nonempty) :
    ∃ L : Set S, IsLine L ∧ (L ∩ A).Nonempty ∧ (L ∩ B).Nonempty ∧
      cap.j '' L ⊆ (Subtype.val : Q → cap.Z) '' F := by
  have : T2Space cap.Z := cap.t2Space_Z
  have : T2Space S := cap.isClosedEmbedding.isEmbedding.t2Space
  have hj := cap.isClosedEmbedding
  obtain ⟨hAB₁, hBA₁, hBA, hAB₂⟩ := hoop_pair_facts cap hS hA hB hAB hle
  obtain ⟨hdA₁, hdA₂, hbA₁, -, hcupA, hcapA, hD₁A, hD₂A⟩ := cap.disc₁_disc₂_spec hS.1 hA
  obtain ⟨hdB₁, hdB₂, hbB₁, -, hcupB, hcapB, hD₁B, hD₂B⟩ := cap.disc₁_disc₂_spec hS.1 hB
  have hcA : IsClosed (cap.j '' A) := (hA.1.isCompact.image hj.continuous).isClosed
  have hcB : IsClosed (cap.j '' B) := (hB.1.isCompact.image hj.continuous).isClosed
  have hcupA' : ∀ z, z ∈ cap.disc₁ hS.1 hA ∪ cap.disc₂ hS.1 hA := fun z => hcupA ▸ mem_univ z
  have hcupB' : ∀ z, z ∈ cap.disc₁ hS.1 hB ∪ cap.disc₂ hS.1 hB := fun z => hcupB ▸ mem_univ z
  have hjA₁ : cap.j '' A ⊆ cap.disc₁ hS.1 hA := hcapA ▸ inter_subset_left
  have hjB₂ : cap.j '' B ⊆ cap.disc₂ hS.1 hB := hcapB ▸ inter_subset_right
  -- a connected set avoiding one image and meeting the other stays on one side
  have hsideA : ∀ K : Set cap.Z, IsPreconnected K → Disjoint K (cap.j '' A) →
      (K ∩ cap.j '' B).Nonempty → K ⊆ cap.disc₁ hS.1 hA := by
    intro K hK hKA hKB
    have hsub : K ⊆ (cap.disc₂ hS.1 hA)ᶜ ∪ (cap.disc₁ hS.1 hA)ᶜ := by
      intro z hz
      by_contra h
      simp only [mem_union, mem_compl_iff, not_or, not_not] at h
      have hz' : z ∈ cap.j '' A := hcapA ▸ ⟨h.2, h.1⟩
      exact disjoint_left.mp hKA hz hz'
    have hdis : Disjoint (cap.disc₂ hS.1 hA)ᶜ (cap.disc₁ hS.1 hA)ᶜ := by
      rw [disjoint_compl_left_iff_subset, ← compl_subset_comm]
      intro z hz
      exact (hcupA' z).resolve_right hz
    obtain ⟨z, hzK, hzB⟩ := hKB
    have hz₂ : z ∉ cap.disc₂ hS.1 hA := fun h => by
      have hz' : z ∈ cap.j '' A := hcapA ▸ ⟨hBA₁ hzB, h⟩
      exact disjoint_left.mp hBA hzB hz'
    have := hK.subset_left_of_subset_union hdA₂.isClosed.isOpen_compl
      hdA₁.isClosed.isOpen_compl hdis hsub ⟨z, hzK, hz₂⟩
    intro y hy
    exact (hcupA' y).resolve_right (this hy)
  have hsideB : ∀ K : Set cap.Z, IsPreconnected K → Disjoint K (cap.j '' B) →
      (K ∩ cap.j '' A).Nonempty → K ⊆ cap.disc₂ hS.1 hB := by
    intro K hK hKB hKA
    have hsub : K ⊆ (cap.disc₁ hS.1 hB)ᶜ ∪ (cap.disc₂ hS.1 hB)ᶜ := by
      intro z hz
      by_contra h
      simp only [mem_union, mem_compl_iff, not_or, not_not] at h
      have hz' : z ∈ cap.j '' B := hcapB ▸ ⟨h.1, h.2⟩
      exact disjoint_left.mp hKB hz hz'
    have hdis : Disjoint (cap.disc₁ hS.1 hB)ᶜ (cap.disc₂ hS.1 hB)ᶜ := by
      rw [disjoint_compl_left_iff_subset, ← compl_subset_comm]
      intro z hz
      exact (hcupB' z).resolve_left hz
    obtain ⟨z, hzK, hzA⟩ := hKA
    have hz₁ : z ∉ cap.disc₁ hS.1 hB := fun h => disjoint_left.mp hAB₁ hzA h
    have := hK.subset_left_of_subset_union hdB₁.isClosed.isOpen_compl
      hdB₂.isClosed.isOpen_compl hdis hsub ⟨z, hzK, hz₁⟩
    intro y hy
    exact (hcupB' y).resolve_left (this hy)
  -- the part of the sphere between the two images lies in the image of `S`
  have hR : ∀ z, z ∈ cap.disc₁ hS.1 hA → z ∈ cap.disc₂ hS.1 hB → z ∈ range cap.j := by
    intro z hzA hzB
    by_contra hz
    have hzD : z ∈ cap.D₁ ∪ cap.D₂ := by
      have h : z ∈ range cap.j ∪ cap.D₁ ∪ cap.D₂ := cap.union_eq ▸ mem_univ z
      rcases h with (h | h) | h
      · exact absurd h hz
      · exact .inl h
      · exact .inr h
    rcases hzD with h | h
    · have h' : z ∈ cap.j '' B := hcapB ▸ ⟨hD₁B h, hzB⟩
      exact hz (image_subset_range _ _ h')
    · have h' : z ∈ cap.j '' A := hcapA ▸ ⟨hzA, hD₂A h⟩
      exact hz (image_subset_range _ _ h')
  -- parametrize the arc
  obtain ⟨e⟩ := hF
  let f : unitInterval → Q := fun t => (e t).1
  let g : unitInterval → cap.Z := fun t => (f t).1
  have hfc : Continuous f := continuous_subtype_val.comp e.continuous
  have hfi : Function.Injective f := Subtype.val_injective.comp e.injective
  have hgc : Continuous g := continuous_subtype_val.comp hfc
  have finish : ∀ u v : unitInterval, u < v →
      (∀ w ∈ Icc u v, g w ∈ cap.disc₁ hS.1 hA ∧ g w ∈ cap.disc₂ hS.1 hB) →
      (∃ w ∈ Icc u v, g w ∈ cap.j '' A) → (∃ w ∈ Icc u v, g w ∈ cap.j '' B) →
      ∃ L : Set S, IsLine L ∧ (L ∩ A).Nonempty ∧ (L ∩ B).Nonempty ∧
        cap.j '' L ⊆ (Subtype.val : Q → cap.Z) '' F := by
    intro u v huv hin ⟨wa, hwa, a, ha, hga⟩ ⟨wb, hwb, b, hb, hgb⟩
    have hsub : (Subtype.val : Q → cap.Z) '' (f '' Icc u v) ⊆ range cap.j := by
      rintro _ ⟨_, ⟨w, hw, rfl⟩, rfl⟩
      exact hR _ (hin w hw).1 (hin w hw).2
    refine ⟨unliftEdge cap.j Q (f '' Icc u v),
      isLine_unliftEdge hj.isEmbedding hsub (GM07.IsLineWithEnds.isLine (subArc_of_lt hfc hfi huv)),
      ⟨a, ?_, ha⟩, ⟨b, ?_, hb⟩, ?_⟩
    · exact ⟨f wa, ⟨wa, hwa, rfl⟩, hga.symm⟩
    · exact ⟨f wb, ⟨wb, hwb, rfl⟩, hgb.symm⟩
    · rintro _ ⟨x, ⟨y, ⟨w, -, rfl⟩, hy⟩, rfl⟩
      exact ⟨f w, (e w).2, hy⟩
  obtain ⟨a, haF, haA⟩ := hFA
  obtain ⟨b, hbF, hbB⟩ := hFB
  let s := e.symm ⟨a, haF⟩
  let t := e.symm ⟨b, hbF⟩
  have hgs : g s ∈ cap.j '' A := by
    change ((e (e.symm ⟨a, haF⟩)).1).1 ∈ _
    rw [e.apply_symm_apply]
    exact haA
  have hgt : g t ∈ cap.j '' B := by
    change ((e (e.symm ⟨b, hbF⟩)).1).1 ∈ _
    rw [e.apply_symm_apply]
    exact hbB
  have hst : s ≠ t := fun h => disjoint_left.mp hBA hgt (h ▸ hgs)
  have hIoc : ∀ u v : unitInterval, IsPreconnected (g '' Ioc u v) := fun u v =>
    isPreconnected_Ioc.image g hgc.continuousOn
  have hIco : ∀ u v : unitInterval, IsPreconnected (g '' Ico u v) := fun u v =>
    isPreconnected_Ico.image g hgc.continuousOn
  rcases lt_or_gt_of_ne hst with hlt | hgt'
  · obtain ⟨u, v, huv, hu, hv, hX, hY⟩ :=
      exists_segment_between hgc hcA hcB hBA.symm hlt hgs hgt
    have h₁ : g '' Ioc u v ⊆ cap.disc₁ hS.1 hA :=
      hsideA _ (hIoc u v) (disjoint_left.mpr fun _ ⟨w, hw, hgw⟩ => hgw ▸ hX w hw)
        ⟨g v, ⟨v, ⟨huv, le_rfl⟩, rfl⟩, hv⟩
    have h₂ : g '' Ico u v ⊆ cap.disc₂ hS.1 hB :=
      hsideB _ (hIco u v) (disjoint_left.mpr fun _ ⟨w, hw, hgw⟩ => hgw ▸ hY w hw)
        ⟨g u, ⟨u, ⟨le_rfl, huv⟩, rfl⟩, hu⟩
    refine finish u v huv ?_ ⟨u, ⟨le_rfl, huv.le⟩, hu⟩ ⟨v, ⟨huv.le, le_rfl⟩, hv⟩
    intro w ⟨hwu, hwv⟩
    rcases eq_or_lt_of_le hwu with rfl | hwu'
    · exact ⟨hjA₁ hu, hAB₂ hu⟩
    rcases eq_or_lt_of_le hwv with rfl | hwv'
    · exact ⟨hBA₁ hv, hjB₂ hv⟩
    exact ⟨h₁ ⟨w, ⟨hwu', hwv⟩, rfl⟩, h₂ ⟨w, ⟨hwu, hwv'⟩, rfl⟩⟩
  · obtain ⟨u, v, huv, hu, hv, hX, hY⟩ :=
      exists_segment_between hgc hcB hcA hBA hgt' hgt hgs
    have h₁ : g '' Ioc u v ⊆ cap.disc₂ hS.1 hB :=
      hsideB _ (hIoc u v) (disjoint_left.mpr fun _ ⟨w, hw, hgw⟩ => hgw ▸ hX w hw)
        ⟨g v, ⟨v, ⟨huv, le_rfl⟩, rfl⟩, hv⟩
    have h₂ : g '' Ico u v ⊆ cap.disc₁ hS.1 hA :=
      hsideA _ (hIco u v) (disjoint_left.mpr fun _ ⟨w, hw, hgw⟩ => hgw ▸ hY w hw)
        ⟨g u, ⟨u, ⟨le_rfl, huv⟩, rfl⟩, hu⟩
    refine finish u v huv ?_ ⟨v, ⟨huv.le, le_rfl⟩, hv⟩ ⟨u, ⟨le_rfl, huv.le⟩, hu⟩
    intro w ⟨hwu, hwv⟩
    rcases eq_or_lt_of_le hwu with rfl | hwu'
    · exact ⟨hBA₁ hu, hjB₂ hu⟩
    rcases eq_or_lt_of_le hwv with rfl | hwv'
    · exact ⟨hjA₁ hv, hAB₂ hv⟩
    exact ⟨h₂ ⟨w, ⟨hwu, hwv'⟩, rfl⟩, h₁ ⟨w, ⟨hwu', hwv⟩, rfl⟩⟩

end GraphMinor.GM08
