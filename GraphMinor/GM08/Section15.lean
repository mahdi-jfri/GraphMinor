module

public import GraphMinor.GM08.Section15Menger
public import GraphMinor.GM08.Section14
public import GraphMinor.GM08.Section15Assembly

/-!
# Graph Minors VIII, Section 15: Decomposing Tubular Grafts into Trains and Concatenations

This file proves side-qualified variants of the decompositions `(15.1)`, `(15.2)`, and `(15.3)` of N. Robertson and
P. D. Seymour, *Graph Minors. VIII. A Kuratowski Theorem for General Surfaces*,
J. Combin. Theory Ser. B **48** (1990), 255–288 (Section 15, pages 280–282).
The width here is the variant defined in `Section15Tube`, with extra side
conditions on its exceptional hoops. The results concern that variant:


- `theorem_15_1`: every tubular graft of width $\ge r$ and index $\le k$ is an $r$-train of
  tubular grafts of width $\ge r + 1$ and index $\le k + 2r$.
- `theorem_15_2_sideQualified`: every tubular graft of index $\le k$ is a concatenation of tubular grafts of
  width $\ge r$ and index $\le k + r(r - 1)$.
- `theorem_15_3_sideQualified`: every graft in $\mathcal{A}(k, r, s)$ is a concatenation of tubular grafts of
  length $< s$ and index $\le k + r(r - 1)$.
-/

@[expose] public section

namespace GraphMinor.GM08

open Set Function Topology Classical Graph GraphMinor.Surface GraphMinor.GM11

universe u v w

/-! ## 1. Transitivity of Sub-tubes and the Monotone Hoop Signature -/

section SubTubeAndSignature

variable {S : Type w} [TopologicalSpace S]

private theorem CylinderSphereCap.disc₁_congr (cap : CylinderSphereCap S)
    (hS : IsSurface S) {F F' : Set S} (hF : IsHoop F) (hF' : IsHoop F') (heq : F = F') :
    cap.disc₁ hS hF = cap.disc₁ hS hF' := by
  subst heq; rfl

private theorem interSet_interSet_of_subset [T1Space S] (Γ : Drawing S) {A B : Set S}
    (hA : IsClosed A) (hB : IsClosed B) (hBA : B ⊆ A) :
    (Γ.interSet A).interSet B = Γ.interSet B := by
  apply Drawing.ext_of_V_E
  · rw [interSet_V_of_isClosed _ hB, interSet_V_of_isClosed _ hA, interSet_V_of_isClosed _ hB,
      inter_assoc, inter_eq_right.mpr hBA]
  · rw [interSet_E, interSet_E, interSet_E]
    ext e
    exact ⟨fun ⟨⟨he, _⟩, heB⟩ => ⟨he, heB⟩, fun ⟨he, heB⟩ => ⟨⟨he, heB.trans hBA⟩, heB⟩⟩

/-- Restricting a tube `τ` to its own boundary hoops `F₁, F₂` returns `τ`. -/
theorem Tube.subTube_self (τ : Tube S) :
    τ.subTube τ.laminar τ.isNormal_F₁ τ.isNormal_F₂ = τ := by
  have : T2Space S := τ.t2Space
  have hcl : IsClosed (cylinderBetween τ.F₁ τ.F₂) := isClosed_cylinderBetween τ.laminar
  have hΓ : τ.Γ.interSet (cylinderBetween τ.F₁ τ.F₂) = τ.Γ := by
    apply Drawing.ext_of_V_E
    · rw [interSet_V_of_isClosed _ hcl]
      exact inter_eq_left.mpr (τ.Γ.V_subset_U.trans τ.U_subset)
    · rw [interSet_E]
      ext e
      exact ⟨fun h => h.1, fun he => ⟨he, fun x hx => τ.U_subset (he.2.1 hx).1⟩⟩
  cases τ
  dsimp only [Tube.subTube] at hΓ ⊢
  congr 1

/-- No edge `e ∈ Γ.E` is contained in a `Γ`-normal set `K`. -/
private theorem not_edge_subset_of_isNormal {Γ : Drawing S} {K e : Set S}
    (hNK : Γ.IsNormal K) (he : e ∈ Γ.E) (hsub : e ⊆ K) : False := by
  obtain ⟨x, hxe⟩ := he.1
  exact (he.2.1 hxe).2 (hNK ⟨hsub hxe, (he.2.1 hxe).1⟩)

/-- A subset `K ⊆ Σ(F₁', F₂')` is normal in `τ.subTube hlam hN₁ hN₂` if and only if it is
`τ.Γ`-normal. -/
theorem Tube.subTube_isNormal_iff (τ : Tube S) {F₁' F₂' K : Set S}
    (hlam : AreLaminarHoops F₁' F₂') (hN₁ : τ.Γ.IsNormal F₁') (hN₂ : τ.Γ.IsNormal F₂')
    (hK_sub : K ⊆ cylinderBetween F₁' F₂') :
    (τ.subTube hlam hN₁ hN₂).Γ.IsNormal K ↔ τ.Γ.IsNormal K := by
  have : T2Space S := τ.t2Space
  have hcl : IsClosed (cylinderBetween F₁' F₂') := isClosed_cylinderBetween hlam
  have hU := interSet_U_eq_of_laminar_normal τ.Γ hlam hN₁ hN₂
  have hV := interSet_V_of_isClosed τ.Γ hcl
  constructor
  · intro hNK' x ⟨hxK, hxU⟩
    have hxU' : x ∈ (τ.subTube hlam hN₁ hN₂).Γ.U := by
      change x ∈ (τ.Γ.interSet (cylinderBetween F₁' F₂')).U
      rw [hU]
      exact ⟨hxU, hK_sub hxK⟩
    have hxV' : x ∈ (τ.Γ.interSet (cylinderBetween F₁' F₂')).V := hNK' ⟨hxK, hxU'⟩
    exact (hV ▸ hxV').1
  · intro hNK x ⟨hxK, hxU'⟩
    change x ∈ (τ.Γ.interSet (cylinderBetween F₁' F₂')).V
    rw [hV]
    have hxU : x ∈ τ.Γ.U := (hU ▸ hxU').1
    exact ⟨hNK ⟨hxK, hxU⟩, hK_sub hxK⟩

/-- Taking a sub-tube of a sub-tube of `τ` produces the corresponding sub-tube of `τ`. -/
theorem Tube.subTube_subTube (τ : Tube S) {F₁' F₂' H₁ H₂ : Set S}
    (hlam : AreLaminarHoops F₁' F₂')
    (hN₁ : τ.Γ.IsNormal F₁') (hN₂ : τ.Γ.IsNormal F₂')
    (hlam' : AreLaminarHoops H₁ H₂)
    (hH₁ : H₁ ⊆ cylinderBetween F₁' F₂') (hH₂ : H₂ ⊆ cylinderBetween F₁' F₂')
    (hNH₁' : (τ.subTube hlam hN₁ hN₂).Γ.IsNormal H₁)
    (hNH₂' : (τ.subTube hlam hN₁ hN₂).Γ.IsNormal H₂) :
    (τ.subTube hlam hN₁ hN₂).subTube hlam' hNH₁' hNH₂' =
      τ.subTube hlam'
        ((τ.subTube_isNormal_iff hlam hN₁ hN₂ hH₁).mp hNH₁')
        ((τ.subTube_isNormal_iff hlam hN₁ hN₂ hH₂).mp hNH₂') := by
  have : T2Space S := τ.t2Space
  have hcl : IsClosed (cylinderBetween F₁' F₂') := isClosed_cylinderBetween hlam
  have hcl' : IsClosed (cylinderBetween H₁ H₂) := isClosed_cylinderBetween hlam'
  have hsub : cylinderBetween H₁ H₂ ⊆ cylinderBetween F₁' F₂' :=
    cylinderBetween_subset_cylinderBetween hlam hlam' hH₁ hH₂
  have hΓ := interSet_interSet_of_subset τ.Γ hcl hcl' hsub
  dsimp only [Tube.subTube]
  congr 1

/-- The finite 4-tuple invariant recording which vertices and edges of `τ.Γ` lie on the `F₁`-side
and `F₂`-side of a hoop `H` in `τ`. -/
def Tube.hoopSignature (τ : Tube S) (H : Set S) :
    Set S × Set (Set S) × Set S × Set (Set S) :=
  (τ.Γ.V ∩ cylinderBetween τ.F₁ H,
   {e ∈ τ.Γ.E | e ⊆ cylinderBetween τ.F₁ H},
   τ.Γ.V ∩ cylinderBetween H τ.F₂,
   {e ∈ τ.Γ.E | e ⊆ cylinderBetween H τ.F₂})

/-- All values of `τ.hoopSignature` lie in a fixed finite set of 4-tuples of subsets of `τ.Γ.V`
and `τ.Γ.E`. -/
private theorem Tube.finite_range_hoopSignature (τ : Tube S) :
    (range τ.hoopSignature).Finite := by
  let Ω : Set (Set S × Set (Set S) × Set S × Set (Set S)) :=
    𝒫 τ.Γ.V ×ˢ (𝒫 τ.Γ.E ×ˢ (𝒫 τ.Γ.V ×ˢ 𝒫 τ.Γ.E))
  have hΩ : Ω.Finite :=
    τ.Γ.finite_V.powerset.prod
      (τ.Γ.finite_edges.powerset.prod (τ.Γ.finite_V.powerset.prod τ.Γ.finite_edges.powerset))
  refine hΩ.subset ?_
  rintro _ ⟨H, rfl⟩
  exact ⟨inter_subset_left, fun _ h => h.1, inter_subset_left, fun _ h => h.1⟩

/-- Monotonicity sandwich for `τ.hoopSignature`: if `H₁ ≤ H₂ ≤ H₃` in `cap.disc₁` order and
`H₁, H₃` have the same signature, then `H₂` also has the same signature. -/
private theorem Tube.hoopSignature_eq_of_between (τ : Tube S) (cap : CylinderSphereCap S)
    {H₁ H₂ H₃ : Set S} (hH₁ : IsHoop H₁) (hH₂ : IsHoop H₂) (hH₃ : IsHoop H₃)
    (hF₁₁ : cap.disc₁ τ.isCylinder.1 τ.isHoop_F₁ ⊆ cap.disc₁ τ.isCylinder.1 hH₁)
    (h12 : cap.disc₁ τ.isCylinder.1 hH₁ ⊆ cap.disc₁ τ.isCylinder.1 hH₂)
    (h23 : cap.disc₁ τ.isCylinder.1 hH₂ ⊆ cap.disc₁ τ.isCylinder.1 hH₃)
    (h3F₂ : cap.disc₁ τ.isCylinder.1 hH₃ ⊆ cap.disc₁ τ.isCylinder.1 τ.isHoop_F₂)
    (heq : τ.hoopSignature H₁ = τ.hoopSignature H₃) :
    τ.hoopSignature H₁ = τ.hoopSignature H₂ := by
  have hL12 : cylinderBetween τ.F₁ H₁ ⊆ cylinderBetween τ.F₁ H₂ :=
    cap.cylinderBetween_mono τ.isCylinder τ.isHoop_F₁ τ.isHoop_F₁ hH₁ hH₂
      Subset.rfl hF₁₁ h12
  have hL23 : cylinderBetween τ.F₁ H₂ ⊆ cylinderBetween τ.F₁ H₃ :=
    cap.cylinderBetween_mono τ.isCylinder τ.isHoop_F₁ τ.isHoop_F₁ hH₂ hH₃
      Subset.rfl (hF₁₁.trans h12) h23
  have hR21 : cylinderBetween H₂ τ.F₂ ⊆ cylinderBetween H₁ τ.F₂ :=
    cap.cylinderBetween_mono τ.isCylinder hH₁ hH₂ τ.isHoop_F₂ τ.isHoop_F₂
      h12 (h23.trans h3F₂) Subset.rfl
  have hR32 : cylinderBetween H₃ τ.F₂ ⊆ cylinderBetween H₂ τ.F₂ :=
    cap.cylinderBetween_mono τ.isCylinder hH₂ hH₃ τ.isHoop_F₂ τ.isHoop_F₂
      h23 h3F₂ Subset.rfl
  have hc1 : τ.Γ.V ∩ cylinderBetween τ.F₁ H₁ = τ.Γ.V ∩ cylinderBetween τ.F₁ H₃ :=
    congrArg Prod.fst heq
  have hc2 : {e ∈ τ.Γ.E | e ⊆ cylinderBetween τ.F₁ H₁} =
      {e ∈ τ.Γ.E | e ⊆ cylinderBetween τ.F₁ H₃} :=
    congrArg (fun p => p.2.1) heq
  have hc3 : τ.Γ.V ∩ cylinderBetween H₁ τ.F₂ = τ.Γ.V ∩ cylinderBetween H₃ τ.F₂ :=
    congrArg (fun p => p.2.2.1) heq
  have hc4 : {e ∈ τ.Γ.E | e ⊆ cylinderBetween H₁ τ.F₂} =
      {e ∈ τ.Γ.E | e ⊆ cylinderBetween H₃ τ.F₂} :=
    congrArg (fun p => p.2.2.2) heq
  refine Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ ?_))
  · exact Subset.antisymm (inter_subset_inter_right _ hL12)
      ((inter_subset_inter_right _ hL23).trans hc1.symm.subset)
  · exact Subset.antisymm (fun e ⟨he, hs⟩ => ⟨he, hs.trans hL12⟩)
      (fun e ⟨he, hs⟩ => hc2.symm.subset ⟨he, hs.trans hL23⟩)
  · exact Subset.antisymm (hc3.subset.trans (inter_subset_inter_right _ hR32))
      (inter_subset_inter_right _ hR21)
  · exact Subset.antisymm
      (fun e h => ⟨h.1, (hc4.subset h).2.trans hR32⟩)
      (fun e ⟨he, hs⟩ => ⟨he, hs.trans hR21⟩)

/-- If a `τ.Γ`-normal hoop `H` with `H_a ≤ H ≤ H_b` is cut-trivial in the sub-tube
`τ.subTube hlam_ab hNa hNb`, then `H` has the same `hoopSignature` in `τ` as either `H_a` or
`H_b`. -/
private theorem Tube.hoopSignature_eq_of_subTube_isCutTrivial (τ : Tube S)
    (cap : CylinderSphereCap S) {Ha H Hb : Set S}
    (hHa : IsHoop Ha) (hH : IsHoop H) (hHb : IsHoop Hb)
    (hNa : τ.Γ.IsNormal Ha) (hNH : τ.Γ.IsNormal H) (hNb : τ.Γ.IsNormal Hb)
    (hF₁a : cap.disc₁ τ.isCylinder.1 τ.isHoop_F₁ ⊆ cap.disc₁ τ.isCylinder.1 hHa)
    (haH : cap.disc₁ τ.isCylinder.1 hHa ⊆ cap.disc₁ τ.isCylinder.1 hH)
    (hHb_le : cap.disc₁ τ.isCylinder.1 hH ⊆ cap.disc₁ τ.isCylinder.1 hHb)
    (hbF₂ : cap.disc₁ τ.isCylinder.1 hHb ⊆ cap.disc₁ τ.isCylinder.1 τ.isHoop_F₂)
    {hlam_ab : AreLaminarHoops Ha Hb}
    (hct : (τ.subTube hlam_ab hNa hNb).IsCutTrivial H) :
    τ.hoopSignature H = τ.hoopSignature Ha ∨ τ.hoopSignature H = τ.hoopSignature Hb := by
  have : T2Space S := τ.t2Space
  have hab : cap.disc₁ τ.isCylinder.1 hHa ⊆ cap.disc₁ τ.isCylinder.1 hHb := haH.trans hHb_le
  have hF₁H : cap.disc₁ τ.isCylinder.1 τ.isHoop_F₁ ⊆ cap.disc₁ τ.isCylinder.1 hH :=
    hF₁a.trans haH
  have hHF₂ : cap.disc₁ τ.isCylinder.1 hH ⊆ cap.disc₁ τ.isCylinder.1 τ.isHoop_F₂ :=
    hHb_le.trans hbF₂
  have haF₂ : cap.disc₁ τ.isCylinder.1 hHa ⊆ cap.disc₁ τ.isCylinder.1 τ.isHoop_F₂ :=
    hab.trans hbF₂
  have hF₁b : cap.disc₁ τ.isCylinder.1 τ.isHoop_F₁ ⊆ cap.disc₁ τ.isCylinder.1 hHb :=
    hF₁a.trans hab
  have hcl_ab : IsClosed (cylinderBetween Ha Hb) := isClosed_cylinderBetween hlam_ab
  have hU' : (τ.subTube hlam_ab hNa hNb).Γ.U = τ.Γ.U ∩ cylinderBetween Ha Hb :=
    interSet_U_eq_of_laminar_normal τ.Γ hlam_ab hNa hNb
  have hV' : (τ.subTube hlam_ab hNa hNb).Γ.V = τ.Γ.V ∩ cylinderBetween Ha Hb :=
    interSet_V_of_isClosed τ.Γ hcl_ab
  have hH_sub_ab : H ⊆ cylinderBetween Ha Hb :=
    (cap.hoop_subset_cylinderBetween_iff τ.isCylinder hHa hHb hH hab).mpr ⟨haH, hHb_le⟩
  have hHa_sub_ab : Ha ⊆ cylinderBetween Ha Hb := subset_cylinderBetween_left hlam_ab
  have hHb_sub_ab : Hb ⊆ cylinderBetween Ha Hb := subset_cylinderBetween_right hlam_ab
  rcases hct with ⟨hU_sub, hV_eq⟩ | ⟨hU_sub, hV_eq⟩
  · left
    rw [hU'] at hU_sub
    dsimp only [Tube.subTube] at hU_sub hV_eq
    have hV_global : H ∩ τ.Γ.V = Ha ∩ τ.Γ.V := by
      have h1 : H ∩ (τ.Γ.V ∩ cylinderBetween Ha Hb) = H ∩ τ.Γ.V := by
        ext x; exact ⟨fun ⟨hxH, hxV, _⟩ => ⟨hxH, hxV⟩, fun ⟨hxH, hxV⟩ => ⟨hxH, hxV, hH_sub_ab hxH⟩⟩
      have h2 : Ha ∩ (τ.Γ.V ∩ cylinderBetween Ha Hb) = Ha ∩ τ.Γ.V := by
        ext x; exact ⟨fun ⟨hxA, hxV, _⟩ => ⟨hxA, hxV⟩, fun ⟨hxA, hxV⟩ => ⟨hxA, hxV, hHa_sub_ab hxA⟩⟩
      rw [interSet_V_of_isClosed τ.Γ hcl_ab, h1, h2] at hV_eq
      exact hV_eq
    have hlam_F₁a : AreLaminarHoops τ.F₁ Ha :=
      (cap.areLaminarHoops_iff τ.isCylinder τ.isHoop_F₁ hHa).mpr (Or.inl hF₁a)
    have hlam_F₁H : AreLaminarHoops τ.F₁ H :=
      (cap.areLaminarHoops_iff τ.isCylinder τ.isHoop_F₁ hH).mpr (Or.inl hF₁H)
    have hlam_aF₂ : AreLaminarHoops Ha τ.F₂ :=
      (cap.areLaminarHoops_iff τ.isCylinder hHa τ.isHoop_F₂).mpr (Or.inl haF₂)
    have hHa_F₁H : Ha ⊆ cylinderBetween τ.F₁ H :=
      (cap.hoop_subset_cylinderBetween_iff τ.isCylinder τ.isHoop_F₁ hH hHa hF₁H).mpr ⟨hF₁a, haH⟩
    have hHb_aF₂ : Hb ⊆ cylinderBetween Ha τ.F₂ :=
      (cap.hoop_subset_cylinderBetween_iff τ.isCylinder hHa τ.isHoop_F₂ hHb haF₂).mpr ⟨hab, hbF₂⟩
    have hsub_aH_ab : cylinderBetween Ha H ⊆ cylinderBetween Ha Hb :=
      cap.cylinderBetween_mono τ.isCylinder hHa hHa hH hHb Subset.rfl haH hHb_le
    have hsub_Hb_HF₂ : cylinderBetween H Hb ⊆ cylinderBetween H τ.F₂ :=
      cap.cylinderBetween_mono τ.isCylinder hH hH hHb τ.isHoop_F₂ Subset.rfl hHb_le hbF₂
    have hsub_bF₂_HF₂ : cylinderBetween Hb τ.F₂ ⊆ cylinderBetween H τ.F₂ :=
      cap.cylinderBetween_mono τ.isCylinder hH hHb τ.isHoop_F₂ τ.isHoop_F₂ hHb_le hbF₂ Subset.rfl
    refine Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ ?_))
    · apply Subset.antisymm
      · rintro x ⟨hxV, hxFH⟩
        rw [← cap.cylinderBetween_union τ.isCylinder τ.isHoop_F₁ hHa hH hF₁a haH] at hxFH
        rcases hxFH with hx1 | hx2
        · exact ⟨hxV, hx1⟩
        · have hxHb : x ∈ cylinderBetween H Hb :=
            hU_sub ⟨τ.Γ.V_subset_U hxV, hsub_aH_ab hx2⟩
          have hxH : x ∈ H :=
            cap.cylinderBetween_inter τ.isCylinder hHa hH hHb haH hHb_le ▸ ⟨hx2, hxHb⟩
          have hxHa : x ∈ Ha := (hV_global.subset ⟨hxH, hxV⟩).1
          exact ⟨hxV, subset_cylinderBetween_right hlam_F₁a hxHa⟩
      · exact inter_subset_inter_right _
          (cap.cylinderBetween_mono τ.isCylinder τ.isHoop_F₁ τ.isHoop_F₁ hHa hH
            Subset.rfl hF₁a haH)
    · apply Subset.antisymm
      · rintro e ⟨he, he_sub⟩
        rcases edge_subset_cylinderBetween_left_or_right τ.Γ hlam_F₁H hHa hHa_F₁H hNa he he_sub
          with ⟨he1, _⟩ | ⟨he2, _⟩
        · exact ⟨he, he1⟩
        · exfalso
          have he_Hb : e ⊆ cylinderBetween H Hb := fun x hxe =>
            hU_sub ⟨(he.2.1 hxe).1, hsub_aH_ab (he2 hxe)⟩
          have he_H : e ⊆ H := fun x hxe =>
            cap.cylinderBetween_inter τ.isCylinder hHa hH hHb haH hHb_le ▸ ⟨he2 hxe, he_Hb hxe⟩
          exact not_edge_subset_of_isNormal hNH he he_H
      · exact fun e ⟨he, hs⟩ => ⟨he, hs.trans
          (cap.cylinderBetween_mono τ.isCylinder τ.isHoop_F₁ τ.isHoop_F₁ hHa hH
            Subset.rfl hF₁a haH)⟩
    · apply Subset.antisymm
      · exact inter_subset_inter_right _
          (cap.cylinderBetween_mono τ.isCylinder hHa hH τ.isHoop_F₂ τ.isHoop_F₂
            haH hHF₂ Subset.rfl)
      · rintro x ⟨hxV, hxaF₂⟩
        rw [← cap.cylinderBetween_union τ.isCylinder hHa hHb τ.isHoop_F₂ hab hbF₂] at hxaF₂
        rcases hxaF₂ with hx1 | hx2
        · exact ⟨hxV, hsub_Hb_HF₂ (hU_sub ⟨τ.Γ.V_subset_U hxV, hx1⟩)⟩
        · exact ⟨hxV, hsub_bF₂_HF₂ hx2⟩
    · apply Subset.antisymm
      · exact fun e ⟨he, hs⟩ => ⟨he, hs.trans
          (cap.cylinderBetween_mono τ.isCylinder hHa hH τ.isHoop_F₂ τ.isHoop_F₂
            haH hHF₂ Subset.rfl)⟩
      · rintro e ⟨he, he_sub⟩
        rcases edge_subset_cylinderBetween_left_or_right τ.Γ hlam_aF₂ hHb hHb_aF₂ hNb he he_sub
          with ⟨he1, _⟩ | ⟨he2, _⟩
        · refine ⟨he, fun x hxe => hsub_Hb_HF₂ (hU_sub ⟨(he.2.1 hxe).1, he1 hxe⟩)⟩
        · exact ⟨he, he2.trans hsub_bF₂_HF₂⟩
  · right
    rw [hU'] at hU_sub
    dsimp only [Tube.subTube] at hU_sub hV_eq
    have hV_global : H ∩ τ.Γ.V = Hb ∩ τ.Γ.V := by
      have h1 : H ∩ (τ.Γ.V ∩ cylinderBetween Ha Hb) = H ∩ τ.Γ.V := by
        ext x; exact ⟨fun ⟨hxH, hxV, _⟩ => ⟨hxH, hxV⟩, fun ⟨hxH, hxV⟩ => ⟨hxH, hxV, hH_sub_ab hxH⟩⟩
      have h2 : Hb ∩ (τ.Γ.V ∩ cylinderBetween Ha Hb) = Hb ∩ τ.Γ.V := by
        ext x; exact ⟨fun ⟨hxB, hxV, _⟩ => ⟨hxB, hxV⟩, fun ⟨hxB, hxV⟩ => ⟨hxB, hxV, hHb_sub_ab hxB⟩⟩
      rw [interSet_V_of_isClosed τ.Γ hcl_ab, h1, h2] at hV_eq
      exact hV_eq
    have hlam_F₁b : AreLaminarHoops τ.F₁ Hb :=
      (cap.areLaminarHoops_iff τ.isCylinder τ.isHoop_F₁ hHb).mpr (Or.inl hF₁b)
    have hlam_bF₂ : AreLaminarHoops Hb τ.F₂ :=
      (cap.areLaminarHoops_iff τ.isCylinder hHb τ.isHoop_F₂).mpr (Or.inl hbF₂)
    have hlam_HF₂ : AreLaminarHoops H τ.F₂ :=
      (cap.areLaminarHoops_iff τ.isCylinder hH τ.isHoop_F₂).mpr (Or.inl hHF₂)
    have hHa_F₁b : Ha ⊆ cylinderBetween τ.F₁ Hb :=
      (cap.hoop_subset_cylinderBetween_iff τ.isCylinder τ.isHoop_F₁ hHb hHa hF₁b).mpr ⟨hF₁a, hab⟩
    have hHb_HF₂ : Hb ⊆ cylinderBetween H τ.F₂ :=
      (cap.hoop_subset_cylinderBetween_iff τ.isCylinder hH τ.isHoop_F₂ hHb hHF₂).mpr ⟨hHb_le, hbF₂⟩
    have hsub_Hb_ab : cylinderBetween H Hb ⊆ cylinderBetween Ha Hb :=
      cap.cylinderBetween_mono τ.isCylinder hHa hH hHb hHb haH hHb_le Subset.rfl
    have hsub_F₁a_F₁H : cylinderBetween τ.F₁ Ha ⊆ cylinderBetween τ.F₁ H :=
      cap.cylinderBetween_mono τ.isCylinder τ.isHoop_F₁ τ.isHoop_F₁ hHa hH Subset.rfl hF₁a haH
    have hsub_aH_F₁H : cylinderBetween Ha H ⊆ cylinderBetween τ.F₁ H :=
      cap.cylinderBetween_mono τ.isCylinder τ.isHoop_F₁ hHa hH hH hF₁a haH Subset.rfl
    refine Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ ?_))
    · apply Subset.antisymm
      · exact inter_subset_inter_right _
          (cap.cylinderBetween_mono τ.isCylinder τ.isHoop_F₁ τ.isHoop_F₁ hH hHb
            Subset.rfl hF₁H hHb_le)
      · rintro x ⟨hxV, hxFb⟩
        rw [← cap.cylinderBetween_union τ.isCylinder τ.isHoop_F₁ hHa hHb hF₁a hab] at hxFb
        rcases hxFb with hx1 | hx2
        · exact ⟨hxV, hsub_F₁a_F₁H hx1⟩
        · exact ⟨hxV, hsub_aH_F₁H (hU_sub ⟨τ.Γ.V_subset_U hxV, hx2⟩)⟩
    · apply Subset.antisymm
      · exact fun e ⟨he, hs⟩ => ⟨he, hs.trans
          (cap.cylinderBetween_mono τ.isCylinder τ.isHoop_F₁ τ.isHoop_F₁ hH hHb
            Subset.rfl hF₁H hHb_le)⟩
      · rintro e ⟨he, he_sub⟩
        rcases edge_subset_cylinderBetween_left_or_right τ.Γ hlam_F₁b hHa hHa_F₁b hNa he he_sub
          with ⟨he1, _⟩ | ⟨he2, _⟩
        · exact ⟨he, he1.trans hsub_F₁a_F₁H⟩
        · refine ⟨he, fun x hxe => hsub_aH_F₁H (hU_sub ⟨(he.2.1 hxe).1, he2 hxe⟩)⟩
    · apply Subset.antisymm
      · rintro x ⟨hxV, hxHF₂⟩
        rw [← cap.cylinderBetween_union τ.isCylinder hH hHb τ.isHoop_F₂ hHb_le hbF₂] at hxHF₂
        rcases hxHF₂ with hx1 | hx2
        · have hxaH : x ∈ cylinderBetween Ha H :=
            hU_sub ⟨τ.Γ.V_subset_U hxV, hsub_Hb_ab hx1⟩
          have hxH : x ∈ H :=
            cap.cylinderBetween_inter τ.isCylinder hHa hH hHb haH hHb_le ▸ ⟨hxaH, hx1⟩
          have hxHb : x ∈ Hb := (hV_global.subset ⟨hxH, hxV⟩).1
          exact ⟨hxV, subset_cylinderBetween_left hlam_bF₂ hxHb⟩
        · exact ⟨hxV, hx2⟩
      · exact inter_subset_inter_right _
          (cap.cylinderBetween_mono τ.isCylinder hH hHb τ.isHoop_F₂ τ.isHoop_F₂
            hHb_le hbF₂ Subset.rfl)
    · apply Subset.antisymm
      · rintro e ⟨he, he_sub⟩
        rcases edge_subset_cylinderBetween_left_or_right τ.Γ hlam_HF₂ hHb hHb_HF₂ hNb he he_sub
          with ⟨he1, _⟩ | ⟨he2, _⟩
        · exfalso
          have he_aH : e ⊆ cylinderBetween Ha H := fun x hxe =>
            hU_sub ⟨(he.2.1 hxe).1, hsub_Hb_ab (he1 hxe)⟩
          have he_H : e ⊆ H := fun x hxe =>
            cap.cylinderBetween_inter τ.isCylinder hHa hH hHb haH hHb_le ▸ ⟨he_aH hxe, he1 hxe⟩
          exact not_edge_subset_of_isNormal hNH he he_H
        · exact ⟨he, he2⟩
      · exact fun e ⟨he, hs⟩ => ⟨he, hs.trans
          (cap.cylinderBetween_mono τ.isCylinder hH hHb τ.isHoop_F₂ τ.isHoop_F₂
            hHb_le hbF₂ Subset.rfl)⟩

/-- Conversely, if a hoop `H` with `H_a ≤ H ≤ H_b` in `cap.disc₁` order has the same
`hoopSignature` in `τ` as `H_a` or `H_b`, then `H` is cut-trivial in `τ.subTube hlam_ab hNa hNb`. -/
private theorem Tube.subTube_isCutTrivial_of_hoopSignature_eq (τ : Tube S)
    (cap : CylinderSphereCap S) {Ha H Hb : Set S}
    (hHa : IsHoop Ha) (hH : IsHoop H) (hHb : IsHoop Hb)
    (hNa : τ.Γ.IsNormal Ha) (hNb : τ.Γ.IsNormal Hb)
    (hF₁a : cap.disc₁ τ.isCylinder.1 τ.isHoop_F₁ ⊆ cap.disc₁ τ.isCylinder.1 hHa)
    (haH : cap.disc₁ τ.isCylinder.1 hHa ⊆ cap.disc₁ τ.isCylinder.1 hH)
    (hHb_le : cap.disc₁ τ.isCylinder.1 hH ⊆ cap.disc₁ τ.isCylinder.1 hHb)
    (hbF₂ : cap.disc₁ τ.isCylinder.1 hHb ⊆ cap.disc₁ τ.isCylinder.1 τ.isHoop_F₂)
    {hlam_ab : AreLaminarHoops Ha Hb}
    (heq : τ.hoopSignature H = τ.hoopSignature Ha ∨ τ.hoopSignature H = τ.hoopSignature Hb) :
    (τ.subTube hlam_ab hNa hNb).IsCutTrivial H := by
  have : T2Space S := τ.t2Space
  have hab : cap.disc₁ τ.isCylinder.1 hHa ⊆ cap.disc₁ τ.isCylinder.1 hHb := haH.trans hHb_le
  have hF₁H : cap.disc₁ τ.isCylinder.1 τ.isHoop_F₁ ⊆ cap.disc₁ τ.isCylinder.1 hH :=
    hF₁a.trans haH
  have hHF₂ : cap.disc₁ τ.isCylinder.1 hH ⊆ cap.disc₁ τ.isCylinder.1 τ.isHoop_F₂ :=
    hHb_le.trans hbF₂
  have haF₂ : cap.disc₁ τ.isCylinder.1 hHa ⊆ cap.disc₁ τ.isCylinder.1 τ.isHoop_F₂ :=
    hab.trans hbF₂
  have hF₁b : cap.disc₁ τ.isCylinder.1 τ.isHoop_F₁ ⊆ cap.disc₁ τ.isCylinder.1 hHb :=
    hF₁a.trans hab
  have hcl_ab : IsClosed (cylinderBetween Ha Hb) := isClosed_cylinderBetween hlam_ab
  have hU' : (τ.subTube hlam_ab hNa hNb).Γ.U = τ.Γ.U ∩ cylinderBetween Ha Hb :=
    interSet_U_eq_of_laminar_normal τ.Γ hlam_ab hNa hNb
  have hV' : (τ.subTube hlam_ab hNa hNb).Γ.V = τ.Γ.V ∩ cylinderBetween Ha Hb :=
    interSet_V_of_isClosed τ.Γ hcl_ab
  have hH_sub_ab : H ⊆ cylinderBetween Ha Hb :=
    (cap.hoop_subset_cylinderBetween_iff τ.isCylinder hHa hHb hH hab).mpr ⟨haH, hHb_le⟩
  have hinter_right : cylinderBetween H τ.F₂ ∩ cylinderBetween Ha Hb = cylinderBetween H Hb := by
    rw [cap.cylinderBetween_eq_of_disc₁_subset τ.isCylinder hH τ.isHoop_F₂ hHF₂,
      cap.cylinderBetween_eq_of_disc₁_subset τ.isCylinder hHa hHb hab,
      cap.cylinderBetween_eq_of_disc₁_subset τ.isCylinder hH hHb hHb_le, ← preimage_inter]
    have haH2 := (cap.disc₂_subset_iff_disc₁_subset τ.isCylinder.1 hHa hH).mpr haH
    congr 1
    ext z
    exact ⟨fun ⟨⟨_, h2⟩, ⟨h1, _⟩⟩ => ⟨h1, h2⟩,
      fun ⟨h1, h2⟩ => ⟨⟨hbF₂ h1, h2⟩, ⟨h1, haH2 h2⟩⟩⟩
  have hinter_left : cylinderBetween τ.F₁ H ∩ cylinderBetween Ha Hb = cylinderBetween Ha H := by
    rw [cap.cylinderBetween_eq_of_disc₁_subset τ.isCylinder τ.isHoop_F₁ hH hF₁H,
      cap.cylinderBetween_eq_of_disc₁_subset τ.isCylinder hHa hHb hab,
      cap.cylinderBetween_eq_of_disc₁_subset τ.isCylinder hHa hH haH, ← preimage_inter]
    have hF₁a2 := (cap.disc₂_subset_iff_disc₁_subset τ.isCylinder.1 τ.isHoop_F₁ hHa).mpr hF₁a
    congr 1
    ext z
    exact ⟨fun ⟨⟨h1, _⟩, ⟨_, h2⟩⟩ => ⟨h1, h2⟩,
      fun ⟨h1, h2⟩ => ⟨⟨h1, hF₁a2 h2⟩, ⟨hHb_le h1, h2⟩⟩⟩
  have hlam_aH : AreLaminarHoops Ha H :=
    (cap.areLaminarHoops_iff τ.isCylinder hHa hH).mpr (Or.inl haH)
  have hlam_Hb : AreLaminarHoops H Hb :=
    (cap.areLaminarHoops_iff τ.isCylinder hH hHb).mpr (Or.inl hHb_le)
  rcases heq with heq | heq
  · left
    have hc1 : τ.Γ.V ∩ cylinderBetween τ.F₁ H = τ.Γ.V ∩ cylinderBetween τ.F₁ Ha :=
      congrArg Prod.fst heq
    have hc3 : τ.Γ.V ∩ cylinderBetween H τ.F₂ = τ.Γ.V ∩ cylinderBetween Ha τ.F₂ :=
      congrArg (fun p => p.2.2.1) heq
    have hc4 : {e ∈ τ.Γ.E | e ⊆ cylinderBetween H τ.F₂} =
        {e ∈ τ.Γ.E | e ⊆ cylinderBetween Ha τ.F₂} :=
      congrArg (fun p => p.2.2.2) heq
    have hab_aF₂ : cylinderBetween Ha Hb ⊆ cylinderBetween Ha τ.F₂ :=
      cap.cylinderBetween_mono τ.isCylinder hHa hHa hHb τ.isHoop_F₂ Subset.rfl hab hbF₂
    have hU_sub : (τ.subTube hlam_ab hNa hNb).Γ.U ⊆ cylinderBetween H Hb := by
      intro x hxU'
      obtain ⟨hxU, hx_ab⟩ := hU' ▸ hxU'
      rw [← hinter_right]
      refine ⟨?_, hx_ab⟩
      by_cases hxV : x ∈ τ.Γ.V
      · exact (hc3.symm.subset ⟨hxV, hab_aF₂ hx_ab⟩).2
      · have hxV' : x ∉ (τ.subTube hlam_ab hNa hNb).Γ.V := fun h => hxV (hV' ▸ h).1
        obtain ⟨e, he', hxe⟩ := (τ.subTube hlam_ab hNa hNb).Γ.exists_edge_of_mem hxU' hxV'
        have he : e ∈ {ed ∈ τ.Γ.E | ed ⊆ cylinderBetween Ha Hb} :=
          interSet_E τ.Γ (cylinderBetween Ha Hb) ▸
            (show e ∈ (τ.Γ.interSet (cylinderBetween Ha Hb)).E from he')
        have he_HF₂ : e ∈ {ed ∈ τ.Γ.E | ed ⊆ cylinderBetween H τ.F₂} :=
          hc4.symm ▸ ⟨he.1, he.2.trans hab_aF₂⟩
        exact he_HF₂.2 hxe
    refine ⟨hU_sub, Subset.antisymm ?_ ?_⟩
    · rintro x ⟨hxH, hxV'⟩
      obtain ⟨hxV, hx_ab⟩ := hV' ▸ hxV'
      have hlam_F₁H : AreLaminarHoops τ.F₁ H :=
        (cap.areLaminarHoops_iff τ.isCylinder τ.isHoop_F₁ hH).mpr (Or.inl hF₁H)
      have hx_F₁a : x ∈ cylinderBetween τ.F₁ Ha :=
        (hc1.subset ⟨hxV, subset_cylinderBetween_right hlam_F₁H hxH⟩).2
      have hxHa : x ∈ Ha :=
        cap.cylinderBetween_inter τ.isCylinder τ.isHoop_F₁ hHa hHb hF₁a hab ▸ ⟨hx_F₁a, hx_ab⟩
      exact ⟨hxHa, hxV'⟩
    · rintro x ⟨hxHa, hxV'⟩
      obtain ⟨hxV, hx_ab⟩ := hV' ▸ hxV'
      have hx1 : x ∈ cylinderBetween Ha H := subset_cylinderBetween_left hlam_aH hxHa
      have hx2 : x ∈ cylinderBetween H Hb :=
        hU_sub (hU'.symm ▸ ⟨τ.Γ.V_subset_U hxV, hx_ab⟩)
      exact ⟨cap.cylinderBetween_inter τ.isCylinder hHa hH hHb haH hHb_le ▸ ⟨hx1, hx2⟩, hxV'⟩
  · right
    have hc1 : τ.Γ.V ∩ cylinderBetween τ.F₁ H = τ.Γ.V ∩ cylinderBetween τ.F₁ Hb :=
      congrArg Prod.fst heq
    have hc2 : {e ∈ τ.Γ.E | e ⊆ cylinderBetween τ.F₁ H} =
        {e ∈ τ.Γ.E | e ⊆ cylinderBetween τ.F₁ Hb} :=
      congrArg (fun p => p.2.1) heq
    have hc3 : τ.Γ.V ∩ cylinderBetween H τ.F₂ = τ.Γ.V ∩ cylinderBetween Hb τ.F₂ :=
      congrArg (fun p => p.2.2.1) heq
    have hab_F₁b : cylinderBetween Ha Hb ⊆ cylinderBetween τ.F₁ Hb :=
      cap.cylinderBetween_mono τ.isCylinder τ.isHoop_F₁ hHa hHb hHb hF₁a hab Subset.rfl
    have hU_sub : (τ.subTube hlam_ab hNa hNb).Γ.U ⊆ cylinderBetween Ha H := by
      intro x hxU'
      obtain ⟨hxU, hx_ab⟩ := hU' ▸ hxU'
      rw [← hinter_left]
      refine ⟨?_, hx_ab⟩
      by_cases hxV : x ∈ τ.Γ.V
      · exact (hc1.symm.subset ⟨hxV, hab_F₁b hx_ab⟩).2
      · have hxV' : x ∉ (τ.subTube hlam_ab hNa hNb).Γ.V := fun h => hxV (hV' ▸ h).1
        obtain ⟨e, he', hxe⟩ := (τ.subTube hlam_ab hNa hNb).Γ.exists_edge_of_mem hxU' hxV'
        have he : e ∈ {ed ∈ τ.Γ.E | ed ⊆ cylinderBetween Ha Hb} :=
          interSet_E τ.Γ (cylinderBetween Ha Hb) ▸
            (show e ∈ (τ.Γ.interSet (cylinderBetween Ha Hb)).E from he')
        have he_F₁H : e ∈ {ed ∈ τ.Γ.E | ed ⊆ cylinderBetween τ.F₁ H} :=
          hc2.symm ▸ ⟨he.1, he.2.trans hab_F₁b⟩
        exact he_F₁H.2 hxe
    refine ⟨hU_sub, Subset.antisymm ?_ ?_⟩
    · rintro x ⟨hxH, hxV'⟩
      obtain ⟨hxV, hx_ab⟩ := hV' ▸ hxV'
      have hlam_HF₂ : AreLaminarHoops H τ.F₂ :=
        (cap.areLaminarHoops_iff τ.isCylinder hH τ.isHoop_F₂).mpr (Or.inl hHF₂)
      have hx_bF₂ : x ∈ cylinderBetween Hb τ.F₂ :=
        (hc3.subset ⟨hxV, subset_cylinderBetween_left hlam_HF₂ hxH⟩).2
      have hxHb : x ∈ Hb :=
        cap.cylinderBetween_inter τ.isCylinder hHa hHb τ.isHoop_F₂ hab hbF₂ ▸ ⟨hx_ab, hx_bF₂⟩
      exact ⟨hxHb, hxV'⟩
    · rintro x ⟨hxHb, hxV'⟩
      obtain ⟨hxV, hx_ab⟩ := hV' ▸ hxV'
      have hx1 : x ∈ cylinderBetween Ha H :=
        hU_sub (hU'.symm ▸ ⟨τ.Γ.V_subset_U hxV, hx_ab⟩)
      have hx2 : x ∈ cylinderBetween H Hb := subset_cylinderBetween_right hlam_Hb hxHb
      exact ⟨cap.cylinderBetween_inter τ.isCylinder hHa hH hHb haH hHb_le ▸ ⟨hx1, hx2⟩, hxV'⟩

/-- Special case of `subTube_isCutTrivial_of_hoopSignature_eq` on `τ` itself. -/
private theorem Tube.isCutTrivial_of_hoopSignature_eq (τ : Tube S) (cap : CylinderSphereCap S)
    {H : Set S} (hH : IsHoop H)
    (h1 : cap.disc₁ τ.isCylinder.1 τ.isHoop_F₁ ⊆ cap.disc₁ τ.isCylinder.1 hH)
    (h2 : cap.disc₁ τ.isCylinder.1 hH ⊆ cap.disc₁ τ.isCylinder.1 τ.isHoop_F₂)
    (heq : τ.hoopSignature H = τ.hoopSignature τ.F₁ ∨ τ.hoopSignature H = τ.hoopSignature τ.F₂) :
    τ.IsCutTrivial H := by
  have h := τ.subTube_isCutTrivial_of_hoopSignature_eq cap τ.isHoop_F₁ hH τ.isHoop_F₂
    τ.isNormal_F₁ τ.isNormal_F₂ Subset.rfl h1 h2 Subset.rfl (hlam_ab := τ.laminar) heq
  rwa [τ.subTube_self] at h

end SubTubeAndSignature

/-! ## 2. Sub-framed Graft Classes and the Proof of (15.1) -/

section Theorem15_1

variable {S : Type w} [TopologicalSpace S] {α : Type u} {β : Type v}

/-- The class of grafts of index `≤ k` admitting a sub-tube of `τ` of width `≥ r` as a framing.
Working with this sub-framed class proves `(15.1)`, `(15.2)`, and `(15.3)` together. -/
def Tube.subFramedClass (τ : Tube S) (r k : ℕ) : Set (Graft α β) :=
  {Y : Graft α β | Y.index ≤ k ∧
    ∃ (F₁' F₂' : Set S) (hlam : AreLaminarHoops F₁' F₂')
      (_ : F₁' ⊆ cylinderBetween τ.F₁ τ.F₂) (_ : F₂' ⊆ cylinderBetween τ.F₁ τ.F₂)
      (hN₁ : τ.Γ.IsNormal F₁') (hN₂ : τ.Γ.IsNormal F₂'),
      (τ.subTube hlam hN₁ hN₂).IsFraming Y ∧
      (r : ℕ∞) ≤ (τ.subTube hlam hN₁ hN₂).width}

theorem Tube.subFramedClass_subset_tubularClass (τ : Tube S) (r k : ℕ) :
    τ.subFramedClass (α := α) (β := β) r k ⊆ tubularClass r k := by
  rintro Y ⟨hk, _, _, _, _, _, _, _, hfr, hw⟩
  exact ⟨IsTubularGraft.of_framing hfr, hw.trans (le_tubularWidth_of_framing hfr), hk⟩

theorem Tube.mem_subFramedClass_self (τ : Tube S) {r k : ℕ} {X : Graft α β}
    (hk : X.index ≤ k) (hfr : τ.IsFraming X) (hw : (r : ℕ∞) ≤ τ.width) :
    X ∈ τ.subFramedClass r k := by
  refine ⟨hk, τ.F₁, τ.F₂, τ.laminar, subset_cylinderBetween_left τ.laminar,
    subset_cylinderBetween_right τ.laminar, τ.isNormal_F₁, τ.isNormal_F₂, ?_, ?_⟩
  · rwa [τ.subTube_self]
  · rwa [τ.subTube_self]

theorem Tube.subTube_subFramedClass_subset (τ : Tube S) {F₁' F₂' : Set S}
    (hlam : AreLaminarHoops F₁' F₂')
    (hsub₁ : F₁' ⊆ cylinderBetween τ.F₁ τ.F₂) (hsub₂ : F₂' ⊆ cylinderBetween τ.F₁ τ.F₂)
    (hN₁ : τ.Γ.IsNormal F₁') (hN₂ : τ.Γ.IsNormal F₂') (r k : ℕ) :
    (τ.subTube hlam hN₁ hN₂).subFramedClass (α := α) (β := β) r k ⊆ τ.subFramedClass r k := by
  rintro Y ⟨hk, H₁, H₂, hlam', hH₁, hH₂, hNH₁', hNH₂', hfr, hw⟩
  have hcyl_sub : cylinderBetween F₁' F₂' ⊆ cylinderBetween τ.F₁ τ.F₂ :=
    cylinderBetween_subset_cylinderBetween τ.laminar hlam hsub₁ hsub₂
  have hNH₁ : τ.Γ.IsNormal H₁ := (τ.subTube_isNormal_iff hlam hN₁ hN₂ hH₁).mp hNH₁'
  have hNH₂ : τ.Γ.IsNormal H₂ := (τ.subTube_isNormal_iff hlam hN₁ hN₂ hH₂).mp hNH₂'
  have heq := τ.subTube_subTube hlam hN₁ hN₂ hlam' hH₁ hH₂ hNH₁' hNH₂'
  refine ⟨hk, H₁, H₂, hlam', hH₁.trans hcyl_sub, hH₂.trans hcyl_sub, hNH₁, hNH₂, ?_, ?_⟩
  · rwa [← heq]
  · rwa [← heq]

/-- An ordered chain `F₁ = H₀, H₁, …, H_n, H_{n+1} = F₂` of `τ.Γ`-normal hoops of size `≤ r`
with strictly advancing `hoopSignature` along `cap`. -/
private structure ValidHoopChain (τ : Tube S) (cap : CylinderSphereCap S) (r n : ℕ) where
  H : Fin (n + 2) → Set S
  first_eq : H ⟨0, by omega⟩ = τ.F₁
  last_eq : H (Fin.last (n + 1)) = τ.F₂
  isHoop : ∀ i : Fin (n + 2), IsHoop (H i)
  isNormal : ∀ i : Fin (n + 2), τ.Γ.IsNormal (H i)
  card_le : ∀ (i : ℕ) (hi : i < n + 2), 1 ≤ i → i ≤ n → (H ⟨i, hi⟩ ∩ τ.Γ.V).ncard ≤ r
  disc₁_mono : ∀ i : Fin (n + 1),
    cap.disc₁ τ.isCylinder.1 (isHoop i.castSucc) ⊆ cap.disc₁ τ.isCylinder.1 (isHoop i.succ)
  sig_ne : ∀ i : Fin (n + 1), τ.hoopSignature (H i.castSucc) ≠ τ.hoopSignature (H i.succ)

private theorem ValidHoopChain.disc₁_le_of_le {τ : Tube S} {cap : CylinderSphereCap S} {r n : ℕ}
    (ch : ValidHoopChain τ cap r n) {i j : Fin (n + 2)} (hij : i ≤ j) :
    cap.disc₁ τ.isCylinder.1 (ch.isHoop i) ⊆ cap.disc₁ τ.isCylinder.1 (ch.isHoop j) := by
  have haux : ∀ d : ℕ, ∀ (a : ℕ) (ha : a + d < n + 2),
      cap.disc₁ τ.isCylinder.1 (ch.isHoop ⟨a, by omega⟩) ⊆
        cap.disc₁ τ.isCylinder.1 (ch.isHoop ⟨a + d, ha⟩) := by
    intro d
    induction d with
    | zero => intro a ha; exact Subset.rfl
    | succ d ih =>
      intro a ha
      exact (ih a (by omega)).trans (ch.disc₁_mono ⟨a + d, by omega⟩)
  obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le (show i.1 ≤ j.1 from hij)
  have hj_eq : (⟨i.1 + d, by omega⟩ : Fin (n + 2)) = j := Fin.ext hd.symm
  exact hj_eq ▸ haux d i.1 (by omega)

private theorem ValidHoopChain.disc₁_F₁_le {τ : Tube S} {cap : CylinderSphereCap S} {r n : ℕ}
    (ch : ValidHoopChain τ cap r n) (i : Fin (n + 2)) :
    cap.disc₁ τ.isCylinder.1 τ.isHoop_F₁ ⊆ cap.disc₁ τ.isCylinder.1 (ch.isHoop i) :=
  cap.disc₁_congr τ.isCylinder.1 (ch.isHoop ⟨0, by omega⟩) τ.isHoop_F₁ ch.first_eq ▸
    ch.disc₁_le_of_le (Fin.zero_le i)

private theorem ValidHoopChain.disc₁_le_F₂ {τ : Tube S} {cap : CylinderSphereCap S} {r n : ℕ}
    (ch : ValidHoopChain τ cap r n) (i : Fin (n + 2)) :
    cap.disc₁ τ.isCylinder.1 (ch.isHoop i) ⊆ cap.disc₁ τ.isCylinder.1 τ.isHoop_F₂ :=
  cap.disc₁_congr τ.isCylinder.1 (ch.isHoop (Fin.last (n + 1))) τ.isHoop_F₂ ch.last_eq ▸
    ch.disc₁_le_of_le (Fin.le_last i)

private theorem ValidHoopChain.subset_cylinderBetween {τ : Tube S} {cap : CylinderSphereCap S}
    {r n : ℕ} (ch : ValidHoopChain τ cap r n) (i : Fin (n + 2)) :
    ch.H i ⊆ cylinderBetween τ.F₁ τ.F₂ := by
  have hle₀ : cap.disc₁ τ.isCylinder.1 τ.isHoop_F₁ ⊆ cap.disc₁ τ.isCylinder.1 τ.isHoop_F₂ :=
    (ch.disc₁_F₁_le i).trans (ch.disc₁_le_F₂ i)
  exact (cap.hoop_subset_cylinderBetween_iff τ.isCylinder τ.isHoop_F₁ τ.isHoop_F₂
    (ch.isHoop i) hle₀).mpr ⟨ch.disc₁_F₁_le i, ch.disc₁_le_F₂ i⟩

private theorem ValidHoopChain.hoopSignature_injective {τ : Tube S} {cap : CylinderSphereCap S}
    {r n : ℕ} (ch : ValidHoopChain τ cap r n) :
    Injective (fun i : Fin (n + 2) => τ.hoopSignature (ch.H i)) := by
  have hlt : ∀ {i j : Fin (n + 2)}, i < j →
      τ.hoopSignature (ch.H i) ≠ τ.hoopSignature (ch.H j) := by
    intro i j hij heq
    have hi_lt : i.1 < n + 1 := by have := j.2; change i.1 < j.1 at hij; omega
    let i' : Fin (n + 1) := ⟨i.1, hi_lt⟩
    have hi'_cs : i'.castSucc = i := Fin.ext rfl
    have hsucc_le : i'.succ ≤ j := by change i.1 + 1 ≤ j.1; change i.1 < j.1 at hij; omega
    have h12 : cap.disc₁ τ.isCylinder.1 (ch.isHoop i) ⊆
        cap.disc₁ τ.isCylinder.1 (ch.isHoop i'.succ) :=
      hi'_cs ▸ ch.disc₁_mono i'
    have h23 : cap.disc₁ τ.isCylinder.1 (ch.isHoop i'.succ) ⊆
        cap.disc₁ τ.isCylinder.1 (ch.isHoop j) :=
      ch.disc₁_le_of_le hsucc_le
    have heq' := τ.hoopSignature_eq_of_between cap (ch.isHoop i) (ch.isHoop i'.succ)
      (ch.isHoop j) (ch.disc₁_F₁_le i) h12 h23 (ch.disc₁_le_F₂ j) heq
    exact ch.sig_ne i' (hi'_cs.symm ▸ heq')
  intro i j heq
  rcases lt_trichotomy i j with h | h | h
  · exact absurd heq (hlt h)
  · exact h
  · exact absurd heq.symm (hlt h)

/-- **Lemma 3 of the printed (15.1), with its chain of hoops.** A tube of side-qualified width
`≥ r` has a path-decomposition into sub-tubes of width `≥ r + 1`, cut along a chain of hoops
`F₁ = H 0, H 1, …, H m = F₂`. Its junctions are the vertex sets of these hoops, and the inner hoops
are not cut-trivial and carry exactly `r` vertices. This is the argument of
`Tube.subFramedClass_subset_LKGraftClass`, which is derived from it below. -/
theorem Tube.exists_chain_decomposition (σ : Tube S) {Y : Graft α β} (fr : σ.Framing Y)
    {r k : ℕ} (hk : Y.index ≤ k) (hw : (r : ℕ∞) ≤ σ.width) :
    ∃ (D : GraftPathDecomposition (σ.subFramedClass (r + 1) (k + 2 * r)) Y) (H : ℕ → Set S),
      H 0 = σ.F₁ ∧ H D.r = σ.F₂ ∧
      (∀ i, i ≤ D.r → IsHoop (H i) ∧ σ.Γ.IsNormal (H i) ∧ H i ⊆ cylinderBetween σ.F₁ σ.F₂) ∧
      (∀ i j, i < j → j ≤ D.r → AreLaminarHoops (H i) (H j)) ∧
      (∀ i, i ≤ D.r → D.Yn i = fr.vertsIn (H i)) ∧
      (∀ i, 1 ≤ i → i < D.r → (D.Yn i).ncard = r ∧ ¬ σ.IsCutTrivial (H i)) := by
  classical
  by_cases hw1 : ((r + 1 : ℕ) : ℕ∞) ≤ σ.width
  · have hsub : fr.vertsIn σ.F₁ ∪ fr.vertsIn σ.F₂ ⊆ V(Y.G) := fr.vertsIn_F_union ▸ Y.T_subset
    have hm : Graft.mk Y.G (fr.vertsIn σ.F₁ ∪ fr.vertsIn σ.F₂) hsub Y.finite_G ∈
        σ.subFramedClass (r + 1) (k + 2 * r) := by
      have hY : Graft.mk Y.G (fr.vertsIn σ.F₁ ∪ fr.vertsIn σ.F₂) hsub Y.finite_G = Y := by
        cases Y
        simp only [Graft.mk.injEq, true_and]
        exact fr.vertsIn_F_union
      rw [hY]
      exact σ.mem_subFramedClass_self (by omega) ⟨fr⟩ hw1
    refine ⟨GraftPathDecomposition.single hsub hm fr.vertsIn_F_union.symm,
      fun i => if i = 0 then σ.F₁ else σ.F₂, rfl, ?_, ?_, ?_, ?_, ?_⟩
    · simp [GraftPathDecomposition.single_r]
    · intro i _
      dsimp only
      split_ifs
      · exact ⟨σ.isHoop_F₁, σ.isNormal_F₁, subset_cylinderBetween_left σ.laminar⟩
      · exact ⟨σ.isHoop_F₂, σ.isNormal_F₂, subset_cylinderBetween_right σ.laminar⟩
    · intro i j hij hj
      rw [GraftPathDecomposition.single_r] at hj
      obtain rfl : i = 0 := by omega
      obtain rfl : j = 1 := by omega
      simpa using σ.laminar
    · intro i hi
      rw [GraftPathDecomposition.single_r] at hi
      rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hi with rfl | rfl
      · simpa using GraftPathDecomposition.single_Yn_zero
      · simpa using GraftPathDecomposition.single_Yn_one
    · intro i h1 h2
      rw [GraftPathDecomposition.single_r] at h2
      omega
  · have : T2Space S := σ.t2Space
    obtain ⟨cap, hle₀⟩ := CylinderSphereCap.exists_oriented σ.isCylinder σ.isHoop_F₁ σ.isHoop_F₂
      σ.laminar
    -- Since ¬ (r + 1 ≤ σ.width), there exists at least one non-cut-trivial normal hoop of size ≤ r
    have hex1 : Nonempty (ValidHoopChain σ cap r 1) := by
      have hnot := mt (le_width_iff σ).mpr hw1
      push Not at hnot
      obtain ⟨H₁, hH₁, hNH₁, hsub₁, hnct₁, hlt₁⟩ := hnot
      have hcard₁ : (H₁ ∩ σ.Γ.V).ncard ≤ r := by
        have hlt_nat : (H₁ ∩ σ.Γ.V).ncard < r + 1 := Nat.cast_lt (α := ℕ∞).mp hlt₁
        omega
      obtain ⟨hF₁H₁, hH₁F₂⟩ :=
        (cap.hoop_subset_cylinderBetween_iff σ.isCylinder σ.isHoop_F₁ σ.isHoop_F₂ hH₁ hle₀).mp hsub₁
      have hne_sig : σ.hoopSignature σ.F₁ ≠ σ.hoopSignature H₁ ∧
          σ.hoopSignature H₁ ≠ σ.hoopSignature σ.F₂ := by
        refine ⟨fun h => hnct₁ (σ.isCutTrivial_of_hoopSignature_eq cap hH₁ hF₁H₁ hH₁F₂
            (Or.inl h.symm)),
          fun h => hnct₁ (σ.isCutTrivial_of_hoopSignature_eq cap hH₁ hF₁H₁ hH₁F₂ (Or.inr h))⟩
      let Hseq : Fin 3 → Set S := ![σ.F₁, H₁, σ.F₂]
      have hHoop : ∀ i : Fin 3, IsHoop (Hseq i) := by
        intro i; fin_cases i
        · exact σ.isHoop_F₁
        · exact hH₁
        · exact σ.isHoop_F₂
      have hNorm : ∀ i : Fin 3, σ.Γ.IsNormal (Hseq i) := by
        intro i; fin_cases i
        · exact σ.isNormal_F₁
        · exact hNH₁
        · exact σ.isNormal_F₂
      refine ⟨{
        H := Hseq
        first_eq := rfl
        last_eq := rfl
        isHoop := hHoop
        isNormal := hNorm
        card_le := fun i hi h1 hle => by
          have hi1 : i = 1 := by omega
          subst hi1
          exact hcard₁
        disc₁_mono := fun i => by
          fin_cases i
          · exact hF₁H₁
          · exact hH₁F₂
        sig_ne := fun i => by
          fin_cases i
          · exact hne_sig.1
          · exact hne_sig.2 }⟩
    -- Boundedness of chain lengths via `finite_range_hoopSignature`
    let NS : Set ℕ := {n : ℕ | Nonempty (ValidHoopChain σ cap r n)}
    have hNS_ne : NS.Nonempty := ⟨1, hex1⟩
    have hNS_bdd : BddAbove NS := by
      refine ⟨(range σ.hoopSignature).ncard, fun n ⟨ch⟩ => ?_⟩
      have hsub : range (fun i : Fin (n + 2) => σ.hoopSignature (ch.H i)) ⊆
          range σ.hoopSignature := by
        rintro _ ⟨i, rfl⟩; exact ⟨ch.H i, rfl⟩
      have hle_card : (range (fun i : Fin (n + 2) => σ.hoopSignature (ch.H i))).ncard ≤
          (range σ.hoopSignature).ncard :=
        ncard_le_ncard hsub σ.finite_range_hoopSignature
      rw [ncard_range_of_injective ch.hoopSignature_injective, Nat.card_fin] at hle_card
      omega
    obtain ⟨ch⟩ : Nonempty (ValidHoopChain σ cap r (sSup NS)) := Nat.sSup_mem hNS_ne hNS_bdd
    set n := sSup NS
    have hn_ge_1 : 1 ≤ n := le_csSup hNS_bdd hex1
    -- Laminarity of consecutive hoops in `ch`
    have hlam_step : ∀ i : Fin (n + 1), AreLaminarHoops (ch.H i.castSucc) (ch.H i.succ) :=
      fun i => (cap.areLaminarHoops_iff σ.isCylinder (ch.isHoop i.castSucc)
        (ch.isHoop i.succ)).mpr (Or.inl (ch.disc₁_mono i))
    -- Maximality of `n` implies each sub-tube has width ≥ r + 1
    have hwidth_step : ∀ i : Fin (n + 1),
        ((r + 1 : ℕ) : ℕ∞) ≤
          (σ.subTube (hlam_step i) (ch.isNormal i.castSucc) (ch.isNormal i.succ)).width := by
      intro i₀
      by_contra hlt_w
      have hnot := mt (le_width_iff _).mpr hlt_w
      push Not at hnot
      obtain ⟨K, hK, hNK', hK_sub, hnctK, hK_lt⟩ := hnot
      have hNK : σ.Γ.IsNormal K :=
        (σ.subTube_isNormal_iff (hlam_step i₀) (ch.isNormal i₀.castSucc)
          (ch.isNormal i₀.succ) hK_sub).mp hNK'
      have hK_card : (K ∩ σ.Γ.V).ncard ≤ r := by
        have hcl_i : IsClosed (cylinderBetween (ch.H i₀.castSucc) (ch.H i₀.succ)) :=
          isClosed_cylinderBetween (hlam_step i₀)
        have hKV_eq : K ∩ (σ.subTube (hlam_step i₀) (ch.isNormal i₀.castSucc)
            (ch.isNormal i₀.succ)).Γ.V = K ∩ σ.Γ.V := by
          change K ∩ (σ.Γ.interSet _).V = K ∩ σ.Γ.V
          rw [interSet_V_of_isClosed _ hcl_i]
          ext x
          exact ⟨fun ⟨hxK, hxV, _⟩ => ⟨hxK, hxV⟩, fun ⟨hxK, hxV⟩ => ⟨hxK, hxV, hK_sub hxK⟩⟩
        rw [hKV_eq] at hK_lt
        have hlt_nat : (K ∩ σ.Γ.V).ncard < r + 1 := Nat.cast_lt (α := ℕ∞).mp hK_lt
        omega
      obtain ⟨hiK, hKi1⟩ :=
        (cap.hoop_subset_cylinderBetween_iff σ.isCylinder (ch.isHoop i₀.castSucc)
          (ch.isHoop i₀.succ) hK (ch.disc₁_mono i₀)).mp hK_sub
      have hK_sig_ne : σ.hoopSignature K ≠ σ.hoopSignature (ch.H i₀.castSucc) ∧
          σ.hoopSignature K ≠ σ.hoopSignature (ch.H i₀.succ) := by
        refine ⟨fun heq => hnctK (σ.subTube_isCutTrivial_of_hoopSignature_eq cap
            (ch.isHoop i₀.castSucc) hK (ch.isHoop i₀.succ)
            (ch.isNormal i₀.castSucc) (ch.isNormal i₀.succ)
            (ch.disc₁_F₁_le i₀.castSucc) hiK hKi1 (ch.disc₁_le_F₂ i₀.succ)
            (hlam_ab := hlam_step i₀) (Or.inl heq)),
          fun heq => hnctK (σ.subTube_isCutTrivial_of_hoopSignature_eq cap
            (ch.isHoop i₀.castSucc) hK (ch.isHoop i₀.succ)
            (ch.isNormal i₀.castSucc) (ch.isNormal i₀.succ)
            (ch.disc₁_F₁_le i₀.castSucc) hiK hKi1 (ch.disc₁_le_F₂ i₀.succ)
            (hlam_ab := hlam_step i₀) (Or.inr heq))⟩
      let H' : Fin (n + 1 + 2) → Set S := fun j =>
        if hj1 : j.1 ≤ i₀.1 then ch.H ⟨j.1, by omega⟩
        else if j.1 = i₀.1 + 1 then K
        else ch.H ⟨j.1 - 1, by omega⟩
      have hH'_hoop : ∀ j : Fin (n + 1 + 2), IsHoop (H' j) := fun j => by
        dsimp only [H']
        split_ifs with h1 h2
        · exact ch.isHoop ⟨j.1, by omega⟩
        · exact hK
        · exact ch.isHoop ⟨j.1 - 1, by omega⟩
      have hH'_norm : ∀ j : Fin (n + 1 + 2), σ.Γ.IsNormal (H' j) := fun j => by
        dsimp only [H']
        split_ifs with h1 h2
        · exact ch.isNormal ⟨j.1, by omega⟩
        · exact hNK
        · exact ch.isNormal ⟨j.1 - 1, by omega⟩
      have ch' : ValidHoopChain σ cap r (n + 1) := {
        H := H'
        first_eq := by
          have h0 : (0 : ℕ) ≤ i₀.1 := Nat.zero_le _
          simp only [H', h0, ↓reduceDIte]
          exact ch.first_eq
        last_eq := by
          have h1 : ¬ (n + 1 + 1 ≤ i₀.1) := by have := i₀.2; omega
          have h2 : n + 1 + 1 ≠ i₀.1 + 1 := by have := i₀.2; omega
          change H' ⟨n + 1 + 1, by omega⟩ = σ.F₂
          simp only [H', h1, h2, ↓reduceDIte, ↓reduceIte]
          exact ch.last_eq
        isHoop := hH'_hoop
        isNormal := hH'_norm
        card_le := fun j hj h1 hle => by
          dsimp only [H']
          split_ifs with hc1 hc2
          · exact ch.card_le j (by omega) h1 (by have := i₀.2; omega)
          · exact hK_card
          · exact ch.card_le (j - 1) (by omega) (by omega) (by omega)
        disc₁_mono := fun j => by
          by_cases hlt : j.1 < i₀.1
          · have hcs : H' j.castSucc = ch.H ⟨j.1, by omega⟩ := by
              change H' ⟨j.1, _⟩ = _; simp [H', show j.1 ≤ i₀.1 by omega]
            have hsc : H' j.succ = ch.H ⟨j.1 + 1, by omega⟩ := by
              change H' ⟨j.1 + 1, _⟩ = _; simp [H', show j.1 + 1 ≤ i₀.1 by omega]
            rw [cap.disc₁_congr σ.isCylinder.1 _ (ch.isHoop ⟨j.1, by omega⟩) hcs,
              cap.disc₁_congr σ.isCylinder.1 _ (ch.isHoop ⟨j.1 + 1, by omega⟩) hsc]
            exact ch.disc₁_mono ⟨j.1, by omega⟩
          · by_cases heq0 : j.1 = i₀.1
            · have hcs : H' j.castSucc = ch.H i₀.castSucc := by
                change H' ⟨j.1, _⟩ = ch.H ⟨i₀.1, _⟩
                simp [H', heq0]
              have hsc : H' j.succ = K := by
                change H' ⟨j.1 + 1, _⟩ = K
                simp [H', heq0]
              rw [cap.disc₁_congr σ.isCylinder.1 _ (ch.isHoop i₀.castSucc) hcs,
                cap.disc₁_congr σ.isCylinder.1 _ hK hsc]
              exact hiK
            · by_cases heq1 : j.1 = i₀.1 + 1
              · have hcs : H' j.castSucc = K := by
                  change H' ⟨j.1, _⟩ = K
                  simp [H', heq1]
                have hsc : H' j.succ = ch.H i₀.succ := by
                  change H' ⟨j.1 + 1, _⟩ = ch.H ⟨i₀.1 + 1, _⟩
                  simp [H', heq1, show ¬ (i₀.1 + 1 + 1 ≤ i₀.1) by omega]
                rw [cap.disc₁_congr σ.isCylinder.1 _ hK hcs,
                  cap.disc₁_congr σ.isCylinder.1 _ (ch.isHoop i₀.succ) hsc]
                exact hKi1
              · have hgt : i₀.1 + 1 < j.1 := by omega
                have hcs : H' j.castSucc = ch.H ⟨j.1 - 1, by omega⟩ := by
                  change H' ⟨j.1, _⟩ = _
                  simp [H', show ¬ (j.1 ≤ i₀.1) by omega, show j.1 ≠ i₀.1 + 1 by omega]
                have hsc : H' j.succ = ch.H (⟨j.1 - 1, by have := j.2; omega⟩ : Fin (n + 1)).succ := by
                  have hidx : (⟨j.1, by omega⟩ : Fin (n + 2)) =
                      (⟨j.1 - 1, by have := j.2; omega⟩ : Fin (n + 1)).succ :=
                    Fin.ext (by change j.1 = j.1 - 1 + 1; omega)
                  rw [← hidx]
                  change H' ⟨j.1 + 1, _⟩ = _
                  simp [H', show ¬ (j.1 + 1 ≤ i₀.1) by omega, heq0]
                rw [cap.disc₁_congr σ.isCylinder.1 _ (ch.isHoop ⟨j.1 - 1, by omega⟩) hcs,
                  cap.disc₁_congr σ.isCylinder.1 _
                    (ch.isHoop (⟨j.1 - 1, by have := j.2; omega⟩ : Fin (n + 1)).succ) hsc]
                exact ch.disc₁_mono ⟨j.1 - 1, by have := j.2; omega⟩
        sig_ne := fun j => by
          by_cases hlt : j.1 < i₀.1
          · have hcs : H' j.castSucc = ch.H ⟨j.1, by omega⟩ := by
              change H' ⟨j.1, _⟩ = _; simp [H', show j.1 ≤ i₀.1 by omega]
            have hsc : H' j.succ = ch.H ⟨j.1 + 1, by omega⟩ := by
              change H' ⟨j.1 + 1, _⟩ = _; simp [H', show j.1 + 1 ≤ i₀.1 by omega]
            rw [hcs, hsc]
            exact ch.sig_ne ⟨j.1, by omega⟩
          · by_cases heq0 : j.1 = i₀.1
            · have hcs : H' j.castSucc = ch.H i₀.castSucc := by
                change H' ⟨j.1, _⟩ = ch.H ⟨i₀.1, _⟩; simp [H', heq0]
              have hsc : H' j.succ = K := by
                change H' ⟨j.1 + 1, _⟩ = K; simp [H', heq0]
              rw [hcs, hsc]
              exact hK_sig_ne.1.symm
            · by_cases heq1 : j.1 = i₀.1 + 1
              · have hcs : H' j.castSucc = K := by
                  change H' ⟨j.1, _⟩ = K; simp [H', heq1]
                have hsc : H' j.succ = ch.H i₀.succ := by
                  change H' ⟨j.1 + 1, _⟩ = ch.H ⟨i₀.1 + 1, _⟩
                  simp [H', heq1, show ¬ (i₀.1 + 1 + 1 ≤ i₀.1) by omega]
                rw [hcs, hsc]
                exact hK_sig_ne.2
              · have hcs : H' j.castSucc = ch.H ⟨j.1 - 1, by omega⟩ := by
                  change H' ⟨j.1, _⟩ = _
                  simp [H', show ¬ (j.1 ≤ i₀.1) by omega, show j.1 ≠ i₀.1 + 1 by omega]
                have hsc : H' j.succ = ch.H ⟨j.1, by omega⟩ := by
                  change H' ⟨j.1 + 1, _⟩ = _
                  simp [H', show ¬ (j.1 + 1 ≤ i₀.1) by omega, heq0]
                rw [hcs, hsc]
                have hstep := ch.sig_ne ⟨j.1 - 1, by have := j.2; omega⟩
                simpa [show j.1 - 1 + 1 = j.1 by omega] using hstep }
      have hmem_succ : n + 1 ∈ NS := ⟨ch'⟩
      have hle_succ : n + 1 ≤ n := le_csSup hNS_bdd hmem_succ
      omega
    -- Non-cut-triviality of every interior hoop `ch.H j` (`1 ≤ j ≤ n`) in `σ`
    have hnct_interior : ∀ (j : ℕ) (hj : j < n + 2), 1 ≤ j → j ≤ n →
        ¬ σ.IsCutTrivial (ch.H ⟨j, hj⟩) := by
      intro j hj h1 hle hct
      have hct' : (σ.subTube σ.laminar σ.isNormal_F₁ σ.isNormal_F₂).IsCutTrivial (ch.H ⟨j, hj⟩) :=
        σ.subTube_self.symm ▸ hct
      rcases σ.hoopSignature_eq_of_subTube_isCutTrivial cap σ.isHoop_F₁ (ch.isHoop ⟨j, hj⟩)
          σ.isHoop_F₂ σ.isNormal_F₁ (ch.isNormal ⟨j, hj⟩) σ.isNormal_F₂
          Subset.rfl (ch.disc₁_F₁_le ⟨j, hj⟩) (ch.disc₁_le_F₂ ⟨j, hj⟩) Subset.rfl hct'
        with heq | heq
      · rw [← ch.first_eq] at heq
        have hidx := ch.hoopSignature_injective heq
        have hval := congrArg Fin.val hidx
        dsimp only at hval
        omega
      · rw [← ch.last_eq] at heq
        have hidx := ch.hoopSignature_injective heq
        have hval := congrArg Fin.val hidx
        change j = n + 1 at hval
        omega
    -- Exact cardinality `|Y_j| = r` for `1 ≤ j ≤ n`
    have hcard_interior : ∀ (j : ℕ) (hj : j < n + 2), 1 ≤ j → j ≤ n →
        (fr.vertsIn (ch.H ⟨j, hj⟩)).ncard = r := by
      intro j hj h1 hle
      rw [fr.ncard_vertsIn]
      apply le_antisymm (ch.card_le j hj h1 hle)
      have hge := ((le_width_iff σ).mp hw (ch.H ⟨j, hj⟩) (ch.isHoop ⟨j, hj⟩)
        (ch.isNormal ⟨j, hj⟩) (ch.subset_cylinderBetween ⟨j, hj⟩)).resolve_left
        (hnct_interior j hj h1 hle)
      exact Nat.cast_le (α := ℕ∞).mp hge
    -- Inductive union & edge-covering of `Σ(H_0, H_{m+1})`
    let A : Fin (n + 1) → Set S := fun i => cylinderBetween (ch.H i.castSucc) (ch.H i.succ)
    have hA_closed : ∀ i : Fin (n + 1), IsClosed (A i) :=
      fun i => isClosed_cylinderBetween (hlam_step i)
    have hA_union_step : ∀ (m : ℕ) (hm : m ≤ n),
        cylinderBetween (ch.H ⟨0, by omega⟩) (ch.H ⟨m + 1, by omega⟩) =
          ⋃ (i : Fin (n + 1)) (_ : i.1 ≤ m), A i := by
      intro m
      induction m with
      | zero =>
        intro hm
        apply Subset.antisymm
        · intro x hx
          exact mem_iUnion₂.mpr ⟨⟨0, by omega⟩, le_rfl, hx⟩
        · refine iUnion₂_subset fun i hi => ?_
          have hi0 : i = ⟨0, by omega⟩ := Fin.ext (Nat.eq_zero_of_le_zero hi)
          rw [hi0]
          exact Subset.rfl
      | succ m ih =>
        intro hm
        have hunion := cap.cylinderBetween_union σ.isCylinder
          (ch.isHoop ⟨0, by omega⟩) (ch.isHoop ⟨m + 1, by omega⟩) (ch.isHoop ⟨m + 2, by omega⟩)
          (ch.disc₁_le_of_le (show (⟨0, by omega⟩ : Fin (n + 2)) ≤ ⟨m + 1, by omega⟩ by
            change 0 ≤ m + 1; omega))
          (ch.disc₁_mono ⟨m + 1, by omega⟩)
        rw [← hunion, ih (by omega)]
        ext x
        simp only [mem_union, mem_iUnion, exists_prop]
        constructor
        · rintro (⟨i, hi, hx⟩ | hx)
          · exact ⟨i, by omega, hx⟩
          · exact ⟨⟨m + 1, by omega⟩, le_rfl, hx⟩
        · rintro ⟨i, hi, hx⟩
          rcases eq_or_lt_of_le hi with heq | hlt
          · right
            have hi_eq : i = ⟨m + 1, by omega⟩ := Fin.ext heq
            rw [hi_eq] at hx
            exact hx
          · left
            exact ⟨i, by omega, hx⟩
    have hA_iUnion : (⋃ i : Fin (n + 1), A i) = cylinderBetween σ.F₁ σ.F₂ := by
      have h := hA_union_step n le_rfl
      have hlast_eq : (⟨n + 1, by omega⟩ : Fin (n + 2)) = Fin.last (n + 1) := Fin.ext rfl
      rw [ch.first_eq, hlast_eq, ch.last_eq] at h
      rw [h]
      ext x
      simp only [mem_iUnion, exists_prop]
      exact ⟨fun ⟨i, hx⟩ => ⟨i, by have := i.2; omega, hx⟩, fun ⟨i, _, hx⟩ => ⟨i, hx⟩⟩
    have hedge_cover_step : ∀ (m : ℕ) (hm : m ≤ n) {ed : Set S},
        ed ∈ σ.Γ.E → ed ⊆ cylinderBetween (ch.H ⟨0, by omega⟩) (ch.H ⟨m + 1, by omega⟩) →
        ∃ i : Fin (n + 1), i.1 ≤ m ∧ ed ⊆ A i := by
      intro m
      induction m with
      | zero =>
        intro hm ed _ hsub
        exact ⟨⟨0, by omega⟩, le_rfl, hsub⟩
      | succ m ih =>
        intro hm ed hed hsub
        have hle0m1 : cap.disc₁ σ.isCylinder.1 (ch.isHoop ⟨0, by omega⟩) ⊆
            cap.disc₁ σ.isCylinder.1 (ch.isHoop ⟨m + 2, by omega⟩) :=
          ch.disc₁_le_of_le (show (⟨0, by omega⟩ : Fin (n + 2)) ≤ ⟨m + 2, by omega⟩ by
            change 0 ≤ m + 2; omega)
        have hlam0m2 : AreLaminarHoops (ch.H ⟨0, by omega⟩) (ch.H ⟨m + 2, by omega⟩) :=
          (cap.areLaminarHoops_iff σ.isCylinder (ch.isHoop ⟨0, by omega⟩)
            (ch.isHoop ⟨m + 2, by omega⟩)).mpr (Or.inl hle0m1)
        have hm1_sub : ch.H ⟨m + 1, by omega⟩ ⊆
            cylinderBetween (ch.H ⟨0, by omega⟩) (ch.H ⟨m + 2, by omega⟩) :=
          (cap.hoop_subset_cylinderBetween_iff σ.isCylinder (ch.isHoop ⟨0, by omega⟩)
            (ch.isHoop ⟨m + 2, by omega⟩) (ch.isHoop ⟨m + 1, by omega⟩) hle0m1).mpr
            ⟨ch.disc₁_le_of_le (show (⟨0, by omega⟩ : Fin (n + 2)) ≤ ⟨m + 1, by omega⟩ by
              change 0 ≤ m + 1; omega),
             ch.disc₁_mono ⟨m + 1, by omega⟩⟩
        rcases edge_subset_cylinderBetween_left_or_right σ.Γ hlam0m2 (ch.isHoop ⟨m + 1, by omega⟩)
            hm1_sub (ch.isNormal ⟨m + 1, by omega⟩) hed hsub with ⟨hL, _⟩ | ⟨hR, _⟩
        · obtain ⟨i, hi, hsub_i⟩ := ih (by omega) hed hL
          exact ⟨i, by omega, hsub_i⟩
        · exact ⟨⟨m + 1, by omega⟩, le_rfl, hR⟩
    -- Assemble the `GraftPathDecomposition` of `Y`
    have hY_fin_T : Y.T.Finite := Y.finite_G.1.subset Y.T_subset
    have hcard_F₁ : (fr.vertsIn σ.F₁).ncard ≤ k := by
      have hsub : fr.vertsIn σ.F₁ ⊆ Y.T := fr.vertsIn_F_union ▸ subset_union_left
      exact (ncard_le_ncard hsub hY_fin_T).trans hk
    have hcard_F₂ : (fr.vertsIn σ.F₂).ncard ≤ k := by
      have hsub : fr.vertsIn σ.F₂ ⊆ Y.T := fr.vertsIn_F_union ▸ subset_union_right
      exact (ncard_le_ncard hsub hY_fin_T).trans hk
    let D : GraftPathDecomposition (σ.subFramedClass (r + 1) (k + 2 * r)) Y := {
      r := n + 1
      hr := by omega
      G := fun i => fr.subGraph (A i) (hA_closed i)
      Y := fun j => fr.vertsIn (ch.H j)
      Y_subset := fun i =>
        union_subset (fr.vertsIn_mono (subset_cylinderBetween_left (hlam_step i)))
          (fr.vertsIn_mono (subset_cylinderBetween_right (hlam_step i)))
      le_G := fun i => fr.subGraph_le (A i) (hA_closed i)
      mem_𝒜 := fun i => by
        have hpart_eq : Graft.mk (fr.subGraph (A i) (hA_closed i))
            (fr.vertsIn (ch.H i.castSucc) ∪ fr.vertsIn (ch.H i.succ))
            (union_subset (fr.vertsIn_mono (subset_cylinderBetween_left (hlam_step i)))
              (fr.vertsIn_mono (subset_cylinderBetween_right (hlam_step i))))
            ⟨Y.finite_G.1.subset (fr.subGraph_le (A i) (hA_closed i)).vertexSet_mono,
             Y.finite_G.2.subset (fr.subGraph_le (A i) (hA_closed i)).edgeSet_mono⟩ =
            fr.subGraft (hlam_step i) := Graft.ext rfl rfl
        rw [hpart_eq]
        have hidx_i : (fr.subGraft (hlam_step i)).index ≤ k + 2 * r := by
          change (fr.vertsIn (ch.H i.castSucc) ∪ fr.vertsIn (ch.H i.succ)).ncard ≤ k + 2 * r
          have hfin1 : (fr.vertsIn (ch.H i.castSucc)).Finite :=
            Y.finite_G.1.subset (fr.vertsIn_subset_V _)
          have hfin2 : (fr.vertsIn (ch.H i.succ)).Finite :=
            Y.finite_G.1.subset (fr.vertsIn_subset_V _)
          have hunion_le := ncard_union_le (fr.vertsIn (ch.H i.castSucc))
            (fr.vertsIn (ch.H i.succ))
          refine hunion_le.trans ?_
          by_cases hi0 : i.1 = 0
          · have hcs_eq : ch.H i.castSucc = σ.F₁ := by
              have h0 : i.castSucc = ⟨0, by omega⟩ := Fin.ext hi0
              exact h0 ▸ ch.first_eq
            have hsc_card : (fr.vertsIn (ch.H i.succ)).ncard = r :=
              hcard_interior (i.1 + 1) (by omega) (by omega) (by omega)
            rw [hcs_eq, hsc_card]
            omega
          · by_cases hin : i.1 = n
            · have hcs_card : (fr.vertsIn (ch.H i.castSucc)).ncard = r :=
                hcard_interior i.1 (by omega) (by omega) (by omega)
              have hsc_eq : ch.H i.succ = σ.F₂ := by
                have hlast : i.succ = Fin.last (n + 1) := Fin.ext (by change i.1 + 1 = n + 1; omega)
                exact hlast ▸ ch.last_eq
              rw [hcs_card, hsc_eq]
              omega
            · have hcs_card : (fr.vertsIn (ch.H i.castSucc)).ncard = r :=
                hcard_interior i.1 (by omega) (by omega) (by have := i.2; omega)
              have hsc_card : (fr.vertsIn (ch.H i.succ)).ncard = r :=
                hcard_interior (i.1 + 1) (by have := i.2; omega) (by omega) (by have := i.2; omega)
              rw [hcs_card, hsc_card]
              omega
        exact ⟨hidx_i, ch.H i.castSucc, ch.H i.succ, hlam_step i,
          ch.subset_cylinderBetween i.castSucc, ch.subset_cylinderBetween i.succ,
          ch.isNormal i.castSucc, ch.isNormal i.succ,
          fr.isFraming_subTube (hlam_step i) (ch.isNormal i.castSucc) (ch.isNormal i.succ),
          hwidth_step i⟩
      vertexSet_iUnion := by
        apply Subset.antisymm (iUnion_subset fun i => fr.vertsIn_subset_V (A i))
        intro v hv
        have hv_cyl : v ∈ fr.vertsIn (cylinderBetween σ.F₁ σ.F₂) :=
          fr.vertsIn_cylinderBetween_F.symm ▸ hv
        obtain ⟨_, hz⟩ := hv_cyl
        rw [← hA_iUnion, mem_iUnion] at hz
        obtain ⟨i, hzi⟩ := hz
        exact mem_iUnion.mpr ⟨i, hv, hzi⟩
      edgeSet_iUnion := by
        apply Subset.antisymm
        · refine iUnion_subset fun i => ?_
          rw [fr.subGraph_edgeSet]
          exact fr.edgesIn_subset_E (A i)
        · intro e he
          have he_cyl : e ∈ fr.edgesIn (cylinderBetween σ.F₁ σ.F₂) :=
            fr.edgesIn_cylinderBetween_F.symm ▸ he
          have hsub_all : (fr.iso.edgeEquiv ⟨e, he⟩).1 ⊆
              cylinderBetween (ch.H ⟨0, by omega⟩) (ch.H ⟨n + 1, by omega⟩) := by
            have hlast_eq : (⟨n + 1, by omega⟩ : Fin (n + 2)) = Fin.last (n + 1) := Fin.ext rfl
            rw [ch.first_eq, hlast_eq, ch.last_eq]
            exact he_cyl.2
          obtain ⟨i, _, hed_i⟩ :=
            hedge_cover_step n le_rfl (fr.iso.edgeEquiv ⟨e, he⟩).2 hsub_all
          refine mem_iUnion.mpr ⟨i, ?_⟩
          rw [fr.subGraph_edgeSet]
          exact ⟨he, hed_i⟩
      edge_disjoint := fun i j hij => by
        rw [fr.subGraph_edgeSet, fr.subGraph_edgeSet]
        refine disjoint_left.mpr fun e hei hej => ?_
        wlog hlt : i < j generalizing i j
        · exact this j i hij.symm hej hei ((lt_or_gt_of_ne hij).resolve_left hlt)
        have hle_ij : i.succ ≤ j.castSucc := by
          change i.1 + 1 ≤ j.1; change i.1 < j.1 at hlt; omega
        have hsubL : A i ⊆ cylinderBetween σ.F₁ (ch.H i.succ) :=
          cap.cylinderBetween_mono σ.isCylinder σ.isHoop_F₁ (ch.isHoop i.castSucc)
            (ch.isHoop i.succ) (ch.isHoop i.succ)
            (ch.disc₁_F₁_le i.castSucc) (ch.disc₁_mono i) Subset.rfl
        have hsubR : A j ⊆ cylinderBetween (ch.H i.succ) σ.F₂ :=
          cap.cylinderBetween_mono σ.isCylinder (ch.isHoop i.succ) (ch.isHoop j.castSucc)
            (ch.isHoop j.succ) σ.isHoop_F₂
            (ch.disc₁_le_of_le hle_ij) (ch.disc₁_mono j) (ch.disc₁_le_F₂ j.succ)
        have hed_H : (fr.iso.edgeEquiv ⟨e, hei.1⟩).1 ⊆ ch.H i.succ := fun x hxe =>
          cap.cylinderBetween_inter σ.isCylinder σ.isHoop_F₁ (ch.isHoop i.succ) σ.isHoop_F₂
            (ch.disc₁_F₁_le i.succ) (ch.disc₁_le_F₂ i.succ) ▸
            ⟨hsubL (hei.2 hxe), hsubR (hej.2 hxe)⟩
        exact not_edge_subset_of_isNormal (ch.isNormal i.succ)
          (fr.iso.edgeEquiv ⟨e, hei.1⟩).2 hed_H
      vertex_inter_subset := fun h i j hhi hij => by
        rcases eq_or_lt_of_le hhi with rfl | hlt1
        · exact inter_subset_left
        · rcases eq_or_lt_of_le hij with rfl | hlt2
          · exact inter_subset_right
          · rintro v ⟨⟨hv, hzh⟩, ⟨_, hzj⟩⟩
            have hle1 : h.succ ≤ i.succ := by
              change h.1 + 1 ≤ i.1 + 1; change h.1 < i.1 at hlt1; omega
            have hle2 : i.castSucc ≤ j.castSucc := by
              change i.1 ≤ j.1; change i.1 < j.1 at hlt2; omega
            dsimp only [A] at hzh hzj ⊢
            rw [cap.cylinderBetween_eq_of_disc₁_subset σ.isCylinder (ch.isHoop h.castSucc)
              (ch.isHoop h.succ) (ch.disc₁_mono h)] at hzh
            rw [cap.cylinderBetween_eq_of_disc₁_subset σ.isCylinder (ch.isHoop j.castSucc)
              (ch.isHoop j.succ) (ch.disc₁_mono j)] at hzj
            have hd2 : cap.disc₂ σ.isCylinder.1 (ch.isHoop j.castSucc) ⊆
                cap.disc₂ σ.isCylinder.1 (ch.isHoop i.castSucc) :=
              (cap.disc₂_subset_iff_disc₁_subset σ.isCylinder.1 (ch.isHoop i.castSucc)
                (ch.isHoop j.castSucc)).mpr (ch.disc₁_le_of_le hle2)
            refine ⟨hv, ?_⟩
            rw [cap.cylinderBetween_eq_of_disc₁_subset σ.isCylinder (ch.isHoop i.castSucc)
              (ch.isHoop i.succ) (ch.disc₁_mono i)]
            exact ⟨ch.disc₁_le_of_le hle1 hzh.1, hd2 hzj.2⟩
      adj_vertex_inter := fun i hi => by
        change fr.vertsIn (A i) ∩ fr.vertsIn (A ⟨i.1 + 1, hi⟩) = fr.vertsIn (ch.H i.succ)
        rw [← fr.vertsIn_inter]
        have hcs_eq : (⟨i.1 + 1, hi⟩ : Fin (n + 1)).castSucc = i.succ := Fin.ext rfl
        have hinter : A i ∩ A ⟨i.1 + 1, hi⟩ = ch.H i.succ := by
          dsimp only [A]
          rw [hcs_eq]
          exact cap.cylinderBetween_inter σ.isCylinder (ch.isHoop i.castSucc)
            (ch.isHoop i.succ) (ch.isHoop (⟨i.1 + 1, hi⟩ : Fin (n + 1)).succ)
            (ch.disc₁_mono i) (hcs_eq ▸ ch.disc₁_mono ⟨i.1 + 1, hi⟩)
        rw [hinter]
      T_eq := by
        change Y.T = fr.vertsIn (ch.H ⟨0, _⟩) ∪ fr.vertsIn (ch.H (Fin.last (n + 1)))
        rw [ch.first_eq, ch.last_eq, fr.vertsIn_F_union] }
    refine ⟨D, fun i => if h : i < n + 2 then ch.H ⟨i, h⟩ else σ.F₂, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simpa using ch.first_eq
    · change (if h : n + 1 < n + 2 then ch.H ⟨n + 1, h⟩ else σ.F₂) = σ.F₂
      rw [dif_pos (by omega)]
      exact ch.last_eq
    · intro i hi
      change i ≤ n + 1 at hi
      dsimp only
      rw [dif_pos (by omega)]
      exact ⟨ch.isHoop _, ch.isNormal _, ch.subset_cylinderBetween _⟩
    · intro i j hij hj
      change j ≤ n + 1 at hj
      dsimp only
      rw [dif_pos (by omega), dif_pos (by omega)]
      exact (cap.areLaminarHoops_iff σ.isCylinder (ch.isHoop _) (ch.isHoop _)).mpr
        (Or.inl (ch.disc₁_le_of_le (Fin.mk_le_mk.mpr hij.le)))
    · intro i hi
      change i ≤ n + 1 at hi
      dsimp only
      rw [dif_pos (by omega)]
      exact (D.Yn_eq ⟨i, show i < D.r + 1 by change i < n + 1 + 1; omega⟩).trans rfl
    · intro i h1 h2
      change i < n + 1 at h2
      dsimp only
      rw [dif_pos (by omega)]
      refine ⟨?_, hnct_interior i (by omega) h1 (by omega)⟩
      exact (congrArg Set.ncard (D.Yn_eq ⟨i, show i < D.r + 1 by change i < n + 1 + 1; omega⟩)).trans
        (hcard_interior i (by omega) h1 (by omega))

/-- Framing-level proof of `(15.1)`: every graft in `τ.subFramedClass r k` is an `r`-train over
`τ.subFramedClass (r + 1) (k + 2 * r)`. -/
theorem Tube.subFramedClass_subset_LKGraftClass (τ : Tube S) (r k : ℕ) :
    τ.subFramedClass (α := α) (β := β) r k ⊆
      LKGraftClass r (τ.subFramedClass (r + 1) (k + 2 * r)) := by
  suffices hmain : ∀ (σ : Tube S) (Y : Graft α β),
      Y.index ≤ k → σ.IsFraming Y → (r : ℕ∞) ≤ σ.width →
      Y ∈ LKGraftClass r (σ.subFramedClass (r + 1) (k + 2 * r)) by
    rintro Y ⟨hk, F₁', F₂', hlam, hsub₁, hsub₂, hN₁, hN₂, hfr, hw⟩
    exact LKGraftClass_mono r
      (τ.subTube_subFramedClass_subset hlam hsub₁ hsub₂ hN₁ hN₂ (r + 1) (k + 2 * r))
      (hmain (τ.subTube hlam hN₁ hN₂) Y hk hfr hw)
  intro σ Y hk ⟨fr⟩ hw
  obtain ⟨D, H, -, -, hH, hlam, hY, hint⟩ := σ.exists_chain_decomposition fr hk hw
  refine isKTrain_of_decomposition D (fun i h1 h2 => (hint i h1 h2).1) fun hr3 => ?_
  rw [hY 1 (by omega), hY (D.r - 1) (by omega)]
  obtain ⟨-, hN1, hs1⟩ := hH 1 (by omega)
  obtain ⟨-, hN2, hs2⟩ := hH (D.r - 1) (by omega)
  exact fr.hasDisjointGraphPaths_of_laminar_hoops hw (hlam 1 (D.r - 1) (by omega) (by omega))
    hs1 hs2 hN1 hN2 (hint 1 le_rfl (by omega)).2 (hint (D.r - 1) (by omega) (by omega)).2

/-- **Graph Minors VIII, (15.1)** (page 280):
"(15.1) *Every tubular graft of width $\ge r$ and index $\le k$ is an $r$-train of tubular grafts
of width $\ge r + 1$ and index $\le k + 2r$.*"
Here width means the side-qualified variant `Tube.width`, whose exceptional hoops satisfy
extra side conditions. The paper's proof fails for the printed width, where a hoop with vertex
set $F_1 \cap V(\Gamma)$ is exempt wherever it lies (see the correction to the proof of (15.1) in
`corrections/GM08.md`). With the
side-qualified width the paper's proof works, and it still gives (15.2) as printed. -/
theorem theorem_15_1_side_qualified {α : Type u} {β : Type v} (r k : ℕ) :
    tubularClass (α := α) (β := β) r k ⊆ LKGraftClass r (tubularClass (r + 1) (k + 2 * r)) := by
  rintro X ⟨htub, hw, hk⟩
  by_cases hw1 : ((r + 1 : ℕ) : ℕ∞) ≤ tubularWidth X
  · exact subset_LKGraftClass r _ ⟨htub, hw1, by omega⟩
  · have hlt : tubularWidth X < ((r + 1 : ℕ) : ℕ∞) := not_le.mp hw1
    have hne_top : tubularWidth X ≠ ⊤ :=
      ne_top_of_lt hlt
    have hw_eq : tubularWidth X = (r : ℕ∞) := by
      have hcast : (((tubularWidth X).toNat : ℕ) : ℕ∞) = tubularWidth X :=
        ENat.natCast_toNat hne_top
      have hle1 : r ≤ (tubularWidth X).toNat :=
        Nat.cast_le (α := ℕ∞).mp (hcast.symm ▸ hw)
      have hlt1 : (tubularWidth X).toNat < r + 1 :=
        Nat.cast_lt (α := ℕ∞).mp (hcast.symm ▸ hlt)
      have heq_nat : (tubularWidth X).toNat = r := by omega
      exact hcast.symm.trans (congrArg Nat.cast heq_nat)
    obtain ⟨S, ts, τ, hfr, hτw⟩ := htub.exists_framing_of_tubularWidth_eq hw_eq
    have hmem : X ∈ τ.subFramedClass r k :=
      τ.mem_subFramedClass_self hk hfr hτw.symm.le
    exact LKGraftClass_mono r (τ.subFramedClass_subset_tubularClass (r + 1) (k + 2 * r))
      (τ.subFramedClass_subset_LKGraftClass r k hmem)

end Theorem15_1

/-! ## 3. Proofs of (15.2) and (15.3), and Reduction of (15.4) -/

section Theorems15_2_15_3

variable {S : Type w} [TopologicalSpace S] {α : Type u} {β : Type v}

/-- Inductive step on `subFramedClass`: for all `t ≥ 0`,
`τ.subFramedClass 0 k ⊆ C^t(τ.subFramedClass (t + 1) (k + (t + 1) * t))`. -/
theorem Tube.subFramedClass_zero_subset_CKGraftClass (τ : Tube S) (t k : ℕ) :
    τ.subFramedClass (α := α) (β := β) 0 k ⊆
      CKGraftClass t (τ.subFramedClass (t + 1) (k + (t + 1) * t)) := by
  induction t with
  | zero =>
    simpa [CKGraftClass] using τ.subFramedClass_subset_LKGraftClass 0 k
  | succ m ih =>
    have hstep := τ.subFramedClass_subset_LKGraftClass (α := α) (β := β)
      (m + 1) (k + (m + 1) * m)
    have harith : k + (m + 1) * m + 2 * (m + 1) = k + (m + 2) * (m + 1) := by ring
    rw [harith] at hstep
    exact ih.trans (CKGraftClass_mono m hstep)

/-- Inductive step from the proof of `(15.2)` (page 281): for all `t ≥ 0`,
`𝒢(0, k) ⊆ C^t(𝒢(t + 1, k + (t + 1) * t))`. -/
theorem tubularClass_zero_subset_CKGraftClass (t k : ℕ) :
    tubularClass (α := α) (β := β) 0 k ⊆
      CKGraftClass t (tubularClass (t + 1) (k + (t + 1) * t)) := by
  induction t with
  | zero =>
    simpa [CKGraftClass] using theorem_15_1_side_qualified (α := α) (β := β) 0 k
  | succ m ih =>
    have hstep := theorem_15_1_side_qualified (α := α) (β := β) (m + 1) (k + (m + 1) * m)
    have harith : k + (m + 1) * m + 2 * (m + 1) = k + (m + 2) * (m + 1) := by ring
    rw [harith] at hstep
    exact ih.trans (CKGraftClass_mono m hstep)

/-- Graph Minors VIII, (15.2) (page 281), for the side-qualified width:
"(15.2) *Let $(G, T)$ be a tubular graft of index $\le k$ and let $r \ge 0$ be an integer. Then
$(G, T)$ is a concatenation of tubular grafts of width $\ge r$ and index $\le k + r(r - 1)$.*"
Here width means the side-qualified variant `Tube.width`, whose exceptional hoops satisfy
extra side conditions. The printed (15.2), `GM08.theorem_15_2_proof`, follows from this. -/
theorem theorem_15_2_sideQualified {X : Graft α β} {k : ℕ} (r : ℕ)
    (hX : IsTubularGraft X) (hk : X.index ≤ k) :
    X ∈ concatenationClass (tubularClass r (k + r * (r - 1))) := by
  have hmem0 : X ∈ tubularClass 0 k := ⟨hX, bot_le, hk⟩
  cases r with
  | zero =>
    refine ⟨0, ?_⟩
    simpa [CKGraftClass] using subset_LKGraftClass 0 (tubularClass 0 k) hmem0
  | succ t =>
    refine ⟨t, ?_⟩
    simpa using tubularClass_zero_subset_CKGraftClass t k hmem0

/-- Graph Minors VIII, (15.3) (page 281), for the side-qualified width:
"(15.3) *If $(G, T) \in \mathcal{A}(k, r, s)$, then $(G, T)$ is a concatenation of tubular grafts
of length $< s$ and index $\le k + r(r - 1)$.*"
Here width means the side-qualified variant `Tube.width`, whose exceptional hoops satisfy
extra side conditions. The printed (15.3) is `GM08.theorem_15_3_proof`. -/
theorem theorem_15_3_sideQualified (k r s : ℕ) :
    classA (α := α) (β := β) k r s ⊆
      concatenationClass
        {Y : Graft α β | IsTubularGraft Y ∧ tubularLength Y < s ∧ Y.index ≤ k + r * (r - 1)} := by
  rintro X ⟨hk, S₀, ts₀, τ, hfr, hno⟩
  let : TopologicalSpace S₀ := ts₀
  have hlen_bound : ∀ u : ℕ,
      τ.subFramedClass (α := α) (β := β) r u ⊆
        {Y : Graft α β | IsTubularGraft Y ∧ tubularLength Y < s ∧ Y.index ≤ u} := by
    rintro u Y ⟨hu, F₁', F₂', hlam, hsub₁, hsub₂, hN₁, hN₂, hfrY, hwY⟩
    have hlt_len : (τ.subTube hlam hN₁ hN₂).length < s := by
      by_contra hge
      exact hno ⟨F₁', F₂', hlam, hsub₁, hsub₂, hN₁, hN₂, hwY, not_lt.mp hge⟩
    exact ⟨IsTubularGraft.of_framing hfrY,
      (tubularLength_le_of_framing hfrY).trans_lt hlt_len, hu⟩
  have hX0 : X ∈ τ.subFramedClass 0 k := τ.mem_subFramedClass_self hk hfr bot_le
  cases r with
  | zero =>
    refine ⟨0, ?_⟩
    have hsub := LKGraftClass_mono 0 (hlen_bound (k + 0 * (0 - 1)))
    have hmem : X ∈ LKGraftClass 0 (τ.subFramedClass 0 (k + 0 * (0 - 1))) := by
      simpa using subset_LKGraftClass 0 (τ.subFramedClass 0 k) hX0
    exact hsub hmem
  | succ t =>
    refine ⟨t, ?_⟩
    have hmem : X ∈ CKGraftClass t (τ.subFramedClass (t + 1) (k + (t + 1) * t)) :=
      τ.subFramedClass_zero_subset_CKGraftClass t k hX0
    simpa using CKGraftClass_mono t (hlen_bound (k + (t + 1) * t)) hmem

/-- Reduction step of `(15.4)` (page 282): once the class $\mathcal{B}'$ of tubular grafts of
length `< s` and index `≤ k + r(r - 1)` is known to be well-rooted (which `(15.4)` deduces from
Section 12 via `(13.3)`), `classA k r s` is well-rooted by `(15.3)` and `(14.5)`. -/
theorem isWellRootedGraftClass_classA_of_tubularLength_lt [Infinite α] (k r s : ℕ)
    (hℬ' : IsWellRootedGraftClass
      {Y : Graft α β | IsTubularGraft Y ∧ tubularLength Y < s ∧ Y.index ≤ k + r * (r - 1)}) :
    IsWellRootedGraftClass (classA (α := α) (β := β) k r s) :=
  isWellRootedGraftClass_mono (theorem_15_3_sideQualified k r s) (theorem_14_5_proof _ hℬ')

end Theorems15_2_15_3

end GraphMinor.GM08
