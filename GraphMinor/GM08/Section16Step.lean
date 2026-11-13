module

public import GraphMinor.GM08.Section15
import GraphMinor.GM08.Section16Region
import GraphMinor.GM07.TameDisc
import GraphMinor.GM07.CuffFinger
import GraphMinor.GM07.Whisker
import GraphMinor.GM11.RadialAccess
import GraphMinor.GM11.Ties

/-!
# Graph Minors VIII, Section 16: Hoop-Step Lemma

Subtube compatibility helpers and the topological inward hoop-step (`Tube.exists_hoop_step_inward`)
used in Case 2 of Theorem `(16.2)` (page 283): given a tube `σ` of length `≥ s + 2`, there is a
`σ.Γ`-normal hoop `F₁'' ⊆ Σ(σ.F₁, σ.F₂)` containing at least one vertex of `σ.Γ.V \ σ.F₁` such that
the subtube between `F₁''` and `σ.F₂` has length `≥ s`.
-/

@[expose] public section

namespace GraphMinor.GM08

open Set Function Relation Topology Graph GraphMinor.Surface GraphMinor.GM11

universe u v w

/-! ## 1. Subtube Compatibility and Width Preservation -/

namespace Tube

variable {S : Type w} [TopologicalSpace S]

theorem subTube_inter_V_eq (τ : Tube S) {H₁ H₂ H : Set S} (hlam : AreLaminarHoops H₁ H₂)
    (hN₁ : τ.Γ.IsNormal H₁) (hN₂ : τ.Γ.IsNormal H₂) (hH : H ⊆ cylinderBetween H₁ H₂) :
    H ∩ (τ.subTube hlam hN₁ hN₂).Γ.V = H ∩ τ.Γ.V := by
  have : T2Space S := τ.t2Space
  have hVEq : (τ.subTube hlam hN₁ hN₂).Γ.V = τ.Γ.V ∩ cylinderBetween H₁ H₂ :=
    interSet_V_of_isClosed τ.Γ (isClosed_cylinderBetween hlam)
  rw [hVEq]
  ext x
  exact ⟨fun ⟨hxH, hxV, _⟩ => ⟨hxH, hxV⟩, fun ⟨hxH, hxV⟩ => ⟨hxH, hxV, hH hxH⟩⟩

theorem ext {τ₁ τ₂ : Tube S} (hΓ : τ₁.Γ = τ₂.Γ) (h₁ : τ₁.F₁ = τ₂.F₁) (h₂ : τ₁.F₂ = τ₂.F₂) :
    τ₁ = τ₂ := by
  cases τ₁; cases τ₂; cases hΓ; cases h₁; cases h₂; rfl

end Tube

/-! ## 2. Topological Helpers and the Inward Hoop-Step -/

section HoopStepHelpers

/-- Pulling a closed disc `B ⊆ cap.Z` with `E₁ ⊆ B` and `Disjoint B (discInt G₂)` back along
`cap.j` yields a hoop `H = cap.j ⁻¹' discBd B` in `S` with `cap.disc₁ _ hH = B` and
`H ⊆ Σ(σ.F₁, σ.F₂)`. -/
private theorem pull_hoop_of_disc_in_cap {S : Type w} [TopologicalSpace S] (σ : Tube S)
    (cap : CylinderSphereCap S)
    (hle : cap.disc₁ σ.isCylinder.1 σ.isHoop_F₁ ⊆ cap.disc₁ σ.isCylinder.1 σ.isHoop_F₂)
    {B : Set cap.Z} (hB : IsClosedDisc B)
    (hsubB : cap.disc₁ σ.isCylinder.1 σ.isHoop_F₁ ⊆ B)
    (hdisB : Disjoint B (discInt (cap.disc₂ σ.isCylinder.1 σ.isHoop_F₂))) :
    IsHoop (cap.j ⁻¹' discBd B) ∧
      cap.j '' (cap.j ⁻¹' discBd B) = discBd B ∧
      (∀ hH : IsHoop (cap.j ⁻¹' discBd B), cap.disc₁ σ.isCylinder.1 hH = B) ∧
      cap.j ⁻¹' discBd B ⊆ cylinderBetween σ.F₁ σ.F₂ ∧
      AreLaminarHoops (cap.j ⁻¹' discBd B) σ.F₂ := by
  have : T2Space S := σ.t2Space
  have : T2Space cap.Z := cap.t2Space_Z
  set E₁ := cap.disc₁ σ.isCylinder.1 σ.isHoop_F₁
  set G₁ := cap.disc₁ σ.isCylinder.1 σ.isHoop_F₂
  set G₂ := cap.disc₂ σ.isCylinder.1 σ.isHoop_F₂
  obtain ⟨_, _, _, _, _, _, hD₁E, _⟩ := cap.disc₁_disc₂_spec σ.isCylinder.1 σ.isHoop_F₁
  obtain ⟨_, _, hbG₁, hbG₂, hcupG, _, _, hD₂G⟩ := cap.disc₁_disc₂_spec σ.isCylinder.1 σ.isHoop_F₂
  have hD₁B : cap.D₁ ⊆ B := hD₁E.trans hsubB
  have hdis_bd_D₁ : Disjoint (discBd B) (discInt cap.D₁) :=
    disjoint_left.mpr fun z hzBd hzInt =>
      (discInt_mono cap.isManifoldPoint_Z cap.isClosedDisc_D₁ hD₁B hzInt).2 hzBd
  have hdis_D₂_B : Disjoint (discInt cap.D₂) B :=
    hdisB.symm.mono_left (discInt_mono cap.isManifoldPoint_Z cap.isClosedDisc_D₂ hD₂G)
  have hsubr : discBd B ⊆ range cap.j :=
    cap.subset_range_of_disjoint_discInts hdis_bd_D₁
      (hdis_D₂_B.symm.mono_left (Surface.discBd_subset B))
  let H : Set S := cap.j ⁻¹' discBd B
  have hjH : cap.j '' H = discBd B := image_preimage_eq_of_subset hsubr
  have hHO : IsOArc H := GM07.pull_oArc cap.isClosedEmbedding.isEmbedding hB.isOArc_discBd hsubr
  obtain ⟨Δ₁, Δ₂, _, hΔ₁, hΔ₂, hbΔ₁, hbΔ₂, hcupΔ, hcapΔ, -, huniqΔ⟩ :=
    sphere_disc cap.Z cap.isSphere (discBd B) hB.isOArc_discBd
  have hB'_ex : ∃ B' : Set cap.Z, IsClosedDisc B' ∧ discBd B' = cap.j '' H ∧
      B ∪ B' = univ ∧ B ∩ B' = cap.j '' H := by
    rcases huniqΔ B hB rfl with hB1 | hB2
    · subst hB1
      exact ⟨Δ₂, hΔ₂, hbΔ₂.trans hjH.symm, hcupΔ, hcapΔ.trans hjH.symm⟩
    · subst hB2
      exact ⟨Δ₁, hΔ₁, hbΔ₁.trans hjH.symm, by rw [union_comm, hcupΔ],
        by rw [inter_comm, hcapΔ, hjH]⟩
  obtain ⟨B', hB'_disc, hbB', hcupBB', hcapBB'⟩ := hB'_ex
  have hD₂B' : cap.D₂ ⊆ B' := by
    have hint_sub : discInt cap.D₂ ⊆ B' := fun z hz =>
      (hcupBB' ▸ mem_univ z).resolve_left (disjoint_left.mp hdis_D₂_B hz)
    exact cap.isClosedDisc_D₂.subset_closure_discInt.trans
      (closure_minimal hint_sub hB'_disc.isCompact.isClosed)
  have hH : IsHoop H := (cap.isHoop_iff_exists_discs σ.isCylinder.1 hHO).mpr
    ⟨B, B', hB, hB'_disc, hjH.symm, hbB', hcupBB', hcapBB', hD₁B, hD₂B'⟩
  have hB_eq : ∀ hH' : IsHoop H, cap.disc₁ σ.isCylinder.1 hH' = B := fun hH' => by
    obtain ⟨hd1, hd2, hbd1, hbd2, _, hcap12, hD1', hD2'⟩ :=
      cap.disc₁_disc₂_spec σ.isCylinder.1 hH'
    exact (cap.hoop_discs_unique hd1 hd2 hbd1 hbd2 hcap12 hD1' hD2'
      hB hB'_disc hjH.symm hbB' hD₁B hD₂B').1.symm
  have hBG₁ : B ⊆ G₁ := fun z hzB => by
    rcases (hcupG ▸ mem_univ z : z ∈ G₁ ∪ G₂) with hz1 | hz2
    · exact hz1
    · by_cases hzBd : z ∈ discBd G₂
      · exact Surface.discBd_subset _ (hbG₁ ▸ hbG₂ ▸ hzBd)
      · exact absurd ⟨hz2, hzBd⟩ (disjoint_left.mp hdisB hzB)
  have hle_E1_H : E₁ ⊆ cap.disc₁ σ.isCylinder.1 hH := (hB_eq hH).symm ▸ hsubB
  have hle_H_G1 : cap.disc₁ σ.isCylinder.1 hH ⊆ G₁ := (hB_eq hH).symm ▸ hBG₁
  have hH_sub : H ⊆ cylinderBetween σ.F₁ σ.F₂ :=
    (cap.hoop_subset_cylinderBetween_iff σ.isCylinder σ.isHoop_F₁ σ.isHoop_F₂ hH hle).mpr
      ⟨hle_E1_H, hle_H_G1⟩
  have hlam : AreLaminarHoops H σ.F₂ :=
    (cap.areLaminarHoops_iff σ.isCylinder hH σ.isHoop_F₂).mpr (Or.inl hle_H_G1)
  exact ⟨hH, hjH, hB_eq, hH_sub, hlam⟩

/-- Length bound for a hoop `H ⊆ Σ(σ.F₁, σ.F₂)` disjoint from `σ.F₂` that shares at least one
point with `σ.F₁` and whose extra vertices `H ∩ σ.Γ.V \ σ.F₁` lie in a finite set `A₀`. -/
private theorem length_subTube_add_ge_length {S : Type w} [TopologicalSpace S] (σ : Tube S)
    {H : Set S} (hlam : AreLaminarHoops H σ.F₂) (hNH : σ.Γ.IsNormal H)
    (_hH_sub : H ⊆ cylinderBetween σ.F₁ σ.F₂)
    (hdis : Disjoint H σ.F₂) (hne : (H ∩ σ.F₁).Nonempty)
    {A₀ : Set S} (hA₀ : A₀.Finite) (hHV : H ∩ σ.Γ.V ⊆ σ.F₁ ∪ A₀) :
    σ.length ≤ (σ.subTube hlam hNH σ.isNormal_F₂).length + (A₀.ncard + 1) := by
  have : T2Space S := σ.t2Space
  let σ' := σ.subTube hlam hNH σ.isNormal_F₂
  obtain ⟨x₀, hx₀H, hx₀F₁⟩ := hne
  suffices hgoal : σ.length - (A₀.ncard + 1) ≤ σ'.length from Nat.le_add_of_sub_le hgoal
  rw [σ'.le_length_iff_sub_cylinderBetween]
  intro I u v hline hu hv hNI' hI_cyl
  have hcl' : IsClosed (cylinderBetween H σ.F₂) := isClosed_cylinderBetween hlam
  have hNI : σ.Γ.IsNormal I := by
    have hUEq := interSet_U_eq_of_laminar_normal σ.Γ hlam hNH σ.isNormal_F₂
    have hVEq := interSet_V_of_isClosed σ.Γ hcl'
    rintro x ⟨hxI, hxU⟩
    exact (hVEq.subset (hNI' ⟨hxI, hUEq.symm.subset ⟨hxU, hI_cyl hxI⟩⟩)).1
  have hIV_eq : I ∩ σ'.Γ.V = I ∩ σ.Γ.V :=
    σ.subTube_inter_V_eq hlam hNH σ.isNormal_F₂ hI_cyl
  rw [hIV_eq]
  -- Trim `I` at its last point on `H` so `I' ∩ H = {u'}`.
  obtain ⟨f₀, hf0, hf1⟩ := hline
  let f : unitInterval → S := fun t => (f₀ t).1
  have hf_cont : Continuous f := continuous_subtype_val.comp f₀.continuous
  have hf_inj : Injective f := Subtype.val_injective.comp f₀.injective
  have hcH : IsCompact (f ⁻¹' H) := (hlam.2.1.isClosed.preimage hf_cont).isCompact
  have h0_mem : (0 : unitInterval) ∈ f ⁻¹' H := by change (f₀ 0).1 ∈ H; rw [hf0]; exact hu
  obtain ⟨t₁, ht₁H, hhigh₁⟩ := hcH.exists_isGreatest ⟨0, h0_mem⟩
  have ht₁_lt_1 : t₁ < 1 := lt_of_le_of_ne t₁.2.2 fun h1 =>
    disjoint_left.mp hdis ht₁H (by change (f₀ t₁).1 ∈ σ.F₂; rw [h1, hf1]; exact hv)
  let u' := f t₁
  let I' := f '' Icc t₁ 1
  have hI'_sub_I : I' ⊆ I := by rintro _ ⟨t, _, rfl⟩; exact (f₀ t).2
  have hf1_eq : f 1 = v := hf1
  have hline' : IsLineWithEnds I' u' v := hf1_eq ▸ subArc_of_lt hf_cont hf_inj ht₁_lt_1
  have hI'_inter_H : I' ∩ H = {u'} := by
    apply Subset.antisymm
    · rintro _ ⟨⟨t, ⟨ht1, _⟩, rfl⟩, htH⟩
      exact congrArg f (le_antisymm (hhigh₁ htH) ht1)
    · rintro _ rfl
      exact ⟨⟨t₁, ⟨le_rfl, t₁.2.2⟩, rfl⟩, ht₁H⟩
  have hNI_sub : σ.Γ.IsNormal I' := fun x ⟨hx, hxU⟩ => hNI ⟨hI'_sub_I hx, hxU⟩
  have hIV_mono : (I' ∩ σ.Γ.V).ncard ≤ (I ∩ σ.Γ.V).ncard :=
    ncard_le_ncard (inter_subset_inter_left _ hI'_sub_I) (σ.Γ.finite_V.subset inter_subset_right)
  by_cases hu'F₁ : u' ∈ σ.F₁
  · have hlen := (σ.le_length_iff.mp le_rfl) I' u' v hline' hu'F₁ hv hNI_sub
    omega
  · -- Walk along `H` from `x₀ ∈ H ∩ σ.F₁` to `u' ∉ σ.F₁`, stopping at the last hit of `H ∩ σ.F₁`.
    obtain ⟨ψ⟩ := hlam.2.1.1
    have hH_pc : IsPathConnected H := by
      have heq : H = range (fun c : Circle => (ψ c).1) := by
        ext x; exact ⟨fun hx => ⟨ψ.symm ⟨x, hx⟩, by simp⟩, fun ⟨c, hc⟩ => hc ▸ (ψ c).2⟩
      rw [heq]
      have : PathConnectedSpace Circle := inferInstance
      exact isPathConnected_range (continuous_subtype_val.comp ψ.continuous)
    have hHF₁_cl : IsClosed (H ∩ σ.F₁) := hlam.2.1.isClosed.inter σ.isHoop_F₁.isClosed
    obtain ⟨x₁, hx₁, J, hJH, hlineJ, hJ_inter⟩ := GM07.exists_whisker_line hHF₁_cl ⟨hx₀H, hx₀F₁⟩
      (fun h => hu'F₁ h.2) (hH_pc.joinedIn x₀ hx₀H u' ht₁H)
    have hJI' : J ∩ I' = {u'} := by
      apply Subset.antisymm
      · intro x ⟨hxJ, hxI'⟩
        exact hI'_inter_H.subset ⟨hxI', hJH hxJ⟩
      · rintro _ rfl
        exact ⟨hlineJ.right_mem, hline'.left_mem⟩
    have hline_union : IsLineWithEnds (J ∪ I') x₁ v := hlineJ.union hline' hJI'
    have hN_union : σ.Γ.IsNormal (J ∪ I') := by
      rintro x ⟨hxJ | hxI', hxU⟩
      · exact hNH ⟨hJH hxJ, hxU⟩
      · exact hNI_sub ⟨hxI', hxU⟩
    have hJV_sub : J ∩ σ.Γ.V ⊆ {x₁} ∪ A₀ := by
      rintro x ⟨hxJ, hxV⟩
      rcases hHV ⟨hJH hxJ, hxV⟩ with hxF₁ | hxA₀
      · exact Or.inl (hJ_inter ⟨hxJ, hJH hxJ, hxF₁⟩)
      · exact Or.inr hxA₀
    have hunion_sub : (J ∪ I') ∩ σ.Γ.V ⊆ ({x₁} ∪ A₀) ∪ (I' ∩ σ.Γ.V) := by
      rintro x ⟨hxJ | hxI', hxV⟩
      · exact Or.inl (hJV_sub ⟨hxJ, hxV⟩)
      · exact Or.inr ⟨hxI', hxV⟩
    have hcard_xA : ({x₁} ∪ A₀).ncard ≤ A₀.ncard + 1 :=
      (ncard_union_le {x₁} A₀).trans (by simp [Nat.add_comm])
    have hcard_union : ((J ∪ I') ∩ σ.Γ.V).ncard ≤ (I' ∩ σ.Γ.V).ncard + (A₀.ncard + 1) := by
      calc ((J ∪ I') ∩ σ.Γ.V).ncard
          ≤ (({x₁} ∪ A₀) ∪ (I' ∩ σ.Γ.V)).ncard :=
            ncard_le_ncard hunion_sub
              (((finite_singleton x₁).union hA₀).union (σ.Γ.finite_V.subset inter_subset_right))
        _ ≤ ({x₁} ∪ A₀).ncard + (I' ∩ σ.Γ.V).ncard := ncard_union_le _ _
        _ ≤ (I' ∩ σ.Γ.V).ncard + (A₀.ncard + 1) := by omega
    have hlen := (σ.le_length_iff.mp le_rfl) (J ∪ I') x₁ v hline_union hx₁.2 hv hN_union
    omega

end HoopStepHelpers

/-- **Inward hoop-step in a tube of length `≥ s + 2` (GM VIII, Section 16, page 283, Case 2).**
For any tube `σ : Tube S` and `s : ℕ` with `s + 2 ≤ σ.length`, there exists a `σ.Γ`-normal hoop
`F₁'' ⊆ Σ(σ.F₁, σ.F₂)` laminar with `σ.F₂` such that `F₁''` contains at least one vertex of
`σ.Γ.V \ σ.F₁` and `(σ.subTube hlam hN σ.isNormal_F₂)` has length `≥ s`. -/
theorem Tube.exists_hoop_step_inward_refined {S : Type w} [TopologicalSpace S] (σ : Tube S) {s : ℕ}
    (hs : s + 2 ≤ σ.length) :
    ∃ (F₁'' : Set S) (hlam : AreLaminarHoops F₁'' σ.F₂) (hN : σ.Γ.IsNormal F₁''),
      F₁'' ⊆ cylinderBetween σ.F₁ σ.F₂ ∧
      (∃ v ∈ σ.Γ.V, v ∈ F₁'' ∧ v ∉ σ.F₁ ∧
        F₁'' ∩ σ.Γ.V ⊆ σ.F₁ ∪ {v}) ∧
      s ≤ (σ.subTube hlam hN σ.isNormal_F₂).length := by
  classical
  have : T2Space S := σ.t2Space
  have : CompactSpace S := σ.isCylinder.1.1
  have : Nonempty S := σ.isCylinder.nonempty
  obtain ⟨cap, hle⟩ :=
    CylinderSphereCap.exists_oriented σ.isCylinder σ.isHoop_F₁ σ.isHoop_F₂ σ.laminar
  have : T2Space cap.Z := cap.t2Space_Z
  have hZ_cs : IsClosedSurface cap.Z := cap.isClosedSurface
  have hman : ∀ z : cap.Z, IsManifoldPoint z := cap.isManifoldPoint_Z
  set E₁ := cap.disc₁ σ.isCylinder.1 σ.isHoop_F₁
  set E₂ := cap.disc₂ σ.isCylinder.1 σ.isHoop_F₁
  set G₁ := cap.disc₁ σ.isCylinder.1 σ.isHoop_F₂
  set G₂ := cap.disc₂ σ.isCylinder.1 σ.isHoop_F₂
  obtain ⟨hE₁, hE₂, hbE₁, _, hcupE, hcapE, _, _⟩ := cap.disc₁_disc₂_spec σ.isCylinder.1 σ.isHoop_F₁
  obtain ⟨hG₁, hG₂, hbG₁, hbG₂, hcupG, hcapG, _, _⟩ :=
    cap.disc₁_disc₂_spec σ.isCylinder.1 σ.isHoop_F₂
  have hdisF : Disjoint σ.F₁ σ.F₂ := σ.disjoint_of_two_le_length (by omega)
  have hdisEG : Disjoint E₁ G₂ := by
    rw [disjoint_iff_inter_eq_empty,
      cap.disc₁_inter_disc₂_eq_image_inter σ.isCylinder.1 σ.isHoop_F₁ σ.isHoop_F₂ hle,
      disjoint_iff_inter_eq_empty.mp hdisF, image_empty]
  obtain ⟨ΓZ, hm⟩ := GM07.exists_image_matched cap.isClosedEmbedding σ.Γ
  have hUZ : ΓZ.U = cap.j '' σ.Γ.U := by simpa using hm.image_U.symm
  have hVZ : ΓZ.V = cap.j '' σ.Γ.V := by simpa using hm.image_V.symm
  have hUsubZ : ΓZ.U ⊆ G₁ ∩ E₂ := by
    rw [hUZ]
    rintro _ ⟨x, hxU, rfl⟩
    have hx := σ.U_subset hxU
    rwa [cap.cylinderBetween_eq_of_disc₁_subset σ.isCylinder σ.isHoop_F₁ σ.isHoop_F₂ hle] at hx
  have hdisU_intG₂ : Disjoint ΓZ.U (discInt G₂) :=
    disjoint_left.mpr fun z hzU hzInt => hzInt.2 (hbG₂ ▸ hcapG ▸ ⟨(hUsubZ hzU).1, hzInt.1⟩)
  have hUG₂_sub_V : ΓZ.U ∩ G₂ ⊆ ΓZ.V := by
    rintro z ⟨hzU, hzG₂⟩
    have hzF₂ : z ∈ cap.j '' σ.F₂ := hcapG ▸ ⟨(hUsubZ hzU).1, hzG₂⟩
    obtain ⟨x, hxU, rfl⟩ := hUZ ▸ hzU
    obtain ⟨y, hyF₂, heq⟩ := hzF₂
    exact hVZ ▸ ⟨x, σ.isNormal_F₂ ⟨cap.inj heq ▸ hyF₂, hxU⟩, rfl⟩
  -- Step 1: Choose `B₁` maximizing `{e ∈ ΓZ.E | e ⊆ B}.ncard` among `GoodDisc`s.
  let GoodDisc : Set cap.Z → Prop := fun B =>
    IsClosedDisc B ∧ E₁ ⊆ B ∧ Disjoint B G₂ ∧
      discBd B ∩ ΓZ.U ⊆ ΓZ.V ∩ discBd E₁ ∧ (discBd B ∩ discBd E₁).Nonempty
  have hGood_E₁ : GoodDisc E₁ := by
    refine ⟨hE₁, Subset.rfl, hdisEG, ?_, ?_⟩
    · rintro z ⟨hzBd, hzU⟩
      obtain ⟨x, hxU, rfl⟩ := hUZ ▸ hzU
      obtain ⟨y, hyF₁, heq⟩ := hbE₁ ▸ hzBd
      exact ⟨hVZ ▸ ⟨x, σ.isNormal_F₁ ⟨cap.inj heq ▸ hyF₁, hxU⟩, rfl⟩, hzBd⟩
    · obtain ⟨z, hz⟩ := (GM07.isConnected_of_isOArc hE₁.isOArc_discBd).nonempty
      exact ⟨z, hz, hz⟩
  let S_num : Set ℕ := {n | ∃ B, GoodDisc B ∧ {e ∈ ΓZ.E | e ⊆ B}.ncard = n}
  have hS_ne : S_num.Nonempty := ⟨_, E₁, hGood_E₁, rfl⟩
  have hS_bdd : BddAbove S_num := ⟨ΓZ.E.ncard, by
    rintro _ ⟨B, _, rfl⟩
    exact ncard_le_ncard (fun _ h => h.1) ΓZ.finite_edges⟩
  obtain ⟨B₁, ⟨hB₁, hE₁B₁, hdisB₁G₂, hbdB₁U, hbdB₁_ne⟩, hB₁_max_eq⟩ :=
    Nat.sSup_mem hS_ne hS_bdd
  have hB₁_max : ∀ D, GoodDisc D → {e ∈ ΓZ.E | e ⊆ D}.ncard ≤ {e ∈ ΓZ.E | e ⊆ B₁}.ncard :=
    fun D hD => hB₁_max_eq ▸ le_csSup hS_bdd ⟨D, hD, rfl⟩
  -- Pull `B₁` back to `H₁ ⊆ Σ(σ.F₁, σ.F₂)` and show length(H₁, σ.F₂) ≥ s + 1.
  obtain ⟨hH₁, hjH₁, _, hH₁_sub, hlamH₁⟩ :=
    pull_hoop_of_disc_in_cap σ cap hle hB₁ hE₁B₁ (hdisB₁G₂.mono_right (discInt_subset G₂))
  let H₁ : Set S := cap.j ⁻¹' discBd B₁
  have hNH₁ : σ.Γ.IsNormal H₁ := by
    rintro x ⟨hxH₁, hxU⟩
    have hzj : cap.j x ∈ ΓZ.V ∩ discBd E₁ := hbdB₁U ⟨hxH₁, hUZ ▸ mem_image_of_mem _ hxU⟩
    obtain ⟨y, hyV, heq⟩ := hVZ ▸ hzj.1
    exact cap.inj heq ▸ hyV
  have hdisH₁F₂ : Disjoint H₁ σ.F₂ := disjoint_left.mpr fun x hxH₁ hxF₂ =>
    disjoint_left.mp hdisB₁G₂ (Surface.discBd_subset B₁ hxH₁)
      (Surface.discBd_subset G₂ (hbG₂ ▸ mem_image_of_mem _ hxF₂))
  obtain ⟨y₀, hy₀Bd₁, hy₀BdE₁⟩ := hbdB₁_ne
  obtain ⟨x₀_S, hx₀F₁, hy₀_eq⟩ := hbE₁ ▸ hy₀BdE₁
  have hx₀H₁ : x₀_S ∈ H₁ := by change cap.j x₀_S ∈ discBd B₁; rw [hy₀_eq]; exact hy₀Bd₁
  have hH₁_HV : H₁ ∩ σ.Γ.V ⊆ σ.F₁ ∪ ∅ := by
    rintro x ⟨hxH₁, hxV⟩
    have hzj := hbdB₁U ⟨hxH₁, hUZ ▸ mem_image_of_mem _ (σ.Γ.V_subset_U hxV)⟩
    obtain ⟨y, hyF₁, heq⟩ := hbE₁ ▸ hzj.2
    exact Or.inl (cap.inj heq ▸ hyF₁)
  have hlen_H₁ : s + 1 ≤ (σ.subTube hlamH₁ hNH₁ σ.isNormal_F₂).length := by
    have h := length_subTube_add_ge_length σ hlamH₁ hNH₁ hH₁_sub hdisH₁F₂ ⟨x₀_S, hx₀H₁, hx₀F₁⟩
      finite_empty hH₁_HV
    simp only [ncard_empty, zero_add] at h
    omega
  -- Step 2: Pick an exterior basepoint `q₀` attached to `p₁ ∈ discBd B₁ \ (G₂ ∪ ΓZ.U ∪ {y₀})`.
  have hfin_bad : (discBd B₁ ∩ (ΓZ.U ∪ {y₀})).Finite := by
    have hsub_bad : discBd B₁ ∩ (ΓZ.U ∪ {y₀}) ⊆ (ΓZ.V ∩ discBd E₁) ∪ {y₀} := by
      rintro z ⟨hzBd, hzU | rfl⟩
      · exact Or.inl (hbdB₁U ⟨hzBd, hzU⟩)
      · exact Or.inr rfl
    exact ((ΓZ.finite_V.subset inter_subset_left).union (finite_singleton y₀)).subset hsub_bad
  have hne_p₀ : (discBd B₁ \ (ΓZ.U ∪ {y₀})).Nonempty := by
    have heq_diff : discBd B₁ \ (ΓZ.U ∪ {y₀}) = discBd B₁ \ (discBd B₁ ∩ (ΓZ.U ∪ {y₀})) := by
      ext z; simp
    rw [heq_diff]
    exact ((infinite_of_isOArc hB₁.isOArc_discBd).sdiff hfin_bad).nonempty
  obtain ⟨p₀, hp₀Bd, hp₀_off⟩ := hne_p₀
  have hp₀_notG₂ : p₀ ∉ G₂ := disjoint_left.mp hdisB₁G₂ (Surface.discBd_subset B₁ hp₀Bd)
  let W₀ : Set cap.Z := (G₂ ∪ ΓZ.U ∪ {y₀})ᶜ
  have hW₀_open : IsOpen W₀ :=
    (hG₂.isClosed.union ΓZ.isClosed_U |>.union isClosed_singleton).isOpen_compl
  have hp₀W₀ : p₀ ∈ W₀ := by
    rintro ((hG | hU) | hy)
    · exact hp₀_notG₂ hG
    · exact hp₀_off (Or.inl hU)
    · exact hp₀_off (Or.inr hy)
  obtain ⟨V₀, hV₀_open, hp₀V₀, _⟩ := hZ_cs.2.2 p₀
  let W₁ : Set cap.Z := connectedComponentIn (V₀ ∩ W₀) p₀
  have : LocallyConnectedSpace cap.Z := GM11.IsClosedSurface.locallyConnectedSpace hZ_cs
  have hW₁_open : IsOpen W₁ := (hV₀_open.inter hW₀_open).connectedComponentIn
  have hp₀W₁ : p₀ ∈ W₁ := mem_connectedComponentIn ⟨hp₀V₀, hp₀W₀⟩
  have hW₁_pc : IsPathConnected W₁ :=
    GM11.isPathConnected_of_isOpen hZ_cs hW₁_open isPreconnected_connectedComponentIn ⟨p₀, hp₀W₁⟩
  have hB₁_sub_intG₁ : B₁ ⊆ G₁ \ discBd G₁ := fun z hz =>
    ⟨(hcupG ▸ mem_univ z).resolve_right (disjoint_left.mp hdisB₁G₂ hz),
      fun hb => disjoint_left.mp hdisB₁G₂ hz (Surface.discBd_subset G₂ (hbG₂ ▸ hbG₁ ▸ hb))⟩
  obtain ⟨N₀, _, _, hN₀W₁, _, ⟨q₀, hq₀N, hq₀_notB₁⟩⟩ :=
    GM07.exists_side_nbhd hman hB₁ hG₁ hB₁_sub_intG₁ hp₀Bd hW₁_open hp₀W₁
  have hq₀W₁ : q₀ ∈ W₁ := hN₀W₁ hq₀N
  obtain ⟨p₁, hp₁B₁, L_rad, hL_radW₁, hL_rad_line, hL_radB₁⟩ :=
    GM07.exists_whisker_line hB₁.isClosed (Surface.discBd_subset B₁ hp₀Bd) hq₀_notB₁
      (hW₁_pc.joinedIn p₀ hp₀W₁ q₀ hq₀W₁)
  have hL_radW₀ : L_rad ⊆ W₀ := hL_radW₁.trans ((connectedComponentIn_subset _ _).trans inter_subset_right)
  have hp₁W₀ : p₁ ∈ W₀ := hL_radW₀ hL_rad_line.left_mem
  have hp₁Bd : p₁ ∈ discBd B₁ := by
    rw [← IsClosedDisc.frontier_eq_discBd hZ_cs hB₁, frontier_eq_closure_inter_closure,
      hB₁.isClosed.closure_eq]
    refine ⟨hp₁B₁, ?_⟩
    obtain ⟨f_r, hf_r0, hf_r1⟩ := hL_rad_line
    have h0_cl : (0 : unitInterval) ∈ closure (Ioi (0 : unitInterval)) := by
      rw [mem_closure_iff]
      intro V hV h0V
      obtain ⟨W, hW, rfl⟩ := isOpen_induced_iff.mp hV
      obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hW 0 h0V
      let r : ℝ := min 1 (ε / 2)
      have hr : r ∈ Icc (0 : ℝ) 1 := ⟨le_min zero_le_one (by positivity), min_le_left _ _⟩
      have hr_pos : (0 : unitInterval) < ⟨r, hr⟩ := lt_min zero_lt_one (half_pos hε)
      refine ⟨⟨r, hr⟩, hball ?_, hr_pos⟩
      rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_nonneg hr.1]
      exact lt_of_le_of_lt (min_le_right _ _) (half_lt_self hε)
    have hcont_r : Continuous (fun t : unitInterval => (f_r t).1) :=
      continuous_subtype_val.comp f_r.continuous
    have hp₁_cl := image_closure_subset_closure_image hcont_r ⟨0, h0_cl, hf_r0⟩
    refine closure_mono ?_ hp₁_cl
    rintro _ ⟨t, ht_pos, rfl⟩ hxB₁
    have htp : (f_r t).1 = p₁ := hL_radB₁ ⟨(f_r t).2, hxB₁⟩
    have ht0 : t = 0 := f_r.injective (Subtype.ext (htp.trans hf_r0.symm))
    exact ht_pos.ne' (congrArg Subtype.val ht0)
  -- Define the exterior region `R = connectedComponentIn Ω q₀` and show `Disjoint R G₂`.
  let Ω : Set cap.Z := (B₁ ∪ ΓZ.U)ᶜ
  have hΩ_open : IsOpen Ω := (hB₁.isClosed.union ΓZ.isClosed_U).isOpen_compl
  have hq₀Ω : q₀ ∈ Ω := by
    rintro (hB | hU)
    · exact hq₀_notB₁ hB
    · exact hL_radW₀ hL_rad_line.right_mem (Or.inl (Or.inr hU))
  let R : Set cap.Z := connectedComponentIn Ω q₀
  have hR_open : IsOpen R := hΩ_open.connectedComponentIn
  have hq₀R : q₀ ∈ R := mem_connectedComponentIn hq₀Ω
  have hR_pc : IsPathConnected R :=
    GM11.isPathConnected_of_isOpen hZ_cs hR_open isPreconnected_connectedComponentIn ⟨q₀, hq₀R⟩
  have hR_sub_Ω : R ⊆ Ω := connectedComponentIn_subset Ω q₀
  have hL_rad_diff_R : L_rad \ {p₁} ⊆ R := by
    obtain ⟨f_r, hf_r0, hf_r1⟩ := id hL_rad_line
    have heq : L_rad \ {p₁} = (fun t : unitInterval => (f_r t).1) '' Ioi 0 := by
      ext z
      constructor
      · rintro ⟨hz, hzp⟩
        let t := f_r.symm ⟨z, hz⟩
        have ht0 : t ≠ 0 := fun h => hzp (by change z = p₁; rw [← hf_r0]; simp [t, ← h])
        exact ⟨t, lt_of_le_of_ne t.2.1 (Subtype.coe_ne_coe.mpr ht0).symm, by simp [t]⟩
      · rintro ⟨t, ht, rfl⟩
        refine ⟨(f_r t).2, fun h => ht.ne' ?_⟩
        exact congrArg Subtype.val (f_r.injective (Subtype.ext (h.trans hf_r0.symm)))
    have hpc : IsPreconnected (L_rad \ {p₁}) := by
      rw [heq]
      have hIoi_pc : IsPreconnected (Ioi (0 : unitInterval)) := by
        have hmap : Ioi (0 : unitInterval) = projIcc 0 1 zero_le_one '' Ioc (0 : ℝ) 1 := by
          ext t
          constructor
          · intro ht
            exact ⟨t.1, ⟨ht, t.2.2⟩, projIcc_of_mem zero_le_one t.2⟩
          · rintro ⟨x, ⟨hx0, hx1⟩, rfl⟩
            change (0 : ℝ) < projIcc 0 1 zero_le_one x
            rwa [projIcc_of_mem zero_le_one ⟨hx0.le, hx1⟩]
        rw [hmap]
        exact (convex_Ioc 0 1).isPreconnected.image _ continuous_projIcc.continuousOn
      exact hIoi_pc.image _ (continuous_subtype_val.comp f_r.continuous).continuousOn
    have hsubΩ : L_rad \ {p₁} ⊆ Ω := by
      rintro z ⟨hz, hzp⟩ (hzB | hzU)
      · exact hzp (hL_radB₁ ⟨hz, hzB⟩)
      · exact hL_radW₀ hz (Or.inl (Or.inr hzU))
    have hq₀_mem : q₀ ∈ L_rad \ {p₁} :=
      ⟨hL_rad_line.right_mem, fun h => hq₀_notB₁ (h ▸ hp₁B₁)⟩
    have := hpc.subset_connectedComponentIn hq₀_mem hsubΩ
    rwa [← connectedComponentIn_eq hq₀R] at this
  have hdisRG₂ : Disjoint R G₂ := by
    rw [disjoint_left]
    intro z_end hzR hzG₂
    have hj_rad : JoinedIn (ΓZ.Uᶜ) p₁ q₀ := by
      refine ((GM07.joinedIn_iff_eq_or_exists_isLineWithEnds
        (show p₁ ∈ ΓZ.Uᶜ from fun h => hp₁W₀ (Or.inl (Or.inr h)))
        (show q₀ ∈ ΓZ.Uᶜ from fun h => hq₀Ω (Or.inr h))).mpr
        (Or.inr ⟨L_rad, fun x hx hU => hL_radW₀ hx (Or.inl (Or.inr hU)), hL_rad_line⟩))
    have hj_R : JoinedIn (ΓZ.Uᶜ) q₀ z_end :=
      (hR_pc.joinedIn q₀ hq₀R z_end hzR).mono fun x hx hU => hR_sub_Ω hx (Or.inr hU)
    have hj_tot := hj_rad.trans hj_R
    have hp₁_ne_zend : p₁ ≠ z_end := fun h => hp₁W₀ (Or.inl (Or.inl (h ▸ hzG₂)))
    obtain ⟨L₀, hL₀_offU, hL₀_line⟩ := ((GM07.joinedIn_iff_eq_or_exists_isLineWithEnds
      (show p₁ ∈ ΓZ.Uᶜ from fun h => hp₁W₀ (Or.inl (Or.inr h)))
      (show z_end ∈ ΓZ.Uᶜ from fun h => hR_sub_Ω hzR (Or.inr h))).mp hj_tot).resolve_left hp₁_ne_zend
    -- Trim `L₀` at its first hit of `G₂` (`z₂ ∈ discBd G₂`) and then its last hit of `B₁` (`p₂ ∈ discBd B₁`).
    obtain ⟨f₀, hf0, hf1⟩ := hL₀_line
    let f : unitInterval → cap.Z := fun t => (f₀ t).1
    have hf_cont : Continuous f := continuous_subtype_val.comp f₀.continuous
    have hf_inj : Injective f := Subtype.val_injective.comp f₀.injective
    have hcG₂ : IsCompact (f ⁻¹' G₂) := (hG₂.isClosed.preimage hf_cont).isCompact
    obtain ⟨t₂, ht₂G₂, hlow₂⟩ := hcG₂.exists_isLeast ⟨1, by change (f₀ 1).1 ∈ G₂; rw [hf1]; exact hzG₂⟩
    have hcB₁ : IsCompact (Iic t₂ ∩ f ⁻¹' B₁) :=
      (isClosed_Iic.inter (hB₁.isClosed.preimage hf_cont)).isCompact
    obtain ⟨t₁, ⟨ht₁_le, ht₁B₁⟩, hhigh₁⟩ := hcB₁.exists_isGreatest
      ⟨0, unitInterval.nonneg t₂, by change (f₀ 0).1 ∈ B₁; rw [hf0]; exact hp₁B₁⟩
    have ht₁_lt_t₂ : t₁ < t₂ :=
      lt_of_le_of_ne ht₁_le fun heq => disjoint_left.mp hdisB₁G₂ ht₁B₁ (heq ▸ ht₂G₂)
    have hmid_off : ∀ t : unitInterval, t₁ < t → t < t₂ → f t ∉ B₁ ∧ f t ∉ G₂ := fun t h1 h2 =>
      ⟨fun hb => not_le.mpr h1 (hhigh₁ ⟨h2.le, hb⟩), fun hg => not_le.mpr h2 (hlow₂ hg)⟩
    have ht₁_bdB₁ : f t₁ ∈ discBd B₁ := by
      rw [← IsClosedDisc.frontier_eq_discBd hZ_cs hB₁, frontier_eq_closure_inter_closure,
        hB₁.isClosed.closure_eq]
      refine ⟨ht₁B₁, ?_⟩
      have hcl_t₁ : (t₁ : ℝ) ∈ closure (Ioo (t₁ : ℝ) (t₂ : ℝ)) := by
        rw [closure_Ioo (show (t₁ : ℝ) ≠ (t₂ : ℝ) from (Subtype.coe_lt_coe.mpr ht₁_lt_t₂).ne)]
        exact left_mem_Icc.mpr ht₁_lt_t₂.le
      have hcl_sub : t₁ ∈ closure (Ioo t₁ t₂) := by
        rw [mem_closure_iff]
        intro V hV htV
        obtain ⟨W, hW, rfl⟩ := isOpen_induced_iff.mp hV
        obtain ⟨r, hrW, hr1, hr2⟩ := mem_closure_iff.mp hcl_t₁ W hW htV
        have hrI : r ∈ Icc (0 : ℝ) 1 := ⟨le_trans t₁.2.1 hr1.le, le_trans hr2.le t₂.2.2⟩
        exact ⟨⟨r, hrI⟩, hrW, hr1, hr2⟩
      refine closure_mono ?_ (image_closure_subset_closure_image hf_cont ⟨t₁, hcl_sub, rfl⟩)
      rintro _ ⟨s, hs, rfl⟩
      exact (hmid_off s hs.1 hs.2).1
    have ht₂_bdG₂ : f t₂ ∈ discBd G₂ := by
      rw [← IsClosedDisc.frontier_eq_discBd hZ_cs hG₂, frontier_eq_closure_inter_closure,
        hG₂.isClosed.closure_eq]
      refine ⟨ht₂G₂, ?_⟩
      have hcl_t₂ : (t₂ : ℝ) ∈ closure (Ioo (t₁ : ℝ) (t₂ : ℝ)) := by
        rw [closure_Ioo (show (t₁ : ℝ) ≠ (t₂ : ℝ) from (Subtype.coe_lt_coe.mpr ht₁_lt_t₂).ne)]
        exact right_mem_Icc.mpr ht₁_lt_t₂.le
      have hcl_sub : t₂ ∈ closure (Ioo t₁ t₂) := by
        rw [mem_closure_iff]
        intro V hV htV
        obtain ⟨W, hW, rfl⟩ := isOpen_induced_iff.mp hV
        obtain ⟨r, hrW, hr1, hr2⟩ := mem_closure_iff.mp hcl_t₂ W hW htV
        have hrI : r ∈ Icc (0 : ℝ) 1 := ⟨le_trans t₁.2.1 hr1.le, le_trans hr2.le t₂.2.2⟩
        exact ⟨⟨r, hrI⟩, hrW, hr1, hr2⟩
      refine closure_mono ?_ (image_closure_subset_closure_image hf_cont ⟨t₂, hcl_sub, rfl⟩)
      rintro _ ⟨s, hs, rfl⟩
      exact (hmid_off s hs.1 hs.2).2
    let L_mid : Set cap.Z := f '' Icc t₁ t₂
    have hL_mid_line : IsLineWithEnds L_mid (f t₁) (f t₂) := subArc_of_lt hf_cont hf_inj ht₁_lt_t₂
    have hL_mid_sub_range : L_mid ⊆ range cap.j := by
      obtain ⟨_, _, _, _, _, _, hD₁E', _⟩ := cap.disc₁_disc₂_spec σ.isCylinder.1 σ.isHoop_F₁
      obtain ⟨_, _, _, _, _, _, _, hD₂G'⟩ := cap.disc₁_disc₂_spec σ.isCylinder.1 σ.isHoop_F₂
      have hD₁B₁ : cap.D₁ ⊆ B₁ := hD₁E'.trans hE₁B₁
      refine cap.subset_range_of_disjoint_discInts ?_ ?_
      · refine disjoint_left.mpr ?_
        rintro z ⟨t, ⟨ht1, ht2⟩, rfl⟩ hzInt
        have hzIntB₁ := discInt_mono hman cap.isClosedDisc_D₁ hD₁B₁ hzInt
        rcases eq_or_lt_of_le ht1 with rfl | hlt1
        · exact hzIntB₁.2 ht₁_bdB₁
        · rcases eq_or_lt_of_le ht2 with rfl | hlt2
          · exact disjoint_left.mp hdisB₁G₂ hzIntB₁.1 ht₂G₂
          · exact (hmid_off t hlt1 hlt2).1 hzIntB₁.1
      · refine disjoint_left.mpr ?_
        rintro z ⟨t, ⟨ht1, ht2⟩, rfl⟩ hzInt
        have hzIntG₂ := discInt_mono hman cap.isClosedDisc_D₂ hD₂G' hzInt
        rcases eq_or_lt_of_le ht2 with rfl | hlt2
        · exact hzIntG₂.2 ht₂_bdG₂
        · rcases eq_or_lt_of_le ht1 with rfl | hlt1
          · exact disjoint_left.mp hdisB₁G₂ ht₁B₁ hzIntG₂.1
          · exact (hmid_off t hlt1 hlt2).2 hzIntG₂.1
    obtain ⟨u_S, hu_S_eq⟩ := hL_mid_sub_range ⟨t₁, ⟨le_rfl, ht₁_lt_t₂.le⟩, rfl⟩
    have hu_S_H₁ : u_S ∈ H₁ := by change cap.j u_S ∈ discBd B₁; rw [hu_S_eq]; exact ht₁_bdB₁
    obtain ⟨v_S, hv_S_F₂, hv_S_eq⟩ : ∃ v_S ∈ σ.F₂, cap.j v_S = f t₂ := by
      rw [← mem_image, ← hbG₂]; exact ht₂_bdG₂
    let I_S : Set S := cap.j ⁻¹' L_mid
    have hL_mid_line' : IsLineWithEnds L_mid (cap.j u_S) (cap.j v_S) := by
      rw [hu_S_eq, hv_S_eq]; exact hL_mid_line
    have hI_S_line : IsLineWithEnds I_S u_S v_S :=
      GM07.pull_line cap.isClosedEmbedding.isEmbedding hL_mid_line' hL_mid_sub_range
    have hI_S_offU : Disjoint I_S σ.Γ.U := disjoint_left.mpr fun x hxI hxU => by
      have hfx : cap.j x ∈ L₀ := by
        obtain ⟨t, _, heq⟩ := hxI
        exact heq ▸ (f₀ t).2
      exact hL₀_offU hfx (hUZ ▸ mem_image_of_mem _ hxU)
    have hNI_S : (σ.subTube hlamH₁ hNH₁ σ.isNormal_F₂).Γ.IsNormal I_S := by
      rintro x ⟨hxI, hxU⟩
      have hxU_full := (interSet_U_subset_of_isClosed σ.Γ (isClosed_cylinderBetween hlamH₁) hxU).1
      exact absurd hxU_full (disjoint_left.mp hI_S_offU hxI)
    have hcard0 : (I_S ∩ (σ.subTube hlamH₁ hNH₁ σ.isNormal_F₂).Γ.V).ncard = 0 := by
      suffices hemp : I_S ∩ (σ.subTube hlamH₁ hNH₁ σ.isNormal_F₂).Γ.V = ∅ by
        rw [hemp, ncard_empty]
      ext x
      simp only [mem_inter_iff, mem_empty_iff_false, iff_false]
      rintro ⟨hxI, hxV⟩
      have hxV_full := (interSet_V_of_isClosed σ.Γ (isClosed_cylinderBetween hlamH₁)).subset hxV
      exact disjoint_left.mp hI_S_offU hxI (σ.Γ.V_subset_U hxV_full.1)
    have hge := ((σ.subTube hlamH₁ hNH₁ σ.isNormal_F₂).le_length_iff.mp hlen_H₁)
      I_S u_S v_S hI_S_line hu_S_H₁ hv_S_F₂ hNI_S
    omega
  -- Step 3: Prove `(closure R \ B₁) ∩ ΓZ.V` is nonempty using maximality of `B₁`.
  have hex_w₀ : ((closure R \ B₁) ∩ ΓZ.V).Nonempty := by
    by_contra hemp
    have hclR_V_sub_B₁ : closure R ∩ ΓZ.V ⊆ B₁ := fun z ⟨hzcl, hzV⟩ =>
      by_contra fun hnotB => hemp ⟨z, ⟨hzcl, hnotB⟩, hzV⟩
    have hclR_in_R : ∀ z ∈ closure R, z ∈ Ω → z ∈ R := fun z hzcl hzΩ => by
      obtain ⟨w, hw1, hw2⟩ := mem_closure_iff.mp hzcl (connectedComponentIn Ω z)
        hΩ_open.connectedComponentIn (mem_connectedComponentIn hzΩ)
      have heq_comp : R = connectedComponentIn Ω z :=
        (connectedComponentIn_eq hw2).trans (connectedComponentIn_eq hw1).symm
      exact heq_comp ▸ mem_connectedComponentIn hzΩ
    have hdis_clR_G₂ : Disjoint (closure R) G₂ := by
      have hdis_int : Disjoint (closure R) (discInt G₂) :=
        (hdisRG₂.mono_right (discInt_subset G₂)).closure_left (hG₂.isOpen_discInt hman)
      rw [disjoint_left]
      intro z hzcl hzG₂
      by_cases hzU : z ∈ ΓZ.U
      · have hzV : z ∈ ΓZ.V := hUG₂_sub_V ⟨hzU, hzG₂⟩
        exact disjoint_left.mp hdisB₁G₂ (hclR_V_sub_B₁ ⟨hzcl, hzV⟩) hzG₂
      · have hzΩ : z ∈ Ω := fun h =>
          h.elim (fun hB => disjoint_left.mp hdisB₁G₂ hB hzG₂) hzU
        exact disjoint_left.mp hdisRG₂ (hclR_in_R z hzcl hzΩ) hzG₂
    -- Helper: absorbing a closed disc `M` bounded by a single edge `e` outside `B₁` gives a
    -- strictly better `GoodDisc`, contradicting `hB₁_max`.
    have habsorb_contradiction : ∀ (e : Set cap.Z) (he : e ∈ ΓZ.E) (hnotB₁ : ¬ e ⊆ B₁)
        (M : Set cap.Z) (hM : IsClosedDisc M) (hB₁M : B₁ ⊆ M) (heM : e ⊆ M)
        (hdisMG₂ : Disjoint M G₂)
        (hbdM : discBd M ∩ (ΓZ.U \ e) ⊆ ΓZ.V ∩ discBd E₁)
        (hu₀ : ∃ u₀ ∈ discBd M ∩ discBd E₁, u₀ ∈ ΓZ.V), False := by
      intro e he hnotB₁ M hM hB₁M heM hdisMG₂ hbdM ⟨u₀, ⟨hu₀BdM, hu₀BdE₁⟩, hu₀V⟩
      have hM_sub_intG₁ : M ⊆ G₁ \ discBd G₁ := fun z hz =>
        ⟨(hcupG ▸ mem_univ z).resolve_right (disjoint_left.mp hdisMG₂ hz),
          fun hb => disjoint_left.mp hdisMG₂ hz (Surface.discBd_subset G₂ (hbG₂ ▸ hbG₁ ▸ hb))⟩
      let Z_e := (ΓZ.U \ e) ∪ G₂
      have hZe_cl : IsClosed Z_e := (isClosed_U_diff_edge ΓZ he).union hG₂.isClosed
      obtain ⟨D, hD, hMD, _, hdiffZ, hbdDM, hkeepM, hbdDZ⟩ :=
        GM07.exists_disc_push_off hM hG₁ hM_sub_intG₁ hZe_cl
      have hdis_e_G₂ : Disjoint e G₂ := disjoint_left.mpr fun z hze hzG₂ =>
        (he.2.1 hze).2 (hUG₂_sub_V ⟨(he.2.1 hze).1, hzG₂⟩)
      have hGoodD : GoodDisc D := by
        refine ⟨hD, hE₁B₁.trans (hB₁M.trans hMD), ?_, ?_, ?_⟩
        · refine disjoint_left.mpr fun z hzD hzG₂ => ?_
          by_cases hzM : z ∈ M
          · exact disjoint_left.mp hdisMG₂ hzM hzG₂
          · exact disjoint_left.mp hdiffZ ⟨hzD, hzM⟩ (Or.inr hzG₂)
        · rintro z ⟨hzBdD, hzU⟩
          have hz_not_e : z ∉ e := fun hze => by
            rcases hbdDM ⟨hzBdD, heM hze⟩ with ⟨_, hne_e⟩ | hzG₂
            · exact hne_e hze
            · exact disjoint_left.mp hdis_e_G₂ hze hzG₂
          have hzBdM : z ∈ discBd M := hbdDZ ⟨hzBdD, Or.inl ⟨hzU, hz_not_e⟩⟩
          exact hbdM ⟨hzBdM, hzU, hz_not_e⟩
        · have hu₀_Ze : u₀ ∈ Z_e :=
            Or.inl ⟨ΓZ.V_subset_U hu₀V, fun hze => (he.2.1 hze).2 hu₀V⟩
          exact ⟨u₀, hkeepM ⟨hu₀BdM, hu₀_Ze⟩, hu₀BdE₁⟩
      have hB₁D : B₁ ⊆ D := hB₁M.trans hMD
      have hlt_card : {e' ∈ ΓZ.E | e' ⊆ B₁}.ncard < {e' ∈ ΓZ.E | e' ⊆ D}.ncard :=
        ncard_lt_ncard
          ⟨fun e' ⟨he', hsub⟩ => ⟨he', hsub.trans hB₁D⟩,
            fun hall => hnotB₁ (hall ⟨he, heM.trans hMD⟩).2⟩
          (ΓZ.finite_edges.subset fun _ h => h.1)
      exact absurd (hB₁_max D hGoodD) (not_le.mpr hlt_card)
    -- Collect all pinched exterior loop-discs on `B₁` and take inclusion-maximal ones.
    let IsPinchedDisc : Set cap.Z → Prop := fun Δ =>
      ∃ e ∈ ΓZ.E, ∃ u ∈ discBd B₁ ∩ ΓZ.V,
        Disjoint e B₁ ∧ IsClosedDisc Δ ∧ discBd Δ = closure e ∧
        closure e ∩ ΓZ.V = {u} ∧ Disjoint Δ G₂ ∧ Δ ∩ B₁ = {u}
    -- Every `IsPinchedDisc Δ` determines `e` uniquely (`e = discBd Δ \ ΓZ.V`), so there are
    -- finitely many `IsPinchedDisc`s!
    have hPinched_sub : {Δ : Set cap.Z | IsPinchedDisc Δ} ⊆
        (fun p : Set cap.Z × Bool =>
          if h : ∃ hO : IsOArc (closure p.1), True then
            if p.2 then (sphere_disc cap.Z cap.isSphere (closure p.1) h.fst).choose
            else (sphere_disc cap.Z cap.isSphere (closure p.1) h.fst).choose_spec.choose
          else ∅) '' (ΓZ.E ×ˢ (univ : Set Bool)) := by
      intro Δ ⟨e, he, _, _, _, hΔ, hbdΔ, _, _, _⟩
      have hO : IsOArc (closure e) := hbdΔ ▸ hΔ.isOArc_discBd
      have hex : ∃ hO : IsOArc (closure e), True := ⟨hO, trivial⟩
      rcases (sphere_disc cap.Z cap.isSphere (closure e) hex.fst).choose_spec.choose_spec with
        ⟨_, _, _, _, _, _, _, -, huniq⟩
      rcases huniq Δ hΔ hbdΔ with h1 | h2
      · refine ⟨(e, true), ⟨he, mem_univ _⟩, ?_⟩
        simp only [hex, ↓reduceDIte, ↓reduceIte]
        exact h1.symm
      · refine ⟨(e, false), ⟨he, mem_univ _⟩, ?_⟩
        simp only [hex, ↓reduceDIte, Bool.false_eq_true, ↓reduceIte]
        exact h2.symm
    have hPinched_fin : {Δ : Set cap.Z | IsPinchedDisc Δ}.Finite :=
      ((ΓZ.finite_edges.prod finite_univ).image _).subset hPinched_sub
    let PFin : Finset (Set cap.Z) := hPinched_fin.toFinset
    let MFin : Finset (Set cap.Z) :=
      PFin.filter fun Δ => ∀ Δ' ∈ PFin, Δ ⊆ Δ' → Δ = Δ'
    -- Every member of `PFin` lies in some maximal member in `MFin`.
    have hsub_MFin : ∀ Δ ∈ PFin, ∃ Δ' ∈ MFin, Δ ⊆ Δ' := by
      intro Δ hΔP
      let C := PFin.filter fun Δ' => Δ ⊆ Δ'
      have hC_ne : C.Nonempty := ⟨Δ, Finset.mem_filter.mpr ⟨hΔP, Subset.rfl⟩⟩
      obtain ⟨Δ', hΔ'C, hmax⟩ := C.exists_maximal hC_ne
      obtain ⟨hΔ'P, hΔ_sub⟩ := Finset.mem_filter.mp hΔ'C
      refine ⟨Δ', Finset.mem_filter.mpr ⟨hΔ'P, fun Δ'' hΔ''P hsub' => ?_⟩, hΔ_sub⟩
      exact Subset.antisymm hsub'
        (hmax (Finset.mem_filter.mpr ⟨hΔ''P, hΔ_sub.trans hsub'⟩) hsub')
    -- Any two distinct pinched discs are either nested or meet only inside `B₁`.
    have hPinched_dichotomy : ∀ Δ₁ ∈ PFin, ∀ Δ₂ ∈ PFin,
        Δ₁ ⊆ Δ₂ ∨ Δ₂ ⊆ Δ₁ ∨ Δ₁ ∩ Δ₂ ⊆ B₁ := by
      intro Δ₁ h1 Δ₂ h2
      obtain ⟨e₁, he₁, u₁, hu₁, hdis1B, hΔ₁, hbd1, hcap1, hdis1G, hpin1⟩ :=
        hPinched_fin.mem_toFinset.mp h1
      obtain ⟨e₂, he₂, u₂, hu₂, hdis2B, hΔ₂, hbd2, hcap2, hdis2G, hpin2⟩ :=
        hPinched_fin.mem_toFinset.mp h2
      by_cases he12 : e₁ = e₂
      · subst he12
        obtain ⟨D_a, D_b, _, _, _, _, _, hcup_ab, _, _, huniq_ab⟩ :=
          sphere_disc cap.Z cap.isSphere (closure e₁) (hbd1 ▸ hΔ₁.isOArc_discBd)
        obtain ⟨zg, hzg⟩ := hG₂.nonempty_discInt
        rcases huniq_ab Δ₁ hΔ₁ hbd1 with rfl | rfl <;>
          rcases huniq_ab Δ₂ hΔ₂ hbd2 with h_eq | h_eq
        · exact Or.inl h_eq.symm.le
        · exfalso
          rcases hcup_ab ▸ mem_univ zg with hza | hzb
          · exact disjoint_left.mp hdis1G hza hzg.1
          · exact disjoint_left.mp hdis2G (h_eq.symm ▸ hzb) hzg.1
        · exfalso
          rcases hcup_ab ▸ mem_univ zg with hza | hzb
          · exact disjoint_left.mp hdis2G (h_eq.symm ▸ hza) hzg.1
          · exact disjoint_left.mp hdis1G hzb hzg.1
        · exact Or.inl h_eq.symm.le
      · have hcl1_eq : closure e₁ = e₁ ∪ {u₁} := by
          ext z
          constructor
          · intro hz
            by_cases hzV : z ∈ ΓZ.V
            · exact Or.inr (hcap1.subset ⟨hz, hzV⟩)
            · exact Or.inl ((GM09.closure_edge_diff_V_eq ΓZ he₁).subset ⟨hz, hzV⟩)
          · rintro (hze | rfl)
            · exact subset_closure hze
            · exact (hcap1.symm.subset rfl).1
        have hcl2_eq : closure e₂ = e₂ ∪ {u₂} := by
          ext z
          constructor
          · intro hz
            by_cases hzV : z ∈ ΓZ.V
            · exact Or.inr (hcap2.subset ⟨hz, hzV⟩)
            · exact Or.inl ((GM09.closure_edge_diff_V_eq ΓZ he₂).subset ⟨hz, hzV⟩)
          · rintro (hze | rfl)
            · exact subset_closure hze
            · exact (hcap2.symm.subset rfl).1
        have hdis_e1_bd2 : Disjoint e₁ (discBd Δ₂) := by
          rw [hbd2, hcl2_eq, disjoint_union_right]
          exact ⟨disjoint_edges_of_ne_local ΓZ he₁ he₂ he12,
            disjoint_singleton_right.mpr fun h => (he₁.2.1 h).2 hu₂.2⟩
        have hdis_e2_bd1 : Disjoint e₂ (discBd Δ₁) := by
          rw [hbd1, hcl1_eq, disjoint_union_right]
          exact ⟨disjoint_edges_of_ne_local ΓZ he₂ he₁ (Ne.symm he12),
            disjoint_singleton_right.mpr fun h => (he₂.2.1 h).2 hu₁.2⟩
        -- Helper: if `e_a ⊆ Δ_b`, then `Δ_a ⊆ Δ_b` (since both avoid `G₂`).
        have hsub_of_edge : ∀ {A B : Set cap.Z} {ea : Set cap.Z},
            IsClosedDisc A → IsClosedDisc B → discBd A = closure ea →
            Disjoint A G₂ → Disjoint B G₂ → ea ⊆ B → A ⊆ B := by
          intro A B ea hA hB hbdA hAG hBG heaB
          obtain ⟨hEB, hbEB⟩ := GM12.isClosedDisc_closure_compl_of_sphere hZ_cs cap.isSphere hB
          have hBc_eq : Bᶜ = discInt (closure (univ \ B)) := by
            ext x
            rw [mem_compl_iff, discInt, mem_sdiff, hbEB]
            refine ⟨fun hx => ⟨subset_closure ⟨mem_univ x, hx⟩,
                fun hb => hx (Surface.discBd_subset B hb)⟩,
              fun ⟨hxcl, hnotBd⟩ hxB => hnotBd ?_⟩
            rw [← IsClosedDisc.frontier_eq_discBd hZ_cs hB, frontier_eq_closure_inter_closure,
              hB.isClosed.closure_eq, compl_eq_univ_sdiff]
            exact ⟨hxB, hxcl⟩
          have hBc_pc : IsPreconnected Bᶜ := hBc_eq ▸ hEB.isPreconnected_discInt
          have hbdA_sub : discBd A ⊆ B := hbdA ▸ closure_minimal heaB hB.isClosed
          have hdis_fr : Disjoint Bᶜ (frontier A) := by
            rw [IsClosedDisc.frontier_eq_discBd hZ_cs hA]
            exact disjoint_left.mpr fun z hzBc hzBdA => hzBc (hbdA_sub hzBdA)
          obtain ⟨zg, hzg⟩ := hG₂.nonempty_discInt
          have hzg_notB : zg ∈ Bᶜ := fun h => disjoint_left.mp hBG h hzg.1
          have hzg_notA : zg ∉ A := fun h => disjoint_left.mp hAG h hzg.1
          rcases GM07.inside_or_off hBc_pc hA.isClosed hdis_fr with hsub_int | hsub_c
          · exact False.elim (hzg_notA (interior_subset (hsub_int hzg_notB)))
          · exact fun x hx => by_contra fun hxB => hsub_c hxB hx
        have hdis_fr2 : Disjoint e₁ (frontier Δ₂) :=
          IsClosedDisc.frontier_eq_discBd hZ_cs hΔ₂ ▸ hdis_e1_bd2
        rcases GM07.inside_or_off he₁.2.2.1.isConnected.isPreconnected hΔ₂.isClosed hdis_fr2 with
            h1_in | h1_off
        · exact Or.inl (hsub_of_edge hΔ₁ hΔ₂ hbd1 hdis1G hdis2G (h1_in.trans interior_subset))
        · have hdis_fr1 : Disjoint e₂ (frontier Δ₁) :=
            IsClosedDisc.frontier_eq_discBd hZ_cs hΔ₁ ▸ hdis_e2_bd1
          rcases GM07.inside_or_off he₂.2.2.1.isConnected.isPreconnected hΔ₁.isClosed hdis_fr1 with
              h2_in | h2_off
          · exact Or.inr (Or.inl
              (hsub_of_edge hΔ₂ hΔ₁ hbd2 hdis2G hdis1G (h2_in.trans interior_subset)))
          · have hdis_int1_bd2 : Disjoint (discInt Δ₁) (discBd Δ₂) := by
              rw [hbd2, hcl2_eq, disjoint_union_right]
              refine ⟨disjoint_left.mpr fun x hx hxe2 => h2_off hxe2 hx.1,
                disjoint_singleton_right.mpr fun hu2_int => ?_⟩
              have hu2_u1 : u₂ = u₁ := hpin1.subset ⟨hu2_int.1, Surface.discBd_subset B₁ hu₂.1⟩
              exact hu2_int.2 (hbd1 ▸ hcl1_eq ▸ Or.inr hu2_u1)
            by_cases hne_int : (discInt Δ₁ ∩ Δ₂).Nonempty
            · exact Or.inl (GM07.disc_subset_of_int_off_bd hman hΔ₁ hΔ₂ hdis_int1_bd2 hne_int)
            · right; right
              intro x ⟨hx1, hx2⟩
              have hx_bd1 : x ∈ discBd Δ₁ :=
                by_contra fun hn => hne_int ⟨x, ⟨hx1, hn⟩, hx2⟩
              rw [hbd1, hcl1_eq] at hx_bd1
              rcases hx_bd1 with hxe1 | rfl
              · exact absurd hx2 (h1_off hxe1)
              · exact Surface.discBd_subset B₁ hu₁.1
    -- Apply `isPathConnected_compl_union_pinched` to `MFin`.
    have hMFin_mem : ∀ {Δ}, Δ ∈ MFin → IsPinchedDisc Δ := fun h =>
      hPinched_fin.mem_toFinset.mp (Finset.mem_filter.mp h).1
    have hex_u : ∀ Δ : Set cap.Z, Δ ∈ MFin →
        ∃ u : cap.Z, u ∈ discBd Δ ∧ Δ ∩ B₁ = {u} ∧ Disjoint Δ G₂ := by
      intro Δ hΔM
      obtain ⟨e, _, u, _, _, _, hbdΔ, hcape, hdisG, hpin⟩ := hMFin_mem hΔM
      exact ⟨u, hbdΔ ▸ (hcape.symm.subset rfl).1, hpin, hdisG⟩
    have : Nonempty cap.Z := ⟨q₀⟩
    choose! u_M hu_M using hex_u
    obtain ⟨zg, hzg⟩ := hG₂.nonempty_discInt
    have hzg_notB₁ : zg ∉ B₁ := fun h => disjoint_left.mp hdisB₁G₂ h hzg.1
    have hM_pair : ∀ Δ₁ ∈ MFin, ∀ Δ₂ ∈ MFin, Δ₁ ≠ Δ₂ → Δ₁ ∩ Δ₂ ⊆ B₁ := by
      intro Δ₁ h1 Δ₂ h2 hne
      rcases hPinched_dichotomy Δ₁ (Finset.mem_filter.mp h1).1
          Δ₂ (Finset.mem_filter.mp h2).1 with hs1 | hs2 | hcapB
      · exact absurd ((Finset.mem_filter.mp h1).2 Δ₂ (Finset.mem_filter.mp h2).1 hs1) hne
      · exact absurd ((Finset.mem_filter.mp h2).2 Δ₁ (Finset.mem_filter.mp h1).1 hs2).symm hne
      · exact hcapB
    obtain ⟨_, hUext_pc⟩ := isPathConnected_compl_union_pinched hZ_cs cap.isSphere hB₁ hzg_notB₁
      id u_M MFin
      (fun Δ hΔ => (hMFin_mem hΔ).choose_spec.2.choose_spec.2.2.1)
      (fun Δ hΔ => (hu_M Δ hΔ).1)
      (fun Δ hΔ => (hu_M Δ hΔ).2.1)
      hM_pair
      (fun Δ hΔ h => disjoint_left.mp (hu_M Δ hΔ).2.2 h hzg.1)
    let U_ext : Set cap.Z := (B₁ ∪ ⋃ Δ ∈ MFin, Δ)ᶜ
    have hq₀_Uext : q₀ ∈ U_ext := by
      rintro (hqB | hqU)
      · exact hq₀_notB₁ hqB
      · obtain ⟨Δ, hΔM, hqΔ⟩ := mem_iUnion₂.mp hqU
        obtain ⟨e, he, _, _, _, hΔ, hbdΔ, _, _, _⟩ := hMFin_mem hΔM
        have hdis_L_fr : Disjoint L_rad (frontier Δ) := by
          rw [IsClosedDisc.frontier_eq_discBd hZ_cs hΔ, hbdΔ]
          exact disjoint_left.mpr fun z hzL hze =>
            hL_radW₀ hzL (Or.inl (Or.inr (ΓZ.closure_subset_U he hze)))
        have hL_rad_pc : IsPreconnected L_rad := by
          obtain ⟨f_r, _, _⟩ := hL_rad_line
          have hrng : L_rad = range (fun t : unitInterval => (f_r t).1) := by
            ext z
            exact ⟨fun hz => ⟨f_r.symm ⟨z, hz⟩, by simp⟩, fun ⟨t, ht⟩ => ht ▸ (f_r t).2⟩
          rw [hrng]
          exact (isConnected_range (continuous_subtype_val.comp f_r.continuous)).isPreconnected
        rcases GM07.inside_or_off hL_rad_pc
            hΔ.isClosed hdis_L_fr with hLin | hLoff
        · have hp₁Δ : p₁ ∈ Δ := interior_subset (hLin hL_rad_line.left_mem)
          have hp₁_u : p₁ = u_M Δ := (hu_M Δ hΔM).2.1.subset ⟨hp₁Δ, hp₁B₁⟩
          have hu_V : u_M Δ ∈ ΓZ.V := by
            obtain ⟨e', _, u', hu', _, _, _, _, _, hpin'⟩ := hMFin_mem hΔM
            have : u_M Δ = u' := hpin'.subset ((hu_M Δ hΔM).2.1.symm.subset rfl)
            exact this ▸ hu'.2
          exact hp₁W₀ (Or.inl (Or.inr (ΓZ.V_subset_U (hp₁_u ▸ hu_V))))
        · exact hLoff hL_rad_line.right_mem hqΔ
    have hzg_Uext : zg ∈ U_ext := by
      rintro (hzB | hzU)
      · exact hzg_notB₁ hzB
      · obtain ⟨Δ, hΔM, hzΔ⟩ := mem_iUnion₂.mp hzU
        exact disjoint_left.mp (hu_M Δ hΔM).2.2 hzΔ hzg.1
    obtain ⟨γ_ex, hγ_ex⟩ := hUext_pc.joinedIn q₀ hq₀_Uext zg hzg_Uext
    have hK_ex : IsCompact (γ_ex ⁻¹' Rᶜ) := (hR_open.isClosed_compl.preimage γ_ex.continuous).isCompact
    have h1_mem_ex : (1 : unitInterval) ∈ γ_ex ⁻¹' Rᶜ := by
      change γ_ex 1 ∉ R
      rw [γ_ex.target]
      exact fun h => disjoint_left.mp hdisRG₂ h hzg.1
    obtain ⟨t_ex, ht_ex_notR, hlow_ex⟩ := hK_ex.exists_isLeast ⟨1, h1_mem_ex⟩
    have ht_ex_pos : (0 : unitInterval) < t_ex :=
      lt_of_le_of_ne t_ex.2.1 fun h0 => ht_ex_notR (by rw [← h0, γ_ex.source]; exact hq₀R)
    have hz_ex_clR : γ_ex t_ex ∈ closure R := by
      have hcl_t : (t_ex : ℝ) ∈ closure (Ioo (0 : ℝ) (t_ex : ℝ)) := by
        rw [closure_Ioo (show (0 : ℝ) ≠ (t_ex : ℝ) from (Subtype.coe_lt_coe.mpr ht_ex_pos).ne)]
        exact right_mem_Icc.mpr ht_ex_pos.le
      have hcl_sub : t_ex ∈ closure (Ioo (0 : unitInterval) t_ex) := by
        rw [mem_closure_iff]
        intro V hV htV
        obtain ⟨W, hW, rfl⟩ := isOpen_induced_iff.mp hV
        obtain ⟨r, hrW, hr1, hr2⟩ := mem_closure_iff.mp hcl_t W hW htV
        have hrI : r ∈ Icc (0 : ℝ) 1 := ⟨hr1.le, le_trans hr2.le t_ex.2.2⟩
        exact ⟨⟨r, hrI⟩, hrW, hr1, hr2⟩
      refine closure_mono ?_
        (image_closure_subset_closure_image γ_ex.continuous ⟨t_ex, hcl_sub, rfl⟩)
      rintro _ ⟨s, hs, rfl⟩
      exact by_contra fun hnR => not_le.mpr hs.2 (hlow_ex hnR)
    let z_ex := γ_ex t_ex
    have hz_ex_Uext : z_ex ∈ U_ext := hγ_ex t_ex
    have hz_ex_notB₁ : z_ex ∉ B₁ := fun h => hz_ex_Uext (Or.inl h)
    have hz_ex_U : z_ex ∈ ΓZ.U := by
      by_contra hnU
      have hzΩ : z_ex ∈ Ω := fun h => h.elim hz_ex_notB₁ hnU
      exact ht_ex_notR (hclR_in_R z_ex hz_ex_clR hzΩ)
    have hz_ex_notV : z_ex ∉ ΓZ.V := fun hV => hz_ex_notB₁ (hclR_V_sub_B₁ ⟨hz_ex_clR, hV⟩)
    obtain ⟨e, he, hze⟩ := ΓZ.exists_edge_of_mem hz_ex_U hz_ex_notV
    have hdis_e_frB₁ : Disjoint e (frontier B₁) := by
      rw [IsClosedDisc.frontier_eq_discBd hZ_cs hB₁]
      exact disjoint_left.mpr fun y hye hyBd => (he.2.1 hye).2 (hbdB₁U ⟨hyBd, (he.2.1 hye).1⟩).1
    have hdis_e_B₁ : Disjoint e B₁ := by
      rcases GM07.inside_or_off he.2.2.1.isConnected.isPreconnected hB₁.isClosed hdis_e_frB₁ with
          hin | hoff
      · exact False.elim (hz_ex_notB₁ (interior_subset (hin hze)))
      · exact disjoint_left.mpr hoff
    have hnot_e_B₁ : ¬ e ⊆ B₁ := fun h => hz_ex_notB₁ (h hze)
    have hcle_clR : closure e ⊆ closure R :=
      closure_edge_subset_closure_component hZ_cs ΓZ hB₁.isClosed he hdis_e_B₁ ⟨z_ex, hze, hz_ex_clR⟩
    have hdis_cle_G₂ : Disjoint (closure e) G₂ := hdis_clR_G₂.mono_left hcle_clR
    have hcle_V_bd : closure e ∩ ΓZ.V ⊆ discBd B₁ ∩ discBd E₁ := by
      rintro v ⟨hvcl, hvV⟩
      have hvB₁ : v ∈ B₁ := hclR_V_sub_B₁ ⟨hcle_clR hvcl, hvV⟩
      have hvBdB₁ : v ∈ discBd B₁ := by
        rw [← IsClosedDisc.frontier_eq_discBd hZ_cs hB₁, frontier_eq_closure_inter_closure,
          hB₁.isClosed.closure_eq]
        exact ⟨hvB₁, closure_mono (disjoint_left.mp hdis_e_B₁) hvcl⟩
      exact ⟨hvBdB₁, (hbdB₁U ⟨hvBdB₁, ΓZ.V_subset_U hvV⟩).2⟩
    rcases ΓZ.edge_cond e he with ⟨a, b, hab, hcap_e, hline_e⟩ | ⟨u, hcap_e, ho_e⟩
    · have ha_mem : a ∈ closure e ∩ ΓZ.V := hcap_e.symm.subset (Or.inl rfl)
      have hb_mem : b ∈ closure e ∩ ΓZ.V := hcap_e.symm.subset (Or.inr rfl)
      have ha_bd := hcle_V_bd ha_mem
      have hb_bd := hcle_V_bd hb_mem
      have hcle_B₁ : closure e ∩ B₁ ⊆ {a, b} := by
        rintro x ⟨hxcl, hxB₁⟩
        by_cases hxV : x ∈ ΓZ.V
        · exact hcap_e.subset ⟨hxcl, hxV⟩
        · have hxe : x ∈ e := (GM09.closure_edge_diff_V_eq ΓZ he).subset ⟨hxcl, hxV⟩
          exact absurd hxB₁ (disjoint_left.mp hdis_e_B₁ hxe)
      have hG₂_pc : IsPreconnected G₂ := by
        have heq_G₂ : closure (discInt G₂) = G₂ :=
          Subset.antisymm (closure_minimal (discInt_subset G₂) hG₂.isClosed)
            hG₂.subset_closure_discInt
        exact heq_G₂ ▸ hG₂.isPreconnected_discInt.closure
      obtain ⟨A₂, Δ₁, _, hdiscM, hcle_Δ₁, hdisG₂M, hbdM, hA₂_sub, _, _, _, _, _, _⟩ :=
        GM07.exists_chord_fill (X := (∅ : Set cap.Z)) hZ_cs cap.isSphere hB₁ hline_e hab
          ha_bd.1 hb_bd.1 hcle_B₁ hG₂_pc hdisB₁G₂.symm hdis_cle_G₂.symm
      refine habsorb_contradiction e he hnot_e_B₁ (B₁ ∪ Δ₁) hdiscM subset_union_left
        (subset_closure.trans (hcle_Δ₁.trans subset_union_right)) hdisG₂M.symm ?_ ?_
      · rw [hbdM]
        rintro x ⟨hxA₂ | hxcle, hxU, hxne⟩
        · exact hbdB₁U ⟨hA₂_sub hxA₂, hxU⟩
        · have hxV : x ∈ ΓZ.V := by_contra fun hnV =>
            hxne ((GM09.closure_edge_diff_V_eq ΓZ he).subset ⟨hxcle, hnV⟩)
          exact ⟨hxV, (hcle_V_bd ⟨hxcle, hxV⟩).2⟩
      · exact ⟨a, ⟨hbdM ▸ Or.inr ha_mem.1, ha_bd.2⟩, ha_mem.2⟩
    · have hu_mem : u ∈ closure e ∩ ΓZ.V := hcap_e.symm.subset rfl
      have hu_bd := hcle_V_bd hu_mem
      obtain ⟨Δ_a, Δ_b, _, hΔ_a, hΔ_b, hb_a, hb_b, hcup_ab, hcap_ab, _, _⟩ :=
        sphere_disc cap.Z cap.isSphere (closure e) ho_e
      have hG₂_pc : IsPreconnected G₂ := by
        have heq_G₂ : closure (discInt G₂) = G₂ :=
          Subset.antisymm (closure_minimal (discInt_subset G₂) hG₂.isClosed)
            hG₂.subset_closure_discInt
        exact heq_G₂ ▸ hG₂.isPreconnected_discInt.closure
      have hex_Δe : ∃ Δ_e Δ_o : Set cap.Z, IsClosedDisc Δ_e ∧ IsClosedDisc Δ_o ∧
          discBd Δ_e = closure e ∧ Δ_e ∪ Δ_o = univ ∧ Δ_e ∩ Δ_o = closure e ∧
          Disjoint Δ_e G₂ := by
        have hcovG : G₂ ⊆ Δ_a ∪ Δ_b := hcup_ab ▸ subset_univ G₂
        by_cases hhit_a : (G₂ ∩ Δ_a).Nonempty
        · refine ⟨Δ_b, Δ_a, hΔ_b, hΔ_a, hb_b, by rw [union_comm, hcup_ab],
            by rw [inter_comm, hcap_ab], disjoint_left.mpr fun z hzb hzG => ?_⟩
          obtain ⟨w, hwG, hwa⟩ := hhit_a
          obtain ⟨x, hxG, hxa, hxb⟩ := isPreconnected_closed_iff.mp hG₂_pc Δ_a Δ_b
            hΔ_a.isClosed hΔ_b.isClosed hcovG ⟨w, hwG, hwa⟩ ⟨z, hzG, hzb⟩
          exact disjoint_left.mp hdis_cle_G₂ (hcap_ab ▸ ⟨hxa, hxb⟩) hxG
        · exact ⟨Δ_a, Δ_b, hΔ_a, hΔ_b, hb_a, hcup_ab, hcap_ab,
            disjoint_left.mpr fun z hza hzG => hhit_a ⟨z, hzG, hza⟩⟩
      obtain ⟨Δ_e, Δ_o, hΔ_e, hΔ_o, hb_e, hcup_eo, hcap_eo, hdis_eG₂⟩ := hex_Δe
      have hcle_eq : closure e = e ∪ {u} := by
        ext z
        constructor
        · intro hz
          by_cases hzV : z ∈ ΓZ.V
          · exact Or.inr (hcap_e.subset ⟨hz, hzV⟩)
          · exact Or.inl ((GM09.closure_edge_diff_V_eq ΓZ he).subset ⟨hz, hzV⟩)
        · rintro (hze' | rfl)
          · exact subset_closure hze'
          · exact (hcap_e.symm.subset rfl).1
      have hdis_intB₁_bde : Disjoint (discInt B₁) (discBd Δ_e) := by
        rw [hb_e, hcle_eq, disjoint_union_right]
        exact ⟨hdis_e_B₁.symm.mono_left (discInt_subset B₁),
          disjoint_singleton_right.mpr fun hu_int => hu_int.2 hu_bd.1⟩
      by_cases hhit_int : (discInt B₁ ∩ Δ_e).Nonempty
      · have hB₁_sub_e : B₁ ⊆ Δ_e :=
          GM07.disc_subset_of_int_off_bd hman hB₁ hΔ_e hdis_intB₁_bde hhit_int
        refine habsorb_contradiction e he hnot_e_B₁ Δ_e hΔ_e hB₁_sub_e
          (subset_closure.trans (hb_e ▸ Surface.discBd_subset Δ_e)) hdis_eG₂ ?_ ?_
        · rw [hb_e, hcle_eq]
          rintro x ⟨hxe' | rfl, _, hxne⟩
          · exact absurd hxe' hxne
          · exact ⟨hu_mem.2, hu_bd.2⟩
        · exact ⟨u, ⟨hb_e ▸ hu_mem.1, hu_bd.2⟩, hu_mem.2⟩
      · have hint_sub_o : discInt B₁ ⊆ Δ_o := fun z hz =>
          (hcup_eo ▸ mem_univ z).resolve_left fun hze' => hhit_int ⟨z, hz, hze'⟩
        have hB₁_sub_o : B₁ ⊆ Δ_o :=
          hB₁.subset_closure_discInt.trans (closure_minimal hint_sub_o hΔ_o.isClosed)
        have hpin_e : Δ_e ∩ B₁ = {u} := by
          apply Subset.antisymm
          · intro z ⟨hze', hzB₁⟩
            have hzcle : z ∈ closure e := hcap_eo ▸ ⟨hze', hB₁_sub_o hzB₁⟩
            rcases hcle_eq ▸ hzcle with hze_mem | hzu
            · exact absurd hzB₁ (disjoint_left.mp hdis_e_B₁ hze_mem)
            · exact hzu
          · rintro _ rfl
            exact ⟨Surface.discBd_subset Δ_e (hb_e ▸ hu_mem.1), Surface.discBd_subset B₁ hu_bd.1⟩
        have hPin_Δe : IsPinchedDisc Δ_e :=
          ⟨e, he, u, ⟨hu_bd.1, hu_mem.2⟩, hdis_e_B₁, hΔ_e, hb_e, hcap_e, hdis_eG₂, hpin_e⟩
        obtain ⟨Δ', hΔ'M, hsub_Δ'⟩ := hsub_MFin Δ_e (hPinched_fin.mem_toFinset.mpr hPin_Δe)
        exact hz_ex_Uext (Or.inr (mem_biUnion hΔ'M
          (hsub_Δ' (Surface.discBd_subset Δ_e (hb_e ▸ subset_closure hze)))))
  -- Step 4: Attach a thin finger from `p₁ ∈ discBd B₁` to `w₀ ∈ (closure R \ B₁) ∩ ΓZ.V`.
  obtain ⟨w₀, ⟨hw₀_clR, hw₀_notB₁⟩, hw₀V⟩ := hex_w₀
  obtain ⟨Φ, hΦ⟩ := GM07.exists_isPolar_of_vertex hZ_cs ΓZ hw₀V
  have hembΦ : IsEmbedding Φ := (Φ.continuous.isClosedEmbedding hΦ.inj).isEmbedding
  have h0_open : IsOpen (Φ ⁻¹' B₁ᶜ) := hB₁.isClosed.isOpen_compl.preimage Φ.continuous
  have h0_mem : polarCentre ∈ Φ ⁻¹' B₁ᶜ := by
    change Φ polarCentre ∉ B₁
    rw [hΦ.centre]
    exact hw₀_notB₁
  obtain ⟨ε_p, hε_p, hball_p⟩ := Metric.isOpen_iff.mp h0_open polarCentre h0_mem
  have hball_nhds : Φ '' Metric.ball polarCentre ε_p ∈ 𝓝 w₀ := by
    obtain ⟨V_ind, hV_ind, heq_ind⟩ :=
      isOpen_induced_iff.mp (hembΦ.toHomeomorph.isOpenMap _ Metric.isOpen_ball)
    have himg_eq : Φ '' Metric.ball polarCentre ε_p = range Φ ∩ V_ind := by
      ext z
      constructor
      · rintro ⟨x, hx, rfl⟩
        have hx' : hembΦ.toHomeomorph x ∈ hembΦ.toHomeomorph '' Metric.ball polarCentre ε_p :=
          mem_image_of_mem _ hx
        rw [← heq_ind] at hx'
        exact ⟨mem_range_self x, hx'⟩
      · rintro ⟨⟨x, rfl⟩, hxV⟩
        have hx' : hembΦ.toHomeomorph x ∈ hembΦ.toHomeomorph '' Metric.ball polarCentre ε_p := by
          rw [← heq_ind]; exact hxV
        obtain ⟨y, hy, hxy⟩ := hx'
        exact ⟨y, hy, by rw [← hembΦ.toHomeomorph.injective hxy]⟩
    rw [himg_eq]
    have hw₀_V : w₀ ∈ V_ind := by
      have : polarCentre ∈ Metric.ball polarCentre ε_p := Metric.mem_ball_self hε_p
      have hw : Φ polarCentre ∈ Φ '' Metric.ball polarCentre ε_p := mem_image_of_mem Φ this
      rw [hΦ.centre, himg_eq] at hw
      exact hw.2
    exact Filter.inter_mem (mem_interior_iff_mem_nhds.mp hΦ.nhd) (hV_ind.mem_nhds hw₀_V)
  obtain ⟨z_p, ⟨hz_p_ball, hz_p_R⟩⟩ := mem_closure_iff_nhds.mp hw₀_clR _ hball_nhds
  obtain ⟨x_p, hx_p_ball, rfl⟩ := hz_p_ball
  have hx_p_ne : x_p ≠ polarCentre := fun h => by
    subst h
    rw [hΦ.centre] at hz_p_R
    exact hR_sub_Ω hz_p_R (Or.inr (ΓZ.V_subset_U hw₀V))
  let ray_w : unitInterval → cap.Z := fun t => Φ (discScale t x_p)
  have hray_cont : Continuous ray_w :=
    Φ.continuous.comp (continuous_discScale.comp (continuous_id.prodMk continuous_const))
  have hray_0 : ray_w 0 = w₀ := by change Φ (discScale 0 x_p) = w₀; rw [discScale_zero, hΦ.centre]
  have hray_1 : ray_w 1 = Φ x_p := by change Φ (discScale 1 x_p) = Φ x_p; rw [discScale_one]
  have hray_pos_Ω : ∀ t : unitInterval, 0 < t → ray_w t ∈ Ω := by
    intro t ht
    have hlt_ε : dist (discScale t x_p) polarCentre < ε_p := by
      have hx_norm : ‖x_p.1‖ < ε_p := by
        simpa [polarCentre, Subtype.dist_eq, dist_zero_right] using hx_p_ball
      have ht_le : (t : ℝ) ≤ 1 := t.2.2
      have ht_nn : 0 ≤ (t : ℝ) := t.2.1
      change ‖(t : ℝ) • x_p.1 - 0‖ < ε_p
      rw [sub_zero, norm_smul, Real.norm_of_nonneg ht_nn]
      calc (t : ℝ) * ‖x_p.1‖ ≤ 1 * ‖x_p.1‖ :=
             mul_le_mul_of_nonneg_right ht_le (norm_nonneg _)
        _ = ‖x_p.1‖ := one_mul _
        _ < ε_p := hx_norm
    have hnotB₁ : ray_w t ∉ B₁ := hball_p hlt_ε
    obtain ⟨a_at, ha_at, hx_at, hsc_at⟩ := hΦ.ray x_p hx_p_ne t ht
    have hnotU : ray_w t ∉ ΓZ.U := by
      rcases ha_at with (⟨v, hv, rfl⟩ | haE) | haR
      · exact absurd (ΓZ.V_subset_U (hx_at ▸ hv)) (fun h => hR_sub_Ω hz_p_R (Or.inr h))
      · exact absurd (haE.2.1 hx_at).1 (fun h => hR_sub_Ω hz_p_R (Or.inr h))
      · exact GM11.region_subset haR hsc_at
    exact fun h => h.elim hnotB₁ hnotU
  have hray_pos_R : ray_w '' Ioi 0 ⊆ R := by
    have hIoi_pc : IsPreconnected (Ioi (0 : unitInterval)) := by
      have hmap : Ioi (0 : unitInterval) = projIcc 0 1 zero_le_one '' Ioc (0 : ℝ) 1 := by
        ext t
        constructor
        · intro ht
          exact ⟨t.1, ⟨ht, t.2.2⟩, projIcc_of_mem zero_le_one t.2⟩
        · rintro ⟨x, ⟨hx0, hx1⟩, rfl⟩
          change (0 : ℝ) < projIcc 0 1 zero_le_one x
          rwa [projIcc_of_mem zero_le_one ⟨hx0.le, hx1⟩]
      rw [hmap]
      exact (convex_Ioc 0 1).isPreconnected.image _ continuous_projIcc.continuousOn
    have hpc_ray : IsPreconnected (ray_w '' Ioi 0) := hIoi_pc.image _ hray_cont.continuousOn
    have h1_mem : Φ x_p ∈ ray_w '' Ioi 0 := ⟨1, zero_lt_one, hray_1⟩
    have hsub_Ω : ray_w '' Ioi 0 ⊆ Ω := by rintro _ ⟨t, ht, rfl⟩; exact hray_pos_Ω t ht
    have := hpc_ray.subset_connectedComponentIn h1_mem hsub_Ω
    rwa [← connectedComponentIn_eq hz_p_R] at this
  have hj_p₁_q₀ : JoinedIn (R ∪ {p₁, w₀}) p₁ q₀ := by
    obtain ⟨f_r, hf_r0, hf_r1⟩ := hL_rad_line
    refine ⟨⟨⟨fun t => (f_r t).1, continuous_subtype_val.comp f_r.continuous⟩, hf_r0, hf_r1⟩,
      fun t => ?_⟩
    by_cases htp : (f_r t).1 = p₁
    · exact Or.inr (Or.inl htp)
    · exact Or.inl (hL_rad_diff_R ⟨(f_r t).2, htp⟩)
  have hj_q₀_xp : JoinedIn (R ∪ {p₁, w₀}) q₀ (Φ x_p) :=
    (hR_pc.joinedIn q₀ hq₀R (Φ x_p) hz_p_R).mono subset_union_left
  have hj_w₀_xp : JoinedIn (R ∪ {p₁, w₀}) w₀ (Φ x_p) := by
    refine ⟨⟨⟨ray_w, hray_cont⟩, hray_0, hray_1⟩, fun t => ?_⟩
    rcases eq_or_lt_of_le t.2.1 with h0 | ht_pos
    · have ht0 : t = 0 := Subtype.ext h0.symm
      exact Or.inr (Or.inr (ht0 ▸ hray_0))
    · exact Or.inl (hray_pos_R ⟨t, ht_pos, rfl⟩)
  have hj_p₁_w₀ : JoinedIn (R ∪ {p₁, w₀}) p₁ w₀ := (hj_p₁_q₀.trans hj_q₀_xp).trans hj_w₀_xp.symm
  have hp₁_ne_w₀ : p₁ ≠ w₀ := fun h => hw₀_notB₁ (h ▸ hp₁B₁)
  obtain ⟨L_f, hL_f_sub, hL_f_line⟩ :=
    ((GM07.joinedIn_iff_eq_or_exists_isLineWithEnds (Z := R ∪ {p₁, w₀})
      (Or.inr (Or.inl rfl)) (Or.inr (Or.inr rfl))).mp hj_p₁_w₀).resolve_left hp₁_ne_w₀
  let Z_lens : Set cap.Z := B₁ ∪ ΓZ.U ∪ G₂
  have hZ_lens_cl : IsClosed Z_lens := (hB₁.isClosed.union ΓZ.isClosed_U).union hG₂.isClosed
  have hL_f_Zlens : L_f ∩ Z_lens ⊆ {p₁, w₀} := by
    rintro z ⟨hzL, (hzB | hzU) | hzG⟩
    · rcases hL_f_sub hzL with hzR | rfl | rfl
      · exact absurd hzB (fun h => hR_sub_Ω hzR (Or.inl h))
      · exact Or.inl rfl
      · exact absurd hzB hw₀_notB₁
    · rcases hL_f_sub hzL with hzR | rfl | rfl
      · exact absurd hzU (fun h => hR_sub_Ω hzR (Or.inr h))
      · exact absurd hzU (fun h => hp₁W₀ (Or.inl (Or.inr h)))
      · exact Or.inr rfl
    · rcases hL_f_sub hzL with hzR | rfl | rfl
      · exact absurd hzG (disjoint_left.mp hdisRG₂ hzR)
      · exact absurd hzG (fun h => hp₁W₀ (Or.inl (Or.inl h)))
      · exact Or.inr rfl
  obtain ⟨Ln, _, _, hLn, _, hLn_Zlens, hp₁_bdLn, hw₀_bdLn, _⟩ :=
    exists_edge_lens hZ_cs hL_f_line hp₁_ne_w₀ hZ_lens_cl hL_f_Zlens
  have hB₁_Ln : B₁ ∩ Ln = {p₁} := by
    apply Subset.antisymm
    · rintro z ⟨hzB₁, hzLn⟩
      rcases hLn_Zlens ⟨hzLn, Or.inl (Or.inl hzB₁)⟩ with rfl | rfl
      · rfl
      · exact absurd hzB₁ hw₀_notB₁
    · rintro _ rfl
      exact ⟨hp₁B₁, Surface.discBd_subset Ln hp₁_bdLn⟩
  obtain ⟨B₂, hB₂, hB₁Ln_B₂, hB₂_cov, _, hkeep_B₂, hbdB₂_cov⟩ :=
    GM07.exists_join hZ_cs hB₁ hLn hB₁_Ln hp₁Bd hp₁_bdLn hW₀_open hp₁W₀
  have hB₂_G₂_sub : B₂ ∩ G₂ ⊆ {w₀} := by
    rintro z ⟨hzB₂, hzG₂⟩
    rcases hB₂_cov hzB₂ with (hzB₁ | hzLn) | hzW
    · exact absurd hzG₂ (disjoint_left.mp hdisB₁G₂ hzB₁)
    · rcases hLn_Zlens ⟨hzLn, Or.inr hzG₂⟩ with rfl | rfl
      · exact absurd hzG₂ (fun h => hp₁W₀ (Or.inl (Or.inl h)))
      · rfl
    · exact absurd (Or.inl (Or.inl hzG₂)) hzW
  have hdis_B₂_intG₂ : Disjoint B₂ (discInt G₂) := by
    refine disjoint_left.mpr fun z hzB₂ hzInt => ?_
    have hzw : z = w₀ := hB₂_G₂_sub ⟨hzB₂, hzInt.1⟩
    subst hzw
    exact hzInt.2 (hbG₂ ▸ hcapG ▸ ⟨(hUsubZ (ΓZ.V_subset_U hw₀V)).1, hzInt.1⟩)
  have hw₀_bdB₂ : w₀ ∈ discBd B₂ :=
    hkeep_B₂ ⟨Or.inr hw₀_bdLn, fun hW => hW (Or.inl (Or.inr (ΓZ.V_subset_U hw₀V)))⟩
  have hy₀_bdB₂ : y₀ ∈ discBd B₂ :=
    hkeep_B₂ ⟨Or.inl hy₀Bd₁, fun hW => hW (Or.inr rfl)⟩
  have hbdB₂_U : discBd B₂ ∩ ΓZ.U ⊆ (ΓZ.V ∩ discBd E₁) ∪ {w₀} := by
    rintro z ⟨hzBd, hzU⟩
    rcases hbdB₂_cov hzBd with (hzBd₁ | hzBdLn) | hzW
    · exact Or.inl (hbdB₁U ⟨hzBd₁, hzU⟩)
    · rcases hLn_Zlens ⟨Surface.discBd_subset Ln hzBdLn, Or.inl (Or.inr hzU)⟩ with rfl | rfl
      · exact absurd hzU (fun h => hp₁W₀ (Or.inl (Or.inr h)))
      · exact Or.inr rfl
    · exact absurd (Or.inl (Or.inr hzU)) hzW
  obtain ⟨hH₂, _, _, hF₁''_sub, hlam₂⟩ :=
    pull_hoop_of_disc_in_cap σ cap hle hB₂ (hE₁B₁.trans (subset_union_left.trans hB₁Ln_B₂))
      hdis_B₂_intG₂
  let F₁'' : Set S := cap.j ⁻¹' discBd B₂
  have hNF₁'' : σ.Γ.IsNormal F₁'' := by
    rintro x ⟨hxF'', hxU⟩
    rcases hbdB₂_U ⟨hxF'', hUZ ▸ mem_image_of_mem _ hxU⟩ with ⟨hzV, _⟩ | hzw
    · obtain ⟨y, hyV, heq⟩ := hVZ ▸ hzV
      exact cap.inj heq ▸ hyV
    · obtain ⟨v₀, hv₀V, hv₀_eq⟩ := hVZ ▸ hw₀V
      exact cap.inj (hzw.trans hv₀_eq.symm) ▸ hv₀V
  obtain ⟨v₀, hv₀V, hv₀_eq⟩ := hVZ ▸ hw₀V
  have hv₀_F₁'' : v₀ ∈ F₁'' := by change cap.j v₀ ∈ discBd B₂; rw [hv₀_eq]; exact hw₀_bdB₂
  have hv₀_notF₁ : v₀ ∉ σ.F₁ := fun hF₁ =>
    hw₀_notB₁ (hE₁B₁ (Surface.discBd_subset E₁ (hbE₁ ▸ hv₀_eq ▸ mem_image_of_mem _ hF₁)))
  have hF₁''_HV : F₁'' ∩ σ.Γ.V ⊆ σ.F₁ ∪ {v₀} := by
    rintro x ⟨hxF'', hxV⟩
    rcases hbdB₂_U ⟨hxF'', hUZ ▸ mem_image_of_mem _ (σ.Γ.V_subset_U hxV)⟩ with ⟨_, hzBdE₁⟩ | hzw
    · obtain ⟨y, hyF₁, heq⟩ := hbE₁ ▸ hzBdE₁
      exact Or.inl (cap.inj heq ▸ hyF₁)
    · exact Or.inr (cap.inj (hzw.trans hv₀_eq.symm))
  refine ⟨F₁'', hlam₂, hNF₁'', hF₁''_sub, ⟨v₀, hv₀V, hv₀_F₁'', hv₀_notF₁, hF₁''_HV⟩, ?_⟩
  rcases Nat.eq_zero_or_pos s with rfl | hs_pos
  · exact Nat.zero_le _
  · have hw₀_notG₂ : w₀ ∉ G₂ := fun hw₀G₂ => by
      have hv₀F₂ : v₀ ∈ σ.F₂ := by
        have hw₀_img : w₀ ∈ cap.j '' σ.F₂ :=
          hcapG ▸ ⟨(hUsubZ (ΓZ.V_subset_U hw₀V)).1, hw₀G₂⟩
        obtain ⟨y, hyF₂, heq⟩ := hw₀_img
        exact cap.inj (hv₀_eq.trans heq.symm) ▸ hyF₂
      have hLf_range : L_f ⊆ range cap.j := by
        obtain ⟨_, _, _, _, _, _, hD₁E', _⟩ := cap.disc₁_disc₂_spec σ.isCylinder.1 σ.isHoop_F₁
        obtain ⟨_, _, _, _, _, _, _, hD₂G'⟩ := cap.disc₁_disc₂_spec σ.isCylinder.1 σ.isHoop_F₂
        have hD₁B₁ : cap.D₁ ⊆ B₁ := hD₁E'.trans hE₁B₁
        refine cap.subset_range_of_disjoint_discInts
          (disjoint_left.mpr fun z hzL hzInt => ?_)
          (disjoint_left.mpr fun z hzL hzInt => ?_)
        · have hzIntB₁ := discInt_mono hman cap.isClosedDisc_D₁ hD₁B₁ hzInt
          rcases hL_f_sub hzL with hzR | rfl | rfl
          · exact hR_sub_Ω hzR (Or.inl hzIntB₁.1)
          · exact hzIntB₁.2 hp₁Bd
          · exact hw₀_notB₁ hzIntB₁.1
        · have hzIntG₂ := discInt_mono hman cap.isClosedDisc_D₂ hD₂G' hzInt
          rcases hL_f_sub hzL with hzR | rfl | rfl
          · exact disjoint_left.mp hdisRG₂ hzR hzIntG₂.1
          · exact hp₁W₀ (Or.inl (Or.inl hzIntG₂.1))
          · exact hzIntG₂.2 (hbG₂ ▸ hv₀_eq ▸ mem_image_of_mem _ hv₀F₂)
      obtain ⟨u₁_S, hu₁_eq⟩ := hLf_range hL_f_line.left_mem
      have hu₁_H₁ : u₁_S ∈ H₁ := by change cap.j u₁_S ∈ discBd B₁; rw [hu₁_eq]; exact hp₁Bd
      let I_f : Set S := cap.j ⁻¹' L_f
      have hL_f_line' : IsLineWithEnds L_f (cap.j u₁_S) (cap.j v₀) := by
        rw [hu₁_eq, hv₀_eq]; exact hL_f_line
      have hI_f_line : IsLineWithEnds I_f u₁_S v₀ :=
        GM07.pull_line cap.isClosedEmbedding.isEmbedding hL_f_line' hLf_range
      have hI_f_U : I_f ∩ σ.Γ.U ⊆ {v₀} := by
        rintro x ⟨hxI, hxU⟩
        rcases hL_f_Zlens ⟨hxI, Or.inl (Or.inr (hUZ ▸ mem_image_of_mem _ hxU))⟩ with hjp | hjw
        · exact absurd (hUZ ▸ mem_image_of_mem _ hxU) (fun h => hp₁W₀ (Or.inl (Or.inr (hjp ▸ h))))
        · exact cap.inj (hjw.trans hv₀_eq.symm)
      have hNI_f : (σ.subTube hlamH₁ hNH₁ σ.isNormal_F₂).Γ.IsNormal I_f := by
        rintro x ⟨hxI, hxU⟩
        have hx_sub := interSet_U_subset_of_isClosed σ.Γ (isClosed_cylinderBetween hlamH₁) hxU
        have hxv₀ : x = v₀ := hI_f_U ⟨hxI, hx_sub.1⟩
        exact (interSet_V_of_isClosed σ.Γ (isClosed_cylinderBetween hlamH₁)).symm.subset
          ⟨hxv₀ ▸ hv₀V, hx_sub.2⟩
      have hIV_sub : I_f ∩ (σ.subTube hlamH₁ hNH₁ σ.isNormal_F₂).Γ.V ⊆ {v₀} := by
        rintro x ⟨hxI, hxV⟩
        have hxV' := (interSet_V_of_isClosed σ.Γ (isClosed_cylinderBetween hlamH₁)).subset hxV
        exact hI_f_U ⟨hxI, σ.Γ.V_subset_U hxV'.1⟩
      have hcard_le : (I_f ∩ (σ.subTube hlamH₁ hNH₁ σ.isNormal_F₂).Γ.V).ncard ≤ 1 :=
        (ncard_le_ncard hIV_sub (finite_singleton v₀)).trans (by simp)
      have hge := ((σ.subTube hlamH₁ hNH₁ σ.isNormal_F₂).le_length_iff.mp hlen_H₁)
        I_f u₁_S v₀ hI_f_line hu₁_H₁ hv₀F₂ hNI_f
      omega
    have hdis_F₁''_F₂ : Disjoint F₁'' σ.F₂ := disjoint_left.mpr fun x hxF'' hxF₂ => by
      have hjxG₂ : cap.j x ∈ G₂ := Surface.discBd_subset G₂ (hbG₂ ▸ mem_image_of_mem _ hxF₂)
      have hjx_w₀ : cap.j x = w₀ := hB₂_G₂_sub ⟨Surface.discBd_subset B₂ hxF'', hjxG₂⟩
      exact hw₀_notG₂ (hjx_w₀ ▸ hjxG₂)
    have hx₀_F₁'' : x₀_S ∈ F₁'' := by change cap.j x₀_S ∈ discBd B₂; rw [hy₀_eq]; exact hy₀_bdB₂
    have hlen_bound := length_subTube_add_ge_length σ hlam₂ hNF₁'' hF₁''_sub hdis_F₁''_F₂
      ⟨x₀_S, hx₀_F₁'', hx₀F₁⟩ (finite_singleton v₀) hF₁''_HV
    simp only [ncard_singleton] at hlen_bound
    omega

/-- The inward hoop step in VIII (16.2), page 283: a two-unit length
allowance gives an inward hoop containing a new drawing vertex. -/
theorem Tube.exists_hoop_step_inward {S : Type w} [TopologicalSpace S] (σ : Tube S) {s : ℕ}
    (hs : s + 2 ≤ σ.length) :
    ∃ (K : Set S) (hlam : AreLaminarHoops K σ.F₂) (hN : σ.Γ.IsNormal K),
      K ⊆ cylinderBetween σ.F₁ σ.F₂ ∧
      (∃ v ∈ σ.Γ.V, v ∈ K ∧ v ∉ σ.F₁) ∧
      s ≤ (σ.subTube hlam hN σ.isNormal_F₂).length := by
  obtain ⟨K, hlam, hN, hsub, ⟨v, hvV, hvK, hvF, _⟩, hlen⟩ :=
    σ.exists_hoop_step_inward_refined hs
  exact ⟨K, hlam, hN, hsub, ⟨v, hvV, hvK, hvF⟩, hlen⟩

end GraphMinor.GM08
