module

public import GraphMinor.GHR18.ArcTypeHelpers

/-!
# Arc parallelism from equal boundary-relative cohomology and `w₁` parity

This file proves the Stage 1 master arc-parallelism theorem `parallel_of_cocycle_eq`:

Given a connected compact surface `S` with atlas `AS`, and two proper `I`-arcs `F, F' ⊆ S` with the
same distinct boundary endpoints `s, t ∈ bd S`, if:
1. `F` is non-separating (`IsPreconnected (Fᶜ : Set S)`),
2. `BdCohRel s t (arcCocycle F') (arcCocycle F)`, and
3. `cocInt (w1 AS) γ' = cocInt (w1 AS) γ` for continuous arcs `γ, γ'` along `F, F'` from `s` to `t`,

then there exists a boundary-fixing homeomorphism `β : S ≃ₜ S` with `β '' F = F'` and
`∀ x ∈ bd S, β x = x`.
-/

@[expose] public section

namespace GraphMinor.GHR18

open Set Topology Function Metric GraphMinor.Surface

universe u

section Helpers

private theorem bool_eq_xor_of_not_eq_beq {fl d d' : Bool} (h : (!fl) = (d == d')) :
    d' = xor d fl := by
  cases fl <;> cases d <;> cases d' <;> simp at h ⊢

/-- Common bundle of cut-surface presentation and untouched-cuff data shared by the three cases. -/
private structure CutSetup {S Y Y' : Type u} [TopologicalSpace S] [TopologicalSpace Y] [T2Space Y]
    [TopologicalSpace Y'] [T2Space Y']
    (ψ : Y → S) (ψ' : Y' → S) (F F' : Set S) (s t : S)
    (X X' : Set Y) (X₂ X₂' : Set Y') (a a' : ℝ → S) (ξ η : ℝ → Y) (ξ' η' : ℝ → Y') where
  a₀ : ℕ
  b₀ : ℕ
  c₀ : ℕ
  f : ℕ × ℂ → Y
  f' : ℕ × ℂ → Y'
  hf : Presents (sW (ew a₀ b₀ c₀)) f
  hf' : Presents (sW (ew a₀ b₀ c₀)) f'
  AY : SurfAtlas Y
  AY' : SurfAtlas Y'
  i_ξ : Fin c₀
  i_η : Fin c₀
  j_ξ0 : Fin c₀
  j_η0 : Fin c₀
  hiξ_eq : holeC a₀ b₀ c₀ f i_ξ.1 = connectedComponentIn (bd Y) (ξ 0)
  hiη_eq : holeC a₀ b₀ c₀ f i_η.1 = connectedComponentIn (bd Y) (η 0)
  hjξ0_eq : holeC a₀ b₀ c₀ f' j_ξ0.1 = connectedComponentIn (bd Y') (ξ' 0)
  hjη0_eq : holeC a₀ b₀ c₀ f' j_η0.1 = connectedComponentIn (bd Y') (η' 0)
  hXC : X ⊆ holeC a₀ b₀ c₀ f i_ξ.1
  hX'C : X' ⊆ holeC a₀ b₀ c₀ f i_η.1
  hX2C : X₂ ⊆ holeC a₀ b₀ c₀ f' j_ξ0.1
  hX2'C : X₂' ⊆ holeC a₀ b₀ c₀ f' j_η0.1

variable {S Y Y' : Type u} [TopologicalSpace S] [TopologicalSpace Y] [T2Space Y]
  [TopologicalSpace Y'] [T2Space Y']

private theorem untouched_cuff_properties (hS : IsSurface S) (hY : IsSurface Y)
    {ψ : Y → S} {F : Set S} {s t : S} (hψ : IsCutting ψ F) (hF : IsClosed F) (hb : F ∩ bd S = {s, t})
    {X X' : Set Y} (hP : LiftPair ψ F s t X X')
    {a₀ b₀ c₀ : ℕ} {f : ℕ × ℂ → Y} (hf : Presents (sW (ew a₀ b₀ c₀)) f)
    {i_ξ i_η : Fin c₀} (hXC : X ⊆ holeC a₀ b₀ c₀ f i_ξ.1) (hX'C : X' ⊆ holeC a₀ b₀ c₀ f i_η.1)
    {i : Fin c₀} (h1 : i ≠ i_ξ) (h2 : i ≠ i_η) :
    Disjoint (holeC a₀ b₀ c₀ f i.1) (ψ ⁻¹' F) ∧
    ψ '' holeC a₀ b₀ c₀ f i.1 ∈ cuffs S ∧
    s ∉ ψ '' holeC a₀ b₀ c₀ f i.1 ∧
    t ∉ ψ '' holeC a₀ b₀ c₀ f i.1 ∧
    ψ ⁻¹' (ψ '' holeC a₀ b₀ c₀ f i.1) = holeC a₀ b₀ c₀ f i.1 := by
  obtain ⟨_, _, _, _, _, _, _, hun, -⟩ := id hP
  have hC : holeC a₀ b₀ c₀ f i.1 ∈ cuffs Y := cuffs_eq_holeC hf ▸ ⟨i.1, i.isLt, rfl⟩
  have hdis : Disjoint (holeC a₀ b₀ c₀ f i.1) (ψ ⁻¹' F) := by
    rw [Set.disjoint_left]; intro y hyi hyF
    rcases (hun.symm ▸ hyF : y ∈ X ∪ X') with hyX | hyX'
    · exact Set.disjoint_left.mp (disjoint_holeC hf i.isLt i_ξ.isLt (fun h => h1 (Fin.ext h))) hyi (hXC hyX)
    · exact Set.disjoint_left.mp (disjoint_holeC hf i.isLt i_η.isLt (fun h => h2 (Fin.ext h))) hyi (hX'C hyX')
  exact ⟨hdis, untouched_cuff_image hY hS hψ hF hb hC hdis⟩

private theorem untouched_dir_pair (hS : IsSurface S) (hY : IsSurface Y) (hY' : IsSurface Y')
    (AS : SurfAtlas S) (AY : SurfAtlas Y) (AY' : SurfAtlas Y')
    {ψ : Y → S} {ψ' : Y' → S} {F F' : Set S} (hψ : IsCutting ψ F) (hψ' : IsCutting ψ' F')
    (hF : IsClosed F) (hF' : IsClosed F')
    {a₀ b₀ c₀ : ℕ} {f : ℕ × ℂ → Y} {f' : ℕ × ℂ → Y'}
    (hf : Presents (sW (ew a₀ b₀ c₀)) f) (hf' : Presents (sW (ew a₀ b₀ c₀)) f')
    {i j : Fin c₀}
    (hdisY : Disjoint (holeC a₀ b₀ c₀ f i.1) (ψ ⁻¹' F))
    (hdisY' : Disjoint (holeC a₀ b₀ c₀ f' j.1) (ψ' ⁻¹' F'))
    (hD : ψ '' holeC a₀ b₀ c₀ f i.1 ∈ cuffs S)
    (him_eq : ψ' '' holeC a₀ b₀ c₀ f' j.1 = ψ '' holeC a₀ b₀ c₀ f i.1) :
    ∃ (dirY dirY' : Bool),
      ∀ (φS : Circle ≃ₜ (ψ '' holeC a₀ b₀ c₀ f i.1)),
        ∃ (v₀ v₀' δ₁ δ₂ : ℝ) (m₁ m₂ : ℝ → ℝ) (d₁ d₂ : Bool),
          0 < δ₁ ∧ 0 < δ₂ ∧
          ψ (holeParam hf i.isLt (ee v₀)).1 = ψ' (holeParam hf' j.isLt (ee v₀')).1 ∧
          ContinuousOn m₁ (Icc (-δ₁) δ₁) ∧ ContinuousOn m₂ (Icc (-δ₂) δ₂) ∧
          (if d₁ then StrictMonoOn m₁ (Icc (-δ₁) δ₁) else StrictAntiOn m₁ (Icc (-δ₁) δ₁)) ∧
          (if d₂ then StrictMonoOn m₂ (Icc (-δ₂) δ₂) else StrictAntiOn m₂ (Icc (-δ₂) δ₂)) ∧
          (∀ r ∈ Icc (-δ₁) δ₁, ψ (holeParam hf i.isLt (ee (v₀ + r))).1 = (φS (ee (m₁ r))).1) ∧
          (∀ r ∈ Icc (-δ₂) δ₂, ψ' (holeParam hf' j.isLt (ee (v₀' + r))).1 = (φS (ee (m₂ r))).1) ∧
          (d₁ == d₂) = (dirY == dirY') := by
  have hCi_bd : holeC a₀ b₀ c₀ f i.1 ⊆ bd Y := by
    obtain ⟨y, -, hy⟩ := (cuffs_eq_holeC hf ▸ ⟨i.1, i.isLt, rfl⟩ : holeC a₀ b₀ c₀ f i.1 ∈ cuffs Y)
    rw [← hy]; exact connectedComponentIn_subset _ _
  have hCj_bd : holeC a₀ b₀ c₀ f' j.1 ⊆ bd Y' := by
    obtain ⟨y, -, hy⟩ := (cuffs_eq_holeC hf' ▸ ⟨j.1, j.isLt, rfl⟩ : holeC a₀ b₀ c₀ f' j.1 ∈ cuffs Y')
    rw [← hy]; exact connectedComponentIn_subset _ _
  obtain ⟨φS0⟩ := (cuff_statement.{u} S hS).2.2 _ hD
  let x₀ : S := ψ (holeParam hf i.isLt (ee 0)).1
  have hx0D : x₀ ∈ ψ '' holeC a₀ b₀ c₀ f i.1 := ⟨(holeParam hf i.isLt (ee 0)).1, (holeParam hf i.isLt _).2, rfl⟩
  have hx0F : x₀ ∉ F := Set.disjoint_left.mp hdisY (holeParam hf i.isLt _).2
  obtain ⟨y₀', hy0'C, hy0'ψ⟩ := him_eq.symm.subset hx0D
  obtain ⟨v₀', -, hv0'e⟩ := exists_param ((holeParam hf' j.isLt).symm ⟨y₀', hy0'C⟩)
  have hv0'y : (holeParam hf' j.isLt (ee v₀')).1 = y₀' := by rw [hv0'e]; simp
  have hx0F' : ψ' (holeParam hf' j.isLt (ee v₀')).1 ∉ F' := Set.disjoint_left.mp hdisY' (holeParam hf' j.isLt _).2
  obtain ⟨δ0, m0, d0, hδ0, _, hm0c, hm0d, hm0e, hsig0⟩ :=
    exists_cuff_local_dir hY hS hψ hF AY AS hCi_bd hD (holeParam hf i.isLt) φS0 hx0D hx0F
  obtain ⟨δ0', m0', d0', hδ0', _, hm0'c, hm0'd, hm0'e, hsig0'⟩ :=
    exists_cuff_local_dir hY' hS hψ' hF' AY' AS hCj_bd hD (holeParam hf' j.isLt) φS0 (by rw [hv0'y, hy0'ψ]; exact hx0D) hx0F'
  refine ⟨d0, d0', fun φS => ?_⟩
  obtain ⟨δ1, m1, d1, hδ1, _, hm1c, hm1d, hm1e, hsig1⟩ :=
    exists_cuff_local_dir hY hS hψ hF AY AS hCi_bd hD (holeParam hf i.isLt) φS hx0D hx0F
  obtain ⟨δ2, m2, d2, hδ2, _, hm2c, hm2d, hm2e, hsig2⟩ :=
    exists_cuff_local_dir hY' hS hψ' hF' AY' AS hCj_bd hD (holeParam hf' j.isLt) φS (by rw [hv0'y, hy0'ψ]; exact hx0D) hx0F'
  have hψeq : ψ' (holeParam hf' j.isLt (ee v₀')).1 = x₀ := by rw [hv0'y, hy0'ψ]
  rw [hψeq] at hsig0' hsig2
  have hdiff : (if d1 then (0 : ZMod 2) else 1) - (if d2 then 0 else 1) =
      (if d0 then (0 : ZMod 2) else 1) - (if d0' then 0 else 1) := by
    have hsub1 : (if d1 then (0 : ZMod 2) else 1) - (if d0 then 0 else 1) = cuffSign AS φS x₀ - cuffSign AS φS0 x₀ := by
      linear_combination hsig0 - hsig1
    have hsub2 : (if d2 then (0 : ZMod 2) else 1) - (if d0' then 0 else 1) = cuffSign AS φS x₀ - cuffSign AS φS0 x₀ := by
      linear_combination hsig0' - hsig2
    linear_combination hsub1 - hsub2
  exact ⟨0, v₀', δ1, δ2, m1, m2, d1, d2, hδ1, hδ2, hψeq.symm, hm1c, hm2c, hm1d, hm2d, hm1e, hm2e,
    bool_beq_of_zmod2_sub_eq hdiff⟩

private theorem untouched_cuff_null (hS : IsSurface S) (hY : IsSurface Y) (hY' : IsSurface Y')
    (AS : SurfAtlas S) (AY : SurfAtlas Y) (AY' : SurfAtlas Y')
    {ψ : Y → S} {ψ' : Y' → S} {F F' : Set S} (hψ : IsCutting ψ F) (hψ' : IsCutting ψ' F')
    (hF : IsClosed F) (hF' : IsClosed F')
    {a₀ b₀ c₀ : ℕ} {f : ℕ × ℂ → Y} {f' : ℕ × ℂ → Y'}
    (hf : Presents (sW (ew a₀ b₀ c₀)) f) (hf' : Presents (sW (ew a₀ b₀ c₀)) f')
    {i j : Fin c₀}
    (hdisY : Disjoint (holeC a₀ b₀ c₀ f i.1) (ψ ⁻¹' F))
    (hdisY' : Disjoint (holeC a₀ b₀ c₀ f' j.1) (ψ' ⁻¹' F'))
    (hD : ψ '' holeC a₀ b₀ c₀ f i.1 ∈ cuffs S)
    (hpreY' : ψ' ⁻¹' (ψ' '' holeC a₀ b₀ c₀ f' j.1) = holeC a₀ b₀ c₀ f' j.1)
    (him_eq : ψ' '' holeC a₀ b₀ c₀ f' j.1 = ψ '' holeC a₀ b₀ c₀ f i.1)
    (H : Y ≃ₜ Y') (fl : Bool)
    (hH_act : ∀ z : Circle, H (holeParam hf i.isLt z).1 = (holeParam hf' j.isLt (if fl then z⁻¹ else z)).1)
    (hfl_ok : ∀ (φS : Circle ≃ₜ (ψ '' holeC a₀ b₀ c₀ f i.1)) (v₀ v₀' δ₁ δ₂ : ℝ) (m₁ m₂ : ℝ → ℝ) (d₁ d₂ : Bool),
      0 < δ₁ → 0 < δ₂ → ψ (holeParam hf i.isLt (ee v₀)).1 = ψ' (holeParam hf' j.isLt (ee v₀')).1 →
      ContinuousOn m₁ (Icc (-δ₁) δ₁) → ContinuousOn m₂ (Icc (-δ₂) δ₂) →
      (if d₁ then StrictMonoOn m₁ (Icc (-δ₁) δ₁) else StrictAntiOn m₁ (Icc (-δ₁) δ₁)) →
      (if d₂ then StrictMonoOn m₂ (Icc (-δ₂) δ₂) else StrictAntiOn m₂ (Icc (-δ₂) δ₂)) →
      (∀ r ∈ Icc (-δ₁) δ₁, ψ (holeParam hf i.isLt (ee (v₀ + r))).1 = (φS (ee (m₁ r))).1) →
      (∀ r ∈ Icc (-δ₂) δ₂, ψ' (holeParam hf' j.isLt (ee (v₀' + r))).1 = (φS (ee (m₂ r))).1) →
      (!fl) = (d₁ == d₂))
    (α : S ≃ₜ S) (hα : ∀ y, α (ψ y) = ψ' (H y)) (φS : Circle ≃ₜ (ψ '' holeC a₀ b₀ c₀ f i.1)) :
    ∃ h : Circle ≃ₜ Circle, PreservesCircleOrientation h ∧ ∀ z, α (φS z).1 = (φS (h z)).1 := by
  have hCi_bd : holeC a₀ b₀ c₀ f i.1 ⊆ bd Y := by
    obtain ⟨y, -, hy⟩ := (cuffs_eq_holeC hf ▸ ⟨i.1, i.isLt, rfl⟩ : holeC a₀ b₀ c₀ f i.1 ∈ cuffs Y)
    rw [← hy]; exact connectedComponentIn_subset _ _
  have hCj_bd : holeC a₀ b₀ c₀ f' j.1 ⊆ bd Y' := by
    obtain ⟨y, -, hy⟩ := (cuffs_eq_holeC hf' ▸ ⟨j.1, j.isLt, rfl⟩ : holeC a₀ b₀ c₀ f' j.1 ∈ cuffs Y')
    rw [← hy]; exact connectedComponentIn_subset _ _
  have hαD : ∀ x, x ∈ ψ '' holeC a₀ b₀ c₀ f i.1 ↔ α x ∈ ψ '' holeC a₀ b₀ c₀ f i.1 := fun x => by
    constructor
    · rintro ⟨y, hyC, rfl⟩
      rw [hα y, ← him_eq]
      obtain ⟨z, hz⟩ := (holeParam hf i.isLt).surjective ⟨y, hyC⟩
      rw [show y = (holeParam hf i.isLt z).1 from congrArg Subtype.val hz.symm, hH_act z]
      exact ⟨_, (holeParam hf' j.isLt _).2, rfl⟩
    · intro hαx
      obtain ⟨y, rfl⟩ := hψ.2.1 x
      rw [hα y, ← him_eq] at hαx
      have hHy : H y ∈ holeC a₀ b₀ c₀ f' j.1 := hpreY' ▸ hαx
      obtain ⟨z', hz'⟩ := (holeParam hf' j.isLt).surjective ⟨H y, hHy⟩
      let z : Circle := if fl then z'⁻¹ else z'
      have heq : H y = H (holeParam hf i.isLt z).1 := by
        rw [hH_act z, show (if fl then z⁻¹ else z) = z' by cases fl <;> simp [z]]
        exact congrArg Subtype.val hz'.symm
      rw [H.injective heq]; exact ⟨_, (holeParam hf i.isLt z).2, rfl⟩
  let x₀ : S := ψ (holeParam hf i.isLt (ee 0)).1
  have hx0D : x₀ ∈ ψ '' holeC a₀ b₀ c₀ f i.1 := ⟨(holeParam hf i.isLt (ee 0)).1, (holeParam hf i.isLt _).2, rfl⟩
  obtain ⟨y₀', hy0'C, hy0'ψ⟩ := him_eq.symm.subset hx0D
  obtain ⟨v₀', -, hv0'e⟩ := exists_param ((holeParam hf' j.isLt).symm ⟨y₀', hy0'C⟩)
  have hv0'y : (holeParam hf' j.isLt (ee v₀')).1 = y₀' := by rw [hv0'e]; simp
  obtain ⟨δ1, m1, d1, hδ1, _, hm1c, hm1d, hm1e, _⟩ :=
    exists_cuff_local_dir hY hS hψ hF AY AS hCi_bd hD (holeParam hf i.isLt) φS hx0D (Set.disjoint_left.mp hdisY (holeParam hf i.isLt _).2)
  obtain ⟨δ2, m2, d2, hδ2, _, hm2c, hm2d, hm2e, _⟩ :=
    exists_cuff_local_dir hY' hS hψ' hF' AY' AS hCj_bd hD (holeParam hf' j.isLt) φS (by rw [hv0'y, hy0'ψ]; exact hx0D) (Set.disjoint_left.mp hdisY' (holeParam hf' j.isLt _).2)
  have hfl_eq := hfl_ok φS 0 v₀' δ1 δ2 m1 m2 d1 d2 hδ1 hδ2 (by rw [hv0'y, hy0'ψ]) hm1c hm2c hm1d hm2d hm1e hm2e
  have hmem0 : ψ' (holeParam hf' j.isLt (ee 0)).1 ∈ ψ '' holeC a₀ b₀ c₀ f i.1 := by
    rw [← him_eq]; exact ⟨_, (holeParam hf' j.isLt _).2, rfl⟩
  obtain ⟨δ3, m3, d3, hδ3, _, hm3c, hm3d, hm3e, _⟩ :=
    exists_cuff_local_dir hY' hS hψ' hF' AY' AS hCj_bd hD (holeParam hf' j.isLt) φS hmem0 (Set.disjoint_left.mp hdisY' (holeParam hf' j.isLt _).2)
  have hd23 : d2 = d3 := local_dir_eq_on_untouched hψ' (holeParam hf' j.isLt) φS
    (fun z => ⟨by rw [← him_eq]; exact ⟨_, (holeParam hf' j.isLt z).2, rfl⟩, Set.disjoint_left.mp hdisY' (holeParam hf' j.isLt z).2⟩)
    hδ2 hδ3 hm2c hm3c hm2d hm3d hm2e hm3e
  let kH : Circle ≃ₜ Circle := if fl then Homeomorph.inv Circle else Homeomorph.refl Circle
  have hkH_or : if !fl then PreservesCircleOrientation kH
      else PreservesCircleOrientation ((Homeomorph.inv Circle).trans kH) := by
    cases fl <;> simp only [Bool.not_false, Bool.not_true, Bool.false_eq_true, ↓reduceIte, kH]
    · exact preservesCircleOrientation_refl
    · have : (Homeomorph.inv Circle).trans (Homeomorph.inv Circle) = Homeomorph.refl Circle :=
        Homeomorph.ext fun z => inv_inv z
      rw [this]; exact preservesCircleOrientation_refl
  have hkH_eq : ∀ z : Circle, H (holeParam hf i.isLt z).1 = (holeParam hf' j.isLt (kH z)).1 := fun z => by
    cases fl <;> simp only [Bool.false_eq_true, ↓reduceIte, kH] <;> exact hH_act z
  have hkH0 : kH (ee 0) = ee 0 := by cases fl <;> simp [kH, ee]
  exact preservesCircleOrientation_of_local_dirs hα hαD φS (holeParam hf i.isLt) (holeParam hf' j.isLt)
    (!fl) hkH_or hkH_eq hkH0 hδ1 hδ3 hm1c hm3c hm1d hm3d hm1e hm3e (by rw [← hd23]; exact hfl_eq)

end Helpers

/-! ### Case 1: Distinct cuffs `C_s ≠ C_t` -/

section CaseDiffCuff

variable {S Y Y' : Type u} [TopologicalSpace S] [TopologicalSpace Y] [T2Space Y]
  [TopologicalSpace Y'] [T2Space Y']

private theorem parallel_case_diff_cuff [ConnectedSpace S] [ConnectedSpace Y] [ConnectedSpace Y']
    (hS : IsSurface S) (hY : IsSurface Y) (hY' : IsSurface Y')
    {F F' : Set S} {s t : S} (hne : s ≠ t)
    (hb : F ∩ bd S = {s, t}) (hb' : F' ∩ bd S = {s, t})
    (hl : IsLineWithEnds F s t) (hl' : IsLineWithEnds F' s t)
    {ψ : Y → S} {ψ' : Y' → S} (hψ : IsCutting ψ F) (hψ' : IsCutting ψ' F')
    {X X' : Set Y} {X₂ X₂' : Set Y'}
    (hP : LiftPair ψ F s t X X') (hP' : LiftPair ψ' F' s t X₂ X₂')
    {a a' : ℝ → S} {ξ η : ℝ → Y} {ξ' η' : ℝ → Y'}
    (L : ArcLift ψ F a ξ η) (L' : ArcLift ψ' F' a' ξ' η')
    (ha0 : a 0 = s) (ha1 : a 1 = t) (ha'0 : a' 0 = s) (ha'1 : a' 1 = t)
    (himξ : ξ '' Icc 0 1 = X) (himη : η '' Icc 0 1 = X')
    (himξ' : ξ' '' Icc 0 1 = X₂) (himη' : η' '' Icc 0 1 = X₂')
    (hiξ : InjOn ξ (Icc 0 1)) (hiη : InjOn η (Icc 0 1))
    (hiξ' : InjOn ξ' (Icc 0 1)) (hiη' : InjOn η' (Icc 0 1))
    (AS : SurfAtlas S)
    (hrel : BdCohRel s t (arcCocycle hS hne hb' hl') (arcCocycle hS hne hb hl))
    (hw1 : cocInt (w1 AS) a' = cocInt (w1 AS) a)
    (hst : connectedComponentIn (bd S) s ≠ connectedComponentIn (bd S) t)
    (st : CutSetup ψ ψ' F F' s t X X' X₂ X₂' a a' ξ η ξ' η')
    (hi_eq : st.i_ξ = st.i_η) (hj_eq : st.j_ξ0 = st.j_η0)
    (π : Equiv.Perm (Fin st.c₀)) (hπ_cut : π st.i_ξ = st.j_ξ0)
    (hπ_unt : ∀ i : Fin st.c₀, i ≠ st.i_ξ → π i ≠ st.j_ξ0 ∧
      ψ' '' holeC st.a₀ st.b₀ st.c₀ st.f' (π i).1 = ψ '' holeC st.a₀ st.b₀ st.c₀ st.f i.1) :
    ∃ β : S ≃ₜ S, β '' F = F' ∧ ∀ x ∈ bd S, β x = x := by
  classical
  have : CompactSpace Y := hY.1
  have : CompactSpace Y' := hY'.1
  have : T2Space S := hS.2.1
  have hF : IsClosed F := hl.isCompact.isClosed
  have hF' : IsClosed F' := hl'.isCompact.isClosed
  have hsb : s ∈ bd S := (show s ∈ F ∩ bd S from hb ▸ mem_insert _ _).2
  have htb : t ∈ bd S := (show t ∈ F ∩ bd S from hb ▸ mem_insert_of_mem _ rfl).2
  let C : Fin st.c₀ → Set Y := fun i => holeC st.a₀ st.b₀ st.c₀ st.f i.1
  let C' : Fin st.c₀ → Set Y' := fun j => holeC st.a₀ st.b₀ st.c₀ st.f' j.1
  let φ : ∀ i : Fin st.c₀, Circle ≃ₜ C i := fun i => holeParam st.hf i.isLt
  let φ' : ∀ j : Fin st.c₀, Circle ≃ₜ C' j := fun j => holeParam st.hf' j.isLt
  have hC_cuff : ∀ i, C i ∈ cuffs Y := fun i => cuffs_eq_holeC st.hf ▸ ⟨i.1, i.isLt, rfl⟩
  have hC'_cuff : ∀ j, C' j ∈ cuffs Y' := fun j => cuffs_eq_holeC st.hf' ▸ ⟨j.1, j.isLt, rfl⟩
  have hC_bd : ∀ i, C i ⊆ bd Y := fun i => by obtain ⟨y, -, hy⟩ := hC_cuff i; rw [← hy]; exact connectedComponentIn_subset _ _
  have hC'_bd : ∀ j, C' j ⊆ bd Y' := fun j => by obtain ⟨y, -, hy⟩ := hC'_cuff j; rw [← hy]; exact connectedComponentIn_subset _ _
  have hC'_inj : Function.Injective C' := fun j₁ j₂ he => by
    by_contra hne'
    have h1 : (φ' j₁ (ee 0)).1 ∈ C' j₁ := (φ' j₁ _).2
    have h2 : (φ' j₁ (ee 0)).1 ∈ C' j₂ := he ▸ h1
    exact Set.disjoint_left.mp (disjoint_holeC st.hf' j₁.isLt j₂.isLt (fun h => hne' (Fin.ext h))) h1 h2
  have hCs_cuff : connectedComponentIn (bd S) s ∈ cuffs S := ⟨s, hsb, rfl⟩
  have hCt_cuff : connectedComponentIn (bd S) t ∈ cuffs S := ⟨t, htb, rfl⟩
  obtain ⟨φs⟩ := (cuff_statement.{u} S hS).2.2 _ hCs_cuff
  obtain ⟨φt⟩ := (cuff_statement.{u} S hS).2.2 _ hCt_cuff
  obtain ⟨_, _, _, _, _, _, hd, hun, -⟩ := id hP
  obtain ⟨_, _, _, _, _, _, hd', hun', -⟩ := id hP'
  obtain ⟨mξ, hmξc, hmξe⟩ := exists_lift (φ st.i_ξ) L.cξ (fun u hu => st.hXC (himξ ▸ ⟨u, hu, rfl⟩))
  obtain ⟨mη, hmηc, hmηe⟩ := exists_lift (φ st.i_ξ) L.cη (fun u hu => hi_eq ▸ st.hX'C (himη ▸ ⟨u, hu, rfl⟩))
  obtain ⟨mξ', hmξ'c, hmξ'e⟩ := exists_lift (φ' st.j_ξ0) L'.cξ (fun u hu => st.hX2C (himξ' ▸ ⟨u, hu, rfl⟩))
  obtain ⟨mη', hmη'c, hmη'e⟩ := exists_lift (φ' st.j_ξ0) L'.cη (fun u hu => hj_eq ▸ st.hX2'C (himη' ▸ ⟨u, hu, rfl⟩))
  obtain ⟨dmY, kY, psY, qsY, ptY, qtY, σsY, σtY, hdmY1, hdmY2, hpsqY, hspSY, hptqY, hspTY, hinSY, hinTY, _, hlocSY, hlocTY, hcocY, _, _⟩ :=
    diff_cuff_info hY hS st.AY AS hne hψ hF hb hP L ha0 ha1 himξ himη hiξ hiη hst φs φt (hC_cuff st.i_ξ) (φ st.i_ξ) hmξc hmξe hmηc hmηe
  obtain ⟨dmY', kY', psY', qsY', ptY', qtY', σsY', σtY', hdmY'1, hdmY'2, _, _, _, _, _, _, _, hlocSY', hlocTY', hcocY', hcovSY', hcovTY'⟩ :=
    diff_cuff_info hY' hS st.AY' AS hne hψ' hF' hb' hP' L' ha'0 ha'1 himξ' himη' hiξ' hiη' hst φs φt (hC'_cuff st.j_ξ0) (φ' st.j_ξ0) hmξ'c hmξ'e hmη'c hmη'e
  have hσ_eq : (σsY == σsY') = (σtY == σtY') := by
    have h1 : (if σsY then (0 : ZMod 2) else 1) - (if σsY' then 0 else 1) =
        (if σtY then (0 : ZMod 2) else 1) - (if σtY' then 0 else 1) := by
      have h2 := hcocY'.symm.trans (hw1.trans hcocY)
      linear_combination h2
    exact bool_beq_of_zmod2_sub_eq h1
  set v_sY := (psY + qsY) / 2
  have hv_sY : v_sY ∈ Ioo psY qsY := by simp only [v_sY]; exact ⟨by linarith, by linarith⟩
  let x_s : S := ψ (φ st.i_ξ (ee v_sY)).1
  have hxs_Cs : x_s ∈ connectedComponentIn (bd S) s := (hinSY v_sY hv_sY).1
  have hxs_nF : x_s ∉ F := (hinSY v_sY hv_sY).2
  have hxs_bd : x_s ∈ bd S \ {s, t} := ⟨connectedComponentIn_subset _ _ hxs_Cs, by
    rintro (he | he)
    · exact hxs_nF (he ▸ (show s ∈ F ∩ bd S from hb ▸ mem_insert _ _).1)
    · exact hxs_nF (he ▸ (show t ∈ F ∩ bd S from hb ▸ mem_insert_of_mem _ rfl).1)⟩
  have hxs_nF' : x_s ∉ F' := fun h => hxs_bd.2 (hb' ▸ ⟨h, hxs_bd.1⟩)
  let eF' := cutComplHomeo hψ' hF'
  let y_s' : Y' := (eF'.symm ⟨x_s, hxs_nF'⟩).1
  have hψ'ys' : ψ' y_s' = x_s := cutComplHomeo_symm_psi hψ' hF' ⟨x_s, hxs_nF'⟩
  have hys'_C : y_s' ∈ C' st.j_ξ0 := by
    have hbd : y_s' ∈ bd Y' := bd_lift hψ' hF' (hψ'ys'.symm ▸ hxs_bd.1) (hψ'ys'.symm ▸ hxs_nF')
    obtain ⟨j, hj⟩ := (cuffs_eq_holeC st.hf').subset (⟨y_s', hbd, rfl⟩ : connectedComponentIn (bd Y') y_s' ∈ cuffs Y')
    have hyj : y_s' ∈ C' ⟨j, hj.1⟩ := show y_s' ∈ holeC st.a₀ st.b₀ st.c₀ st.f' j by rw [hj.2]; exact mem_connectedComponentIn hbd
    by_contra hnot
    have hjne : (⟨j, hj.1⟩ : Fin st.c₀) ≠ st.j_ξ0 := fun he => hnot (he ▸ hyj)
    obtain ⟨_, hD, hsD, _, _⟩ := untouched_cuff_properties hS hY' hψ' hF' hb' hP' st.hf' st.hX2C st.hX2'C hjne (hj_eq ▸ hjne)
    have hDeq : ψ' '' C' ⟨j, hj.1⟩ = connectedComponentIn (bd S) s := by
      by_contra hne'
      exact Set.disjoint_left.mp (cuffs_disjoint hD hCs_cuff hne') ⟨y_s', hyj, hψ'ys'⟩ hxs_Cs
    exact hsD (hDeq.symm ▸ mem_connectedComponentIn hsb)
  obtain ⟨v_sY'0, -, hv_sY'0e⟩ := exists_param ((φ' st.j_ξ0).symm ⟨y_s', hys'_C⟩)
  have hv_sY'0ψ : ψ' (φ' st.j_ξ0 (ee v_sY'0)).1 = x_s := by rw [hv_sY'0e]; simp [hψ'ys']
  obtain ⟨v_sY', hv_sY'_in, hv_sY'_ee⟩ := hcovSY' v_sY'0 ⟨hv_sY'0ψ.symm ▸ hxs_Cs, hv_sY'0ψ.symm ▸ hxs_bd.2⟩
  have hv_sY'_ψ : ψ' (φ' st.j_ξ0 (ee v_sY')).1 = x_s := by rw [hv_sY'_ee, hv_sY'0ψ]
  have hex_flip : ∃ flip : Fin st.c₀ → Bool,
      (st.b₀ = 0 → ∀ i j : Fin st.c₀, flip i = flip j) ∧
      (!flip st.i_ξ) = (σsY == σsY') ∧
      (∀ i : Fin st.c₀, ∀ hi : i ≠ st.i_ξ,
        ∀ (φD : Circle ≃ₜ (ψ '' C i)) (v₀ v₀' δa δb : ℝ) (ma mb : ℝ → ℝ) (da db : Bool),
          0 < δa → 0 < δb → ψ (φ i (ee v₀)).1 = ψ' (φ' (π i) (ee v₀')).1 →
          ContinuousOn ma (Icc (-δa) δa) → ContinuousOn mb (Icc (-δb) δb) →
          (if da then StrictMonoOn ma (Icc (-δa) δa) else StrictAntiOn ma (Icc (-δa) δa)) →
          (if db then StrictMonoOn mb (Icc (-δb) δb) else StrictAntiOn mb (Icc (-δb) δb)) →
          (∀ r ∈ Icc (-δa) δa, ψ (φ i (ee (v₀ + r))).1 = (φD (ee (ma r))).1) →
          (∀ r ∈ Icc (-δb) δb, ψ' (φ' (π i) (ee (v₀' + r))).1 = (φD (ee (mb r))).1) →
          (!flip i) = (da == db)) := by
    by_cases hb0 : st.b₀ = 0
    · have hf0 : Presents (sW (ew st.a₀ 0 st.c₀)) st.f := hb0 ▸ st.hf
      have hf'0 : Presents (sW (ew st.a₀ 0 st.c₀)) st.f' := hb0 ▸ st.hf'
      obtain ⟨Δ, hΔ⟩ := orient_cut_global_flip hS hne hb hb' hl hl' hY hY' hψ hψ' hP hP' hf0 hf'0 hrel
      obtain ⟨δs1, ms1, hδs1, hms1c, hms1d, hms1e⟩ := hlocSY v_sY hv_sY
      obtain ⟨δs2, ms2, hδs2, hms2c, hms2d, hms2e⟩ := hlocSY' v_sY' hv_sY'_in
      have hcast : ∀ (i : Fin st.c₀) (z : Circle), (holeParam hf0 i.isLt z).1 = (φ i z).1 := fun i z => by
        cases st; dsimp only at hb0; subst hb0; rfl
      have hcast' : ∀ (j : Fin st.c₀) (z : Circle), (holeParam hf'0 j.isLt z).1 = (φ' j z).1 := fun j z => by
        cases st; dsimp only at hb0; subst hb0; rfl
      refine ⟨fun _ => decide (Δ ≠ 0), fun _ _ _ => rfl, ?_, fun i hi φD v₀ v₀' δa δb ma mb da db hδa hδb hψeq hmac hmbc hmad hmbd hmae hmbe => ?_⟩
      · exact bool_not_eq_beq_of_zmod2 (hΔ x_s hxs_bd _ hCs_cuff φs hxs_Cs st.i_ξ.1 st.j_ξ0.1 st.i_ξ.isLt st.j_ξ0.isLt
          v_sY v_sY' (by rw [hcast]) (by rw [hcast']; exact hv_sY'_ψ) δs1 δs2 ms1 ms2 σsY σsY' hδs1 hδs2 hms1c hms2c hms1d hms2d
          (fun r hr => by rw [hcast]; exact hms1e r hr) (fun r hr => by rw [hcast']; exact hms2e r hr))
      · obtain ⟨_, hD, hsD, htD, _⟩ := untouched_cuff_properties hS hY hψ hF hb hP st.hf st.hXC st.hX'C hi (hi_eq ▸ hi)
        have hxD : ψ (φ i (ee v₀)).1 ∈ ψ '' C i := ⟨_, (φ i _).2, rfl⟩
        have hxbd : ψ (φ i (ee v₀)).1 ∈ bd S \ {s, t} := ⟨by obtain ⟨z, -, hz⟩ := hD; rw [← hz] at hxD; exact connectedComponentIn_subset _ _ hxD,
          fun h => h.elim (fun he => hsD (Set.mem_of_eq_of_mem he.symm hxD)) (fun he => htD (Set.mem_of_eq_of_mem he.symm hxD))⟩
        exact bool_not_eq_beq_of_zmod2 (hΔ _ hxbd _ hD φD hxD i.1 (π i).1 i.isLt (π i).isLt v₀ v₀'
          (by rw [hcast]) (by rw [hcast']; exact hψeq.symm) δa δb ma mb da db hδa hδb hmac hmbc hmad hmbd
          (fun r hr => by rw [hcast]; exact hmae r hr) (fun r hr => by rw [hcast']; exact hmbe r hr))
    · let hdir : ∀ i : Fin st.c₀, i ≠ st.i_ξ → _ := fun i hi =>
        untouched_dir_pair hS hY hY' AS st.AY st.AY' hψ hψ' hF hF' st.hf st.hf'
          (untouched_cuff_properties hS hY hψ hF hb hP st.hf st.hXC st.hX'C hi (hi_eq ▸ hi)).1
          (untouched_cuff_properties hS hY' hψ' hF' hb' hP' st.hf' st.hX2C st.hX2'C (hπ_unt i hi).1 (hj_eq ▸ (hπ_unt i hi).1)).1
          (untouched_cuff_properties hS hY hψ hF hb hP st.hf st.hXC st.hX'C hi (hi_eq ▸ hi)).2.1
          (hπ_unt i hi).2
      let flip : Fin st.c₀ → Bool := fun i =>
        if hi : i = st.i_ξ then !(σsY == σsY') else !((hdir i hi).choose == (hdir i hi).choose_spec.choose)
      refine ⟨flip, fun h => absurd h hb0, by simp [flip], fun i hi φD v₀ v₀' δa δb ma mb da db hδa hδb _ hmac hmbc hmad hmbd hmae hmbe => ?_⟩
      obtain ⟨w₀, w₀', δw1, δw2, mw1, mw2, dw1, dw2, hδw1, hδw2, _, hmw1c, hmw2c, hmw1d, hmw2d, hmw1e, hmw2e, hbeq⟩ :=
        (hdir i hi).choose_spec.choose_spec φD
      have hdisY := (untouched_cuff_properties hS hY hψ hF hb hP st.hf st.hXC st.hX'C hi (hi_eq ▸ hi)).1
      have hdisY' := (untouched_cuff_properties hS hY' hψ' hF' hb' hP' st.hf' st.hX2C st.hX2'C (hπ_unt i hi).1 (hj_eq ▸ (hπ_unt i hi).1)).1
      have hda : da = dw1 := local_dir_eq_on_untouched hψ (φ i) φD
        (fun z => ⟨⟨_, (φ i z).2, rfl⟩, Set.disjoint_left.mp hdisY (φ i z).2⟩) hδa hδw1 hmac hmw1c hmad hmw1d hmae hmw1e
      have hdb : db = dw2 := local_dir_eq_on_untouched hψ' (φ' (π i)) φD
        (fun z => ⟨by rw [← (hπ_unt i hi).2]; exact ⟨_, (φ' (π i) z).2, rfl⟩, Set.disjoint_left.mp hdisY' (φ' (π i) z).2⟩) hδb hδw2 hmbc hmw2c hmbd hmw2d hmbe hmw2e
      simp only [flip, dite_eq_right hi, Bool.not_not, hda, hdb, hbeq]
  obtain ⟨flip, hfl_const, hfl_cut, hfl_unt⟩ := hex_flip
  obtain ⟨H₀, hH₀⟩ := exists_homeo_match_cuffs st.hf st.hf' π flip hfl_const
  let p₁ : ℝ → ℝ := fun u => if flip st.i_ξ then -mξ u else mξ u
  let p₂ : ℝ → ℝ := fun u => if flip st.i_ξ then -mη u else mη u
  have hp1c : ContinuousOn p₁ (Icc 0 1) := by cases hfl : flip st.i_ξ <;> simp only [p₁, hfl, Bool.false_eq_true, ↓reduceIte]; exact hmξc; exact hmξc.neg
  have hp2c : ContinuousOn p₂ (Icc 0 1) := by cases hfl : flip st.i_ξ <;> simp only [p₂, hfl, Bool.false_eq_true, ↓reduceIte]; exact hmηc; exact hmηc.neg
  have hp1e : ∀ u ∈ Icc (0 : ℝ) 1, (φ' st.j_ξ0 (ee (p₁ u))).1 = H₀ (ξ u) := fun u hu => by
    rw [← hmξe u hu, hH₀ st.i_ξ (ee (mξ u)), hπ_cut]
    cases hfl : flip st.i_ξ <;> simp only [p₁, hfl, Bool.false_eq_true, ↓reduceIte]
    · rfl
    · rw [show ee (-mξ u) = (ee (mξ u))⁻¹ by unfold ee; rw [mul_neg, Circle.exp_neg]]
  have hp2e : ∀ u ∈ Icc (0 : ℝ) 1, (φ' st.j_ξ0 (ee (p₂ u))).1 = H₀ (η u) := fun u hu => by
    rw [← hmηe u hu, hH₀ st.i_ξ (ee (mη u)), hπ_cut]
    cases hfl : flip st.i_ξ <;> simp only [p₂, hfl, Bool.false_eq_true, ↓reduceIte]
    · rfl
    · rw [show ee (-mη u) = (ee (mη u))⁻¹ by unfold ee; rw [mul_neg, Circle.exp_neg]]
  let dp : Bool := xor dmY (flip st.i_ξ)
  let sw : Bool := dp != dmY'
  let ξ₀' : ℝ → Y' := if sw then η' else ξ'
  let η₀' : ℝ → Y' := if sw then ξ' else η'
  let X₀' : Set Y' := if sw then X₂' else X₂
  let X₀'' : Set Y' := if sw then X₂ else X₂'
  let q₁ : ℝ → ℝ := if sw then mη' else mξ'
  let q₂ : ℝ → ℝ := if sw then mξ' else mη'
  have hP₀' : LiftPair ψ' F' s t X₀' X₀'' := by
    cases hsw : sw <;> simp only [X₀', X₀'', hsw, Bool.false_eq_true, ↓reduceIte]
    · exact hP'
    · obtain ⟨x0, x1, y0, y1, l1, l2, hd0, hun0, b1, b2, h7, h8, h9, h10⟩ := id hP'
      exact ⟨y0, y1, x0, x1, l2, l1, hd0.symm, by rw [union_comm]; exact hun0, b2, b1, h8, h7, h10, h9⟩
  have L₀' : ArcLift ψ' F' a' ξ₀' η₀' := by cases hsw : sw <;> simp only [ξ₀', η₀', hsw, Bool.false_eq_true, ↓reduceIte]; exact L'; exact L'.swap
  have him₁' : ξ₀' '' Icc 0 1 = X₀' := by cases hsw : sw <;> simp only [ξ₀', X₀', hsw, Bool.false_eq_true, ↓reduceIte] <;> assumption
  have him₂' : η₀' '' Icc 0 1 = X₀'' := by cases hsw : sw <;> simp only [η₀', X₀'', hsw, Bool.false_eq_true, ↓reduceIte] <;> assumption
  have hi₁' : InjOn ξ₀' (Icc 0 1) := by cases hsw : sw <;> simp only [ξ₀', hsw, Bool.false_eq_true, ↓reduceIte] <;> assumption
  have hi₂' : InjOn η₀' (Icc 0 1) := by cases hsw : sw <;> simp only [η₀', hsw, Bool.false_eq_true, ↓reduceIte] <;> assumption
  have hp1d : if dp then StrictMonoOn p₁ (Icc 0 1) else StrictAntiOn p₁ (Icc 0 1) :=
    strictMono_flip_dir (by simp only [dp]; cases flip st.i_ξ <;> cases dmY <;> rfl) hdmY1
  have hp2d : if !dp then StrictMonoOn p₂ (Icc 0 1) else StrictAntiOn p₂ (Icc 0 1) :=
    strictMono_flip_dir (d := !dmY) (by simp only [dp]; cases flip st.i_ξ <;> cases dmY <;> rfl) (by cases dmY <;> simpa using hdmY2)
  have hq1c : ContinuousOn q₁ (Icc 0 1) := by cases hsw : sw <;> simp only [q₁, hsw, Bool.false_eq_true, ↓reduceIte] <;> assumption
  have hq2c : ContinuousOn q₂ (Icc 0 1) := by cases hsw : sw <;> simp only [q₂, hsw, Bool.false_eq_true, ↓reduceIte] <;> assumption
  have hq1d : if dp then StrictMonoOn q₁ (Icc 0 1) else StrictAntiOn q₁ (Icc 0 1) := by
    cases hdp : dp <;> cases hdm' : dmY' <;> simp only [sw, q₁, hdp, hdm', Bool.bne_false, Bool.bne_true,
      Bool.false_eq_true, ↓reduceIte] at hdmY'1 hdmY'2 ⊢ <;> assumption
  have hq2d : if !dp then StrictMonoOn q₂ (Icc 0 1) else StrictAntiOn q₂ (Icc 0 1) := by
    cases hdp : dp <;> cases hdm' : dmY' <;> simp only [sw, q₂, hdp, hdm', Bool.bne_false, Bool.bne_true,
      Bool.not_false, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hdmY'1 hdmY'2 ⊢ <;> assumption
  have hq1e : ∀ u ∈ Icc (0 : ℝ) 1, (φ' st.j_ξ0 (ee (q₁ u))).1 = ξ₀' u := by cases hsw : sw <;> simp only [q₁, ξ₀', hsw, Bool.false_eq_true, ↓reduceIte] <;> assumption
  have hq2e : ∀ u ∈ Icc (0 : ℝ) 1, (φ' st.j_ξ0 (ee (q₂ u))).1 = η₀' u := by cases hsw : sw <;> simp only [q₂, η₀', hsw, Bool.false_eq_true, ↓reduceIte] <;> assumption
  have hdj_p : ∀ u ∈ Icc (0 : ℝ) 1, ∀ v ∈ Icc (0 : ℝ) 1, ee (p₁ u) ≠ ee (p₂ v) := fun u hu v hv he => by
    have h1 : H₀ (ξ u) = H₀ (η v) := by rw [← hp1e u hu, ← hp2e v hv, he]
    exact Set.disjoint_left.mp hd (himξ ▸ ⟨u, hu, rfl⟩) (H₀.injective h1 ▸ show η v ∈ X' from himη ▸ ⟨v, hv, rfl⟩)
  have hdj_q : ∀ u ∈ Icc (0 : ℝ) 1, ∀ v ∈ Icc (0 : ℝ) 1, ee (q₁ u) ≠ ee (q₂ v) := fun u hu v hv he => by
    have h1 : ξ₀' u = η₀' v := by rw [← hq1e u hu, ← hq2e v hv, he]
    have hd0 : Disjoint X₀' X₀'' := by cases hsw : sw <;> simp only [X₀', X₀'', hsw, Bool.false_eq_true, ↓reduceIte]; exact hd'; exact hd'.symm
    exact Set.disjoint_left.mp hd0 (him₁' ▸ ⟨u, hu, rfl⟩) (h1 ▸ show η₀' v ∈ X₀'' from him₂' ▸ ⟨v, hv, rfl⟩)
  obtain ⟨M, hM1, hM2, hM_fix, kM, hkMp, hkMe⟩ := exists_align_two_arcs_any hY' (hC'_cuff st.j_ξ0) (φ' st.j_ξ0) dp (!dp)
    hp1c hp2c hq1c hq2c hp1d hp2d hq1d hq2d
    (inj_of_lift hp1e (fun a ha b hb he => hiξ ha hb (H₀.injective he)))
    (inj_of_lift hp2e (fun a ha b hb he => hiη ha hb (H₀.injective he)))
    (inj_of_lift hq1e hi₁') (inj_of_lift hq2e hi₂') hdj_p hdj_q
  let H : Y ≃ₜ Y' := H₀.trans M
  have hHξ : ∀ u ∈ Icc (0 : ℝ) 1, H (ξ u) = ξ₀' u := fun u hu => by
    simp only [H, Homeomorph.trans_apply]; rw [← hp1e u hu, hM1 u hu, hq1e u hu]
  have hHη : ∀ u ∈ Icc (0 : ℝ) 1, H (η u) = η₀' u := fun u hu => by
    simp only [H, Homeomorph.trans_apply]; rw [← hp2e u hu, hM2 u hu, hq2e u hu]
  obtain ⟨α, hα_comm, hαF⟩ := exists_descend_of_lifts hψ hψ' L L₀' hP hP₀' himξ himη him₁' him₂' H hHξ hHη
  have hαs : α s = s := by
    have := hα_comm (ξ 0)
    rw [L.hξ 0 ⟨le_rfl, zero_le_one⟩, ha0, hHξ 0 ⟨le_rfl, zero_le_one⟩, L₀'.hξ 0 ⟨le_rfl, zero_le_one⟩, ha'0] at this; exact this
  have hαt : α t = t := by
    have := hα_comm (ξ 1)
    rw [L.hξ 1 ⟨zero_le_one, le_rfl⟩, ha1, hHξ 1 ⟨zero_le_one, le_rfl⟩, L₀'.hξ 1 ⟨zero_le_one, le_rfl⟩, ha'1] at this; exact this
  let k0 : Circle ≃ₜ Circle := if flip st.i_ξ then Homeomorph.inv Circle else Homeomorph.refl Circle
  let kH : Circle ≃ₜ Circle := k0.trans kM
  have hkH_eq : ∀ z : Circle, H (φ st.i_ξ z).1 = (φ' st.j_ξ0 (kH z)).1 := fun z => by
    simp only [H, kH, Homeomorph.trans_apply]
    have h1 : H₀ (φ st.i_ξ z).1 = (φ' st.j_ξ0 (k0 z)).1 := by
      have h := hH₀ st.i_ξ z
      change H₀ (φ st.i_ξ z).1 = (φ' (π st.i_ξ) _).1 at h
      rw [hπ_cut] at h
      cases hfl : flip st.i_ξ <;> simp only [k0, hfl, Bool.false_eq_true, ↓reduceIte] at h ⊢ <;> exact h
    rw [h1, hkMe (k0 z)]
  have hkH_or : if !flip st.i_ξ then PreservesCircleOrientation kH
      else PreservesCircleOrientation ((Homeomorph.inv Circle).trans kH) := by
    cases hfl : flip st.i_ξ <;> simp only [kH, k0, hfl, Bool.not_false, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    · exact preservesCircleOrientation_trans preservesCircleOrientation_refl hkMp
    · have : (Homeomorph.inv Circle).trans ((Homeomorph.inv Circle).trans kM) = kM := Homeomorph.ext fun z => by simp
      rw [this]; exact hkMp
  have hnull : HasNullSignature α := fun D φD hD => by
    by_cases hDCs : D = connectedComponentIn (bd S) s
    · subst hDCs
      have hαCs : ∀ x, x ∈ connectedComponentIn (bd S) s ↔ α x ∈ connectedComponentIn (bd S) s := fun x => by
        have h1 : α '' connectedComponentIn (bd S) s = connectedComponentIn (bd S) s := by
          rw [α.image_connectedComponentIn hsb, image_bd_homeomorph α, hαs]
        exact ⟨fun hx => h1 ▸ mem_image_of_mem α hx, fun hαx => by obtain ⟨z, hz, hzα⟩ := h1.symm.subset hαx; rwa [α.injective hzα] at hz⟩
      obtain ⟨w_s', -, hw_s'e⟩ := exists_param (kH (ee v_sY))
      have hw_s'ψ : ψ' (φ' st.j_ξ0 (ee w_s')).1 = α x_s := by rw [hw_s'e, ← hkH_eq, ← hα_comm]
      have hw_s'Cs : ψ' (φ' st.j_ξ0 (ee w_s')).1 ∈ connectedComponentIn (bd S) s := hw_s'ψ ▸ (hαCs x_s).mp hxs_Cs
      have hw_s'nF' : ψ' (φ' st.j_ξ0 (ee w_s')).1 ∉ F' := hw_s'ψ ▸ fun hF' => by
        obtain ⟨z, hzF, hzα⟩ := hαF.symm.subset hF'; exact hxs_nF (α.injective hzα ▸ hzF)
      obtain ⟨w_sY', hw_sY'_in, hw_sY'_ee⟩ := hcovSY' w_s' ⟨hw_s'Cs, fun hst' => hw_s'nF' (hb' ▸ hst' : ψ' (φ' st.j_ξ0 (ee w_s')).1 ∈ F' ∩ bd S).1⟩
      obtain ⟨δa, ma, da, hδa, _, hmac, hmad, hmae, hsig_a⟩ :=
        exists_cuff_local_dir hY hS hψ hF st.AY AS (hC_bd st.i_ξ) hCs_cuff (φ st.i_ξ) φD hxs_Cs hxs_nF
      obtain ⟨δb, mb, db, hδb, _, hmbc, hmbd, hmbe, hsig_b⟩ :=
        exists_cuff_local_dir hY' hS hψ' hF' st.AY' AS (hC'_bd st.j_ξ0) hCs_cuff (φ' st.j_ξ0) φD hw_s'Cs hw_s'nF'
      obtain ⟨δ1s, m1s, hδ1s, hm1sc, hm1sd, hm1se⟩ := hlocSY v_sY hv_sY
      obtain ⟨δ2s, m2s, hδ2s, hm2sc, hm2sd, hm2se⟩ := hlocSY' w_sY' hw_sY'_in
      have hm2se' : ∀ r ∈ Icc (-δ2s) δ2s, ψ' (φ' st.j_ξ0 (ee (w_s' + r))).1 = (φs (ee (m2s r))).1 := fun r hr => by
        obtain ⟨j, hj⟩ := ee_eq_iff.mp hw_sY'_ee
        rw [show ee (w_s' + r) = ee (w_sY' + r) from ee_eq_iff.mpr ⟨-j, by push_cast; linarith⟩]; exact hm2se r hr
      have hdab : (da == db) = (σsY == σsY') := by
        let kSD : Circle ≃ₜ Circle := φD.trans φs.symm
        have hcs_const : ∀ x ∈ connectedComponentIn (bd S) s,
            cuffSign AS φD x - cuffSign AS φs x = if PreservesCircleOrientation kSD then 0 else 1 := fun x hx => by
          have h1 := cuffSign_comp_circle AS (connectedComponentIn_subset _ _) φs kSD hx
          have : φD = kSD.trans φs := Homeomorph.ext fun z => by simp [kSD]
          rw [this, h1]; ring
        have hsub1 : (if da then (0 : ZMod 2) else 1) - (if σsY then 0 else 1) = if PreservesCircleOrientation kSD then 0 else 1 := by
          have h1 := cutOrientDiff_cuff_mono hY hS hψ hF st.AY AS (hC_bd st.i_ξ) (connectedComponentIn_subset _ _)
            (φ st.i_ξ) φs (φ st.i_ξ _).2 hxs_nF hδ1s σsY hm1sc hm1sd hm1se rfl
          have h2 := hcs_const x_s hxs_Cs; linear_combination h1 + h2 - hsig_a
        have hsub2 : (if db then (0 : ZMod 2) else 1) - (if σsY' then 0 else 1) = if PreservesCircleOrientation kSD then 0 else 1 := by
          have h1 := cutOrientDiff_cuff_mono hY' hS hψ' hF' st.AY' AS (hC'_bd st.j_ξ0) (connectedComponentIn_subset _ _)
            (φ' st.j_ξ0) φs (φ' st.j_ξ0 _).2 hw_s'nF' hδ2s σsY' hm2sc hm2sd hm2se' rfl
          have h2 := hcs_const _ hw_s'Cs; linear_combination h1 + h2 - hsig_b
        exact bool_beq_of_zmod2_sub_eq (by linear_combination hsub1 - hsub2)
      exact preservesCircleOrientation_of_local_dirs hα_comm hαCs φD (φ st.i_ξ) (φ' st.j_ξ0) (!flip st.i_ξ) hkH_or hkH_eq
        hw_s'e.symm hδa hδb hmac hmbc hmad hmbd hmae hmbe (by rw [hdab]; exact hfl_cut)
    · by_cases hDCt : D = connectedComponentIn (bd S) t
      · subst hDCt
        have hαCt : ∀ x, x ∈ connectedComponentIn (bd S) t ↔ α x ∈ connectedComponentIn (bd S) t := fun x => by
          have h1 : α '' connectedComponentIn (bd S) t = connectedComponentIn (bd S) t := by
            rw [α.image_connectedComponentIn htb, image_bd_homeomorph α, hαt]
          exact ⟨fun hx => h1 ▸ mem_image_of_mem α hx, fun hαx => by obtain ⟨z, hz, hzα⟩ := h1.symm.subset hαx; rwa [α.injective hzα] at hz⟩
        set v_tY := (ptY + qtY) / 2
        have hv_tY : v_tY ∈ Ioo ptY qtY := by simp only [v_tY]; exact ⟨by linarith, by linarith⟩
        let x_t : S := ψ (φ st.i_ξ (ee v_tY)).1
        have hxt_Ct : x_t ∈ connectedComponentIn (bd S) t := (hinTY v_tY hv_tY).1
        have hxt_nF : x_t ∉ F := (hinTY v_tY hv_tY).2
        obtain ⟨w_t', -, hw_t'e⟩ := exists_param (kH (ee v_tY))
        have hw_t'ψ : ψ' (φ' st.j_ξ0 (ee w_t')).1 = α x_t := by rw [hw_t'e, ← hkH_eq, ← hα_comm]
        have hw_t'Ct : ψ' (φ' st.j_ξ0 (ee w_t')).1 ∈ connectedComponentIn (bd S) t := hw_t'ψ ▸ (hαCt x_t).mp hxt_Ct
        have hw_t'nF' : ψ' (φ' st.j_ξ0 (ee w_t')).1 ∉ F' := hw_t'ψ ▸ fun hF' => by
          obtain ⟨z, hzF, hzα⟩ := hαF.symm.subset hF'; exact hxt_nF (α.injective hzα ▸ hzF)
        obtain ⟨w_tY', hw_tY'_in, hw_tY'_ee⟩ := hcovTY' w_t' ⟨hw_t'Ct, fun hst' => hw_t'nF' (hb' ▸ hst' : ψ' (φ' st.j_ξ0 (ee w_t')).1 ∈ F' ∩ bd S).1⟩
        obtain ⟨δa, ma, da, hδa, _, hmac, hmad, hmae, hsig_a⟩ :=
          exists_cuff_local_dir hY hS hψ hF st.AY AS (hC_bd st.i_ξ) hCt_cuff (φ st.i_ξ) φD hxt_Ct hxt_nF
        obtain ⟨δb, mb, db, hδb, _, hmbc, hmbd, hmbe, hsig_b⟩ :=
          exists_cuff_local_dir hY' hS hψ' hF' st.AY' AS (hC'_bd st.j_ξ0) hCt_cuff (φ' st.j_ξ0) φD hw_t'Ct hw_t'nF'
        obtain ⟨δ1t, m1t, hδ1t, hm1tc, hm1td, hm1te⟩ := hlocTY v_tY hv_tY
        obtain ⟨δ2t, m2t, hδ2t, hm2tc, hm2td, hm2te⟩ := hlocTY' w_tY' hw_tY'_in
        have hm2te' : ∀ r ∈ Icc (-δ2t) δ2t, ψ' (φ' st.j_ξ0 (ee (w_t' + r))).1 = (φt (ee (m2t r))).1 := fun r hr => by
          obtain ⟨j, hj⟩ := ee_eq_iff.mp hw_tY'_ee
          rw [show ee (w_t' + r) = ee (w_tY' + r) from ee_eq_iff.mpr ⟨-j, by push_cast; linarith⟩]; exact hm2te r hr
        have hdab : (da == db) = (σtY == σtY') := by
          let kTD : Circle ≃ₜ Circle := φD.trans φt.symm
          have hcs_const : ∀ x ∈ connectedComponentIn (bd S) t,
              cuffSign AS φD x - cuffSign AS φt x = if PreservesCircleOrientation kTD then 0 else 1 := fun x hx => by
            have h1 := cuffSign_comp_circle AS (connectedComponentIn_subset _ _) φt kTD hx
            have : φD = kTD.trans φt := Homeomorph.ext fun z => by simp [kTD]
            rw [this, h1]; ring
          have hsub1 : (if da then (0 : ZMod 2) else 1) - (if σtY then 0 else 1) = if PreservesCircleOrientation kTD then 0 else 1 := by
            have h1 := cutOrientDiff_cuff_mono hY hS hψ hF st.AY AS (hC_bd st.i_ξ) (connectedComponentIn_subset _ _)
              (φ st.i_ξ) φt (φ st.i_ξ _).2 hxt_nF hδ1t σtY hm1tc hm1td hm1te rfl
            have h2 := hcs_const x_t hxt_Ct; linear_combination h1 + h2 - hsig_a
          have hsub2 : (if db then (0 : ZMod 2) else 1) - (if σtY' then 0 else 1) = if PreservesCircleOrientation kTD then 0 else 1 := by
            have h1 := cutOrientDiff_cuff_mono hY' hS hψ' hF' st.AY' AS (hC'_bd st.j_ξ0) (connectedComponentIn_subset _ _)
              (φ' st.j_ξ0) φt (φ' st.j_ξ0 _).2 hw_t'nF' hδ2t σtY' hm2tc hm2td hm2te' rfl
            have h2 := hcs_const _ hw_t'Ct; linear_combination h1 + h2 - hsig_b
          exact bool_beq_of_zmod2_sub_eq (by linear_combination hsub1 - hsub2)
        exact preservesCircleOrientation_of_local_dirs hα_comm hαCt φD (φ st.i_ξ) (φ' st.j_ξ0) (!flip st.i_ξ) hkH_or hkH_eq
          hw_t'e.symm hδa hδb hmac hmbc hmad hmbd hmae hmbe (by rw [hdab, ← hσ_eq]; exact hfl_cut)
      · have hsD : s ∉ D := fun hs => hDCs (by by_contra hne'; exact Set.disjoint_left.mp (cuffs_disjoint hD hCs_cuff hne') hs (mem_connectedComponentIn hsb))
        have htD : t ∉ D := fun ht => hDCt (by by_contra hne'; exact Set.disjoint_left.mp (cuffs_disjoint hD hCt_cuff hne') ht (mem_connectedComponentIn htb))
        obtain ⟨hpre_cuff, hpre_disj, him⟩ := untouched_cuff_preimage hY hS hψ hF hb hD hsD htD
        obtain ⟨i, hi_lt, hi_eq'⟩ := (cuffs_eq_holeC st.hf).subset hpre_cuff
        let iF : Fin st.c₀ := ⟨i, hi_lt⟩
        have hξ0 : ξ 0 ∈ X := himξ ▸ ⟨0, ⟨le_rfl, zero_le_one⟩, rfl⟩
        have hi_ne : iF ≠ st.i_ξ := fun he =>
          Set.disjoint_left.mp hpre_disj (by rw [← hi_eq', show holeC st.a₀ st.b₀ st.c₀ st.f i = C iF from rfl, he]; exact st.hXC hξ0) (show ξ 0 ∈ ψ ⁻¹' F from hun ▸ Or.inl hξ0)
        have hDeq : ψ '' C iF = D := by rw [show C iF = holeC st.a₀ st.b₀ st.c₀ st.f i from rfl, hi_eq']; exact him
        subst hDeq
        have huY := untouched_cuff_properties hS hY hψ hF hb hP st.hf st.hXC st.hX'C hi_ne (hi_eq ▸ hi_ne)
        have huY' := untouched_cuff_properties hS hY' hψ' hF' hb' hP' st.hf' st.hX2C st.hX2'C (hπ_unt iF hi_ne).1 (hj_eq ▸ (hπ_unt iF hi_ne).1)
        exact untouched_cuff_null hS hY hY' AS st.AY st.AY' hψ hψ' hF hF' st.hf st.hf'
          huY.1 huY'.1 huY.2.1 huY'.2.2.2.2 (hπ_unt iF hi_ne).2 H (flip iF)
          (fun z => by
            simp only [H, Homeomorph.trans_apply, hH₀ iF z]
            exact hM_fix (C' (π iF)) (hC'_cuff (π iF)) (fun he => (hπ_unt iF hi_ne).1 (hC'_inj he)) _ (φ' (π iF) _).2)
          (hfl_unt iF hi_ne) α hα_comm φD
  exact parallel_conn hS hne hb' hl' hαF hαs hαt hnull

end CaseDiffCuff

/-! ### Case 2: Same cuff `C_s = C_t`, 1-sided (`C_ξ = C_η`) -/

section CaseSame1Sided

variable {S Y Y' : Type u} [TopologicalSpace S] [TopologicalSpace Y] [T2Space Y]
  [TopologicalSpace Y'] [T2Space Y']

private theorem parallel_case_1sided [ConnectedSpace S] [ConnectedSpace Y] [ConnectedSpace Y']
    (hS : IsSurface S) (hY : IsSurface Y) (hY' : IsSurface Y')
    {F F' : Set S} {s t : S} (hne : s ≠ t)
    (hb : F ∩ bd S = {s, t}) (hb' : F' ∩ bd S = {s, t})
    (hl : IsLineWithEnds F s t) (hl' : IsLineWithEnds F' s t)
    {ψ : Y → S} {ψ' : Y' → S} (hψ : IsCutting ψ F) (hψ' : IsCutting ψ' F')
    {X X' : Set Y} {X₂ X₂' : Set Y'}
    (hP : LiftPair ψ F s t X X') (hP' : LiftPair ψ' F' s t X₂ X₂')
    {a a' : ℝ → S} {ξ η : ℝ → Y} {ξ' η' : ℝ → Y'}
    (L : ArcLift ψ F a ξ η) (L' : ArcLift ψ' F' a' ξ' η')
    (ha0 : a 0 = s) (ha1 : a 1 = t) (ha'0 : a' 0 = s) (ha'1 : a' 1 = t)
    (himξ : ξ '' Icc 0 1 = X) (himη : η '' Icc 0 1 = X')
    (himξ' : ξ' '' Icc 0 1 = X₂) (himη' : η' '' Icc 0 1 = X₂')
    (hiξ : InjOn ξ (Icc 0 1)) (hiη : InjOn η (Icc 0 1))
    (hiξ' : InjOn ξ' (Icc 0 1)) (hiη' : InjOn η' (Icc 0 1))
    (AS : SurfAtlas S)
    (hrel : BdCohRel s t (arcCocycle hS hne hb' hl') (arcCocycle hS hne hb hl))
    (hst : connectedComponentIn (bd S) s = connectedComponentIn (bd S) t)
    (φS : Circle ≃ₜ connectedComponentIn (bd S) s)
    {u_s u_t : ℝ} (hu1 : u_s < u_t) (hu2 : u_t < u_s + 1)
    (hus : (φS (ee u_s)).1 = s) (hut : (φS (ee u_t)).1 = t)
    (st : CutSetup ψ ψ' F F' s t X X' X₂ X₂' a a' ξ η ξ' η')
    (hi_eq : st.i_ξ = st.i_η) (hj_eq : st.j_ξ0 = st.j_η0)
    (π : Equiv.Perm (Fin st.c₀)) (hπ_cut : π st.i_ξ = st.j_ξ0)
    (hπ_unt : ∀ i : Fin st.c₀, i ≠ st.i_ξ → π i ≠ st.j_ξ0 ∧
      ψ' '' holeC st.a₀ st.b₀ st.c₀ st.f' (π i).1 = ψ '' holeC st.a₀ st.b₀ st.c₀ st.f i.1) :
    ∃ β : S ≃ₜ S, β '' F = F' ∧ ∀ x ∈ bd S, β x = x := by
  classical
  have : CompactSpace Y := hY.1
  have : CompactSpace Y' := hY'.1
  have : T2Space S := hS.2.1
  have hF : IsClosed F := hl.isCompact.isClosed
  have hF' : IsClosed F' := hl'.isCompact.isClosed
  have hsb : s ∈ bd S := (show s ∈ F ∩ bd S from hb ▸ mem_insert _ _).2
  have hCs_cuff : connectedComponentIn (bd S) s ∈ cuffs S := ⟨s, hsb, rfl⟩
  let C : Fin st.c₀ → Set Y := fun i => holeC st.a₀ st.b₀ st.c₀ st.f i.1
  let C' : Fin st.c₀ → Set Y' := fun j => holeC st.a₀ st.b₀ st.c₀ st.f' j.1
  let φ : ∀ i : Fin st.c₀, Circle ≃ₜ C i := fun i => holeParam st.hf i.isLt
  let φ' : ∀ j : Fin st.c₀, Circle ≃ₜ C' j := fun j => holeParam st.hf' j.isLt
  have hC_cuff : ∀ i, C i ∈ cuffs Y := fun i => cuffs_eq_holeC st.hf ▸ ⟨i.1, i.isLt, rfl⟩
  have hC'_cuff : ∀ j, C' j ∈ cuffs Y' := fun j => cuffs_eq_holeC st.hf' ▸ ⟨j.1, j.isLt, rfl⟩
  have hC_bd : ∀ i, C i ⊆ bd Y := fun i => by obtain ⟨y, -, hy⟩ := hC_cuff i; rw [← hy]; exact connectedComponentIn_subset _ _
  have hC'_bd : ∀ j, C' j ⊆ bd Y' := fun j => by obtain ⟨y, -, hy⟩ := hC'_cuff j; rw [← hy]; exact connectedComponentIn_subset _ _
  have hC'_inj : Function.Injective C' := fun j₁ j₂ he => by
    by_contra hne'
    have h1 : (φ' j₁ (ee 0)).1 ∈ C' j₁ := (φ' j₁ _).2
    have h2 : (φ' j₁ (ee 0)).1 ∈ C' j₂ := he ▸ h1
    exact Set.disjoint_left.mp (disjoint_holeC st.hf' j₁.isLt j₂.isLt (fun h => hne' (Fin.ext h))) h1 h2
  obtain ⟨_, _, _, _, _, _, hd, hun, -⟩ := id hP
  obtain ⟨_, _, _, _, _, _, hd', hun', -⟩ := id hP'
  let G₁ : Set S := (fun v => (φS (ee v)).1) '' Ioo u_t (u_s + 1)
  let G₂ : Set S := (fun v => (φS (ee v)).1) '' Ioo u_s u_t
  have hGpart_eq : connectedComponentIn (bd S) s \ {s, t} = G₁ ∪ G₂ := (same_cuff_gaps_partition φS hu1 hu2 hus hut).1
  let x₁ : S := (φS (ee ((u_t + (u_s + 1)) / 2))).1
  have hx₁G₁ : x₁ ∈ G₁ := ⟨(u_t + (u_s + 1)) / 2, ⟨by linarith, by linarith⟩, rfl⟩
  have hx₁_diff : x₁ ∈ connectedComponentIn (bd S) s \ {s, t} := by rw [hGpart_eq]; exact Or.inl hx₁G₁
  have hx₁_bd : x₁ ∈ bd S \ {s, t} := ⟨connectedComponentIn_subset _ _ hx₁_diff.1, hx₁_diff.2⟩
  have hx₁nF : x₁ ∉ F := fun h => hx₁_bd.2 (hb ▸ ⟨h, hx₁_bd.1⟩)
  have hx₁nF' : x₁ ∉ F' := fun h => hx₁_bd.2 (hb' ▸ ⟨h, hx₁_bd.1⟩)
  let eF := cutComplHomeo hψ hF
  let eF' := cutComplHomeo hψ' hF'
  let y₁ : Y := (eF.symm ⟨x₁, hx₁nF⟩).1
  let y₁' : Y' := (eF'.symm ⟨x₁, hx₁nF'⟩).1
  have hψy₁ : ψ y₁ = x₁ := cutComplHomeo_symm_psi hψ hF ⟨x₁, hx₁nF⟩
  have hψ'y₁ : ψ' y₁' = x₁ := cutComplHomeo_symm_psi hψ' hF' ⟨x₁, hx₁nF'⟩
  have hy₁C : y₁ ∈ C st.i_ξ := by
    have hbd : y₁ ∈ bd Y := bd_lift hψ hF (hψy₁.symm ▸ hx₁_bd.1) (hψy₁.symm ▸ hx₁nF)
    obtain ⟨i, hi_lt, hi_eq'⟩ := (cuffs_eq_holeC st.hf).subset (⟨y₁, hbd, rfl⟩ : connectedComponentIn (bd Y) y₁ ∈ cuffs Y)
    have hyi : y₁ ∈ C ⟨i, hi_lt⟩ := show y₁ ∈ holeC st.a₀ st.b₀ st.c₀ st.f i by rw [hi_eq']; exact mem_connectedComponentIn hbd
    by_contra hnot
    have hne1 : (⟨i, hi_lt⟩ : Fin st.c₀) ≠ st.i_ξ := fun he => hnot (he ▸ hyi)
    obtain ⟨_, hD, hsD, _, _⟩ := untouched_cuff_properties hS hY hψ hF hb hP st.hf st.hXC st.hX'C hne1 (hi_eq ▸ hne1)
    have hDeq : ψ '' C ⟨i, hi_lt⟩ = connectedComponentIn (bd S) s := by
      by_contra hne'; exact Set.disjoint_left.mp (cuffs_disjoint hD hCs_cuff hne') ⟨y₁, hyi, hψy₁⟩ hx₁_diff.1
    exact hsD (hDeq.symm ▸ mem_connectedComponentIn hsb)
  have hy₁'C : y₁' ∈ C' st.j_ξ0 := by
    have hbd : y₁' ∈ bd Y' := bd_lift hψ' hF' (hψ'y₁.symm ▸ hx₁_bd.1) (hψ'y₁.symm ▸ hx₁nF')
    obtain ⟨j, hj_lt, hj_eq'⟩ := (cuffs_eq_holeC st.hf').subset (⟨y₁', hbd, rfl⟩ : connectedComponentIn (bd Y') y₁' ∈ cuffs Y')
    have hyj : y₁' ∈ C' ⟨j, hj_lt⟩ := show y₁' ∈ holeC st.a₀ st.b₀ st.c₀ st.f' j by rw [hj_eq']; exact mem_connectedComponentIn hbd
    by_contra hnot
    have hne1 : (⟨j, hj_lt⟩ : Fin st.c₀) ≠ st.j_ξ0 := fun he => hnot (he ▸ hyj)
    obtain ⟨_, hD, hsD, _, _⟩ := untouched_cuff_properties hS hY' hψ' hF' hb' hP' st.hf' st.hX2C st.hX2'C hne1 (hj_eq ▸ hne1)
    have hDeq : ψ' '' C' ⟨j, hj_lt⟩ = connectedComponentIn (bd S) s := by
      by_contra hne'; exact Set.disjoint_left.mp (cuffs_disjoint hD hCs_cuff hne') ⟨y₁', hyj, hψ'y₁⟩ hx₁_diff.1
    exact hsD (hDeq.symm ▸ mem_connectedComponentIn hsb)
  obtain ⟨v₁, -, hv₁e⟩ := exists_param ((φ st.i_ξ).symm ⟨y₁, hy₁C⟩)
  obtain ⟨v₁', -, hv₁'e⟩ := exists_param ((φ' st.j_ξ0).symm ⟨y₁', hy₁'C⟩)
  have hv₁y : (φ st.i_ξ (ee v₁)).1 = y₁ := by rw [hv₁e]; simp
  have hv₁'y : (φ' st.j_ξ0 (ee v₁')).1 = y₁' := by rw [hv₁'e]; simp
  obtain ⟨δ₁, m₁_loc, d₁, hδ₁, _, hm₁lc, hm₁ld, hm₁le, _⟩ :=
    exists_cuff_local_dir hY hS hψ hF st.AY AS (hC_bd st.i_ξ) hCs_cuff (φ st.i_ξ) φS (by rw [hv₁y, hψy₁]; exact hx₁_diff.1) (by rw [hv₁y, hψy₁]; exact hx₁nF)
  obtain ⟨δ₁', m₁'_loc, d₁', hδ₁', _, hm₁'lc, hm₁'ld, hm₁'le, _⟩ :=
    exists_cuff_local_dir hY' hS hψ' hF' st.AY' AS (hC'_bd st.j_ξ0) hCs_cuff (φ' st.j_ξ0) φS (by rw [hv₁'y, hψ'y₁]; exact hx₁_diff.1) (by rw [hv₁'y, hψ'y₁]; exact hx₁nF')
  have hex_flip : ∃ flip : Fin st.c₀ → Bool,
      (st.b₀ = 0 → ∀ i j : Fin st.c₀, flip i = flip j) ∧
      (!flip st.i_ξ) = (d₁ == d₁') ∧
      (∀ i : Fin st.c₀, ∀ hi : i ≠ st.i_ξ,
        ∀ (φD : Circle ≃ₜ (ψ '' C i)) (v₀ v₀' δa δb : ℝ) (ma mb : ℝ → ℝ) (da db : Bool),
          0 < δa → 0 < δb → ψ (φ i (ee v₀)).1 = ψ' (φ' (π i) (ee v₀')).1 →
          ContinuousOn ma (Icc (-δa) δa) → ContinuousOn mb (Icc (-δb) δb) →
          (if da then StrictMonoOn ma (Icc (-δa) δa) else StrictAntiOn ma (Icc (-δa) δa)) →
          (if db then StrictMonoOn mb (Icc (-δb) δb) else StrictAntiOn mb (Icc (-δb) δb)) →
          (∀ r ∈ Icc (-δa) δa, ψ (φ i (ee (v₀ + r))).1 = (φD (ee (ma r))).1) →
          (∀ r ∈ Icc (-δb) δb, ψ' (φ' (π i) (ee (v₀' + r))).1 = (φD (ee (mb r))).1) →
          (!flip i) = (da == db)) := by
    by_cases hb0 : st.b₀ = 0
    · have hf0 : Presents (sW (ew st.a₀ 0 st.c₀)) st.f := hb0 ▸ st.hf
      have hf'0 : Presents (sW (ew st.a₀ 0 st.c₀)) st.f' := hb0 ▸ st.hf'
      obtain ⟨Δ, hΔ⟩ := orient_cut_global_flip hS hne hb hb' hl hl' hY hY' hψ hψ' hP hP' hf0 hf'0 hrel
      have hcast : ∀ (i : Fin st.c₀) (z : Circle), (holeParam hf0 i.isLt z).1 = (φ i z).1 := fun i z => by
        cases st; dsimp only at hb0; subst hb0; rfl
      have hcast' : ∀ (j : Fin st.c₀) (z : Circle), (holeParam hf'0 j.isLt z).1 = (φ' j z).1 := fun j z => by
        cases st; dsimp only at hb0; subst hb0; rfl
      refine ⟨fun _ => decide (Δ ≠ 0), fun _ _ _ => rfl, ?_, fun i hi φD v₀ v₀' δa δb ma mb da db hδa hδb hψeq hmac hmbc hmad hmbd hmae hmbe => ?_⟩
      · exact bool_not_eq_beq_of_zmod2 (hΔ x₁ hx₁_bd _ hCs_cuff φS hx₁_diff.1 st.i_ξ.1 st.j_ξ0.1 st.i_ξ.isLt st.j_ξ0.isLt
          v₁ v₁' (by rw [hcast, hv₁y, hψy₁]) (by rw [hcast', hv₁'y, hψ'y₁]) δ₁ δ₁' m₁_loc m₁'_loc d₁ d₁' hδ₁ hδ₁' hm₁lc hm₁'lc hm₁ld hm₁'ld
          (fun r hr => by rw [hcast]; exact hm₁le r hr) (fun r hr => by rw [hcast']; exact hm₁'le r hr))
      · obtain ⟨_, hD, hsD, htD, _⟩ := untouched_cuff_properties hS hY hψ hF hb hP st.hf st.hXC st.hX'C hi (hi_eq ▸ hi)
        have hxD : ψ (φ i (ee v₀)).1 ∈ ψ '' C i := ⟨_, (φ i _).2, rfl⟩
        have hxbd : ψ (φ i (ee v₀)).1 ∈ bd S \ {s, t} := ⟨by obtain ⟨z, -, hz⟩ := hD; rw [← hz] at hxD; exact connectedComponentIn_subset _ _ hxD,
          fun h => h.elim (fun he => hsD (Set.mem_of_eq_of_mem he.symm hxD)) (fun he => htD (Set.mem_of_eq_of_mem he.symm hxD))⟩
        exact bool_not_eq_beq_of_zmod2 (hΔ _ hxbd _ hD φD hxD i.1 (π i).1 i.isLt (π i).isLt v₀ v₀'
          (by rw [hcast]) (by rw [hcast']; exact hψeq.symm) δa δb ma mb da db hδa hδb hmac hmbc hmad hmbd
          (fun r hr => by rw [hcast]; exact hmae r hr) (fun r hr => by rw [hcast']; exact hmbe r hr))
    · let hdir : ∀ i : Fin st.c₀, i ≠ st.i_ξ → _ := fun i hi =>
        untouched_dir_pair hS hY hY' AS st.AY st.AY' hψ hψ' hF hF' st.hf st.hf'
          (untouched_cuff_properties hS hY hψ hF hb hP st.hf st.hXC st.hX'C hi (hi_eq ▸ hi)).1
          (untouched_cuff_properties hS hY' hψ' hF' hb' hP' st.hf' st.hX2C st.hX2'C (hπ_unt i hi).1 (hj_eq ▸ (hπ_unt i hi).1)).1
          (untouched_cuff_properties hS hY hψ hF hb hP st.hf st.hXC st.hX'C hi (hi_eq ▸ hi)).2.1
          (hπ_unt i hi).2
      let flip : Fin st.c₀ → Bool := fun i =>
        if hi : i = st.i_ξ then !(d₁ == d₁') else !((hdir i hi).choose == (hdir i hi).choose_spec.choose)
      refine ⟨flip, fun h => absurd h hb0, by simp [flip], fun i hi φD v₀ v₀' δa δb ma mb da db hδa hδb _ hmac hmbc hmad hmbd hmae hmbe => ?_⟩
      obtain ⟨w₀, w₀', δw1, δw2, mw1, mw2, dw1, dw2, hδw1, hδw2, _, hmw1c, hmw2c, hmw1d, hmw2d, hmw1e, hmw2e, hbeq⟩ :=
        (hdir i hi).choose_spec.choose_spec φD
      have hdisY := (untouched_cuff_properties hS hY hψ hF hb hP st.hf st.hXC st.hX'C hi (hi_eq ▸ hi)).1
      have hdisY' := (untouched_cuff_properties hS hY' hψ' hF' hb' hP' st.hf' st.hX2C st.hX2'C (hπ_unt i hi).1 (hj_eq ▸ (hπ_unt i hi).1)).1
      have hda : da = dw1 := local_dir_eq_on_untouched hψ (φ i) φD
        (fun z => ⟨⟨_, (φ i z).2, rfl⟩, Set.disjoint_left.mp hdisY (φ i z).2⟩) hδa hδw1 hmac hmw1c hmad hmw1d hmae hmw1e
      have hdb : db = dw2 := local_dir_eq_on_untouched hψ' (φ' (π i)) φD
        (fun z => ⟨by rw [← (hπ_unt i hi).2]; exact ⟨_, (φ' (π i) z).2, rfl⟩, Set.disjoint_left.mp hdisY' (φ' (π i) z).2⟩) hδb hδw2 hmbc hmw2c hmbd hmw2d hmbe hmw2e
      simp only [flip, dite_eq_right hi, Bool.not_not, hda, hdb, hbeq]
  obtain ⟨flip, hfl_const, hfl_cut, hfl_unt⟩ := hex_flip
  obtain ⟨H₀, hH₀⟩ := exists_homeo_match_cuffs st.hf st.hf' π flip hfl_const
  obtain ⟨mξ, hmξc, hmξe⟩ := exists_lift (φ st.i_ξ) L.cξ (fun u hu => st.hXC (himξ ▸ ⟨u, hu, rfl⟩))
  obtain ⟨mη, hmηc, hmηe⟩ := exists_lift (φ st.i_ξ) L.cη (fun u hu => hi_eq ▸ st.hX'C (himη ▸ ⟨u, hu, rfl⟩))
  obtain ⟨mξ', hmξ'c, hmξ'e⟩ := exists_lift (φ' st.j_ξ0) L'.cξ (fun u hu => st.hX2C (himξ' ▸ ⟨u, hu, rfl⟩))
  obtain ⟨mη', hmη'c, hmη'e⟩ := exists_lift (φ' st.j_ξ0) L'.cη (fun u hu => hj_eq ▸ st.hX2'C (himη' ▸ ⟨u, hu, rfl⟩))
  obtain ⟨hmξ_d, hmη_d, kY, g1Y, hgY_info⟩ :=
    onesided_cuff_info hY hS hne hψ hF hb hP L ha0 ha1 himξ himη hiξ hiη hst φS hu1 hu2 hus hut
      (hC_cuff st.i_ξ) (φ st.i_ξ) hmξc hmξe hmηc hmηe hx₁G₁ hx₁_bd (by rw [hv₁y, hψy₁]) hδ₁ hm₁lc hm₁ld hm₁le
  obtain ⟨hmξ'_d, hmη'_d, kY', g1Y', hgY'_info⟩ :=
    onesided_cuff_info hY' hS hne hψ' hF' hb' hP' L' ha'0 ha'1 himξ' himη' hiξ' hiη' hst φS hu1 hu2 hus hut
      (hC'_cuff st.j_ξ0) (φ' st.j_ξ0) hmξ'c hmξ'e hmη'c hmη'e hx₁G₁ hx₁_bd (by rw [hv₁'y, hψ'y₁]) hδ₁' hm₁'lc hm₁'ld hm₁'le
  let p₁ : ℝ → ℝ := fun u => if flip st.i_ξ then -mξ u else mξ u
  let p₂ : ℝ → ℝ := fun u => if flip st.i_ξ then -mη u else mη u
  have hp1c : ContinuousOn p₁ (Icc 0 1) := by cases hfl : flip st.i_ξ <;> simp only [p₁, hfl, Bool.false_eq_true, ↓reduceIte]; exact hmξc; exact hmξc.neg
  have hp2c : ContinuousOn p₂ (Icc 0 1) := by cases hfl : flip st.i_ξ <;> simp only [p₂, hfl, Bool.false_eq_true, ↓reduceIte]; exact hmηc; exact hmηc.neg
  have hp1e : ∀ u ∈ Icc (0 : ℝ) 1, (φ' st.j_ξ0 (ee (p₁ u))).1 = H₀ (ξ u) := fun u hu => by
    rw [← hmξe u hu, hH₀ st.i_ξ (ee (mξ u)), hπ_cut]
    cases hfl : flip st.i_ξ <;> simp only [p₁, hfl, Bool.false_eq_true, ↓reduceIte]
    · rfl
    · rw [show ee (-mξ u) = (ee (mξ u))⁻¹ by unfold ee; rw [mul_neg, Circle.exp_neg]]
  have hp2e : ∀ u ∈ Icc (0 : ℝ) 1, (φ' st.j_ξ0 (ee (p₂ u))).1 = H₀ (η u) := fun u hu => by
    rw [← hmηe u hu, hH₀ st.i_ξ (ee (mη u)), hπ_cut]
    cases hfl : flip st.i_ξ <;> simp only [p₂, hfl, Bool.false_eq_true, ↓reduceIte]
    · rfl
    · rw [show ee (-mη u) = (ee (mη u))⁻¹ by unfold ee; rw [mul_neg, Circle.exp_neg]]
  have hp1d : if d₁' then StrictMonoOn p₁ (Icc 0 1) else StrictAntiOn p₁ (Icc 0 1) := strictMono_flip_dir hfl_cut hmξ_d
  have hp2d : if d₁' then StrictMonoOn p₂ (Icc 0 1) else StrictAntiOn p₂ (Icc 0 1) := strictMono_flip_dir hfl_cut hmη_d
  let sw : Bool := (xor g1Y (flip st.i_ξ)) != g1Y'
  let ξ₀' : ℝ → Y' := if sw then η' else ξ'
  let η₀' : ℝ → Y' := if sw then ξ' else η'
  let X₀' : Set Y' := if sw then X₂' else X₂
  let X₀'' : Set Y' := if sw then X₂ else X₂'
  let q₁ : ℝ → ℝ := if sw then mη' else mξ'
  let q₂ : ℝ → ℝ := if sw then mξ' else mη'
  have hP₀' : LiftPair ψ' F' s t X₀' X₀'' := by
    cases hsw : sw <;> simp only [X₀', X₀'', hsw, Bool.false_eq_true, ↓reduceIte]
    · exact hP'
    · obtain ⟨x0, x1, y0, y1, l1, l2, hd0, hun0, b1, b2, h7, h8, h9, h10⟩ := id hP'
      exact ⟨y0, y1, x0, x1, l2, l1, hd0.symm, by rw [union_comm]; exact hun0, b2, b1, h8, h7, h10, h9⟩
  have L₀' : ArcLift ψ' F' a' ξ₀' η₀' := by cases hsw : sw <;> simp only [ξ₀', η₀', hsw, Bool.false_eq_true, ↓reduceIte]; exact L'; exact L'.swap
  have him₁' : ξ₀' '' Icc 0 1 = X₀' := by cases hsw : sw <;> simp only [ξ₀', X₀', hsw, Bool.false_eq_true, ↓reduceIte] <;> assumption
  have him₂' : η₀' '' Icc 0 1 = X₀'' := by cases hsw : sw <;> simp only [η₀', X₀'', hsw, Bool.false_eq_true, ↓reduceIte] <;> assumption
  have hi₁' : InjOn ξ₀' (Icc 0 1) := by cases hsw : sw <;> simp only [ξ₀', hsw, Bool.false_eq_true, ↓reduceIte] <;> assumption
  have hi₂' : InjOn η₀' (Icc 0 1) := by cases hsw : sw <;> simp only [η₀', hsw, Bool.false_eq_true, ↓reduceIte] <;> assumption
  have hq1c : ContinuousOn q₁ (Icc 0 1) := by cases hsw : sw <;> simp only [q₁, hsw, Bool.false_eq_true, ↓reduceIte] <;> assumption
  have hq2c : ContinuousOn q₂ (Icc 0 1) := by cases hsw : sw <;> simp only [q₂, hsw, Bool.false_eq_true, ↓reduceIte] <;> assumption
  have hq1d : if d₁' then StrictMonoOn q₁ (Icc 0 1) else StrictAntiOn q₁ (Icc 0 1) := by cases hsw : sw <;> simp only [q₁, hsw, Bool.false_eq_true, ↓reduceIte] <;> assumption
  have hq2d : if d₁' then StrictMonoOn q₂ (Icc 0 1) else StrictAntiOn q₂ (Icc 0 1) := by cases hsw : sw <;> simp only [q₂, hsw, Bool.false_eq_true, ↓reduceIte] <;> assumption
  have hq1e : ∀ u ∈ Icc (0 : ℝ) 1, (φ' st.j_ξ0 (ee (q₁ u))).1 = ξ₀' u := by cases hsw : sw <;> simp only [q₁, ξ₀', hsw, Bool.false_eq_true, ↓reduceIte] <;> assumption
  have hq2e : ∀ u ∈ Icc (0 : ℝ) 1, (φ' st.j_ξ0 (ee (q₂ u))).1 = η₀' u := by cases hsw : sw <;> simp only [q₂, η₀', hsw, Bool.false_eq_true, ↓reduceIte] <;> assumption
  have hdj_p : ∀ u ∈ Icc (0 : ℝ) 1, ∀ v ∈ Icc (0 : ℝ) 1, ee (p₁ u) ≠ ee (p₂ v) := fun u hu v hv he => by
    have h1 : H₀ (ξ u) = H₀ (η v) := by rw [← hp1e u hu, ← hp2e v hv, he]
    exact Set.disjoint_left.mp hd (himξ ▸ ⟨u, hu, rfl⟩) (H₀.injective h1 ▸ show η v ∈ X' from himη ▸ ⟨v, hv, rfl⟩)
  have hdj_q : ∀ u ∈ Icc (0 : ℝ) 1, ∀ v ∈ Icc (0 : ℝ) 1, ee (q₁ u) ≠ ee (q₂ v) := fun u hu v hv he => by
    have h1 : ξ₀' u = η₀' v := by rw [← hq1e u hu, ← hq2e v hv, he]
    have hd0 : Disjoint X₀' X₀'' := by cases hsw : sw <;> simp only [X₀', X₀'', hsw, Bool.false_eq_true, ↓reduceIte]; exact hd'; exact hd'.symm
    exact Set.disjoint_left.mp hd0 (him₁' ▸ ⟨u, hu, rfl⟩) (h1 ▸ show η₀' v ∈ X₀'' from him₂' ▸ ⟨v, hv, rfl⟩)
  obtain ⟨M, hM1, hM2, hM_fix, kM, hkMp, hkMe⟩ := exists_align_two_arcs_any hY' (hC'_cuff st.j_ξ0) (φ' st.j_ξ0) d₁' d₁'
    hp1c hp2c hq1c hq2c hp1d hp2d hq1d hq2d
    (inj_of_lift hp1e (fun a ha b hb he => hiξ ha hb (H₀.injective he)))
    (inj_of_lift hp2e (fun a ha b hb he => hiη ha hb (H₀.injective he)))
    (inj_of_lift hq1e hi₁') (inj_of_lift hq2e hi₂') hdj_p hdj_q
  let H : Y ≃ₜ Y' := H₀.trans M
  have hHξ : ∀ u ∈ Icc (0 : ℝ) 1, H (ξ u) = ξ₀' u := fun u hu => by
    simp only [H, Homeomorph.trans_apply]; rw [← hp1e u hu, hM1 u hu, hq1e u hu]
  have hHη : ∀ u ∈ Icc (0 : ℝ) 1, H (η u) = η₀' u := fun u hu => by
    simp only [H, Homeomorph.trans_apply]; rw [← hp2e u hu, hM2 u hu, hq2e u hu]
  obtain ⟨α, hα_comm, hαF⟩ := exists_descend_of_lifts hψ hψ' L L₀' hP hP₀' himξ himη him₁' him₂' H hHξ hHη
  have hαs : α s = s := by
    have := hα_comm (ξ 0)
    rw [L.hξ 0 ⟨le_rfl, zero_le_one⟩, ha0, hHξ 0 ⟨le_rfl, zero_le_one⟩, L₀'.hξ 0 ⟨le_rfl, zero_le_one⟩, ha'0] at this; exact this
  have hαt : α t = t := by
    have := hα_comm (ξ 1)
    rw [L.hξ 1 ⟨zero_le_one, le_rfl⟩, ha1, hHξ 1 ⟨zero_le_one, le_rfl⟩, L₀'.hξ 1 ⟨zero_le_one, le_rfl⟩, ha'1] at this; exact this
  have hnull : HasNullSignature α := fun D φD hD => by
    by_cases hDCs : D = connectedComponentIn (bd S) s
    · subst hDCs
      have hαCs : ∀ x, x ∈ connectedComponentIn (bd S) s ↔ α x ∈ connectedComponentIn (bd S) s := fun x => by
        have h1 : α '' connectedComponentIn (bd S) s = connectedComponentIn (bd S) s := by
          rw [α.image_connectedComponentIn hsb, image_bd_homeomorph α, hαs]
        exact ⟨fun hx => h1 ▸ mem_image_of_mem α hx, fun hαx => by obtain ⟨z, hz, hzα⟩ := h1.symm.subset hαx; rwa [α.injective hzα] at hz⟩
      let k0 : Circle ≃ₜ Circle := if flip st.i_ξ then Homeomorph.inv Circle else Homeomorph.refl Circle
      let kH : Circle ≃ₜ Circle := k0.trans kM
      have hkH_eq : ∀ z : Circle, H (φ st.i_ξ z).1 = (φ' st.j_ξ0 (kH z)).1 := fun z => by
        simp only [H, kH, Homeomorph.trans_apply]
        have h1 : H₀ (φ st.i_ξ z).1 = (φ' st.j_ξ0 (k0 z)).1 := by
          have h := hH₀ st.i_ξ z
          change H₀ (φ st.i_ξ z).1 = (φ' (π st.i_ξ) _).1 at h
          rw [hπ_cut] at h
          cases hfl : flip st.i_ξ <;> simp only [k0, hfl, Bool.false_eq_true, ↓reduceIte] at h ⊢ <;> exact h
        rw [h1, hkMe (k0 z)]
      have hkH_or : if !flip st.i_ξ then PreservesCircleOrientation kH
          else PreservesCircleOrientation ((Homeomorph.inv Circle).trans kH) := by
        cases hfl : flip st.i_ξ <;> simp only [kH, k0, hfl, Bool.not_false, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
        · exact preservesCircleOrientation_trans preservesCircleOrientation_refl hkMp
        · have : (Homeomorph.inv Circle).trans ((Homeomorph.inv Circle).trans kM) = kM := Homeomorph.ext fun z => by simp
          rw [this]; exact hkMp
      obtain ⟨w₁', -, hw₁'e⟩ := exists_param (kH (ee v₁))
      have hw₁'y : (φ' st.j_ξ0 (ee w₁')).1 = H y₁ := by rw [hw₁'e, ← hkH_eq, hv₁y]
      have hw₁'nF' : ψ' (φ' st.j_ξ0 (ee w₁')).1 ∉ F' := by
        rw [hw₁'y, ← hα_comm y₁, hψy₁]; intro hF'; obtain ⟨z, hzF, hzα⟩ := hαF.symm.subset hF'
        exact hx₁nF (α.injective hzα ▸ hzF)
      have hw₁'Cs : ψ' (φ' st.j_ξ0 (ee w₁')).1 ∈ connectedComponentIn (bd S) s := by
        rw [hw₁'y, ← hα_comm y₁, hψy₁]; exact (hαCs x₁).mp hx₁_diff.1
      obtain ⟨δa, ma, da, hδa, _, hmac, hmad, hmae, hsig_a⟩ :=
        exists_cuff_local_dir hY hS hψ hF st.AY AS (hC_bd st.i_ξ) hCs_cuff (φ st.i_ξ) φD (by rw [hv₁y, hψy₁]; exact hx₁_diff.1) (by rw [hv₁y, hψy₁]; exact hx₁nF)
      obtain ⟨δb, mb, db, hδb, _, hmbc, hmbd, hmbe, hsig_b⟩ :=
        exists_cuff_local_dir hY' hS hψ' hF' st.AY' AS (hC'_bd st.j_ξ0) hCs_cuff (φ' st.j_ξ0) φD hw₁'Cs hw₁'nF'
      obtain ⟨δbS, mbS, dbS, hδbS, _, hmbSc, hmbSd, hmbSe, hsig_bS⟩ :=
        exists_cuff_local_dir hY' hS hψ' hF' st.AY' AS (hC'_bd st.j_ξ0) hCs_cuff (φ' st.j_ξ0) φS hw₁'Cs hw₁'nF'
      -- Show `ψ' (φ' st.j_ξ0 (ee w₁')).1 ∈ G₁`:
      have hHy₁_G₁ : ψ' (φ' st.j_ξ0 (ee w₁')).1 ∈ G₁ := by
        obtain ⟨lH, hlHc, hlHm, hlHe, hlH_per⟩ := circle_lift_of_orient (!flip st.i_ξ) hkH_or
        obtain ⟨h12Y, hsp1Y, h34Y, hsp2Y, _, _, hhitY⟩ := hgY_info
        obtain ⟨h12Y', hsp1Y', h34Y', hsp2Y', _, _, hhitY'⟩ := hgY'_info
        have hcheck_gap : ∀ {pY qY pY' qY' : ℝ}, pY < qY → qY - pY < 1 → pY' < qY' → qY' - pY' < 1 →
            (∀ v ∈ Ioo pY' qY', ψ' (φ' st.j_ξ0 (ee v)).1 ∈ G₁) →
            (∃ v ∈ Ioo pY qY, ee v = ee v₁) →
            (if !flip st.i_ξ then kH (ee pY) = ee pY' ∧ kH (ee qY) = ee qY'
             else kH (ee qY) = ee pY' ∧ kH (ee pY) = ee qY') →
            ψ' (φ' st.j_ξ0 (ee w₁')).1 ∈ G₁ := by
          intro pY qY pY' qY' hpqY hspY hpqY' hspY' hG1Y' ⟨vY, hvY, hvYe⟩ hends
          set lo := if !flip st.i_ξ then lH pY else lH qY
          set hi := if !flip st.i_ξ then lH qY else lH pY
          have hlo_lt : lo < hi := by
            cases hfl : flip st.i_ξ <;> simp only [lo, hi, hfl, Bool.not_false, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hlHm ⊢ <;> exact hlHm hpqY
          have hspan_lh : hi - lo < 1 := by
            cases hfl : flip st.i_ξ <;> simp only [lo, hi, hfl, Bool.not_false, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hlHm hlH_per ⊢
            · have h1 := hlHm (show qY < pY + 1 by linarith); rw [hlH_per pY] at h1; linarith
            · have h1 := hlHm (show qY < pY + 1 by linarith); rw [hlH_per pY] at h1; linarith
          have hlo_e : ee lo = ee pY' := by
            cases hfl : flip st.i_ξ <;> simp only [lo, hfl, Bool.not_false, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hends ⊢ <;> rw [← hlHe, hends.1]
          have hhi_e : ee hi = ee qY' := by
            cases hfl : flip st.i_ξ <;> simp only [hi, hfl, Bool.not_false, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hends ⊢ <;> rw [← hlHe, hends.2]
          obtain ⟨k1, hk1⟩ := ee_eq_iff.mp hlo_e
          obtain ⟨k2, hk2⟩ := ee_eq_iff.mp hhi_e
          have hk12 : k1 = k2 := by
            have hdiff : |(k2 - k1 : ℝ)| < 1 := by rw [abs_lt]; exact ⟨by linarith [hlo_lt, hspY'], by linarith [hspan_lh, hpqY']⟩
            have := abs_lt.mp (show |k2 - k1| < 1 by exact_mod_cast hdiff)
            omega
          subst hk12
          have hv_in : lH vY ∈ Ioo lo hi := by
            cases hfl : flip st.i_ξ <;> simp only [lo, hi, hfl, Bool.not_false, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hlHm ⊢
            · exact ⟨hlHm hvY.1, hlHm hvY.2⟩
            · exact ⟨hlHm hvY.2, hlHm hvY.1⟩
          have hee_eq : ee w₁' = ee (lH vY - k1) := by rw [hw₁'e, ← hvYe, hlHe]; exact ee_eq_iff.mpr ⟨k1, by ring⟩
          rw [hee_eq]; exact hG1Y' _ ⟨by linarith [hv_in.1], by linarith [hv_in.2]⟩
        have hH_xi : ∀ u ∈ Icc (0 : ℝ) 1, kH (ee (mξ u)) = ee (if sw then mη' u else mξ' u) := fun u hu =>
          (φ' st.j_ξ0).injective (Subtype.ext (by rw [← hkH_eq, hmξe u hu, hHξ u hu, ← hq1e u hu]; cases hsw : sw <;> simp [q₁, hsw]))
        have hH_eta : ∀ u ∈ Icc (0 : ℝ) 1, kH (ee (mη u)) = ee (if sw then mξ' u else mη' u) := fun u hu =>
          (φ' st.j_ξ0).injective (Subtype.ext (by rw [← hkH_eq, hmηe u hu, hHη u hu, ← hq2e u hu]; cases hsw : sw <;> simp [q₂, hsw]))
        have hshift : ∀ r (k : ℤ), ee (r + k) = ee r := fun r k => ee_eq_iff.mpr ⟨k, rfl⟩
        have hxi0 := hH_xi 0 ⟨le_rfl, zero_le_one⟩
        have hxi1 := hH_xi 1 ⟨zero_le_one, le_rfl⟩
        have heta0 := hH_eta 0 ⟨le_rfl, zero_le_one⟩
        have heta1 := hH_eta 1 ⟨zero_le_one, le_rfl⟩
        have hd1'_eq : d₁' = xor d₁ (flip st.i_ξ) := bool_eq_xor_of_not_eq_beq hfl_cut
        -- Split on `(flip st.i_ξ, g1Y, g1Y', d₁)` — clean 16 cases, each closed in 1 line!
        cases hfl : flip st.i_ξ
        · simp only [hfl, Bool.xor_false] at hd1'_eq; subst d₁'
          cases g1Y <;> cases g1Y' <;> cases d₁ <;>
            simp only [sw, hfl, Bool.xor_false, Bool.bne_true,
              Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h12Y hsp1Y h34Y hsp2Y hhitY h12Y' hsp1Y' h34Y' hsp2Y' hhitY' hxi0 hxi1 heta0 heta1
          · exact hcheck_gap h34Y hsp2Y h34Y' hsp2Y' hhitY'.2 hhitY.1 (by simp only [hfl, Bool.not_false, ↓reduceIte]; exact ⟨by simpa [hshift] using heta0, by simpa [ee_add_one] using hxi1⟩)
          · exact hcheck_gap h34Y hsp2Y h34Y' hsp2Y' hhitY'.2 hhitY.1 (by simp only [hfl, Bool.not_false, ↓reduceIte]; exact ⟨by simpa [hshift] using heta1, by simpa [ee_add_one] using hxi0⟩)
          · exact hcheck_gap h34Y hsp2Y h12Y' hsp1Y' hhitY'.2 hhitY.1 (by simp only [hfl, Bool.not_false, ↓reduceIte]; exact ⟨by simpa [hshift] using heta0, by simpa [hshift, ee_add_one] using hxi1⟩)
          · exact hcheck_gap h34Y hsp2Y h12Y' hsp1Y' hhitY'.2 hhitY.1 (by simp only [hfl, Bool.not_false, ↓reduceIte]; exact ⟨by simpa [hshift] using heta1, by simpa [hshift, ee_add_one] using hxi0⟩)
          · exact hcheck_gap h12Y hsp1Y h34Y' hsp2Y' hhitY'.2 hhitY.1 (by simp only [hfl, Bool.not_false, ↓reduceIte]; exact ⟨by simpa [hshift] using hxi0, by simpa [hshift, ee_add_one] using heta1⟩)
          · exact hcheck_gap h12Y hsp1Y h34Y' hsp2Y' hhitY'.2 hhitY.1 (by simp only [hfl, Bool.not_false, ↓reduceIte]; exact ⟨by simpa [hshift] using hxi1, by simpa [hshift, ee_add_one] using heta0⟩)
          · exact hcheck_gap h12Y hsp1Y h12Y' hsp1Y' hhitY'.2 hhitY.1 (by simp only [hfl, Bool.not_false, ↓reduceIte]; exact ⟨hxi0, by simpa [hshift] using heta1⟩)
          · exact hcheck_gap h12Y hsp1Y h12Y' hsp1Y' hhitY'.2 hhitY.1 (by simp only [hfl, Bool.not_false, ↓reduceIte]; exact ⟨hxi1, by simpa [hshift] using heta0⟩)
        · simp only [hfl, Bool.xor_true] at hd1'_eq; subst d₁'
          cases g1Y <;> cases g1Y' <;> cases d₁ <;>
            simp only [sw, hfl, Bool.xor_true, Bool.bne_false,
              Bool.not_false, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h12Y hsp1Y h34Y hsp2Y hhitY h12Y' hsp1Y' h34Y' hsp2Y' hhitY' hxi0 hxi1 heta0 heta1
          · exact hcheck_gap h34Y hsp2Y h34Y' hsp2Y' hhitY'.2 hhitY.1 (by simp only [hfl, Bool.not_true, Bool.false_eq_true, ↓reduceIte]; exact ⟨by simpa [hshift, ee_add_one] using hxi1, by simpa [hshift, ee_add_one] using heta0⟩)
          · exact hcheck_gap h34Y hsp2Y h34Y' hsp2Y' hhitY'.2 hhitY.1 (by simp only [hfl, Bool.not_true, Bool.false_eq_true, ↓reduceIte]; exact ⟨by simpa [hshift, ee_add_one] using hxi0, by simpa [hshift, ee_add_one] using heta1⟩)
          · exact hcheck_gap h34Y hsp2Y h12Y' hsp1Y' hhitY'.2 hhitY.1 (by simp only [hfl, Bool.not_true, Bool.false_eq_true, ↓reduceIte]; exact ⟨by simpa [ee_add_one] using hxi1, by simpa [hshift] using heta0⟩)
          · exact hcheck_gap h34Y hsp2Y h12Y' hsp1Y' hhitY'.2 hhitY.1 (by simp only [hfl, Bool.not_true, Bool.false_eq_true, ↓reduceIte]; exact ⟨by simpa [ee_add_one] using hxi0, by simpa [hshift] using heta1⟩)
          · exact hcheck_gap h12Y hsp1Y h34Y' hsp2Y' hhitY'.2 hhitY.1 (by simp only [hfl, Bool.not_true, Bool.false_eq_true, ↓reduceIte]; exact ⟨by simpa [hshift] using heta1, by simpa [ee_add_one] using hxi0⟩)
          · exact hcheck_gap h12Y hsp1Y h34Y' hsp2Y' hhitY'.2 hhitY.1 (by simp only [hfl, Bool.not_true, Bool.false_eq_true, ↓reduceIte]; exact ⟨by simpa [hshift] using heta0, by simpa [ee_add_one] using hxi1⟩)
          · exact hcheck_gap h12Y hsp1Y h12Y' hsp1Y' hhitY'.2 hhitY.1 (by simp only [hfl, Bool.not_true, Bool.false_eq_true, ↓reduceIte]; exact ⟨by simpa [hshift] using heta1, by simpa [hshift] using hxi0⟩)
          · exact hcheck_gap h12Y hsp1Y h12Y' hsp1Y' hhitY'.2 hhitY.1 (by simp only [hfl, Bool.not_true, Bool.false_eq_true, ↓reduceIte]; exact ⟨by simpa [hshift] using heta0, by simpa [hshift] using hxi1⟩)
      -- Deduce `dbS = d₁'` from `hHy₁_G₁`:
      have hdbS_eq : dbS = d₁' := by
        obtain ⟨h12Y', hsp1Y', h34Y', hsp2Y', hoff1Y', hoff2Y', _⟩ := hgY'_info
        set p₁' := if d₁' then mξ' 1 else mξ' 0
        set q₁' := if d₁' then mη' 0 + kY' else mη' 1 + kY'
        set p₂' := if d₁' then mη' 1 + kY' else mη' 0 + kY'
        set q₂' := if d₁' then mξ' 0 + 1 else mξ' 1 + 1
        set a₀' := if d₁' then mξ' 0 else mξ' 1
        set w_s := a₀' + Int.fract (w₁' - a₀')
        have hws_ee : ee w_s = ee w₁' := ee_eq_iff.mpr ⟨-⌊w₁' - a₀'⌋, by simp only [w_s, Int.cast_neg]; linarith [Int.floor_add_fract (w₁' - a₀')]⟩
        have hws_lo : a₀' ≤ w_s := by simp only [w_s]; linarith [Int.fract_nonneg (w₁' - a₀')]
        have hws_hi : w_s < q₂' := by have : q₂' = a₀' + 1 := by cases d₁' <;> rfl
                                      rw [this]; simp only [w_s]; linarith [Int.fract_lt_one (w₁' - a₀')]
        have hws_gt1 : p₁' < w_s := by
          by_contra hle'
          have hmem : w_s ∈ Icc (mξ' 0) (mξ' 1) ∨ w_s ∈ Icc (mξ' 1) (mξ' 0) := by
            cases d₁' <;> simp only [p₁', a₀', Bool.false_eq_true, ↓reduceIte] at hws_lo hle'
            · exact .inr ⟨hws_lo, not_lt.mp hle'⟩
            · exact .inl ⟨hws_lo, not_lt.mp hle'⟩
          obtain ⟨u, hu, hue⟩ : ∃ u ∈ Icc (0 : ℝ) 1, mξ' u = w_s :=
            hmem.elim (fun h => intermediate_value_Icc zero_le_one hmξ'c h) (fun h => intermediate_value_Icc' zero_le_one hmξ'c h)
          exact hw₁'nF' (by rw [← hws_ee, ← hue, hmξ'e u hu]; exact show ξ' u ∈ ψ' ⁻¹' F' from hun' ▸ Or.inl (himξ' ▸ ⟨u, hu, rfl⟩))
        have hws_not2 : w_s ∉ Icc q₁' p₂' := fun hmem => by
          have hmem' : w_s - kY' ∈ Icc (mη' 0) (mη' 1) ∨ w_s - kY' ∈ Icc (mη' 1) (mη' 0) := by
            cases d₁' <;> simp only [q₁', p₂', Bool.false_eq_true, ↓reduceIte] at hmem
            · exact .inr ⟨by linarith [hmem.1], by linarith [hmem.2]⟩
            · exact .inl ⟨by linarith [hmem.1], by linarith [hmem.2]⟩
          obtain ⟨u, hu, hue⟩ : ∃ u ∈ Icc (0 : ℝ) 1, mη' u = w_s - kY' :=
            hmem'.elim (fun h => intermediate_value_Icc zero_le_one hmη'c h) (fun h => intermediate_value_Icc' zero_le_one hmη'c h)
          have heee : ee w₁' = ee (mη' u) := hws_ee.symm.trans (ee_eq_iff.mpr ⟨kY', by linarith⟩)
          exact hw₁'nF' (by rw [heee, hmη'e u hu]; exact show η' u ∈ ψ' ⁻¹' F' from hun' ▸ Or.inr (himη' ▸ ⟨u, hu, rfl⟩))
        have hmbS_ws : ∀ r ∈ Icc (-δbS) δbS, ψ' (φ' st.j_ξ0 (ee (w_s + r))).1 = (φS (ee (mbS r))).1 := fun r hr => by
          obtain ⟨j, hj⟩ := ee_eq_iff.mp hws_ee
          rw [show ee (w_s + r) = ee (w₁' + r) from ee_eq_iff.mpr ⟨j, by linarith⟩]; exact hmbSe r hr
        have hG1_ends : (φS (ee u_t)).1 ∈ ({s, t} : Set S) ∧ (φS (ee (u_s + 1))).1 ∈ ({s, t} : Set S) ∧ (φS (ee u_t)).1 ≠ (φS (ee (u_s + 1))).1 := by
          rw [hut, ee_add_one, hus]; exact ⟨mem_insert_of_mem _ rfl, mem_insert _ _, hne.symm⟩
        by_cases hws_g1 : w_s < q₁'
        · have hps : (ψ' (φ' st.j_ξ0 (ee p₁')).1 = (φS (ee (if d₁' then u_t else u_s))).1) ∧
              (ψ' (φ' st.j_ξ0 (ee q₁')).1 = (φS (ee (if d₁' then u_s + 1 else u_t))).1) := by
            cases d₁' <;> simp only [p₁', q₁', Bool.false_eq_true, ↓reduceIte, ee_add_one]
            · exact ⟨by rw [hmξ'e 0 ⟨le_rfl, zero_le_one⟩, L'.hξ 0 ⟨le_rfl, zero_le_one⟩, ha'0, hus],
                     by rw [ee_eq_iff.mpr ⟨kY', rfl⟩, hmη'e 1 ⟨zero_le_one, le_rfl⟩, L'.hη 1 ⟨zero_le_one, le_rfl⟩, ha'1, hut]⟩
            · exact ⟨by rw [hmξ'e 1 ⟨zero_le_one, le_rfl⟩, L'.hξ 1 ⟨zero_le_one, le_rfl⟩, ha'1, hut],
                     by rw [ee_eq_iff.mpr ⟨kY', rfl⟩, hmη'e 0 ⟨le_rfl, zero_le_one⟩, L'.hη 0 ⟨le_rfl, zero_le_one⟩, ha'0, hus]⟩
          have hg := gap_into_G_of_hit hY' hS hψ' hF' hb' hst φS (hC'_bd st.j_ξ0) (φ' st.j_ξ0) h12Y' hoff1Y'
            (by cases d₁' <;> simp only [Bool.false_eq_true, ↓reduceIte, ee_add_one, hus, hut] at hps <;> [exact .inl hps; exact .inr hps])
            hu2 (by linarith) hG1_ends ⟨w_s, ⟨hws_gt1, hws_g1⟩, by rw [hws_ee]; exact hHy₁_G₁⟩
          have hgd := gap_dir_eq hψ' (φ' st.j_ξ0) φS hu2 (by linarith) h12Y' hsp1Y' hoff1Y' hg ⟨hws_gt1, hws_g1⟩ hδbS hmbSc hmbSd hmbS_ws
          cases d₁' <;> simp only [Bool.false_eq_true, ↓reduceIte] at hps
          · exact hgd.2 ⟨by rw [hps.1, ee_add_one], hps.2⟩
          · exact hgd.1 hps
        · have hws_gt2 : p₂' < w_s := lt_of_not_ge fun hle' => hws_not2 ⟨not_lt.mp hws_g1, hle'⟩
          have hps : (ψ' (φ' st.j_ξ0 (ee p₂')).1 = (φS (ee (if d₁' then u_t else u_s))).1) ∧
              (ψ' (φ' st.j_ξ0 (ee q₂')).1 = (φS (ee (if d₁' then u_s + 1 else u_t))).1) := by
            cases d₁' <;> simp only [p₂', q₂', Bool.false_eq_true, ↓reduceIte, ee_add_one]
            · exact ⟨by rw [ee_eq_iff.mpr ⟨kY', rfl⟩, hmη'e 0 ⟨le_rfl, zero_le_one⟩, L'.hη 0 ⟨le_rfl, zero_le_one⟩, ha'0, hus],
                     by rw [hmξ'e 1 ⟨zero_le_one, le_rfl⟩, L'.hξ 1 ⟨zero_le_one, le_rfl⟩, ha'1, hut]⟩
            · exact ⟨by rw [ee_eq_iff.mpr ⟨kY', rfl⟩, hmη'e 1 ⟨zero_le_one, le_rfl⟩, L'.hη 1 ⟨zero_le_one, le_rfl⟩, ha'1, hut],
                     by rw [hmξ'e 0 ⟨le_rfl, zero_le_one⟩, L'.hξ 0 ⟨le_rfl, zero_le_one⟩, ha'0, hus]⟩
          have hg := gap_into_G_of_hit hY' hS hψ' hF' hb' hst φS (hC'_bd st.j_ξ0) (φ' st.j_ξ0) h34Y' hoff2Y'
            (by cases d₁' <;> simp only [Bool.false_eq_true, ↓reduceIte, ee_add_one, hus, hut] at hps <;> [exact .inl hps; exact .inr hps])
            hu2 (by linarith) hG1_ends ⟨w_s, ⟨hws_gt2, hws_hi⟩, by rw [hws_ee]; exact hHy₁_G₁⟩
          have hgd := gap_dir_eq hψ' (φ' st.j_ξ0) φS hu2 (by linarith) h34Y' hsp2Y' hoff2Y' hg ⟨hws_gt2, hws_hi⟩ hδbS hmbSc hmbSd hmbS_ws
          cases d₁' <;> simp only [Bool.false_eq_true, ↓reduceIte] at hps
          · exact hgd.2 ⟨by rw [hps.1, ee_add_one], hps.2⟩
          · exact hgd.1 hps
      have hdab : (da == db) = (d₁ == d₁') := by
        let kSD : Circle ≃ₜ Circle := φD.trans φS.symm
        have hcs_const : ∀ x ∈ connectedComponentIn (bd S) s,
            cuffSign AS φD x - cuffSign AS φS x = if PreservesCircleOrientation kSD then 0 else 1 := fun x hx => by
          have h1 := cuffSign_comp_circle AS (connectedComponentIn_subset _ _) φS kSD hx
          have : φD = kSD.trans φS := Homeomorph.ext fun z => by simp [kSD]
          rw [this, h1]; ring
        have hsub1 : (if da then (0 : ZMod 2) else 1) - (if d₁ then 0 else 1) = if PreservesCircleOrientation kSD then 0 else 1 := by
          have h1 := cutOrientDiff_cuff_mono hY hS hψ hF st.AY AS (hC_bd st.i_ξ) (connectedComponentIn_subset _ _)
            (φ st.i_ξ) φS (φ st.i_ξ _).2 (by rw [hv₁y, hψy₁]; exact hx₁nF) hδ₁ d₁ hm₁lc hm₁ld hm₁le rfl
          have h2 := hcs_const (ψ (φ st.i_ξ (ee v₁)).1) (by rw [hv₁y, hψy₁]; exact hx₁_diff.1); linear_combination h1 + h2 - hsig_a
        have hsub2 : (if db then (0 : ZMod 2) else 1) - (if dbS then 0 else 1) = if PreservesCircleOrientation kSD then 0 else 1 := by
          have h2 := hcs_const _ hw₁'Cs; linear_combination hsig_bS + h2 - hsig_b
        exact bool_beq_of_zmod2_sub_eq (by rw [← hdbS_eq]; linear_combination hsub1 - hsub2)
      exact preservesCircleOrientation_of_local_dirs hα_comm hαCs φD (φ st.i_ξ) (φ' st.j_ξ0) (!flip st.i_ξ) hkH_or hkH_eq
        hw₁'e.symm hδa hδb hmac hmbc hmad hmbd hmae hmbe (by rw [hdab]; exact hfl_cut)
    · have hsD : s ∉ D := fun hs => hDCs (by by_contra hne'; exact Set.disjoint_left.mp (cuffs_disjoint hD hCs_cuff hne') hs (mem_connectedComponentIn hsb))
      have htD : t ∉ D := fun ht => hDCs (by by_contra hne'; exact Set.disjoint_left.mp (cuffs_disjoint hD hCs_cuff hne') ht (hst ▸ mem_connectedComponentIn (show t ∈ bd S from (show t ∈ F ∩ bd S from hb ▸ mem_insert_of_mem _ rfl).2)))
      obtain ⟨hpre_cuff, hpre_disj, him⟩ := untouched_cuff_preimage hY hS hψ hF hb hD hsD htD
      obtain ⟨i, hi_lt, hi_eq'⟩ := (cuffs_eq_holeC st.hf).subset hpre_cuff
      let iF : Fin st.c₀ := ⟨i, hi_lt⟩
      have hξ0 : ξ 0 ∈ X := himξ ▸ ⟨0, ⟨le_rfl, zero_le_one⟩, rfl⟩
      have hi_ne : iF ≠ st.i_ξ := fun he =>
        Set.disjoint_left.mp hpre_disj (by rw [← hi_eq', show holeC st.a₀ st.b₀ st.c₀ st.f i = C iF from rfl, he]; exact st.hXC hξ0) (show ξ 0 ∈ ψ ⁻¹' F from hun ▸ Or.inl hξ0)
      have hDeq : ψ '' C iF = D := by rw [show C iF = holeC st.a₀ st.b₀ st.c₀ st.f i from rfl, hi_eq']; exact him
      subst hDeq
      have huY := untouched_cuff_properties hS hY hψ hF hb hP st.hf st.hXC st.hX'C hi_ne (hi_eq ▸ hi_ne)
      have huY' := untouched_cuff_properties hS hY' hψ' hF' hb' hP' st.hf' st.hX2C st.hX2'C (hπ_unt iF hi_ne).1 (hj_eq ▸ (hπ_unt iF hi_ne).1)
      exact untouched_cuff_null hS hY hY' AS st.AY st.AY' hψ hψ' hF hF' st.hf st.hf'
        huY.1 huY'.1 huY.2.1 huY'.2.2.2.2 (hπ_unt iF hi_ne).2 H (flip iF)
        (fun z => by
          simp only [H, Homeomorph.trans_apply, hH₀ iF z]
          exact hM_fix (C' (π iF)) (hC'_cuff (π iF)) (fun he => (hπ_unt iF hi_ne).1 (hC'_inj he)) _ (φ' (π iF) _).2)
        (hfl_unt iF hi_ne) α hα_comm φD
  exact parallel_conn hS hne hb' hl' hαF hαs hαt hnull

end CaseSame1Sided

/-! ### Case 3: Same cuff `C_s = C_t`, 2-sided (`C_ξ ≠ C_η`) -/

section CaseSame2Sided

variable {S Y Y' : Type u} [TopologicalSpace S] [TopologicalSpace Y] [T2Space Y]
  [TopologicalSpace Y'] [T2Space Y']

private theorem parallel_case_2sided [ConnectedSpace S] [ConnectedSpace Y] [ConnectedSpace Y']
    (hS : IsSurface S) (hY : IsSurface Y) (hY' : IsSurface Y')
    {F F' : Set S} {s t : S} (hne : s ≠ t)
    (hb : F ∩ bd S = {s, t}) (hb' : F' ∩ bd S = {s, t})
    (hl : IsLineWithEnds F s t) (hl' : IsLineWithEnds F' s t)
    {ψ : Y → S} {ψ' : Y' → S} (hψ : IsCutting ψ F) (hψ' : IsCutting ψ' F')
    {X X' : Set Y} {X₂ X₂' : Set Y'}
    (hP : LiftPair ψ F s t X X') (hP' : LiftPair ψ' F' s t X₂ X₂')
    {a a' : ℝ → S} {ξ η : ℝ → Y} {ξ' η' : ℝ → Y'}
    (L : ArcLift ψ F a ξ η) (L' : ArcLift ψ' F' a' ξ' η')
    (ha0 : a 0 = s) (ha1 : a 1 = t) (ha'0 : a' 0 = s) (ha'1 : a' 1 = t)
    (himξ : ξ '' Icc 0 1 = X) (himη : η '' Icc 0 1 = X')
    (himξ' : ξ' '' Icc 0 1 = X₂) (himη' : η' '' Icc 0 1 = X₂')
    (hiξ : InjOn ξ (Icc 0 1)) (hiη : InjOn η (Icc 0 1))
    (hiξ' : InjOn ξ' (Icc 0 1)) (hiη' : InjOn η' (Icc 0 1))
    (AS : SurfAtlas S)
    (hrel : BdCohRel s t (arcCocycle hS hne hb' hl') (arcCocycle hS hne hb hl))
    (hst : connectedComponentIn (bd S) s = connectedComponentIn (bd S) t)
    (φS : Circle ≃ₜ connectedComponentIn (bd S) s)
    {u_s u_t : ℝ} (hu1 : u_s < u_t) (hu2 : u_t < u_s + 1)
    (hus : (φS (ee u_s)).1 = s) (hut : (φS (ee u_t)).1 = t)
    (st : CutSetup ψ ψ' F F' s t X X' X₂ X₂' a a' ξ η ξ' η')
    (hi_ne : st.i_ξ ≠ st.i_η) (hj_ne : st.j_ξ0 ≠ st.j_η0)
    (hbuild_perm_two : ∀ (j_ξ j_η : Fin st.c₀), ({j_ξ, j_η} : Set (Fin st.c₀)) = {st.j_ξ0, st.j_η0} → j_ξ ≠ j_η →
      ∃ π : Equiv.Perm (Fin st.c₀), π st.i_ξ = j_ξ ∧ π st.i_η = j_η ∧
        ∀ i : Fin st.c₀, i ≠ st.i_ξ → i ≠ st.i_η → π i ≠ j_ξ ∧ π i ≠ j_η ∧
          ψ' '' holeC st.a₀ st.b₀ st.c₀ st.f' (π i).1 = ψ '' holeC st.a₀ st.b₀ st.c₀ st.f i.1) :
    ∃ β : S ≃ₜ S, β '' F = F' ∧ ∀ x ∈ bd S, β x = x := by
  classical
  have : CompactSpace Y := hY.1
  have : CompactSpace Y' := hY'.1
  have : T2Space S := hS.2.1
  have hF : IsClosed F := hl.isCompact.isClosed
  have hF' : IsClosed F' := hl'.isCompact.isClosed
  have hsb : s ∈ bd S := (show s ∈ F ∩ bd S from hb ▸ mem_insert _ _).2
  have hCs_cuff : connectedComponentIn (bd S) s ∈ cuffs S := ⟨s, hsb, rfl⟩
  let C : Fin st.c₀ → Set Y := fun i => holeC st.a₀ st.b₀ st.c₀ st.f i.1
  let C' : Fin st.c₀ → Set Y' := fun j => holeC st.a₀ st.b₀ st.c₀ st.f' j.1
  let φ : ∀ i : Fin st.c₀, Circle ≃ₜ C i := fun i => holeParam st.hf i.isLt
  let φ' : ∀ j : Fin st.c₀, Circle ≃ₜ C' j := fun j => holeParam st.hf' j.isLt
  have hC_cuff : ∀ i, C i ∈ cuffs Y := fun i => cuffs_eq_holeC st.hf ▸ ⟨i.1, i.isLt, rfl⟩
  have hC'_cuff : ∀ j, C' j ∈ cuffs Y' := fun j => cuffs_eq_holeC st.hf' ▸ ⟨j.1, j.isLt, rfl⟩
  have hC_bd : ∀ i, C i ⊆ bd Y := fun i => by obtain ⟨y, -, hy⟩ := hC_cuff i; rw [← hy]; exact connectedComponentIn_subset _ _
  have hC'_bd : ∀ j, C' j ⊆ bd Y' := fun j => by obtain ⟨y, -, hy⟩ := hC'_cuff j; rw [← hy]; exact connectedComponentIn_subset _ _
  have hC_inj : Function.Injective C := fun i₁ i₂ he => by
    by_contra hne'
    have h1 : (φ i₁ (ee 0)).1 ∈ C i₁ := (φ i₁ _).2
    have h2 : (φ i₁ (ee 0)).1 ∈ C i₂ := he ▸ h1
    exact Set.disjoint_left.mp (disjoint_holeC st.hf i₁.isLt i₂.isLt (fun h => hne' (Fin.ext h))) h1 h2
  have hC'_inj : Function.Injective C' := fun j₁ j₂ he => by
    by_contra hne'
    have h1 : (φ' j₁ (ee 0)).1 ∈ C' j₁ := (φ' j₁ _).2
    have h2 : (φ' j₁ (ee 0)).1 ∈ C' j₂ := he ▸ h1
    exact Set.disjoint_left.mp (disjoint_holeC st.hf' j₁.isLt j₂.isLt (fun h => hne' (Fin.ext h))) h1 h2
  obtain ⟨_, _, _, _, _, _, _, hun, -⟩ := id hP
  let G₁ : Set S := (fun v => (φS (ee v)).1) '' Ioo u_t (u_s + 1)
  let G₂ : Set S := (fun v => (φS (ee v)).1) '' Ioo u_s u_t
  have hGpart := same_cuff_gaps_partition φS hu1 hu2 hus hut
  have hGpart_eq : connectedComponentIn (bd S) s \ {s, t} = G₁ ∪ G₂ := hGpart.1
  have hGpart_disj : Disjoint G₁ G₂ := hGpart.2.1
  let x₁ : S := (φS (ee ((u_t + (u_s + 1)) / 2))).1
  let x₂ : S := (φS (ee ((u_s + u_t) / 2))).1
  have hx₁G₁ : x₁ ∈ G₁ := ⟨(u_t + (u_s + 1)) / 2, ⟨by linarith, by linarith⟩, rfl⟩
  have hx₂G₂ : x₂ ∈ G₂ := ⟨(u_s + u_t) / 2, ⟨by linarith, by linarith⟩, rfl⟩
  have hx₁_diff : x₁ ∈ connectedComponentIn (bd S) s \ {s, t} := by rw [hGpart_eq]; exact Or.inl hx₁G₁
  have hx₂_diff : x₂ ∈ connectedComponentIn (bd S) s \ {s, t} := by rw [hGpart_eq]; exact Or.inr hx₂G₂
  have hx₁_bd : x₁ ∈ bd S \ {s, t} := ⟨connectedComponentIn_subset _ _ hx₁_diff.1, hx₁_diff.2⟩
  have hx₂_bd : x₂ ∈ bd S \ {s, t} := ⟨connectedComponentIn_subset _ _ hx₂_diff.1, hx₂_diff.2⟩
  have hx₁nF : x₁ ∉ F := fun h => hx₁_bd.2 (hb ▸ ⟨h, hx₁_bd.1⟩)
  have hx₁nF' : x₁ ∉ F' := fun h => hx₁_bd.2 (hb' ▸ ⟨h, hx₁_bd.1⟩)
  have hx₂nF : x₂ ∉ F := fun h => hx₂_bd.2 (hb ▸ ⟨h, hx₂_bd.1⟩)
  have hx₂nF' : x₂ ∉ F' := fun h => hx₂_bd.2 (hb' ▸ ⟨h, hx₂_bd.1⟩)
  let eF := cutComplHomeo hψ hF
  let eF' := cutComplHomeo hψ' hF'
  let y₁ : Y := (eF.symm ⟨x₁, hx₁nF⟩).1
  let y₂ : Y := (eF.symm ⟨x₂, hx₂nF⟩).1
  let y₁' : Y' := (eF'.symm ⟨x₁, hx₁nF'⟩).1
  let y₂' : Y' := (eF'.symm ⟨x₂, hx₂nF'⟩).1
  have hψy₁ : ψ y₁ = x₁ := cutComplHomeo_symm_psi hψ hF ⟨x₁, hx₁nF⟩
  have hψy₂ : ψ y₂ = x₂ := cutComplHomeo_symm_psi hψ hF ⟨x₂, hx₂nF⟩
  have hψ'y₁ : ψ' y₁' = x₁ := cutComplHomeo_symm_psi hψ' hF' ⟨x₁, hx₁nF'⟩
  have hψ'y₂ : ψ' y₂' = x₂ := cutComplHomeo_symm_psi hψ' hF' ⟨x₂, hx₂nF'⟩
  have hpreY : ∀ y : Y, ψ y ∈ connectedComponentIn (bd S) s \ {s, t} → y ∈ C st.i_ξ ∨ y ∈ C st.i_η := fun y hy => by
    have hyF : ψ y ∉ F := fun h => hy.2 (hb ▸ ⟨h, connectedComponentIn_subset _ _ hy.1⟩)
    have hybd : y ∈ bd Y := bd_lift hψ hF (connectedComponentIn_subset _ _ hy.1) hyF
    obtain ⟨i, hi_lt, hi_eq'⟩ := (cuffs_eq_holeC st.hf).subset (⟨y, hybd, rfl⟩ : connectedComponentIn (bd Y) y ∈ cuffs Y)
    have hyi : y ∈ C ⟨i, hi_lt⟩ := show y ∈ holeC st.a₀ st.b₀ st.c₀ st.f i by rw [hi_eq']; exact mem_connectedComponentIn hybd
    by_contra hnot; push Not at hnot
    obtain ⟨_, hD, hsD, _, _⟩ := untouched_cuff_properties hS hY hψ hF hb hP st.hf st.hXC st.hX'C (fun he => hnot.1 (he ▸ hyi)) (fun he => hnot.2 (he ▸ hyi))
    have hDeq : ψ '' C ⟨i, hi_lt⟩ = connectedComponentIn (bd S) s := by
      by_contra hne'; exact Set.disjoint_left.mp (cuffs_disjoint hD hCs_cuff hne') ⟨y, hyi, rfl⟩ hy.1
    exact hsD (hDeq.symm ▸ mem_connectedComponentIn hsb)
  have hpreY' : ∀ y' : Y', ψ' y' ∈ connectedComponentIn (bd S) s \ {s, t} → y' ∈ C' st.j_ξ0 ∨ y' ∈ C' st.j_η0 := fun y' hy => by
    have hyF : ψ' y' ∉ F' := fun h => hy.2 (hb' ▸ ⟨h, connectedComponentIn_subset _ _ hy.1⟩)
    have hybd : y' ∈ bd Y' := bd_lift hψ' hF' (connectedComponentIn_subset _ _ hy.1) hyF
    obtain ⟨j, hj_lt, hj_eq'⟩ := (cuffs_eq_holeC st.hf').subset (⟨y', hybd, rfl⟩ : connectedComponentIn (bd Y') y' ∈ cuffs Y')
    have hyj : y' ∈ C' ⟨j, hj_lt⟩ := show y' ∈ holeC st.a₀ st.b₀ st.c₀ st.f' j by rw [hj_eq']; exact mem_connectedComponentIn hybd
    by_contra hnot; push Not at hnot
    obtain ⟨_, hD, hsD, _, _⟩ := untouched_cuff_properties hS hY' hψ' hF' hb' hP' st.hf' st.hX2C st.hX2'C (fun he => hnot.1 (he ▸ hyj)) (fun he => hnot.2 (he ▸ hyj))
    have hDeq : ψ' '' C' ⟨j, hj_lt⟩ = connectedComponentIn (bd S) s := by
      by_contra hne'; exact Set.disjoint_left.mp (cuffs_disjoint hD hCs_cuff hne') ⟨y', hyj, rfl⟩ hy.1
    exact hsD (hDeq.symm ▸ mem_connectedComponentIn hsb)
  have hy₁Y := hpreY y₁ (hψy₁.symm ▸ hx₁_diff)
  have hy₂Y := hpreY y₂ (hψy₂.symm ▸ hx₂_diff)
  have hy₁Y' := hpreY' y₁' (hψ'y₁.symm ▸ hx₁_diff)
  have hy₂Y' := hpreY' y₂' (hψ'y₂.symm ▸ hx₂_diff)
  have hy_sep : ∀ {Z : Type u} [TopologicalSpace Z] [T2Space Z] (hZ : IsSurface Z)
      {ψZ : Z → S} {FZ : Set S} (hψZ : IsCutting ψZ FZ) (hFZ : IsClosed FZ) (hbZ : FZ ∩ bd S = {s, t})
      {XZ XZ' : Set Z} (hPZ : LiftPair ψZ FZ s t XZ XZ')
      {aZ : ℝ → S} {ξZ ηZ : ℝ → Z} (LZ : ArcLift ψZ FZ aZ ξZ ηZ)
      (haZ0 : aZ 0 = s) (haZ1 : aZ 1 = t)
      (him1 : ξZ '' Icc 0 1 = XZ) (hi1 : InjOn ξZ (Icc 0 1))
      {CZ CZ' : Set Z} (hCZ : CZ ∈ cuffs Z) (hCZ' : CZ' ∈ cuffs Z) (hneC : CZ ≠ CZ')
      (hXZC : XZ ⊆ CZ) (hXZ'C : XZ' ⊆ CZ')
      {z₁ z₂ : Z} (hz1 : ψZ z₁ = x₁) (hz2 : ψZ z₂ = x₂),
      z₁ ∈ CZ → z₂ ∉ CZ := by
    intro Z _ _ hZ ψZ FZ hψZ hFZ hbZ XZ XZ' hPZ aZ ξZ ηZ LZ haZ0 haZ1 him1 hi1 CZ CZ' hCZ hCZ' hneC hXZC hXZ'C z₁ z₂ hz1 hz2 hz1C hz2C
    obtain ⟨AZ⟩ := exists_surfAtlas hZ
    obtain ⟨φZ⟩ := (cuff_statement.{u} Z hZ).2.2 _ hCZ
    obtain ⟨m, hmc, hme⟩ := exists_lift φZ LZ.cξ (fun u hu => hXZC (him1 ▸ ⟨u, hu, rfl⟩))
    obtain ⟨v₁, -, hv1e⟩ := exists_param (φZ.symm ⟨z₁, hz1C⟩)
    obtain ⟨v₂, -, hv2e⟩ := exists_param (φZ.symm ⟨z₂, hz2C⟩)
    have hv1z : (φZ (ee v₁)).1 = z₁ := by rw [hv1e]; simp
    have hv2z : (φZ (ee v₂)).1 = z₂ := by rw [hv2e]; simp
    have hz1nF : ψZ (φZ (ee v₁)).1 ∉ FZ := fun h => hx₁_bd.2 (hbZ ▸ ⟨by rwa [hv1z, hz1] at h, hx₁_bd.1⟩)
    obtain ⟨δ, ml, dl, hδ, _, hmlc, hmld, hmle, _⟩ :=
      exists_cuff_local_dir hZ hS hψZ hFZ AZ AS (by obtain ⟨w, -, rfl⟩ := hCZ; exact connectedComponentIn_subset _ _)
        hCs_cuff φZ φS (by rw [hv1z, hz1]; exact hx₁_diff.1) hz1nF
    obtain ⟨dm, _, _, _, _, _, hgap, _⟩ :=
      twosided_cuff_info hZ hS hne hψZ hFZ hbZ hPZ LZ haZ0 haZ1 him1 hi1 hst φS hCZ hCZ' hneC hXZ'C φZ hmc hme
        hu2 (by linarith) (.inl ⟨hut, by rw [ee_add_one]; exact hus⟩) (by rw [hv1z, hz1]; exact hx₁G₁) hδ hmlc hmld hmle
    set p := if dm then m 1 else m 0
    set q := if dm then m 0 + 1 else m 1 + 1
    set a₀v := if dm then m 0 else m 1
    set v2s := a₀v + Int.fract (v₂ - a₀v)
    have hv2s_ee : ee v2s = ee v₂ := ee_eq_iff.mpr ⟨-⌊v₂ - a₀v⌋, by simp only [v2s, Int.cast_neg]; linarith [Int.floor_add_fract (v₂ - a₀v)]⟩
    have hv2s_nF : ψZ (φZ (ee v2s)).1 ∉ FZ := fun h => hx₂_bd.2 (hbZ ▸ ⟨by rwa [hv2s_ee, hv2z, hz2] at h, hx₂_bd.1⟩)
    have hv2s_in : v2s ∈ Ioo p q := by
      have hlo : a₀v ≤ v2s := by simp only [v2s]; linarith [Int.fract_nonneg (v₂ - a₀v)]
      have hhi : v2s < q := by have : q = a₀v + 1 := by cases dm <;> rfl
                               rw [this]; simp only [v2s]; linarith [Int.fract_lt_one (v₂ - a₀v)]
      refine ⟨?_, hhi⟩
      by_contra hle'
      have hmem : v2s ∈ Icc (m 0) (m 1) ∨ v2s ∈ Icc (m 1) (m 0) := by
        cases dm <;> simp only [p, a₀v, Bool.false_eq_true, ↓reduceIte] at hlo hle'
        · exact .inr ⟨hlo, not_lt.mp hle'⟩
        · exact .inl ⟨hlo, not_lt.mp hle'⟩
      obtain ⟨u, hu, hue⟩ : ∃ u ∈ Icc (0 : ℝ) 1, m u = v2s :=
        hmem.elim (fun h => intermediate_value_Icc zero_le_one hmc h) (fun h => intermediate_value_Icc' zero_le_one hmc h)
      obtain ⟨_, _, _, _, _, _, _, hunZ, -⟩ := id hPZ
      exact hv2s_nF (by rw [← hue, hme u hu]; exact show ξZ u ∈ ψZ ⁻¹' FZ from hunZ ▸ Or.inl (him1 ▸ ⟨u, hu, rfl⟩))
    exact Set.disjoint_left.mp hGpart_disj (by rw [← hz2, ← hv2z, ← hv2s_ee]; exact hgap v2s hv2s_in) hx₂G₂
  let sw : Bool := decide ((y₁ ∈ C st.i_ξ) ≠ (y₁' ∈ C' st.j_ξ0))
  let ξ₀' : ℝ → Y' := if sw then η' else ξ'
  let η₀' : ℝ → Y' := if sw then ξ' else η'
  let X₀' : Set Y' := if sw then X₂' else X₂
  let X₀'' : Set Y' := if sw then X₂ else X₂'
  let j_ξ : Fin st.c₀ := if sw then st.j_η0 else st.j_ξ0
  let j_η : Fin st.c₀ := if sw then st.j_ξ0 else st.j_η0
  have hP₀' : LiftPair ψ' F' s t X₀' X₀'' := by
    cases hsw : sw <;> simp only [X₀', X₀'', hsw, Bool.false_eq_true, ↓reduceIte]
    · exact hP'
    · obtain ⟨x0, x1, y0, y1, l1, l2, hd0, hun0, b1, b2, h7, h8, h9, h10⟩ := id hP'
      exact ⟨y0, y1, x0, x1, l2, l1, hd0.symm, by rw [union_comm]; exact hun0, b2, b1, h8, h7, h10, h9⟩
  have L₀' : ArcLift ψ' F' a' ξ₀' η₀' := by cases hsw : sw <;> simp only [ξ₀', η₀', hsw, Bool.false_eq_true, ↓reduceIte]; exact L'; exact L'.swap
  have him₁' : ξ₀' '' Icc 0 1 = X₀' := by cases hsw : sw <;> simp only [ξ₀', X₀', hsw, Bool.false_eq_true, ↓reduceIte] <;> assumption
  have him₂' : η₀' '' Icc 0 1 = X₀'' := by cases hsw : sw <;> simp only [η₀', X₀'', hsw, Bool.false_eq_true, ↓reduceIte] <;> assumption
  have hi₁' : InjOn ξ₀' (Icc 0 1) := by cases hsw : sw <;> simp only [ξ₀', hsw, Bool.false_eq_true, ↓reduceIte] <;> assumption
  have hi₂' : InjOn η₀' (Icc 0 1) := by cases hsw : sw <;> simp only [η₀', hsw, Bool.false_eq_true, ↓reduceIte] <;> assumption
  have hX₀C' : X₀' ⊆ C' j_ξ := by cases hsw : sw <;> simp only [X₀', j_ξ, hsw, Bool.false_eq_true, ↓reduceIte]; exact st.hX2C; exact st.hX2'C
  have hX₀''C' : X₀'' ⊆ C' j_η := by cases hsw : sw <;> simp only [X₀'', j_η, hsw, Bool.false_eq_true, ↓reduceIte]; exact st.hX2'C; exact st.hX2C
  have hj_ne' : j_ξ ≠ j_η := by cases hsw : sw <;> simp only [j_ξ, j_η, hsw, Bool.false_eq_true, ↓reduceIte]; exact hj_ne; exact hj_ne.symm
  have hj_set : ({j_ξ, j_η} : Set (Fin st.c₀)) = {st.j_ξ0, st.j_η0} := by cases hsw : sw <;> simp [j_ξ, j_η, hsw, Set.pair_comm]
  have hy₁Y'_sw : y₁' ∈ C' j_ξ ∨ y₁' ∈ C' j_η := by cases hsw : sw <;> simp only [j_ξ, j_η, hsw, Bool.false_eq_true, ↓reduceIte]; exact hy₁Y'; exact hy₁Y'.symm
  have hy₂Y'_sw : y₂' ∈ C' j_ξ ∨ y₂' ∈ C' j_η := by cases hsw : sw <;> simp only [j_ξ, j_η, hsw, Bool.false_eq_true, ↓reduceIte]; exact hy₂Y'; exact hy₂Y'.symm
  have hP_sw : LiftPair ψ F s t X' X := by
    obtain ⟨x0, x1, y0, y1, l1, l2, hd0, hun0, b1, b2, h7, h8, h9, h10⟩ := id hP
    exact ⟨y0, y1, x0, x1, l2, l1, hd0.symm, by rw [union_comm]; exact hun0, b2, b1, h8, h7, h10, h9⟩
  have hP₀'_sw : LiftPair ψ' F' s t X₀'' X₀' := by
    obtain ⟨x0, x1, y0, y1, l1, l2, hd0, hun0, b1, b2, h7, h8, h9, h10⟩ := id hP₀'
    exact ⟨y0, y1, x0, x1, l2, l1, hd0.symm, by rw [union_comm]; exact hun0, b2, b1, h8, h7, h10, h9⟩
  have hsame_side : (y₁ ∈ C st.i_ξ ↔ y₁' ∈ C' j_ξ) ∧ (y₂ ∈ C st.i_η ↔ y₂' ∈ C' j_η) := by
    have h1 : y₁ ∈ C st.i_ξ ↔ y₁' ∈ C' j_ξ := by
      by_cases hA : y₁ ∈ C st.i_ξ
      · by_cases hB : y₁' ∈ C' st.j_ξ0
        · have hsw : sw = false := by simp [sw, hA, hB]
          simp [hsw, j_ξ, hA, hB]
        · have hsw : sw = true := by simp [sw, hA, hB]
          simp [hsw, j_ξ, hA, hy₁Y'.resolve_left hB]
      · by_cases hB : y₁' ∈ C' st.j_ξ0
        · have hsw : sw = true := by simp [sw, hA, hB]
          have hB' : y₁' ∉ C' st.j_η0 := fun h => Set.disjoint_left.mp (disjoint_holeC st.hf' st.j_ξ0.isLt st.j_η0.isLt (fun e => hj_ne (Fin.ext e))) hB h
          simp [hsw, j_ξ, hA, hB']
        · have hsw : sw = false := by simp [sw, hA, hB]
          simp [hsw, j_ξ, hA, hB]
    refine ⟨h1, ?_⟩
    by_cases hA : y₁ ∈ C st.i_ξ
    · have h2Y : y₂ ∈ C st.i_η := hy₂Y.resolve_left (hy_sep hY hψ hF hb hP L ha0 ha1 himξ hiξ (hC_cuff st.i_ξ) (hC_cuff st.i_η) (fun e => hi_ne (hC_inj e)) st.hXC st.hX'C hψy₁ hψy₂ hA)
      have h2Y' : y₂' ∈ C' j_η := hy₂Y'_sw.resolve_left (hy_sep hY' hψ' hF' hb' hP₀' L₀' ha'0 ha'1 him₁' hi₁' (hC'_cuff j_ξ) (hC'_cuff j_η) (fun e => hj_ne' (hC'_inj e)) hX₀C' hX₀''C' hψ'y₁ hψ'y₂ (h1.mp hA))
      exact iff_of_true h2Y h2Y'
    · have h1η : y₁ ∈ C st.i_η := hy₁Y.resolve_left hA
      have h1η' : y₁' ∈ C' j_η := hy₁Y'_sw.resolve_left (fun h => hA (h1.mpr h))
      exact iff_of_false
        (hy_sep hY hψ hF hb hP_sw L.swap ha0 ha1 himη hiη (hC_cuff st.i_η) (hC_cuff st.i_ξ) (fun e => hi_ne (hC_inj e).symm) st.hX'C st.hXC hψy₁ hψy₂ h1η)
        (hy_sep hY' hψ' hF' hb' hP₀'_sw L₀'.swap ha'0 ha'1 him₂' hi₂' (hC'_cuff j_η) (hC'_cuff j_ξ) (fun e => hj_ne' (hC'_inj e).symm) hX₀''C' hX₀C' hψ'y₁ hψ'y₂ h1η')
  let b_ξ : Bool := decide (y₁ ∈ C st.i_ξ)
  let x_ξ : S := if b_ξ then x₁ else x₂
  let x_η : S := if b_ξ then x₂ else x₁
  let y_ξ : Y := if b_ξ then y₁ else y₂
  let y_η : Y := if b_ξ then y₂ else y₁
  let y_ξ' : Y' := if b_ξ then y₁' else y₂'
  let y_η' : Y' := if b_ξ then y₂' else y₁'
  have hy_ξC : y_ξ ∈ C st.i_ξ := by
    by_cases h : y₁ ∈ C st.i_ξ
    · simp [b_ξ, y_ξ, h]
    · simp only [b_ξ, y_ξ, decide_eq_false h, Bool.false_eq_true, ↓reduceIte]
      exact hy₂Y.resolve_right (hy_sep hY hψ hF hb hP_sw L.swap ha0 ha1 himη hiη (hC_cuff st.i_η) (hC_cuff st.i_ξ) (fun e => hi_ne (hC_inj e).symm) st.hX'C st.hXC hψy₁ hψy₂ (hy₁Y.resolve_left h))
  have hy_ηC : y_η ∈ C st.i_η := by
    by_cases h : y₁ ∈ C st.i_ξ
    · simp only [b_ξ, y_η, decide_eq_true h, ↓reduceIte]
      exact hy₂Y.resolve_left (hy_sep hY hψ hF hb hP L ha0 ha1 himξ hiξ (hC_cuff st.i_ξ) (hC_cuff st.i_η) (fun e => hi_ne (hC_inj e)) st.hXC st.hX'C hψy₁ hψy₂ h)
    · simp only [b_ξ, y_η, decide_eq_false h, Bool.false_eq_true, ↓reduceIte]; exact hy₁Y.resolve_left h
  have hy_ξ'C : y_ξ' ∈ C' j_ξ := by
    by_cases h : y₁ ∈ C st.i_ξ
    · simp only [b_ξ, y_ξ', decide_eq_true h, ↓reduceIte]; exact hsame_side.1.mp h
    · simp only [b_ξ, y_ξ', decide_eq_false h, Bool.false_eq_true, ↓reduceIte]
      exact hy₂Y'_sw.resolve_right (hy_sep hY' hψ' hF' hb' hP₀'_sw L₀'.swap ha'0 ha'1 him₂' hi₂' (hC'_cuff j_η) (hC'_cuff j_ξ) (fun e => hj_ne' (hC'_inj e).symm) hX₀''C' hX₀C' hψ'y₁ hψ'y₂ (hy₁Y'_sw.resolve_left (fun h' => h (hsame_side.1.mpr h'))))
  have hy_η'C : y_η' ∈ C' j_η := by
    by_cases h : y₁ ∈ C st.i_ξ
    · simp only [b_ξ, y_η', decide_eq_true h, ↓reduceIte]; exact hsame_side.2.mp (by simpa [b_ξ, y_η, h] using hy_ηC)
    · simp only [b_ξ, y_η', decide_eq_false h, Bool.false_eq_true, ↓reduceIte]; exact hy₁Y'_sw.resolve_left (fun h' => h (hsame_side.1.mpr h'))
  have hψy_ξ : ψ y_ξ = x_ξ := by cases hbξ : b_ξ <;> simp [y_ξ, x_ξ, hbξ, hψy₁, hψy₂]
  have hψy_η : ψ y_η = x_η := by cases hbξ : b_ξ <;> simp [y_η, x_η, hbξ, hψy₁, hψy₂]
  have hψ'y_ξ : ψ' y_ξ' = x_ξ := by cases hbξ : b_ξ <;> simp [y_ξ', x_ξ, hbξ, hψ'y₁, hψ'y₂]
  have hψ'y_η : ψ' y_η' = x_η := by cases hbξ : b_ξ <;> simp [y_η', x_η, hbξ, hψ'y₁, hψ'y₂]
  have hx_ξ_bd : x_ξ ∈ bd S \ {s, t} := by cases hbξ : b_ξ <;> simp [x_ξ, hbξ, hx₁_bd, hx₂_bd]
  have hx_η_bd : x_η ∈ bd S \ {s, t} := by cases hbξ : b_ξ <;> simp [x_η, hbξ, hx₁_bd, hx₂_bd]
  have hx_ξ_Cs : x_ξ ∈ connectedComponentIn (bd S) s := by cases hbξ : b_ξ <;> simp only [x_ξ, hbξ, Bool.false_eq_true, ↓reduceIte]; exact hx₂_diff.1; exact hx₁_diff.1
  have hx_η_Cs : x_η ∈ connectedComponentIn (bd S) s := by cases hbξ : b_ξ <;> simp only [x_η, hbξ, Bool.false_eq_true, ↓reduceIte]; exact hx₁_diff.1; exact hx₂_diff.1
  have hx_ξ_nF : x_ξ ∉ F := by cases hbξ : b_ξ <;> simp [x_ξ, hbξ, hx₁nF, hx₂nF]
  have hx_ξ_nF' : x_ξ ∉ F' := by cases hbξ : b_ξ <;> simp [x_ξ, hbξ, hx₁nF', hx₂nF']
  have hx_η_nF : x_η ∉ F := by cases hbξ : b_ξ <;> simp [x_η, hbξ, hx₁nF, hx₂nF]
  have hx_η_nF' : x_η ∉ F' := by cases hbξ : b_ξ <;> simp [x_η, hbξ, hx₁nF', hx₂nF']
  obtain ⟨v_ξ, -, hv_ξe⟩ := exists_param ((φ st.i_ξ).symm ⟨y_ξ, hy_ξC⟩)
  obtain ⟨v_η, -, hv_ηe⟩ := exists_param ((φ st.i_η).symm ⟨y_η, hy_ηC⟩)
  obtain ⟨v_ξ', -, hv_ξ'e⟩ := exists_param ((φ' j_ξ).symm ⟨y_ξ', hy_ξ'C⟩)
  obtain ⟨v_η', -, hv_η'e⟩ := exists_param ((φ' j_η).symm ⟨y_η', hy_η'C⟩)
  have hv_ξy : (φ st.i_ξ (ee v_ξ)).1 = y_ξ := by rw [hv_ξe]; simp
  have hv_ηy : (φ st.i_η (ee v_η)).1 = y_η := by rw [hv_ηe]; simp
  have hv_ξ'y : (φ' j_ξ (ee v_ξ')).1 = y_ξ' := by rw [hv_ξ'e]; simp
  have hv_η'y : (φ' j_η (ee v_η')).1 = y_η' := by rw [hv_η'e]; simp
  obtain ⟨δ_ξ, m_ξl, d_ξ, hδ_ξ, _, hm_ξlc, hm_ξld, hm_ξle, _⟩ :=
    exists_cuff_local_dir hY hS hψ hF st.AY AS (hC_bd st.i_ξ) hCs_cuff (φ st.i_ξ) φS (by rw [hv_ξy, hψy_ξ]; exact hx_ξ_Cs) (by rw [hv_ξy, hψy_ξ]; exact hx_ξ_nF)
  obtain ⟨δ_η, m_ηl, d_η, hδ_η, _, hm_ηlc, hm_ηld, hm_ηle, _⟩ :=
    exists_cuff_local_dir hY hS hψ hF st.AY AS (hC_bd st.i_η) hCs_cuff (φ st.i_η) φS (by rw [hv_ηy, hψy_η]; exact hx_η_Cs) (by rw [hv_ηy, hψy_η]; exact hx_η_nF)
  obtain ⟨δ_ξ', m_ξ'l, d_ξ', hδ_ξ', _, hm_ξ'lc, hm_ξ'ld, hm_ξ'le, _⟩ :=
    exists_cuff_local_dir hY' hS hψ' hF' st.AY' AS (hC'_bd j_ξ) hCs_cuff (φ' j_ξ) φS (by rw [hv_ξ'y, hψ'y_ξ]; exact hx_ξ_Cs) (by rw [hv_ξ'y, hψ'y_ξ]; exact hx_ξ_nF')
  obtain ⟨δ_η', m_η'l, d_η', hδ_η', _, hm_η'lc, hm_η'ld, hm_η'le, _⟩ :=
    exists_cuff_local_dir hY' hS hψ' hF' st.AY' AS (hC'_bd j_η) hCs_cuff (φ' j_η) φS (by rw [hv_η'y, hψ'y_η]; exact hx_η_Cs) (by rw [hv_η'y, hψ'y_η]; exact hx_η_nF')
  obtain ⟨π, hπ_ξ, hπ_η, hπ_unt⟩ := hbuild_perm_two j_ξ j_η hj_set hj_ne'
  have hnot0 : ∀ i : Fin st.c₀, i ≠ st.i_ξ → i ≠ st.i_η → π i ≠ st.j_ξ0 ∧ π i ≠ st.j_η0 := fun i h1 h2 => by
    have h := hπ_unt i h1 h2
    cases hsw : sw <;> simp only [j_ξ, j_η, hsw, Bool.false_eq_true, ↓reduceIte] at h <;> [exact ⟨h.1, h.2.1⟩; exact ⟨h.2.1, h.1⟩]
  have hex_flip : ∃ flip : Fin st.c₀ → Bool,
      (st.b₀ = 0 → ∀ i j : Fin st.c₀, flip i = flip j) ∧
      (!flip st.i_ξ) = (d_ξ == d_ξ') ∧ (!flip st.i_η) = (d_η == d_η') ∧
      (∀ i : Fin st.c₀, ∀ hi1 : i ≠ st.i_ξ, ∀ hi2 : i ≠ st.i_η,
        ∀ (φD : Circle ≃ₜ (ψ '' C i)) (v₀ v₀' δa δb : ℝ) (ma mb : ℝ → ℝ) (da db : Bool),
          0 < δa → 0 < δb → ψ (φ i (ee v₀)).1 = ψ' (φ' (π i) (ee v₀')).1 →
          ContinuousOn ma (Icc (-δa) δa) → ContinuousOn mb (Icc (-δb) δb) →
          (if da then StrictMonoOn ma (Icc (-δa) δa) else StrictAntiOn ma (Icc (-δa) δa)) →
          (if db then StrictMonoOn mb (Icc (-δb) δb) else StrictAntiOn mb (Icc (-δb) δb)) →
          (∀ r ∈ Icc (-δa) δa, ψ (φ i (ee (v₀ + r))).1 = (φD (ee (ma r))).1) →
          (∀ r ∈ Icc (-δb) δb, ψ' (φ' (π i) (ee (v₀' + r))).1 = (φD (ee (mb r))).1) →
          (!flip i) = (da == db)) := by
    by_cases hb0 : st.b₀ = 0
    · have hf0 : Presents (sW (ew st.a₀ 0 st.c₀)) st.f := hb0 ▸ st.hf
      have hf'0 : Presents (sW (ew st.a₀ 0 st.c₀)) st.f' := hb0 ▸ st.hf'
      obtain ⟨Δ, hΔ⟩ := orient_cut_global_flip hS hne hb hb' hl hl' hY hY' hψ hψ' hP hP' hf0 hf'0 hrel
      have hcast : ∀ (i : Fin st.c₀) (z : Circle), (holeParam hf0 i.isLt z).1 = (φ i z).1 := fun i z => by
        cases st; dsimp only at hb0; subst hb0; rfl
      have hcast' : ∀ (j : Fin st.c₀) (z : Circle), (holeParam hf'0 j.isLt z).1 = (φ' j z).1 := fun j z => by
        cases st; dsimp only at hb0; subst hb0; rfl
      refine ⟨fun _ => decide (Δ ≠ 0), fun _ _ _ => rfl, ?_, ?_, fun i hi1 hi2 φD v₀ v₀' δa δb ma mb da db hδa hδb hψeq hmac hmbc hmad hmbd hmae hmbe => ?_⟩
      · exact bool_not_eq_beq_of_zmod2 (hΔ x_ξ hx_ξ_bd _ hCs_cuff φS hx_ξ_Cs st.i_ξ.1 j_ξ.1 st.i_ξ.isLt j_ξ.isLt
          v_ξ v_ξ' (by rw [hcast, hv_ξy, hψy_ξ]) (by rw [hcast', hv_ξ'y, hψ'y_ξ]) δ_ξ δ_ξ' m_ξl m_ξ'l d_ξ d_ξ' hδ_ξ hδ_ξ' hm_ξlc hm_ξ'lc hm_ξld hm_ξ'ld
          (fun r hr => by rw [hcast]; exact hm_ξle r hr) (fun r hr => by rw [hcast']; exact hm_ξ'le r hr))
      · exact bool_not_eq_beq_of_zmod2 (hΔ x_η hx_η_bd _ hCs_cuff φS hx_η_Cs st.i_η.1 j_η.1 st.i_η.isLt j_η.isLt
          v_η v_η' (by rw [hcast, hv_ηy, hψy_η]) (by rw [hcast', hv_η'y, hψ'y_η]) δ_η δ_η' m_ηl m_η'l d_η d_η' hδ_η hδ_η' hm_ηlc hm_η'lc hm_ηld hm_η'ld
          (fun r hr => by rw [hcast]; exact hm_ηle r hr) (fun r hr => by rw [hcast']; exact hm_η'le r hr))
      · obtain ⟨_, hD, hsD, htD, _⟩ := untouched_cuff_properties hS hY hψ hF hb hP st.hf st.hXC st.hX'C hi1 hi2
        have hxD : ψ (φ i (ee v₀)).1 ∈ ψ '' C i := ⟨_, (φ i _).2, rfl⟩
        have hxbd : ψ (φ i (ee v₀)).1 ∈ bd S \ {s, t} := ⟨by obtain ⟨z, -, hz⟩ := hD; rw [← hz] at hxD; exact connectedComponentIn_subset _ _ hxD,
          fun h => h.elim (fun he => hsD (Set.mem_of_eq_of_mem he.symm hxD)) (fun he => htD (Set.mem_of_eq_of_mem he.symm hxD))⟩
        exact bool_not_eq_beq_of_zmod2 (hΔ _ hxbd _ hD φD hxD i.1 (π i).1 i.isLt (π i).isLt v₀ v₀'
          (by rw [hcast]) (by rw [hcast']; exact hψeq.symm) δa δb ma mb da db hδa hδb hmac hmbc hmad hmbd
          (fun r hr => by rw [hcast]; exact hmae r hr) (fun r hr => by rw [hcast']; exact hmbe r hr))
    · let hdir : ∀ i : Fin st.c₀, i ≠ st.i_ξ → i ≠ st.i_η → _ := fun i hi1 hi2 =>
        untouched_dir_pair hS hY hY' AS st.AY st.AY' hψ hψ' hF hF' st.hf st.hf'
          (untouched_cuff_properties hS hY hψ hF hb hP st.hf st.hXC st.hX'C hi1 hi2).1
          (untouched_cuff_properties hS hY' hψ' hF' hb' hP' st.hf' st.hX2C st.hX2'C (hnot0 i hi1 hi2).1 (hnot0 i hi1 hi2).2).1
          (untouched_cuff_properties hS hY hψ hF hb hP st.hf st.hXC st.hX'C hi1 hi2).2.1
          (hπ_unt i hi1 hi2).2.2
      let flip : Fin st.c₀ → Bool := fun i =>
        if h1 : i = st.i_ξ then !(d_ξ == d_ξ')
        else if h2 : i = st.i_η then !(d_η == d_η')
        else !((hdir i h1 h2).choose == (hdir i h1 h2).choose_spec.choose)
      refine ⟨flip, fun h => absurd h hb0, by simp [flip], by simp [flip, hi_ne.symm],
        fun i hi1 hi2 φD v₀ v₀' δa δb ma mb da db hδa hδb _ hmac hmbc hmad hmbd hmae hmbe => ?_⟩
      obtain ⟨w₀, w₀', δw1, δw2, mw1, mw2, dw1, dw2, hδw1, hδw2, _, hmw1c, hmw2c, hmw1d, hmw2d, hmw1e, hmw2e, hbeq⟩ :=
        (hdir i hi1 hi2).choose_spec.choose_spec φD
      have hdisY := (untouched_cuff_properties hS hY hψ hF hb hP st.hf st.hXC st.hX'C hi1 hi2).1
      have hdisY' := (untouched_cuff_properties hS hY' hψ' hF' hb' hP' st.hf' st.hX2C st.hX2'C (hnot0 i hi1 hi2).1 (hnot0 i hi1 hi2).2).1
      have hda : da = dw1 := local_dir_eq_on_untouched hψ (φ i) φD
        (fun z => ⟨⟨_, (φ i z).2, rfl⟩, Set.disjoint_left.mp hdisY (φ i z).2⟩) hδa hδw1 hmac hmw1c hmad hmw1d hmae hmw1e
      have hdb : db = dw2 := local_dir_eq_on_untouched hψ' (φ' (π i)) φD
        (fun z => ⟨by rw [← (hπ_unt i hi1 hi2).2.2]; exact ⟨_, (φ' (π i) z).2, rfl⟩, Set.disjoint_left.mp hdisY' (φ' (π i) z).2⟩) hδb hδw2 hmbc hmw2c hmbd hmw2d hmbe hmw2e
      simp only [flip, dite_eq_right hi1, dite_eq_right hi2, Bool.not_not, hda, hdb, hbeq]
  obtain ⟨flip, hfl_const, hfl_ξ, hfl_η, hfl_unt⟩ := hex_flip
  obtain ⟨H₀, hH₀⟩ := exists_homeo_match_cuffs st.hf st.hf' π flip hfl_const
  obtain ⟨mξ, hmξc, hmξe⟩ := exists_lift (φ st.i_ξ) L.cξ (fun u hu => st.hXC (himξ ▸ ⟨u, hu, rfl⟩))
  obtain ⟨mη, hmηc, hmηe⟩ := exists_lift (φ st.i_η) L.cη (fun u hu => st.hX'C (himη ▸ ⟨u, hu, rfl⟩))
  obtain ⟨mξ', hmξ'c, hmξ'e⟩ := exists_lift (φ' j_ξ) L₀'.cξ (fun u hu => hX₀C' (him₁' ▸ ⟨u, hu, rfl⟩))
  obtain ⟨mη', hmη'c, hmη'e⟩ := exists_lift (φ' j_η) L₀'.cη (fun u hu => hX₀''C' (him₂' ▸ ⟨u, hu, rfl⟩))
  set u1_ξ := if b_ξ then u_t else u_s
  set u2_ξ := if b_ξ then u_s + 1 else u_t
  set u1_η := if b_ξ then u_s else u_t
  set u2_η := if b_ξ then u_t else u_s + 1
  have h_uξ_lt : u1_ξ < u2_ξ ∧ u2_ξ < u1_ξ + 1 := by cases hbξ : b_ξ <;> simp only [u1_ξ, u2_ξ, hbξ, Bool.false_eq_true, ↓reduceIte] <;> exact ⟨by linarith, by linarith⟩
  have h_uη_lt : u1_η < u2_η ∧ u2_η < u1_η + 1 := by cases hbξ : b_ξ <;> simp only [u1_η, u2_η, hbξ, Bool.false_eq_true, ↓reduceIte] <;> exact ⟨by linarith, by linarith⟩
  have h_uξ_ends : ((φS (ee u1_ξ)).1 = t ∧ (φS (ee u2_ξ)).1 = s) ∨ ((φS (ee u1_ξ)).1 = s ∧ (φS (ee u2_ξ)).1 = t) := by
    cases hbξ : b_ξ <;> simp only [u1_ξ, u2_ξ, hbξ, Bool.false_eq_true, ↓reduceIte, ee_add_one] <;> [exact .inr ⟨hus, hut⟩; exact .inl ⟨hut, hus⟩]
  have h_uη_ends : ((φS (ee u1_η)).1 = t ∧ (φS (ee u2_η)).1 = s) ∨ ((φS (ee u1_η)).1 = s ∧ (φS (ee u2_η)).1 = t) := by
    cases hbξ : b_ξ <;> simp only [u1_η, u2_η, hbξ, Bool.false_eq_true, ↓reduceIte, ee_add_one] <;> [exact .inl ⟨hut, hus⟩; exact .inr ⟨hus, hut⟩]
  have hx_ξ_in : x_ξ ∈ (fun w => (φS (ee w)).1) '' Ioo u1_ξ u2_ξ := by cases hbξ : b_ξ <;> simp only [x_ξ, u1_ξ, u2_ξ, hbξ, Bool.false_eq_true, ↓reduceIte]; exact hx₂G₂; exact hx₁G₁
  have hx_η_in : x_η ∈ (fun w => (φS (ee w)).1) '' Ioo u1_η u2_η := by cases hbξ : b_ξ <;> simp only [x_η, u1_η, u2_η, hbξ, Bool.false_eq_true, ↓reduceIte]; exact hx₁G₁; exact hx₂G₂
  obtain ⟨dm_ξ, hdm_ξ, hd_ξ_rel, _⟩ :=
    twosided_cuff_info hY hS hne hψ hF hb hP L ha0 ha1 himξ hiξ hst φS (hC_cuff st.i_ξ) (hC_cuff st.i_η) (fun e => hi_ne (hC_inj e)) st.hX'C (φ st.i_ξ)
      hmξc hmξe h_uξ_lt.1 h_uξ_lt.2 h_uξ_ends (by rw [hv_ξy, hψy_ξ]; exact hx_ξ_in) hδ_ξ hm_ξlc hm_ξld hm_ξle
  obtain ⟨dm_η, hdm_η, hd_η_rel, _⟩ :=
    twosided_cuff_info hY hS hne hψ hF hb hP_sw L.swap ha0 ha1 himη hiη hst φS (hC_cuff st.i_η) (hC_cuff st.i_ξ) (fun e => hi_ne (hC_inj e).symm) st.hXC (φ st.i_η)
      hmηc hmηe h_uη_lt.1 h_uη_lt.2 h_uη_ends (by rw [hv_ηy, hψy_η]; exact hx_η_in) hδ_η hm_ηlc hm_ηld hm_ηle
  obtain ⟨dm_ξ', hdm_ξ', hd_ξ'_rel, hgap_ξ'⟩ :=
    twosided_cuff_info hY' hS hne hψ' hF' hb' hP₀' L₀' ha'0 ha'1 him₁' hi₁' hst φS (hC'_cuff j_ξ) (hC'_cuff j_η) (fun e => hj_ne' (hC'_inj e)) hX₀''C' (φ' j_ξ)
      hmξ'c hmξ'e h_uξ_lt.1 h_uξ_lt.2 h_uξ_ends (by rw [hv_ξ'y, hψ'y_ξ]; exact hx_ξ_in) hδ_ξ' hm_ξ'lc hm_ξ'ld hm_ξ'le
  obtain ⟨dm_η', hdm_η', hd_η'_rel, _⟩ :=
    twosided_cuff_info hY' hS hne hψ' hF' hb' hP₀'_sw L₀'.swap ha'0 ha'1 him₂' hi₂' hst φS (hC'_cuff j_η) (hC'_cuff j_ξ) (fun e => hj_ne' (hC'_inj e).symm) hX₀C' (φ' j_η)
      hmη'c hmη'e h_uη_lt.1 h_uη_lt.2 h_uη_ends (by rw [hv_η'y, hψ'y_η]; exact hx_η_in) hδ_η' hm_η'lc hm_η'ld hm_η'le
  let p_ξ : ℝ → ℝ := fun u => if flip st.i_ξ then -mξ u else mξ u
  let p_η : ℝ → ℝ := fun u => if flip st.i_η then -mη u else mη u
  have hpξc : ContinuousOn p_ξ (Icc 0 1) := by cases hfl : flip st.i_ξ <;> simp only [p_ξ, hfl, Bool.false_eq_true, ↓reduceIte]; exact hmξc; exact hmξc.neg
  have hpηc : ContinuousOn p_η (Icc 0 1) := by cases hfl : flip st.i_η <;> simp only [p_η, hfl, Bool.false_eq_true, ↓reduceIte]; exact hmηc; exact hmηc.neg
  have hpξe : ∀ u ∈ Icc (0 : ℝ) 1, (φ' j_ξ (ee (p_ξ u))).1 = H₀ (ξ u) := fun u hu => by
    rw [← hmξe u hu, hH₀ st.i_ξ (ee (mξ u)), hπ_ξ]
    cases hfl : flip st.i_ξ <;> simp only [p_ξ, hfl, Bool.false_eq_true, ↓reduceIte]
    · rfl
    · rw [show ee (-mξ u) = (ee (mξ u))⁻¹ by unfold ee; rw [mul_neg, Circle.exp_neg]]
  have hpηe : ∀ u ∈ Icc (0 : ℝ) 1, (φ' j_η (ee (p_η u))).1 = H₀ (η u) := fun u hu => by
    rw [← hmηe u hu, hH₀ st.i_η (ee (mη u)), hπ_η]
    cases hfl : flip st.i_η <;> simp only [p_η, hfl, Bool.false_eq_true, ↓reduceIte]
    · rfl
    · rw [show ee (-mη u) = (ee (mη u))⁻¹ by unfold ee; rw [mul_neg, Circle.exp_neg]]
  have hpξd : if dm_ξ' then StrictMonoOn p_ξ (Icc 0 1) else StrictAntiOn p_ξ (Icc 0 1) := by
    have hrel_dm : (!flip st.i_ξ) = (dm_ξ == dm_ξ') := by
      rcases h_uξ_ends with ⟨h1, -⟩ | ⟨h1, -⟩
      · rw [← hd_ξ_rel.1 h1, ← hd_ξ'_rel.1 h1]; exact hfl_ξ
      · rw [hd_ξ_rel.2 h1, hd_ξ'_rel.2 h1] at hfl_ξ; cases dm_ξ <;> cases dm_ξ' <;> simpa using hfl_ξ
    exact strictMono_flip_dir hrel_dm hdm_ξ
  have hpηd : if dm_η' then StrictMonoOn p_η (Icc 0 1) else StrictAntiOn p_η (Icc 0 1) := by
    have hrel_dm : (!flip st.i_η) = (dm_η == dm_η') := by
      rcases h_uη_ends with ⟨h1, -⟩ | ⟨h1, -⟩
      · rw [← hd_η_rel.1 h1, ← hd_η'_rel.1 h1]; exact hfl_η
      · rw [hd_η_rel.2 h1, hd_η'_rel.2 h1] at hfl_η; cases dm_η <;> cases dm_η' <;> simpa using hfl_η
    exact strictMono_flip_dir hrel_dm hdm_η
  obtain ⟨M₁, hM1a, hM1_fix, kM1, hkM1p, hkM1e⟩ := exists_align_one_arc_any hY' (hC'_cuff j_ξ) (φ' j_ξ) dm_ξ'
    hpξc hmξ'c hpξd hdm_ξ' (inj_of_lift hpξe (fun a ha b hb he => hiξ ha hb (H₀.injective he))) (inj_of_lift hmξ'e hi₁')
  obtain ⟨M₂, hM2a, hM2_fix, kM2, _, _⟩ := exists_align_one_arc_any hY' (hC'_cuff j_η) (φ' j_η) dm_η'
    hpηc hmη'c hpηd hdm_η' (inj_of_lift hpηe (fun a ha b hb he => hiη ha hb (H₀.injective he))) (inj_of_lift hmη'e hi₂')
  let H : Y ≃ₜ Y' := (H₀.trans M₁).trans M₂
  have hHξ : ∀ u ∈ Icc (0 : ℝ) 1, H (ξ u) = ξ₀' u := fun u hu => by
    simp only [H, Homeomorph.trans_apply]; rw [← hpξe u hu, hM1a u hu, hmξ'e u hu]
    exact hM2_fix (C' j_ξ) (hC'_cuff j_ξ) (fun e => hj_ne' (hC'_inj e)) _ (hX₀C' (him₁' ▸ ⟨u, hu, rfl⟩))
  have hHη : ∀ u ∈ Icc (0 : ℝ) 1, H (η u) = η₀' u := fun u hu => by
    simp only [H, Homeomorph.trans_apply]
    rw [← hpηe u hu, hM1_fix (C' j_η) (hC'_cuff j_η) (fun e => hj_ne' (hC'_inj e).symm) _ (φ' j_η _).2, hM2a u hu, hmη'e u hu]
  obtain ⟨α, hα_comm, hαF⟩ := exists_descend_of_lifts hψ hψ' L L₀' hP hP₀' himξ himη him₁' him₂' H hHξ hHη
  have hαs : α s = s := by
    have := hα_comm (ξ 0)
    rw [L.hξ 0 ⟨le_rfl, zero_le_one⟩, ha0, hHξ 0 ⟨le_rfl, zero_le_one⟩, L₀'.hξ 0 ⟨le_rfl, zero_le_one⟩, ha'0] at this; exact this
  have hαt : α t = t := by
    have := hα_comm (ξ 1)
    rw [L.hξ 1 ⟨zero_le_one, le_rfl⟩, ha1, hHξ 1 ⟨zero_le_one, le_rfl⟩, L₀'.hξ 1 ⟨zero_le_one, le_rfl⟩, ha'1] at this; exact this
  have hnull : HasNullSignature α := fun D φD hD => by
    by_cases hDCs : D = connectedComponentIn (bd S) s
    · subst hDCs
      have hαCs : ∀ x, x ∈ connectedComponentIn (bd S) s ↔ α x ∈ connectedComponentIn (bd S) s := fun x => by
        have h1 : α '' connectedComponentIn (bd S) s = connectedComponentIn (bd S) s := by
          rw [α.image_connectedComponentIn hsb, image_bd_homeomorph α, hαs]
        exact ⟨fun hx => h1 ▸ mem_image_of_mem α hx, fun hαx => by obtain ⟨z, hz, hzα⟩ := h1.symm.subset hαx; rwa [α.injective hzα] at hz⟩
      let k0 : Circle ≃ₜ Circle := if flip st.i_ξ then Homeomorph.inv Circle else Homeomorph.refl Circle
      let kH : Circle ≃ₜ Circle := k0.trans kM1
      have hkH_eq : ∀ z : Circle, H (φ st.i_ξ z).1 = (φ' j_ξ (kH z)).1 := fun z => by
        simp only [H, kH, Homeomorph.trans_apply]
        have h1 : H₀ (φ st.i_ξ z).1 = (φ' j_ξ (k0 z)).1 := by
          have h := hH₀ st.i_ξ z
          change H₀ (φ st.i_ξ z).1 = (φ' (π st.i_ξ) _).1 at h
          rw [hπ_ξ] at h
          cases hfl : flip st.i_ξ <;> simp only [k0, hfl, Bool.false_eq_true, ↓reduceIte] at h ⊢ <;> exact h
        rw [h1, hkM1e (k0 z)]
        exact hM2_fix (C' j_ξ) (hC'_cuff j_ξ) (fun e => hj_ne' (hC'_inj e)) _ (φ' j_ξ _).2
      have hkH_or : if !flip st.i_ξ then PreservesCircleOrientation kH
          else PreservesCircleOrientation ((Homeomorph.inv Circle).trans kH) := by
        cases hfl : flip st.i_ξ <;> simp only [kH, k0, hfl, Bool.not_false, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
        · exact preservesCircleOrientation_trans preservesCircleOrientation_refl hkM1p
        · have : (Homeomorph.inv Circle).trans ((Homeomorph.inv Circle).trans kM1) = kM1 := Homeomorph.ext fun z => by simp
          rw [this]; exact hkM1p
      obtain ⟨w_ξ', -, hw_ξ'e⟩ := exists_param (kH (ee v_ξ))
      have hw_ξ'y : (φ' j_ξ (ee w_ξ')).1 = H y_ξ := by rw [hw_ξ'e, ← hkH_eq, hv_ξy]
      have hw_ξ'nF' : ψ' (φ' j_ξ (ee w_ξ')).1 ∉ F' := by
        rw [hw_ξ'y, ← hα_comm y_ξ, hψy_ξ]; intro hF'; obtain ⟨z, hzF, hzα⟩ := hαF.symm.subset hF'
        exact hx_ξ_nF (α.injective hzα ▸ hzF)
      have hw_ξ'Cs : ψ' (φ' j_ξ (ee w_ξ')).1 ∈ connectedComponentIn (bd S) s := by
        rw [hw_ξ'y, ← hα_comm y_ξ, hψy_ξ]; exact (hαCs x_ξ).mp hx_ξ_Cs
      obtain ⟨δa, ma, da, hδa, _, hmac, hmad, hmae, hsig_a⟩ :=
        exists_cuff_local_dir hY hS hψ hF st.AY AS (hC_bd st.i_ξ) hCs_cuff (φ st.i_ξ) φD (by rw [hv_ξy, hψy_ξ]; exact hx_ξ_Cs) (by rw [hv_ξy, hψy_ξ]; exact hx_ξ_nF)
      obtain ⟨δb, mb, db, hδb, _, hmbc, hmbd, hmbe, hsig_b⟩ :=
        exists_cuff_local_dir hY' hS hψ' hF' st.AY' AS (hC'_bd j_ξ) hCs_cuff (φ' j_ξ) φD hw_ξ'Cs hw_ξ'nF'
      obtain ⟨δbS, mbS, dbS, hδbS, _, hmbSc, hmbSd, hmbSe, hsig_bS⟩ :=
        exists_cuff_local_dir hY' hS hψ' hF' st.AY' AS (hC'_bd j_ξ) hCs_cuff (φ' j_ξ) φS hw_ξ'Cs hw_ξ'nF'
      have hdbS_eq : dbS = d_ξ' := by
        obtain ⟨hpq', hsp', hoff', hgap', ⟨v_s', hv_s'_in, hv_s'_ee⟩⟩ := hgap_ξ'
        set p' := if dm_ξ' then mξ' 1 else mξ' 0
        set q' := if dm_ξ' then mξ' 0 + 1 else mξ' 1 + 1
        set a₀' := if dm_ξ' then mξ' 0 else mξ' 1
        set w_s := a₀' + Int.fract (w_ξ' - a₀')
        have hws_ee : ee w_s = ee w_ξ' := ee_eq_iff.mpr ⟨-⌊w_ξ' - a₀'⌋, by simp only [w_s, Int.cast_neg]; linarith [Int.floor_add_fract (w_ξ' - a₀')]⟩
        have hws_in : w_s ∈ Ioo p' q' := by
          have hlo : a₀' ≤ w_s := by simp only [w_s]; linarith [Int.fract_nonneg (w_ξ' - a₀')]
          have hhi : w_s < q' := by have : q' = a₀' + 1 := by cases dm_ξ' <;> rfl
                                    rw [this]; simp only [w_s]; linarith [Int.fract_lt_one (w_ξ' - a₀')]
          refine ⟨?_, hhi⟩
          by_contra hle'
          have hmem : w_s ∈ Icc (mξ' 0) (mξ' 1) ∨ w_s ∈ Icc (mξ' 1) (mξ' 0) := by
            cases dm_ξ' <;> simp only [p', a₀', Bool.false_eq_true, ↓reduceIte] at hlo hle'
            · exact .inr ⟨hlo, not_lt.mp hle'⟩
            · exact .inl ⟨hlo, not_lt.mp hle'⟩
          obtain ⟨u, hu, hue⟩ : ∃ u ∈ Icc (0 : ℝ) 1, mξ' u = w_s :=
            hmem.elim (fun h => intermediate_value_Icc zero_le_one hmξ'c h) (fun h => intermediate_value_Icc' zero_le_one hmξ'c h)
          obtain ⟨_, _, _, _, _, _, _, hun0', -⟩ := id hP₀'
          exact hw_ξ'nF' (by rw [← hws_ee, ← hue, hmξ'e u hu]; exact show ξ₀' u ∈ ψ' ⁻¹' F' from hun0' ▸ Or.inl (him₁' ▸ ⟨u, hu, rfl⟩))
        have hmbS_ws : ∀ r ∈ Icc (-δbS) δbS, ψ' (φ' j_ξ (ee (w_s + r))).1 = (φS (ee (mbS r))).1 := fun r hr => by
          obtain ⟨j, hj⟩ := ee_eq_iff.mp hws_ee
          rw [show ee (w_s + r) = ee (w_ξ' + r) from ee_eq_iff.mpr ⟨j, by linarith⟩]; exact hmbSe r hr
        have hmξ'_vs : ∀ r ∈ Icc (-δ_ξ') δ_ξ', ψ' (φ' j_ξ (ee (v_s' + r))).1 = (φS (ee (m_ξ'l r))).1 := fun r hr => by
          obtain ⟨j, hj⟩ := ee_eq_iff.mp hv_s'_ee
          rw [show ee (v_s' + r) = ee (v_ξ' + r) from ee_eq_iff.mpr ⟨j, by linarith⟩]; exact hm_ξ'le r hr
        exact local_dir_eq_on_interval hψ' (φ' j_ξ) φS hpq' hsp'
          (fun v hv => ⟨by obtain ⟨w, -, hw⟩ := hgap' v hv; rw [← hw]; exact (φS _).2, hoff' v hv⟩)
          hws_in hv_s'_in hδbS hδ_ξ' hmbSc hm_ξ'lc hmbSd hm_ξ'ld hmbS_ws hmξ'_vs
      have hdab : (da == db) = (d_ξ == d_ξ') := by
        let kSD : Circle ≃ₜ Circle := φD.trans φS.symm
        have hcs_const : ∀ x ∈ connectedComponentIn (bd S) s,
            cuffSign AS φD x - cuffSign AS φS x = if PreservesCircleOrientation kSD then 0 else 1 := fun x hx => by
          have h1 := cuffSign_comp_circle AS (connectedComponentIn_subset _ _) φS kSD hx
          have : φD = kSD.trans φS := Homeomorph.ext fun z => by simp [kSD]
          rw [this, h1]; ring
        have hsub1 : (if da then (0 : ZMod 2) else 1) - (if d_ξ then 0 else 1) = if PreservesCircleOrientation kSD then 0 else 1 := by
          have h1 := cutOrientDiff_cuff_mono hY hS hψ hF st.AY AS (hC_bd st.i_ξ) (connectedComponentIn_subset _ _)
            (φ st.i_ξ) φS (φ st.i_ξ _).2 (by rw [hv_ξy, hψy_ξ]; exact hx_ξ_nF) hδ_ξ d_ξ hm_ξlc hm_ξld hm_ξle rfl
          have h2 := hcs_const (ψ (φ st.i_ξ (ee v_ξ)).1) (by rw [hv_ξy, hψy_ξ]; exact hx_ξ_Cs); linear_combination h1 + h2 - hsig_a
        have hsub2 : (if db then (0 : ZMod 2) else 1) - (if dbS then 0 else 1) = if PreservesCircleOrientation kSD then 0 else 1 := by
          have h2 := hcs_const _ hw_ξ'Cs; linear_combination hsig_bS + h2 - hsig_b
        exact bool_beq_of_zmod2_sub_eq (by rw [← hdbS_eq]; linear_combination hsub1 - hsub2)
      exact preservesCircleOrientation_of_local_dirs hα_comm hαCs φD (φ st.i_ξ) (φ' j_ξ) (!flip st.i_ξ) hkH_or hkH_eq
        hw_ξ'e.symm hδa hδb hmac hmbc hmad hmbd hmae hmbe (by rw [hdab]; exact hfl_ξ)
    · have hsD : s ∉ D := fun hs => hDCs (by by_contra hne'; exact Set.disjoint_left.mp (cuffs_disjoint hD hCs_cuff hne') hs (mem_connectedComponentIn hsb))
      have htD : t ∉ D := fun ht => hDCs (by by_contra hne'; exact Set.disjoint_left.mp (cuffs_disjoint hD hCs_cuff hne') ht (hst ▸ mem_connectedComponentIn (show t ∈ bd S from (show t ∈ F ∩ bd S from hb ▸ mem_insert_of_mem _ rfl).2)))
      obtain ⟨hpre_cuff, hpre_disj, him⟩ := untouched_cuff_preimage hY hS hψ hF hb hD hsD htD
      obtain ⟨i, hi_lt, hi_eq'⟩ := (cuffs_eq_holeC st.hf).subset hpre_cuff
      let iF : Fin st.c₀ := ⟨i, hi_lt⟩
      have hξ0 : ξ 0 ∈ X := himξ ▸ ⟨0, ⟨le_rfl, zero_le_one⟩, rfl⟩
      have hη0 : η 0 ∈ X' := himη ▸ ⟨0, ⟨le_rfl, zero_le_one⟩, rfl⟩
      have hi1 : iF ≠ st.i_ξ := fun he =>
        Set.disjoint_left.mp hpre_disj (by rw [← hi_eq', show holeC st.a₀ st.b₀ st.c₀ st.f i = C iF from rfl, he]; exact st.hXC hξ0) (show ξ 0 ∈ ψ ⁻¹' F from hun ▸ Or.inl hξ0)
      have hi2 : iF ≠ st.i_η := fun he =>
        Set.disjoint_left.mp hpre_disj (by rw [← hi_eq', show holeC st.a₀ st.b₀ st.c₀ st.f i = C iF from rfl, he]; exact st.hX'C hη0) (show η 0 ∈ ψ ⁻¹' F from hun ▸ Or.inr hη0)
      have hDeq : ψ '' C iF = D := by rw [show C iF = holeC st.a₀ st.b₀ st.c₀ st.f i from rfl, hi_eq']; exact him
      subst hDeq
      have huY := untouched_cuff_properties hS hY hψ hF hb hP st.hf st.hXC st.hX'C hi1 hi2
      have huY' := untouched_cuff_properties hS hY' hψ' hF' hb' hP' st.hf' st.hX2C st.hX2'C (hnot0 iF hi1 hi2).1 (hnot0 iF hi1 hi2).2
      exact untouched_cuff_null hS hY hY' AS st.AY st.AY' hψ hψ' hF hF' st.hf st.hf'
        huY.1 huY'.1 huY.2.1 huY'.2.2.2.2 (hπ_unt iF hi1 hi2).2.2 H (flip iF)
        (fun z => by
          simp only [H, Homeomorph.trans_apply, hH₀ iF z]
          rw [hM1_fix (C' (π iF)) (hC'_cuff (π iF)) (fun e => (hπ_unt iF hi1 hi2).1 (hC'_inj e)) _ (φ' (π iF) _).2]
          exact hM2_fix (C' (π iF)) (hC'_cuff (π iF)) (fun e => (hπ_unt iF hi1 hi2).2.1 (hC'_inj e)) _ (φ' (π iF) _).2)
        (hfl_unt iF hi1 hi2) α hα_comm φD
  exact parallel_conn hS hne hb' hl' hαF hαs hαt hnull

end CaseSame2Sided

/-! ### Master Arc-Parallelism Theorem -/

section ParallelOfCocycle

variable {S : Type u} [TopologicalSpace S]

/-- Core theorem: given cuttings `Y, Y'` of proper `I`-arcs `F, F'` with the same distinct boundary
ends `s ≠ t`, `ConnectedSpace Y`, `BdCohRel s t (arcCocycle F') (arcCocycle F)`, and
`cocInt (w1 AS) a' = cocInt (w1 AS) a`, there exists a homeomorphism `β : S ≃ₜ S` with
`β '' F = F'` and `∀ x ∈ bd S, β x = x`. -/
theorem parallel_of_cocycle_eq_of_cut [ConnectedSpace S] (hS : IsSurface S)
    {F F' : Set S} {s t : S} (hne : s ≠ t)
    (hb : F ∩ bd S = {s, t}) (hb' : F' ∩ bd S = {s, t})
    (hl : IsLineWithEnds F s t) (hl' : IsLineWithEnds F' s t)
    {Y Y' : Type u} [TopologicalSpace Y] [T2Space Y] [TopologicalSpace Y'] [T2Space Y']
    {ψ : Y → S} {ψ' : Y' → S} (hY : IsSurface Y) (hY' : IsSurface Y')
    (hψ : IsCutting ψ F) (hψ' : IsCutting ψ' F')
    {X X' : Set Y} {X₂ X₂' : Set Y'}
    (hP : LiftPair ψ F s t X X') (hP' : LiftPair ψ' F' s t X₂ X₂')
    {a a' : ℝ → S} {ξ η : ℝ → Y} {ξ' η' : ℝ → Y'}
    (L : ArcLift ψ F a ξ η) (L' : ArcLift ψ' F' a' ξ' η')
    (ha0 : a 0 = s) (ha1 : a 1 = t) (ha'0 : a' 0 = s) (ha'1 : a' 1 = t)
    (himξ : ξ '' Icc 0 1 = X) (himη : η '' Icc 0 1 = X')
    (himξ' : ξ' '' Icc 0 1 = X₂) (himη' : η' '' Icc 0 1 = X₂')
    (hiξ : InjOn ξ (Icc 0 1)) (hiη : InjOn η (Icc 0 1))
    (hiξ' : InjOn ξ' (Icc 0 1)) (hiη' : InjOn η' (Icc 0 1))
    (hconn : ConnectedSpace Y)
    (AS : SurfAtlas S)
    (hrel : BdCohRel s t (arcCocycle hS hne hb' hl') (arcCocycle hS hne hb hl))
    (hw1 : cocInt (w1 AS) a' = cocInt (w1 AS) a) :
    ∃ β : S ≃ₜ S, β '' F = F' ∧ ∀ x ∈ bd S, β x = x := by
  classical
  have : CompactSpace Y := hY.1
  have : CompactSpace Y' := hY'.1
  have : T2Space S := hS.2.1
  have hF : IsClosed F := hl.isCompact.isClosed
  have hF' : IsClosed F' := hl'.isCompact.isClosed
  have hsb : s ∈ bd S := (show s ∈ F ∩ bd S from hb ▸ mem_insert _ _).2
  have htb : t ∈ bd S := (show t ∈ F ∩ bd S from hb ▸ mem_insert_of_mem _ rfl).2
  obtain ⟨AY⟩ := exists_surfAtlas hY
  obtain ⟨AY'⟩ := exists_surfAtlas hY'
  obtain ⟨hconn', hsame_cut, a₀, b₀, c₀, ⟨eY⟩, ⟨eY'⟩⟩ :=
    same_cut_model_of_cocycle_eq hS hne hb hb' hl hl' hY hY' hψ hψ' hP hP' L L'
      ha0 ha1 ha'0 ha'1 himξ himη himξ' himη' hiξ hiη hiξ' hiη' hconn AS hrel hw1
  obtain ⟨_, fM, hfM⟩ := presents_ew a₀ b₀ c₀
  let f : ℕ × ℂ → Y := eY.symm ∘ fM
  let f' : ℕ × ℂ → Y' := eY'.symm ∘ fM
  have hf : Presents (sW (ew a₀ b₀ c₀)) f := presents_comp hfM eY.symm
  have hf' : Presents (sW (ew a₀ b₀ c₀)) f' := presents_comp hfM eY'.symm
  let C : Fin c₀ → Set Y := fun i => holeC a₀ b₀ c₀ f i.1
  let C' : Fin c₀ → Set Y' := fun j => holeC a₀ b₀ c₀ f' j.1
  have hC_inj : Function.Injective C := fun i₁ i₂ he => by
    by_contra hne'
    have h1 : (holeParam hf i₁.isLt (ee 0)).1 ∈ C i₁ := (holeParam hf i₁.isLt _).2
    have h2 : (holeParam hf i₁.isLt (ee 0)).1 ∈ C i₂ := he ▸ h1
    exact Set.disjoint_left.mp (disjoint_holeC hf i₁.isLt i₂.isLt (fun h => hne' (Fin.ext h))) h1 h2
  have hC'_inj : Function.Injective C' := fun j₁ j₂ he => by
    by_contra hne'
    have h1 : (holeParam hf' j₁.isLt (ee 0)).1 ∈ C' j₁ := (holeParam hf' j₁.isLt _).2
    have h2 : (holeParam hf' j₁.isLt (ee 0)).1 ∈ C' j₂ := he ▸ h1
    exact Set.disjoint_left.mp (disjoint_holeC hf' j₁.isLt j₂.isLt (fun h => hne' (Fin.ext h))) h1 h2
  obtain ⟨_, _, _, _, _, _, _, hun, -⟩ := id hP
  obtain ⟨_, _, _, _, _, _, _, hun', -⟩ := id hP'
  have hXb : X ⊆ bd Y := fun y hy => hψ.2.2.2.2 (hun ▸ Or.inl hy)
  have hX'b : X' ⊆ bd Y := fun y hy => hψ.2.2.2.2 (hun ▸ Or.inr hy)
  have hX2b : X₂ ⊆ bd Y' := fun y hy => hψ'.2.2.2.2 (hun' ▸ Or.inl hy)
  have hX2'b : X₂' ⊆ bd Y' := fun y hy => hψ'.2.2.2.2 (hun' ▸ Or.inr hy)
  obtain ⟨iξ_n, hiξ_lt, hiξ_eq⟩ := (cuffs_eq_holeC hf).subset (⟨_, hXb (himξ ▸ ⟨0, ⟨le_rfl, zero_le_one⟩, rfl⟩), rfl⟩ : connectedComponentIn (bd Y) (ξ 0) ∈ cuffs Y)
  obtain ⟨iη_n, hiη_lt, hiη_eq⟩ := (cuffs_eq_holeC hf).subset (⟨_, hX'b (himη ▸ ⟨0, ⟨le_rfl, zero_le_one⟩, rfl⟩), rfl⟩ : connectedComponentIn (bd Y) (η 0) ∈ cuffs Y)
  obtain ⟨jξ_n, hjξ_lt, hjξ_eq⟩ := (cuffs_eq_holeC hf').subset (⟨_, hX2b (himξ' ▸ ⟨0, ⟨le_rfl, zero_le_one⟩, rfl⟩), rfl⟩ : connectedComponentIn (bd Y') (ξ' 0) ∈ cuffs Y')
  obtain ⟨jη_n, hjη_lt, hjη_eq⟩ := (cuffs_eq_holeC hf').subset (⟨_, hX2'b (himη' ▸ ⟨0, ⟨le_rfl, zero_le_one⟩, rfl⟩), rfl⟩ : connectedComponentIn (bd Y') (η' 0) ∈ cuffs Y')
  let i_ξ : Fin c₀ := ⟨iξ_n, hiξ_lt⟩
  let i_η : Fin c₀ := ⟨iη_n, hiη_lt⟩
  let j_ξ0 : Fin c₀ := ⟨jξ_n, hjξ_lt⟩
  let j_η0 : Fin c₀ := ⟨jη_n, hjη_lt⟩
  have hXC : X ⊆ C i_ξ := by rw [show C i_ξ = connectedComponentIn (bd Y) (ξ 0) from hiξ_eq]; exact (himξ ▸ isPreconnected_Icc.image _ L.cξ).subset_connectedComponentIn (himξ ▸ ⟨0, ⟨le_rfl, zero_le_one⟩, rfl⟩) hXb
  have hX'C : X' ⊆ C i_η := by rw [show C i_η = connectedComponentIn (bd Y) (η 0) from hiη_eq]; exact (himη ▸ isPreconnected_Icc.image _ L.cη).subset_connectedComponentIn (himη ▸ ⟨0, ⟨le_rfl, zero_le_one⟩, rfl⟩) hX'b
  have hX2C : X₂ ⊆ C' j_ξ0 := by rw [show C' j_ξ0 = connectedComponentIn (bd Y') (ξ' 0) from hjξ_eq]; exact (himξ' ▸ isPreconnected_Icc.image _ L'.cξ).subset_connectedComponentIn (himξ' ▸ ⟨0, ⟨le_rfl, zero_le_one⟩, rfl⟩) hX2b
  have hX2'C : X₂' ⊆ C' j_η0 := by rw [show C' j_η0 = connectedComponentIn (bd Y') (η' 0) from hjη_eq]; exact (himη' ▸ isPreconnected_Icc.image _ L'.cη).subset_connectedComponentIn (himη' ▸ ⟨0, ⟨le_rfl, zero_le_one⟩, rfl⟩) hX2'b
  let st : CutSetup ψ ψ' F F' s t X X' X₂ X₂' a a' ξ η ξ' η' :=
    ⟨a₀, b₀, c₀, f, f', hf, hf', AY, AY', i_ξ, i_η, j_ξ0, j_η0, hiξ_eq, hiη_eq, hjξ_eq, hjη_eq, hXC, hX'C, hX2C, hX2'C⟩
  have hunt_match : ∀ i : Fin c₀, i ≠ i_ξ → i ≠ i_η → ∃ j : Fin c₀, j ≠ j_ξ0 ∧ j ≠ j_η0 ∧ ψ' '' C' j = ψ '' C i := fun i h1 h2 => by
    obtain ⟨_, hD, hsD, htD, _⟩ := untouched_cuff_properties hS hY hψ hF hb hP hf hXC hX'C h1 h2
    obtain ⟨hpre_cuff, hpre_disj, him⟩ := untouched_cuff_preimage hY' hS hψ' hF' hb' hD hsD htD
    obtain ⟨j_n, hj_lt, hj_eq⟩ := (cuffs_eq_holeC hf').subset hpre_cuff
    let j : Fin c₀ := ⟨j_n, hj_lt⟩
    have hξ'0 : ξ' 0 ∈ X₂ := himξ' ▸ ⟨0, ⟨le_rfl, zero_le_one⟩, rfl⟩
    have hη'0 : η' 0 ∈ X₂' := himη' ▸ ⟨0, ⟨le_rfl, zero_le_one⟩, rfl⟩
    have hj1 : j ≠ j_ξ0 := fun he => Set.disjoint_left.mp hpre_disj
      (by rw [← hj_eq, show holeC a₀ b₀ c₀ f' j_n = C' j from rfl, he]; exact hX2C hξ'0)
      (show ξ' 0 ∈ ψ' ⁻¹' F' from hun' ▸ Or.inl hξ'0)
    have hj2 : j ≠ j_η0 := fun he => Set.disjoint_left.mp hpre_disj
      (by rw [← hj_eq, show holeC a₀ b₀ c₀ f' j_n = C' j from rfl, he]; exact hX2'C hη'0)
      (show η' 0 ∈ ψ' ⁻¹' F' from hun' ▸ Or.inr hη'0)
    exact ⟨j, hj1, hj2, by rw [show C' j = holeC a₀ b₀ c₀ f' j_n from rfl, hj_eq]; exact him⟩
  have hbuild_perm_one : i_ξ = i_η → j_ξ0 = j_η0 →
      ∃ π : Equiv.Perm (Fin c₀), π i_ξ = j_ξ0 ∧ ∀ i : Fin c₀, i ≠ i_ξ → π i ≠ j_ξ0 ∧ ψ' '' C' (π i) = ψ '' C i := by
    intro hi_eq hj_eq
    let f_to : Fin c₀ → Fin c₀ := fun i => if h : i = i_ξ then j_ξ0 else (hunt_match i h (hi_eq ▸ h)).choose
    have hf_inj : Function.Injective f_to := fun i₁ i₂ he => by
      dsimp only [f_to] at he; split_ifs at he with h1 h2 h2
      · rw [h1, h2]
      · exact absurd he.symm (hunt_match i₂ h2 (hi_eq ▸ h2)).choose_spec.1
      · exact absurd he (hunt_match i₁ h1 (hi_eq ▸ h1)).choose_spec.1
      · have s1 := (hunt_match i₁ h1 (hi_eq ▸ h1)).choose_spec.2.2
        have s2 := (hunt_match i₂ h2 (hi_eq ▸ h2)).choose_spec.2.2
        rw [he] at s1
        exact hC_inj (by dsimp only [C]; rw [← (untouched_cuff_properties hS hY hψ hF hb hP hf hXC hX'C h1 (hi_eq ▸ h1)).2.2.2.2,
          s1.symm.trans s2, (untouched_cuff_properties hS hY hψ hF hb hP hf hXC hX'C h2 (hi_eq ▸ h2)).2.2.2.2])
    refine ⟨Equiv.ofBijective f_to (Finite.injective_iff_bijective.mp hf_inj), by simp [f_to], fun i hi => ?_⟩
    have hsp := (hunt_match i hi (hi_eq ▸ hi)).choose_spec
    simpa [f_to, hi] using ⟨hsp.1, hsp.2.2⟩
  have hbuild_perm_two : i_ξ ≠ i_η → j_ξ0 ≠ j_η0 →
      ∀ (j_ξ j_η : Fin c₀), ({j_ξ, j_η} : Set (Fin c₀)) = {j_ξ0, j_η0} → j_ξ ≠ j_η →
      ∃ π : Equiv.Perm (Fin c₀), π i_ξ = j_ξ ∧ π i_η = j_η ∧
        ∀ i : Fin c₀, i ≠ i_ξ → i ≠ i_η → π i ≠ j_ξ ∧ π i ≠ j_η ∧ ψ' '' C' (π i) = ψ '' C i := by
    intro hi_ne hj_ne j_ξ j_η hset hne_j
    have hnot_mem : ∀ j : Fin c₀, j ≠ j_ξ0 → j ≠ j_η0 → j ≠ j_ξ ∧ j ≠ j_η := fun j h1 h2 => by
      constructor <;> intro he
      · rcases (hset ▸ (he ▸ mem_insert _ _) : j ∈ ({j_ξ0, j_η0} : Set (Fin c₀))) with rfl | rfl <;> contradiction
      · rcases (hset ▸ (he ▸ mem_insert_of_mem _ rfl) : j ∈ ({j_ξ0, j_η0} : Set (Fin c₀))) with rfl | rfl <;> contradiction
    let f_to : Fin c₀ → Fin c₀ := fun i =>
      if h1 : i = i_ξ then j_ξ else if h2 : i = i_η then j_η else (hunt_match i h1 h2).choose
    have hf_inj : Function.Injective f_to := fun i₁ i₂ he => by
      dsimp only [f_to] at he; split_ifs at he with h1a h2a h2b h1b h2a' h2b' h2a'' h2b''
      · rw [h1a, h2a]
      · exact absurd he hne_j
      · exact absurd he.symm (hnot_mem _ (hunt_match i₂ h2a h2b).choose_spec.1 (hunt_match i₂ h2a h2b).choose_spec.2.1).1
      · exact absurd he.symm hne_j
      · rw [h1b, h2b']
      · exact absurd he.symm (hnot_mem _ (hunt_match i₂ h2a' h2b').choose_spec.1 (hunt_match i₂ h2a' h2b').choose_spec.2.1).2
      · exact absurd he (hnot_mem _ (hunt_match i₁ h1a h1b).choose_spec.1 (hunt_match i₁ h1a h1b).choose_spec.2.1).1
      · exact absurd he (hnot_mem _ (hunt_match i₁ h1a h1b).choose_spec.1 (hunt_match i₁ h1a h1b).choose_spec.2.1).2
      · have s1 := (hunt_match i₁ h1a h1b).choose_spec.2.2
        have s2 := (hunt_match i₂ h2a'' h2b'').choose_spec.2.2
        rw [he] at s1
        exact hC_inj (by dsimp only [C]; rw [← (untouched_cuff_properties hS hY hψ hF hb hP hf hXC hX'C h1a h1b).2.2.2.2,
          s1.symm.trans s2, (untouched_cuff_properties hS hY hψ hF hb hP hf hXC hX'C h2a'' h2b'').2.2.2.2])
    refine ⟨Equiv.ofBijective f_to (Finite.injective_iff_bijective.mp hf_inj), by simp [f_to], by simp [f_to, hi_ne.symm], fun i h1 h2 => ?_⟩
    have hsp := (hunt_match i h1 h2).choose_spec
    have hnm := hnot_mem _ hsp.1 hsp.2.1
    simpa [f_to, h1, h2] using ⟨hnm.1, hnm.2, hsp.2.2⟩
  by_cases hst : connectedComponentIn (bd S) s = connectedComponentIn (bd S) t
  · obtain ⟨φS⟩ := (cuff_statement.{u} S hS).2.2 _ ⟨s, hsb, rfl⟩
    obtain ⟨u_s, -, hus_e⟩ := exists_param (φS.symm ⟨s, mem_connectedComponentIn hsb⟩)
    obtain ⟨r_t, -, hrt_e⟩ := exists_param (φS.symm ⟨t, hst ▸ mem_connectedComponentIn htb⟩)
    set u_t := u_s + Int.fract (r_t - u_s)
    have hus : (φS (ee u_s)).1 = s := by rw [hus_e]; simp
    have hut : (φS (ee u_t)).1 = t := by
      rw [show ee u_t = ee r_t from ee_eq_iff.mpr ⟨-⌊r_t - u_s⌋, by simp only [u_t, Int.cast_neg]; linarith [Int.floor_add_fract (r_t - u_s)]⟩, hrt_e]; simp
    have hu1 : u_s < u_t := lt_of_le_of_ne (by simp only [u_t]; linarith [Int.fract_nonneg (r_t - u_s)]) fun he => hne (by rw [← hus, ← hut, he])
    have hu2 : u_t < u_s + 1 := by simp only [u_t]; linarith [Int.fract_lt_one (r_t - u_s)]
    by_cases hi_eq : i_ξ = i_η
    · have hj_eq : j_ξ0 = j_η0 := hC'_inj (hjξ_eq.trans ((hsame_cut.mp (hiξ_eq.symm.trans ((congrArg C hi_eq).trans hiη_eq))).trans hjη_eq.symm))
      obtain ⟨π, hπ_cut, hπ_unt⟩ := hbuild_perm_one hi_eq hj_eq
      exact parallel_case_1sided hS hY hY' hne hb hb' hl hl' hψ hψ' hP hP' L L' ha0 ha1 ha'0 ha'1
        himξ himη himξ' himη' hiξ hiη hiξ' hiη' AS hrel hst φS hu1 hu2 hus hut st hi_eq hj_eq π hπ_cut hπ_unt
    · have hj_ne : j_ξ0 ≠ j_η0 := fun he => hi_eq (hC_inj (hiξ_eq.trans ((hsame_cut.mpr (hjξ_eq.symm.trans ((congrArg C' he).trans hjη_eq))).trans hiη_eq.symm)))
      exact parallel_case_2sided hS hY hY' hne hb hb' hl hl' hψ hψ' hP hP' L L' ha0 ha1 ha'0 ha'1
        himξ himη himξ' himη' hiξ hiη hiξ' hiη' AS hrel hst φS hu1 hu2 hus hut st hi_eq hj_ne (hbuild_perm_two hi_eq hj_ne)
  · obtain ⟨aS, bS, cS, ⟨eS⟩⟩ := classification.{u} S hS inferInstance
    have hinv := cut_arc_model_invariants hS hY hne hψ hb hl hP L ha0 ha1 himξ himη hiξ hiη eS eY
    have hinv' := cut_arc_model_invariants hS hY' hne hψ' hb' hl' hP' L' ha'0 ha'1 himξ' himη' hiξ' hiη' eS eY'
    have hi_eq : i_ξ = i_η := hC_inj (hiξ_eq.trans ((hinv.1 hst).1.trans hiη_eq.symm))
    have hj_eq : j_ξ0 = j_η0 := hC'_inj (hjξ_eq.trans ((hinv'.1 hst).1.trans hjη_eq.symm))
    obtain ⟨π, hπ_cut, hπ_unt⟩ := hbuild_perm_one hi_eq hj_eq
    exact parallel_case_diff_cuff hS hY hY' hne hb hb' hl hl' hψ hψ' hP hP' L L' ha0 ha1 ha'0 ha'1
      himξ himη himξ' himη' hiξ hiη hiξ' hiη' AS hrel hw1 hst st hi_eq hj_eq π hπ_cut hπ_unt

/-- **Master Arc-Parallelism Theorem (Stage 1 Finale)**:
Given a connected compact surface `S` with atlas `AS`, and two proper `I`-arcs `F, F' ⊆ S` with the
same distinct boundary endpoints `s, t ∈ bd S`:
if `F` is non-separating (`IsPreconnected (Fᶜ : Set S)`), `BdCohRel s t (arcCocycle F') (arcCocycle F)`,
and `cocInt (w1 AS) γ' = cocInt (w1 AS) γ` for continuous arcs `γ, γ'` along `F, F'` from `s` to `t`,
then there exists a boundary-fixing homeomorphism `β : S ≃ₜ S` with `β '' F = F'` and
`∀ x ∈ bd S, β x = x`. -/
theorem parallel_of_cocycle_eq [ConnectedSpace S] (hS : IsSurface S)
    {F F' : Set S} {s t : S} (hne : s ≠ t)
    (hb : F ∩ bd S = {s, t}) (hb' : F' ∩ bd S = {s, t})
    (hl : IsLineWithEnds F s t) (hl' : IsLineWithEnds F' s t)
    (hnonsep : IsPreconnected (Fᶜ : Set S))
    (AS : SurfAtlas S)
    (hrel : BdCohRel s t (arcCocycle hS hne hb' hl') (arcCocycle hS hne hb hl))
    {γ γ' : ℝ → S}
    (hγc : ContinuousOn γ (Icc 0 1)) (hγ'c : ContinuousOn γ' (Icc 0 1))
    (hγsub : γ '' Icc 0 1 ⊆ F) (hγ'sub : γ' '' Icc 0 1 ⊆ F')
    (hγ0 : γ 0 = s) (hγ1 : γ 1 = t) (hγ'0 : γ' 0 = s) (hγ'1 : γ' 1 = t)
    (hw1 : cocInt (w1 AS) γ' = cocInt (w1 AS) γ) :
    ∃ β : S ≃ₜ S, β '' F = F' ∧ ∀ x ∈ bd S, β x = x := by
  have : T2Space S := hS.2.1
  obtain ⟨Y, _, _, ψ, hY, hψ, X, X', hP⟩ := exists_cut_arc hS hne hb hl
  obtain ⟨Y', _, _, ψ', hY', hψ', X₂, X₂', hP'⟩ := exists_cut_arc hS hne hb' hl'
  obtain ⟨a, ξ, η, L, ha0, ha1, himξ, himη, hiξ, hiη⟩ := exists_arcLift hP hψ
  obtain ⟨a', ξ', η', L', ha'0, ha'1, himξ', himη', hiξ', hiη'⟩ := exists_arcLift hP' hψ'
  have : Nonempty Y := ⟨ξ 0⟩
  have hconn : ConnectedSpace Y := (connectedSpace_cut_iff hY hS hψ hl.isCompact.isClosed).mpr hnonsep
  have hac : ContinuousOn a (Icc 0 1) := (hψ.1.comp_continuousOn L.cξ).congr fun u hu => (L.hξ u hu).symm
  have ha'c : ContinuousOn a' (Icc 0 1) := (hψ'.1.comp_continuousOn L'.cξ).congr fun u hu => (L'.hξ u hu).symm
  have hw1_a : cocInt (w1 AS) a' = cocInt (w1 AS) a := by
    rw [cocInt_eq_of_arc_eq (isCoc_w1 hS AS) hl' ha'c hγ'c (L'.img ▸ subset_rfl) hγ'sub ha'0 ha'1 hγ'0 hγ'1,
        hw1,
        cocInt_eq_of_arc_eq (isCoc_w1 hS AS) hl hγc hac hγsub (L.img ▸ subset_rfl) hγ0 hγ1 ha0 ha1]
  exact parallel_of_cocycle_eq_of_cut hS hne hb hb' hl hl' hY hY' hψ hψ' hP hP' L L'
    ha0 ha1 ha'0 ha'1 himξ himη himξ' himη' hiξ hiη hiξ' hiη' hconn AS hrel hw1_a

end ParallelOfCocycle

end GraphMinor.GHR18
