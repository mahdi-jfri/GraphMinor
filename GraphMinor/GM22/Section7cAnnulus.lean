module

public import GraphMinor.GM22.Section7c1
public import GraphMinor.Surface.JoinedCollar
public import GraphMinor.GM19.CircleOrder
public import GraphMinor.GM19.MarkedMatch
public import GraphMinor.GM11.RadialChord

/-!
# Annulus Routing Drawing for Graph Minors XXII (7.3)

This file constructs the annulus drawing $M_i$ in $D(A_i) \setminus \operatorname{int}(D_i)$
used in Claim (6) of the proof of (7.3) in Graph Minors XXII (pages 548–549), along with
general finite drawing gluing (`exists_glue_fin`).
-/

@[expose] public section

namespace GraphMinor.GM22

open Set Function Topology Metric GraphMinor.Surface GraphMinor.GM11
open scoped Pointwise

universe u

variable {S : Type u} [TopologicalSpace S]

local notation "𝕀" => unitInterval

/-! ### Gluing a finite family of drawings -/

/-- The empty drawing on `S`, with no vertices and no edges. -/
def emptyDrawing : Drawing S where
  U := ∅
  V := ∅
  V_subset_U := empty_subset _
  isClosed_U := isClosed_empty
  finite_V := finite_empty
  finite_edges := by
    refine finite_empty.subset ?_
    rintro C ⟨⟨x, hx⟩, hsub, -⟩
    exact (hsub hx).1
  edge_cond := by
    rintro C ⟨⟨x, hx⟩, hsub, -⟩
    exact False.elim (hsub hx).1

theorem emptyDrawing_U : (emptyDrawing (S := S)).U = ∅ := rfl

theorem emptyDrawing_V : (emptyDrawing (S := S)).V = ∅ := rfl

theorem emptyDrawing_E : (emptyDrawing (S := S)).E = ∅ := by
  ext C
  simp only [Drawing.E, emptyDrawing, sdiff_self, mem_empty_iff_false, iff_false]
  rintro ⟨⟨x, hx⟩, hsub, -⟩
  exact hsub hx

private theorem iUnion_fin_succ {α : Type*} {n : ℕ} (f : Fin (n + 1) → Set α) :
    (⋃ i : Fin n, f i.castSucc) ∪ f (Fin.last n) = ⋃ i : Fin (n + 1), f i := by
  ext x
  simp only [mem_union, mem_iUnion]
  constructor
  · rintro (⟨i, hx⟩ | hx)
    · exact ⟨i.castSucc, hx⟩
    · exact ⟨Fin.last n, hx⟩
  · rintro ⟨i, hx⟩
    by_cases hi : i = Fin.last n
    · subst hi
      exact Or.inr hx
    · refine Or.inl ⟨⟨i.1, Nat.lt_of_le_of_ne (Nat.le_of_lt_succ i.2) (Fin.val_ne_of_ne hi)⟩, ?_⟩
      simpa using hx

/-- Glue a finite family of drawings that meet pairwise only in common vertices. -/
theorem exists_glue_fin {n : ℕ} (G : Fin n → Drawing S)
    (hG : ∀ i j : Fin n, i ≠ j → (G i).U ∩ (G j).U ⊆ (G i).V ∩ (G j).V) :
    ∃ M : Drawing S,
      M.U = (⋃ i : Fin n, (G i).U) ∧
      M.V = (⋃ i : Fin n, (G i).V) ∧
      M.E = (⋃ i : Fin n, (G i).E) := by
  induction n with
  | zero =>
    refine ⟨emptyDrawing, ?_, ?_, ?_⟩ <;> simp [emptyDrawing_U, emptyDrawing_V, emptyDrawing_E]
  | succ n ih =>
    have hG' : ∀ i j : Fin n, i ≠ j →
        (G i.castSucc).U ∩ (G j.castSucc).U ⊆ (G i.castSucc).V ∩ (G j.castSucc).V :=
      fun i j hij => hG i.castSucc j.castSucc (Fin.castSucc_injective n |>.ne hij)
    obtain ⟨M', hU', hV', hE'⟩ := ih (fun i => G i.castSucc) hG'
    have hcap : M'.U ∩ (G (Fin.last n)).U ⊆ M'.V ∩ (G (Fin.last n)).V := by
      rintro x ⟨hx₁, hx₂⟩
      rw [hU', mem_iUnion] at hx₁
      obtain ⟨i, hxi⟩ := hx₁
      have hne : i.castSucc ≠ Fin.last n := Fin.castSucc_lt_last i |>.ne
      have hxv := hG i.castSucc (Fin.last n) hne ⟨hxi, hx₂⟩
      exact ⟨hV' ▸ mem_iUnion.mpr ⟨i, hxv.1⟩, hxv.2⟩
    refine ⟨M'.glue (G (Fin.last n)) hcap, ?_, ?_, ?_⟩
    · show M'.U ∪ (G (Fin.last n)).U = ⋃ i : Fin (n + 1), (G i).U
      rw [hU']
      exact iUnion_fin_succ (fun i => (G i).U)
    · show M'.V ∪ (G (Fin.last n)).V = ⋃ i : Fin (n + 1), (G i).V
      rw [hV']
      exact iUnion_fin_succ (fun i => (G i).V)
    · rw [Drawing.glue_E, hE']
      exact iUnion_fin_succ (fun i => (G i).E)

/-! ### Radial disc resize with explicit linear scaling on the inner ball -/

private theorem tentMap_pos' {l w t r : ℝ} (hl : 0 < l) (hlt : l < t)
    (hw : 0 < w) (_hwt : w < t) (hr : 0 < r) : 0 < tentMap 0 l w t r := by
  by_cases hrl : r ≤ l
  · rw [tentMap, tent_left hl hlt hr.le hrl]
    simp only [sub_zero]
    have heq : r + (w - l) * (r / l) = w * r / l := by field_simp; ring
    rw [heq]
    exact div_pos (mul_pos hw hr) hl
  · by_cases hrt : r ≤ t
    · rw [tentMap, tent_right hl hlt (le_of_not_ge hrl) hrt]
      have heq : r + (w - l) * ((t - r) / (t - l)) =
          w * ((t - r) / (t - l)) + t * ((r - l) / (t - l)) := by
        field_simp [sub_ne_zero.mpr hlt.ne']; ring
      rw [heq]
      have h1 := mul_nonneg hw.le (div_nonneg (sub_nonneg.mpr hrt) (sub_pos.mpr hlt).le)
      have h2 := mul_pos (hl.trans hlt) (div_pos (sub_pos.mpr (lt_of_not_ge hrl)) (sub_pos.mpr hlt))
      exact add_pos_of_nonneg_of_pos h1 h2
    · rw [tentMap, tent_high hl hlt (le_of_not_ge hrt), mul_zero, add_zero]
      exact hr

private noncomputable def radialFactor' (l w t r : ℝ) : ℝ :=
  tentMap 0 l w t (max l r) / max l r

private theorem radialFactor'_pos {l w t : ℝ} (hl : 0 < l) (hlt : l < t)
    (hw : 0 < w) (hwt : w < t) (r : ℝ) : 0 < radialFactor' l w t r :=
  div_pos (tentMap_pos' hl hlt hw hwt (hl.trans_le (le_max_left _ _)))
    (hl.trans_le (le_max_left _ _))

private theorem radialFactor'_mul {l w t r : ℝ} (hl : 0 < l) (hlt : l < t)
    (hr : 0 ≤ r) : radialFactor' l w t r * r = tentMap 0 l w t r := by
  by_cases hrl : r ≤ l
  · simp only [radialFactor', max_eq_left hrl]
    rw [tentMap, tent_left hl hlt hl.le le_rfl]
    simp only [sub_zero, div_self hl.ne', mul_one]
    rw [tentMap, tent_left hl hlt hr hrl]
    simp only [sub_zero]
    field_simp
  · simp only [radialFactor', max_eq_right (le_of_not_ge hrl)]
    exact div_mul_cancel₀ _ (hl.trans (lt_of_not_ge hrl)).ne'

private theorem radialFactor'_continuous {l w t : ℝ} (hl : 0 < l) (_hlt : l < t) :
    Continuous (radialFactor' l w t) := by
  unfold radialFactor' tentMap tent
  apply Continuous.div
  · fun_prop
  · fun_prop
  · intro r
    exact (hl.trans_le (le_max_left _ _)).ne'

private noncomputable def radialMap' (l w t : ℝ) (z : ℂ) : ℂ :=
  radialFactor' l w t ‖z‖ • z

private theorem radialMap'_norm {l w t : ℝ} (hl : 0 < l) (hlt : l < t)
    (hw : 0 < w) (hwt : w < t) (z : ℂ) :
    ‖radialMap' l w t z‖ = tentMap 0 l w t ‖z‖ := by
  rw [radialMap', norm_smul, Real.norm_eq_abs,
    abs_of_pos (radialFactor'_pos hl hlt hw hwt _)]
  exact radialFactor'_mul hl hlt (norm_nonneg z)

private theorem radialMap'_inverse {l w t : ℝ} (hl : 0 < l) (hlt : l < t)
    (hw : 0 < w) (hwt : w < t) (z : ℂ) :
    radialMap' w l t (radialMap' l w t z) = z := by
  by_cases hz : z = 0
  · simp [hz, radialMap']
  have hn : 0 < ‖z‖ := norm_pos_iff.mpr hz
  have heq : radialFactor' w l t (tentMap 0 l w t ‖z‖) * radialFactor' l w t ‖z‖ = 1 := by
    apply mul_right_cancel₀ hn.ne'
    rw [one_mul, mul_assoc, radialFactor'_mul hl hlt hn.le,
      radialFactor'_mul hw hwt (tentMap_pos' hl hlt hw hwt hn).le,
      tentMap_inv hl hlt hw hwt]
  change radialFactor' w l t ‖radialMap' l w t z‖ • (radialFactor' l w t ‖z‖ • z) = z
  rw [radialMap'_norm hl hlt hw hwt, smul_smul, heq, one_smul]

/-- Radial disc resize exposing the linear scaling on `closedBall 0 l`. -/
theorem exists_radial_disc_resize_scale {l w t : ℝ} (hl : 0 < l) (hlt : l < t)
    (hw : 0 < w) (hwt : w < t) :
    ∃ Θ : ℂ ≃ₜ ℂ,
      (∀ z, t ≤ ‖z‖ → Θ z = z) ∧
      (∀ z, ‖z‖ ≤ l → Θ z = (w / l) • z) ∧
      Θ '' closedBall 0 l = closedBall 0 w := by
  let Θ : ℂ ≃ₜ ℂ := {
    toFun := radialMap' l w t
    invFun := radialMap' w l t
    left_inv := radialMap'_inverse hl hlt hw hwt
    right_inv := radialMap'_inverse hw hwt hl hlt
    continuous_toFun := (radialFactor'_continuous hl hlt).comp continuous_norm |>.smul continuous_id
    continuous_invFun := (radialFactor'_continuous hw hwt).comp continuous_norm |>.smul continuous_id }
  have hscale : ∀ z : ℂ, ‖z‖ ≤ l → Θ z = (w / l) • z := by
    intro z hz
    change radialFactor' l w t ‖z‖ • z = _
    congr 1
    simp only [radialFactor', max_eq_left hz, tentMap, tent_left hl hlt hl.le le_rfl,
      sub_zero, div_self hl.ne', mul_one]
    congr 1
    ring
  refine ⟨Θ, ?_, hscale, ?_⟩
  · intro z hz
    change radialFactor' l w t ‖z‖ • z = z
    have hn : l ≤ ‖z‖ := hlt.le.trans hz
    have hnpos : 0 < ‖z‖ := hl.trans_le hn
    simp only [radialFactor', max_eq_right hn, tentMap, tent_high hl hlt hz,
      mul_zero, add_zero, div_self hnpos.ne', one_smul]
  · apply Set.Subset.antisymm
    · rintro _ ⟨z, hz, rfl⟩
      rw [mem_closedBall_zero_iff] at hz ⊢
      rw [hscale z hz, norm_smul, Real.norm_eq_abs, abs_of_pos (div_pos hw hl)]
      exact (mul_le_mul_of_nonneg_left hz (div_pos hw hl).le).trans_eq (div_mul_cancel₀ w hl.ne')
    · intro z hz
      rw [mem_closedBall_zero_iff] at hz
      let v : ℂ := (l / w) • z
      have hv : ‖v‖ ≤ l := by
        dsimp only [v]
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos (div_pos hl hw)]
        exact (mul_le_mul_of_nonneg_left hz (div_pos hl hw).le).trans_eq (div_mul_cancel₀ l hw.ne')
      refine ⟨v, mem_closedBall_zero_iff.mpr hv, ?_⟩
      rw [hscale v hv]
      dsimp only [v]
      rw [smul_smul]
      have heq : w / l * (l / w) = 1 := by field_simp
      rw [heq, one_smul]

/-! ### Collar coordinates with coherent inner and outer boundary directions -/

variable [T2Space S]

private theorem exists_inverse_on' {K : Set ℂ} (hK : IsCompact K) {c : ℂ → S}
    (hc : ContinuousOn c K) (hi : InjOn c K) :
    ∃ c' : S → ℂ, ContinuousOn c' (c '' K) ∧ MapsTo c' (c '' K) K ∧
      LeftInvOn c' c K ∧ RightInvOn c' c (c '' K) := by
  classical
  have : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let f : K → S := K.domRestrict c
  have hf : Continuous f := continuousOn_iff_continuous_domRestrict.mp hc
  have hfi : Function.Injective f := fun a b he => Subtype.ext (hi a.2 b.2 he)
  have hem := hf.isClosedEmbedding hfi
  let e : K ≃ₜ range f := hem.isEmbedding.toHomeomorph
  have hrange : range f = c '' K := by
    ext x
    constructor
    · rintro ⟨z, rfl⟩
      exact ⟨z.1, z.2, rfl⟩
    · rintro ⟨z, hz, rfl⟩
      exact ⟨⟨z, hz⟩, rfl⟩
  let c' : S → ℂ := fun x => if hx : x ∈ range f then (e.symm ⟨x, hx⟩).1 else 0
  have hval : ∀ z (hz : z ∈ K), c' (c z) = z := fun z hz => by
    have hx : c z ∈ range f := ⟨⟨z, hz⟩, rfl⟩
    show (if hx : c z ∈ range f then (e.symm ⟨c z, hx⟩).1 else 0) = z
    simp only [hx, ↓reduceDIte]
    have : (⟨c z, hx⟩ : range f) = e ⟨z, hz⟩ := rfl
    rw [this, e.symm_apply_apply]
  refine ⟨c', ?_, ?_, fun z hz => hval z hz, ?_⟩
  · rw [← hrange, continuousOn_iff_continuous_domRestrict]
    have : (range f).domRestrict c' = fun x : range f => (e.symm x).1 := by
      funext x
      show (if hx : x.1 ∈ range f then (e.symm ⟨x.1, hx⟩).1 else 0) = _
      simp only [x.2, ↓reduceDIte]
    rw [this]
    exact continuous_subtype_val.comp e.symm.continuous
  · rintro _ ⟨z, hz, rfl⟩
    rw [hval z hz]
    exact hz
  · rintro _ ⟨z, hz, rfl⟩
    show c (c' (c z)) = c z
    rw [hval z hz]

/-- Given nested closed discs `A ⊆ B \ discBd B` disjoint from a closed disc `Δ` on a connected
closed surface `S` with orientation `orient`, there are collar coordinates `c : ℂ → S` on
`closedBall 0 2` such that `w ↦ c w` on `discBd A` and `w ↦ c (2 * w)` on `discBd B`
have the same orientation under `orient`. -/
theorem exists_oriented_collar [ConnectedSpace S] (hS : IsClosedSurface S)
    (orient : GM19.SurfaceOrientation S)
    {A B Δ : Set S} (hA : IsClosedDisc A) (hB : IsClosedDisc B) (hΔ : IsClosedDisc Δ)
    (hAB : A ⊆ B \ discBd B) (hBΔ : Disjoint B Δ) :
    ∃ c : ℂ → S,
      ContinuousOn c (closedBall 0 2) ∧
      InjOn c (closedBall 0 2) ∧
      c '' closedBall 0 1 = A ∧
      c '' sphere 0 1 = discBd A ∧
      c '' closedBall 0 2 = B ∧
      c '' sphere 0 2 = discBd B ∧
      (∀ a b d : Circle, a ≠ b → b ≠ d → a ≠ d →
        (orient.pos A (c a) (c b) (c d) ↔
          orient.pos B (c (((2 : ℝ) : ℂ) * a)) (c (((2 : ℝ) : ℂ) * b))
            (c (((2 : ℝ) : ℂ) * d)))) := by
  have hman : ∀ x : S, IsManifoldPoint x := fun x => (hS.2.2 x).isManifoldPoint
  obtain ⟨E, hE, hBE, hEΔ⟩ := GM12.exists_disc_enlargement_avoiding hS hB hΔ.isClosed hBΔ
  obtain ⟨pA⟩ := hA.isOArc_discBd
  obtain ⟨c₁, c₁', hcc₁, -, hm₁, hm₁', hl₁, hr₁, hin₁, hs₁, -⟩ :=
    exists_disc_collar hA hB hAB pA
  have hi₁ : InjOn c₁ (closedBall 0 2) := hl₁.injOn
  have hB₁ : c₁ '' closedBall 0 2 = B :=
    (hm₁.image_subset).antisymm fun x hx => ⟨_, hm₁' hx, hr₁ hx⟩
  have hS2 : ∀ w : Circle, ((2 : ℝ) : ℂ) * w ∈ sphere (0 : ℂ) 2 := fun w => by
    rw [mem_sphere_zero_iff_norm, norm_mul, Circle.norm_coe, Complex.norm_real]
    norm_num
  let u : Circle → discBd B := fun w =>
    ⟨c₁ (((2 : ℝ) : ℂ) * w), by rw [← hs₁]; exact mem_image_of_mem c₁ (hS2 w)⟩
  have huc : Continuous u := by
    refine Continuous.subtype_mk (hcc₁.comp_continuous (by
      exact continuous_const.mul continuous_induced_dom) fun w => sphere_subset_closedBall (hS2 w)) _
  have hui : Function.Injective u := fun w w' he => by
    have h1 := hi₁ (sphere_subset_closedBall (hS2 w)) (sphere_subset_closedBall (hS2 w'))
      (congrArg Subtype.val he)
    exact Circle.ext (mul_left_cancel₀ (by norm_num) h1)
  have hus : Function.Surjective u := fun x => by
    obtain ⟨z, hz, he⟩ : x.1 ∈ c₁ '' sphere 0 2 := by rw [hs₁]; exact x.2
    have hzn : ‖z‖ = 2 := mem_sphere_zero_iff_norm.mp hz
    have hz0 : z ≠ 0 := fun h => by simp [h] at hzn
    refine ⟨unitOf z hz0, Subtype.ext ?_⟩
    show c₁ (((2 : ℝ) : ℂ) * unitOf z hz0) = x.1
    rw [← hzn, norm_mul_unitOf, he]
  let pB : Circle ≃ₜ discBd B :=
    huc.homeoOfEquivCompactToT2 (f := Equiv.ofBijective u ⟨hui, hus⟩)
  have hpB : ∀ w : Circle, (pB w).1 = c₁ (((2 : ℝ) : ℂ) * w) := fun _ => rfl
  obtain ⟨c₂, c₂', hcc₂, -, hm₂, hm₂', hl₂, hr₂, hin₂, hs₂, hp₂⟩ :=
    exists_disc_collar hB hE hBE pB
  have hi₂ : InjOn c₂ (closedBall 0 2) := hl₂.injOn
  have hE₂ : c₂ '' closedBall 0 2 = E :=
    (hm₂.image_subset).antisymm fun x hx => ⟨_, hm₂' hx, hr₂ hx⟩
  have hcompat : ∀ z : ℂ, ‖z‖ = 2 → c₁ z = c₂ (collarOuterStep z) := by
    intro z hzn
    have hz0 : z ≠ 0 := fun h => by simp [h] at hzn
    have h1 : collarOuterStep z = (unitOf z hz0 : ℂ) := by
      rw [collarOuterStep_two hzn, coe_unitOf, hzn, Complex.real_smul]
      push_cast
      ring
    rw [h1, hp₂, hpB, ← hzn, norm_mul_unitOf]
  obtain ⟨c, hcc, hci, hcA, hcB, hcE, hcs⟩ :=
    exists_joined_collar_coordinates c₁ c₂ hcc₁ hi₁ hcc₂ hi₂ hin₁ hB₁ hin₂ hE₂ hs₂ hcompat
  let sc : ℂ → ℂ := fun z => (3 / 2 : ℝ) • z
  have hsc : Continuous sc := by fun_prop
  have hsci : Function.Injective sc := smul_right_injective ℂ (by norm_num)
  have hball : ∀ r : ℝ, sc '' closedBall 0 r = closedBall 0 (3 / 2 * r) := fun r => by
    change (3 / 2 : ℝ) • closedBall (0 : ℂ) r = _
    have := _root_.smul_closedBall' (by norm_num : (3 / 2 : ℝ) ≠ 0) (0 : ℂ) r
    simpa only [smul_zero, Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 3 / 2)] using this
  have hsph : sc '' sphere 0 2 = sphere 0 3 := by
    change (3 / 2 : ℝ) • sphere (0 : ℂ) 2 = _
    have := _root_.smul_sphere' (by norm_num : (3 / 2 : ℝ) ≠ 0) (0 : ℂ) 2
    have h2 : |(3 / 2 : ℝ)| * 2 = 3 := by rw [abs_of_pos (by norm_num)]; norm_num
    simpa only [smul_zero, Real.norm_eq_abs, h2] using this
  let d : ℂ → S := fun z => c (sc z)
  have hsub : MapsTo sc (closedBall 0 2) (closedBall 0 3) := fun z hz => by
    have : sc z ∈ sc '' closedBall 0 2 := mem_image_of_mem sc hz
    rw [hball 2] at this
    convert this using 2
    norm_num
  have hdc : ContinuousOn d (closedBall 0 2) := hcc.comp hsc.continuousOn hsub
  have hdi : InjOn d (closedBall 0 2) := fun z hz w hw he => hsci (hci (hsub hz) (hsub hw) he)
  have hdimg : ∀ r r' : ℝ, 3 / 2 * r = r' → d '' closedBall 0 r = c '' closedBall 0 r' :=
    fun r r' he => by rw [← he, ← hball r, image_image]
  have hdE : d '' closedBall 0 2 = E := by rw [hdimg 2 3 (by norm_num), hcE]
  have hdA : d '' closedBall 0 (2 / 3) = A := by rw [hdimg (2 / 3) 1 (by norm_num), hcA]
  have hdB : d '' closedBall 0 (4 / 3) = B := by rw [hdimg (4 / 3) 2 (by norm_num), hcB]
  have hds : d '' sphere 0 2 = discBd E := by rw [← hcs, ← hsph, image_image]
  obtain ⟨d', hdc', hdm', hdl, hdr⟩ := exists_inverse_on' (isCompact_closedBall 0 2) hdc hdi
  rw [hdE] at hdc' hdm' hdr
  have hdm : MapsTo d (closedBall 0 2) E := fun z hz => hdE ▸ mem_image_of_mem d hz
  obtain ⟨Θ, hΘfix, hΘscale, hΘball⟩ := exists_radial_disc_resize_scale
    (show (0 : ℝ) < 2 / 3 by norm_num) (show (2 / 3 : ℝ) < 3 / 2 by norm_num)
    (show (0 : ℝ) < 4 / 3 by norm_num) (show (4 / 3 : ℝ) < 3 / 2 by norm_num)
  obtain ⟨e, hec, hefix⟩ :=
    exists_homeomorph_of_collar hman hE hdc hdc' hdm hdm' hdl hdr hds Θ hΘfix
  have heAB : e '' A = B := by
    rw [← hdA, image_image, ← hdB, ← hΘball, image_image]
    exact image_congr fun z hz => hec z (closedBall_subset_closedBall (by norm_num) hz)
  have he_fixΔ : ∀ x ∈ Δ, e x = x :=
    fun x hx => hefix x (fun hxE => Set.disjoint_left.mp hEΔ hxE hx)
  have he_pres : orient.IsPreservedBy e :=
    preserved_of_fix_closedDisc hS orient e hΔ he_fixΔ
  have he_circle : ∀ w : Circle, e (c w) = c (((2 : ℝ) : ℂ) * w) := by
    intro w
    let z : ℂ := (2 / 3 : ℝ) • (w : ℂ)
    have hzn : ‖z‖ = 2 / 3 := by
      simp only [z, norm_smul, Real.norm_eq_abs, Circle.norm_coe, mul_one]
      norm_num
    have hz2 : z ∈ closedBall (0 : ℂ) 2 := mem_closedBall_zero_iff.mpr (by linarith)
    have hdz : d z = c w := by
      show c ((3 / 2 : ℝ) • ((2 / 3 : ℝ) • (w : ℂ))) = c w
      rw [smul_smul]
      norm_num
    have hΘz : Θ z = (4 / 3 : ℝ) • (w : ℂ) := by
      rw [hΘscale z (by linarith)]
      simp only [z, smul_smul]
      congr 1
      norm_num
    have hdΘz : d (Θ z) = c (((2 : ℝ) : ℂ) * w) := by
      rw [hΘz]
      show c ((3 / 2 : ℝ) • ((4 / 3 : ℝ) • (w : ℂ))) = c (((2 : ℝ) : ℂ) * w)
      rw [smul_smul, Complex.real_smul]
      congr 2
      norm_num
    rw [← hdz, hec z hz2, hdΘz]
  obtain ⟨c', hc', hcm', hcl, hcr⟩ := exists_inverse_on' (isCompact_closedBall 0 3) hcc hci
  rw [hcE] at hc' hcm' hcr
  have hc_sub1 : closedBall (0 : ℂ) 1 ⊆ closedBall 0 3 := closedBall_subset_closedBall (by norm_num)
  have hc_sub2 : closedBall (0 : ℂ) 2 ⊆ closedBall 0 3 := closedBall_subset_closedBall (by norm_num)
  have hAE : A ⊆ E := by rw [← hcA, ← hcE]; exact image_mono hc_sub1
  have hcs1 : c '' sphere 0 1 = discBd A := by
    obtain ⟨_, hbd1⟩ := isClosedDisc_closedBall.1.image (f := c) (f' := c')
      (hcc.mono hc_sub1) (hc'.mono (hcA.symm ▸ hAE)) (hcl.mono hc_sub1)
    rw [hcA, isClosedDisc_closedBall.2] at hbd1
    exact hbd1.symm
  have hcs2 : c '' sphere 0 2 = discBd B := by
    obtain ⟨_, hbdB⟩ := hA.image (f := e) (f' := e.symm)
      e.continuous.continuousOn e.symm.continuous.continuousOn (fun _ _ => e.symm_apply_apply _)
    rw [heAB, ← hcs1] at hbdB
    rw [hbdB]
    ext x
    constructor
    · rintro ⟨z, hz, rfl⟩
      have hzn : ‖z‖ = 2 := mem_sphere_zero_iff_norm.mp hz
      have hz0 : z ≠ 0 := fun h => by simp [h] at hzn
      let w : Circle := unitOf z hz0
      have hw : (w : ℂ) ∈ sphere (0 : ℂ) 1 := mem_sphere_zero_iff_norm.mpr (Circle.norm_coe w)
      refine ⟨c w, mem_image_of_mem c hw, ?_⟩
      rw [he_circle w, show ((2 : ℝ) : ℂ) * (w : ℂ) = z by rw [← hzn, norm_mul_unitOf]]
    · rintro ⟨_, ⟨z, hz, rfl⟩, rfl⟩
      let w : Circle := ⟨z, by simpa [Submonoid.unitSphere] using hz⟩
      have hw_eq : (w : ℂ) = z := rfl
      rw [← hw_eq, he_circle w]
      exact mem_image_of_mem c (hS2 w)
  have hc1_mem : ∀ w : Circle, c w ∈ discBd A := fun w => by
    rw [← hcs1]
    exact mem_image_of_mem c (mem_sphere_zero_iff_norm.mpr (Circle.norm_coe w))
  have hc1_inj : ∀ {w₁ w₂ : Circle}, w₁ ≠ w₂ → c w₁ ≠ c w₂ := by
    intro w₁ w₂ hne heq
    have hw₁ : (w₁ : ℂ) ∈ closedBall (0 : ℂ) 3 :=
      hc_sub1 (sphere_subset_closedBall (mem_sphere_zero_iff_norm.mpr (Circle.norm_coe w₁)))
    have hw₂ : (w₂ : ℂ) ∈ closedBall (0 : ℂ) 3 :=
      hc_sub1 (sphere_subset_closedBall (mem_sphere_zero_iff_norm.mpr (Circle.norm_coe w₂)))
    exact hne (Circle.ext (hci hw₁ hw₂ heq))
  refine ⟨c, hcc.mono hc_sub2, hci.mono hc_sub2, hcA, hcs1, hcB, hcs2, ?_⟩
  intro a b d hab hbd had
  have hpres := he_pres A hA (c a) (c b) (c d) (hc1_mem a) (hc1_mem b) (hc1_mem d)
    (hc1_inj hab) (hc1_inj hbd) (hc1_inj had)
  rw [heAB, he_circle a, he_circle b, he_circle d] at hpres
  exact hpres.symm

/-! ### Matching finite tuples on `Circle` with the same cyclic order -/

/-- Two injective maps `w_in, w_out : Fin k → Circle` with the same cyclic order on triples
are related by an orientation-preserving homeomorphism of `Circle`. -/
theorem exists_circle_match_of_cyclic {k : ℕ} (w_in w_out : Fin k → Circle)
    (h_in : Function.Injective w_in) (h_out : Function.Injective w_out)
    (h_cyc : ∀ j₁ j₂ j₃ : Fin k, j₁ ≠ j₂ → j₂ ≠ j₃ → j₁ ≠ j₃ →
      (GM19.CircleCyclic (w_in j₁) (w_in j₂) (w_in j₃) ↔
        GM19.CircleCyclic (w_out j₁) (w_out j₂) (w_out j₃))) :
    ∃ h : Circle ≃ₜ Circle, PreservesCircleOrientation h ∧ ∀ j : Fin k, h (w_out j) = w_in j := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · refine ⟨Homeomorph.refl Circle, ⟨id, continuous_id, strictMono_id, fun _ => rfl⟩,
      fun j => Fin.elim0 j⟩
  let j₀ : Fin k := ⟨0, hk⟩
  have hA : ∀ j : Fin k, ∃ a : ℝ, 0 ≤ a ∧ a < 1 ∧ (j = j₀ → a = 0) ∧
      (j ≠ j₀ → a ≠ 0) ∧ w_out j = w_out j₀ * ee a := by
    intro j
    by_cases hj : j = j₀
    · subst hj
      exact ⟨0, le_rfl, one_pos, fun _ => rfl, fun h => absurd rfl h, by simp [ee]⟩
    · have hne : (w_out j₀)⁻¹ * w_out j ≠ 1 := fun h => hj (h_out (inv_mul_eq_one.mp h).symm)
      obtain ⟨s, hs0, hs1, hs⟩ := exists_angle hne
      have hpi := Real.pi_pos
      refine ⟨s / (2 * Real.pi), by positivity, by rw [div_lt_one (by positivity)]; exact hs1,
        fun h => absurd h hj, fun _ => by positivity, ?_⟩
      rw [ee, mul_div_cancel₀ _ (by positivity), ← hs, mul_inv_cancel_left]
  choose a ha0 ha1 haj₀ hane ha_eq using hA
  have ha_inj : Function.Injective a := by
    intro j₁ j₂ heq
    exact h_out (by rw [ha_eq j₁, ha_eq j₂, heq])
  have ha_win : ∀ j₁ j₂ : Fin k, a j₁ < a j₂ + 1 := fun j₁ j₂ => by linarith [ha1 j₁, ha0 j₂]
  have h_interp_cyc : ∀ j₁ j₂ j₃ : Fin k, j₁ ≠ j₂ → j₂ ≠ j₃ → j₁ ≠ j₃ →
      (GM19.CircleCyclic (w_in j₁) (w_in j₂) (w_in j₃) ↔ GM19.CycOrder (a j₁) (a j₂) (a j₃)) := by
    intro j₁ j₂ j₃ h12 h23 h13
    rw [h_cyc j₁ j₂ j₃ h12 h23 h13, ha_eq j₁, ha_eq j₂, ha_eq j₃, GM19.circleCyclic_mul_iff]
    exact GM19.circleCyclic_ee_iff (ha_win j₁ j₂) (ha_win j₂ j₁) (ha_win j₂ j₃) (ha_win j₃ j₂)
      (ha_win j₁ j₃) (ha_win j₃ j₁) (ha_inj.ne h12) (ha_inj.ne h23) (ha_inj.ne h13)
  obtain ⟨τ, hτ_orient, hτ_eq⟩ :=
    GM19.exists_circle_interp a ha_inj ha_win w_in h_in h_interp_cyc
  refine ⟨(Homeomorph.mulLeft (w_out j₀)⁻¹).trans τ,
    PreservesCircleOrientation.comp hτ_orient (preservesCircleOrientation_mul _),
    fun j => ?_⟩
  show τ ((w_out j₀)⁻¹ * w_out j) = w_in j
  rw [ha_eq j, inv_mul_cancel_left, hτ_eq j]

/-! ### Annulus routing drawing between `subBd A` and `subBd B` -/

/-- Given nested closed discs `A ⊆ B \ subBd B` disjoint from a closed disc `Δ` on a connected
closed surface `S` with orientation `orient`, and injective tuples `π_in, π_out : Fin k → S`
on `subBd A` and `subBd B` whose triples have the same orientation under `orient`, there is
a drawing `M` in `B` whose vertices are `range π_in ∪ range π_out` and whose edges are `k`
disjoint paths from `π_in j` to `π_out j` with interiors in `(B \ subBd B) \ A`. -/
theorem exists_annulus_drawing [ConnectedSpace S] (hS : IsClosedSurface S)
    (orient : GM19.SurfaceOrientation S)
    {A B Δ : Set S} (hA : IsClosedDisc A) (hB : IsClosedDisc B) (hΔ : IsClosedDisc Δ)
    (hAB : A ⊆ B \ subBd B) (hBΔ : Disjoint B Δ)
    {k : ℕ} (π_in π_out : Fin k → S)
    (hπ_in_bd : range π_in ⊆ subBd A) (hπ_in_inj : Function.Injective π_in)
    (hπ_out_bd : range π_out ⊆ subBd B) (hπ_out_inj : Function.Injective π_out)
    (h_orient : ∀ j₁ j₂ j₃ : Fin k, j₁ ≠ j₂ → j₂ ≠ j₃ → j₁ ≠ j₃ →
      (orient.pos A (π_in j₁) (π_in j₂) (π_in j₃) ↔
        orient.pos B (π_out j₁) (π_out j₂) (π_out j₃))) :
    ∃ (M : Drawing S) (L : Fin k → Set S),
      M.U = (⋃ j : Fin k, L j) ∧
      M.V = range π_in ∪ range π_out ∧
      M.E = range (fun j : Fin k => L j \ {π_in j, π_out j}) ∧
      M.U ⊆ B ∧
      M.U ∩ A = range π_in ∧
      M.U ∩ subBd B = range π_out ∧
      (∀ j : Fin k, IsLineWithEnds (L j) (π_in j) (π_out j)) ∧
      (∀ j : Fin k, π_in j ≠ π_out j) ∧
      Pairwise (fun j₁ j₂ : Fin k => Disjoint (L j₁) (L j₂)) ∧
      (∀ j : Fin k, L j \ {π_in j, π_out j} ⊆ (B \ subBd B) \ A) ∧
      (∀ j : Fin k, L j ∩ A = {π_in j}) ∧
      (∀ j : Fin k, L j ∩ subBd B = {π_out j}) := by
  have hbdA : subBd A = discBd A := GM14.IsClosedDisc.subBd_eq_discBd hS hA
  have hbdB : subBd B = discBd B := GM14.IsClosedDisc.subBd_eq_discBd hS hB
  have hAB' : A ⊆ B \ discBd B := hbdB ▸ hAB
  obtain ⟨c, hcc, hci, hcA, hcs1, hcB, hcs2, hc_pos⟩ :=
    exists_oriented_collar hS orient hA hB hΔ hAB' hBΔ
  have hS1 : ∀ w : Circle, (w : ℂ) ∈ sphere (0 : ℂ) 1 :=
    fun w => mem_sphere_zero_iff_norm.mpr (Circle.norm_coe w)
  have hS2 : ∀ w : Circle, ((2 : ℝ) : ℂ) * w ∈ sphere (0 : ℂ) 2 := fun w => by
    rw [mem_sphere_zero_iff_norm, norm_mul, Circle.norm_coe, Complex.norm_real]
    norm_num
  let p_in : Circle → S := fun w => c w
  let p_out : Circle → S := fun w => c (((2 : ℝ) : ℂ) * w)
  have hp_in_inj : Function.Injective p_in := fun w₁ w₂ heq => by
    have h1 : (w₁ : ℂ) ∈ closedBall 0 2 :=
      closedBall_subset_closedBall (by norm_num) (sphere_subset_closedBall (hS1 w₁))
    have h2 : (w₂ : ℂ) ∈ closedBall 0 2 :=
      closedBall_subset_closedBall (by norm_num) (sphere_subset_closedBall (hS1 w₂))
    exact Circle.ext (hci h1 h2 heq)
  have hp_out_inj : Function.Injective p_out := fun w₁ w₂ heq => by
    have h1 := sphere_subset_closedBall (hS2 w₁)
    have h2 := sphere_subset_closedBall (hS2 w₂)
    exact Circle.ext (mul_left_cancel₀ (by norm_num) (hci h1 h2 heq))
  have hp_in_range : range p_in = discBd A := by
    rw [← hcs1]
    ext x
    constructor
    · rintro ⟨w, rfl⟩
      exact mem_image_of_mem c (hS1 w)
    · rintro ⟨z, hz, rfl⟩
      exact ⟨⟨z, by simpa [Submonoid.unitSphere] using hz⟩, rfl⟩
  have hp_out_range : range p_out = discBd B := by
    rw [← hcs2]
    ext x
    constructor
    · rintro ⟨w, rfl⟩
      exact mem_image_of_mem c (hS2 w)
    · rintro ⟨z, hz, rfl⟩
      have hzn : ‖z‖ = 2 := mem_sphere_zero_iff_norm.mp hz
      have hz0 : z ≠ 0 := fun h => by simp [h] at hzn
      refine ⟨unitOf z hz0, ?_⟩
      show c (((2 : ℝ) : ℂ) * unitOf z hz0) = c z
      rw [← hzn, norm_mul_unitOf]
  have hw_in_ex : ∀ j : Fin k, ∃ w : Circle, p_in w = π_in j := by
    intro j
    have hj : π_in j ∈ range p_in := by
      rw [hp_in_range, ← hbdA]
      exact hπ_in_bd ⟨j, rfl⟩
    exact hj
  have hw_out_ex : ∀ j : Fin k, ∃ w : Circle, p_out w = π_out j := by
    intro j
    have hj : π_out j ∈ range p_out := by
      rw [hp_out_range, ← hbdB]
      exact hπ_out_bd ⟨j, rfl⟩
    exact hj
  choose w_in hw_in using hw_in_ex
  choose w_out hw_out using hw_out_ex
  have hw_in_inj : Function.Injective w_in := fun j₁ j₂ heq =>
    hπ_in_inj (by rw [← hw_in j₁, ← hw_in j₂, heq])
  have hw_out_inj : Function.Injective w_out := fun j₁ j₂ heq =>
    hπ_out_inj (by rw [← hw_out j₁, ← hw_out j₂, heq])
  -- Show `w_in` and `w_out` have the same `GM19.CircleCyclic` on triples
  have hw_cyc : ∀ j₁ j₂ j₃ : Fin k, j₁ ≠ j₂ → j₂ ≠ j₃ → j₁ ≠ j₃ →
      (GM19.CircleCyclic (w_in j₁) (w_in j₂) (w_in j₃) ↔
        GM19.CircleCyclic (w_out j₁) (w_out j₂) (w_out j₃)) := by
    intro j₁ j₂ j₃ h12 h23 h13
    have hpos_eq : orient.pos A (p_in (w_in j₁)) (p_in (w_in j₂)) (p_in (w_in j₃)) ↔
        orient.pos A (p_in (w_out j₁)) (p_in (w_out j₂)) (p_in (w_out j₃)) := by
      have h1 := h_orient j₁ j₂ j₃ h12 h23 h13
      rw [← hw_in j₁, ← hw_in j₂, ← hw_in j₃, ← hw_out j₁, ← hw_out j₂, ← hw_out j₃] at h1
      exact h1.trans (hc_pos (w_out j₁) (w_out j₂) (w_out j₃)
        (hw_out_inj.ne h12) (hw_out_inj.ne h23) (hw_out_inj.ne h13)).symm
    obtain ⟨φ, hφc, hφi, hφr, hφpos⟩ := orient.isDirection A hA
    have hp_in_cont : Continuous p_in :=
      hcc.comp_continuous continuous_induced_dom
        (fun w => closedBall_subset_closedBall (by norm_num) (sphere_subset_closedBall (hS1 w)))
    have he_in := (hp_in_cont.isClosedEmbedding hp_in_inj).isEmbedding
    have he_φ := (hφc.isClosedEmbedding hφi).isEmbedding
    let τ : Circle ≃ₜ Circle :=
      he_in.toHomeomorph.trans
        ((Homeomorph.setCongr (hp_in_range.trans hφr.symm)).trans he_φ.toHomeomorph.symm)
    have hτ' : ∀ w : Circle, φ (τ w) = p_in w := fun w =>
      congrArg Subtype.val
        (he_φ.toHomeomorph.apply_symm_apply
          ((Homeomorph.setCongr (hp_in_range.trans hφr.symm)) (he_in.toHomeomorph w)))
    have hpos_φ : ∀ a b d : Circle, a ≠ b → b ≠ d → a ≠ d →
        (orient.pos A (p_in a) (p_in b) (p_in d) ↔ GM19.CircleCyclic (τ a) (τ b) (τ d)) := by
      intro a b d hab hbd had
      rw [← hτ' a, ← hτ' b, ← hτ' d]
      exact hφpos (τ a) (τ b) (τ d) (τ.injective.ne hab) (τ.injective.ne hbd) (τ.injective.ne had)
    rw [hpos_φ (w_in j₁) (w_in j₂) (w_in j₃) (hw_in_inj.ne h12) (hw_in_inj.ne h23) (hw_in_inj.ne h13),
      hpos_φ (w_out j₁) (w_out j₂) (w_out j₃) (hw_out_inj.ne h12) (hw_out_inj.ne h23) (hw_out_inj.ne h13)] at hpos_eq
    rcases GM19.circle_dichotomy τ with hmono | hanti
    · rw [hmono (w_in j₁) (w_in j₂) (w_in j₃) (hw_in_inj.ne h12) (hw_in_inj.ne h23) (hw_in_inj.ne h13),
        hmono (w_out j₁) (w_out j₂) (w_out j₃) (hw_out_inj.ne h12) (hw_out_inj.ne h23) (hw_out_inj.ne h13)] at hpos_eq
      exact hpos_eq
    · rw [hanti (w_in j₁) (w_in j₂) (w_in j₃) (hw_in_inj.ne h12) (hw_in_inj.ne h23) (hw_in_inj.ne h13),
        hanti (w_out j₁) (w_out j₂) (w_out j₃) (hw_out_inj.ne h12) (hw_out_inj.ne h23) (hw_out_inj.ne h13)] at hpos_eq
      exact not_iff_not.mp hpos_eq
  obtain ⟨h, hh_orient, hh_eq⟩ :=
    exists_circle_match_of_cyclic w_in w_out hw_in_inj hw_out_inj hw_cyc
  obtain ⟨μ, hμc, hμ0, hμ1, hμb⟩ := exists_circle_homotopy hh_orient
  let z_arc : Fin k → 𝕀 → ℂ :=
    fun j t => ((1 + (t : ℝ) : ℝ) : ℂ) * (μ (t, w_out j) : ℂ)
  have hz_norm : ∀ (j : Fin k) (t : 𝕀), ‖z_arc j t‖ = 1 + (t : ℝ) := by
    intro j t
    have ht0 : 0 ≤ (t : ℝ) := t.2.1
    simp only [z_arc, norm_mul, Complex.norm_real, Circle.norm_coe, mul_one, Real.norm_eq_abs,
      abs_of_pos (by linarith : (0 : ℝ) < 1 + (t : ℝ))]
  have hz_mem2 : ∀ (j : Fin k) (t : 𝕀), z_arc j t ∈ closedBall (0 : ℂ) 2 := by
    intro j t
    rw [mem_closedBall_zero_iff, hz_norm]
    linarith [t.2.2]
  have hz_cont : ∀ j : Fin k, Continuous (z_arc j) := by
    intro j
    refine Continuous.mul (by fun_prop) (continuous_induced_dom.comp (hμc.comp ?_))
    exact continuous_id.prodMk continuous_const
  let γ : Fin k → 𝕀 → S := fun j t => c (z_arc j t)
  have hγ_cont : ∀ j : Fin k, Continuous (γ j) :=
    fun j => hcc.comp_continuous (hz_cont j) (hz_mem2 j)
  have hγ_inj : ∀ {j₁ j₂ : Fin k} {t₁ t₂ : 𝕀}, γ j₁ t₁ = γ j₂ t₂ → j₁ = j₂ ∧ t₁ = t₂ := by
    intro j₁ j₂ t₁ t₂ heq
    have hz_eq := hci (hz_mem2 j₁ t₁) (hz_mem2 j₂ t₂) heq
    have hn_eq : ‖z_arc j₁ t₁‖ = ‖z_arc j₂ t₂‖ := congrArg norm hz_eq
    rw [hz_norm, hz_norm] at hn_eq
    have ht_eq : t₁ = t₂ := Subtype.ext (by linarith)
    subst ht_eq
    have hr_ne : ((1 + (t₁ : ℝ) : ℝ) : ℂ) ≠ 0 := by
      exact_mod_cast (by linarith [t₁.2.1] : (1 + (t₁ : ℝ) : ℝ) ≠ 0)
    have hμ_eq : μ (t₁, w_out j₁) = μ (t₁, w_out j₂) :=
      Circle.ext (mul_left_cancel₀ hr_ne hz_eq)
    have hw_eq := (hμb t₁).1 hμ_eq
    exact ⟨hw_out_inj hw_eq, rfl⟩
  have hγ0 : ∀ j : Fin k, γ j 0 = π_in j := by
    intro j
    show c (((1 + ((0 : 𝕀) : ℝ) : ℝ) : ℂ) * (μ (0, w_out j) : ℂ)) = π_in j
    rw [Icc.coe_zero, add_zero, Complex.ofReal_one, one_mul, hμ0, hh_eq j]
    exact hw_in j
  have hγ1 : ∀ j : Fin k, γ j 1 = π_out j := by
    intro j
    show c (((1 + ((1 : 𝕀) : ℝ) : ℝ) : ℂ) * (μ (1, w_out j) : ℂ)) = π_out j
    have h11 : (1 + ((1 : 𝕀) : ℝ) : ℝ) = 2 := by rw [Icc.coe_one]; norm_num
    rw [h11, hμ1]
    exact hw_out j
  have hπ_ne : ∀ j : Fin k, π_in j ≠ π_out j := by
    intro j heq
    rw [← hγ0 j, ← hγ1 j] at heq
    exact zero_ne_one (hγ_inj heq).2
  let L : Fin k → Set S := fun j => range (γ j)
  have hL_line : ∀ j : Fin k, IsLineWithEnds (L j) (π_in j) (π_out j) := by
    intro j
    have harc : IsArcMap (γ j) := ⟨hγ_cont j, fun t₁ t₂ h => (hγ_inj h).2⟩
    have hl := harc.isLineWithEnds
    rwa [hγ0 j, hγ1 j] at hl
  have hL_disj : Pairwise (fun j₁ j₂ : Fin k => Disjoint (L j₁) (L j₂)) := by
    intro j₁ j₂ hj
    rw [disjoint_left]
    rintro _ ⟨t₁, rfl⟩ ⟨t₂, heq⟩
    exact hj (hγ_inj heq.symm).1
  have hL_sub_B : ∀ j : Fin k, L j ⊆ B := by
    rintro j _ ⟨t, rfl⟩
    rw [← hcB]
    exact mem_image_of_mem c (hz_mem2 j t)
  have hL_inter_A : ∀ j : Fin k, L j ∩ A = {π_in j} := by
    intro j
    ext x
    constructor
    · rintro ⟨⟨t, rfl⟩, hxA⟩
      rw [← hcA] at hxA
      obtain ⟨w, hw, heq⟩ := hxA
      have hw2 : w ∈ closedBall (0 : ℂ) 2 := closedBall_subset_closedBall (by norm_num) hw
      have hzw := hci (hz_mem2 j t) hw2 heq.symm
      have hn : 1 + (t : ℝ) ≤ 1 := by
        rw [← hz_norm j t, hzw]
        exact mem_closedBall_zero_iff.mp hw
      have ht0 : t = 0 := Subtype.ext (show (t : ℝ) = 0 by linarith [t.2.1])
      rw [ht0, hγ0 j]
      rfl
    · rintro rfl
      refine ⟨⟨0, hγ0 j⟩, ?_⟩
      exact Surface.discBd_subset A (hbdA ▸ hπ_in_bd ⟨j, rfl⟩)
  have hL_inter_bdB : ∀ j : Fin k, L j ∩ subBd B = {π_out j} := by
    intro j
    ext x
    constructor
    · rintro ⟨⟨t, rfl⟩, hxB⟩
      rw [hbdB, ← hcs2] at hxB
      obtain ⟨w, hw, heq⟩ := hxB
      have hw2 : w ∈ closedBall (0 : ℂ) 2 := sphere_subset_closedBall hw
      have hzw := hci (hz_mem2 j t) hw2 heq.symm
      have hn : 1 + (t : ℝ) = 2 := by
        rw [← hz_norm j t, hzw]
        exact mem_sphere_zero_iff_norm.mp hw
      have ht1 : t = 1 := Subtype.ext (show (t : ℝ) = 1 by linarith [t.2.2])
      rw [ht1, hγ1 j]
      rfl
    · rintro rfl
      exact ⟨⟨1, hγ1 j⟩, hπ_out_bd ⟨j, rfl⟩⟩
  have hL_int : ∀ j : Fin k, L j \ {π_in j, π_out j} ⊆ (B \ subBd B) \ A := by
    rintro j x ⟨hxL, hx_ends⟩
    refine ⟨⟨hL_sub_B j hxL, fun hx_bd => ?_⟩, fun hxA => ?_⟩
    · have hx_eq : x ∈ ({π_out j} : Set S) := hL_inter_bdB j ▸ ⟨hxL, hx_bd⟩
      exact hx_ends (Or.inr hx_eq)
    · have hx_eq : x ∈ ({π_in j} : Set S) := hL_inter_A j ▸ ⟨hxL, hxA⟩
      exact hx_ends (Or.inl hx_eq)
  let G : Fin k → Drawing S := fun j => lineDrawing (hL_line j) (hπ_ne j)
  have hG_disj : ∀ j₁ j₂ : Fin k, j₁ ≠ j₂ → (G j₁).U ∩ (G j₂).U ⊆ (G j₁).V ∩ (G j₂).V := by
    intro j₁ j₂ hj x ⟨hx₁, hx₂⟩
    exact False.elim (Set.disjoint_left.mp (hL_disj hj) hx₁ hx₂)
  obtain ⟨M, hMU, hMV, hME⟩ := exists_glue_fin G hG_disj
  have hMU' : M.U = ⋃ j : Fin k, L j := hMU
  refine ⟨M, L, hMU', ?_, ?_, ?_, ?_, ?_, hL_line, hπ_ne, hL_disj, hL_int,
    hL_inter_A, hL_inter_bdB⟩
  · rw [hMV]
    ext x
    simp only [G, lineDrawing, mem_iUnion, mem_insert_iff, mem_singleton_iff, mem_union,
      mem_range]
    constructor
    · rintro ⟨j, rfl | rfl⟩
      · exact Or.inl ⟨j, rfl⟩
      · exact Or.inr ⟨j, rfl⟩
    · rintro (⟨j, rfl⟩ | ⟨j, rfl⟩)
      · exact ⟨j, Or.inl rfl⟩
      · exact ⟨j, Or.inr rfl⟩
  · rw [hME]
    ext e
    simp only [G, lineDrawing_E, mem_iUnion, mem_singleton_iff, mem_range]
    exact ⟨fun ⟨j, he⟩ => ⟨j, he.symm⟩, fun ⟨j, he⟩ => ⟨j, he.symm⟩⟩
  · rw [hMU']
    exact iUnion_subset hL_sub_B
  · rw [hMU', iUnion_inter]
    ext x
    simp only [hL_inter_A, mem_iUnion, mem_singleton_iff, mem_range]
    exact ⟨fun ⟨j, hx⟩ => ⟨j, hx.symm⟩, fun ⟨j, hx⟩ => ⟨j, hx.symm⟩⟩
  · rw [hMU', iUnion_inter]
    ext x
    simp only [hL_inter_bdB, mem_iUnion, mem_singleton_iff, mem_range]
    exact ⟨fun ⟨j, hx⟩ => ⟨j, hx.symm⟩, fun ⟨j, hx⟩ => ⟨j, hx.symm⟩⟩

end GraphMinor.GM22
