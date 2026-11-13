module

public import GraphMinor.GM08.Section18PinchedDisc
public import GraphMinor.GM08.Section18Invariance
import Mathlib.Geometry.Manifold.Instances.Sphere
import GraphMinor.Surface.MoveCuff
import GraphMinor.Surface.Classification

/-!
# Graph Minors VIII, (18.2) for every cut

(18.2) on page 286 is about "the" surface obtained by cutting along a schism `X`. We state
cuts with `GM07.IsCutAlongSet`, and `GM08.theorem_18_2` gives some cut with smaller `g`.
Here we show that any two cuts along the same set are homeomorphic, so every cut has
smaller `g` (`GM08.theorem_18_2_every_cut`).

The idea is as follows. Let `ψ₁ : T₁ → S` and `ψ₂ : T₂ → S` be cuts along `X`. Off the
new boundary each cut map is one to one onto `S - (bd(S) ∪ X)`, so there is a map `f`
from the interior of `T₁` to the interior of `T₂` with `ψ₂ ∘ f = ψ₁`, and it is continuous.
Near a boundary point `y` of `T₁` the interior of `T₁` is connected
(`exists_nhds_preconnected_compl_bd`, from a collar of the cuff through `y`). The points of
`T₂` over `ψ₁ y` are finitely many, and have disjoint neighbourhoods. A connected piece of
the interior near `y` is sent by `f` near this fibre, so into one of these neighbourhoods.
So `f` has a limit at `y`, and `f` extends to a continuous map `T₁ → T₂`. The extensions in
both directions are inverse to each other, since they are on the dense interior.
-/

@[expose] public section

namespace GraphMinor.GM08

open Set Topology Filter GraphMinor.Surface

universe u w

/-- Every neighbourhood of a boundary point `y` of a surface contains a neighbourhood of `y`
whose interior points form a nonempty preconnected set. We take a collar of the cuff through
`y` (`exists_collar`) and the image of a product of an arc around `y` with a short interval. -/
theorem exists_nhds_preconnected_compl_bd {S : Type u} [TopologicalSpace S] (hS : IsSurface S)
    {y : S} (hy : y ∈ bd S) {V : Set S} (hV : V ∈ 𝓝 y) :
    ∃ N ∈ 𝓝 y, N ⊆ V ∧ IsPreconnected (N ∩ (bd S)ᶜ) ∧ (N ∩ (bd S)ᶜ).Nonempty := by
  classical
  obtain ⟨hcpt, ht2, -⟩ := id hS
  obtain ⟨-, hfin, hO⟩ := cuff_statement.{u} S hS
  have hy' : y ∈ ⋃₀ cuffs S := by rw [sUnion_cuffs]; exact hy
  obtain ⟨C, hC, hyC⟩ := hy'
  obtain ⟨φ⟩ := hO C hC
  have hUo : IsOpen (⋃₀ (cuffs S \ {C}))ᶜ := ((hfin.subset sdiff_subset).isClosed_sUnion
    fun C' hC' ↦ (hO C' hC'.1).isCompact.isClosed).isOpen_compl
  have hCU : C ⊆ (⋃₀ (cuffs S \ {C}))ᶜ := by
    intro x hx
    rw [mem_compl_iff]
    rintro ⟨C', ⟨hC', hne⟩, hxC'⟩
    exact Set.disjoint_left.mp (cuffs_disjoint hC hC' (Ne.symm hne)) hx hxC'
  obtain ⟨b, hbc, hbi, hbU, hb0, hbo⟩ := exists_collar hS hC φ hUo hCU
  have hbC : ∀ w t, b (w, t) ∈ C → t = 0 := fun w t h' ↦ by
    have h1 := hb0 (φ.symm ⟨_, h'⟩)
    rw [Homeomorph.apply_symm_apply] at h1
    exact congrArg Prod.snd (hbi h1) |>.symm
  -- A point of the collar is on the boundary only at level `0`.
  have hbbd : ∀ w t, b (w, t) ∈ bd S → t = 0 := by
    intro w t hbdx
    have hxb : b (w, t) ∈ ⋃₀ cuffs S := sUnion_cuffs (S := S) ▸ hbdx
    obtain ⟨C', hC', hxC'⟩ := hxb
    by_cases hCC : C' = C
    · exact hbC w t (hCC ▸ hxC')
    · exact absurd ⟨C', ⟨hC', hCC⟩, hxC'⟩ ((mem_compl_iff _ _).mp (hbU ⟨_, rfl⟩))
  have hb0bd : ∀ w, b (w, 0) ∈ bd S := fun w => by
    rw [hb0, ← sUnion_cuffs]
    exact ⟨C, hC, (φ w).2⟩
  set w₀ : Circle := φ.symm ⟨y, hyC⟩ with hw₀
  have hy0 : b (w₀, 0) = y := by rw [hb0, hw₀, Homeomorph.apply_symm_apply]
  set O : Set S := range b \ b '' {x | x.2 = 1} with hOdef
  have hyO : y ∈ O := by
    refine ⟨⟨_, hy0⟩, ?_⟩
    rintro ⟨⟨w, t⟩, h1, h2⟩
    rw [← hy0] at h2
    have h3 : t = 0 := congrArg Prod.snd (hbi h2)
    have h4 : t = 1 := h1
    exact zero_ne_one (h3.symm.trans h4)
  have hpre : b ⁻¹' (V ∩ O) ∈ 𝓝 (w₀, (0 : unitInterval)) :=
    hbc.continuousAt.preimage_mem_nhds (by rw [hy0]; exact inter_mem hV (hbo.mem_nhds hyO))
  obtain ⟨u, hu, v, hv, huv⟩ := mem_nhds_prod_iff.mp hpre
  have : LocallyConnectedSpace Circle :=
    ChartedSpace.locallyConnectedSpace (EuclideanSpace ℝ (Fin 1)) Circle
  obtain ⟨J, hJu, hJo, hw₀J, hJc⟩ :=
    locallyConnectedSpace_iff_subsets_isOpen_isConnected.mp inferInstance w₀ u hu
  obtain ⟨ε, hε, hεv⟩ := Metric.mem_nhds_iff.mp hv
  set I : Set unitInterval := {t | (t : ℝ) < ε} with hIdef
  have hIv : I ⊆ v := fun t ht => hεv (by
    have hd : dist (t : ℝ) ((0 : unitInterval) : ℝ) = t := by
      simp [abs_of_nonneg t.2.1]
    rw [Metric.mem_ball, Subtype.dist_eq, hd]
    exact ht)
  have hIo : IsOpen I := isOpen_lt continuous_subtype_val continuous_const
  have h0I : (0 : unitInterval) ∈ I := by
    change ((0 : unitInterval) : ℝ) < ε
    simpa using hε
  have hbe : IsClosedEmbedding b := hbc.isClosedEmbedding hbi
  obtain ⟨W, hWo, hbW⟩ := hbe.isInducing.isOpen_iff.mp (hJo.prod hIo)
  have hNeq : O ∩ W = b '' (J ×ˢ I) := by
    ext z
    constructor
    · rintro ⟨⟨⟨p, rfl⟩, -⟩, hzW⟩
      exact ⟨p, by rw [← hbW]; exact hzW, rfl⟩
    · rintro ⟨p, hp, rfl⟩
      refine ⟨(huv ⟨hJu hp.1, hIv hp.2⟩).2, ?_⟩
      change p ∈ b ⁻¹' W
      rw [hbW]
      exact hp
  set I' : Set unitInterval := {t | 0 < (t : ℝ) ∧ (t : ℝ) < ε} with hI'def
  have hint : O ∩ W ∩ (bd S)ᶜ = b '' (J ×ˢ I') := by
    rw [hNeq]
    ext z
    constructor
    · rintro ⟨⟨⟨w, t⟩, ⟨hw, ht⟩, rfl⟩, hz⟩
      refine ⟨(w, t), ⟨hw, lt_of_le_of_ne t.2.1 fun h => hz ?_, ht⟩, rfl⟩
      have h0 : t = 0 := Subtype.ext h.symm
      rw [h0]
      exact hb0bd w
    · rintro ⟨⟨w, t⟩, ⟨hw, ht0, ht⟩, rfl⟩
      refine ⟨⟨(w, t), ⟨hw, ht⟩, rfl⟩, fun hz => ?_⟩
      have h0 := hbbd w t hz
      rw [h0] at ht0
      simp at ht0
  have hI'c : IsPreconnected I' := by
    apply OrdConnected.isPreconnected
    refine ⟨fun x hx z hz t ht => ⟨lt_of_lt_of_le hx.1 ht.1, lt_of_le_of_lt ht.2 hz.2⟩⟩
  refine ⟨O ∩ W, (hbo.inter hWo).mem_nhds ⟨hyO, ?_⟩, ?_, ?_, ?_⟩
  · rw [← hy0]
    change (w₀, (0 : unitInterval)) ∈ b ⁻¹' W
    rw [hbW]
    exact ⟨hw₀J, h0I⟩
  · rw [hNeq]
    rintro _ ⟨p, hp, rfl⟩
    exact (huv ⟨hJu hp.1, hIv hp.2⟩).1
  · rw [hint]
    exact (hJc.isPreconnected.prod hI'c).image _ hbc.continuousOn
  · rw [hint]
    have hm : (0 : ℝ) ≤ min (ε / 2) (1 / 2) := le_min (by linarith) (by norm_num)
    have hm1 : min (ε / 2) (1 / 2) ≤ (1 : ℝ) := (min_le_right _ _).trans (by norm_num)
    refine ⟨b (w₀, ⟨min (ε / 2) (1 / 2), hm, hm1⟩), (w₀, _), ⟨hw₀J, ?_, ?_⟩, rfl⟩
    · exact lt_min (by linarith) (by norm_num)
    · exact (min_le_left _ _).trans_lt (by linarith)

/-- The interior of a surface is dense. -/
theorem dense_compl_bd_of_isSurface {S : Type u} [TopologicalSpace S] (hS : IsSurface S) :
    Dense (bd S)ᶜ := by
  intro y
  by_cases hy : y ∈ bd S
  · refine mem_closure_iff_nhds.mpr fun V hV => ?_
    obtain ⟨N, -, hNV, -, hne⟩ := exists_nhds_preconnected_compl_bd hS hy hV
    exact hne.mono (inter_subset_inter_left _ hNV)
  · exact subset_closure hy

/-- A cut along `X` lifts to any other cut along `X`: there is a continuous map between the
cut surfaces that commutes with the cut maps on the interior. -/
theorem IsCutAlongSet.exists_lift {S T₁ T₂ : Type u} [TopologicalSpace S] [TopologicalSpace T₁]
    [TopologicalSpace T₂] (hS : IsSurface S) {X : Set S} {ψ₁ : T₁ → S} {ψ₂ : T₂ → S}
    (h₁ : GM07.IsCutAlongSet X ψ₁) (h₂ : GM07.IsCutAlongSet X ψ₂) :
    ∃ H : T₁ → T₂, Continuous H ∧ ∀ y, y ∉ bd T₁ → ψ₂ (H y) = ψ₁ y := by
  classical
  obtain ⟨-, ht₁, -⟩ := h₁.isSurface
  obtain ⟨hcpt₂, ht₂, -⟩ := h₂.isSurface
  obtain ⟨-, htS, -⟩ := hS
  have := hcpt₂
  have := ht₂
  have := htS
  have := ht₁
  have hc₁ := h₁.quotientMap.continuous
  have hc₂ := h₂.quotientMap.continuous
  have hbd₂ : IsClosed (bd T₂) := (cuff_statement.{u} T₂ h₂.isSurface).1
  have hoff : ∀ y : T₁, y ∉ bd T₁ → ψ₁ y ∉ bd S ∪ X := fun y hy h =>
    hy (by rw [← h₁.preimage_bd]; exact h)
  choose f hf using fun y : T₁ => h₂.quotientMap.surjective (ψ₁ y)
  -- `ψ₂` sends open sets of the interior to open sets.
  have himg : ∀ W : Set T₂, IsOpen W → W ⊆ (bd T₂)ᶜ → IsOpen (ψ₂ '' W) := by
    intro W hW hWi
    refine h₂.quotientMap.isOpen_preimage.mp ?_
    have : ψ₂ ⁻¹' (ψ₂ '' W) = W := by
      ext z
      constructor
      · rintro ⟨w, hw, hwz⟩
        exact (h₂.interior_inj w (hWi hw) z hwz) ▸ hw
      · exact fun hz => ⟨z, hz, rfl⟩
    rw [this]
    exact hW
  -- `f` is continuous at interior points.
  have hcont : ∀ y, y ∉ bd T₁ → ContinuousAt f y := by
    intro y hy
    refine tendsto_nhds.mpr fun V hV hfyV => ?_
    have hfy : f y ∉ bd T₂ := fun h => hoff y hy (by
      rw [← hf y, ← mem_preimage, h₂.preimage_bd]; exact h)
    have hWo : IsOpen (ψ₂ '' (V ∩ (bd T₂)ᶜ)) :=
      himg _ (hV.inter hbd₂.isOpen_compl) inter_subset_right
    have hmem : ψ₁ ⁻¹' (ψ₂ '' (V ∩ (bd T₂)ᶜ)) ∈ 𝓝 y :=
      hc₁.continuousAt.preimage_mem_nhds (hWo.mem_nhds ⟨f y, ⟨hfyV, hfy⟩, hf y⟩)
    refine mem_of_superset hmem fun y' hy' => ?_
    obtain ⟨w, ⟨hwV, hwi⟩, hw⟩ := hy'
    have := h₂.interior_inj w hwi (f y') (hw.trans (hf y').symm)
    show f y' ∈ V
    rw [← this]
    exact hwV
  -- The key step at a boundary point.
  have key : ∀ y, y ∈ bd T₁ → ∀ (U : T₂ → Set T₂), (∀ z, IsOpen (U z)) →
      (∀ z ∈ ψ₂ ⁻¹' {ψ₁ y}, z ∈ U z) → (ψ₂ ⁻¹' {ψ₁ y}).PairwiseDisjoint U →
      ∀ M ∈ 𝓝 y, ∃ z ∈ ψ₂ ⁻¹' {ψ₁ y}, ∃ N ∈ 𝓝 y, N ⊆ M ∧ (N ∩ (bd T₁)ᶜ).Nonempty ∧
        f '' (N ∩ (bd T₁)ᶜ) ⊆ U z := by
    intro y hy U hUo hUmem hUd M hM
    set F := ψ₂ ⁻¹' {ψ₁ y} with hFdef
    set K := ⋃ z ∈ F, U z with hKdef
    have hKo : IsOpen K := isOpen_biUnion fun z _ => hUo z
    have hBo : IsOpen (ψ₂ '' Kᶜ)ᶜ := (hc₂.isClosedMap _ hKo.isClosed_compl).isOpen_compl
    have hxB : ψ₁ y ∈ (ψ₂ '' Kᶜ)ᶜ := by
      rintro ⟨v, hvK, hv⟩
      exact hvK (mem_biUnion (show v ∈ F from hv) (hUmem v hv))
    have hV : M ∩ ψ₁ ⁻¹' (ψ₂ '' Kᶜ)ᶜ ∈ 𝓝 y :=
      inter_mem hM (hc₁.continuousAt.preimage_mem_nhds (hBo.mem_nhds hxB))
    obtain ⟨N, hN, hNV, hPc, ⟨y₀, hy₀⟩⟩ := exists_nhds_preconnected_compl_bd h₁.isSurface hy hV
    have hfK : f '' (N ∩ (bd T₁)ᶜ) ⊆ K := by
      rintro _ ⟨y', hy', rfl⟩
      by_contra hK
      exact (hNV hy'.1).2 ⟨f y', hK, hf y'⟩
    have hfc : IsPreconnected (f '' (N ∩ (bd T₁)ᶜ)) :=
      hPc.image f fun y' hy' => (hcont y' hy'.2).continuousWithinAt
    obtain ⟨z, hzF, hz⟩ := mem_iUnion₂.mp (hfK ⟨y₀, hy₀, rfl⟩)
    refine ⟨z, hzF, N, hN, hNV.trans inter_subset_left, ⟨y₀, hy₀⟩, ?_⟩
    refine hfc.subset_left_of_subset_union (hUo z) (isOpen_biUnion fun z' _ => hUo z')
      (v := ⋃ z' ∈ F \ {z}, U z') ?_ ?_ ⟨f y₀, ⟨y₀, hy₀, rfl⟩, hz⟩
    · refine Set.disjoint_left.mpr fun a ha hb => ?_
      obtain ⟨z', ⟨hz'F, hz'z⟩, ha'⟩ := mem_iUnion₂.mp hb
      exact Set.disjoint_left.mp (hUd hzF hz'F (Ne.symm hz'z)) ha ha'
    · intro a ha
      obtain ⟨z', hz'F, ha'⟩ := mem_iUnion₂.mp (hfK ha)
      by_cases hzz : z' = z
      · exact Or.inl (hzz ▸ ha')
      · exact Or.inr (mem_iUnion₂.mpr ⟨z', ⟨hz'F, hzz⟩, ha'⟩)
  have hlim : ∀ y, ∃ z, Tendsto f (𝓝[(bd T₁)ᶜ] y) (𝓝 z) := by
    intro y
    by_cases hy : y ∈ bd T₁
    · obtain ⟨U, hU, hUd⟩ := (h₂.finite_fiber (ψ₁ y)).t2_separation
      obtain ⟨z₀, hz₀F, N₀, hN₀, -, -, hsub₀⟩ := key y hy U (fun z => (hU z).2)
        (fun z _ => (hU z).1) hUd univ univ_mem
      refine ⟨z₀, (nhds_basis_opens z₀).tendsto_right_iff.mpr fun V ⟨hz₀V, hVo⟩ => ?_⟩
      let U' : T₂ → Set T₂ := fun z => if z = z₀ then U z ∩ V else U z
      have hU'o : ∀ z, IsOpen (U' z) := fun z => by
        by_cases h : z = z₀
        · simp only [U', h, ↓reduceIte]; exact (hU z₀).2.inter hVo
        · simp only [U', h, ↓reduceIte]; exact (hU z).2
      have hU'sub : ∀ z, U' z ⊆ U z := fun z => by
        by_cases h : z = z₀
        · simp only [U', h, ↓reduceIte]; exact inter_subset_left
        · simp only [U', h, ↓reduceIte]; exact le_rfl
      have hU'mem : ∀ z ∈ ψ₂ ⁻¹' {ψ₁ y}, z ∈ U' z := fun z _ => by
        by_cases h : z = z₀
        · subst h; simp only [U', ↓reduceIte]; exact ⟨(hU z).1, hz₀V⟩
        · simp only [U', h, ↓reduceIte]; exact (hU z).1
      have hU'd : (ψ₂ ⁻¹' {ψ₁ y}).PairwiseDisjoint U' := fun a ha b hb hab =>
        (hUd ha hb hab).mono (hU'sub a) (hU'sub b)
      obtain ⟨z, hzF, N, hN, hNN₀, ⟨y₁, hy₁⟩, hsub⟩ := key y hy U' hU'o hU'mem hU'd N₀ hN₀
      have hzz : z = z₀ := by
        by_contra hne
        have h1 : f y₁ ∈ U z := hU'sub z (hsub ⟨y₁, hy₁, rfl⟩)
        have h2 : f y₁ ∈ U z₀ := hsub₀ ⟨y₁, ⟨hNN₀ hy₁.1, hy₁.2⟩, rfl⟩
        exact Set.disjoint_left.mp (hUd hzF hz₀F hne) h1 h2
      subst hzz
      refine mem_of_superset (inter_mem_nhdsWithin _ hN) fun y' hy' => ?_
      have h1 := hsub ⟨y', ⟨hy'.2, hy'.1⟩, rfl⟩
      simp only [U', ↓reduceIte] at h1
      exact h1.2
    · exact ⟨f y, (hcont y hy).tendsto.mono_left nhdsWithin_le_nhds⟩
  refine ⟨extendFrom (bd T₁)ᶜ f, continuous_extendFrom (dense_compl_bd_of_isSurface h₁.isSurface)
    hlim, fun y hy => ?_⟩
  rw [extendFrom_eq (subset_closure hy) ((hcont y hy).tendsto.mono_left nhdsWithin_le_nhds)]
  exact hf y

/-- Any two cuts along the same set are homeomorphic. -/
theorem IsCutAlongSet.nonempty_homeomorph {S T₁ T₂ : Type u} [TopologicalSpace S]
    [TopologicalSpace T₁] [TopologicalSpace T₂] (hS : IsSurface S) {X : Set S}
    {ψ₁ : T₁ → S} {ψ₂ : T₂ → S} (h₁ : GM07.IsCutAlongSet X ψ₁)
    (h₂ : GM07.IsCutAlongSet X ψ₂) : Nonempty (T₁ ≃ₜ T₂) := by
  obtain ⟨H, hH, hHψ⟩ := IsCutAlongSet.exists_lift hS h₁ h₂
  obtain ⟨H', hH', hH'ψ⟩ := IsCutAlongSet.exists_lift hS h₂ h₁
  obtain ⟨-, ht₁, -⟩ := h₁.isSurface
  obtain ⟨-, ht₂, -⟩ := h₂.isSurface
  have := ht₁
  have := ht₂
  -- Interior points go to interior points.
  have hint : ∀ {T T' : Type u} [TopologicalSpace T] [TopologicalSpace T'] {φ : T → S}
      {φ' : T' → S} (_ : GM07.IsCutAlongSet X φ) (_ : GM07.IsCutAlongSet X φ') (G : T → T'),
      (∀ y, y ∉ bd T → φ' (G y) = φ y) → ∀ y, y ∉ bd T → G y ∉ bd T' := by
    intro T T' _ _ φ φ' hφ hφ' G hG y hy hGy
    refine hy ?_
    rw [← hφ.preimage_bd, mem_preimage, ← hG y hy]
    rw [← hφ'.preimage_bd] at hGy
    exact hGy
  have hleft : H' ∘ H = id := by
    refine Continuous.ext_on (dense_compl_bd_of_isSurface h₁.isSurface) (hH'.comp hH)
      continuous_id fun y hy => ?_
    have hHy := hint h₁ h₂ H hHψ y hy
    exact (h₁.interior_inj y hy _ ((hH'ψ _ hHy).trans (hHψ y hy)).symm).symm
  have hright : H ∘ H' = id := by
    refine Continuous.ext_on (dense_compl_bd_of_isSurface h₂.isSurface) (hH.comp hH')
      continuous_id fun y hy => ?_
    have hHy := hint h₂ h₁ H' hH'ψ y hy
    exact (h₂.interior_inj y hy _ ((hHψ _ hHy).trans (hH'ψ y hy)).symm).symm
  exact ⟨Homeomorph.mk ⟨H, H', congrFun hleft, congrFun hright⟩ hH hH'⟩

/-- **Graph Minors VIII, (18.2)** (page 286), for every cut:
"Let $\Sigma$ be a connected surface, not a sphere, disc or cylinder, and let $X$ be a
schism in $\Sigma$. Let $\Sigma'$ be obtained from $\Sigma$ by cutting along $X$. Then
$g(\Sigma') < g(\Sigma)$."
Every cut along `X` in the sense of `GM07.IsCutAlongSet` is homeomorphic to the cut given by
`GM08.theorem_18_2_proof` (`IsCutAlongSet.nonempty_homeomorph`), so it has smaller `g`. -/
theorem theorem_18_2_every_cut (S : Type w) [TopologicalSpace S] [ConnectedSpace S]
    (hS : IsSurface S) (a b c : ℕ) (h3 : 3 ≤ 3 * a + 3 * b + c)
    (he : Nonempty (S ≃ₜ SurfaceModel a b c)) (X : Set S) (hX : GM07.IsSchism X)
    (T : Type w) [TopologicalSpace T] (ψ : T → S) (hψ : GM07.IsCutAlongSet X ψ) :
    surfaceComplexity T < surfaceComplexity S := by
  obtain ⟨T', _, ψ', hψ', hlt⟩ := theorem_18_2_proof S hS a b c h3 he X hX
  obtain ⟨e⟩ := IsCutAlongSet.nonempty_homeomorph hS hψ hψ'
  rw [surfaceComplexity_congr e]
  exact hlt

end GraphMinor.GM08
