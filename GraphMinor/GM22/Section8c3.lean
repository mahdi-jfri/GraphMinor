module

public import GraphMinor.GM22.Section8c2
public import GraphMinor.GM12.Section4NormalArcDisc
public import GraphMinor.GM12.Section2StraightArcChart
public import GraphMinor.GM12.Section4ThinArcDisc
public import GraphMinor.GM12.Section4ThinStripDisc
public import GraphMinor.GM12.Section4ThinPlaneDisc
public import GraphMinor.GM12.Section4PinchedDisc
public import GraphMinor.Surface.Classification
public import GraphMinor.Surface.ArcDisc
import GraphMinor.GM12.Section79

/-!
# Graph Minors XXII – Section 8 (Part 3c): Adjusted Embedding and Edge-Disc Augmentation for (8.3)

This file provides the auxiliary constructions needed to assemble the `(J1)`–`(J7)` system in
the proof of **Theorem (8.3)** of Robertson and Seymour,
*Graph Minors. XXII. Irrelevant vertices in linkage problems*,
J. Combin. Theory Ser. B **102** (2012), 530–563 (pages 561–563):

- `exists_adjusted_embedding_8_3`: adjusts the surface-to-vertex embedding `ιV : S ↪ α` to
  `ιV' : S ↪ α` so that `ιV'` agrees with `ιV` on `Γ.V`, satisfies `ιV' (α_map z) = z` for all
  `z ∈ Z`, and maps `S \ (Γ.V ∪ α_map '' Z)` outside `V(G)`.
- `exists_normal_arc_disc_interior` and `exists_shared_endpoint_arc_discs`: thickens any finite
  family of arcs in a closed surface whose pairwise intersections lie in their endpoints into
  thin closed discs whose boundaries meet the arcs only at their endpoints.
- Correction of the edge-coverage oversight on page 562 (`K ∪ ⋃(A : A ∈ 𝒜') = G`):
  edges in `E_Γ_rem = {e ∈ Γ.E | ιE e ∉ ⋃ A ∈ 𝒜', E(A)}` (which were deleted from `K` on page 561
  so that `E(N) ∩ E(K) = ∅`) are wrapped as single-edge pieces `edgePiece` with thin
  closed discs `D_edge e`, ensuring `E(K) ∪ ⋃ B ∈ 𝒜'', E(B) = E(G)` while preserving `(J1)`–`(J7)`
  with the same `N` and `K`.
-/

@[expose] public section

namespace GraphMinor.GM22

open Classical Set Function Topology Metric Graph Hypergraph
open GraphMinor GraphMinor.Surface GraphMinor.GM06 GraphMinor.GM09 GraphMinor.GM10 GraphMinor.GM11
open GraphMinor.GM12 GraphMinor.GM14 GraphMinor.GM14.Whitney

universe w u v u₁ v₁

variable {S : Type w} [TopologicalSpace S] [T2Space S]
  {α : Type u} {β : Type v}

/-! ## 1. Adjusted Vertex Embedding `ιV' : S ↪ α` -/

/-- Because `S` is a sphere (hence infinite) and `V(G)`, `Γ.V`, and `Z` are finite, there exists an
embedding `ιV' : S ↪ α` that agrees with `ιV` on `Γ.V`, sends `α_map z` to `z` for every `z ∈ Z`,
and maps every point outside `Γ.V ∪ α_map '' Z` outside `V(G)`. -/
theorem exists_adjusted_embedding_8_3
    {q δ h θ : ℕ}
    {ιV : S ↪ α} {ιE : Set S ↪ β}
    {R_G : RootedDigraph α β q} {W : Set α}
    {Γ C₀ : Drawing S} {r₀ : Set S} {orient : GM19.SurfaceOrientation S}
    {PiSet : Set S}
    {ord : ℕ} {T : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    {d : Set S → Set S → ℕ}
    {J : Graph α β} {Z : Set α} {𝒜 : Set (Graph α β)}
    {πLen : Graph α β → ℕ} {πA : ∀ A : Graph α β, Fin (πLen A) → α}
    {vA : Graph α β → S} {D_disc : Set S} {v_star : S}
    (h83 : Hypotheses83 q δ h θ ιV ιE R_G W Γ C₀ r₀ orient PiSet ord T d J Z 𝒜
      πLen πA vA D_disc v_star)
    {α_map : α → S}
    (hα_inj : ∀ v ∈ Z, ∀ v' ∈ Z, v ≠ v' → α_map v ≠ α_map v')
    (hα_ΓU : ∀ v ∈ Z, α_map v ∈ Γ.U ↔ v ∈ ιV '' Γ.V)
    (hα_ΓV : ∀ s ∈ Γ.V, ιV s ∈ Z → α_map (ιV s) = s) :
    ∃ ιV' : S ↪ α,
      (∀ s ∈ Γ.V, ιV' s = ιV s) ∧
      (∀ z ∈ Z, ιV' (α_map z) = z) ∧
      (∀ s : S, ιV' s ∈ V(R_G.G.toGraph) ↔ s ∈ Γ.V ∪ (α_map '' Z)) := by
  let G := R_G.G.toGraph
  have hZ_sub_VG : Z ⊆ V(G) :=
    (h83.hyp_vi.1.trans sdiff_subset).trans h83.hyp_v.1.vertexSet_mono
  have hΓV_sub_VG : ιV '' Γ.V ⊆ V(G) :=
    (h83.Γ_le.trans Graph.deleteVerts_le).vertexSet_mono
  have hZ_fin : Z.Finite := h83.finite_V.subset hZ_sub_VG
  let F : Set S := ιV ⁻¹' V(G)
  have hF_fin : F.Finite := h83.finite_V.preimage ιV.injective.injOn
  -- `S` is infinite since `D_disc` is a closed disc (`exists_isChart` gives an injection from `closedBall (0 : ℂ) 1`).
  obtain ⟨h_ch, g_ch, ch⟩ := h83.hyp_xii.1.exists_isChart
  have : Infinite S := Infinite.of_injective
    (fun k : ℕ => g_ch ((1 / (k + 2 : ℝ) : ℝ) : ℂ))
    (fun k₁ k₂ hk => by
      have hz_mem : ∀ k : ℕ, (((1 / (k + 2 : ℝ) : ℝ) : ℂ)) ∈ closedBall (0 : ℂ) 1 := fun k => by
        rw [mem_closedBall_zero_iff, Complex.norm_real, Real.norm_eq_abs,
          abs_of_pos (by positivity)]
        exact div_le_one_of_le₀ (by linarith) (by positivity)
      have h1 : (((1 / (k₁ + 2 : ℝ) : ℝ) : ℂ)) = (((1 / (k₂ + 2 : ℝ) : ℝ) : ℂ)) := by
        rw [← ch.hg (hz_mem k₁), ← ch.hg (hz_mem k₂)]
        exact congrArg h_ch hk
      have h2 := Complex.ofReal_injective h1
      have h3 : (k₁ : ℝ) + 2 = (k₂ : ℝ) + 2 := by
        have := congrArg Inv.inv h2
        simpa [one_div] using this
      exact Nat.cast_injective (add_right_cancel h3))
  have hSF_inf : (Set.univ \ F).Infinite := Set.infinite_univ.sdiff hF_fin
  let η : ℕ ↪ ↑(Set.univ \ F) := hSF_inf.natEmbedding
  have : Finite F := hF_fin.to_subtype
  obtain ⟨n, ⟨e_F⟩⟩ := Finite.exists_equiv_fin F
  -- Define an injection `ψ : S → S` with range in `Set.univ \ F`.
  let ψ : S → S := fun s =>
    if hsF : s ∈ F then (η (e_F ⟨s, hsF⟩).val).1
    else if hsη : ∃ k : ℕ, (η k).1 = s then (η (Classical.choose hsη + n)).1
    else s
  have hψ_not_F : ∀ s : S, ψ s ∉ F := by
    intro s
    dsimp only [ψ]
    split_ifs with hsF hsη
    · exact (η (e_F ⟨s, hsF⟩).val).2.2
    · exact (η (Classical.choose hsη + n)).2.2
    · exact hsF
  have hψ_inj : Function.Injective ψ := by
    intro s₁ s₂ heq
    have hη_inj : ∀ a b : ℕ, (η a).1 = (η b).1 → a = b :=
      fun a b h => η.injective (Subtype.ext h)
    by_cases h1F : s₁ ∈ F <;> by_cases h2F : s₂ ∈ F
    · have heq' : (η (e_F ⟨s₁, h1F⟩).val).1 = (η (e_F ⟨s₂, h2F⟩).val).1 := by
        simpa [ψ, h1F, h2F] using heq
      exact congrArg Subtype.val (e_F.injective (Fin.ext (hη_inj _ _ heq')))
    · by_cases h2η : ∃ k : ℕ, (η k).1 = s₂
      · have heq' : (η (e_F ⟨s₁, h1F⟩).val).1 = (η (Classical.choose h2η + n)).1 := by
          simpa [ψ, h1F, h2F, h2η] using heq
        have hidx := hη_inj _ _ heq'
        have hlt := (e_F ⟨s₁, h1F⟩).isLt
        omega
      · have heq' : (η (e_F ⟨s₁, h1F⟩).val).1 = s₂ := by
          simpa [ψ, h1F, h2F, h2η] using heq
        exact False.elim (h2η ⟨(e_F ⟨s₁, h1F⟩).val, heq'⟩)
    · by_cases h1η : ∃ k : ℕ, (η k).1 = s₁
      · have heq' : (η (Classical.choose h1η + n)).1 = (η (e_F ⟨s₂, h2F⟩).val).1 := by
          simpa [ψ, h1F, h1η, h2F] using heq
        have hidx := hη_inj _ _ heq'
        have hlt := (e_F ⟨s₂, h2F⟩).isLt
        omega
      · have heq' : s₁ = (η (e_F ⟨s₂, h2F⟩).val).1 := by
          simpa [ψ, h1F, h1η, h2F] using heq
        exact False.elim (h1η ⟨(e_F ⟨s₂, h2F⟩).val, heq'.symm⟩)
    · by_cases h1η : ∃ k : ℕ, (η k).1 = s₁ <;> by_cases h2η : ∃ k : ℕ, (η k).1 = s₂
      · have heq' : (η (Classical.choose h1η + n)).1 = (η (Classical.choose h2η + n)).1 := by
          simpa [ψ, h1F, h1η, h2F, h2η] using heq
        have hidx := hη_inj _ _ heq'
        have hk : Classical.choose h1η = Classical.choose h2η := by omega
        rw [← Classical.choose_spec h1η, ← Classical.choose_spec h2η, hk]
      · have heq' : (η (Classical.choose h1η + n)).1 = s₂ := by
          simpa [ψ, h1F, h1η, h2F, h2η] using heq
        exact False.elim (h2η ⟨Classical.choose h1η + n, heq'⟩)
      · have heq' : s₁ = (η (Classical.choose h2η + n)).1 := by
          simpa [ψ, h1F, h1η, h2F, h2η] using heq
        exact False.elim (h1η ⟨Classical.choose h2η + n, heq'.symm⟩)
      · simpa [ψ, h1F, h1η, h2F, h2η] using heq
  -- Now define `f : S → α`.
  let f : S → α := fun s =>
    if s ∈ Γ.V then ιV s
    else if hz : ∃ z ∈ Z, α_map z = s then Classical.choose hz
    else ιV (ψ s)
  have hf_ΓV : ∀ s ∈ Γ.V, f s = ιV s := fun s hs => by simp [f, hs]
  have hf_Z : ∀ z ∈ Z, f (α_map z) = z := by
    intro z hz
    dsimp only [f]
    split_ifs with hsV hex
    · have hz_ΓU : α_map z ∈ Γ.U := Γ.V_subset_U hsV
      obtain ⟨v, hv, rfl⟩ := (hα_ΓU z hz).mp hz_ΓU
      rw [hα_ΓV v hv hz]
    · obtain ⟨hz', hα_eq⟩ := Classical.choose_spec hex
      by_contra hne
      exact hα_inj (Classical.choose hex) hz' z hz hne hα_eq
    · exact False.elim (hex ⟨z, hz, rfl⟩)
  have hf_mem_VG : ∀ s : S, f s ∈ V(G) ↔ s ∈ Γ.V ∪ (α_map '' Z) := by
    intro s
    constructor
    · intro hmem
      dsimp only [f] at hmem
      split_ifs at hmem with hsV hex
      · exact Or.inl hsV
      · rcases hex with ⟨z, hz, rfl⟩
        exact Or.inr ⟨z, hz, rfl⟩
      · exact False.elim (hψ_not_F s hmem)
    · rintro (hsV | ⟨z, hz, rfl⟩)
      · rw [hf_ΓV s hsV]
        exact hΓV_sub_VG ⟨s, hsV, rfl⟩
      · rw [hf_Z z hz]
        exact hZ_sub_VG hz
  have hf_inj : Function.Injective f := by
    intro s₁ s₂ heq
    by_cases h1 : s₁ ∈ Γ.V ∪ (α_map '' Z)
    · have h2 : s₂ ∈ Γ.V ∪ (α_map '' Z) :=
        (hf_mem_VG s₂).mp (heq ▸ (hf_mem_VG s₁).mpr h1)
      rcases h1 with h1V | ⟨z₁, hz₁, rfl⟩ <;> rcases h2 with h2V | ⟨z₂, hz₂, rfl⟩
      · rw [hf_ΓV s₁ h1V, hf_ΓV s₂ h2V] at heq
        exact ιV.injective heq
      · rw [hf_ΓV s₁ h1V, hf_Z z₂ hz₂] at heq
        subst heq
        exact (hα_ΓV s₁ h1V hz₂).symm
      · rw [hf_Z z₁ hz₁, hf_ΓV s₂ h2V] at heq
        subst heq
        exact hα_ΓV s₂ h2V hz₁
      · rw [hf_Z z₁ hz₁, hf_Z z₂ hz₂] at heq
        rw [heq]
    · have h2 : s₂ ∉ Γ.V ∪ (α_map '' Z) := fun h2 =>
        h1 ((hf_mem_VG s₁).mp (heq.symm ▸ (hf_mem_VG s₂).mpr h2))
      have h1_notV : s₁ ∉ Γ.V := fun h => h1 (Or.inl h)
      have h1_notZ : ¬ ∃ z ∈ Z, α_map z = s₁ := fun ⟨z, hz, h⟩ => h1 (Or.inr ⟨z, hz, h⟩)
      have h2_notV : s₂ ∉ Γ.V := fun h => h2 (Or.inl h)
      have h2_notZ : ¬ ∃ z ∈ Z, α_map z = s₂ := fun ⟨z, hz, h⟩ => h2 (Or.inr ⟨z, hz, h⟩)
      have hf1 : f s₁ = ιV (ψ s₁) := by simp [f, h1_notV, h1_notZ]
      have hf2 : f s₂ = ιV (ψ s₂) := by simp [f, h2_notV, h2_notZ]
      rw [hf1, hf2] at heq
      exact hψ_inj (ιV.injective heq)
  exact ⟨⟨f, hf_inj⟩, hf_ΓV, hf_Z, hf_mem_VG⟩

/-! ## 2. Thin Closed Discs Around Shared-Endpoint Arcs -/

/-- Refinement of `GM12.exists_thin_plane_disc` recording that the boundary `discBd D` meets the
segment `[-1, 1]` only at `{-1, 1}`. -/
theorem exists_thin_plane_disc_interior
    {O B : Set ℂ} (hO : IsOpen O) (hB : IsClosed B)
    (hsegO : Complex.ofReal '' Icc (-1 : ℝ) 1 ⊆ O)
    (hBseg : B ∩ (Complex.ofReal '' Icc (-1 : ℝ) 1) ⊆ {-1, 1})
    (hleft : (-1 : ℂ) ∈ B) (hright : (1 : ℂ) ∈ B) :
    ∃ D : Set ℂ, IsClosedDisc D ∧ D ⊆ O ∧ D ∩ B = {-1, 1} ∧
      ({-1, 1} : Set ℂ) ⊆ discBd D ∧
      Complex.ofReal '' Icc (-1 : ℝ) 1 ⊆ D ∧
      discBd D ∩ (Complex.ofReal '' Icc (-1 : ℝ) 1) = {-1, 1} := by
  let F : Set ℂ := Oᶜ ∪ B
  have hF : IsClosed F := hO.isClosed_compl.union hB
  have hFne : F.Nonempty := ⟨-1, Or.inr hleft⟩
  let ε : ℝ → ℝ := fun x => min 1 (infDist (x : ℂ) F / 2)
  have hεc : Continuous ε := continuous_const.min
    (((continuous_infDist_pt F).comp Complex.continuous_ofReal).div_const 2)
  have hεnn : ∀ x, 0 ≤ ε x := fun x => le_min (by norm_num)
    (div_nonneg infDist_nonneg (by norm_num))
  have hεpos : ∀ x ∈ Ioo (-1 : ℝ) 1, 0 < ε x := by
    intro x hx
    have hxseg : (x : ℂ) ∈ Complex.ofReal '' Icc (-1 : ℝ) 1 :=
      ⟨x, ⟨hx.1.le, hx.2.le⟩, rfl⟩
    have hxF : (x : ℂ) ∉ F := by
      rintro (hxO | hxB)
      · exact hxO (hsegO hxseg)
      · have hend := hBseg ⟨hxB, hxseg⟩
        rcases hend with h | h
        · have h' := congrArg Complex.re h
          simp only [Complex.ofReal_re, Complex.neg_re, Complex.one_re] at h'
          linarith [hx.1]
        · have h' := congrArg Complex.re (Set.mem_singleton_iff.mp h)
          simp only [Complex.ofReal_re, Complex.one_re] at h'
          linarith [hx.2]
    have hdist : 0 < infDist (x : ℂ) F :=
      (infDist_pos_iff_notMem_closure hFne).mp (by rw [hF.closure_eq]; exact hxF)
    exact lt_min (by norm_num) (half_pos hdist)
  have hzero₀ : infDist (-1 : ℂ) F = 0 :=
    Metric.infDist_zero_of_mem (s := F) (x := -1) (Or.inr hleft)
  have hzero₁ : infDist (1 : ℂ) F = 0 :=
    Metric.infDist_zero_of_mem (s := F) (x := 1) (Or.inr hright)
  have hεends : ε (-1) = 0 ∧ ε 1 = 0 := by
    constructor <;> simp [ε, hzero₀, hzero₁]
  let f : ℂ → ℂ := fun z => (z.re : ℂ) + (ε z.re * z.im : ℝ) * Complex.I
  have hfc : Continuous f := (Complex.continuous_ofReal.comp Complex.continuous_re).add
    ((Complex.continuous_ofReal.comp ((hεc.comp Complex.continuous_re).mul
      Complex.continuous_im)).mul_const Complex.I)
  have hfi := GM12.pinched_disc_injOn ε (fun x hx => (hεpos x hx).ne')
  have hdisc := Surface.isClosedDisc_image_injOn Surface.isClosedDisc_closedBall.1
    (isCompact_closedBall (0 : ℂ) 1) hfc.continuousOn hfi
  have hendf : f (-1) = -1 ∧ f 1 = 1 := by
    constructor <;> simp [f, hεends.1, hεends.2]
  have hloc : ∀ z ∈ closedBall (0 : ℂ) 1,
      f z ∈ O ∧ (f z ∈ B → f z ∈ ({-1, 1} : Set ℂ)) := by
    intro z hz
    have hzN : ‖z‖ ≤ 1 := mem_closedBall_zero_iff.mp hz
    have hre := abs_le.mp ((Complex.abs_re_le_norm z).trans hzN)
    have him := (Complex.abs_im_le_norm z).trans hzN
    by_cases hmid : z.re ∈ Ioo (-1 : ℝ) 1
    · have hdist : dist (f z) (z.re : ℂ) ≤ ε z.re := by
        have heq : f z - (z.re : ℂ) = (ε z.re * z.im : ℝ) * Complex.I := by
          dsimp only [f]; ring
        rw [dist_eq_norm, heq, norm_mul, Complex.norm_I, mul_one, Complex.norm_real,
          Real.norm_eq_abs, abs_mul, abs_of_nonneg (hεnn _)]
        exact mul_le_of_le_one_right (hεnn _) him
      have hsmall : ε z.re < infDist (z.re : ℂ) F :=
        (min_le_right _ _).trans_lt (half_lt_self (by
          have hpos := hεpos z.re hmid
          have hle : ε z.re ≤ infDist (z.re : ℂ) F / 2 := min_le_right _ _
          linarith))
      have hnot : f z ∉ F := by
        intro hmem
        have hle := infDist_le_dist_of_mem (x := (z.re : ℂ)) hmem
        rw [dist_comm] at hle
        exact (hdist.trans_lt hsmall).not_ge hle
      exact ⟨not_not.mp (fun hn => hnot (Or.inl hn)), fun hb => False.elim (hnot (Or.inr hb))⟩
    · have hext : z.re = -1 ∨ z.re = 1 := by
        simp only [mem_Ioo] at hmid
        rcases le_or_gt z.re (-1) with h | h
        · exact Or.inl (le_antisymm h hre.1)
        · exact Or.inr (le_antisymm hre.2 (not_lt.mp (fun h' => hmid ⟨h, h'⟩)))
      have hfend : f z ∈ ({-1, 1} : Set ℂ) := by
        rcases hext with he | he
        · simp [f, he, hεends.1]
        · simp [f, he, hεends.2]
      have hOend : ({-1, 1} : Set ℂ) ⊆ O := by
        intro w hw
        apply hsegO
        rcases hw with rfl | hw
        · exact ⟨-1, by norm_num, by simp⟩
        · have hw' := Set.mem_singleton_iff.mp hw
          exact hw' ▸ ⟨1, by norm_num, by simp⟩
      exact ⟨hOend hfend, fun _ => hfend⟩
  have hbd_ends : ({-1, 1} : Set ℂ) ⊆ discBd (f '' closedBall 0 1) := by
    rw [hdisc.2, Surface.isClosedDisc_closedBall.2]
    intro w hw
    rcases hw with rfl | hw
    · exact ⟨-1, by norm_num, hendf.1⟩
    · have hw' := Set.mem_singleton_iff.mp hw
      subst w
      exact ⟨1, by norm_num, hendf.2⟩
  refine ⟨f '' closedBall 0 1, hdisc.1, ?_, ?_, hbd_ends, ?_, ?_⟩
  · rintro _ ⟨z, hz, rfl⟩
    exact (hloc z hz).1
  · apply Set.Subset.antisymm
    · rintro w ⟨⟨z, hz, rfl⟩, hwB⟩
      exact (hloc z hz).2 hwB
    · intro w hw
      rcases hw with rfl | hw
      · exact ⟨⟨-1, by norm_num, hendf.1⟩, hleft⟩
      · have hw' := Set.mem_singleton_iff.mp hw
        subst w
        exact ⟨⟨1, by norm_num, hendf.2⟩, hright⟩
  · rintro _ ⟨x, hx, rfl⟩
    refine ⟨(x : ℂ), ?_, ?_⟩
    · rw [mem_closedBall_zero_iff, Complex.norm_real, Real.norm_eq_abs]
      exact abs_le.mpr hx
    · simp [f]
  · apply Set.Subset.antisymm
    · rw [hdisc.2, Surface.isClosedDisc_closedBall.2]
      rintro w ⟨⟨z, hz_sph, rfl⟩, ⟨x, hx, hfx⟩⟩
      have hz_ball : z ∈ closedBall (0 : ℂ) 1 := sphere_subset_closedBall hz_sph
      have hx_ball : (x : ℂ) ∈ closedBall (0 : ℂ) 1 := by
        rw [mem_closedBall_zero_iff, Complex.norm_real, Real.norm_eq_abs]
        exact abs_le.mpr hx
      have hfx_eq : f (x : ℂ) = (x : ℂ) := by simp [f]
      have hzx : z = (x : ℂ) := hfi hz_ball hx_ball (hfx.symm.trans hfx_eq.symm)
      rw [hzx, mem_sphere_zero_iff_norm, Complex.norm_real, Real.norm_eq_abs, abs_eq (by norm_num)]
        at hz_sph
      rcases hz_sph with rfl | rfl
      · rw [← hfx]; exact Or.inr (by norm_num)
      · rw [← hfx]; exact Or.inl (by norm_num)
    · refine subset_inter hbd_ends ?_
      intro w hw
      rcases hw with rfl | hw
      · exact ⟨-1, by norm_num, by simp⟩
      · have hw' := Set.mem_singleton_iff.mp hw
        exact hw' ▸ ⟨1, by norm_num, by simp⟩

/-- Refinement of `GM12.exists_thin_disc_of_strip_arc` recording `discBd D ∩ range a = {a 0, a 1}`. -/
theorem exists_thin_disc_of_strip_arc_interior
    {S₀ : Type*} [TopologicalSpace S₀] [T2Space S₀]
    {O : Set ℂ} {K : ℂ → S₀} (hO : IsOpen O)
    (hKc : ContinuousOn K O) (hKi : InjOn K O)
    {a : unitInterval → S₀} (ha : IsArcMap a)
    {θ : unitInterval → ℝ} (hθc : Continuous θ) (hθm : StrictMono θ)
    (hθK : ∀ t, (θ t : ℂ) ∈ O ∧ K (θ t) = a t)
    {B : Set S₀} (hB : IsClosed B) (hleft : a 0 ∈ B) (hright : a 1 ∈ B)
    (hmeet : range a ∩ B ⊆ {a 0, a 1}) :
    ∃ D : Set S₀, IsClosedDisc D ∧ D ∩ B = {a 0, a 1} ∧
      ({a 0, a 1} : Set S₀) ⊆ discBd D ∧ range a ⊆ D ∧
      discBd D ∩ range a = {a 0, a 1} := by
  let s : ℝ := (θ 1 - θ 0) / 2
  have hs : 0 < s := half_pos (sub_pos.mpr (hθm (show (0 : unitInterval) < 1 by norm_num)))
  let A : ℂ → ℂ := fun z => (θ 0 : ℂ) + (s : ℂ) * (z + 1)
  have hAc : Continuous A := by fun_prop
  have hAi : Function.Injective A := by
    intro z w h
    have hs' : (s : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hs.ne'
    exact add_right_cancel (mul_left_cancel₀ hs' (add_left_cancel h))
  have hAleft : A (-1) = (θ 0 : ℂ) := by simp [A]
  have hAright : A 1 = (θ 1 : ℂ) := by
    dsimp only [A, s]
    push_cast
    ring
  have hseg : ∀ z ∈ Complex.ofReal '' Icc (-1 : ℝ) 1,
      ∃ t : unitInterval, A z = (θ t : ℂ) := by
    rintro _ ⟨x, hx, rfl⟩
    have hn : θ 0 + s * (x + 1) ∈ Icc (θ 0) (θ 1) := by
      have hlo : 0 ≤ x + 1 := by linarith [hx.1]
      have hhi : x + 1 ≤ 2 := by linarith [hx.2]
      have heq : s * 2 = θ 1 - θ 0 := by dsimp only [s]; ring
      constructor
      · exact le_add_of_nonneg_right (mul_nonneg hs.le hlo)
      · have hmul := mul_le_mul_of_nonneg_left hhi hs.le
        rw [heq] at hmul
        linarith
    have himage := hθc.image_Icc_of_strictMono (a := 0) (b := 1) hθm
    have hn' : θ 0 + s * (x + 1) ∈ θ '' Icc (0 : unitInterval) 1 := by
      rw [himage]
      exact hn
    obtain ⟨t, _, ht⟩ := hn'
    refine ⟨t, ?_⟩
    dsimp only [A]
    exact_mod_cast ht.symm
  let G : Set ℂ := O ∩ K ⁻¹' Bᶜ
  have hG : IsOpen G := hKc.isOpen_inter_preimage hO hB.isOpen_compl
  let O' : Set ℂ := A ⁻¹' O
  let B' : Set ℂ := (A ⁻¹' G)ᶜ
  have hO' : IsOpen O' := hO.preimage hAc
  have hB' : IsClosed B' := (hG.preimage hAc).isClosed_compl
  have hsegO : Complex.ofReal '' Icc (-1 : ℝ) 1 ⊆ O' := by
    intro z hz
    obtain ⟨t, ht⟩ := hseg z hz
    change A z ∈ O
    rw [ht]
    exact (hθK t).1
  have hB'seg : B' ∩ (Complex.ofReal '' Icc (-1 : ℝ) 1) ⊆ {-1, 1} := by
    rintro z ⟨hzB, hzseg⟩
    obtain ⟨t, ht⟩ := hseg z hzseg
    have hatB : a t ∈ B := by
      by_contra hn
      apply hzB
      exact ⟨ht ▸ (hθK t).1, by change K (A z) ∉ B; rw [ht, (hθK t).2]; exact hn⟩
    have hend := hmeet ⟨mem_range_self t, hatB⟩
    rcases hend with he | he
    · have ht0 : t = 0 := ha.2 he
      exact Or.inl (hAi (ht.trans (ht0 ▸ hAleft.symm)))
    · have ht1 : t = 1 := ha.2 (Set.mem_singleton_iff.mp he)
      exact Or.inr (Set.mem_singleton_iff.mpr (hAi (ht.trans (ht1 ▸ hAright.symm))))
  have hB'left : (-1 : ℂ) ∈ B' := by
    intro h
    exact h.2 (by rw [hAleft, (hθK 0).2]; exact hleft)
  have hB'right : (1 : ℂ) ∈ B' := by
    intro h
    exact h.2 (by rw [hAright, (hθK 1).2]; exact hright)
  obtain ⟨D, hD, hDO, hDB, hends, hsegD, hbd_seg⟩ :=
    exists_thin_plane_disc_interior hO' hB' hsegO hB'seg hB'left hB'right
  let f : ℂ → S₀ := fun z => K (A z)
  have hfc : ContinuousOn f O' := hKc.comp hAc.continuousOn (fun _ hx => hx)
  have hfi : InjOn f O' := fun z hz w hw he => hAi (hKi hz hw he)
  have himage := Surface.isClosedDisc_image_injOn hD hD.isCompact (hfc.mono hDO) (hfi.mono hDO)
  have hfleft : f (-1) = a 0 := by dsimp only [f]; rw [hAleft, (hθK 0).2]
  have hfright : f 1 = a 1 := by dsimp only [f]; rw [hAright, (hθK 1).2]
  have hmem : ∀ z ∈ D, f z ∈ B → z ∈ B' := fun z _ hzB hzG => hzG.2 hzB
  have hseg_pt : ∀ t : unitInterval,
      ∃ x ∈ Icc (-1 : ℝ) 1, (x : ℂ) ∈ D ∧ f (x : ℂ) = a t := by
    intro t
    let x : ℝ := (θ t - θ 0) / s - 1
    have htlo : θ 0 ≤ θ t := hθm.monotone (unitInterval.nonneg t)
    have hthi : θ t ≤ θ 1 := hθm.monotone (unitInterval.le_one t)
    have hst : s * 2 = θ 1 - θ 0 := by dsimp only [s]; ring
    have hx : x ∈ Icc (-1 : ℝ) 1 := by
      dsimp only [x]
      constructor
      · have hdiv := div_nonneg (sub_nonneg.mpr htlo) hs.le
        linarith
      · have hdiv : (θ t - θ 0) / s ≤ 2 := (div_le_iff₀ hs).mpr (by linarith)
        linarith
    have hAx : A (x : ℂ) = (θ t : ℂ) := by
      have hreal : θ 0 + s * (x + 1) = θ t := by
        dsimp only [x]
        field_simp
        ring
      dsimp only [A]
      exact_mod_cast hreal
    exact ⟨x, hx, hsegD ⟨x, hx, rfl⟩, (congrArg K hAx).trans (hθK t).2⟩
  have hbd_ends : ({a 0, a 1} : Set S₀) ⊆ discBd (f '' D) := by
    rw [himage.2]
    intro w hw
    rcases hw with rfl | hw
    · exact ⟨-1, hends (by simp), hfleft⟩
    · have hw1 := Set.mem_singleton_iff.mp hw
      subst w
      exact ⟨1, hends (by simp), hfright⟩
  refine ⟨f '' D, himage.1, ?_, hbd_ends, ?_, ?_⟩
  · apply Set.Subset.antisymm
    · rintro w ⟨⟨z, hzD, rfl⟩, hzB⟩
      have hzends : z ∈ ({-1, 1} : Set ℂ) := hDB.subset ⟨hzD, hmem z hzD hzB⟩
      rcases hzends with rfl | hzends
      · exact Or.inl hfleft
      · have hz1 := Set.mem_singleton_iff.mp hzends
        subst z
        exact Or.inr (Set.mem_singleton_iff.mpr hfright)
    · intro w hw
      rcases hw with rfl | hw
      · exact ⟨⟨-1, Surface.discBd_subset D (hends (by simp)), hfleft⟩, hleft⟩
      · have hw1 := Set.mem_singleton_iff.mp hw
        subst w
        exact ⟨⟨1, Surface.discBd_subset D (hends (by simp)), hfright⟩, hright⟩
  · rintro _ ⟨t, rfl⟩
    obtain ⟨x, _, hxD, hfx⟩ := hseg_pt t
    exact ⟨(x : ℂ), hxD, hfx⟩
  · apply Set.Subset.antisymm
    · rw [himage.2]
      rintro w ⟨⟨z, hz_bd, rfl⟩, ⟨t, hat⟩⟩
      obtain ⟨x, hx, hxD, hfx⟩ := hseg_pt t
      have hzD : z ∈ D := Surface.discBd_subset D hz_bd
      have hzx : z = (x : ℂ) := hfi (hDO hzD) (hDO hxD) (hat.symm.trans hfx.symm)
      have hz_mem : z ∈ discBd D ∩ (Complex.ofReal '' Icc (-1 : ℝ) 1) :=
        ⟨hz_bd, x, hx, hzx.symm⟩
      rw [hbd_seg] at hz_mem
      rcases hz_mem with rfl | hz1
      · exact Or.inl hfleft
      · have hz1' := Set.mem_singleton_iff.mp hz1
        rw [hz1']
        exact Or.inr (Set.mem_singleton_iff.mpr hfright)
    · refine subset_inter hbd_ends ?_
      rintro w (rfl | hw)
      · exact ⟨0, rfl⟩
      · exact (Set.mem_singleton_iff.mp hw) ▸ ⟨1, rfl⟩

/-- Refinement of `GM12.exists_normal_arc_disc` recording `discBd D ∩ range a = {a 0, a 1}`. -/
theorem exists_normal_arc_disc_interior
    {S₀ : Type*} [TopologicalSpace S₀] [T2Space S₀] [ConnectedSpace S₀]
    (hS : IsClosedSurface S₀) {a : unitInterval → S₀} (ha : IsArcMap a)
    {B : Set S₀} (hB : IsClosed B) (hleft : a 0 ∈ B) (hright : a 1 ∈ B)
    (hmeet : range a ∩ B ⊆ {a 0, a 1}) :
    ∃ D : Set S₀, IsClosedDisc D ∧ D ∩ B = {a 0, a 1} ∧
      ({a 0, a 1} : Set S₀) ⊆ discBd D ∧ range a ⊆ D ∧
      discBd D ∩ range a = {a 0, a 1} := by
  let : CompactSpace S₀ := hS.1
  have hsurf : IsSurface S₀ := ⟨hS.1, hS.2.1, fun x => (hS.2.2 x).isManifoldPoint⟩
  obtain ⟨n, m, c, ⟨e⟩⟩ := classification S₀ hsurf inferInstance
  let : T2Space (SurfaceModel n m c) := e.t2Space
  have hM : IsClosedSurface (SurfaceModel n m c) := by
    refine ⟨e.compactSpace, e.t2Space, ?_⟩
    intro x
    have hx := (isInteriorPoint_homeomorph_iff e (e.symm x)).mpr (hS.2.2 (e.symm x))
    simpa only [e.apply_symm_apply] using hx
  let a' : unitInterval → SurfaceModel n m c := fun t => e (a t)
  let B' : Set (SurfaceModel n m c) := e.symm ⁻¹' B
  have ha' : IsArcMap a' := ⟨e.continuous.comp ha.1, e.injective.comp ha.2⟩
  have hB' : IsClosed B' := hB.preimage e.symm.continuous
  have hleft' : a' 0 ∈ B' := by simpa only [a', B', mem_preimage, e.symm_apply_apply] using hleft
  have hright' : a' 1 ∈ B' := by simpa only [a', B', mem_preimage, e.symm_apply_apply] using hright
  have hmeet' : range a' ∩ B' ⊆ {a' 0, a' 1} := by
    rintro _ ⟨⟨t, rfl⟩, ht⟩
    have htB : a t ∈ B := by simpa only [a', B', mem_preimage, e.symm_apply_apply] using ht
    rcases hmeet ⟨mem_range_self t, htB⟩ with h | h
    · exact Or.inl (congrArg e h)
    · exact Or.inr (Set.mem_singleton_iff.mpr (congrArg e (Set.mem_singleton_iff.mp h)))
  have hman : ∀ x : SurfaceModel n m c, IsManifoldPoint x :=
    fun x => (hM.2.2 x).isManifoldPoint
  obtain ⟨E, hE, haE⟩ := Surface.exists_disc_of_arc hM ha'
  obtain ⟨h, g, ch⟩ := hE.exists_isChart
  have hbc : BallChart 1 (g '' ball 0 1) h g := by
    refine ⟨ch.isOpen_image_ball hman, ch.hc.mono ?_, ch.gc.mono ball_subset_closedBall,
      ?_, ?_, ?_, ?_⟩
    · rintro _ ⟨z, hz, rfl⟩
      exact ch.gm (ball_subset_closedBall hz)
    · rintro _ ⟨z, hz, rfl⟩
      rwa [ch.hg (ball_subset_closedBall hz)]
    · exact fun z hz => ⟨z, hz, rfl⟩
    · rintro _ ⟨z, hz, rfl⟩
      rw [ch.hg (ball_subset_closedBall hz)]
    · exact fun z hz => ch.hg (ball_subset_closedBall hz)
  have haU : range a' ⊆ g '' ball 0 1 := by
    rw [← ch.discInt_eq]
    exact haE
  obtain ⟨O, K, θ, hO, hKc, hKi, _, hθc, hθm, hθK⟩ :=
    GM12.exists_straight_arc_chart hman hbc ha' haU
  obtain ⟨D, hD, hDB, hends, haD, hbd_range⟩ :=
    exists_thin_disc_of_strip_arc_interior hO hKc hKi ha' hθc hθm hθK hB' hleft' hright' hmeet'
  let : Nonempty (SurfaceModel n m c) := ⟨a' 0⟩
  have himage := Surface.isClosedDisc_image_injOn hD hD.isCompact e.symm.continuous.continuousOn
    e.symm.injective.injOn
  have hbd_ends : ({a 0, a 1} : Set S₀) ⊆ discBd (e.symm '' D) := by
    rw [himage.2]
    intro x hx
    rcases hx with rfl | hx
    · exact ⟨a' 0, hends (by simp), e.symm_apply_apply (a 0)⟩
    · have hx1 := Set.mem_singleton_iff.mp hx
      subst x
      exact ⟨a' 1, hends (by simp), e.symm_apply_apply (a 1)⟩
  refine ⟨e.symm '' D, himage.1, ?_, hbd_ends, ?_, ?_⟩
  · apply Set.Subset.antisymm
    · rintro _ ⟨⟨x, hx, rfl⟩, hxB⟩
      have hxends : x ∈ ({a' 0, a' 1} : Set (SurfaceModel n m c)) := hDB.subset ⟨hx, hxB⟩
      rcases hxends with rfl | hxends
      · exact Or.inl (e.symm_apply_apply (a 0))
      · have hx1 := Set.mem_singleton_iff.mp hxends
        subst x
        exact Or.inr (Set.mem_singleton_iff.mpr (e.symm_apply_apply (a 1)))
    · intro x hx
      rcases hx with rfl | hx
      · exact ⟨⟨a' 0, Surface.discBd_subset D (hends (by simp)), e.symm_apply_apply (a 0)⟩, hleft⟩
      · have hx1 := Set.mem_singleton_iff.mp hx
        subst x
        exact ⟨⟨a' 1, Surface.discBd_subset D (hends (by simp)), e.symm_apply_apply (a 1)⟩, hright⟩
  · rintro _ ⟨t, rfl⟩
    exact ⟨a' t, haD (mem_range_self t), e.symm_apply_apply (a t)⟩
  · apply Set.Subset.antisymm
    · rw [himage.2]
      rintro _ ⟨⟨x, hx_bd, rfl⟩, ⟨t, hat⟩⟩
      have hxa' : x = a' t := e.symm.injective (hat.symm.trans (e.symm_apply_apply (a t)).symm)
      have hx_mem : x ∈ discBd D ∩ range a' := ⟨hx_bd, t, hxa'.symm⟩
      rw [hbd_range] at hx_mem
      rcases hx_mem with rfl | hx1
      · exact Or.inl (e.symm_apply_apply (a 0))
      · have hx1' := Set.mem_singleton_iff.mp hx1
        rw [hx1']
        exact Or.inr (Set.mem_singleton_iff.mpr (e.symm_apply_apply (a 1)))
    · refine subset_inter hbd_ends ?_
      rintro w (rfl | hw)
      · exact ⟨0, rfl⟩
      · exact (Set.mem_singleton_iff.mp hw) ▸ ⟨1, rfl⟩

/-- A finite family of arcs in a closed connected surface whose pairwise intersections lie in their
shared endpoints can be thickened into thin closed discs `Q i` meeting a forbidden closed set `B`
only at `{a i 0, a i 1}`, with `discBd (Q i) ∩ range (a i) = {a i 0, a i 1}` and
`Q i ∩ Q j = {a i 0, a i 1} ∩ {a j 0, a j 1}` for `i ≠ j`. -/
theorem exists_shared_endpoint_arc_discs
    {S₀ ι : Type*} [TopologicalSpace S₀] [T2Space S₀] [ConnectedSpace S₀]
    (hS₀ : IsClosedSurface S₀) {F : Set ι} (hF : F.Finite) (a : ι → unitInterval → S₀)
    (hArc : ∀ i ∈ F, IsArcMap (a i))
    (hinter : ∀ i ∈ F, ∀ j ∈ F, i ≠ j →
      range (a i) ∩ range (a j) ⊆ ({a i 0, a i 1} : Set S₀) ∩ {a j 0, a j 1}) :
    ∀ B : Set S₀, IsClosed B → (∀ i ∈ F, range (a i) ∩ B = {a i 0, a i 1}) →
    ∃ Q : ι → Set S₀,
      (∀ i ∈ F, IsClosedDisc (Q i) ∧ Q i ∩ B = {a i 0, a i 1} ∧
        ({a i 0, a i 1} : Set S₀) ⊆ discBd (Q i) ∧ range (a i) ⊆ Q i ∧
        discBd (Q i) ∩ range (a i) = {a i 0, a i 1}) ∧
      (∀ i ∈ F, ∀ j ∈ F, i ≠ j → Q i ∩ Q j = ({a i 0, a i 1} : Set S₀) ∩ {a j 0, a j 1}) := by
  classical
  revert hArc hinter
  induction F, hF using Set.Finite.induction_on with
  | empty =>
    intro _ _ B _ _
    exact ⟨fun _ => ∅, by simp, by simp⟩
  | @insert i F hi hF ih =>
    intro hArc hinter B hB hcontact
    have hArcF := fun j hj => hArc j (Or.inr hj)
    have hinterF := fun j hj k hk hjk => hinter j (Or.inr hj) k (Or.inr hk) hjk
    have hAi : IsClosed (range (a i)) := (isCompact_range (hArc i (Or.inl rfl)).1).isClosed
    let B' : Set S₀ := B ∪ range (a i)
    have hcontact' : ∀ j ∈ F, range (a j) ∩ B' = {a j 0, a j 1} := by
      intro j hj
      have hji : j ≠ i := fun h => hi (h ▸ hj)
      change range (a j) ∩ (B ∪ range (a i)) = _
      rw [inter_union_distrib_left, hcontact j (Or.inr hj)]
      apply Subset.antisymm
      · rintro z (hz | hz)
        · exact hz
        · exact (hinter j (Or.inr hj) i (Or.inl rfl) hji hz).1
      · exact subset_union_left
    obtain ⟨Q, hQ, hQQ⟩ := ih hArcF hinterF B' (hB.union hAi) hcontact'
    have hendsB : ∀ j ∈ insert i F, ({a j 0, a j 1} : Set S₀) ⊆ B := by
      intro j hj z hz
      exact ((hcontact j hj).symm.subset hz).2
    have hendsRange : ∀ j, ({a j 0, a j 1} : Set S₀) ⊆ range (a j) := by
      rintro j z (rfl | hz)
      · exact mem_range_self 0
      · exact (Set.mem_singleton_iff.mp hz) ▸ mem_range_self 1
    have hQ_range : ∀ j ∈ F, Q j ∩ range (a i) ⊆ ({a i 0, a i 1} : Set S₀) ∩ {a j 0, a j 1} := by
      intro j hj z ⟨hzQ, hzAi⟩
      have hji : j ≠ i := fun h => hi (h ▸ hj)
      have hzends : z ∈ ({a j 0, a j 1} : Set S₀) := (hQ j hj).2.1.subset ⟨hzQ, Or.inr hzAi⟩
      exact hinter i (Or.inl rfl) j (Or.inr hj) hji.symm ⟨hzAi, hendsRange j hzends⟩
    let Z : Set S₀ := B ∪ ⋃ j ∈ F, Q j
    have hZ : IsClosed Z := hB.union (hF.isClosed_biUnion fun j hj => (hQ j hj).1.isClosed)
    have hmeet : range (a i) ∩ Z ⊆ {a i 0, a i 1} := by
      rintro z ⟨hzA, hzZ⟩
      rcases hzZ with hzB | hzQ
      · exact (hcontact i (Or.inl rfl)).subset ⟨hzA, hzB⟩
      · obtain ⟨j, hj, hzQj⟩ := mem_iUnion₂.mp hzQ
        exact (hQ_range j hj ⟨hzQj, hzA⟩).1
    obtain ⟨Qi, hQi, hQiZ, hQibd, haQi, hQibd_range⟩ :=
      exists_normal_arc_disc_interior hS₀ (hArc i (Or.inl rfl)) hZ
        (Or.inl (hendsB i (Or.inl rfl) (by simp)))
        (Or.inl (hendsB i (Or.inl rfl) (by simp))) hmeet
    have hQiB : Qi ∩ B = {a i 0, a i 1} := by
      apply Subset.antisymm
      · exact fun z hz => hQiZ.subset ⟨hz.1, Or.inl hz.2⟩
      · intro z hz
        exact ⟨Surface.discBd_subset Qi (hQibd hz), hendsB i (Or.inl rfl) hz⟩
    have hQB : ∀ j ∈ F, Q j ∩ B = {a j 0, a j 1} := by
      intro j hj
      apply Subset.antisymm
      · exact fun z hz => (hQ j hj).2.1.subset ⟨hz.1, Or.inl hz.2⟩
      · intro z hz
        exact ⟨Surface.discBd_subset (Q j) ((hQ j hj).2.2.1 hz), hendsB j (Or.inr hj) hz⟩
    have hQiQ : ∀ j ∈ F, Qi ∩ Q j = ({a i 0, a i 1} : Set S₀) ∩ {a j 0, a j 1} := by
      intro j hj
      apply Subset.antisymm
      · rintro z ⟨hzQi, hzQj⟩
        have hzends : z ∈ ({a i 0, a i 1} : Set S₀) :=
          hQiZ.subset ⟨hzQi, Or.inr (mem_iUnion₂.mpr ⟨j, hj, hzQj⟩)⟩
        exact hQ_range j hj ⟨hzQj, hendsRange i hzends⟩
      · rintro z ⟨hzi, hzj⟩
        exact ⟨haQi (hendsRange i hzi), (hQ j hj).2.2.2.1 (hendsRange j hzj)⟩
    let Q' : ι → Set S₀ := fun j => if j = i then Qi else Q j
    refine ⟨Q', ?_, ?_⟩
    · intro j hj
      rcases hj with rfl | hj
      · simpa only [Q', ↓reduceIte] using
          (show IsClosedDisc Qi ∧ Qi ∩ B = {a j 0, a j 1} ∧
            ({a j 0, a j 1} : Set S₀) ⊆ discBd Qi ∧ range (a j) ⊆ Qi ∧
            discBd Qi ∩ range (a j) = {a j 0, a j 1} from
              ⟨hQi, hQiB, hQibd, haQi, hQibd_range⟩)
      · have hji : j ≠ i := fun h => hi (h ▸ hj)
        simpa only [Q', hji, ↓reduceIte] using
          (show IsClosedDisc (Q j) ∧ Q j ∩ B = {a j 0, a j 1} ∧
            ({a j 0, a j 1} : Set S₀) ⊆ discBd (Q j) ∧ range (a j) ⊆ Q j ∧
            discBd (Q j) ∩ range (a j) = {a j 0, a j 1} from
              ⟨(hQ j hj).1, hQB j hj, (hQ j hj).2.2⟩)
    · intro j hj k hk hjk
      by_cases hji : j = i
      · subst j
        have hki : k ≠ i := Ne.symm hjk
        simpa only [Q', ↓reduceIte, hki] using hQiQ k (hk.resolve_left hki)
      · have hjF : j ∈ F := hj.resolve_left hji
        by_cases hki : k = i
        · subst k
          simpa only [Q', hji, ↓reduceIte] using
            (Set.inter_comm Qi (Q j)).symm.trans
              ((hQiQ j hjF).trans (Set.inter_comm ({a i 0, a i 1} : Set S₀) {a j 0, a j 1}))
        · have hkF : k ∈ F := hk.resolve_left hki
          simpa only [Q', hji, hki, ↓reduceIte] using hQQ j hjF k hkF hjk

/-! ## 3. Single-Edge Piece Discs for Remaining Drawing Edges -/

omit [T2Space S] in
/-- If `ιV₁` and `ιV₂` agree on `H.V`, then `H.toEmbeddedGraph ιV₁ ιE = H.toEmbeddedGraph ιV₂ ιE`. -/
theorem toEmbeddedGraph_congr_of_eq_on_V
    {H : Drawing S} {ιV₁ ιV₂ : S ↪ α} {ιE : Set S ↪ β}
    (heq : ∀ s ∈ H.V, ιV₁ s = ιV₂ s) :
    H.toEmbeddedGraph ιV₁ ιE = H.toEmbeddedGraph ιV₂ ιE := by
  ext x y
  · simp only [Drawing.toEmbeddedGraph, mem_image]
    exact ⟨fun ⟨s, hs, hx⟩ => ⟨s, hs, hx ▸ (heq s hs).symm⟩,
      fun ⟨s, hs, hx⟩ => ⟨s, hs, hx ▸ heq s hs⟩⟩
  · simp only [Drawing.toEmbeddedGraph]
    constructor <;> rintro ⟨e₀, x₀, y₀, hlk, rfl, rfl, rfl⟩
    · rw [heq x₀ hlk.left_mem, heq y₀ hlk.right_mem]
      exact ⟨e₀, x₀, y₀, hlk, rfl, rfl, rfl⟩
    · rw [← heq x₀ hlk.left_mem, ← heq y₀ hlk.right_mem]
      exact ⟨e₀, x₀, y₀, hlk, rfl, rfl, rfl⟩

/-- No edge of a simple walk is a loop. -/
theorem not_isLink_self_of_mem_edges_isSimple
    {P : Graph α β} {a b : α} (W : GraphWalk P a b)
    (hW : W.IsSimple) {e : β} (he : e ∈ W.edges) (u : α) :
    ¬ P.IsLink e u u := by
  induction W with
  | nil _ => simp [GraphWalk.edges] at he
  | @cons x y z g hlink rest ih =>
    have hs : rest.IsSimple := (List.nodup_cons.mp hW).2
    have hnd : x ∉ rest.support := (List.nodup_cons.mp hW).1
    simp only [GraphWalk.edges, List.mem_cons] at he
    rcases he with rfl | he
    · intro hloop
      rcases P.eq_or_eq_of_isLink_of_isLink hlink hloop with rfl | rfl <;>
        rcases P.eq_or_eq_of_isLink_of_isLink hlink.symm hloop with h | h <;>
        exact hnd (h ▸ rest.start_mem_support)
    · exact ih hs he

omit [T2Space S] in
/-- In a drawing `Γ` whose graph `Γ.toGraph` is a subdivision of a simple 3-connected graph, every
edge `e ∈ Γ.E` has two distinct endpoints `u ≠ v` in `Γ.V` with `closure e ∩ Γ.V = {u, v}` and
`IsLineWithEnds (closure e) u v`. -/
theorem line_ends_of_edge_8_3
    {Γ : Drawing S} (hSub : IsSubdivisionOfSimpleThreeConnected Γ.toGraph)
    {e : Set S} (he : e ∈ Γ.E) :
    ∃ u v : S, u ≠ v ∧ u ∈ Γ.V ∧ v ∈ Γ.V ∧
      Γ.toGraph.IsLink e u v ∧ closure e ∩ Γ.V = {u, v} ∧
      IsLineWithEnds (closure e) u v := by
  obtain ⟨G₀, P, hSD⟩ := Whitney.exists_subData hSub
  have he_mem : e ∈ E(Γ.toGraph) := he
  rw [hSD.eunion] at he_mem
  obtain ⟨g, hg, he_Pg⟩ := mem_iUnion₂.mp he_mem
  obtain ⟨x₀, y₀, _, ⟨hle, W, hs, _, hE⟩, _, _⟩ := hSD.path g hg
  have he_W : e ∈ W.edges := by rwa [hE] at he_Pg
  rcases Γ.edge_cond e he with ⟨u, v, huv, hcap, hL⟩ | ⟨u, hcap, _⟩
  · have hu : u ∈ Γ.V := by
      have : u ∈ closure e ∩ Γ.V := by rw [hcap]; exact Or.inl rfl
      exact this.2
    have hv : v ∈ Γ.V := by
      have : v ∈ closure e ∩ Γ.V := by rw [hcap]; exact Or.inr rfl
      exact this.2
    exact ⟨u, v, huv, hu, hv, ⟨he, hu, hv, hcap⟩, hcap, hL⟩
  · exfalso
    have hu : u ∈ Γ.V := by
      have : u ∈ closure e ∩ Γ.V := by rw [hcap]; exact mem_singleton u
      exact this.2
    have hlk_Γ : Γ.toGraph.IsLink e u u :=
      ⟨he, hu, hu, by rw [Set.pair_eq_singleton, hcap]⟩
    have hlk_Pg : (P g).IsLink e u u := (hle.isLink_iff he_Pg).mpr hlk_Γ
    exact not_isLink_self_of_mem_edges_isSimple W hs he_W u hlk_Pg

/-- Any closed disc `D_e ⊆ Δ₀` whose boundary is `Γ`-normal and meets `Γ.V` in at most 3 vertices
satisfies `IsTangleIns Γ T (subBd D_e) D_e` and is the unique such disc. -/
theorem isTangleIns_of_disc_in_Δ₀_8_3
    {q δ h θ : ℕ}
    {ιV : S ↪ α} {ιE : Set S ↪ β}
    {R_G : RootedDigraph α β q} {W : Set α}
    {Γ C₀ : Drawing S} {r₀ : Set S} {orient : GM19.SurfaceOrientation S}
    {PiSet : Set S}
    {ord : ℕ} {T : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    {d : Set S → Set S → ℕ}
    {J : Graph α β} {Z : Set α} {𝒜 : Set (Graph α β)}
    {πLen : Graph α β → ℕ} {πA : ∀ A : Graph α β, Fin (πLen A) → α}
    {vA : Graph α β → S} {D_disc : Set S} {v_star : S}
    (h83 : Hypotheses83 q δ h θ ιV ιE R_G W Γ C₀ r₀ orient PiSet ord T d J Z 𝒜
      πLen πA vA D_disc v_star)
    (hord : 4 ≤ ord)
    {Δ₀ : Set S} (hΔ₀ : IsClosedDisc Δ₀) (hbd_Δ₀ : subBd Δ₀ ∩ Γ.U = PiSet)
    {D_e : Set S} (hDe_disc : IsClosedDisc D_e) (hDe_sub : D_e ⊆ Δ₀)
    (hDe_norm : subBd D_e ∩ Γ.U ⊆ Γ.V) (hDe_card : (subBd D_e ∩ Γ.V).ncard ≤ 3) :
    IsTangleIns Γ T (subBd D_e) D_e ∧
    ∀ Δ : Set S, IsTangleIns Γ T (subBd D_e) Δ → Δ = D_e := by
  obtain ⟨hS_closed, _⟩ := GM11.IsSphere.isClosedSurface h83.hyp_i.1
  let F : Set S := subBd D_e
  have hF_eq_discBd : F = discBd D_e :=
    GM14.IsClosedDisc.subBd_eq_discBd hS_closed hDe_disc
  have hF_oarc : IsOArc F := hF_eq_discBd ▸ hDe_disc.isOArc_discBd
  have hF_sub_Δ₀ : F ⊆ Δ₀ :=
    (GM14.Whitney.subBd_subset_of subset_rfl hDe_disc.isClosed).trans hDe_sub
  have hFV_lt_ord : (F ∩ Γ.V).ncard < ord := lt_of_le_of_lt hDe_card (by omega)
  obtain ⟨Δ₁, Δ₂, _, _, _, _, _, _, _, _, hcap, _, hcl21, _, hbd₀_Δ₂, h_either, h_uniq₁⟩ :=
    sphere_oArc_discs_in_Δ₀ h83.hyp_i.1 hΔ₀ hF_sub_Δ₀ hF_oarc
  have hΔ₁_eq : Δ₁ = D_e := (h_uniq₁ D_e hDe_sub hDe_disc rfl).symm
  subst hΔ₁_eq
  have h_not_ins₂ : ¬ IsTangleIns Γ T F Δ₂ := by
    rintro ⟨_, _, hmem_T⟩
    let A_hyp := (PaintingOrDrawing.drawing Γ).inter Δ₂
    let B_hyp := (PaintingOrDrawing.drawing Γ).interOutside Δ₂
    have hA_V : A_hyp.vertexSet = Γ.V ∩ Δ₂ := rfl
    have hB_V : B_hyp.vertexSet = Γ.V ∩ closure (univ \ Δ₂) := rfl
    have hinter_V : A_hyp.vertexSet ∩ B_hyp.vertexSet = F ∩ Γ.V := by
      rw [hA_V, hB_V, hcl21]
      ext v
      simp only [mem_inter_iff]
      have hcap' : Δ₁ ∩ Δ₂ = F := hcap
      constructor
      · rintro ⟨⟨hvV, hv₂⟩, ⟨_, hv₁⟩⟩
        exact ⟨hcap' ▸ ⟨hv₁, hv₂⟩, hvV⟩
      · rintro ⟨hvF, hvV⟩
        have hv₁₂ : v ∈ Δ₁ ∩ Δ₂ := hcap'.symm ▸ hvF
        exact ⟨⟨hvV, hv₁₂.2⟩, ⟨hvV, hv₁₂.1⟩⟩
    have hord_AB : separationOrder A_hyp B_hyp ≤ 3 := by
      change (A_hyp.vertexSet ∩ B_hyp.vertexSet).ncard ≤ 3
      rw [hinter_V]
      exact hDe_card
    have hPi_sub_A : PiSet ⊆ A_hyp.vertexSet := by
      intro p hp
      have hpV : p ∈ Γ.V := h83.hyp_ii.1.1 (h83.hyp_iii.1 hp)
      have hp_bd₀ : p ∈ subBd Δ₀ := (hbd_Δ₀.symm ▸ hp).1
      exact ⟨hpV, hbd₀_Δ₂ hp_bd₀⟩
    exact h83.hyp_iv.2.2 A_hyp B_hyp hmem_T hord_AB hPi_sub_A
  obtain ⟨Δ_ins, hΔ_ins⟩ := h83.hyp_iv.2.1.1.2.2.2 F hF_oarc hDe_norm hFV_lt_ord
  have h_uniq_all : ∀ Δ : Set S, IsTangleIns Γ T F Δ → Δ = Δ₁ := by
    intro Δ hΔ
    rcases h_either Δ hΔ.1 hΔ.2.1 with h1 | h2
    · exact h1
    · exact False.elim (h_not_ins₂ (h2 ▸ hΔ))
  have hDe_ins : IsTangleIns Γ T F Δ₁ := h_uniq_all Δ_ins hΔ_ins ▸ hΔ_ins
  exact ⟨hDe_ins, h_uniq_all⟩

/-- Construction of thin closed discs `Q e ⊆ Δ₀` around the remaining edges
`e ∈ E_rem := {e ∈ Γ.E | ∀ A ∈ 𝒜', ιE e ∉ E(A)}`. -/
theorem exists_edge_rem_discs_8_3
    {q δ h θ : ℕ}
    {ιV : S ↪ α} {ιE : Set S ↪ β}
    {R_G : RootedDigraph α β q} {W : Set α}
    {Γ C₀ : Drawing S} {r₀ : Set S} {orient : GM19.SurfaceOrientation S}
    {PiSet : Set S}
    {ord : ℕ} {T : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    {d : Set S → Set S → ℕ}
    {J : Graph α β} {Z : Set α} {𝒜 : Set (Graph α β)}
    {πLen : Graph α β → ℕ} {πA : ∀ A : Graph α β, Fin (πLen A) → α}
    {vA : Graph α β → S} {D_disc : Set S} {v_star : S}
    (h83 : Hypotheses83 q δ h θ ιV ιE R_G W Γ C₀ r₀ orient PiSet ord T d J Z 𝒜
      πLen πA vA D_disc v_star)
    {Δ₀ : Set S} (hΔ₀ : IsClosedDisc Δ₀) (hΓ_Δ₀ : Γ.U ⊆ Δ₀)
    (hbd_Δ₀ : subBd Δ₀ ∩ Γ.U = PiSet)
    {α_map : α → S} {D₀ : Graph α β → Set S}
    (hα_ΓV : ∀ v ∈ Γ.V, ιV v ∈ Z → α_map (ιV v) = v)
    (hα_ΓU : ∀ v ∈ Z, α_map v ∈ Γ.U ↔ v ∈ ιV '' Γ.V)
    (hD₀ : ∀ A ∈ 𝒜, IsClosedDisc (D₀ A) ∧ D₀ A ⊆ Δ₀)
    (hD₀_norm : ∀ A ∈ 𝒜, subBd (D₀ A) ∩ Γ.U ⊆ Γ.V)
    (hα_bdA : ∀ A ∈ 𝒜, ∀ v ∈ Set.range (πA A), α_map v ∈ subBd (D₀ A))
    (hD₀_props : ∀ A ∈ 𝒜,
      subBd (D₀ A) ∩ Γ.U = {v ∈ Γ.V | ιV v ∈ Set.range (πA A)} ∧
      subBd (D₀ A) ∩ Γ.V = {v ∈ Γ.V | ιV v ∈ Set.range (πA A)} ∧
      (Γ.interSet (D₀ A)).V = {v ∈ Γ.V | ιV v ∈ V(A)} ∧
      (Γ.interSet (D₀ A)).E = {e ∈ Γ.E | ιE e ∈ E(A)} ∧
      (Γ.interSet (D₀ A)).toEmbeddedGraph ιV ιE = (Γ.toEmbeddedGraph ιV ιE) ⊓ A) :
    let 𝒜' := {A ∈ 𝒜 | 5 ≤ subsetTangleDist Γ ord d {vA A} C₀.V}
    let E_rem := {e ∈ Γ.E | ∀ A ∈ 𝒜', ιE e ∉ E(A)}
    ∃ (u_end v_end : Set S → S) (Q : Set S → Set S),
      (∀ e ∈ E_rem,
        u_end e ≠ v_end e ∧ u_end e ∈ Γ.V ∧ v_end e ∈ Γ.V ∧
        Γ.toGraph.IsLink e (u_end e) (v_end e) ∧
        closure e ∩ Γ.V = {u_end e, v_end e} ∧
        (∃ A₀ ∈ 𝒜 \ 𝒜', ιE e ∈ E(A₀) ∧
          ιV (u_end e) ∈ V(A₀) \ W ∧ ιV (v_end e) ∈ V(A₀) \ W ∧ u_end e ∈ D₀ A₀) ∧
        IsClosedDisc (Q e) ∧ Q e ⊆ Δ₀ ∧
        subBd (Q e) ∩ Γ.U = {u_end e, v_end e} ∧
        subBd (Q e) ∩ Γ.V = {u_end e, v_end e} ∧
        Q e ∩ (Γ.V ∪ (α_map '' Z)) = {u_end e, v_end e} ∧
        subBd (Q e) ∩ (Γ.V ∪ (α_map '' Z)) = {u_end e, v_end e} ∧
        (Γ.interSet (Q e)).V = {u_end e, v_end e} ∧
        (Γ.interSet (Q e)).E = {e} ∧
        (∀ A ∈ 𝒜', Q e ∩ D₀ A = {u_end e, v_end e} ∩ (α_map '' Set.range (πA A)))) ∧
      (∀ e₁ ∈ E_rem, ∀ e₂ ∈ E_rem, e₁ ≠ e₂ →
        Q e₁ ∩ Q e₂ = {u_end e₁, v_end e₁} ∩ {u_end e₂, v_end e₂}) := by
  intro 𝒜' E_rem
  obtain ⟨hS, hConn⟩ := GM11.IsSphere.isClosedSurface h83.hyp_i.1
  let : ConnectedSpace S := hConn
  have hE_rem_fin : E_rem.Finite := Γ.finite_edges.subset (fun _ he => he.1)
  have h_ends : ∀ e : Set S, ∃ u v : S, ∃ a : unitInterval → S,
      e ∈ E_rem → u ≠ v ∧ u ∈ Γ.V ∧ v ∈ Γ.V ∧
        Γ.toGraph.IsLink e u v ∧ closure e ∩ Γ.V = {u, v} ∧
        IsArcMap a ∧ range a = closure e ∧ a 0 = u ∧ a 1 = v := by
    intro e
    by_cases he : e ∈ E_rem
    · obtain ⟨u, v, huv, huV, hvV, hlk, hcap, ⟨f, hf0, hf1⟩⟩ :=
        line_ends_of_edge_8_3 h83.hyp_i.2 he.1
      let a : unitInterval → S := fun t => (f t).1
      have ha : IsArcMap a :=
        ⟨continuous_subtype_val.comp f.continuous, Subtype.val_injective.comp f.injective⟩
      have hrange : range a = closure e := by
        ext x
        exact ⟨fun ⟨t, ht⟩ => ht ▸ (f t).2, fun hx => ⟨f.symm ⟨x, hx⟩, by simp [a]⟩⟩
      exact ⟨u, v, a, fun _ => ⟨huv, huV, hvV, hlk, hcap, ha, hrange, hf0, hf1⟩⟩
    · exact ⟨v_star, v_star, fun _ => v_star, fun h => False.elim (he h)⟩
  choose u_end v_end a_arc ha_spec using h_ends
  -- Every `e ∈ E_rem` belongs to some `A₀ ∈ 𝒜 \ 𝒜'`.
  have hZdiv : IsZDivision J (Z ∪ W) 𝒜 := h83.hyp_vi.2.2.1
  have hΓ_le_J := Γ_le_J_8_3 h83
  have he_in_A₀ : ∀ e ∈ E_rem, ∃ A₀ ∈ 𝒜 \ 𝒜',
      ιE e ∈ E(A₀) ∧ ιV (u_end e) ∈ V(A₀) \ W ∧ ιV (v_end e) ∈ V(A₀) \ W ∧
      u_end e ∈ D₀ A₀ := by
    intro e he
    obtain ⟨_, huV, hvV, hlk_Γ, _, _, _, _, _⟩ := ha_spec e he
    have hlk_del : (J.deleteVerts W).IsLink (ιE e) (ιV (u_end e)) (ιV (v_end e)) :=
      hΓ_le_J.1.2 ⟨e, u_end e, v_end e, hlk_Γ, rfl, rfl, rfl⟩
    rw [Graph.deleteVerts_isLink] at hlk_del
    obtain ⟨hlk_J, hu_not_W, hv_not_W⟩ := hlk_del
    have he_J : ιE e ∈ E(J) := hlk_J.edge_mem
    have hEJ : E(J) = ⋃ A ∈ 𝒜, E(A) := by
      have := congrArg Graph.edgeSet hZdiv.2.2.1.symm
      rwa [edgeSet_subgraphSUnion hZdiv.2.1] at this
    rw [hEJ] at he_J
    obtain ⟨A₀, hA₀, he_A₀⟩ := mem_iUnion₂.mp he_J
    have hA₀_not' : A₀ ∉ 𝒜' := fun hA₀' => he.2 A₀ hA₀' he_A₀
    have hlk_A₀ : A₀.IsLink (ιE e) (ιV (u_end e)) (ιV (v_end e)) :=
      ((hZdiv.2.1 A₀ hA₀).isLink_iff he_A₀).mpr hlk_J
    have hu_interV : u_end e ∈ (Γ.interSet (D₀ A₀)).V := by
      rw [(hD₀_props A₀ hA₀).2.2.1]
      exact ⟨huV, hlk_A₀.left_mem⟩
    have hu_D₀ : u_end e ∈ D₀ A₀ := by
      obtain ⟨hV_eq, _⟩ := interSet_V_and_U (hD₀ A₀ hA₀).1.isClosed (hD₀_norm A₀ hA₀)
      exact (hV_eq ▸ hu_interV).2
    exact ⟨A₀, ⟨hA₀, hA₀_not'⟩, he_A₀, ⟨hlk_A₀.left_mem, hu_not_W⟩,
      ⟨hlk_A₀.right_mem, hv_not_W⟩, hu_D₀⟩
  -- Fininiteness of `𝒜` and `Z` for closedness of the forbidden set `B_forbid`.
  have hfin_𝒜 : 𝒜.Finite := hZdiv.1
  have hfin_𝒜' : 𝒜'.Finite := hfin_𝒜.subset fun _ hA => hA.1
  have hfin_Z : Z.Finite :=
    h83.finite_V.subset (h83.hyp_vi.1.trans (sdiff_subset.trans h83.hyp_v.1.vertexSet_mono))
  -- Forbidden closed set `B_forbid`.
  let B_forbid : Set S :=
    Γ.V ∪ (α_map '' Z) ∪ (Set.univ \ interior Δ₀) ∪
      (⋃ g ∈ Γ.E \ E_rem, closure g) ∪ (⋃ A ∈ 𝒜', D₀ A)
  have hB_closed : IsClosed B_forbid := by
    refine ((((Γ.finite_V.isClosed.union (hfin_Z.image α_map).isClosed).union
      (isClosed_univ.sdiff isOpen_interior)).union ?_).union ?_)
    · exact (Γ.finite_edges.subset sdiff_subset).isClosed_biUnion fun _ _ => isClosed_closure
    · exact hfin_𝒜'.isClosed_biUnion fun A hA => (hD₀ A hA.1).1.isClosed
  -- Verify hypotheses of `exists_shared_endpoint_arc_discs`.
  have hArc : ∀ e ∈ E_rem, IsArcMap (a_arc e) := fun e he => (ha_spec e he).2.2.2.2.2.1
  have hinter_arcs : ∀ e₁ ∈ E_rem, ∀ e₂ ∈ E_rem, e₁ ≠ e₂ →
      range (a_arc e₁) ∩ range (a_arc e₂) ⊆
        ({a_arc e₁ 0, a_arc e₁ 1} : Set S) ∩ {a_arc e₂ 0, a_arc e₂ 1} := by
    intro e₁ he₁ e₂ he₂ hne x ⟨hx₁, hx₂⟩
    obtain ⟨_, _, _, _, hcap₁, _, hr₁, h0₁, h1₁⟩ := ha_spec e₁ he₁
    obtain ⟨_, _, _, _, hcap₂, _, hr₂, h0₂, h1₂⟩ := ha_spec e₂ he₂
    rw [hr₁] at hx₁
    rw [hr₂] at hx₂
    have hxV : x ∈ Γ.V := by
      by_contra hx_notV
      have hxe₁ : x ∈ e₁ := by rw [← Γ.closure_diff_V he₁.1]; exact ⟨hx₁, hx_notV⟩
      have hxe₂ : x ∈ e₂ := by rw [← Γ.closure_diff_V he₂.1]; exact ⟨hx₂, hx_notV⟩
      exact hne (Γ.edge_eq_of_mem he₁.1 he₂.1 hxe₁ hxe₂)
    rw [h0₁, h1₁, h0₂, h1₂, ← hcap₁, ← hcap₂]
    exact ⟨⟨hx₁, hxV⟩, ⟨hx₂, hxV⟩⟩
  have hcontact : ∀ e ∈ E_rem, range (a_arc e) ∩ B_forbid = {a_arc e 0, a_arc e 1} := by
    intro e he
    obtain ⟨_, huV, hvV, _, hcap, _, hrange, h0, h1⟩ := ha_spec e he
    rw [hrange, h0, h1]
    apply Subset.antisymm
    · rintro x ⟨hxe, hxB⟩
      have hxU : x ∈ Γ.U := Γ.closure_subset_U he.1 hxe
      have hxV : x ∈ Γ.V := by
        rcases hxB with (((hxV | hxZ) | hx_compl) | hxg) | hxD₀
        · exact hxV
        · obtain ⟨z, hzZ, rfl⟩ := hxZ
          obtain ⟨v, hvV, hvz⟩ := (hα_ΓU z hzZ).mp hxU
          rw [← hvz, hα_ΓV v hvV (hvz ▸ hzZ)]
          exact hvV
        · have hx_Δ₀ : x ∈ Δ₀ := hΓ_Δ₀ hxU
          have hx_bd : x ∈ subBd Δ₀ := by
            rw [GM11.subBd_eq_frontier, frontier, hΔ₀.isClosed.closure_eq]
            exact ⟨hx_Δ₀, hx_compl.2⟩
          have hx_Pi : x ∈ PiSet := hbd_Δ₀ ▸ ⟨hx_bd, hxU⟩
          exact h83.hyp_ii.1.1 (h83.hyp_iii.1 hx_Pi)
        · obtain ⟨g, ⟨hgE, hg_not_rem⟩, hxg_cl⟩ := mem_iUnion₂.mp hxg
          by_contra hx_notV
          have hxe' : x ∈ e := by rw [← Γ.closure_diff_V he.1]; exact ⟨hxe, hx_notV⟩
          have hxg' : x ∈ g := by rw [← Γ.closure_diff_V hgE]; exact ⟨hxg_cl, hx_notV⟩
          exact hg_not_rem (Γ.edge_eq_of_mem hgE he.1 hxg' hxe' ▸ he)
        · obtain ⟨A, hA', hxDA⟩ := mem_iUnion₂.mp hxD₀
          by_contra hx_notV
          have hxe' : x ∈ e := by rw [← Γ.closure_diff_V he.1]; exact ⟨hxe, hx_notV⟩
          obtain ⟨hV_eq, hU_eq⟩ := interSet_V_and_U (hD₀ A hA'.1).1.isClosed (hD₀_norm A hA'.1)
          have hx_diff : x ∈ (Γ.interSet (D₀ A)).U \ (Γ.interSet (D₀ A)).V := by
            rw [hU_eq, hV_eq]
            exact ⟨⟨hxU, hxDA⟩, fun h => hx_notV h.1⟩
          change x ∈ Γ.spanU _ _ \ Γ.spanV _ _ at hx_diff
          rw [Γ.spanU_diff_spanV] at hx_diff
          obtain ⟨g, hg_span, hxg⟩ := hx_diff
          have hg_interE : g ∈ (Γ.interSet (D₀ A)).E := by
            change g ∈ (Γ.span _ _).E
            rwa [Γ.span_E]
          rw [(hD₀_props A hA'.1).2.2.2.1] at hg_interE
          have heq_eg : e = g := Γ.edge_eq_of_mem he.1 hg_interE.1 hxe' hxg
          exact he.2 A hA' (heq_eg ▸ hg_interE.2)
      exact hcap ▸ ⟨hxe, hxV⟩
    · rintro x (rfl | hx)
      · exact ⟨(hcap.symm.subset (Or.inl rfl)).1,
          Or.inl (Or.inl (Or.inl (Or.inl huV)))⟩
      · rw [mem_singleton_iff.mp hx]
        exact ⟨(hcap.symm.subset (Or.inr rfl)).1,
          Or.inl (Or.inl (Or.inl (Or.inl hvV)))⟩
  obtain ⟨Q, hQ, hQQ⟩ :=
    exists_shared_endpoint_arc_discs hS hE_rem_fin a_arc hArc hinter_arcs B_forbid hB_closed hcontact
  refine ⟨u_end, v_end, Q, ?_, ?_⟩
  · intro e he
    obtain ⟨huv, huV, hvV, hlk, hcap, _, hrange, h0, h1⟩ := ha_spec e he
    obtain ⟨hQe_disc, hQe_B, hQe_bd_ends, hQe_cl, hQe_bd_cl⟩ := hQ e he
    rw [h0, h1] at hQe_B hQe_bd_ends
    rw [hrange] at hQe_cl
    rw [hrange, h0, h1] at hQe_bd_cl
    have hbd_eq_discBd : subBd (Q e) = discBd (Q e) :=
      GM14.IsClosedDisc.subBd_eq_discBd hS hQe_disc
    rw [← hbd_eq_discBd] at hQe_bd_ends hQe_bd_cl
    have hQe_sub_Δ₀ : Q e ⊆ Δ₀ := by
      intro x hx
      by_cases hx_int : x ∈ interior Δ₀
      · exact interior_subset hx_int
      · have hx_ends : x ∈ ({u_end e, v_end e} : Set S) :=
          hQe_B.subset ⟨hx, Or.inl (Or.inl (Or.inr ⟨mem_univ x, hx_int⟩))⟩
        rcases hx_ends with rfl | hx_v
        · exact hΓ_Δ₀ (Γ.V_subset_U huV)
        · rw [mem_singleton_iff.mp hx_v]
          exact hΓ_Δ₀ (Γ.V_subset_U hvV)
    -- Show `Q e ∩ Γ.U = closure e`.
    have hQe_inter_U : Q e ∩ Γ.U = closure e := by
      apply Subset.antisymm
      · rintro x ⟨hxQ, hxU⟩
        by_cases hxV : x ∈ Γ.V
        · have hx_ends : x ∈ ({u_end e, v_end e} : Set S) :=
            hQe_B.subset ⟨hxQ, Or.inl (Or.inl (Or.inl (Or.inl hxV)))⟩
          exact (hcap.symm.subset hx_ends).1
        · obtain ⟨g, hgE, hxg⟩ := GM11.exists_mem_arcComponent (F := Γ.U \ Γ.V) ⟨hxU, hxV⟩
          by_cases hge : g = e
          · exact subset_closure (hge ▸ hxg)
          · by_cases hg_rem : g ∈ E_rem
            · have h_in_Qg : x ∈ Q e ∩ Q g := by
                obtain ⟨_, _, _, _, _, _, hrg, _, _⟩ := ha_spec g hg_rem
                have hcl_g : closure g ⊆ Q g := hrg ▸ (hQ g hg_rem).2.2.2.1
                exact ⟨hxQ, hcl_g (subset_closure hxg)⟩
              rw [hQQ e he g hg_rem (Ne.symm hge), h0, h1] at h_in_Qg
              exact (hcap.symm.subset h_in_Qg.1).1
            · have hx_ends : x ∈ ({u_end e, v_end e} : Set S) :=
                hQe_B.subset ⟨hxQ, Or.inl (Or.inr (mem_iUnion₂.mpr ⟨g, ⟨hgE, hg_rem⟩, subset_closure hxg⟩))⟩
              exact (hcap.symm.subset hx_ends).1
      · exact subset_inter hQe_cl (Γ.closure_subset_U he.1)
    have hbd_inter_U : subBd (Q e) ∩ Γ.U = {u_end e, v_end e} := by
      have h1 : subBd (Q e) ∩ Γ.U = subBd (Q e) ∩ (Q e ∩ Γ.U) := by
        rw [← Set.inter_assoc, inter_eq_self_of_subset_left
          (GM14.Whitney.subBd_subset_of subset_rfl hQe_disc.isClosed)]
      rw [h1, hQe_inter_U, hQe_bd_cl]
    have hbd_inter_V : subBd (Q e) ∩ Γ.V = {u_end e, v_end e} := by
      apply Subset.antisymm
      · exact (inter_subset_inter_right _ Γ.V_subset_U).trans hbd_inter_U.subset
      · refine subset_inter hQe_bd_ends ?_
        rintro x (rfl | hx)
        · exact huV
        · exact (mem_singleton_iff.mp hx) ▸ hvV
    have hQe_VZ : Q e ∩ (Γ.V ∪ (α_map '' Z)) = {u_end e, v_end e} := by
      apply Subset.antisymm
      · exact fun x ⟨hxQ, hxVZ⟩ => hQe_B.subset ⟨hxQ, Or.inl (Or.inl (Or.inl hxVZ))⟩
      · refine subset_inter (hQe_bd_ends.trans (GM14.Whitney.subBd_subset_of subset_rfl hQe_disc.isClosed)) ?_
        rintro x (rfl | hx)
        · exact Or.inl huV
        · exact Or.inl ((mem_singleton_iff.mp hx) ▸ hvV)
    have hbd_VZ : subBd (Q e) ∩ (Γ.V ∪ (α_map '' Z)) = {u_end e, v_end e} := by
      apply Subset.antisymm
      · exact (inter_subset_inter_left _ (GM14.Whitney.subBd_subset_of subset_rfl hQe_disc.isClosed)).trans
          hQe_VZ.subset
      · exact hbd_inter_V.symm.subset.trans (inter_subset_inter_right _ subset_union_left)
    have hbd_norm : subBd (Q e) ∩ Γ.U ⊆ Γ.V := by
      rw [hbd_inter_U, ← hbd_inter_V]
      exact inter_subset_right
    have hinter_V : (Γ.interSet (Q e)).V = {u_end e, v_end e} := by
      obtain ⟨hV_eq, _⟩ := interSet_V_and_U hQe_disc.isClosed hbd_norm
      rw [hV_eq]
      apply Subset.antisymm
      · exact fun x ⟨hxV, hxQ⟩ => hQe_VZ.subset ⟨hxQ, Or.inl hxV⟩
      · rintro x (rfl | hx)
        · exact ⟨huV, (hQe_VZ.symm.subset (Or.inl rfl)).1⟩
        · rw [mem_singleton_iff.mp hx]
          exact ⟨hvV, (hQe_VZ.symm.subset (Or.inr rfl)).1⟩
    have hinter_E : (Γ.interSet (Q e)).E = {e} := by
      change (Γ.span _ _).E = {e}
      rw [Γ.span_E]
      ext g
      simp only [mem_inter_iff, mem_ofPred_eq, mem_singleton_iff]
      constructor
      · rintro ⟨⟨hgE, hg_sub⟩, _⟩
        obtain ⟨x, hxg⟩ := hgE.1
        have hx_cl : x ∈ closure e := hQe_inter_U ▸ ⟨hg_sub hxg, (hgE.2.1 hxg).1⟩
        have hx_e : x ∈ e := by
          rw [← Γ.closure_diff_V he.1]
          exact ⟨hx_cl, (hgE.2.1 hxg).2⟩
        exact Γ.edge_eq_of_mem hgE he.1 hxg hx_e
      · rintro rfl
        exact ⟨⟨he.1, subset_closure.trans hQe_cl⟩, he.1⟩
    obtain ⟨A₀, hA₀_diff, he_A₀, hu_A₀, hv_A₀, hu_D₀⟩ := he_in_A₀ e he
    have hQe_D₀ : ∀ A ∈ 𝒜', Q e ∩ D₀ A = {u_end e, v_end e} ∩ (α_map '' Set.range (πA A)) := by
      intro A hA'
      apply Subset.antisymm
      · rintro x ⟨hxQ, hxDA⟩
        have hx_ends : x ∈ ({u_end e, v_end e} : Set S) :=
          hQe_B.subset ⟨hxQ, Or.inr (mem_iUnion₂.mpr ⟨A, hA', hxDA⟩)⟩
        refine ⟨hx_ends, ?_⟩
        have hxV : x ∈ Γ.V := by
          rcases hx_ends with rfl | hx_v
          · exact huV
          · exact (mem_singleton_iff.mp hx_v) ▸ hvV
        have hx_A₀ : ιV x ∈ V(A₀) \ W := by
          rcases hx_ends with rfl | hx_v
          · exact hu_A₀
          · exact (mem_singleton_iff.mp hx_v) ▸ hv_A₀
        have hx_interV : x ∈ (Γ.interSet (D₀ A)).V := by
          obtain ⟨hV_eq, _⟩ := interSet_V_and_U (hD₀ A hA'.1).1.isClosed (hD₀_norm A hA'.1)
          exact hV_eq ▸ ⟨hxV, hxDA⟩
        rw [(hD₀_props A hA'.1).2.2.1] at hx_interV
        have hne_A₀A : A₀ ≠ A := fun heq => hA₀_diff.2 (heq ▸ hA')
        have hx_ZW : ιV x ∈ Z ∪ W :=
          (hZdiv.2.2.2 A₀ hA₀_diff.1 A hA'.1 hne_A₀A).2 ⟨hx_A₀.1, hx_interV.2⟩
        have hxZ : ιV x ∈ Z := hx_ZW.resolve_right hx_A₀.2
        have hx_range : ιV x ∈ Set.range (πA A) :=
          (h83.hyp_vii A hA'.1).2.2.symm ▸ ⟨hxZ, hx_interV.2⟩
        exact ⟨ιV x, hx_range, hα_ΓV x hxV hxZ⟩
      · rintro x ⟨hx_ends, ⟨z, hz_range, rfl⟩⟩
        exact ⟨(hQe_VZ.symm.subset hx_ends).1,
          GM14.Whitney.subBd_subset_of subset_rfl (hD₀ A hA'.1).1.isClosed
            (hα_bdA A hA'.1 z hz_range)⟩
    exact ⟨huv, huV, hvV, hlk, hcap, ⟨A₀, hA₀_diff, he_A₀, hu_A₀, hv_A₀, hu_D₀⟩,
      hQe_disc, hQe_sub_Δ₀, hbd_inter_U, hbd_inter_V, hQe_VZ, hbd_VZ,
      hinter_V, hinter_E, hQe_D₀⟩
  · intro e₁ he₁ e₂ he₂ hne
    obtain ⟨_, _, _, _, _, _, _, h0₁, h1₁⟩ := ha_spec e₁ he₁
    obtain ⟨_, _, _, _, _, _, _, h0₂, h1₂⟩ := ha_spec e₂ he₂
    rw [← h0₁, ← h1₁, ← h0₂, ← h1₂]
    exact hQQ e₁ he₁ e₂ he₂ hne

/-- The subgraph `B_e = P_e ∪ N_W` associated with an edge `e ∈ Γ.E` linking `u` and `v` in `Γ`. -/
noncomputable def edgePieceSubgraph (W : Set α) (ιV : S ↪ α) (ιE : Set S ↪ β) (Γ : Drawing S)
    (e : Set S) (u v : S) (hlk : Γ.toGraph.IsLink e u v) : Graph α β :=
  let hlk_emb : (Γ.toEmbeddedGraph ιV ιE).IsLink (ιE e) (ιV u) (ιV v) :=
    ⟨e, u, v, hlk, rfl, rfl, rfl⟩
  graphUnion (walkSubgraph (GraphWalk.cons hlk_emb (GraphWalk.nil hlk_emb.right_mem)))
    (Graph.noEdge W β)

/-- Structural, separation, and tangle-distance properties of `edgePieceSubgraph` and its disc `Q_e`. -/
theorem edge_piece_props_8_3
    {q δ h θ θ' : ℕ}
    {ιV ιV' : S ↪ α} {ιE : Set S ↪ β}
    {R_G : RootedDigraph α β q} {W : Set α}
    {Γ C₀ : Drawing S} {r₀ : Set S} {orient : GM19.SurfaceOrientation S}
    {PiSet : Set S}
    {ord : ℕ} {T : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    {d : Set S → Set S → ℕ}
    {J : Graph α β} {Z : Set α} {𝒜 : Set (Graph α β)}
    {πLen : Graph α β → ℕ} {πA : ∀ A : Graph α β, Fin (πLen A) → α}
    {vA : Graph α β → S} {D_disc : Set S} {v_star : S}
    (h83 : Hypotheses83 q δ h θ ιV ιE R_G W Γ C₀ r₀ orient PiSet ord T d J Z 𝒜
      πLen πA vA D_disc v_star)
    (hθ'4 : 4 ≤ θ') (hθ_bound : 2 * θ' + 13 ≤ θ)
    (hιV'_ΓV : ∀ s ∈ Γ.V, ιV' s = ιV s)
    {Δ₀ Δ : Set S} (hΔ₀ : IsClosedDisc Δ₀) (hbd_Δ₀ : subBd Δ₀ ∩ Γ.U = PiSet)
    (hcompl_r₀ : Set.univ \ Δ₀ ⊆ r₀)
    {D₀ : Graph α β → Set S}
    (hD₀_disc : ∀ A ∈ 𝒜, IsClosedDisc (D₀ A))
    (hD₀_norm : ∀ A ∈ 𝒜, subBd (D₀ A) ∩ Γ.U ⊆ Γ.V)
    (hD₀_bdV : ∀ A ∈ 𝒜, subBd (D₀ A) ∩ Γ.V = {v ∈ Γ.V | ιV v ∈ Set.range (πA A)})
    (hD₀_interV : ∀ A ∈ 𝒜, (Γ.interSet (D₀ A)).V = {v ∈ Γ.V | ιV v ∈ V(A)})
    (hins₀ : ∀ A ∈ 𝒜, IsTangleIns Γ T (subBd (D₀ A)) (D₀ A))
    (hc6 : ∀ A ∈ 𝒜, ∃ r ∈ Γ.R, vA A ∈ subBd r ∧ (r ∩ D₀ A).Nonempty)
    (hc10 : θ - θ' - 2 ≤ subsetTangleDist Γ ord d D_disc (Set.univ \ Δ))
    {e : Set S} {u v : S} (huv : u ≠ v) (huV : u ∈ Γ.V) (hvV : v ∈ Γ.V)
    (hlk : Γ.toGraph.IsLink e u v)
    {A₀ : Graph α β} (hA₀ : A₀ ∈ 𝒜)
    (hA₀_not' : ¬ 5 ≤ subsetTangleDist Γ ord d {vA A₀} C₀.V)
    (hu_D₀ : u ∈ D₀ A₀)
    {Q_e : Set S} (hQe_disc : IsClosedDisc Q_e) (hQe_sub : Q_e ⊆ Δ₀)
    (hQe_bdU : subBd Q_e ∩ Γ.U = {u, v}) (hQe_bdV : subBd Q_e ∩ Γ.V = {u, v})
    (hQe_interV : (Γ.interSet Q_e).V = {u, v}) (hQe_interE : (Γ.interSet Q_e).E = {e}) :
    let B_e := edgePieceSubgraph W ιV ιE Γ e u v hlk
    let GA := (Γ.toEmbeddedGraph ιV' ιE) ⊓ B_e
    B_e ≤ graphUnion (Γ.toEmbeddedGraph ιV ιE) (Graph.noEdge W β) ∧
    B_e ≤ R_G.G.toGraph ∧
    V(B_e) = {ιV u, ιV v} ∪ W ∧
    E(B_e) = {ιE e} ∧
    (Γ.interSet Q_e).toEmbeddedGraph ιV' ιE = GA ∧
    IsGraphPathWithEnds GA GA (ιV u) (ιV v) ∧
    (∀ x ∈ ({ιV u, ιV v} : Set α), ∀ y ∈ ({ιV u, ιV v} : Set α),
      ∃ P : Graph α β, IsGraphPathWithEnds (B_e.deleteVerts W) P x y ∧
        Disjoint (pathInternalVerts (B_e.deleteVerts W) P) {ιV u, ιV v}) ∧
    (¬ ∃ (C D : Graph α β) (C_Γ D_Γ : Hypergraph S (Set S)),
      IsGraphSeparation (R_G.G.toGraph.deleteVerts W) C D ∧
      (V(C) ∩ V(D)).ncard < 2 ∧
      B_e.deleteVerts W ≤ C ∧
      C_Γ.vertexSet = ιV' ⁻¹' V(C) ∩ Γ.V ∧ C_Γ.edgeSet = ιE ⁻¹' E(C) ∩ Γ.E ∧
      D_Γ.vertexSet = ιV' ⁻¹' V(D) ∩ Γ.V ∧ D_Γ.edgeSet = ιE ⁻¹' E(D) ∩ Γ.E ∧
      (C_Γ, D_Γ) ∈ T) ∧
    θ' ≤ subsetTangleDist Γ ord d Q_e (Set.univ \ Δ) ∧
    ¬ Disjoint Q_e Δ := by
  intro B_e GA
  obtain ⟨hS, _⟩ := GM11.IsSphere.isClosedSurface h83.hyp_i.1
  have hθ_ord := h83.hyp_iv.1
  have hord5 : 5 ≤ ord := by omega
  let Γ_emb := Γ.toEmbeddedGraph ιV ιE
  have hΓ_emb_eq : Γ.toEmbeddedGraph ιV' ιE = Γ_emb :=
    toEmbeddedGraph_congr_of_eq_on_V hιV'_ΓV
  have hlk_emb : Γ_emb.IsLink (ιE e) (ιV u) (ιV v) := ⟨e, u, v, hlk, rfl, rfl, rfl⟩
  let W_e : GraphWalk Γ_emb (ιV u) (ιV v) := .cons hlk_emb (.nil hlk_emb.right_mem)
  let P_e : Graph α β := walkSubgraph W_e
  have hPe_le_Γ : P_e ≤ Γ_emb := walkSubgraph_le W_e
  have hΓ_le_G : Γ_emb ≤ R_G.G.toGraph := h83.Γ_le.trans Graph.deleteVerts_le
  have hNW_le_G : Graph.noEdge W β ≤ R_G.G.toGraph :=
    ⟨h83.ordering_W.1, fun _ _ _ hl => by simp at hl⟩
  have hBe_le_union : B_e ≤ graphUnion Γ_emb (Graph.noEdge W β) :=
    graphUnion_le (hPe_le_Γ.trans (le_graphUnion_left _ _))
      (le_graphUnion_right (Compatible.of_le_le hΓ_le_G hNW_le_G))
  have hBe_le_G : B_e ≤ R_G.G.toGraph :=
    hBe_le_union.trans (graphUnion_le hΓ_le_G hNW_le_G)
  have hVPe : V(P_e) = {ιV u, ιV v} := by
    ext x
    simp [P_e, W_e, vertexSet_walkSubgraph, GraphWalk.support]
  have hEPe : E(P_e) = {ιE e} := by
    ext f
    simp [P_e, W_e, edgeSet_walkSubgraph, GraphWalk.edges]
  have hVBe : V(B_e) = {ιV u, ιV v} ∪ W := by
    change V(graphUnion P_e (Graph.noEdge W β)) = _
    rw [vertexSet_graphUnion, hVPe, Graph.vertexSet_noEdge]
  have hEBe : E(B_e) = {ιE e} := by
    change E(graphUnion P_e (Graph.noEdge W β)) = _
    rw [edgeSet_graphUnion, hEPe, Graph.edgeSet_noEdge, union_empty]
  have hu_not_W : ιV u ∉ W := by
    have hmem := h83.Γ_le.vertexSet_mono ⟨u, huV, rfl⟩
    rw [Graph.vertexSet_deleteVerts] at hmem
    exact hmem.2
  have hv_not_W : ιV v ∉ W := by
    have hmem := h83.Γ_le.vertexSet_mono ⟨v, hvV, rfl⟩
    rw [Graph.vertexSet_deleteVerts] at hmem
    exact hmem.2
  -- Show `B_e.deleteVerts W = P_e` and `GA = P_e`.
  have hBe_del : B_e.deleteVerts W = P_e := by
    refine Graph.ext ?_ fun f x y => ?_
    · rw [Graph.vertexSet_deleteVerts, hVBe, hVPe]
      ext x
      simp only [mem_sdiff, mem_union, mem_insert_iff, mem_singleton_iff]
      constructor
      · rintro ⟨(rfl | rfl) | hxW, hx_notW⟩
        · exact Or.inl rfl
        · exact Or.inr rfl
        · exact False.elim (hx_notW hxW)
      · rintro (rfl | rfl)
        · exact ⟨Or.inl (Or.inl rfl), hu_not_W⟩
        · exact ⟨Or.inl (Or.inr rfl), hv_not_W⟩
    · rw [Graph.deleteVerts_isLink]
      change (P_e.IsLink f x y ∨ (f ∉ E(P_e) ∧ (Graph.noEdge W β).IsLink f x y)) ∧
          x ∉ W ∧ y ∉ W ↔ P_e.IsLink f x y
      simp only [Graph.noEdge_isLink, and_false, or_false]
      constructor
      · exact And.left
      · intro hlk_P
        have hx_Pe : x ∈ ({ιV u, ιV v} : Set α) := hVPe ▸ hlk_P.left_mem
        have hy_Pe : y ∈ ({ιV u, ιV v} : Set α) := hVPe ▸ hlk_P.right_mem
        exact ⟨hlk_P, hx_Pe.elim (fun h => h ▸ hu_not_W) (fun h => h ▸ hv_not_W),
          hy_Pe.elim (fun h => h ▸ hu_not_W) (fun h => h ▸ hv_not_W)⟩
  have hGA_eq : GA = P_e := by
    change (Γ.toEmbeddedGraph ιV' ιE) ⊓ B_e = P_e
    rw [hΓ_emb_eq]
    refine Graph.ext ?_ fun f x y => ?_
    · rw [Graph.vertexSet_inf, hVBe, hVPe]
      ext x
      simp only [mem_inter_iff, mem_union, mem_insert_iff, mem_singleton_iff]
      constructor
      · rintro ⟨hxΓ, (rfl | rfl) | hxW⟩
        · exact Or.inl rfl
        · exact Or.inr rfl
        · have hx_del := h83.Γ_le.vertexSet_mono hxΓ
          rw [Graph.vertexSet_deleteVerts] at hx_del
          exact False.elim (hx_del.2 hxW)
      · rintro (rfl | rfl)
        · exact ⟨⟨u, huV, rfl⟩, Or.inl (Or.inl rfl)⟩
        · exact ⟨⟨v, hvV, rfl⟩, Or.inl (Or.inr rfl)⟩
    · rw [inf_isLink]
      change Γ_emb.IsLink f x y ∧ (P_e.IsLink f x y ∨ (f ∉ E(P_e) ∧ (Graph.noEdge W β).IsLink f x y)) ↔
          P_e.IsLink f x y
      simp only [Graph.noEdge_isLink, and_false, or_false]
      exact ⟨And.right, fun h => ⟨h.mono hPe_le_Γ, h⟩⟩
  -- Show `(Γ.interSet Q_e).toEmbeddedGraph ιV' ιE = P_e`.
  have hinter_emb : (Γ.interSet Q_e).toEmbeddedGraph ιV' ιE = P_e := by
    have hsub : (Γ.interSet Q_e).IsSubdrawing Γ := Γ.span_isSubdrawing _ _
    have hcongr : (Γ.interSet Q_e).toEmbeddedGraph ιV' ιE =
        (Γ.interSet Q_e).toEmbeddedGraph ιV ιE :=
      toEmbeddedGraph_congr_of_eq_on_V fun s hs => hιV'_ΓV s (hsub.1 hs)
    rw [hcongr]
    refine Graph.ext ?_ fun f x y => ?_
    · change ιV '' (Γ.interSet Q_e).V = V(P_e)
      rw [hQe_interV, hVPe, image_pair]
    · simp only [Drawing.toEmbeddedGraph, P_e, W_e, walkSubgraph_isLink,
        GraphWalk.edges, List.mem_cons, List.not_mem_nil, or_false]
      constructor
      · rintro ⟨e₀, x₀, y₀, hlk₀, rfl, rfl, rfl⟩
        have he₀ : e₀ ∈ (Γ.interSet Q_e).E := hlk₀.edge_mem
        have hlk_Γ₀ : Γ.toGraph.IsLink e₀ x₀ y₀ := (hsub.isLink_iff he₀).mp hlk₀
        rw [hQe_interE, mem_singleton_iff] at he₀
        subst he₀
        exact ⟨rfl, e₀, x₀, y₀, hlk_Γ₀, rfl, rfl, rfl⟩
      · rintro ⟨rfl, e₀, x₀, y₀, hlk_Γ₀, he_eq, rfl, rfl⟩
        obtain rfl : e₀ = e := ιE.injective he_eq
        have he_mem : e₀ ∈ (Γ.interSet Q_e).E := hQe_interE.symm ▸ rfl
        exact ⟨e₀, x₀, y₀, (hsub.isLink_iff he_mem).mpr hlk_Γ₀, rfl, rfl, rfl⟩
  -- Show `IsGraphPathWithEnds P_e P_e (ιV u) (ιV v)`.
  have hWe_simp : W_e.IsSimple := by
    change [ιV u, ιV v].Nodup
    simp [ιV.injective.ne huv]
  have hPe_path_Γ : IsGraphPathWithEnds Γ_emb P_e (ιV u) (ιV v) :=
    isGraphPathWithEnds_walkSubgraph hWe_simp
  obtain ⟨_, W_Pe, hs_Pe, hV_Pe_W, hE_Pe_W⟩ := hPe_path_Γ
  have hPe_path_self : IsGraphPathWithEnds P_e P_e (ιV u) (ιV v) :=
    ⟨le_rfl, W_Pe, hs_Pe, hV_Pe_W, hE_Pe_W⟩
  -- Property 4: `path_in_A` for `B_e`.
  have hpath_Be : ∀ x ∈ ({ιV u, ιV v} : Set α), ∀ y ∈ ({ιV u, ιV v} : Set α),
      ∃ P : Graph α β, IsGraphPathWithEnds (B_e.deleteVerts W) P x y ∧
        Disjoint (pathInternalVerts (B_e.deleteVerts W) P) {ιV u, ιV v} := by
    rw [hBe_del]
    intro x hx y hy
    by_cases hxy : x = y
    · subst hxy
      have hx_Pe : x ∈ V(P_e) := hVPe.symm ▸ hx
      obtain ⟨P₀, hP₀, hP₀_int⟩ := exists_trivial_path_self hx_Pe
      exact ⟨P₀, hP₀, by rw [hP₀_int]; exact Set.empty_disjoint _⟩
    · have h_ends : IsGraphPathWithEnds P_e P_e x y := by
        rcases hx with rfl | hx' <;> rcases hy with rfl | hy'
        · exact (hxy rfl).elim
        · rw [mem_singleton_iff.mp hy']
          exact hPe_path_self
        · rw [mem_singleton_iff.mp hx']
          exact hPe_path_self.symm
        · rw [mem_singleton_iff.mp hx', mem_singleton_iff.mp hy'] at hxy
          exact (hxy rfl).elim
      refine ⟨P_e, h_ends, ?_⟩
      rw [Set.disjoint_left]
      intro z hz_int hz_pair
      have hz_diff : z ∈ V(P_e) \ {x, y} :=
        IsGraphPathWithEnds.pathInternalVerts_subset h_ends hz_int
      rcases hx with rfl | hx' <;> rcases hy with rfl | hy'
      · exact (hxy rfl).elim
      · rw [mem_singleton_iff.mp hy'] at hz_diff
        exact hz_diff.2 hz_pair
      · rw [mem_singleton_iff.mp hx'] at hz_diff
        rw [Set.pair_comm] at hz_diff
        exact hz_diff.2 hz_pair
      · rw [mem_singleton_iff.mp hx', mem_singleton_iff.mp hy'] at hxy
        exact (hxy rfl).elim
  -- Property 5: `no_small_sep` for `B_e`.
  have hno_sep : ¬ ∃ (C D : Graph α β) (C_Γ D_Γ : Hypergraph S (Set S)),
      IsGraphSeparation (R_G.G.toGraph.deleteVerts W) C D ∧
      (V(C) ∩ V(D)).ncard < 2 ∧
      B_e.deleteVerts W ≤ C ∧
      C_Γ.vertexSet = ιV' ⁻¹' V(C) ∩ Γ.V ∧ C_Γ.edgeSet = ιE ⁻¹' E(C) ∩ Γ.E ∧
      D_Γ.vertexSet = ιV' ⁻¹' V(D) ∩ Γ.V ∧ D_Γ.edgeSet = ιE ⁻¹' E(D) ∩ Γ.E ∧
      (C_Γ, D_Γ) ∈ T := by
    rintro ⟨C, D, C_Γ, D_Γ, hsep, hcard_lt, hBe_C, hC_V, hC_E, hD_V, hD_E, hmem_T⟩
    rw [hBe_del] at hBe_C
    have hT : IsRespectfulDrawingTangle Γ ord T := h83.hyp_iv.2.1.1
    have he_EC : e ∈ C_Γ.edgeSet := by
      rw [hC_E]
      exact ⟨hBe_C.edgeSet_mono (hEPe.symm ▸ rfl), hlk.edge_mem⟩
    have hEC_ne : C_Γ.edgeSet.Nonempty := ⟨e, he_EC⟩
    have hEC_sub : C_Γ.edgeSet ⊆ Γ.E := by rw [hC_E]; exact inter_subset_right
    have hC_V' : C_Γ.vertexSet = ιV ⁻¹' V(C) ∩ Γ.V := by
      rw [hC_V]
      ext s
      simp only [mem_inter_iff, mem_preimage]
      exact and_congr_left fun hs => by rw [hιV'_ΓV s hs]
    have hD_V' : D_Γ.vertexSet = ιV ⁻¹' V(D) ∩ Γ.V := by
      rw [hD_V]
      ext s
      simp only [mem_inter_iff, mem_preimage]
      exact and_congr_left fun hs => by rw [hιV'_ΓV s hs]
    obtain ⟨G₀, P_sub, hSD⟩ := Whitney.exists_subData h83.hyp_i.2
    -- Show `(Γ.E \ C_Γ.edgeSet).Nonempty`.
    have hcompl_ne : (Γ.E \ C_Γ.edgeSet).Nonempty := by
      by_contra hemp
      rw [Set.not_nonempty_iff_eq_empty, Set.sdiff_eq_empty] at hemp
      have hEC_eq : C_Γ.edgeSet = Γ.E := Subset.antisymm hEC_sub hemp
      have hED_emp : D_Γ.edgeSet = ∅ := by
        rw [hD_E]
        ext g
        simp only [mem_inter_iff, mem_preimage, mem_empty_iff_false, iff_false, not_and]
        intro hgD hgE
        have hgC : ιE g ∈ E(C) := by
          have : g ∈ C_Γ.edgeSet := hEC_eq.symm ▸ hgE
          rw [hC_E] at this
          exact this.1
        exact disjoint_left.mp hsep.2.2.2.2 hgC hgD
      let Q₀ : Graph S (Set S) := Graph.noEdge {u} (Set S)
      have hQ₀_path : IsGraphPathWithEnds Γ.toGraph Q₀ u u := by
        refine ⟨⟨singleton_subset_iff.mpr huV, fun _ _ _ h => h.elim⟩,
          .nil (mem_singleton u), List.nodup_singleton u, ?_, ?_⟩
        · ext z; exact mem_singleton_iff.trans List.mem_singleton.symm
        · ext g; exact iff_of_false id List.not_mem_nil
      have hbd_Q₀ : bdry Γ.toGraph E(Q₀) ⊆ {u, u} := fun _ ⟨⟨_, hg, _⟩, _⟩ => hg.elim
      have hDC_T : (D_Γ, C_Γ) ∈ T :=
        path_sep_mem_tangle hT.2.1 (by omega) hQ₀_path hbd_Q₀ (hT.2.1.isSeparation hmem_T).symm
          (by rw [GM10.separationOrder_comm]; exact hT.2.1.order_lt hmem_T)
          (by rw [hED_emp]; exact empty_subset _)
      exact tangle_not_both hT.2.1 hmem_T hDC_T
    -- Bound `(bdry Γ.toGraph C_Γ.edgeSet).ncard`.
    have hbd_sub : ιV '' (bdry Γ.toGraph C_Γ.edgeSet) ⊆ V(C) ∩ V(D) := by
      rintro _ ⟨s, ⟨⟨g₁, hg₁, y₁, hlk₁⟩, g₂, ⟨hg₂E, hg₂_not⟩, y₂, hlk₂⟩, rfl⟩
      have hg₁C : ιE g₁ ∈ E(C) := by rw [hC_E] at hg₁; exact hg₁.1
      have hg₂_notC : ιE g₂ ∉ E(C) := fun h => hg₂_not (by rw [hC_E]; exact ⟨h, hg₂E⟩)
      have hlk₁_del : (R_G.G.toGraph.deleteVerts W).IsLink (ιE g₁) (ιV s) (ιV y₁) :=
        h83.Γ_le.2 ⟨g₁, s, y₁, hlk₁, rfl, rfl, rfl⟩
      have hlk₂_del : (R_G.G.toGraph.deleteVerts W).IsLink (ιE g₂) (ιV s) (ιV y₂) :=
        h83.Γ_le.2 ⟨g₂, s, y₂, hlk₂, rfl, rfl, rfl⟩
      have hg₂D : ιE g₂ ∈ E(D) :=
        (hsep.2.2.2.1 ▸ hlk₂_del.edge_mem).resolve_left hg₂_notC
      exact ⟨((hsep.1.isLink_iff hg₁C).mpr hlk₁_del).left_mem,
        ((hsep.2.1.isLink_iff hg₂D).mpr hlk₂_del).left_mem⟩
    have hfin_CD : (V(C) ∩ V(D)).Finite :=
      h83.finite_V.subset (inter_subset_left.trans
        (hsep.1.vertexSet_mono.trans Graph.deleteVerts_le.vertexSet_mono))
    have hbd_lt : (bdry Γ.toGraph C_Γ.edgeSet).ncard < 2 := by
      have h1 : (bdry Γ.toGraph C_Γ.edgeSet).ncard =
          (ιV '' (bdry Γ.toGraph C_Γ.edgeSet)).ncard :=
        (Set.ncard_image_of_injective _ ιV.injective).symm
      have h2 : (ιV '' (bdry Γ.toGraph C_Γ.edgeSet)).ncard ≤ (V(C) ∩ V(D)).ncard :=
        Set.ncard_le_ncard hbd_sub hfin_CD
      omega
    obtain ⟨_, x, y, _, _, hxy, hbd_eq, _, _, _⟩ :=
      SubDataSepGeneral.sep_general hSD hEC_sub (by omega) hEC_ne hcompl_ne
    have hbd_card2 : (bdry Γ.toGraph C_Γ.edgeSet).ncard = 2 := by
      rw [hbd_eq, Set.ncard_pair hxy]
    omega
  -- Property 6: `θ' ≤ subsetTangleDist Γ ord d Q_e (Set.univ \ Δ)` and `¬ Disjoint Q_e Δ`.
  have hQe_dist : θ' ≤ subsetTangleDist Γ ord d Q_e (Set.univ \ Δ) := by
    have hQe_norm : subBd Q_e ∩ Γ.U ⊆ Γ.V := by
      rw [hQe_bdU, ← hQe_bdV]
      exact inter_subset_right
    have hQe_card : (subBd Q_e ∩ Γ.V).ncard ≤ 3 := by
      rw [hQe_bdV, Set.ncard_pair huv]
      omega
    obtain ⟨hQe_ins, _⟩ :=
      isTangleIns_of_disc_in_Δ₀_8_3 h83 (by omega) hΔ₀ hbd_Δ₀ hQe_disc hQe_sub hQe_norm hQe_card
    have hF_oarc : IsOArc (subBd Q_e) := by
      rw [GM14.IsClosedDisc.subBd_eq_discBd hS hQe_disc]
      exact hQe_disc.isOArc_discBd
    have hFV_lt_ord : (subBd Q_e ∩ Γ.V).ncard < ord := by omega
    have hdist_Qe : ∀ z ∈ Γ.A, ∀ y ∈ Γ.A, (z ∩ Q_e).Nonempty → (y ∩ Q_e).Nonempty → d z y ≤ 3 := by
      intro z hz y hy hzQ hyQ
      exact (GM12.dist_le_of_oarc_disc hS h83.hyp_iv.2.1 hF_oarc hQe_norm hFV_lt_ord
        hQe_disc hQe_ins.2.1 hQe_ins.2.2 hz hy hzQ hyQ).trans hQe_card
    have hu_Qe : u ∈ Q_e :=
      GM14.Whitney.subBd_subset_of subset_rfl hQe_disc.isClosed (hQe_bdV.symm.subset (Or.inl rfl)).1
    have hu_atom : ({u} : Set S) ∈ Γ.A := Or.inl (Or.inl ⟨u, huV, rfl⟩)
    have hd_u_vA₀ : d {u} {vA A₀} ≤ 3 :=
      ((dist_vA_atom_meets_DA_le_three h83 (by omega) hD₀_disc hD₀_norm hD₀_bdV hD₀_interV
        hins₀ hc6 hA₀).2.1 {u} hu_atom ⟨u, rfl, hu_D₀⟩).2
    have hvA₀_V : vA A₀ ∈ Γ.V := (h83.hyp_xi A₀ hA₀).1
    have hvA₀_atom : ({vA A₀} : Set S) ∈ Γ.A := Or.inl (Or.inl ⟨vA A₀, hvA₀_V, rfl⟩)
    have hd_vA₀_r₀ : d {vA A₀} r₀ ≤ 5 :=
      (dist_compl_Δ₀_le_five_of_dist_C₀_lt_five h83 hord5 hΔ₀ hcompl_r₀ hvA₀_V
        (not_le.mp hA₀_not')).1
    obtain ⟨Δ_c, hΔc_disc, _, _, hΔc_int⟩ :=
      exists_complementary_closedDisc_in_sphere h83.hyp_i.1 hΔ₀
    have hbd_c : subBd Δ_c = discBd Δ_c := GM14.IsClosedDisc.subBd_eq_discBd hS hΔc_disc
    obtain ⟨_, g_c, hc_chart⟩ := hΔc_disc.exists_isChart
    have hp₀_compl : g_c 0 ∈ Set.univ \ Δ₀ := by
      rw [← hΔc_int, hbd_c]
      refine ⟨hc_chart.gm (Metric.mem_closedBall_self zero_le_one), ?_⟩
      rw [← hc_chart.g_sphere]
      rintro ⟨w, hw, heq⟩
      have h0w : w = 0 := hc_chart.injOn (sphere_subset_closedBall hw)
        (Metric.mem_closedBall_self zero_le_one) heq
      rw [h0w] at hw
      simp at hw
    have hp₀_r₀ : g_c 0 ∈ r₀ := hcompl_r₀ hp₀_compl
    have hp₀_D : g_c 0 ∈ D_disc := h83.hyp_xii.2.2 hp₀_r₀
    have hr₀A : r₀ ∈ Γ.A := Or.inr h83.hyp_ii.2.2.1
    refine le_subsetTangleDist_of_forall (by omega) fun z hz b hb hzQ hb_compl => ?_
    have hd_zu : d z {u} ≤ 3 := hdist_Qe z hz {u} hu_atom hzQ ⟨u, rfl, hu_Qe⟩
    have hd_r₀b : θ - θ' - 2 ≤ d r₀ b :=
      hc10.trans (subsetTangleDist_le_of_mem hr₀A hb ⟨g_c 0, hp₀_r₀, hp₀_D⟩ hb_compl)
    have htri₁ : d r₀ b ≤ d r₀ {vA A₀} + d {vA A₀} b :=
      HasTangleMetric.triangle hS h83.hyp_iv.2.1 hr₀A hvA₀_atom hb
    have htri₂ : d {vA A₀} b ≤ d {vA A₀} {u} + d {u} b :=
      HasTangleMetric.triangle hS h83.hyp_iv.2.1 hvA₀_atom hu_atom hb
    have htri₃ : d {u} b ≤ d {u} z + d z b :=
      HasTangleMetric.triangle hS h83.hyp_iv.2.1 hu_atom hz hb
    have hc1 : d r₀ {vA A₀} = d {vA A₀} r₀ := HasTangleMetric.comm h83.hyp_iv.2.1 hr₀A hvA₀_atom
    have hc2 : d {vA A₀} {u} = d {u} {vA A₀} := HasTangleMetric.comm h83.hyp_iv.2.1 hvA₀_atom hu_atom
    have hc3 : d {u} z = d z {u} := HasTangleMetric.comm h83.hyp_iv.2.1 hu_atom hz
    omega
  have hQe_not_disj : ¬ Disjoint Q_e Δ := by
    have hQe_sub_Δ : Q_e ⊆ Δ :=
      subset_of_one_le_subsetTangleDist_compl h83.hyp_iv.2.1 (by omega)
    have hu_Qe : u ∈ Q_e :=
      GM14.Whitney.subBd_subset_of subset_rfl hQe_disc.isClosed (hQe_bdV.symm.subset (Or.inl rfl)).1
    intro hdisj
    exact hdisj.le_bot ⟨hu_Qe, hQe_sub_Δ hu_Qe⟩
  exact ⟨hBe_le_union, hBe_le_G, hVBe, hEBe, hinter_emb.trans hGA_eq.symm,
    hGA_eq.symm ▸ hPe_path_self, hpath_Be, hno_sep, hQe_dist, hQe_not_disj⟩

/-! ## 4. Assembling the Augmented `(J1)`–`(J7)` System for Theorem 8.3 -/

omit [T2Space S] in
/-- The boundary `subBd D` of any closed disc `D` in a closed surface `S` is infinite. -/
theorem isClosedDisc_infinite_subBd (hS : IsClosedSurface S) {D : Set S} (hD : IsClosedDisc D) :
    (subBd D).Infinite := by
  rw [GM14.IsClosedDisc.subBd_eq_discBd hS hD]
  obtain ⟨h_ch, g_ch, ch⟩ := hD.exists_isChart
  let z : ℕ → ℂ := fun k =>
    ⟨1 / (k + 2 : ℝ), Real.sqrt (1 - (1 / (k + 2 : ℝ)) ^ 2)⟩
  have hz_mem : ∀ k : ℕ, z k ∈ Metric.sphere (0 : ℂ) 1 := by
    intro k
    rw [mem_sphere_zero_iff_norm, Complex.norm_def]
    have hle : (1 / (k + 2 : ℝ)) ^ 2 ≤ 1 := by
      have h1 : (0 : ℝ) ≤ 1 / (k + 2 : ℝ) := by positivity
      have h2 : 1 / (k + 2 : ℝ) ≤ 1 := div_le_one_of_le₀ (by linarith) (by positivity)
      nlinarith
    have hnsq : Complex.normSq (z k) = 1 := by
      dsimp [z, Complex.normSq]
      rw [Real.mul_self_sqrt (by linarith)]
      ring
    rw [hnsq, Real.sqrt_one]
  have hf_mem : ∀ k : ℕ, g_ch (z k) ∈ discBd D := by
    intro k
    rw [← ch.g_sphere]
    exact ⟨z k, hz_mem k, rfl⟩
  refine Set.infinite_of_injective_forall_mem (f := fun k : ℕ => g_ch (z k)) ?_ hf_mem
  intro k₁ k₂ hk
  have hz_eq : z k₁ = z k₂ := by
    rw [← ch.hg (sphere_subset_closedBall (hz_mem k₁)),
      ← ch.hg (sphere_subset_closedBall (hz_mem k₂))]
    exact congrArg h_ch hk
  have hre : (1 / (k₁ + 2 : ℝ)) = (1 / (k₂ + 2 : ℝ)) := congrArg Complex.re hz_eq
  have hinv : (k₁ : ℝ) + 2 = (k₂ : ℝ) + 2 := by
    have := congrArg Inv.inv hre
    simpa [one_div] using this
  exact Nat.cast_injective (add_right_cancel hinv)

set_option maxHeartbeats 1200000 in
/-- Assembles the augmented division `𝒜''` and discs `D''` in the proof of Theorem 8.3 (pages
561–563) satisfying `(J1)`–`(J7)` with `θ` replaced by `θ'`, such that every `B ∈ 𝒜''` with
`Disjoint (D'' B) Δ` belongs to `𝒜'`. -/
theorem exists_augmented_system_8_3
    {q δ h θ θ' : ℕ}
    {ιV : S ↪ α} {ιE : Set S ↪ β}
    {R_G : RootedDigraph α β q} {W : Set α}
    {Γ C₀ : Drawing S} {r₀ : Set S} {orient : GM19.SurfaceOrientation S}
    {PiSet : Set S}
    {ord : ℕ} {T : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    {d : Set S → Set S → ℕ}
    {J : Graph α β} {Z : Set α} {𝒜 : Set (Graph α β)}
    {πLen : Graph α β → ℕ} {πA : ∀ A : Graph α β, Fin (πLen A) → α}
    {vA : Graph α β → S} {D_disc : Set S} {v_star : S}
    (h83 : Hypotheses83 q δ h θ ιV ιE R_G W Γ C₀ r₀ orient PiSet ord T d J Z 𝒜
      πLen πA vA D_disc v_star)
    (hθ'4 : 4 ≤ θ')
    (hθ_bound : 2 * θ' + h + 13 ≤ θ)
    {Δ₀ : Set S} (hΔ₀ : IsClosedDisc Δ₀) (hΓ_Δ₀ : Γ.U ⊆ Δ₀)
    (hbd_Δ₀_Pi : subBd Δ₀ ∩ Γ.U = PiSet) (hcompl_r₀ : Set.univ \ Δ₀ ⊆ r₀)
    (h_disc_compl : IsClosedDisc (Set.univ \ r₀)) (h_bd_compl : discBd (Set.univ \ r₀) = C₀.U)
    {α_map : α → S} {D₀ : Graph α β → Set S}
    (hα_Δ₀ : α_map '' Z ⊆ Δ₀)
    (hα_Pi : ∀ p ∈ PiSet, α_map (ιV p) = p)
    (hα_ΓV : ∀ v ∈ Γ.V, ιV v ∈ Z → α_map (ιV v) = v)
    (hα_ΓU : ∀ v ∈ Z, α_map v ∈ Γ.U ↔ v ∈ ιV '' Γ.V)
    (hinj : InjOn α_map Z)
    (hD₀ : ∀ A ∈ 𝒜, IsClosedDisc (D₀ A) ∧ D₀ A ⊆ Δ₀)
    (hD₀_norm_bd : ∀ A ∈ 𝒜, subBd (D₀ A) ∩ Γ.U ⊆ Γ.V ∧ subBd (D₀ A) ∩ subBd Δ₀ ⊆ PiSet)
    (hα_bdA : ∀ A ∈ 𝒜, ∀ v ∈ Set.range (πA A), α_map v ∈ subBd (D₀ A))
    (hα_inA : ∀ v ∈ Z, ∀ A ∈ 𝒜, α_map v ∈ D₀ A → v ∈ Set.range (πA A))
    (hD₀_props : ∀ A ∈ 𝒜,
      subBd (D₀ A) ∩ Γ.U = {v ∈ Γ.V | ιV v ∈ Set.range (πA A)} ∧
      subBd (D₀ A) ∩ Γ.V = {v ∈ Γ.V | ιV v ∈ Set.range (πA A)} ∧
      (Γ.interSet (D₀ A)).V = {v ∈ Γ.V | ιV v ∈ V(A)} ∧
      (Γ.interSet (D₀ A)).E = {e ∈ Γ.E | ιE e ∈ E(A)} ∧
      (Γ.interSet (D₀ A)).toEmbeddedGraph ιV ιE = (Γ.toEmbeddedGraph ιV ιE) ⊓ A)
    (hD₀_inter : ∀ A ∈ 𝒜, ∀ A' ∈ 𝒜, A ≠ A' →
      D₀ A ∩ D₀ A' = α_map '' (Set.range (πA A) ∩ Set.range (πA A')))
    (hD₀_bdΔ₀ : ∀ A ∈ 𝒜,
      D₀ A ∩ subBd Δ₀ = α_map '' (Set.range (πA A) ∩ (ιV '' PiSet)))
    {Δ : Set S} (hΔ_disc : IsClosedDisc Δ) (hΔ_bd : subBd Δ ⊆ Γ.U)
    (hv_star_not_Δ : v_star ∉ Δ)
    (hc9_near : ∀ x ∈ Γ.A, ¬ (x ⊆ Δ \ subBd Δ) → d {v_star} x ≤ θ' + 2) :
    let 𝒜' := {A ∈ 𝒜 | 5 ≤ subsetTangleDist Γ ord d {vA A} C₀.V}
    ∃ (ιV' : S ↪ α) (𝒜'' : Set (Graph α β)) (πLen'' : Graph α β → ℕ)
      (πS'' : ∀ B : Graph α β, Fin (πLen'' B) → S)
      (D'' : Graph α β → Set S) (ins : Set S → Set S)
      (N K : Graph α β),
      (∀ s ∈ Γ.V, ιV' s = ιV s) ∧
      𝒜' ⊆ 𝒜'' ∧
      (∀ B ∈ 𝒜'', Disjoint (D'' B) Δ → B ∈ 𝒜') ∧
      (∀ A ∈ 𝒜', D'' A = D₀ A ∧ ∃ hlen : πLen'' A = πLen A,
        ∀ i : Fin (πLen A), ιV' (πS'' A (Fin.cast hlen.symm i)) = πA A i) ∧
      ConditionJ7 ιV' ιE R_G.G.toGraph W 𝒜'' πLen'' πS'' Γ T ∧
      ∀ {αH : Type u₁} {βH : Type v₁} (R_H : RootedDigraph αH βH q)
        (φV : αH → Graph α β) (φE : βH → β),
        R_H.HasDetailLE δ →
        IsRootedDigraphModel R_G R_H φV φE →
        SystemJ1ToJ6 ιV' ιE R_G W 𝒜'' πLen'' πS'' Γ orient θ' ord T ins d D'' N K Δ
          v_star δ R_H φV φE := by
  intro 𝒜'
  obtain ⟨hS, hConn⟩ := GM11.IsSphere.isClosedSurface h83.hyp_i.1
  let : ConnectedSpace S := hConn
  have hθ_ord : θ ≤ ord := h83.hyp_iv.1
  have hord5 : 5 ≤ ord := by omega
  have hord4 : 4 ≤ ord := by omega
  have hD₀_disc : ∀ A ∈ 𝒜, IsClosedDisc (D₀ A) := fun A hA => (hD₀ A hA).1
  have hD₀_norm : ∀ A ∈ 𝒜, subBd (D₀ A) ∩ Γ.U ⊆ Γ.V := fun A hA => (hD₀_norm_bd A hA).1
  have hD₀_bdV : ∀ A ∈ 𝒜, subBd (D₀ A) ∩ Γ.V = {v ∈ Γ.V | ιV v ∈ Set.range (πA A)} :=
    fun A hA => (hD₀_props A hA).2.1
  have hD₀_interV : ∀ A ∈ 𝒜, (Γ.interSet (D₀ A)).V = {v ∈ Γ.V | ιV v ∈ V(A)} :=
    fun A hA => (hD₀_props A hA).2.2.1
  -- Claims 4, 5, 6, 8, 10, 11.
  have h_compl_r₀_sub : Set.univ \ r₀ ⊆ Δ₀ := by
    intro x hx
    by_contra hx_not
    exact hx.2 (hcompl_r₀ ⟨mem_univ x, hx_not⟩)
  have hc4 : ∀ A ∈ 𝒜, EnumeratesClockwise orient (D₀ A) (α_map ∘ πA A) :=
    lemma_8_3_claim_4 h83 hΔ₀ h_compl_r₀_sub hbd_Δ₀_Pi h_disc_compl h_bd_compl
      hα_Δ₀ hα_Pi hinj hD₀ hα_bdA hα_inA hD₀_inter hD₀_bdΔ₀
  have hc5 : ∀ A ∈ 𝒜, IsTangleIns Γ T (subBd (D₀ A)) (D₀ A) :=
    fun A hA => (lemma_8_3_claim_5 h83 hord4 hΔ₀ hbd_Δ₀_Pi hD₀ hD₀_norm hD₀_bdV A hA).1
  have hc6 : ∀ A ∈ 𝒜, ∃ r ∈ Γ.R, vA A ∈ subBd r ∧ (r ∩ D₀ A).Nonempty :=
    lemma_8_3_claim_6 h83 hord4 hΔ₀ hbd_Δ₀_Pi hα_ΓV hα_ΓU hinj hD₀ hD₀_norm hα_bdA hD₀_props
  obtain ⟨K₀, hsep_K₀, hinter_K₀⟩ := exists_separation_J_K₀_8_3 h83
  obtain ⟨hc10, _⟩ := lemma_8_3_claim_10 h83 (by omega) hc9_near
  have hα_bdA_ex : ∀ A ∈ 𝒜, ∀ v ∈ Set.range (πA A), ∃ p ∈ subBd (D₀ A),
      ∀ A' ∈ 𝒜, v ∈ Set.range (πA A') → p ∈ subBd (D₀ A') :=
    fun A hA v hv => ⟨α_map v, hα_bdA A hA v hv, fun A' hA' hv' => hα_bdA A' hA' v hv'⟩
  obtain ⟨hc8_sep, hc8_W, _, _⟩ :=
    lemma_8_3_claim_8 h83 hord5 hΔ₀ hcompl_r₀ hD₀_disc hD₀_norm hD₀_bdV hD₀_interV hc5 hc6
      hsep_K₀ hinter_K₀
  obtain ⟨hc11_v, hc11_A⟩ :=
    lemma_8_3_claim_11 h83 hord5 (by omega) hΔ₀ hcompl_r₀ hD₀_disc hD₀_norm hα_bdA_ex
      hD₀_bdV hD₀_interV hc5 hc6 hsep_K₀ hinter_K₀ hc10
  -- Adjusted embedding `ιV'`.
  obtain ⟨ιV', hf_ΓV, hf_Z, hf_mem_VG⟩ :=
    exists_adjusted_embedding_8_3 h83 (fun v hv v' hv' hne heq => hne (hinj hv hv' heq))
      hα_ΓU hα_ΓV
  have hΓ_emb_eq : Γ.toEmbeddedGraph ιV' ιE = Γ.toEmbeddedGraph ιV ιE :=
    toEmbeddedGraph_congr_of_eq_on_V hf_ΓV
  let πS₀ : ∀ A : Graph α β, Fin (πLen A) → S := fun A i => α_map (πA A i)
  have hπ_eq_Z : ∀ A ∈ 𝒜, Set.range (πA A) = Z ∩ V(A) :=
    fun A hA => (h83.hyp_vii A hA).2.2
  have hπS₀_eq : ∀ A ∈ 𝒜, ∀ i : Fin (πLen A), ιV' (πS₀ A i) = πA A i := by
    intro A hA i
    have hiZ : πA A i ∈ Z := ((hπ_eq_Z A hA).subset ⟨i, rfl⟩).1
    exact hf_Z (πA A i) hiZ
  have hπS₀_inj : ∀ A ∈ 𝒜, Function.Injective (πS₀ A) := by
    intro A hA i j heq
    have hiZ : πA A i ∈ Z := ((hπ_eq_Z A hA).subset ⟨i, rfl⟩).1
    have hjZ : πA A j ∈ Z := ((hπ_eq_Z A hA).subset ⟨j, rfl⟩).1
    exact (h83.hyp_vii A hA).2.1 (hinj hiZ hjZ heq)
  have hD₀_bdV_πS₀ : ∀ A ∈ 𝒜, subBd (D₀ A) ∩ Γ.V = Set.range (πS₀ A) ∩ Γ.V := by
    intro A hA
    rw [hD₀_bdV A hA]
    ext v
    simp only [mem_ofPred_eq, mem_inter_iff, mem_range]
    constructor
    · rintro ⟨hvV, i, hi⟩
      have hvZ : ιV v ∈ Z := ((hπ_eq_Z A hA).subset ⟨i, hi⟩).1
      refine ⟨⟨i, ?_⟩, hvV⟩
      change α_map (πA A i) = v
      rw [hi, hα_ΓV v hvV hvZ]
    · rintro ⟨⟨i, rfl⟩, hvV⟩
      have hiZ : πA A i ∈ Z := ((hπ_eq_Z A hA).subset ⟨i, rfl⟩).1
      obtain ⟨w, hwV, hw_eq⟩ := (hα_ΓU (πA A i) hiZ).mp (Γ.V_subset_U hvV)
      have hα_eq : πS₀ A i = w := by
        change α_map (πA A i) = w
        rw [← hw_eq, hα_ΓV w hwV (hw_eq ▸ hiZ)]
      exact ⟨hvV, i, hα_eq ▸ hw_eq.symm⟩
  have hD₀_inter_emb' : ∀ A ∈ 𝒜,
      (Γ.interSet (D₀ A)).toEmbeddedGraph ιV' ιE = (Γ.toEmbeddedGraph ιV' ιE) ⊓ A := by
    intro A hA
    have hsub_V : (Γ.interSet (D₀ A)).V ⊆ Γ.V := GM11.interSet_isSub.1
    rw [toEmbeddedGraph_congr_of_eq_on_V (fun s hs => hf_ΓV s (hsub_V hs)), hΓ_emb_eq]
    exact (hD₀_props A hA).2.2.2.2
  have hJ7_𝒜' : ConditionJ7 ιV' ιE R_G.G.toGraph W 𝒜' πLen πS₀ Γ T :=
    conditionJ7_8_3 h83 hord4 hf_ΓV hπS₀_eq hπS₀_inj hD₀_disc hD₀_norm hD₀_bdV_πS₀
      hD₀_inter_emb' hc5
  -- Construct edge-discs `Q e` and edge-pieces `B_e` for `e ∈ E_rem`.
  let E_rem : Set (Set S) := {e ∈ Γ.E | ∀ A ∈ 𝒜', ιE e ∉ E(A)}
  obtain ⟨u_end, v_end, Q, hQe_spec, hQQ_inter⟩ :=
    exists_edge_rem_discs_8_3 h83 hΔ₀ hΓ_Δ₀ hbd_Δ₀_Pi hα_ΓV hα_ΓU hD₀ hD₀_norm hα_bdA hD₀_props
  let B_piece : ∀ e ∈ E_rem, Graph α β := fun e he =>
    edgePieceSubgraph W ιV ιE Γ e (u_end e) (v_end e) (hQe_spec e he).2.2.2.1
  let B_set : Set (Graph α β) := {B | ∃ e, ∃ he : e ∈ E_rem, B = B_piece e he}
  let 𝒜'' : Set (Graph α β) := 𝒜' ∪ B_set
  have hBe_props : ∀ e (he : e ∈ E_rem),
      B_piece e he ≤ graphUnion (Γ.toEmbeddedGraph ιV' ιE) (Graph.noEdge W β) ∧
      B_piece e he ≤ R_G.G.toGraph ∧
      V(B_piece e he) = {ιV' (u_end e), ιV' (v_end e)} ∪ W ∧
      E(B_piece e he) = {ιE e} ∧
      (Γ.interSet (Q e)).toEmbeddedGraph ιV' ιE =
        (Γ.toEmbeddedGraph ιV' ιE) ⊓ B_piece e he ∧
      IsGraphPathWithEnds ((Γ.toEmbeddedGraph ιV' ιE) ⊓ B_piece e he)
        ((Γ.toEmbeddedGraph ιV' ιE) ⊓ B_piece e he) (ιV' (u_end e)) (ιV' (v_end e)) ∧
      (∀ x ∈ ({ιV' (u_end e), ιV' (v_end e)} : Set α),
        ∀ y ∈ ({ιV' (u_end e), ιV' (v_end e)} : Set α),
        ∃ P : Graph α β, IsGraphPathWithEnds ((B_piece e he).deleteVerts W) P x y ∧
          Disjoint (pathInternalVerts ((B_piece e he).deleteVerts W) P)
            {ιV' (u_end e), ιV' (v_end e)}) ∧
      (¬ ∃ (C D : Graph α β) (C_Γ D_Γ : Hypergraph S (Set S)),
        IsGraphSeparation (R_G.G.toGraph.deleteVerts W) C D ∧
        (V(C) ∩ V(D)).ncard < 2 ∧
        (B_piece e he).deleteVerts W ≤ C ∧
        C_Γ.vertexSet = ιV' ⁻¹' V(C) ∩ Γ.V ∧ C_Γ.edgeSet = ιE ⁻¹' E(C) ∩ Γ.E ∧
        D_Γ.vertexSet = ιV' ⁻¹' V(D) ∩ Γ.V ∧ D_Γ.edgeSet = ιE ⁻¹' E(D) ∩ Γ.E ∧
        (C_Γ, D_Γ) ∈ T) ∧
      θ' ≤ subsetTangleDist Γ ord d (Q e) (Set.univ \ Δ) ∧
      ¬ Disjoint (Q e) Δ := by
    intro e he
    obtain ⟨huv, huV, hvV, hlk, _, ⟨A₀, ⟨hA₀, hA₀_not'⟩, _, _, _, hu_D₀⟩,
      hQe_disc, hQe_sub, hQe_bdU, hQe_bdV, _, _, hQe_interV, hQe_interE, _⟩ := hQe_spec e he
    rw [hf_ΓV (u_end e) huV, hf_ΓV (v_end e) hvV]
    have hprops := edge_piece_props_8_3 h83 hθ'4 (by omega) hf_ΓV hΔ₀ hbd_Δ₀_Pi hcompl_r₀
      hD₀_disc hD₀_norm hD₀_bdV hD₀_interV hc5 hc6 hc10 huv huV hvV hlk
      hA₀ (fun h5 => hA₀_not' ⟨hA₀, h5⟩) hu_D₀ hQe_disc hQe_sub hQe_bdU hQe_bdV hQe_interV hQe_interE
    rwa [← hΓ_emb_eq] at hprops
  -- Disjointness of `𝒜'` and `B_set`, and injectivity of `B_piece`.
  have hB_not_𝒜' : ∀ e (he : e ∈ E_rem), B_piece e he ∉ 𝒜' := by
    intro e he hmem
    have he_in : ιE e ∈ E(B_piece e he) := by
      rw [(hBe_props e he).2.2.2.1]
      exact rfl
    exact he.2 (B_piece e he) hmem he_in
  have hB_inj : ∀ e₁ (he₁ : e₁ ∈ E_rem) e₂ (he₂ : e₂ ∈ E_rem),
      B_piece e₁ he₁ = B_piece e₂ he₂ → e₁ = e₂ := by
    intro e₁ he₁ e₂ he₂ heq
    have hE_eq : E(B_piece e₁ he₁) = E(B_piece e₂ he₂) := congrArg Graph.edgeSet heq
    rw [(hBe_props e₁ he₁).2.2.2.1, (hBe_props e₂ he₂).2.2.2.1, singleton_eq_singleton_iff] at hE_eq
    exact ιE.injective hE_eq
  -- Define `D''`, `πLen''`, `πS''`.
  let pieceEnd (e : Set S) (n : ℕ) : S := if n = 0 then u_end e else v_end e
  let D'' (B : Graph α β) : Set S :=
    if h : ∃ e, ∃ he : e ∈ E_rem, B = B_piece e he then Q (Classical.choose h) else D₀ B
  let πLen'' (B : Graph α β) : ℕ :=
    if ∃ e, ∃ he : e ∈ E_rem, B = B_piece e he then 2 else πLen B
  let πS'' (B : Graph α β) (i : Fin (πLen'' B)) : S :=
    if h : ∃ e, ∃ he : e ∈ E_rem, B = B_piece e he then
      pieceEnd (Classical.choose h) (i : ℕ)
    else
      πS₀ B (Fin.cast (by dsimp only [πLen'']; split_ifs; rfl) i)
  have h_not_B_of_𝒜' : ∀ A ∈ 𝒜', ¬ ∃ e, ∃ he : e ∈ E_rem, A = B_piece e he := by
    rintro A hA' ⟨e, he, rfl⟩
    exact hB_not_𝒜' e he hA'
  have hD''_𝒜' : ∀ A ∈ 𝒜', D'' A = D₀ A := by
    intro A hA'
    dsimp only [D'']
    split_ifs with h
    · exact False.elim (h_not_B_of_𝒜' A hA' h)
    · rfl
  have hπLen''_𝒜' : ∀ A ∈ 𝒜', πLen'' A = πLen A := by
    intro A hA'
    dsimp only [πLen'']
    split_ifs with h
    · exact False.elim (h_not_B_of_𝒜' A hA' h)
    · rfl
  have hπS''_𝒜'_eq : ∀ A (hA' : A ∈ 𝒜') (i : Fin (πLen'' A)),
      πS'' A i = πS₀ A (Fin.cast (hπLen''_𝒜' A hA') i) := by
    intro A hA' i
    dsimp only [πS'']
    split_ifs with h
    · exact False.elim (h_not_B_of_𝒜' A hA' h)
    · rfl
  have hπS''_𝒜'_range : ∀ A ∈ 𝒜', Set.range (πS'' A) = Set.range (πS₀ A) := by
    intro A hA'
    ext s
    simp only [mem_range]
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨Fin.cast (hπLen''_𝒜' A hA') i, (hπS''_𝒜'_eq A hA' i).symm⟩
    · rintro ⟨j, rfl⟩
      exact ⟨Fin.cast (hπLen''_𝒜' A hA').symm j, by simp [hπS''_𝒜'_eq A hA']⟩
  have hD''_B : ∀ e (he : e ∈ E_rem), D'' (B_piece e he) = Q e := by
    intro e he
    dsimp only [D'']
    split_ifs with hex
    · obtain ⟨he', heq⟩ := Classical.choose_spec hex
      rw [hB_inj _ he' e he heq.symm]
    · exact False.elim (hex ⟨e, he, rfl⟩)
  have hπLen''_B : ∀ e (he : e ∈ E_rem), πLen'' (B_piece e he) = 2 := by
    intro e he
    dsimp only [πLen'']
    split_ifs with hex
    · rfl
    · exact False.elim (hex ⟨e, he, rfl⟩)
  have hπS''_B_val : ∀ e (he : e ∈ E_rem) (i : Fin (πLen'' (B_piece e he))),
      πS'' (B_piece e he) i = if (i : ℕ) = 0 then u_end e else v_end e := by
    intro e he i
    change πS'' (B_piece e he) i = pieceEnd e (i : ℕ)
    dsimp only [πS'']
    split_ifs with hex
    · obtain ⟨he', heq⟩ := Classical.choose_spec hex
      rw [hB_inj _ he' e he heq.symm]
    · exact False.elim (hex ⟨e, he, rfl⟩)
  have hπS''_B_range : ∀ e (he : e ∈ E_rem),
      Set.range (πS'' (B_piece e he)) = {u_end e, v_end e} := by
    intro e he
    ext s
    simp only [mem_range, mem_insert_iff, mem_singleton_iff]
    constructor
    · rintro ⟨i, rfl⟩
      rw [hπS''_B_val e he i]
      split_ifs <;> [exact Or.inl rfl; exact Or.inr rfl]
    · rintro (rfl | rfl)
      · refine ⟨⟨0, by rw [hπLen''_B e he]; omega⟩, ?_⟩
        rw [hπS''_B_val e he]
        rfl
      · refine ⟨⟨1, by rw [hπLen''_B e he]; omega⟩, ?_⟩
        rw [hπS''_B_val e he]
        simp
  have hπS''_B_inj : ∀ e (he : e ∈ E_rem), Function.Injective (πS'' (B_piece e he)) := by
    intro e he i j hij
    rw [hπS''_B_val e he i, hπS''_B_val e he j] at hij
    have hi_lt : (i : ℕ) < 2 := i.2.trans_eq (hπLen''_B e he)
    have hj_lt : (j : ℕ) < 2 := j.2.trans_eq (hπLen''_B e he)
    have huv : u_end e ≠ v_end e := (hQe_spec e he).1
    ext
    split_ifs at hij with hi0 hj0 hj0
    · omega
    · exact False.elim (huv hij)
    · exact False.elim (huv hij.symm)
    · omega
  -- Disc properties for all `B ∈ 𝒜''`.
  have hD''_disc_norm_ins : ∀ B ∈ 𝒜'',
      IsClosedDisc (D'' B) ∧ Γ.IsNormal (subBd (D'' B)) ∧
      Set.range (πS'' B) = subBd (D'' B) ∩ (ιV' ⁻¹' V(R_G.G.toGraph)) ∧
      IsTangleIns Γ T (subBd (D'' B)) (D'' B) := by
    rintro B (hB' | ⟨e, he, rfl⟩)
    · rw [hD''_𝒜' B hB', hπS''_𝒜'_range B hB']
      have hB : B ∈ 𝒜 := hB'.1
      refine ⟨hD₀_disc B hB, hD₀_norm B hB, ?_, hc5 B hB⟩
      ext s
      simp only [πS₀, mem_range, mem_inter_iff, mem_preimage, hf_mem_VG]
      constructor
      · rintro ⟨i, rfl⟩
        have hiZ : πA B i ∈ Z := ((hπ_eq_Z B hB).subset ⟨i, rfl⟩).1
        exact ⟨hα_bdA B hB (πA B i) ⟨i, rfl⟩, Or.inr ⟨πA B i, hiZ, rfl⟩⟩
      · rintro ⟨hs_bd, hsV | ⟨z, hzZ, rfl⟩⟩
        · have hs_in : s ∈ subBd (D₀ B) ∩ Γ.V := ⟨hs_bd, hsV⟩
          rw [hD₀_bdV_πS₀ B hB] at hs_in
          exact hs_in.1
        · have hs_D₀ : α_map z ∈ D₀ B :=
            GM14.Whitney.subBd_subset_of subset_rfl (hD₀_disc B hB).isClosed hs_bd
          obtain ⟨i, hi⟩ := hα_inA z hzZ B hB hs_D₀
          exact ⟨i, congrArg α_map hi⟩
    · rw [hD''_B e he, hπS''_B_range e he]
      obtain ⟨huv, _, _, _, _, _, hQe_disc, hQe_sub, hQe_bdU, hQe_bdV, _, hQe_bd_VZ, _, _, _⟩ :=
        hQe_spec e he
      have hQe_norm : Γ.IsNormal (subBd (Q e)) := by
        change subBd (Q e) ∩ Γ.U ⊆ Γ.V
        rw [hQe_bdU, ← hQe_bdV]
        exact inter_subset_right
      have hQe_card : (subBd (Q e) ∩ Γ.V).ncard ≤ 3 := by
        rw [hQe_bdV, Set.ncard_pair huv]
        omega
      obtain ⟨hQe_ins, _⟩ :=
        isTangleIns_of_disc_in_Δ₀_8_3 h83 hord4 hΔ₀ hbd_Δ₀_Pi hQe_disc hQe_sub hQe_norm hQe_card
      have hpre_eq : ιV' ⁻¹' V(R_G.G.toGraph) = Γ.V ∪ (α_map '' Z) := by
        ext s
        exact hf_mem_VG s
      rw [hpre_eq, hQe_bd_VZ]
      exact ⟨hQe_disc, hQe_norm, rfl, hQe_ins⟩
  have hD''_inter_eq : ∀ B₁ ∈ 𝒜'', ∀ B₂ ∈ 𝒜'', B₁ ≠ B₂ →
      D'' B₁ ∩ D'' B₂ = Set.range (πS'' B₁) ∩ Set.range (πS'' B₂) := by
    rintro B₁ (hB₁' | ⟨e₁, he₁, rfl⟩) B₂ (hB₂' | ⟨e₂, he₂, rfl⟩) hne
    · rw [hD''_𝒜' B₁ hB₁', hD''_𝒜' B₂ hB₂', hπS''_𝒜'_range B₁ hB₁', hπS''_𝒜'_range B₂ hB₂']
      rw [hD₀_inter B₁ hB₁'.1 B₂ hB₂'.1 hne]
      ext s
      simp only [πS₀, mem_image, mem_inter_iff, mem_range]
      constructor
      · rintro ⟨z, ⟨⟨i, rfl⟩, ⟨j, hj⟩⟩, rfl⟩
        exact ⟨⟨i, rfl⟩, ⟨j, congrArg α_map hj⟩⟩
      · rintro ⟨⟨i, rfl⟩, ⟨j, hij⟩⟩
        have hiZ : πA B₁ i ∈ Z := ((hπ_eq_Z B₁ hB₁'.1).subset ⟨i, rfl⟩).1
        have hjZ : πA B₂ j ∈ Z := ((hπ_eq_Z B₂ hB₂'.1).subset ⟨j, rfl⟩).1
        have heq := hinj hjZ hiZ hij
        exact ⟨πA B₁ i, ⟨⟨i, rfl⟩, ⟨j, heq⟩⟩, rfl⟩
    · rw [hD''_𝒜' B₁ hB₁', hD''_B e₂ he₂, hπS''_𝒜'_range B₁ hB₁', hπS''_B_range e₂ he₂]
      rw [Set.inter_comm, (hQe_spec e₂ he₂).2.2.2.2.2.2.2.2.2.2.2.2.2.2 B₁ hB₁', Set.inter_comm]
      have hcomp : α_map '' Set.range (πA B₁) = Set.range (πS₀ B₁) :=
        (Set.range_comp α_map (πA B₁)).symm
      rw [hcomp]
    · rw [hD''_B e₁ he₁, hD''_𝒜' B₂ hB₂', hπS''_B_range e₁ he₁, hπS''_𝒜'_range B₂ hB₂']
      rw [(hQe_spec e₁ he₁).2.2.2.2.2.2.2.2.2.2.2.2.2.2 B₂ hB₂']
      have hcomp : α_map '' Set.range (πA B₂) = Set.range (πS₀ B₂) :=
        (Set.range_comp α_map (πA B₂)).symm
      rw [hcomp]
    · rw [hD''_B e₁ he₁, hD''_B e₂ he₂, hπS''_B_range e₁ he₁, hπS''_B_range e₂ he₂]
      have he_ne : e₁ ≠ e₂ := by
        rintro rfl
        exact hne rfl
      exact hQQ_inter e₁ he₁ e₂ he₂ he_ne
  -- Define `ins : Set S → Set S`.
  let ins (F : Set S) : Set S :=
    if h : ∃ B ∈ 𝒜'', F = subBd (D'' B) then D'' (Classical.choose h)
    else if h' : ∃ Δ_F, IsTangleIns Γ T F Δ_F then Classical.choose h'
    else ∅
  have hsubBd_inj_𝒜'' : ∀ B₁ ∈ 𝒜'', ∀ B₂ ∈ 𝒜'', subBd (D'' B₁) = subBd (D'' B₂) → B₁ = B₂ := by
    intro B₁ hB₁ B₂ hB₂ hbd_eq
    by_contra hne
    have hsub_inter : subBd (D'' B₁) ⊆ D'' B₁ ∩ D'' B₂ := by
      refine subset_inter
        (GM14.Whitney.subBd_subset_of subset_rfl (hD''_disc_norm_ins B₁ hB₁).1.isClosed) ?_
      rw [hbd_eq]
      exact GM14.Whitney.subBd_subset_of subset_rfl (hD''_disc_norm_ins B₂ hB₂).1.isClosed
    rw [hD''_inter_eq B₁ hB₁ B₂ hB₂ hne] at hsub_inter
    have hfin : (subBd (D'' B₁)).Finite :=
      (Set.finite_range (πS'' B₁)).subset (hsub_inter.trans inter_subset_left)
    exact isClosedDisc_infinite_subBd hS (hD''_disc_norm_ins B₁ hB₁).1 hfin
  have hins_D'' : ∀ B ∈ 𝒜'', D'' B = ins (subBd (D'' B)) := by
    intro B hB
    dsimp only [ins]
    split_ifs with hex
    · obtain ⟨hB', hbd_eq⟩ := Classical.choose_spec hex
      rw [hsubBd_inj_𝒜'' _ hB' B hB hbd_eq.symm]
    · exact False.elim (hex ⟨B, hB, rfl⟩)
    · exact False.elim (hex ⟨B, hB, rfl⟩)
  have hins_spec : ∀ F : Set S, IsOArc F → Γ.IsNormal F → (F ∩ Γ.V).ncard < ord →
      IsTangleIns Γ T F (ins F) := by
    intro F hOArc hNorm hlt
    dsimp only [ins]
    split_ifs with hex hex'
    · obtain ⟨hB, hF_eq⟩ := Classical.choose_spec hex
      have h1 := (hD''_disc_norm_ins _ hB).2.2.2
      exact Eq.mp (congrArg (fun X => IsTangleIns Γ T X (D'' (Classical.choose hex))) hF_eq.symm) h1
    · exact Classical.choose_spec hex'
    · exact False.elim (hex' (h83.hyp_iv.2.1.1.2.2.2 F hOArc hNorm hlt))
  -- Define `N` and `K`.
  let G := R_G.G.toGraph
  let Γ_emb := Γ.toEmbeddedGraph ιV ιE
  let N := graphUnion (graphUnion (Γ.toEmbeddedGraph ιV' ιE) (Graph.noEdge W β))
    (subgraphSUnion G 𝒜'')
  let remPiece (A : Graph α β) : Graph α β := A.deleteEdges E(Γ_emb ⊓ A)
  let K := graphUnion K₀ (subgraphSUnion G (remPiece '' (𝒜 \ 𝒜')))
  have hZdiv : IsZDivision J (Z ∪ W) 𝒜 := h83.hyp_vi.2.2.1
  have hA_le_G : ∀ A ∈ 𝒜, A ≤ G := fun A hA => (hZdiv.2.1 A hA).trans h83.hyp_v.1
  have hB_le_G : ∀ B ∈ 𝒜'', B ≤ G := by
    rintro B (hB' | ⟨e, he, rfl⟩)
    · exact hA_le_G B hB'.1
    · exact (hBe_props e he).2.1
  have hN_eq_N₀ : N = graphUnion (graphUnion Γ_emb (Graph.noEdge W β)) (subgraphSUnion G 𝒜') := by
    have hΓ_le_G : Γ_emb ≤ G := h83.Γ_le.trans Graph.deleteVerts_le
    have hNW_le_G : Graph.noEdge W β ≤ G := ⟨h83.ordering_W.1, fun _ _ _ h => h.elim⟩
    have h1_le : N ≤ G := by
      refine graphUnion_le (graphUnion_le ?_ hNW_le_G) (subgraphSUnion_le hB_le_G)
      rwa [hΓ_emb_eq]
    have h2_le : graphUnion (graphUnion Γ_emb (Graph.noEdge W β)) (subgraphSUnion G 𝒜') ≤ G :=
      graphUnion_le (graphUnion_le hΓ_le_G hNW_le_G)
        (subgraphSUnion_le (fun A hA => hA_le_G A hA.1))
    have hV_eq : V(N) =
        V(graphUnion (graphUnion Γ_emb (Graph.noEdge W β)) (subgraphSUnion G 𝒜')) := by
      change V(graphUnion (graphUnion (Γ.toEmbeddedGraph ιV' ιE) (Graph.noEdge W β))
        (subgraphSUnion G 𝒜'')) =
        V(graphUnion (graphUnion Γ_emb (Graph.noEdge W β)) (subgraphSUnion G 𝒜'))
      simp only [hΓ_emb_eq, vertexSet_graphUnion, vertexSet_subgraphSUnion]
      apply Subset.antisymm
      · rintro x (hx1 | hx2)
        · exact Or.inl hx1
        · obtain ⟨B, hB' | ⟨e, he, rfl⟩, hxB⟩ := mem_iUnion₂.mp hx2
          · exact Or.inr (mem_iUnion₂.mpr ⟨B, hB', hxB⟩)
          · have hx_in := (hBe_props e he).1.vertexSet_mono hxB
            rw [hΓ_emb_eq, vertexSet_graphUnion] at hx_in
            exact Or.inl hx_in
      · rintro x (hx1 | hx2)
        · exact Or.inl hx1
        · obtain ⟨A, hA', hxA⟩ := mem_iUnion₂.mp hx2
          exact Or.inr (mem_iUnion₂.mpr ⟨A, Or.inl hA', hxA⟩)
    have hE_eq : E(N) =
        E(graphUnion (graphUnion Γ_emb (Graph.noEdge W β)) (subgraphSUnion G 𝒜')) := by
      change E(graphUnion (graphUnion (Γ.toEmbeddedGraph ιV' ιE) (Graph.noEdge W β))
        (subgraphSUnion G 𝒜'')) =
        E(graphUnion (graphUnion Γ_emb (Graph.noEdge W β)) (subgraphSUnion G 𝒜'))
      simp only [hΓ_emb_eq, edgeSet_graphUnion, edgeSet_subgraphSUnion hB_le_G,
        edgeSet_subgraphSUnion (fun A (hA : A ∈ 𝒜') => hA_le_G A hA.1)]
      apply Subset.antisymm
      · rintro g (hg1 | hg2)
        · exact Or.inl hg1
        · obtain ⟨B, hB' | ⟨e, he, rfl⟩, hgB⟩ := mem_iUnion₂.mp hg2
          · exact Or.inr (mem_iUnion₂.mpr ⟨B, hB', hgB⟩)
          · have hg_in := (hBe_props e he).1.edgeSet_mono hgB
            rw [hΓ_emb_eq, edgeSet_graphUnion] at hg_in
            exact Or.inl hg_in
      · rintro g (hg1 | hg2)
        · exact Or.inl hg1
        · obtain ⟨A, hA', hgA⟩ := mem_iUnion₂.mp hg2
          exact Or.inr (mem_iUnion₂.mpr ⟨A, Or.inl hA', hgA⟩)
    refine Graph.ext hV_eq fun g x y => ?_
    constructor
    · intro hlk
      exact (h2_le.isLink_iff (hE_eq ▸ hlk.edge_mem)).mpr (hlk.mono h1_le)
    · intro hlk
      exact (h1_le.isLink_iff (hE_eq.symm ▸ hlk.edge_mem)).mpr (hlk.mono h2_le)
  -- Vertex and edge coverage: `V(K) ∪ ⋃ B ∈ 𝒜'', V(B) = V(G)` and `E(K) ∪ ⋃ B ∈ 𝒜'', E(B) = E(G)`.
  have hVK_cov : V(K) ∪ ⋃ B ∈ 𝒜'', V(B) = V(G) := by
    have hrem_le_G : ∀ B ∈ remPiece '' (𝒜 \ 𝒜'), B ≤ G := by
      rintro _ ⟨B, hB, rfl⟩
      exact Graph.deleteEdges_le.trans (hA_le_G B hB.1)
    have hK_le_G : K ≤ G := graphUnion_le hsep_K₀.2.1 (subgraphSUnion_le hrem_le_G)
    refine Subset.antisymm
      (union_subset hK_le_G.vertexSet_mono (iUnion₂_subset fun B hB => (hB_le_G B hB).vertexSet_mono)) ?_
    intro x hxG
    have hx_JK₀ : x ∈ V(J) ∪ V(K₀) := hsep_K₀.2.2.1 ▸ hxG
    rcases hx_JK₀ with hxJ | hxK₀
    · have hVJ : V(J) = ⋃ A ∈ 𝒜, V(A) := by
        have := congrArg Graph.vertexSet hZdiv.2.2.1.symm
        rwa [vertexSet_subgraphSUnion] at this
      rw [hVJ] at hxJ
      obtain ⟨A, hA, hxA⟩ := mem_iUnion₂.mp hxJ
      by_cases hA' : A ∈ 𝒜'
      · exact Or.inr (mem_iUnion₂.mpr ⟨A, Or.inl hA', hxA⟩)
      · left
        change x ∈ V(K₀) ∪ V(subgraphSUnion G (remPiece '' (𝒜 \ 𝒜')))
        rw [vertexSet_subgraphSUnion]
        exact Or.inr (mem_iUnion₂.mpr ⟨remPiece A, ⟨A, ⟨hA, hA'⟩, rfl⟩, hxA⟩)
    · exact Or.inl (Or.inl hxK₀)
  have hEK_cov : E(K) ∪ ⋃ B ∈ 𝒜'', E(B) = E(G) := by
    have hrem_le_G : ∀ B ∈ remPiece '' (𝒜 \ 𝒜'), B ≤ G := by
      rintro _ ⟨B, hB, rfl⟩
      exact Graph.deleteEdges_le.trans (hA_le_G B hB.1)
    have hK_le_G : K ≤ G := graphUnion_le hsep_K₀.2.1 (subgraphSUnion_le hrem_le_G)
    refine Subset.antisymm
      (union_subset hK_le_G.edgeSet_mono (iUnion₂_subset fun B hB => (hB_le_G B hB).edgeSet_mono)) ?_
    intro g hgG
    have hg_NK : g ∈ E(N) ∪ E(K) := by
      have hsep_NK' : IsGraphSeparation G N K := hN_eq_N₀ ▸ hc8_sep
      exact hsep_NK'.2.2.2.1 ▸ hgG
    rcases hg_NK with hgN | hgK
    · rw [hN_eq_N₀, edgeSet_graphUnion, edgeSet_graphUnion, Graph.edgeSet_noEdge, union_empty,
        edgeSet_subgraphSUnion (fun A hA => hA_le_G A hA.1)] at hgN
      rcases hgN with ⟨e, heE, rfl⟩ | hg𝒜'
      · by_cases he_rem : e ∈ E_rem
        · right
          refine mem_iUnion₂.mpr ⟨B_piece e he_rem, Or.inr ⟨e, he_rem, rfl⟩, ?_⟩
          rw [(hBe_props e he_rem).2.2.2.1]
          exact rfl
        · obtain ⟨A, hA', heA⟩ : ∃ A ∈ 𝒜', ιE e ∈ E(A) := by
            by_contra! hno
            exact he_rem ⟨heE, hno⟩
          exact Or.inr (mem_iUnion₂.mpr ⟨A, Or.inl hA', heA⟩)
      · obtain ⟨A, hA', hgA⟩ := mem_iUnion₂.mp hg𝒜'
        exact Or.inr (mem_iUnion₂.mpr ⟨A, Or.inl hA', hgA⟩)
    · exact Or.inl hgK
  -- Verify `ConditionJ7` for `𝒜''`.
  have hJ7_𝒜'' : ConditionJ7 ιV' ιE R_G.G.toGraph W 𝒜'' πLen'' πS'' Γ T := by
    refine ⟨?_, ?_, ?_⟩
    · rintro B (hB' | ⟨e, he, rfl⟩) u hu v hv
      · rw [hπS''_𝒜'_range B hB'] at hu hv ⊢
        exact hJ7_𝒜'.1 B hB' u hu v hv
      · rw [hπS''_B_range e he, Set.image_pair] at hu hv ⊢
        exact (hBe_props e he).2.2.2.2.2.2.1 u hu v hv
    · rintro B (hB' | ⟨e, he, rfl⟩)
      · rw [hπLen''_𝒜' B hB']
        exact hJ7_𝒜'.no_small_sep B hB'
      · rw [hπLen''_B e he]
        exact (hBe_props e he).2.2.2.2.2.2.2.1
    · rintro B (hB' | ⟨e, he, rfl⟩)
      · have h3 := hJ7_𝒜'.structure_Γ_inter_A B hB'
        dsimp only at h3 ⊢
        rw [hπS''_𝒜'_range B hB', hπLen''_𝒜' B hB']
        have hGood_iff : IsGoodMember ιV' ιE Γ πLen'' πS'' B ↔ IsGoodMember ιV' ιE Γ πLen πS₀ B := by
          unfold IsGoodMember
          rw [hπS''_𝒜'_range B hB']
        rwa [hGood_iff]
      · dsimp only
        rw [hπS''_B_range e he, Set.image_pair]
        right; left
        exact ⟨ιV' (u_end e), Or.inl rfl, ιV' (v_end e), Or.inr rfl, (hBe_props e he).2.2.2.2.2.1⟩
  -- Assemble the full existential witness.
  refine ⟨ιV', 𝒜'', πLen'', πS'', D'', ins, N, K, hf_ΓV, subset_union_left, ?_, ?_, hJ7_𝒜'', ?_⟩
  · -- `∀ B ∈ 𝒜'', Disjoint (D'' B) Δ → B ∈ 𝒜'`
    rintro B (hB' | ⟨e, he, rfl⟩) hdisj
    · exact hB'
    · rw [hD''_B e he] at hdisj
      exact False.elim ((hBe_props e he).2.2.2.2.2.2.2.2.2 hdisj)
  · -- `∀ A ∈ 𝒜', D'' A = D₀ A ∧ ∃ hlen : πLen'' A = πLen A, ...`
    intro A hA'
    refine ⟨hD''_𝒜' A hA', hπLen''_𝒜' A hA', fun i => ?_⟩
    rw [hπS''_𝒜'_eq A hA']
    have hcast : Fin.cast (hπLen''_𝒜' A hA') (Fin.cast (hπLen''_𝒜' A hA').symm i) = i := by
      ext; rfl
    rw [hcast]
    exact hπS₀_eq A hA'.1 i
  · -- `SystemJ1ToJ6` for any `(R_H, φV, φE)`.
    intro αH βH R_H φV φE hDet hMod
    have hE_rem_fin : E_rem.Finite := Γ.finite_edges.subset fun _ h => h.1
    have hB_set_fin : B_set.Finite := by
      have hsub : B_set ⊆ (fun s : E_rem => B_piece s.1 s.2) '' Set.univ := by
        rintro _ ⟨e, he, rfl⟩
        exact ⟨⟨e, he⟩, mem_univ _, rfl⟩
      have : Finite E_rem := hE_rem_fin.to_subtype
      exact (Set.toFinite _).subset hsub
    have h𝒜''_fin : 𝒜''.Finite := (hZdiv.1.subset fun _ h => h.1).union hB_set_fin
    refine
      { finite_V := h83.finite_V
        finite_E := h83.finite_E
        inj_roots := h83.ordering_W.2.1
        W_eq := h83.ordering_W.2.2.symm
        finite_𝒜 := h𝒜''_fin
        le_of_mem_𝒜 := hB_le_G
        edge_disjoint_𝒜 := ?_
        W_subset_V := ?_
        π_valid := ?_
        vertex_inter_𝒜 := ?_
        isSphere := h83.hyp_i.1
        Γ_le := hΓ_emb_eq ▸ h83.Γ_le
        isTwoCell := h83.hyp_iv.2.1.2.choose_spec.choose_spec.1.1
        four_le_θ := hθ'4
        θ_le_ord := by omega
        hasMetric := h83.hyp_iv.2.1
        ins_spec := hins_spec
        disc_D := fun B hB =>
          ⟨(hD''_disc_norm_ins B hB).1, (hD''_disc_norm_ins B hB).2.1, hins_D'' B hB⟩
        Γ_inter_D := ?_
        π_bar_eq_bd_inter := fun B hB => (hD''_disc_norm_ins B hB).2.2.1
        π_clockwise := ?_
        D_inter_eq := hD''_inter_eq
        N_eq := rfl
        sep_NK := ⟨hN_eq_N₀ ▸ hc8_sep, hN_eq_N₀ ▸ hc8_W⟩
        disc_Δ := ⟨hΔ_disc, hΔ_bd⟩
        dist_Γ_inter_K := fun v hv hvK => hc11_v v hv (hf_ΓV v hv ▸ hvK)
        dist_D_of_inter_K := ?_
        v_star_mem := ⟨h83.hyp_xiv.1.1, hv_star_not_Δ⟩
        detail_H := hDet
        isModel := hMod
        φV_meets := ?_
        φE_mem := ?_ }
    · -- `edge_disjoint_𝒜`
      rintro B₁ (hB₁' | ⟨e₁, he₁, rfl⟩) B₂ (hB₂' | ⟨e₂, he₂, rfl⟩) hne
      · exact (hZdiv.2.2.2 B₁ hB₁'.1 B₂ hB₂'.1 hne).1
      · rw [(hBe_props e₂ he₂).2.2.2.1, Set.disjoint_singleton_right]
        exact he₂.2 B₁ hB₁'
      · rw [(hBe_props e₁ he₁).2.2.2.1, Set.disjoint_singleton_left]
        exact he₁.2 B₂ hB₂'
      · rw [(hBe_props e₁ he₁).2.2.2.1, (hBe_props e₂ he₂).2.2.2.1, Set.disjoint_singleton]
        intro h_eq
        exact hne (by congr 1; exact ιE.injective h_eq)
    · -- `W_subset_V`
      rintro B (hB' | ⟨e, he, rfl⟩)
      · exact h83.hyp_vi.2.2.2 B hB'.1
      · rw [(hBe_props e he).2.2.1]
        exact subset_union_right
    · -- `π_valid`
      rintro B (hB' | ⟨e, he, rfl⟩)
      · have hB : B ∈ 𝒜 := hB'.1
        obtain ⟨_, u_ξ, hu_ξ, _, _, _⟩ := h83.hyp_xi B hB
        obtain ⟨i₀, _⟩ := (hπ_eq_Z B hB).symm ▸ hu_ξ
        have hpos : 1 ≤ πLen'' B := by rw [hπLen''_𝒜' B hB']; exact Nat.succ_le_of_lt i₀.pos
        have hle3 : πLen'' B ≤ 3 := by rw [hπLen''_𝒜' B hB']; exact (h83.hyp_vii B hB).1
        refine ⟨hpos, hle3, ?_, ?_⟩
        · intro i j hij
          rw [hπS''_𝒜'_eq B hB' i, hπS''_𝒜'_eq B hB' j] at hij
          exact Fin.cast_injective _ (hπS₀_inj B hB hij)
        · intro i
          rw [hπS''_𝒜'_eq B hB' i, hπS₀_eq B hB]
          have hmem : πA B (Fin.cast (hπLen''_𝒜' B hB') i) ∈ Z ∩ V(B) :=
            (hπ_eq_Z B hB).subset ⟨_, rfl⟩
          exact ⟨hmem.2, (h83.hyp_vi.1 hmem.1).2⟩
      · refine ⟨by rw [hπLen''_B e he]; omega, by rw [hπLen''_B e he]; omega, hπS''_B_inj e he, ?_⟩
        intro i
        have hs_mem : πS'' (B_piece e he) i ∈ ({u_end e, v_end e} : Set S) := by
          rw [← hπS''_B_range e he]
          exact ⟨i, rfl⟩
        have hsV : πS'' (B_piece e he) i ∈ Γ.V := by
          rcases hs_mem with h1 | h2
          · exact h1 ▸ (hQe_spec e he).2.1
          · exact (mem_singleton_iff.mp h2) ▸ (hQe_spec e he).2.2.1
        have hnotW : ιV' (πS'' (B_piece e he) i) ∉ W := by
          rw [hf_ΓV _ hsV]
          have hdel := h83.Γ_le.vertexSet_mono ⟨_, hsV, rfl⟩
          rw [Graph.vertexSet_deleteVerts] at hdel
          exact hdel.2
        rw [(hBe_props e he).2.2.1]
        refine ⟨Or.inl ?_, hnotW⟩
        rcases hs_mem with h1 | h2
        · exact Or.inl (congrArg ιV' h1)
        · exact Or.inr (congrArg ιV' (mem_singleton_iff.mp h2))
    · -- `vertex_inter_𝒜`
      have h_img_range : ∀ B ∈ 𝒜', ιV' '' Set.range (πS'' B) = Z ∩ V(B) := by
        intro B hB'
        rw [hπS''_𝒜'_range B hB', ← hπ_eq_Z B hB'.1]
        ext x
        simp only [mem_image, mem_range]
        constructor
        · rintro ⟨s, ⟨i, rfl⟩, rfl⟩
          exact ⟨i, (hπS₀_eq B hB'.1 i).symm⟩
        · rintro ⟨i, rfl⟩
          exact ⟨πS₀ B i, ⟨i, rfl⟩, hπS₀_eq B hB'.1 i⟩
      rintro B₁ (hB₁' | ⟨e₁, he₁, rfl⟩) B₂ (hB₂' | ⟨e₂, he₂, rfl⟩) hne
      · rw [h_img_range B₁ hB₁', h_img_range B₂ hB₂']
        apply Subset.antisymm
        · intro x ⟨hx₁, hx₂⟩
          rcases (hZdiv.2.2.2 B₁ hB₁'.1 B₂ hB₂'.1 hne).2 ⟨hx₁, hx₂⟩ with hxZ | hxW
          · exact Or.inl ⟨⟨hxZ, hx₁⟩, ⟨hxZ, hx₂⟩⟩
          · exact Or.inr hxW
        · rintro x (⟨⟨_, hx₁⟩, ⟨_, hx₂⟩⟩ | hxW)
          · exact ⟨hx₁, hx₂⟩
          · exact ⟨h83.hyp_vi.2.2.2 B₁ hB₁'.1 hxW, h83.hyp_vi.2.2.2 B₂ hB₂'.1 hxW⟩
      · rw [h_img_range B₁ hB₁', hπS''_B_range e₂ he₂, Set.image_pair, (hBe_props e₂ he₂).2.2.1]
        apply Subset.antisymm
        · rintro x ⟨hx₁, hx₂ | hxW⟩
          · left
            refine ⟨?_, hx₂⟩
            have hex_s : ∃ s ∈ ({u_end e₂, v_end e₂} : Set S), ιV' s = x := by
              rcases hx₂ with rfl | hx_v
              · exact ⟨u_end e₂, Or.inl rfl, rfl⟩
              · rw [mem_singleton_iff.mp hx_v]
                exact ⟨v_end e₂, Or.inr rfl, rfl⟩
            obtain ⟨s, hs_uv, rfl⟩ := hex_s
            have hsV : s ∈ Γ.V := by
              rcases hs_uv with rfl | hs_v
              · exact (hQe_spec e₂ he₂).2.1
              · exact (mem_singleton_iff.mp hs_v) ▸ (hQe_spec e₂ he₂).2.2.1
            have hs_interV : s ∈ (Γ.interSet (D₀ B₁)).V := by
              rw [hD₀_interV B₁ hB₁'.1]
              exact ⟨hsV, hf_ΓV s hsV ▸ hx₁⟩
            have hs_D₀ : s ∈ D₀ B₁ := by
              obtain ⟨hV_eq, _⟩ := interSet_V_and_U (hD₀_disc B₁ hB₁'.1).isClosed (hD₀_norm B₁ hB₁'.1)
              exact (hV_eq ▸ hs_interV).2
            have hs_Qe : s ∈ Q e₂ := by
              have hbd := (hQe_spec e₂ he₂).2.2.2.2.2.2.2.2.1.symm.subset hs_uv
              exact GM14.Whitney.subBd_subset_of subset_rfl (hQe_spec e₂ he₂).2.2.2.2.2.2.1.isClosed hbd.1
            have hs_in : s ∈ Q e₂ ∩ D₀ B₁ := ⟨hs_Qe, hs_D₀⟩
            rw [(hQe_spec e₂ he₂).2.2.2.2.2.2.2.2.2.2.2.2.2.2 B₁ hB₁'] at hs_in
            obtain ⟨z, hz_range, rfl⟩ := hs_in.2
            have hzZ : z ∈ Z := ((hπ_eq_Z B₁ hB₁'.1).subset hz_range).1
            rw [hf_Z z hzZ]
            exact hπ_eq_Z B₁ hB₁'.1 ▸ hz_range
          · exact Or.inr hxW
        · rintro x (⟨⟨_, hx₁⟩, hx₂⟩ | hxW)
          · exact ⟨hx₁, Or.inl hx₂⟩
          · exact ⟨h83.hyp_vi.2.2.2 B₁ hB₁'.1 hxW, Or.inr hxW⟩
      · rw [hπS''_B_range e₁ he₁, Set.image_pair, (hBe_props e₁ he₁).2.2.1, h_img_range B₂ hB₂']
        apply Subset.antisymm
        · rintro x ⟨hx₁ | hxW, hx₂⟩
          · left
            refine ⟨hx₁, ?_⟩
            have hex_s : ∃ s ∈ ({u_end e₁, v_end e₁} : Set S), ιV' s = x := by
              rcases hx₁ with rfl | hx_v
              · exact ⟨u_end e₁, Or.inl rfl, rfl⟩
              · rw [mem_singleton_iff.mp hx_v]
                exact ⟨v_end e₁, Or.inr rfl, rfl⟩
            obtain ⟨s, hs_uv, rfl⟩ := hex_s
            have hsV : s ∈ Γ.V := by
              rcases hs_uv with rfl | hs_v
              · exact (hQe_spec e₁ he₁).2.1
              · exact (mem_singleton_iff.mp hs_v) ▸ (hQe_spec e₁ he₁).2.2.1
            have hs_interV : s ∈ (Γ.interSet (D₀ B₂)).V := by
              rw [hD₀_interV B₂ hB₂'.1]
              exact ⟨hsV, hf_ΓV s hsV ▸ hx₂⟩
            have hs_D₀ : s ∈ D₀ B₂ := by
              obtain ⟨hV_eq, _⟩ := interSet_V_and_U (hD₀_disc B₂ hB₂'.1).isClosed (hD₀_norm B₂ hB₂'.1)
              exact (hV_eq ▸ hs_interV).2
            have hs_Qe : s ∈ Q e₁ := by
              have hbd := (hQe_spec e₁ he₁).2.2.2.2.2.2.2.2.1.symm.subset hs_uv
              exact GM14.Whitney.subBd_subset_of subset_rfl (hQe_spec e₁ he₁).2.2.2.2.2.2.1.isClosed hbd.1
            have hs_in : s ∈ Q e₁ ∩ D₀ B₂ := ⟨hs_Qe, hs_D₀⟩
            rw [(hQe_spec e₁ he₁).2.2.2.2.2.2.2.2.2.2.2.2.2.2 B₂ hB₂'] at hs_in
            obtain ⟨z, hz_range, rfl⟩ := hs_in.2
            have hzZ : z ∈ Z := ((hπ_eq_Z B₂ hB₂'.1).subset hz_range).1
            rw [hf_Z z hzZ]
            exact hπ_eq_Z B₂ hB₂'.1 ▸ hz_range
          · exact Or.inr hxW
        · rintro x (⟨hx₁, _, hx₂⟩ | hxW)
          · exact ⟨Or.inl hx₁, hx₂⟩
          · exact ⟨Or.inr hxW, h83.hyp_vi.2.2.2 B₂ hB₂'.1 hxW⟩
      · rw [hπS''_B_range e₁ he₁, hπS''_B_range e₂ he₂, Set.image_pair, Set.image_pair,
          (hBe_props e₁ he₁).2.2.1, (hBe_props e₂ he₂).2.2.1]
        ext x
        simp only [mem_inter_iff, mem_union]
        tauto
    · -- `Γ_inter_D`
      rintro B (hB' | ⟨e, he, rfl⟩)
      · rw [hD''_𝒜' B hB']
        exact hD₀_inter_emb' B hB'.1
      · rw [hD''_B e he]
        exact (hBe_props e he).2.2.2.2.1
    · -- `π_clockwise`
      rintro B (hB' | ⟨e, he, rfl⟩) h3
      · rw [hD''_𝒜' B hB']
        have h3' : πLen B = 3 := (hπLen''_𝒜' B hB').symm.trans h3
        have hcw := hc4 B hB'.1 h3'
        have h0 : πS'' B ⟨0, by omega⟩ = α_map (πA B ⟨0, by omega⟩) := by
          rw [hπS''_𝒜'_eq B hB']; rfl
        have h1 : πS'' B ⟨1, by omega⟩ = α_map (πA B ⟨1, by omega⟩) := by
          rw [hπS''_𝒜'_eq B hB']; rfl
        have h2 : πS'' B ⟨2, by omega⟩ = α_map (πA B ⟨2, by omega⟩) := by
          rw [hπS''_𝒜'_eq B hB']; rfl
        rw [h0, h1, h2]
        exact hcw
      · have h2 := hπLen''_B e he
        omega
    · -- `dist_D_of_inter_K`
      rintro B (hB' | ⟨e, he, rfl⟩) hne_NW
      · rw [hD''_𝒜' B hB']
        exact hc11_A B hB' hne_NW
      · rw [hD''_B e he]
        exact (hBe_props e he).2.2.2.2.2.2.2.2.1
    · -- `φV_meets`
      intro v hv
      obtain ⟨x, hx⟩ := (hMod.connected_of_mem v hv).1
      have hxG : x ∈ V(G) := (hMod.1 v hv).vertexSet_mono hx
      exact ⟨x, hx, hVK_cov.symm ▸ hxG⟩
    · -- `φE_mem`
      intro e_H he_H
      have hgG : φE e_H ∈ E(G) := hMod.edge_mem e_H he_H
      exact hEK_cov.symm ▸ hgG

end GraphMinor.GM22
