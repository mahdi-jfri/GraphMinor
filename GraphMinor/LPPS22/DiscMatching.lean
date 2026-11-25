module

public import GraphMinor.GHR18.StripBox
public import GraphMinor.Surface.Cap
public import GraphMinor.Surface.CutIArc

/-!
# Straightening Matchings in a Closed Disc

Given a closed disc `D` (homeomorphic to `closedBall (0 : ℂ) 1`) and two matchings `M : Fin n → Set D`
and `L : Fin m → Set D` of pairwise disjoint proper `I`-arcs with disjoint endpoints on `bd D`, there
exists a boundary-fixing homeomorphism `φ : D ≃ₜ D` such that `φ '' M j ∩ L i` has at most `1` point
for all `j, i`.

## Proof
1. `straighten_disc_matching_convex`: By strong induction on `n`, for any compact convex disc
   `K ⊆ closedBall (0 : ℂ) 1` with nonempty interior and any matching of `n` pairwise disjoint chords
   of `K` whose endpoints lie on `sphere (0 : ℂ) 1` and whose open Euclidean chords lie in `interior K`,
   there is a homeomorphism `α : ℂ ≃ₜ ℂ` fixing `(interior K)ᶜ` that carries every arc `A i` to its
   Euclidean straight segment `segment ℝ (u i) (v i)`.
   At each step, `exists_chord_homeo` straightens `A 0` to `seg₀ := segment ℝ (u 0) (v 0)`, which
   cuts `K` into two convex sub-discs `K₁, K₂` with disjoint interiors; each remaining chord lies in
   one of `K₁ \ seg₀` or `K₂ \ seg₀`, and composing the two recursive homeomorphisms (which have
   disjoint supports in `interior K₁` and `interior K₂`) completes the step.
2. `segment_inter_le_one`: Any two Euclidean chords of `sphere (0 : ℂ) 1` with four distinct
   endpoints intersect in at most `1` point (since a line meets the unit circle in at most `2` points).
3. `lpps22_disc_matching`: Straighten `M` by `α_M` and `L` by `α_L`, both fixing `bd D`; then
   `φ := α_M.trans α_L.symm` carries `M j ∩ L i` into the intersection of two Euclidean chords.
-/

@[expose] public section

namespace GraphMinor.LPPS22

open Set Topology Metric Complex Function GraphMinor.Surface GraphMinor.GHR18

/-! ### Section 1: Euclidean chords of the unit circle -/

theorem norm_lt_one_of_openSegment {u v z : ℂ}
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (huv : u ≠ v) (hz : z ∈ openSegment ℝ u v) :
    ‖z‖ < 1 := by
  obtain ⟨a, b, ha, hb, hab, rfl⟩ := hz
  have h1 : Complex.normSq (a • u + b • v) = 1 - a * b * Complex.normSq (u - v) := by
    have hnu : u.re ^ 2 + u.im ^ 2 = 1 := by
      have := Complex.normSq_eq_norm_sq u; rw [hu, one_pow, Complex.normSq_apply] at this; linarith
    have hnv : v.re ^ 2 + v.im ^ 2 = 1 := by
      have := Complex.normSq_eq_norm_sq v; rw [hv, one_pow, Complex.normSq_apply] at this; linarith
    simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im,
      Complex.real_smul, Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, sub_zero, add_zero]
    have hb_eq : b = 1 - a := by linarith
    subst hb_eq
    nlinarith [hnu, hnv]
  have hpos : 0 < a * b * Complex.normSq (u - v) :=
    mul_pos (mul_pos ha hb) (Complex.normSq_pos.mpr (sub_ne_zero.mpr huv))
  have hsq : ‖a • u + b • v‖ ^ 2 < 1 := by
    rw [← Complex.normSq_eq_norm_sq, h1]; linarith
  nlinarith [norm_nonneg (a • u + b • v)]

theorem mem_openSegment_of_mem_segment_ne {u v z : ℂ} (hz : z ∈ segment ℝ u v) (h1 : z ≠ u) (h2 : z ≠ v) :
    z ∈ openSegment ℝ u v := by
  obtain ⟨a, b, ha, hb, hab, rfl⟩ := hz
  refine ⟨a, b, lt_of_le_of_ne ha (fun h0 => h2 (by rw [← h0, zero_smul, zero_add, show b = 1 by linarith, one_smul])),
    lt_of_le_of_ne hb (fun h0 => h1 (by rw [← h0, zero_smul, add_zero, show a = 1 by linarith, one_smul])), hab, rfl⟩

theorem isLineWithEnds_segment {u v : ℂ} (huv : u ≠ v) :
    IsLineWithEnds (segment ℝ u v) u v := by
  let f : unitInterval → segment ℝ u v := fun t =>
    ⟨(1 - t.1) • u + t.1 • v, ⟨1 - t.1, t.1, sub_nonneg.mpr t.2.2, t.2.1, by ring, rfl⟩⟩
  let d := v - u
  have hd : Complex.normSq d ≠ 0 := (Complex.normSq_pos.mpr (sub_ne_zero.mpr huv.symm)).ne'
  let proj : ℂ → ℝ := fun z => ((z - u).re * d.re + (z - u).im * d.im) / Complex.normSq d
  have hproj_f : ∀ t : ℝ, proj ((1 - t) • u + t • v) = t := fun t => by
    have hsub : ((1 - t) • u + t • v) - u = t • d := by
      simp only [d, smul_sub, sub_smul, one_smul]; abel
    dsimp only [proj]
    rw [hsub]
    simp only [Complex.real_smul, Complex.mul_re, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero, add_zero, Complex.normSq_apply]
    have hne : d.re ^ 2 + d.im ^ 2 ≠ 0 := by
      have := hd; rw [Complex.normSq_apply] at this; intro h; apply this; linarith
    rw [show d.re * d.re + d.im * d.im = d.re ^ 2 + d.im ^ 2 by ring]
    field_simp [hne]
  let g : segment ℝ u v → unitInterval := fun z =>
    ⟨proj z.1, by
      obtain ⟨a, b, ha, hb, hab, hze⟩ := z.2
      have ha' : a = 1 - b := by linarith
      rw [← hze, ha', hproj_f b]
      exact ⟨hb, by linarith⟩⟩
  refine ⟨{
    toFun := f
    invFun := g
    left_inv := fun t => Subtype.ext (hproj_f t.1)
    right_inv := fun z => by
      apply Subtype.ext
      obtain ⟨a, b, ha, hb, hab, hze⟩ := z.2
      have ha' : a = 1 - b := by linarith
      dsimp only [f, g]
      rw [← hze, ha', hproj_f b]
    continuous_toFun := by
      refine Continuous.subtype_mk ?_ _
      exact ((continuous_const.sub continuous_subtype_val).smul continuous_const).add
        (continuous_subtype_val.smul continuous_const)
    continuous_invFun := by
      refine Continuous.subtype_mk ?_ _
      have hc : Continuous proj := by
        unfold proj
        fun_prop
      exact hc.comp continuous_subtype_val
  }, ?_, ?_⟩
  · show (1 - (0 : ℝ)) • u + (0 : ℝ) • v = u; simp
  · show (1 - (1 : ℝ)) • u + (1 : ℝ) • v = v; simp

/-- Two Euclidean chords of the unit circle with four distinct endpoints intersect in at most
one point. -/
theorem segment_inter_le_one {s t u v : ℂ}
    (hs : s ∈ sphere (0 : ℂ) 1) (ht : t ∈ sphere (0 : ℂ) 1)
    (hu : u ∈ sphere (0 : ℂ) 1) (_hv : v ∈ sphere (0 : ℂ) 1)
    (hst : s ≠ t) (_huv : u ≠ v) (hdisj : Disjoint ({s, t} : Set ℂ) {u, v}) :
    (segment ℝ s t ∩ segment ℝ u v).Finite ∧ (segment ℝ s t ∩ segment ℝ u v).ncard ≤ 1 := by
  have hsub : (segment ℝ s t ∩ segment ℝ u v).Subsingleton := by
    intro z₁ hz₁ z₂ hz₂
    by_contra hne
    obtain ⟨a₁, b₁, _, _, hab₁, hz₁_st⟩ := hz₁.1
    obtain ⟨a₂, b₂, _, _, hab₂, hz₂_st⟩ := hz₂.1
    obtain ⟨c₁, d₁, _, _, hcd₁, hz₁_uv⟩ := hz₁.2
    obtain ⟨c₂, d₂, _, _, hcd₂, hz₂_uv⟩ := hz₂.2
    have hz₁_st' : z₁ = s + b₁ • (t - s) := by
      rw [← hz₁_st, show a₁ = 1 - b₁ by linarith, sub_smul, one_smul, smul_sub]; abel
    have hz₂_st' : z₂ = s + b₂ • (t - s) := by
      rw [← hz₂_st, show a₂ = 1 - b₂ by linarith, sub_smul, one_smul, smul_sub]; abel
    have hz₁_uv' : z₁ = u + d₁ • (v - u) := by
      rw [← hz₁_uv, show c₁ = 1 - d₁ by linarith, sub_smul, one_smul, smul_sub]; abel
    have hz₂_uv' : z₂ = u + d₂ • (v - u) := by
      rw [← hz₂_uv, show c₂ = 1 - d₂ by linarith, sub_smul, one_smul, smul_sub]; abel
    have hb_ne : b₂ - b₁ ≠ 0 := fun h => hne (by rw [hz₁_st', hz₂_st', show b₂ = b₁ by linarith])
    have hd_ne : d₂ - d₁ ≠ 0 := fun h => hne (by rw [hz₁_uv', hz₂_uv', show d₂ = d₁ by linarith])
    have hdiff : (b₂ - b₁) • (t - s) = (d₂ - d₁) • (v - u) := by
      calc (b₂ - b₁) • (t - s) = z₂ - z₁ := by rw [hz₂_st', hz₁_st', sub_smul]; abel
        _ = (d₂ - d₁) • (v - u) := by rw [hz₂_uv', hz₁_uv', sub_smul]; abel
    let lam : ℝ := (b₂ - b₁) / (d₂ - d₁)
    have hv_u : v - u = lam • (t - s) := by
      have h1 := congrArg (fun w : ℂ => (d₂ - d₁)⁻¹ • w) hdiff
      simp only [smul_smul, inv_mul_cancel₀ hd_ne, one_smul] at h1
      rw [← h1]; simp only [lam, div_eq_inv_mul]
    let r : ℝ := b₁ - d₁ * lam
    have hu_eq : u = s + r • (t - s) := by
      calc u = z₁ - d₁ • (v - u) := by rw [hz₁_uv']; abel
        _ = (s + b₁ • (t - s)) - (d₁ * lam) • (t - s) := by rw [hz₁_st', hv_u, smul_smul]
        _ = s + r • (t - s) := by simp only [r, sub_smul]; abel
    have hns : Complex.normSq s = 1 := by
      rw [Complex.normSq_eq_norm_sq, mem_sphere_zero_iff_norm.mp hs, one_pow]
    have hnt : Complex.normSq t = 1 := by
      rw [Complex.normSq_eq_norm_sq, mem_sphere_zero_iff_norm.mp ht, one_pow]
    have hnu : Complex.normSq u = 1 := by
      rw [Complex.normSq_eq_norm_sq, mem_sphere_zero_iff_norm.mp hu, one_pow]
    have hA_pos : 0 < Complex.normSq (t - s) := Complex.normSq_pos.mpr (sub_ne_zero.mpr hst.symm)
    have h_quad : ∀ x : ℝ, Complex.normSq (s + x • (t - s)) =
        Complex.normSq s + 2 * x * (s.re * (t - s).re + s.im * (t - s).im) + x ^ 2 * Complex.normSq (t - s) := by
      intro x
      simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im, Complex.real_smul,
        Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero, add_zero]
      ring
    have ht_eq : s + (1 : ℝ) • (t - s) = t := by simp
    have h1 := h_quad 1; rw [ht_eq, hns, hnt] at h1
    have hr := h_quad r; rw [← hu_eq, hns, hnu] at hr
    have hr0 : r ≠ 0 := fun h0 => by
      rw [h0, zero_smul, add_zero] at hu_eq
      exact Set.disjoint_left.mp hdisj (Or.inl rfl) (Or.inl hu_eq.symm)
    have hr1 : r ≠ 1 := fun h1' => by
      rw [h1', one_smul, add_sub_cancel] at hu_eq
      exact Set.disjoint_left.mp hdisj (Or.inr rfl) (Or.inl hu_eq.symm)
    have hB : 2 * (s.re * (t - s).re + s.im * (t - s).im) + Complex.normSq (t - s) = 0 := by linarith
    have hBr : r * (2 * (s.re * (t - s).re + s.im * (t - s).im) + r * Complex.normSq (t - s)) = 0 := by nlinarith
    have hBr' : 2 * (s.re * (t - s).re + s.im * (t - s).im) + r * Complex.normSq (t - s) = 0 :=
      (mul_eq_zero.mp hBr).resolve_left hr0
    have : (r - 1) * Complex.normSq (t - s) = 0 := by linarith
    rcases mul_eq_zero.mp this with h | h
    · exact hr1 (by linarith)
    · linarith
  refine ⟨hsub.finite, ?_⟩
  rcases hsub.eq_empty_or_singleton with h | ⟨x, h⟩
  · rw [h]; simp
  · rw [h]; simp

/-! ### Section 2: Straightening a matching of chords in a convex sub-disc -/

private theorem mem_sphere_not_openSegment {u v z : ℂ}
    (hu : z ∈ sphere (0 : ℂ) 1) (h1 : u ∈ closedBall (0 : ℂ) 1) (h2 : v ∈ closedBall (0 : ℂ) 1)
    (hne : u ≠ v) : z ∉ openSegment ℝ u v := by
  rintro ⟨a, b, ha, hb, hab, hze⟩
  have hnu : Complex.normSq u ≤ 1 := by
    rw [Complex.normSq_eq_norm_sq]
    have := mem_closedBall_zero_iff.mp h1; nlinarith [norm_nonneg u]
  have hnv : Complex.normSq v ≤ 1 := by
    rw [Complex.normSq_eq_norm_sq]
    have := mem_closedBall_zero_iff.mp h2; nlinarith [norm_nonneg v]
  have hnz : Complex.normSq z = 1 := by
    rw [Complex.normSq_eq_norm_sq, mem_sphere_zero_iff_norm.mp hu, one_pow]
  have hident : Complex.normSq (a • u + b • v) =
      a * Complex.normSq u + b * Complex.normSq v - a * b * Complex.normSq (u - v) := by
    simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im,
      Complex.real_smul, Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, sub_zero, add_zero]
    have hb' : b = 1 - a := by linarith
    subst hb'; ring
  have hpos : 0 < a * b * Complex.normSq (u - v) :=
    mul_pos (mul_pos ha hb) (Complex.normSq_pos.mpr (sub_ne_zero.mpr hne))
  rw [hze] at hident
  nlinarith

/-- Strong induction straightening a matching of `n` chords in a compact convex sub-disc `K ⊆ closedBall 0 1`. -/
private theorem straighten_disc_matching_convex :
    ∀ n : ℕ, ∀ {K : Set ℂ}
      (_hK_sub : K ⊆ closedBall (0 : ℂ) 1)
      (_hK_conv : Convex ℝ K) (_hK_cl : IsClosed K) (_hK_int : (interior K).Nonempty)
      {A : Fin n → Set ℂ} {u v : Fin n → ℂ}
      (_huv : ∀ i, u i ≠ v i)
      (_hA_sub : ∀ i, A i ⊆ K)
      (_hA_line : ∀ i, IsLineWithEnds (A i) (u i) (v i))
      (_hA_bd : ∀ i, A i ∩ frontier K = {u i, v i})
      (_hA_disj : Pairwise fun i j => Disjoint (A i) (A j))
      (_hu_sph : ∀ i, u i ∈ sphere (0 : ℂ) 1)
      (_hv_sph : ∀ i, v i ∈ sphere (0 : ℂ) 1)
      (_hseg_int : ∀ i, openSegment ℝ (u i) (v i) ⊆ interior K),
      ∃ α : ℂ ≃ₜ ℂ, (∀ x ∈ (interior K)ᶜ, α x = x) ∧
        (∀ i : Fin n, α '' A i = segment ℝ (u i) (v i)) := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro K hK_sub hK_conv hK_cl hK_int A u v huv hA_sub hA_line hA_bd hA_disj hu_sph hv_sph hseg_int
    classical
    cases n with
    | zero => exact ⟨Homeomorph.refl ℂ, fun _ _ => rfl, fun i => Fin.elim0 i⟩
    | succ k =>
      have hK_bdd : Bornology.IsBounded K := isBounded_closedBall.subset hK_sub
      obtain ⟨hK_disc, hK_discBd⟩ := isClosedDisc_of_convex hK_conv hK_int hK_bdd hK_cl
      have hdiscInt_eq : discInt K = interior K := by
        rw [discInt, hK_discBd, frontier, hK_cl.closure_eq, sdiff_sdiff_right_self, inter_eq_right.mpr interior_subset]
      let u₀ := u 0
      let v₀ := v 0
      have huv₀ : u₀ ≠ v₀ := huv 0
      let seg₀ : Set ℂ := segment ℝ u₀ v₀
      have hu₀K : u₀ ∈ K := hA_sub 0 (hA_line 0).left_mem
      have hv₀K : v₀ ∈ K := hA_sub 0 (hA_line 0).right_mem
      have hu₀fr : u₀ ∈ frontier K := (hA_bd 0 ▸ Or.inl rfl : u₀ ∈ A 0 ∩ frontier K).2
      have hv₀fr : v₀ ∈ frontier K := (hA_bd 0 ▸ Or.inr rfl : v₀ ∈ A 0 ∩ frontier K).2
      have hseg₀_sub : seg₀ ⊆ K := hK_conv.segment_subset hu₀K hv₀K
      have hseg₀_line : IsLineWithEnds seg₀ u₀ v₀ := isLineWithEnds_segment huv₀
      have hseg₀_bd : seg₀ ∩ discBd K = {u₀, v₀} := by
        rw [hK_discBd]; ext z; constructor
        · rintro ⟨hzS, hzfr⟩
          by_cases h1 : z = u₀
          · exact Or.inl h1
          · by_cases h2 : z = v₀
            · exact Or.inr h2
            · exfalso
              have hoo : z ∈ openSegment ℝ u₀ v₀ := by
                obtain ⟨a, b, ha, hb, hab, rfl⟩ := hzS
                refine ⟨a, b, lt_of_le_of_ne ha (fun h0 => h2 (by rw [← h0, zero_smul, zero_add, show b = 1 by linarith, one_smul])),
                  lt_of_le_of_ne hb (fun h0 => h1 (by rw [← h0, zero_smul, add_zero, show a = 1 by linarith, one_smul])), hab, rfl⟩
              exact hzfr.2 (hseg_int 0 hoo)
        · rintro (rfl | rfl)
          · exact ⟨left_mem_segment ℝ u₀ v₀, hu₀fr⟩
          · exact ⟨right_mem_segment ℝ u₀ v₀, hv₀fr⟩
      have hA0_bd : A 0 ∩ discBd K = {u₀, v₀} := hK_discBd ▸ hA_bd 0
      -- Step 1: Straighten `A 0` to `seg₀` fixing `(interior K)ᶜ`
      have hmanℂ : ∀ x : ℂ, IsManifoldPoint x := isManifoldPoint_complex
      obtain ⟨α₀, hα₀A, hα₀fix⟩ := exists_chord_homeo hmanℂ hK_disc (hA_sub 0) hseg₀_sub huv₀
        (hA_line 0) hseg₀_line hA0_bd hseg₀_bd
      rw [hdiscInt_eq] at hα₀fix
      have hα₀_K : α₀ '' K = K := by
        ext z; constructor
        · rintro ⟨w, hw, rfl⟩
          by_cases hint : w ∈ interior K
          · by_contra hnotK
            have hnotI : α₀ w ∈ (interior K)ᶜ := fun h => hnotK (interior_subset h)
            have h1 := hα₀fix (α₀ w) hnotI
            have h2 := α₀.injective h1
            exact hnotK (h2.symm ▸ hw)
          · rwa [hα₀fix w hint]
        · intro hz
          by_cases hint : z ∈ interior K
          · refine ⟨α₀.symm z, ?_, α₀.apply_symm_apply z⟩
            by_contra hnotK
            have hnotI : α₀.symm z ∈ (interior K)ᶜ := fun h => hnotK (interior_subset h)
            have h1 := hα₀fix (α₀.symm z) hnotI
            rw [α₀.apply_symm_apply] at h1
            exact hnotK (h1 ▸ hz)
          · exact ⟨z, hz, hα₀fix z hint⟩
      -- Step 2: Cut `K` along the line through `u₀, v₀` into two convex sub-discs `K₁, K₂`
      let f : ℂ → ℝ := fun z => ((z - u₀) * star (v₀ - u₀)).im
      have hf_cont : Continuous f := by
        unfold f; fun_prop
      have hf_affine : ∀ (a b : ℝ) (x y : ℂ), a + b = 1 → f (a • x + b • y) = a * f x + b * f y := by
        intro a b x y hab
        have h1 : (a • x + b • y) - u₀ = a • (x - u₀) + b • (y - u₀) := by
          have : u₀ = a • u₀ + b • u₀ := by rw [← add_smul, hab, one_smul]
          conv_lhs => rw [this]
          simp only [smul_sub]; abel
        dsimp only [f]
        rw [h1, add_mul, Complex.add_im]
        simp only [Complex.real_smul, mul_assoc,
          Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero]
      have hf_u₀ : f u₀ = 0 := by simp [f]
      have hf_v₀ : f v₀ = 0 := by
        simp only [f, Complex.star_def, Complex.mul_conj, Complex.ofReal_im]
      have hf_zero_iff : ∀ z ∈ K, f z = 0 ↔ z ∈ seg₀ := by
        intro z hzK; constructor
        · intro hfz
          let d := v₀ - u₀
          have hd0 : d ≠ 0 := sub_ne_zero.mpr huv₀.symm
          have hnd : 0 < Complex.normSq d := Complex.normSq_pos.mpr hd0
          let t : ℝ := ((z - u₀) * star d).re / Complex.normSq d
          have hmul : (z - u₀) * star d = (t * Complex.normSq d : ℝ) := by
            apply Complex.ext
            · simp only [Complex.ofReal_re, t]; field_simp [hnd.ne']
            · simp only [Complex.ofReal_im]; exact hfz
          have hzeq : z = u₀ + t • d := by
            have h1 := congrArg (fun w : ℂ => w * d) hmul
            have hsd : star d * d = (Complex.normSq d : ℂ) := by
              rw [mul_comm, Complex.star_def, Complex.mul_conj]
            rw [mul_assoc, hsd] at h1
            have h2 : (z - u₀) * (Complex.normSq d : ℂ) = (t • d) * (Complex.normSq d : ℂ) := by
              rw [h1, Complex.real_smul, Complex.ofReal_mul]; ring
            have h3 : z - u₀ = t • d := mul_right_cancel₀ (Complex.ofReal_ne_zero.mpr hnd.ne') h2
            calc z = u₀ + (z - u₀) := by abel
              _ = u₀ + t • d := by rw [h3]
          have ht0 : 0 ≤ t := by
            by_contra hlt; push Not at hlt
            have hu_os : u₀ ∈ openSegment ℝ z v₀ := by
              refine ⟨1 / (1 - t), -t / (1 - t), div_pos one_pos (by linarith), div_pos (neg_pos.mpr hlt) (by linarith), ?_, ?_⟩
              · field_simp [show (1 : ℝ) - t ≠ 0 by linarith]; ring
              · rw [hzeq]; simp only [d, smul_add, smul_smul, smul_sub]
                have hne1 : (1 : ℝ) - t ≠ 0 := by linarith
                apply Complex.ext <;> simp only [Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im,
                  Complex.real_smul, Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
                  zero_mul, sub_zero, add_zero] <;> field_simp [hne1] <;> ring
            have hne_zv : z ≠ v₀ := fun h => by
              have : (1 - t) • d = 0 := by
                rw [sub_smul, one_smul]; calc d - t • d = v₀ - (u₀ + t • d) := by simp [d]; abel
                  _ = v₀ - z := by rw [← hzeq]
                  _ = 0 := sub_eq_zero.mpr h.symm
              rcases smul_eq_zero.mp this with h1 | h2
              · linarith
              · exact hd0 h2
            exact mem_sphere_not_openSegment (hu_sph 0) (hK_sub hzK) (hK_sub hv₀K) hne_zv hu_os
          have ht1 : t ≤ 1 := by
            by_contra hgt; push Not at hgt
            have hv_os : v₀ ∈ openSegment ℝ u₀ z := by
              refine ⟨(t - 1) / t, 1 / t, div_pos (by linarith) (by linarith), by positivity, ?_, ?_⟩
              · field_simp [show t ≠ 0 by linarith]; ring
              · rw [hzeq]; simp only [d]
                have hne0 : t ≠ 0 := by linarith
                apply Complex.ext <;> simp only [Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im,
                  Complex.real_smul, Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
                  zero_mul, sub_zero, add_zero] <;> field_simp [hne0] <;> ring
            have hne_uz : u₀ ≠ z := fun h => by
              have : t • d = 0 := by
                calc t • d = (u₀ + t • d) - u₀ := by abel
                  _ = z - u₀ := by rw [← hzeq]
                  _ = 0 := sub_eq_zero.mpr h.symm
              rcases smul_eq_zero.mp this with h1 | h2
              · linarith
              · exact hd0 h2
            exact mem_sphere_not_openSegment (hv_sph 0) (hK_sub hu₀K) (hK_sub hzK) hne_uz hv_os
          refine ⟨1 - t, t, by linarith, ht0, by ring, ?_⟩
          rw [hzeq]; simp only [d, sub_smul, one_smul, smul_sub]; abel
        · rintro ⟨a, b, _, _, hab, rfl⟩
          rw [hf_affine a b u₀ v₀ hab, hf_u₀, hf_v₀]; ring
      let K₁ : Set ℂ := K ∩ {z | 0 ≤ f z}
      let K₂ : Set ℂ := K ∩ {z | f z ≤ 0}
      have hK₁_conv : Convex ℝ K₁ := hK_conv.inter fun x hx y hy a b ha hb hab => by
        show 0 ≤ f (a • x + b • y); rw [hf_affine a b x y hab]
        exact add_nonneg (mul_nonneg ha hx) (mul_nonneg hb hy)
      have hK₂_conv : Convex ℝ K₂ := hK_conv.inter fun x hx y hy a b ha hb hab => by
        show f (a • x + b • y) ≤ 0; rw [hf_affine a b x y hab]
        exact add_nonpos (mul_nonpos_of_nonneg_of_nonpos ha hx) (mul_nonpos_of_nonneg_of_nonpos hb hy)
      have hK₁_cl : IsClosed K₁ := hK_cl.inter (isClosed_le continuous_const hf_cont)
      have hK₂_cl : IsClosed K₂ := hK_cl.inter (isClosed_le hf_cont continuous_const)
      -- Both `K₁` and `K₂` have nonempty interior (push off midpoint of `seg₀` along `± I * (v₀ - u₀)`):
      have hmid_int : ((1 / 2 : ℝ) • u₀ + (1 / 2 : ℝ) • v₀) ∈ interior K :=
        hseg_int 0 ⟨1 / 2, 1 / 2, by norm_num, by norm_num, by norm_num, rfl⟩
      obtain ⟨r, hr, hrsub⟩ := Metric.isOpen_iff.mp isOpen_interior _ hmid_int
      let d := v₀ - u₀
      have hd_pos : 0 < ‖d‖ := norm_pos_iff.mpr (sub_ne_zero.mpr huv₀.symm)
      have hf_shift : ∀ s : ℝ, f (((1 / 2 : ℝ) • u₀ + (1 / 2 : ℝ) • v₀) + (s : ℂ) * (I * d)) = s * Complex.normSq d := by
        intro s
        have h1 : (((1 / 2 : ℝ) • u₀ + (1 / 2 : ℝ) • v₀) + (s : ℂ) * (I * d)) - u₀ =
            ((1 / 2 : ℝ) : ℂ) * d + (s : ℂ) * (I * d) := by
          simp only [d, Complex.real_smul]; push_cast; ring
        have hsd : d * star d = (Complex.normSq d : ℂ) := by rw [Complex.star_def, Complex.mul_conj]
        have h2 : (((1 / 2 : ℝ) : ℂ) * d + (s : ℂ) * (I * d)) * star d =
            ((1 / 2 : ℝ) * Complex.normSq d : ℝ) + ((s * Complex.normSq d : ℝ) : ℂ) * I := by
          calc (((1 / 2 : ℝ) : ℂ) * d + (s : ℂ) * (I * d)) * star d
              = ((1 / 2 : ℝ) : ℂ) * (d * star d) + (s : ℂ) * I * (d * star d) := by ring
            _ = ((1 / 2 : ℝ) : ℂ) * (Complex.normSq d : ℂ) + (s : ℂ) * I * (Complex.normSq d : ℂ) := by rw [hsd]
            _ = _ := by push_cast; ring
        dsimp only [f]
        rw [show v₀ - u₀ = d from rfl, h1, h2]
        simp only [Complex.add_im, Complex.ofReal_re, Complex.ofReal_im, Complex.mul_im, Complex.I_re, Complex.I_im,
          mul_one, mul_zero, zero_add, add_zero]
      have hK₁_int : (interior K₁).Nonempty := by
        let s := r / (2 * ‖d‖)
        have hs : 0 < s := by positivity
        let z := ((1 / 2 : ℝ) • u₀ + (1 / 2 : ℝ) • v₀) + (s : ℂ) * (I * d)
        have hzK : z ∈ interior K := hrsub (by
          rw [mem_ball, dist_eq_norm, show z - ((1 / 2 : ℝ) • u₀ + (1 / 2 : ℝ) • v₀) = (s : ℂ) * (I * d) by simp [z]]
          rw [norm_mul, norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_of_nonneg hs.le]
          simp only [s]; field_simp [hd_pos.ne']; linarith)
        have hfz : 0 < f z := by rw [hf_shift s]; exact mul_pos hs (Complex.normSq_pos.mpr (sub_ne_zero.mpr huv₀.symm))
        exact ⟨z, mem_interior.mpr ⟨interior K ∩ {w | 0 < f w}, fun w hw => ⟨interior_subset hw.1, show 0 ≤ f w from le_of_lt hw.2⟩,
          isOpen_interior.inter (isOpen_lt continuous_const hf_cont), hzK, hfz⟩⟩
      have hK₂_int : (interior K₂).Nonempty := by
        let s := -(r / (2 * ‖d‖))
        have hs : s < 0 := neg_lt_zero.mpr (by positivity)
        let z := ((1 / 2 : ℝ) • u₀ + (1 / 2 : ℝ) • v₀) + (s : ℂ) * (I * d)
        have hzK : z ∈ interior K := hrsub (by
          rw [mem_ball, dist_eq_norm, show z - ((1 / 2 : ℝ) • u₀ + (1 / 2 : ℝ) • v₀) = (s : ℂ) * (I * d) by simp [z]]
          rw [norm_mul, norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_neg hs]
          simp only [s, neg_neg]; field_simp [hd_pos.ne']; linarith)
        have hfz : f z < 0 := by rw [hf_shift s]; exact mul_neg_of_neg_of_pos hs (Complex.normSq_pos.mpr (sub_ne_zero.mpr huv₀.symm))
        exact ⟨z, mem_interior.mpr ⟨interior K ∩ {w | f w < 0}, fun w hw => ⟨interior_subset hw.1, show f w ≤ 0 from le_of_lt hw.2⟩,
          isOpen_interior.inter (isOpen_lt hf_cont continuous_const), hzK, hfz⟩⟩
      -- Characterization of `interior K₁` and `interior K₂`:
      have hint₁_eq : interior K₁ = interior K ∩ {z | 0 < f z} := by
        apply subset_antisymm
        · intro z hz
          refine ⟨interior_mono inter_subset_left hz, ?_⟩
          have hz0 : 0 ≤ f z := (interior_subset hz).2
          refine lt_of_le_of_ne hz0 (Ne.symm fun hf0 => ?_)
          obtain ⟨ρ, hρ, hρsub⟩ := Metric.isOpen_iff.mp isOpen_interior z hz
          let s := -(ρ / (2 * ‖d‖))
          have hs : s < 0 := neg_lt_zero.mpr (by positivity)
          let w := z + (s : ℂ) * (I * d)
          have hw : w ∈ K₁ := interior_subset (hρsub (by
            rw [mem_ball, dist_eq_norm, show w - z = (s : ℂ) * (I * d) by simp [w]]
            rw [norm_mul, norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_neg hs]
            simp only [s, neg_neg]; field_simp [hd_pos.ne']; linarith))
          have hfw : f w = s * Complex.normSq d := by
            have hsd : d * star d = (Complex.normSq d : ℂ) := by rw [Complex.star_def, Complex.mul_conj]
            have h1 : (w - u₀) * star d = (z - u₀) * star d + ((s * Complex.normSq d : ℝ) : ℂ) * I := by
              simp only [w]
              calc (z + (s : ℂ) * (I * d) - u₀) * star d
                  = (z - u₀) * star d + (s : ℂ) * I * (d * star d) := by ring
                _ = _ := by rw [hsd]; push_cast; ring
            dsimp only [f]
            rw [show v₀ - u₀ = d from rfl, h1, Complex.add_im]
            have hfz0 : ((z - u₀) * star d).im = 0 := hf0
            rw [hfz0, zero_add]
            simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
              Complex.I_re, Complex.I_im, mul_one, mul_zero, add_zero]
          have hlt : f w < 0 := hfw ▸ mul_neg_of_neg_of_pos hs (Complex.normSq_pos.mpr (sub_ne_zero.mpr huv₀.symm))
          have hge : 0 ≤ f w := hw.2
          linarith
        · exact interior_maximal (fun z ⟨hzK, hfz⟩ => ⟨interior_subset hzK, show 0 ≤ f z from le_of_lt hfz⟩)
            (isOpen_interior.inter (isOpen_lt continuous_const hf_cont))
      have hint₂_eq : interior K₂ = interior K ∩ {z | f z < 0} := by
        apply subset_antisymm
        · intro z hz
          refine ⟨interior_mono inter_subset_left hz, ?_⟩
          have hz0 : f z ≤ 0 := (interior_subset hz).2
          refine lt_of_le_of_ne hz0 (fun hf0 => ?_)
          obtain ⟨ρ, hρ, hρsub⟩ := Metric.isOpen_iff.mp isOpen_interior z hz
          let s := ρ / (2 * ‖d‖)
          have hs : 0 < s := by positivity
          let w := z + (s : ℂ) * (I * d)
          have hw : w ∈ K₂ := interior_subset (hρsub (by
            rw [mem_ball, dist_eq_norm, show w - z = (s : ℂ) * (I * d) by simp [w]]
            rw [norm_mul, norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_of_nonneg hs.le]
            simp only [s]; field_simp [hd_pos.ne']; linarith))
          have hfw : f w = s * Complex.normSq d := by
            have hsd : d * star d = (Complex.normSq d : ℂ) := by rw [Complex.star_def, Complex.mul_conj]
            have h1 : (w - u₀) * star d = (z - u₀) * star d + ((s * Complex.normSq d : ℝ) : ℂ) * I := by
              simp only [w]
              calc (z + (s : ℂ) * (I * d) - u₀) * star d
                  = (z - u₀) * star d + (s : ℂ) * I * (d * star d) := by ring
                _ = _ := by rw [hsd]; push_cast; ring
            dsimp only [f]
            rw [show v₀ - u₀ = d from rfl, h1, Complex.add_im]
            have hfz0 : ((z - u₀) * star d).im = 0 := hf0
            rw [hfz0, zero_add]
            simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
              Complex.I_re, Complex.I_im, mul_one, mul_zero, add_zero]
          have hgt : 0 < f w := hfw ▸ mul_pos hs (Complex.normSq_pos.mpr (sub_ne_zero.mpr huv₀.symm))
          have hle : f w ≤ 0 := hw.2
          linarith
        · exact interior_maximal (fun z ⟨hzK, hfz⟩ => ⟨interior_subset hzK, show f z ≤ 0 from le_of_lt hfz⟩)
            (isOpen_interior.inter (isOpen_lt hf_cont continuous_const))
      -- Step 3: Partition the remaining `k` chords `B j := α₀ '' A j.succ` into `K₁` (`f > 0`) and `K₂` (`f < 0`)
      let B : Fin k → Set ℂ := fun j => α₀ '' A j.succ
      have hB_sub : ∀ j : Fin k, B j ⊆ K := fun j => hα₀_K ▸ image_mono (hA_sub j.succ)
      have hB_disj0 : ∀ j : Fin k, Disjoint (B j) seg₀ := fun j => by
        rw [← hα₀A]; exact Set.disjoint_image_of_injective α₀.injective (hA_disj (Fin.succ_ne_zero j))
      have hB_side : ∀ j : Fin k, (∀ z ∈ B j, 0 < f z) ∨ (∀ z ∈ B j, f z < 0) := by
        intro j
        have hpc : IsPreconnected (B j) := by
          obtain ⟨φ, -, -⟩ := hA_line j.succ
          have hA_pc : IsPreconnected (A j.succ) := by
            have := (isPreconnected_univ (α := unitInterval)).image (fun r => (φ r).1)
              (continuous_subtype_val.comp φ.continuous).continuousOn
            have him : (fun r => (φ r).1) '' (univ : Set unitInterval) = A j.succ := by
              ext x; constructor
              · rintro ⟨r, -, rfl⟩; exact (φ r).2
              · intro hx; exact ⟨φ.symm ⟨x, hx⟩, mem_univ _, congrArg Subtype.val (φ.apply_symm_apply ⟨x, hx⟩)⟩
            rwa [him] at this
          exact hA_pc.image α₀ α₀.continuous.continuousOn
        have hne0 : ∀ z ∈ B j, f z ≠ 0 := fun z hz h0 =>
          Set.disjoint_left.mp (hB_disj0 j) hz ((hf_zero_iff z (hB_sub j hz)).mp h0)
        by_contra hnot; push Not at hnot
        obtain ⟨⟨z₁, hz₁, hle₁⟩, ⟨z₂, hz₂, hge₂⟩⟩ := hnot
        have hlt₁ : f z₁ < 0 := lt_of_le_of_ne hle₁ (hne0 z₁ hz₁)
        have hgt₂ : 0 < f z₂ := lt_of_le_of_ne hge₂ (Ne.symm (hne0 z₂ hz₂))
        obtain ⟨z, -, h1, h2⟩ := hpc {w | 0 < f w} {w | f w < 0}
          (isOpen_lt continuous_const hf_cont) (isOpen_lt hf_cont continuous_const)
          (fun w hw => lt_or_gt_of_ne (hne0 w hw) |>.symm)
          ⟨z₂, hz₂, hgt₂⟩ ⟨z₁, hz₁, hlt₁⟩
        linarith [show 0 < f z from h1, show f z < 0 from h2]
      have hB_line : ∀ j : Fin k, IsLineWithEnds (B j) (u j.succ) (v j.succ) := fun j => by
        obtain ⟨φ, hφ0, hφ1⟩ := hA_line j.succ
        have hufr : u j.succ ∈ frontier K := (hA_bd j.succ ▸ Or.inl rfl : u j.succ ∈ A j.succ ∩ frontier K).2
        have hvfr : v j.succ ∈ frontier K := (hA_bd j.succ ▸ Or.inr rfl : v j.succ ∈ A j.succ ∩ frontier K).2
        refine ⟨φ.trans (α₀.image (A j.succ)), ?_, ?_⟩
        · show α₀ (φ 0).1 = u j.succ; rw [hφ0, hα₀fix _ hufr.2]
        · show α₀ (φ 1).1 = v j.succ; rw [hφ1, hα₀fix _ hvfr.2]
      have hB_bd : ∀ j : Fin k, B j ∩ frontier K = {u j.succ, v j.succ} := fun j => by
        ext z; constructor
        · rintro ⟨⟨w, hwA, rfl⟩, hzfr⟩
          have hwe : α₀ w = w := α₀.injective (hα₀fix (α₀ w) hzfr.2)
          rw [hwe]; exact hA_bd j.succ ▸ ⟨hwA, hwe ▸ hzfr⟩
        · rintro (hz | hz)
          · rw [hz]
            have hu : u j.succ ∈ A j.succ ∩ frontier K := hA_bd j.succ ▸ Or.inl rfl
            exact ⟨⟨u j.succ, hu.1, hα₀fix _ hu.2.2⟩, hu.2⟩
          · rw [mem_singleton_iff.mp hz]
            have hv : v j.succ ∈ A j.succ ∩ frontier K := hA_bd j.succ ▸ Or.inr rfl
            exact ⟨⟨v j.succ, hv.1, hα₀fix _ hv.2.2⟩, hv.2⟩
      -- Helper to run IH on one side (`K₁` or `K₂`):
      let S₁ : Finset (Fin k) := Finset.univ.filter fun j => ∀ z ∈ B j, 0 < f z
      let S₂ : Finset (Fin k) := Finset.univ.filter fun j => ∀ z ∈ B j, f z < 0
      have hS_disj : Disjoint S₁ S₂ := Finset.disjoint_left.mpr fun j h1 h2 => by
        have huB : u j.succ ∈ B j := (hB_line j).left_mem
        linarith [(Finset.mem_filter.mp h1).2 _ huB, (Finset.mem_filter.mp h2).2 _ huB]
      have hS_cov : ∀ j : Fin k, j ∈ S₁ ∨ j ∈ S₂ := fun j =>
        (hB_side j).imp (fun h => Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩)
          (fun h => Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩)
      let e₁ : Fin S₁.card ≃ S₁ := (Fintype.equivFinOfCardEq (Fintype.card_coe S₁)).symm
      let e₂ : Fin S₂.card ≃ S₂ := (Fintype.equivFinOfCardEq (Fintype.card_coe S₂)).symm
      have hcard₁ : S₁.card < k + 1 := lt_of_le_of_lt (Finset.card_le_univ S₁ |>.trans (by simp)) (Nat.lt_succ_self k)
      have hcard₂ : S₂.card < k + 1 := lt_of_le_of_lt (Finset.card_le_univ S₂ |>.trans (by simp)) (Nat.lt_succ_self k)
      obtain ⟨α₁, hα₁fix, hα₁im⟩ := ih S₁.card hcard₁ (inter_subset_left.trans hK_sub) hK₁_conv hK₁_cl hK₁_int
        (A := fun r => B (e₁ r).1) (u := fun r => u (e₁ r).1.succ) (v := fun r => v (e₁ r).1.succ)
        (fun r => huv (e₁ r).1.succ)
        (fun r z hz => ⟨hB_sub _ hz, le_of_lt ((Finset.mem_filter.mp (e₁ r).2).2 z hz)⟩)
        (fun r => hB_line (e₁ r).1)
        (fun r => by
          ext z; constructor
          · rintro ⟨hzB, hzfr₁⟩
            have hfz : 0 < f z := (Finset.mem_filter.mp (e₁ r).2).2 z hzB
            have hzfr : z ∈ frontier K := ⟨subset_closure (hB_sub _ hzB), fun hzI => hzfr₁.2 (by rw [hint₁_eq]; exact ⟨hzI, hfz⟩)⟩
            exact hB_bd (e₁ r).1 ▸ ⟨hzB, hzfr⟩
          · intro hz
            have hz' : z ∈ B (e₁ r).1 ∩ frontier K := hB_bd (e₁ r).1 ▸ hz
            exact ⟨hz'.1, ⟨hK₁_cl.closure_eq ▸ ⟨hB_sub _ hz'.1, le_of_lt ((Finset.mem_filter.mp (e₁ r).2).2 z hz'.1)⟩,
              fun hzI => hz'.2.2 (interior_mono inter_subset_left hzI)⟩⟩)
        (fun r₁ r₂ hne => Set.disjoint_image_of_injective α₀.injective
          (hA_disj (fun h => hne (e₁.injective (Subtype.ext (Fin.succ_injective k h))))))
        (fun r => hu_sph (e₁ r).1.succ) (fun r => hv_sph (e₁ r).1.succ)
        (fun r z hz => by
          rw [hint₁_eq]; refine ⟨hseg_int _ hz, ?_⟩
          obtain ⟨a, b, ha, hb, hab, rfl⟩ := hz
          show 0 < f (a • u (e₁ r).1.succ + b • v (e₁ r).1.succ)
          rw [hf_affine a b _ _ hab]
          exact add_pos (mul_pos ha ((Finset.mem_filter.mp (e₁ r).2).2 _ (hB_line _).left_mem))
            (mul_pos hb ((Finset.mem_filter.mp (e₁ r).2).2 _ (hB_line _).right_mem)))
      obtain ⟨α₂, hα₂fix, hα₂im⟩ := ih S₂.card hcard₂ (inter_subset_left.trans hK_sub) hK₂_conv hK₂_cl hK₂_int
        (A := fun r => B (e₂ r).1) (u := fun r => u (e₂ r).1.succ) (v := fun r => v (e₂ r).1.succ)
        (fun r => huv (e₂ r).1.succ)
        (fun r z hz => ⟨hB_sub _ hz, le_of_lt ((Finset.mem_filter.mp (e₂ r).2).2 z hz)⟩)
        (fun r => hB_line (e₂ r).1)
        (fun r => by
          ext z; constructor
          · rintro ⟨hzB, hzfr₂⟩
            have hfz : f z < 0 := (Finset.mem_filter.mp (e₂ r).2).2 z hzB
            have hzfr : z ∈ frontier K := ⟨subset_closure (hB_sub _ hzB), fun hzI => hzfr₂.2 (by rw [hint₂_eq]; exact ⟨hzI, hfz⟩)⟩
            exact hB_bd (e₂ r).1 ▸ ⟨hzB, hzfr⟩
          · intro hz
            have hz' : z ∈ B (e₂ r).1 ∩ frontier K := hB_bd (e₂ r).1 ▸ hz
            exact ⟨hz'.1, ⟨hK₂_cl.closure_eq ▸ ⟨hB_sub _ hz'.1, le_of_lt ((Finset.mem_filter.mp (e₂ r).2).2 z hz'.1)⟩,
              fun hzI => hz'.2.2 (interior_mono inter_subset_left hzI)⟩⟩)
        (fun r₁ r₂ hne => Set.disjoint_image_of_injective α₀.injective
          (hA_disj (fun h => hne (e₂.injective (Subtype.ext (Fin.succ_injective k h))))))
        (fun r => hu_sph (e₂ r).1.succ) (fun r => hv_sph (e₂ r).1.succ)
        (fun r z hz => by
          rw [hint₂_eq]; refine ⟨hseg_int _ hz, ?_⟩
          obtain ⟨a, b, ha, hb, hab, rfl⟩ := hz
          show f (a • u (e₂ r).1.succ + b • v (e₂ r).1.succ) < 0
          rw [hf_affine a b _ _ hab]
          exact add_neg (mul_neg_of_pos_of_neg ha ((Finset.mem_filter.mp (e₂ r).2).2 _ (hB_line _).left_mem))
            (mul_neg_of_pos_of_neg hb ((Finset.mem_filter.mp (e₂ r).2).2 _ (hB_line _).right_mem)))
      -- Step 4: Compose `α := α₀.trans (α₁.trans α₂)`
      let α : ℂ ≃ₜ ℂ := α₀.trans (α₁.trans α₂)
      have hα_fix : ∀ x ∈ (interior K)ᶜ, α x = x := fun x hx => by
        simp only [α, Homeomorph.trans_apply]
        rw [hα₀fix x hx, hα₁fix x (fun h => hx (interior_mono inter_subset_left h)),
          hα₂fix x (fun h => hx (interior_mono inter_subset_left h))]
      have hα₁_fix_K₂ : ∀ x ∈ K₂, α₁ x = x := fun x hx =>
        hα₁fix x fun h => by
          have h1 : 0 < f x := (hint₁_eq ▸ h : x ∈ interior K ∩ {z | 0 < f z}).2
          have h2 : f x ≤ 0 := hx.2
          linarith
      have hα₂_fix_K₁ : ∀ x ∈ K₁, α₂ x = x := fun x hx =>
        hα₂fix x fun h => by
          have h1 : f x < 0 := (hint₂_eq ▸ h : x ∈ interior K ∩ {z | f z < 0}).2
          have h2 : 0 ≤ f x := hx.2
          linarith
      have hα_im : ∀ i : Fin (k + 1), α '' A i = segment ℝ (u i) (v i) := by
        intro i
        refine Fin.cases ?_ (fun j => ?_) i
        · change (α₂ ∘ α₁ ∘ α₀) '' A 0 = seg₀
          rw [Set.image_comp, Set.image_comp, hα₀A]
          ext z; constructor
          · rintro ⟨w, ⟨y, hy, rfl⟩, rfl⟩
            have hy0 : f y = 0 := (hf_zero_iff y (hseg₀_sub hy)).mpr hy
            rw [hα₁_fix_K₂ y ⟨hseg₀_sub hy, le_of_eq hy0⟩, hα₂_fix_K₁ y ⟨hseg₀_sub hy, le_of_eq hy0.symm⟩]; exact hy
          · intro hz
            have hz0 : f z = 0 := (hf_zero_iff z (hseg₀_sub hz)).mpr hz
            exact ⟨z, ⟨z, hz, hα₁_fix_K₂ z ⟨hseg₀_sub hz, le_of_eq hz0⟩⟩, hα₂_fix_K₁ z ⟨hseg₀_sub hz, le_of_eq hz0.symm⟩⟩
        · change (α₂ ∘ α₁ ∘ α₀) '' A j.succ = segment ℝ (u j.succ) (v j.succ)
          rw [Set.image_comp, Set.image_comp]
          change α₂ '' (α₁ '' B j) = segment ℝ (u j.succ) (v j.succ)
          rcases hS_cov j with hj₁ | hj₂
          · let r := e₁.symm ⟨j, hj₁⟩
            have hr : (e₁ r).1 = j := congrArg Subtype.val (e₁.apply_symm_apply ⟨j, hj₁⟩)
            have h1 : α₁ '' B j = segment ℝ (u j.succ) (v j.succ) := by
              have := hα₁im r; rwa [hr] at this
            rw [h1]
            ext z; constructor
            · rintro ⟨w, hw, rfl⟩
              have hwK₁ : w ∈ K₁ := by
                refine ⟨hK_conv.segment_subset (hB_sub j (hB_line j).left_mem) (hB_sub j (hB_line j).right_mem) hw, ?_⟩
                obtain ⟨a, b, ha, hb, hab, rfl⟩ := hw
                show 0 ≤ f (a • u j.succ + b • v j.succ)
                rw [hf_affine a b _ _ hab]
                exact add_nonneg (mul_nonneg ha (le_of_lt ((Finset.mem_filter.mp hj₁).2 _ (hB_line j).left_mem)))
                  (mul_nonneg hb (le_of_lt ((Finset.mem_filter.mp hj₁).2 _ (hB_line j).right_mem)))
              rwa [hα₂_fix_K₁ w hwK₁]
            · intro hz
              have hzK₁ : z ∈ K₁ := by
                refine ⟨hK_conv.segment_subset (hB_sub j (hB_line j).left_mem) (hB_sub j (hB_line j).right_mem) hz, ?_⟩
                obtain ⟨a, b, ha, hb, hab, rfl⟩ := hz
                show 0 ≤ f (a • u j.succ + b • v j.succ)
                rw [hf_affine a b _ _ hab]
                exact add_nonneg (mul_nonneg ha (le_of_lt ((Finset.mem_filter.mp hj₁).2 _ (hB_line j).left_mem)))
                  (mul_nonneg hb (le_of_lt ((Finset.mem_filter.mp hj₁).2 _ (hB_line j).right_mem)))
              exact ⟨z, hz, hα₂_fix_K₁ z hzK₁⟩
          · let r := e₂.symm ⟨j, hj₂⟩
            have hr : (e₂ r).1 = j := congrArg Subtype.val (e₂.apply_symm_apply ⟨j, hj₂⟩)
            have h1 : α₁ '' B j = B j := by
              ext z; constructor
              · rintro ⟨w, hw, rfl⟩
                rwa [hα₁_fix_K₂ w ⟨hB_sub j hw, le_of_lt ((Finset.mem_filter.mp hj₂).2 w hw)⟩]
              · intro hz
                exact ⟨z, hz, hα₁_fix_K₂ z ⟨hB_sub j hz, le_of_lt ((Finset.mem_filter.mp hj₂).2 z hz)⟩⟩
            rw [h1]
            have := hα₂im r; rwa [hr] at this
      exact ⟨α, hα_fix, hα_im⟩

/-! ### Section 3: Straightening a matching on any closed disc surface -/

/-- Straighten a matching of `n` pairwise disjoint proper `I`-arcs on `closedBall (0 : ℂ) 1`
to Euclidean straight chords via a boundary-fixing homeomorphism. -/
theorem straighten_disc_matching {n : ℕ}
    {A : Fin n → Set (closedBall (0 : ℂ) 1)}
    (hA : ∀ i, ∃ u v, u ≠ v ∧ IsLineWithEnds (A i) u v ∧ A i ∩ bd (closedBall (0 : ℂ) 1) = {u, v})
    (hAdisj : Pairwise fun i j => Disjoint (A i) (A j)) :
    ∃ (α : closedBall (0 : ℂ) 1 ≃ₜ closedBall (0 : ℂ) 1),
      (∀ x ∈ bd (closedBall (0 : ℂ) 1), α x = x) ∧
      (∀ i, ∃ u v : ℂ, u ∈ sphere (0 : ℂ) 1 ∧ v ∈ sphere (0 : ℂ) 1 ∧ u ≠ v ∧
        Subtype.val '' (A i ∩ bd (closedBall (0 : ℂ) 1)) = {u, v} ∧
        Subtype.val '' (α '' A i) = segment ℝ u v) := by
  classical
  have hbd_eq : Subtype.val '' bd (closedBall (0 : ℂ) 1) = sphere (0 : ℂ) 1 := isClosedDisc_closedBall.2
  have hbd_iff : ∀ x : closedBall (0 : ℂ) 1, x ∈ bd (closedBall (0 : ℂ) 1) ↔ x.1 ∈ sphere (0 : ℂ) 1 := fun x => by
    constructor
    · intro hx; exact hbd_eq ▸ ⟨x, hx, rfl⟩
    · intro hx; obtain ⟨y, hy, hye⟩ := hbd_eq.symm ▸ hx; exact Subtype.ext hye ▸ hy
  have hint_ball : interior (closedBall (0 : ℂ) 1) = ball (0 : ℂ) 1 := interior_closedBall _ one_ne_zero
  have hfr_ball : frontier (closedBall (0 : ℂ) 1) = sphere (0 : ℂ) 1 := frontier_closedBall _ one_ne_zero
  choose u v huv hAl hAb using hA
  let Aℂ : Fin n → Set ℂ := fun i => Subtype.val '' A i
  have hAℂ_line : ∀ i, IsLineWithEnds (Aℂ i) (u i).1 (v i).1 := fun i => by
    obtain ⟨φ, hφ0, hφ1⟩ := hAl i
    let eSub : A i ≃ₜ Aℂ i :=
      { toFun := fun x => ⟨x.1.1, ⟨x.1, x.2, rfl⟩⟩
        invFun := fun y => ⟨⟨y.1, by rcases y.2 with ⟨w, -, hwe⟩; exact hwe ▸ w.2⟩,
          by rcases y.2 with ⟨w, hw, hwe⟩; have hEq : w = ⟨y.1, hwe ▸ w.2⟩ := Subtype.ext hwe; exact hEq ▸ hw⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl
        continuous_toFun := Continuous.subtype_mk (continuous_subtype_val.comp continuous_subtype_val) _
        continuous_invFun := Continuous.subtype_mk
          (Continuous.subtype_mk continuous_subtype_val fun y => by rcases y.2 with ⟨w, -, hwe⟩; exact hwe ▸ w.2)
          (fun y => by rcases y.2 with ⟨w, hw, hwe⟩; have hEq : w = ⟨y.1, hwe ▸ w.2⟩ := Subtype.ext hwe; exact hEq ▸ hw) }
    exact ⟨φ.trans eSub, by show (φ 0).1.1 = (u i).1; rw [hφ0], by show (φ 1).1.1 = (v i).1; rw [hφ1]⟩
  have hu_sph : ∀ i, (u i).1 ∈ sphere (0 : ℂ) 1 := fun i =>
    (hbd_iff (u i)).mp (hAb i ▸ Or.inl rfl : u i ∈ A i ∩ bd _).2
  have hv_sph : ∀ i, (v i).1 ∈ sphere (0 : ℂ) 1 := fun i =>
    (hbd_iff (v i)).mp (hAb i ▸ Or.inr rfl : v i ∈ A i ∩ bd _).2
  obtain ⟨αℂ, hαℂ_fix, hαℂ_im⟩ := straighten_disc_matching_convex n subset_rfl
    (convex_closedBall 0 1) isClosed_closedBall ⟨0, hint_ball ▸ mem_ball_self zero_lt_one⟩
    (A := Aℂ) (u := fun i => (u i).1) (v := fun i => (v i).1)
    (fun i h => huv i (Subtype.ext h))
    (fun i _ ⟨x, _, hxe⟩ => hxe ▸ x.2)
    hAℂ_line
    (fun i => by
      rw [hfr_ball]; ext z; constructor
      · rintro ⟨⟨x, hxA, rfl⟩, hxsph⟩
        have hxbd : x ∈ A i ∩ bd (closedBall (0 : ℂ) 1) := ⟨hxA, (hbd_iff x).mpr hxsph⟩
        rw [hAb i] at hxbd
        rcases hxbd with rfl | h
        · exact Or.inl rfl
        · exact Or.inr (congrArg Subtype.val (mem_singleton_iff.mp h))
      · rintro (rfl | h)
        · exact ⟨⟨u i, (hAl i).left_mem, rfl⟩, hu_sph i⟩
        · rw [mem_singleton_iff.mp h]; exact ⟨⟨v i, (hAl i).right_mem, rfl⟩, hv_sph i⟩)
    (fun i j hne => Set.disjoint_image_of_injective Subtype.val_injective (hAdisj hne))
    hu_sph hv_sph
    (fun i z hz => by
      rw [hint_ball, mem_ball_zero_iff]
      exact norm_lt_one_of_openSegment (mem_sphere_zero_iff_norm.mp (hu_sph i))
        (mem_sphere_zero_iff_norm.mp (hv_sph i)) (fun h => huv i (Subtype.ext h)) hz)
  have hαℂ_mem : ∀ x : closedBall (0 : ℂ) 1, αℂ x.1 ∈ closedBall (0 : ℂ) 1 := fun x => by
    by_cases hx : x.1 ∈ interior (closedBall (0 : ℂ) 1)
    · by_contra hnot
      have hnotI : αℂ x.1 ∈ (interior (closedBall (0 : ℂ) 1))ᶜ := fun h => hnot (interior_subset h)
      have := αℂ.injective (hαℂ_fix (αℂ x.1) hnotI)
      exact hnot (this.symm ▸ x.2)
    · rw [hαℂ_fix x.1 hx]; exact x.2
  have hαℂ_symm_mem : ∀ x : closedBall (0 : ℂ) 1, αℂ.symm x.1 ∈ closedBall (0 : ℂ) 1 := fun x => by
    by_cases hx : x.1 ∈ interior (closedBall (0 : ℂ) 1)
    · by_contra hnot
      have hnotI : αℂ.symm x.1 ∈ (interior (closedBall (0 : ℂ) 1))ᶜ := fun h => hnot (interior_subset h)
      have h1 := hαℂ_fix (αℂ.symm x.1) hnotI
      rw [αℂ.apply_symm_apply] at h1
      exact hnot (h1 ▸ x.2)
    · have h1 : αℂ.symm x.1 = x.1 := αℂ.injective (by rw [αℂ.apply_symm_apply, hαℂ_fix x.1 hx])
      rw [h1]; exact x.2
  let α : closedBall (0 : ℂ) 1 ≃ₜ closedBall (0 : ℂ) 1 :=
    { toFun := fun x => ⟨αℂ x.1, hαℂ_mem x⟩
      invFun := fun x => ⟨αℂ.symm x.1, hαℂ_symm_mem x⟩
      left_inv := fun x => Subtype.ext (αℂ.symm_apply_apply x.1)
      right_inv := fun x => Subtype.ext (αℂ.apply_symm_apply x.1)
      continuous_toFun := Continuous.subtype_mk (αℂ.continuous.comp continuous_subtype_val) _
      continuous_invFun := Continuous.subtype_mk (αℂ.symm.continuous.comp continuous_subtype_val) _ }
  refine ⟨α, fun x hx => ?_, fun i => ?_⟩
  · apply Subtype.ext
    have hxsph : x.1 ∈ sphere (0 : ℂ) 1 := (hbd_iff x).mp hx
    have hnotI : x.1 ∈ (interior (closedBall (0 : ℂ) 1))ᶜ := by
      rw [hint_ball, mem_compl_iff, mem_ball_zero_iff, mem_sphere_zero_iff_norm.mp hxsph]; norm_num
    exact hαℂ_fix x.1 hnotI
  · refine ⟨(u i).1, (v i).1, hu_sph i, hv_sph i, fun h => huv i (Subtype.ext h), ?_, ?_⟩
    · rw [hAb i]; simp
    · have heq : Subtype.val '' (α '' A i) = αℂ '' Aℂ i := by
        ext z; simp only [mem_image, α, Aℂ]; constructor
        · rintro ⟨_, ⟨x, hxA, rfl⟩, rfl⟩; exact ⟨x.1, ⟨x, hxA, rfl⟩, rfl⟩
        · rintro ⟨_, ⟨x, hxA, rfl⟩, rfl⟩; exact ⟨⟨αℂ x.1, hαℂ_mem x⟩, ⟨x, hxA, rfl⟩, rfl⟩
      rw [heq, hαℂ_im i]

/-- **LPPS22 Disc Matching Lemma**:
On any closed disc surface `D` (homeomorphic to `closedBall (0 : ℂ) 1`), given two matchings
`M : Fin n → Set D` and `L : Fin m → Set D` with disjoint boundary endpoints, there exists a
boundary-fixing homeomorphism `φ : D ≃ₜ D` such that `φ '' M j ∩ L i` has at most `1` point
for all `j, i`. -/
theorem lpps22_disc_matching {D : Type} [TopologicalSpace D]
    (e : D ≃ₜ closedBall (0 : ℂ) 1) {n m : ℕ}
    {M : Fin n → Set D} {L : Fin m → Set D}
    (hM : ∀ j, ∃ s t, s ≠ t ∧ IsLineWithEnds (M j) s t ∧ M j ∩ bd D = {s, t})
    (hMdisj : Pairwise fun j₁ j₂ => Disjoint (M j₁) (M j₂))
    (hL : ∀ i, ∃ u v, u ≠ v ∧ IsLineWithEnds (L i) u v ∧ L i ∩ bd D = {u, v})
    (hLdisj : Pairwise fun i₁ i₂ => Disjoint (L i₁) (L i₂))
    (hbd_disj : ∀ j i, Disjoint (M j ∩ bd D) (L i ∩ bd D)) :
    ∃ φ : D ≃ₜ D, (∀ x ∈ bd D, φ x = x) ∧
      (∀ j i, (φ '' M j ∩ L i).Finite ∧ (φ '' M j ∩ L i).ncard ≤ 1) := by
  have he_bd : e '' bd D = bd (closedBall (0 : ℂ) 1) := image_bd_homeomorph e
  have hM' : ∀ j, ∃ s t, s ≠ t ∧ IsLineWithEnds (e '' M j) s t ∧ (e '' M j) ∩ bd (closedBall (0 : ℂ) 1) = {s, t} := by
    intro j; obtain ⟨s, t, hst, hMl, hMb⟩ := hM j
    obtain ⟨f, hf0, hf1⟩ := hMl
    refine ⟨e s, e t, fun h => hst (e.injective h), ⟨f.trans (e.image (M j)), ?_, ?_⟩, ?_⟩
    · show e (f 0).1 = e s; rw [hf0]
    · show e (f 1).1 = e t; rw [hf1]
    · rw [← he_bd, ← Set.image_inter e.injective, hMb, Set.image_pair]
  have hL' : ∀ i, ∃ u v, u ≠ v ∧ IsLineWithEnds (e '' L i) u v ∧ (e '' L i) ∩ bd (closedBall (0 : ℂ) 1) = {u, v} := by
    intro i; obtain ⟨u, v, huv, hLl, hLb⟩ := hL i
    obtain ⟨f, hf0, hf1⟩ := hLl
    refine ⟨e u, e v, fun h => huv (e.injective h), ⟨f.trans (e.image (L i)), ?_, ?_⟩, ?_⟩
    · show e (f 0).1 = e u; rw [hf0]
    · show e (f 1).1 = e v; rw [hf1]
    · rw [← he_bd, ← Set.image_inter e.injective, hLb, Set.image_pair]
  obtain ⟨αM, hαMfix, hαMseg⟩ := straighten_disc_matching hM'
    (fun j₁ j₂ hne => Set.disjoint_image_of_injective e.injective (hMdisj hne))
  obtain ⟨αL, hαLfix, hαLseg⟩ := straighten_disc_matching hL'
    (fun i₁ i₂ hne => Set.disjoint_image_of_injective e.injective (hLdisj hne))
  let ψ : closedBall (0 : ℂ) 1 ≃ₜ closedBall (0 : ℂ) 1 := αM.trans αL.symm
  let φ : D ≃ₜ D := (e.trans ψ).trans e.symm
  have hψfix : ∀ y ∈ bd (closedBall (0 : ℂ) 1), ψ y = y := fun y hy => by
    simp only [ψ, Homeomorph.trans_apply, hαMfix y hy]
    exact αL.injective (by rw [αL.apply_symm_apply, hαLfix y hy])
  refine ⟨φ, fun x hx => ?_, fun j i => ?_⟩
  · simp only [φ, Homeomorph.trans_apply]
    rw [hψfix (e x) (he_bd ▸ mem_image_of_mem e hx), e.symm_apply_apply]
  · obtain ⟨s, t, hs, ht, hst, hMbd, hMseg⟩ := hαMseg j
    obtain ⟨u, v, hu, hv, huv, hLbd, hLseg⟩ := hαLseg i
    have hdisj_stuv : Disjoint ({s, t} : Set ℂ) {u, v} := by
      rw [← hMbd, ← hLbd]
      refine Set.disjoint_image_of_injective Subtype.val_injective ?_
      rw [← he_bd, ← Set.image_inter e.injective, ← Set.image_inter e.injective]
      exact Set.disjoint_image_of_injective e.injective (hbd_disj j i)
    obtain ⟨hfin, hcard⟩ := segment_inter_le_one hs ht hu hv hst huv hdisj_stuv
    have heq : Subtype.val '' (αL '' (e '' (φ '' M j ∩ L i))) = segment ℝ s t ∩ segment ℝ u v := by
      rw [Set.image_inter e.injective, Set.image_inter αL.injective, Set.image_inter Subtype.val_injective]
      have h1 : αL '' (e '' (φ '' M j)) = αM '' (e '' M j) := by
        ext y; simp only [φ, ψ, Homeomorph.trans_apply, mem_image]
        constructor
        · rintro ⟨w, ⟨z, ⟨x, hxM, rfl⟩, rfl⟩, rfl⟩
          rw [e.apply_symm_apply, αL.apply_symm_apply]
          exact ⟨e x, ⟨x, hxM, rfl⟩, rfl⟩
        · rintro ⟨_, ⟨x, hxM, rfl⟩, rfl⟩
          exact ⟨e (e.symm (αL.symm (αM (e x)))), ⟨e.symm (αL.symm (αM (e x))), ⟨x, hxM, rfl⟩, rfl⟩,
            by rw [e.apply_symm_apply, αL.apply_symm_apply]⟩
      rw [h1, hMseg, hLseg]
    have hinj : Function.Injective (fun x : D => (αL (e x)).1) :=
      Subtype.val_injective.comp (αL.injective.comp e.injective)
    have him : (fun x : D => (αL (e x)).1) '' (φ '' M j ∩ L i) = segment ℝ s t ∩ segment ℝ u v := by
      rw [← heq, Set.image_image, Set.image_image]
    exact ⟨Set.Finite.of_finite_image (him.symm ▸ hfin) hinj.injOn,
      by rw [← Set.ncard_image_of_injective _ hinj, him]; exact hcard⟩

end GraphMinor.LPPS22
