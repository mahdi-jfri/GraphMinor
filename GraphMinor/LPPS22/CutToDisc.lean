module

public import GraphMinor.Surface.CutIArc
public import GraphMinor.GHR18.Theorem13
public import GraphMinor.LPPS22.DiscMatching

/-!
# Cutting a Surface with Boundary to a Closed Disc (LPPS22 Lemmas A.4 and A.5)

Given a connected compact surface `S ≃ₜ SurfaceModel a b c` with `c ≥ 1`, a closed forbidden
boundary set `K ⊆ bd S` containing no cuff, and a matching `G : Fin n → Set S` with endpoints
disjoint from `K`, we construct a non-separating matching `N` of size `2 * a + b + c - 1`
consisting of a subset `G₀ ⊆ G` together with new proper `I`-arcs disjoint from `G` and avoiding
`K` (`exists_disc_cutting_matching`).

Cutting `S` sequentially along `N` reduces the Euler invariant `2 * a + b + c - 1` by `1` at each
step (`cut_iArc_euler_connected`), terminating in `SurfaceModel 0 0 1 ≃ₜ closedBall (0 : ℂ) 1`.
-/

@[expose] public section

namespace GraphMinor.LPPS22

open Set Topology Metric Complex Function GraphMinor.Surface GraphMinor.GHR18

/-! ### Section 1: Exact Euler invariant for cutting along a proper `I`-arc -/

/-- Cutting a connected surface `S ≃ₜ SurfaceModel a b c` along a non-separating proper `I`-arc `F`
gives a connected surface `Y ≃ₜ SurfaceModel a' b' c'` with `1 ≤ c'` and
`2 * a' + b' + c' + 1 = 2 * a + b + c`. -/
theorem cut_iArc_euler_connected {S Y : Type} [TopologicalSpace S] [ConnectedSpace S]
    [TopologicalSpace Y] [T2Space Y] (hS : IsSurface S) (hY : IsSurface Y)
    {a b c : ℕ} (eS : S ≃ₜ SurfaceModel a b c)
    {F : Set S} {s t : S} (_hst : s ≠ t) (_hFb : F ∩ bd S = {s, t}) (hFl : IsLineWithEnds F s t)
    {ψ : Y → S} (hψ : IsCutting ψ F) {X X' : Set Y} (hP : LiftPair ψ F s t X X')
    [hYc : ConnectedSpace Y] :
    ∃ a' b' c' : ℕ, Nonempty (Y ≃ₜ SurfaceModel a' b' c') ∧ 1 ≤ c' ∧
      2 * a' + b' + c' + 1 = 2 * a + b + c := by
  have hcS : CompactSpace S := hS.1
  have ht2S : T2Space S := hS.2.1
  have hcY : CompactSpace Y := hY.1
  have hFc : IsClosed F := hFl.isCompact.isClosed
  obtain ⟨a₀, ξ, η, L, ha0, ha1, himξ, himη, hiξ, hiη⟩ := exists_arcLift hP hψ
  obtain ⟨x0, x1, y0, y1, l1, l2, hd, hun, -, -, -, -, -, -⟩ := hP
  have hub : ψ ⁻¹' F = ξ '' Icc 0 1 ∪ η '' Icc 0 1 := by rw [himξ, himη, hun]
  have hXb : X ⊆ bd Y := fun z hz => hψ.2.2.2.2 (hun ▸ Or.inl hz)
  have hXb' : X' ⊆ bd Y := fun z hz => hψ.2.2.2.2 (hun ▸ Or.inr hz)
  have pX : IsPreconnected X := himξ ▸ isPreconnected_Icc.image _ L.cξ
  have pX' : IsPreconnected X' := himη ▸ isPreconnected_Icc.image _ L.cη
  have hex : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := by simp
  have hx : ξ 0 ∈ X := himξ ▸ ⟨0, hex, rfl⟩
  have hy : η 0 ∈ X' := himη ▸ ⟨0, hex, rfl⟩
  have hξm : ∀ u ∈ Icc (0 : ℝ) 1, ξ u ∈ X := fun u hu => himξ ▸ ⟨u, hu, rfl⟩
  have hηm : ∀ u ∈ Icc (0 : ℝ) 1, η u ∈ X' := fun u hu => himη ▸ ⟨u, hu, rfl⟩
  have hdcuff := cuff_statement.{0} Y hY
  obtain ⟨a', b', c', ⟨e⟩⟩ := classification.{0} Y hY hYc
  have hC : connectedComponentIn (bd Y) (ξ 0) ∈ cuffs Y := ⟨_, hXb hx, rfl⟩
  have hC' : connectedComponentIn (bd Y) (η 0) ∈ cuffs Y := ⟨_, hXb' hy, rfl⟩
  have hXC := pX.subset_connectedComponentIn hx hXb
  have hXC' := pX'.subset_connectedComponentIn hy hXb'
  have hcrit : ∀ {a₂ b₂ c₂ : ℕ}, Nonempty (S ≃ₜ SurfaceModel a₂ b₂ c₂) →
      c₂ = c ∧ 2 * a₂ + b₂ = 2 * a + b := fun {a₂ b₂ c₂} ⟨e₂⟩ => by
    have := (modelCriterion.2 a₂ b₂ c₂ a b c).mp ⟨e₂.symm.trans eS⟩
    exact ⟨this.1, this.2.1⟩
  by_cases hCC : connectedComponentIn (bd Y) (ξ 0) = connectedComponentIn (bd Y) (η 0)
  · obtain ⟨i, hi, φ, g, hg, hs⟩ := exists_one_hole e hC
    obtain ⟨a₁, ξ', η', m, L', -, hxim, heim, hix, hie, hmc, hmm, hmξ⟩ :=
      orient_lift L φ (fun u hu => hXC (hξm u hu)) hiξ hiη
    obtain ⟨hN, hLf⟩ := erase_facts c' i
    have hξ' : ∀ u ∈ Icc (0 : ℝ) 1, ξ' u ∈ X := fun u hu => by rw [← himξ, ← hxim]; exact ⟨u, hu, rfl⟩
    have hη' : ∀ u ∈ Icc (0 : ℝ) 1, η' u ∈ X' := fun u hu => by rw [← himη, ← heim]; exact ⟨u, hu, rfl⟩
    obtain ⟨σ, g', hp, -⟩ := arc_one_aux hY L' hψ.1 hψ.2.1 hC φ hi hLf hg hs hmc hmm hmξ
      (fun u hu => hCC ▸ hXC' (hη' u hu)) hix hie
      (fun u hu v hv he => Set.disjoint_left.mp hd (hξ' u hu) (he ▸ hη' v hv))
    have hn := nf_blkB (a := a') (b := b') (c := c') hi hN hLf σ
    have hlen := length_erase_range hi
    have : Nonempty S := ⟨s⟩
    cases σ with
    | false =>
      obtain ⟨w, h5, h6⟩ := hn.1 rfl
      obtain ⟨e'⟩ := homeo_of_nf hp h5 h6
      obtain ⟨hc_eq, h2ab⟩ := hcrit ⟨e'⟩
      refine ⟨a', b', c', ⟨e⟩, by omega, by omega⟩
    | true =>
      obtain ⟨w, h5, h6⟩ := hn.2 rfl
      obtain ⟨e'⟩ := homeo_of_nf hp h5 h6
      obtain ⟨hc_eq, h2ab⟩ := hcrit ⟨e'⟩
      refine ⟨a', b', c', ⟨e⟩, by omega, by omega⟩
  · have hdis := cuffs_disjoint hC hC' hCC
    obtain ⟨i, hi, j, hj, hij, φ, φ', g, hg, hs, hs'⟩ := exists_two_holes e hC hC' hCC
    obtain ⟨a₁, ξ', η', m, L', -, hxim, heim, hix, hie, hmc, hmm, hmξ⟩ :=
      orient_lift L φ (fun u hu => hXC (hξm u hu)) hiξ hiη
    obtain ⟨hN, hLf⟩ := erase_erase_facts c' i j
    have hη' : ∀ u ∈ Icc (0 : ℝ) 1, η' u ∈ X' := fun u hu => by rw [← himη, ← heim]; exact ⟨u, hu, rfl⟩
    obtain ⟨σ, g', hp, -⟩ := arc_two_aux hY L' hψ.1 hψ.2.1 hC hC' (hdcuff.2.2 _ hC).isCompact.isClosed
      (hdcuff.2.2 _ hC').isCompact.isClosed hdis φ φ' hij hi hj hLf hg hs hs' hmc hmm hmξ
      (fun u hu => hXC' (hη' u hu)) hix hie
    have hn := nf_blkA (a := a') (b := b') (c := c') hij hi hj hN hLf σ
    have hlen := length_erase_erase hij hi hj
    have : Nonempty S := ⟨s⟩
    cases σ with
    | false =>
      obtain ⟨w, h5, h6⟩ := hn.1 rfl
      obtain ⟨e'⟩ := homeo_of_nf hp h5 h6
      obtain ⟨hc_eq, h2ab⟩ := hcrit ⟨e'⟩
      refine ⟨a', b', c', ⟨e⟩, by omega, by omega⟩
    | true =>
      obtain ⟨w, h5, h6⟩ := hn.2 rfl
      obtain ⟨e'⟩ := homeo_of_nf hp h5 h6
      obtain ⟨hc_eq, h2ab⟩ := hcrit ⟨e'⟩
      refine ⟨a', b', c', ⟨e⟩, by omega, by omega⟩

/-- Cutting a connected surface `S ≃ₜ SurfaceModel a b c` along a separating proper `I`-arc `F`
gives two clopen disjoint connected components `W₁, W₂` whose Euler invariants sum to
`2 * a + b + c - 1`. -/
theorem cut_iArc_euler_sep {S Y : Type} [TopologicalSpace S] [ConnectedSpace S]
    [TopologicalSpace Y] [T2Space Y] (hS : IsSurface S) (hY : IsSurface Y)
    {a b c : ℕ} (eS : S ≃ₜ SurfaceModel a b c)
    {F : Set S} {s t : S} (_hst : s ≠ t) (_hFb : F ∩ bd S = {s, t}) (_hFl : IsLineWithEnds F s t)
    {ψ : Y → S} (hψ : IsCutting ψ F) {X X' : Set Y} (hP : LiftPair ψ F s t X X')
    (hnotc : ¬ ConnectedSpace Y) :
    ∃ (W₁ W₂ : Set Y), IsClopen W₁ ∧ IsClopen W₂ ∧ Disjoint W₁ W₂ ∧ W₁ ∪ W₂ = univ ∧
      X ⊆ W₁ ∧ X' ⊆ W₂ ∧ ConnectedSpace W₁ ∧ ConnectedSpace W₂ ∧
      ∃ a₁ b₁ c₁ a₂ b₂ c₂ : ℕ,
        Nonempty (W₁ ≃ₜ SurfaceModel a₁ b₁ c₁) ∧ Nonempty (W₂ ≃ₜ SurfaceModel a₂ b₂ c₂) ∧
        1 ≤ c₁ ∧ 1 ≤ c₂ ∧
        (2 * a₁ + b₁ + c₁ - 1) + (2 * a₂ + b₂ + c₂ - 1) = 2 * a + b + c - 1 := by
  have hcS : CompactSpace S := hS.1
  have ht2S : T2Space S := hS.2.1
  have hcY : CompactSpace Y := hY.1
  obtain ⟨a₀, ξ, η, L, -, -, himξ, himη, hiξ, hiη⟩ := exists_arcLift hP hψ
  obtain ⟨-, -, -, -, -, -, -, hun, -, -, -, -, -, -⟩ := hP
  have hXb : X ⊆ bd Y := fun z hz => hψ.2.2.2.2 (hun ▸ Or.inl hz)
  have hXb' : X' ⊆ bd Y := fun z hz => hψ.2.2.2.2 (hun ▸ Or.inr hz)
  have pX : IsPreconnected X := himξ ▸ isPreconnected_Icc.image _ L.cξ
  have pX' : IsPreconnected X' := himη ▸ isPreconnected_Icc.image _ L.cη
  have hex : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := by simp
  have hx : ξ 0 ∈ X := himξ ▸ ⟨0, hex, rfl⟩
  have hy : η 0 ∈ X' := himη ▸ ⟨0, hex, rfl⟩
  rcases cut_comps hψ hY pX pX' hun hx hy with hYc | ⟨W₁, W₂, -, -, hX₁, hX₂, hW₁, hW₂, hU, hdW, hc₁, hc₂⟩
  · exact absurd hYc hnotc
  · obtain ⟨a₁, b₁, c₁, ⟨e₁⟩⟩ := classification.{0} W₁ (isSurface_sub hY hW₁) hc₁
    obtain ⟨a₂, b₂, c₂, ⟨e₂⟩⟩ := classification.{0} W₂ (isSurface_sub hY hW₂) hc₂
    obtain ⟨i, j, σ, a', f, hi, hj, -, -, hf, -⟩ := arc_comps_aux hY L hψ.1 hψ.2.1 hW₁ hW₂ hdW hU e₁ e₂
      (by rw [himξ]; exact hX₁) (by rw [himη]; exact hX₂) (by rw [himξ]; exact hXb) (by rw [himη]; exact hXb') hiξ hiη
    have : Nonempty S := ⟨s⟩
    obtain ⟨hN₁, hL₁⟩ := erase_facts c₁ i
    obtain ⟨hN₂, hL₂⟩ := erase_facts c₂ j
    obtain ⟨e'⟩ := homeo_of_two_arc hi hj hN₁ hN₂ hL₁ hL₂ hf
    have hlen₁ := length_erase_range hi
    have hlen₂ := length_erase_range hj
    have hcrit := (modelCriterion.2 (a₂ + a₁) (b₂ + b₁)
      (((List.range' 0 c₂).erase j).length + ((List.range' 0 c₁).erase i).length + 1) a b c).mp
      ⟨e'.symm.trans eS⟩
    refine ⟨W₁, W₂, hW₁, hW₂, hdW, hU, hX₁, hX₂, hc₁, hc₂, a₁, b₁, c₁, a₂, b₂, c₂, ⟨e₁⟩, ⟨e₂⟩,
      by omega, by omega, by omega⟩

/-! ### Section 2: Trig sign lemma and non-separating `I`-arc on `SurfaceModel a b c` -/

/-- Signed cross product `Im((z - a) * conj(b - a))`. -/
private noncomputable def crossIm (a b z : ℂ) : ℝ := ((z - a) * star (b - a)).im

private theorem crossIm_affine (a b x y : ℂ) (s t : ℝ) (hst : s + t = 1) :
    crossIm a b (s • x + t • y) = s * crossIm a b x + t * crossIm a b y := by
  have h1 : (s • x + t • y) - a = s • (x - a) + t • (y - a) := by
    have ha : a = s • a + t • a := by rw [← add_smul, hst, one_smul]
    conv_lhs => rw [ha]
    simp only [smul_sub]; abel
  dsimp only [crossIm]
  rw [h1, add_mul, Complex.add_im]
  simp only [Complex.real_smul, mul_assoc,
    Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero]

private theorem crossIm_cyc (a b c : ℂ) : crossIm a b c = crossIm b c a := by
  simp only [crossIm, Complex.star_def, Complex.mul_im, Complex.conj_re, Complex.conj_im,
    Complex.sub_re, Complex.sub_im]
  ring

private theorem crossIm_swap (a b c : ℂ) : crossIm a b c = - crossIm b a c := by
  simp only [crossIm, Complex.star_def, Complex.mul_im, Complex.conj_re, Complex.conj_im,
    Complex.sub_re, Complex.sub_im]
  ring

private theorem crossIm_cis_eq (α β γ : ℝ) :
    crossIm (cis' α) (cis' β) (cis' γ) =
      4 * Real.sin ((β - α) / 2) * Real.sin ((γ - β) / 2) * Real.sin ((γ - α) / 2) := by
  have hcis : ∀ θ : ℝ, cis' θ = ⟨Real.cos θ, Real.sin θ⟩ := fun θ => by
    apply Complex.ext <;> simp [cis', Complex.exp_mul_I, Complex.cos_ofReal_re,
      Complex.sin_ofReal_re, Complex.cos_ofReal_im, Complex.sin_ofReal_im]
  have h1 : crossIm (cis' α) (cis' β) (cis' γ) =
      Real.sin (γ - β) + Real.sin (β - α) - Real.sin (γ - α) := by
    simp only [crossIm, Complex.star_def, Complex.mul_im, Complex.conj_re, Complex.conj_im,
      Complex.sub_re, Complex.sub_im, hcis, Real.sin_sub]
    ring
  rw [h1]
  set u := (β - α) / 2
  set v := (γ - β) / 2
  have hu : β - α = 2 * u := by simp only [u]; ring
  have hv : γ - β = 2 * v := by simp only [v]; ring
  have huv : γ - α = 2 * (u + v) := by simp only [u, v]; ring
  rw [hu, hv, huv, show 2 * (u + v) / 2 = u + v by ring,
    Real.sin_two_mul, Real.sin_two_mul, Real.sin_two_mul, Real.sin_add, Real.cos_add]
  have hsu : Real.sin u ^ 2 + Real.cos u ^ 2 = 1 := Real.sin_sq_add_cos_sq u
  have hsv : Real.sin v ^ 2 + Real.cos v ^ 2 = 1 := Real.sin_sq_add_cos_sq v
  linear_combination -(2 * Real.sin v * Real.cos v) * hsu - (2 * Real.sin u * Real.cos u) * hsv

private theorem crossIm_per_pos {n : ℕ} (hn : 0 < n) {x y z : ℝ}
    (hxy : x < y) (hyz : y < z) (hzn : z - x < n) :
    0 < crossIm (per n x) (per n y) (per n z) := by
  rw [per, per, per, crossIm_cis_eq]
  have hn' : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hpi : 0 < Real.pi := Real.pi_pos
  have h1 : 0 < (2 * Real.pi * y / n - 2 * Real.pi * x / n) / 2 := by
    rw [show (2 * Real.pi * y / n - 2 * Real.pi * x / n) / 2 = Real.pi * (y - x) / n by ring]
    exact div_pos (mul_pos hpi (sub_pos.mpr hxy)) hn'
  have h1' : (2 * Real.pi * y / n - 2 * Real.pi * x / n) / 2 < Real.pi := by
    rw [show (2 * Real.pi * y / n - 2 * Real.pi * x / n) / 2 = Real.pi * (y - x) / n by ring, div_lt_iff₀ hn']
    nlinarith
  have h2 : 0 < (2 * Real.pi * z / n - 2 * Real.pi * y / n) / 2 := by
    rw [show (2 * Real.pi * z / n - 2 * Real.pi * y / n) / 2 = Real.pi * (z - y) / n by ring]
    exact div_pos (mul_pos hpi (sub_pos.mpr hyz)) hn'
  have h2' : (2 * Real.pi * z / n - 2 * Real.pi * y / n) / 2 < Real.pi := by
    rw [show (2 * Real.pi * z / n - 2 * Real.pi * y / n) / 2 = Real.pi * (z - y) / n by ring, div_lt_iff₀ hn']
    nlinarith
  have h3 : 0 < (2 * Real.pi * z / n - 2 * Real.pi * x / n) / 2 := by
    rw [show (2 * Real.pi * z / n - 2 * Real.pi * x / n) / 2 = Real.pi * (z - x) / n by ring]
    exact div_pos (mul_pos hpi (by linarith)) hn'
  have h3' : (2 * Real.pi * z / n - 2 * Real.pi * x / n) / 2 < Real.pi := by
    rw [show (2 * Real.pi * z / n - 2 * Real.pi * x / n) / 2 = Real.pi * (z - x) / n by ring, div_lt_iff₀ hn']
    nlinarith
  exact mul_pos (mul_pos (mul_pos (by norm_num) (Real.sin_pos_of_pos_of_lt_pi h1 h1'))
    (Real.sin_pos_of_pos_of_lt_pi h2 h2')) (Real.sin_pos_of_pos_of_lt_pi h3 h3')

private theorem crossIm_zero_iff_mem_segment {a b z : ℂ}
    (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) (hab : a ≠ b) (hz : z ∈ closedBall (0 : ℂ) 1) :
    crossIm a b z = 0 ↔ z ∈ segment ℝ a b := by
  constructor
  · intro h0
    let d := b - a
    have hd0 : d ≠ 0 := sub_ne_zero.mpr hab.symm
    have hnd : 0 < Complex.normSq d := Complex.normSq_pos.mpr hd0
    let t : ℝ := ((z - a) * star d).re / Complex.normSq d
    have hmul : (z - a) * star d = (t * Complex.normSq d : ℝ) := by
      apply Complex.ext
      · simp only [Complex.ofReal_re, t]; field_simp [hnd.ne']
      · simp only [Complex.ofReal_im]; exact h0
    have hzeq : z = a + t • d := by
      have h1 := congrArg (fun w : ℂ => w * d) hmul
      have hsd : star d * d = (Complex.normSq d : ℂ) := by rw [mul_comm, Complex.star_def, Complex.mul_conj]
      rw [mul_assoc, hsd] at h1
      have h2 : (z - a) * (Complex.normSq d : ℂ) = (t • d) * (Complex.normSq d : ℂ) := by
        rw [h1, Complex.real_smul, Complex.ofReal_mul]; ring
      have h3 : z - a = t • d := mul_right_cancel₀ (Complex.ofReal_ne_zero.mpr hnd.ne') h2
      calc z = a + (z - a) := by abel
        _ = a + t • d := by rw [h3]
    have hna : Complex.normSq a = 1 := by rw [Complex.normSq_eq_norm_sq, ha, one_pow]
    have hnb : Complex.normSq b = 1 := by rw [Complex.normSq_eq_norm_sq, hb, one_pow]
    have hnz : Complex.normSq z ≤ 1 := by
      rw [Complex.normSq_eq_norm_sq]; have := mem_closedBall_zero_iff.mp hz; nlinarith [norm_nonneg z]
    have h_quad : ∀ r : ℝ, Complex.normSq (a + r • d) =
        Complex.normSq a + 2 * r * (a.re * d.re + a.im * d.im) + r ^ 2 * Complex.normSq d := fun r => by
      simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im, Complex.real_smul,
        Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero, add_zero]
      ring
    have h1 := h_quad 1; rw [show a + (1 : ℝ) • d = b by simp [d], hna, hnb] at h1
    have ht := h_quad t; rw [← hzeq, hna] at ht
    have hB : 2 * (a.re * d.re + a.im * d.im) = - Complex.normSq d := by linarith
    have hprod : t * (t - 1) * Complex.normSq d ≤ 0 := by
      have : t * (t - 1) * Complex.normSq d = t ^ 2 * Complex.normSq d + t * (- Complex.normSq d) := by ring
      rw [this, ← hB]; linarith
    have hprod' : t * (t - 1) ≤ 0 := nonpos_of_mul_nonpos_left hprod hnd
    have ht0 : 0 ≤ t := by nlinarith
    have ht1 : t ≤ 1 := by nlinarith
    refine ⟨1 - t, t, by linarith, ht0, by ring, ?_⟩
    rw [hzeq]; simp only [d, sub_smul, one_smul, smul_sub]; abel
  · rintro ⟨r, s, _, _, hrs, rfl⟩
    rw [crossIm_affine a b a b r s hrs]
    have h1 : crossIm a b a = 0 := by simp [crossIm]
    have h2 : crossIm a b b = 0 := by simp only [crossIm, Complex.star_def, Complex.mul_conj, Complex.ofReal_im]
    rw [h1, h2]; ring

/-- On a model surface `Y` presented by `ew a b c`, any closed set `K` not containing the `i`-th
cuff leaves two distinct open-interval points `0 < u₁ < u₂ < 1` on `holeP a b c f i`. -/
private theorem exists_two_pts_in_hole {Y : Type} [TopologicalSpace Y] [T2Space Y]
    {a b c : ℕ} {f : ℕ × ℂ → Y} (hf : Presents (sW (ew a b c)) f)
    {K : Set Y} (hKcl : IsClosed K) {i : ℕ} (_hi : i < c)
    (hne : (holeC a b c f i \ K).Nonempty) :
    ∃ u₁ u₂ : ℝ, 0 < u₁ ∧ u₁ < u₂ ∧ u₂ < 1 ∧ holeP a b c f i u₁ ∉ K ∧ holeP a b c f i u₂ ∉ K := by
  obtain ⟨_, ⟨u₀, hu₀, rfl⟩, hu₀K⟩ := hne
  have hcont := continuousOn_hole hf i
  have hnhd : (holeP a b c f i) ⁻¹' Kᶜ ∈ 𝓝[Icc (0 : ℝ) 1] u₀ :=
    (hcont u₀ hu₀).preimage_mem_nhdsWithin (hKcl.isOpen_compl.mem_nhds hu₀K)
  obtain ⟨δ, hδ, hδsub⟩ := Metric.mem_nhdsWithin_iff.mp hnhd
  by_cases h0 : u₀ = 0
  · subst h0
    let ε := min (δ / 2) (1 / 2)
    have hε : 0 < ε := lt_min (half_pos hδ) (by norm_num)
    refine ⟨ε / 2, ε, by linarith, by linarith, by linarith [min_le_right (δ / 2) (1 / 2 : ℝ)], ?_, ?_⟩
    · exact hδsub ⟨by rw [mem_ball, Real.dist_eq, sub_zero, abs_of_pos (by linarith)]; linarith [min_le_left (δ / 2) (1 / 2 : ℝ)],
        ⟨by linarith, by linarith [min_le_right (δ / 2) (1 / 2 : ℝ)]⟩⟩
    · exact hδsub ⟨by rw [mem_ball, Real.dist_eq, sub_zero, abs_of_pos hε]; linarith [min_le_left (δ / 2) (1 / 2 : ℝ)],
        ⟨by linarith, by linarith [min_le_right (δ / 2) (1 / 2 : ℝ)]⟩⟩
  · by_cases h1 : u₀ = 1
    · subst h1
      let ε := min (δ / 2) (1 / 2)
      have hε : 0 < ε := lt_min (half_pos hδ) (by norm_num)
      refine ⟨1 - ε, 1 - ε / 2, by linarith [min_le_right (δ / 2) (1 / 2 : ℝ)], by linarith, by linarith, ?_, ?_⟩
      · exact hδsub ⟨by rw [mem_ball, Real.dist_eq, show (1 - ε) - 1 = -ε by ring, abs_neg, abs_of_pos hε]
                        linarith [min_le_left (δ / 2) (1 / 2 : ℝ)],
          ⟨by linarith [min_le_right (δ / 2) (1 / 2 : ℝ)], by linarith⟩⟩
      · exact hδsub ⟨by rw [mem_ball, Real.dist_eq, show (1 - ε / 2) - 1 = -(ε / 2) by ring, abs_neg, abs_of_pos (by linarith)]
                        linarith [min_le_left (δ / 2) (1 / 2 : ℝ)],
          ⟨by linarith [min_le_right (δ / 2) (1 / 2 : ℝ)], by linarith⟩⟩
    · have hu₀_oo : u₀ ∈ Ioo (0 : ℝ) 1 := ⟨lt_of_le_of_ne hu₀.1 (Ne.symm h0), lt_of_le_of_ne hu₀.2 h1⟩
      let ε := min (δ / 2) (min u₀ (1 - u₀) / 2)
      have hε : 0 < ε := lt_min (half_pos hδ) (half_pos (lt_min hu₀_oo.1 (sub_pos.mpr hu₀_oo.2)))
      have hεu : ε ≤ u₀ / 2 := (min_le_right _ _).trans (div_le_div_of_nonneg_right (min_le_left _ _) (by norm_num))
      have hε1 : ε ≤ (1 - u₀) / 2 := (min_le_right _ _).trans (div_le_div_of_nonneg_right (min_le_right _ _) (by norm_num))
      refine ⟨u₀, u₀ + ε, hu₀_oo.1, by linarith, by linarith, hu₀K, ?_⟩
      exact hδsub ⟨by rw [mem_ball, Real.dist_eq, show u₀ + ε - u₀ = ε by ring, abs_of_pos hε]
                      linarith [min_le_left (δ / 2) (min u₀ (1 - u₀) / 2)],
        ⟨by linarith, by linarith⟩⟩

private theorem exists_nonsep_iArc_one_cuff_params {S : Type} [TopologicalSpace S] [T2Space S]
    {a b : ℕ} (hnd : 2 ≤ 2 * a + b + 1) {f : ℕ × ℂ → S} (hf : Presents (sW (ew a b 1)) f)
    (hbd_eq : bd S = ⋃ i ∈ {i | i < 1}, holeC a b 1 f i)
    {u₁ u₂ : ℝ} (hu₁0 : 0 < u₁) (hu₁₂ : u₁ < u₂) (hu₂1 : u₂ < 1) :
    let n : ℕ := 4 * a + 2 * b + 3 * 1 + 2
    let j_hole : ℕ := 4 * a + 2 * b + 1
    let z₁ : ℂ := per n ((j_hole : ℝ) + u₁)
    let z₂ : ℂ := per n ((j_hole : ℝ) + u₂)
    ∃ (j₁ j₂ : ℕ) (e₁ e₂ : Bool) (k₀ : ℕ),
      j₁ < j₂ ∧ j₂ < j_hole ∧
      (ew a b 1)[j₁]? = some (k₀, e₁) ∧ (ew a b 1)[j₂]? = some (k₀, e₂) ∧
      (∃ (x₁ y₁ x₂ y₂ : ℝ),
        0 < x₁ ∧ x₁ < n ∧ 0 < y₁ ∧ y₁ < n ∧ 0 < x₂ ∧ x₂ < n ∧ 0 < y₂ ∧ y₂ < n ∧
        f (0, per n x₁) = f (0, per n y₁) ∧ f (0, per n x₂) = f (0, per n y₂) ∧
        (let m₁ : ℝ := (j₁ : ℝ) + 1 / 2
         let m₂ : ℝ := (j₂ : ℝ) + 1 / 2
         let L₁ := crossIm z₂ (per n m₁)
         let L₂ := crossIm (per n m₂) z₁
         ((L₁ (per n x₁) < 0 ∧ 0 < L₁ (per n y₁) ∧ 0 < L₂ (per n y₁) ∧
           0 < L₁ (per n x₂) ∧ 0 < L₂ (per n x₂) ∧ L₂ (per n y₂) < 0) ∨
          (0 < L₁ (per n x₁) ∧ 0 < L₂ (per n x₁) ∧ L₂ (per n y₁) < 0 ∧
           L₁ (per n x₂) < 0 ∧ L₂ (per n y₂) < 0))) ∧
        (∀ w : ℂ, w = per n x₁ ∨ w = per n x₂ →
          f (0, w) ≠ f (0, per n ((j₁ : ℝ) + 1 / 2)) ∧ f (0, w) ∉ bd S) ∧
        f (0, per n ((j₁ : ℝ) + 1 / 2)) ∉ bd S) := by
  intro n j_hole z₁ z₂
  have hn : 0 < n := by omega
  have hDsk : ∀ z ∈ closedBall (0 : ℂ) 1, ((0 : ℕ), z) ∈ Dsk (sW (ew a b 1)) := fun z hz =>
    ⟨(ew_mem_dsk a b 1).1, by simpa using hz⟩
  -- Helper for computing `L₁` and `L₂` signs on `per n t`:
  have hL1_pos : ∀ (j₁ : ℕ) (t : ℝ), (j₁ : ℝ) + 1 / 2 < t → t < (j_hole : ℝ) + u₂ →
      0 < crossIm z₂ (per n ((j₁ : ℝ) + 1 / 2)) (per n t) := fun j₁ t h1 h2 => by
    rw [crossIm_cyc]
    exact crossIm_per_pos hn h1 h2 (by
      have : ((j_hole + 1 : ℕ) : ℝ) ≤ n := by exact_mod_cast (by omega : j_hole + 1 ≤ n)
      push_cast at this; linarith)
  have hL1_neg_lt : ∀ (j₁ : ℕ) (t : ℝ), 0 < t → t < (j₁ : ℝ) + 1 / 2 → (j₁ : ℝ) + 1 / 2 < (j_hole : ℝ) + u₂ →
      crossIm z₂ (per n ((j₁ : ℝ) + 1 / 2)) (per n t) < 0 := fun j₁ t h0 h1 h2 => by
    rw [crossIm_swap, neg_lt_zero, crossIm_cyc, crossIm_cyc]
    exact crossIm_per_pos hn h1 h2 (by
      have : ((j_hole + 1 : ℕ) : ℝ) ≤ n := by exact_mod_cast (by omega : j_hole + 1 ≤ n)
      push_cast at this; linarith)
  have hL2_pos_lt : ∀ (j₂ : ℕ) (t : ℝ), 0 < t → t < (j₂ : ℝ) + 1 / 2 → (j₂ : ℝ) + 1 / 2 < (j_hole : ℝ) + u₁ →
      0 < crossIm (per n ((j₂ : ℝ) + 1 / 2)) z₁ (per n t) := fun j₂ t h0 h1 h2 => by
    rw [crossIm_cyc, crossIm_cyc]
    exact crossIm_per_pos hn h1 h2 (by
      have : ((j_hole + 1 : ℕ) : ℝ) ≤ n := by exact_mod_cast (by omega : j_hole + 1 ≤ n)
      push_cast at this; linarith)
  have hL2_neg : ∀ (j₂ : ℕ) (t : ℝ), (j₂ : ℝ) + 1 / 2 < t → t < (j_hole : ℝ) + u₁ →
      crossIm (per n ((j₂ : ℝ) + 1 / 2)) z₁ (per n t) < 0 := fun j₂ t h1 h2 => by
    rw [crossIm_swap, neg_lt_zero, crossIm_cyc]
    exact crossIm_per_pos hn h1 h2 (by
      have : ((j_hole + 1 : ℕ) : ℝ) ≤ n := by exact_mod_cast (by omega : j_hole + 1 ≤ n)
      push_cast at this; linarith)
  -- Helper: a point on a PAIRED side `p` at `t ∈ (0, 1)` is NOT in `bd S` and NOT equal to a distinct side/param!
  have hnot_bd_paired : ∀ (p q k : ℕ) (e e' : Bool) (t : ℝ),
      p ≠ q → t ∈ Ioo (0 : ℝ) 1 → (ew a b 1)[p]? = some (k, e) → (ew a b 1)[q]? = some (k, e') →
      f (0, per n (p + t)) ∉ bd S := by
    intro p q k e e' t hpq ht hp hq hbd
    rw [hbd_eq] at hbd
    obtain ⟨l, hl, u, hu, hfe⟩ := mem_iUnion₂.mp hbd
    have hl0 : l = 0 := Nat.lt_one_iff.mp hl
    subst hl0
    have hrel := (hf.2.2 _ (hDsk _ (mem_closedBall_zero_iff.mpr (norm_per _ _).le)) _
      (hDsk _ (mem_closedBall_zero_iff.mpr (norm_per _ _).le))).mp hfe.symm
    have h1 : ((0 : ℕ), per n (p + t)) = spt (sW (ew a b 1)) 0 p t := by rw [spt_ew]
    have h2 : ((0 : ℕ), per n ((j_hole : ℕ) + u)) = spt (sW (ew a b 1)) 0 j_hole u := by rw [spt_ew]
    rw [h1] at hrel
    have hp' : (sW (ew a b 1) 0)[p]? = some (k, e) := by rw [sW_zero]; exact hp
    have hq' : (sW (ew a b 1) 0)[q]? = some (k, e') := by rw [sW_zero]; exact hq
    have hfree := freeSide_hole (a := a) (b := b) (c := 1) (i := 0) (by omega)
    have hlt_n : p < n := by
      have := (List.getElem?_eq_some_iff.mp hp).1; rwa [ew_length] at this
    rcases PRel.eq_or_stp (isPaired_ew a b 1) hp' ht hrel with heq | hstp
    · have hp_ne_jh : p ≠ j_hole := fun h => by
        subst h
        have hq_eq : 4 * a + 2 * b + 3 * 0 + 1 = q := (Prod.mk.inj (hfree 0 q _ _ _ hp' hq')).2
        exact hpq (by omega)
      have hper := (Prod.mk.inj heq).2
      rw [sW_zero, ew_length] at hper
      have hp_nonneg : 0 ≤ (p : ℝ) + t := by have := ht.1; linarith [Nat.cast_nonneg (α := ℝ) p]
      have hjh_nonneg : 0 ≤ (j_hole : ℝ) + u := by have := hu.1; linarith [Nat.cast_nonneg (α := ℝ) j_hole]
      have hu_lt : u ≤ 1 := hu.2
      rcases eq_or_lt_of_le hu_lt with rfl | hu1'
      · -- `per n (j_hole + 1) = per n (p + t)` contradicts `t ∈ (0, 1)`!
        have := per_injOn hn ⟨by positivity, by have : ((j_hole + 1 : ℕ) : ℝ) < n := (by exact_mod_cast (by omega : j_hole + 1 < n)); push_cast at this; linarith⟩
          ⟨hp_nonneg, by have : ((p + 1 : ℕ) : ℝ) ≤ n := (by exact_mod_cast (by omega : p + 1 ≤ n)); push_cast at this; linarith [ht.2]⟩ hper
        have : (p : ℝ) + t = ((j_hole + 1 : ℕ) : ℝ) := by push_cast; linarith
        have : (p : ℝ) < ((j_hole + 1 : ℕ) : ℝ) ∧ ((j_hole + 1 : ℕ) : ℝ) < (p : ℝ) + 1 := ⟨by linarith [ht.1], by linarith [ht.2]⟩
        have hlt1 : p < j_hole + 1 := by exact_mod_cast this.1
        have hlt2 : j_hole + 1 < p + 1 := by exact_mod_cast this.2
        omega
      · have := per_injOn hn ⟨hjh_nonneg, by have : ((j_hole + 1 : ℕ) : ℝ) ≤ n := (by exact_mod_cast (by omega : j_hole + 1 ≤ n)); push_cast at this; linarith⟩
          ⟨hp_nonneg, by have : ((p + 1 : ℕ) : ℝ) ≤ n := (by exact_mod_cast (by omega : p + 1 ≤ n)); push_cast at this; linarith [ht.2]⟩ hper
        have : (j_hole : ℝ) + u = (p : ℝ) + t := this
        have h1' : (j_hole : ℝ) < (p : ℝ) + 1 := by linarith [hu.1, ht.2]
        have h2' : (p : ℝ) < (j_hole : ℝ) + 1 := by linarith [ht.1, hu1']
        have h1'' : j_hole < p + 1 := by exact_mod_cast h1'
        have h2'' : p < j_hole + 1 := by exact_mod_cast h2'
        exact hp_ne_jh (by omega)
    · obtain ⟨j', q', e'', hq'', hne', heq⟩ := stp_of_side (isPaired_ew a b 1) hp' ht hstp
      have hj'0 : j' = 0 := by
        by_contra h0; simp [sW, h0, nW] at hq''
      subst hj'0
      have hq'_ne_jh : q' ≠ j_hole := fun h => by
        subst h; exact absurd (hfree 0 p _ _ _ hq'' hp') (by simpa [ne_comm] using hne')
      have hq'_lt : q' < n := by
        have := (List.getElem?_eq_some_iff.mp (by rwa [sW_zero] at hq'')).1; rwa [ew_length] at this
      rw [spt_ew] at heq
      have hper := (Prod.mk.inj heq).2
      have hflp_oo : flp e e'' t ∈ Ioo (0 : ℝ) 1 := by
        cases e <;> cases e'' <;> simp [flp] <;> exact ⟨by linarith [ht.1, ht.2], by linarith [ht.1, ht.2]⟩
      have hq'_nonneg : 0 ≤ (q' : ℝ) + flp e e'' t := by
        have := hflp_oo.1; linarith [Nat.cast_nonneg (α := ℝ) q']
      have hjh_nonneg : 0 ≤ (j_hole : ℝ) + u := by have := hu.1; linarith [Nat.cast_nonneg (α := ℝ) j_hole]
      rcases eq_or_lt_of_le hu.2 with rfl | hu1'
      · have := per_injOn hn ⟨by positivity, by have : ((j_hole + 1 : ℕ) : ℝ) < n := (by exact_mod_cast (by omega : j_hole + 1 < n)); push_cast at this; linarith⟩
          ⟨hq'_nonneg, by have : ((q' + 1 : ℕ) : ℝ) ≤ n := (by exact_mod_cast (by omega : q' + 1 ≤ n)); push_cast at this; linarith [hflp_oo.2]⟩ hper
        have h1' : (q' : ℝ) < ((j_hole + 1 : ℕ) : ℝ) := by push_cast; linarith [hflp_oo.1]
        have h2' : ((j_hole + 1 : ℕ) : ℝ) < (q' : ℝ) + 1 := by push_cast; linarith [hflp_oo.2]
        have h1'' : q' < j_hole + 1 := by exact_mod_cast h1'
        have h2'' : j_hole + 1 < q' + 1 := by exact_mod_cast h2'
        omega
      · have := per_injOn hn ⟨hjh_nonneg, by have : ((j_hole + 1 : ℕ) : ℝ) ≤ n := (by exact_mod_cast (by omega : j_hole + 1 ≤ n)); push_cast at this; linarith⟩
          ⟨hq'_nonneg, by have : ((q' + 1 : ℕ) : ℝ) ≤ n := (by exact_mod_cast (by omega : q' + 1 ≤ n)); push_cast at this; linarith [hflp_oo.2]⟩ hper
        have h1' : (j_hole : ℝ) < (q' : ℝ) + 1 := by linarith [hu.1, hflp_oo.2]
        have h2' : (q' : ℝ) < (j_hole : ℝ) + 1 := by linarith [hflp_oo.1, hu1']
        have h1'' : j_hole < q' + 1 := by exact_mod_cast h1'
        have h2'' : q' < j_hole + 1 := by exact_mod_cast h2'
        exact hq'_ne_jh (by omega)
  -- Helper: two points on `ew a b 1` at `(p, t)` (`t ∈ (0, 1)`) and `(j₁, 1/2)` are unequal if `p ≠ j₁, j₂` or `t ≠ 1/2`:
  have hne_mid : ∀ (j₁ j₂ k₀ p : ℕ) (e₁ e₂ : Bool) (t : ℝ),
      j₁ < j₂ → j₂ < j_hole → p < n → t ∈ Ioo (0 : ℝ) 1 →
      (ew a b 1)[j₁]? = some (k₀, e₁) → (ew a b 1)[j₂]? = some (k₀, e₂) →
      (p ≠ j₁ ∧ p ≠ j₂ ∨ t ≠ 1 / 2) →
      f (0, per n (p + t)) ≠ f (0, per n ((j₁ : ℝ) + 1 / 2)) := by
    intro j₁ j₂ k₀ p e₁ e₂ t hj12 hj2h hpn ht hj1 hj2 hcond heq
    have hrel := (hf.2.2 _ (hDsk _ (mem_closedBall_zero_iff.mpr (norm_per _ _).le)) _
      (hDsk _ (mem_closedBall_zero_iff.mpr (norm_per _ _).le))).mp heq.symm
    have h1 : ((0 : ℕ), per n ((j₁ : ℝ) + 1 / 2)) = spt (sW (ew a b 1)) 0 j₁ (1 / 2) := by rw [spt_ew]
    rw [h1] at hrel
    have hj1' : (sW (ew a b 1) 0)[j₁]? = some (k₀, e₁) := by rw [sW_zero]; exact hj1
    have hj2' : (sW (ew a b 1) 0)[j₂]? = some (k₀, e₂) := by rw [sW_zero]; exact hj2
    have hp_nonneg : 0 ≤ (p : ℝ) + t := by have := ht.1; linarith [Nat.cast_nonneg (α := ℝ) p]
    rcases PRel.eq_or_stp (isPaired_ew a b 1) hj1' (by norm_num : (1 / 2 : ℝ) ∈ Ioo 0 1) hrel with he | hstp
    · have hper := (Prod.mk.inj he).2
      rw [sW_zero, ew_length] at hper
      have := per_injOn hn ⟨hp_nonneg, by have : ((p + 1 : ℕ) : ℝ) ≤ n := (by exact_mod_cast (by omega : p + 1 ≤ n)); push_cast at this; linarith [ht.2]⟩
        ⟨by positivity, by have : ((j₁ + 1 : ℕ) : ℝ) ≤ n := (by exact_mod_cast (by omega : j₁ + 1 ≤ n)); push_cast at this; linarith⟩ hper
      have hp_eq : p = j₁ := by
        have h1' : (p : ℝ) < (j₁ : ℝ) + 1 := by linarith [ht.1]
        have h2' : (j₁ : ℝ) < (p : ℝ) + 1 := by linarith [ht.2]
        have h1'' : p < j₁ + 1 := by exact_mod_cast h1'
        have h2'' : j₁ < p + 1 := by exact_mod_cast h2'
        omega
      subst hp_eq
      rcases hcond with ⟨h, -⟩ | h
      · exact h rfl
      · exact h (by linarith)
    · obtain ⟨j', q', e'', hq'', hne', he⟩ := stp_of_side (isPaired_ew a b 1) hj1' (by norm_num : (1 / 2 : ℝ) ∈ Ioo 0 1) hstp
      have hj'0 : j' = 0 := by by_contra h0; simp [sW, h0, nW] at hq''
      subst hj'0
      have hq'_lt : q' < n := by
        have := (List.getElem?_eq_some_iff.mp (by rwa [sW_zero] at hq'')).1; rwa [ew_length] at this
      have hq'_eq : q' = j₂ := by
        rw [sW_zero, ew_get a b 1 hq'_lt] at hq''
        rw [ew_get a b 1 (by omega)] at hj1 hj2
        have hk1 : lab a b 1 j₁ = k₀ := (Prod.mk.inj (Option.some.inj hj1)).1
        have hk2 : lab a b 1 j₂ = k₀ := (Prod.mk.inj (Option.some.inj hj2)).1
        have hkq : lab a b 1 q' = k₀ := (Prod.mk.inj (Option.some.inj hq'')).1
        rcases lab_three (a := a) (b := b) (c := 1) (by omega) (by omega) hq'_lt (hk1.trans hk2.symm) (hk2.trans hkq.symm) with h | h | h
        · exact absurd h (by omega)
        · exact h.symm
        · exact absurd (by simp [h] : (0, j₁) = (0, q')) hne'
      rw [hq'_eq, spt_ew] at he
      have hflp : flp e₁ e'' (1 / 2 : ℝ) = 1 / 2 := by cases e₁ <;> cases e'' <;> simp [flp] <;> norm_num
      rw [hflp] at he
      have hper := (Prod.mk.inj he).2
      have := per_injOn hn ⟨hp_nonneg, by have : ((p + 1 : ℕ) : ℝ) ≤ n := (by exact_mod_cast (by omega : p + 1 ≤ n)); push_cast at this; linarith [ht.2]⟩
        ⟨by positivity, by have : ((j₂ + 1 : ℕ) : ℝ) ≤ n := (by exact_mod_cast (by omega : j₂ + 1 ≤ n)); push_cast at this; linarith⟩ hper
      have hp_eq : p = j₂ := by
        have h1' : (p : ℝ) < (j₂ : ℝ) + 1 := by linarith [ht.1]
        have h2' : (j₂ : ℝ) < (p : ℝ) + 1 := by linarith [ht.2]
        have h1'' : p < j₂ + 1 := by exact_mod_cast h1'
        have h2'' : j₂ < p + 1 := by exact_mod_cast h2'
        omega
      subst hp_eq
      rcases hcond with ⟨-, h⟩ | h
      · exact h rfl
      · exact h (by linarith)
  by_cases hb1 : 1 ≤ b
  · -- Subcase 2a: `b ≥ 1`, crosscap at `j₁ = 4a`, `j₂ = 4a + 1`
    have hj1 : (ew a b 1)[4 * a]? = some (2 * a, true) := by
      rw [ew_get a b 1 (by omega)]; simp [lab, sgn, show 4 * a < 4 * a + 2 * b by omega]
    have hj2 : (ew a b 1)[4 * a + 1]? = some (2 * a, true) := by
      rw [ew_get a b 1 (by omega)]; simp [lab, sgn, show ¬ (4 * a + 1 < 4 * a) by omega,
        show 4 * a + 1 < 4 * a + 2 * b by omega]
    refine ⟨4 * a, 4 * a + 1, true, true, 2 * a, by omega, by omega, hj1, hj2,
      ((4 * a : ℕ) : ℝ) + 1 / 4, ((4 * a + 1 : ℕ) : ℝ) + 1 / 4, ((4 * a : ℕ) : ℝ) + 3 / 4, ((4 * a + 1 : ℕ) : ℝ) + 3 / 4,
      by positivity, by have : ((4 * a + 1 : ℕ) : ℝ) ≤ n := (by exact_mod_cast (by omega : 4 * a + 1 ≤ n)); push_cast at this ⊢; linarith,
      by positivity, by have : ((4 * a + 2 : ℕ) : ℝ) ≤ n := (by exact_mod_cast (by omega : 4 * a + 2 ≤ n)); push_cast at this ⊢; linarith,
      by positivity, by have : ((4 * a + 1 : ℕ) : ℝ) ≤ n := (by exact_mod_cast (by omega : 4 * a + 1 ≤ n)); push_cast at this ⊢; linarith,
      by positivity, by have : ((4 * a + 2 : ℕ) : ℝ) ≤ n := (by exact_mod_cast (by omega : 4 * a + 2 ≤ n)); push_cast at this ⊢; linarith,
      ?_, ?_, Or.inl ⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩
    · have hstp : Stp (sW (ew a b 1)) (0, per n (((4 * a : ℕ) : ℝ) + 1 / 4)) (0, per n (((4 * a + 1 : ℕ) : ℝ) + 1 / 4)) := by
        refine ⟨0, 0, 4 * a, 4 * a + 1, 2 * a, true, true, 1 / 4, by rw [sW_zero]; exact hj1,
          by rw [sW_zero]; exact hj2, by simp, by norm_num, ?_, ?_⟩
        · simp [sdPt, sW_zero, ew_length, n]
        · simp [sdPt, sW_zero, ew_length, n]
      exact (hf.2.2 _ hstp.mem_Dsk.1 _ hstp.mem_Dsk.2).mpr (.rel _ _ hstp)
    · have hstp : Stp (sW (ew a b 1)) (0, per n (((4 * a : ℕ) : ℝ) + 3 / 4)) (0, per n (((4 * a + 1 : ℕ) : ℝ) + 3 / 4)) := by
        refine ⟨0, 0, 4 * a, 4 * a + 1, 2 * a, true, true, 3 / 4, by rw [sW_zero]; exact hj1,
          by rw [sW_zero]; exact hj2, by simp, by norm_num, ?_, ?_⟩
        · simp [sdPt, sW_zero, ew_length, n]
        · simp [sdPt, sW_zero, ew_length, n]
      exact (hf.2.2 _ hstp.mem_Dsk.1 _ hstp.mem_Dsk.2).mpr (.rel _ _ hstp)
    · exact hL1_neg_lt (4 * a) _ (by positivity) (by push_cast; linarith) (by have : ((4 * a + 2 : ℕ) : ℝ) ≤ j_hole := (by exact_mod_cast (by omega : 4 * a + 2 ≤ j_hole)); push_cast at this ⊢; linarith)
    · exact hL1_pos (4 * a) _ (by push_cast; linarith) (by have : ((4 * a + 2 : ℕ) : ℝ) ≤ j_hole := (by exact_mod_cast (by omega : 4 * a + 2 ≤ j_hole)); push_cast at this ⊢; linarith)
    · exact hL2_pos_lt (4 * a + 1) _ (by positivity) (by push_cast; linarith) (by have : ((4 * a + 2 : ℕ) : ℝ) ≤ j_hole := (by exact_mod_cast (by omega : 4 * a + 2 ≤ j_hole)); push_cast at this ⊢; linarith)
    · exact hL1_pos (4 * a) _ (by push_cast; linarith) (by have : ((4 * a + 2 : ℕ) : ℝ) ≤ j_hole := (by exact_mod_cast (by omega : 4 * a + 2 ≤ j_hole)); push_cast at this ⊢; linarith)
    · exact hL2_pos_lt (4 * a + 1) _ (by positivity) (by push_cast; linarith) (by have : ((4 * a + 2 : ℕ) : ℝ) ≤ j_hole := (by exact_mod_cast (by omega : 4 * a + 2 ≤ j_hole)); push_cast at this ⊢; linarith)
    · exact hL2_neg (4 * a + 1) _ (by push_cast; linarith) (by have : ((4 * a + 2 : ℕ) : ℝ) ≤ j_hole := (by exact_mod_cast (by omega : 4 * a + 2 ≤ j_hole)); push_cast at this ⊢; linarith)
    · rintro w (rfl | rfl)
      · exact ⟨hne_mid (4 * a) (4 * a + 1) (2 * a) (4 * a) true true (1 / 4) (by omega) (by omega) (by omega) (by norm_num) hj1 hj2 (Or.inr (by norm_num)),
          hnot_bd_paired (4 * a) (4 * a + 1) (2 * a) true true (1 / 4) (by omega) (by norm_num) hj1 hj2⟩
      · exact ⟨hne_mid (4 * a) (4 * a + 1) (2 * a) (4 * a) true true (3 / 4) (by omega) (by omega) (by omega) (by norm_num) hj1 hj2 (Or.inr (by norm_num)),
          hnot_bd_paired (4 * a) (4 * a + 1) (2 * a) true true (3 / 4) (by omega) (by norm_num) hj1 hj2⟩
    · exact hnot_bd_paired (4 * a) (4 * a + 1) (2 * a) true true (1 / 2) (by omega) (by norm_num) hj1 hj2
  · -- Subcase 2b: `b = 0`, `a ≥ 1`, handle at `j₁ = 0`, `j₂ = 2` (and bridge sides `1`, `3`)
    have ha1 : 1 ≤ a := by omega
    have hj0 : (ew a b 1)[0]? = some (0, true) := by
      rw [ew_get a b 1 (by omega)]; simp [lab, sgn, show 0 < 4 * a by omega]
    have hj1' : (ew a b 1)[1]? = some (1, true) := by
      rw [ew_get a b 1 (by omega)]; simp [lab, sgn, show 1 < 4 * a by omega]
    have hj2 : (ew a b 1)[2]? = some (0, false) := by
      rw [ew_get a b 1 (by omega)]; simp [lab, sgn, show 2 < 4 * a by omega]
    have hj3 : (ew a b 1)[3]? = some (1, false) := by
      rw [ew_get a b 1 (by omega)]; simp [lab, sgn, show 3 < 4 * a by omega]
    refine ⟨0, 2, true, false, 0, by omega, by omega, hj0, hj2,
      ((1 : ℕ) : ℝ) + 1 / 2, ((3 : ℕ) : ℝ) + 1 / 2, ((0 : ℕ) : ℝ) + 1 / 4, ((2 : ℕ) : ℝ) + 3 / 4,
      by norm_num, by have : ((4 : ℕ) : ℝ) ≤ n := (by exact_mod_cast (by omega : 4 ≤ n)); push_cast at this ⊢; linarith,
      by norm_num, by have : ((4 : ℕ) : ℝ) ≤ n := (by exact_mod_cast (by omega : 4 ≤ n)); push_cast at this ⊢; linarith,
      by norm_num, by have : ((4 : ℕ) : ℝ) ≤ n := (by exact_mod_cast (by omega : 4 ≤ n)); push_cast at this ⊢; linarith,
      by norm_num, by have : ((4 : ℕ) : ℝ) ≤ n := (by exact_mod_cast (by omega : 4 ≤ n)); push_cast at this ⊢; linarith,
      ?_, ?_, Or.inr ⟨?_, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩
    · have hstp : Stp (sW (ew a b 1)) (0, per n (((1 : ℕ) : ℝ) + 1 / 2)) (0, per n (((3 : ℕ) : ℝ) + 1 / 2)) := by
        refine ⟨0, 0, 1, 3, 1, true, false, 1 / 2, by rw [sW_zero]; exact hj1',
          by rw [sW_zero]; exact hj3, by simp, by norm_num, ?_, ?_⟩
        · simp [sdPt, sW_zero, ew_length, n]
        · simp [sdPt, sW_zero, ew_length, n]; norm_num
      exact (hf.2.2 _ hstp.mem_Dsk.1 _ hstp.mem_Dsk.2).mpr (.rel _ _ hstp)
    · have hstp : Stp (sW (ew a b 1)) (0, per n (((0 : ℕ) : ℝ) + 1 / 4)) (0, per n (((2 : ℕ) : ℝ) + 3 / 4)) := by
        refine ⟨0, 0, 0, 2, 0, true, false, 1 / 4, by rw [sW_zero]; exact hj0,
          by rw [sW_zero]; exact hj2, by simp, by norm_num, ?_, ?_⟩
        · simp [sdPt, sW_zero, ew_length, n]
        · simp [sdPt, sW_zero, ew_length, n]; norm_num
      exact (hf.2.2 _ hstp.mem_Dsk.1 _ hstp.mem_Dsk.2).mpr (.rel _ _ hstp)
    · exact hL1_pos 0 _ (by norm_num) (by have : ((5 : ℕ) : ℝ) ≤ j_hole := (by exact_mod_cast (by omega : 5 ≤ j_hole)); push_cast at this ⊢; linarith)
    · exact hL2_pos_lt 2 _ (by norm_num) (by norm_num) (by have : ((5 : ℕ) : ℝ) ≤ j_hole := (by exact_mod_cast (by omega : 5 ≤ j_hole)); push_cast at this ⊢; linarith)
    · exact hL2_neg 2 _ (by norm_num) (by have : ((5 : ℕ) : ℝ) ≤ j_hole := (by exact_mod_cast (by omega : 5 ≤ j_hole)); push_cast at this ⊢; linarith)
    · exact hL1_neg_lt 0 _ (by norm_num) (by norm_num) (by have : ((5 : ℕ) : ℝ) ≤ j_hole := (by exact_mod_cast (by omega : 5 ≤ j_hole)); push_cast at this ⊢; linarith)
    · exact hL2_neg 2 _ (by norm_num) (by have : ((5 : ℕ) : ℝ) ≤ j_hole := (by exact_mod_cast (by omega : 5 ≤ j_hole)); push_cast at this ⊢; linarith)
    · rintro w (rfl | rfl)
      · exact ⟨hne_mid 0 2 0 1 true false (1 / 2) (by omega) (by omega) (by omega) (by norm_num) hj0 hj2 (Or.inl ⟨by omega, by omega⟩),
          hnot_bd_paired 1 3 1 true false (1 / 2) (by omega) (by norm_num) hj1' hj3⟩
      · exact ⟨hne_mid 0 2 0 0 true false (1 / 4) (by omega) (by omega) (by omega) (by norm_num) hj0 hj2 (Or.inr (by norm_num)),
          hnot_bd_paired 0 2 0 true false (1 / 4) (by omega) (by norm_num) hj0 hj2⟩
    · exact hnot_bd_paired 0 2 0 true false (1 / 2) (by omega) (by norm_num) hj0 hj2

/-- On a connected surface `S ≃ₜ SurfaceModel a b c` with `1 ≤ c` and `2 ≤ 2 * a + b + c`,
for any closed set `K ⊆ bd S` containing no cuff, there exists a non-separating proper `I`-arc
`F ⊆ S` with endpoints outside `K`. -/
theorem exists_nonsep_iArc_avoiding {S : Type} [TopologicalSpace S] [ConnectedSpace S]
    (hS : IsSurface S) {a b c : ℕ} (eS : S ≃ₜ SurfaceModel a b c)
    (hc : 1 ≤ c) (hnd : 2 ≤ 2 * a + b + c)
    {K : Set S} (hKcl : IsClosed K) (hKcuff : ∀ C ∈ cuffs S, (C \ K).Nonempty) :
    ∃ (F : Set S) (s t : S), s ≠ t ∧ IsLineWithEnds F s t ∧ F ∩ bd S = {s, t} ∧
      s ∉ K ∧ t ∉ K ∧ IsPreconnected (Fᶜ : Set S) := by
  classical
  have ht2S : T2Space S := hS.2.1
  obtain ⟨htM, fM, hfM⟩ := presents_ew a b c
  have : T2Space (SurfaceModel a b c) := htM
  let f : ℕ × ℂ → S := eS.symm ∘ fM
  have hf : Presents (sW (ew a b c)) f := presents_comp hfM eS.symm
  let n : ℕ := 4 * a + 2 * b + 3 * c + 2
  have hn : 0 < n := by omega
  have hDsk : ∀ z ∈ closedBall (0 : ℂ) 1, ((0 : ℕ), z) ∈ Dsk (sW (ew a b c)) := fun z hz =>
    ⟨(ew_mem_dsk a b c).1, by simpa using hz⟩
  have hfc : ContinuousOn (fun z : ℂ => f (0, z)) (closedBall (0 : ℂ) 1) :=
    hf.1.comp (continuous_const.prodMk continuous_id).continuousOn hDsk
  have hbd_eq : bd S = ⋃ i ∈ {i | i < c}, holeC a b c f i := by
    have hcuffs := cuffs_eq_holeC hf
    ext x; constructor
    · intro hx
      have hC : connectedComponentIn (bd S) x ∈ cuffs S := ⟨x, hx, rfl⟩
      rw [hcuffs] at hC
      obtain ⟨i, hi, he⟩ := hC
      exact mem_biUnion hi (he ▸ mem_connectedComponentIn hx)
    · intro hx
      obtain ⟨i, hi, hxi⟩ := mem_iUnion₂.mp hx
      have hC : holeC a b c f i ∈ cuffs S := hcuffs ▸ ⟨i, hi, rfl⟩
      obtain ⟨y, -, hye⟩ := hC
      exact connectedComponentIn_subset _ _ (hye ▸ hxi)
  have hbd_not_lt : ∀ z : ℂ, ‖z‖ < 1 → f (0, z) ∉ bd S := by
    intro z hz hbd
    rw [hbd_eq] at hbd
    obtain ⟨i, hi, u, hu, hfe⟩ := mem_iUnion₂.mp hbd
    have hrel := (hf.2.2 _ (hDsk z (mem_closedBall_zero_iff.mpr hz.le)) _
      (hDsk _ (mem_closedBall_zero_iff.mpr (norm_per _ _).le))).mp hfe.symm
    have heq := PRel.eq_of_lt hrel hz
    have hnorm := congrArg (fun p : ℕ × ℂ => ‖p.2‖) heq
    simp only [norm_per] at hnorm; linarith
  -- Case 1: `c ≥ 2` (single straight chord joining hole 0 and hole 1)
  by_cases hc2 : 2 ≤ c
  · have hC0 : holeC a b c f 0 ∈ cuffs S := by rw [cuffs_eq_holeC hf]; exact ⟨0, show 0 < c by omega, rfl⟩
    have hC1 : holeC a b c f 1 ∈ cuffs S := by rw [cuffs_eq_holeC hf]; exact ⟨1, show 1 < c by omega, rfl⟩
    obtain ⟨u₁, u₁', hu₁0, hu₁lt, hu₁'1, hu₁K, -⟩ := exists_two_pts_in_hole hf hKcl (by omega : 0 < c) (hKcuff _ hC0)
    have hu₁1 : u₁ < 1 := hu₁lt.trans hu₁'1
    obtain ⟨u₂, u₂', hu₂0, hu₂lt, hu₂'1, hu₂K, -⟩ := exists_two_pts_in_hole hf hKcl (by omega : 1 < c) (hKcuff _ hC1)
    have hu₂1 : u₂ < 1 := hu₂lt.trans hu₂'1
    let z₁ : ℂ := per n ((4 * a + 2 * b + 1 : ℕ) + u₁)
    let z₂ : ℂ := per n ((4 * a + 2 * b + 4 : ℕ) + u₂)
    have hz₁_norm : ‖z₁‖ = 1 := norm_per _ _
    have hz₂_norm : ‖z₂‖ = 1 := norm_per _ _
    have hz12 : z₁ ≠ z₂ := fun h => by
      have hu1_lt : ((4 * a + 2 * b + 1 : ℕ) : ℝ) + u₁ < (n : ℝ) := by
        have hle : ((4 * a + 2 * b + 2 : ℕ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast (by omega : 4 * a + 2 * b + 2 ≤ n)
        push_cast at hle ⊢; linarith
      have hu2_lt : ((4 * a + 2 * b + 4 : ℕ) : ℝ) + u₂ < (n : ℝ) := by
        have hle : ((4 * a + 2 * b + 5 : ℕ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast (by omega : 4 * a + 2 * b + 5 ≤ n)
        push_cast at hle ⊢; linarith
      have := per_injOn hn ⟨by positivity, hu1_lt⟩ ⟨by positivity, hu2_lt⟩ h
      push_cast at this; linarith
    let s : S := f (0, z₁)
    let t : S := f (0, z₂)
    have hs_eq : s = holeP a b c f 0 u₁ := rfl
    have ht_eq : t = holeP a b c f 1 u₂ := by
      simp only [t, z₂, holeP, pmap, n, mul_one]
    have hs_mem : s ∈ holeC a b c f 0 := ⟨u₁, ⟨hu₁0.le, hu₁1.le⟩, hs_eq.symm⟩
    have ht_mem : t ∈ holeC a b c f 1 := ⟨u₂, ⟨hu₂0.le, hu₂1.le⟩, ht_eq.symm⟩
    have hst : s ≠ t := fun h => Set.disjoint_left.mp (disjoint_holeC hf (by omega) (by omega) (by omega : (0 : ℕ) ≠ 1)) hs_mem (h ▸ ht_mem)
    let seg : Set ℂ := segment ℝ z₁ z₂
    let F : Set S := (fun z => f (0, z)) '' seg
    have hseg_sub : seg ⊆ closedBall (0 : ℂ) 1 :=
      (convex_closedBall 0 1).segment_subset (mem_closedBall_zero_iff.mpr hz₁_norm.le) (mem_closedBall_zero_iff.mpr hz₂_norm.le)
    have hinj : InjOn (fun z => f (0, z)) seg := by
      intro w₁ hw₁ w₂ hw₂ he
      by_cases h1 : w₁ = z₁
      · subst h1
        by_cases h2 : w₂ = z₁
        · exact h2.symm
        · by_cases h2' : w₂ = z₂
          · subst h2'; exact (hst he).elim
          · exfalso
            have hw2_lt : ‖w₂‖ < 1 := norm_lt_one_of_openSegment hz₁_norm hz₂_norm hz12
              (mem_openSegment_of_mem_segment_ne hw₂ h2 h2')
            have hrel := (hf.2.2 _ (hDsk w₂ (hseg_sub hw₂)) _ (hDsk z₁ (hseg_sub hw₁))).mp he.symm
            have hnorm := congrArg (fun p : ℕ × ℂ => ‖p.2‖) (PRel.eq_of_lt hrel hw2_lt)
            simp only [hz₁_norm] at hnorm; linarith
      · by_cases h1' : w₁ = z₂
        · subst h1'
          by_cases h2 : w₂ = z₁
          · subst h2; exact (hst he.symm).elim
          · by_cases h2' : w₂ = z₂
            · exact h2'.symm
            · exfalso
              have hw2_lt : ‖w₂‖ < 1 := norm_lt_one_of_openSegment hz₁_norm hz₂_norm hz12
                (mem_openSegment_of_mem_segment_ne hw₂ h2 h2')
              have hrel := (hf.2.2 _ (hDsk w₂ (hseg_sub hw₂)) _ (hDsk z₂ (hseg_sub hw₁))).mp he.symm
              have hnorm := congrArg (fun p : ℕ × ℂ => ‖p.2‖) (PRel.eq_of_lt hrel hw2_lt)
              simp only [hz₂_norm] at hnorm; linarith
        · have hw1_lt : ‖w₁‖ < 1 := norm_lt_one_of_openSegment hz₁_norm hz₂_norm hz12
            (mem_openSegment_of_mem_segment_ne hw₁ h1 h1')
          have hrel := (hf.2.2 _ (hDsk w₁ (hseg_sub hw₁)) _ (hDsk w₂ (hseg_sub hw₂))).mp he
          exact (congrArg Prod.snd (PRel.eq_of_lt hrel hw1_lt)).symm
    have hFl : IsLineWithEnds F s t :=
      (isLineWithEnds_segment hz12).image_injOn (hfc.mono hseg_sub) hinj
    have hFb : F ∩ bd S = {s, t} := by
      ext x; constructor
      · rintro ⟨⟨w, hw, rfl⟩, hxbd⟩
        by_cases h1 : w = z₁
        · exact Or.inl (by rw [h1])
        · by_cases h2 : w = z₂
          · exact Or.inr (mem_singleton_iff.mpr (by rw [h2]))
          · exfalso
            have hw_lt : ‖w‖ < 1 := norm_lt_one_of_openSegment hz₁_norm hz₂_norm hz12
              (mem_openSegment_of_mem_segment_ne hw h1 h2)
            exact hbd_not_lt w hw_lt hxbd
      · rintro (rfl | rfl)
        · exact ⟨⟨z₁, left_mem_segment ℝ z₁ z₂, rfl⟩, hbd_eq ▸ mem_biUnion (show 0 < c by omega) hs_mem⟩
        · exact ⟨⟨z₂, right_mem_segment ℝ z₁ z₂, rfl⟩, hbd_eq ▸ mem_biUnion (show 1 < c by omega) ht_mem⟩
    have hcc_ne : connectedComponentIn (bd S) s ≠ connectedComponentIn (bd S) t := by
      have h0 : connectedComponentIn (bd S) s = holeC a b c f 0 := by
        obtain ⟨y, -, hye⟩ := hC0
        rw [← hye] at hs_mem ⊢; exact (connectedComponentIn_eq hs_mem).symm
      have h1 : connectedComponentIn (bd S) t = holeC a b c f 1 := by
        obtain ⟨y, -, hye⟩ := hC1
        rw [← hye] at ht_mem ⊢; exact (connectedComponentIn_eq ht_mem).symm
      rw [h0, h1]
      intro h
      exact Set.disjoint_left.mp (disjoint_holeC hf (by omega) (by omega) (by omega : (0 : ℕ) ≠ 1)) hs_mem (h ▸ hs_mem)
    obtain ⟨S', tS', ψ', hS', hψ', hdiff, -, -⟩ := cutIArc.{0} S F s t hS ‹ConnectedSpace S› hst hFb hFl
    have hconn' : ConnectedSpace S' := (hdiff hcc_ne).1
    have : T2Space S' := hS'.2.1
    have hnonsep : IsPreconnected (Fᶜ : Set S) :=
      (connectedSpace_cut_iff hS' hS hψ' hFl.isCompact.isClosed).mp hconn'
    exact ⟨F, s, t, hst, hFl, hFb, hs_eq ▸ hu₁K, ht_eq ▸ hu₂K, hnonsep⟩
  -- Case 2: `c = 1` and `2 * a + b ≥ 1` (two-segment chord across a crosscap or a handle)
  · have hc1 : c = 1 := by omega
    subst hc1
    have hC0 : holeC a b 1 f 0 ∈ cuffs S := by rw [cuffs_eq_holeC hf]; exact ⟨0, show 0 < 1 by omega, rfl⟩
    obtain ⟨u₁, u₂, hu₁0, hu₁₂, hu₂1, hu₁K, hu₂K⟩ := exists_two_pts_in_hole hf hKcl (by omega : 0 < 1) (hKcuff _ hC0)
    -- Choose paired sides `(j₁, j₂)` with `j₁ < j₂ < j_hole` and bridge pairs `(p₁, q₁)`, `(p₂, q₂)`:
    let j_hole : ℕ := 4 * a + 2 * b + 1
    let z₁ : ℂ := per n ((j_hole : ℝ) + u₁)
    let z₂ : ℂ := per n ((j_hole : ℝ) + u₂)
    have hparam := exists_nonsep_iArc_one_cuff_params hnd hf hbd_eq hu₁0 hu₁₂ hu₂1
    obtain ⟨j₁, j₂, e₁, e₂, k₀, hj12, hj2h, hj1_eq, hj2_eq, x₁, y₁, x₂, y₂,
      hx₁0, hx₁n, hy₁0, hy₁n, hx₂0, hx₂n, hy₂0, hy₂n, hbr1, hbr2, hbr_signs, hbr_off, hm1_not_bd⟩ := hparam
    let m₁ : ℂ := per n ((j₁ : ℝ) + 1 / 2)
    let m₂ : ℂ := per n ((j₂ : ℝ) + 1 / 2)
    have hfm12 : f (0, m₁) = f (0, m₂) := by
      have hstp : Stp (sW (ew a b 1)) (0, m₁) (0, m₂) := by
        refine ⟨0, 0, j₁, j₂, k₀, e₁, e₂, 1 / 2, by rw [sW_zero]; exact hj1_eq,
          by rw [sW_zero]; exact hj2_eq, by simp [show j₁ ≠ j₂ by omega], by norm_num, ?_, ?_⟩
        · cases e₁
          · simp [m₁, sdPt, sW_zero, ew_length, n]; norm_num
          · simp [m₁, sdPt, sW_zero, ew_length, n]
        · cases e₂
          · simp [m₂, sdPt, sW_zero, ew_length, n]; norm_num
          · simp [m₂, sdPt, sW_zero, ew_length, n]
      exact (hf.2.2 _ hstp.mem_Dsk.1 _ hstp.mem_Dsk.2).mpr (.rel _ _ hstp)
    -- Define the two straight segments `seg₁ = [z₂, m₁]` and `seg₂ = [m₂, z₁]` and concatenate their images!
    let seg₁ : Set ℂ := segment ℝ z₂ m₁
    let seg₂ : Set ℂ := segment ℝ m₂ z₁
    have hseg₁_sub : seg₁ ⊆ closedBall (0 : ℂ) 1 :=
      (convex_closedBall 0 1).segment_subset (mem_closedBall_zero_iff.mpr (norm_per _ _).le)
        (mem_closedBall_zero_iff.mpr (norm_per _ _).le)
    have hseg₂_sub : seg₂ ⊆ closedBall (0 : ℂ) 1 :=
      (convex_closedBall 0 1).segment_subset (mem_closedBall_zero_iff.mpr (norm_per _ _).le)
        (mem_closedBall_zero_iff.mpr (norm_per _ _).le)
    have hne_z2m1 : z₂ ≠ m₁ := fun h => by
      have := per_injOn hn
        ⟨by linarith [Nat.cast_nonneg (α := ℝ) j_hole], by have : ((j_hole + 1 : ℕ) : ℝ) ≤ n := (by exact_mod_cast (by omega : j_hole + 1 ≤ n)); push_cast at this; linarith⟩
        ⟨by positivity, by have : ((j₁ + 1 : ℕ) : ℝ) ≤ n := (by exact_mod_cast (by omega : j₁ + 1 ≤ n)); push_cast at this; linarith⟩ h
      have : (j₁ : ℝ) + 1 ≤ (j_hole : ℝ) := by exact_mod_cast (by omega : j₁ + 1 ≤ j_hole)
      linarith
    have hne_m2z1 : m₂ ≠ z₁ := fun h => by
      have := per_injOn hn
        ⟨by positivity, by have : ((j₂ + 1 : ℕ) : ℝ) ≤ n := (by exact_mod_cast (by omega : j₂ + 1 ≤ n)); push_cast at this; linarith⟩
        ⟨by positivity, by have : ((j_hole + 1 : ℕ) : ℝ) ≤ n := (by exact_mod_cast (by omega : j_hole + 1 ≤ n)); push_cast at this; linarith⟩ h
      have : (j₂ : ℝ) + 1 ≤ (j_hole : ℝ) := by exact_mod_cast (by omega : j₂ + 1 ≤ j_hole)
      linarith
    have hdisj_seg : Disjoint seg₁ seg₂ := by
      rw [Set.disjoint_left]; intro w hw₁ hw₂
      have hL2_w : crossIm m₂ z₁ w = 0 := (crossIm_zero_iff_mem_segment (norm_per _ _) (norm_per _ _) hne_m2z1 (hseg₂_sub hw₂)).mpr hw₂
      have hL2_m1 : 0 < crossIm m₂ z₁ m₁ := by
        rw [crossIm_cyc, crossIm_cyc]
        exact crossIm_per_pos hn (by have : ((j₁ + 1 : ℕ) : ℝ) ≤ j₂ := (by exact_mod_cast (by omega : j₁ + 1 ≤ j₂)); push_cast at this; linarith)
          (by have : ((j₂ + 1 : ℕ) : ℝ) ≤ j_hole := (by exact_mod_cast (by omega : j₂ + 1 ≤ j_hole)); push_cast at this; linarith)
          (by have : ((j_hole + 1 : ℕ) : ℝ) ≤ n := (by exact_mod_cast (by omega : j_hole + 1 ≤ n)); push_cast at this; linarith)
      have hL2_z2 : 0 < crossIm m₂ z₁ z₂ :=
        crossIm_per_pos hn (by have : ((j₂ + 1 : ℕ) : ℝ) ≤ j_hole := (by exact_mod_cast (by omega : j₂ + 1 ≤ j_hole)); push_cast at this; linarith)
          (by linarith)
          (by have : ((j_hole + 1 : ℕ) : ℝ) ≤ n := (by exact_mod_cast (by omega : j_hole + 1 ≤ n)); push_cast at this; linarith)
      obtain ⟨r, s', hr, hs', hrs, rfl⟩ := hw₁
      rw [crossIm_affine m₂ z₁ z₂ m₁ r s' hrs] at hL2_w
      have : 0 < r * crossIm m₂ z₁ z₂ + s' * crossIm m₂ z₁ m₁ := by
        rcases eq_or_lt_of_le hr with rfl | hr'
        · rw [show s' = 1 by linarith]; linarith
        · nlinarith
      linarith
    -- Build the concatenated curve `γ : unitInterval → S` from `z₂` to `m₁ (= m₂)` to `z₁`:
    let s : S := f (0, z₂)
    let t : S := f (0, z₁)
    have hs_eq : s = holeP a b 1 f 0 u₂ := rfl
    have ht_eq : t = holeP a b 1 f 0 u₁ := rfl
    have hst : s ≠ t := fun h => by
      have hinj := (hole_loop hf (show 0 < 1 by omega)).2.1
      have := hinj ⟨by linarith, hu₂1⟩ ⟨by linarith, by linarith⟩ (hs_eq.symm.trans (h.trans ht_eq))
      linarith
    let γ : unitInterval → S := fun r =>
      if r.1 ≤ 1 / 2 then f (0, (1 - 2 * r.1) • z₂ + (2 * r.1) • m₁)
      else f (0, (2 - 2 * r.1) • m₂ + (2 * r.1 - 1) • z₁)
    have hγ0 : γ 0 = s := by simp [γ, s]
    have hγ1 : γ 1 = t := by
      simp only [γ, Set.Icc.coe_one, show ¬ ((1 : ℝ) ≤ 1 / 2) by norm_num, ↓reduceIte]
      have : (2 - 2 * (1 : ℝ)) • m₂ + (2 * (1 : ℝ) - 1) • z₁ = z₁ := by norm_num
      rw [this]
    have hγ_cont : Continuous γ := by
      let A₁ : Set unitInterval := {r | r.1 ≤ 1 / 2}
      let A₂ : Set unitInterval := {r | 1 / 2 ≤ r.1}
      have hA₁c : IsClosed A₁ := isClosed_le continuous_subtype_val continuous_const
      have hA₂c : IsClosed A₂ := isClosed_le continuous_const continuous_subtype_val
      have hcov : A₁ ∪ A₂ = univ := by ext r; simp [A₁, A₂, le_total]
      rw [← continuousOn_univ, ← hcov]
      refine ContinuousOn.union_of_isClosed ?_ ?_ hA₁c hA₂c
      · have h1 : ContinuousOn (fun r : unitInterval => f (0, (1 - 2 * r.1) • z₂ + (2 * r.1) • m₁)) A₁ :=
          hfc.comp (by fun_prop) fun r hr => hseg₁_sub ⟨1 - 2 * r.1, 2 * r.1, by linarith [show r.1 ≤ 1 / 2 from hr],
            by linarith [r.2.1], by ring, rfl⟩
        exact h1.congr fun r hr => by simp only [γ, ite_eq_left (show r.1 ≤ 1 / 2 from hr)]
      · have h2 : ContinuousOn (fun r : unitInterval => f (0, (2 - 2 * r.1) • m₂ + (2 * r.1 - 1) • z₁)) A₂ :=
          hfc.comp (by fun_prop) fun r hr => hseg₂_sub ⟨2 - 2 * r.1, 2 * r.1 - 1, by linarith [r.2.2],
            by linarith [show 1 / 2 ≤ r.1 from hr], by ring, rfl⟩
        refine h2.congr fun r hr => ?_
        by_cases hlt : r.1 ≤ 1 / 2
        · have heq : r.1 = 1 / 2 := le_antisymm hlt hr
          simp only [γ, ite_eq_left hlt, heq]
          have e1 : (1 - 2 * (1 / 2 : ℝ)) • z₂ + (2 * (1 / 2 : ℝ)) • m₁ = m₁ := by norm_num
          have e2 : (2 - 2 * (1 / 2 : ℝ)) • m₂ + (2 * (1 / 2 : ℝ) - 1) • z₁ = m₂ := by norm_num
          rw [e1, e2, hfm12]
        · simp only [γ, ite_eq_right hlt]
    have hγ_norm_lt : ∀ r : unitInterval, r.1 ≠ 0 → r.1 ≠ 1 / 2 → r.1 ≠ 1 →
        (r.1 < 1 / 2 ∧ ‖(1 - 2 * r.1) • z₂ + (2 * r.1) • m₁‖ < 1) ∨
        (1 / 2 < r.1 ∧ ‖(2 - 2 * r.1) • m₂ + (2 * r.1 - 1) • z₁‖ < 1) := by
      intro r hr0 hrh hr1
      rcases lt_or_gt_of_ne hrh with hlt | hgt
      · left; exact ⟨hlt, norm_lt_one_of_openSegment (norm_per _ _) (norm_per _ _) hne_z2m1
          ⟨1 - 2 * r.1, 2 * r.1, by linarith, by linarith [lt_of_le_of_ne r.2.1 (Ne.symm hr0)], by ring, rfl⟩⟩
      · right; exact ⟨hgt, norm_lt_one_of_openSegment (norm_per _ _) (norm_per _ _) hne_m2z1
          ⟨2 - 2 * r.1, 2 * r.1 - 1, by linarith [lt_of_le_of_ne r.2.2 hr1], by linarith, by ring, rfl⟩⟩
    have hγ_inj : Function.Injective γ := by
      intro r₁ r₂ he
      let w : unitInterval → ℂ := fun r =>
        if r.1 ≤ 1 / 2 then (1 - 2 * r.1) • z₂ + (2 * r.1) • m₁
        else (2 - 2 * r.1) • m₂ + (2 * r.1 - 1) • z₁
      have hγ_eq : ∀ r, γ r = f (0, w r) := fun r => by dsimp only [γ, w]; split_ifs <;> rfl
      have hw_mem : ∀ r, w r ∈ closedBall (0 : ℂ) 1 := fun r => by
        dsimp only [w]; split_ifs with h
        · exact hseg₁_sub ⟨1 - 2 * r.1, 2 * r.1, by linarith, by linarith [r.2.1], by ring, rfl⟩
        · exact hseg₂_sub ⟨2 - 2 * r.1, 2 * r.1 - 1, by linarith [r.2.2], by linarith, by ring, rfl⟩
      have hw_lt : ∀ r : unitInterval, r.1 ≠ 0 → r.1 ≠ 1 / 2 → r.1 ≠ 1 → ‖w r‖ < 1 := fun r h0 hh h1 => by
        rcases hγ_norm_lt r h0 hh h1 with ⟨hlt, hn1⟩ | ⟨hgt, hn2⟩
        · simpa only [w, ite_eq_left hlt.le] using hn1
        · simpa only [w, ite_eq_right (not_le.mpr hgt)] using hn2
      have hspec : ∀ r : unitInterval, r.1 = 0 ∨ r.1 = 1 / 2 ∨ r.1 = 1 → ‖w r‖ = 1 := fun r hr => by
        rcases hr with h0 | hh | h1
        · simp [w, h0]; exact norm_per _ _
        · simp only [w, hh, le_refl, ↓reduceIte]
          have : (1 - 2 * (1 / 2 : ℝ)) • z₂ + (2 * (1 / 2 : ℝ)) • m₁ = m₁ := by norm_num
          rw [this]; exact norm_per _ _
        · simp only [w, h1, show ¬ ((1 : ℝ) ≤ 1 / 2) by norm_num, ↓reduceIte]
          have : (2 - 2 * (1 : ℝ)) • m₂ + (2 * (1 : ℝ) - 1) • z₁ = z₁ := by norm_num
          rw [this]; exact norm_per _ _
      by_cases h1 : r₁.1 = 0 ∨ r₁.1 = 1 / 2 ∨ r₁.1 = 1
      · by_cases h2 : r₂.1 = 0 ∨ r₂.1 = 1 / 2 ∨ r₂.1 = 1
        · have hs_bd : s ∈ bd S := hbd_eq ▸ mem_biUnion (show 0 < 1 by omega) ⟨u₂, ⟨by linarith, hu₂1.le⟩, hs_eq.symm⟩
          have ht_bd : t ∈ bd S := hbd_eq ▸ mem_biUnion (show 0 < 1 by omega) ⟨u₁, ⟨hu₁0.le, by linarith⟩, ht_eq.symm⟩
          have hγ_half : ∀ r : unitInterval, r.1 = 1 / 2 → γ r = f (0, m₁) := fun r hr => by
            simp only [γ, hr, le_refl, ↓reduceIte]
            have : (1 - 2 * (1 / 2 : ℝ)) • z₂ + (2 * (1 / 2 : ℝ)) • m₁ = m₁ := by norm_num
            rw [this]
          rcases h1 with h10 | h1h | h11 <;> rcases h2 with h20 | h2h | h21
          · exact Subtype.ext (h10.trans h20.symm)
          · exfalso; rw [show r₁ = 0 from Subtype.ext h10, hγ0, hγ_half r₂ h2h] at he; exact hm1_not_bd (he ▸ hs_bd)
          · exfalso; rw [show r₁ = 0 from Subtype.ext h10, hγ0, show r₂ = 1 from Subtype.ext h21, hγ1] at he; exact hst he
          · exfalso; rw [hγ_half r₁ h1h, show r₂ = 0 from Subtype.ext h20, hγ0] at he; exact hm1_not_bd (he.symm ▸ hs_bd)
          · exact Subtype.ext (h1h.trans h2h.symm)
          · exfalso; rw [hγ_half r₁ h1h, show r₂ = 1 from Subtype.ext h21, hγ1] at he; exact hm1_not_bd (he.symm ▸ ht_bd)
          · exfalso; rw [show r₁ = 1 from Subtype.ext h11, hγ1, show r₂ = 0 from Subtype.ext h20, hγ0] at he; exact hst he.symm
          · exfalso; rw [show r₁ = 1 from Subtype.ext h11, hγ1, hγ_half r₂ h2h] at he; exact hm1_not_bd (he ▸ ht_bd)
          · exact Subtype.ext (h11.trans h21.symm)
        · exfalso; push Not at h2
          have hrel := (hf.2.2 _ (hDsk _ (hw_mem r₂)) _ (hDsk _ (hw_mem r₁))).mp (by rw [← hγ_eq, ← hγ_eq, he])
          have hnorm := congrArg (fun p : ℕ × ℂ => ‖p.2‖) (PRel.eq_of_lt hrel (hw_lt r₂ h2.1 h2.2.1 h2.2.2))
          linarith only [hnorm, hspec r₁ h1, hw_lt r₂ h2.1 h2.2.1 h2.2.2]
      · push Not at h1
        have hrel := (hf.2.2 _ (hDsk _ (hw_mem r₁)) _ (hDsk _ (hw_mem r₂))).mp (by rw [← hγ_eq, ← hγ_eq, he])
        have hw12 : w r₂ = w r₁ := congrArg Prod.snd (PRel.eq_of_lt hrel (hw_lt r₁ h1.1 h1.2.1 h1.2.2))
        have hside1 : r₁.1 ≤ 1 / 2 ↔ r₂.1 ≤ 1 / 2 := by
          constructor <;> intro hle
          · by_contra hgt
            have hgt' : 1 / 2 < r₂.1 := not_le.mp hgt
            have hm1 : w r₁ ∈ seg₁ := by simp only [w, ite_eq_left hle]; exact ⟨1 - 2 * r₁.1, 2 * r₁.1, by linarith only [hle], by linarith only [r₁.2.1], by ring, rfl⟩
            have hm2 : w r₂ ∈ seg₂ := by simp only [w, ite_eq_right hgt]; exact ⟨2 - 2 * r₂.1, 2 * r₂.1 - 1, by linarith only [r₂.2.2], by linarith only [hgt'], by ring, rfl⟩
            exact Set.disjoint_left.mp hdisj_seg hm1 (hw12 ▸ hm2)
          · by_contra hgt
            have hgt' : 1 / 2 < r₁.1 := not_le.mp hgt
            have hm1 : w r₁ ∈ seg₂ := by simp only [w, ite_eq_right hgt]; exact ⟨2 - 2 * r₁.1, 2 * r₁.1 - 1, by linarith only [r₁.2.2], by linarith only [hgt'], by ring, rfl⟩
            have hm2 : w r₂ ∈ seg₁ := by simp only [w, ite_eq_left hle]; exact ⟨1 - 2 * r₂.1, 2 * r₂.1, by linarith only [hle], by linarith only [r₂.2.1], by ring, rfl⟩
            exact Set.disjoint_left.mp hdisj_seg hm2 (hw12.symm ▸ hm1)
        apply Subtype.ext
        by_cases hle : r₁.1 ≤ 1 / 2
        · have hle2 : r₂.1 ≤ 1 / 2 := hside1.mp hle
          simp only [w, ite_eq_left hle, ite_eq_left hle2] at hw12
          have hsub : (2 * (r₂.1 - r₁.1)) • (m₁ - z₂) = 0 := by
            rw [← sub_eq_zero.mpr hw12]; simp only [Complex.real_smul]; push_cast; ring
          rcases smul_eq_zero.mp hsub with h0 | h0
          · linarith only [h0]
          · exact absurd (sub_eq_zero.mp h0).symm hne_z2m1
        · have hle2 : ¬ r₂.1 ≤ 1 / 2 := fun h => hle (hside1.mpr h)
          simp only [w, ite_eq_right hle, ite_eq_right hle2] at hw12
          have hsub : (2 * (r₂.1 - r₁.1)) • (z₁ - m₂) = 0 := by
            rw [← sub_eq_zero.mpr hw12]; simp only [Complex.real_smul]; push_cast; ring
          rcases smul_eq_zero.mp hsub with h0 | h0
          · linarith only [h0]
          · exact absurd (sub_eq_zero.mp h0).symm hne_m2z1
    let F : Set S := range γ
    have hFl : IsLineWithEnds F s t := by
      let eγ : unitInterval ≃ₜ F :=
        (Continuous.subtype_mk hγ_cont fun r => mem_range_self r).homeoOfEquivCompactToT2
          (f := Equiv.ofBijective (fun r => ⟨γ r, mem_range_self r⟩)
            ⟨fun _ _ h => hγ_inj (congrArg Subtype.val h), fun ⟨_, r, hr⟩ => ⟨r, Subtype.ext hr⟩⟩)
      exact ⟨eγ, hγ0, hγ1⟩
    have hFb : F ∩ bd S = {s, t} := by
      ext x; constructor
      · rintro ⟨⟨r, rfl⟩, hbd⟩
        by_cases hr0 : r.1 = 0
        · exact Or.inl (by rw [show r = 0 from Subtype.ext hr0, hγ0])
        · by_cases hr1 : r.1 = 1
          · exact Or.inr (mem_singleton_iff.mpr (by rw [show r = 1 from Subtype.ext hr1, hγ1]))
          · exfalso
            by_cases hrh : r.1 = 1 / 2
            · have : γ r = f (0, m₁) := by
                simp only [γ, hrh, le_refl, ↓reduceIte]
                have e1 : (1 - 2 * (1 / 2 : ℝ)) • z₂ + (2 * (1 / 2 : ℝ)) • m₁ = m₁ := by norm_num
                rw [e1]
              exact hm1_not_bd (this ▸ hbd)
            · rcases hγ_norm_lt r hr0 hrh hr1 with ⟨hlt, hn1⟩ | ⟨hgt, hn2⟩
              · exact hbd_not_lt _ hn1 (by simpa only [γ, ite_eq_left hlt.le] using hbd)
              · exact hbd_not_lt _ hn2 (by simpa only [γ, ite_eq_right (not_le.mpr hgt)] using hbd)
      · rintro (rfl | rfl)
        · exact ⟨⟨0, hγ0⟩, hbd_eq ▸ mem_biUnion (show 0 < 1 by omega) ⟨u₂, ⟨by linarith only [hu₁0, hu₁₂], hu₂1.le⟩, hs_eq.symm⟩⟩
        · exact ⟨⟨1, hγ1⟩, hbd_eq ▸ mem_biUnion (show 0 < 1 by omega) ⟨u₁, ⟨hu₁0.le, by linarith only [hu₁₂, hu₂1]⟩, ht_eq.symm⟩⟩
    -- Prove `IsPreconnected Fᶜ` via the 3 convex open regions `R₁, R₂, R₃` in `ball 0 1 \ (seg₁ ∪ seg₂)` + 2 bridge points!
    let L₁ : ℂ → ℝ := crossIm z₂ m₁
    let L₂ : ℂ → ℝ := crossIm m₂ z₁
    have hL₁_cont : Continuous L₁ := by unfold L₁ crossIm; fun_prop
    have hL₂_cont : Continuous L₂ := by unfold L₂ crossIm; fun_prop
    let R₁ : Set ℂ := ball (0 : ℂ) 1 ∩ {z | 0 < L₁ z ∧ 0 < L₂ z}
    let R₂ : Set ℂ := ball (0 : ℂ) 1 ∩ {z | L₂ z < 0}
    let R₃ : Set ℂ := ball (0 : ℂ) 1 ∩ {z | L₁ z < 0}
    have hR₁_pre : IsPreconnected R₁ := by
      refine ((convex_ball (0 : ℂ) 1).inter ?_).isPreconnected
      intro a ha b hb u v hu hv huv
      show 0 < L₁ (u • a + v • b) ∧ 0 < L₂ (u • a + v • b)
      dsimp only [L₁, L₂]
      rw [crossIm_affine _ _ _ _ u v huv, crossIm_affine _ _ _ _ u v huv]
      rcases eq_or_lt_of_le hu with rfl | hu'
      · rw [show v = 1 by linarith only [huv]]; simpa using hb
      · exact ⟨by nlinarith only [hu', hv, ha.1, hb.1], by nlinarith only [hu', hv, ha.2, hb.2]⟩
    have hR₂_pre : IsPreconnected R₂ := by
      refine ((convex_ball (0 : ℂ) 1).inter ?_).isPreconnected
      intro a ha b hb u v hu hv huv
      show L₂ (u • a + v • b) < 0
      dsimp only [L₂]; rw [crossIm_affine _ _ _ _ u v huv]
      rcases eq_or_lt_of_le hu with rfl | hu'
      · rw [show v = 1 by linarith only [huv]]; simpa using hb
      · nlinarith only [hu', hv, show L₂ a < 0 from ha, show L₂ b < 0 from hb]
    have hR₃_pre : IsPreconnected R₃ := by
      refine ((convex_ball (0 : ℂ) 1).inter ?_).isPreconnected
      intro a ha b hb u v hu hv huv
      show L₁ (u • a + v • b) < 0
      dsimp only [L₁]; rw [crossIm_affine _ _ _ _ u v huv]
      rcases eq_or_lt_of_le hu with rfl | hu'
      · rw [show v = 1 by linarith only [huv]]; simpa using hb
      · nlinarith only [hu', hv, show L₁ a < 0 from ha, show L₁ b < 0 from hb]
    let fR₁ : Set S := (fun z => f (0, z)) '' R₁
    let fR₂ : Set S := (fun z => f (0, z)) '' R₂
    let fR₃ : Set S := (fun z => f (0, z)) '' R₃
    have hfR₁_pre : IsPreconnected fR₁ := hR₁_pre.image _ (hfc.mono fun _ h => ball_subset_closedBall h.1)
    have hfR₂_pre : IsPreconnected fR₂ := hR₂_pre.image _ (hfc.mono fun _ h => ball_subset_closedBall h.1)
    have hfR₃_pre : IsPreconnected fR₃ := hR₃_pre.image _ (hfc.mono fun _ h => ball_subset_closedBall h.1)
    have hfR_sub : fR₁ ∪ fR₂ ∪ fR₃ ⊆ Fᶜ := by
      have hoff : ∀ z ∈ ball (0 : ℂ) 1, L₁ z ≠ 0 → L₂ z ≠ 0 → f (0, z) ∉ F := by
        intro z hz h1 h2 ⟨r, hr⟩
        have hz_lt : ‖z‖ < 1 := mem_ball_zero_iff.mp hz
        let wr : ℂ := if r.1 ≤ 1 / 2 then (1 - 2 * r.1) • z₂ + (2 * r.1) • m₁
          else (2 - 2 * r.1) • m₂ + (2 * r.1 - 1) • z₁
        have hwr_mem : wr ∈ closedBall (0 : ℂ) 1 := by
          dsimp only [wr]; split_ifs with hle
          · exact hseg₁_sub ⟨1 - 2 * r.1, 2 * r.1, by linarith, by linarith [r.2.1], by ring, rfl⟩
          · exact hseg₂_sub ⟨2 - 2 * r.1, 2 * r.1 - 1, by linarith [r.2.2], by linarith, by ring, rfl⟩
        have hγ_wr : γ r = f (0, wr) := by dsimp only [γ, wr]; split_ifs <;> rfl
        have hrel := (hf.2.2 _ (hDsk z (ball_subset_closedBall hz)) _ (hDsk wr hwr_mem)).mp (hr.symm.trans hγ_wr)
        have hzw : wr = z := congrArg Prod.snd (PRel.eq_of_lt hrel hz_lt)
        by_cases hle : r.1 ≤ 1 / 2
        · have hz1 : z ∈ seg₁ := hzw ▸ (by simp only [wr, ite_eq_left hle]; exact ⟨1 - 2 * r.1, 2 * r.1, by linarith only [hle], by linarith only [r.2.1], by ring, rfl⟩)
          exact h1 ((crossIm_zero_iff_mem_segment (norm_per _ _) (norm_per _ _) hne_z2m1 (ball_subset_closedBall hz)).mpr hz1)
        · have hgt : 1 / 2 < r.1 := not_le.mp hle
          have hz2 : z ∈ seg₂ := hzw ▸ (by simp only [wr, ite_eq_right hle]; exact ⟨2 - 2 * r.1, 2 * r.1 - 1, by linarith only [r.2.2], by linarith only [hgt], by ring, rfl⟩)
          exact h2 ((crossIm_zero_iff_mem_segment (norm_per _ _) (norm_per _ _) hne_m2z1 (ball_subset_closedBall hz)).mpr hz2)
      rintro _ ((⟨z, ⟨hz, h1, h2⟩, rfl⟩ | ⟨z, ⟨hz, h2⟩, rfl⟩) | ⟨z, ⟨hz, h1⟩, rfl⟩)
      · exact hoff z hz h1.ne' h2.ne'
      · have h1 : L₁ z ≠ 0 := fun h0 => by
          have hz1 : z ∈ seg₁ := (crossIm_zero_iff_mem_segment (norm_per _ _) (norm_per _ _) hne_z2m1 (ball_subset_closedBall hz)).mp h0
          obtain ⟨r, s', hr, hs', hrs, rfl⟩ := hz1
          have hL2_m1 : 0 < L₂ m₁ := by
            rw [show L₂ m₁ = crossIm m₂ z₁ m₁ from rfl, crossIm_cyc, crossIm_cyc]
            exact crossIm_per_pos hn (by have : ((j₁ + 1 : ℕ) : ℝ) ≤ j₂ := (by exact_mod_cast (by omega : j₁ + 1 ≤ j₂)); push_cast at this; linarith only [this])
              (by have : ((j₂ + 1 : ℕ) : ℝ) ≤ j_hole := (by exact_mod_cast (by omega : j₂ + 1 ≤ j_hole)); push_cast at this; linarith only [this, hu₁0])
              (by have : ((j_hole + 1 : ℕ) : ℝ) ≤ n := (by exact_mod_cast (by omega : j_hole + 1 ≤ n)); push_cast at this; linarith only [this, hu₁₂, hu₂1, Nat.cast_nonneg (α := ℝ) j₁])
          have hL2_z2 : 0 < L₂ z₂ :=
            crossIm_per_pos hn (by have : ((j₂ + 1 : ℕ) : ℝ) ≤ j_hole := (by exact_mod_cast (by omega : j₂ + 1 ≤ j_hole)); push_cast at this; linarith only [this, hu₁0])
              (by linarith only [hu₁₂])
              (by have : ((j_hole + 1 : ℕ) : ℝ) ≤ n := (by exact_mod_cast (by omega : j_hole + 1 ≤ n)); push_cast at this; linarith only [this, hu₂1, Nat.cast_nonneg (α := ℝ) j₂])
          have hpos : 0 < L₂ (r • z₂ + s' • m₁) := by
            dsimp only [L₂]; rw [crossIm_affine _ _ _ _ r s' hrs]
            rcases eq_or_lt_of_le hr with rfl | hr'
            · rw [show s' = 1 by linarith only [hrs]]; linarith only [hL2_m1]
            · nlinarith only [hr', hs', hL2_z2, hL2_m1]
          linarith only [hpos, show L₂ (r • z₂ + s' • m₁) < 0 from h2]
        exact hoff z hz h1 h2.ne
      · have h2 : L₂ z ≠ 0 := fun h0 => by
          have hz2 : z ∈ seg₂ := (crossIm_zero_iff_mem_segment (norm_per _ _) (norm_per _ _) hne_m2z1 (ball_subset_closedBall hz)).mp h0
          obtain ⟨r, s', hr, hs', hrs, rfl⟩ := hz2
          have hL1_m2 : 0 < L₁ m₂ := by
            rw [show L₁ m₂ = crossIm z₂ m₁ m₂ from rfl, crossIm_cyc]
            exact crossIm_per_pos hn (by have : ((j₁ + 1 : ℕ) : ℝ) ≤ j₂ := (by exact_mod_cast (by omega : j₁ + 1 ≤ j₂)); push_cast at this; linarith only [this])
              (by have : ((j₂ + 1 : ℕ) : ℝ) ≤ j_hole := (by exact_mod_cast (by omega : j₂ + 1 ≤ j_hole)); push_cast at this; linarith only [this, hu₁0, hu₁₂])
              (by have : ((j_hole + 1 : ℕ) : ℝ) ≤ n := (by exact_mod_cast (by omega : j_hole + 1 ≤ n)); push_cast at this; linarith only [this, hu₂1, Nat.cast_nonneg (α := ℝ) j₁])
          have hL1_z1 : 0 < L₁ z₁ := by
            rw [show L₁ z₁ = crossIm z₂ m₁ z₁ from rfl, crossIm_cyc]
            exact crossIm_per_pos hn (by have : ((j₁ + 1 : ℕ) : ℝ) ≤ j_hole := (by exact_mod_cast (by omega : j₁ + 1 ≤ j_hole)); push_cast at this; linarith only [this, hu₁0])
              (by linarith only [hu₁₂])
              (by have : ((j_hole + 1 : ℕ) : ℝ) ≤ n := (by exact_mod_cast (by omega : j_hole + 1 ≤ n)); push_cast at this; linarith only [this, hu₂1, Nat.cast_nonneg (α := ℝ) j₁])
          have hpos : 0 < L₁ (r • m₂ + s' • z₁) := by
            dsimp only [L₁]; rw [crossIm_affine _ _ _ _ r s' hrs]
            rcases eq_or_lt_of_le hr with rfl | hr'
            · rw [show s' = 1 by linarith only [hrs]]; linarith only [hL1_z1]
            · nlinarith only [hr', hs', hL1_m2, hL1_z1]
          linarith only [hpos, show L₁ (r • m₂ + s' • z₁) < 0 from h1]
        exact hoff z hz h1.ne h2
    -- Closure of `fR₁ ∪ fR₂ ∪ fR₃` is `univ`:
    have hdense_R : closure (fR₁ ∪ fR₂ ∪ fR₃) = univ := by
      have hball_dense : closure (R₁ ∪ R₂ ∪ R₃) = closedBall (0 : ℂ) 1 := by
        apply subset_antisymm
        · exact closure_minimal (fun z hz => by
            rcases hz with (h | h) | h <;> exact ball_subset_closedBall h.1) isClosed_closedBall
        · intro z hz
          rw [Metric.mem_closure_iff]; intro ε hε
          -- Pick a point in `ball 0 1 ∩ ball z ε` off the two lines `{L₁ = 0}` and `{L₂ = 0}`:
          let w₀ : ℂ := if ‖z‖ = 0 then 0 else ((1 - min (1 / 2) (ε / (4 * ‖z‖))) : ℝ) • z
          have hw₀_ball : w₀ ∈ ball (0 : ℂ) 1 := by
            dsimp only [w₀]; split_ifs with h0
            · simp
            · rw [mem_ball_zero_iff, norm_smul, Real.norm_of_nonneg (by linarith [min_le_left (1 / 2 : ℝ) (ε / (4 * ‖z‖))])]
              have hzpos : 0 < ‖z‖ := lt_of_le_of_ne (norm_nonneg z) (Ne.symm h0)
              have hmin : 0 < min (1 / 2 : ℝ) (ε / (4 * ‖z‖)) := lt_min (by norm_num) (by positivity)
              have hzle : ‖z‖ ≤ 1 := mem_closedBall_zero_iff.mp hz
              nlinarith
          have hw₀_dist : dist w₀ z < ε / 2 := by
            dsimp only [w₀]; split_ifs with h0
            · rw [norm_eq_zero.mp h0, dist_self]; positivity
            · have hzpos : 0 < ‖z‖ := lt_of_le_of_ne (norm_nonneg z) (Ne.symm h0)
              rw [dist_eq_norm, show ((1 - min (1 / 2 : ℝ) (ε / (4 * ‖z‖))) : ℝ) • z - z =
                (-(min (1 / 2 : ℝ) (ε / (4 * ‖z‖)))) • z by rw [sub_smul, one_smul, neg_smul]; abel,
                norm_smul, Real.norm_eq_abs, abs_neg, abs_of_pos (lt_min (by norm_num) (by positivity))]
              have hle : min (1 / 2 : ℝ) (ε / (4 * ‖z‖)) ≤ ε / (4 * ‖z‖) := min_le_right _ _
              calc min (1 / 2 : ℝ) (ε / (4 * ‖z‖)) * ‖z‖ ≤ (ε / (4 * ‖z‖)) * ‖z‖ := by nlinarith only [hle, hzpos]
                _ = ε / 4 := by field_simp [hzpos.ne']
                _ < ε / 2 := by linarith only [hε]
          let ρ := min (1 - ‖w₀‖) (ε / 2) / 2
          have hρ : 0 < ρ := half_pos (lt_min (sub_pos.mpr (mem_ball_zero_iff.mp hw₀_ball)) (half_pos hε))
          -- Move in the open ball `ball w₀ ρ` (all in `ball 0 1 ∩ ball z ε`) to avoid `{L₁ = 0} ∪ {L₂ = 0}`:
          have hex_off : ∃ w ∈ ball w₀ ρ, L₁ w ≠ 0 ∧ L₂ w ≠ 0 := by
            -- Choose a vector `v ≠ 0` with `L₁(w₀ + t v)` and `L₂(w₀ + t v)` both nonconstant in `t`:
            have hv_ex : ∃ v : ℂ, ‖v‖ = 1 ∧ (v * star (m₁ - z₂)).im ≠ 0 ∧ (v * star (z₁ - m₂)).im ≠ 0 := by
              -- Try `v = 1`, `v = I`, `v = (1 + I)/√2`: if both `1` and `I` fail for one functional, that functional is 0 (impossible since `m₁ ≠ z₂`, `z₁ ≠ m₂`)!
              have hne1 : star (m₁ - z₂) ≠ 0 := star_ne_zero.mpr (sub_ne_zero.mpr hne_z2m1.symm)
              have hne2 : star (z₁ - m₂) ≠ 0 := star_ne_zero.mpr (sub_ne_zero.mpr hne_m2z1.symm)
              by_cases h1 : ((1 : ℂ) * star (m₁ - z₂)).im ≠ 0 ∧ ((1 : ℂ) * star (z₁ - m₂)).im ≠ 0
              · exact ⟨1, by simp, h1.1, h1.2⟩
              · by_cases h2 : (I * star (m₁ - z₂)).im ≠ 0 ∧ (I * star (z₁ - m₂)).im ≠ 0
                · exact ⟨I, Complex.norm_I, h2.1, h2.2⟩
                · -- Then one has `.im = 0` and the other has `.re = 0`, so `(1 + I)/‖1 + I‖` has BOTH nonzero!
                  let u : ℂ := (1 + I) / ‖(1 : ℂ) + I‖
                  have h1I_ne : (1 : ℂ) + I ≠ 0 := fun h => by have := congrArg Complex.re h; simp at this
                  have h1I_pos : 0 < ‖(1 : ℂ) + I‖ := norm_pos_iff.mpr h1I_ne
                  refine ⟨u, by simp [u, div_self h1I_pos.ne'], ?_, ?_⟩
                  · intro h0
                    simp only [u, div_mul_eq_mul_div, Complex.div_ofReal_im, div_eq_zero_iff] at h0
                    have h0' : ((1 + I) * star (m₁ - z₂)).im = 0 := h0.resolve_right h1I_pos.ne'
                    have hsum : ((1 + I) * star (m₁ - z₂)).im = (star (m₁ - z₂)).im + (star (m₁ - z₂)).re := by
                      simp [add_mul]
                    rw [hsum] at h0'
                    by_cases ha0 : (star (m₁ - z₂)).im = 0
                    · exact hne1 (Complex.ext (by simp only [Complex.zero_re]; linarith only [h0', ha0]) (by simp only [Complex.zero_im]; exact ha0))
                    · by_cases hb0 : (star (m₁ - z₂)).re = 0
                      · exact hne1 (Complex.ext (by simp only [Complex.zero_re]; exact hb0) (by simp only [Complex.zero_im]; linarith only [h0', hb0]))
                      · push Not at h1 h2
                        have hsec1 : (star (z₁ - m₂)).im = 0 := by simpa using h1 (by simpa using ha0)
                        have hsec2 : (star (z₁ - m₂)).re = 0 := by simpa using h2 (by simpa using hb0)
                        exact hne2 (Complex.ext (by simp only [Complex.zero_re]; exact hsec2) (by simp only [Complex.zero_im]; exact hsec1))
                  · intro h0
                    simp only [u, div_mul_eq_mul_div, Complex.div_ofReal_im, div_eq_zero_iff] at h0
                    have h0' : ((1 + I) * star (z₁ - m₂)).im = 0 := h0.resolve_right h1I_pos.ne'
                    have hsum : ((1 + I) * star (z₁ - m₂)).im = (star (z₁ - m₂)).im + (star (z₁ - m₂)).re := by
                      simp [add_mul]
                    rw [hsum] at h0'
                    by_cases ha0 : (star (z₁ - m₂)).im = 0
                    · exact hne2 (Complex.ext (by simp only [Complex.zero_re]; linarith only [h0', ha0]) (by simp only [Complex.zero_im]; exact ha0))
                    · by_cases hb0 : (star (z₁ - m₂)).re = 0
                      · exact hne2 (Complex.ext (by simp only [Complex.zero_re]; exact hb0) (by simp only [Complex.zero_im]; linarith only [h0', hb0]))
                      · push Not at h1 h2
                        have hfir1 : (star (m₁ - z₂)).im = 0 := by
                          by_contra h; exact ha0 (by simpa using h1 (by simpa using h))
                        have hfir2 : (star (m₁ - z₂)).re = 0 := by
                          by_contra h; exact hb0 (by simpa using h2 (by simpa using h))
                        exact hne1 (Complex.ext (by simp only [Complex.zero_re]; exact hfir2) (by simp only [Complex.zero_im]; exact hfir1))
            obtain ⟨v, hvn, hv1, hv2⟩ := hv_ex
            -- Among `t ∈ {0, ρ/4, ρ/2}` (3 distinct values), at most 2 can zero the two nonconstant linear functions!
            have hlin1 : ∀ t : ℝ, L₁ (w₀ + t • v) = L₁ w₀ + t * (v * star (m₁ - z₂)).im := fun t => by
              dsimp only [L₁, crossIm]
              rw [show w₀ + t • v - z₂ = (w₀ - z₂) + t • v by abel, add_mul, Complex.add_im]
              simp only [Complex.real_smul, mul_assoc, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
                zero_mul, add_zero]
            have hlin2 : ∀ t : ℝ, L₂ (w₀ + t • v) = L₂ w₀ + t * (v * star (z₁ - m₂)).im := fun t => by
              dsimp only [L₂, crossIm]
              rw [show w₀ + t • v - m₂ = (w₀ - m₂) + t • v by abel, add_mul, Complex.add_im]
              simp only [Complex.real_smul, mul_assoc, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
                zero_mul, add_zero]
            have hex_t : ∃ t : ℝ, 0 ≤ t ∧ t < ρ ∧ L₁ (w₀ + t • v) ≠ 0 ∧ L₂ (w₀ + t • v) ≠ 0 := by
              by_contra hall; push Not at hall
              have h0 := hall 0 le_rfl hρ
              have h1 := hall (ρ / 4) (by linarith only [hρ]) (by linarith only [hρ])
              have h2 := hall (ρ / 2) (by linarith only [hρ]) (by linarith only [hρ])
              rw [hlin1, hlin2] at h0 h1 h2
              by_cases ha : L₁ w₀ + 0 * (v * star (m₁ - z₂)).im = 0
              · have hb : L₁ w₀ + ρ / 4 * (v * star (m₁ - z₂)).im ≠ 0 := fun h => hv1 (by nlinarith only [ha, h, hρ])
                have hc : L₁ w₀ + ρ / 2 * (v * star (m₁ - z₂)).im ≠ 0 := fun h => hv1 (by nlinarith only [ha, h, hρ])
                have h2a := h1 hb; have h2b := h2 hc
                exact hv2 (by nlinarith only [h2a, h2b, hρ])
              · have h20 := h0 ha
                have hb : L₂ w₀ + ρ / 4 * (v * star (z₁ - m₂)).im ≠ 0 := fun h => hv2 (by nlinarith only [h20, h, hρ])
                have hc : L₂ w₀ + ρ / 2 * (v * star (z₁ - m₂)).im ≠ 0 := fun h => hv2 (by nlinarith only [h20, h, hρ])
                have h1a : L₁ w₀ + ρ / 4 * (v * star (m₁ - z₂)).im = 0 := by by_contra h; exact hb (h1 h)
                have h1b : L₁ w₀ + ρ / 2 * (v * star (m₁ - z₂)).im = 0 := by by_contra h; exact hc (h2 h)
                exact hv1 (by nlinarith only [h1a, h1b, hρ])
            obtain ⟨t, ht0, htρ, ht1, ht2⟩ := hex_t
            refine ⟨w₀ + t • v, ?_, ht1, ht2⟩
            rw [mem_ball, dist_eq_norm, show w₀ + t • v - w₀ = t • v by abel,
              norm_smul, Real.norm_of_nonneg ht0, hvn, mul_one]
            exact htρ
          obtain ⟨w, hwB, hw1, hw2⟩ := hex_off
          have hw_ball : w ∈ ball (0 : ℂ) 1 := by
            rw [mem_ball_zero_iff]
            have h1 : ‖w - w₀‖ < ρ := by rwa [mem_ball, dist_eq_norm] at hwB
            have h2 : ρ ≤ (1 - ‖w₀‖) / 2 := div_le_div_of_nonneg_right (min_le_left _ _) (by norm_num)
            have h3 : ‖w‖ ≤ ‖w - w₀‖ + ‖w₀‖ := by simpa using norm_add_le (w - w₀) w₀
            linarith [mem_ball_zero_iff.mp hw₀_ball]
          have hw_dist : dist w z < ε := by
            have h1 : dist w w₀ < ρ := mem_ball.mp hwB
            have h2 : ρ ≤ ε / 4 := by
              dsimp only [ρ]; linarith only [min_le_right (1 - ‖w₀‖) (ε / 2)]
            calc dist w z ≤ dist w w₀ + dist w₀ z := dist_triangle w w₀ z
              _ < ε := by linarith only [h1, h2, hw₀_dist, hε]
          refine ⟨w, ?_, dist_comm w z ▸ hw_dist⟩
          rcases lt_or_gt_of_ne hw1 with h1lt | h1gt
          · exact Or.inr ⟨hw_ball, h1lt⟩
          · rcases lt_or_gt_of_ne hw2 with h2lt | h2gt
            · exact Or.inl (Or.inr ⟨hw_ball, h2lt⟩)
            · exact Or.inl (Or.inl ⟨hw_ball, h1gt, h2gt⟩)
      have hsurj : (fun z => f (0, z)) '' closedBall (0 : ℂ) 1 = univ := by
        ext y; simp only [mem_univ, iff_true, mem_image]
        have hy : y ∈ f '' Dsk (sW (ew a b 1)) := hf.2.1 ▸ mem_univ y
        obtain ⟨⟨i, z⟩, hz, rfl⟩ := hy
        have hi : i = 0 := by by_contra h; exact hz.1 (by simp [sW, h, nW])
        subst hi; exact ⟨z, by simpa using hz.2, rfl⟩
      apply subset_antisymm (subset_univ _)
      rw [← hsurj, ← hball_dense]
      have h1 : (fun z => f (0, z)) '' closure (R₁ ∪ R₂ ∪ R₃) ⊆ closure ((fun z => f (0, z)) '' (R₁ ∪ R₂ ∪ R₃)) := by
        rintro y ⟨z, hz, rfl⟩
        rw [hball_dense] at hz
        rw [mem_closure_iff_nhds] at *
        intro U hU
        have hpre : (fun z => f (0, z)) ⁻¹' U ∈ 𝓝[closedBall (0 : ℂ) 1] z := (hfc z hz) hU
        obtain ⟨V, hVo, hzV, hVsub⟩ := mem_nhdsWithin.mp hpre
        obtain ⟨w, hwV, hwR⟩ := _root_.mem_closure_iff.mp (hball_dense ▸ hz) V hVo hzV
        exact ⟨f (0, w), hVsub ⟨hwV, by rcases hwR with (h | h) | h <;> exact ball_subset_closedBall h.1⟩, w, hwR, rfl⟩
      simpa only [image_union] using h1
    -- Helper: any unit circle point with `L₁ > 0, L₂ > 0` lies in `closure fR₁`, etc.
    have hrad_tendsto : ∀ w : ℂ, ‖w‖ = 1 →
        Filter.Tendsto (fun k : ℕ => ((1 - 1 / ((k : ℝ) + 2)) : ℝ) • w) Filter.atTop (𝓝 w) ∧
        Filter.Tendsto (fun k : ℕ => f (0, ((1 - 1 / ((k : ℝ) + 2)) : ℝ) • w)) Filter.atTop (𝓝 (f (0, w))) ∧
        (∀ k : ℕ, ((1 - 1 / ((k : ℝ) + 2)) : ℝ) • w ∈ ball (0 : ℂ) 1) := by
      intro w hwn
      have hseq_lim : Filter.Tendsto (fun k : ℕ => ((1 - 1 / ((k : ℝ) + 2)) : ℝ) • w) Filter.atTop (𝓝 w) := by
        have ht0 : Filter.Tendsto (fun k : ℕ => (1 : ℝ) / ((k : ℝ) + 2)) Filter.atTop (𝓝 0) :=
          ((tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).comp (Filter.tendsto_add_atTop_nat 1)).congr fun k => by
            simp only [Function.comp_apply, Nat.cast_add, Nat.cast_one]; ring
        have h1s := (tendsto_const_nhds (x := (1 : ℝ))).sub ht0
        rw [sub_zero] at h1s
        have hsm := h1s.smul (tendsto_const_nhds (x := w))
        rwa [one_smul] at hsm
      have hball_k : ∀ k : ℕ, ((1 - 1 / ((k : ℝ) + 2)) : ℝ) • w ∈ ball (0 : ℂ) 1 := fun k => by
        have hpos : (0 : ℝ) < 1 / ((k : ℝ) + 2) := by positivity
        have hle1 : 1 / ((k : ℝ) + 2) ≤ 1 := by rw [div_le_one (by positivity)]; linarith
        rw [mem_ball_zero_iff, norm_smul, hwn, mul_one, Real.norm_of_nonneg (by linarith only [hle1])]
        linarith only [hpos]
      have hlim_f : Filter.Tendsto (fun k : ℕ => f (0, ((1 - 1 / ((k : ℝ) + 2)) : ℝ) • w)) Filter.atTop (𝓝 (f (0, w))) :=
        (hfc w (mem_closedBall_zero_iff.mpr hwn.le)).tendsto.comp
          (tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ hseq_lim
            (Filter.Eventually.of_forall fun k => ball_subset_closedBall (hball_k k)))
      exact ⟨hseq_lim, hlim_f, hball_k⟩
    have hcl_R1 : ∀ w : ℂ, ‖w‖ = 1 → 0 < L₁ w → 0 < L₂ w → f (0, w) ∈ closure fR₁ := by
      intro w hwn h1 h2
      obtain ⟨hseq_lim, hlim_f, hball_k⟩ := hrad_tendsto w hwn
      have hev1 := (hL₁_cont.continuousAt.tendsto.comp hseq_lim).eventually (isOpen_Ioi.mem_nhds h1)
      have hev2 := (hL₂_cont.continuousAt.tendsto.comp hseq_lim).eventually (isOpen_Ioi.mem_nhds h2)
      exact mem_closure_of_tendsto hlim_f (by filter_upwards [hev1, hev2] with k hk1 hk2; exact ⟨_, ⟨hball_k k, hk1, hk2⟩, rfl⟩)
    have hcl_R2 : ∀ w : ℂ, ‖w‖ = 1 → L₂ w < 0 → f (0, w) ∈ closure fR₂ := by
      intro w hwn h2
      obtain ⟨hseq_lim, hlim_f, hball_k⟩ := hrad_tendsto w hwn
      have hev2 := (hL₂_cont.continuousAt.tendsto.comp hseq_lim).eventually (isOpen_Iio.mem_nhds h2)
      exact mem_closure_of_tendsto hlim_f (by filter_upwards [hev2] with k hk2; exact ⟨_, ⟨hball_k k, hk2⟩, rfl⟩)
    have hcl_R3 : ∀ w : ℂ, ‖w‖ = 1 → L₁ w < 0 → f (0, w) ∈ closure fR₃ := by
      intro w hwn h1
      obtain ⟨hseq_lim, hlim_f, hball_k⟩ := hrad_tendsto w hwn
      have hev1 := (hL₁_cont.continuousAt.tendsto.comp hseq_lim).eventually (isOpen_Iio.mem_nhds h1)
      exact mem_closure_of_tendsto hlim_f (by filter_upwards [hev1] with k hk1; exact ⟨_, ⟨hball_k k, hk1⟩, rfl⟩)
    -- Check bridge points lie in `Fᶜ`:
    have hbr_notF : ∀ w : ℂ, (w = per n x₁ ∨ w = per n x₂) → f (0, w) ∉ F := by
      intro w hw ⟨r, hr⟩
      have hwn : ‖w‖ = 1 := by rcases hw with rfl | rfl <;> exact norm_per _ _
      by_cases hr0 : r.1 = 0
      · rw [show r = 0 from Subtype.ext hr0, hγ0] at hr
        exact (hbr_off w hw).2 (hr ▸ (hFb ▸ Or.inl rfl : s ∈ F ∩ bd S).2)
      · by_cases hr1 : r.1 = 1
        · rw [show r = 1 from Subtype.ext hr1, hγ1] at hr
          exact (hbr_off w hw).2 (hr ▸ (hFb ▸ Or.inr rfl : t ∈ F ∩ bd S).2)
        · by_cases hrh : r.1 = 1 / 2
          · have : γ r = f (0, m₁) := by
              simp only [γ, hrh, le_refl, ↓reduceIte]
              have e1 : (1 - 2 * (1 / 2 : ℝ)) • z₂ + (2 * (1 / 2 : ℝ)) • m₁ = m₁ := by norm_num
              rw [e1]
            exact (hbr_off w hw).1 (hr.symm.trans this)
          · rcases hγ_norm_lt r hr0 hrh hr1 with ⟨hlt, hn1⟩ | ⟨hgt, hn2⟩
            · have hrel := (hf.2.2 _ (hDsk _ (mem_closedBall_zero_iff.mpr hn1.le)) _
                (hDsk w (mem_closedBall_zero_iff.mpr hwn.le))).mp (by simpa only [γ, ite_eq_left hlt.le] using hr)
              have hnorm := congrArg (fun p : ℕ × ℂ => ‖p.2‖) (PRel.eq_of_lt hrel hn1)
              linarith only [hnorm, hn1, hwn]
            · have hrel := (hf.2.2 _ (hDsk _ (mem_closedBall_zero_iff.mpr hn2.le)) _
                (hDsk w (mem_closedBall_zero_iff.mpr hwn.le))).mp (by simpa only [γ, ite_eq_right (not_le.mpr hgt)] using hr)
              have hnorm := congrArg (fun p : ℕ × ℂ => ‖p.2‖) (PRel.eq_of_lt hrel hn2)
              linarith only [hnorm, hn2, hwn]
    let b₁ : S := f (0, per n x₁)
    let b₂ : S := f (0, per n x₂)
    have hb1_notF : b₁ ∈ Fᶜ := hbr_notF _ (Or.inl rfl)
    have hb2_notF : b₂ ∈ Fᶜ := hbr_notF _ (Or.inr rfl)
    have hchain_pre : IsPreconnected ((fR₁ ∪ fR₂ ∪ fR₃) ∪ {b₁, b₂}) := by
      rcases hbr_signs with ⟨h1a, h1b, h1c, h2a, h2b, h2c⟩ | ⟨h1a, h1b, h1c, h2a, h2b⟩
      · have h31 : b₁ ∈ closure fR₃ := hcl_R3 _ (norm_per _ _) h1a
        have h11 : b₁ ∈ closure fR₁ := by dsimp only [b₁]; rw [hbr1]; exact hcl_R1 _ (norm_per _ _) h1b h1c
        have h12 : b₂ ∈ closure fR₁ := hcl_R1 _ (norm_per _ _) h2a h2b
        have h22 : b₂ ∈ closure fR₂ := by dsimp only [b₂]; rw [hbr2]; exact hcl_R2 _ (norm_per _ _) h2c
        have hp3 : IsPreconnected (insert b₁ fR₃) :=
          hfR₃_pre.subset_closure (subset_insert _ _) (insert_subset h31 subset_closure)
        have hp1 : IsPreconnected (insert b₁ (insert b₂ fR₁)) :=
          hfR₁_pre.subset_closure (subset_insert _ _ |>.trans (subset_insert _ _))
            (insert_subset h11 (insert_subset h12 subset_closure))
        have hp2 : IsPreconnected (insert b₂ fR₂) :=
          hfR₂_pre.subset_closure (subset_insert _ _) (insert_subset h22 subset_closure)
        have hp31 : IsPreconnected (insert b₁ fR₃ ∪ insert b₁ (insert b₂ fR₁)) :=
          hp3.union b₁ (mem_insert _ _) (mem_insert _ _) hp1
        have hp312 : IsPreconnected ((insert b₁ fR₃ ∪ insert b₁ (insert b₂ fR₁)) ∪ insert b₂ fR₂) :=
          hp31.union b₂ (Or.inr (mem_insert_of_mem _ (mem_insert _ _))) (mem_insert _ _) hp2
        have heq : (insert b₁ fR₃ ∪ insert b₁ (insert b₂ fR₁)) ∪ insert b₂ fR₂ = (fR₁ ∪ fR₂ ∪ fR₃) ∪ {b₁, b₂} := by
          ext x; constructor
          · rintro (((rfl | h) | (rfl | rfl | h)) | (rfl | h))
            · exact Or.inr (Or.inl rfl)
            · exact Or.inl (Or.inr h)
            · exact Or.inr (Or.inl rfl)
            · exact Or.inr (Or.inr rfl)
            · exact Or.inl (Or.inl (Or.inl h))
            · exact Or.inr (Or.inr rfl)
            · exact Or.inl (Or.inl (Or.inr h))
          · rintro (((h | h) | h) | (rfl | rfl))
            · exact Or.inl (Or.inr (Or.inr (Or.inr h)))
            · exact Or.inr (Or.inr h)
            · exact Or.inl (Or.inl (Or.inr h))
            · exact Or.inl (Or.inl (Or.inl rfl))
            · exact Or.inr (Or.inl rfl)
        rwa [heq] at hp312
      · have h11 : b₁ ∈ closure fR₁ := hcl_R1 _ (norm_per _ _) h1a h1b
        have h21 : b₁ ∈ closure fR₂ := by dsimp only [b₁]; rw [hbr1]; exact hcl_R2 _ (norm_per _ _) h1c
        have h32 : b₂ ∈ closure fR₃ := hcl_R3 _ (norm_per _ _) h2a
        have h22 : b₂ ∈ closure fR₂ := by dsimp only [b₂]; rw [hbr2]; exact hcl_R2 _ (norm_per _ _) h2b
        have hp1 : IsPreconnected (insert b₁ fR₁) :=
          hfR₁_pre.subset_closure (subset_insert _ _) (insert_subset h11 subset_closure)
        have hp2 : IsPreconnected (insert b₁ (insert b₂ fR₂)) :=
          hfR₂_pre.subset_closure (subset_insert _ _ |>.trans (subset_insert _ _))
            (insert_subset h21 (insert_subset h22 subset_closure))
        have hp3 : IsPreconnected (insert b₂ fR₃) :=
          hfR₃_pre.subset_closure (subset_insert _ _) (insert_subset h32 subset_closure)
        have hp12 : IsPreconnected (insert b₁ fR₁ ∪ insert b₁ (insert b₂ fR₂)) :=
          hp1.union b₁ (mem_insert _ _) (mem_insert _ _) hp2
        have hp123 : IsPreconnected ((insert b₁ fR₁ ∪ insert b₁ (insert b₂ fR₂)) ∪ insert b₂ fR₃) :=
          hp12.union b₂ (Or.inr (mem_insert_of_mem _ (mem_insert _ _))) (mem_insert _ _) hp3
        have heq : (insert b₁ fR₁ ∪ insert b₁ (insert b₂ fR₂)) ∪ insert b₂ fR₃ = (fR₁ ∪ fR₂ ∪ fR₃) ∪ {b₁, b₂} := by
          ext x; constructor
          · rintro (((rfl | h) | (rfl | rfl | h)) | (rfl | h))
            · exact Or.inr (Or.inl rfl)
            · exact Or.inl (Or.inl (Or.inl h))
            · exact Or.inr (Or.inl rfl)
            · exact Or.inr (Or.inr rfl)
            · exact Or.inl (Or.inl (Or.inr h))
            · exact Or.inr (Or.inr rfl)
            · exact Or.inl (Or.inr h)
          · rintro (((h | h) | h) | (rfl | rfl))
            · exact Or.inl (Or.inl (Or.inr h))
            · exact Or.inl (Or.inr (Or.inr (Or.inr h)))
            · exact Or.inr (Or.inr h)
            · exact Or.inl (Or.inl (Or.inl rfl))
            · exact Or.inr (Or.inl rfl)
        rwa [heq] at hp123
    have hnonsep : IsPreconnected (Fᶜ : Set S) := by
      refine hchain_pre.subset_closure (union_subset hfR_sub (by rintro _ (rfl | rfl) <;> assumption)) ?_
      have : closure (fR₁ ∪ fR₂ ∪ fR₃) ⊆ closure ((fR₁ ∪ fR₂ ∪ fR₃) ∪ {b₁, b₂}) := closure_mono subset_union_left
      rw [hdense_R] at this; exact (subset_univ _).trans this
    exact ⟨F, s, t, hst, hFl, hFb, hs_eq ▸ hu₂K, ht_eq ▸ hu₁K, hnonsep⟩

/-! ### Section 3: Preserving the cuff-avoidance invariant across a cut -/

/-- An endpoint of an `I`-arc `X` contained in an `O`-arc `C` lies in `closure (C \ X)`. -/
private theorem end_mem_closure_diff_of_line_in_oArc {Y : Type} [TopologicalSpace Y] [T2Space Y]
    {C X : Set Y} {x₀ x₁ : Y} (hC : IsOArc C) (hX : IsLineWithEnds X x₀ x₁) (hXC : X ⊆ C) :
    x₀ ∈ closure (C \ X) := by
  classical
  by_contra hnot
  rw [_root_.mem_closure_iff] at hnot
  push Not at hnot
  obtain ⟨U, hUo, hx₀U, hUdisj⟩ := hnot
  obtain ⟨φC⟩ := hC
  have hx₀X : x₀ ∈ X := hX.left_mem
  obtain ⟨fX, hf0, -⟩ := hX
  let c₀ : Circle := φC.symm ⟨x₀, hXC hx₀X⟩
  have hc₀_eq : (φC c₀).1 = x₀ := congrArg Subtype.val (φC.apply_symm_apply ⟨x₀, hXC hx₀X⟩)
  -- Pull back `U` along `θ ↦ φC (c₀ * Circle.exp θ)`:
  let rot : ℝ → Circle := fun θ => c₀ * Circle.exp θ
  have hrot_cont : Continuous rot := continuous_const.mul Circle.exp.continuous
  have hrot0 : rot 0 = c₀ := by simp [rot]
  have hU_pre : (fun θ => (φC (rot θ)).1) ⁻¹' U ∈ 𝓝 (0 : ℝ) :=
    ((continuous_subtype_val.comp (φC.continuous.comp hrot_cont)).continuousAt).preimage_mem_nhds
      (by show U ∈ 𝓝 (φC (rot 0)).1; rw [hrot0, hc₀_eq]; exact hUo.mem_nhds hx₀U)
  obtain ⟨δ, hδ, hδsub⟩ := Metric.mem_nhds_iff.mp hU_pre
  let δ' := min (δ / 2) (Real.pi / 2)
  have hδ' : 0 < δ' := lt_min (half_pos hδ) (by positivity)
  have hmemX : ∀ θ ∈ Icc (-δ') δ', (φC (rot θ)).1 ∈ X := fun θ hθ => by
    have hU' : (φC (rot θ)).1 ∈ U := hδsub (by
      rw [mem_ball_zero_iff, Real.norm_eq_abs, abs_lt]
      have := min_le_left (δ / 2) (Real.pi / 2)
      exact ⟨by linarith [hθ.1], by linarith [hθ.2]⟩)
    by_contra hnotX
    exact Set.eq_empty_iff_forall_notMem.mp hUdisj _ ⟨hU', (φC (rot θ)).2, hnotX⟩
  let g : ℝ → ℝ := fun θ => if h : (φC (rot θ)).1 ∈ X then (fX.symm ⟨(φC (rot θ)).1, h⟩).1 else 0
  have hg_cont : ContinuousOn g (Icc (-δ') δ') := by
    let g' : Icc (-δ') δ' → ℝ := fun θ => (fX.symm ⟨(φC (rot θ.1)).1, hmemX θ.1 θ.2⟩).1
    have hg'c : Continuous g' :=
      continuous_subtype_val.comp (fX.symm.continuous.comp
        (Continuous.subtype_mk (continuous_subtype_val.comp (φC.continuous.comp (hrot_cont.comp continuous_subtype_val))) _))
    rw [continuousOn_iff_continuous_domRestrict]
    exact hg'c.congr fun θ => by simp only [Set.domRestrict, g, g', dite_eq_left (hmemX θ.1 θ.2)]
  have hg_inj : InjOn g (Icc (-δ') δ') := by
    intro θ₁ hθ₁ θ₂ hθ₂ he
    simp only [g, dite_eq_left (hmemX θ₁ hθ₁), dite_eq_left (hmemX θ₂ hθ₂)] at he
    have h1val : (φC (rot θ₁)).1 = (φC (rot θ₂)).1 :=
      congrArg (Subtype.val : X → Y) (fX.symm.injective (Subtype.ext he))
    have h1 : φC (rot θ₁) = φC (rot θ₂) := Subtype.ext h1val
    have h2 : Circle.exp θ₁ = Circle.exp θ₂ := mul_left_cancel (φC.injective h1)
    have h3 : Complex.exp ((θ₁ - θ₂) * I) = 1 := by
      have hval : Complex.exp (θ₁ * I) = Complex.exp (θ₂ * I) := by
        simpa [Circle.coe_exp] using congrArg Subtype.val h2
      calc Complex.exp ((θ₁ - θ₂) * I) = Complex.exp (θ₁ * I) * (Complex.exp (θ₂ * I))⁻¹ := by
            rw [← Complex.exp_neg, ← Complex.exp_add]; congr 1; ring
        _ = 1 := by rw [hval, mul_inv_cancel₀ (Complex.exp_ne_zero _)]
    rw [Complex.exp_eq_one_iff] at h3
    obtain ⟨k, hk⟩ := h3
    have hre : θ₁ - θ₂ = k * (2 * Real.pi) := by
      have := congrArg Complex.im hk
      simp only [Complex.mul_im, Complex.mul_re, Complex.sub_re, Complex.sub_im,
        Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
        mul_one, mul_zero, add_zero, zero_add, sub_zero, Complex.intCast_re, Complex.intCast_im,
        Complex.re_ofNat, Complex.im_ofNat] at this
      linarith
    have hbd : |θ₁ - θ₂| ≤ Real.pi := by
      rw [abs_le]; have := min_le_right (δ / 2) (Real.pi / 2)
      exact ⟨by linarith [hθ₁.1, hθ₂.2], by linarith [hθ₁.2, hθ₂.1]⟩
    have hk0 : k = 0 := by
      by_contra hkn
      have h1k : (1 : ℝ) ≤ |(k : ℝ)| := by exact_mod_cast Int.one_le_abs hkn
      have habs : |θ₁ - θ₂| = |(k : ℝ)| * (2 * Real.pi) := by
        rw [hre, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi)]
      nlinarith [Real.pi_pos]
    subst hk0; simp at hre; linarith
  have hg0 : g 0 = 0 := by
    have h0m : (0 : ℝ) ∈ Icc (-δ') δ' := ⟨by linarith, by linarith⟩
    simp only [g, dite_eq_left (hmemX 0 h0m)]
    have hval : (⟨(φC (rot 0)).1, hmemX 0 h0m⟩ : X) = fX 0 := Subtype.ext (by simp [hrot0, hc₀_eq, hf0])
    rw [hval, fX.symm_apply_apply]; rfl
  have hg_nonneg : ∀ θ ∈ Icc (-δ') δ', 0 ≤ g θ := fun θ hθ => by
    simp only [g, dite_eq_left (hmemX θ hθ)]; exact (fX.symm _).2.1
  have hgL : 0 < g (-δ') := lt_of_le_of_ne (hg_nonneg (-δ') ⟨le_rfl, by linarith⟩)
    (Ne.symm fun h => by have := hg_inj ⟨le_rfl, by linarith⟩ ⟨by linarith, by linarith⟩ (h.trans hg0.symm); linarith)
  have hgR : 0 < g δ' := lt_of_le_of_ne (hg_nonneg δ' ⟨by linarith, le_rfl⟩)
    (Ne.symm fun h => by have := hg_inj ⟨by linarith, le_rfl⟩ ⟨by linarith, by linarith⟩ (h.trans hg0.symm); linarith)
  let m := min (g (-δ')) (g δ') / 2
  have hm_pos : 0 < m := half_pos (lt_min hgL hgR)
  have hm_L : m ∈ Icc (g 0) (g (-δ')) := ⟨by rw [hg0]; exact hm_pos.le, by dsimp only [m]; linarith [min_le_left (g (-δ')) (g δ')]⟩
  have hm_R : m ∈ Icc (g 0) (g δ') := ⟨by rw [hg0]; exact hm_pos.le, by dsimp only [m]; linarith [min_le_right (g (-δ')) (g δ')]⟩
  obtain ⟨t₁, ht₁, hgt₁⟩ := intermediate_value_Icc' (by linarith : -δ' ≤ 0)
    (hg_cont.mono (Icc_subset_Icc_right (by linarith))) hm_L
  obtain ⟨t₂, ht₂, hgt₂⟩ := intermediate_value_Icc (by linarith : (0 : ℝ) ≤ δ')
    (hg_cont.mono (Icc_subset_Icc_left (by linarith))) hm_R
  have ht12 := hg_inj ⟨ht₁.1, ht₁.2.trans (by linarith)⟩ ⟨(by linarith : -δ' ≤ 0).trans ht₂.1, ht₂.2⟩ (hgt₁.trans hgt₂.symm)
  have ht1_0 : t₁ = 0 := le_antisymm ht₁.2 (ht12 ▸ ht₂.1)
  rw [ht1_0, hg0] at hgt₁; linarith

private theorem isConnected_of_isOArc {Y : Type} [TopologicalSpace Y] {C : Set Y} (hC : IsOArc C) :
    IsConnected C := by
  obtain ⟨φ⟩ := hC
  have h : ConnectedSpace C := φ.surjective.connectedSpace φ.continuous
  exact isConnected_iff_connectedSpace.mpr h

private theorem isCompact_of_isOArc {Y : Type} [TopologicalSpace Y] {C : Set Y} (hC : IsOArc C) :
    IsCompact C := by
  obtain ⟨φ⟩ := hC
  have h : CompactSpace C := φ.surjective.compactSpace φ.continuous
  exact isCompact_iff_compactSpace.mpr h

/-- Cutting a surface `S` along a proper `I`-arc `F` whose endpoints avoid a closed set `K ⊆ bd S`
containing no cuff preserves the cuff-avoidance property for `K' := ψ ⁻¹' (K ∪ F)`. -/
private theorem cuffs_not_subset_after_cut {S Y : Type} [TopologicalSpace S] [TopologicalSpace Y] [T2Space Y]
    (hS : IsSurface S) (hY : IsSurface Y)
    {F : Set S} {s t : S} (_hFb : F ∩ bd S = {s, t}) (hFl : IsLineWithEnds F s t)
    {ψ : Y → S} (hψ : IsCutting ψ F) {X X' : Set Y} (hP : LiftPair ψ F s t X X')
    {K : Set S} (hKcl : IsClosed K) (hKcuff : ∀ C ∈ cuffs S, (C \ K).Nonempty)
    (hsK : s ∉ K) (_htK : t ∉ K) :
    IsClosed (ψ ⁻¹' (K ∪ F)) ∧ ∀ C' ∈ cuffs Y, (C' \ ψ ⁻¹' (K ∪ F)).Nonempty := by
  have : CompactSpace Y := hY.1
  have : T2Space S := hS.2.1
  have hFcl : IsClosed F := hFl.isCompact.isClosed
  refine ⟨(hKcl.union hFcl).preimage hψ.1, fun C' hC' => ?_⟩
  obtain ⟨x0, x1, y0, y1, l1, l2, hXX', hun, -, -, hψx0, hψy0, -, -⟩ := hP
  have hC'oarc : IsOArc C' := (cuff_statement.{0} Y hY).2.2 C' hC'
  have hC'sub : C' ⊆ bd Y := by obtain ⟨z, -, rfl⟩ := hC'; exact connectedComponentIn_subset _ _
  by_cases hdisj : Disjoint C' (ψ ⁻¹' F)
  · -- `C'` avoids `ψ ⁻¹' F`, so `ψ '' C'` is a cuff of `S`!
    have hC'_open_bd : IsOpen (Subtype.val ⁻¹' C' : Set (bd Y)) := by
      have hfin : (cuffs Y).Finite := (cuff_statement.{0} Y hY).2.1
      have hcompl : (Subtype.val ⁻¹' C' : Set (bd Y))ᶜ = Subtype.val ⁻¹' (⋃ D ∈ cuffs Y \ {C'}, D) := by
        ext ⟨y, hy⟩; simp only [mem_compl_iff, mem_preimage, mem_iUnion, mem_sdiff, mem_singleton_iff]
        constructor
        · intro hnot
          refine ⟨connectedComponentIn (bd Y) y, ⟨⟨y, hy, rfl⟩, fun h => hnot (h ▸ mem_connectedComponentIn hy)⟩,
            mem_connectedComponentIn hy⟩
        · rintro ⟨D, ⟨hD, hne⟩, hyD⟩ hyC'
          exact Set.disjoint_left.mp (cuffs_disjoint hD hC' hne) hyD hyC'
      rw [← isClosed_compl_iff, hcompl]
      have hfin' : (cuffs Y \ {C'}).Finite := hfin.subset sdiff_subset
      rw [preimage_iUnion₂]
      exact hfin'.isClosed_biUnion fun D hD =>
        ((cuff_statement.{0} Y hY).2.2 D hD.1).isCompact.isClosed.preimage continuous_subtype_val
    have hC'_conn : IsConnected C' := isConnected_of_isOArc hC'oarc
    have hC'_comp : IsCompact C' := isCompact_of_isOArc hC'oarc
    obtain ⟨φC'⟩ := hC'oarc
    let y₀ : Y := (φC' 1).1
    have hy₀ : y₀ ∈ C' := (φC' 1).2
    have hψy₀_bd : ψ y₀ ∈ bd S :=
      (mem_bd_cut_iff hY hS hψ hFcl (Set.disjoint_left.mp hdisj hy₀)).mp (hC'sub hy₀)
    let C : Set S := connectedComponentIn (bd S) (ψ y₀)
    have hC_mem : C ∈ cuffs S := ⟨ψ y₀, hψy₀_bd, rfl⟩
    have hψC'_sub : ψ '' C' ⊆ C := by
      have hpre : IsPreconnected (ψ '' C') := hC'_conn.2.image ψ hψ.1.continuousOn
      exact hpre.subset_connectedComponentIn ⟨y₀, hy₀, rfl⟩ (by
        rintro _ ⟨y, hy, rfl⟩
        exact (mem_bd_cut_iff hY hS hψ hFcl (Set.disjoint_left.mp hdisj hy)).mp (hC'sub hy))
    have hψC'_eq : ψ '' C' = C := by
      have hcl : IsClosed (Subtype.val ⁻¹' (ψ '' C') : Set C) :=
        (hC'_comp.image hψ.1).isClosed.preimage continuous_subtype_val
      have hop : IsOpen (Subtype.val ⁻¹' (ψ '' C') : Set C) := by
        let eF := cutComplHomeo hψ hFcl
        rw [isOpen_induced_iff] at hC'_open_bd
        obtain ⟨V, hVo, hVeq⟩ := hC'_open_bd
        have hV_sub : V ∩ bd Y = C' := by
          ext y; constructor
          · rintro ⟨hyV, hybd⟩; exact show (⟨y, hybd⟩ : bd Y) ∈ Subtype.val ⁻¹' C' by rw [← hVeq]; exact hyV
          · intro hy; exact ⟨show (⟨y, hC'sub hy⟩ : bd Y) ∈ Subtype.val ⁻¹' V by rw [hVeq]; exact hy, hC'sub hy⟩
        -- Image of `V ∩ ψ ⁻¹' Fᶜ` under `eF` is open in `Fᶜ`, hence open in `S`!
        let W : Set S := Subtype.val '' (eF '' (Subtype.val ⁻¹' V : Set (ψ ⁻¹' Fᶜ : Set Y)))
        have hWo : IsOpen W := by
          have h1 : IsOpen (eF '' (Subtype.val ⁻¹' V : Set (ψ ⁻¹' Fᶜ : Set Y))) :=
            eF.isOpenMap _ (hVo.preimage continuous_subtype_val)
          exact hFcl.isOpen_compl.isOpenMap_subtype_val _ h1
        have hW_inter : Subtype.val ⁻¹' W = (Subtype.val ⁻¹' (ψ '' C') : Set C) := by
          ext ⟨x, hxC⟩; simp only [mem_preimage]
          constructor
          · rintro ⟨⟨z, hnotF⟩, ⟨⟨y, hyF⟩, hyV, hye⟩, hzx⟩
            have hψy : ψ y = x := (congrArg Subtype.val hye).trans hzx
            have hybd : y ∈ bd Y := (mem_bd_cut_iff hY hS hψ hFcl hyF).mpr (hψy.symm ▸ connectedComponentIn_subset _ _ hxC)
            exact ⟨y, hV_sub ▸ ⟨hyV, hybd⟩, hψy⟩
          · rintro ⟨y, hyC', rfl⟩
            have hyF : ψ y ∉ F := Set.disjoint_left.mp hdisj hyC'
            have hyV : y ∈ V := (hV_sub ▸ hyC').1
            exact ⟨⟨ψ y, hyF⟩, ⟨⟨y, hyF⟩, hyV, rfl⟩, rfl⟩
        exact hW_inter ▸ hWo.preimage continuous_subtype_val
      have hC_conn : IsConnected C := isConnected_of_isOArc ((cuff_statement.{0} S hS).2.2 C hC_mem)
      have : ConnectedSpace C := isConnected_iff_connectedSpace.mp hC_conn
      have hne : (Subtype.val ⁻¹' (ψ '' C') : Set C).Nonempty := ⟨⟨ψ y₀, hψC'_sub ⟨y₀, hy₀, rfl⟩⟩, y₀, hy₀, rfl⟩
      have huniv : (Subtype.val ⁻¹' (ψ '' C') : Set C) = univ :=
        IsClopen.eq_univ ⟨hcl, hop⟩ hne
      ext x; constructor
      · exact fun hx => hψC'_sub hx
      · intro hx; exact show (⟨x, hx⟩ : C) ∈ Subtype.val ⁻¹' (ψ '' C') by rw [huniv]; trivial
    obtain ⟨x, hxC, hxK⟩ := hKcuff C hC_mem
    obtain ⟨y, hyC', rfl⟩ := hψC'_eq.symm ▸ hxC
    exact ⟨y, hyC', fun h => by rcases h with hK | hF; exact hxK hK; exact Set.disjoint_left.mp hdisj hyC' hF⟩
  · -- `C'` meets `ψ ⁻¹' F = X ∪ X'`, so WLOG `X ⊆ C'` or `X' ⊆ C'`. Use `end_mem_closure_diff_of_line_in_oArc`!
    rw [Set.not_disjoint_iff] at hdisj
    obtain ⟨z, hzC', hzF⟩ := hdisj
    rw [← hun] at hzF
    rcases hzF with hzX | hzX'
    · have hXC' : X ⊆ C' := by
        obtain ⟨w, -, hwe⟩ := hC'
        have hpre : IsPreconnected X := by
          obtain ⟨φ, -, -⟩ := l1
          have := (isPreconnected_univ (α := unitInterval)).image (fun r => (φ r).1)
            (continuous_subtype_val.comp φ.continuous).continuousOn
          have him : (fun r => (φ r).1) '' (univ : Set unitInterval) = X := by
            ext p; constructor
            · rintro ⟨r, -, rfl⟩; exact (φ r).2
            · intro hp; exact ⟨φ.symm ⟨p, hp⟩, mem_univ _, congrArg Subtype.val (φ.apply_symm_apply ⟨p, hp⟩)⟩
          rwa [him] at this
        have hXbd : X ⊆ bd Y := fun p hp => hψ.2.2.2.2 (hun ▸ Or.inl hp)
        have h1 := hpre.subset_connectedComponentIn hzX hXbd
        rw [← hwe] at hzC' ⊢
        exact (connectedComponentIn_eq hzC').symm ▸ h1
      have hx0_cl : x0 ∈ closure (C' \ X) := end_mem_closure_diff_of_line_in_oArc hC'oarc l1 hXC'
      have hUo : IsOpen (ψ ⁻¹' Kᶜ \ X') := (hKcl.isOpen_compl.preimage hψ.1).sdiff l2.isCompact.isClosed
      have hx0U : x0 ∈ ψ ⁻¹' Kᶜ \ X' := ⟨by show ψ x0 ∉ K; rw [hψx0]; exact hsK, Set.disjoint_left.mp hXX' l1.left_mem⟩
      obtain ⟨y, ⟨hyK, hyX'⟩, hyC', hyX⟩ := _root_.mem_closure_iff.mp hx0_cl _ hUo hx0U
      refine ⟨y, hyC', fun h => ?_⟩
      rcases h with hK | hF
      · exact hyK hK
      · have hF' : y ∈ ψ ⁻¹' F := hF
        rw [← hun] at hF'; rcases hF' with hX | hX'
        · exact hyX hX
        · exact hyX' hX'
    · have hX'C' : X' ⊆ C' := by
        obtain ⟨w, -, hwe⟩ := hC'
        have hpre : IsPreconnected X' := by
          obtain ⟨φ, -, -⟩ := l2
          have := (isPreconnected_univ (α := unitInterval)).image (fun r => (φ r).1)
            (continuous_subtype_val.comp φ.continuous).continuousOn
          have him : (fun r => (φ r).1) '' (univ : Set unitInterval) = X' := by
            ext p; constructor
            · rintro ⟨r, -, rfl⟩; exact (φ r).2
            · intro hp; exact ⟨φ.symm ⟨p, hp⟩, mem_univ _, congrArg Subtype.val (φ.apply_symm_apply ⟨p, hp⟩)⟩
          rwa [him] at this
        have hX'bd : X' ⊆ bd Y := fun p hp => hψ.2.2.2.2 (hun ▸ Or.inr hp)
        have h1 := hpre.subset_connectedComponentIn hzX' hX'bd
        rw [← hwe] at hzC' ⊢
        exact (connectedComponentIn_eq hzC').symm ▸ h1
      have hy0_cl : y0 ∈ closure (C' \ X') := end_mem_closure_diff_of_line_in_oArc hC'oarc l2 hX'C'
      have hUo : IsOpen (ψ ⁻¹' Kᶜ \ X) := (hKcl.isOpen_compl.preimage hψ.1).sdiff l1.isCompact.isClosed
      have hy0U : y0 ∈ ψ ⁻¹' Kᶜ \ X := ⟨by show ψ y0 ∉ K; rw [hψy0]; exact hsK, Set.disjoint_right.mp hXX' l2.left_mem⟩
      obtain ⟨y, ⟨hyK, hyX⟩, hyC', hyX'⟩ := _root_.mem_closure_iff.mp hy0_cl _ hUo hy0U
      refine ⟨y, hyC', fun h => ?_⟩
      rcases h with hK | hF
      · exact hyK hK
      · have hF' : y ∈ ψ ⁻¹' F := hF
        rw [← hun] at hF'; rcases hF' with hX | hX'
        · exact hyX hX
        · exact hyX' hX'

/-! ### Section 4: Extending a matching to a disc-cutting non-separating matching (LPPS22 A.4 & A.5) -/

/-- Removing any subset of `bd Y` from an open preconnected subset `O` of a surface `Y` leaves a
preconnected set. -/
private theorem isPreconnected_open_sdiff_bd {Y : Type} [TopologicalSpace Y]
    (hY : IsSurface Y) {O B : Set Y} (hOo : IsOpen O) (hOpre : IsPreconnected O) (hB : B ⊆ bd Y) :
    IsPreconnected (O \ B) := by
  have hdense_int : closure ((bd Y)ᶜ : Set Y) = univ := by
    ext y; simp only [mem_univ, iff_true, _root_.mem_closure_iff]
    intro U hUo hyU
    obtain ⟨c, hyU'⟩ := exists_surfChart (hY.2.2 y)
    have hO_nhd : c.k ⁻¹' (c.U ∩ U) ∈ 𝓝[c.O ∩ halfPlane] (c.j y) :=
      (c.hk (c.j y) (c.hm hyU')).preimage_mem_nhdsWithin
        ((c.hU.inter hUo).mem_nhds ⟨by rw [c.hl hyU']; exact hyU', by rw [c.hl hyU']; exact hyU⟩)
    obtain ⟨r, hr, hrsub⟩ := Metric.mem_nhdsWithin_iff.mp hO_nhd
    obtain ⟨r', hr', hr'O⟩ := Metric.isOpen_iff.mp c.hO (c.j y) (c.hm hyU').1
    let ε := min (r / 2) (r' / 2)
    have hε : 0 < ε := lt_min (half_pos hr) (half_pos hr')
    let w : ℂ := c.j y + (ε : ℂ)
    have hw_re : 0 < w.re := by
      have hre0 : 0 ≤ (c.j y).re := (c.hm hyU').2
      simp only [w, Complex.add_re, Complex.ofReal_re]; linarith
    have hw_O : w ∈ c.O := hr'O (by
      rw [mem_ball, dist_eq_norm, show w - c.j y = (ε : ℂ) by simp [w], Complex.norm_real, Real.norm_of_nonneg hε.le]
      exact lt_of_le_of_lt (min_le_right _ _) (half_lt_self hr'))
    have hw_ball : w ∈ ball (c.j y) r := by
      rw [mem_ball, dist_eq_norm, show w - c.j y = (ε : ℂ) by simp [w], Complex.norm_real, Real.norm_of_nonneg hε.le]
      exact lt_of_le_of_lt (min_le_left _ _) (half_lt_self hr)
    have hw_in : c.k w ∈ c.U ∩ U := hrsub ⟨hw_ball, hw_O, hw_re.le⟩
    refine ⟨c.k w, hw_in.2, fun hbd => ?_⟩
    have hre0 := (c.mem_bd_iff hw_in.1).mp hbd
    rw [c.hr ⟨hw_O, hw_re.le⟩] at hre0; linarith
  intro U V hUo hVo hcov hU hV
  by_contra hnot
  have hdisjUV : ∀ z ∈ O \ B, ¬ (z ∈ U ∧ z ∈ V) := fun z hz huv => hnot ⟨z, hz, huv⟩
  let U₁ : Set Y := {y | ∃ W, IsOpen W ∧ y ∈ W ∧ W ∩ (O \ B) ⊆ U}
  let V₁ : Set Y := {y | ∃ W, IsOpen W ∧ y ∈ W ∧ W ∩ (O \ B) ⊆ V}
  have hU₁o : IsOpen U₁ := isOpen_iff_forall_mem_open.mpr fun y ⟨W, hWo, hyW, hWU⟩ =>
    ⟨W, fun z hz => ⟨W, hWo, hz, hWU⟩, hWo, hyW⟩
  have hV₁o : IsOpen V₁ := isOpen_iff_forall_mem_open.mpr fun y ⟨W, hWo, hyW, hWV⟩ =>
    ⟨W, fun z hz => ⟨W, hWo, hz, hWV⟩, hWo, hyW⟩
  have hO_cov : O ⊆ U₁ ∪ V₁ := by
    intro y hyO
    by_cases hyB : y ∈ B
    · obtain ⟨c, hyU⟩ := exists_surfChart (hY.2.2 y)
      have hO_nhd : c.k ⁻¹' (c.U ∩ O) ∈ 𝓝[c.O ∩ halfPlane] (c.j y) :=
        (c.hk (c.j y) (c.hm hyU)).preimage_mem_nhdsWithin
          ((c.hU.inter hOo).mem_nhds ⟨by rw [c.hl hyU]; exact hyU, by rw [c.hl hyU]; exact hyO⟩)
      obtain ⟨r₁, hr₁, hr₁sub⟩ := Metric.mem_nhdsWithin_iff.mp hO_nhd
      obtain ⟨r₂, hr₂, hr₂O⟩ := Metric.isOpen_iff.mp c.hO (c.j y) (c.hm hyU).1
      let r := min r₁ r₂
      have hr : 0 < r := lt_min hr₁ hr₂
      let W : Set Y := c.U ∩ c.j ⁻¹' ball (c.j y) r
      have hWo : IsOpen W := c.hj.isOpen_inter_preimage c.hU isOpen_ball
      have hyW : y ∈ W := ⟨hyU, mem_ball_self hr⟩
      have hWO : W ⊆ O := fun z ⟨hzU, hzB⟩ => by
        have h1 : c.k (c.j z) ∈ c.U ∩ O := hr₁sub ⟨ball_subset_ball (min_le_left _ _) hzB, c.hm hzU⟩
        rw [c.hl hzU] at h1; exact h1.2
      have hW_int_pre : IsPreconnected (W ∩ (bd Y)ᶜ) := by
        have heq : W ∩ (bd Y)ᶜ = c.k '' (ball (c.j y) r ∩ {w : ℂ | 0 < w.re}) := by
          ext z; constructor
          · rintro ⟨⟨hzU, hzB⟩, hzI⟩
            exact ⟨c.j z, ⟨hzB, lt_of_le_of_ne (c.hm hzU).2 (Ne.symm fun h0 => hzI ((c.mem_bd_iff hzU).mpr h0))⟩, c.hl hzU⟩
          · rintro ⟨w, ⟨hwB, hwre⟩, rfl⟩
            have hwO : w ∈ c.O ∩ halfPlane := ⟨hr₂O (ball_subset_ball (min_le_right _ _) hwB), show 0 ≤ w.re from le_of_lt hwre⟩
            refine ⟨⟨c.hk' hwO, by show c.j (c.k w) ∈ ball (c.j y) r; rwa [c.hr hwO]⟩, fun hbd => ?_⟩
            have := (c.mem_bd_iff (c.hk' hwO)).mp hbd; rw [c.hr hwO] at this; linarith [show 0 < w.re from hwre]
        rw [heq]
        have hconv : Convex ℝ {w : ℂ | 0 < w.re} := by
          intro x hx z hz u v hu hv huv
          show 0 < (u • x + v • z).re
          simp only [Complex.add_re, Complex.real_smul, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
          rcases eq_or_lt_of_le hu with rfl | hu'
          · rw [show v = 1 by linarith]; simp; exact hz
          · nlinarith [show 0 < x.re from hx, show 0 < z.re from hz]
        exact ((convex_ball (c.j y) r).inter hconv).isPreconnected.image c.k
          (c.hk.mono fun w hw => ⟨hr₂O (ball_subset_ball (min_le_right _ _) hw.1), show 0 ≤ w.re from le_of_lt hw.2⟩)
      have hW_int_sub : W ∩ (bd Y)ᶜ ⊆ O \ B := fun z ⟨hzW, hzI⟩ => ⟨hWO hzW, fun h => hzI (hB h)⟩
      by_cases hmU : ((W ∩ (bd Y)ᶜ) ∩ U).Nonempty
      · left; refine ⟨W, hWo, hyW, fun z ⟨hzW, hzOB⟩ => ?_⟩
        refine (hcov hzOB).resolve_right fun hzV => ?_
        obtain ⟨z', ⟨hz'W, hz'V⟩, hz'I⟩ := _root_.mem_closure_iff.mp (hdense_int ▸ mem_univ z)
          (W ∩ V) (hWo.inter hVo) ⟨hzW, hzV⟩
        obtain ⟨w, hw, hwU, hwV⟩ := hW_int_pre U V hUo hVo (hW_int_sub.trans hcov) hmU ⟨z', ⟨hz'W, hz'I⟩, hz'V⟩
        exact hdisjUV w (hW_int_sub hw) ⟨hwU, hwV⟩
      · right; refine ⟨W, hWo, hyW, fun z ⟨hzW, hzOB⟩ => ?_⟩
        refine (hcov hzOB).resolve_left fun hzU => ?_
        obtain ⟨z', ⟨hz'W, hz'U⟩, hz'I⟩ := _root_.mem_closure_iff.mp (hdense_int ▸ mem_univ z)
          (W ∩ U) (hWo.inter hUo) ⟨hzW, hzU⟩
        exact hmU ⟨z', ⟨hz'W, hz'I⟩, hz'U⟩
    · rcases hcov ⟨hyO, hyB⟩ with hyU | hyV
      · exact Or.inl ⟨U, hUo, hyU, fun _ h => h.1⟩
      · exact Or.inr ⟨V, hVo, hyV, fun _ h => h.1⟩
  obtain ⟨y, hyO, ⟨W₁, hW₁o, hyW₁, hW₁U⟩, ⟨W₂, hW₂o, hyW₂, hW₂V⟩⟩ := hOpre U₁ V₁ hU₁o hV₁o hO_cov
    (by obtain ⟨y, hyOB, hyU⟩ := hU; exact ⟨y, hyOB.1, U, hUo, hyU, fun _ h => h.1⟩)
    (by obtain ⟨y, hyOB, hyV⟩ := hV; exact ⟨y, hyOB.1, V, hVo, hyV, fun _ h => h.1⟩)
  obtain ⟨z, ⟨⟨hzW₁, hzW₂⟩, hzO⟩, hzI⟩ := _root_.mem_closure_iff.mp (hdense_int ▸ mem_univ y)
    (W₁ ∩ W₂ ∩ O) ((hW₁o.inter hW₂o).inter hOo) ⟨⟨hyW₁, hyW₂⟩, hyO⟩
  have hzOB : z ∈ O \ B := ⟨hzO, fun h => hzI (hB h)⟩
  exact hdisjUV z hzOB ⟨hW₁U ⟨hzW₁, hzOB⟩, hW₂V ⟨hzW₂, hzOB⟩⟩

/-- Projecting a proper `I`-arc `Q' ⊆ Y` disjoint from `ψ ⁻¹' F` down through `ψ : Y → S`. -/
private theorem push_disjoint_iArc {S Y : Type} [TopologicalSpace S] [TopologicalSpace Y] [T2Space Y]
    (hS : IsSurface S) (hY : IsSurface Y) {ψ : Y → S} {F : Set S}
    (hψ : IsCutting ψ F) (hFcl : IsClosed F)
    {Q' : Set Y} {u' v' : Y} (huv' : u' ≠ v') (hQl' : IsLineWithEnds Q' u' v') (hQb' : Q' ∩ bd Y = {u', v'})
    (hdisj : Disjoint Q' (ψ ⁻¹' F)) :
    ψ u' ≠ ψ v' ∧ IsLineWithEnds (ψ '' Q') (ψ u') (ψ v') ∧ (ψ '' Q') ∩ bd S = {ψ u', ψ v'} ∧
      Disjoint (ψ '' Q') F := by
  have : CompactSpace Y := hY.1
  have : T2Space S := hS.2.1
  have hQ'off : ∀ y ∈ Q', ψ y ∉ F := fun y hy => Set.disjoint_left.mp hdisj hy
  have hinj : InjOn ψ Q' := fun y₁ hy₁ y₂ hy₂ he => hψ.2.2.1 (hQ'off y₁ hy₁) (hQ'off y₂ hy₂) he
  have huv : ψ u' ≠ ψ v' := fun h => huv' (hinj hQl'.left_mem hQl'.right_mem h)
  have hQl : IsLineWithEnds (ψ '' Q') (ψ u') (ψ v') := by
    obtain ⟨φ, hφ0, hφ1⟩ := hQl'
    let g : unitInterval → ψ '' Q' := fun r => ⟨ψ (φ r).1, (φ r).1, (φ r).2, rfl⟩
    have hgc : Continuous g := Continuous.subtype_mk (hψ.1.comp (continuous_subtype_val.comp φ.continuous)) _
    have hgi : Function.Injective g := fun r₁ r₂ he =>
      φ.injective (Subtype.ext (hinj (φ r₁).2 (φ r₂).2 (congrArg Subtype.val he)))
    have hgs : Function.Surjective g := fun ⟨_, y, hy, rfl⟩ =>
      ⟨φ.symm ⟨y, hy⟩, Subtype.ext (congrArg ψ (congrArg Subtype.val (φ.apply_symm_apply ⟨y, hy⟩)))⟩
    exact ⟨hgc.homeoOfEquivCompactToT2 (f := Equiv.ofBijective g ⟨hgi, hgs⟩),
      by show ψ (φ 0).1 = ψ u'; rw [hφ0], by show ψ (φ 1).1 = ψ v'; rw [hφ1]⟩
  have hQb : (ψ '' Q') ∩ bd S = {ψ u', ψ v'} := by
    ext x; constructor
    · rintro ⟨⟨y, hy, rfl⟩, hxbd⟩
      have hybd : y ∈ bd Y := (mem_bd_cut_iff hY hS hψ hFcl (hQ'off y hy)).mpr hxbd
      have hm : y ∈ Q' ∩ bd Y := ⟨hy, hybd⟩
      rw [hQb'] at hm
      rcases hm with rfl | h
      · exact Or.inl rfl
      · exact Or.inr (congrArg ψ (mem_singleton_iff.mp h))
    · rintro (rfl | rfl)
      · exact ⟨⟨u', hQl'.left_mem, rfl⟩, (mem_bd_cut_iff hY hS hψ hFcl (hQ'off u' hQl'.left_mem)).mp (hQb'.symm ▸ Or.inl rfl : u' ∈ Q' ∩ bd Y).2⟩
      · exact ⟨⟨v', hQl'.right_mem, rfl⟩, (mem_bd_cut_iff hY hS hψ hFcl (hQ'off v' hQl'.right_mem)).mp (hQb'.symm ▸ Or.inr rfl : v' ∈ Q' ∩ bd Y).2⟩
  have hdisjF : Disjoint (ψ '' Q') F := Set.disjoint_left.mpr fun _ ⟨y, hy, hye⟩ => hye ▸ hQ'off y hy
  exact ⟨huv, hQl, hQb, hdisjF⟩

/-- **LPPS22 Lemmas A.4 and A.5 unified**:
On any connected surface `S ≃ₜ SurfaceModel a b c` with `1 ≤ c`, given a closed set `K ⊆ bd S`
containing no cuff and a matching `G : Fin n → Set S` whose endpoints avoid `K`, there exists a
subset `I₀ ⊆ Fin n` and a family `N₁ : Fin r₁ → Set S` of new proper `I`-arcs (disjoint from `G`
and with endpoints outside `K`) such that `I₀.card + r₁ = 2 * a + b + c - 1` and together
`N := (G on I₀) ⊕ N₁` is a non-separating matching of size `2 * a + b + c - 1`. -/
theorem exists_disc_cutting_matching :
    ∀ M : ℕ, ∀ {S : Type} [TopologicalSpace S] [ConnectedSpace S]
      (_hS : IsSurface S) {a b c n : ℕ}
      (_eS : S ≃ₜ SurfaceModel a b c) (_hc : 1 ≤ c)
      (_hM : n + (2 * a + b + c - 1) ≤ M)
      {K : Set S} (_hKcl : IsClosed K) (_hKcuff : ∀ C ∈ cuffs S, (C \ K).Nonempty)
      {G : Fin n → Set S}
      (_hG : ∀ j, ∃ s t, s ≠ t ∧ IsLineWithEnds (G j) s t ∧ G j ∩ bd S = {s, t})
      (_hGdisj : Pairwise fun j₁ j₂ => Disjoint (G j₁) (G j₂))
      (_hGK : ∀ j, Disjoint (G j ∩ bd S) K),
      ∃ (I₀ : Finset (Fin n)) (r₁ : ℕ) (N₁ : Fin r₁ → Set S),
        I₀.card + r₁ = 2 * a + b + c - 1 ∧
        (∀ k, ∃ s t, s ≠ t ∧ IsLineWithEnds (N₁ k) s t ∧ N₁ k ∩ bd S = {s, t} ∧ s ∉ K ∧ t ∉ K) ∧
        (Pairwise fun k₁ k₂ => Disjoint (N₁ k₁) (N₁ k₂)) ∧
        (∀ k j, Disjoint (N₁ k) (G j)) ∧
        IsPreconnected (((⋃ j ∈ I₀, G j) ∪ ⋃ k : Fin r₁, N₁ k)ᶜ : Set S) := by
  intro M
  induction M using Nat.strong_induction_on with
  | h M ih =>
    intro S _ _ hS a b c n eS hc hM K hKcl hKcuff G hG hGdisj hGK
    classical
    have ht2S : T2Space S := hS.2.1
    by_cases hn0 : n = 0
    · -- Base `n = 0`: `G` is empty; induct on `d := 2 * a + b + c - 1`
      subst hn0
      by_cases hd0 : 2 * a + b + c - 1 = 0
      · refine ⟨∅, 0, fun k => Fin.elim0 k, by simp [hd0], fun k => Fin.elim0 k,
          fun k => Fin.elim0 k, fun k => Fin.elim0 k, ?_⟩
        simp only [Finset.notMem_empty, iUnion_of_empty, union_empty, compl_empty]
        exact isPreconnected_univ
      · have hnd : 2 ≤ 2 * a + b + c := by omega
        obtain ⟨F, s, t, hst, hFl, hFb, hsK, htK, hFnonsep⟩ :=
          exists_nonsep_iArc_avoiding hS eS hc hnd hKcl hKcuff
        have hFcl : IsClosed F := hFl.isCompact.isClosed
        obtain ⟨Y, tY, t2Y, ψ, hY, hψ, X, X', hP⟩ := exists_cut_arc hS hst hFb hFl
        have : CompactSpace Y := hY.1
        have : Nonempty Y := by obtain ⟨x⟩ := ‹ConnectedSpace S›.toNonempty; obtain ⟨y, -⟩ := hψ.2.1 x; exact ⟨y⟩
        have : ConnectedSpace Y := (connectedSpace_cut_iff hY hS hψ hFcl).mpr hFnonsep
        obtain ⟨a', b', c', ⟨eY⟩, hc', heuler⟩ := cut_iArc_euler_connected hS hY eS hst hFb hFl hψ hP
        obtain ⟨hK'cl, hK'cuff⟩ := cuffs_not_subset_after_cut hS hY hFb hFl hψ hP hKcl hKcuff hsK htK
        obtain ⟨I₀', r₁', N₁', hcard', hN₁', hN₁'disj, _, hnonsep'⟩ :=
          ih (0 + (2 * a' + b' + c' - 1)) (by omega) hY eY hc' le_rfl hK'cl hK'cuff
            (G := fun j : Fin 0 => Fin.elim0 j) (fun j => Fin.elim0 j) (fun j => Fin.elim0 j) (fun j => Fin.elim0 j)
        have hN₁'_disjF : ∀ k : Fin r₁', Disjoint (N₁' k) (ψ ⁻¹' F) := fun k => by
          obtain ⟨s', t', -, -, hbd', hs', ht'⟩ := hN₁' k
          rw [Set.disjoint_left]; intro y hyQ hyF
          have hybd : y ∈ bd Y := hψ.2.2.2.2 hyF
          have hm : y ∈ N₁' k ∩ bd Y := ⟨hyQ, hybd⟩
          rw [hbd'] at hm
          rcases hm with rfl | h
          · exact hs' (Or.inr hyF)
          · exact ht' (mem_singleton_iff.mp h ▸ Or.inr hyF)
        let N₁ : Fin (r₁' + 1) → Set S := Fin.cons F (fun k => ψ '' N₁' k)
        refine ⟨∅, r₁' + 1, N₁, by rw [Finset.eq_empty_of_isEmpty I₀'] at hcard'; simp only [Finset.card_empty, zero_add] at hcard' ⊢; omega, ?_, ?_, fun _ j => Fin.elim0 j, ?_⟩
        · intro k
          refine Fin.cases ?_ (fun k' => ?_) k
          · exact ⟨s, t, hst, hFl, hFb, hsK, htK⟩
          · obtain ⟨s', t', hst', hL', hbd', hs', ht'⟩ := hN₁' k'
            obtain ⟨huv, hL, hbd, -⟩ := push_disjoint_iArc hS hY hψ hFcl hst' hL' hbd' (hN₁'_disjF k')
            exact ⟨ψ s', ψ t', huv, hL, hbd, fun h => hs' (Or.inl h), fun h => ht' (Or.inl h)⟩
        · intro k₁ k₂ hne
          refine Fin.cases (fun k₂ => Fin.cases (fun h => absurd rfl h) (fun k₂' _ => ?_) k₂)
            (fun k₁' k₂ => Fin.cases (fun _ => ?_) (fun k₂' hne' => ?_) k₂) k₁ k₂ hne
          · obtain ⟨s', t', hst', hL', hbd', -, -⟩ := hN₁' k₂'
            exact (push_disjoint_iArc hS hY hψ hFcl hst' hL' hbd' (hN₁'_disjF k₂')).2.2.2.symm
          · obtain ⟨s', t', hst', hL', hbd', -, -⟩ := hN₁' k₁'
            exact (push_disjoint_iArc hS hY hψ hFcl hst' hL' hbd' (hN₁'_disjF k₁')).2.2.2
          · rw [Set.disjoint_left]; rintro _ ⟨y₁, hy₁, rfl⟩ ⟨y₂, hy₂, he⟩
            have hy1F : ψ y₁ ∉ F := Set.disjoint_left.mp (hN₁'_disjF k₁') hy₁
            have hy2F : ψ y₂ ∉ F := Set.disjoint_left.mp (hN₁'_disjF k₂') hy₂
            have hy12 : y₁ = y₂ := hψ.2.2.1 hy1F hy2F he.symm
            exact Set.disjoint_left.mp (hN₁'disj (fun h => hne' (congrArg Fin.succ h))) hy₁ (hy12 ▸ hy₂)
        · -- Preconnectedness of `(F ∪ ⋃ k', ψ '' N₁' k')ᶜ`:
          have hcompl_eq : ((⋃ j ∈ (∅ : Finset (Fin 0)), G j) ∪ ⋃ k : Fin (r₁' + 1), N₁ k)ᶜ =
              ψ '' ((ψ ⁻¹' Fᶜ) ∩ (⋃ k' : Fin r₁', N₁' k')ᶜ) := by
            ext x; constructor
            · intro hx
              have hxF : x ∉ F := fun h => hx (Or.inr (mem_iUnion.mpr ⟨0, h⟩))
              obtain ⟨y, rfl⟩ := hψ.2.1 x
              refine ⟨y, ⟨hxF, fun h => ?_⟩, rfl⟩
              obtain ⟨k', hyk'⟩ := mem_iUnion.mp h
              exact hx (Or.inr (mem_iUnion.mpr ⟨k'.succ, ⟨y, hyk', rfl⟩⟩))
            · rintro ⟨y, ⟨hyF, hyN'⟩, rfl⟩ hx
              rcases hx with hxG | hxN
              · simp at hxG
              · obtain ⟨k, hxk⟩ := mem_iUnion.mp hxN
                refine Fin.cases (fun h => hyF h) (fun k' h => ?_) k hxk
                obtain ⟨y', hy'k', hye⟩ := h
                have hy'F : ψ y' ∉ F := Set.disjoint_left.mp (hN₁'_disjF k') hy'k'
                exact hyN' (mem_iUnion.mpr ⟨k', hψ.2.2.1 hy'F hyF hye ▸ hy'k'⟩)
          rw [hcompl_eq]
          have hO_pre : IsPreconnected ((⋃ k' : Fin r₁', N₁' k')ᶜ : Set Y) := by
            simpa [Finset.eq_empty_of_isEmpty I₀'] using hnonsep'
          have hO_open : IsOpen ((⋃ k' : Fin r₁', N₁' k')ᶜ : Set Y) :=
            (isClosed_iUnion_of_finite fun k' => by obtain ⟨_, _, _, hl, _, _, _⟩ := hN₁' k'; exact hl.isCompact.isClosed).isOpen_compl
          have hpre_sub : IsPreconnected ((ψ ⁻¹' Fᶜ) ∩ (⋃ k' : Fin r₁', N₁' k')ᶜ) := by
            have heq : (ψ ⁻¹' Fᶜ) ∩ (⋃ k' : Fin r₁', N₁' k')ᶜ = (⋃ k' : Fin r₁', N₁' k')ᶜ \ ψ ⁻¹' F := by
              ext y; simp [and_comm]
            rw [heq]
            exact isPreconnected_open_sdiff_bd hY hO_open hO_pre hψ.2.2.2.2
          exact hpre_sub.image ψ hψ.1.continuousOn
    · -- Inductive case `n ≥ 1`: check whether some `G i` is non-separating, or all `G i` separate!
      have hn_pos : 0 < n := Nat.pos_of_ne_zero hn0
      by_cases hex_ns : ∃ i₀ : Fin n, IsPreconnected ((G i₀)ᶜ : Set S)
      · -- Case A: `G i₀` is non-separating! Cut along `G i₀`, apply IH with `n - 1` and `d - 1`!
        obtain ⟨i₀, hns₀⟩ := hex_ns
        obtain ⟨s₀, t₀, hst₀, hGl₀, hGb₀⟩ := hG i₀
        have hGcl₀ : IsClosed (G i₀) := hGl₀.isCompact.isClosed
        have hs₀K : s₀ ∉ K := Set.disjoint_left.mp (hGK i₀) (hGb₀ ▸ Or.inl rfl)
        have ht₀K : t₀ ∉ K := Set.disjoint_left.mp (hGK i₀) (hGb₀ ▸ Or.inr rfl)
        obtain ⟨Y, tY, t2Y, ψ, hY, hψ, X, X', hP⟩ := exists_cut_arc hS hst₀ hGb₀ hGl₀
        have : CompactSpace Y := hY.1
        have : Nonempty Y := by obtain ⟨x⟩ := ‹ConnectedSpace S›.toNonempty; obtain ⟨y, -⟩ := hψ.2.1 x; exact ⟨y⟩
        have : ConnectedSpace Y := (connectedSpace_cut_iff hY hS hψ hGcl₀).mpr hns₀
        obtain ⟨a', b', c', ⟨eY⟩, hc', heuler⟩ := cut_iArc_euler_connected hS hY eS hst₀ hGb₀ hGl₀ hψ hP
        obtain ⟨hK'cl, hK'cuff⟩ := cuffs_not_subset_after_cut hS hY hGb₀ hGl₀ hψ hP hKcl hKcuff hs₀K ht₀K
        -- Reindex `Fin n \ {i₀}` by `Fin (n - 1)` using `i₀.succAbove` (writing `n = (n - 1) + 1`):
        obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
        let G' : Fin m → Set Y := fun j => ψ ⁻¹' G (i₀.succAbove j)
        have hG'_arc : ∀ j : Fin m, ∃ s' t' : Y, s' ≠ t' ∧ IsLineWithEnds (G' j) s' t' ∧ G' j ∩ bd Y = {s', t'} ∧
            Disjoint (G' j ∩ bd Y) (ψ ⁻¹' (K ∪ G i₀)) := by
          intro j
          obtain ⟨s, t, hst, hGl, hGb⟩ := hG (i₀.succAbove j)
          have hdisj0 : Disjoint (G (i₀.succAbove j)) (G i₀) := hGdisj (Fin.succAbove_ne i₀ j)
          obtain ⟨s', t', hst', hψs', hψt', hL', hbd'⟩ := lift_disjoint_iArc hY hS hψ hGcl₀ hst hGl hGb hdisj0
          refine ⟨s', t', hst', hL', hbd', ?_⟩
          rw [Set.disjoint_left]; intro y hyG hyK'
          have hybdS : ψ y ∈ G (i₀.succAbove j) ∩ bd S := by
            rw [hbd'] at hyG; rcases hyG with rfl | h
            · rw [hψs']; exact hGb ▸ Or.inl rfl
            · rw [mem_singleton_iff.mp h, hψt']; exact hGb ▸ Or.inr rfl
          rcases hyK' with hK | hGi0
          · exact Set.disjoint_left.mp (hGK (i₀.succAbove j)) hybdS hK
          · exact Set.disjoint_left.mp hdisj0 hybdS.1 hGi0
        obtain ⟨I₀', r₁, N₁', hcard', hN₁', hN₁'disj, hN₁'G', hnonsep'⟩ :=
          ih (m + (2 * a' + b' + c' - 1)) (by omega) hY eY hc' le_rfl hK'cl hK'cuff
            (fun j => by obtain ⟨s', t', h1, h2, h3, -⟩ := hG'_arc j; exact ⟨s', t', h1, h2, h3⟩)
            (fun j₁ j₂ hne => (hGdisj (fun h => hne (Fin.succAbove_right_injective h))).preimage ψ)
            (fun j => (hG'_arc j).choose_spec.choose_spec.2.2.2)
        have hN₁'_disj0 : ∀ k : Fin r₁, Disjoint (N₁' k) (ψ ⁻¹' G i₀) := fun k => by
          obtain ⟨s', t', -, -, hbd', hs', ht'⟩ := hN₁' k
          rw [Set.disjoint_left]; intro y hyN hy0
          have hm : y ∈ N₁' k ∩ bd Y := ⟨hyN, hψ.2.2.2.2 hy0⟩
          rw [hbd'] at hm
          rcases hm with rfl | h
          · exact hs' (Or.inr hy0)
          · exact ht' (mem_singleton_iff.mp h ▸ Or.inr hy0)
        let I₀ : Finset (Fin (m + 1)) := insert i₀ (I₀'.image i₀.succAbove)
        let N₁ : Fin r₁ → Set S := fun k => ψ '' N₁' k
        have hi0_not_mem : i₀ ∉ I₀'.image i₀.succAbove := by
          simp only [Finset.mem_image, not_exists, not_and]
          exact fun j _ h => Fin.succAbove_ne i₀ j h
        have hcard : I₀.card + r₁ = 2 * a + b + c - 1 := by
          rw [Finset.card_insert_of_notMem hi0_not_mem, Finset.card_image_of_injective _ Fin.succAbove_right_injective]
          omega
        refine ⟨I₀, r₁, N₁, hcard, ?_, ?_, ?_, ?_⟩
        · intro k
          obtain ⟨s', t', hst', hL', hbd', hs', ht'⟩ := hN₁' k
          obtain ⟨huv, hL, hbd, -⟩ := push_disjoint_iArc hS hY hψ hGcl₀ hst' hL' hbd' (hN₁'_disj0 k)
          exact ⟨ψ s', ψ t', huv, hL, hbd, fun h => hs' (Or.inl h), fun h => ht' (Or.inl h)⟩
        · intro k₁ k₂ hne
          rw [Set.disjoint_left]; rintro _ ⟨y₁, hy₁, rfl⟩ ⟨y₂, hy₂, he⟩
          have hy12 := hψ.2.2.1 (Set.disjoint_left.mp (hN₁'_disj0 k₁) hy₁) (Set.disjoint_left.mp (hN₁'_disj0 k₂) hy₂) he.symm
          exact Set.disjoint_left.mp (hN₁'disj hne) hy₁ (hy12 ▸ hy₂)
        · intro k j
          by_cases hj : j = i₀
          · subst hj
            obtain ⟨s', t', hst', hL', hbd', -, -⟩ := hN₁' k
            exact (push_disjoint_iArc hS hY hψ hGcl₀ hst' hL' hbd' (hN₁'_disj0 k)).2.2.2
          · obtain ⟨j', rfl⟩ := Fin.exists_succAbove_eq hj
            rw [Set.disjoint_left]; rintro _ ⟨y, hy, rfl⟩ hxG
            exact Set.disjoint_left.mp (hN₁'G' k j') hy hxG
        · -- Preconnectedness via `ψ '' (ψ ⁻¹' (G i₀)ᶜ ∩ ((⋃ j' ∈ I₀', G' j') ∪ ⋃ k, N₁' k)ᶜ)`
          have hcompl_eq : ((⋃ j ∈ I₀, G j) ∪ ⋃ k : Fin r₁, N₁ k)ᶜ =
              ψ '' ((ψ ⁻¹' (G i₀)ᶜ) ∩ ((⋃ j' ∈ I₀', G' j') ∪ ⋃ k : Fin r₁, N₁' k)ᶜ) := by
            ext x; constructor
            · intro hx
              have hx0 : x ∉ G i₀ := fun h => hx (Or.inl (mem_biUnion (Finset.mem_insert_self i₀ _) h))
              obtain ⟨y, rfl⟩ := hψ.2.1 x
              refine ⟨y, ⟨hx0, fun h => ?_⟩, rfl⟩
              rcases h with hG' | hN'
              · obtain ⟨j', hj', hyG'⟩ := mem_iUnion₂.mp hG'
                exact hx (Or.inl (mem_biUnion (Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ hj')) hyG'))
              · obtain ⟨k, hyk⟩ := mem_iUnion.mp hN'
                exact hx (Or.inr (mem_iUnion.mpr ⟨k, ⟨y, hyk, rfl⟩⟩))
            · rintro ⟨y, ⟨hy0, hyGN⟩, rfl⟩ hx
              rcases hx with hG' | hN'
              · obtain ⟨j, hj, hGj⟩ := mem_iUnion₂.mp hG'
                rcases Finset.mem_insert.mp hj with rfl | hj_img
                · exact hy0 hGj
                · obtain ⟨j', hj', rfl⟩ := Finset.mem_image.mp hj_img
                  exact hyGN (Or.inl (mem_biUnion hj' hGj))
              · obtain ⟨k, y', hy'k, hye⟩ := mem_iUnion.mp hN'
                have hy12 := hψ.2.2.1 (Set.disjoint_left.mp (hN₁'_disj0 k) hy'k) hy0 hye
                exact hyGN (Or.inr (mem_iUnion.mpr ⟨k, hy12 ▸ hy'k⟩))
          rw [hcompl_eq]
          have hO_open : IsOpen (((⋃ j' ∈ I₀', G' j') ∪ ⋃ k : Fin r₁, N₁' k)ᶜ : Set Y) :=
            ((I₀'.finite_toSet.isClosed_biUnion fun j' _ => by
                obtain ⟨_, _, _, hl, _, _⟩ := hG'_arc j'; exact hl.isCompact.isClosed).union
              (isClosed_iUnion_of_finite fun k => by
                obtain ⟨_, _, _, hl, _, _, _⟩ := hN₁' k; exact hl.isCompact.isClosed)).isOpen_compl
          have hpre_sub : IsPreconnected ((ψ ⁻¹' (G i₀)ᶜ) ∩ ((⋃ j' ∈ I₀', G' j') ∪ ⋃ k : Fin r₁, N₁' k)ᶜ) := by
            have heq : (ψ ⁻¹' (G i₀)ᶜ) ∩ ((⋃ j' ∈ I₀', G' j') ∪ ⋃ k : Fin r₁, N₁' k)ᶜ =
                ((⋃ j' ∈ I₀', G' j') ∪ ⋃ k : Fin r₁, N₁' k)ᶜ \ ψ ⁻¹' G i₀ := by ext y; simp [and_comm]
            rw [heq]
            exact isPreconnected_open_sdiff_bd hY hO_open hnonsep' hψ.2.2.2.2
          exact hpre_sub.image ψ hψ.1.continuousOn
      · -- Case B: EVERY `G i` separates `S`! Cut along `G 0`, split into `W₁, W₂`, apply IH to BOTH!
        push Not at hex_ns
        obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
        obtain ⟨s₀, t₀, hst₀, hGl₀, hGb₀⟩ := hG 0
        have hGcl₀ : IsClosed (G 0) := hGl₀.isCompact.isClosed
        have hs₀K : s₀ ∉ K := Set.disjoint_left.mp (hGK 0) (hGb₀ ▸ Or.inl rfl)
        have ht₀K : t₀ ∉ K := Set.disjoint_left.mp (hGK 0) (hGb₀ ▸ Or.inr rfl)
        obtain ⟨Y, tY, t2Y, ψ, hY, hψ, X, X', hP⟩ := exists_cut_arc hS hst₀ hGb₀ hGl₀
        have : CompactSpace Y := hY.1
        have : Nonempty Y := by obtain ⟨x⟩ := ‹ConnectedSpace S›.toNonempty; obtain ⟨y, -⟩ := hψ.2.1 x; exact ⟨y⟩
        have hnotc : ¬ ConnectedSpace Y := fun hcY => hex_ns 0 ((connectedSpace_cut_iff hY hS hψ hGcl₀).mp hcY)
        obtain ⟨W₁, W₂, hW₁, hW₂, hdW, hUW, hXW₁, hX'W₂, hcW₁, hcW₂,
          a₁, b₁, c₁, a₂, b₂, c₂, ⟨e₁⟩, ⟨e₂⟩, hc₁, hc₂, heuler⟩ :=
          cut_iArc_euler_sep hS hY eS hst₀ hGb₀ hGl₀ hψ hP hnotc
        obtain ⟨hK'cl, hK'cuff⟩ := cuffs_not_subset_after_cut hS hY hGb₀ hGl₀ hψ hP hKcl hKcuff hs₀K ht₀K
        -- Partition `j : Fin m` according to whether `ψ ⁻¹' G j.succ ⊆ W₁` or `⊆ W₂`:
        have hlift_part : ∀ j : Fin m, ψ ⁻¹' G j.succ ⊆ W₁ ∨ ψ ⁻¹' G j.succ ⊆ W₂ := fun j => by
          obtain ⟨s, t, hst, hGl, hGb⟩ := hG j.succ
          obtain ⟨s', t', -, -, -, hL', -⟩ := lift_disjoint_iArc hY hS hψ hGcl₀ hst hGl hGb (hGdisj (Fin.succ_ne_zero j))
          have hpre : IsPreconnected (ψ ⁻¹' G j.succ) := by
            obtain ⟨φ, -, -⟩ := hL'
            have := (isPreconnected_univ (α := unitInterval)).image (fun r => (φ r).1)
              (continuous_subtype_val.comp φ.continuous).continuousOn
            have him : (fun r => (φ r).1) '' (univ : Set unitInterval) = ψ ⁻¹' G j.succ := by
              ext y; constructor
              · rintro ⟨r, -, rfl⟩; exact (φ r).2
              · intro hy; exact ⟨φ.symm ⟨y, hy⟩, mem_univ _, congrArg Subtype.val (φ.apply_symm_apply ⟨y, hy⟩)⟩
            rwa [him] at this
          by_cases hm1 : ((ψ ⁻¹' G j.succ) ∩ W₁).Nonempty
          · left; exact hpre.subset_isClopen hW₁ hm1
          · right
            have hne : (ψ ⁻¹' G j.succ).Nonempty := ⟨s', hL'.left_mem⟩
            obtain ⟨y, hy⟩ := hne
            have hy2 : y ∈ W₂ := (hUW ▸ mem_univ y : y ∈ W₁ ∪ W₂).resolve_left fun h => hm1 ⟨y, hy, h⟩
            exact hpre.subset_isClopen hW₂ ⟨y, hy, hy2⟩
        let J₁ : Finset (Fin m) := Finset.univ.filter fun j => ψ ⁻¹' G j.succ ⊆ W₁
        let J₂ : Finset (Fin m) := Finset.univ.filter fun j => ψ ⁻¹' G j.succ ⊆ W₂
        have hJ_disj : Disjoint J₁ J₂ := Finset.disjoint_left.mpr fun j h1 h2 => by
          obtain ⟨s, t, hst, hGl, hGb⟩ := hG j.succ
          obtain ⟨y, hy⟩ := hψ.2.1 s
          have hyG : y ∈ ψ ⁻¹' G j.succ := by show ψ y ∈ G j.succ; rw [hy]; exact hGl.left_mem
          exact Set.disjoint_left.mp hdW ((Finset.mem_filter.mp h1).2 hyG) ((Finset.mem_filter.mp h2).2 hyG)
        let eJ₁ : Fin J₁.card ≃ J₁ := (Fintype.equivFinOfCardEq (Fintype.card_coe J₁)).symm
        let eJ₂ : Fin J₂.card ≃ J₂ := (Fintype.equivFinOfCardEq (Fintype.card_coe J₂)).symm
        -- Note `J₁.card ≤ m` and `2*a₁+b₁+c₁-1 ≤ 2*a+b+c-1`, so `J₁.card + (2*a₁+b₁+c₁-1) < (m+1) + (2*a+b+c-1) ≤ M`!
        have hcardJ₁ : J₁.card ≤ m := (Finset.card_le_univ J₁).trans (by simp)
        have hcardJ₂ : J₂.card ≤ m := (Finset.card_le_univ J₂).trans (by simp)
        -- Helper to run IH on a clopen component `W` (`W₁` or `W₂`):
        have hbd_sub : ∀ {W : Set Y}, IsClopen W → bd W = Subtype.val ⁻¹' bd Y := fun {W} hW => by
          ext ⟨y, hyW⟩
          show ¬ IsInteriorPoint (⟨y, hyW⟩ : W) ↔ ¬ IsInteriorPoint y
          rw [isInteriorPoint_sub hW.2]
        have hcuffs_sub : ∀ {W : Set Y} (hW : IsClopen W) {C : Set W}, C ∈ cuffs W → Subtype.val '' C ∈ cuffs Y := by
          rintro W hW C ⟨x, hxbd, rfl⟩
          have hbdW : bd W = Subtype.val ⁻¹' bd Y := hbd_sub hW
          have hxbdY : x.1 ∈ bd Y := by rw [hbdW] at hxbd; exact hxbd
          refine ⟨x.1, hxbdY, ?_⟩
          apply subset_antisymm
          · intro y hy
            have hcc_sub : connectedComponentIn (bd Y) x.1 ⊆ W :=
              isPreconnected_connectedComponentIn.subset_isClopen hW ⟨x.1, mem_connectedComponentIn hxbdY, x.2⟩
            have hyW : y ∈ W := hcc_sub hy
            refine ⟨⟨y, hyW⟩, ?_, rfl⟩
            have hpreW : IsPreconnected (Subtype.val ⁻¹' connectedComponentIn (bd Y) x.1 : Set W) := by
              rw [← IsEmbedding.subtypeVal.isPreconnected_image, Subtype.image_preimage_coe, inter_eq_right.mpr hcc_sub]
              exact isPreconnected_connectedComponentIn
            exact hpreW.subset_connectedComponentIn (mem_connectedComponentIn hxbdY)
              (fun z hz => by rw [hbdW]; exact connectedComponentIn_subset (bd Y) x.1 hz) hy
          · exact (isPreconnected_connectedComponentIn.image Subtype.val continuous_subtype_val.continuousOn).subset_connectedComponentIn
              ⟨x, mem_connectedComponentIn hxbd, rfl⟩
              (fun _ ⟨z, hz, hze⟩ => hze ▸ (by have := connectedComponentIn_subset _ _ hz; rw [hbdW] at this; exact this))
        have hrun_comp : ∀ (W : Set Y) (hW : IsClopen W) (_hcW : ConnectedSpace W)
            (a' b' c' : ℕ) (eW : W ≃ₜ SurfaceModel a' b' c') (hc' : 1 ≤ c')
            (hde : 2 * a' + b' + c' - 1 ≤ 2 * a + b + c - 1)
            (J : Finset (Fin m)) (hJW : ∀ j ∈ J, ψ ⁻¹' G j.succ ⊆ W),
            ∃ (I_W : Finset (Fin m)) (r_W : ℕ) (N_W : Fin r_W → Set Y),
              I_W ⊆ J ∧ I_W.card + r_W = 2 * a' + b' + c' - 1 ∧
              (∀ k, N_W k ⊆ W) ∧
              (∀ k, ∃ s' t' : Y, s' ≠ t' ∧ IsLineWithEnds (N_W k) s' t' ∧ N_W k ∩ bd Y = {s', t'} ∧
                ψ s' ∉ K ∧ ψ t' ∉ K ∧ Disjoint (N_W k) (ψ ⁻¹' G 0)) ∧
              (Pairwise fun k₁ k₂ => Disjoint (N_W k₁) (N_W k₂)) ∧
              (∀ k (j : Fin m), j ∈ J → Disjoint (N_W k) (ψ ⁻¹' G j.succ)) ∧
              IsPreconnected (W \ ((⋃ j ∈ I_W, ψ ⁻¹' G j.succ) ∪ ⋃ k : Fin r_W, N_W k)) := by
          intro W hW hcW a' b' c' eW hc' hde J hJW
          have hW_surf : IsSurface W := isSurface_sub hY hW
          let eJ : Fin J.card ≃ J := (Fintype.equivFinOfCardEq (Fintype.card_coe J)).symm
          have hcardJ : J.card ≤ m := (Finset.card_le_univ J).trans (by simp)
          let K_W : Set W := Subtype.val ⁻¹' (ψ ⁻¹' (K ∪ G 0))
          have hKW_cl : IsClosed K_W := hK'cl.preimage continuous_subtype_val
          have hKW_cuff : ∀ C ∈ cuffs W, (C \ K_W).Nonempty := fun C hC => by
            obtain ⟨y, hyC, hyK'⟩ := hK'cuff (Subtype.val '' C) (hcuffs_sub hW hC)
            obtain ⟨x, hxC, rfl⟩ := hyC
            exact ⟨x, hxC, hyK'⟩
          let G_W : Fin J.card → Set W := fun i => Subtype.val ⁻¹' (ψ ⁻¹' G (eJ i).1.succ)
          have hGW_arc : ∀ i : Fin J.card, ∃ s' t' : W, s' ≠ t' ∧ IsLineWithEnds (G_W i) s' t' ∧
              G_W i ∩ bd W = {s', t'} ∧ Disjoint (G_W i ∩ bd W) K_W := by
            intro i
            let j := (eJ i).1
            obtain ⟨s, t, hst, hGl, hGb⟩ := hG j.succ
            have hdisj0 : Disjoint (G j.succ) (G 0) := hGdisj (Fin.succ_ne_zero j)
            obtain ⟨s', t', hst', hψs', hψt', hL', hbd'⟩ := lift_disjoint_iArc hY hS hψ hGcl₀ hst hGl hGb hdisj0
            have hsubW : ψ ⁻¹' G j.succ ⊆ W := hJW j (eJ i).2
            have hs'W : s' ∈ W := hsubW hL'.left_mem
            have ht'W : t' ∈ W := hsubW hL'.right_mem
            obtain ⟨φ, hφ0, hφ1⟩ := hL'
            let eSub : G_W i ≃ₜ (ψ ⁻¹' G j.succ : Set Y) :=
              { toFun := fun x => ⟨x.1.1, x.2⟩
                invFun := fun y => ⟨⟨y.1, hsubW y.2⟩, y.2⟩
                left_inv := fun _ => rfl
                right_inv := fun _ => rfl
                continuous_toFun := Continuous.subtype_mk (continuous_subtype_val.comp continuous_subtype_val) _
                continuous_invFun := Continuous.subtype_mk (Continuous.subtype_mk continuous_subtype_val fun y => hsubW y.2) (fun y => y.2) }
            have hL_W : IsLineWithEnds (G_W i) ⟨s', hs'W⟩ ⟨t', ht'W⟩ :=
              ⟨φ.trans eSub.symm, Subtype.ext hφ0, Subtype.ext hφ1⟩
            have hbd_W : G_W i ∩ bd W = {⟨s', hs'W⟩, ⟨t', ht'W⟩} := by
              rw [hbd_sub hW]; ext ⟨y, hyW⟩; simp only [G_W, mem_inter_iff, mem_preimage, mem_insert_iff, mem_singleton_iff, Subtype.mk.injEq]
              exact show y ∈ ψ ⁻¹' G j.succ ∩ bd Y ↔ y = s' ∨ y = t' by rw [hbd']; rfl
            refine ⟨⟨s', hs'W⟩, ⟨t', ht'W⟩, fun h => hst' (congrArg Subtype.val h), hL_W, hbd_W, ?_⟩
            rw [Set.disjoint_left]; rintro ⟨y, hyW⟩ hyG hyK
            rw [hbd_W] at hyG
            have hybdS : ψ y ∈ G j.succ ∩ bd S := by
              rcases hyG with h | h
              · have := congrArg Subtype.val h; subst this; rw [hψs']; exact hGb ▸ Or.inl rfl
              · have := congrArg Subtype.val (mem_singleton_iff.mp h); subst this; rw [hψt']; exact hGb ▸ Or.inr rfl
            rcases hyK with hK | h0
            · exact Set.disjoint_left.mp (hGK j.succ) hybdS hK
            · exact Set.disjoint_left.mp hdisj0 hybdS.1 h0
          obtain ⟨I_raw, r_W, N_raw, hcard_W, hN_raw, hN_raw_disj, hN_raw_G, hnonsep_W⟩ :=
            ih (J.card + (2 * a' + b' + c' - 1)) (by omega) hW_surf eW hc' le_rfl hKW_cl hKW_cuff
              (fun i => by obtain ⟨s', t', h1, h2, h3, -⟩ := hGW_arc i; exact ⟨s', t', h1, h2, h3⟩)
              (fun i₁ i₂ hne => ((hGdisj (fun h => hne (eJ.injective (Subtype.ext (Fin.succ_injective m h))))).preimage ψ).preimage Subtype.val)
              (fun i => (hGW_arc i).choose_spec.choose_spec.2.2.2)
          let I_W : Finset (Fin m) := I_raw.image fun i => (eJ i).1
          let N_W : Fin r_W → Set Y := fun k => Subtype.val '' N_raw k
          have hIW_sub : I_W ⊆ J := fun j hj => by
            obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hj; exact (eJ i).2
          have hIW_card : I_W.card = I_raw.card :=
            Finset.card_image_of_injective _ fun i₁ i₂ h => eJ.injective (Subtype.ext h)
          refine ⟨I_W, r_W, N_W, hIW_sub, hIW_card.symm ▸ hcard_W, fun k _ ⟨x, _, hxe⟩ => hxe ▸ x.2, ?_, ?_, ?_, ?_⟩
          · intro k
            obtain ⟨s', t', hst', hL', hbd', hs', ht'⟩ := hN_raw k
            have hs'N : s' ∈ N_raw k := hL'.left_mem
            have ht'N : t' ∈ N_raw k := hL'.right_mem
            obtain ⟨φ, hφ0, hφ1⟩ := hL'
            let eIm : N_raw k ≃ₜ N_W k :=
              (IsEmbedding.subtypeVal.homeomorphImage (N_raw k))
            have hL_Y : IsLineWithEnds (N_W k) s'.1 t'.1 :=
              ⟨φ.trans eIm, by show (φ 0).1.1 = s'.1; rw [hφ0], by show (φ 1).1.1 = t'.1; rw [hφ1]⟩
            have hbd_Y : N_W k ∩ bd Y = {s'.1, t'.1} := by
              ext y; constructor
              · rintro ⟨⟨x, hxN, rfl⟩, hybd⟩
                have hxbd : x ∈ N_raw k ∩ bd W := ⟨hxN, by rw [hbd_sub hW]; exact hybd⟩
                rw [hbd'] at hxbd
                rcases hxbd with rfl | h
                · exact Or.inl rfl
                · exact Or.inr (congrArg Subtype.val (mem_singleton_iff.mp h))
              · rintro (rfl | rfl)
                · refine ⟨⟨s', hs'N, rfl⟩, ?_⟩
                  have h1 : s' ∈ bd W := (hbd'.symm ▸ Or.inl rfl : s' ∈ N_raw k ∩ bd W).2
                  rw [hbd_sub hW] at h1; exact h1
                · refine ⟨⟨t', ht'N, rfl⟩, ?_⟩
                  have h1 : t' ∈ bd W := (hbd'.symm ▸ Or.inr rfl : t' ∈ N_raw k ∩ bd W).2
                  rw [hbd_sub hW] at h1; exact h1
            have hdisj0 : Disjoint (N_W k) (ψ ⁻¹' G 0) := by
              rw [Set.disjoint_left]; rintro _ ⟨x, hxN, rfl⟩ hx0
              have hxbd : x ∈ N_raw k ∩ bd W := ⟨hxN, by rw [hbd_sub hW]; exact hψ.2.2.2.2 hx0⟩
              rw [hbd'] at hxbd
              rcases hxbd with rfl | h
              · exact hs' (Or.inr hx0)
              · exact ht' (mem_singleton_iff.mp h ▸ Or.inr hx0)
            exact ⟨s'.1, t'.1, fun h => hst' (Subtype.ext h), hL_Y, hbd_Y,
              fun h => hs' (Or.inl h), fun h => ht' (Or.inl h), hdisj0⟩
          · intro k₁ k₂ hne
            exact Set.disjoint_image_of_injective Subtype.val_injective (hN_raw_disj hne)
          · intro k j hj
            let i := eJ.symm ⟨j, hj⟩
            have hi : (eJ i).1 = j := congrArg Subtype.val (eJ.apply_symm_apply ⟨j, hj⟩)
            rw [Set.disjoint_left]; rintro _ ⟨x, hxN, rfl⟩ hxG
            exact Set.disjoint_left.mp (hN_raw_G k i) hxN (show ψ x.1 ∈ G (eJ i).1.succ by rwa [hi])
          · have him : Subtype.val '' (((⋃ i ∈ I_raw, G_W i) ∪ ⋃ k : Fin r_W, N_raw k)ᶜ : Set W) =
                W \ ((⋃ j ∈ I_W, ψ ⁻¹' G j.succ) ∪ ⋃ k : Fin r_W, N_W k) := by
              ext y; constructor
              · rintro ⟨⟨y, hyW⟩, hyc, rfl⟩
                refine ⟨hyW, ?_⟩
                rintro (h1 | h2)
                · obtain ⟨j, hj, hyG⟩ := mem_iUnion₂.mp h1
                  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hj
                  exact hyc (Or.inl (mem_biUnion hi hyG))
                · obtain ⟨k, x, hxN, hxe⟩ := mem_iUnion.mp h2
                  exact hyc (Or.inr (mem_iUnion.mpr ⟨k, (Subtype.ext hxe : x = ⟨y, hyW⟩) ▸ hxN⟩))
              · rintro ⟨hyW, hyc⟩
                refine ⟨⟨y, hyW⟩, ?_, rfl⟩
                rintro (h1 | h2)
                · obtain ⟨i, hi, hyG⟩ := mem_iUnion₂.mp h1
                  exact hyc (Or.inl (mem_biUnion (Finset.mem_image_of_mem _ hi) hyG))
                · obtain ⟨k, hyN⟩ := mem_iUnion.mp h2
                  exact hyc (Or.inr (mem_iUnion.mpr ⟨k, ⟨y, hyW⟩, hyN, rfl⟩))
            rw [← him]
            exact hnonsep_W.image Subtype.val continuous_subtype_val.continuousOn
        -- Run on BOTH components `W₁` and `W₂`:
        obtain ⟨I₁, r₁, NW₁, hI₁sub, hcard₁, hNW₁W, hNW₁arc, hNW₁disj, hNW₁G, hpre₁⟩ :=
          hrun_comp W₁ hW₁ hcW₁ a₁ b₁ c₁ e₁ hc₁ (by omega) J₁ (fun j hj => (Finset.mem_filter.mp hj).2)
        obtain ⟨I₂, r₂, NW₂, hI₂sub, hcard₂, hNW₂W, hNW₂arc, hNW₂disj, hNW₂G, hpre₂⟩ :=
          hrun_comp W₂ hW₂ hcW₂ a₂ b₂ c₂ e₂ hc₂ (by omega) J₂ (fun j hj => (Finset.mem_filter.mp hj).2)
        let I₀ : Finset (Fin (m + 1)) := (I₁ ∪ I₂).image Fin.succ
        let N₁ : Fin (r₁ + r₂) → Set S := fun k =>
          if h : k.1 < r₁ then ψ '' NW₁ ⟨k.1, h⟩ else ψ '' NW₂ ⟨k.1 - r₁, by omega⟩
        have hI12_disj : Disjoint I₁ I₂ := hJ_disj.mono hI₁sub hI₂sub
        have hcard : I₀.card + (r₁ + r₂) = 2 * a + b + c - 1 := by
          rw [Finset.card_image_of_injective _ (Fin.succ_injective m), Finset.card_union_of_disjoint hI12_disj]
          omega
        refine ⟨I₀, r₁ + r₂, N₁, hcard, ?_, ?_, ?_, ?_⟩
        · intro k; dsimp only [N₁]; split_ifs with hk
          · obtain ⟨s', t', hst', hL', hbd', hs', ht', hdisj0⟩ := hNW₁arc ⟨k.1, hk⟩
            obtain ⟨huv, hL, hbd, -⟩ := push_disjoint_iArc hS hY hψ hGcl₀ hst' hL' hbd' hdisj0
            exact ⟨ψ s', ψ t', huv, hL, hbd, hs', ht'⟩
          · obtain ⟨s', t', hst', hL', hbd', hs', ht', hdisj0⟩ := hNW₂arc ⟨k.1 - r₁, by omega⟩
            obtain ⟨huv, hL, hbd, -⟩ := push_disjoint_iArc hS hY hψ hGcl₀ hst' hL' hbd' hdisj0
            exact ⟨ψ s', ψ t', huv, hL, hbd, hs', ht'⟩
        · intro k₁ k₂ hne
          dsimp only [N₁]; split_ifs with h1 h2 h2
          · rw [Set.disjoint_left]; rintro _ ⟨y₁, hy₁, rfl⟩ ⟨y₂, hy₂, he⟩
            obtain ⟨-, -, -, -, -, -, -, hd1⟩ := hNW₁arc ⟨k₁.1, h1⟩
            obtain ⟨-, -, -, -, -, -, -, hd2⟩ := hNW₁arc ⟨k₂.1, h2⟩
            have hy12 := hψ.2.2.1 (Set.disjoint_left.mp hd1 hy₁) (Set.disjoint_left.mp hd2 hy₂) he.symm
            exact Set.disjoint_left.mp (hNW₁disj (fun h => hne (Fin.ext (congrArg (Fin.val : Fin r₁ → ℕ) h)))) hy₁ (hy12 ▸ hy₂)
          · rw [Set.disjoint_left]; rintro _ ⟨y₁, hy₁, rfl⟩ ⟨y₂, hy₂, he⟩
            obtain ⟨-, -, -, -, -, -, -, hd1⟩ := hNW₁arc ⟨k₁.1, h1⟩
            obtain ⟨-, -, -, -, -, -, -, hd2⟩ := hNW₂arc ⟨k₂.1 - r₁, by omega⟩
            have hy12 := hψ.2.2.1 (Set.disjoint_left.mp hd1 hy₁) (Set.disjoint_left.mp hd2 hy₂) he.symm
            exact Set.disjoint_left.mp hdW (hNW₁W _ hy₁) (hy12 ▸ hNW₂W _ hy₂)
          · rw [Set.disjoint_left]; rintro _ ⟨y₁, hy₁, rfl⟩ ⟨y₂, hy₂, he⟩
            obtain ⟨-, -, -, -, -, -, -, hd1⟩ := hNW₂arc ⟨k₁.1 - r₁, by omega⟩
            obtain ⟨-, -, -, -, -, -, -, hd2⟩ := hNW₁arc ⟨k₂.1, h2⟩
            have hy12 := hψ.2.2.1 (Set.disjoint_left.mp hd1 hy₁) (Set.disjoint_left.mp hd2 hy₂) he.symm
            exact Set.disjoint_left.mp hdW (hy12 ▸ hNW₁W _ hy₂) (hNW₂W _ hy₁)
          · rw [Set.disjoint_left]; rintro _ ⟨y₁, hy₁, rfl⟩ ⟨y₂, hy₂, he⟩
            obtain ⟨-, -, -, -, -, -, -, hd1⟩ := hNW₂arc ⟨k₁.1 - r₁, by omega⟩
            obtain ⟨-, -, -, -, -, -, -, hd2⟩ := hNW₂arc ⟨k₂.1 - r₁, by omega⟩
            have hy12 := hψ.2.2.1 (Set.disjoint_left.mp hd1 hy₁) (Set.disjoint_left.mp hd2 hy₂) he.symm
            exact Set.disjoint_left.mp (hNW₂disj (fun h => hne (Fin.ext (by have := congrArg Fin.val h; dsimp at this; omega)))) hy₁ (hy12 ▸ hy₂)
        · intro k j
          refine Fin.cases ?_ (fun j' => ?_) j
          · dsimp only [N₁]; split_ifs with hk
            · obtain ⟨s', t', hst', hL', hbd', -, -, hdisj0⟩ := hNW₁arc ⟨k.1, hk⟩
              exact (push_disjoint_iArc hS hY hψ hGcl₀ hst' hL' hbd' hdisj0).2.2.2
            · obtain ⟨s', t', hst', hL', hbd', -, -, hdisj0⟩ := hNW₂arc ⟨k.1 - r₁, by omega⟩
              exact (push_disjoint_iArc hS hY hψ hGcl₀ hst' hL' hbd' hdisj0).2.2.2
          · dsimp only [N₁]; split_ifs with hk
            · rcases hlift_part j' with hW1 | hW2
              · rw [Set.disjoint_left]; rintro _ ⟨y, hy, rfl⟩ hyG
                exact Set.disjoint_left.mp (hNW₁G ⟨k.1, hk⟩ j' (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hW1⟩)) hy hyG
              · rw [Set.disjoint_left]; rintro _ ⟨y, hy, rfl⟩ hyG
                exact Set.disjoint_left.mp hdW (hNW₁W _ hy) (hW2 hyG)
            · rcases hlift_part j' with hW1 | hW2
              · rw [Set.disjoint_left]; rintro _ ⟨y, hy, rfl⟩ hyG
                exact Set.disjoint_left.mp hdW (hW1 hyG) (hNW₂W _ hy)
              · rw [Set.disjoint_left]; rintro _ ⟨y, hy, rfl⟩ hyG
                exact Set.disjoint_left.mp (hNW₂G ⟨k.1 - r₁, by omega⟩ j' (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hW2⟩)) hy hyG
        · -- Preconnectedness of `S \ (⋃ I₀ ∪ ⋃ N₁)`: it is the union of `ψ '' C₁` and `ψ '' C₂`, which meet at `s₀ ∈ G 0`!
          let C₁ : Set Y := W₁ \ ((⋃ j ∈ I₁, ψ ⁻¹' G j.succ) ∪ ⋃ k : Fin r₁, NW₁ k)
          let C₂ : Set Y := W₂ \ ((⋃ j ∈ I₂, ψ ⁻¹' G j.succ) ∪ ⋃ k : Fin r₂, NW₂ k)
          have hC1_eq : ψ '' C₁ ∪ ψ '' C₂ = ((⋃ j ∈ I₀, G j) ∪ ⋃ k : Fin (r₁ + r₂), N₁ k)ᶜ := by
            ext x; constructor
            · rintro (⟨y, ⟨hyW, hyC⟩, rfl⟩ | ⟨y, ⟨hyW, hyC⟩, rfl⟩)
              · rintro (hG' | hN')
                · obtain ⟨j, hj, hxG⟩ := mem_iUnion₂.mp hG'
                  obtain ⟨j', hj', rfl⟩ := Finset.mem_image.mp hj
                  rcases Finset.mem_union.mp hj' with hj1 | hj2
                  · exact hyC (Or.inl (mem_biUnion hj1 hxG))
                  · exact Set.disjoint_left.mp hdW hyW ((Finset.mem_filter.mp (hI₂sub hj2)).2 hxG)
                · obtain ⟨k, hxN⟩ := mem_iUnion.mp hN'
                  dsimp only [N₁] at hxN; split_ifs at hxN with hk
                  · obtain ⟨y', hy'N, hye⟩ := hxN
                    obtain ⟨-, -, -, -, -, -, -, hd0⟩ := hNW₁arc ⟨k.1, hk⟩
                    have hy'0 : ψ y' ∉ G 0 := Set.disjoint_left.mp hd0 hy'N
                    have hy12 : y' = y := hψ.2.2.1 hy'0 (by rwa [hye] at hy'0) hye
                    exact hyC (Or.inr (mem_iUnion.mpr ⟨⟨k.1, hk⟩, hy12 ▸ hy'N⟩))
                  · obtain ⟨y', hy'N, hye⟩ := hxN
                    obtain ⟨-, -, -, -, -, -, -, hd0⟩ := hNW₂arc ⟨k.1 - r₁, by omega⟩
                    have hy'0 : ψ y' ∉ G 0 := Set.disjoint_left.mp hd0 hy'N
                    have hy12 : y' = y := hψ.2.2.1 hy'0 (by rwa [hye] at hy'0) hye
                    exact Set.disjoint_left.mp hdW hyW (hy12 ▸ hNW₂W _ hy'N)
              · rintro (hG' | hN')
                · obtain ⟨j, hj, hxG⟩ := mem_iUnion₂.mp hG'
                  obtain ⟨j', hj', rfl⟩ := Finset.mem_image.mp hj
                  rcases Finset.mem_union.mp hj' with hj1 | hj2
                  · exact Set.disjoint_left.mp hdW ((Finset.mem_filter.mp (hI₁sub hj1)).2 hxG) hyW
                  · exact hyC (Or.inl (mem_biUnion hj2 hxG))
                · obtain ⟨k, hxN⟩ := mem_iUnion.mp hN'
                  dsimp only [N₁] at hxN; split_ifs at hxN with hk
                  · obtain ⟨y', hy'N, hye⟩ := hxN
                    obtain ⟨-, -, -, -, -, -, -, hd0⟩ := hNW₁arc ⟨k.1, hk⟩
                    have hy'0 : ψ y' ∉ G 0 := Set.disjoint_left.mp hd0 hy'N
                    have hy12 : y' = y := hψ.2.2.1 hy'0 (by rwa [hye] at hy'0) hye
                    exact Set.disjoint_left.mp hdW (hy12 ▸ hNW₁W _ hy'N) hyW
                  · obtain ⟨y', hy'N, hye⟩ := hxN
                    obtain ⟨-, -, -, -, -, -, -, hd0⟩ := hNW₂arc ⟨k.1 - r₁, by omega⟩
                    have hy'0 : ψ y' ∉ G 0 := Set.disjoint_left.mp hd0 hy'N
                    have hy12 : y' = y := hψ.2.2.1 hy'0 (by rwa [hye] at hy'0) hye
                    exact hyC (Or.inr (mem_iUnion.mpr ⟨⟨k.1 - r₁, by omega⟩, hy12 ▸ hy'N⟩))
            · intro hx
              obtain ⟨y, rfl⟩ := hψ.2.1 x
              rcases (hUW ▸ mem_univ y : y ∈ W₁ ∪ W₂) with hy1 | hy2
              · left; refine ⟨y, ⟨hy1, ?_⟩, rfl⟩
                rintro (hG' | hN')
                · obtain ⟨j', hj', hyG⟩ := mem_iUnion₂.mp hG'
                  exact hx (Or.inl (mem_biUnion (Finset.mem_image_of_mem _ (Finset.mem_union_left _ hj')) hyG))
                · obtain ⟨k, hyN⟩ := mem_iUnion.mp hN'
                  refine hx (Or.inr (mem_iUnion.mpr ⟨⟨k.1, by omega⟩, ?_⟩))
                  simp only [N₁, k.2, ↓reduceDIte]; exact ⟨y, hyN, rfl⟩
              · right; refine ⟨y, ⟨hy2, ?_⟩, rfl⟩
                rintro (hG' | hN')
                · obtain ⟨j', hj', hyG⟩ := mem_iUnion₂.mp hG'
                  exact hx (Or.inl (mem_biUnion (Finset.mem_image_of_mem _ (Finset.mem_union_right _ hj')) hyG))
                · obtain ⟨k, hyN⟩ := mem_iUnion.mp hN'
                  refine hx (Or.inr (mem_iUnion.mpr ⟨⟨r₁ + k.1, by omega⟩, ?_⟩))
                  simp only [N₁, show ¬ (r₁ + k.1 < r₁) by omega, ↓reduceDIte, Nat.add_sub_cancel_left]
                  exact ⟨y, hyN, rfl⟩
          rw [← hC1_eq]
          obtain ⟨x0, _x1, y0, _y1, l1, l2, -, -, -, -, hψx0, hψy0, -, -⟩ := hP
          have hs0_C1 : s₀ ∈ ψ '' C₁ := by
            refine ⟨x0, ⟨hXW₁ l1.left_mem, ?_⟩, hψx0⟩
            rintro (hG' | hN')
            · obtain ⟨j', -, hxG⟩ := mem_iUnion₂.mp hG'
              exact Set.disjoint_left.mp (hGdisj (Fin.succ_ne_zero j')) (by rw [← hψx0]; exact hxG) hGl₀.left_mem
            · obtain ⟨k, hxN⟩ := mem_iUnion.mp hN'
              obtain ⟨-, -, -, -, -, -, -, hd0⟩ := hNW₁arc k
              exact Set.disjoint_left.mp hd0 hxN (by show ψ x0 ∈ G 0; rw [hψx0]; exact hGl₀.left_mem)
          have hs0_C2 : s₀ ∈ ψ '' C₂ := by
            refine ⟨y0, ⟨hX'W₂ l2.left_mem, ?_⟩, hψy0⟩
            rintro (hG' | hN')
            · obtain ⟨j', -, hyG⟩ := mem_iUnion₂.mp hG'
              exact Set.disjoint_left.mp (hGdisj (Fin.succ_ne_zero j')) (by rw [← hψy0]; exact hyG) hGl₀.left_mem
            · obtain ⟨k, hyN⟩ := mem_iUnion.mp hN'
              obtain ⟨-, -, -, -, -, -, -, hd0⟩ := hNW₂arc k
              exact Set.disjoint_left.mp hd0 hyN (by show ψ y0 ∈ G 0; rw [hψy0]; exact hGl₀.left_mem)
          exact (hpre₁.image ψ hψ.1.continuousOn).union s₀ hs0_C1 hs0_C2 (hpre₂.image ψ hψ.1.continuousOn)

end GraphMinor.LPPS22
