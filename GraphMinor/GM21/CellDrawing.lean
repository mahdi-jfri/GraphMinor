module

public import GraphMinor.GM21.Defs
public import GraphMinor.GM21.PortraitDefs
import GraphMinor.Surface.DiscArcs
import GraphMinor.Surface.Circle

/-!
# Graph Minors XXI, Section 9: Drawing Internal Cells in `closure c` for `(9.2)`

This file formalizes the construction in the proof of **Graph Minors XXI, (9.2)** (page 39 of the
preprint): "For each internal cell $c \in C(\Gamma) \setminus \mathcal{A}_1$, there is a drawing of
$\alpha(c)$ in the closed disc $\bar{c}$ with the vertices in $\tilde{c}$ representing themselves,
by (9.1), and this drawing can be chosen so that it meets $bd(\bar{c})$ only in $\tilde{c}$. We may
therefore assume, to simplify the notation, that $\alpha(c)$ is such a drawing in $\bar{c}$ for
each internal cell $c \in C(\Gamma) \setminus \mathcal{A}_1$. Let $\Gamma'$ be the drawing formed
by the vertices in $V(\Gamma)$ and the union of the drawings $\alpha(c)$ over all internal
$c \in C(\Gamma) \setminus \mathcal{A}_1$. Then $\Gamma'$ is a drawing in $\Sigma$, and there is a
1-1 correspondence between the spaces of $\Gamma'$ and the border cells of $\Gamma$."
-/

@[expose] public section

namespace GraphMinor.GM21

open Set Function Topology Metric Classical
open GraphMinor.Surface
open GraphMinor.GM10
open GraphMinor.GM17
open GraphMinor.Hypergraph

universe u v

local notation "𝕀" => unitInterval

/-! ## 1. Path Indexing of `α(c)` from `CanBeDrawnInDisc21` when `|c̃| = 2` -/

/-- If `X = {a, b}`, then for any `v ∈ X`, `X \ {v}` has no two distinct elements. -/
private theorem not_two_distinct_in_pair_diff {α : Type u} {a b v x₁ x₂ : α}
    (hv : v ∈ ({a, b} : Set α)) (hx₁ : x₁ ∈ ({a, b} : Set α) \ {v})
    (hx₂ : x₂ ∈ ({a, b} : Set α) \ {v}) (hne : x₁ ≠ x₂) : False := by
  rcases hv with rfl | rfl
  · have h1 : x₁ = b := hx₁.1.resolve_left hx₁.2
    have h2 : x₂ = b := hx₂.1.resolve_left hx₂.2
    exact hne (h1.trans h2.symm)
  · have h1 : x₁ = a := hx₁.1.resolve_right hx₁.2
    have h2 : x₂ = a := hx₂.1.resolve_right hx₂.2
    exact hne (h1.trans h2.symm)

/-- Uniform vertex indexing for `H` satisfying `CanBeDrawnInDisc21 H {a, b}` with `a ≠ b`. -/
theorem exists_path_indexing_of_canBeDrawnInDisc21 {α : Type u} {β : Type v}
    {H : Hypergraph α β} {a b : α} (hab : a ≠ b)
    (hdraw : CanBeDrawnInDisc21 H {a, b}) :
    ∃ (m : ℕ) (_ : 1 ≤ m) (v : Fin (m + 1) → α),
      Function.Injective v ∧
      v 0 = a ∧
      v ⟨m, Nat.lt_succ_self m⟩ = b ∧
      H.vertexSet = Set.range v ∧
      ∀ i j : Fin (m + 1), H.skeleton.Adj (v i) (v j) → (i.1 + 1 = j.1 ∨ j.1 + 1 = i.1) := by
  rcases hdraw with hVX | ⟨_, x₁, hx₁, x₂, hx₂, hx₁₂, hpath⟩ |
      ⟨_, v₀, hv₀, x₁, hx₁, x₂, hx₂, hx₁₂, _⟩
  · let v : Fin 2 → α := fun i => if i.1 = 0 then a else b
    have hv_inj : Function.Injective v := by
      intro i j h
      fin_cases i <;> fin_cases j
      · rfl
      · exact (hab h).elim
      · exact (hab h.symm).elim
      · rfl
    refine ⟨1, le_rfl, v, hv_inj, rfl, rfl, ?_, ?_⟩
    · rw [hVX]
      ext w
      simp only [mem_insert_iff, mem_singleton_iff, mem_range]
      constructor
      · rintro (rfl | rfl)
        · exact ⟨0, rfl⟩
        · exact ⟨1, rfl⟩
      · rintro ⟨i, rfl⟩
        fin_cases i
        · exact Or.inl rfl
        · exact Or.inr rfl
    · intro i j hadj
      have hne : i ≠ j := fun h => hadj.ne (congrArg v h)
      omega
  · have hpath_ab : IsIndexedPath H a b := by
      rcases hx₁ with rfl | rfl <;> rcases hx₂ with rfl | rfl
      · exact (hx₁₂ rfl).elim
      · exact hpath
      · exact hpath.symm
      · exact (hx₁₂ rfl).elim
    rcases hpath_ab with ⟨m, hm, v, hv_inj, hv0, hvm, hV, hadj⟩
    exact ⟨m, hm, v, hv_inj, hv0, hvm, hV, fun i j h => (hadj i j).mp h⟩
  · exact (not_two_distinct_in_pair_diff hv₀ hx₁ hx₂ hx₁₂).elim

/-- Every edge `e ∈ H.edgeSet` in a graph `H` with path-indexed vertices `v : Fin (m + 1) → α`
is either a loop at a single `i : Fin (m + 1)` (`H.ends e = {v i}`) or a link between consecutive
vertices `v i` and `v (i + 1)` for a unique `i : Fin m`. -/
theorem edge_ends_of_path_indexing {α : Type u} {β : Type v}
    {H : Hypergraph α β} (hH : H.IsGraph) {m : ℕ} (_hm : 1 ≤ m)
    {v : Fin (m + 1) → α} (_hv_inj : Function.Injective v) (hV : H.vertexSet = Set.range v)
    (hadj : ∀ i j : Fin (m + 1), H.skeleton.Adj (v i) (v j) → (i.1 + 1 = j.1 ∨ j.1 + 1 = i.1))
    {e : β} (he : e ∈ H.edgeSet) :
    (∃ i : Fin (m + 1), H.ends e = {v i}) ∨
    (∃ i : Fin m, H.ends e = {v ⟨i.1, by omega⟩, v ⟨i.1 + 1, by omega⟩}) := by
  obtain ⟨⟨w₁, hw₁⟩, hle2⟩ := hH e he
  have hw₁_V : w₁ ∈ H.vertexSet := H.vertex_mem_of_inc hw₁
  rw [hV] at hw₁_V
  rcases hw₁_V with ⟨i₁, rfl⟩
  by_cases h_all : ∀ w ∈ H.ends e, w = v i₁
  · left
    refine ⟨i₁, Subset.antisymm (fun w hw => ?_) (singleton_subset_iff.mpr hw₁)⟩
    exact mem_singleton_iff.mpr (h_all w hw)
  · right
    push Not at h_all
    rcases h_all with ⟨w₂, hw₂, hw₂_ne⟩
    have hw₂_V : w₂ ∈ H.vertexSet := H.vertex_mem_of_inc hw₂
    rw [hV] at hw₂_V
    rcases hw₂_V with ⟨i₂, rfl⟩
    have hfin_ends : (H.ends e).Finite :=
      H.vertexSet_finite.subset fun _ hw => H.vertex_mem_of_inc hw
    have hends_pair : H.ends e = {v i₁, v i₂} :=
      eq_pair_of_mem_of_ncard_le_two hfin_ends hle2 hw₁ hw₂ (Ne.symm hw₂_ne)
    have hadj_12 : H.skeleton.Adj (v i₁) (v i₂) := ⟨Ne.symm hw₂_ne, e, hw₁, hw₂⟩
    rcases hadj i₁ i₂ hadj_12 with h12 | h21
    · refine ⟨⟨i₁.1, by omega⟩, ?_⟩
      have hi₁_eq : (⟨i₁.1, by omega⟩ : Fin (m + 1)) = i₁ := Fin.ext rfl
      have hi₂_eq : (⟨i₁.1 + 1, by omega⟩ : Fin (m + 1)) = i₂ := Fin.ext h12
      rw [hends_pair, hi₁_eq, hi₂_eq]
    · refine ⟨⟨i₂.1, by omega⟩, ?_⟩
      have hi₂_eq : (⟨i₂.1, by omega⟩ : Fin (m + 1)) = i₂ := Fin.ext rfl
      have hi₁_eq : (⟨i₂.1 + 1, by omega⟩ : Fin (m + 1)) = i₁ := Fin.ext h21
      rw [hends_pair, hi₂_eq, hi₁_eq, pair_comm]

/-! ## 2. Complex Coordinates in the Unit Disc Relative to Two Boundary Points -/

private theorem norm_convex_combo_eq {z w : ℂ} (hz : ‖z‖ = 1) (hw : ‖w‖ = 1) (u : ℝ) :
    ‖(1 - (u : ℂ)) * z + (u : ℂ) * w‖ ^ 2 + u * (1 - u) * ‖z - w‖ ^ 2 = 1 := by
  have h1 : ∀ a : ℂ, ‖a‖ ^ 2 = a.re ^ 2 + a.im ^ 2 := fun a => by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    ring
  have hz2 : z.re ^ 2 + z.im ^ 2 = 1 := by rw [← h1 z, hz, one_pow]
  have hw2 : w.re ^ 2 + w.im ^ 2 = 1 := by rw [← h1 w, hw, one_pow]
  rw [h1, h1]
  simp only [Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im,
    Complex.mul_re, Complex.mul_im, Complex.one_re, Complex.one_im,
    Complex.ofReal_re, Complex.ofReal_im]
  linear_combination (1 - u) * hz2 + u * hw2

/-- Coordinate map `Φ(z₀, z₁)(s, y) = (1 - s) z₀ + s z₁ + y i (z₁ - z₀)` in `ℂ`. -/
noncomputable def discCoordC (z₀ z₁ : ℂ) (s y : ℝ) : ℂ :=
  (1 - (s : ℂ)) * z₀ + (s : ℂ) * z₁ + (y : ℂ) * Complex.I * (z₁ - z₀)

theorem discCoordC_eq_add_mul (z₀ z₁ : ℂ) (s y : ℝ) :
    discCoordC z₀ z₁ s y = z₀ + ((s : ℂ) + (y : ℂ) * Complex.I) * (z₁ - z₀) := by
  dsimp [discCoordC]
  ring

theorem discCoordC_zero_zero (z₀ z₁ : ℂ) : discCoordC z₀ z₁ 0 0 = z₀ := by
  dsimp [discCoordC]
  simp

theorem discCoordC_one_zero (z₀ z₁ : ℂ) : discCoordC z₀ z₁ 1 0 = z₁ := by
  dsimp [discCoordC]
  simp

theorem discCoordC_injective {z₀ z₁ : ℂ} (hne : z₀ ≠ z₁) {s₁ y₁ s₂ y₂ : ℝ}
    (h : discCoordC z₀ z₁ s₁ y₁ = discCoordC z₀ z₁ s₂ y₂) : s₁ = s₂ ∧ y₁ = y₂ := by
  rw [discCoordC_eq_add_mul, discCoordC_eq_add_mul] at h
  have hmul : ((s₁ : ℂ) + (y₁ : ℂ) * Complex.I) * (z₁ - z₀) =
      ((s₂ : ℂ) + (y₂ : ℂ) * Complex.I) * (z₁ - z₀) := add_left_cancel h
  have h_eq : (s₁ : ℂ) + (y₁ : ℂ) * Complex.I = (s₂ : ℂ) + (y₂ : ℂ) * Complex.I :=
    mul_right_cancel₀ (sub_ne_zero.mpr hne.symm) hmul
  have hre := congrArg Complex.re h_eq
  have him := congrArg Complex.im h_eq
  simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, mul_zero,
    Complex.ofReal_im, Complex.I_im, mul_one, sub_self, add_zero,
    Complex.add_im, Complex.mul_im, zero_add] at hre him
  exact ⟨hre, him⟩

/-- Key norm estimate for `discCoordC z₀ z₁ s y`: if `‖z₀‖ = 1`, `‖z₁‖ = 1`, `0 ≤ s ≤ 1`, and
`|y| ≤ (1 / 4) * s * (1 - s) * ‖z₁ - z₀‖`, then
`‖discCoordC z₀ z₁ s y‖ ≤ 1 - (1 / 4) * s * (1 - s) * ‖z₁ - z₀‖ ^ 2`. -/
theorem norm_discCoordC_le {z₀ z₁ : ℂ} (hz₀ : ‖z₀‖ = 1) (hz₁ : ‖z₁‖ = 1)
    {s y : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1)
    (hy : |y| ≤ (1 / 4) * s * (1 - s) * ‖z₁ - z₀‖) :
    ‖discCoordC z₀ z₁ s y‖ ≤ 1 - (1 / 4) * s * (1 - s) * ‖z₁ - z₀‖ ^ 2 := by
  set d := ‖z₁ - z₀‖
  have hd_nonneg : 0 ≤ d := norm_nonneg _
  have hd_le_two : d ≤ 2 := by
    calc ‖z₁ - z₀‖ ≤ ‖z₁‖ + ‖z₀‖ := norm_sub_le z₁ z₀
      _ = 2 := by rw [hz₁, hz₀]; norm_num
  have h_d_symm : ‖z₀ - z₁‖ = d := norm_sub_rev z₀ z₁
  let p : ℂ := (1 - (s : ℂ)) * z₀ + (s : ℂ) * z₁
  have hp_sq : ‖p‖ ^ 2 = 1 - s * (1 - s) * d ^ 2 := by
    have hid := norm_convex_combo_eq hz₀ hz₁ s
    rw [h_d_symm] at hid
    dsimp [p]
    linarith
  have hs_prod_le : s * (1 - s) ≤ 1 / 4 := by
    have : (s - 1 / 2) ^ 2 ≥ 0 := sq_nonneg (s - 1 / 2)
    nlinarith
  have hd2_le : d ^ 2 ≤ 4 := by nlinarith
  have h_term_le_one : s * (1 - s) * d ^ 2 ≤ 1 := by
    have hs_nonneg : 0 ≤ s * (1 - s) := mul_nonneg hs0 (sub_nonneg.mpr hs1)
    nlinarith
  have h_rhs_nonneg : 0 ≤ 1 - (1 / 2) * s * (1 - s) * d ^ 2 := by linarith
  have hp_le_sq : ‖p‖ ^ 2 ≤ (1 - (1 / 2) * s * (1 - s) * d ^ 2) ^ 2 := by
    have : 0 ≤ ((1 / 2) * s * (1 - s) * d ^ 2) ^ 2 := sq_nonneg _
    linarith
  have hp_le : ‖p‖ ≤ 1 - (1 / 2) * s * (1 - s) * d ^ 2 :=
    (abs_le_of_sq_le_sq' hp_le_sq h_rhs_nonneg).2
  have hq_norm : ‖(y : ℂ) * Complex.I * (z₁ - z₀)‖ = |y| * d := by
    rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_I, mul_one]
  have hyd_le : |y| * d ≤ (1 / 4) * s * (1 - s) * d ^ 2 := by
    calc |y| * d ≤ ((1 / 4) * s * (1 - s) * d) * d := mul_le_mul_of_nonneg_right hy hd_nonneg
      _ = (1 / 4) * s * (1 - s) * d ^ 2 := by ring
  calc ‖discCoordC z₀ z₁ s y‖
      = ‖p + (y : ℂ) * Complex.I * (z₁ - z₀)‖ := rfl
    _ ≤ ‖p‖ + ‖(y : ℂ) * Complex.I * (z₁ - z₀)‖ := norm_add_le _ _
    _ = ‖p‖ + |y| * d := by rw [hq_norm]
    _ ≤ 1 - (1 / 4) * s * (1 - s) * d ^ 2 := by linarith

theorem discCoordC_mem_closedBall {z₀ z₁ : ℂ} (hz₀ : ‖z₀‖ = 1) (hz₁ : ‖z₁‖ = 1)
    {s y : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1)
    (hy : |y| ≤ (1 / 4) * s * (1 - s) * ‖z₁ - z₀‖) :
    discCoordC z₀ z₁ s y ∈ closedBall (0 : ℂ) 1 := by
  rw [mem_closedBall_zero_iff]
  have h1 := norm_discCoordC_le hz₀ hz₁ hs0 hs1 hy
  have h2 : 0 ≤ (1 / 4) * s * (1 - s) * ‖z₁ - z₀‖ ^ 2 := by
    have : 0 ≤ 1 - s := sub_nonneg.mpr hs1
    positivity
  linarith

theorem discCoordC_not_mem_sphere {z₀ z₁ : ℂ} (hz₀ : ‖z₀‖ = 1) (hz₁ : ‖z₁‖ = 1)
    (hne : z₀ ≠ z₁) {s y : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
    (hy : |y| ≤ (1 / 4) * s * (1 - s) * ‖z₁ - z₀‖) :
    discCoordC z₀ z₁ s y ∉ sphere (0 : ℂ) 1 := by
  rw [mem_sphere_zero_iff_norm]
  have h1 := norm_discCoordC_le hz₀ hz₁ hs0.le hs1.le hy
  have hd_pos : 0 < ‖z₁ - z₀‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hne.symm)
  have h2 : 0 < (1 / 4) * s * (1 - s) * ‖z₁ - z₀‖ ^ 2 := by
    have : 0 < 1 - s := sub_pos.mpr hs1
    positivity
  linarith

/-! ## 3. Vertex, Link-Edge, and Loop-Edge Curves in a Single Closed Disc -/

/-- `s`-coordinate of vertex `i : Fin (m + 1)`. -/
noncomputable def sVert (m : ℕ) (i : Fin (m + 1)) : ℝ := (i.1 : ℝ) / (m : ℝ)

theorem sVert_zero (m : ℕ) : sVert m 0 = 0 := by simp [sVert]

theorem sVert_last {m : ℕ} (hm : 1 ≤ m) : sVert m ⟨m, Nat.lt_succ_self m⟩ = 1 := by
  have hm_ne : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  dsimp [sVert]
  exact div_self hm_ne

theorem sVert_nonneg (m : ℕ) (i : Fin (m + 1)) : 0 ≤ sVert m i := by
  dsimp [sVert]; positivity

theorem sVert_le_one (m : ℕ) (i : Fin (m + 1)) : sVert m i ≤ 1 := by
  dsimp [sVert]
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp
  · rw [div_le_one (Nat.cast_pos.mpr hm)]
    exact Nat.cast_le.mpr (Nat.lt_succ_iff.mp i.2)

theorem sVert_pos_of_ne_zero {m : ℕ} (hm : 1 ≤ m) {i : Fin (m + 1)} (hi : i ≠ 0) :
    0 < sVert m i := by
  have hi_pos : 0 < i.1 := Nat.pos_of_ne_zero (fun h => hi (Fin.ext h))
  dsimp [sVert]
  positivity

theorem sVert_lt_one_of_ne_last {m : ℕ} (hm : 1 ≤ m) {i : Fin (m + 1)}
    (hi : i ≠ ⟨m, Nat.lt_succ_self m⟩) : sVert m i < 1 := by
  have hi_lt : i.1 < m := Nat.lt_of_le_of_ne (Nat.lt_succ_iff.mp i.2) (fun h => hi (Fin.ext h))
  dsimp [sVert]
  rw [div_lt_one (Nat.cast_pos.mpr (by omega))]
  exact Nat.cast_lt.mpr hi_lt

theorem sVert_injective {m : ℕ} (hm : 1 ≤ m) : Function.Injective (sVert m) := by
  intro i j h
  have hm_ne : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have h1 : (i.1 : ℝ) = (j.1 : ℝ) := (div_left_inj' hm_ne).mp h
  exact Fin.ext (Nat.cast_injective h1)

/-- `s`-coordinate along a link edge between `i` and `i + 1` (`i : Fin m`). -/
noncomputable def sLink (m : ℕ) (i : Fin m) (t : 𝕀) : ℝ :=
  ((i.1 : ℝ) + (t : ℝ)) / (m : ℝ)

/-- `y`-coordinate along a link edge with index `k`. -/
noncomputable def yLink (z₀ z₁ : ℂ) (m K k : ℕ) (t : 𝕀) : ℝ :=
  (‖z₁ - z₀‖ / (8 * (m : ℝ) ^ 2)) * ((k : ℝ) / (K : ℝ)) * (t : ℝ) * (1 - (t : ℝ))

theorem sLink_zero (m : ℕ) (i : Fin m) :
    sLink m i 0 = sVert m ⟨i.1, Nat.lt_succ_of_lt i.2⟩ := by
  simp [sLink, sVert]

theorem sLink_one (m : ℕ) (i : Fin m) :
    sLink m i 1 = sVert m ⟨i.1 + 1, Nat.succ_lt_succ i.2⟩ := by
  simp [sLink, sVert]

theorem yLink_zero (z₀ z₁ : ℂ) (m K k : ℕ) : yLink z₀ z₁ m K k 0 = 0 := by
  simp [yLink]

theorem yLink_one (z₀ z₁ : ℂ) (m K k : ℕ) : yLink z₀ z₁ m K k 1 = 0 := by
  simp [yLink]

theorem sLink_bounds {m : ℕ} (hm : 1 ≤ m) (i : Fin m) (t : 𝕀) :
    0 ≤ sLink m i t ∧ sLink m i t ≤ 1 := by
  have hm_pos : (0 : ℝ) < m := Nat.cast_pos.mpr (by omega)
  have hi_le : (i.1 : ℝ) + 1 ≤ (m : ℝ) := by exact_mod_cast i.2
  have ht0 : 0 ≤ (t : ℝ) := t.2.1
  have ht1 : (t : ℝ) ≤ 1 := t.2.2
  dsimp [sLink]
  exact ⟨by positivity, (div_le_one hm_pos).mpr (by linarith)⟩

theorem sLink_interior {m : ℕ} (hm : 1 ≤ m) (i : Fin m) {t : 𝕀}
    (ht0 : 0 < (t : ℝ)) (ht1 : (t : ℝ) < 1) :
    0 < sLink m i t ∧ sLink m i t < 1 := by
  have hm_pos : (0 : ℝ) < m := Nat.cast_pos.mpr (by omega)
  have hi_le : (i.1 : ℝ) + 1 ≤ (m : ℝ) := by exact_mod_cast i.2
  have hi_nonneg : (0 : ℝ) ≤ i.1 := Nat.cast_nonneg _
  dsimp [sLink]
  exact ⟨div_pos (by linarith) hm_pos, (div_lt_one hm_pos).mpr (by linarith)⟩

theorem yLink_nonneg (z₀ z₁ : ℂ) (m K k : ℕ) (t : 𝕀) :
    0 ≤ yLink z₀ z₁ m K k t := by
  have ht0 : 0 ≤ (t : ℝ) := t.2.1
  have ht1 : 0 ≤ 1 - (t : ℝ) := sub_nonneg.mpr t.2.2
  dsimp [yLink]
  positivity

theorem yLink_pos {z₀ z₁ : ℂ} (hne : z₀ ≠ z₁) {m K k : ℕ}
    (hm : 1 ≤ m) (hK : 1 ≤ K) (hk : 1 ≤ k) {t : 𝕀}
    (ht0 : 0 < (t : ℝ)) (ht1 : (t : ℝ) < 1) :
    0 < yLink z₀ z₁ m K k t := by
  have hd_pos : 0 < ‖z₁ - z₀‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hne.symm)
  have hm_pos : (0 : ℝ) < m := Nat.cast_pos.mpr (by omega)
  have hK_pos : (0 : ℝ) < K := Nat.cast_pos.mpr (by omega)
  have hk_pos : (0 : ℝ) < k := Nat.cast_pos.mpr (by omega)
  have ht1' : 0 < 1 - (t : ℝ) := sub_pos.mpr ht1
  dsimp [yLink]
  positivity

theorem abs_yLink_le {z₀ z₁ : ℂ} {m K k : ℕ} (hm : 1 ≤ m) (hK : 1 ≤ K) (hk_le : k ≤ K)
    (i : Fin m) (t : 𝕀) :
    |yLink z₀ z₁ m K k t| ≤ (1 / 4) * sLink m i t * (1 - sLink m i t) * ‖z₁ - z₀‖ := by
  rw [abs_of_nonneg (yLink_nonneg z₀ z₁ m K k t)]
  have hm_pos : (0 : ℝ) < m := Nat.cast_pos.mpr (by omega)
  have hm_ne : (m : ℝ) ≠ 0 := hm_pos.ne'
  have hK_pos : (0 : ℝ) < K := Nat.cast_pos.mpr (by omega)
  have hkK_le : (k : ℝ) / (K : ℝ) ≤ 1 :=
    (div_le_one hK_pos).mpr (Nat.cast_le.mpr hk_le)
  have hi_le : (i.1 : ℝ) + 1 ≤ (m : ℝ) := by exact_mod_cast i.2
  have hi_nonneg : (0 : ℝ) ≤ i.1 := Nat.cast_nonneg _
  have ht0 : 0 ≤ (t : ℝ) := t.2.1
  have ht1 : (t : ℝ) ≤ 1 := t.2.2
  have hs1 : (t : ℝ) / (m : ℝ) ≤ sLink m i t := by
    dsimp [sLink]
    exact div_le_div_of_nonneg_right (by linarith) hm_pos.le
  have hs2 : (1 - (t : ℝ)) / (m : ℝ) ≤ 1 - sLink m i t := by
    have h_eq : 1 - sLink m i t = ((m : ℝ) - (i.1 : ℝ) - (t : ℝ)) / (m : ℝ) := by
      dsimp [sLink]; field_simp; ring
    rw [h_eq]
    exact div_le_div_of_nonneg_right (by linarith) hm_pos.le
  have hprod : ((t : ℝ) * (1 - (t : ℝ))) / (m : ℝ) ^ 2 ≤ sLink m i t * (1 - sLink m i t) := by
    calc ((t : ℝ) * (1 - (t : ℝ))) / (m : ℝ) ^ 2
        = ((t : ℝ) / (m : ℝ)) * ((1 - (t : ℝ)) / (m : ℝ)) := by ring
      _ ≤ sLink m i t * (1 - sLink m i t) :=
          mul_le_mul hs1 hs2 (by positivity) (sLink_bounds hm i t).1
  have hd_nonneg : 0 ≤ ‖z₁ - z₀‖ := norm_nonneg _
  calc yLink z₀ z₁ m K k t
      = (1 / 8) * ((k : ℝ) / (K : ℝ)) * (((t : ℝ) * (1 - (t : ℝ))) / (m : ℝ) ^ 2) * ‖z₁ - z₀‖ := by
        dsimp [yLink]; ring
    _ ≤ (1 / 8) * 1 * (sLink m i t * (1 - sLink m i t)) * ‖z₁ - z₀‖ := by
        refine mul_le_mul_of_nonneg_right ?_ hd_nonneg
        refine mul_le_mul ?_ hprod (by positivity) (by positivity)
        linarith
    _ ≤ (1 / 4) * sLink m i t * (1 - sLink m i t) * ‖z₁ - z₀‖ := by
        have h_s_nonneg : 0 ≤ sLink m i t * (1 - sLink m i t) * ‖z₁ - z₀‖ := by
          have hb0 : 0 ≤ sLink m i t := (sLink_bounds hm i t).1
          have hb1 : 0 ≤ 1 - sLink m i t := sub_nonneg.mpr (sLink_bounds hm i t).2
          positivity
        linarith

/-- Direction sign for loop edges at vertex `i : Fin (m + 1)`. -/
def loopDir {m : ℕ} (i : Fin (m + 1)) : ℝ := if i.1 = 0 then 1 else -1

/-- `s`-coordinate along a loop edge at `i : Fin (m + 1)`. -/
noncomputable def sLoop (m : ℕ) (i : Fin (m + 1)) (z : Circle) : ℝ :=
  ((i.1 : ℝ) + loopDir i * (1 - (z : ℂ).re) / 8) / (m : ℝ)

/-- `y`-coordinate along a loop edge with index `k`. -/
noncomputable def yLoop (z₀ z₁ : ℂ) (m K k : ℕ) (z : Circle) : ℝ :=
  -(‖z₁ - z₀‖ / (256 * (m : ℝ) ^ 2 * (K : ℝ))) * (1 - (z : ℂ).re) * (4 * (k : ℝ) + (z : ℂ).im)

theorem circle_re_sq_add_im_sq (z : Circle) : (z : ℂ).re ^ 2 + (z : ℂ).im ^ 2 = 1 := by
  have h1 : ‖(z : ℂ)‖ = 1 := mem_sphere_zero_iff_norm.mp z.2
  have h2 : ‖(z : ℂ)‖ ^ 2 = (z : ℂ).re ^ 2 + (z : ℂ).im ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]; ring
  rw [← h2, h1, one_pow]

theorem circle_re_bounds (z : Circle) : -1 ≤ (z : ℂ).re ∧ (z : ℂ).re ≤ 1 := by
  have h := circle_re_sq_add_im_sq z
  have him : 0 ≤ (z : ℂ).im ^ 2 := sq_nonneg _
  have hsq : (z : ℂ).re ^ 2 ≤ 1 ^ 2 := by linarith
  exact abs_le_of_sq_le_sq' hsq zero_le_one

theorem circle_im_bounds (z : Circle) : -1 ≤ (z : ℂ).im ∧ (z : ℂ).im ≤ 1 := by
  have h := circle_re_sq_add_im_sq z
  have hre : 0 ≤ (z : ℂ).re ^ 2 := sq_nonneg _
  have hsq : (z : ℂ).im ^ 2 ≤ 1 ^ 2 := by linarith
  exact abs_le_of_sq_le_sq' hsq zero_le_one

theorem circle_re_eq_one_iff (z : Circle) : (z : ℂ).re = 1 ↔ z = 1 := by
  constructor
  · intro hre
    have h := circle_re_sq_add_im_sq z
    rw [hre] at h
    have him2 : (z : ℂ).im ^ 2 = 0 := by linarith
    have him : (z : ℂ).im = 0 := sq_eq_zero_iff.mp him2
    apply Subtype.ext
    exact Complex.ext (by simpa using hre) (by simpa using him)
  · rintro rfl
    rfl

theorem circle_one_sub_re_pos_iff (z : Circle) : 0 < 1 - (z : ℂ).re ↔ z ≠ 1 := by
  constructor
  · intro h hz
    subst hz
    simp at h
  · intro hz
    have hle := (circle_re_bounds z).2
    have hne : (z : ℂ).re ≠ 1 := mt (circle_re_eq_one_iff z).mp hz
    exact sub_pos.mpr (lt_of_le_of_ne hle hne)

theorem sLoop_one (m : ℕ) (i : Fin (m + 1)) : sLoop m i 1 = sVert m i := by
  simp [sLoop, sVert]

theorem yLoop_one (z₀ z₁ : ℂ) (m K k : ℕ) : yLoop z₀ z₁ m K k 1 = 0 := by
  simp [yLoop]

theorem yLoop_nonpos {z₀ z₁ : ℂ} {m K k : ℕ} (hk : 1 ≤ k) (z : Circle) :
    yLoop z₀ z₁ m K k z ≤ 0 := by
  have hre : 0 ≤ 1 - (z : ℂ).re := by linarith [(circle_re_bounds z).2]
  have him : 0 ≤ 4 * (k : ℝ) + (z : ℂ).im := by
    have hk' : (1 : ℝ) ≤ k := Nat.one_le_cast.mpr hk
    linarith [(circle_im_bounds z).1]
  have hpos : 0 ≤ (‖z₁ - z₀‖ / (256 * (m : ℝ) ^ 2 * (K : ℝ))) * (1 - (z : ℂ).re) *
      (4 * (k : ℝ) + (z : ℂ).im) := by positivity
  dsimp [yLoop]
  linarith

theorem yLoop_neg {z₀ z₁ : ℂ} (hne : z₀ ≠ z₁) {m K k : ℕ}
    (hm : 1 ≤ m) (hK : 1 ≤ K) (hk : 1 ≤ k) {z : Circle} (hz : z ≠ 1) :
    yLoop z₀ z₁ m K k z < 0 := by
  have hd_pos : 0 < ‖z₁ - z₀‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hne.symm)
  have hm_pos : (0 : ℝ) < m := Nat.cast_pos.mpr (by omega)
  have hK_pos : (0 : ℝ) < K := Nat.cast_pos.mpr (by omega)
  have hre_pos : 0 < 1 - (z : ℂ).re := (circle_one_sub_re_pos_iff z).mpr hz
  have him_pos : 0 < 4 * (k : ℝ) + (z : ℂ).im := by
    have hk' : (1 : ℝ) ≤ k := Nat.one_le_cast.mpr hk
    linarith [(circle_im_bounds z).1]
  have hpos : 0 < (‖z₁ - z₀‖ / (256 * (m : ℝ) ^ 2 * (K : ℝ))) * (1 - (z : ℂ).re) *
      (4 * (k : ℝ) + (z : ℂ).im) := by positivity
  dsimp [yLoop]
  linarith

theorem sLoop_bounds_and_prod {m : ℕ} (hm : 1 ≤ m) (i : Fin (m + 1)) (z : Circle) :
    0 ≤ sLoop m i z ∧ sLoop m i z ≤ 1 ∧
      (3 / (32 * (m : ℝ) ^ 2)) * (1 - (z : ℂ).re) ≤ sLoop m i z * (1 - sLoop m i z) := by
  have hm_pos : (0 : ℝ) < m := Nat.cast_pos.mpr (by omega)
  have hm_ne : (m : ℝ) ≠ 0 := hm_pos.ne'
  have hm_ge1 : (1 : ℝ) ≤ m := Nat.one_le_cast.mpr hm
  have hre_bounds := circle_re_bounds z
  set δ := (1 - (z : ℂ).re) / 8
  have hδ0 : 0 ≤ δ := by dsimp [δ]; linarith [hre_bounds.2]
  have hδ1 : δ ≤ 1 / 4 := by dsimp [δ]; linarith [hre_bounds.1]
  by_cases hi0 : i.1 = 0
  · have h_dir : loopDir i = 1 := by simp [loopDir, hi0]
    have hs_eq : sLoop m i z = δ / (m : ℝ) := by
      dsimp [sLoop, δ]; rw [hi0, h_dir]; ring
    have h1_sub : 1 - sLoop m i z = ((m : ℝ) - δ) / (m : ℝ) := by
      rw [hs_eq]; field_simp
    refine ⟨by rw [hs_eq]; positivity, ?_, ?_⟩
    · rw [hs_eq]
      exact (div_le_one hm_pos).mpr (by linarith)
    rw [h1_sub, hs_eq]
    have h_num : (3 / 4) * δ ≤ δ * ((m : ℝ) - δ) := by nlinarith
    have h_lhs : (3 / (32 * (m : ℝ) ^ 2)) * (1 - (z : ℂ).re) = ((3 / 4) * δ) / (m : ℝ) ^ 2 := by
      dsimp [δ]; ring
    have h_rhs : (δ / (m : ℝ)) * (((m : ℝ) - δ) / (m : ℝ)) = (δ * ((m : ℝ) - δ)) / (m : ℝ) ^ 2 := by
      ring
    rw [h_lhs, h_rhs]
    exact div_le_div_of_nonneg_right h_num (sq_nonneg _)
  · have h_dir : loopDir i = -1 := by simp [loopDir, hi0]
    have hi_ge1 : (1 : ℝ) ≤ i.1 := by
      have : 1 ≤ i.1 := Nat.pos_of_ne_zero hi0
      exact_mod_cast this
    have hi_le_m : (i.1 : ℝ) ≤ m := by exact_mod_cast (Nat.lt_succ_iff.mp i.2)
    have hs_eq : sLoop m i z = ((i.1 : ℝ) - δ) / (m : ℝ) := by
      dsimp [sLoop, δ]; rw [h_dir]; ring
    have h1_sub : 1 - sLoop m i z = ((m : ℝ) - (i.1 : ℝ) + δ) / (m : ℝ) := by
      rw [hs_eq]; field_simp; ring
    refine ⟨by rw [hs_eq]; exact div_nonneg (by linarith) hm_pos.le,
      by rw [hs_eq]; exact (div_le_one hm_pos).mpr (by linarith), ?_⟩
    rw [h1_sub, hs_eq]
    have h_num : (3 / 4) * δ ≤ ((i.1 : ℝ) - δ) * ((m : ℝ) - (i.1 : ℝ) + δ) := by nlinarith
    have h_lhs : (3 / (32 * (m : ℝ) ^ 2)) * (1 - (z : ℂ).re) = ((3 / 4) * δ) / (m : ℝ) ^ 2 := by
      dsimp [δ]; ring
    have h_rhs : (((i.1 : ℝ) - δ) / (m : ℝ)) * (((m : ℝ) - (i.1 : ℝ) + δ) / (m : ℝ)) =
        (((i.1 : ℝ) - δ) * ((m : ℝ) - (i.1 : ℝ) + δ)) / (m : ℝ) ^ 2 := by ring
    rw [h_lhs, h_rhs]
    exact div_le_div_of_nonneg_right h_num (sq_nonneg _)

theorem sLoop_interior {m : ℕ} (hm : 1 ≤ m) (i : Fin (m + 1)) {z : Circle} (hz : z ≠ 1) :
    0 < sLoop m i z ∧ sLoop m i z < 1 := by
  have hm_pos : (0 : ℝ) < m := Nat.cast_pos.mpr (by omega)
  have hm_ge1 : (1 : ℝ) ≤ m := Nat.one_le_cast.mpr hm
  have hre_pos : 0 < 1 - (z : ℂ).re := (circle_one_sub_re_pos_iff z).mpr hz
  have hre_le : 1 - (z : ℂ).re ≤ 2 := by linarith [(circle_re_bounds z).1]
  by_cases hi0 : i.1 = 0
  · have h_dir : loopDir i = 1 := by simp [loopDir, hi0]
    dsimp [sLoop]
    rw [hi0, h_dir]
    exact ⟨div_pos (by linarith) hm_pos, (div_lt_one hm_pos).mpr (by linarith)⟩
  · have h_dir : loopDir i = -1 := by simp [loopDir, hi0]
    have hi_ge1 : (1 : ℝ) ≤ i.1 := by
      have : 1 ≤ i.1 := Nat.pos_of_ne_zero hi0
      exact_mod_cast this
    have hi_le_m : (i.1 : ℝ) ≤ m := by exact_mod_cast (Nat.lt_succ_iff.mp i.2)
    dsimp [sLoop]
    rw [h_dir]
    exact ⟨div_pos (by linarith) hm_pos, (div_lt_one hm_pos).mpr (by linarith)⟩

theorem abs_yLoop_le {z₀ z₁ : ℂ} {m K k : ℕ} (hm : 1 ≤ m) (hK : 1 ≤ K)
    (hk : 1 ≤ k) (hk_le : k ≤ K) (i : Fin (m + 1)) (z : Circle) :
    |yLoop z₀ z₁ m K k z| ≤ (1 / 4) * sLoop m i z * (1 - sLoop m i z) * ‖z₁ - z₀‖ := by
  rw [abs_of_nonpos (yLoop_nonpos hk z)]
  have hm_pos : (0 : ℝ) < m := Nat.cast_pos.mpr (by omega)
  have hK_pos : (0 : ℝ) < K := Nat.cast_pos.mpr (by omega)
  have hK_ge1 : (1 : ℝ) ≤ K := Nat.one_le_cast.mpr hK
  have hk_le' : (k : ℝ) ≤ K := Nat.cast_le.mpr hk_le
  have him_le : 4 * (k : ℝ) + (z : ℂ).im ≤ 5 * (K : ℝ) := by
    linarith [(circle_im_bounds z).2]
  have hre_nonneg : 0 ≤ 1 - (z : ℂ).re := by linarith [(circle_re_bounds z).2]
  have hd_nonneg : 0 ≤ ‖z₁ - z₀‖ := norm_nonneg _
  have hprod := (sLoop_bounds_and_prod hm i z).2.2
  have h_step1 : -yLoop z₀ z₁ m K k z ≤
      (5 / (256 * (m : ℝ) ^ 2)) * (1 - (z : ℂ).re) * ‖z₁ - z₀‖ := by
    have h_eq : -yLoop z₀ z₁ m K k z =
        (‖z₁ - z₀‖ / (256 * (m : ℝ) ^ 2)) * (1 - (z : ℂ).re) *
          ((4 * (k : ℝ) + (z : ℂ).im) / (K : ℝ)) := by
      dsimp [yLoop]; ring
    rw [h_eq]
    have h_div : (4 * (k : ℝ) + (z : ℂ).im) / (K : ℝ) ≤ 5 :=
      (div_le_iff₀ hK_pos).mpr him_le
    have h_fac : 0 ≤ (‖z₁ - z₀‖ / (256 * (m : ℝ) ^ 2)) * (1 - (z : ℂ).re) := by positivity
    calc (‖z₁ - z₀‖ / (256 * (m : ℝ) ^ 2)) * (1 - (z : ℂ).re) * ((4 * (k : ℝ) + (z : ℂ).im) / (K : ℝ))
        ≤ (‖z₁ - z₀‖ / (256 * (m : ℝ) ^ 2)) * (1 - (z : ℂ).re) * 5 :=
          mul_le_mul_of_nonneg_left h_div h_fac
      _ = (5 / (256 * (m : ℝ) ^ 2)) * (1 - (z : ℂ).re) * ‖z₁ - z₀‖ := by ring
  have h_step2 : (5 / (256 * (m : ℝ) ^ 2)) * (1 - (z : ℂ).re) ≤
      (1 / 4) * ((3 / (32 * (m : ℝ) ^ 2)) * (1 - (z : ℂ).re)) := by
    have h_lhs : (5 / (256 * (m : ℝ) ^ 2)) * (1 - (z : ℂ).re) =
        5 * ((1 - (z : ℂ).re) / (256 * (m : ℝ) ^ 2)) := by ring
    have h_rhs : (1 / 4) * ((3 / (32 * (m : ℝ) ^ 2)) * (1 - (z : ℂ).re)) =
        6 * ((1 - (z : ℂ).re) / (256 * (m : ℝ) ^ 2)) := by ring
    have h_c : 0 ≤ (1 - (z : ℂ).re) / (256 * (m : ℝ) ^ 2) := by positivity
    rw [h_lhs, h_rhs]
    linarith
  have h_step3 : (1 / 4) * ((3 / (32 * (m : ℝ) ^ 2)) * (1 - (z : ℂ).re)) ≤
      (1 / 4) * (sLoop m i z * (1 - sLoop m i z)) := by linarith
  have h_comb : (5 / (256 * (m : ℝ) ^ 2)) * (1 - (z : ℂ).re) ≤
      (1 / 4) * sLoop m i z * (1 - sLoop m i z) := by linarith
  exact h_step1.trans (mul_le_mul_of_nonneg_right h_comb hd_nonneg)

theorem sLoop_close_to_i {m : ℕ} (hm : 1 ≤ m) (i : Fin (m + 1)) (z : Circle) :
    |(m : ℝ) * sLoop m i z - (i.1 : ℝ)| ≤ 1 / 4 := by
  have hm_ne : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have h_eq : (m : ℝ) * sLoop m i z - (i.1 : ℝ) = loopDir i * (1 - (z : ℂ).re) / 8 := by
    dsimp [sLoop]; field_simp; ring
  rw [h_eq, abs_le]
  have hre := circle_re_bounds z
  by_cases hi0 : i.1 = 0 <;> simp [loopDir, hi0] <;> constructor <;> linarith

theorem loop_params_inj {z₀ z₁ : ℂ} (hne : z₀ ≠ z₁) {m K : ℕ} (hm : 1 ≤ m) (hK : 1 ≤ K)
    {i₁ i₂ : Fin (m + 1)} {k₁ k₂ : ℕ} {z₁' z₂' : Circle}
    (hs : sLoop m i₁ z₁' = sLoop m i₂ z₂')
    (hy : yLoop z₀ z₁ m K k₁ z₁' = yLoop z₀ z₁ m K k₂ z₂') :
    i₁ = i₂ ∧ (z₁' ≠ 1 → k₁ = k₂) ∧ (k₁ = k₂ → z₁' = z₂') := by
  have hm_ne : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hc1 := abs_le.mp (sLoop_close_to_i hm i₁ z₁')
  have hc2 := abs_le.mp (sLoop_close_to_i hm i₂ z₂')
  have h_diff : |(i₁.1 : ℝ) - (i₂.1 : ℝ)| ≤ 1 / 2 := by
    rw [hs] at hc1
    rw [abs_le]
    constructor <;> linarith
  have hi_eq : i₁ = i₂ := by
    by_contra hne_i
    rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hne_i) with hlt | hgt
    · have : (i₁.1 : ℝ) + 1 ≤ (i₂.1 : ℝ) := by exact_mod_cast hlt
      linarith [(abs_le.mp h_diff).1]
    · have : (i₂.1 : ℝ) + 1 ≤ (i₁.1 : ℝ) := by exact_mod_cast hgt
      linarith [(abs_le.mp h_diff).2]
  subst hi_eq
  have hdir_ne : loopDir i₁ ≠ 0 := by
    by_cases h0 : i₁.1 = 0 <;> simp [loopDir, h0]
  have hre_eq : (z₁' : ℂ).re = (z₂' : ℂ).re := by
    dsimp [sLoop] at hs
    have h1 := (div_left_inj' hm_ne).mp hs
    have h2 : loopDir i₁ * (1 - (z₁' : ℂ).re) = loopDir i₁ * (1 - (z₂' : ℂ).re) := by linarith
    have h3 := mul_left_cancel₀ hdir_ne h2
    linarith
  have hd_pos : 0 < ‖z₁ - z₀‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hne.symm)
  have hm_pos : (0 : ℝ) < m := Nat.cast_pos.mpr (by omega)
  have hK_pos : (0 : ℝ) < K := Nat.cast_pos.mpr (by omega)
  have hfac_pos : 0 < ‖z₁ - z₀‖ / (256 * (m : ℝ) ^ 2 * (K : ℝ)) := by positivity
  have hfac_ne : -(‖z₁ - z₀‖ / (256 * (m : ℝ) ^ 2 * (K : ℝ))) ≠ 0 := neg_ne_zero.mpr hfac_pos.ne'
  refine ⟨rfl, ?_, ?_⟩
  · intro hz₁_ne
    have h1_re_ne : 1 - (z₁' : ℂ).re ≠ 0 :=
      ((circle_one_sub_re_pos_iff z₁').mpr hz₁_ne).ne'
    dsimp [yLoop] at hy
    rw [← hre_eq] at hy
    have h_im_k : 4 * (k₁ : ℝ) + (z₁' : ℂ).im = 4 * (k₂ : ℝ) + (z₂' : ℂ).im := by
      apply mul_left_cancel₀ h1_re_ne
      apply mul_left_cancel₀ hfac_ne
      linarith
    have him1 := circle_im_bounds z₁'
    have him2 := circle_im_bounds z₂'
    by_contra hk_ne
    rcases lt_or_gt_of_ne hk_ne with hlt | hgt
    · have : (k₁ : ℝ) + 1 ≤ (k₂ : ℝ) := by exact_mod_cast hlt
      linarith
    · have : (k₂ : ℝ) + 1 ≤ (k₁ : ℝ) := by exact_mod_cast hgt
      linarith
  · intro hk_eq
    subst hk_eq
    by_cases hz₁_1 : z₁' = 1
    · subst hz₁_1
      have hz₂_re : (z₂' : ℂ).re = 1 := hre_eq.symm.trans rfl
      exact ((circle_re_eq_one_iff z₂').mp hz₂_re).symm
    · have h1_re_ne : 1 - (z₁' : ℂ).re ≠ 0 :=
        ((circle_one_sub_re_pos_iff z₁').mpr hz₁_1).ne'
      dsimp [yLoop] at hy
      rw [← hre_eq] at hy
      have h_im_k : 4 * (k₁ : ℝ) + (z₁' : ℂ).im = 4 * (k₁ : ℝ) + (z₂' : ℂ).im := by
        apply mul_left_cancel₀ h1_re_ne
        apply mul_left_cancel₀ hfac_ne
        linarith
      have him_eq : (z₁' : ℂ).im = (z₂' : ℂ).im := by linarith
      exact Subtype.ext (Complex.ext hre_eq him_eq)

/-- `({1}ᶜ : Set Circle)` is dense in `Circle`: `closure ({1}ᶜ : Set Circle) = univ`. -/
theorem closure_compl_singleton_one_circle : closure ({1}ᶜ : Set Circle) = univ := by
  ext z
  simp only [mem_univ, iff_true]
  by_cases hz : z = 1
  · subst hz
    have h0_cl : (0 : ℝ) ∈ closure (Ioo (0 : ℝ) 1) := by
      rw [closure_Ioo (zero_ne_one : (0 : ℝ) ≠ 1)]
      exact ⟨le_rfl, zero_le_one⟩
    have h1_img : (1 : Circle) ∈ Circle.exp '' closure (Ioo (0 : ℝ) 1) :=
      ⟨0, h0_cl, Circle.exp_zero⟩
    have h_sub : Circle.exp '' Ioo (0 : ℝ) 1 ⊆ ({1}ᶜ : Set Circle) := by
      rintro _ ⟨t, ⟨ht0, ht1⟩, rfl⟩ h_eq
      have ht_2pi : t < 2 * Real.pi := by linarith [Real.two_le_pi]
      have h_ang := angleDiff_exp_mul (v := (1 : Circle)) ht0 ht_2pi
      rw [mul_one, h_eq] at h_ang
      have h_zero : (1 : Circle).angleDiff 1 = 0 := by simp [Circle.angleDiff]
      linarith
    exact closure_mono h_sub (image_closure_subset_closure_image Circle.exp.continuous h1_img)
  · exact subset_closure hz

theorem link_params_inj {z₀ z₁ : ℂ} (hne : z₀ ≠ z₁) {m K : ℕ} (hm : 1 ≤ m) (hK : 1 ≤ K)
    {i₁ i₂ : Fin m} {k₁ k₂ : ℕ} {t₁ t₂ : 𝕀}
    (hs : sLink m i₁ t₁ = sLink m i₂ t₂)
    (hy : yLink z₀ z₁ m K k₁ t₁ = yLink z₀ z₁ m K k₂ t₂) :
    (i₁ = i₂ → t₁ = t₂) ∧
    (0 < (t₁ : ℝ) → (t₁ : ℝ) < 1 → 0 < (t₂ : ℝ) → (t₂ : ℝ) < 1 →
      i₁ = i₂ ∧ t₁ = t₂ ∧ k₁ = k₂) := by
  have hm_ne : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have h_sum : (i₁.1 : ℝ) + (t₁ : ℝ) = (i₂.1 : ℝ) + (t₂ : ℝ) := (div_left_inj' hm_ne).mp hs
  have h_t_of_i : i₁ = i₂ → t₁ = t₂ := fun hi => by
    subst hi
    exact Subtype.ext (by linarith)
  refine ⟨h_t_of_i, fun ht₁0 ht₁1 ht₂0 ht₂1 => ?_⟩
  have hi_eq : i₁ = i₂ := by
    by_contra hne_i
    rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hne_i) with hlt | hgt
    · have : (i₁.1 : ℝ) + 1 ≤ (i₂.1 : ℝ) := by exact_mod_cast hlt
      linarith
    · have : (i₂.1 : ℝ) + 1 ≤ (i₁.1 : ℝ) := by exact_mod_cast hgt
      linarith
  have ht_eq : t₁ = t₂ := h_t_of_i hi_eq
  subst hi_eq ht_eq
  refine ⟨rfl, rfl, ?_⟩
  have hd_pos : 0 < ‖z₁ - z₀‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hne.symm)
  have hm_pos : (0 : ℝ) < m := Nat.cast_pos.mpr (by omega)
  have hK_pos : (0 : ℝ) < K := Nat.cast_pos.mpr (by omega)
  have ht₁1' : 0 < 1 - (t₁ : ℝ) := sub_pos.mpr ht₁1
  have h_fac1 : (‖z₁ - z₀‖ / (8 * (m : ℝ) ^ 2)) ≠ 0 := by positivity
  have h_fac2 : (t₁ : ℝ) * (1 - (t₁ : ℝ)) ≠ 0 := by positivity
  dsimp [yLink] at hy
  have h_kK : (k₁ : ℝ) / (K : ℝ) = (k₂ : ℝ) / (K : ℝ) := by
    have h1 : (‖z₁ - z₀‖ / (8 * (m : ℝ) ^ 2)) * ((k₁ : ℝ) / (K : ℝ)) * ((t₁ : ℝ) * (1 - (t₁ : ℝ))) =
        (‖z₁ - z₀‖ / (8 * (m : ℝ) ^ 2)) * ((k₂ : ℝ) / (K : ℝ)) * ((t₁ : ℝ) * (1 - (t₁ : ℝ))) := by
      linarith
    exact mul_left_cancel₀ h_fac1 (mul_right_cancel₀ h_fac2 h1)
  have hk_real : (k₁ : ℝ) = (k₂ : ℝ) := (div_left_inj' hK_pos.ne').mp h_kK
  exact Nat.cast_injective hk_real

/-! ## 4. Single-Disc Drawing of a Cell Subgraph `H = α(c)` -/

/-- Specification of a drawing of `H` inside a closed disc `D` with boundary terminals `u₁, u₂`
representing `v₁, v₂`. -/
structure IsCellDiscDrawing {α : Type u} {β : Type v} {S : Type} [TopologicalSpace S]
    (D : Set S) (u₁ u₂ : S) (H : Hypergraph α β) (v₁ v₂ : α)
    (V_D : Set S) (ιV_D : S → α)
    (closedEdge_D openEdge_D : β → Set S) : Prop where
  u₁_mem : u₁ ∈ V_D
  u₂_mem : u₂ ∈ V_D
  V_subset_D : V_D ⊆ D
  V_finite : V_D.Finite
  V_inter_discBd : V_D ∩ discBd D = {u₁, u₂}
  ιV_u₁ : ιV_D u₁ = v₁
  ιV_u₂ : ιV_D u₂ = v₂
  ιV_injOn : InjOn ιV_D V_D
  ιV_image : ιV_D '' V_D = H.vertexSet
  closedEdge_isClosed : ∀ e ∈ H.edgeSet, IsClosed (closedEdge_D e)
  closedEdge_subset_D : ∀ e ∈ H.edgeSet, closedEdge_D e ⊆ D
  openEdge_eq_diff : ∀ e ∈ H.edgeSet, openEdge_D e = closedEdge_D e \ V_D
  openEdge_subset_int : ∀ e ∈ H.edgeSet, openEdge_D e ⊆ D \ discBd D
  closure_openEdge : ∀ e ∈ H.edgeSet, closure (openEdge_D e) = closedEdge_D e
  openEdge_nonempty : ∀ e ∈ H.edgeSet, (openEdge_D e).Nonempty
  openEdge_isPathConnected : ∀ e ∈ H.edgeSet, IsPathConnected (openEdge_D e)
  edge_cond : ∀ e ∈ H.edgeSet,
    (∃ x y : S, x ≠ y ∧ closedEdge_D e ∩ V_D = {x, y} ∧ IsLineWithEnds (closedEdge_D e) x y) ∨
    (∃ x : S, closedEdge_D e ∩ V_D = {x} ∧ IsOArc (closedEdge_D e))
  inc_iff : ∀ e ∈ H.edgeSet, ∀ u ∈ V_D, H.Inc e (ιV_D u) ↔ u ∈ closedEdge_D e
  openEdge_disjoint : ∀ e₁ ∈ H.edgeSet, ∀ e₂ ∈ H.edgeSet, e₁ ≠ e₂ →
    Disjoint (openEdge_D e₁) (openEdge_D e₂)

/-- Given a closed disc `D`, distinct boundary points `u₁, u₂ ∈ discBd D`, and a graph `H`
satisfying `CanBeDrawnInDisc21 H {v₁, v₂}` (`v₁ ≠ v₂`), `H` can be drawn in `D` meeting `discBd D`
only in `{u₁, u₂}` with `u₁, u₂` representing `v₁, v₂`. -/
theorem exists_cell_disc_drawing {α : Type u} {β : Type v} {S : Type}
    [TopologicalSpace S] [T2Space S]
    {D : Set S} (hD : IsClosedDisc D)
    {u₁ u₂ : S} (hu₁ : u₁ ∈ discBd D) (hu₂ : u₂ ∈ discBd D) (hu₁₂ : u₁ ≠ u₂)
    {H : Hypergraph α β} (hH : H.IsGraph)
    {v₁ v₂ : α} (hv₁₂ : v₁ ≠ v₂)
    (hdraw : CanBeDrawnInDisc21 H {v₁, v₂}) (x₀ : α) :
    ∃ (V_D : Set S) (ιV_D : S → α) (closedEdge_D openEdge_D : β → Set S),
      IsCellDiscDrawing D u₁ u₂ H v₁ v₂ V_D ιV_D closedEdge_D openEdge_D := by
  obtain ⟨m, hm, v, hv_inj, hv0, hvm, hV, hadj⟩ :=
    exists_path_indexing_of_canBeDrawnInDisc21 hv₁₂ hdraw
  obtain ⟨h, g, c⟩ := hD.exists_isChart
  have hu₁_D : u₁ ∈ D := discBd_subset D hu₁
  have hu₂_D : u₂ ∈ D := discBd_subset D hu₂
  set z₀ := h u₁
  set z₁ := h u₂
  have hz₀_sph : z₀ ∈ sphere (0 : ℂ) 1 := by rw [← c.bd]; exact mem_image_of_mem h hu₁
  have hz₁_sph : z₁ ∈ sphere (0 : ℂ) 1 := by rw [← c.bd]; exact mem_image_of_mem h hu₂
  have hz₀ : ‖z₀‖ = 1 := mem_sphere_zero_iff_norm.mp hz₀_sph
  have hz₁ : ‖z₁‖ = 1 := mem_sphere_zero_iff_norm.mp hz₁_sph
  have hz_ne : z₀ ≠ z₁ := fun hEq => hu₁₂ (c.gh.injOn hu₁_D hu₂_D hEq)
  -- Vertex points in D
  let ptC : Fin (m + 1) → ℂ := fun i => discCoordC z₀ z₁ (sVert m i) 0
  have hptC_ball : ∀ i : Fin (m + 1), ptC i ∈ closedBall (0 : ℂ) 1 := fun i =>
    discCoordC_mem_closedBall hz₀ hz₁ (sVert_nonneg m i) (sVert_le_one m i) (by
      have : 0 ≤ 1 - sVert m i := sub_nonneg.mpr (sVert_le_one m i)
      have : 0 ≤ sVert m i := sVert_nonneg m i
      simp; positivity)
  let pt : Fin (m + 1) → S := fun i => g (ptC i)
  have hpt_D : ∀ i : Fin (m + 1), pt i ∈ D := fun i => c.gm (hptC_ball i)
  have hpt_0 : pt 0 = u₁ := by
    show g (discCoordC z₀ z₁ (sVert m 0) 0) = u₁
    rw [sVert_zero, discCoordC_zero_zero]
    exact c.gh hu₁_D
  have hpt_m : pt ⟨m, Nat.lt_succ_self m⟩ = u₂ := by
    show g (discCoordC z₀ z₁ (sVert m ⟨m, Nat.lt_succ_self m⟩) 0) = u₂
    rw [sVert_last hm, discCoordC_one_zero]
    exact c.gh hu₂_D
  have hpt_inj : Function.Injective pt := fun i j hEq => by
    have hC := c.injOn (hptC_ball i) (hptC_ball j) hEq
    exact sVert_injective hm (discCoordC_injective hz_ne hC).1
  have hpt_bd : ∀ i : Fin (m + 1), pt i ∈ discBd D ↔ (i = 0 ∨ i = ⟨m, Nat.lt_succ_self m⟩) := by
    intro i
    constructor
    · intro hbd
      by_contra hnot
      push Not at hnot
      have hs0 : 0 < sVert m i := sVert_pos_of_ne_zero hm hnot.1
      have hs1 : sVert m i < 1 := sVert_lt_one_of_ne_last hm hnot.2
      have h_not_sph : ptC i ∉ sphere (0 : ℂ) 1 :=
        discCoordC_not_mem_sphere hz₀ hz₁ hz_ne hs0 hs1 (by
          have : 0 ≤ 1 - sVert m i := sub_nonneg.mpr hs1.le
          simp; positivity)
      have h_in_sph : ptC i ∈ sphere (0 : ℂ) 1 := by
        rw [← c.bd, ← c.hg (hptC_ball i)]
        exact mem_image_of_mem h hbd
      exact h_not_sph h_in_sph
    · rintro (rfl | rfl)
      · rw [hpt_0]; exact hu₁
      · rw [hpt_m]; exact hu₂
  let V_D : Set S := range pt
  have hV_D_sub : V_D ⊆ D := by rintro _ ⟨i, rfl⟩; exact hpt_D i
  have hV_D_fin : V_D.Finite := finite_range pt
  have hu₁_V : u₁ ∈ V_D := ⟨0, hpt_0⟩
  have hu₂_V : u₂ ∈ V_D := ⟨⟨m, Nat.lt_succ_self m⟩, hpt_m⟩
  have hV_D_bd : V_D ∩ discBd D = {u₁, u₂} := by
    ext x
    simp only [V_D, mem_inter_iff, mem_range, mem_insert_iff, mem_singleton_iff]
    constructor
    · rintro ⟨⟨i, rfl⟩, hbd⟩
      rcases (hpt_bd i).mp hbd with rfl | rfl
      · exact Or.inl hpt_0
      · exact Or.inr hpt_m
    · rintro (rfl | rfl)
      · exact ⟨hu₁_V, hu₁⟩
      · exact ⟨hu₂_V, hu₂⟩
  let ιV_D : S → α := fun x => if hx : x ∈ V_D then v (Classical.choose hx) else x₀
  have hιV_pt : ∀ i : Fin (m + 1), ιV_D (pt i) = v i := fun i => by
    have hx : pt i ∈ V_D := ⟨i, rfl⟩
    simp only [ιV_D, hx, ↓reduceDIte]
    exact congrArg v (hpt_inj (Classical.choose_spec hx))
  have hιV_u₁ : ιV_D u₁ = v₁ := by rw [← hpt_0, hιV_pt 0, hv0]
  have hιV_u₂ : ιV_D u₂ = v₂ := by rw [← hpt_m, hιV_pt, hvm]
  have hιV_inj : InjOn ιV_D V_D := by
    rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩ hEq
    rw [hιV_pt i, hιV_pt j] at hEq
    exact congrArg pt (hv_inj hEq)
  have hιV_img : ιV_D '' V_D = H.vertexSet := by
    rw [hV]
    ext w
    simp only [V_D, mem_image, mem_range, exists_exists_eq_and, hιV_pt]
  -- Edge indexing
  have : Finite ↑H.edgeSet := H.edgeSet_finite.to_subtype
  rcases Finite.exists_equiv_fin ↑H.edgeSet with ⟨n_E, ⟨e_equiv⟩⟩
  let K : ℕ := n_E + 1
  have hK : 1 ≤ K := Nat.le_add_left 1 n_E
  let edgeIdx : β → ℕ := fun e =>
    if he : e ∈ H.edgeSet then (e_equiv ⟨e, he⟩).1 + 1 else 1
  have hedgeIdx_bounds : ∀ e : β, 1 ≤ edgeIdx e ∧ edgeIdx e ≤ K := fun e => by
    by_cases he : e ∈ H.edgeSet
    · simp only [edgeIdx, he, ↓reduceDIte, K]
      have hlt := (e_equiv ⟨e, he⟩).2
      omega
    · simp only [edgeIdx, he, ↓reduceDIte, K]
      omega
  have hedgeIdx_inj : InjOn edgeIdx H.edgeSet := by
    intro e₁ he₁ e₂ he₂ hEq
    simp only [edgeIdx, he₁, he₂, ↓reduceDIte] at hEq
    have h_fin : e_equiv ⟨e₁, he₁⟩ = e_equiv ⟨e₂, he₂⟩ := Fin.ext (by omega)
    exact congrArg Subtype.val (e_equiv.injective h_fin)
  -- Link and loop parameterizations in D
  let linkC_map (i : Fin m) (k : ℕ) (t : 𝕀) : ℂ :=
    discCoordC z₀ z₁ (sLink m i t) (yLink z₀ z₁ m K k t)
  have hlinkC_cont : ∀ i k, Continuous (linkC_map i k) := fun i k => by
    unfold linkC_map discCoordC sLink yLink
    fun_prop
  have hlinkC_ball : ∀ i : Fin m, ∀ k, k ≤ K → ∀ t : 𝕀, linkC_map i k t ∈ closedBall (0 : ℂ) 1 :=
    fun i k hk_le t =>
      discCoordC_mem_closedBall hz₀ hz₁ (sLink_bounds hm i t).1 (sLink_bounds hm i t).2
        (abs_yLink_le hm hK hk_le i t)
  let linkParam (i : Fin m) (k : ℕ) (t : 𝕀) : S := g (linkC_map i k t)
  have hlink_cont : ∀ i : Fin m, ∀ k, k ≤ K → Continuous (linkParam i k) :=
    fun i k hk_le => c.gc.comp_continuous (hlinkC_cont i k) (hlinkC_ball i k hk_le)
  have hlink_inj : ∀ i : Fin m, ∀ k, k ≤ K → Function.Injective (linkParam i k) :=
    fun i k hk_le t₁ t₂ hEq => by
      have hC := c.injOn (hlinkC_ball i k hk_le t₁) (hlinkC_ball i k hk_le t₂) hEq
      obtain ⟨hs, hy⟩ := discCoordC_injective hz_ne hC
      exact (link_params_inj hz_ne hm hK hs hy).1 rfl
  have hlink_0 : ∀ i : Fin m, ∀ k, linkParam i k 0 = pt ⟨i.1, Nat.lt_succ_of_lt i.2⟩ :=
    fun i k => by
      show g (discCoordC z₀ z₁ (sLink m i 0) (yLink z₀ z₁ m K k 0)) = pt ⟨i.1, _⟩
      rw [sLink_zero, yLink_zero]
  have hlink_1 : ∀ i : Fin m, ∀ k, linkParam i k 1 = pt ⟨i.1 + 1, Nat.succ_lt_succ i.2⟩ :=
    fun i k => by
      show g (discCoordC z₀ z₁ (sLink m i 1) (yLink z₀ z₁ m K k 1)) = pt ⟨i.1 + 1, _⟩
      rw [sLink_one, yLink_one]
  let closedLinkSet (i : Fin m) (k : ℕ) : Set S := range (linkParam i k)
  let openLinkSet (i : Fin m) (k : ℕ) : Set S :=
    linkParam i k '' {t : 𝕀 | 0 < (t : ℝ) ∧ (t : ℝ) < 1}
  -- Loop parameterizations in D
  let loopC_map (i : Fin (m + 1)) (k : ℕ) (z : Circle) : ℂ :=
    discCoordC z₀ z₁ (sLoop m i z) (yLoop z₀ z₁ m K k z)
  have hloopC_cont : ∀ i k, Continuous (loopC_map i k) := fun i k => by
    unfold loopC_map discCoordC sLoop yLoop
    fun_prop
  have hloopC_ball : ∀ i : Fin (m + 1), ∀ k, 1 ≤ k → k ≤ K → ∀ z : Circle,
      loopC_map i k z ∈ closedBall (0 : ℂ) 1 :=
    fun i k hk1 hk_le z =>
      discCoordC_mem_closedBall hz₀ hz₁ (sLoop_bounds_and_prod hm i z).1
        (sLoop_bounds_and_prod hm i z).2.1 (abs_yLoop_le hm hK hk1 hk_le i z)
  let loopParam (i : Fin (m + 1)) (k : ℕ) (z : Circle) : S := g (loopC_map i k z)
  have hloop_cont : ∀ i : Fin (m + 1), ∀ k, 1 ≤ k → k ≤ K → Continuous (loopParam i k) :=
    fun i k hk1 hk_le => c.gc.comp_continuous (hloopC_cont i k) (hloopC_ball i k hk1 hk_le)
  have hloop_inj : ∀ i : Fin (m + 1), ∀ k, 1 ≤ k → k ≤ K → Function.Injective (loopParam i k) :=
    fun i k hk1 hk_le z₁' z₂' hEq => by
      have hC := c.injOn (hloopC_ball i k hk1 hk_le z₁') (hloopC_ball i k hk1 hk_le z₂') hEq
      obtain ⟨hs, hy⟩ := discCoordC_injective hz_ne hC
      exact (loop_params_inj hz_ne hm hK hs hy).2.2 rfl
  have hloop_1 : ∀ i : Fin (m + 1), ∀ k, loopParam i k 1 = pt i := fun i k => by
    show g (discCoordC z₀ z₁ (sLoop m i 1) (yLoop z₀ z₁ m K k 1)) = pt i
    rw [sLoop_one, yLoop_one]
  let closedLoopSet (i : Fin (m + 1)) (k : ℕ) : Set S := range (loopParam i k)
  let openLoopSet (i : Fin (m + 1)) (k : ℕ) : Set S :=
    loopParam i k '' ({1}ᶜ : Set Circle)
  -- Properties of link sets
  have hlink_inter_V : ∀ i : Fin m, ∀ k, 1 ≤ k → k ≤ K →
      closedLinkSet i k ∩ V_D =
        {pt ⟨i.1, Nat.lt_succ_of_lt i.2⟩, pt ⟨i.1 + 1, Nat.succ_lt_succ i.2⟩} := by
    intro i k hk1 hk_le
    refine Subset.antisymm ?_ ?_
    · rintro _ ⟨⟨t, rfl⟩, ⟨j, h_eq⟩⟩
      by_cases ht0 : (t : ℝ) = 0
      · have ht : t = 0 := Subtype.ext ht0
        subst ht
        exact Or.inl (hlink_0 i k)
      · by_cases ht1 : (t : ℝ) = 1
        · have ht : t = 1 := Subtype.ext ht1
          subst ht
          exact Or.inr (hlink_1 i k)
        · have h_pos : 0 < yLink z₀ z₁ m K k t :=
            yLink_pos hz_ne hm hK hk1 (lt_of_le_of_ne t.2.1 (Ne.symm ht0)) (lt_of_le_of_ne t.2.2 ht1)
          have hC := c.injOn (hlinkC_ball i k hk_le t) (hptC_ball j) h_eq.symm
          have hy0 : yLink z₀ z₁ m K k t = 0 := (discCoordC_injective hz_ne hC).2
          linarith
    · rintro x (rfl | rfl)
      · exact ⟨⟨0, hlink_0 i k⟩, ⟨_, rfl⟩⟩
      · exact ⟨⟨1, hlink_1 i k⟩, ⟨_, rfl⟩⟩
  have hlink_diff_V : ∀ i : Fin m, ∀ k, 1 ≤ k → k ≤ K →
      closedLinkSet i k \ V_D = openLinkSet i k := by
    intro i k hk1 hk_le
    ext x
    simp only [closedLinkSet, openLinkSet, mem_sdiff, mem_range, mem_image, mem_ofPred_eq]
    constructor
    · rintro ⟨⟨t, rfl⟩, hxV⟩
      have ht0 : (t : ℝ) ≠ 0 := by
        intro h0
        have ht : t = 0 := Subtype.ext h0
        subst ht
        exact hxV ⟨_, (hlink_0 i k).symm⟩
      have ht1 : (t : ℝ) ≠ 1 := by
        intro h1
        have ht : t = 1 := Subtype.ext h1
        subst ht
        exact hxV ⟨_, (hlink_1 i k).symm⟩
      exact ⟨t, ⟨lt_of_le_of_ne t.2.1 (Ne.symm ht0), lt_of_le_of_ne t.2.2 ht1⟩, rfl⟩
    · rintro ⟨t, ⟨ht0, ht1⟩, rfl⟩
      refine ⟨⟨t, rfl⟩, ?_⟩
      rintro ⟨j, h_eq⟩
      have h_pos : 0 < yLink z₀ z₁ m K k t := yLink_pos hz_ne hm hK hk1 ht0 ht1
      have hC := c.injOn (hlinkC_ball i k hk_le t) (hptC_ball j) h_eq.symm
      have hy0 : yLink z₀ z₁ m K k t = 0 := (discCoordC_injective hz_ne hC).2
      linarith
  have hlink_open_int : ∀ i : Fin m, ∀ k, 1 ≤ k → k ≤ K →
      openLinkSet i k ⊆ D \ discBd D := by
    rintro i k hk1 hk_le _ ⟨t, ⟨ht0, ht1⟩, rfl⟩
    refine ⟨c.gm (hlinkC_ball i k hk_le t), fun hbd => ?_⟩
    have h_not_sph : linkC_map i k t ∉ sphere (0 : ℂ) 1 :=
      discCoordC_not_mem_sphere hz₀ hz₁ hz_ne (sLink_interior hm i ht0 ht1).1
        (sLink_interior hm i ht0 ht1).2 (abs_yLink_le hm hK hk_le i t)
    have h_in_sph : linkC_map i k t ∈ sphere (0 : ℂ) 1 := by
      rw [← c.bd, ← c.hg (hlinkC_ball i k hk_le t)]
      exact mem_image_of_mem h hbd
    exact h_not_sph h_in_sph
  have hlink_closure : ∀ i : Fin m, ∀ k, k ≤ K →
      closure (openLinkSet i k) = closedLinkSet i k := by
    intro i k hk_le
    refine Subset.antisymm ?_ ?_
    · refine closure_minimal ?_ (isCompact_range (hlink_cont i k hk_le)).isClosed
      rintro _ ⟨t, _, rfl⟩
      exact ⟨t, rfl⟩
    · have h_sub_cl : closure {t : 𝕀 | 0 < (t : ℝ) ∧ (t : ℝ) < 1} = univ := by
        rw [IsInducing.subtypeVal.closure_eq_preimage_closure_image]
        have himg : Subtype.val '' {t : 𝕀 | 0 < (t : ℝ) ∧ (t : ℝ) < 1} = Ioo (0 : ℝ) 1 := by
          ext r
          simp only [mem_image, mem_ofPred_eq, mem_Ioo]
          exact ⟨by rintro ⟨t, ht, rfl⟩; exact ht,
            fun hr => ⟨⟨r, Ioo_subset_Icc_self hr⟩, hr, rfl⟩⟩
        rw [himg, closure_Ioo (zero_ne_one : (0 : ℝ) ≠ 1)]
        ext t; simp
      calc closedLinkSet i k
          = linkParam i k '' univ := image_univ.symm
        _ = linkParam i k '' closure {t : 𝕀 | 0 < (t : ℝ) ∧ (t : ℝ) < 1} := by rw [h_sub_cl]
        _ ⊆ closure (openLinkSet i k) :=
            image_closure_subset_closure_image (hlink_cont i k hk_le)
  have hlink_nonempty : ∀ i : Fin m, ∀ k, (openLinkSet i k).Nonempty := fun i k =>
    ⟨linkParam i k ⟨1 / 2, by constructor <;> norm_num⟩,
      ⟨1 / 2, by constructor <;> norm_num⟩, by constructor <;> norm_num, rfl⟩
  have hlink_pc : ∀ i : Fin m, ∀ k, k ≤ K → IsPathConnected (openLinkSet i k) := by
    intro i k hk_le
    have hconv : IsPathConnected (Ioo (0 : ℝ) 1) :=
      (convex_Ioo (0 : ℝ) 1).isPathConnected ⟨1 / 2, by constructor <;> norm_num⟩
    let φ : ℝ → S := fun r => linkParam i k (projIcc 0 1 zero_le_one r)
    have hφ_eq : openLinkSet i k = φ '' Ioo (0 : ℝ) 1 := by
      ext x
      simp only [openLinkSet, φ, mem_image, mem_ofPred_eq, mem_Ioo]
      constructor
      · rintro ⟨t, ht, rfl⟩
        exact ⟨(t : ℝ), ht, by rw [projIcc_of_mem zero_le_one t.2]⟩
      · rintro ⟨r, hr, rfl⟩
        have hr_icc : r ∈ Icc (0 : ℝ) 1 := Ioo_subset_Icc_self hr
        exact ⟨⟨r, hr_icc⟩, hr, by rw [projIcc_of_mem zero_le_one hr_icc]⟩
    rw [hφ_eq]
    exact hconv.image ((hlink_cont i k hk_le).comp continuous_projIcc)
  have hlink_line : ∀ i : Fin m, ∀ k, k ≤ K →
      IsLineWithEnds (closedLinkSet i k)
        (pt ⟨i.1, Nat.lt_succ_of_lt i.2⟩) (pt ⟨i.1 + 1, Nat.succ_lt_succ i.2⟩) := by
    intro i k hk_le
    let ev : 𝕀 ≃ₜ closedLinkSet i k :=
      Continuous.homeoOfEquivCompactToT2
        (f := Equiv.ofInjective (linkParam i k) (hlink_inj i k hk_le))
        (hlink_cont i k hk_le).rangeFactorization
    exact ⟨ev, hlink_0 i k, hlink_1 i k⟩
  -- Properties of loop sets
  have hloop_inter_V : ∀ i : Fin (m + 1), ∀ k, 1 ≤ k → k ≤ K →
      closedLoopSet i k ∩ V_D = {pt i} := by
    intro i k hk1 hk_le
    refine Subset.antisymm ?_ ?_
    · rintro _ ⟨⟨z, rfl⟩, ⟨j, h_eq⟩⟩
      by_cases hz1 : z = 1
      · subst hz1
        exact mem_singleton_iff.mpr (hloop_1 i k)
      · have h_neg : yLoop z₀ z₁ m K k z < 0 := yLoop_neg hz_ne hm hK hk1 hz1
        have hC := c.injOn (hloopC_ball i k hk1 hk_le z) (hptC_ball j) h_eq.symm
        have hy0 : yLoop z₀ z₁ m K k z = 0 := (discCoordC_injective hz_ne hC).2
        linarith
    · rintro x rfl
      exact ⟨⟨1, hloop_1 i k⟩, ⟨i, rfl⟩⟩
  have hloop_diff_V : ∀ i : Fin (m + 1), ∀ k, 1 ≤ k → k ≤ K →
      closedLoopSet i k \ V_D = openLoopSet i k := by
    intro i k hk1 hk_le
    ext x
    simp only [closedLoopSet, openLoopSet, mem_sdiff, mem_range, mem_image, mem_compl_iff,
      mem_singleton_iff]
    constructor
    · rintro ⟨⟨z, rfl⟩, hxV⟩
      refine ⟨z, fun hz1 => ?_, rfl⟩
      subst hz1
      exact hxV ⟨i, (hloop_1 i k).symm⟩
    · rintro ⟨z, hz1, rfl⟩
      refine ⟨⟨z, rfl⟩, ?_⟩
      rintro ⟨j, h_eq⟩
      have h_neg : yLoop z₀ z₁ m K k z < 0 := yLoop_neg hz_ne hm hK hk1 hz1
      have hC := c.injOn (hloopC_ball i k hk1 hk_le z) (hptC_ball j) h_eq.symm
      have hy0 : yLoop z₀ z₁ m K k z = 0 := (discCoordC_injective hz_ne hC).2
      linarith
  have hloop_open_int : ∀ i : Fin (m + 1), ∀ k, 1 ≤ k → k ≤ K →
      openLoopSet i k ⊆ D \ discBd D := by
    rintro i k hk1 hk_le _ ⟨z, hz1, rfl⟩
    refine ⟨c.gm (hloopC_ball i k hk1 hk_le z), fun hbd => ?_⟩
    have h_not_sph : loopC_map i k z ∉ sphere (0 : ℂ) 1 :=
      discCoordC_not_mem_sphere hz₀ hz₁ hz_ne (sLoop_interior hm i hz1).1
        (sLoop_interior hm i hz1).2 (abs_yLoop_le hm hK hk1 hk_le i z)
    have h_in_sph : loopC_map i k z ∈ sphere (0 : ℂ) 1 := by
      rw [← c.bd, ← c.hg (hloopC_ball i k hk1 hk_le z)]
      exact mem_image_of_mem h hbd
    exact h_not_sph h_in_sph
  have hloop_closure : ∀ i : Fin (m + 1), ∀ k, 1 ≤ k → k ≤ K →
      closure (openLoopSet i k) = closedLoopSet i k := by
    intro i k hk1 hk_le
    refine Subset.antisymm ?_ ?_
    · refine closure_minimal ?_ (isCompact_range (hloop_cont i k hk1 hk_le)).isClosed
      rintro _ ⟨z, _, rfl⟩
      exact ⟨z, rfl⟩
    · calc closedLoopSet i k
          = loopParam i k '' univ := image_univ.symm
        _ = loopParam i k '' closure ({1}ᶜ : Set Circle) := by
            rw [closure_compl_singleton_one_circle]
        _ ⊆ closure (openLoopSet i k) :=
            image_closure_subset_closure_image (hloop_cont i k hk1 hk_le)
  have hloop_nonempty : ∀ i : Fin (m + 1), ∀ k, (openLoopSet i k).Nonempty := fun i k =>
    ⟨loopParam i k (-1), -1, Circle.neg_ne_self 1, rfl⟩
  have hloop_pc : ∀ i : Fin (m + 1), ∀ k, 1 ≤ k → k ≤ K →
      IsPathConnected (openLoopSet i k) := fun i k hk1 hk_le =>
    (Circle.isPathConnected_compl_singleton 1).image (hloop_cont i k hk1 hk_le)
  have hloop_oarc : ∀ i : Fin (m + 1), ∀ k, 1 ≤ k → k ≤ K →
      IsOArc (closedLoopSet i k) := fun i k hk1 hk_le =>
    ⟨Continuous.homeoOfEquivCompactToT2
      (f := Equiv.ofInjective (loopParam i k) (hloop_inj i k hk1 hk_le))
      (hloop_cont i k hk1 hk_le).rangeFactorization⟩
  -- Define closedEdge_D and openEdge_D for e ∈ H.edgeSet
  have h_link_ex : ∀ e ∈ H.edgeSet, ¬ (∃ i : Fin (m + 1), H.ends e = {v i}) →
      ∃ i : Fin m, H.ends e = {v ⟨i.1, by omega⟩, v ⟨i.1 + 1, by omega⟩} :=
    fun e he hnot => (edge_ends_of_path_indexing hH hm hv_inj hV hadj he).resolve_left hnot
  let closedEdge_D : β → Set S := fun e =>
    if he : e ∈ H.edgeSet then
      if hloop : ∃ i : Fin (m + 1), H.ends e = {v i} then
        closedLoopSet (Classical.choose hloop) (edgeIdx e)
      else
        closedLinkSet (Classical.choose (h_link_ex e he hloop)) (edgeIdx e)
    else ∅
  let openEdge_D : β → Set S := fun e =>
    if he : e ∈ H.edgeSet then
      if hloop : ∃ i : Fin (m + 1), H.ends e = {v i} then
        openLoopSet (Classical.choose hloop) (edgeIdx e)
      else
        openLinkSet (Classical.choose (h_link_ex e he hloop)) (edgeIdx e)
    else ∅
  refine ⟨V_D, ιV_D, closedEdge_D, openEdge_D,
    { u₁_mem := hu₁_V
      u₂_mem := hu₂_V
      V_subset_D := hV_D_sub
      V_finite := hV_D_fin
      V_inter_discBd := hV_D_bd
      ιV_u₁ := hιV_u₁
      ιV_u₂ := hιV_u₂
      ιV_injOn := hιV_inj
      ιV_image := hιV_img
      closedEdge_isClosed := fun e he => by
        obtain ⟨hk1, hk_le⟩ := hedgeIdx_bounds e
        by_cases hloop : ∃ i : Fin (m + 1), H.ends e = {v i}
        · simp only [closedEdge_D, he, hloop, ↓reduceDIte]
          exact (isCompact_range (hloop_cont _ _ hk1 hk_le)).isClosed
        · simp only [closedEdge_D, he, hloop, ↓reduceDIte]
          exact (isCompact_range (hlink_cont _ _ hk_le)).isClosed
      closedEdge_subset_D := fun e he => by
        obtain ⟨hk1, hk_le⟩ := hedgeIdx_bounds e
        by_cases hloop : ∃ i : Fin (m + 1), H.ends e = {v i}
        · simp only [closedEdge_D, he, hloop, ↓reduceDIte]
          rintro _ ⟨z, rfl⟩
          exact c.gm (hloopC_ball _ _ hk1 hk_le z)
        · simp only [closedEdge_D, he, hloop, ↓reduceDIte]
          rintro _ ⟨t, rfl⟩
          exact c.gm (hlinkC_ball _ _ hk_le t)
      openEdge_eq_diff := fun e he => by
        obtain ⟨hk1, hk_le⟩ := hedgeIdx_bounds e
        by_cases hloop : ∃ i : Fin (m + 1), H.ends e = {v i}
        · simp only [closedEdge_D, openEdge_D, he, hloop, ↓reduceDIte]
          exact (hloop_diff_V _ _ hk1 hk_le).symm
        · simp only [closedEdge_D, openEdge_D, he, hloop, ↓reduceDIte]
          exact (hlink_diff_V _ _ hk1 hk_le).symm
      openEdge_subset_int := fun e he => by
        obtain ⟨hk1, hk_le⟩ := hedgeIdx_bounds e
        by_cases hloop : ∃ i : Fin (m + 1), H.ends e = {v i}
        · simp only [openEdge_D, he, hloop, ↓reduceDIte]
          exact hloop_open_int _ _ hk1 hk_le
        · simp only [openEdge_D, he, hloop, ↓reduceDIte]
          exact hlink_open_int _ _ hk1 hk_le
      closure_openEdge := fun e he => by
        obtain ⟨hk1, hk_le⟩ := hedgeIdx_bounds e
        by_cases hloop : ∃ i : Fin (m + 1), H.ends e = {v i}
        · simp only [closedEdge_D, openEdge_D, he, hloop, ↓reduceDIte]
          exact hloop_closure _ _ hk1 hk_le
        · simp only [closedEdge_D, openEdge_D, he, hloop, ↓reduceDIte]
          exact hlink_closure _ _ hk_le
      openEdge_nonempty := fun e he => by
        by_cases hloop : ∃ i : Fin (m + 1), H.ends e = {v i}
        · simp only [openEdge_D, he, hloop, ↓reduceDIte]
          exact hloop_nonempty _ _
        · simp only [openEdge_D, he, hloop, ↓reduceDIte]
          exact hlink_nonempty _ _
      openEdge_isPathConnected := fun e he => by
        obtain ⟨hk1, hk_le⟩ := hedgeIdx_bounds e
        by_cases hloop : ∃ i : Fin (m + 1), H.ends e = {v i}
        · simp only [openEdge_D, he, hloop, ↓reduceDIte]
          exact hloop_pc _ _ hk1 hk_le
        · simp only [openEdge_D, he, hloop, ↓reduceDIte]
          exact hlink_pc _ _ hk_le
      edge_cond := fun e he => by
        obtain ⟨hk1, hk_le⟩ := hedgeIdx_bounds e
        by_cases hloop : ∃ i : Fin (m + 1), H.ends e = {v i}
        · right
          simp only [closedEdge_D, he, hloop, ↓reduceDIte]
          exact ⟨pt (Classical.choose hloop), hloop_inter_V _ _ hk1 hk_le,
            hloop_oarc _ _ hk1 hk_le⟩
        · left
          simp only [closedEdge_D, he, hloop, ↓reduceDIte]
          let i := Classical.choose (h_link_ex e he hloop)
          have hne_pts : pt ⟨i.1, Nat.lt_succ_of_lt i.2⟩ ≠ pt ⟨i.1 + 1, Nat.succ_lt_succ i.2⟩ :=
            fun hEq => by
              have hval : i.1 = i.1 + 1 := Fin.ext_iff.mp (hpt_inj hEq)
              omega
          exact ⟨_, _, hne_pts, hlink_inter_V i (edgeIdx e) hk1 hk_le,
            hlink_line i (edgeIdx e) hk_le⟩
      inc_iff := fun e he u hu => by
        obtain ⟨hk1, hk_le⟩ := hedgeIdx_bounds e
        have hu_mem : u ∈ V_D := hu
        rcases hu with ⟨j, rfl⟩
        rw [hιV_pt j]
        by_cases hloop : ∃ i : Fin (m + 1), H.ends e = {v i}
        · let i := Classical.choose hloop
          have hends : H.ends e = {v i} := Classical.choose_spec hloop
          have hinter := hloop_inter_V i (edgeIdx e) hk1 hk_le
          have h_ce : closedEdge_D e = closedLoopSet i (edgeIdx e) := by
            simp only [closedEdge_D, he, hloop, ↓reduceDIte, i]
          change v j ∈ H.ends e ↔ pt j ∈ closedEdge_D e
          rw [h_ce, hends, mem_singleton_iff, hv_inj.eq_iff, ← hpt_inj.eq_iff]
          constructor
          · intro hj
            rw [hj]
            exact (hinter.symm ▸ rfl : pt i ∈ closedLoopSet i (edgeIdx e) ∩ V_D).1
          · intro hmem
            have h_in : pt j ∈ closedLoopSet i (edgeIdx e) ∩ V_D := ⟨hmem, hu_mem⟩
            rw [hinter] at h_in
            exact h_in
        · let i := Classical.choose (h_link_ex e he hloop)
          have hends := Classical.choose_spec (h_link_ex e he hloop)
          have hinter := hlink_inter_V i (edgeIdx e) hk1 hk_le
          have h_ce : closedEdge_D e = closedLinkSet i (edgeIdx e) := by
            simp only [closedEdge_D, he, hloop, ↓reduceDIte, i]
          change v j ∈ H.ends e ↔ pt j ∈ closedEdge_D e
          rw [h_ce, hends]
          simp only [mem_insert_iff, mem_singleton_iff, hv_inj.eq_iff]
          constructor
          · rintro (hj | hj)
            · rw [hj]
              exact (hinter.symm ▸ Or.inl rfl : pt _ ∈ closedLinkSet i (edgeIdx e) ∩ V_D).1
            · rw [hj]
              exact (hinter.symm ▸ Or.inr rfl : pt _ ∈ closedLinkSet i (edgeIdx e) ∩ V_D).1
          · intro hmem
            have h_in : pt j ∈ closedLinkSet i (edgeIdx e) ∩ V_D := ⟨hmem, hu_mem⟩
            rw [hinter] at h_in
            rcases h_in with h1 | h2
            · exact Or.inl (hpt_inj h1)
            · exact Or.inr (hpt_inj h2)
      openEdge_disjoint := fun e₁ he₁ e₂ he₂ hne => by
        obtain ⟨hk₁1, hk₁_le⟩ := hedgeIdx_bounds e₁
        obtain ⟨hk₂1, hk₂_le⟩ := hedgeIdx_bounds e₂
        have hk_ne : edgeIdx e₁ ≠ edgeIdx e₂ := fun hEq => hne (hedgeIdx_inj he₁ he₂ hEq)
        rw [Set.disjoint_left]
        intro x hx₁ hx₂
        by_cases hloop₁ : ∃ i : Fin (m + 1), H.ends e₁ = {v i} <;>
          by_cases hloop₂ : ∃ i : Fin (m + 1), H.ends e₂ = {v i}
        · simp only [openEdge_D, he₁, hloop₁, ↓reduceDIte] at hx₁
          simp only [openEdge_D, he₂, hloop₂, ↓reduceDIte] at hx₂
          rcases hx₁ with ⟨z₁', hz₁', rfl⟩
          rcases hx₂ with ⟨z₂', _, h_eq⟩
          have hC := c.injOn (hloopC_ball _ _ hk₂1 hk₂_le z₂') (hloopC_ball _ _ hk₁1 hk₁_le z₁') h_eq
          obtain ⟨hs, hy⟩ := discCoordC_injective hz_ne hC.symm
          exact hk_ne ((loop_params_inj hz_ne hm hK hs hy).2.1 hz₁')
        · simp only [openEdge_D, he₁, hloop₁, ↓reduceDIte] at hx₁
          simp only [openEdge_D, he₂, hloop₂, ↓reduceDIte] at hx₂
          rcases hx₁ with ⟨z₁', hz₁', rfl⟩
          rcases hx₂ with ⟨t₂, ⟨ht₂0, ht₂1⟩, h_eq⟩
          have hC := c.injOn (hlinkC_ball _ _ hk₂_le t₂) (hloopC_ball _ _ hk₁1 hk₁_le z₁') h_eq
          obtain ⟨_, hy⟩ := discCoordC_injective hz_ne hC
          have hy_pos := yLink_pos hz_ne hm hK hk₂1 ht₂0 ht₂1
          have hy_neg := yLoop_neg hz_ne hm hK hk₁1 hz₁'
          linarith
        · simp only [openEdge_D, he₁, hloop₁, ↓reduceDIte] at hx₁
          simp only [openEdge_D, he₂, hloop₂, ↓reduceDIte] at hx₂
          rcases hx₁ with ⟨t₁, ⟨ht₁0, ht₁1⟩, rfl⟩
          rcases hx₂ with ⟨z₂', hz₂', h_eq⟩
          have hC := c.injOn (hloopC_ball _ _ hk₂1 hk₂_le z₂') (hlinkC_ball _ _ hk₁_le t₁) h_eq
          obtain ⟨_, hy⟩ := discCoordC_injective hz_ne hC
          have hy_pos := yLink_pos hz_ne hm hK hk₁1 ht₁0 ht₁1
          have hy_neg := yLoop_neg hz_ne hm hK hk₂1 hz₂'
          linarith
        · simp only [openEdge_D, he₁, hloop₁, ↓reduceDIte] at hx₁
          simp only [openEdge_D, he₂, hloop₂, ↓reduceDIte] at hx₂
          rcases hx₁ with ⟨t₁, ⟨ht₁0, ht₁1⟩, rfl⟩
          rcases hx₂ with ⟨t₂, ⟨ht₂0, ht₂1⟩, h_eq⟩
          have hC := c.injOn (hlinkC_ball _ _ hk₂_le t₂) (hlinkC_ball _ _ hk₁_le t₁) h_eq
          obtain ⟨hs, hy⟩ := discCoordC_injective hz_ne hC.symm
          exact hk_ne (link_params_inj hz_ne hm hK hs hy |>.2 ht₁0 ht₁1 ht₂0 ht₂1).2.2 }⟩

/-! ## 5. Global Assembly Across Internal Cells `c ∈ ℐ` -/

/-- For any cell `c ∈ Γ.C`, points of `closure c` outside `discBd (closure c)` lie in `c`. -/
theorem closure_cell_diff_discBd_subset {S : Type} [TopologicalSpace S]
    (Γ : GM17.Painting S) {c : Set S} (hc : c ∈ Γ.C) :
    closure c \ discBd (closure c) ⊆ c := by
  intro x ⟨hxcl, hx_not_bd⟩
  rw [← Γ.closure_cell_diff_N hc]
  refine ⟨hxcl, fun hxN => hx_not_bd ?_⟩
  have hxt : x ∈ tilde c := by
    rw [← Γ.closure_cell_inter_N hc]
    exact ⟨hxcl, hxN⟩
  exact (Γ.cell_disc c hc).2.1 hxt

/-- For any two distinct cells `c₁, c₂ ∈ Γ.C`, `c₁` is disjoint from `closure c₂`. -/
theorem cell_disjoint_closure_cell {S : Type} [TopologicalSpace S]
    (Γ : GM17.Painting S) {c₁ c₂ : Set S} (hc₁ : c₁ ∈ Γ.C) (hc₂ : c₂ ∈ Γ.C) (hne : c₁ ≠ c₂) :
    Disjoint c₁ (closure c₂) := by
  rw [Set.disjoint_left]
  intro x hxc₁ hxcl₂
  have hx_not_N : x ∉ Γ.N := (Γ.cell_subset_diff hc₁ hxc₁).2
  have hxc₂ : x ∈ c₂ := by
    rw [← Γ.closure_cell_diff_N hc₂]
    exact ⟨hxcl₂, hx_not_N⟩
  exact Set.disjoint_left.mp (Γ.cell_disjoint hc₁ hc₂ hne) hxc₁ hxc₂

/-- Construct the drawing `Γ'` and isomorphism maps `(ιV', ιE')` onto `Γ'_sub` for the proof of
**Graph Minors XXI, (9.2)** (page 39 of the preprint) by drawing `α_cell c` in
`closure c` for each internal cell `c ∈ ℐ` (`c ∉ 𝒜₁`), meeting `discBd (closure c)` only in
`tilde c`, with the vertices of `tilde c` representing themselves. -/
theorem exists_drawing_of_internal_cells {α : Type u} {β : Type v} {S : Type}
    [TopologicalSpace S] [Nonempty S] (hS : IsSurface S)
    {G : Hypergraph α β} (hG : G.IsGraph)
    {Γ : GM17.Painting S} {ιN : S → α}
    {α_cell : Set S → Hypergraph α β} {α_vert : S → Hypergraph α β}
    {q_cuff : Set S → ℕ}
    (hport : IsPortrait21 G Γ ιN α_cell α_vert q_cuff)
    {ℐ : Set (Set S)} (hℐ_sub : ℐ ⊆ Γ.C)
    (hℐ_int : ∀ c ∈ ℐ, IsInternalCell Γ c)
    (hℐ_card : ∀ c ∈ ℐ, (tilde c).ncard = 2)
    (hℐ_draw : ∀ c ∈ ℐ, CanBeDrawnInDisc21 (α_cell c) (ιN '' tilde c))
    (x₀ : α) (e₀ : β)
    {Γ'_sub : Hypergraph α β}
    (hΓ'_sub_V : Γ'_sub.vertexSet = (ιN '' Γ.N) ∪ (⋃ c ∈ ℐ, (α_cell c).vertexSet))
    (hΓ'_sub_E : Γ'_sub.edgeSet = ⋃ c ∈ ℐ, (α_cell c).edgeSet)
    (hΓ'_sub_inc : ∀ e ∈ Γ'_sub.edgeSet, ∀ w, Γ'_sub.Inc e w ↔ G.Inc e w) :
    ∃ (Γ' : Surface.Drawing S) (ιV' : S → α) (ιE' : Set S → β),
      Γ'.IsProper ∧
      Γ'.V ∩ bd S = Γ.N ∩ bd S ∧
      (∀ x ∈ Γ.N, ιV' x = ιN x) ∧
      IsDrawingIso Γ' Γ'_sub ιV' ιE' := by
  have : T2Space S := hS.2.1
  have hℐ_fin : ℐ.Finite := Γ.finite_cells.subset hℐ_sub
  -- For each c ∈ ℐ, obtain its disc drawing in closure c
  have h_cell_draw : ∀ c ∈ ℐ,
      ∃ (u₁ u₂ : S) (V_D : Set S) (ιV_D : S → α) (closedEdge_D openEdge_D : β → Set S),
        u₁ ≠ u₂ ∧ tilde c = {u₁, u₂} ∧
        IsCellDiscDrawing (closure c) u₁ u₂ (α_cell c) (ιN u₁) (ιN u₂)
          V_D ιV_D closedEdge_D openEdge_D := by
    intro c hc_ℐ
    have hc : c ∈ Γ.C := hℐ_sub hc_ℐ
    obtain ⟨u₁, u₂, hu₁₂, htilde_c⟩ := ncard_eq_two.mp (hℐ_card c hc_ℐ)
    have htilde_bd : tilde c ⊆ discBd (closure c) := (Γ.cell_disc c hc).2.1
    have hu₁_bd : u₁ ∈ discBd (closure c) := htilde_bd (htilde_c ▸ Or.inl rfl)
    have hu₂_bd : u₂ ∈ discBd (closure c) := htilde_bd (htilde_c ▸ Or.inr rfl)
    have htilde_N : tilde c ⊆ Γ.N := Γ.tilde_subset_N hc
    have hu₁_N : u₁ ∈ Γ.N := htilde_N (htilde_c ▸ Or.inl rfl)
    have hu₂_N : u₂ ∈ Γ.N := htilde_N (htilde_c ▸ Or.inr rfl)
    have hι_ne : ιN u₁ ≠ ιN u₂ := fun hEq => hu₁₂ (hport.r1_injOn hu₁_N hu₂_N hEq)
    have hα_le : α_cell c ≤ G := hport.r2_cell_le c hc
    have hα_graph : (α_cell c).IsGraph := fun e he => by
      rw [← hα_le.3 e he]
      exact hG e (hα_le.2 he)
    have hdraw_c : CanBeDrawnInDisc21 (α_cell c) {ιN u₁, ιN u₂} := by
      have h_img : ιN '' tilde c = {ιN u₁, ιN u₂} := by rw [htilde_c, image_pair]
      exact h_img ▸ hℐ_draw c hc_ℐ
    obtain ⟨V_D, ιV_D, closedEdge_D, openEdge_D, hcd⟩ :=
      exists_cell_disc_drawing (Γ.isClosedDisc_closure_cell hc) hu₁_bd hu₂_bd hu₁₂
        hα_graph hι_ne hdraw_c x₀
    exact ⟨u₁, u₂, V_D, ιV_D, closedEdge_D, openEdge_D, hu₁₂, htilde_c, hcd⟩
  let u₁_c (c : Set S) : S :=
    if hc : c ∈ ℐ then Classical.choose (h_cell_draw c hc) else Classical.arbitrary S
  let u₂_c (c : Set S) : S :=
    if hc : c ∈ ℐ then Classical.choose (Classical.choose_spec (h_cell_draw c hc))
    else Classical.arbitrary S
  let V_c (c : Set S) : Set S :=
    if hc : c ∈ ℐ then
      Classical.choose (Classical.choose_spec (Classical.choose_spec (h_cell_draw c hc)))
    else ∅
  let ιV_c (c : Set S) : S → α :=
    if hc : c ∈ ℐ then
      Classical.choose (Classical.choose_spec (Classical.choose_spec
        (Classical.choose_spec (h_cell_draw c hc))))
    else fun _ => x₀
  let closedEdge_c (c : Set S) : β → Set S :=
    if hc : c ∈ ℐ then
      Classical.choose (Classical.choose_spec (Classical.choose_spec
        (Classical.choose_spec (Classical.choose_spec (h_cell_draw c hc)))))
    else fun _ => ∅
  let openEdge_c (c : Set S) : β → Set S :=
    if hc : c ∈ ℐ then
      Classical.choose (Classical.choose_spec (Classical.choose_spec (Classical.choose_spec
        (Classical.choose_spec (Classical.choose_spec (h_cell_draw c hc))))))
    else fun _ => ∅
  have hc_spec : ∀ c ∈ ℐ,
      u₁_c c ≠ u₂_c c ∧ tilde c = {u₁_c c, u₂_c c} ∧
      IsCellDiscDrawing (closure c) (u₁_c c) (u₂_c c) (α_cell c) (ιN (u₁_c c)) (ιN (u₂_c c))
        (V_c c) (ιV_c c) (closedEdge_c c) (openEdge_c c) := fun c hc => by
    simp only [u₁_c, u₂_c, V_c, ιV_c, closedEdge_c, openEdge_c, hc, ↓reduceDIte]
    exact Classical.choose_spec (Classical.choose_spec (Classical.choose_spec
      (Classical.choose_spec (Classical.choose_spec (Classical.choose_spec (h_cell_draw c hc))))))
  -- Basic consequences for each c ∈ ℐ
  have htilde_sub_Vc : ∀ c ∈ ℐ, tilde c ⊆ V_c c := fun c hc => by
    obtain ⟨_, htilde, hcd⟩ := hc_spec c hc
    rw [htilde]
    rintro x (rfl | rfl)
    · exact hcd.u₁_mem
    · exact hcd.u₂_mem
  have hVc_inter_bd : ∀ c ∈ ℐ, V_c c ∩ discBd (closure c) = tilde c := fun c hc => by
    obtain ⟨_, htilde, hcd⟩ := hc_spec c hc
    rw [hcd.V_inter_discBd, htilde]
  have hVc_diff_sub_c : ∀ c ∈ ℐ, V_c c \ tilde c ⊆ c := fun c hc x ⟨hxV, hxt⟩ => by
    apply closure_cell_diff_discBd_subset Γ (hℐ_sub hc)
    refine ⟨(hc_spec c hc).2.2.V_subset_D hxV, fun hxbd => hxt ?_⟩
    rw [← hVc_inter_bd c hc]
    exact ⟨hxV, hxbd⟩
  have hVc_inter_N : ∀ c ∈ ℐ, V_c c ∩ Γ.N = tilde c := fun c hc => by
    refine Subset.antisymm ?_ (subset_inter (htilde_sub_Vc c hc) (Γ.tilde_subset_N (hℐ_sub hc)))
    intro x ⟨hxV, hxN⟩
    rw [← Γ.closure_cell_inter_N (hℐ_sub hc)]
    exact ⟨(hc_spec c hc).2.2.V_subset_D hxV, hxN⟩
  have hιVc_on_tilde : ∀ c ∈ ℐ, ∀ x ∈ tilde c, ιV_c c x = ιN x := fun c hc x hxt => by
    obtain ⟨_, htilde, hcd⟩ := hc_spec c hc
    rw [htilde] at hxt
    rcases hxt with rfl | rfl
    · exact hcd.ιV_u₁
    · exact hcd.ιV_u₂
  have hιVc_diff_not_N : ∀ c ∈ ℐ, ∀ x ∈ V_c c \ tilde c, ιV_c c x ∉ ιN '' Γ.N := by
    intro c hc x ⟨hxV, hxt⟩ h_in_N
    obtain ⟨_, _, hcd⟩ := hc_spec c hc
    have h_in_cell : ιV_c c x ∈ (α_cell c).vertexSet := by
      rw [← hcd.ιV_image]; exact mem_image_of_mem _ hxV
    have h_inter : ιV_c c x ∈ ιN '' tilde c := by
      rw [← hport.r2_cell_inter c (hℐ_sub hc)]
      exact ⟨h_in_cell, h_in_N⟩
    rcases h_inter with ⟨u, hut, h_eq⟩
    rw [← hιVc_on_tilde c hc u hut] at h_eq
    have hx_eq_u : x = u := hcd.ιV_injOn hxV (htilde_sub_Vc c hc hut) h_eq.symm
    exact hxt (hx_eq_u ▸ hut)
  have hopen_sub_c : ∀ c ∈ ℐ, ∀ e ∈ (α_cell c).edgeSet, openEdge_c c e ⊆ c :=
    fun c hc e he =>
      ((hc_spec c hc).2.2.openEdge_subset_int e he).trans
        (closure_cell_diff_discBd_subset Γ (hℐ_sub hc))
  -- Define V' and U'
  let V' : Set S := Γ.N ∪ ⋃ c ∈ ℐ, V_c c
  have hV'_fin : V'.Finite :=
    Γ.finite_N.union (hℐ_fin.biUnion fun c hc => (hc_spec c hc).2.2.V_finite)
  let U' : Set S := V' ∪ ⋃ c ∈ ℐ, ⋃ e ∈ (α_cell c).edgeSet, closedEdge_c c e
  have hU'_closed : IsClosed U' := by
    refine hV'_fin.isClosed.union (hℐ_fin.isClosed_biUnion fun c hc => ?_)
    exact (α_cell c).edgeSet_finite.isClosed_biUnion fun e he =>
      (hc_spec c hc).2.2.closedEdge_isClosed e he
  -- Key intersection property: closure c ∩ V' = V_c c for every c ∈ ℐ
  have hcl_inter_V' : ∀ c ∈ ℐ, closure c ∩ V' = V_c c := by
    intro c hc
    refine Subset.antisymm ?_ (subset_inter (hc_spec c hc).2.2.V_subset_D
      (fun x hx => Or.inr (mem_biUnion hc hx)))
    rintro x ⟨hxcl, hxN | hxV_all⟩
    · have hxt : x ∈ tilde c := by
        rw [← Γ.closure_cell_inter_N (hℐ_sub hc)]
        exact ⟨hxcl, hxN⟩
      exact htilde_sub_Vc c hc hxt
    · rw [mem_iUnion₂] at hxV_all
      rcases hxV_all with ⟨c', hc', hxV'⟩
      by_cases h_eq : c' = c
      · subst h_eq; exact hxV'
      · by_cases hxt' : x ∈ tilde c'
        · have hxN : x ∈ Γ.N := Γ.tilde_subset_N (hℐ_sub hc') hxt'
          have hxt : x ∈ tilde c := by
            rw [← Γ.closure_cell_inter_N (hℐ_sub hc)]
            exact ⟨hxcl, hxN⟩
          exact htilde_sub_Vc c hc hxt
        · have hxc' : x ∈ c' := hVc_diff_sub_c c' hc' ⟨hxV', hxt'⟩
          exact (Set.disjoint_left.mp
            (cell_disjoint_closure_cell Γ (hℐ_sub hc') (hℐ_sub hc) h_eq) hxc' hxcl).elim
  have hclosed_inter_V' : ∀ c ∈ ℐ, ∀ e ∈ (α_cell c).edgeSet,
      closedEdge_c c e ∩ V' = closedEdge_c c e ∩ V_c c := by
    intro c hc e he
    have hsub : closedEdge_c c e ⊆ closure c := (hc_spec c hc).2.2.closedEdge_subset_D e he
    calc closedEdge_c c e ∩ V'
        = (closedEdge_c c e ∩ closure c) ∩ V' := by rw [inter_eq_left.mpr hsub]
      _ = closedEdge_c c e ∩ (closure c ∩ V') := Set.inter_assoc _ _ _
      _ = closedEdge_c c e ∩ V_c c := by rw [hcl_inter_V' c hc]
  have hclosed_diff_V' : ∀ c ∈ ℐ, ∀ e ∈ (α_cell c).edgeSet,
      closedEdge_c c e \ V' = openEdge_c c e := by
    intro c hc e he
    have hsub : closedEdge_c c e ⊆ closure c := (hc_spec c hc).2.2.closedEdge_subset_D e he
    rw [((hc_spec c hc).2.2.openEdge_eq_diff e he)]
    ext x
    simp only [mem_sdiff]
    refine and_congr_right fun hx_edge => not_congr ?_
    calc x ∈ V' ↔ x ∈ closure c ∩ V' := ⟨fun h => ⟨hsub hx_edge, h⟩, fun h => h.2⟩
      _ ↔ x ∈ V_c c := by rw [hcl_inter_V' c hc]
  -- Collection of open edges 𝒥
  let 𝒥 : Set (Set S) := ⋃ c ∈ ℐ, (openEdge_c c) '' (α_cell c).edgeSet
  have h𝒥_fin : 𝒥.Finite :=
    hℐ_fin.biUnion fun c _ => (α_cell c).edgeSet_finite.image (openEdge_c c)
  have hcov : ⋃₀ 𝒥 = U' \ V' := by
    ext x
    simp only [𝒥, U', mem_sUnion, mem_iUnion, mem_image, exists_prop, mem_sdiff, mem_union]
    constructor
    · rintro ⟨_, ⟨c, hc, e, he, rfl⟩, hxo⟩
      rw [← hclosed_diff_V' c hc e he] at hxo
      exact ⟨Or.inr ⟨c, hc, e, he, hxo.1⟩, hxo.2⟩
    · rintro ⟨hxV' | ⟨c, hc, e, he, hxc⟩, hx_not_V'⟩
      · exact (hx_not_V' hxV').elim
      · refine ⟨openEdge_c c e, ⟨c, hc, e, he, rfl⟩, ?_⟩
        rw [← hclosed_diff_V' c hc e he]
        exact ⟨hxc, hx_not_V'⟩
  -- Pairwise disjointness of openEdge_c c e across all (c, e)
  have hopen_disj_all : ∀ c₁ ∈ ℐ, ∀ e₁ ∈ (α_cell c₁).edgeSet,
      ∀ c₂ ∈ ℐ, ∀ e₂ ∈ (α_cell c₂).edgeSet,
      (c₁ ≠ c₂ ∨ e₁ ≠ e₂) → Disjoint (openEdge_c c₁ e₁) (openEdge_c c₂ e₂) := by
    intro c₁ hc₁ e₁ he₁ c₂ hc₂ e₂ he₂ hne
    by_cases hc_eq : c₁ = c₂
    · subst hc_eq
      exact (hc_spec c₁ hc₁).2.2.openEdge_disjoint e₁ he₁ e₂ he₂ (hne.resolve_left ( not_not.mpr rfl))
    · exact (Γ.cell_disjoint (hℐ_sub hc₁) (hℐ_sub hc₂) hc_eq).mono
        (hopen_sub_c c₁ hc₁ e₁ he₁) (hopen_sub_c c₂ hc₂ e₂ he₂)
  have hopen_inj_all : ∀ c₁ ∈ ℐ, ∀ e₁ ∈ (α_cell c₁).edgeSet,
      ∀ c₂ ∈ ℐ, ∀ e₂ ∈ (α_cell c₂).edgeSet,
      openEdge_c c₁ e₁ = openEdge_c c₂ e₂ → c₁ = c₂ ∧ e₁ = e₂ := by
    intro c₁ hc₁ e₁ he₁ c₂ hc₂ e₂ he₂ hEq
    by_contra hnot
    rw [not_and_or] at hnot
    have hdisj := hopen_disj_all c₁ hc₁ e₁ he₁ c₂ hc₂ e₂ he₂ hnot
    obtain ⟨x, hx⟩ := (hc_spec c₁ hc₁).2.2.openEdge_nonempty e₁ he₁
    exact Set.disjoint_left.mp hdisj hx (hEq ▸ hx)
  have hE_eq : arcComponentsIn (U' \ V') = 𝒥 := by
    apply arcComponentsIn_eq_of_finite_cover h𝒥_fin hcov
    · intro J hJ
      simp only [𝒥, mem_iUnion, mem_image, exists_prop] at hJ
      rcases hJ with ⟨c, hc, e, he, rfl⟩
      exact (hc_spec c hc).2.2.openEdge_nonempty e he
    · intro J hJ
      simp only [𝒥, mem_iUnion, mem_image, exists_prop] at hJ
      rcases hJ with ⟨c, hc, e, he, rfl⟩
      exact (hc_spec c hc).2.2.openEdge_isPathConnected e he
    · intro J₁ hJ₁ J₂ hJ₂ hne
      simp only [𝒥, mem_iUnion, mem_image, exists_prop] at hJ₁ hJ₂
      rcases hJ₁ with ⟨c₁, hc₁, e₁, he₁, rfl⟩
      rcases hJ₂ with ⟨c₂, hc₂, e₂, he₂, rfl⟩
      have h_ne_pair : c₁ ≠ c₂ ∨ e₁ ≠ e₂ := by
        by_contra h_and
        push Not at h_and
        exact hne (by rw [h_and.1, h_and.2])
      exact hopen_disj_all c₁ hc₁ e₁ he₁ c₂ hc₂ e₂ he₂ h_ne_pair
    · intro J hJ
      simp only [𝒥, mem_iUnion, mem_image, exists_prop] at hJ
      rcases hJ with ⟨c, hc, e, he, rfl⟩
      rw [(hc_spec c hc).2.2.closure_openEdge e he]
      refine Subset.antisymm ?_ ?_
      · rintro x ⟨hxc, _, hx_not_V'⟩
        rw [← hclosed_diff_V' c hc e he]
        exact ⟨hxc, hx_not_V'⟩
      · intro x hxo
        rw [← hclosed_diff_V' c hc e he] at hxo
        exact ⟨hxo.1, ⟨Or.inr (mem_biUnion hc (mem_biUnion he hxo.1)), hxo.2⟩⟩
  let Γ' : Surface.Drawing S :=
    { U := U'
      V := V'
      V_subset_U := subset_union_left
      isClosed_U := hU'_closed
      finite_V := hV'_fin
      finite_edges := hE_eq ▸ h𝒥_fin
      edge_cond := by
        intro J hJ
        rw [hE_eq] at hJ
        simp only [𝒥, mem_iUnion, mem_image, exists_prop] at hJ
        rcases hJ with ⟨c, hc, e, he, rfl⟩
        rw [(hc_spec c hc).2.2.closure_openEdge e he, hclosed_inter_V' c hc e he]
        exact (hc_spec c hc).2.2.edge_cond e he }
  -- Properness and boundary vertices of Γ'
  have hV'_bd : Γ'.V ∩ bd S = Γ.N ∩ bd S := by
    ext x
    simp only [Γ', V', mem_inter_iff, mem_union, mem_iUnion]
    refine ⟨?_, fun ⟨hxN, hxbd⟩ => ⟨Or.inl hxN, hxbd⟩⟩
    rintro ⟨hxN | ⟨c, hc, hxV⟩, hxbd⟩
    · exact ⟨hxN, hxbd⟩
    · by_cases hxt : x ∈ tilde c
      · exact ⟨Γ.tilde_subset_N (hℐ_sub hc) hxt, hxbd⟩
      · have hxc : x ∈ c := hVc_diff_sub_c c hc ⟨hxV, hxt⟩
        exact (Set.disjoint_left.mp (hℐ_int c hc).2 hxc hxbd).elim
  have hΓ'_proper : Γ'.IsProper := by
    rintro x ⟨hxbd, hxV' | hx_edges⟩
    · exact hxV'
    · rw [mem_iUnion₂] at hx_edges
      rcases hx_edges with ⟨c, hc, hx_e⟩
      rw [mem_iUnion₂] at hx_e
      rcases hx_e with ⟨e, he, hxc_edge⟩
      by_cases hxV' : x ∈ V'
      · exact hxV'
      · have hxo : x ∈ openEdge_c c e := by
          rw [← hclosed_diff_V' c hc e he]
          exact ⟨hxc_edge, hxV'⟩
        have hxc : x ∈ c := hopen_sub_c c hc e he hxo
        exact (Set.disjoint_left.mp (hℐ_int c hc).2 hxc hxbd).elim
  -- Define ιV' : S → α
  let ιV' : S → α := fun x =>
    if hx : ∃ c ∈ ℐ, x ∈ V_c c \ tilde c then
      ιV_c (Classical.choose hx) x
    else
      ιN x
  have hιV'_N : ∀ x ∈ Γ.N, ιV' x = ιN x := by
    intro x hxN
    have hnot : ¬ ∃ c ∈ ℐ, x ∈ V_c c \ tilde c := by
      rintro ⟨c, hc, hxV, hxt⟩
      exact hxt (hVc_inter_N c hc ▸ ⟨hxV, hxN⟩)
    simp only [ιV', hnot, ↓reduceDIte]
  have hιV'_Vc : ∀ c ∈ ℐ, ∀ x ∈ V_c c, ιV' x = ιV_c c x := by
    intro c hc x hxV
    by_cases hxt : x ∈ tilde c
    · rw [hιV'_N x (Γ.tilde_subset_N (hℐ_sub hc) hxt), hιVc_on_tilde c hc x hxt]
    · have hx_ex : ∃ c' ∈ ℐ, x ∈ V_c c' \ tilde c' := ⟨c, hc, hxV, hxt⟩
      simp only [ιV', hx_ex, ↓reduceDIte]
      obtain ⟨hc', hxV', hxt'⟩ := Classical.choose_spec hx_ex
      have h_eq_c : Classical.choose hx_ex = c := by
        by_contra hne
        exact Set.disjoint_left.mp (Γ.cell_disjoint (hℐ_sub hc') (hℐ_sub hc) hne)
          (hVc_diff_sub_c _ hc' ⟨hxV', hxt'⟩) (hVc_diff_sub_c c hc ⟨hxV, hxt⟩)
      rw [h_eq_c]
  have hιV'_inj : InjOn ιV' Γ'.V := by
    have hV'_decomp : ∀ x ∈ Γ'.V, x ∈ Γ.N ∨ ∃ c ∈ ℐ, x ∈ V_c c \ tilde c := by
      rintro x (hxN | hxV_all)
      · exact Or.inl hxN
      · rw [mem_iUnion₂] at hxV_all
        rcases hxV_all with ⟨c, hc, hxV⟩
        by_cases hxt : x ∈ tilde c
        · exact Or.inl (Γ.tilde_subset_N (hℐ_sub hc) hxt)
        · exact Or.inr ⟨c, hc, hxV, hxt⟩
    intro x₁ hx₁ x₂ hx₂ hEq
    rcases hV'_decomp x₁ hx₁ with hx₁N | ⟨c₁, hc₁, hx₁V, hx₁t⟩ <;>
      rcases hV'_decomp x₂ hx₂ with hx₂N | ⟨c₂, hc₂, hx₂V, hx₂t⟩
    · rw [hιV'_N x₁ hx₁N, hιV'_N x₂ hx₂N] at hEq
      exact hport.r1_injOn hx₁N hx₂N hEq
    · rw [hιV'_N x₁ hx₁N, hιV'_Vc c₂ hc₂ x₂ hx₂V] at hEq
      exact (hιVc_diff_not_N c₂ hc₂ x₂ ⟨hx₂V, hx₂t⟩ ⟨x₁, hx₁N, hEq⟩).elim
    · rw [hιV'_Vc c₁ hc₁ x₁ hx₁V, hιV'_N x₂ hx₂N] at hEq
      exact (hιVc_diff_not_N c₁ hc₁ x₁ ⟨hx₁V, hx₁t⟩ ⟨x₂, hx₂N, hEq.symm⟩).elim
    · rw [hιV'_Vc c₁ hc₁ x₁ hx₁V, hιV'_Vc c₂ hc₂ x₂ hx₂V] at hEq
      by_cases hc_eq : c₁ = c₂
      · subst hc_eq
        exact (hc_spec c₁ hc₁).2.2.ιV_injOn hx₁V hx₂V hEq
      · have hw₁ : ιV_c c₁ x₁ ∈ (α_cell c₁).vertexSet := by
          rw [← (hc_spec c₁ hc₁).2.2.ιV_image]; exact mem_image_of_mem _ hx₁V
        have hw₂ : ιV_c c₁ x₁ ∈ (α_cell c₂).vertexSet := by
          rw [hEq, ← (hc_spec c₂ hc₂).2.2.ιV_image]; exact mem_image_of_mem _ hx₂V
        have hno_cuff : ∀ C ∈ cuffs S, ¬ ((c₁ ∩ C).Nonempty ∧ (c₂ ∩ C).Nonempty) := by
          intro C hC ⟨⟨z, hzc₁, hzC⟩, _⟩
          have hzbd : z ∈ bd S := by rw [← sUnion_cuffs (S := S)]; exact ⟨C, hC, hzC⟩
          exact Set.disjoint_left.mp (hℐ_int c₁ hc₁).2 hzc₁ hzbd
        have hw_inter : ιV_c c₁ x₁ ∈ (α_cell c₁ ∩ α_cell c₂).vertexSet := ⟨hw₁, hw₂⟩
        rw [hport.r7_inter c₁ (hℐ_sub hc₁) c₂ (hℐ_sub hc₂) hc_eq hno_cuff] at hw_inter
        have hw_N : ιV_c c₁ x₁ ∈ ιN '' Γ.N :=
          image_mono (inter_subset_left.trans (Γ.tilde_subset_N (hℐ_sub hc₁))) hw_inter
        exact (hιVc_diff_not_N c₁ hc₁ x₁ ⟨hx₁V, hx₁t⟩ hw_N).elim
  have hιV'_img : ιV' '' Γ'.V = Γ'_sub.vertexSet := by
    rw [hΓ'_sub_V]
    change ιV' '' (Γ.N ∪ ⋃ c ∈ ℐ, V_c c) = _
    rw [image_union, image_congr hιV'_N, image_iUnion₂]
    congr 1
    refine iUnion₂_congr fun c hc => ?_
    rw [image_congr (hιV'_Vc c hc), (hc_spec c hc).2.2.ιV_image]
  -- Define ιE' : Set S → β
  let ιE' : Set S → β := fun J =>
    if hJ : ∃ c ∈ ℐ, ∃ e ∈ (α_cell c).edgeSet, openEdge_c c e = J then
      Classical.choose (Classical.choose_spec hJ).2
    else
      e₀
  have hιE'_open : ∀ c ∈ ℐ, ∀ e ∈ (α_cell c).edgeSet, ιE' (openEdge_c c e) = e := by
    intro c hc e he
    have hJ : ∃ c' ∈ ℐ, ∃ e' ∈ (α_cell c').edgeSet, openEdge_c c' e' = openEdge_c c e :=
      ⟨c, hc, e, he, rfl⟩
    simp only [ιE', hJ, ↓reduceDIte]
    let c' := Classical.choose hJ
    obtain ⟨hc', hJ2⟩ := Classical.choose_spec hJ
    let e' := Classical.choose hJ2
    obtain ⟨he', h_eq⟩ := Classical.choose_spec hJ2
    exact (hopen_inj_all c' hc' e' he' c hc e he h_eq).2
  have hιE'_inj : InjOn ιE' Γ'.E := by
    intro J₁ hJ₁ J₂ hJ₂ hEq
    change J₁ ∈ arcComponentsIn (U' \ V') at hJ₁
    change J₂ ∈ arcComponentsIn (U' \ V') at hJ₂
    rw [hE_eq] at hJ₁ hJ₂
    simp only [𝒥, mem_iUnion, mem_image, exists_prop] at hJ₁ hJ₂
    rcases hJ₁ with ⟨c₁, hc₁, e₁, he₁, rfl⟩
    rcases hJ₂ with ⟨c₂, hc₂, e₂, he₂, rfl⟩
    rw [hιE'_open c₁ hc₁ e₁ he₁, hιE'_open c₂ hc₂ e₂ he₂] at hEq
    subst hEq
    have hc_eq : c₁ = c₂ := by
      by_contra hne
      exact Set.disjoint_left.mp (hport.r3_edge_disjoint c₁ (hℐ_sub hc₁) c₂ (hℐ_sub hc₂) hne)
        he₁ he₂
    subst hc_eq
    rfl
  have hιE'_img : ιE' '' Γ'.E = Γ'_sub.edgeSet := by
    rw [hΓ'_sub_E]
    change ιE' '' arcComponentsIn (U' \ V') = _
    rw [hE_eq]
    dsimp only [𝒥]
    rw [image_iUnion₂]
    refine iUnion₂_congr fun c hc => ?_
    ext e
    simp only [mem_image, exists_exists_and_eq_and]
    constructor
    · rintro ⟨e', he', rfl⟩
      rwa [hιE'_open c hc e' he']
    · intro he
      exact ⟨e, he, hιE'_open c hc e he⟩
  -- Incidence correspondence
  have hinc_iff : ∀ J ∈ Γ'.E, ∀ u ∈ Γ'.V, Γ'_sub.Inc (ιE' J) (ιV' u) ↔ u ∈ closure J := by
    intro J hJ u hu
    change J ∈ arcComponentsIn (U' \ V') at hJ
    rw [hE_eq] at hJ
    simp only [𝒥, mem_iUnion, mem_image, exists_prop] at hJ
    rcases hJ with ⟨c, hc, e, he, rfl⟩
    rw [hιE'_open c hc e he, (hc_spec c hc).2.2.closure_openEdge e he]
    have he_Γ' : e ∈ Γ'_sub.edgeSet := by rw [hΓ'_sub_E]; exact mem_biUnion hc he
    have hα_le : α_cell c ≤ G := hport.r2_cell_le c (hℐ_sub hc)
    rw [hΓ'_sub_inc e he_Γ', ← GM10.inc_iff_of_le hα_le he]
    by_cases hu_Vc : u ∈ V_c c
    · rw [hιV'_Vc c hc u hu_Vc]
      exact (hc_spec c hc).2.2.inc_iff e he u hu_Vc
    · constructor
      · intro hinc_c
        have h_in_V : ιV' u ∈ (α_cell c).vertexSet := (α_cell c).vertex_mem_of_inc hinc_c
        rw [← (hc_spec c hc).2.2.ιV_image] at h_in_V
        rcases h_in_V with ⟨u', hu'_Vc, h_eq⟩
        rw [← hιV'_Vc c hc u' hu'_Vc] at h_eq
        have hu'_V' : u' ∈ Γ'.V := Or.inr (mem_biUnion hc hu'_Vc)
        have hu_eq : u = u' := hιV'_inj hu hu'_V' h_eq.symm
        exact (hu_Vc (hu_eq ▸ hu'_Vc)).elim
      · intro hu_edge
        have hu_cl : u ∈ closure c := (hc_spec c hc).2.2.closedEdge_subset_D e he hu_edge
        have : u ∈ V_c c := hcl_inter_V' c hc ▸ ⟨hu_cl, hu⟩
        exact (hu_Vc this).elim
  exact ⟨Γ', ιV', ιE', hΓ'_proper, hV'_bd, hιV'_N,
    ⟨hιV'_inj, hιV'_img, hιE'_inj, hιE'_img, hinc_iff⟩⟩

/-- Any hypergraph `G` admitting a tangle `𝒯` of order `θ ≥ 2` has at least one edge. -/
theorem exists_edge_of_isTangle {α : Type u} {β : Type v} {G : Hypergraph α β}
    {θ : ℕ} {𝒯 : Set (Hypergraph α β × Hypergraph α β)}
    (h𝒯 : IsTangle G θ 𝒯) (hθ : 2 ≤ θ) : G.edgeSet.Nonempty := by
  have hsep_bot : G.IsSeparation ⊥ G := by
    rw [GM10.isSeparation_iff_of_le bot_le le_rfl]
    simp
  have hord_bot : separationOrder (⊥ : Hypergraph α β) G < θ := by
    have : separationOrder (⊥ : Hypergraph α β) G = 0 := by
      simp [separationOrder]
    omega
  have hbot_mem : (⊥, G) ∈ 𝒯 :=
    (h𝒯.axiom1 hsep_bot hord_bot).resolve_right fun hG => h𝒯.axiom3 hG rfl
  have hne := GM10.theorem_2_3_proof h𝒯 hθ hbot_mem hbot_mem hbot_mem
  rw [Set.nonempty_iff_ne_empty]
  intro hE_empty
  apply hne
  rw [hE_empty]
  simp

end GraphMinor.GM21
