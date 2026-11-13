module

public import GraphMinor.GM01.Basic
public import GraphMinor.GM05.Defs
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Nat.ModEq
import Mathlib.Tactic.Ring

/-!
# Basic Lemmas for Graph Minors V

This file provides the basic infrastructure for Graph Minors V:

- The reduction in Section 2 (`mem_𝓕_of_not_isIsoMinor`): if `G` has no minor isomorphic to `H` and
  `H` is isomorphic to a minor of `gridGraph θ`, then `G ∈ 𝓕_θ`.
- Unfolding, monotonicity, parity, and positivity lemmas for the parameters `α`, `θ₁, …, θ₉`,
  `φ_k`, and `ψ_k` of Sections 2 and 4.
- Basic properties of separations `(V₁, V₂)` (`IsSeparation`), including constructing a separation
  `(V₁, V₂)` with `V₁ ∩ V₂ = X`, `A ⊆ V₁`, and `B ⊆ V₂` from any set `X` separating `A` and `B`
  (`exists_isSeparation_of_separates`), and localization of connected subgraphs avoiding `V₁ ∩ V₂`.
- Basic properties of connected components (`IsComponentOf`) and vertex weights (`weightSum`).
-/

@[expose] public section

namespace GraphMinor.GM05

open SimpleGraph Graph Set Relation GM01

variable {V : Type*}

/-! ## Section 2: Reduction to Grid Minors -/

/-- The reduction in Graph Minors V, Section 2 (page 95):
"To prove this, we observe that if $G$ has no minor isomorphic to $H$ then $G$ certainly has
no minor isomorphic to the $\theta$-grid, where $\theta = \theta(H)$." -/
theorem mem_𝓕_of_not_isIsoMinor {α' β' : Type*} {H : Graph α' β'}
    {G : (⊤ : SimpleGraph V).Subgraph} {θ : ℕ}
    (hGH : ¬ IsIsoMinor H (toGraph G)) (hHgrid : IsIsoMinor H (gridGraph θ)) :
    G ∈ 𝓕 θ :=
  fun hgridG ↦ hGH (hHgrid.trans hgridG)

/-! ## Section 2 and Section 4 Parameters: `α`, `φ_k`, `ψ_k`, and `θ₁, …, θ₉` -/

@[simp]
theorem α_zero (θ n : ℕ) : α θ 0 n = n + 1 := rfl

@[simp]
theorem α_one (θ n : ℕ) : α θ 1 n = n + 1 := rfl

@[simp]
theorem α_two (θ n : ℕ) : α θ 2 n = n + 1 := rfl

theorem α_succ_of_two_le (θ : ℕ) {k : ℕ} (hk : 2 ≤ k) (n : ℕ) :
    α θ (k + 1) n = 2 ^ (n * θ ^ 4) + α θ k (2 ^ (n * θ ^ 4) + n + 1) := by
  have hk_eq : k = (k - 2) + 2 := by omega
  rw [hk_eq]
  rfl

theorem α_of_three_le (θ : ℕ) {k : ℕ} (hk : 3 ≤ k) (n : ℕ) :
    α θ k n = 2 ^ (n * θ ^ 4) + α θ (k - 1) (2 ^ (n * θ ^ 4) + n + 1) := by
  have hk' : k = (k - 1) + 1 := (Nat.sub_add_cancel (by omega)).symm
  conv_lhs => rw [hk']
  exact α_succ_of_two_le θ (by omega) n

theorem le_α (θ : ℕ) : ∀ k n : ℕ, n + 1 ≤ α θ k n
  | 0, _ => le_rfl
  | 1, _ => le_rfl
  | 2, _ => le_rfl
  | k + 3, n => by
    change n + 1 ≤ 2 ^ (n * θ ^ 4) + α θ (k + 2) (2 ^ (n * θ ^ 4) + n + 1)
    have h := le_α θ (k + 2) (2 ^ (n * θ ^ 4) + n + 1)
    generalize 2 ^ (n * θ ^ 4) = B at h ⊢
    omega

theorem α_pos (θ k n : ℕ) : 0 < α θ k n :=
  Nat.lt_of_lt_of_le (Nat.succ_pos n) (le_α θ k n)

theorem α_mono_right (θ : ℕ) : ∀ (k : ℕ) {n m : ℕ}, n ≤ m → α θ k n ≤ α θ k m
  | 0, _, _, hnm => by simpa using hnm
  | 1, _, _, hnm => by simpa using hnm
  | 2, _, _, hnm => by simpa using hnm
  | k + 3, n, m, hnm => by
    change 2 ^ (n * θ ^ 4) + α θ (k + 2) (2 ^ (n * θ ^ 4) + n + 1) ≤
      2 ^ (m * θ ^ 4) + α θ (k + 2) (2 ^ (m * θ ^ 4) + m + 1)
    have hpow : 2 ^ (n * θ ^ 4) ≤ 2 ^ (m * θ ^ 4) :=
      Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_right (θ ^ 4) hnm)
    have harg : 2 ^ (n * θ ^ 4) + n + 1 ≤ 2 ^ (m * θ ^ 4) + m + 1 :=
      Nat.add_le_add (Nat.add_le_add hpow hnm) le_rfl
    exact Nat.add_le_add hpow (α_mono_right θ (k + 2) harg)

theorem α_le_α_succ (θ k n : ℕ) : α θ k n ≤ α θ (k + 1) n := by
  rcases k with _ | _ | k
  · rfl
  · rfl
  · change α θ (k + 2) n ≤ 2 ^ (n * θ ^ 4) + α θ (k + 2) (2 ^ (n * θ ^ 4) + n + 1)
    have hle : n ≤ 2 ^ (n * θ ^ 4) + n + 1 := by
      generalize 2 ^ (n * θ ^ 4) = B
      omega
    exact (α_mono_right θ (k + 2) hle).trans (Nat.le_add_left _ _)

theorem α_mono_left (θ : ℕ) {k k' : ℕ} (h : k ≤ k') (n : ℕ) : α θ k n ≤ α θ k' n := by
  induction h with
  | refl => exact le_rfl
  | @step m _ ih => exact ih.trans (α_le_α_succ θ m n)

theorem add_le_α (θ : ℕ) : ∀ {k : ℕ}, 2 ≤ k → ∀ n : ℕ, k - 1 + n ≤ α θ k n
  | 2, _, n => by simp [Nat.add_comm]
  | k + 3, _, n => by
    change k + 2 + n ≤ 2 ^ (n * θ ^ 4) + α θ (k + 2) (2 ^ (n * θ ^ 4) + n + 1)
    have ih := add_le_α θ (Nat.le_add_left 2 k) (2 ^ (n * θ ^ 4) + n + 1)
    generalize 2 ^ (n * θ ^ 4) = B at ih ⊢
    omega

theorem self_le_α_of_three_le (θ : ℕ) {k : ℕ} (hk : 3 ≤ k) (n : ℕ) : k ≤ α θ k n := by
  rw [α_of_three_le θ hk n]
  have h1 := add_le_α θ (show 2 ≤ k - 1 by omega) (2 ^ (n * θ ^ 4) + n + 1)
  have h2 : 1 ≤ 2 ^ (n * θ ^ 4) := Nat.one_le_pow _ 2 (by decide)
  generalize 2 ^ (n * θ ^ 4) = B at h1 h2 ⊢
  omega

theorem θ₁_pos (θ : ℕ) : 0 < θ₁ θ := by
  unfold θ₁
  have := α_pos θ (θ ^ 2 / 2) (θ ^ 2 / 2)
  omega

@[simp]
theorem φ_θ₁ (θ : ℕ) : φ θ (θ₁ θ) = θ ^ 2 / 2 := by
  simp [φ, φAux]

theorem φ_of_lt (θ : ℕ) {k : ℕ} (hk : k < θ₁ θ) :
    φ θ k = φ θ (k + 1) * 2 ^ (φ θ (k + 1) * θ ^ 2) := by
  unfold φ
  have hsub : θ₁ θ - k = (θ₁ θ - (k + 1)) + 1 := by omega
  rw [hsub]
  rfl

theorem eighteen_le_half_θ_sq {θ : ℕ} (hθ : 6 ≤ θ) : 18 ≤ θ ^ 2 / 2 := by
  have h36 : 36 ≤ θ ^ 2 := by
    calc 36 = 6 ^ 2 := by norm_num
    _ ≤ θ ^ 2 := Nat.pow_le_pow_left hθ 2
  omega

theorem half_θ_sq_pos {θ : ℕ} (hθ : 6 ≤ θ) : 0 < θ ^ 2 / 2 := by
  have := eighteen_le_half_θ_sq hθ
  omega

theorem two_mul_half_θ_sq {θ : ℕ} (heven : Even θ) : 2 * (θ ^ 2 / 2) = θ ^ 2 := by
  obtain ⟨m, rfl⟩ := heven
  have h : (m + m) ^ 2 = 2 * (2 * m ^ 2) := by ring
  rw [h, Nat.mul_div_cancel_left _ (by decide)]

theorem half_θ_sq_mul_two {θ : ℕ} (heven : Even θ) : (θ ^ 2 / 2) * 2 = θ ^ 2 := by
  rw [Nat.mul_comm, two_mul_half_θ_sq heven]

theorem even_half_θ_sq {θ : ℕ} (heven : Even θ) : Even (θ ^ 2 / 2) := by
  obtain ⟨m, rfl⟩ := heven
  have h : (m + m) ^ 2 = 2 * (2 * m ^ 2) := by ring
  rw [h, Nat.mul_div_cancel_left _ (by decide)]
  exact ⟨m ^ 2, by ring⟩

theorem φAux_pos {θ : ℕ} (hθ : 6 ≤ θ) : ∀ d : ℕ, 0 < φAux θ d
  | 0 => half_θ_sq_pos hθ
  | d + 1 => by
    change 0 < φAux θ d * 2 ^ (φAux θ d * θ ^ 2)
    exact Nat.mul_pos (φAux_pos hθ d) (Nat.two_pow_pos _)

theorem φ_pos {θ : ℕ} (hθ : 6 ≤ θ) (k : ℕ) : 0 < φ θ k :=
  φAux_pos hθ (θ₁ θ - k)

theorem φ_zero_le_θ₂ (θ : ℕ) : φ θ 0 ≤ θ₂ θ := by
  unfold θ₂
  omega

theorem φ_θ₁_le_θ₂ (θ : ℕ) : φ θ (θ₁ θ) ≤ θ₂ θ := by
  unfold θ₂
  omega

@[simp]
theorem ψ_θ₁ (θ : ℕ) : ψ θ (θ₁ θ) = 0 := by
  simp [ψ]

theorem ψ_zero (θ : ℕ) : ψ θ 0 = θ₂ θ := by
  unfold ψ θ₂
  simp only [θ₁_pos θ, ↓reduceIte]

theorem ψ_of_lt (θ : ℕ) {k : ℕ} (hk : k < θ₁ θ) :
    ψ θ k = ψ θ (k + 1) + φ θ k + φ θ (k + 1) := by
  unfold ψ
  simp only [hk, ↓reduceIte]
  by_cases hk1 : k + 1 < θ₁ θ
  · simp only [hk1, ↓reduceIte]
    have hIco : Finset.Ico (k + 1) (θ₁ θ) = insert (k + 1) (Finset.Ico (k + 1 + 1) (θ₁ θ)) := by
      ext x
      simp only [Finset.mem_Ico, Finset.mem_insert]
      omega
    have hnotMem : k + 1 ∉ Finset.Ico (k + 1 + 1) (θ₁ θ) := by simp
    rw [hIco, Finset.sum_insert hnotMem]
    omega
  · have heq : k + 1 = θ₁ θ := by omega
    simp only [hk1, ↓reduceIte]
    rw [heq, Finset.Ico_self, Finset.sum_empty]
    omega

theorem eighteen_le_θ₂ {θ : ℕ} (hθ : 6 ≤ θ) : 18 ≤ θ₂ θ := by
  have h1 := eighteen_le_half_θ_sq hθ
  have h2 := φ_θ₁_le_θ₂ θ
  rw [φ_θ₁] at h2
  omega

theorem two_le_θ₂ {θ : ℕ} (hθ : 6 ≤ θ) : 2 ≤ θ₂ θ := by
  have := eighteen_le_θ₂ hθ
  omega

private lemma lt_pow_pred {a b : ℕ} (ha : 18 ≤ a) (hb : 2 ≤ b) : b < a ^ (b - 1) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hb
  clear hb
  have haux : ∀ m : ℕ, 2 + m < a ^ (1 + m) := by
    intro m
    induction m with
    | zero =>
      simp only [Nat.add_zero, pow_one]
      omega
    | succ m ih =>
      have h1 : 2 + (m + 1) = (2 + m) + 1 := by omega
      have h2 : 1 + (m + 1) = (1 + m) + 1 := by omega
      rw [h1, h2, pow_succ]
      have hpos : 1 ≤ a ^ (1 + m) := Nat.one_le_pow _ a (by omega)
      have hmul : (2 + m) + 2 ≤ a ^ (1 + m) * 18 := by
        generalize a ^ (1 + m) = P at ih hpos
        omega
      exact Nat.lt_of_lt_of_le (Nat.lt_succ_self _)
        (hmul.trans (Nat.mul_le_mul_left _ ha))
  have hsub : 2 + m - 1 = 1 + m := by omega
  rw [hsub]
  exact haux m

theorem θ₂_lt_θ₃ {θ : ℕ} (hθ : 6 ≤ θ) : θ₂ θ < θ₃ θ :=
  lt_pow_pred (eighteen_le_half_θ_sq hθ) (two_le_θ₂ hθ)

theorem two_le_θ₃ {θ : ℕ} (hθ : 6 ≤ θ) : 2 ≤ θ₃ θ := by
  have h1 := two_le_θ₂ hθ
  have h2 := θ₂_lt_θ₃ hθ
  omega

theorem eighteen_le_θ₄ {θ : ℕ} (hθ : 6 ≤ θ) : 18 ≤ θ₄ θ := by
  unfold θ₄
  have hle : θ₂ θ ≤ θ₃ θ := Nat.le_of_lt (θ₂_lt_θ₃ hθ)
  have hch : 1 ≤ (θ₃ θ).choose (θ₂ θ) := Nat.choose_pos hle
  have h18 := eighteen_le_θ₂ hθ
  have hprod : 18 ≤ θ₂ θ * (θ₃ θ).choose (θ₂ θ) := by
    calc 18 ≤ θ₂ θ * 1 := by omega
    _ ≤ θ₂ θ * (θ₃ θ).choose (θ₂ θ) := Nat.mul_le_mul_left _ hch
  omega

theorem two_le_θ₄ {θ : ℕ} (hθ : 6 ≤ θ) : 2 ≤ θ₄ θ := by
  have := eighteen_le_θ₄ hθ
  omega

theorem θ₄_lt_θ₅ {θ : ℕ} (hθ : 6 ≤ θ) : θ₄ θ < θ₅ θ :=
  lt_pow_pred (eighteen_le_half_θ_sq hθ) (two_le_θ₄ hθ)

theorem eighteen_le_θ₅ {θ : ℕ} (hθ : 6 ≤ θ) : 18 ≤ θ₅ θ := by
  have h1 := eighteen_le_θ₄ hθ
  have h2 := θ₄_lt_θ₅ hθ
  omega

theorem two_le_θ₅ {θ : ℕ} (hθ : 6 ≤ θ) : 2 ≤ θ₅ θ := by
  have := eighteen_le_θ₅ hθ
  omega

theorem three_le_θ₅ {θ : ℕ} (hθ : 6 ≤ θ) : 3 ≤ θ₅ θ := by
  have := eighteen_le_θ₅ hθ
  omega

theorem θ₅_pos {θ : ℕ} (hθ : 6 ≤ θ) : 0 < θ₅ θ := by
  have := eighteen_le_θ₅ hθ
  omega

theorem even_θ₅ {θ : ℕ} (hθ : 6 ≤ θ) (heven : Even θ) : Even (θ₅ θ) := by
  unfold θ₅
  have h4 := two_le_θ₄ hθ
  have hne : θ₄ θ - 1 ≠ 0 := by omega
  exact (even_half_θ_sq heven).pow_of_ne_zero hne

theorem four_dvd_three_mul_θ₅_mul_pow_sub_one {θ : ℕ} (hθ : 6 ≤ θ) (heven : Even θ) :
    4 ∣ 3 * θ₅ θ * (3 ^ θ₅ θ - 1) := by
  obtain ⟨m, hm⟩ := even_θ₅ hθ heven
  have h_odd : Odd (3 ^ θ₅ θ) := Odd.pow (by decide)
  obtain ⟨k, hk⟩ := h_odd
  have hsub : 3 ^ θ₅ θ - 1 = 2 * k := by omega
  refine ⟨3 * m * k, ?_⟩
  rw [hsub, hm]
  ring

theorem four_mul_θ₈ {θ : ℕ} (hθ : 6 ≤ θ) (heven : Even θ) :
    4 * θ₈ θ = 3 * θ₅ θ * (3 ^ θ₅ θ - 1) := by
  unfold θ₈
  exact Nat.mul_div_cancel' (four_dvd_three_mul_θ₅_mul_pow_sub_one hθ heven)

theorem three_le_θ₈ {θ : ℕ} (hθ : 6 ≤ θ) (heven : Even θ) : 3 ≤ θ₈ θ := by
  have h4 := four_mul_θ₈ hθ heven
  have h5 := two_le_θ₅ hθ
  have hpow : 9 ≤ 3 ^ θ₅ θ := by
    calc 9 = 3 ^ 2 := by norm_num
    _ ≤ 3 ^ θ₅ θ := Nat.pow_le_pow_right (by decide) h5
  have hmul : 48 ≤ 3 * θ₅ θ * (3 ^ θ₅ θ - 1) := by
    calc 48 = 3 * 2 * 8 := by norm_num
    _ ≤ 3 * θ₅ θ * (3 ^ θ₅ θ - 1) :=
      Nat.mul_le_mul (Nat.mul_le_mul_left 3 h5) (by omega)
  omega

theorem θ₈_pos {θ : ℕ} (hθ : 6 ≤ θ) (heven : Even θ) : 0 < θ₈ θ := by
  have := three_le_θ₈ hθ heven
  omega

theorem θ₅_le_θ₇ {θ : ℕ} (hθ : 6 ≤ θ) : θ₅ θ ≤ θ₇ θ :=
  self_le_α_of_three_le θ (three_le_θ₅ hθ) (θ₆ θ)

/-! ## Separations of Graphs -/

theorem IsSeparation.symm {G : (⊤ : SimpleGraph V).Subgraph} {V₁ V₂ : Set V}
    (h : IsSeparation G V₁ V₂) : IsSeparation G V₂ V₁ where
  subset_left := h.subset_right
  subset_right := h.subset_left
  union_eq := Set.union_comm V₂ V₁ ▸ h.union_eq
  not_adj _ _ hu hv hadj := h.not_adj hv hu hadj.symm

theorem Separates.symm {G : (⊤ : SimpleGraph V).Subgraph} {X A B : Set V}
    (h : Separates G X A B) : Separates G X B A := by
  intro P hP hav
  apply h P.reverse
  · exact ⟨by simpa using hP.1, hP.2.2, hP.2.1⟩
  · simpa [Path.Avoids] using hav

/-- If `X ⊆ V(G)` separates `A ⊆ V(G)` from `B ⊆ V(G)` in `G`, then there is a separation
`(V₁, V₂)` of `G` with `V₁ ∩ V₂ = X`, `A ⊆ V₁`, and `B ⊆ V₂`
(used in the proofs of (3.2) and (7.1), pages 96 and 107). -/
theorem exists_isSeparation_of_separates {G : (⊤ : SimpleGraph V).Subgraph} {X A B : Set V}
    (hX : X ⊆ G.verts) (hA : A ⊆ G.verts) (hB : B ⊆ G.verts) (hsep : Separates G X A B) :
    ∃ V₁ V₂ : Set V, IsSeparation G V₁ V₂ ∧ V₁ ∩ V₂ = X ∧ A ⊆ V₁ ∧ B ⊆ V₂ := by
  let R : Set V := {v ∈ G.verts \ X | ∃ P : GM01.Path V, P.IsFromTo G A {v} ∧ P.Avoids X}
  have hR_sub : R ⊆ G.verts \ X := fun _ hv ↦ hv.1
  let V₁ : Set V := R ∪ X
  let V₂ : Set V := G.verts \ R
  have hV₁_sub : V₁ ⊆ G.verts := Set.union_subset (hR_sub.trans Set.sdiff_subset) hX
  have hV₂_sub : V₂ ⊆ G.verts := Set.sdiff_subset
  have hunion : V₁ ∪ V₂ = G.verts := by
    ext v
    change (v ∈ R ∨ v ∈ X) ∨ (v ∈ G.verts ∧ v ∉ R) ↔ v ∈ G.verts
    refine ⟨?_, fun hv ↦ ?_⟩
    · rintro ((hvR | hvX) | ⟨hvG, _⟩)
      · exact (hR_sub hvR).1
      · exact hX hvX
      · exact hvG
    · by_cases hvR : v ∈ R
      · exact Or.inl (Or.inl hvR)
      · exact Or.inr ⟨hv, hvR⟩
  have hinter : V₁ ∩ V₂ = X := by
    ext v
    change (v ∈ R ∨ v ∈ X) ∧ (v ∈ G.verts ∧ v ∉ R) ↔ v ∈ X
    refine ⟨?_, fun hvX ↦ ⟨Or.inr hvX, hX hvX, fun hvR ↦ (hR_sub hvR).2 hvX⟩⟩
    rintro ⟨hvR | hvX, _, hnotR⟩
    · exact absurd hvR hnotR
    · exact hvX
  have hnot_adj : ∀ ⦃u v : V⦄, u ∈ V₁ \ V₂ → v ∈ V₂ \ V₁ → ¬ G.Adj u v := by
    intro u v hu hv hadj
    have huR : u ∈ R := by
      rcases hu.1 with huR | huX
      · exact huR
      · exact absurd ⟨hX huX, fun hR' ↦ (hR_sub hR').2 huX⟩ hu.2
    have hvG : v ∈ G.verts := hv.1.1
    have hvnotR : v ∉ R := hv.1.2
    have hvnotX : v ∉ X := fun hvX ↦ hv.2 (Or.inr hvX)
    obtain ⟨_, P, ⟨hPG, hPfirst, hPlast⟩, hPavoid⟩ := huR
    have hPlast' : P.last = u := Set.mem_singleton_iff.1 hPlast
    let w : (⊤ : SimpleGraph V).Walk P.first v :=
      P.walk.append (.cons (hPlast' ▸ hadj.adj_sub) .nil)
    let Q : GM01.Path V := GM01.Path.ofWalk w
    have hQ_le : Q.toSubgraph ≤ G := by
      refine (GM01.Path.ofWalk_toSubgraph_le w).trans ?_
      rw [Walk.toSubgraph_append, Walk.toSubgraph_cons_nil_eq_subgraphOfAdj]
      exact sup_le hPG (subgraphOfAdj_le_of_adj G (hPlast' ▸ hadj))
    have hQ_avoid : Q.Avoids X := by
      rw [GM01.Path.Avoids, Set.disjoint_left]
      intro z hzQ hzX
      have hzw : z ∈ w.toSubgraph.verts := GM01.Path.ofWalk_verts_subset w hzQ
      rw [Walk.toSubgraph_append, Subgraph.verts_sup, Set.mem_union] at hzw
      rcases hzw with hzP | hzv
      · exact Set.disjoint_left.1 hPavoid hzP hzX
      · rw [Walk.toSubgraph_cons_nil_eq_subgraphOfAdj] at hzv
        have hzv' : z = P.last ∨ z = v := by simpa [subgraphOfAdj] using hzv
        rcases hzv' with rfl | rfl
        · exact Set.disjoint_left.1 hPavoid P.last_mem_verts hzX
        · exact hvnotX hzX
    exact hvnotR ⟨⟨hvG, hvnotX⟩, Q, ⟨hQ_le, hPfirst, rfl⟩, hQ_avoid⟩
  refine ⟨V₁, V₂, ⟨hV₁_sub, hV₂_sub, hunion, hnot_adj⟩, hinter, ?_, ?_⟩
  · intro a ha
    by_cases haX : a ∈ X
    · exact Or.inr haX
    · refine Or.inl ⟨⟨hA ha, haX⟩, GM01.Path.singleton a, ?_, ?_⟩
      · refine ⟨?_, ha, rfl⟩
        change (Walk.nil : (⊤ : SimpleGraph V).Walk a a).toSubgraph ≤ G
        simp [hA ha]
      · rw [GM01.Path.Avoids, GM01.Path.singleton_verts, Set.disjoint_singleton_left]
        exact haX
  · intro b hb
    refine ⟨hB hb, ?_⟩
    rintro ⟨_, P, ⟨hPG, hPfirst, hPlast⟩, hPavoid⟩
    have hPlast' : P.last = b := Set.mem_singleton_iff.1 hPlast
    exact hsep P ⟨hPG, hPfirst, hPlast' ▸ hb⟩ hPavoid

/-- If `(V₁, V₂)` is a separation of `G`, and `B ≤ G` is a preconnected subgraph whose vertex set
is disjoint from `V₁ ∩ V₂` and meets `V₁`, then `B.verts ⊆ V₁ \ V₂`. -/
theorem IsSeparation.verts_subset_diff_of_preconnected {G B : (⊤ : SimpleGraph V).Subgraph}
    {V₁ V₂ : Set V} (hsep : IsSeparation G V₁ V₂) (hBG : B ≤ G) (hB : B.Preconnected)
    (hdisj : Disjoint B.verts (V₁ ∩ V₂)) (hmeet : (B.verts ∩ V₁).Nonempty) :
    B.verts ⊆ V₁ \ V₂ := by
  obtain ⟨u₀, hu₀B, hu₀V₁⟩ := hmeet
  have hu₀_notV₂ : u₀ ∉ V₂ := fun hu₀V₂ ↦
    Set.disjoint_left.1 hdisj hu₀B ⟨hu₀V₁, hu₀V₂⟩
  intro v hvB
  obtain ⟨p, hp⟩ := (Subgraph.preconnected_iff_forall_exists_walk_subgraph B).1 hB hu₀B hvB
  have hwalk : ∀ {x y : V} (q : (⊤ : SimpleGraph V).Walk x y),
      q.toSubgraph ≤ B → x ∈ V₁ \ V₂ → y ∈ V₁ \ V₂ := by
    intro x y q hq hx
    induction q with
    | nil => exact hx
    | @cons x z y hxz rest ih =>
      rw [Walk.toSubgraph, sup_le_iff] at hq
      have hadjB : B.Adj x z := hq.1.2 (by simp)
      have hadjG : G.Adj x z := hBG.2 hadjB
      have hzB : z ∈ B.verts := hadjB.snd_mem
      have hzG : z ∈ G.verts := hBG.1 hzB
      rw [← hsep.union_eq] at hzG
      have hz : z ∈ V₁ \ V₂ := by
        rcases hzG with hzV₁ | hzV₂
        · exact ⟨hzV₁, fun hzV₂ ↦ Set.disjoint_left.1 hdisj hzB ⟨hzV₁, hzV₂⟩⟩
        · have hz_notV₁ : z ∉ V₁ := fun hzV₁ ↦ Set.disjoint_left.1 hdisj hzB ⟨hzV₁, hzV₂⟩
          exact absurd hadjG (hsep.not_adj hx ⟨hzV₂, hz_notV₁⟩)
      exact ih hq.2 hz
  exact hwalk p hp ⟨hu₀V₁, hu₀_notV₂⟩

/-- If `(V₁, V₂)` is a separation of `G`, and `B ≤ G` is a preconnected subgraph whose vertex set
is disjoint from `V₁ ∩ V₂` and meets `V₁`, then `B ≤ G.induce (V₁ \ V₂)`. -/
theorem IsSeparation.le_induce_diff_of_preconnected {G B : (⊤ : SimpleGraph V).Subgraph}
    {V₁ V₂ : Set V} (hsep : IsSeparation G V₁ V₂) (hBG : B ≤ G) (hB : B.Preconnected)
    (hdisj : Disjoint B.verts (V₁ ∩ V₂)) (hmeet : (B.verts ∩ V₁).Nonempty) :
    B ≤ G.induce (V₁ \ V₂) := by
  have hsub := hsep.verts_subset_diff_of_preconnected hBG hB hdisj hmeet
  refine ⟨hsub, fun u v hadj ↦ ⟨hsub hadj.fst_mem, hsub hadj.snd_mem, hBG.2 hadj⟩⟩

/-! ## Connected Components (`IsComponentOf`) -/

/-- For each connected component `c : H.coe.ConnectedComponent`, the induced subgraph of `H` on
the vertices of `c`. -/
def componentSubgraph (H : (⊤ : SimpleGraph V).Subgraph) (c : H.coe.ConnectedComponent) :
    (⊤ : SimpleGraph V).Subgraph :=
  H.induce (Subtype.val '' c.supp)

@[simp]
theorem verts_componentSubgraph (H : (⊤ : SimpleGraph V).Subgraph)
    (c : H.coe.ConnectedComponent) :
    (componentSubgraph H c).verts = Subtype.val '' c.supp := rfl

theorem componentSubgraph_le (H : (⊤ : SimpleGraph V).Subgraph) (c : H.coe.ConnectedComponent) :
    componentSubgraph H c ≤ H := by
  refine ⟨?_, fun _ _ h ↦ h.2.2⟩
  rintro _ ⟨v, _, rfl⟩
  exact v.2

theorem connected_componentSubgraph (H : (⊤ : SimpleGraph V).Subgraph)
    (c : H.coe.ConnectedComponent) : (componentSubgraph H c).Connected := by
  rw [Subgraph.connected_iff_forall_exists_walk_subgraph]
  obtain ⟨v₀, hv₀⟩ := c.nonempty_supp
  refine ⟨⟨v₀.1, v₀, hv₀, rfl⟩, ?_⟩
  rintro x y ⟨u, hu, rfl⟩ ⟨w, hw, rfl⟩
  have hreach : H.coe.Reachable u w :=
    ConnectedComponent.exact (hu.trans hw.symm)
  obtain ⟨p⟩ := hreach
  have haux : ∀ {a b : H.verts} (q : H.coe.Walk a b),
      H.coe.connectedComponentMk a = c →
        ∃ r : (⊤ : SimpleGraph V).Walk a.1 b.1, r.toSubgraph ≤ componentSubgraph H c := by
    intro a b q
    induction q with
    | @nil a =>
      intro ha
      exact ⟨.nil, by simp [ha]⟩
    | @cons a d b hadj rest ih =>
      intro ha
      have hd : H.coe.connectedComponentMk d = c := by
        rw [← ha]
        exact ConnectedComponent.eq.2 ⟨.cons hadj.symm .nil⟩
      obtain ⟨r, hr⟩ := ih hd
      have hadj_comp : (componentSubgraph H c).Adj a.1 d.1 :=
        ⟨⟨a, ha, rfl⟩, ⟨d, hd, rfl⟩, hadj⟩
      refine ⟨.cons hadj_comp.adj_sub r, ?_⟩
      rw [Walk.toSubgraph]
      exact sup_le (subgraphOfAdj_le_of_adj (componentSubgraph H c) hadj_comp) hr
  exact haux p hu

theorem le_componentSubgraph_of_preconnected {C H : (⊤ : SimpleGraph V).Subgraph}
    (hCH : C ≤ H) (hC : C.Preconnected) {v : V} (hvC : v ∈ C.verts) :
    C ≤ componentSubgraph H (H.coe.connectedComponentMk ⟨v, hCH.1 hvC⟩) := by
  have hv_mem : ∀ w ∈ C.verts,
      w ∈ (componentSubgraph H (H.coe.connectedComponentMk ⟨v, hCH.1 hvC⟩)).verts := by
    intro w hwC
    obtain ⟨p, hp⟩ := (Subgraph.preconnected_iff_forall_exists_walk_subgraph C).1 hC hvC hwC
    have hwalk : ∀ {a b : V} (q : (⊤ : SimpleGraph V).Walk a b),
        q.toSubgraph ≤ C → ∀ (haH : a ∈ H.verts) (hbH : b ∈ H.verts),
          H.coe.Reachable ⟨a, haH⟩ ⟨b, hbH⟩ := by
      intro a b q
      induction q with
      | nil => exact fun _ _ _ ↦ .refl _
      | @cons a d b _ rest ih =>
        intro hq haH hbH
        rw [Walk.toSubgraph, sup_le_iff] at hq
        have hadjC : C.Adj a d := hq.1.2 (by simp)
        have hadjH : H.Adj a d := hCH.2 hadjC
        have hdH : d ∈ H.verts := hadjH.snd_mem
        have hadj_coe : H.coe.Adj ⟨a, haH⟩ ⟨d, hdH⟩ := hadjH
        exact (Adj.reachable hadj_coe).trans (ih hq.2 hdH hbH)
    have hreach := hwalk p hp (hCH.1 hvC) (hCH.1 hwC)
    exact ⟨⟨w, hCH.1 hwC⟩, ConnectedComponent.eq.2 hreach.symm, rfl⟩
  refine ⟨hv_mem, fun x y hxy ↦ ⟨hv_mem x hxy.fst_mem, hv_mem y hxy.snd_mem, hCH.2 hxy⟩⟩

theorem isComponentOf_componentSubgraph (H : (⊤ : SimpleGraph V).Subgraph)
    (c : H.coe.ConnectedComponent) : IsComponentOf (componentSubgraph H c) H where
  le := componentSubgraph_le H c
  connected := connected_componentSubgraph H c
  eq_of_le {C'} hle hC'H hC' := by
    obtain ⟨v, hv⟩ := (connected_componentSubgraph H c).nonempty
    have hvC' : v ∈ C'.verts := hle.1 hv
    obtain ⟨⟨v₀, hv₀H⟩, hv₀c, rfl⟩ := hv
    have hC'_le := le_componentSubgraph_of_preconnected hC'H hC'.preconnected hvC'
    have hc_eq : H.coe.connectedComponentMk ⟨v₀, hC'H.1 hvC'⟩ = c := hv₀c
    rw [hc_eq] at hC'_le
    exact le_antisymm hC'_le hle

theorem isComponentOf_iff_exists_connectedComponent {C H : (⊤ : SimpleGraph V).Subgraph} :
    IsComponentOf C H ↔ ∃ c : H.coe.ConnectedComponent, C = componentSubgraph H c := by
  refine ⟨fun h ↦ ?_, ?_⟩
  · obtain ⟨v, hvC⟩ := h.connected.nonempty
    let c := H.coe.connectedComponentMk ⟨v, h.le.1 hvC⟩
    have hle := le_componentSubgraph_of_preconnected h.le h.connected.preconnected hvC
    have heq := h.eq_of_le hle (componentSubgraph_le H c) (connected_componentSubgraph H c)
    exact ⟨c, heq.symm⟩
  · rintro ⟨c, rfl⟩
    exact isComponentOf_componentSubgraph H c

theorem IsComponentOf.disjoint_or_eq {C₁ C₂ H : (⊤ : SimpleGraph V).Subgraph}
    (h₁ : IsComponentOf C₁ H) (h₂ : IsComponentOf C₂ H) :
    Disjoint C₁.verts C₂.verts ∨ C₁ = C₂ := by
  rw [isComponentOf_iff_exists_connectedComponent] at h₁ h₂
  obtain ⟨c₁, rfl⟩ := h₁
  obtain ⟨c₂, rfl⟩ := h₂
  by_cases heq : c₁ = c₂
  · exact Or.inr (congrArg (componentSubgraph H) heq)
  · left
    rw [Set.disjoint_left]
    rintro v ⟨u₁, hu₁, rfl⟩ ⟨u₂, hu₂, hu₂_eq⟩
    have hu : u₁ = u₂ := Subtype.ext hu₂_eq.symm
    exact heq (hu₁.symm.trans (hu ▸ hu₂))

theorem IsComponentOf.not_adj_of_ne {C₁ C₂ H : (⊤ : SimpleGraph V).Subgraph}
    (h₁ : IsComponentOf C₁ H) (h₂ : IsComponentOf C₂ H) (hne : C₁ ≠ C₂)
    {u v : V} (hu : u ∈ C₁.verts) (hv : v ∈ C₂.verts) : ¬ H.Adj u v := by
  rw [isComponentOf_iff_exists_connectedComponent] at h₁ h₂
  obtain ⟨c₁, rfl⟩ := h₁
  obtain ⟨c₂, rfl⟩ := h₂
  obtain ⟨u', hu', rfl⟩ := hu
  obtain ⟨v', hv', rfl⟩ := hv
  intro hadj
  have hadj_coe : H.coe.Adj u' v' := hadj
  have hc : c₁ = c₂ := hu'.symm.trans ((ConnectedComponent.eq.2 ⟨.cons hadj_coe .nil⟩).trans hv')
  exact hne (congrArg (componentSubgraph H) hc)

/-! ## Vertex Weights (`weightSum`) -/

@[simp]
theorem weightSum_empty (w : V → ℕ) : weightSum w ∅ = 0 := by
  simp [weightSum]

theorem weightSum_eq_sum (w : V → ℕ) {X : Set V} (hX : X.Finite) :
    weightSum w X = ∑ v ∈ hX.toFinset, w v := by
  unfold weightSum
  exact finsum_mem_eq_finite_toFinset_sum w hX

@[simp]
theorem weightSum_singleton (w : V → ℕ) (v : V) : weightSum w {v} = w v := by
  rw [weightSum_eq_sum w (Set.finite_singleton v)]
  simp

theorem weightSum_union_disjoint (w : V → ℕ) {X Y : Set V} (hX : X.Finite) (hY : Y.Finite)
    (hdisj : Disjoint X Y) :
    weightSum w (X ∪ Y) = weightSum w X + weightSum w Y := by
  classical
  rw [weightSum_eq_sum w (hX.union hY), weightSum_eq_sum w hX, weightSum_eq_sum w hY]
  have hfin : (hX.union hY).toFinset = hX.toFinset ∪ hY.toFinset := by
    ext v
    simp
  have hdisj_fin : Disjoint hX.toFinset hY.toFinset := by
    rw [Finset.disjoint_left]
    intro v hvX hvY
    exact Set.disjoint_left.1 hdisj (hX.mem_toFinset.1 hvX) (hY.mem_toFinset.1 hvY)
  rw [hfin, Finset.sum_union hdisj_fin]

theorem weightSum_mono (w : V → ℕ) {X Y : Set V} (hY : Y.Finite) (hXY : X ⊆ Y) :
    weightSum w X ≤ weightSum w Y := by
  have hX : X.Finite := hY.subset hXY
  have hdiff : (Y \ X).Finite := hY.subset Set.sdiff_subset
  have hunion : X ∪ (Y \ X) = Y := Set.union_sdiff_cancel hXY
  have hdisj : Disjoint X (Y \ X) := disjoint_sdiff_self_right
  have h := weightSum_union_disjoint w hX hdiff hdisj
  rw [hunion] at h
  omega

theorem weightSum_const_one {X : Set V} (hX : X.Finite) :
    weightSum (fun _ ↦ 1) X = X.ncard := by
  rw [weightSum_eq_sum _ hX, Finset.sum_const, smul_eq_mul, mul_one,
    Set.ncard_eq_toFinset_card X hX]

end GraphMinor.GM05
