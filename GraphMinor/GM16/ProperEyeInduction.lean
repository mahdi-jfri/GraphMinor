module

public import GraphMinor.GM16.ProperEyeInductionStep
public import GraphMinor.GM15.Section8

import GraphMinor.GM09.Bridge

import GraphMinor.GM12.Section710

import GraphMinor.GM12.Section77

import GraphMinor.GM14.Bridge

import GraphMinor.GM15.Section3Crosscap

import GraphMinor.GM15.Section3Parallel

import GraphMinor.GM15.Section5

import GraphMinor.GM15.Section7

/-!
# Proper arrangements through the downward eye induction

The induction in XV, pages 115–116, repeatedly applies the eye step.
The arrangement outcome keeps the same discs while its numerical bounds
increase. We retain its properness for XVI (7.2), page 62.
-/

public section
namespace GraphMinor.GM16
open Set Function Topology
open Graph SimpleGraph Hypergraph Surface GM06 GM09 GM10 GM11 GM14 GM15
universe u v w

/-- One iteration step of the downward eye induction in `ProperEyeInduction`. -/
@[expose] def properEyeIndStep (φ' μ' : ℕ) (st : ℕ × ℕ × ℕ) : ℕ × ℕ × ℕ :=
  let (p_n, lam_n, θ_n) := st
  let (p_k, lam_k, θ_k) := properEyeStep φ' μ' lam_n θ_n
  let lam_next := max lam_k 4
  (max p_k p_n, lam_next, max θ_k (4 * lam_next + μ' + 2))

/-- Explicit `(θ, lam, p)` parameters for `proper_arrangement_or_independent_eyes_or_crosscap`. -/
@[expose] def properArrangementBound (κ φ μ : ℕ) : ℕ × ℕ × ℕ :=
  let μ' : ℕ := 2 * (μ + 6)
  let φ' : ℕ := max φ 8
  let θ_top : ℕ := max φ' (4 * 4 + μ' + 2)
  let res := Nat.iterate (properEyeIndStep φ' μ') (κ + 1) (0, 4, θ_top)
  (max res.2.2 (4 * res.2.1 + μ' + 2), res.2.1, res.1)

private theorem proper_eye_inductive_step_explicit
    {S : Type w} [TopologicalSpace S] [T2Space S]
    (hSurf : IsSurface S) (hConn : ConnectedSpace S) (hBd : bd S = ∅)
    {κ φ' μ' lam_target θ_target : ℕ}
    (hφ'8 : 8 ≤ φ') (hμ'12 : 12 ≤ μ') (hμ'_even : Even μ')
    (hlam_t : 4 ≤ lam_target) (hθ_t : 4 * lam_target + μ' + 2 ≤ θ_target) :
    ∀ n ≤ κ + 1,
      let st := Nat.iterate (properEyeIndStep φ' μ') n (0, lam_target, θ_target)
      4 ≤ st.2.1 ∧ 4 * st.2.1 + μ' + 2 ≤ st.2.2 ∧
      ∀ {α : Type u} {β : Type v} (G : Graph α β) (θ_star : ℕ)
        (T_star : Set (Hypergraph α β × Hypergraph α β))
        (H₀ : Drawing S) (η₀ : SpanEmbedding H₀ G) (θ₀ : ℕ)
        (T₀ : Set (Hypergraph S (Set S) × Hypergraph S (Set S)))
        (d₀ : Set S → Set S → ℕ),
        IsFlatSpan G H₀ η₀ θ_star θ₀ st.2.1 μ' T_star T₀ →
        HasTangleMetric H₀ θ₀ T₀ d₀ →
        st.2.2 ≤ θ₀ →
        HasEyesAtDistance G H₀ η₀ θ₀ T₀ d₀ (κ + 1 - n) st.2.2 →
        Section7S1 S G θ_star T_star κ μ' lam_target θ_target ∨
        Section7S2 S G θ_star T_star φ' ∨
        (∃ (𝒮 : Set (Society α β)) (disc : Society α β → Set S) (pt : α → S),
          IsCentralSegregation G T_star 𝒮 ∧
          GM15.IsSegregationOfType G st.1 κ 𝒮 ∧ IsProperArrangement 𝒮 disc pt) := by
  intro n
  induction n with
  | zero =>
    intro _
    refine ⟨hlam_t, hθ_t, ?_⟩
    intro α β G θ_star T_star H₀ η₀ θ₀ T₀ d₀ hFlat₀ hMetric₀ hθ₀_ge hEyes₀
    left
    have h4 : 4 ≤ θ_target := by omega
    exact GraphMinor.GM15.theorem_7_1_proof.{u, v, w} G H₀ η₀ θ_star θ₀ θ_target lam_target μ' (κ + 1) T_star T₀ d₀
      hFlat₀ hMetric₀ (by omega) hθ_t h4 hθ₀_ge hEyes₀
  | succ n ih =>
    intro hn1
    have hn : n ≤ κ + 1 := Nat.le_of_succ_le hn1
    obtain ⟨hlam_n4, hθ_n_ge, hIH⟩ := ih hn
    set st := Nat.iterate (properEyeIndStep φ' μ') n (0, lam_target, θ_target)
    have hiter : Nat.iterate (properEyeIndStep φ' μ') (n + 1) (0, lam_target, θ_target) =
        properEyeIndStep φ' μ' st :=
      Function.iterate_succ_apply' (properEyeIndStep φ' μ') n (0, lam_target, θ_target)
    rw [hiter]
    let k := κ + 1 - (n + 1)
    have hk_le : k ≤ κ := by omega
    have hk_succ : k + 1 = κ + 1 - n := by omega
    obtain ⟨hθ_k_ge, hStep⟩ :=
      proper_eye_induction_step_explicit.{u, v, w} S hSurf hConn hBd k φ' μ' st.2.1 st.2.2
        hφ'8 hμ'12 hμ'_even hlam_n4 hθ_n_ge
    dsimp only [properEyeIndStep]
    set step := properEyeStep φ' μ' st.2.1 st.2.2
    refine ⟨le_max_right _ _, le_max_right _ _, ?_⟩
    intro α β G θ_star T_star H₀ η₀ θ₀ T₀ d₀ hFlat₀ hMetric₀ hθ₀_ge hEyes₀
    have hθ_k_le_θ_next : step.2.2 ≤ max step.2.2 (4 * max step.2.1 4 + μ' + 2) := le_max_left _ _
    have hθ_k_le_θ₀ : step.2.2 ≤ θ₀ := hθ_k_le_θ_next.trans hθ₀_ge
    have hFlat_k : IsFlatSpan G H₀ η₀ θ_star θ₀ step.2.1 μ' T_star T₀ :=
      hFlat₀.mono_lam_mu (le_max_left _ _) le_rfl (hθ_k_ge.trans hθ_k_le_θ₀)
        (fun _ => by have := hFlat₀.order_ge; omega)
    have hEyes_k : HasEyesAtDistance G H₀ η₀ θ₀ T₀ d₀ k step.2.2 := by
      rcases hEyes₀ with ⟨r, hr_inj, hr_eye, hr_dist⟩
      exact ⟨r, hr_inj, hr_eye, fun i j hij => hθ_k_le_θ_next.trans (hr_dist i j hij)⟩
    rcases hStep G θ_star T_star H₀ η₀ θ₀ T₀ d₀ hFlat_k hMetric₀ hθ_k_le_θ₀ hEyes_k with
      hS1 | hS2 | hS3
    · rcases hS1 with ⟨H₁, η₁, T₁, d₁, r₁, hFlat₁, hMetric₁, hr₁_inj, hr₁_eye, hr₁_dist⟩
      have hEyes₁ : HasEyesAtDistance G H₁ η₁ st.2.2 T₁ d₁ (k + 1) st.2.2 :=
        ⟨r₁, hr₁_inj, hr₁_eye, fun i j hij => le_of_eq (hr₁_dist i j hij).symm⟩
      rw [hk_succ] at hEyes₁
      rcases hIH G θ_star T_star H₁ η₁ st.2.2 T₁ d₁ hFlat₁ hMetric₁ le_rfl hEyes₁ with
        hOut1 | hOut2 | ⟨S_seg, α_disc, α_pt, hCent, hType, hArr⟩
      · exact Or.inl hOut1
      · exact Or.inr (Or.inl hOut2)
      · exact Or.inr (Or.inr ⟨S_seg, α_disc, α_pt, hCent,
          hType.mono (le_max_right _ _) le_rfl, hArr⟩)
    · exact Or.inr (Or.inl hS2)
    · rcases hS3 with ⟨S_seg, α_disc, α_pt, hCent, hType, hArr⟩
      exact Or.inr (Or.inr ⟨S_seg, α_disc, α_pt, hCent,
        hType.mono (le_max_left _ _) hk_le, hArr⟩)

/-- Explicit version of `proper_arrangement_or_independent_eyes_or_crosscap` using
`properArrangementBound κ φ μ`. -/
theorem proper_arrangement_explicit
    (S : Type w) [TopologicalSpace S] [T2Space S]
    (hSurf : IsSurface S) (hConn : ConnectedSpace S) (hBd : bd S = ∅)
    (κ φ μ : ℕ) :
    let res := properArrangementBound κ φ μ
    ∀ {α : Type u} {β : Type v} (G : Graph α β) (θ_star : ℕ)
      (T_star : Set (Hypergraph α β × Hypergraph α β))
      (H₀ : Drawing S) (η₀ : SpanEmbedding H₀ G) (θ₀ : ℕ)
      (T₀ : Set (Hypergraph S (Set S) × Hypergraph S (Set S)))
      (d₀ : Set S → Set S → ℕ),
      IsFlatSpan G H₀ η₀ θ_star θ₀ res.2.1 μ T_star T₀ →
      HasTangleMetric H₀ θ₀ T₀ d₀ →
      res.1 ≤ θ₀ →
      (∃ (H' : Drawing S) (η' : SpanEmbedding H' G) (θ' : ℕ)
        (T' : Set (Hypergraph S (Set S) × Hypergraph S (Set S)))
        (d' : Set S → Set S → ℕ),
        IsSigmaSpan G H' η' θ_star θ' T_star T' ∧
        HasTangleMetric H' θ' T' d' ∧
        φ ≤ θ' ∧
        HasIndependentEyes G H' η' θ' T' d' (κ + 1)) ∨
      (∃ (S' : Type w) (_ : TopologicalSpace S') (_ : T2Space S'),
        IsObtainedByAddingCrosscap S S' ∧
        ∃ (H' : Drawing S') (η' : SpanEmbedding H' G) (θ' : ℕ)
          (T' : Set (Hypergraph S' (Set S') × Hypergraph S' (Set S'))),
           φ ≤ θ' ∧ IsSigmaSpan G H' η' θ_star θ' T_star T') ∨
      (∃ (𝒮 : Set (Society α β)) (disc : Society α β → Set S) (pt : α → S),
        IsCentralSegregation G T_star 𝒮 ∧
        GM15.IsSegregationOfType G res.2.2 κ 𝒮 ∧ IsProperArrangement 𝒮 disc pt) := by
  let μ' : ℕ := 2 * (μ + 6)
  let φ' : ℕ := max φ 8
  let θ_top : ℕ := max φ' (4 * 4 + μ' + 2)
  have hφ'8 : 8 ≤ φ' := le_max_right _ _
  have hφ_le_φ' : φ ≤ φ' := le_max_left _ _
  have hμ'12 : 12 ≤ μ' := by omega
  have hμ_le_μ' : μ ≤ μ' := by omega
  have hμ'_even : Even μ' := ⟨μ + 6, by ring⟩
  have hθ_top_ge : 4 * 4 + μ' + 2 ≤ θ_top := le_max_right _ _
  have hφ_le_θ_top : φ ≤ θ_top := hφ_le_φ'.trans (le_max_left _ _)
  obtain ⟨_, _, hInd⟩ :=
    proper_eye_inductive_step_explicit.{u, v, w} hSurf hConn hBd hφ'8 hμ'12 hμ'_even
      (le_refl 4) hθ_top_ge (κ + 1) le_rfl
  dsimp only [properArrangementBound]
  set st := Nat.iterate (properEyeIndStep φ' μ') (κ + 1) (0, 4, θ_top)
  intro α β G θ_star T_star H₀ η₀ θ₀ T₀ d₀ hFlat₀ hMetric₀ hθ_le
  have hθ₀_base_le : st.2.2 ≤ θ₀ := (le_max_left _ _).trans hθ_le
  have hord_μ' : 4 * st.2.1 + μ' + 2 ≤ θ₀ := (le_max_right _ _).trans hθ_le
  have hFlat_μ' : IsFlatSpan G H₀ η₀ θ_star θ₀ st.2.1 μ' T_star T₀ :=
    hFlat₀.mono_mu hμ_le_μ' hord_μ'
  have hEyes0 : HasEyesAtDistance G H₀ η₀ θ₀ T₀ d₀ (κ + 1 - (κ + 1)) st.2.2 := by
    rw [Nat.sub_self]
    exact ⟨Fin.elim0, fun i => Fin.elim0 i, fun i => Fin.elim0 i, fun i => Fin.elim0 i⟩
  rcases hInd G θ_star T_star H₀ η₀ θ₀ T₀ d₀ hFlat_μ' hMetric₀ hθ₀_base_le hEyes0 with
    ⟨H₁, η₁, T₁, d₁, r₁, hFlat₁, hMetric₁, hr₁_inj, hr₁_eye, hr₁_dist⟩ |
    ⟨S', hTS', hT2S', hCross, H', η', T', hSpan'⟩ | hS3
  · left
    have hθ_top_18 : μ' + 18 ≤ θ_top := by omega
    have hIndEyes : HasIndependentEyes G H₁ η₁ θ_top T₁ d₁ (κ + 1) :=
      independentEyes_of_flatSpan G H₁ η₁ θ_star θ_top μ' κ T_star T₁ d₁ r₁ hFlat₁ hMetric₁
        hμ'12 hθ_top_18 hr₁_inj hr₁_eye hr₁_dist
    exact ⟨H₁, η₁, θ_top, T₁, d₁, hFlat₁.isSpan, hMetric₁, hφ_le_θ_top, hIndEyes⟩
  · right; left
    exact ⟨S', hTS', hT2S', hCross, H', η', φ', T', hφ_le_φ', hSpan'⟩
  · right; right
    exact hS3

/-- XV (1.1), pages 115–116, with the properness retained from the actual
arrangement construction, as required in XVI (7.2), page 62. -/
theorem proper_arrangement_or_independent_eyes_or_crosscap
     :
    ∀ (S : Type w) [TopologicalSpace S] [T2Space S],
    IsSurface S → ConnectedSpace S → bd S = ∅ →
    ∀ (κ φ μ : ℕ),
      ∃ (θ lam p : ℕ),
        ∀ {α : Type u} {β : Type v} (G : Graph α β) (θ_star : ℕ)
          (T_star : Set (Hypergraph α β × Hypergraph α β))
          (H₀ : Drawing S) (η₀ : SpanEmbedding H₀ G) (θ₀ : ℕ)
          (T₀ : Set (Hypergraph S (Set S) × Hypergraph S (Set S)))
          (d₀ : Set S → Set S → ℕ),
          IsFlatSpan G H₀ η₀ θ_star θ₀ lam μ T_star T₀ →
          HasTangleMetric H₀ θ₀ T₀ d₀ →
          θ ≤ θ₀ →
          (∃ (H' : Drawing S) (η' : SpanEmbedding H' G) (θ' : ℕ)
            (T' : Set (Hypergraph S (Set S) × Hypergraph S (Set S)))
            (d' : Set S → Set S → ℕ),
            IsSigmaSpan G H' η' θ_star θ' T_star T' ∧
            HasTangleMetric H' θ' T' d' ∧
            φ ≤ θ' ∧
            HasIndependentEyes G H' η' θ' T' d' (κ + 1)) ∨
          (∃ (S' : Type w) (_ : TopologicalSpace S') (_ : T2Space S'),
            IsObtainedByAddingCrosscap S S' ∧
            ∃ (H' : Drawing S') (η' : SpanEmbedding H' G) (θ' : ℕ)
              (T' : Set (Hypergraph S' (Set S') × Hypergraph S' (Set S'))),
               φ ≤ θ' ∧ IsSigmaSpan G H' η' θ_star θ' T_star T') ∨
          (∃ (𝒮 : Set (Society α β)) (disc : Society α β → Set S) (pt : α → S),
            IsCentralSegregation G T_star 𝒮 ∧
            GM15.IsSegregationOfType G p κ 𝒮 ∧ IsProperArrangement 𝒮 disc pt) := by
  intro S _ _ hSurf hConn hBd κ φ μ
  exact ⟨(properArrangementBound κ φ μ).1, (properArrangementBound κ φ μ).2.1,
    (properArrangementBound κ φ μ).2.2,
    proper_arrangement_explicit.{u, v, w} S hSurf hConn hBd κ φ μ⟩


end GraphMinor.GM16
