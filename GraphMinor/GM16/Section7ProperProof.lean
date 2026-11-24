module

public import GraphMinor.GM16.Section7
public import GraphMinor.GM16.ProperEyeInduction
import GraphMinor.GM16.VortexComparison
import GraphMinor.GM16.Section3
import GraphMinor.GM11.PlaneFacts

import GraphMinor.GM09.Bridge

import GraphMinor.GM12.Bridge

import GraphMinor.GM12.Section710

import GraphMinor.GM12.Section77

import GraphMinor.GM14.Bridge

import GraphMinor.GM15.Section3Crosscap

import GraphMinor.GM15.Section3Parallel

/-!
# Graph Minors XVI (7.2)

We follow XV (8.4), using XV (8.3) to pass from level spans to flat
spans and XV (8.1) to replace independent eyes by a controlled clique.
The arrangement outcome retains properness from its construction in
XV (7.7), as the proof of XVI (7.2), page 62, requires.
-/

public section
namespace GraphMinor.GM16
open Set Function Topology
open Graph SimpleGraph Hypergraph Surface GM06 GM09 GM10 GM11 GM14 GM15
universe u v w

/-- Explicit `(κ, lam, ρ, θ)` parameters for Graph Minors XVI, (7.2). -/
@[expose] def theorem_7_2_bound (V : ℕ → ℕ → ℕ → ℕ → ℕ) (a b p φ μ : ℕ) :
    ℕ × ℕ × ℕ × ℕ :=
  let p4 := max p 4
  let κ := GM12.theorem_4_5_kBound p4
  let φ₁ := GM12.theorem_4_5_NBound V a b p4
  let φ₂ := max φ φ₁
  let res := properArrangementBound κ φ₂ μ
  let θ := max (max res.1 p4) (4 * (res.2.1 + μ + 2) + 3)
  (κ, res.2.1 + μ + 2, res.2.2, θ)

/-- Graph Minors XVI, (7.2), page 62, with explicit parameters `theorem_7_2_bound V a b p φ μ`. -/
theorem theorem_7_2_explicit
    (V : ℕ → ℕ → ℕ → ℕ → ℕ) (hV : ∀ a b c k, GM07.vModel a b c k ≤ V a b c k)
    {S : Type w} [TopologicalSpace S] [T2Space S]
    (hClosed : IsClosedSurface S) (hConn : ConnectedSpace S)
    {a b : ℕ} (he : Nonempty (S ≃ₜ SurfaceModel a b 0)) (p φ μ : ℕ) :
    let res := theorem_7_2_bound V a b p φ μ
    1 ≤ res.2.2.2 ∧
    ∀ {α : Type u} {β : Type v} (G : Graph α β) (θ_star θ_span : ℕ)
      (T_star : Set (Hypergraph α β × Hypergraph α β))
      (H : Drawing S) (η : SpanEmbedding H G)
      (T : Set (Hypergraph S (Set S) × Hypergraph S (Set S)))
      (d : Set S → Set S → ℕ),
      IsGraphTangle G θ_star T_star →
      res.2.2.2 ≤ θ_span →
      IsLevelSpan G H η θ_star θ_span res.2.1 μ T_star T d →
      (∃ (S' : Type w) (_ : TopologicalSpace S') (_ : T2Space S')
        (H' : Drawing S') (η' : SpanEmbedding H' G) (θ_span' : ℕ)
        (T' : Set (Hypergraph S' (Set S') × Hypergraph S' (Set S'))),
        IsClosedSurface S' ∧ ConnectedSpace S' ∧
        IsObtainedByAddingCrosscap S S' ∧
        φ ≤ θ_span' ∧ IsSigmaSpan G H' η' θ_star θ_span' T_star T') ∨
      (∃ (S_seg : Set (Society α β))
        (α_disc : Society α β → Set S) (α_pt : α → S),
        IsCentralSegregation G T_star S_seg ∧
        IsSegregationOfType G res.2.2.1 res.1 S_seg ∧
        IsProperArrangement S_seg α_disc α_pt) ∨
      ControlsMinor G (completeGraph p) T_star := by
  have hSurf : IsSurface S := hClosed.isSurface
  have hBd : bd S = ∅ := by
    ext x
    exact iff_false_intro (fun hx => hx (hClosed.2.2 x))
  let p4 := max p 4
  let κ := GM12.theorem_4_5_kBound p4
  let φ₁ := GM12.theorem_4_5_NBound V a b p4
  let φ₂ := max φ φ₁
  let res := properArrangementBound κ φ₂ μ
  let θ₁ := res.1
  let lam := res.2.1
  let ρ := res.2.2
  let θ := max (max θ₁ p4) (4 * (lam + μ + 2) + 3)
  refine ⟨by dsimp [theorem_7_2_bound]; omega, ?_⟩
  intro α β G θ_star θ_span T_star H η T d hT hθ hLevel
  have hθ₁ : θ₁ ≤ θ_span := (le_max_left _ _).trans ((le_max_left _ _).trans hθ)
  have hp4 : p4 ≤ θ_star :=
    ((le_max_right θ₁ p4).trans ((le_max_left _ _).trans hθ)).trans
      hLevel.isSpan.isControlling.theta_le
  have hFlat : IsFlatSpan G H η θ_star θ_span lam μ T_star T :=
    GM15.theorem_8_3_proof G H η θ_star θ_span lam μ T_star T d
      (by have := (le_max_right (max θ₁ p4) (4 * (lam + μ + 2) + 3)).trans hθ; omega)
      hLevel
  rcases proper_arrangement_explicit.{u, v, w} S hSurf hConn hBd κ φ₂ μ
      G θ_star T_star H η θ_span T d hFlat hLevel.hasMetric hθ₁ with
    ⟨H', η', θ', T', d', hSpan', hMetric', hφ₂, hEyes⟩ |
    ⟨S', hTS', hT2S', hCross, H', η', θ', T', hφ₂, hSpan'⟩ |
    ⟨𝒮, disc, pt, hCentral, hType, hProper⟩
  · right; right
    have hMinor : ControlsCliqueMinor G p4 T_star :=
      GM15.theorem_8_1_explicit.{u, v, w} V hV S hSurf hConn hBd he p4
        G θ_star T_star H' η' θ' T' d' hSpan' hMetric' hp4
        ((le_max_right φ φ₁).trans hφ₂) (hEyes.mono (Nat.le_succ κ))
    have hβ : Nonempty β := by
      obtain ⟨X, _, _, hlink, _⟩ := hMinor
      obtain ⟨e, _⟩ := hlink ⟨0, by dsimp [p4]; omega⟩ ⟨1, by dsimp [p4]; omega⟩
        (Fin.mk_lt_mk.mpr Nat.zero_lt_one)
      exact ⟨e⟩
    exact controlsMinor_of_controlsCliqueMinor (Or.inr hβ) (hMinor.mono (le_max_left p 4))
  · left
    have hClosed' : IsClosedSurface S' :=
      ⟨hSpan'.isSurface.1, hSpan'.isSurface.2.1, fun x => by
        by_contra hx
        exact Set.eq_empty_iff_forall_notMem.mp hSpan'.bd_empty x hx⟩
    exact ⟨S', hTS', hT2S', H', η', θ', T', hClosed', hSpan'.isConnected,
      hCross, (le_max_left φ φ₁).trans hφ₂, hSpan'⟩
  · right; left
    exact ⟨𝒮, disc, pt, hCentral, isSegregationOfType_of_gm15 hType, hProper⟩

/-- Graph Minors XVI, (7.2), page 62. The properness omitted from the
statement of XV (8.4) is proved at the construction of its arrangements
in XV (7.7) and retained through the downward eye induction. -/
theorem theorem_7_2_proof
     :
    GM16Theorem72Statement.{u, v, w} := by
  intro S _ _ hClosed hConn p φ μ
  let : ConnectedSpace S := hConn
  obtain ⟨a, b, he⟩ := GM12.exists_closed_surface_model hClosed
  let res := theorem_7_2_bound GM07.vModel a b p φ μ
  exact ⟨res.1, res.2.1, res.2.2.1, res.2.2.2,
    theorem_7_2_explicit.{u, v, w} GM07.vModel (fun _ _ _ _ => le_rfl) hClosed hConn he p φ μ⟩

end GraphMinor.GM16
