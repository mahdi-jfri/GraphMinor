module

public import GraphMinor.GM16.Section7ProperProof
public import GraphMinor.GM16.Tower
public import GraphMinor.GM16.Section8Main
public import GraphMinor.GM16.Section6Proof
public import GraphMinor.GM16.Section5Five
public import GraphMinor.GM16.Section4Proof
public import GraphMinor.GM12.Bridge
import GraphMinor.GM16.Metric

/-!
# The backward and surface-tower inductions of Graph Minors XVI

Use the proved animal step and proper arrangement to obtain (6.1), then
remove hairs to get (5.1) and horns to get (4.1). The finite surface tower
combines (4.1) with the sphere span to obtain (3.1). Each induction uses
the earlier proofs directly.
-/

public section

namespace GraphMinor.GM16

attribute [local instance] SurfaceTowerFor.topSpace SurfaceTowerFor.t2Space

open Set Function Topology
open Graph SimpleGraph Hypergraph
open GraphMinor.Surface GraphMinor.GM06 GraphMinor.GM09 GraphMinor.GM10 GraphMinor.GM11
  GraphMinor.GM14 GraphMinor.GM15

universe u v w u' v'

/-- Explicit `(σ, κ, ρ, ζ, θ)` parameters for Graph Minors XVI, (6.1). -/
@[expose] def theorem_6_1_bound (V : ℕ → ℕ → ℕ → ℕ → ℕ) (a b p τ χ δ φ ψ : ℕ) :
    ℕ × ℕ × ℕ × ℕ × ℕ :=
  let φ' := max φ 3
  let ψ' := max ψ 3
  let res72 := theorem_7_2_bound V a b p φ' (2 * ψ')
  let θ' := max res72.2.2.2 p
  let θ := theorem_7_1_theta χ δ res72.2.1 θ' φ' ψ'
  let σ := theorem_7_1_sigma τ χ δ φ'
  let ζ := χ + δ ^ 2 * φ' ^ 2 / 2
  (σ, res72.1, res72.2.2.1, ζ, θ)

/-- **Graph Minors XVI, (6.1)** (pages 58 and 63), with explicit parameters
`theorem_6_1_bound V a b p τ χ δ φ ψ`. -/
theorem theorem_6_1_explicit
    (V : ℕ → ℕ → ℕ → ℕ → ℕ) (hV : ∀ a b c k, GM07.vModel a b c k ≤ V a b c k)
    {S : Type w} [TopologicalSpace S] [T2Space S]
    (hS : IsClosedSurface S) (hconn : ConnectedSpace S)
    {a b : ℕ} (he : Nonempty (S ≃ₜ SurfaceModel a b 0))
    (p τ χ δ φ ψ : ℕ) (hφ : 1 ≤ φ) (hψ : 1 ≤ ψ) :
    let res := theorem_6_1_bound V a b p τ χ δ φ ψ
    1 ≤ res.2.2.2.2 ∧
    ∀ {α : Type u} {β : Type v} (G : Graph α β) (θ_star : ℕ)
      (T_star : Set (Hypergraph α β × Hypergraph α β))
      (hT : IsGraphTangle G θ_star T_star),
      HasAnimal S G T_star θ_star χ δ res.2.2.2.2 res.1 →
      (∃ (S' : Type w) (_ : TopologicalSpace S') (_ : T2Space S')
        (H' : Drawing S') (η' : SpanEmbedding H' G) (θ_span' : ℕ)
        (T' : Set (Hypergraph S' (Set S') × Hypergraph S' (Set S'))),
        IsClosedSurface S' ∧ ConnectedSpace S' ∧
        IsObtainedByAddingHandleOrCrosscap S S' ∧
        φ ≤ θ_span' ∧ IsSigmaSpan G H' η' θ_star θ_span' T_star T') ∨
      HasAnimal S G T_star θ_star χ (δ + 1) ψ τ ∨
      (∃ (Z : Set α) (S_seg : Set (Society α β))
        (α_disc : Society α β → Set S) (α_pt : α → S),
        Z ⊆ V(G) ∧ Z.ncard ≤ res.2.2.2.1 ∧ Z.ncard < θ_star ∧
        IsCentralSegregation (deleteVertices G Z)
          (deleteGraphVerticesTangle G hT.finite_V hT.finite_E Z T_star θ_star) S_seg ∧
        IsSegregationOfType (deleteVertices G Z) res.2.2.1 res.2.1 S_seg ∧
        IsProperArrangement S_seg α_disc α_pt) ∨
      ControlsMinor G (completeGraph p) T_star := by
  let φ' := max φ 3
  let ψ' := max ψ 3
  have hφ'3 : 3 ≤ φ' := le_max_right _ _
  have hψ'3 : 3 ≤ ψ' := le_max_right _ _
  obtain ⟨hθ₂_pos, h72_prop⟩ := theorem_7_2_explicit.{u, v, w} V hV hS hconn he p φ' (2 * ψ')
  let res72 := theorem_7_2_bound V a b p φ' (2 * ψ')
  let θ' := max res72.2.2.2 p
  have hθ'_pos : 1 ≤ θ' := le_trans hθ₂_pos (le_max_left _ _)
  obtain ⟨hθ_pos, h71_prop⟩ :=
    theorem_7_1_explicit.{u, v, w} hS hconn τ χ δ res72.2.1 θ' φ' ψ' hθ'_pos hφ'3 hψ'3
  refine ⟨hθ_pos, ?_⟩
  intro α β G θ_star T_star hT hAnim
  rcases h71_prop G θ_star T_star hT hAnim with
    ⟨S', htopS', ht2S', H', η', θ_span', T', hCS', hconnS', hHandle, hφ'_le, hSpan'⟩ |
    hAnim_next |
    ⟨Z, H_l, η_l, θ_l, T_l, d_l, hZ_sub, hZ_le, hZ_lt, hθ'_le, hLevel⟩
  · exact Or.inl ⟨S', htopS', ht2S', H', η', θ_span', T', hCS', hconnS',
      Or.inl hHandle, (le_max_left _ _).trans hφ'_le, hSpan'⟩
  · exact Or.inr (Or.inl (hAnim_next.mono hψ (le_max_left _ _) le_rfl))
  · have hT_del : IsGraphTangle (GM09.deleteVertices G Z) (θ_star - Z.ncard)
        (deleteGraphVerticesTangle G hT.finite_V hT.finite_E Z T_star θ_star) :=
      isGraphTangle_deleteGraphVerticesTangle hT hZ_sub hZ_lt
    have hθ₂_le : res72.2.2.2 ≤ θ_l := (le_max_left _ _).trans hθ'_le
    rcases h72_prop (GM09.deleteVertices G Z) (θ_star - Z.ncard) θ_l
        (deleteGraphVerticesTangle G hT.finite_V hT.finite_E Z T_star θ_star)
        H_l η_l T_l d_l hT_del hθ₂_le hLevel with
      ⟨S', htopS', ht2S', H', η', θ_span', T', hCS', hconnS', hCross, hφ'_le, hSpan_del⟩ |
      ⟨S_seg, α_disc, α_pt, hCent, hType, hProp⟩ |
      hCtrl_del
    · have hSpan_G : @IsSigmaSpan α β S' htopS' ht2S' G H'
          (@liftSpanEmbedding S' htopS' α β H' (GM09.deleteVertices G Z) G η'
            (G.induce_le sdiff_subset)) θ_star θ_span' T_star T' :=
        @theorem_7_4_proof S' htopS' ht2S' α β G θ_star θ_span' T_star hT Z H' η' T' hZ_sub hZ_lt hSpan_del
      exact Or.inl ⟨S', htopS', ht2S', H',
        @liftSpanEmbedding S' htopS' α β H' (GM09.deleteVertices G Z) G η'
          (G.induce_le sdiff_subset),
        θ_span', T', hCS', hconnS', Or.inr hCross, (le_max_left _ _).trans hφ'_le, hSpan_G⟩
    · exact Or.inr (Or.inr (Or.inl ⟨Z, S_seg, α_disc, α_pt,
        hZ_sub, hZ_le, hZ_lt, hCent, hType, hProp⟩))
    · have hp_le_del : V(completeGraph p).ncard ≤ θ_star - Z.ncard := by
        rw [vertexSet_completeGraph_ncard]
        have hp_le_θ' : p ≤ θ_l := (le_max_right _ _).trans hθ'_le
        exact hp_le_θ'.trans hLevel.isSpan.isControlling.theta_le
      exact Or.inr (Or.inr (Or.inr
        (controlsMinor_of_deleteGraphVerticesTangle hT hZ_sub hZ_lt hp_le_del hCtrl_del)))

/-- **Graph Minors XVI, (6.1)** (page 58, proved on page 63 from (7.1), (7.2), and (7.4)). -/
theorem theorem_6_1_of_7_1_and_7_2
     :
    GM16Theorem61Statement.{u, v, w} := by
  intro S _ _ hS hconn p τ χ δ φ ψ hφ hψ
  let : ConnectedSpace S := hconn
  obtain ⟨a, b, he⟩ := GM12.exists_closed_surface_model hS
  let res := theorem_6_1_bound GM07.vModel a b p τ χ δ φ ψ
  exact ⟨res.1, res.2.1, res.2.2.1, res.2.2.2.1, res.2.2.2.2,
    theorem_6_1_explicit.{u, v, w} GM07.vModel (fun _ _ _ _ => le_rfl) hS hconn he p τ χ δ φ ψ hφ hψ⟩

/-- Graph Minors XVI, (6.1), pages 58 and 63, from the proved animal
step (7.1), the proper arrangement theorem (7.2), and tangle deletion. -/
theorem theorem_6_1_proof : GM16Theorem61Statement.{u, v, w} :=
  theorem_6_1_of_7_1_and_7_2

/-- One backward-induction step on the number of hairs for Graph Minors XVI, (5.1). -/
@[expose] def theorem_5_1_step (V : ℕ → ℕ → ℕ → ℕ → ℕ) (a b p χ φ δ : ℕ)
    (m : ℕ) (st : ℕ × ℕ × ℕ × ℕ × ℕ) : ℕ × ℕ × ℕ × ℕ × ℕ :=
  let (σ_next, κ_next, ρ_next, ζ_next, θ_next) := st
  let res := theorem_6_1_bound V a b p σ_next χ (δ - (m + 1)) φ θ_next
  (res.1, max κ_next res.2.1, max ρ_next res.2.2.1, max ζ_next res.2.2.2.1, res.2.2.2.2)

/-- Explicit `(σ, κ, ρ, ζ, θ)` parameters for Graph Minors XVI, (5.1). -/
@[expose] def theorem_5_1_bound (V : ℕ → ℕ → ℕ → ℕ → ℕ) (a b p τ χ φ ψ : ℕ) :
    ℕ × ℕ × ℕ × ℕ × ℕ :=
  let δ := theorem_6_3_delta p τ
  let init : ℕ × ℕ × ℕ × ℕ × ℕ := (τ + 1, 0, 0, 0, theorem_6_3_theta V a b p ψ)
  Nat.rec (motive := fun _ => ℕ × ℕ × ℕ × ℕ × ℕ) init
    (fun m acc => theorem_5_1_step V a b p χ φ δ m acc) δ

/-- **Graph Minors XVI, (5.1)** (pages 55 and 61), with explicit parameters
`theorem_5_1_bound V a b p τ χ φ ψ`. -/
theorem theorem_5_1_explicit
    (V : ℕ → ℕ → ℕ → ℕ → ℕ) (hV : ∀ a b c k, GM07.vModel a b c k ≤ V a b c k)
    {S : Type w} [TopologicalSpace S] [T2Space S]
    (hS : IsClosedSurface S) (hconn : ConnectedSpace S)
    {a b : ℕ} (he : Nonempty (S ≃ₜ SurfaceModel a b 0))
    (p τ χ φ ψ : ℕ) (hφ : 1 ≤ φ) (hψ : 1 ≤ ψ) :
    let res := theorem_5_1_bound V a b p τ χ φ ψ
    1 ≤ res.2.2.2.2 ∧
    ∀ {α : Type u} {β : Type v} (G : Graph α β) (θ_star : ℕ)
      (T_star : Set (Hypergraph α β × Hypergraph α β))
      (hT : IsGraphTangle G θ_star T_star),
      HasHairlessAnimal S G T_star θ_star χ res.2.2.2.2 res.1 →
      (∃ (S' : Type w) (_ : TopologicalSpace S') (_ : T2Space S')
        (H' : Drawing S') (η' : SpanEmbedding H' G) (θ_span' : ℕ)
        (T' : Set (Hypergraph S' (Set S') × Hypergraph S' (Set S'))),
        IsClosedSurface S' ∧ ConnectedSpace S' ∧
        IsObtainedByAddingHandleOrCrosscap S S' ∧
        φ ≤ θ_span' ∧ IsSigmaSpan G H' η' θ_star θ_span' T_star T') ∨
      HasHairlessAnimal S G T_star θ_star (χ + 1) ψ τ ∨
      (∃ (Z : Set α) (S_seg : Set (Society α β))
        (α_disc : Society α β → Set S) (α_pt : α → S),
        Z ⊆ V(G) ∧ Z.ncard ≤ res.2.2.2.1 ∧ Z.ncard < θ_star ∧
        IsCentralSegregation (deleteVertices G Z)
          (deleteGraphVerticesTangle G hT.finite_V hT.finite_E Z T_star θ_star) S_seg ∧
        IsSegregationOfType (deleteVertices G Z) res.2.2.1 res.2.1 S_seg ∧
        IsProperArrangement S_seg α_disc α_pt) ∨
      ControlsMinor G (completeGraph p) T_star := by
  let δ := theorem_6_3_delta p τ
  let init : ℕ × ℕ × ℕ × ℕ × ℕ := (τ + 1, 0, 0, 0, theorem_6_3_theta V a b p ψ)
  let st : ℕ → ℕ × ℕ × ℕ × ℕ × ℕ := fun m =>
    Nat.rec (motive := fun _ => ℕ × ℕ × ℕ × ℕ × ℕ) init
      (fun k acc => theorem_5_1_step V a b p χ φ δ k acc) m
  obtain ⟨hθ_δ_pos, h63_prop⟩ :=
    theorem_6_3_explicit.{u, v, w} V hV hS hconn he p τ χ ψ hψ
  have hind : ∀ m : ℕ, m ≤ δ →
      1 ≤ (st m).2.2.2.2 ∧
      ∀ {α : Type u} {β : Type v} (G : Graph α β) (θ_star : ℕ)
        (T_star : Set (Hypergraph α β × Hypergraph α β))
        (hT : IsGraphTangle G θ_star T_star),
        HasAnimal S G T_star θ_star χ (δ - m) (st m).2.2.2.2 (st m).1 →
        (∃ (S' : Type w) (_ : TopologicalSpace S') (_ : T2Space S')
          (H' : Drawing S') (η' : SpanEmbedding H' G) (θ_span' : ℕ)
          (T' : Set (Hypergraph S' (Set S') × Hypergraph S' (Set S'))),
          IsClosedSurface S' ∧ ConnectedSpace S' ∧
          IsObtainedByAddingHandleOrCrosscap S S' ∧
          φ ≤ θ_span' ∧ IsSigmaSpan G H' η' θ_star θ_span' T_star T') ∨
        HasHairlessAnimal S G T_star θ_star (χ + 1) ψ τ ∨
        (∃ (Z : Set α) (S_seg : Set (Society α β))
          (α_disc : Society α β → Set S) (α_pt : α → S),
          Z ⊆ V(G) ∧ Z.ncard ≤ (st m).2.2.2.1 ∧ Z.ncard < θ_star ∧
          IsCentralSegregation (deleteVertices G Z)
            (deleteGraphVerticesTangle G hT.finite_V hT.finite_E Z T_star θ_star) S_seg ∧
          IsSegregationOfType (deleteVertices G Z) (st m).2.2.1 (st m).2.1 S_seg ∧
          IsProperArrangement S_seg α_disc α_pt) ∨
        ControlsMinor G (completeGraph p) T_star := by
    intro m
    induction m with
    | zero =>
      intro _
      refine ⟨hθ_δ_pos, ?_⟩
      intro α β G θ_star T_star hT hAnim
      rw [Nat.sub_zero] at hAnim
      rcases h63_prop G θ_star T_star hT hAnim with hOut2 | hOut4
      · exact Or.inr (Or.inl hOut2)
      · exact Or.inr (Or.inr (Or.inr hOut4))
    | succ m ih =>
      intro hm_le
      obtain ⟨hθ_next_pos, hnext⟩ := ih (by omega)
      let i := δ - (m + 1)
      obtain ⟨hθ_i_pos, h61_prop⟩ :=
        theorem_6_1_explicit.{u, v, w} V hV hS hconn he p (st m).1 χ i φ (st m).2.2.2.2
          hφ hθ_next_pos
      refine ⟨hθ_i_pos, ?_⟩
      intro α β G θ_star T_star hT hAnim
      rcases h61_prop G θ_star T_star hT hAnim with
        hOut1 | hOut2 | ⟨Z, S_seg, α_disc, α_pt, hZ_sub, hZ_le, hZ_lt, hCent, hType, hProp⟩ | hOut4
      · exact Or.inl hOut1
      · have hi_succ : i + 1 = δ - m := by omega
        rw [hi_succ] at hOut2
        rcases hnext G θ_star T_star hT hOut2 with
          hOut1' | hOut2' | ⟨Z, S_seg, α_disc, α_pt, hZ_sub, hZ_le, hZ_lt, hCent, hType, hProp⟩ | hOut4'
        · exact Or.inl hOut1'
        · exact Or.inr (Or.inl hOut2')
        · exact Or.inr (Or.inr (Or.inl ⟨Z, S_seg, α_disc, α_pt,
            hZ_sub, hZ_le.trans (le_max_left _ _), hZ_lt, hCent,
            hType.mono (le_max_left _ _) (le_max_left _ _), hProp⟩))
        · exact Or.inr (Or.inr (Or.inr hOut4'))
      · exact Or.inr (Or.inr (Or.inl ⟨Z, S_seg, α_disc, α_pt,
          hZ_sub, hZ_le.trans (le_max_right _ _), hZ_lt, hCent,
          hType.mono (le_max_right _ _) (le_max_right _ _), hProp⟩))
      · exact Or.inr (Or.inr (Or.inr hOut4))
  obtain ⟨hθ₀_pos, hfull⟩ := hind δ le_rfl
  refine ⟨hθ₀_pos, ?_⟩
  intro α β G θ_star T_star hT hAnim
  have hAnim₀ : HasAnimal S G T_star θ_star χ (δ - δ) (st δ).2.2.2.2 (st δ).1 := by
    rw [Nat.sub_self]
    exact hAnim
  exact hfull G θ_star T_star hT hAnim₀

/-- **Graph Minors XVI, (5.1)** (page 55, proved on page 61 from (6.1) and (6.3)). -/
theorem theorem_5_1_of_6_1_and_6_3
     :
    GM16Theorem51Statement.{u, v, w} := by
  intro S _ _ hS hconn p τ χ φ ψ hφ hψ
  let : ConnectedSpace S := hconn
  obtain ⟨a, b, he⟩ := GM12.exists_closed_surface_model hS
  let res := theorem_5_1_bound GM07.vModel a b p τ χ φ ψ
  exact ⟨res.1, res.2.1, res.2.2.1, res.2.2.2.1, res.2.2.2.2,
    theorem_5_1_explicit.{u, v, w} GM07.vModel (fun _ _ _ _ => le_rfl) hS hconn he p τ χ φ ψ hφ hψ⟩

/-- Graph Minors XVI, (5.1), pages 55 and 61, by the backward induction
on the number of hairs, using the proved (6.1) and (6.3). -/
theorem theorem_5_1_proof : GM16Theorem51Statement.{u, v, w} :=
  theorem_5_1_of_6_1_and_6_3

/-- One backward-induction step on the number of horns for Graph Minors XVI, (4.1). -/
@[expose] def theorem_4_1_step (V : ℕ → ℕ → ℕ → ℕ → ℕ) (a b p φ μ : ℕ)
    (m : ℕ) (st : ℕ × ℕ × ℕ × ℕ × ℕ) : ℕ × ℕ × ℕ × ℕ × ℕ :=
  let (σ_next, κ_next, ρ_next, ζ_next, θ_next) := st
  let res := theorem_5_1_bound V a b p σ_next (μ - (m + 1)) φ θ_next
  (res.1, max κ_next res.2.1, max ρ_next res.2.2.1, max ζ_next res.2.2.2.1, res.2.2.2.2)

/-- Explicit `(κ, ρ, ζ, θ)` parameters for Graph Minors XVI, (4.1). -/
@[expose] def theorem_4_1_bound (V : ℕ → ℕ → ℕ → ℕ → ℕ) (a b p φ : ℕ) :
    ℕ × ℕ × ℕ × ℕ :=
  let μ := p * (p - 1) / 2
  let init : ℕ × ℕ × ℕ × ℕ × ℕ := (4 * p * (p - 1), 0, 0, 0, theorem_5_5_bound V a b p)
  let res := Nat.rec (motive := fun _ => ℕ × ℕ × ℕ × ℕ × ℕ) init
    (fun m acc => theorem_4_1_step V a b p φ μ m acc) μ
  (res.2.1, res.2.2.1, res.2.2.2.1, res.2.2.2.2)

/-- **Graph Minors XVI, (4.1)** (pages 52 and 58), with explicit parameters
`theorem_4_1_bound V a b p φ`. -/
theorem theorem_4_1_explicit
    (V : ℕ → ℕ → ℕ → ℕ → ℕ) (hV : ∀ a b c k, GM07.vModel a b c k ≤ V a b c k)
    {S : Type w} [TopologicalSpace S] [T2Space S]
    (hS : IsClosedSurface S) (hconn : ConnectedSpace S)
    {a b : ℕ} (he : Nonempty (S ≃ₜ SurfaceModel a b 0))
    (p φ : ℕ) (hφ : 1 ≤ φ) :
    let res := theorem_4_1_bound V a b p φ
    1 ≤ res.2.2.2 ∧
    ∀ {α : Type u} {β : Type v} (G : Graph α β) (θ_star θ_span : ℕ)
      (T_star : Set (Hypergraph α β × Hypergraph α β))
      (H : Drawing S) (η : SpanEmbedding H G)
      (T : Set (Hypergraph S (Set S) × Hypergraph S (Set S)))
      (hT : IsGraphTangle G θ_star T_star),
      res.2.2.2 ≤ θ_span → IsSigmaSpan G H η θ_star θ_span T_star T →
      (∃ (S' : Type w) (_ : TopologicalSpace S') (_ : T2Space S')
        (H' : Drawing S') (η' : SpanEmbedding H' G) (θ_span' : ℕ)
        (T' : Set (Hypergraph S' (Set S') × Hypergraph S' (Set S'))),
        IsClosedSurface S' ∧ ConnectedSpace S' ∧
        IsObtainedByAddingHandleOrCrosscap S S' ∧
        φ ≤ θ_span' ∧ IsSigmaSpan G H' η' θ_star θ_span' T_star T') ∨
      (∃ (Z : Set α) (S_seg : Set (Society α β))
        (α_disc : Society α β → Set S) (α_pt : α → S),
        Z ⊆ V(G) ∧ Z.ncard ≤ res.2.2.1 ∧ Z.ncard < θ_star ∧
        IsCentralSegregation (deleteVertices G Z)
          (deleteGraphVerticesTangle G hT.finite_V hT.finite_E Z T_star θ_star) S_seg ∧
        IsSegregationOfType (deleteVertices G Z) res.2.1 res.1 S_seg ∧
        IsProperArrangement S_seg α_disc α_pt) ∨
      ControlsMinor G (completeGraph p) T_star := by
  let μ := p * (p - 1) / 2
  let init : ℕ × ℕ × ℕ × ℕ × ℕ := (4 * p * (p - 1), 0, 0, 0, theorem_5_5_bound V a b p)
  let st : ℕ → ℕ × ℕ × ℕ × ℕ × ℕ := fun m =>
    Nat.rec (motive := fun _ => ℕ × ℕ × ℕ × ℕ × ℕ) init
      (fun k acc => theorem_4_1_step V a b p φ μ k acc) m
  obtain ⟨hθ_μ_pos, h55_prop⟩ := theorem_5_5_explicit.{u, v, w} V hV hS hconn he p
  have hind : ∀ m : ℕ, m ≤ μ →
      1 ≤ (st m).2.2.2.2 ∧
      ∀ {α : Type u} {β : Type v} (G : Graph α β) (θ_star : ℕ)
        (T_star : Set (Hypergraph α β × Hypergraph α β))
        (hT : IsGraphTangle G θ_star T_star),
        HasHairlessAnimal S G T_star θ_star (μ - m) (st m).2.2.2.2 (st m).1 →
        (∃ (S' : Type w) (_ : TopologicalSpace S') (_ : T2Space S')
          (H' : Drawing S') (η' : SpanEmbedding H' G) (θ_span' : ℕ)
          (T' : Set (Hypergraph S' (Set S') × Hypergraph S' (Set S'))),
          IsClosedSurface S' ∧ ConnectedSpace S' ∧
          IsObtainedByAddingHandleOrCrosscap S S' ∧
          φ ≤ θ_span' ∧ IsSigmaSpan G H' η' θ_star θ_span' T_star T') ∨
        (∃ (Z : Set α) (S_seg : Set (Society α β))
          (α_disc : Society α β → Set S) (α_pt : α → S),
          Z ⊆ V(G) ∧ Z.ncard ≤ (st m).2.2.2.1 ∧ Z.ncard < θ_star ∧
          IsCentralSegregation (deleteVertices G Z)
            (deleteGraphVerticesTangle G hT.finite_V hT.finite_E Z T_star θ_star) S_seg ∧
          IsSegregationOfType (deleteVertices G Z) (st m).2.2.1 (st m).2.1 S_seg ∧
          IsProperArrangement S_seg α_disc α_pt) ∨
        ControlsMinor G (completeGraph p) T_star := by
    intro m
    induction m with
    | zero =>
      intro _
      refine ⟨hθ_μ_pos, ?_⟩
      intro α β G θ_star T_star hT hAnim
      rw [Nat.sub_zero] at hAnim
      exact Or.inr (Or.inr (h55_prop G θ_star T_star hT hAnim))
    | succ m ih =>
      intro hm_le
      obtain ⟨hθ_next_pos, hnext⟩ := ih (by omega)
      let i := μ - (m + 1)
      obtain ⟨hθ_i_pos, h51_prop⟩ :=
        theorem_5_1_explicit.{u, v, w} V hV hS hconn he p (st m).1 i φ (st m).2.2.2.2
          hφ hθ_next_pos
      refine ⟨hθ_i_pos, ?_⟩
      intro α β G θ_star T_star hT hAnim
      rcases h51_prop G θ_star T_star hT hAnim with
        hOut1 | hOut2 | ⟨Z, S_seg, α_disc, α_pt, hZ_sub, hZ_le, hZ_lt, hCent, hType, hProp⟩ | hOut4
      · exact Or.inl hOut1
      · have hi_succ : i + 1 = μ - m := by omega
        rw [hi_succ] at hOut2
        rcases hnext G θ_star T_star hT hOut2 with
          hOut1' | ⟨Z, S_seg, α_disc, α_pt, hZ_sub, hZ_le, hZ_lt, hCent, hType, hProp⟩ | hOut4'
        · exact Or.inl hOut1'
        · exact Or.inr (Or.inl ⟨Z, S_seg, α_disc, α_pt,
            hZ_sub, hZ_le.trans (le_max_left _ _), hZ_lt, hCent,
            hType.mono (le_max_left _ _) (le_max_left _ _), hProp⟩)
        · exact Or.inr (Or.inr hOut4')
      · exact Or.inr (Or.inl ⟨Z, S_seg, α_disc, α_pt,
          hZ_sub, hZ_le.trans (le_max_right _ _), hZ_lt, hCent,
          hType.mono (le_max_right _ _) (le_max_right _ _), hProp⟩)
      · exact Or.inr (Or.inr hOut4)
  obtain ⟨hθ₀_pos, hfull⟩ := hind μ le_rfl
  refine ⟨hθ₀_pos, ?_⟩
  intro α β G θ_star θ_span T_star H η T hT hθ₀_le hSpan
  obtain ⟨d, hMet⟩ := exists_tangleMetric hS hSpan.isRespectful
  have hAnim₀ : HasHairlessAnimal S G T_star θ_star (μ - μ) (st μ).2.2.2.2 (st μ).1 := by
    rw [Nat.sub_self]
    exact hasHairlessAnimal_zero_of_isSigmaSpan hθ₀_pos hθ₀_le hSpan hMet
  exact hfull G θ_star T_star hT hAnim₀

/-- **Graph Minors XVI, (4.1)** (page 52, proved on page 58 from (5.1) and (5.5)). -/
theorem theorem_4_1_of_5_1_and_5_5
     :
    GM16Theorem41Statement.{u, v, w} := by
  intro S _ _ hS hconn p φ hφ
  let : ConnectedSpace S := hconn
  obtain ⟨a, b, he⟩ := GM12.exists_closed_surface_model hS
  let res := theorem_4_1_bound GM07.vModel a b p φ
  exact ⟨res.1, res.2.1, res.2.2.1, res.2.2.2,
    theorem_4_1_explicit.{u, v, w} GM07.vModel (fun _ _ _ _ => le_rfl) hS hconn he p φ hφ⟩

/-- Graph Minors XVI, (4.1), pages 52 and 58, by the backward induction
on the number of horns, using the proved (5.1) and (5.5). -/
theorem theorem_4_1_proof : GM16Theorem41Statement.{u, v, w} :=
  theorem_4_1_of_5_1_and_5_5

/-- One step of the backward surface-tower induction in Graph Minors XVI, (3.1),
carrying `(κ, ρ, ζ, θ_max)`. -/
@[expose] def theorem_3_1_towerStep (V : ℕ → ℕ → ℕ → ℕ → ℕ) (vB eB : ℕ)
    (m : ℕ) (st : ℕ × ℕ × ℕ × ℕ) : ℕ × ℕ × ℕ × ℕ :=
  let (κ_prev, ρ_prev, ζ_prev, θ_max) := st
  let p := GM12.gm16_theorem42_bound vB eB
  let N := towerN eB
  let len := towerLen eB
  let idx := len - (m + 1)
  let a := towerA N idx
  let b := towerB N idx
  let φ_m := θ_max + 1
  let θ_draw := GM12.theorem_4_3_bound V a b vB eB
  let cur := theorem_4_1_bound V a b p φ_m
  (max κ_prev cur.1, max ρ_prev cur.2.1, max ζ_prev cur.2.2.1,
    max θ_max (max θ_draw cur.2.2.2))

/-- Explicit `(κ, ρ, ζ, θ)` parameters for Graph Minors XVI, (3.1), depending only on
an upper bound `V` on `GM07.vModel` and upper bounds `(vB, eB)` on the excluded graph's
vertex and edge counts. -/
@[expose] def theorem_3_1_bound (V : ℕ → ℕ → ℕ → ℕ → ℕ) (vB eB : ℕ) : ℕ × ℕ × ℕ × ℕ :=
  let p := GM12.gm16_theorem42_bound vB eB
  let len := towerLen eB
  let st := Nat.rec (motive := fun _ => ℕ × ℕ × ℕ × ℕ) (0, 0, 0, 1)
    (fun m acc => theorem_3_1_towerStep V vB eB m acc) len
  (st.1, st.2.1, st.2.2.1, max (theorem_4_2_bound st.2.2.2) p)

/-- **Graph Minors XVI, (3.1)** (pages 49 and 54), with explicit parameters
`theorem_3_1_bound V vB eB`. -/
theorem theorem_3_1_explicit
    (V : ℕ → ℕ → ℕ → ℕ → ℕ) (hV : ∀ a b c k, GM07.vModel a b c k ≤ V a b c k)
    {α' : Type u'} {β' : Type v'} (L : Graph α' β') (hVL : V(L).Finite) (hEL : E(L).Finite)
    {vB eB : ℕ} (hvB : V(L).ncard ≤ vB) (heB : E(L).ncard ≤ eB) :
    let res := theorem_3_1_bound V vB eB
    1 ≤ res.2.2.2 ∧
    ∀ {α : Type u} {β : Type v} (G : Graph α β) (θ_G : ℕ)
      (T : Set (Hypergraph α β × Hypergraph α β))
      (hT : IsGraphTangle G θ_G T),
      res.2.2.2 ≤ θ_G → ¬ ControlsMinor G L T →
      ∃ (Z : Set α) (S_seg : Set (Society α β))
        (S : Type w) (_ : TopologicalSpace S) (_ : T2Space S)
        (α_disc : Society α β → Set S) (α_pt : α → S),
        Z ⊆ V(G) ∧ Z.ncard ≤ res.2.2.1 ∧ Z.ncard < θ_G ∧
        IsClosedSurface S ∧ ConnectedSpace S ∧ ¬ CanBeDrawnIn S L ∧
        IsCentralSegregation (deleteVertices G Z)
          (deleteGraphVerticesTangle G hT.finite_V hT.finite_E Z T θ_G) S_seg ∧
        IsSegregationOfType (deleteVertices G Z) res.2.1 res.1 S_seg ∧
        IsProperArrangement S_seg α_disc α_pt := by
  classical
  let tower : SurfaceTowerFor.{u, v, w, u', v'} L := surfaceTowerExplicit L hVL hEL heB
  let len := towerLen eB
  letI : ∀ i : Fin len, TopologicalSpace (tower.Surf i) := fun i => tower.topSpace i
  letI : ∀ i : Fin len, T2Space (tower.Surf i) := fun i => tower.t2Space i
  let p := GM12.gm16_theorem42_bound vB eB
  let st : ℕ → ℕ × ℕ × ℕ × ℕ := fun m =>
    Nat.rec (motive := fun _ => ℕ × ℕ × ℕ × ℕ) (0, 0, 0, 1)
      (fun k acc => theorem_3_1_towerStep V vB eB k acc) m
  have hind : ∀ m : ℕ, m ≤ len →
      1 ≤ (st m).2.2.2 ∧
      ∀ {α : Type u} {β : Type v} (G : Graph α β) (θ_G : ℕ)
        (T_star : Set (Hypergraph α β × Hypergraph α β))
        (hT : IsGraphTangle G θ_G T_star),
        p ≤ θ_G → ¬ ControlsMinor G L T_star →
        ∀ (i : Fin len), len - m ≤ i.1 →
        ∀ (H : Drawing (tower.Surf i)) (η : SpanEmbedding H G) (θ_span : ℕ)
          (T : Set (Hypergraph (tower.Surf i) (Set (tower.Surf i)) ×
            Hypergraph (tower.Surf i) (Set (tower.Surf i)))),
          (st m).2.2.2 ≤ θ_span → IsSigmaSpan G H η θ_G θ_span T_star T →
          ∃ (Z : Set α) (S_seg : Set (Society α β))
            (S : Type w) (_ : TopologicalSpace S) (_ : T2Space S)
            (α_disc : Society α β → Set S) (α_pt : α → S),
            Z ⊆ V(G) ∧ Z.ncard ≤ (st m).2.2.1 ∧ Z.ncard < θ_G ∧
            IsClosedSurface S ∧ ConnectedSpace S ∧ ¬ CanBeDrawnIn S L ∧
            IsCentralSegregation (deleteVertices G Z)
              (deleteGraphVerticesTangle G hT.finite_V hT.finite_E Z T_star θ_G) S_seg ∧
            IsSegregationOfType (deleteVertices G Z) (st m).2.1 (st m).1 S_seg ∧
            IsProperArrangement S_seg α_disc α_pt := by
    intro m
    induction m with
    | zero =>
      intro _
      refine ⟨le_rfl, ?_⟩
      intro α β G θ_G T_star hT _ _ i hi
      exact absurd i.2 (not_lt_of_ge (by omega))
    | succ m ih =>
      intro hm_le
      obtain ⟨hθ_prev_pos, hprev⟩ := ih (by omega)
      let idx_m : Fin len := ⟨len - (m + 1), by omega⟩
      let a_m := towerA (towerN eB) idx_m.1
      let b_m := towerB (towerN eB) idx_m.1
      have he_m : Nonempty (tower.Surf idx_m ≃ₜ SurfaceModel a_m b_m 0) :=
        ⟨Homeomorph.ulift⟩
      let φ_m := (st m).2.2.2 + 1
      have hφ_pos : 1 ≤ φ_m := Nat.le_add_left 1 _
      have hθ_step_ge : (st m).2.2.2 ≤ (st (m + 1)).2.2.2 := le_max_left _ _
      refine ⟨hθ_prev_pos.trans hθ_step_ge, ?_⟩
      intro α β G θ_G T_star hT hp_le hnot_L i hi H η θ_span T hθ_le hSpan
      by_cases hi_eq : i = idx_m
      · subst hi_eq
        by_cases hdraw : CanBeDrawnIn (tower.Surf idx_m) L
        · have hθ_draw_le : GM12.theorem_4_3_bound V a_m b_m vB eB ≤ θ_span :=
            ((le_max_left _ _).trans (le_max_right _ _)).trans hθ_le
          exact (theorem_4_3_explicit.{u, v, w, u', v'} V hV L
            (tower.isClosedSurface idx_m) (tower.isConnected idx_m) he_m hVL hEL hvB heB hdraw
            G θ_G T_star H η θ_span T hT hnot_L hθ_draw_le hSpan).elim
        · have hθ_cur_le : (theorem_4_1_bound V a_m b_m p φ_m).2.2.2 ≤ θ_span :=
            ((le_max_right _ _).trans (le_max_right _ _)).trans hθ_le
          obtain ⟨_, h41_prop⟩ := theorem_4_1_explicit.{u, v, w} V hV
            (tower.isClosedSurface idx_m) (tower.isConnected idx_m) he_m p φ_m hφ_pos
          rcases h41_prop G θ_G θ_span T_star H η T hT hθ_cur_le hSpan with
            ⟨S', htopS', ht2S', H', η', θ_span', T', hCS', hconnS', hAdd, hφ_le', hSpan'⟩ |
            ⟨Z, S_seg, α_disc, α_pt, hZ_sub, hZ_le, hZ_lt, hCent, hType, hProp⟩ |
            hCtrlKp
          · obtain ⟨j, hij, H_j, η_j, θ_span_j, T_j, hφ_j, hSpan_j⟩ :=
              tower.step_index idx_m hdraw G θ_G φ_m T_star S' H' η' θ_span' T'
                hCS' hconnS' hAdd hφ_le' hSpan'
            have hj_ge : len - m ≤ j.1 := by
              have : idx_m.1 < j.1 := hij
              dsimp [idx_m] at this
              omega
            have hθ_prev_j : (st m).2.2.2 ≤ θ_span_j := (Nat.le_succ _).trans hφ_j
            obtain ⟨Z, S_seg, S_out, htop_out, ht2_out, α_disc, α_pt,
              hZ_sub, hZ_le, hZ_lt, hCS_out, hconn_out, hnot_draw_out,
              hCent, hType, hProp⟩ :=
              hprev G θ_G T_star hT hp_le hnot_L j hj_ge H_j η_j θ_span_j T_j hθ_prev_j hSpan_j
            exact ⟨Z, S_seg, S_out, htop_out, ht2_out, α_disc, α_pt,
              hZ_sub, hZ_le.trans (le_max_left _ _), hZ_lt, hCS_out, hconn_out, hnot_draw_out,
              hCent, hType.mono (le_max_left _ _) (le_max_left _ _), hProp⟩
          · exact ⟨Z, S_seg, tower.Surf idx_m, tower.topSpace idx_m, tower.t2Space idx_m,
              α_disc, α_pt, hZ_sub, hZ_le.trans (le_max_right _ _), hZ_lt,
              tower.isClosedSurface idx_m, tower.isConnected idx_m, hdraw,
              hCent, hType.mono (le_max_right _ _) (le_max_right _ _), hProp⟩
          · have hgm12_Kp :
                GM12.ControlsMinor (Hypergraph.ofGraph G hT.finite_V hT.finite_E) θ_G T_star
                  (completeGraph p) :=
              gm12_controlsMinor_of_controlsMinor hT.finite_V hT.finite_E hCtrlKp
                (by simpa using hp_le)
            have hgm12_L := GM12.gm16_theorem42_explicit L hVL hEL hvB heB G θ_G T_star hT hgm12_Kp
            exact (hnot_L (controlsMinor_of_gm12 hgm12_L)).elim
      · have hi_gt : len - m ≤ i.1 := by
          have : i.1 ≠ len - (m + 1) := fun h => hi_eq (Fin.ext h)
          omega
        obtain ⟨Z, S_seg, S_out, htop_out, ht2_out, α_disc, α_pt,
          hZ_sub, hZ_le, hZ_lt, hCS_out, hconn_out, hnot_draw_out,
          hCent, hType, hProp⟩ :=
          hprev G θ_G T_star hT hp_le hnot_L i hi_gt H η θ_span T (hθ_step_ge.trans hθ_le) hSpan
        exact ⟨Z, S_seg, S_out, htop_out, ht2_out, α_disc, α_pt,
          hZ_sub, hZ_le.trans (le_max_left _ _), hZ_lt, hCS_out, hconn_out, hnot_draw_out,
          hCent, hType.mono (le_max_left _ _) (le_max_left _ _), hProp⟩
  obtain ⟨_, hfull⟩ := hind len le_rfl
  let i₀ : Fin len := ⟨0, tower.one_le_n⟩
  have hθ_pos : 1 ≤ max (theorem_4_2_bound (st len).2.2.2) p := by
    dsimp only [theorem_4_2_bound]
    exact (by omega : 1 ≤ conformalWallBound (2 * ((st len).2.2.2 + 2)) + 2 * ((st len).2.2.2 + 2)).trans
      (le_max_left _ _)
  refine ⟨hθ_pos, ?_⟩
  intro α β G θ_G T hT hθ_le hnot_L
  have hθ_star₀_le : theorem_4_2_bound (st len).2.2.2 ≤ θ_G := (le_max_left _ _).trans hθ_le
  have hp_le : p ≤ θ_G := (le_max_right _ _).trans hθ_le
  obtain ⟨H₀, η₀, θ_span₀, T₀, hθ₀_le, hSpan₀⟩ :=
    theorem_4_2_explicit.{u, v, w} (st len).2.2.2 G θ_G T hT hθ_star₀_le (tower.Surf i₀)
      (tower.isClosedSurface i₀) (tower.isConnected i₀) tower.isSphere_zero
  exact hfull G θ_G T hT hp_le hnot_L i₀ (by omega) H₀ η₀ θ_span₀ T₀ hθ₀_le hSpan₀

/-- **Graph Minors XVI, (3.1)** (page 54, proved from (4.1), (4.2), (4.3), and Graph Minors XII,
(4.2)):
For any finite graph `L` with a surface tower `tower : SurfaceTowerFor L`, there exist
`κ, ρ, ζ ≥ 0` and `θ ≥ 1` such that any tangle `T` of order `≥ θ` in a graph `G` controlling no
`L`-minor admits `Z ⊆ V(G)` with `|Z| ≤ ζ` and a `T \ Z`-central segregation of `G \ Z` of type
`(ρ, κ)` with a proper arrangement in some surface in which `L` cannot be drawn. -/
theorem theorem_3_1_of_tower
    {α' : Type u'} {β' : Type v'} (L : Graph α' β') (hVL : V(L).Finite) (hEL : E(L).Finite)
    (_tower : SurfaceTowerFor.{u, v, w, u', v'} L) :
    ∃ κ ρ ζ θ : ℕ, 1 ≤ θ ∧
      ∀ {α : Type u} {β : Type v} (G : Graph α β) (θ_G : ℕ)
        (T : Set (Hypergraph α β × Hypergraph α β))
        (hT : IsGraphTangle G θ_G T),
        θ ≤ θ_G → ¬ ControlsMinor G L T →
        ∃ (Z : Set α) (S_seg : Set (Society α β))
          (S : Type w) (_ : TopologicalSpace S) (_ : T2Space S)
          (α_disc : Society α β → Set S) (α_pt : α → S),
          Z ⊆ V(G) ∧ Z.ncard ≤ ζ ∧ Z.ncard < θ_G ∧
          IsClosedSurface S ∧ ConnectedSpace S ∧ ¬ CanBeDrawnIn S L ∧
          IsCentralSegregation (deleteVertices G Z)
            (deleteGraphVerticesTangle G hT.finite_V hT.finite_E Z T θ_G) S_seg ∧
          IsSegregationOfType (deleteVertices G Z) ρ κ S_seg ∧
          IsProperArrangement S_seg α_disc α_pt := by
  let res := theorem_3_1_bound GM07.vModel V(L).ncard E(L).ncard
  exact ⟨res.1, res.2.1, res.2.2.1, res.2.2.2,
    theorem_3_1_explicit.{u, v, w, u', v'} GM07.vModel (fun _ _ _ _ => le_rfl)
      L hVL hEL le_rfl le_rfl⟩

/-- **Graph Minors XVI, (3.1)** (page 49, proved on page 54 from (4.1), (4.2), (4.3), and
Graph Minors XII, (4.2)). -/
theorem theorem_3_1_of_statements
     :
    GM16Theorem31Statement.{u, v, w, u', v'} := by
  intro α' β' L hVL hEL
  let res := theorem_3_1_bound GM07.vModel V(L).ncard E(L).ncard
  exact ⟨res.1, res.2.1, res.2.2.1, res.2.2.2,
    theorem_3_1_explicit.{u, v, w, u', v'} GM07.vModel (fun _ _ _ _ => le_rfl)
      L hVL hEL le_rfl le_rfl⟩

/-- Graph Minors XVI, (3.1), pages 49 and 54, by induction over the
surface tower, starting with the proved sphere span (4.2) and using
the proved animal reduction (4.1). No result of XVI is assumed. -/
theorem theorem_3_1_proof : GM16Theorem31Statement.{u, v, w, u', v'} :=
  theorem_3_1_of_statements

end GraphMinor.GM16
