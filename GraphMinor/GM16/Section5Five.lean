module

public import GraphMinor.GM16.Section5
import GraphMinor.GM16.Section5Linkage
import GraphMinor.GM09.Basic
import GraphMinor.GM11.Regions

import GraphMinor.GM11.CitedResults

import GraphMinor.GM12.Bridge

/-!
# Graph Minors XVI (5.5)

Choose the threshold from (5.2) and double it. Claim (1), proved in
Section5Linkage, supplies the required number of disjoint old-graph paths
with separated ends. Their disjointness also makes all these ends
distinct, so (5.2) gives the controlled clique minor.
-/

public section
namespace GraphMinor.GM16
open Set Function Graph GraphMinor.Surface GraphMinor.GM09 GraphMinor.GM11 GraphMinor.GM14 GraphMinor.GM15
universe u v w

/-- Explicit threshold for Graph Minors XVI, (5.5). -/
@[expose] def theorem_5_5_bound (V : ℕ → ℕ → ℕ → ℕ → ℕ) (a b p : ℕ) : ℕ :=
  2 * GM12.theorem_4_4_bound V a b p

/-- **Graph Minors XVI, (5.5)** (pages 57–58), with explicit threshold `theorem_5_5_bound V a b p`. -/
theorem theorem_5_5_explicit
    (V : ℕ → ℕ → ℕ → ℕ → ℕ) (hV : ∀ a b c k, GM07.vModel a b c k ≤ V a b c k)
    {S : Type w} [TopologicalSpace S] [T2Space S]
    (hS : IsClosedSurface S) (hConn : ConnectedSpace S)
    {a b : ℕ} (he : Nonempty (S ≃ₜ SurfaceModel a b 0)) (p : ℕ) :
    1 ≤ theorem_5_5_bound V a b p ∧
    ∀ {α : Type u} {β : Type v} (G : Graph α β) (θ_star : ℕ)
      (T_star : Set (Hypergraph α β × Hypergraph α β)),
      IsGraphTangle G θ_star T_star →
      HasHairlessAnimal S G T_star θ_star (p * (p - 1) / 2)
        (theorem_5_5_bound V a b p) (4 * p * (p - 1)) →
      ControlsMinor G (completeGraph p) T_star := by
  classical
  let μ := p * (p - 1) / 2
  set r := GM12.theorem_4_4_bound V a b p
  have hr : 1 ≤ r := GM12.one_le_theorem_4_4_bound V a b p
  refine ⟨by unfold theorem_5_5_bound; omega, ?_⟩
  intro α β G θ_star T_star hT hAnimal
  obtain ⟨H, η, θ_span, T, d, X, Y, hAnim⟩ := hAnimal
  have hσ : 8 * μ ≤ 4 * p * (p - 1) := by
    calc
      8 * μ = 4 * (μ * 2) := by ring
      _ ≤ 4 * (p * (p - 1)) := Nat.mul_le_mul_left 4 (Nat.div_mul_le_self _ _)
      _ = 4 * p * (p - 1) := by ring
  have hAnim' : IsAnimal G T_star θ_star H η θ_span T d X Y μ 0 (2 * r) (8 * μ) :=
    hAnim.mono (by omega) le_rfl hσ
  obtain ⟨_, horder, hSpan, hMet, hXsub, hXcard, _, _, hhorns, _, _⟩ := hAnim'
  have hXfin : X.Finite := hT.finite_V.subset (fun x hx => (hXsub hx).1)
  obtain ⟨_, _, _, hsymm, htri, _⟩ := GraphMinor.GM11.gm15_theorem_9_1.{w} H θ_span T d hS hConn hMet
  have hsymV : ∀ a ∈ H.V, ∀ b ∈ H.V, d {a} {b} = d {b} {a} := by
    intro a ha b hb
    exact hsymm {a} ((Or.inl (Or.inl ⟨a, ha, rfl⟩))) {b} ((Or.inl (Or.inl ⟨b, hb, rfl⟩)))
  have htriV : ∀ a ∈ H.V, ∀ b ∈ H.V, ∀ c ∈ H.V,
      d {a} {c} ≤ d {a} {b} + d {b} {c} := by
    intro a ha b hb c hc
    exact htri {a} ((Or.inl (Or.inl ⟨a, ha, rfl⟩))) {b} ((Or.inl (Or.inl ⟨b, hb, rfl⟩)))
      {c} ((Or.inl (Or.inl ⟨c, hc, rfl⟩)))
  obtain ⟨Q, s, t, hst, hQ, hQQ, _, hdist⟩ := theorem_5_5_claim_1
    hT.finite_V hT.finite_E hXfin hXcard hhorns hsymV htriV μ le_rfl
  have hs : Injective s := by
    intro i j hij
    by_contra hne
    have hsi := IsGraphPathWithEnds.left_mem (hQ i).2.1
    have hsj := IsGraphPathWithEnds.left_mem (hQ j).2.1
    have heq := congrArg η.vMap hij
    exact (Set.disjoint_left.mp (hQQ hne)) hsi (heq ▸ hsj)
  have ht : Injective t := by
    intro i j hij
    by_contra hne
    have hti := IsGraphPathWithEnds.right_mem (hQ i).2.1
    have htj := IsGraphPathWithEnds.right_mem (hQ j).2.1
    have heq := congrArg η.vMap hij
    exact (Set.disjoint_left.mp (hQQ hne)) hti (heq ▸ htj)
  have hstdisj : Disjoint (range s) (range t) := by
    apply Set.disjoint_left.mpr
    rintro z ⟨i, rfl⟩ ⟨j, htj⟩
    by_cases hij : i = j
    · subst j
      exact (hst i).2.2 htj.symm
    · have hsi := IsGraphPathWithEnds.left_mem (hQ i).2.1
      have htj' := IsGraphPathWithEnds.right_mem (hQ j).2.1
      have heq := congrArg η.vMap htj
      exact (Set.disjoint_left.mp (hQQ hij)) hsi (heq ▸ htj')
  exact theorem_5_2_explicit.{u, v, w} V hV hS hConn he p
    G θ_star θ_span T_star H η T d s t Q hSpan hMet (by omega)
    hst hs ht hstdisj hdist hQ hQQ

/-- **Graph Minors XVI, (5.5)** (pages 57–58), by the paper's induction
on disjoint paths and then (5.2). The metric laws are supplied by XI (9.1),
and (5.2) uses XII (4.4). No statement of XVI is assumed. -/
theorem theorem_5_5_proof
     : GM16Theorem55Statement.{u, v, w} := by
  intro S _ _ hS hConn p
  let : ConnectedSpace S := hConn
  obtain ⟨a, b, he⟩ := GM12.exists_closed_surface_model hS
  exact ⟨theorem_5_5_bound GM07.vModel a b p,
    theorem_5_5_explicit.{u, v, w} GM07.vModel (fun _ _ _ _ => le_rfl) hS hConn he p⟩

end GraphMinor.GM16
