module

public import GraphMinor.GM16.Section6
import GraphMinor.GM16.Section6Linkages

public import GraphMinor.GM12.Bridge

/-!
# The two applications of (5.2) in XVI (6.3)

The paths used on pages 60–61 lie in a subgraph with no edge of the
embedded drawing. Its drawing vertices are all in a separated marked
set. Shortening the paths gives exactly the paths required by (5.2).
-/

public section
namespace GraphMinor.GM16
open Set Graph GraphMinor.Surface GraphMinor.GM11 GraphMinor.GM14 GraphMinor.GM15
universe u v w

/-- Marked-path threshold property for a given threshold `r`. -/
@[expose] def IsMarkedPathThreshold (S : Type w) [TopologicalSpace S] [T2Space S] (p r : ℕ) : Prop :=
  ∀ {α : Type u} {β : Type v} (G K : Graph α β) (θ_star θ_span : ℕ)
    (T_star : Set (Hypergraph α β × Hypergraph α β))
    (H : Drawing S) (η : SpanEmbedding H G)
    (T : Set (Hypergraph S (Set S) × Hypergraph S (Set S)))
    (d : Set S → Set S → ℕ) (Y : Set S)
    (P : Fin (p * (p - 1) / 2) → Graph α β)
    (a b : Fin (p * (p - 1) / 2) → α),
    IsSigmaSpan G H η θ_star θ_span T_star T → HasTangleMetric H θ_span T d →
    r ≤ θ_span → Y ⊆ H.V →
    (∀ y ∈ Y, ∀ z ∈ Y, y ≠ z → r ≤ d {y} {z}) →
    K ≤ G → Disjoint E(K) E(η.imageGraph) →
    V(K) ∩ V(η.imageGraph) ⊆ η.vMap '' Y →
    (∀ i, a i ∈ V(η.imageGraph) ∧ b i ∈ V(η.imageGraph) ∧ a i ≠ b i ∧
      GraphMinor.GM09.IsGraphPathWithEnds K (P i) (a i) (b i)) →
    Pairwise (fun i j => Disjoint V(P i) V(P j)) → ControlsMinor G (completeGraph p) T_star

/-- Explicit marked-path threshold from `theorem_5_2_explicit`, with `r = GM12.theorem_4_4_bound V a b p`. -/
theorem clique_threshold_for_marked_paths_explicit
    (V : ℕ → ℕ → ℕ → ℕ → ℕ) (hV : ∀ a b c k, GM07.vModel a b c k ≤ V a b c k)
    {S : Type w} [TopologicalSpace S] [T2Space S]
    (hS : IsClosedSurface S) (hConn : ConnectedSpace S)
    {a b : ℕ} (he : Nonempty (S ≃ₜ SurfaceModel a b 0)) (p : ℕ) :
    IsMarkedPathThreshold.{u, v, w} S p (GM12.theorem_4_4_bound V a b p) := by
  intro α β G K θ_star θ_span T_star H η T d Y P a_end b_end
    hSpan hMet horder hY hsep hKG hKH hKY hP hPP
  obtain ⟨R, s, t, hst, hR, hRR⟩ :=
    hPaths_of_disjoint_paths_in_subgraph hKG hKH hKY hP hPP
  obtain ⟨hs, ht, hstdisj⟩ := hPath_end_labels_injective hR hRR
  apply theorem_5_2_explicit.{u, v, w} V hV hS hConn he p
    G θ_star θ_span T_star H η T d s t R hSpan hMet horder
    (fun i => ⟨hY (hst i).1, hY (hst i).2.1, (hst i).2.2⟩) hs ht hstdisj
  · intro y hy z hz hyz
    have hyY : y ∈ Y := by
      rcases hy with ⟨i, rfl⟩ | ⟨i, rfl⟩
      · exact (hst i).1
      · exact (hst i).2.1
    have hzY : z ∈ Y := by
      rcases hz with ⟨i, rfl⟩ | ⟨i, rfl⟩
      · exact (hst i).1
      · exact (hst i).2.1
    exact hsep y hyY z hzY hyz
  · exact hR
  · exact hRR

/-- The threshold from (5.2) also applies to disjoint paths in any
subgraph whose old-graph vertices lie in a separated set. This proves
the form used twice in XVI (6.3), pages 60–61. -/
theorem clique_threshold_for_marked_paths
    {S : Type w} [TopologicalSpace S] [T2Space S]
    (hS : IsClosedSurface S) (hConn : ConnectedSpace S) (p : ℕ) :
    ∃ r : ℕ, 1 ≤ r ∧
      ∀ {α : Type u} {β : Type v} (G K : Graph α β) (θ_star θ_span : ℕ)
        (T_star : Set (Hypergraph α β × Hypergraph α β))
        (H : Drawing S) (η : SpanEmbedding H G)
        (T : Set (Hypergraph S (Set S) × Hypergraph S (Set S)))
        (d : Set S → Set S → ℕ) (Y : Set S)
        (P : Fin (p * (p - 1) / 2) → Graph α β)
        (a b : Fin (p * (p - 1) / 2) → α),
        IsSigmaSpan G H η θ_star θ_span T_star T → HasTangleMetric H θ_span T d →
        r ≤ θ_span → Y ⊆ H.V →
        (∀ y ∈ Y, ∀ z ∈ Y, y ≠ z → r ≤ d {y} {z}) →
        K ≤ G → Disjoint E(K) E(η.imageGraph) →
        V(K) ∩ V(η.imageGraph) ⊆ η.vMap '' Y →
        (∀ i, a i ∈ V(η.imageGraph) ∧ b i ∈ V(η.imageGraph) ∧ a i ≠ b i ∧
          GraphMinor.GM09.IsGraphPathWithEnds K (P i) (a i) (b i)) →
        Pairwise (fun i j => Disjoint V(P i) V(P j)) → ControlsMinor G (completeGraph p) T_star := by
  let : ConnectedSpace S := hConn
  obtain ⟨a, b, he⟩ := GM12.exists_closed_surface_model hS
  exact ⟨GM12.theorem_4_4_bound GM07.vModel a b p, GM12.one_le_theorem_4_4_bound _ a b p,
    clique_threshold_for_marked_paths_explicit.{u, v, w} GM07.vModel (fun _ _ _ _ => le_rfl)
      hS hConn he p⟩

/-- The threshold from (5.2) for the two marked-path applications in
XVI (6.3), pages 60–61. -/
noncomputable def cliquePathThreshold
    (h44 : GM12Theorem44Statement.{u, v, w})
    {S : Type w} [TopologicalSpace S] [T2Space S]
    (hS : IsClosedSurface S) (hConn : ConnectedSpace S) (p : ℕ) : ℕ :=
  (clique_threshold_for_marked_paths.{u, v, w} hS hConn p).choose

/-- The marked-path property of the chosen threshold. -/
theorem cliquePathThreshold_spec
    {S : Type w} [TopologicalSpace S] [T2Space S]
    (hS : IsClosedSurface S) (hConn : ConnectedSpace S) (p : ℕ) :
    1 ≤ cliquePathThreshold GraphMinor.GM12.gm16_theorem44.{u, v, w} hS hConn p ∧
    ∀ {α : Type u} {β : Type v} (G K : Graph α β) (θ_star θ_span : ℕ)
        (T_star : Set (Hypergraph α β × Hypergraph α β))
        (H : Drawing S) (η : SpanEmbedding H G)
        (T : Set (Hypergraph S (Set S) × Hypergraph S (Set S)))
        (d : Set S → Set S → ℕ) (Y : Set S)
        (P : Fin (p * (p - 1) / 2) → Graph α β)
        (a b : Fin (p * (p - 1) / 2) → α),
        IsSigmaSpan G H η θ_star θ_span T_star T → HasTangleMetric H θ_span T d →
        cliquePathThreshold GraphMinor.GM12.gm16_theorem44.{u, v, w} hS hConn p ≤ θ_span → Y ⊆ H.V →
        (∀ y ∈ Y, ∀ z ∈ Y, y ≠ z → cliquePathThreshold GraphMinor.GM12.gm16_theorem44.{u, v, w} hS hConn p ≤ d {y} {z}) →
        K ≤ G → Disjoint E(K) E(η.imageGraph) →
        V(K) ∩ V(η.imageGraph) ⊆ η.vMap '' Y →
        (∀ i, a i ∈ V(η.imageGraph) ∧ b i ∈ V(η.imageGraph) ∧ a i ≠ b i ∧
          GraphMinor.GM09.IsGraphPathWithEnds K (P i) (a i) (b i)) →
        Pairwise (fun i j => Disjoint V(P i) V(P j)) → ControlsMinor G (completeGraph p) T_star := by
  exact (clique_threshold_for_marked_paths.{u, v, w} hS hConn p).choose_spec

end GraphMinor.GM16
