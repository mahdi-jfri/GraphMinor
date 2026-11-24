module

public import GraphMinor.GM12.Cited
public import GraphMinor.GM12.Defs
public import GraphMinor.GM15.Defs
public import GraphMinor.GM16.Defs
public import GraphMinor.GM12.Section4Theorem44Large
public import GraphMinor.GM12.Section4Theorem43
import GraphMinor.GM12.Section4SmallClique
import GraphMinor.GM12.Section3GeometricReduction
import GraphMinor.GM12.Section4SpanControl
import GraphMinor.GM12.Section4InducedEmbedding
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.FinCases

import GraphMinor.GM07.Section7
import GraphMinor.GM07.Bridge

/-!
# Graph Minors XII (4.4): all clique sizes

Use the path and branch construction of pages 251--252 when the
clique has at least three vertices. For the smaller cliques, the
target is drawable in the surface, so (4.3) applies as the paper
instructs. The conclusion is expressed for an embedded drawing and
an ambient tangle controlling its tangle.
-/

public section

namespace GraphMinor.GM12

open Set Graph Surface Hypergraph GM14 GM15

universe u

/-- Explicit threshold for Graph Minors XII, (4.4), for all clique sizes `p`. -/
@[expose] def theorem_4_4_bound (V : ℕ → ℕ → ℕ → ℕ → ℕ) (a b p : ℕ) : ℕ :=
  max (theorem_4_4_large_bound V a b p) (theorem_4_3_bound V a b 2 1)

theorem one_le_theorem_4_4_bound (V : ℕ → ℕ → ℕ → ℕ → ℕ) (a b p : ℕ) :
    1 ≤ theorem_4_4_bound V a b p :=
  (one_le_theorem_4_3_bound V a b 2 1).trans (le_max_right _ _)

/-- XII (4.4), pages 251--252, with the embedding and tangle relation explicit and
explicit threshold `theorem_4_4_bound V a b p`. -/
theorem theorem_4_4_span_explicit
    (V : ℕ → ℕ → ℕ → ℕ → ℕ) (hV : ∀ a b c k, GM07.vModel a b c k ≤ V a b c k)
    {S : Type u} [TopologicalSpace S] [T2Space S] [ConnectedSpace S]
    (hS : IsClosedSurface S) {a b : ℕ} (he : Nonempty (S ≃ₜ SurfaceModel a b 0)) (p : ℕ) :
    ∀ {α β : Type*} (G : Graph α β) (θstar θ : ℕ)
      (Tstar : Set (Hypergraph α β × Hypergraph α β))
      (Γ : Drawing S) (η : SpanEmbedding Γ G)
      (T : Set (Hypergraph S (Set S) × Hypergraph S (Set S)))
      (d : Set S → Set S → ℕ)
      (s r : Fin (p * (p - 1) / 2) → S) (P : Fin (p * (p - 1) / 2) → Graph α β)
      (hCtrl : IsControllingTangle G Γ η θstar θ Tstar T),
      HasTangleMetric Γ θ T d → theorem_4_4_bound V a b p ≤ θ →
      (∀ i, s i ∈ Γ.V ∧ r i ∈ Γ.V ∧ s i ≠ r i) →
      Function.Injective s → Function.Injective r → Disjoint (range s) (range r) →
      (∀ x ∈ range s ∪ range r, ∀ y ∈ range s ∪ range r, x ≠ y →
        theorem_4_4_bound V a b p ≤ d {x} {y}) →
      (∀ i, IsHPathWithEnds G η.imageGraph (P i) (η.vMap (s i)) (η.vMap (r i))) →
      Pairwise (fun i j => Disjoint (P i).vertexSet (P j).vertexSet) →
      ControlsMinor (Hypergraph.ofGraph G hCtrl.isTangle_star.finite_V
        hCtrl.isTangle_star.finite_E) θstar Tstar (GM16.completeGraph p) := by
  by_cases hp : 3 ≤ p
  · intro G θstar θ Tstar Γ η T d s r P hCtrl hm hθ hends hs hr hsr hfar hP hPP
    exact theorem_4_4_span_large_explicit V hV hS he p hp G θstar θ Tstar Γ η T d s r P hCtrl
      hm ((le_max_left _ _).trans hθ) hends hs hr hsr
      (fun x hx y hy hxy => (le_max_left _ _).trans (hfar x hx y hy hxy)) hP hPP
  · have hp2 : p ≤ 2 := by omega
    obtain ⟨D⟩ := exists_graphDrawing_complete_of_le_two hS hp2
    have hVle : (GM16.completeGraph p).vertexSet.ncard ≤ 2 := by
      have h1 : (GM16.completeGraph p).vertexSet = univ := rfl
      rw [h1, Set.ncard_univ, Nat.card_fin]
      exact hp2
    have hEle : (GM16.completeGraph p).edgeSet.ncard ≤ 1 := by
      interval_cases p
      · have hE0 : (GM16.completeGraph 0).edgeSet = ∅ := by
          ext e; simp only [mem_empty_iff_false, iff_false]
          rintro ⟨v, _, _⟩; exact Fin.elim0 v
        rw [hE0]; simp
      · have hE1 : (GM16.completeGraph 1).edgeSet = ∅ := by
          ext e; simp only [mem_empty_iff_false, iff_false]
          rintro ⟨u, v, huv, _⟩; exact huv (Subsingleton.elim u v)
        rw [hE1]; simp
      · have hE2 : (GM16.completeGraph 2).edgeSet ⊆ {s((0 : Fin 2), 1)} := by
          rintro e ⟨u, v, huv, rfl⟩
          fin_cases u <;> fin_cases v <;> simp_all [Sym2.eq_swap]
        exact (Set.ncard_le_ncard hE2 (Set.finite_singleton _)).trans (by simp)
    have hmain := theorem_4_3_drawing_explicit V hV hS he D hVle hEle
    intro G θstar θ Tstar Γ η T d s r P hCtrl hm hθ _ _ _ _ _ _ _
    exact controlsMinor_of_controlling_drawing_tangle η hCtrl
      (hmain Γ θ T d hm ((le_max_right _ _).trans hθ))

/-- XII (4.4), pages 251--252, with the embedding and tangle
relation explicit. The only statement hypotheses are the cited
VII (7.5), (5.1), and (5.5). -/
theorem theorem_4_4_span
    {S : Type u} [TopologicalSpace S] [T2Space S] [ConnectedSpace S]
    (hS : IsClosedSurface S) (p : ℕ) :
    ∃ N : ℕ, 1 ≤ N ∧
      ∀ {α β : Type*} (G : Graph α β) (θstar θ : ℕ)
        (Tstar : Set (Hypergraph α β × Hypergraph α β))
        (Γ : Drawing S) (η : SpanEmbedding Γ G)
        (T : Set (Hypergraph S (Set S) × Hypergraph S (Set S)))
        (d : Set S → Set S → ℕ)
        (s r : Fin (p * (p - 1) / 2) → S) (P : Fin (p * (p - 1) / 2) → Graph α β)
        (hCtrl : IsControllingTangle G Γ η θstar θ Tstar T),
      HasTangleMetric Γ θ T d → N ≤ θ →
      (∀ i, s i ∈ Γ.V ∧ r i ∈ Γ.V ∧ s i ≠ r i) →
      Function.Injective s → Function.Injective r → Disjoint (range s) (range r) →
      (∀ x ∈ range s ∪ range r, ∀ y ∈ range s ∪ range r, x ≠ y → N ≤ d {x} {y}) →
      (∀ i, IsHPathWithEnds G η.imageGraph (P i) (η.vMap (s i)) (η.vMap (r i))) →
      Pairwise (fun i j => Disjoint (P i).vertexSet (P j).vertexSet) →
      ControlsMinor (Hypergraph.ofGraph G hCtrl.isTangle_star.finite_V
        hCtrl.isTangle_star.finite_E) θstar Tstar (GM16.completeGraph p) := by
  obtain ⟨a, b, he⟩ := exists_closed_surface_model hS
  exact ⟨theorem_4_4_bound GM07.vModel a b p, one_le_theorem_4_4_bound _ a b p,
    theorem_4_4_span_explicit GM07.vModel (fun _ _ _ _ => le_rfl) hS he p⟩

/-- Graph Minors XII (4.4), pages 251--252, for the tangle induced
from a literal drawn subgraph of the ambient graph. All vertex and
edge names are shared with the drawing, as in the paper. -/
theorem theorem_4_4_proof
    {S : Type u} [TopologicalSpace S] [T2Space S] [ConnectedSpace S]
    (hS : IsClosedSurface S) (p : ℕ) :
    ∃ N : ℕ, 1 ≤ N ∧
      ∀ (Γ : Drawing S) (θ : ℕ)
        (T : Set (Hypergraph S (Set S) × Hypergraph S (Set S)))
        (d : Set S → Set S → ℕ) (G : Graph S (Set S))
        (hV : G.vertexSet.Finite) (hE : G.edgeSet.Finite),
      Γ.toGraph ≤ G → HasTangleMetric Γ θ T d → N ≤ θ →
      ∀ (s r : Fin (p * (p - 1) / 2) → S) (P : Fin (p * (p - 1) / 2) → Graph S (Set S)),
      (∀ i, s i ∈ Γ.V ∧ r i ∈ Γ.V ∧ s i ≠ r i) →
      Function.Injective s → Function.Injective r → Disjoint (range s) (range r) →
      (∀ x ∈ range s ∪ range r, ∀ y ∈ range s ∪ range r, x ≠ y → N ≤ d {x} {y}) →
      (∀ i, IsHPathWithEnds G Γ.toGraph (P i) (s i) (r i)) →
      Pairwise (fun i j => Disjoint (P i).vertexSet (P j).vertexSet) →
      ControlsMinor (Hypergraph.ofGraph G hV hE) θ
        (inducedBySubgraph (Hypergraph.ofGraph G hV hE) Γ.toHypergraph θ T) (GM16.completeGraph p) := by
  obtain ⟨N, hN, hmain⟩ := theorem_4_4_span hS p
  refine ⟨N, hN, ?_⟩
  intro Γ θ T d G hV hE hΓG hm hθ s r P hends hs hr hsr hfar hP hPP
  obtain ⟨η, hηG, hηv, _, hCtrl⟩ := exists_identity_embedding_induced_tangle Γ hV hE hΓG hm.1.2.1
  apply hmain G θ θ _ Γ η T d s r P hCtrl hm hθ hends hs hr hsr hfar
  · intro i
    have h := hP i
    simpa only [hηv, hηG] using h
  · exact hPP

end GraphMinor.GM12
