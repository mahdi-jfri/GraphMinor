module

public import GraphMinor.Surface.Defs
public import GraphMinor.Statement
import GraphMinor.GM12.Section4TargetReplacement
import GraphMinor.GM12.Section4FiniteLabels
import GraphMinor.GM12.Section4IsoIncidence
import GraphMinor.Minor.Basic

/-!
# A finite labelled drawable replacement of the target

The first reduction in XII (4.3), page 249, replaces the target
by a drawable loopless graph with at least two incident edges at
each vertex. Build that replacement, enumerate its vertices and
edges, and carry the drawing across the enumeration isomorphism.
The original graph remains a minor of the labelled replacement.
-/

public section

namespace GraphMinor.GM12

open Set Surface

/-- The complete target reduction in XII (4.3), page 249, with explicit bounds on the
labelled replacement's vertex and edge counts in terms of `G`. -/
theorem exists_normalized_target_replacement_bounded
    {α β S : Type*} [TopologicalSpace S] [T2Space S] [ConnectedSpace S]
    (hS : IsClosedSurface S) {G : Graph α β} (D : GraphDrawing G S) :
    ∃ (p t : ℕ) (L : Graph (Fin p) (Fin t)) (_D' : GraphDrawing L S),
      p ≤ 3 * G.vertexSet.ncard + G.edgeSet.ncard ∧
      t ≤ 4 * G.vertexSet.ncard + 4 * G.edgeSet.ncard ∧
      L.vertexSet = univ ∧ L.edgeSet = univ ∧ IsIsoMinor G L ∧
        (∀ e v, ¬ L.IsLink e v v) ∧
        ∀ v ∈ L.vertexSet, ∃ e f, e ≠ f ∧ L.Inc e v ∧ L.Inc f v := by
  obtain ⟨H, hminor, hHV, hHE, hloop, htwo⟩ :=
    exists_loopless_minimum_degree_two_minor_bounded hS D.drawing
  have hGminor : IsIsoMinor G H.toGraph := D.iso.isIsoMinor_left hminor
  obtain ⟨p, t, L, hLV, hLE, ⟨φ⟩⟩ := exists_finite_labels H.toGraph H.finite_V H.finite_edges
  have hp_eq : p = H.V.ncard := by
    have h1 : Nat.card L.vertexSet = Nat.card H.V := Nat.card_congr φ.vertexEquiv
    rw [hLV, Nat.card_coe_set_eq, Set.ncard_univ, Nat.card_fin] at h1
    rwa [Nat.card_coe_set_eq] at h1
  have ht_eq : t = H.E.ncard := by
    have h1 : Nat.card L.edgeSet = Nat.card H.E := Nat.card_congr φ.edgeEquiv
    rw [hLE, Nat.card_coe_set_eq, Set.ncard_univ, Nat.card_fin] at h1
    rwa [Nat.card_coe_set_eq] at h1
  have hDV_eq : D.drawing.V.ncard = G.vertexSet.ncard := by
    have h1 : Nat.card G.vertexSet = Nat.card D.drawing.V := Nat.card_congr D.iso.vertexEquiv
    rw [Nat.card_coe_set_eq, Nat.card_coe_set_eq] at h1
    exact h1.symm
  have hDE_eq : D.drawing.E.ncard = G.edgeSet.ncard := by
    have h1 : Nat.card G.edgeSet = Nat.card D.drawing.E := Nat.card_congr D.iso.edgeEquiv
    rw [Nat.card_coe_set_eq, Nat.card_coe_set_eq] at h1
    exact h1.symm
  exact ⟨p, t, L, ⟨H, φ⟩, by omega, by omega, hLV, hLE, Iso.isIsoMinor_right hGminor φ.symm,
    loopless_of_iso φ hloop, two_incident_edges_of_iso φ htwo⟩

/-- The complete target reduction in XII (4.3), page 249, when a
drawing of the original abstract graph is supplied. -/
theorem exists_normalized_target_replacement
    {α β S : Type*} [TopologicalSpace S] [T2Space S] [ConnectedSpace S]
    (hS : IsClosedSurface S) {G : Graph α β} (D : GraphDrawing G S) :
    ∃ (p t : ℕ) (L : Graph (Fin p) (Fin t)) (_D' : GraphDrawing L S),
      L.vertexSet = univ ∧ L.edgeSet = univ ∧ IsIsoMinor G L ∧
        (∀ e v, ¬ L.IsLink e v v) ∧
        ∀ v ∈ L.vertexSet, ∃ e f, e ≠ f ∧ L.Inc e v ∧ L.Inc f v := by
  obtain ⟨p, t, L, D', _, _, hLV, hLE, hmin, hloop, htwo⟩ :=
    exists_normalized_target_replacement_bounded hS D
  exact ⟨p, t, L, D', hLV, hLE, hmin, hloop, htwo⟩

end GraphMinor.GM12
