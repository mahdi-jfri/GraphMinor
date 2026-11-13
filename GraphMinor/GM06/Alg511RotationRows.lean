module

public import GraphMinor.GM06.Alg511RotationEnds
public import GraphMinor.GM06.Section5RotationRowEdgeLabels
import GraphMinor.GM11.LocalCone
import Mathlib.Data.List.FinRange
import Mathlib.Tactic

/-!
# Geometric coverage of finite vertex rotation rows

The drawing data for VI (5.11), page 134, use the vertex rotations
of (5.7). A row lists exactly the incident directed endpoint labels.
With at least two ends, its order is the angular order in a small
polar chart of the actual drawing. With at most one end the cyclic
order has no choice. All charts, parametrizations and directions
are interpretation witnesses, outside the supplied finite rows.
-/

@[expose] public section
namespace GraphMinor.GM06
open GraphMinor.Compute Set Topology GraphMinor.Surface GraphMinor.GM11 unitInterval
universe u

/-- Interpretation of an ordinary rotation row by the drawing's
actual directed ends and their cyclic order in a polar chart. -/
def Alg511RotationRowRep {S : Type u} [TopologicalSpace S]
    (x : GM06SuccessorInput) {G : Drawing S} (rep : GM06SuccessorGraphRep x G.toGraph)
    (γ : Set S → I → S) (v : Fin x.vertexCount) (xs : List ℕ) : Prop :=
  xs.Nodup ∧
  (∀ r, r ∈ xs ↔ r < x.endpoints.length ∧ x.endpoints.getD r 0 = v.val) ∧
  (xs.length ≤ 1 ∨ ∃ (Φ : C(ClosedUnitDisc, S)) (z : ℕ → Circle),
    IsPolar G (rep.vertex v).val Φ ∧ Set.InjOn z {r | r ∈ xs} ∧
    xs.Pairwise (fun a b => circleStdCoord.angle (z a) < circleStdCoord.angle (z b)) ∧
    (∀ a : halfEdges G γ (rep.vertex v).val, ∀ t : I, 0 < t →
      Φ (polarDiscPoint t (z (halfEdgeLabel rep.edge a))) ∈ range (spoke γ a.1)) ∧
    ∀ (j : Fin rep.pairs.length) (w : Circle),
      polarRimMap Φ w ∈ (rep.edge j).val ↔ ∃ r ∈ xs,
        z r = w ∧ (r = 2 * j.val ∨ r = 2 * j.val + 1))

/-- Every vertex of a labelled closed-surface drawing has a finite
rotation row with the exact endpoint incidence and geometric order. -/
theorem alg511_exists_rotation_row
    {S : Type u} [TopologicalSpace S] (hS : IsClosedSurface S)
    (x : GM06SuccessorInput) {G : Drawing S} (rep : GM06SuccessorGraphRep x G.toGraph)
    {γ : Set S → I → S} (hγ : EdgePar G γ)
    (hends : ∀ i : Fin rep.pairs.length,
      γ (rep.edge i).val 0 = (rep.vertex rep.pairs[i.val].1).val ∧
      γ (rep.edge i).val 1 = (rep.vertex rep.pairs[i.val].2).val)
    (v : Fin x.vertexCount) : ∃ xs : List ℕ, Alg511RotationRowRep x rep γ v xs := by
  classical
  let : T2Space S := hS.2.1
  by_cases htwo : 2 ≤ Nat.card (halfEdges G γ (rep.vertex v).val)
  · obtain ⟨Φ, hp⟩ := exists_isPolar_of_sectors hS hγ (rep.vertex v).property htwo
    obtain ⟨Ψ, hΨ, _, d, hd⟩ := exists_polar_chart_with_halfedge_equiv hS hγ
      (rep.vertex v).property hp isOpen_univ (mem_univ _)
    obtain ⟨xs, z, hnd, hmem, hz, hzi, hs, _⟩ :=
      exists_polar_rotation_row d (halfEdgeLabel rep.edge) (halfEdgeLabel_injective rep.edge)
    refine ⟨xs, hnd, ?_, Or.inr ⟨Ψ, z, hΨ, hzi, hs, ?_, ?_⟩⟩
    · intro r
      exact (hmem r).trans (alg511_halfEdgeLabel_exists_iff x rep hends v r)
    · intro a t ht
      rw [hz a]
      exact hd a t ht
    · exact polar_rotation_row_edge_labels hγ hΨ d hd rep.edge xs z hmem hz
  · let H := halfEdges G γ (rep.vertex v).val
    let : Fintype H := (finite_halfEdges G γ (rep.vertex v).val).fintype
    let e : Fin (Fintype.card H) ≃ H := (Fintype.equivFin H).symm
    let xs := List.ofFn (fun i => halfEdgeLabel rep.edge (e i))
    have hnd : xs.Nodup := List.nodup_ofFn_ofInjective
      ((halfEdgeLabel_injective rep.edge).comp e.injective)
    have hmem (r : ℕ) : r ∈ xs ↔ ∃ a : H, halfEdgeLabel rep.edge a = r := by
      rw [List.mem_ofFn]
      constructor
      · rintro ⟨i, hi⟩
        exact ⟨e i, hi⟩
      · rintro ⟨a, ha⟩
        obtain ⟨i, rfl⟩ := e.surjective a
        exact ⟨i, ha⟩
    refine ⟨xs, hnd, fun r => (hmem r).trans
      (alg511_halfEdgeLabel_exists_iff x rep hends v r), Or.inl ?_⟩
    have hcard : Nat.card H = Fintype.card H := Nat.card_eq_fintype_card
    change xs.length ≤ 1
    rw [show xs.length = Fintype.card H from List.length_ofFn]
    change ¬ 2 ≤ Nat.card H at htwo
    omega

/-- All vertex rotations can be supplied simultaneously as a plain
list of finite rows, with geometry occurring only in its interpretation. -/
theorem alg511_exists_rotation_rows
    {S : Type u} [TopologicalSpace S] [Nonempty S] (hS : IsClosedSurface S)
    (x : GM06SuccessorInput) {G : Drawing S} (rep : GM06SuccessorGraphRep x G.toGraph) :
    ∃ (γ : Set S → I → S) (rows : List (List ℕ)), EdgePar G γ ∧
      (∀ i : Fin rep.pairs.length,
        γ (rep.edge i).val 0 = (rep.vertex rep.pairs[i.val].1).val ∧
        γ (rep.edge i).val 1 = (rep.vertex rep.pairs[i.val].2).val) ∧
      rows.length = x.vertexCount ∧
      ∀ v : Fin x.vertexCount, Alg511RotationRowRep x rep γ v (rows.getD v.val []) := by
  classical
  let : T2Space S := hS.2.1
  obtain ⟨γ, hγ, hends⟩ := alg511_exists_edgePar_with_prescribed_ends x rep
  choose row hrow using fun v => alg511_exists_rotation_row hS x rep hγ hends v
  refine ⟨γ, List.ofFn row, hγ, hends, List.length_ofFn, ?_⟩
  intro v
  simpa [List.getD_eq_getElem?_getD, v.isLt] using hrow v

end GraphMinor.GM06
