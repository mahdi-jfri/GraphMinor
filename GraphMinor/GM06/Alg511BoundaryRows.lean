module

public import GraphMinor.GM06.Alg511BoundaryDarts
public import GraphMinor.GM06.Alg511RegionBoundaryWalks
import Mathlib.Data.List.FinRange
import Mathlib.Tactic

/-!
# Ordered region-boundary rows with explicit region labels

The drawing data of VI (5.11), page 134, allow several boundary
components in one region. Enumerate the incident drawing components
and retain their geometrically traced closed walks. Encode each walk
by its directed edge labels and put the region label first. An
isolated vertex has an empty walk and contributes just its region
label. The region and component bijections interpret the rows and
keep every actual boundary component in the supplied finite data.
-/

public section
namespace GraphMinor.GM06
open Set Topology GraphMinor.Surface GraphMinor.GM11 unitInterval
universe u

/-- List every boundary component in region order, retaining the
region label as the first word of each row. -/
@[expose] def alg511BoundaryRows {r : ℕ} {count : Fin r → ℕ}
    (darts : ∀ i, Fin (count i) → List ℕ) : List (List ℕ) :=
  (List.finRange r).flatMap fun i => List.ofFn fun j => i.val :: darts i j

/-- A supplied boundary row follows the actual region-side collar
in its stated direction. Empty walks record isolated vertices. -/
@[expose] def Alg511RegionBoundaryRowRep
    {S : Type u} [TopologicalSpace S] {G : Drawing S} {m : ℕ}
    (edge : Fin m ≃ G.E) (γ : Set S → I → S) (r : Set S)
    (C : Graph S (Set S)) {v : S} (W : GraphWalk G.toGraph v v) (ds : List ℕ) : Prop :=
  (W.length = 0 ∧ ds = []) ∨ ∃ (h : C(Circle × I, S)) (ε : I),
    0 < ε ∧ InjOn h {p | 0 < p.2} ∧
    (∀ z t, 0 < t → t ≤ ε → h (z, t) ∈ r) ∧
    range (fun z : Circle => h (z, 0)) = frontier r ∩ compPointSet C ∧
    Alg511BoundaryDartsRep edge γ (collarCurve h) 0 1 W ds

/-- Interpretation of the finite boundary rows by the actual
region and component labels, closed walks and region-side collars.
No linkage or feasibility information occurs in this relation. -/
@[expose] def Alg511RegionRowsRep
    {S : Type u} [TopologicalSpace S] [T2Space S] (G : Drawing S) {m r : ℕ}
    (edge : Fin m ≃ G.E) (γ : Set S → I → S) (region : Fin r → G.R)
    (rows : List (List ℕ)) : Prop :=
  ∃ (count : Fin r → ℕ)
    (component : ∀ i, Fin (count i) ≃ {C : Graph S (Set S) |
      IsGraphComponent C G.toGraph ∧ (compPointSet C ∩ closure (region i).val).Nonempty})
    (start : ∀ i, Fin (count i) → S)
    (W : ∀ i j, GraphWalk G.toGraph (start i j) (start i j))
    (darts : ∀ i, Fin (count i) → List ℕ),
    rows = alg511BoundaryRows darts ∧
    ∀ i j, (walkDrawing G (W i j)).U = frontier (region i).val ∩ compPointSet (component i j).val ∧
      Alg511RegionBoundaryRowRep edge γ (region i).val (component i j).val (W i j) (darts i j)

private theorem exists_region_boundary_row
    {S : Type u} [TopologicalSpace S] [T2Space S] {G : Drawing S} {m : ℕ}
    (edge : Fin m ≃ G.E) {γ : Set S → I → S} (hγ : EdgePar G γ)
    {r : Set S} {C : Graph S (Set S)} {v : S} (W : GraphWalk G.toGraph v v)
    (htrace : Alg511RegionBoundaryTrace G r C W) :
    ∃ ds : List ℕ, Alg511RegionBoundaryRowRep edge γ r C W ds ∧
      ds.length = W.edges.length ∧ ∀ d ∈ ds, d < 2 * m := by
  rcases htrace with hzero | ⟨h, ε, hε, hinj, hpos, hbot, hrun⟩
  · refine ⟨[], Or.inl ⟨hzero, rfl⟩, ?_, by simp⟩
    cases W with
    | nil _ => rfl
    | cons _ _ => simp [GraphWalk.length] at hzero
  · have hc : Continuous (collarCurve h) := by
      exact h.continuous.comp ((Circle.exp.continuous.comp
        (continuous_const.mul continuous_id)).prodMk continuous_const)
    obtain ⟨ds, hds, hlen, hbound, _⟩ := alg511_exists_boundary_darts edge hγ hc W hrun
    exact ⟨ds, Or.inr ⟨h, ε, hε, hinj, hpos, hbot, hds⟩, hlen, hbound⟩

/-- Every finite family of actual sphere regions has supplied
boundary rows, in region order, with each directed label in range. -/
theorem alg511_exists_region_rows
    {S : Type u} [TopologicalSpace S] [T2Space S] [ConnectedSpace S]
    (hS : IsClosedSurface S) (hsph : IsSphere S) (G : Drawing S) {m r : ℕ}
    (edge : Fin m ≃ G.E) {γ : Set S → I → S} (hγ : EdgePar G γ)
    (region : Fin r → G.R) :
    ∃ rows : List (List ℕ), Alg511RegionRowsRep G edge γ region rows ∧
      ∀ row ∈ rows, ∃ i : Fin r, ∃ ds : List ℕ,
        row = i.val :: ds ∧ ∀ d ∈ ds, d < 2 * m := by
  classical
  choose count component start W hW hcover hdis using
    fun i => alg511_exists_region_boundary_traces hS hsph G (region i).property
  choose darts hdarts hlen hbound using fun i j =>
    exists_region_boundary_row edge hγ (W i j) (hW i j).2
  refine ⟨alg511BoundaryRows darts, ?_, ?_⟩
  · exact ⟨count, component, start, W, darts, rfl, fun i j => ⟨(hW i j).1, hdarts i j⟩⟩
  · intro row hrow
    obtain ⟨i, _, hi⟩ := List.mem_flatMap.mp hrow
    obtain ⟨j, hji⟩ := List.mem_ofFn.mp hi
    exact ⟨i, darts i j, hji.symm, hbound i j⟩

/-- The component bijections and exact walk point sets in the input
relation imply that each represented family covers precisely its
region frontier and has pairwise disjoint point sets. -/
theorem Alg511RegionRowsRep.frontier_covered
    {S : Type u} [TopologicalSpace S] [T2Space S] [LocallyConnectedSpace S]
    {G : Drawing S} {m r : ℕ} {edge : Fin m ≃ G.E}
    {γ : Set S → I → S} {region : Fin r → G.R} {rows : List (List ℕ)}
    (h : Alg511RegionRowsRep G edge γ region rows) :
    ∃ (count : Fin r → ℕ)
      (component : ∀ i, Fin (count i) ≃ {C : Graph S (Set S) |
        IsGraphComponent C G.toGraph ∧ (compPointSet C ∩ closure (region i).val).Nonempty})
      (start : ∀ i, Fin (count i) → S)
      (W : ∀ i j, GraphWalk G.toGraph (start i j) (start i j))
      (darts : ∀ i, Fin (count i) → List ℕ),
      rows = alg511BoundaryRows darts ∧
      (∀ i j, Alg511RegionBoundaryRowRep edge γ (region i).val (component i j).val
        (W i j) (darts i j)) ∧
      (∀ i, (⋃ j, (walkDrawing G (W i j)).U) = frontier (region i).val) ∧
      ∀ i, Pairwise (fun j l => Disjoint (walkDrawing G (W i j)).U (walkDrawing G (W i l)).U) := by
  obtain ⟨count, component, start, W, darts, hrows, hW⟩ := h
  refine ⟨count, component, start, W, darts, hrows, fun i j => (hW i j).2, ?_, ?_⟩
  · intro i
    ext p
    constructor
    · intro hp
      obtain ⟨j, hpj⟩ := mem_iUnion.mp hp
      rw [(hW i j).1] at hpj
      exact hpj.1
    · intro hp
      have hpnr : p ∉ (region i).val := by
        simpa only [(region_isOpen (region i).property).interior_eq] using hp.2
      have hpU : p ∈ G.U := (closure_region_subset (region i).property hp.1).resolve_left hpnr
      rw [← biUnion_compPointSet_eq_U G] at hpU
      obtain ⟨C, hC, hpC⟩ := mem_iUnion₂.mp hpU
      let c : {C : Graph S (Set S) | IsGraphComponent C G.toGraph ∧
          (compPointSet C ∩ closure (region i).val).Nonempty} := ⟨C, hC, p, hpC, hp.1⟩
      obtain ⟨j, hj⟩ := (component i).surjective c
      refine mem_iUnion.mpr ⟨j, ?_⟩
      rw [(hW i j).1]
      refine ⟨hp, ?_⟩
      have heq : (component i j).val = C := congrArg Subtype.val hj
      rw [heq]
      exact hpC
  · intro i j l hjl
    rw [(hW i j).1, (hW i l).1]
    have hne : (component i j).val ≠ (component i l).val :=
      fun heq => hjl ((component i).injective (Subtype.ext heq))
    exact (disjoint_compPointSet_of_ne G (component i j).property.1
      (component i l).property.1 hne).mono inter_subset_right inter_subset_right

end GraphMinor.GM06
