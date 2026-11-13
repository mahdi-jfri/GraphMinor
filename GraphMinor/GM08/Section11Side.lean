module

public import GraphMinor.GM08.Section11Topo

/-!
# The nodes and cells of a derived portrait

Facts about one side of Graph Minors VIII, (11.2): a drawing `Γ` in the disc `S` with a
foundation `F_1, …, F_t`. The nodes `N'` are the vertices not inside any `F_i`, and the edges of
`Γ_0` are the edges not inside any `F_i`.

* The rings are disjoint away from vertices: no point of `F_i` is inside `F_j` (`disjoint_ring_inside`).
* An edge not inside any `F_i` has its ends in `N'` (`ends_subset_nodes`).
* `Σ_i ∩ N' = V(Γ) ∩ F_i` (`ring_inter_nodes`).
-/

public section

namespace GraphMinor
namespace GM08

open Set Topology Surface

universe u

variable {S : Type u} [TopologicalSpace S]

/-- The nodes `N'` of a derived portrait: the vertices of `Γ` not inside any ring. -/
@[expose] def ringNodes (Γ : Drawing S) {t : ℕ} (F : Fin t → Set S) : Set S :=
  {v ∈ Γ.V | ∀ i : Fin t, ¬ InsideOArc univ (F i) v}

/-- The edges of `Γ_0`: the edges of `Γ` not inside any ring. -/
@[expose] def ringEdges (Γ : Drawing S) {t : ℕ} (F : Fin t → Set S) : Set (Set S) :=
  {e ∈ Γ.E | ∀ i : Fin t, ¬ SetInsideOArc univ (F i) e}

variable {Γ : Drawing S} {t : ℕ} {F : Fin t → Set S}

theorem IsFoundation.isOArc (hF : IsFoundation Γ univ F) (i : Fin t) : IsOArc (F i) := by
  obtain ⟨C, -, -, -, hmin, -⟩ := hF
  exact (hmin i).1.2.1

theorem IsFoundation.isNormal (hF : IsFoundation Γ univ F) (i : Fin t) : Γ.IsNormal (F i) := by
  obtain ⟨C, -, -, -, hmin, -⟩ := hF
  exact (hmin i).1.2.2.1

theorem IsFoundation.disjoint_inside (hF : IsFoundation Γ univ F) {i j : Fin t} (hij : i ≠ j) :
    Disjoint (insideSet (F i)) (insideSet (F j)) := by
  obtain ⟨C, -, -, -, -, hdisj, -⟩ := hF
  exact hdisj hij

/-- No point of `F_i` is inside `F_j`, for `i ≠ j`. -/
theorem IsFoundation.disjoint_ring_inside (hS : IsClosedDisc (univ : Set S))
    (hF : IsFoundation Γ univ F) {i j : Fin t} (hij : i ≠ j) :
    Disjoint (F i) (insideSet (F j)) := by
  obtain ⟨y, hy⟩ := insideSet_nonempty hS (hF.isOArc i)
  obtain ⟨C, -, -, -, -, hdisj, -⟩ := hF
  exact Set.disjoint_left.mpr fun x hx hxj => not_insideOArc_of_mem hS (hdisj hij) hy hx hxj

/-- A point of `F_i` is inside no ring. -/
theorem IsFoundation.not_inside_of_mem (hS : IsClosedDisc (univ : Set S))
    (hF : IsFoundation Γ univ F) {i : Fin t} {x : S} (hx : x ∈ F i) (j : Fin t) :
    x ∉ insideSet (F j) := by
  by_cases hij : i = j
  · subst hij
    exact not_mem_insideSet_of_mem hx
  · exact Set.disjoint_left.mp (hF.disjoint_ring_inside hS hij) hx

/-- `Σ_i ∩ N' = V(Γ) ∩ F_i`. -/
theorem IsFoundation.ring_inter_nodes (hS : IsClosedDisc (univ : Set S))
    (hF : IsFoundation Γ univ F) (i : Fin t) :
    (F i ∪ insideSet (F i)) ∩ ringNodes Γ F = Γ.V ∩ F i := by
  ext x
  constructor
  · rintro ⟨hx | hx, hxV, hxN⟩
    · exact ⟨hxV, hx⟩
    · exact absurd hx (hxN i)
  · rintro ⟨hxV, hx⟩
    exact ⟨Or.inl hx, hxV, fun j => hF.not_inside_of_mem hS hx j⟩

/-- An edge is inside a ring, or its closure misses the inside of every ring. -/
theorem IsFoundation.closure_disjoint_inside (hS : IsClosedDisc (univ : Set S))
    (hF : IsFoundation Γ univ F) {e : Set S} (he : e ∈ ringEdges Γ F) (i : Fin t) :
    Disjoint (closure e) (insideSet (F i)) := by
  rcases edge_inside_or_disjoint hS (hF.isOArc i) (hF.isNormal i) he.1 with h | h
  · exact absurd h (he.2 i)
  · exact closure_disjoint_insideSet hS (hF.isOArc i) h

/-- The ends of an edge of `Γ_0` are nodes. -/
theorem IsFoundation.ends_subset_nodes (hS : IsClosedDisc (univ : Set S))
    (hF : IsFoundation Γ univ F) {e : Set S} (he : e ∈ ringEdges Γ F) :
    closure e ∩ Γ.V ⊆ ringNodes Γ F := fun x hx =>
  ⟨hx.2, fun i hxi => Set.disjoint_left.mp (hF.closure_disjoint_inside hS he i) hx.1 hxi⟩

/-- Every edge of `Γ` is an edge of `Γ_0` or inside a ring. -/
theorem mem_ringEdges_or_inside {e : Set S} (he : e ∈ Γ.E) :
    e ∈ ringEdges Γ F ∨ ∃ i, e ⊆ insideSet (F i) := by
  by_cases h : ∀ i : Fin t, ¬ SetInsideOArc univ (F i) e
  · exact Or.inl ⟨he, h⟩
  · push Not at h
    obtain ⟨i, hi⟩ := h
    exact Or.inr ⟨i, hi⟩

/-- An edge is inside at most one ring. -/
theorem IsFoundation.eq_of_inside (hF : IsFoundation Γ univ F) {e : Set S} (he : e ∈ Γ.E)
    {i j : Fin t} (hi : e ⊆ insideSet (F i)) (hj : e ⊆ insideSet (F j)) : i = j := by
  by_contra hij
  obtain ⟨x, hx⟩ := he.1
  exact Set.disjoint_left.mp (hF.disjoint_inside hij) (hi hx) (hj hx)

/-- A vertex is a node or inside exactly one ring. -/
theorem mem_ringNodes_or_inside {v : S} (hv : v ∈ Γ.V) :
    v ∈ ringNodes Γ F ∨ ∃ i, v ∈ insideSet (F i) := by
  by_cases h : ∀ i : Fin t, ¬ InsideOArc univ (F i) v
  · exact Or.inl ⟨hv, h⟩
  · push Not at h
    obtain ⟨i, hi⟩ := h
    exact Or.inr ⟨i, hi⟩

/-- Two components of a set are equal or disjoint. -/
theorem eq_or_disjoint_of_mem_componentsIn {T A B : Set S} (hA : A ∈ componentsIn T)
    (hB : B ∈ componentsIn T) : A = B ∨ Disjoint A B := by
  obtain ⟨x, -, rfl⟩ := hA
  obtain ⟨y, -, rfl⟩ := hB
  by_cases h : Disjoint (connectedComponentIn T x) (connectedComponentIn T y)
  · exact Or.inr h
  · left
    obtain ⟨z, hzx, hzy⟩ := Set.not_disjoint_iff.mp h
    rw [connectedComponentIn_eq hzx, connectedComponentIn_eq hzy]

end GM08
end GraphMinor
