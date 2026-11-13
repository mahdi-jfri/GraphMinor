module

public import GraphMinor.GM01.PathCombTrees

/-!
# Degree bound for the rooted path configurations

In the proof of Graph Minors I, (1.1), the positive-height argument on
page 55 passes from a minor model of `P(γ,δ)` to a subdivision because
all its vertices have degree at most three. A spine vertex has at most
two spine neighbours and one attached root. A vertex in a binary copy
has at most its parent and its two children. We prove the bound from
these explicit lists of possible neighbours.
-/

public section

namespace GraphMinor.GM01

open SimpleGraph

/-- A set contained in three specified candidates has at most three elements. -/
theorem ncard_le_three_of_subset {V : Type*} {S : Set V} {a b c : V}
    (h : S ⊆ {a, b, c}) : S.ncard ≤ 3 := by
  calc
    S.ncard ≤ ({a, b, c} : Set V).ncard :=
      Set.ncard_le_ncard h (((Set.finite_singleton c).insert b).insert a)
    _ ≤ ({b, c} : Set V).ncard + 1 := Set.ncard_insert_le a _
    _ ≤ (({c} : Set V).ncard + 1) + 1 :=
      Nat.add_le_add_right (Set.ncard_insert_le b _) 1
    _ = 3 := by rw [Set.ncard_singleton]

/-- The ambient neighbour set of each `P(γ,δ)` vertex has at most three
members, as used on page 55 of the rooted proof. -/
theorem pathComb_neighborSet_ncard_le_three (γ δ : ℕ) (v : PathCombVertex δ) :
    ((pathComb γ δ).neighborSet v).ncard ≤ 3 := by
  classical
  cases v with
  | inl i =>
    let prev : Fin δ := ⟨i.val - 1, (Nat.sub_le _ _).trans_lt i.isLt⟩
    let next : Fin δ := if h : i.val + 1 < δ then ⟨i.val + 1, h⟩ else i
    apply ncard_le_three_of_subset
      (a := Sum.inl prev) (b := Sum.inl next) (c := Sum.inr (i, []))
    intro w hw
    cases w with
    | inl j =>
      rcases pathGraph_adj.mp hw with hij | hji
      · have hnext : i.val + 1 < δ := by have := j.isLt; omega
        have hj : j = next := Fin.ext (by
          simp only [next, hnext, ↓reduceDIte]
          exact hij.symm)
        exact Or.inr (Or.inl (congrArg Sum.inl hj))
      · have hj : j = prev := Fin.ext (by change j.val = i.val - 1; omega)
        exact Or.inl (congrArg Sum.inl hj)
    | inr p =>
      rcases p with ⟨j, word⟩
      rcases hw with ⟨rfl, rfl, hγ⟩
      exact Or.inr (Or.inr rfl)
  | inr p =>
    rcases p with ⟨i, word⟩
    apply ncard_le_three_of_subset (a := pathCombParent (Sum.inr (i, word)))
      (b := Sum.inr (i, false :: word)) (c := Sum.inr (i, true :: word))
    intro w hw
    cases w with
    | inl j =>
      rcases hw with ⟨rfl, rfl, hγ⟩
      exact Or.inl rfl
    | inr q =>
      rcases q with ⟨j, word'⟩
      rcases hw with ⟨rfl, hv, hw, hedge⟩
      rcases hedge with ⟨bit, rfl⟩ | ⟨bit, rfl⟩
      · cases bit
        · exact Or.inr (Or.inl rfl)
        · exact Or.inr (Or.inr rfl)
      · exact Or.inl rfl

/-- The same degree bound on the actual vertex type of `P(γ,δ)`.
The subtype inclusion is the bijection between its two neighbour sets. -/
theorem pathComb_coe_neighborSet_ncard_le_three (γ δ : ℕ) (v : (pathComb γ δ).verts) :
    ((pathComb γ δ).coe.neighborSet v).ncard ≤ 3 := by
  have hsubset : (pathComb γ δ).neighborSet v.val ⊆
      Set.range (Subtype.val : (pathComb γ δ).verts → PathCombVertex δ) := by
    intro w hw
    have ha : (pathComb γ δ).Adj v.val w := hw
    exact ⟨⟨w, ha.snd_mem⟩, rfl⟩
  change (Subtype.val ⁻¹' (pathComb γ δ).neighborSet v.val).ncard ≤ 3
  rw [Set.ncard_preimage_of_injective_subset_range Subtype.val_injective hsubset]
  exact pathComb_neighborSet_ncard_le_three γ δ v.val

/-- The distinguished first spine vertex has at most two neighbours. This
leaves room for the path to the target root in the rooted subdivision
construction. -/
theorem pathComb_root_neighborSet_ncard_le_two (γ δ : ℕ) (hδ : 0 < δ) :
    ((pathComb γ δ).neighborSet (Sum.inl ⟨0, hδ⟩)).ncard ≤ 2 := by
  classical
  let first : Fin δ := ⟨0, hδ⟩
  let next : Fin δ := if h : 1 < δ then ⟨1, h⟩ else first
  have hsub : (pathComb γ δ).neighborSet (Sum.inl first) ⊆
      {Sum.inl next, Sum.inr (first, [])} := by
    intro v hv
    cases v with
    | inl i =>
      rcases pathGraph_adj.mp hv with hforward | hback
      · have hi : i.val = 1 := hforward.symm
        have hnext : 1 < δ := hi ▸ i.isLt
        have hieq : i = next := Fin.ext (by
          simp only [next, hnext, ↓reduceDIte]
          exact hi)
        exact Or.inl (congrArg Sum.inl hieq)
      · have hi : i.val + 1 = 0 := hback
        omega
    | inr p =>
      rcases p with ⟨i, word⟩
      rcases hv with ⟨rfl, rfl, hγ⟩
      exact Or.inr rfl
  calc
    _ ≤ ({Sum.inl next, Sum.inr (first, [])} : Set (PathCombVertex δ)).ncard :=
      Set.ncard_le_ncard hsub ((Set.finite_singleton _).insert _)
    _ ≤ ({Sum.inr (first, [])} : Set (PathCombVertex δ)).ncard + 1 := Set.ncard_insert_le _ _
    _ = 2 := by rw [Set.ncard_singleton]

/-- The root degree bound on the actual vertex type of the rooted comb. -/
theorem pathComb_root_coe_neighborSet_ncard_le_two (γ δ : ℕ) (hδ : 0 < δ) :
    ((pathComb γ δ).coe.neighborSet (rootedPathComb γ δ hδ).root).ncard ≤ 2 := by
  let root := (rootedPathComb γ δ hδ).root
  have hsub : (pathComb γ δ).neighborSet root.val ⊆
      Set.range (Subtype.val : (pathComb γ δ).verts → PathCombVertex δ) := by
    intro w hw
    have ha : (pathComb γ δ).Adj root.val w := hw
    exact ⟨⟨w, ha.snd_mem⟩, rfl⟩
  change (Subtype.val ⁻¹' (pathComb γ δ).neighborSet root.val).ncard ≤ 2
  rw [Set.ncard_preimage_of_injective_subset_range Subtype.val_injective hsub]
  exact pathComb_root_neighborSet_ncard_le_two γ δ hδ

/-- A comb with at least two spine vertices has a neighbour at its root,
namely the second spine vertex. -/
theorem pathComb_root_coe_neighborSet_nonempty (γ δ : ℕ) (hδ : 2 ≤ δ) :
    ((pathComb γ δ).coe.neighborSet (rootedPathComb γ δ (by omega)).root).Nonempty := by
  let next : (pathComb γ δ).verts := ⟨Sum.inl ⟨1, by omega⟩, pathComb_spine_mem γ δ _⟩
  refine ⟨next, ?_⟩
  exact pathComb_spine_adj (γ := γ) (pathGraph_adj.mpr (Or.inl rfl))

end GraphMinor.GM01
