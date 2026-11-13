module

public import GraphMinor.GM01.Defs
import GraphMinor.GM01.GridDiagramCoordinates
import GraphMinor.GM01.RootedBranchModels
import GraphMinor.GM01.RootedModelMinor
import GraphMinor.Minor.Basic

/-!
# A smaller grid inside a larger grid

Graph Minors I, (3.5), page 52, uses the grid from (3.4) inside the
slightly larger grid defining the exclusion class. Include the
smaller square by keeping both coordinates. Its vertices give
singleton branches, so this inclusion is an ordinary minor model.
-/

public section

namespace GraphMinor.GM01

open Set Graph SimpleGraph

/-- Including the coordinates of a nonempty smaller grid gives a
minor of the larger grid, as used in GM01 (3.5), page 52. -/
theorem gridGraph_isIsoMinor_of_le {m n : ℕ} (hm : 0 < m) (hmn : m ≤ n) :
    IsIsoMinor (gridGraph m) (gridGraph n) := by
  let zero : Fin m := ⟨0, hm⟩
  let f : (Fin m × Fin m) ↪ (Fin n × Fin n) :=
    ⟨fun x ↦ (Fin.castLE hmn x.1, Fin.castLE hmn x.2), by
      intro x y h
      apply Prod.ext <;> apply Fin.ext
      · exact congrArg (fun z : Fin n × Fin n ↦ z.1.val) h
      · exact congrArg (fun z : Fin n × Fin n ↦ z.2.val) h⟩
  let G : RootedGraph (Fin n × Fin n) (Sym2 (Fin n × Fin n)) :=
    ⟨gridGraph n, ⟨f (zero, zero), mem_univ _⟩⟩
  let M := rootedModelOfBranchSets (pathGraph m □ pathGraph m) G
    (fun x ↦ {f x}) (fun _ ↦ singleton_subset_iff.mpr (mem_univ _))
    (fun _ _ hxy ↦ disjoint_singleton.mpr (fun h ↦ hxy (f.injective h)))
    (fun x ↦ by
      refine ⟨⟨f x, rfl⟩, ?_⟩
      intro u hu v hv
      have hu' : u = f x := hu
      have hv' : v = f x := hv
      subst u
      subst v
      exact .refl)
    (by
      intro x y hxy
      have h : (gridGraph n).Adj (f x) (f y) := by
        apply (gridGraph_adj_iff _ _).mpr
        rcases (gridGraph_adj_iff x y).mp ((Graph.ofSimpleGraph_adj_iff x y).mpr hxy) with h | h
        · exact Or.inl ⟨h.1, congrArg (Fin.castLE hmn) h.2⟩
        · exact Or.inr ⟨h.1, congrArg (Fin.castLE hmn) h.2⟩
      obtain ⟨e, he⟩ := h
      exact ⟨e, f x, rfl, f y, rfl, he⟩)
    (zero, zero) rfl
  let : Nonempty (Sym2 (Fin n × Fin n)) := ⟨s(f (zero, zero), f (zero, zero))⟩
  obtain ⟨v, e, he⟩ := M.exists_isMinorModel_of_simple (pathGraph m □ pathGraph m) (zero, zero) G
  exact isIsoMinor_of_isMinorModel (gridGraph m) (gridGraph n)
    (Set.toFinite _) (Set.toFinite _) (Set.toFinite _) (Set.toFinite _) v e he

end GraphMinor.GM01
