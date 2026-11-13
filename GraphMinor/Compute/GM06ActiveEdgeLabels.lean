module

public import Mathlib.Data.List.FinRange
public import Mathlib.Data.Set.Function
public import Mathlib.Logic.Equiv.Defs
import Mathlib.Data.List.NodupEquivFin
import Mathlib.Data.List.OfFn

/-!
# Enumerating the remaining original edge labels

The masks in VI (5.7), page 133, keep original labels after
edge deletion. Filter the finite index list by its activity bit.
Distinct active labels and edge coverage give a bijection from
the filtered positions to the actual remaining edges. This lets
ordinary endpoint-count proofs apply to a masked drawing too.
-/

@[expose] public section
namespace GraphMinor.Compute
open Set
universe u v

/-- Original edge indices whose current activity word is one. -/
def gm06ActiveEdgeIndices {α : Type u} (tagged : List (α × ℕ)) : List (Fin tagged.length) :=
  (List.finRange tagged.length).filter fun j => tagged[j.val].2 == 1

/-- The filtered index list contains exactly the active original labels. -/
theorem gm06ActiveEdgeIndices_mem_iff {α : Type u} (tagged : List (α × ℕ))
    (j : Fin tagged.length) : j ∈ gm06ActiveEdgeIndices tagged ↔ tagged[j.val].2 = 1 := by
  simp [gm06ActiveEdgeIndices]

/-- Every original edge index occurs at most once in the active list. -/
theorem gm06ActiveEdgeIndices_nodup {α : Type u} (tagged : List (α × ℕ)) :
    (gm06ActiveEdgeIndices tagged).Nodup :=
  (List.nodup_finRange tagged.length).filter _

/-- Reading the retained original indices returns exactly the
activity-filtered input rows, in their original order. -/
theorem gm06ActiveEdgeIndices_map_get {α : Type u} (tagged : List (α × ℕ)) :
    (gm06ActiveEdgeIndices tagged).map (fun j => tagged[j.val]) =
      tagged.filter (fun p => p.2 == 1) := by
  have hmap : (List.finRange tagged.length).map (fun j => tagged[j.val]) = tagged := by
    rw [← List.ofFn_eq_map, List.ofFn_getElem]
  calc
    _ = ((List.finRange tagged.length).map (fun j => tagged[j.val])).filter
        (fun p => p.2 == 1) := (List.filter_map (f := fun j : Fin tagged.length => tagged[j.val])
          (p := fun p => p.2 == 1) (l := List.finRange tagged.length)).symm
    _ = _ := congrArg (List.filter (fun p => p.2 == 1)) hmap

/-- The filtered positions label the actual remaining edge set,
using only active-label injectivity, incidence and edge coverage. -/
theorem exists_active_edge_position_equiv {α : Type u} {β : Type v}
    (tagged : List (α × ℕ)) (edge : Fin tagged.length → β) (E : Set β)
    (hinj : Set.InjOn edge {j | tagged[j.val].2 = 1})
    (hmem : ∀ j : Fin tagged.length, tagged[j.val].2 = 1 → edge j ∈ E)
    (hcover : ∀ e ∈ E, ∃ j : Fin tagged.length, tagged[j.val].2 = 1 ∧ edge j = e) :
    ∃ e : Fin (gm06ActiveEdgeIndices tagged).length ≃ E,
      ∀ i, (e i).val = edge ((gm06ActiveEdgeIndices tagged)[i.val]) := by
  classical
  let labels := gm06ActiveEdgeIndices tagged
  let f : {j : Fin tagged.length // j ∈ labels} → E := fun j =>
    ⟨edge j.val, hmem j.val ((gm06ActiveEdgeIndices_mem_iff tagged j.val).mp j.property)⟩
  have hf : Function.Bijective f := by
    constructor
    · intro a b hab
      apply Subtype.ext
      apply hinj ((gm06ActiveEdgeIndices_mem_iff tagged a.val).mp a.property)
        ((gm06ActiveEdgeIndices_mem_iff tagged b.val).mp b.property)
      exact congrArg Subtype.val hab
    · intro e
      obtain ⟨j, hj, hje⟩ := hcover e.val e.property
      refine ⟨⟨j, (gm06ActiveEdgeIndices_mem_iff tagged j).mpr hj⟩, ?_⟩
      exact Subtype.ext hje
  let e := ((gm06ActiveEdgeIndices_nodup tagged).getEquiv labels).trans (Equiv.ofBijective f hf)
  exact ⟨e, fun _ => rfl⟩

end GraphMinor.Compute
