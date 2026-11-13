module

public import GraphMinor.Compute.GM02InjectedPattern
import Mathlib.Data.List.Sort

/-!
# Host-order enumeration of injected pattern vertices

The labelled input of (4.6) lists its pattern vertices in increasing
order. A scan of host positions can produce that list directly: retain
exactly those host positions hit by the current injection. The list has
one entry for every pattern vertex, including isolated vertices.
-/

public section
namespace GraphMinor.Compute
open Classical

/-- Scan host positions in order, retaining the image of the injection. -/
@[expose] noncomputable def gm02InjectedVertexList (G H : GM02EdgeListInput)
    (f : Fin H.n ↪ Fin G.n) : List (Fin G.n) :=
  (List.finRange G.n).filter (fun v => ∃ i, f i = v)

/-- The host scan produces exactly the sorted vertex list required by the labelled encoding. -/
theorem gm02InjectedVertexList_eq_sort (G H : GM02EdgeListInput)
    (f : Fin H.n ↪ Fin G.n) :
    gm02InjectedVertexList G H f = (gm02InjectedPattern G H f).vertices.sort := by
  have hleft : (gm02InjectedVertexList G H f).Pairwise (· < ·) := by
    apply List.Pairwise.filter
    change (List.ofFn (fun i : Fin G.n => i)).Pairwise (· < ·)
    rw [List.pairwise_ofFn]
    intro i j hij
    exact hij
  have hright : ((gm02InjectedPattern G H f).vertices.sort).Pairwise (· < ·) :=
    (Finset.sortedLT_sort _).pairwise
  apply List.Pairwise.eq_of_mem_iff hleft hright
  intro v
  simp only [gm02InjectedVertexList, List.mem_filter, List.mem_finRange, true_and,
    Finset.mem_sort, gm02InjectedPattern, Finset.mem_image, Finset.mem_univ, true_and, decide_eq_true_eq]

/-- The host scan retains precisely the fixed number of pattern vertices. -/
theorem gm02InjectedVertexList_length (G H : GM02EdgeListInput)
    (f : Fin H.n ↪ Fin G.n) : (gm02InjectedVertexList G H f).length = H.n := by
  rw [gm02InjectedVertexList_eq_sort]
  change ((Finset.univ.image f).sort).length = H.n
  rw [Finset.length_sort, Finset.card_image_of_injective _ f.injective,
    Finset.card_univ, Fintype.card_fin]

end GraphMinor.Compute
