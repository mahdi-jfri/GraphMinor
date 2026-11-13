module

public import GraphMinor.GM05.ChordalDefs
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise

/-!
# Representatives in the induction for independent sets

In Graph Minors V, (8.5), choose one representative from each independent
set, using the simplicial vertex itself in its own set. In every other
set choose a neighbor of that vertex when possible. Simpliciality and
independence imply that these representatives include all its neighbors.
Deleting them removes exactly one vertex from each of the disjoint sets.
-/

public section

namespace GraphMinor.GM05

open SimpleGraph Set
open scoped BigOperators

variable {V I : Type*} {G : SimpleGraph V} {Z : I → Set V}

/-- Graph Minors V, proof of (8.5), page 110: the chosen representative is
the only point of its independent set that can be adjacent to the
simplicial vertex. Thus every neighbor is a representative. -/
theorem lemma_8_5_neighbours_are_representatives {v : V} (hv : IsSimplicial G v)
    (hZ : ∀ i, G.IsIndepSet (Z i))
    (hN : ∀ i, (Z i).Nonempty) {j : I} (hvj : v∈Z j)
    (hcover : ∀ u, G.Adj v u → ∃ i, u∈Z i) :
    ∃ z : I → V, (∀ i, z i∈Z i) ∧ z j=v ∧ ∀ u, G.Adj v u → u∈range z := by
  classical
  have hex (i : I) : ∃ u∈Z i, (i=j → u=v) ∧
      ((∃ w∈Z i, G.Adj v w) → G.Adj v u) := by
    by_cases hij : i=j
    · subst i
      refine ⟨v,hvj,fun _ ↦ rfl,?_⟩
      rintro ⟨w,hw,hvw⟩
      exact (hZ j hvj hw hvw.ne hvw).elim
    · by_cases hn : ∃ w∈Z i, G.Adj v w
      · obtain ⟨w,hw,hvw⟩ := hn
        exact ⟨w,hw,fun h ↦ (hij h).elim,fun _ ↦ hvw⟩
      · obtain ⟨w,hw⟩ := hN i
        exact ⟨w,hw,fun h ↦ (hij h).elim,fun h ↦ (hn h).elim⟩
  choose z hz hsame hadj using hex
  refine ⟨z,hz,hsame j rfl,?_⟩
  intro u hvu
  obtain ⟨i,hi⟩ := hcover u hvu
  have hvz : G.Adj v (z i) := hadj i ⟨u,hi,hvu⟩
  have he : z i=u := by
    by_contra hne
    exact hZ i (hz i) hi hne (hv hvz hvu hne)
  exact ⟨i,he⟩

/-- Representatives from disjoint sets have exactly one point in each
set. No finiteness assumption is needed for this identity. -/
theorem inter_range_representatives (hdisj : Pairwise (fun i j ↦ Disjoint (Z i) (Z j)))
    {z : I → V} (hz : ∀ i, z i∈Z i) (i : I) : Z i ∩ range z = {z i} := by
  ext x
  constructor
  · rintro ⟨hx,k,rfl⟩
    by_cases he : i=k
    · subst k; rfl
    · exact (Set.disjoint_left.mp (hdisj he) hx (hz k)).elim
  · rintro rfl
    exact ⟨hz i,⟨i,rfl⟩⟩

/-- Deleting all representatives is the same, on each independent set,
as deleting just its own representative. -/
theorem sdiff_range_representatives (hdisj : Pairwise (fun i j ↦ Disjoint (Z i) (Z j)))
    {z : I → V} (hz : ∀ i, z i∈Z i) (i : I) : Z i\range z = Z i\{z i} := by
  rw [←inter_range_representatives hdisj hz i]
  ext x
  constructor
  · rintro ⟨hx,hn⟩
    exact ⟨hx,fun h ↦ hn h.2⟩
  · rintro ⟨hx,hn⟩
    exact ⟨hx,fun h ↦ hn ⟨hx,h⟩⟩

/-- Each residual independent set has cardinality `k-1`, as in the
induction step of Graph Minors V, (8.5), pages 110–111. -/
theorem ncard_residual_representatives [Finite V]
    (hdisj : Pairwise (fun i j ↦ Disjoint (Z i) (Z j)))
    {z : I → V} (hz : ∀ i, z i∈Z i) {k : ℕ} (hcard : ∀ i, (Z i).ncard=k) (i : I) :
    (Z i\range z).ncard=k-1 := by
  rw [sdiff_range_representatives hdisj hz,ncard_sdiff_singleton_of_mem (hz i),hcard i]

/-- Decreasing one positive target decreases the total by one. -/
theorem sum_update_pred [Fintype I] [DecidableEq I] (x : I → ℕ) (j : I)
    (hj : 0<x j) : (∑ i, Function.update x j (x j-1) i) = (∑ i,x i)-1 := by
  have hsum := Finset.sum_update_of_mem (Finset.mem_univ j) x (x j-1)
  have hold := Finset.sum_erase_add (Finset.univ : Finset I) x (Finset.mem_univ j)
  rw [hsum,Finset.sdiff_singleton_eq_erase]
  omega

/-- Omitting a color with target zero leaves the total unchanged. -/
theorem sum_subtype_ne_of_zero [Fintype I] [DecidableEq I] (x : I → ℕ) (j : I)
    (hj : x j=0) : (∑ i : {i // i≠j},x i.1) = ∑ i,x i := by
  have hs := Finset.sum_subtype (F:=inferInstance) (Finset.univ.erase j)
    (show ∀ i : I, i∈Finset.univ.erase j ↔ i≠j by intro i; simp) x
  rw [←hs]
  have hsum := Finset.sum_erase_add (Finset.univ : Finset I) x (Finset.mem_univ j)
  simpa only [hj,Nat.add_zero] using hsum

end GraphMinor.GM05
