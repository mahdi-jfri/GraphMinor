module

public import GraphMinor.GM06.Alg34Cells

/-!
# Computing complement components from a finite cell cover

A finite family of connected cells determines the connected components
of its union. Join two cells when one meets the other's closure. Chains
give connected subsets by the preceding cell lemma. Conversely, a
connected subset cannot meet two chain classes: the closures of their
finite unions would separate that subset. This gives the region update
criterion for vertex deletion in (3.3)(i).
-/

public section
namespace GraphMinor.GM06

open Set Relation

universe u v

/-- A preconnected subset of a finite cell union can only meet cells
joined by a finite chain of closure incidences. -/
theorem alg34_cell_reachable_of_isPreconnected {S : Type u} [TopologicalSpace S]
    {ι : Type v} (A : ι → Set S) (K : Set ι) (hK : K.Finite)
    {C : Set S} (hC : IsPreconnected C) (hsub : C ⊆ ⋃ a ∈ K, A a)
    {i j : ι} (hi : i ∈ K) (hj : j ∈ K) {x y : S}
    (hxC : x ∈ C) (hxA : x ∈ A i) (hyC : y ∈ C) (hyA : y ∈ A j) :
    ReflTransGen (fun a b => a ∈ K ∧ b ∈ K ∧ alg34CellTouch A a b) i j := by
  classical
  let R := fun a b => a ∈ K ∧ b ∈ K ∧ alg34CellTouch A a b
  let L := {a ∈ K | ReflTransGen R i a}
  let M := {a ∈ K | ¬ ReflTransGen R i a}
  let F := ⋃ a ∈ L, closure (A a)
  let H := ⋃ a ∈ M, closure (A a)
  by_contra hnot
  have hF : IsClosed F := (hK.subset (fun _ h => h.1)).isClosed_biUnion
    (fun _ _ => isClosed_closure)
  have hH : IsClosed H := (hK.subset (fun _ h => h.1)).isClosed_biUnion
    (fun _ _ => isClosed_closure)
  have hcover : C ⊆ F ∪ H := by
    intro z hz
    obtain ⟨a, haK, hza⟩ := mem_iUnion₂.mp (hsub hz)
    by_cases ha : ReflTransGen R i a
    · exact Or.inl (mem_iUnion₂.mpr ⟨a, ⟨haK, ha⟩, subset_closure hza⟩)
    · exact Or.inr (mem_iUnion₂.mpr ⟨a, ⟨haK, ha⟩, subset_closure hza⟩)
  have hxF : x ∈ F := mem_iUnion₂.mpr ⟨i, ⟨hi, ReflTransGen.refl⟩, subset_closure hxA⟩
  have hyH : y ∈ H := mem_iUnion₂.mpr ⟨j, ⟨hj, hnot⟩, subset_closure hyA⟩
  obtain ⟨z, hzC, hzF, hzH⟩ := isPreconnected_closed_iff.mp hC F H hF hH hcover
    ⟨x, hxC, hxF⟩ ⟨y, hyC, hyH⟩
  obtain ⟨a, ha, hza⟩ := mem_iUnion₂.mp hzF
  obtain ⟨b, hb, hzb⟩ := mem_iUnion₂.mp hzH
  obtain ⟨k, hk, hzk⟩ := mem_iUnion₂.mp (hsub hzC)
  have hik : ReflTransGen R i k := ha.2.tail ⟨ha.1, hk, Or.inr ⟨z, hzk, hza⟩⟩
  have hib : ReflTransGen R i b := hik.tail ⟨hk, hb.1, Or.inl ⟨z, hzk, hzb⟩⟩
  exact hb.2 hib

/-- Connected-component membership in a finite union of connected cells
is exactly finite reachability in the cell-incidence graph. -/
theorem alg34_cell_component_iff {S : Type u} [TopologicalSpace S]
    {ι : Type v} (A : ι → Set S) (K : Set ι) (hK : K.Finite)
    (hA : ∀ a ∈ K, IsConnected (A a)) {i j : ι} (hi : i ∈ K) (hj : j ∈ K)
    {x y : S} (hx : x ∈ A i) (hy : y ∈ A j) :
    y ∈ connectedComponentIn (⋃ a ∈ K, A a) x ↔
      ReflTransGen (fun a b => a ∈ K ∧ b ∈ K ∧ alg34CellTouch A a b) i j := by
  constructor
  · intro hcomp
    exact alg34_cell_reachable_of_isPreconnected A K hK isPreconnected_connectedComponentIn
      (connectedComponentIn_subset _ _) hi hj
      (mem_connectedComponentIn (mem_iUnion₂.mpr ⟨i, hi, hx⟩)) hx hcomp hy
  · intro hpath
    obtain ⟨U, hU, hsub, hiU, hjU⟩ := alg34_cell_chain_connected A K hA hi hj hpath
    exact hU.2.subset_connectedComponentIn (hiU hx) hsub (hjU hy)

end GraphMinor.GM06
