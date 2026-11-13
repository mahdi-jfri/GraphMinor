module

public import GraphMinor.GM08.Defs6to18
import GraphMinor.GM07.Section9Cylinder
import GraphMinor.Surface.DiscGrow

/-!
# The painting made from the foundation and thickened edges

The closed discs meet only at nodes, and nodes on a disc lie on its
boundary. Removing the nodes leaves a connected dense subset of each
disc. These subsets are exactly the components of the union minus the
nodes: a component meeting two discs would cross their node intersection.
This verifies the painting assertion in the derived portrait construction
on VIII, page 272, used in Section 12.
-/

public section

namespace GraphMinor.GM08

open Set Surface

universe u v

private theorem disc_sdiff_nodes {S : Type u} [TopologicalSpace S] [T2Space S]
    {B N : Set S} (hB : IsClosedDisc B) (hN : B ∩ N ⊆ discBd B) :
    IsPreconnected (B \ N) ∧ (B \ N).Nonempty ∧ closure (B \ N) = B := by
  have hint : discInt B ⊆ B \ N := fun x hx =>
    ⟨hx.1, fun hxN => hx.2 (hN ⟨hx.1, hxN⟩)⟩
  refine ⟨hB.isPreconnected_discInt.subset_closure hint
    (sdiff_subset.trans hB.subset_closure_discInt), hB.nonempty_discInt.mono hint, ?_⟩
  exact Subset.antisymm (closure_minimal sdiff_subset hB.isClosed)
    (hB.subset_closure_discInt.trans (closure_mono hint))

/-- Distinct closed discs meeting only at boundary nodes give distinct
cells. This makes the cell labels in VIII, Section 12 unambiguous. -/
theorem injective_disc_cells {S : Type u} [TopologicalSpace S] [T2Space S]
    {ι : Type v} {N : Set S} {B : ι → Set S}
    (hB : ∀ i, IsClosedDisc (B i))
    (hBN : ∀ i, B i ∩ N ⊆ discBd (B i))
    (hBB : ∀ i j, i ≠ j → B i ∩ B j ⊆ N) :
    Function.Injective (fun i => B i \ N) := by
  intro i j hij
  by_contra hne
  obtain ⟨x, hx⟩ := (disc_sdiff_nodes (hB i) (hBN i)).2.1
  change B i \ N = B j \ N at hij
  have hxj : x ∈ B j \ N := by rw [← hij]; exact hx
  exact hx.2 (hBB i j hne ⟨hx.1, hxj.1⟩)

/-- Closed discs meeting only at boundary nodes form the painting
used for the derived portrait on VIII, page 272. Its cells are exactly
the discs with their nodes removed. -/
theorem exists_painting_of_discs {S : Type u} [TopologicalSpace S] [T2Space S]
    {ι : Type v} [Finite ι] (N : Set S) (hN : N.Finite) (B : ι → Set S)
    (hB : ∀ i, IsClosedDisc (B i))
    (hBN : ∀ i, B i ∩ N ⊆ discBd (B i))
    (hBB : ∀ i j, i ≠ j → B i ∩ B j ⊆ N)
    (hbd : ∀ i, B i ∩ bd S ⊆ N) :
    ∃ P : PaintingInDisc S, P.N = N ∧ P.U = N ∪ ⋃ i, B i ∧
      P.cells = range (fun i => B i \ N) ∧ ∀ i, closure (B i \ N) = B i := by
  classical
  let U := N ∪ ⋃ i, B i
  have hcell := fun i => disc_sdiff_nodes (hB i) (hBN i)
  have hcellSub : ∀ i, B i \ N ⊆ U \ N := fun i x hx =>
    ⟨.inr (mem_iUnion.mpr ⟨i, hx.1⟩), hx.2⟩
  have hcomp : ∀ i x, x ∈ B i \ N → connectedComponentIn (U \ N) x = B i \ N := by
    intro i x hx
    let C := connectedComponentIn (U \ N) x
    let R := ⋃ j, ⋃ (_ : j ≠ i), B j
    have hR : IsClosed R := isClosed_iUnion_of_finite fun j => isClosed_iUnion_of_finite fun _ => (hB j).isClosed
    have hCsub : C ⊆ U \ N := connectedComponentIn_subset _ _
    have hxC : x ∈ C := mem_connectedComponentIn (hcellSub i hx)
    have hcover : C ⊆ B i ∪ R := by
      intro y hy
      rcases (hCsub hy).1 with hyN | hyB
      · exact False.elim ((hCsub hy).2 hyN)
      · obtain ⟨j, hyj⟩ := mem_iUnion.mp hyB
        by_cases hji : j = i
        · exact .inl (hji ▸ hyj)
        · exact .inr (mem_iUnion₂.mpr ⟨j, hji, hyj⟩)
    apply Subset.antisymm
    · intro y hy
      refine ⟨?_, (hCsub hy).2⟩
      by_contra hyB
      have hyR : y ∈ R := (hcover hy).resolve_left hyB
      obtain ⟨z, hzC, hzB, hzR⟩ := GM07.preconnected_inter_nonempty_of_closed_cover
        isPreconnected_connectedComponentIn (hB i).isClosed hR hcover ⟨x, hxC, hx.1⟩ ⟨y, hy, hyR⟩
      obtain ⟨j, hji, hzj⟩ := mem_iUnion₂.mp hzR
      exact (hCsub hzC).2 (hBB i j hji.symm ⟨hzB, hzj⟩)
    · exact (hcell i).1.subset_connectedComponentIn hx (hcellSub i)
  have hcells : componentsIn (U \ N) = range (fun i => B i \ N) := by
    ext C
    constructor
    · rintro ⟨x, hx, rfl⟩
      have hxB : x ∈ ⋃ i, B i := hx.1.resolve_left hx.2
      obtain ⟨i, hxi⟩ := mem_iUnion.mp hxB
      exact ⟨i, (hcomp i x ⟨hxi, hx.2⟩).symm⟩
    · rintro ⟨i, rfl⟩
      obtain ⟨x, hx⟩ := (hcell i).2.1
      exact ⟨x, hcellSub i hx, hcomp i x hx⟩
  let P : PaintingInDisc S := {
    U := U
    N := N
    isClosed_U := hN.isClosed.union (isClosed_iUnion_of_finite fun i => (hB i).isClosed)
    N_subset_U := subset_union_left
    finite_N := hN
    finite_cells := hcells.symm ▸ finite_range _
    cell_disc := by
      intro C hC
      obtain ⟨i, rfl⟩ := hcells ▸ hC
      rw [(hcell i).2.2]
      exact ⟨hB i, fun x hx => hBN i ⟨hx.1, by
        by_contra hn; exact hx.2 ⟨hx.1, hn⟩⟩⟩
    cell_disjoint_bd := by
      intro C hC
      obtain ⟨i, rfl⟩ := hcells ▸ hC
      exact disjoint_left.mpr fun x hx hxbd => hx.2 (hbd i ⟨hx.1, hxbd⟩) }
  exact ⟨P, rfl, rfl, hcells, fun i => (hcell i).2.2⟩

end GraphMinor.GM08
