module

public import GraphMinor.Surface.TopologyStatements
import GraphMinor.Surface.EdgeLens
import GraphMinor.Surface.SurfaceGraph

/-!
# Thickening finitely many non-loop edges

Choose an edge lens for one line at a time. Protect the fixed closed
set, every other line, and all lenses already chosen. The earlier lenses
meet the new line only at its ends, so the next lens exists. This gives
the pairwise intersection condition for the thickened edges on VIII,
page 272, used in the derived portraits of Section 12.
-/

public section

namespace GraphMinor.GM08

open Set Surface

universe v

/-- A finite family of lines meeting only at their ends can be thickened
to closed discs, avoiding a protected closed set except at their ends.
The discs meet one another only where their original lines meet. This
is the non-loop thickening step on VIII, page 272. -/
theorem exists_edge_lens_family {S : Type} [TopologicalSpace S]
    (hS : IsClosedSurface S) {ι : Type v} [Finite ι]
    (L : ι → Set S) (u v : ι → S) (hL : ∀ i, IsLineWithEnds (L i) (u i) (v i))
    (huv : ∀ i, u i ≠ v i) {Z : Set S} (hZ : IsClosed Z)
    (hLZ : ∀ i, L i ∩ Z ⊆ {u i, v i})
    (hLL : ∀ i j, i ≠ j → L i ∩ L j ⊆ {u i, v i} ∩ {u j, v j}) :
    ∃ D : ι → Set S,
      (∀ i, IsClosedDisc (D i) ∧ L i ⊆ D i ∧ D i ∩ Z ⊆ {u i, v i} ∧
        u i ∈ discBd (D i) ∧ v i ∈ discBd (D i) ∧
        ∀ j, j ≠ i → D i ∩ L j ⊆ L i ∩ L j) ∧
      ∀ i j, i ≠ j → D i ∩ D j ⊆ L i ∩ L j := by
  classical
  have : T2Space S := hS.2.1
  have : Fintype ι := Fintype.ofFinite ι
  have hends : ∀ i, ({u i, v i} : Set S) ⊆ L i := fun i =>
    insert_subset (hL i).left_mem (singleton_subset_iff.mpr (hL i).right_mem)
  have hex : ∀ A : Finset ι, ∃ D : ι → Set S,
      (∀ i ∈ A, IsClosedDisc (D i) ∧ L i ⊆ D i ∧ D i ∩ Z ⊆ {u i, v i} ∧
        u i ∈ discBd (D i) ∧ v i ∈ discBd (D i) ∧
        ∀ j, j ≠ i → D i ∩ L j ⊆ L i ∩ L j) ∧
      ∀ i ∈ A, ∀ j ∈ A, i ≠ j → D i ∩ D j ⊆ L i ∩ L j := by
    intro A
    induction A using Finset.induction_on with
    | empty => exact ⟨fun _ => ∅, fun i hi => False.elim (Finset.notMem_empty i hi),
        fun i hi => False.elim (Finset.notMem_empty i hi)⟩
    | @insert a A ha ih =>
      obtain ⟨D, hD, hDD⟩ := ih
      let Z' := (Z ∪ ⋃ j, ⋃ (_ : j ≠ a), L j) ∪ ⋃ j ∈ A, D j
      have hZ' : IsClosed Z' := (hZ.union
        (isClosed_iUnion_of_finite fun j => isClosed_iUnion_of_finite fun _ =>
          (hL j).isCompact.isClosed)).union
        (A.finite_toSet.isClosed_biUnion fun j hj => (hD j hj).1.isClosed)
      have hLaZ' : L a ∩ Z' ⊆ {u a, v a} := by
        rintro x ⟨hxL, (hxZ | hxOld)⟩
        · rcases hxZ with hxZ | hxLine
          · exact hLZ a ⟨hxL, hxZ⟩
          · obtain ⟨j, hja, hxj⟩ := mem_iUnion₂.mp hxLine
            exact (hLL a j hja.symm ⟨hxL, hxj⟩).1
        · obtain ⟨j, hj, hxj⟩ := mem_iUnion₂.mp hxOld
          have hja : a ≠ j := fun h => ha (h ▸ hj)
          have hxLj := (hD j hj).2.2.2.2.2 a hja ⟨hxj, hxL⟩
          exact (hLL a j hja ⟨hxL, hxLj.1⟩).1
      obtain ⟨Da, _, _, hDa, hLa, hDaZ, hua, hva, _⟩ := exists_edge_lens hS (hL a) (huv a) hZ' hLaZ'
      have hcross : ∀ j ∈ A, Da ∩ D j ⊆ L a ∩ L j := by
        intro j hj x hx
        have hja : a ≠ j := fun h => ha (h ▸ hj)
        have hxend : x ∈ ({u a, v a} : Set S) := hDaZ
          ⟨hx.1, .inr (mem_iUnion₂.mpr ⟨j, hj, hx.2⟩)⟩
        have hxLa := hends a hxend
        exact ⟨hxLa, ((hD j hj).2.2.2.2.2 a hja ⟨hx.2, hxLa⟩).1⟩
      refine ⟨Function.update D a Da, ?_, ?_⟩
      · intro i hi
        rcases Finset.mem_insert.mp hi with hia | hi
        · subst i
          rw [Function.update_self]
          refine ⟨hDa, hLa, fun x hx => hDaZ ⟨hx.1, .inl (.inl hx.2)⟩, hua, hva, ?_⟩
          intro j hja x hx
          have hxend : x ∈ ({u a, v a} : Set S) := hDaZ
            ⟨hx.1, .inl (.inr (mem_iUnion₂.mpr ⟨j, hja, hx.2⟩))⟩
          exact ⟨hends a hxend, hx.2⟩
        · have hia : i ≠ a := fun h => ha (h ▸ hi)
          simpa only [Function.update_of_ne hia] using hD i hi
      · intro i hi j hj hij
        by_cases hia : i = a
        · subst i
          have hjA : j ∈ A := (Finset.mem_insert.mp hj).resolve_left hij.symm
          rw [Function.update_self, Function.update_of_ne hij.symm]
          exact hcross j hjA
        · have hiA : i ∈ A := (Finset.mem_insert.mp hi).resolve_left hia
          by_cases hja : j = a
          · subst j
            rw [Function.update_of_ne hia, Function.update_self, inter_comm (D i) Da, inter_comm (L i) (L a)]
            exact hcross i hiA
          · have hjA : j ∈ A := (Finset.mem_insert.mp hj).resolve_left hja
            rw [Function.update_of_ne hia, Function.update_of_ne hja]
            exact hDD i hiA j hjA hij
  obtain ⟨D, hD, hDD⟩ := hex Finset.univ
  exact ⟨D, fun i => hD i (Finset.mem_univ _),
    fun i j hij => hDD i (Finset.mem_univ _) j (Finset.mem_univ _) hij⟩

end GraphMinor.GM08
