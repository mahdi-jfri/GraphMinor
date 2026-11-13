module

public import GraphMinor.GM16.NestedLoopArcs
import Mathlib.Topology.Separation.Hausdorff

/-!
# Loop families at finitely many boundary vertices

For the small torso drawing in XVI (1.3), page 51, first separate the
boundary vertices by disjoint open neighborhoods. At each vertex draw
nested loop arcs in its neighborhood. Distinct vertices then give
disjoint arcs, and loops at the same vertex meet only there.
-/

public section
namespace GraphMinor.GM16
open Set Surface
universe u w

/-- Finitely many loops at prescribed boundary points have drawings
that meet the disc boundary only at their respective vertices. -/
theorem exists_boundary_loop_family
    {S : Type w} [TopologicalSpace S] [T2Space S] {ι : Type u}
    {D P : Set S} (hD : IsClosedDisc D) (hP : P.Finite) (hPb : P ⊆ discBd D)
    (v : ι → S) (F : Set ι) (hFinite : F.Finite) (hv : ∀ i ∈ F, v i ∈ P) :
    ∃ L : ι → Set S,
      (∀ i ∈ F, IsOArc (L i) ∧ L i ⊆ D ∧ v i ∈ L i ∧
        L i ∩ discBd D = {v i}) ∧
      F.Pairwise (fun i j => L i ∩ L j ⊆ P) := by
  classical
  let : Finite F := hFinite.to_subtype
  obtain ⟨n, ⟨eqv⟩⟩ := Finite.exists_equiv_fin F
  obtain ⟨U, hU, hDisj⟩ := hP.t2_separation
  have hex : ∀ x : P, ∃ C : Fin n → Set S,
      (∀ i, IsOArc (C i) ∧ C i ⊆ D ∧ C i ⊆ U x ∧
        (x : S) ∈ C i ∧ C i ∩ discBd D = {(x : S)}) ∧
      Pairwise (fun i j => C i ∩ C j = {(x : S)}) := by
    intro x
    exact exists_loop_arcs_in_neighborhood n hD (hU x).2 (hPb x.2) (hU x).1
  choose C hC hCC using hex
  let L : ι → Set S := fun i => if hi : i ∈ F then
    C ⟨v i, hv i hi⟩ (eqv ⟨i, hi⟩) else ∅
  refine ⟨L, ?_, ?_⟩
  · intro i hi
    simp only [L, dite_eq_left hi]
    obtain ⟨hArc, hSub, _, hmem, hmeet⟩ := hC ⟨v i, hv i hi⟩ (eqv ⟨i, hi⟩)
    exact ⟨hArc, hSub, hmem, hmeet⟩
  · intro i hi j hj hij
    simp only [L, dite_eq_left hi, dite_eq_left hj]
    by_cases hvij : v i = v j
    · have hx : (⟨v i, hv i hi⟩ : P) = ⟨v j, hv j hj⟩ := Subtype.ext hvij
      rw [hx]
      have hIdx : eqv ⟨i, hi⟩ ≠ eqv ⟨j, hj⟩ := fun heq =>
        hij (congrArg Subtype.val (eqv.injective heq))
      rw [hCC ⟨v j, hv j hj⟩ hIdx]
      exact singleton_subset_iff.mpr (hv j hj)
    · exact (disjoint_left.mpr (fun x hx hy =>
        disjoint_left.mp (hDisj (hv i hi) (hv j hj) hvij)
          ((hC ⟨v i, hv i hi⟩ (eqv ⟨i, hi⟩)).2.2.1 hx)
          ((hC ⟨v j, hv j hj⟩ (eqv ⟨j, hj⟩)).2.2.1 hy))).le_bot.trans (empty_subset P)

end GraphMinor.GM16
