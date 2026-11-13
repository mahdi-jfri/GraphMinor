module

public import GraphMinor.GM16.SmallBoundaryLines
public import GraphMinor.GM16.BoundaryLoopFamily

/-!
# Drawing all edges on at most three boundary vertices

The small pieces of the torso in XVI (1.3), page 51, may have parallel
edges and loops. Insert their non-loop edges as successive chords,
retaining a disc through every vertex. Draw the loops in that remaining
disc. Their tangent discs avoid the previously drawn edges except at
the marked boundary points.
-/

public section
namespace GraphMinor.GM16
open Set Surface
universe u w

/-- A finite graph edge family on at most three boundary points has
pairwise disjoint interiors in the disc. Loops and parallel edges are
allowed. Every edge meets the original boundary only at its ends. -/
theorem exists_small_boundary_curves
    {S : Type w} [TopologicalSpace S] [T2Space S] {ι : Type u}
    {D P : Set S} (hD : IsClosedDisc D) (hP : P.Finite)
    (hcard : P.ncard ≤ 3) (hPb : P ⊆ discBd D)
    (a b : ι → S) (F : Set ι) (hFinite : F.Finite)
    (hEnds : ∀ i ∈ F, a i ∈ P ∧ b i ∈ P) :
    ∃ J : ι → Set S,
      (∀ i ∈ F,
        (a i ≠ b i → IsLineWithEnds (J i) (a i) (b i)) ∧
        (a i = b i → IsOArc (J i) ∧ a i ∈ J i) ∧
        J i ⊆ D ∧ J i ∩ P = {a i, b i} ∧
        J i ∩ discBd D = {a i, b i}) ∧
      F.Pairwise (fun i j => J i ∩ J j ⊆ P) := by
  classical
  let N : Set ι := {i ∈ F | a i ≠ b i}
  let Q : Set ι := {i ∈ F | a i = b i}
  obtain ⟨K, D', hD', hD'D, hPD', hOldBd, hK, hKK⟩ :=
    exists_small_boundary_lines hD hP hcard hPb a b N
      (hFinite.subset (fun _ h => h.1))
      (fun i hi => ⟨(hEnds i hi.1).1, (hEnds i hi.1).2, hi.2⟩)
  obtain ⟨L, hL, hLL⟩ := exists_boundary_loop_family hD' hP hPD' a Q
    (hFinite.subset (fun _ h => h.1)) (fun i hi => (hEnds i hi.1).1)
  let J : ι → Set S := fun i => if a i = b i then L i else K i
  have hLoopMeet : ∀ i ∈ Q, L i ∩ P = {a i} := by
    intro i hi
    ext x
    constructor
    · rintro ⟨hxL, hxP⟩
      exact (hL i hi).2.2.2 ▸ And.intro hxL (hPD' hxP)
    · rintro rfl
      exact ⟨(hL i hi).2.2.1, (hEnds i hi.1).1⟩
  have hLoopOuter : ∀ i ∈ Q, L i ∩ discBd D = {a i} := by
    intro i hi
    ext x
    constructor
    · rintro ⟨hxL, hxD⟩
      exact (hL i hi).2.2.2 ▸ And.intro hxL (hOldBd ⟨(hL i hi).2.1 hxL, hxD⟩)
    · rintro rfl
      exact ⟨(hL i hi).2.2.1, hPb (hEnds i hi.1).1⟩
  have hLoopLine : ∀ i ∈ Q, ∀ j ∈ N, L i ∩ K j ⊆ P := by
    intro i hi j hj x ⟨hxL, hxK⟩
    have hxBd := (hK j hj).2.2.2.2 ⟨hxK, (hL i hi).2.1 hxL⟩
    have hxSingleton : x ∈ ({a i} : Set S) := (hL i hi).2.2.2 ▸ And.intro hxL hxBd
    have hxa : x = a i := mem_singleton_iff.mp hxSingleton
    exact hxa ▸ (hEnds i hi.1).1
  refine ⟨J, ?_, ?_⟩
  · intro i hi
    by_cases hab : a i = b i
    · have hiQ : i ∈ Q := ⟨hi, hab⟩
      simp only [J, ite_eq_left hab]
      refine ⟨fun hne => (hne hab).elim, fun _ => ⟨(hL i hiQ).1, (hL i hiQ).2.2.1⟩,
        (hL i hiQ).2.1.trans hD'D, ?_, ?_⟩
      · simpa [hab] using hLoopMeet i hiQ
      · simpa [hab] using hLoopOuter i hiQ
    · have hiN : i ∈ N := ⟨hi, hab⟩
      simp only [J, ite_eq_right hab]
      obtain ⟨hLine, hSub, hMeet, hOuter, _⟩ := hK i hiN
      exact ⟨fun _ => hLine, fun heq => (hab heq).elim, hSub, hMeet, hOuter⟩
  · intro i hi j hj hij
    by_cases habi : a i = b i <;> by_cases habj : a j = b j
    · simp only [J, ite_eq_left habi, ite_eq_left habj]
      exact hLL ⟨hi, habi⟩ ⟨hj, habj⟩ hij
    · simp only [J, ite_eq_left habi, ite_eq_right habj]
      exact hLoopLine i ⟨hi, habi⟩ j ⟨hj, habj⟩
    · simp only [J, ite_eq_right habi, ite_eq_left habj]
      rw [inter_comm]
      exact hLoopLine j ⟨hj, habj⟩ i ⟨hi, habi⟩
    · simp only [J, ite_eq_right habi, ite_eq_right habj]
      exact hKK ⟨hi, habi⟩ ⟨hj, habj⟩ hij

end GraphMinor.GM16
