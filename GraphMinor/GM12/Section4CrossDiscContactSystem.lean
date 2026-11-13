module

public import GraphMinor.GM12.Section4CrossDiscFamily
public import GraphMinor.GM12.Section4CrossDiscQuadrants

/-!
# The marked disc system at the source crossings

For XII (4.5), claim (1), page 253, choose disjoint crossing
discs and enumerate their four boundary marks by the four
quarter-turn positions. The first and third marks belong to
one crossing arc, and the second and fourth to the other.
This combines the small-disc and boundary-parametrization
constructions into a single finite marked family.
-/

public section

namespace GraphMinor.GM12

open Set Surface

universe u

/-- The small discs around finitely many locally straight
crossings have four distinct boundary marks, alternating
between the two crossing arcs. This is the local marked-disc
construction used in XII (4.5), claim (1), page 253. -/
theorem exists_cross_disc_contact_system {ι : Type u} [Finite ι]
    (x : ι → ℂ) (hinj : Function.Injective x) (A : ι → ℂ ≃L[ℝ] ℂ)
    (E F U : ι → Set ℂ) (hU : ∀ i, IsOpen (U i)) (hx : ∀ i, x i ∈ U i)
    (hE : ∀ i, E i ∩ U i = (line[ℝ, x i, x i + A i 1] : Set ℂ) ∩ U i)
    (hF : ∀ i, F i ∩ U i = (line[ℝ, x i, x i + A i Complex.I] : Set ℂ) ∩ U i) :
    ∃ (D : ι → Set ℂ) (m : ι → Fin 4 → ℂ) (p : ι → Circle → ℂ),
      (∀ i, IsClosedDisc (D i)) ∧ (∀ i, D i ⊆ U i) ∧
      (∀ i j, i ≠ j → Disjoint (D i) (D j)) ∧
      (∀ i, Function.Injective (m i)) ∧
      (∀ i, (range (m i)).ncard = 4 ∧ range (m i) ⊆ discBd (D i)) ∧
      (∀ i, Continuous (p i) ∧ Function.Injective (p i) ∧ range (p i) = discBd (D i)) ∧
      (∀ i j, m i j = p i (ee ((j.val : ℝ) / 4))) ∧
      (∀ i, E i ∩ discBd (D i) = {m i 0, m i 2}) ∧
      (∀ i, F i ∩ discBd (D i) = {m i 1, m i 3}) ∧
      (∀ i, x i ∈ interior (D i)) := by
  obtain ⟨r, hr, D, hD, hsub, hdisj, hEM, hFM, hcoord⟩ :=
    exists_local_cross_disc_family x hinj A E F U hU hx hE hF
  let m := fun i => crossDiscMarks (A i) (x i) (r i)
  let p := fun i => crossDiscParam (A i) (x i) (r i)
  refine ⟨D, m, p, hD, hsub, hdisj,
    (fun i => crossDiscMarks_injective (A i) (x i) (hr i)), ?_, ?_, (fun _ _ => rfl), ?_, ?_, ?_⟩
  · intro i
    rw [hcoord i]
    exact crossDiscMarks_card_boundary (A i) (x i) (hr i)
  · intro i
    rw [hcoord i]
    exact crossDiscParam_properties (A i) (x i) (hr i)
  · intro i
    obtain ⟨h0, -, h2, -⟩ := crossDiscMarks_values (A i) (x i) (r i)
    change E i ∩ discBd (D i) =
      {crossDiscMarks (A i) (x i) (r i) 0, crossDiscMarks (A i) (x i) (r i) 2}
    rw [h0, h2]
    exact hEM i
  · intro i
    obtain ⟨-, h1, -, h3⟩ := crossDiscMarks_values (A i) (x i) (r i)
    change F i ∩ discBd (D i) =
      {crossDiscMarks (A i) (x i) (r i) 1, crossDiscMarks (A i) (x i) (r i) 3}
    rw [h1, h3]
    exact hFM i
  · intro i
    rw [hcoord i]
    exact cross_disc_center_mem_interior (A i) (x i) (hr i)

end GraphMinor.GM12
