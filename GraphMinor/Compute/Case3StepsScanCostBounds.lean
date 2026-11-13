module

public import GraphMinor.Compute.Case3StepsScanRecords
public import GraphMinor.Compute.Case3StepsCandidateSizeBound
import GraphMinor.Compute.Case3StepsMultigraphComponents

/-!
# Summing all iteration charges

Selected labels are distinct candidates, so their number is bounded by the
vertex and simple-edge counts. The sum of member call sizes is controlled
by page 106, and routed directed copies are counted only once. The extra
construction and original-label copying costs therefore fit the same
ambient vertex-times-edge bound.
-/

@[expose] public section

namespace GraphMinor.Compute

/-- The nonconstant charge for one selected scan iteration. -/
noncomputable def case3MemberScanCharge (x : Alg81Input) (D : MultiDigraph x.n)
    (Z : Finset (Fin x.n)) (N : ℕ) (i : Case3SelectedGroup x Z) : ℕ :=
  algorithm72Size (case3MemberAlgorithm72Input x D Z i) + x.n +
    (case3RoutedMember x D Z (case3RawIndexLabel x i.1)).numActivePairs +
    (case3CompactMember x D Z i).numActivePairs + (case3CompactMember x D Z i).numEdges + N + 1

/-- Selected groups inject into the contiguous candidate label range. -/
theorem case3SelectedGroups_card_le (x : Alg81Input) (Z : Finset (Fin x.n)) :
    Fintype.card (Case3SelectedGroup x Z) ≤ x.n + (case3InputEdges x).length := by
  let f := fun i : Case3SelectedGroup x Z => case3GroupLabelEquiv x i.1
  have hf : Function.Injective f := fun i j hij =>
    Subtype.ext ((case3GroupLabelEquiv x).injective hij)
  exact (Fintype.card_le_of_injective f hf).trans_eq (Fintype.card_fin _)

/-- The selected-member pair count also sums to at most the full input
edge count, since every positive pair accounts for at least one copy. -/
theorem case3SelectedMembers_sum_numActivePairs_le (x : Alg81Input) (D : MultiDigraph x.n)
    (Z : Finset (Fin x.n)) :
    (∑ i : Case3SelectedGroup x Z,
      (case3RoutedMember x D Z (case3RawIndexLabel x i.1)).numActivePairs) ≤ D.numEdges :=
  (Finset.sum_le_sum (fun i _ =>
    (case3RoutedMember x D Z (case3RawIndexLabel x i.1)).numActivePairs_le_numEdges)).trans
      (case3SelectedMembers_sum_numEdges_le x D Z)

/-- All selected iteration charges fit a fixed multiple of the ambient
product, including the original vertex count charged to wall copying. -/
theorem case3MemberScanCharge_sum_le (x : Alg81Input) (D : MultiDigraph x.n)
    (hG : D.toSimpleGraph = x.G) (d : Alg86DivisionOutput x)
    (hd : IsValidAlg86DivisionOutput x d)
    (hdiv : GM13.IsSocietyDivision x.toSociety
      (Alg86Subgraph.toGMGraph '' case3SelectedMembers x d.core.Z))
    (N : ℕ) (hn : x.n ≤ N) :
    (∑ i : Case3SelectedGroup x d.core.Z, case3MemberScanCharge x D d.core.Z N i) ≤
      13 * ((N + 1) * (D.numEdges + N + 1)) := by
  classical
  let K := Fintype.card (Case3SelectedGroup x d.core.Z)
  let V := (N + 1) * (D.numEdges + N + 1)
  have hsimple := (case3InputEdges_length_le x D hG).trans D.numActivePairs_le_numEdges
  have hK : K ≤ x.n + D.numEdges :=
    (case3SelectedGroups_card_le x d.core.Z).trans (Nat.add_le_add_left hsimple x.n)
  have hcall := case3SelectedMembers_sum_algorithm72Size_le x D hG d hd hdiv
  have hambient : (x.n + 1) * (D.numEdges + x.n + 1) ≤ V :=
    Nat.mul_le_mul (Nat.add_le_add_right hn 1)
      (Nat.add_le_add_right (Nat.add_le_add_left hn D.numEdges) 1)
  have hcallV : (∑ i : Case3SelectedGroup x d.core.Z,
      algorithm72Size (case3MemberAlgorithm72Input x D d.core.Z i)) ≤ 8 * V := by
    rw [Nat.mul_assoc 8] at hcall
    exact hcall.trans (Nat.mul_le_mul_left 8 hambient)
  have hRA := case3SelectedMembers_sum_numActivePairs_le x D d.core.Z
  have hCA : (∑ i : Case3SelectedGroup x d.core.Z,
      (case3CompactMember x D d.core.Z i).numActivePairs) ≤ D.numEdges := by
    have heq : (∑ i : Case3SelectedGroup x d.core.Z,
        (case3CompactMember x D d.core.Z i).numActivePairs) =
        ∑ i : Case3SelectedGroup x d.core.Z,
          (case3RoutedMember x D d.core.Z (case3RawIndexLabel x i.1)).numActivePairs :=
      Finset.sum_congr rfl (fun i _ => case3CompactMember_numActivePairs x D hG d.core.Z hdiv i)
    exact heq ▸ hRA
  have hCE : (∑ i : Case3SelectedGroup x d.core.Z,
      (case3CompactMember x D d.core.Z i).numEdges) ≤ D.numEdges := by
    have heq : (∑ i : Case3SelectedGroup x d.core.Z,
        (case3CompactMember x D d.core.Z i).numEdges) =
        ∑ i : Case3SelectedGroup x d.core.Z,
          (case3RoutedMember x D d.core.Z (case3RawIndexLabel x i.1)).numEdges :=
      Finset.sum_congr rfl (fun i _ => case3CompactMember_numEdges x D hG d.core.Z hdiv i)
    exact heq ▸ case3SelectedMembers_sum_numEdges_le x D d.core.Z
  have hcount : K * (x.n + N + 1) ≤ 2 * V := by
    calc
      _ ≤ (D.numEdges + N + 1) * (2 * (N + 1)) :=
        Nat.mul_le_mul (by omega) (by omega)
      _ = _ := by dsimp only [V]; ring
  have hE : D.numEdges ≤ V := by
    have hmul := Nat.mul_le_mul_right (D.numEdges + N + 1) (show 1 ≤ N + 1 by omega)
    dsimp only [V]
    omega
  have hsum : (∑ i : Case3SelectedGroup x d.core.Z, case3MemberScanCharge x D d.core.Z N i) =
      (∑ i : Case3SelectedGroup x d.core.Z,
        algorithm72Size (case3MemberAlgorithm72Input x D d.core.Z i)) + K * (x.n + N + 1) +
      (∑ i : Case3SelectedGroup x d.core.Z,
        (case3RoutedMember x D d.core.Z (case3RawIndexLabel x i.1)).numActivePairs) +
      (∑ i : Case3SelectedGroup x d.core.Z, (case3CompactMember x D d.core.Z i).numActivePairs) +
      ∑ i : Case3SelectedGroup x d.core.Z, (case3CompactMember x D d.core.Z i).numEdges := by
    simp only [case3MemberScanCharge, Finset.sum_add_distrib, Finset.sum_const,
      Finset.card_univ, smul_eq_mul, K]
    ring
  rw [hsum]
  change _ ≤ 13 * V
  omega

end GraphMinor.Compute
