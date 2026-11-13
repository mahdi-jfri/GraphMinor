module

public import GraphMinor.Compute.Case3StepsSelectedSizeBound
public import GraphMinor.Compute.Case3StepsCompactCounts
public import GraphMinor.Compute.Case3StepsBranchRecordBounds
public import GraphMinor.Compute.Algorithm99TransportOrig
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Records retained by the interior-member scan

Retain the selected candidate and the returned code for each branch
result. Their records use the composed original vertex map. Distinct
processed candidates charge distinct terms in the page 106 capacity sum.
A candidate not yet processed therefore has room for its next record.
-/

@[expose] public section

namespace GraphMinor.Compute

open GraphMinor.Transport

/-- The original-label record determined by one selected member and code. -/
noncomputable def case3SelectedRecord {N : ℕ} (x : Alg81Input) (D : MultiDigraph x.n)
    (Z : Finset (Fin x.n)) (e : Fin x.n ↪ Fin N) (i : Case3SelectedGroup x Z)
    (code : List ℕ) : Case3MemberRecord :=
  let orig := e ∘ (case3SelectedMember x Z i).verts.orderEmbOfFin rfl
  let hinj := e.injective.comp ((case3SelectedMember x Z i).verts.orderEmbOfFin rfl).injective
  case3BranchRecord (case3CompactMember x D Z i) (origVertexEmb orig hinj) (origEdgeEmb orig hinj) code

/-- The member list encoded by the stored selected candidates and codes. -/
noncomputable def case3SelectedRecordList {N : ℕ} (x : Alg81Input) (D : MultiDigraph x.n)
    (Z : Finset (Fin x.n)) (e : Fin x.n ↪ Fin N)
    (entries : List (Case3SelectedGroup x Z × List ℕ)) : List Case3MemberRecord :=
  entries.map (fun p => case3SelectedRecord x D Z e p.1 p.2)

/-- The record buffer's used prefix. -/
noncomputable def case3SelectedRecordsEncoding {N : ℕ} (x : Alg81Input) (D : MultiDigraph x.n)
    (Z : Finset (Fin x.n)) (e : Fin x.n ↪ Fin N)
    (entries : List (Case3SelectedGroup x Z × List ℕ)) : List ℕ :=
  (case3SelectedRecordList x D Z e entries).flatMap Case3MemberRecord.enc

/-- The uniform capacity reserved for a selected member record. -/
noncomputable def case3SelectedRecordCapacity (x : Alg81Input) (D : MultiDigraph x.n)
    (Z : Finset (Fin x.n)) (i : Case3SelectedGroup x Z) : ℕ :=
  (case3SelectedMember x Z i).verts.card + 6 * (case3CompactMember x D Z i).numEdges + 4

/-- The returned branch code bounds its record by the reserved member capacity. -/
theorem case3SelectedRecord_length_le {N B : ℕ} (x : Alg81Input) (D : MultiDigraph x.n)
    (Z : Finset (Fin x.n)) (e : Fin x.n ↪ Fin N) (i : Case3SelectedGroup x Z)
    (code : List ℕ) (hcode : IsValidBranchDecompCode B (case3CompactMember x D Z i) code) :
    (case3SelectedRecord x D Z e i code).enc.length ≤ case3SelectedRecordCapacity x D Z i :=
  case3BranchRecord_enc_length_le _ _ _ code hcode

/-- The sum of the capacities uses the full directed-copy count from page 106. -/
theorem case3SelectedRecordCapacity_sum_le (x : Alg81Input) (D : MultiDigraph x.n)
    (hG : D.toSimpleGraph = x.G) (d : Alg86DivisionOutput x)
    (hd : IsValidAlg86DivisionOutput x d)
    (hdiv : GM13.IsSocietyDivision x.toSociety
      (Alg86Subgraph.toGMGraph '' case3SelectedMembers x d.core.Z)) :
    (∑ i : Case3SelectedGroup x d.core.Z, case3SelectedRecordCapacity x D d.core.Z i) ≤
      24 * (x.n + D.numEdges) := by
  have hsum : (∑ i : Case3SelectedGroup x d.core.Z, case3SelectedRecordCapacity x D d.core.Z i) =
      ∑ i : Case3SelectedGroup x d.core.Z,
        ((case3SelectedMember x d.core.Z i).verts.card +
          6 * (case3RoutedMember x D d.core.Z (case3RawIndexLabel x i.1)).numEdges + 4) := by
    apply Finset.sum_congr rfl
    intro i _
    unfold case3SelectedRecordCapacity
    rw [case3CompactMember_numEdges x D hG d.core.Z hdiv i]
  rw [hsum]
  exact case3SelectedMembers_sum_recordCapacity_le x D hG d hd

private theorem list_cost_le_sum {I : Type*} [Fintype I] (l : List I)
    (hn : l.Nodup) (f : I → ℕ) : (l.map f).sum ≤ ∑ i : I, f i := by
  classical
  have heq : (l.map f).sum = ∑ i ∈ l.toFinset, f i := by
    induction l with
    | nil => simp only [List.map_nil, List.sum_nil, List.toFinset_nil, Finset.sum_empty]
    | cons a l ih =>
      have ha := List.nodup_cons.mp hn
      have ha' : a ∉ l.toFinset := by simpa only [List.mem_toFinset] using ha.1
      simp only [List.map_cons, List.sum_cons, List.toFinset_cons,
        Finset.sum_insert ha', ih ha.2]
  rw [heq]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (by intro i _ _; exact Nat.zero_le _)

/-- The used record prefix is bounded by the capacities of its retained
candidates, before any uniqueness assumption is needed. -/
theorem case3SelectedRecordsEncoding_length_le {N B : ℕ} (x : Alg81Input) (D : MultiDigraph x.n)
    (Z : Finset (Fin x.n)) (e : Fin x.n ↪ Fin N)
    (entries : List (Case3SelectedGroup x Z × List ℕ))
    (hcodes : ∀ p ∈ entries, IsValidBranchDecompCode B (case3CompactMember x D Z p.1) p.2) :
    (case3SelectedRecordsEncoding x D Z e entries).length ≤
      ((entries.map Prod.fst).map (case3SelectedRecordCapacity x D Z)).sum := by
  induction entries with
  | nil => simp only [case3SelectedRecordsEncoding, case3SelectedRecordList, List.map_nil,
      List.flatMap_nil, List.length_nil, List.sum_nil, Nat.le_refl]
  | cons p entries ih =>
    have hp := hcodes p (List.mem_cons_self ..)
    have htail : ∀ q ∈ entries, IsValidBranchDecompCode B (case3CompactMember x D Z q.1) q.2 :=
      fun q hq => hcodes q (List.mem_cons_of_mem _ hq)
    simp only [List.map_cons, List.sum_cons]
    change ((case3SelectedRecord x D Z e p.1 p.2).enc ++
      case3SelectedRecordsEncoding x D Z e entries).length ≤
        case3SelectedRecordCapacity x D Z p.1 + _
    rw [List.length_append]
    exact Nat.add_le_add (case3SelectedRecord_length_le x D Z e p.1 p.2 hp) (ih htail)

/-- The same prefix bound applies to any retained records whose encoded
lengths fit their member capacities, including noninterior placeholders. -/
theorem case3SelectedRecordsEncoding_length_le_of_bounds {N : ℕ} (x : Alg81Input) (D : MultiDigraph x.n)
    (Z : Finset (Fin x.n)) (e : Fin x.n ↪ Fin N)
    (entries : List (Case3SelectedGroup x Z × List ℕ))
    (hbounds : ∀ p ∈ entries, (case3SelectedRecord x D Z e p.1 p.2).enc.length ≤
      case3SelectedRecordCapacity x D Z p.1) :
    (case3SelectedRecordsEncoding x D Z e entries).length ≤
      ((entries.map Prod.fst).map (case3SelectedRecordCapacity x D Z)).sum := by
  induction entries with
  | nil => simp only [case3SelectedRecordsEncoding, case3SelectedRecordList, List.map_nil,
      List.flatMap_nil, List.length_nil, List.sum_nil, Nat.le_refl]
  | cons p entries ih =>
    have hp := hbounds p (List.mem_cons_self ..)
    have htail : ∀ q ∈ entries, (case3SelectedRecord x D Z e q.1 q.2).enc.length ≤
        case3SelectedRecordCapacity x D Z q.1 := fun q hq => hbounds q (List.mem_cons_of_mem _ hq)
    simp only [List.map_cons, List.sum_cons]
    change ((case3SelectedRecord x D Z e p.1 p.2).enc ++
      case3SelectedRecordsEncoding x D Z e entries).length ≤ case3SelectedRecordCapacity x D Z p.1 + _
    rw [List.length_append]
    exact Nat.add_le_add hp (ih htail)

/-- Distinct retained records leave the next fresh member's capacity
available in the global sum, for both branch and placeholder records. -/
theorem case3SelectedRecordsEncoding_add_fresh_capacity_le_of_bounds {N : ℕ}
    (x : Alg81Input) (D : MultiDigraph x.n) (Z : Finset (Fin x.n))
    (e : Fin x.n ↪ Fin N) (entries : List (Case3SelectedGroup x Z × List ℕ))
    (hbounds : ∀ p ∈ entries, (case3SelectedRecord x D Z e p.1 p.2).enc.length ≤
      case3SelectedRecordCapacity x D Z p.1)
    (hn : (entries.map Prod.fst).Nodup) (i : Case3SelectedGroup x Z)
    (hi : i ∉ entries.map Prod.fst) :
    (case3SelectedRecordsEncoding x D Z e entries).length + case3SelectedRecordCapacity x D Z i ≤
      ∑ j : Case3SelectedGroup x Z, case3SelectedRecordCapacity x D Z j := by
  classical
  have hlist := list_cost_le_sum (i :: entries.map Prod.fst) (List.nodup_cons.mpr ⟨hi, hn⟩)
    (case3SelectedRecordCapacity x D Z)
  simp only [List.map_cons, List.sum_cons] at hlist
  have hprefix := case3SelectedRecordsEncoding_length_le_of_bounds x D Z e entries hbounds
  omega

/-- A fresh candidate's entire reserved capacity fits after the records
already written, because the scan never processes a candidate twice. -/
theorem case3SelectedRecordsEncoding_add_fresh_capacity_le {N B : ℕ}
    (x : Alg81Input) (D : MultiDigraph x.n) (Z : Finset (Fin x.n))
    (e : Fin x.n ↪ Fin N) (entries : List (Case3SelectedGroup x Z × List ℕ))
    (hcodes : ∀ p ∈ entries, IsValidBranchDecompCode B (case3CompactMember x D Z p.1) p.2)
    (hn : (entries.map Prod.fst).Nodup) (i : Case3SelectedGroup x Z)
    (hi : i ∉ entries.map Prod.fst) :
    (case3SelectedRecordsEncoding x D Z e entries).length + case3SelectedRecordCapacity x D Z i ≤
      ∑ j : Case3SelectedGroup x Z, case3SelectedRecordCapacity x D Z j := by
  classical
  have hlist := list_cost_le_sum (i :: entries.map Prod.fst) (List.nodup_cons.mpr ⟨hi, hn⟩)
    (case3SelectedRecordCapacity x D Z)
  simp only [List.map_cons, List.sum_cons] at hlist
  have hprefix := case3SelectedRecordsEncoding_length_le x D Z e entries hcodes
  omega

end GraphMinor.Compute
