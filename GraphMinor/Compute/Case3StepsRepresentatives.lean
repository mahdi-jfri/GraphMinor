module

public import GraphMinor.Compute.Case3StepsFindBoundaryProg

/-!
# Representatives for equal component boundaries

The least outside seed with a given attachment set represents all components
with that set. Each outside seed has such a representative, and equality of
representatives is equivalent to equality of attachment sets. This is the
component part of the equivalence relation in XIII (8.6), page 96.
-/

@[expose] public section

namespace GraphMinor.Compute

/-- The least outside seed whose attachment set equals that of `u`. -/
noncomputable def case3ComponentRepresentative (x : Alg81Input) (Z : Finset (Fin x.n))
    (u : Fin x.n) : ℕ :=
  case3FirstIndex (fun v => v ∉ Z ∧ case3AttachmentRowSet x Z v = case3AttachmentRowSet x Z u)

/-- The stored representative label of one vertex, or the sentinel for a core seed. -/
noncomputable def case3ComponentRepEntry (x : Alg81Input) (Z : Finset (Fin x.n))
    (u : Fin x.n) : ℕ :=
  if u ∈ Z then x.n else case3ComponentRepresentative x Z u

/-- A seed represents a component group exactly when its stored label is its
own index. Core seeds never pass this test. -/
theorem case3ComponentRepEntry_eq_own_iff (x : Alg81Input) (Z : Finset (Fin x.n))
    (u : Fin x.n) :
    case3ComponentRepEntry x Z u = u.1 ↔ u ∉ Z ∧ case3ComponentRepresentative x Z u = u.1 := by
  by_cases hu : u ∈ Z
  · simp only [case3ComponentRepEntry, hu, ↓reduceIte, not_true_eq_false, false_and, iff_false]
    exact ne_of_gt u.2
  · simp only [case3ComponentRepEntry, hu, ↓reduceIte, not_false_eq_true, true_and]

/-- The array of representative labels, with the sentinel at core vertices. -/
noncomputable def case3ComponentRepList (x : Alg81Input) (Z : Finset (Fin x.n)) : List ℕ :=
  List.ofFn (fun u => if u ∈ Z then x.n else case3ComponentRepresentative x Z u)

/-- There is one representative word per vertex. -/
theorem case3ComponentRepList_length (x : Alg81Input) (Z : Finset (Fin x.n)) :
    (case3ComponentRepList x Z).length = x.n := by
  simp only [case3ComponentRepList, List.length_ofFn]

/-- An outside seed has a matching representative, since it matches itself. -/
theorem case3ComponentRepresentative_lt (x : Alg81Input) (Z : Finset (Fin x.n))
    (u : Fin x.n) (hu : u ∉ Z) : case3ComponentRepresentative x Z u < x.n := by
  have hle := case3FirstIndex_le
    (fun v => v ∉ Z ∧ case3AttachmentRowSet x Z v = case3AttachmentRowSet x Z u)
  change case3ComponentRepresentative x Z u ≤ x.n at hle
  by_contra h
  have heq : case3ComponentRepresentative x Z u = x.n := by omega
  have hn := (case3FirstIndex_eq_sentinel_iff
    (fun v => v ∉ Z ∧ case3AttachmentRowSet x Z v = case3AttachmentRowSet x Z u)).mp heq
  exact hn u ⟨hu, rfl⟩

/-- The representative lies outside the core and has the same attachment set. -/
theorem case3ComponentRepresentative_spec (x : Alg81Input) (Z : Finset (Fin x.n))
    (u : Fin x.n) (hu : u ∉ Z) :
    let r : Fin x.n := ⟨case3ComponentRepresentative x Z u, case3ComponentRepresentative_lt x Z u hu⟩
    r ∉ Z ∧ case3AttachmentRowSet x Z r = case3AttachmentRowSet x Z u :=
  (case3FirstIndex_spec _ (case3ComponentRepresentative_lt x Z u hu)).1

/-- Equal attachment sets have the same least matching seed. -/
theorem case3ComponentRepresentative_eq_of_attachment_eq (x : Alg81Input)
    (Z : Finset (Fin x.n)) (u v : Fin x.n)
    (h : case3AttachmentRowSet x Z u = case3AttachmentRowSet x Z v) :
    case3ComponentRepresentative x Z u = case3ComponentRepresentative x Z v := by
  unfold case3ComponentRepresentative
  rw [h]

/-- For outside seeds, equal representatives mean exactly equal attachment sets. -/
theorem case3ComponentRepresentative_eq_iff (x : Alg81Input) (Z : Finset (Fin x.n))
    (u v : Fin x.n) (hu : u ∉ Z) (hv : v ∉ Z) :
    case3ComponentRepresentative x Z u = case3ComponentRepresentative x Z v ↔
      attachOf x Z u = attachOf x Z v := by
  constructor
  · intro h
    have hsU := (case3ComponentRepresentative_spec x Z u hu).2
    have hsV := (case3ComponentRepresentative_spec x Z v hv).2
    have hrep : (⟨case3ComponentRepresentative x Z u, case3ComponentRepresentative_lt x Z u hu⟩ : Fin x.n) =
        ⟨case3ComponentRepresentative x Z v, case3ComponentRepresentative_lt x Z v hv⟩ := Fin.ext h
    rw [hrep] at hsU
    have heq := hsU.symm.trans hsV
    simpa only [case3AttachmentRowSet_eq_attachOf x Z u hu,
      case3AttachmentRowSet_eq_attachOf x Z v hv] using heq
  · intro h
    apply case3ComponentRepresentative_eq_of_attachment_eq
    simpa only [case3AttachmentRowSet_eq_attachOf x Z u hu,
      case3AttachmentRowSet_eq_attachOf x Z v hv] using h

/-- Applying the representative choice twice leaves the same representative. -/
theorem case3ComponentRepresentative_idempotent (x : Alg81Input) (Z : Finset (Fin x.n))
    (u : Fin x.n) (hu : u ∉ Z) :
    case3ComponentRepresentative x Z
      ⟨case3ComponentRepresentative x Z u, case3ComponentRepresentative_lt x Z u hu⟩ =
        case3ComponentRepresentative x Z u :=
  case3ComponentRepresentative_eq_of_attachment_eq x Z _ u
    (case3ComponentRepresentative_spec x Z u hu).2

end GraphMinor.Compute
