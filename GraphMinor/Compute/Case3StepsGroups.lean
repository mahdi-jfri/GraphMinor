module

public import GraphMinor.Compute.Case3StepsRepresentatives
public import GraphMinor.Compute.Case3StepsCoreEdgeRepresentatives

/-!
# Selecting the distinct boundary groups

Component candidates use vertex indices and core-edge candidates use simple
edge indices. A candidate is selected when its computed representative is
its own label. Its boundary is either a component attachment set or the
endpoint pair of a core edge. These are the raw boundary types of (8.6).
-/

@[expose] public section

namespace GraphMinor.Compute

open Classical

/-- Candidate indices for component and core-edge raw members. -/
abbrev Case3RawIndex (x : Alg81Input) := Fin x.n ⊕ Fin (case3InputEdges x).length

/-- The disjoint numeric label ranges used by the two representative arrays. -/
def case3RawIndexLabel (x : Alg81Input) : Case3RawIndex x → ℕ
  | .inl u => u.1
  | .inr j => x.n + j.1

/-- Every candidate label lies below the common sentinel. -/
theorem case3RawIndexLabel_lt (x : Alg81Input) (i : Case3RawIndex x) :
    case3RawIndexLabel x i < x.n + (case3InputEdges x).length := by
  cases i with
  | inl u => have h := u.2; change u.1 < _; omega
  | inr j => have h := j.2; change x.n + j.1 < _; omega

/-- Distinct candidates have distinct numeric labels. -/
theorem case3RawIndexLabel_injective (x : Alg81Input) : Function.Injective (case3RawIndexLabel x) := by
  intro i j heq
  cases i <;> cases j
  · rename_i u v
    exact congrArg Sum.inl (Fin.ext heq)
  · rename_i u j
    change u.1 = x.n + j.1 at heq
    have h := u.2
    omega
  · rename_i j u
    change x.n + j.1 = u.1 at heq
    have h := u.2
    omega
  · rename_i j k
    change x.n + j.1 = x.n + k.1 at heq
    exact congrArg Sum.inr (Fin.ext (by omega))

/-- The boundary represented by a component or edge candidate. -/
noncomputable def case3GroupBoundary (x : Alg81Input) (Z : Finset (Fin x.n)) :
    Case3RawIndex x → Finset (Fin x.n)
  | .inl u => case3AttachmentRowSet x Z u
  | .inr j => {((case3InputEdges x)[j.1]).1, ((case3InputEdges x)[j.1]).2}

/-- A candidate is selected when its representative word is its own label. -/
def case3GroupActive (x : Alg81Input) (Z : Finset (Fin x.n)) : Case3RawIndex x → Prop
  | .inl u => case3ComponentRepEntry x Z u = u.1
  | .inr j => case3CoreEdgeRepEntry x Z j = x.n + j.1

/-- The selected candidates, one for each distinct raw-member boundary. -/
noncomputable def case3GroupSeeds (x : Alg81Input) (Z : Finset (Fin x.n)) : Finset (Case3RawIndex x) :=
  Finset.univ.filter (case3GroupActive x Z)

/-- Selected component candidates lie outside the core and represent themselves. -/
theorem case3GroupActive_inl_iff (x : Alg81Input) (Z : Finset (Fin x.n)) (u : Fin x.n) :
    case3GroupActive x Z (.inl u) ↔ u ∉ Z ∧ case3ComponentRepresentative x Z u = u.1 :=
  case3ComponentRepEntry_eq_own_iff x Z u

/-- Selected edge candidates are core edges whose boundary has no component match. -/
theorem case3GroupActive_inr_iff (x : Alg81Input) (Z : Finset (Fin x.n))
    (j : Fin (case3InputEdges x).length) :
    case3GroupActive x Z (.inr j) ↔
      (let e := (case3InputEdges x)[j.1]
       (e.1 ∈ Z ∧ e.2 ∈ Z) ∧
         ∀ z : Fin x.n, ¬ (z ∉ Z ∧ case3AttachmentRowSet x Z z = {e.1, e.2})) :=
  case3CoreEdgeRepEntry_eq_own_iff x Z j

/-- The candidate set tests exactly the computed self-representative condition. -/
theorem mem_case3GroupSeeds (x : Alg81Input) (Z : Finset (Fin x.n)) (i : Case3RawIndex x) :
    i ∈ case3GroupSeeds x Z ↔ case3GroupActive x Z i := by
  simp only [case3GroupSeeds, Finset.mem_filter, Finset.mem_univ, true_and]

/-- Every candidate boundary has at most three vertices for a valid (8.6) core. -/
theorem case3GroupBoundary_card_le_three (x : Alg81Input) (d : Alg86DivisionOutput x)
    (hd : IsValidAlg86DivisionOutput x d) (i : Case3RawIndex x) :
    (case3GroupBoundary x d.core.Z i).card ≤ 3 := by
  cases i with
  | inl u => exact case3AttachmentRowSet_card_le_three x d hd u
  | inr j =>
    have he := ((mem_edgeListOf x.G _).mp (List.getElem_mem j.2)).1
    change ({((case3InputEdges x)[j.1]).1, ((case3InputEdges x)[j.1]).2} : Finset (Fin x.n)).card ≤ 3
    have hne : ((case3InputEdges x)[j.1]).1 ≠ ((case3InputEdges x)[j.1]).2 := by
      intro h
      exact ne_of_lt he (congrArg Fin.val h)
    rw [Finset.card_pair hne]
    decide

/-- Every selected candidate has one of the two raw-member boundaries in (8.6). -/
theorem case3GroupActive_isRawBoundary (x : Alg81Input) (Z : Finset (Fin x.n))
    (i : Case3RawIndex x) (hi : case3GroupActive x Z i) :
    IsRawBoundary x Z (case3GroupBoundary x Z i) := by
  cases i with
  | inl u =>
    have hu := (case3GroupActive_inl_iff x Z u).mp hi
    exact Or.inl ⟨u, hu.1, (case3AttachmentRowSet_eq_attachOf x Z u hu.1).symm⟩
  | inr j =>
    have he := (case3GroupActive_inr_iff x Z j).mp hi
    have hadj := ((mem_edgeListOf x.G _).mp (List.getElem_mem j.2)).2
    exact Or.inr ⟨_, _, he.1.1, he.1.2, hadj, rfl⟩

end GraphMinor.Compute
