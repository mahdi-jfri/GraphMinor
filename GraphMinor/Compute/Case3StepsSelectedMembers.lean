module

public import GraphMinor.Compute.Case3StepsGroupCoverage
public import GraphMinor.Compute.Case3StepsDivision

/-!
# The merged members selected by the group-label arrays

A selected candidate specifies one raw boundary. Its member is the union of
all raw members with that boundary, as in XIII (8.6), page 96. Coverage and
uniqueness of the selected boundaries identify this finite family exactly
with the division returned by the valid (8.6) output.
-/

@[expose] public section

namespace GraphMinor.Compute

/-- A selected candidate, carrying only its computed self-representative test. -/
abbrev Case3SelectedGroup (x : Alg81Input) (Z : Finset (Fin x.n)) :=
  {i : Case3RawIndex x // case3GroupActive x Z i}

/-- The merged simple member specified by a selected boundary. -/
noncomputable def case3SelectedMember (x : Alg81Input) (Z : Finset (Fin x.n))
    (i : Case3SelectedGroup x Z) : Alg86Subgraph x.G :=
  mergedMemberOfBoundary x Z (case3GroupBoundary x Z i.1)
    (case3GroupActive_isRawBoundary x Z i.1 i.2).subset_Z

/-- All selected merged members. -/
noncomputable def case3SelectedMembers (x : Alg81Input) (Z : Finset (Fin x.n)) :
    Set (Alg86Subgraph x.G) := Set.range (case3SelectedMember x Z)

/-- Only finitely many selected members occur. -/
theorem case3SelectedMembers_finite (x : Alg81Input) (Z : Finset (Fin x.n)) :
    (case3SelectedMembers x Z).Finite := Set.finite_range _

/-- The core part of a selected member is exactly its selected boundary. -/
theorem case3SelectedMember_inter_core (x : Alg81Input) (Z : Finset (Fin x.n))
    (i : Case3SelectedGroup x Z) :
    (case3SelectedMember x Z i).verts ∩ Z = case3GroupBoundary x Z i.1 :=
  verts_inter_Z_mergedMemberOfBoundary x Z _ _

/-- Distinct selected candidates produce distinct merged members. -/
theorem case3SelectedMember_injective (x : Alg81Input) (Z : Finset (Fin x.n)) :
    Function.Injective (case3SelectedMember x Z) := by
  intro i j heq
  apply Subtype.ext
  apply case3GroupBoundary_injective_on_active x Z i.1 j.1 i.2 j.2
  have hcore := congrArg (fun A : Alg86Subgraph x.G => A.verts ∩ Z) heq
  simpa only [case3SelectedMember_inter_core] using hcore

/-- Selecting one candidate for each boundary gives precisely the unions of
boundary-equivalence classes in (8.6). The isolated-vertex raw type is absent
in the wall society to which step (5) applies. -/
theorem case3SelectedMembers_eq_alg86Division {x : Alg81Input}
    {Z : Finset (Fin x.n)} {C : SimpleGraph (Fin x.n)}
    (htrace : Alg83Trace x Z C) (h4 : IsFourLinkedCore x.omega Z C)
    (hnocross : ¬ HasCrossInSociety x.G x.omega)
    (hnoIII : ∀ A : Alg86Subgraph x.G, ¬ IsAlg86TypeIII x A) :
    case3SelectedMembers x Z = alg86Division x Z := by
  ext B
  rw [mem_alg86Division_iff_exists_isRawBoundary htrace h4 hnocross hnoIII]
  constructor
  · rintro ⟨i, rfl⟩
    exact ⟨_, case3GroupActive_isRawBoundary x Z i.1 i.2, rfl⟩
  · rintro ⟨bd, hbd, hB⟩
    obtain ⟨i, hi, hbi⟩ := (case3IsRawBoundary_iff_exists_group x Z bd).mp hbd
    subst bd
    exact ⟨⟨i, hi⟩, hB.symm⟩

/-- The computed selected family is the division in the valid decoded output. -/
theorem case3SelectedMembers_eq_div (x : Alg81Input) (d : Alg86DivisionOutput x)
    (hd : IsValidAlg86DivisionOutput x d)
    (hnoIII : ∀ A : Alg86Subgraph x.G, ¬ IsAlg86TypeIII x A) :
    case3SelectedMembers x d.core.Z = d.div := by
  rw [(case3Alg86Division_families hd).2]
  have hcore := hd.2.2.1
  exact case3SelectedMembers_eq_alg86Division hcore.2.2.1 hcore.2.2.2.2.2.1 hd.1 hnoIII

/-- The selected member family inherits the returned rural division. -/
theorem case3SelectedMembers_isRuralDivision (x : Alg81Input) (d : Alg86DivisionOutput x)
    (hd : IsValidAlg86DivisionOutput x d)
    (hnoIII : ∀ A : Alg86Subgraph x.G, ¬ IsAlg86TypeIII x A) :
    GM13.IsRuralDivision x.toSociety (Alg86Subgraph.toGMGraph '' case3SelectedMembers x d.core.Z) := by
  rw [case3SelectedMembers_eq_div x d hd hnoIII]
  exact hd.2.2.2.2.2.2.2.2

end GraphMinor.Compute
