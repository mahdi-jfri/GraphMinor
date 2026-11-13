module

public import GraphMinor.Compute.Case3StepsCoreMath
public import GraphMinor.Compute.Case3StepsSelectedMembers

/-!
# The program's selected family is a rural compass division

Every wall corner has a wall neighbor. The isolated boundary-vertex raw type
of (8.6) is therefore absent in the compact society written by the program.
The selected candidate family consequently equals its decoded division and
inherits rurality, with no additional hypothesis about raw types.
-/

public section

namespace GraphMinor.Compute

/-- A corner's wall neighbor excludes the isolated-vertex raw type in the
compact society used by the program in XIII (9.9), step 5, p. 105. -/
theorem case3CompactSocietyInput_noTypeIII {h n : ℕ} (D : MultiDigraph n)
    (W : WallOfHeight h D) (h2 : 2 ≤ h) (he : Even h) (hW : W.IsValid)
    (A : Alg86Subgraph (case3CompactSocietyInput D W h2 he hW).G) :
    ¬ IsAlg86TypeIII (case3CompactSocietyInput D W h2 he hW) A := by
  change ¬ ∃ v ∈ (List.ofFn (compactCorner W h2 he)).toFinset,
    (∀ w, ¬ (case3CompactCompassMultigraph D W).toSimpleGraph.Adj v w) ∧
      A.verts = {v} ∧ A.graph = ⊥
  rintro ⟨v, hv, hiso, _, _⟩
  have hv' : v ∈ List.ofFn (compactCorner W h2 he) := List.mem_toFinset.mp hv
  have hnb₀ := @exists_adj_of_mem_omega_case3Alg81Input h n D W
  have hnb₁ := hnb₀ h2
  have hnb₂ := hnb₁ he
  have hnb₃ := hnb₂ hW (u := v)
  obtain ⟨w, hadj⟩ := hnb₃ hv'
  apply hiso w
  change (case3CompactCompassMultigraph D W).toSimpleGraph.Adj v w
  rw [case3CompactCompassMultigraph_toSimpleGraph]
  exact hadj

/-- The selected members computed from a valid compact (8.6) output are
exactly its division, because wall corners are not isolated. -/
theorem case3CompactSelectedMembers_eq_div {h n : ℕ} (D : MultiDigraph n)
    (W : WallOfHeight h D) (h2 : 2 ≤ h) (he : Even h) (hW : W.IsValid)
    (d : Alg86DivisionOutput (case3CompactSocietyInput D W h2 he hW))
    (hd : IsValidAlg86DivisionOutput (case3CompactSocietyInput D W h2 he hW) d) :
    case3SelectedMembers (case3CompactSocietyInput D W h2 he hW) d.core.Z = d.div :=
  case3SelectedMembers_eq_div _ d hd (case3CompactSocietyInput_noTypeIII D W h2 he hW)

/-- Rurality of the program's computed compact member family follows from
validity of the supplied (8.6) output. -/
theorem case3CompactSelectedMembers_isRuralDivision {h n : ℕ} (D : MultiDigraph n)
    (W : WallOfHeight h D) (h2 : 2 ≤ h) (he : Even h) (hW : W.IsValid)
    (d : Alg86DivisionOutput (case3CompactSocietyInput D W h2 he hW))
    (hd : IsValidAlg86DivisionOutput (case3CompactSocietyInput D W h2 he hW) d) :
    GM13.IsRuralDivision (case3CompactSocietyInput D W h2 he hW).toSociety
      (Alg86Subgraph.toGMGraph '' case3SelectedMembers (case3CompactSocietyInput D W h2 he hW) d.core.Z) :=
  case3SelectedMembers_isRuralDivision _ d hd (case3CompactSocietyInput_noTypeIII D W h2 he hW)

end GraphMinor.Compute
