module

public import GraphMinor.Compute.Case3StepsPairSelection
public import GraphMinor.Compute.MultiDigraph

/-!
# The multigraph member selected by computed pair owners

A member retains the full input multiplicity at precisely the pairs carrying
its label. Its positive pair list is the corresponding ordered input filter.
For a simple society this is exactly the previously proved edge lift with
the first-containing-member loop assignment.
-/

@[expose] public section

namespace GraphMinor.Compute

/-- Keep a complete directed parallel class precisely at its computed owner. -/
noncomputable def case3RoutedMember (x : Alg81Input) (D : MultiDigraph x.n)
    (Z : Finset (Fin x.n)) (label : ℕ) : MultiDigraph x.n where
  edgeMult u v := if case3PairOwner x Z u v = label then D.edgeMult u v else 0

/-- Routing keeps each input parallel class whole or removes it. -/
theorem case3RoutedMember_le (x : Alg81Input) (D : MultiDigraph x.n)
    (Z : Finset (Fin x.n)) (label : ℕ) : case3RoutedMember x D Z label ≤ D := by
  intro u v
  change (if case3PairOwner x Z u v = label then D.edgeMult u v else 0) ≤ D.edgeMult u v
  split_ifs
  · exact le_rfl
  · exact Nat.zero_le _

/-- The routed positive pairs are exactly the input's ordered owner filter. -/
theorem case3RoutedMember_activePairs (x : Alg81Input) (D : MultiDigraph x.n)
    (Z : Finset (Fin x.n)) (label : ℕ) :
    (case3RoutedMember x D Z label).activePairsList =
      D.activePairsList.filter (fun p => decide (case3PairOwner x Z p.1 p.2 = label)) := by
  classical
  simp only [MultiDigraph.activePairsList, List.filter_filter]
  apply List.filter_congr
  intro p _
  by_cases h : case3PairOwner x Z p.1 p.2 = label <;>
    simp only [case3RoutedMember, h, ↓reduceIte, decide_true, decide_false,
      Bool.true_and, Bool.false_and, Nat.not_lt_zero]

private theorem routed_flatTriples (x : Alg81Input) (D : MultiDigraph x.n)
    (Z : Finset (Fin x.n)) (label : ℕ) (pairs : List (Fin x.n × Fin x.n))
    (hsel : ∀ p ∈ pairs, case3PairOwner x Z p.1 p.2 = label) :
    MultiDigraph.flatTriples (case3RoutedMember x D Z label) pairs = MultiDigraph.flatTriples D pairs := by
  induction pairs with
  | nil => rfl
  | cons p ps ih =>
    simp only [MultiDigraph.flatTriples, case3RoutedMember, hsel p List.mem_cons_self, ↓reduceIte]
    have htail := ih (fun q hq => hsel q (List.mem_cons_of_mem _ hq))
    simp only [case3RoutedMember] at htail
    rw [htail]

/-- The member encoding copies full input triples in their canonical order. -/
theorem case3RoutedMember_enc (x : Alg81Input) (D : MultiDigraph x.n)
    (Z : Finset (Fin x.n)) (label : ℕ) :
    (case3RoutedMember x D Z label).enc =
      [x.n, (D.activePairsList.filter (fun p => decide (case3PairOwner x Z p.1 p.2 = label))).length] ++
        MultiDigraph.flatTriples D
          (D.activePairsList.filter (fun p => decide (case3PairOwner x Z p.1 p.2 = label))) := by
  classical
  unfold MultiDigraph.enc MultiDigraph.numActivePairs
  rw [case3RoutedMember_activePairs, routed_flatTriples]
  intro p hp
  exact of_decide_eq_true (List.mem_filter.mp hp).2

/-- Computed owner routing gives exactly the multigraph lift with the ordered
loop assignment, including all original multiplicities. -/
theorem case3RoutedMember_eq_lift {n : ℕ} (D : MultiDigraph n)
    (omega : List (Fin n)) (homega : omega.Nodup) (Z : Finset (Fin n))
    (hdiv : GM13.IsSocietyDivision (case3SimpleSocietyInput D omega homega).toSociety
      (Alg86Subgraph.toGMGraph '' case3SelectedMembers (case3SimpleSocietyInput D omega homega) Z))
    (i : Case3SelectedGroup (case3SimpleSocietyInput D omega homega) Z) :
    case3RoutedMember (case3SimpleSocietyInput D omega homega) D Z
      (case3RawIndexLabel (case3SimpleSocietyInput D omega homega) i.1) =
      case3MemberMultiDigraph D (case3SelectedMember (case3SimpleSocietyInput D omega homega) Z i)
        (case3AssignedLoops (case3OrderedLoopAssignment (case3SimpleSocietyInput D omega homega) Z hdiv)
          (case3SelectedMember (case3SimpleSocietyInput D omega homega) Z i)) := by
  classical
  let x := case3SimpleSocietyInput D omega homega
  ext u v
  rw [case3MemberMultiDigraph_edgeMult]
  by_cases hp : 0 < D.edgeMult u v
  · have hvalid : u = v ∨ x.G.Adj u v := by
      by_cases he : u = v
      · exact Or.inl he
      · right
        exact (MultiDigraph.toSimpleGraph_adj D u v).mpr ⟨he, Or.inl hp⟩
    have hs := case3PairOwner_selection_iff x Z hdiv u v hvalid i
    dsimp only [x] at hs
    simp only [case3RoutedMember]
    simp only [hs]
  · have hz : D.edgeMult u v = 0 := by omega
    simp only [case3RoutedMember, hz, ite_self]

end GraphMinor.Compute
