module

public import GraphMinor.Compute.Case3StepsSelectedEdges

/-!
# Routing outside vertices to their selected group

The representative table supplies the unique selected group containing an
outside vertex. Its incident simple edges belong to that same group by the
edge test. This gives the component part of the routing used in Graph Minors
XIII, (9.9), step 5, p. 105.
-/

@[expose] public section

namespace GraphMinor.Compute

/-- The selected group obtained directly from an outside vertex's representative. -/
noncomputable def case3ComponentOwner (x : Alg81Input) (Z : Finset (Fin x.n))
    (u : Fin x.n) (hu : u ∉ Z) : Case3SelectedGroup x Z :=
  ⟨.inl ⟨case3ComponentRepresentative x Z u, case3ComponentRepresentative_lt x Z u hu⟩,
    (case3GroupActive_inl_iff x Z _).mpr
      ⟨(case3ComponentRepresentative_spec x Z u hu).1,
        case3ComponentRepresentative_idempotent x Z u hu⟩⟩

/-- The owner's numeric label is exactly the table entry. -/
theorem case3ComponentOwner_label (x : Alg81Input) (Z : Finset (Fin x.n))
    (u : Fin x.n) (hu : u ∉ Z) :
    case3RawIndexLabel x (case3ComponentOwner x Z u hu).1 =
      case3ComponentRepresentative x Z u := rfl

/-- The owner has the outside vertex's attachment boundary. -/
theorem case3ComponentOwner_boundary (x : Alg81Input) (Z : Finset (Fin x.n))
    (u : Fin x.n) (hu : u ∉ Z) :
    case3GroupBoundary x Z (case3ComponentOwner x Z u hu).1 = attachOf x Z u := by
  exact (case3ComponentRepresentative_spec x Z u hu).2.trans
    (case3AttachmentRowSet_eq_attachOf x Z u hu)

/-- The outside vertex belongs to the group selected by its table entry. -/
theorem case3ComponentOwner_contains (x : Alg81Input) (Z : Finset (Fin x.n))
    (u : Fin x.n) (hu : u ∉ Z) :
    u ∈ (case3SelectedMember x Z (case3ComponentOwner x Z u hu)).verts :=
  (case3SelectedMember_mem_outside_iff x Z _ u hu).mpr rfl

/-- No other selected group contains the same outside vertex. -/
theorem case3ComponentOwner_unique (x : Alg81Input) (Z : Finset (Fin x.n))
    (u : Fin x.n) (hu : u ∉ Z) (i : Case3SelectedGroup x Z) :
    u ∈ (case3SelectedMember x Z i).verts ↔ i = case3ComponentOwner x Z u hu := by
  rw [case3SelectedMember_mem_outside_iff x Z i u hu]
  constructor
  · intro h
    apply Subtype.ext
    apply case3RawIndexLabel_injective x
    exact h.symm
  · rintro rfl
    rfl

/-- Every incident edge routes to the outside endpoint's owner and nowhere else. -/
theorem case3ComponentOwner_edge_iff (x : Alg81Input) (Z : Finset (Fin x.n))
    (u v : Fin x.n) (hu : u ∉ Z) (hadj : x.G.Adj u v)
    (i : Case3SelectedGroup x Z) :
    (case3SelectedMember x Z i).graph.Adj u v ↔ i = case3ComponentOwner x Z u hu := by
  rw [case3SelectedMember_adj_outside_iff x Z i u v hu hadj,
    ← case3SelectedMember_mem_outside_iff x Z i u hu,
    case3ComponentOwner_unique x Z u hu i]

end GraphMinor.Compute
