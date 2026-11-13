module

public import GraphMinor.GM02.SidePieceIndex

/-!
# Terminations formed by side pieces

Take the endpoint pair of each maximal path run assigned to a fixed side.
The original linkage and the alternating-run disjointness lemma ensure
that distinct pairs have disjoint endpoints. Each pair has distinct ends
and lies in the original graph. This constructs the two terminations in
the forward implication of corrected II (2.9), without assuming their
matching properties.
-/

@[expose] public section
namespace GraphMinor.GM02
open Graph SimpleGraph List Set Classical
universe u v
variable {α : Type u} {β : Type v} {S : Set α} (A : Termination S) (G H : Graph α β)
variable (P : ∀ p : {p // p ∈ A.pairs}, PairPath (pathGraph G) p.val)
variable (hP : ∀ p q, p ≠ q → Disjoint (P p).vertices (P q).vertices)

/-- The termination consisting of endpoint pairs of all pieces on one side. -/
noncomputable def sideTermination (side : Bool) : Termination V(G) := by
  let J := {i : RunPieceIndex A G H P // i.color A G H P = side}
  let _ : Fintype J := Fintype.ofFinite J
  refine { pairs := Finset.univ.image (fun j : J => j.val.pair A G H P)
           not_diag := ?_, vertex_mem := ?_, disjoint := ?_ }
  · intro e he
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.1 he
    exact i.val.pair_not_diag A G H P
  · intro e he a hae
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.1 he
    exact (i.val.path A G H P).vertices_subset (i.val.pair_not_diag A G H P)
      ((i.val.path A G H P).endpoint_mem hae)
  · intro e he f hf hef
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.1 he
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.1 hf
    have hij : i.val ≠ j.val := fun h => hef (congrArg (fun k => k.pair A G H P) h)
    have hdis := RunPieceIndex.same_color_disjoint A G H P hP i.val j.val hij
      (i.property.trans j.property.symm)
    apply Set.disjoint_left.2
    intro a hai haj
    exact Set.disjoint_left.1 hdis ((i.val.path A G H P).endpoint_mem hai)
      ((j.val.path A G H P).endpoint_mem haj)

/-- The pairs of a side termination are precisely the pairs of pieces
with that side color. -/
theorem mem_sideTermination_pairs (side : Bool) (e : Sym2 α) :
    e ∈ (sideTermination A G H P hP side).pairs ↔
      ∃ i : RunPieceIndex A G H P, i.color A G H P = side ∧ i.pair A G H P = e := by
  simp only [sideTermination, Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨i, hi⟩
    exact ⟨i.val, i.property, hi⟩
  · rintro ⟨i, hside, hi⟩
    exact ⟨⟨i, hside⟩, hi⟩

/-- The support of a side termination is exactly the endpoints of its pieces. -/
theorem mem_sideTermination_support (side : Bool) (a : α) :
    a ∈ (sideTermination A G H P hP side).support ↔
      ∃ i : RunPieceIndex A G H P, i.color A G H P = side ∧ a ∈ i.pair A G H P := by
  constructor
  · intro ha
    obtain ⟨e, hea⟩ := Set.mem_iUnion.1 ha
    obtain ⟨he, hae⟩ := Set.mem_iUnion.1 hea
    obtain ⟨i, hc, hi⟩ := (mem_sideTermination_pairs A G H P hP side e).1 he
    exact ⟨i, hc, hi.symm ▸ hae⟩
  · rintro ⟨i, hc, hai⟩
    exact Set.mem_iUnion.2 ⟨i.pair A G H P, Set.mem_iUnion.2
      ⟨(mem_sideTermination_pairs A G H P hP side _).2 ⟨i, hc, rfl⟩, hai⟩⟩

include hP in
/-- Equal-colored pieces are uniquely determined by their endpoint pair,
since two distinct such pieces have disjoint nonempty vertex supports. -/
theorem RunPieceIndex.eq_of_pair_eq (i j : RunPieceIndex A G H P)
    (hc : i.color A G H P = j.color A G H P) (he : i.pair A G H P = j.pair A G H P) : i = j := by
  by_contra hne
  have hdis := RunPieceIndex.same_color_disjoint A G H P hP i j hne hc
  have hai : (i.path A G H P).start ∈ i.pair A G H P :=
    (congrArg (fun e => (i.path A G H P).start ∈ e) (i.path A G H P).ends_eq).mp
      (Sym2.mem_mk_left _ _)
  have haj : (i.path A G H P).start ∈ j.pair A G H P := he ▸ hai
  exact Set.disjoint_left.1 hdis ((i.path A G H P).endpoint_mem hai)
    ((j.path A G H P).endpoint_mem haj)

end GraphMinor.GM02
