module

public import GraphMinor.Compute.Case3StepsGroups
import GraphMinor.Compute.Case3StepsReadCoreEdgeProg
import GraphMinor.Compute.Case3StepsPairKey

/-!
# The selected candidates cover exactly the raw boundaries

Every component boundary is represented by its least matching seed. A core
edge either joins such a component group or retains its own edge candidate.
The selected candidates are unique for each boundary, implementing precisely
the equivalence classes in the description of XIII (8.6), page 96.
-/

public section

namespace GraphMinor.Compute

open Classical

private theorem group_exists_of_component (x : Alg81Input) (Z : Finset (Fin x.n))
    (u : Fin x.n) (hu : u ∉ Z) (bd : Finset (Fin x.n)) (hbd : attachOf x Z u = bd) :
    ∃ i : Case3RawIndex x, case3GroupActive x Z i ∧ case3GroupBoundary x Z i = bd := by
  let r : Fin x.n := ⟨case3ComponentRepresentative x Z u, case3ComponentRepresentative_lt x Z u hu⟩
  have hs := case3ComponentRepresentative_spec x Z u hu
  refine ⟨.inl r, (case3GroupActive_inl_iff x Z r).mpr ⟨hs.1, ?_⟩, ?_⟩
  · exact case3ComponentRepresentative_idempotent x Z u hu
  · exact hs.2.trans ((case3AttachmentRowSet_eq_attachOf x Z u hu).trans hbd)

private theorem group_exists_of_ordered_edge (x : Alg81Input) (Z : Finset (Fin x.n))
    (u v : Fin x.n) (hu : u ∈ Z) (hv : v ∈ Z) (huv : u < v) (hadj : x.G.Adj u v)
    (hnone : ∀ z : Fin x.n, ¬ (z ∉ Z ∧ attachOf x Z z = {u, v})) :
    ∃ i : Case3RawIndex x, case3GroupActive x Z i ∧ case3GroupBoundary x Z i = {u, v} := by
  have hmem : (u, v) ∈ case3InputEdges x := (mem_edgeListOf x.G _).mpr ⟨huv, hadj⟩
  obtain ⟨k, hk, hget⟩ := List.mem_iff_getElem.mp hmem
  let j : Fin (case3InputEdges x).length := ⟨k, hk⟩
  refine ⟨.inr j, (case3GroupActive_inr_iff x Z j).mpr ?_, ?_⟩
  · change ((((case3InputEdges x)[k]).1 ∈ Z ∧ ((case3InputEdges x)[k]).2 ∈ Z) ∧ _)
    rw [hget]
    refine ⟨⟨hu, hv⟩, ?_⟩
    intro z hz
    exact hnone z ⟨hz.1, (case3AttachmentRowSet_eq_attachOf x Z z hz.1).symm.trans hz.2⟩
  · change {((case3InputEdges x)[k]).1, ((case3InputEdges x)[k]).2} = _
    rw [hget]

/-- Every raw boundary in (8.6) has a selected representative candidate. -/
theorem case3IsRawBoundary_iff_exists_group (x : Alg81Input) (Z bd : Finset (Fin x.n)) :
    IsRawBoundary x Z bd ↔
      ∃ i : Case3RawIndex x, case3GroupActive x Z i ∧ case3GroupBoundary x Z i = bd := by
  constructor
  · intro hraw
    by_cases hcomp : ∃ u : Fin x.n, u ∉ Z ∧ attachOf x Z u = bd
    · obtain ⟨u, hu, hbd⟩ := hcomp
      exact group_exists_of_component x Z u hu bd hbd
    · rcases hraw with hcomp' | ⟨u, v, hu, hv, hadj, rfl⟩
      · exact False.elim (hcomp hcomp')
      · have hne : u ≠ v := by
          intro h
          subst v
          exact x.G.loopless.irrefl u hadj
        have hnone : ∀ z : Fin x.n, ¬ (z ∉ Z ∧ attachOf x Z z = {u, v}) :=
          fun z hz => hcomp ⟨z, hz⟩
        rcases lt_or_gt_of_ne hne with huv | hvu
        · exact group_exists_of_ordered_edge x Z u v hu hv huv hadj hnone
        · have hnone' : ∀ z : Fin x.n, ¬ (z ∉ Z ∧ attachOf x Z z = {v, u}) := by
            simpa only [Finset.pair_comm v u] using hnone
          simpa only [Finset.pair_comm v u] using
            group_exists_of_ordered_edge x Z v u hv hu hvu hadj.symm hnone'
  · rintro ⟨i, hi, hbd⟩
    exact hbd ▸ case3GroupActive_isRawBoundary x Z i hi

/-- Distinct selected candidates have distinct boundaries, just as the
merged members of (8.6) do. -/
theorem case3GroupBoundary_injective_on_active (x : Alg81Input) (Z : Finset (Fin x.n))
    (i j : Case3RawIndex x) (hi : case3GroupActive x Z i) (hj : case3GroupActive x Z j)
    (heq : case3GroupBoundary x Z i = case3GroupBoundary x Z j) : i = j := by
  cases i <;> cases j
  · rename_i u v
    have hu := (case3GroupActive_inl_iff x Z u).mp hi
    have hv := (case3GroupActive_inl_iff x Z v).mp hj
    have hrep := case3ComponentRepresentative_eq_of_attachment_eq x Z u v heq
    rw [hu.2, hv.2] at hrep
    exact congrArg Sum.inl (Fin.ext hrep)
  · rename_i u j
    have hu := (case3GroupActive_inl_iff x Z u).mp hi
    have hj' := (case3GroupActive_inr_iff x Z j).mp hj
    exact False.elim (hj'.2 u ⟨hu.1, heq⟩)
  · rename_i j u
    have hu := (case3GroupActive_inl_iff x Z u).mp hj
    have hj' := (case3GroupActive_inr_iff x Z j).mp hi
    exact False.elim (hj'.2 u ⟨hu.1, heq.symm⟩)
  · rename_i j k
    let e := (case3InputEdges x)[j.1]
    let f := (case3InputEdges x)[k.1]
    have he : e.1 < e.2 := (case3InputEdges_get_spec x j).1
    have hf : f.1 < f.2 := (case3InputEdges_get_spec x k).1
    change {e.1, e.2} = {f.1, f.2} at heq
    have hkeys := congrArg case3BoundaryKey heq
    rw [case3BoundaryKey_pair e.1 e.2 he, case3BoundaryKey_pair f.1 f.2 hf] at hkeys
    have htail := (List.cons.inj hkeys).2
    have hu := (List.cons.inj htail).1
    have hv := (List.cons.inj (List.cons.inj htail).2).1
    have hef : e = f := Prod.ext (Fin.ext hu) (Fin.ext hv)
    have hidx : j.1 = k.1 := (nodup_edgeListOf x.G).getElem_inj.mp hef
    exact congrArg Sum.inr (Fin.ext hidx)

end GraphMinor.Compute
