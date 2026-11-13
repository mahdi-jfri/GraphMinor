module

public import GraphMinor.Compute.Case3StepsScanRecords

/-!
# Distinct members remain distinct in the record list

A selected member's record lists exactly its original-label vertex image.
Different selected boundaries give different intersections of those vertex
sets with the core. Thus distinct selected candidates have different
record vertex sets, regardless of the branch code stored beside them.
-/

public section

namespace GraphMinor.Compute

open GraphMinor.Transport

/-- The record vertex set is the original-label image of the selected vertices. -/
theorem case3SelectedRecord_vertexFinset {N : ℕ} (x : Alg81Input)
    (D : MultiDigraph x.n) (Z : Finset (Fin x.n)) (e : Fin x.n ↪ Fin N)
    (i : Case3SelectedGroup x Z) (code : List ℕ) :
    (case3SelectedRecord x D Z e i code).vList.toFinset =
      ((case3SelectedMember x Z i).verts.image e).image Fin.val := by
  classical
  let A := case3SelectedMember x Z i
  let orig := e ∘ A.verts.orderEmbOfFin rfl
  have hinj := e.injective.comp (A.verts.orderEmbOfFin rfl).injective
  change ((case3BranchRecord _ (origVertexEmb orig hinj) _ code).vList).toFinset = _
  ext v
  simp only [case3BranchRecord, List.mem_toFinset, List.mem_map, Finset.mem_image]
  constructor
  · rintro ⟨u, _, rfl⟩
    rw [origVertexEmb_apply_val]
    exact ⟨e (A.verts.orderEmbOfFin rfl u),
      ⟨A.verts.orderEmbOfFin rfl u, A.verts.orderEmbOfFin_mem rfl u, rfl⟩, rfl⟩
  · rintro ⟨_, ⟨u, hu, rfl⟩, rfl⟩
    obtain ⟨q, hq⟩ := (show u ∈ Set.range (A.verts.orderEmbOfFin rfl) from
      (A.verts.range_orderEmbOfFin rfl).symm ▸ hu)
    refine ⟨q, List.mem_finRange _, ?_⟩
    rw [origVertexEmb_apply_val]
    exact congrArg (fun z => (e z).1) hq

/-- Equality of record vertex sets forces equality of the selected candidates. -/
theorem case3SelectedRecord_eq_candidate_of_vertices {N : ℕ} (x : Alg81Input)
    (D : MultiDigraph x.n) (Z : Finset (Fin x.n)) (e : Fin x.n ↪ Fin N)
    (i j : Case3SelectedGroup x Z) (ci cj : List ℕ)
    (h : (case3SelectedRecord x D Z e i ci).vList.toFinset =
      (case3SelectedRecord x D Z e j cj).vList.toFinset) : i = j := by
  classical
  rw [case3SelectedRecord_vertexFinset, case3SelectedRecord_vertexFinset] at h
  have hv := Finset.image_injective e.injective (Finset.image_injective Fin.val_injective h)
  apply Subtype.ext
  apply case3GroupBoundary_injective_on_active x Z i.1 j.1 i.2 j.2
  rw [← case3SelectedMember_inter_core x Z i, ← case3SelectedMember_inter_core x Z j, hv]

/-- A history with no repeated candidate passes the parser's member
identity check, even when some records use placeholder trees. -/
theorem case3SelectedRecordList_distinct {N : ℕ} (x : Alg81Input)
    (D : MultiDigraph x.n) (Z : Finset (Fin x.n)) (e : Fin x.n ↪ Fin N)
    (entries : List (Case3SelectedGroup x Z × List ℕ)) (hn : (entries.map Prod.fst).Nodup) :
    ((case3SelectedRecordList x D Z e entries).map
      (fun r => (r.vList.toFinset, r.eList.toFinset))).Nodup := by
  classical
  induction entries with
  | nil => simp [case3SelectedRecordList]
  | cons p entries ih =>
    have hp := List.nodup_cons.mp hn
    simp only [case3SelectedRecordList, List.map_cons, List.nodup_cons]
    refine ⟨?_, ih hp.2⟩
    intro h
    obtain ⟨q, hq, heq⟩ := List.mem_map.mp h
    obtain ⟨q', hq', rfl⟩ := List.mem_map.mp hq
    have heq' := congrArg Prod.fst heq
    have hid := case3SelectedRecord_eq_candidate_of_vertices x D Z e q'.1 p.1 q'.2 p.2 heq'
    exact hp.1 (hid ▸ List.mem_map_of_mem hq')

end GraphMinor.Compute
