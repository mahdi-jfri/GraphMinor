module

public import GraphMinor.Compute.GM06Alg34GapRetainedPositions

/-!
# Exact region labels at retained gap positions

A nonrepeating cuff list identifies each vertex/region pair in its zip
with the region at that vertex's old position. Projecting the filtered
pairs gives the retained vertex list. Thus every updated gap slot is
exactly the reindexed old region at its selected old cuff position.
-/

public section
namespace GraphMinor.Compute

/-- A region paired with a listed vertex is exactly the region at that vertex's position. -/
theorem gm06ZipOfFn_snd {α β : Type*} [DecidableEq α] {L : List α}
    (hL : L.Nodup) (g : Fin L.length → β) (i : Fin L.length) {a : β}
    (hm : (L.get i, a) ∈ L.zip (List.ofFn g)) : a = g i := by
  obtain ⟨k, hk⟩ := List.mem_iff_get.mp hm
  have hklen : k.val < L.length := by
    have hh := k.isLt
    simpa only [List.length_zip, List.length_ofFn, Nat.min_self] using hh
  let j : Fin L.length := ⟨k.val, hklen⟩
  have hget : (L.zip (List.ofFn g)).get k = (L.get j, g j) := by
    simp only [List.get_eq_getElem, List.getElem_zip, List.getElem_ofFn]
    rfl
  rw [hget] at hk
  have hji : j = i := hL.get_inj_iff.mp (congrArg Prod.fst hk)
  exact (congrArg Prod.snd hk).symm.trans (congrArg g hji)

/-- The finite gap update records exactly the old region selected by
each induced cuff position, followed by canonical new region reindexing. -/
theorem gm06GapRegionsAfterDeletion_eq_ofFn (x : GM06DrawingData)
    (vs L : List (Fin x.n)) (hL : L.Nodup) (g : Fin L.length → Fin x.regions.length) :
    x.gapRegionsAfterDeletion vs L (List.ofFn g) =
      List.ofFn (fun i : Fin (x.relabelVertexList vs L).length =>
        x.regionAfterDeletion vs (g (gm06InducedGapPosition x vs L i))) := by
  let p := fun v : Fin x.n => decide (v ∈ vs)
  let Z := (L.zip (List.ofFn g)).filter (fun q => p q.1)
  have hfirst : Z.map Prod.fst = L.filter p :=
    GM06DrawingData.gapZipFilter_first L (List.ofFn g) p (by simp only [List.length_ofFn])
  have hZlen : Z.length = (L.filter p).length := by
    simpa only [List.length_map] using congrArg List.length hfirst
  have hlen : (x.relabelVertexList vs L).length = (L.filter p).length :=
    gm06RelabelVertexList_length_filter x vs L
  apply List.ext_getElem (by
    rw [List.length_ofFn]
    exact x.gapRegionsAfterDeletion_length vs L (List.ofFn g) (by simp only [List.length_ofFn]))
  intro i hi₁ hi₂
  let j : Fin (x.relabelVertexList vs L).length := ⟨i, by simpa only [List.length_ofFn] using hi₂⟩
  let k : Fin (L.filter p).length := Fin.cast hlen j
  have hiZ : i < Z.length := by rw [hZlen, ← hlen]; exact j.isLt
  let t : Fin Z.length := ⟨i, hiZ⟩
  have hiF : i < (L.filter p).length := k.isLt
  have hopt := congrArg (fun A : List (Fin x.n) => A[i]?) hfirst
  rw [List.getElem?_map, List.getElem?_eq_getElem hiZ, List.getElem?_eq_getElem hiF] at hopt
  have hfst : (Z.get t).1 = (L.filter p).get k := Option.some.inj hopt
  have hpair : ((L.filter p).get k, (Z.get t).2) ∈ L.zip (List.ofFn g) := by
    have hh := List.mem_of_mem_filter (Z.get_mem t)
    change ((Z.get t).1, (Z.get t).2) ∈ L.zip (List.ofFn g) at hh
    rw [hfst] at hh
    exact hh
  have hget : L.get (gm06InducedGapPosition x vs L j) = (L.filter p).get k :=
    gm06FilterPosition_get L p k
  rw [← hget] at hpair
  have hsnd := gm06ZipOfFn_snd hL g (gm06InducedGapPosition x vs L j) hpair
  change (Z.map (fun q => x.regionAfterDeletion vs q.2))[i]'
    (by rw [List.length_map]; exact hiZ) = _
  rw [List.getElem_map, List.getElem_ofFn]
  exact congrArg (x.regionAfterDeletion vs) hsnd

end GraphMinor.Compute
