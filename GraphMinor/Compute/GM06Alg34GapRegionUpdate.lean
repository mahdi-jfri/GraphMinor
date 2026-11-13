module

public import GraphMinor.Compute.GM06Alg34InducedData

/-!
# Reindexing old gap regions after vertex deletion

An old region remains in the complement of every induced drawing. Find
the first canonical complement root reachable from its supplied cell
label. Its index is the new region label. The search succeeds by the
finite root existence proof, and two old regions receive the same new
label exactly when their complement cells are connected.
-/

@[expose] public section
namespace GraphMinor.Compute.GM06DrawingData

private theorem gap_region_root_exists (x : GM06DrawingData) (vs : List (Fin x.n))
    (r : Fin x.regions.length) :
    ∃ a ∈ x.regionRoots vs,
      decide ((x.complementGraph vs).Reachable (x.cellNumbering (.inr (.inr r))) a) = true := by
  obtain ⟨a, ha, hr⟩ := x.exists_regionRoot vs (x.cellNumbering (.inr (.inr r)))
    (by simp only [Equiv.symm_apply_apply, activeCell])
  exact ⟨a, ha, decide_eq_true hr⟩

/-- Read the canonical new region containing the supplied old region.
The index is computed by a finite reachability scan, with no geometric selection. -/
def regionAfterDeletion (x : GM06DrawingData) (vs : List (Fin x.n))
    (r : Fin x.regions.length) : Fin (x.inducedData vs).regions.length :=
  ⟨(x.regionRoots vs).findIdx (fun a =>
      decide ((x.complementGraph vs).Reachable (x.cellNumbering (.inr (.inr r))) a)), by
    rw [x.inducedData_regions_length vs]
    exact List.findIdx_lt_length_of_exists (gap_region_root_exists x vs r)⟩

/-- The canonical packed root selected for an old region cell. -/
def regionRootAfterDeletion (x : GM06DrawingData) (vs : List (Fin x.n))
    (r : Fin x.regions.length) : Fin x.cellCount :=
  (x.regionRoots vs).get (Fin.cast (x.inducedData_regions_length vs) (x.regionAfterDeletion vs r))

/-- The selected new region root is a listed canonical complement root. -/
theorem regionRootAfterDeletion_mem (x : GM06DrawingData) (vs : List (Fin x.n))
    (r : Fin x.regions.length) : x.regionRootAfterDeletion vs r ∈ x.regionRoots vs :=
  List.get_mem _ _

/-- The supplied old region cell reaches its computed new region root. -/
theorem regionAfterDeletion_reachable (x : GM06DrawingData) (vs : List (Fin x.n))
    (r : Fin x.regions.length) :
    (x.complementGraph vs).Reachable (x.cellNumbering (.inr (.inr r)))
      (x.regionRootAfterDeletion vs r) := by
  apply of_decide_eq_true
  exact List.findIdx_getElem (w := List.findIdx_lt_length_of_exists (gap_region_root_exists x vs r))

/-- Complement connectivity makes the computed new labels equal. -/
theorem regionAfterDeletion_eq_of_reachable (x : GM06DrawingData) (vs : List (Fin x.n))
    {r s : Fin x.regions.length}
    (hrs : (x.complementGraph vs).Reachable (x.cellNumbering (.inr (.inr r)))
      (x.cellNumbering (.inr (.inr s)))) :
    x.regionAfterDeletion vs r = x.regionAfterDeletion vs s := by
  have he := x.regionRoots_eq_of_reachable vs (x.regionRootAfterDeletion_mem vs r)
    (x.regionRootAfterDeletion_mem vs s)
    (((x.regionAfterDeletion_reachable vs r).symm.trans hrs).trans (x.regionAfterDeletion_reachable vs s))
  have hi := (x.regionRoots_nodup vs).get_inj_iff.mp he
  apply Fin.ext
  have hval := congrArg (fun i : Fin (x.regionRoots vs).length => i.val) hi
  exact hval

/-- Two old regions receive the same new label exactly when their cells
belong to the same complement component after deletion. -/
theorem regionAfterDeletion_eq_iff (x : GM06DrawingData) (vs : List (Fin x.n))
    (r s : Fin x.regions.length) :
    x.regionAfterDeletion vs r = x.regionAfterDeletion vs s ↔
      (x.complementGraph vs).Reachable (x.cellNumbering (.inr (.inr r)))
        (x.cellNumbering (.inr (.inr s))) := by
  constructor
  · intro he
    have hr := x.regionAfterDeletion_reachable vs r
    have hs := x.regionAfterDeletion_reachable vs s
    have he' : x.regionRootAfterDeletion vs r = x.regionRootAfterDeletion vs s :=
      congrArg (fun i => (x.regionRoots vs).get (Fin.cast (x.inducedData_regions_length vs) i)) he
    rw [he'] at hr
    exact hr.trans hs.symm
  · exact x.regionAfterDeletion_eq_of_reachable vs

end GraphMinor.Compute.GM06DrawingData
