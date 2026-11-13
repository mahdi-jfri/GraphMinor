module

public import GraphMinor.Compute.GM06Alg34ComponentInputs

/-!
# Vertex mass of component branching

Canonical root components are disjoint and cover every supplied vertex.
Their concatenated vertex lists therefore permute the original finite
range. The sum of the child vertex counts equals the parent count,
so branching does not create additional vertex work.
-/

public section
namespace GraphMinor.Compute.GM06DrawingData

/-- Lists belonging to distinct canonical roots have no common vertex. -/
theorem componentVertices_disjoint (x : GM06DrawingData) {a b : Fin x.n}
    (ha : a ∈ x.componentRoots) (hb : b ∈ x.componentRoots) (hne : a ≠ b) :
    (x.componentVertices a).Disjoint (x.componentVertices b) := by
  apply List.disjoint_left.mpr
  intro v hva hvb
  have hav := (x.mem_componentVertices_iff a v).mp hva
  have hbv := (x.mem_componentVertices_iff b v).mp hvb
  exact hne (x.componentRoots_eq_of_reachable ha hb (hav.trans hbv.symm))

/-- The canonical component lists partition the supplied vertex range. -/
theorem componentVertices_flatMap_perm (x : GM06DrawingData) :
    (x.componentRoots.flatMap x.componentVertices).Perm (List.finRange x.n) := by
  have hn : x.componentRoots.Nodup := (List.nodup_finRange _).filter _
  have hp : List.Pairwise (Function.onFun List.Disjoint x.componentVertices) x.componentRoots :=
    List.Pairwise.imp_of_mem (fun ha hb hne => x.componentVertices_disjoint ha hb hne) hn
  apply (List.perm_ext_iff_of_nodup
    (List.nodup_flatMap.mpr ⟨fun a _ => x.componentVertices_nodup a, hp⟩)
    (List.nodup_finRange _)).mpr
  intro a
  simp only [List.mem_finRange, iff_true]
  obtain ⟨r, hr, har⟩ := x.exists_componentRoot a
  exact List.mem_flatMap.mpr ⟨r, hr, (x.mem_componentVertices_iff r a).mpr har.symm⟩

/-- Induced component inputs retain exactly their component vertex list. -/
theorem componentData_n (x : GM06DrawingData) (a : Fin x.n) :
    (x.componentData a).n = (x.componentVertices a).length := by
  change (x.activeVertices (x.componentVertices a)).length = _
  apply congrArg List.length
  unfold activeVertices componentVertices
  simp only [List.mem_filter, List.mem_finRange, true_and, decide_eq_true_eq,
    List.filter_filter, Bool.and_self]

/-- The sum of all canonical child vertex counts is the parent vertex count. -/
theorem componentData_sum_n (x : GM06DrawingData) :
    (x.componentRoots.map (fun a => (x.componentData a).n)).sum = x.n := by
  have hh := (x.componentVertices_flatMap_perm).length_eq
  simpa only [List.length_flatMap, List.length_finRange, x.componentData_n] using hh

end GraphMinor.Compute.GM06DrawingData
