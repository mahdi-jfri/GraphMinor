module

public import GraphMinor.Compute.GM06FindPuncturedComponent

/-!
# Interpreting the punctured component search result

For Reduction 2 in VI (5.7), page 133, the first-success fold has
two outcomes. A missing source excludes every live component with
zero protected intersection. A returned source is a live vertex
whose computed component has zero protected intersection. Both
facts follow from the finite source scan, without extra certificates.
-/

public section
namespace GraphMinor.Compute

private theorem option_or_fold (xs : List (Option ℕ)) (a : Option ℕ) :
    xs.foldl Option.or a = a.or (xs.findSome? id) := by
  induction xs generalizing a with
  | nil => cases a <;> rfl
  | cons x xs ih =>
    rw [List.foldl_cons, ih, List.findSome?_cons]
    cases a <;> cases x <;> rfl

private theorem option_or_fold_eq_none (xs : List (Option ℕ)) :
    xs.foldl Option.or none = none ↔ ∀ x ∈ xs, x = none := by
  rw [option_or_fold, Option.none_or, List.findSome?_eq_none_iff]
  rfl

private theorem option_or_fold_mem {xs : List (Option ℕ)} {v : ℕ}
    (h : xs.foldl Option.or none = some v) : some v ∈ xs := by
  rw [option_or_fold, Option.none_or] at h
  obtain ⟨a, ha, hav⟩ := List.exists_of_findSome?_eq_some h
  exact hav ▸ ha

/-- The source search either excludes every eligible live vertex or
returns an actual live source with zero protected intersection. -/
theorem gm06PuncturedSourceCandidates_fold_spec {n : ℕ}
    (tagged : List ((Fin n × Fin n) × ℕ)) (cut : Fin n) (Q A : Finset (Fin n)) :
    (((gm06PuncturedSourceCandidates tagged cut Q A).foldl Option.or none = none ∧
      ∀ source ∈ A,
        (Q ∩ reachSet (gm06PuncturedGraphData tagged cut).vertexGraph source).card ≠ 0) ∨
      ∃ source : Fin n,
        (gm06PuncturedSourceCandidates tagged cut Q A).foldl Option.or none = some source.val ∧
        source ∈ A ∧
        (Q ∩ reachSet (gm06PuncturedGraphData tagged cut).vertexGraph source).card = 0) := by
  classical
  cases hfold : (gm06PuncturedSourceCandidates tagged cut Q A).foldl Option.or none with
  | none =>
    left
    refine ⟨rfl, ?_⟩
    intro source hsource hzero
    have hmem : some source.val ∈ gm06PuncturedSourceCandidates tagged cut Q A := by
      unfold gm06PuncturedSourceCandidates
      apply List.mem_ofFn.mpr
      refine ⟨source, ?_⟩
      simp only [hsource, hzero, and_self, ite_true]
    have hh := (option_or_fold_eq_none _).mp hfold _ hmem
    cases hh
  | some v =>
    have hmem := option_or_fold_mem hfold
    unfold gm06PuncturedSourceCandidates at hmem
    obtain ⟨source, hsource⟩ := List.mem_ofFn.mp hmem
    split_ifs at hsource with hsuccess
    · have hv : source.val = v := Option.some.inj hsource
      exact Or.inr ⟨source, congrArg some hv.symm, hsuccess.1, hsuccess.2⟩

end GraphMinor.Compute
