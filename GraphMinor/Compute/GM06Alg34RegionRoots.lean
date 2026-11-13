module

public import GraphMinor.Compute.GM06Alg34CellGraph
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Finite
public import Mathlib.Data.List.FinRange

/-!
# Canonical finite labels for the new regions

Keep the least packed inactive-cell label in each complement component.
These labels are found by a finite scan of the supplied incidence graph.
The root test and root list are executable finite reference functions.
Each inactive cell reaches one root, and two reachable roots coincide.
This gives canonical labels without choosing geometric points or regions.
-/

@[expose] public section
namespace GraphMinor.Compute.GM06DrawingData

/-- The least inactive label in one component of the finite complement graph. -/
def isRegionRoot (x : GM06DrawingData) (vs : List (Fin x.n)) (a : Fin x.cellCount) : Bool :=
  decide (x.activeCell vs (x.cellNumbering.symm a) = false ∧
    ∀ b : Fin x.cellCount, b < a → x.activeCell vs (x.cellNumbering.symm b) = false →
      ¬ (x.complementGraph vs).Reachable a b)

/-- The packed root labels, in increasing order, for regions after deletion. -/
def regionRoots (x : GM06DrawingData) (vs : List (Fin x.n)) : List (Fin x.cellCount) :=
  (List.finRange x.cellCount).filter (x.isRegionRoot vs)

/-- The root-list predicate is exactly inactivity and minimality in its component. -/
theorem mem_regionRoots_iff (x : GM06DrawingData) (vs : List (Fin x.n)) (a : Fin x.cellCount) :
    a ∈ x.regionRoots vs ↔ x.activeCell vs (x.cellNumbering.symm a) = false ∧
      ∀ b : Fin x.cellCount, b < a → x.activeCell vs (x.cellNumbering.symm b) = false →
        ¬ (x.complementGraph vs).Reachable a b := by
  simp only [regionRoots, List.mem_filter, List.mem_finRange, true_and, isRegionRoot, decide_eq_true_eq]

/-- Canonical roots have no repeated labels. -/
theorem regionRoots_nodup (x : GM06DrawingData) (vs : List (Fin x.n)) :
    (x.regionRoots vs).Nodup := (List.nodup_finRange _).filter _

/-- Two reachable roots are the same least label. -/
theorem regionRoots_eq_of_reachable (x : GM06DrawingData) (vs : List (Fin x.n))
    {a b : Fin x.cellCount} (ha : a ∈ x.regionRoots vs) (hb : b ∈ x.regionRoots vs)
    (hab : (x.complementGraph vs).Reachable a b) : a = b := by
  obtain ⟨ha0, hamin⟩ := (x.mem_regionRoots_iff vs a).mp ha
  obtain ⟨hb0, hbmin⟩ := (x.mem_regionRoots_iff vs b).mp hb
  rcases lt_trichotomy a b with hab' | rfl | hba'
  · exact False.elim (hbmin a hab' ha0 hab.symm)
  · rfl
  · exact False.elim (hamin b hba' hb0 hab)

/-- Every inactive cell reaches a canonical root. The finite minimum is
taken over supplied labels, with no selection from geometric data. -/
theorem exists_regionRoot (x : GM06DrawingData) (vs : List (Fin x.n))
    (a : Fin x.cellCount) (ha : x.activeCell vs (x.cellNumbering.symm a) = false) :
    ∃ r ∈ x.regionRoots vs, (x.complementGraph vs).Reachable a r := by
  let C := Finset.univ.filter (fun b : Fin x.cellCount =>
    x.activeCell vs (x.cellNumbering.symm b) = false ∧ (x.complementGraph vs).Reachable a b)
  have haC : a ∈ C := Finset.mem_filter.mpr ⟨Finset.mem_univ _, ha, .refl a⟩
  have hC : C.Nonempty := ⟨a, haC⟩
  let r := C.min' hC
  have hrC : r ∈ C := Finset.min'_mem C hC
  have hr := (Finset.mem_filter.mp hrC).2
  refine ⟨r, (x.mem_regionRoots_iff vs r).mpr ⟨hr.1, ?_⟩, hr.2⟩
  intro b hbr hb hab
  have hbC : b ∈ C := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hb, hr.2.trans hab⟩
  have hrb : r ≤ b := Finset.min'_le C b hbC
  exact (not_lt_of_ge hrb) hbr

end GraphMinor.Compute.GM06DrawingData
