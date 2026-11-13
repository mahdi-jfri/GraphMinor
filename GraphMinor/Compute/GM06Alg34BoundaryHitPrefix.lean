module

public import GraphMinor.Compute.GM06Alg34BoundaryHitExpr
public import GraphMinor.Compute.GM06Alg34ScanLoop

/-!
# A counted scan for the boundary closure-hit predicate

Enumerate supplied cell labels by natural indices, testing their
component marks and closure incidences. The disjunction of the first
cell-count tests is exactly the closure-hit predicate for an inactive
source. Values outside the supplied range are set to false.
-/

@[expose] public section
namespace GraphMinor.Compute

/-- A successful counted prefix contains a successful tested index. -/
theorem gm06AnyPrefix_eq_true (f : ℕ → Bool) (n : ℕ) :
    gm06AnyPrefix f n = true ↔ ∃ i < n, f i = true := by
  induction n with
  | zero => simp [gm06AnyPrefix]
  | succ n ih =>
    simp only [gm06AnyPrefix, Bool.or_eq_true, ih]
    constructor
    · rintro (⟨i, hi, hf⟩ | hn)
      · exact ⟨i, Nat.lt_succ_of_lt hi, hf⟩
      · exact ⟨n, Nat.lt_succ_self n, hn⟩
    · rintro ⟨i, hi, hf⟩
      rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
      · exact Or.inl ⟨i, hi, hf⟩
      · exact Or.inr hf

/-- The natural-index contribution test uses only valid packed labels. -/
def gm06BoundaryContribution (x : GM06DrawingData) (vs : List (Fin x.n))
    (a b : Fin x.cellCount) (i : ℕ) : Bool :=
  if hi : i < x.cellCount then
    decide ((x.complementGraph vs).Reachable a ⟨i, hi⟩ ∧
      x.cellNumbering.symm b ∈ x.cellClosure (x.cellNumbering.symm ⟨i, hi⟩))
  else false

/-- Scanning all supplied cell contributions computes precisely the
new region's closure-hit predicate. -/
theorem gm06BoundaryContribution_prefix (x : GM06DrawingData) (vs : List (Fin x.n))
    (a b : Fin x.cellCount) (ha : x.activeCell vs (x.cellNumbering.symm a) = false) :
    gm06AnyPrefix (gm06BoundaryContribution x vs a b) x.cellCount =
      x.regionClosureHit vs a (x.cellNumbering.symm b) := by
  rw [x.regionClosureHit_eq_any_reached vs a (x.cellNumbering.symm b) ha]
  apply Bool.eq_iff_iff.mpr
  simp only [gm06AnyPrefix_eq_true, List.any_eq_true, List.mem_finRange, true_and,
    decide_eq_true_eq]
  constructor
  · rintro ⟨i, hi, hf⟩
    refine ⟨⟨i, hi⟩, ?_⟩
    simpa only [gm06BoundaryContribution, dif_pos hi, decide_eq_true_eq] using hf
  · rintro ⟨c, hc⟩
    refine ⟨c.val, c.isLt, ?_⟩
    simpa only [gm06BoundaryContribution, dif_pos c.isLt, decide_eq_true_eq] using hc

end GraphMinor.Compute
