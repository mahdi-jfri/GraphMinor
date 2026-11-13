module

public import GraphMinor.Compute.CrossingLiftBoundaryTest
public import GraphMinor.Compute.CrossingLiftReplacementTest

/-!
# The replacement-edge test returns exactly `usesNewEdge`

The boundary scan visits vertices in their recorded order, while the mathematical new-edge
test visits consecutive path positions. Since a path has no repeated vertex, each boundary
vertex has only one possible path position. This file identifies the two tests, then applies
the encoded-edge representation to prove the RAM test's graph specification.
-/

public section

namespace GraphMinor.Compute.Crossing

open GraphMinor.Crossing

private theorem missing_boundary_iff_index {V : Type*} [DecidableEq V]
    (B : List V) (E : List (V × V)) : ∀ L : List V,
    liftMissingBoundaryEdge B E L = true ↔
      ∃ (i : ℕ) (hi : i + 1 < L.length),
        L[i]'(by omega) ∈ B ∧ L[i + 1] ∈ B ∧ (L[i]'(by omega), L[i + 1]) ∉ E
  | [] => by simp [liftMissingBoundaryEdge]
  | [a] => by simp [liftMissingBoundaryEdge]
  | a :: b :: rest => by
    rw [liftMissingBoundaryEdge, Bool.or_eq_true, decide_eq_true_eq,
      missing_boundary_iff_index B E (b :: rest)]
    constructor
    · rintro (h | ⟨i, hi, ha, hb, he⟩)
      · exact ⟨0, by simp, h⟩
      · refine ⟨i + 1, by simpa only [List.length_cons] using Nat.succ_lt_succ hi, ?_⟩
        simpa only [List.getElem_cons_succ] using And.intro ha (And.intro hb he)
    · rintro ⟨i, hi, ha, hb, he⟩
      cases i with
      | zero => exact Or.inl ⟨ha, hb, he⟩
      | succ i =>
        refine Or.inr ⟨i, by simpa only [List.length_cons] using Nat.lt_of_succ_lt_succ hi, ?_⟩
        simpa only [List.getElem_cons_succ] using And.intro ha (And.intro hb he)

/-- On a duplicate-free path, testing after each recorded boundary vertex agrees with testing
consecutive path positions. No graph hypotheses are needed for this equality of tests. -/
theorem boundary_after_iff_missing {N : ℕ} (B L : List (Fin N))
    (E : List (Fin N × Fin N)) (hL : L.Nodup) :
    (∃ a ∈ B, liftBoundaryAfterFlag B E L a = 1) ↔ liftMissingBoundaryEdge B E L = true := by
  rw [missing_boundary_iff_index]
  constructor
  · rintro ⟨a, haB, hflag⟩
    by_cases hn : L.idxOf a + 1 < L.length
    · have htest : L[L.idxOf a + 1] ∈ B ∧ (a, L[L.idxOf a + 1]) ∉ E := by
        by_contra hc
        simp only [liftBoundaryAfterFlag, hn, ↓reduceDIte, hc, ↓reduceIte] at hflag
        contradiction
      have haidx : L[L.idxOf a]'(by omega) = a := List.getElem_idxOf (by omega)
      refine ⟨L.idxOf a, hn, ?_, ?_, ?_⟩
      · simpa only [haidx] using haB
      · exact htest.1
      · simpa only [haidx] using htest.2
    · simp only [liftBoundaryAfterFlag, hn, ↓reduceDIte] at hflag
      contradiction
  · rintro ⟨i, hi, haB, hbB, hnot⟩
    refine ⟨L[i]'(by omega), haB, ?_⟩
    have hidx : L.idxOf (L[i]'(by omega)) = i := hL.idxOf_getElem i (by omega)
    simp only [liftBoundaryAfterFlag, hidx, hi, ↓reduceDIte, hbB, hnot, not_false_eq_true, true_and, ↓reduceIte]

open Classical in
/-- On a path of a valid replaced instance, the RAM boundary test returns exactly whether that
path uses a new edge. Its representation hypotheses are the boundary and recorded old edges,
with the mapped lists and flat edge array in memory. No reverse-search result is assumed. -/
theorem liftBoundaryTestProg_exec_graph {w N : ℕ} (r : ReplRecord (Fin N))
    (D L B : List (Fin N)) (E : List (Fin N × Fin N))
    (hval : r.IsValid D) (hp : IsPathList r.newGraph L)
    (hBnd : B.Nodup) (hB : ∀ y, y ∈ B ↔ y ∈ r.boundary)
    (hE : ∀ a b, (a, b) ∈ E ↔ r.graph.Adj a b ∧
      (a ∈ r.rep ∨ a ∈ r.boundary) ∧ (b ∈ r.rep ∨ b ∈ r.boundary))
    (src boundary edges r_bad R : ℕ) (hbR : r_bad < R) (s : State)
    (hsrc : s.arrs src = L.map Fin.val) (hbd : s.arrs boundary = B.map Fin.val)
    (hedges : s.arrs edges = E.flatMap encPair)
    (hw : 16 * (N + L.length + B.length + E.length + 5) < 2 ^ w) :
    ∃ s' t, Exec w (liftBoundaryTestProg src boundary edges r_bad R) s s' t ∧
      t ≤ 500 * (L.length + E.length + 1) + 1500 ∧
      s'.regs r_bad = (if usesNewEdge r.graph L then 1 else 0) ∧
      (∀ c, s'.arrs c = s.arrs c) ∧
      (∀ q < R, q ≠ r_bad → s'.regs q = s.regs q) := by
  have hBset : B.toFinset = r.boundary := by ext y; simpa only [List.mem_toFinset] using hB y
  have hsmall : B.length ≤ 3 := by
    rw [← List.toFinset_card_of_nodup hBnd, hBset]
    exact hval.2.2.1
  have htest : (∃ a ∈ B, liftBoundaryAfterFlag B E L a = 1) ↔ usesNewEdge r.graph L :=
    (boundary_after_iff_missing B L E hp.2.1).trans
      (liftMissingBoundaryEdge_eq_true_iff r B E hB (recorded_boundary_edges r E hE) L hp.2.2)
  obtain ⟨s', t, he, ht, ho, ha, hr⟩ := liftBoundaryTestProg_exec src boundary edges r_bad R
    hbR L B E hp.2.1 hBnd hsmall s hsrc hbd hedges hw
  exact ⟨s', t, he, ht, by simpa only [htest] using ho, ha, hr⟩

end GraphMinor.Compute.Crossing
