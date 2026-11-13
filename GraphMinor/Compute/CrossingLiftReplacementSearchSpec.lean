module

public import GraphMinor.Compute.CrossingLiftBoundedSearch
public import GraphMinor.Compute.CrossingLiftSearchReach
public import GraphMinor.Compute.CrossingLiftSearchPathSpec
public import GraphMinor.Compute.CrossingLiftReplacementMath

/-!
# The recorded replacement search meets Lemma 1

The record's edge list describes exactly the old graph restricted to its boundary and
recorded component. The inferred bound contains all those labels. Replacement validity
joins the prescribed endpoints through that component, so the existing search returns
exactly a path allowed by Lemma 1's reverse rule.
-/

public section

namespace GraphMinor.Compute.Crossing

open SimpleGraph GraphMinor.Crossing

/-- The graph-building search returns the replacement path required by Lemma 1.
Its hypotheses are the valid replacement, its recorded lists and their storage, the
prescribed first/last endpoints and inferred count, memory layout, and word bounds. -/
theorem liftBuildSearchProg_exec_replacement {w N : ℕ} (r : ReplRecord (Fin N))
    (D L B C : List (Fin N)) (E : List (Fin N × Fin N))
    (hvalid : r.IsValid D) (hB : ∀ x, x ∈ B ↔ x ∈ r.boundary)
    (hC : ∀ x, x ∈ C ↔ x ∈ r.rep) (hEnd : E.Nodup)
    (hE : ∀ a b, (a, b) ∈ E ↔ r.graph.Adj a b ∧
      (a ∈ r.rep ∨ a ∈ r.boundary) ∧ (b ∈ r.rep ∨ b ∈ r.boundary))
    (p q : Fin N) (hp : firstIn r.boundary L = some p) (hq : lastIn r.boundary L = some q)
    (edges component R A : ℕ) (heA : edges < A) (hcA : component < A) (s : State)
    (he : s.arrs edges = E.flatMap encPair) (hc : s.arrs component = C.map Fin.val)
    (hn : s.regs (R + 40) = liftVertexBound (B ++ C) 0)
    (hu : s.regs (R + 74) = p.val) (hv : s.regs (R + 75) = q.val)
    (hw : 32 * (N + C.length + E.length + 1) < 2 ^ w) :
    ∃ (s' : State) (t : ℕ) (Y : List (Fin N)),
      Exec w (liftBuildSearchProg edges component R A) s s' t ∧
      t ≤ 400 * (N + C.length + E.length + 1) ∧ IsReplSearchPath r L Y ∧
      s'.arrs (A + 66) = Y.map Fin.val ∧
      (∀ a < A, s'.arrs a = s.arrs a) ∧ (∀ k < R, s'.regs k = s.regs k) := by
  let H := HP25.restrict r.graph (r.rep ∪ (r.boundary : Set (Fin N)))
  let M := liftVertexBound (B ++ C) 0
  have hMN : M ≤ N := liftVertexBound_le _ (Nat.zero_le _)
  have hbound : ∀ x : Fin N, x ∈ r.rep ∨ x ∈ r.boundary → x.val < M := by
    intro x hx
    apply liftVertexBound_mem (M := 0)
    rcases hx with hx | hx
    · exact List.mem_append_right _ ((hC x).mpr hx)
    · exact List.mem_append_left _ ((hB x).mpr hx)
  have hEM : ∀ e ∈ E, e.1.val < M ∧ e.2.val < M := by
    intro e he
    have h := (hE e.1 e.2).mp he
    exact ⟨hbound _ h.2.1, hbound _ h.2.2⟩
  have hCM : ∀ x ∈ C, x.val < M := fun x hx => hbound x (Or.inl ((hC x).mp hx))
  obtain ⟨hpB, hqB⟩ := liftBoundaryEnds_mem hp hq
  have hpM : p.val < M := hbound p (Or.inr hpB)
  have hqM : q.val < M := hbound q (Or.inr hqB)
  have hgraph : ∀ a b, (a, b) ∈ E ↔ H.Adj a b := hE
  obtain ⟨W, hW⟩ := liftReplacementReach hvalid hpB hqB
  have hreach : ∃ W : H.Walk p q, ∀ x ∈ W.support, x ≠ p → x ≠ q → x ∈ C :=
    ⟨W, fun x hx hxp hxq => (hC x).mpr (hW x hx hxp hxq)⟩
  obtain ⟨s', t, Z, hex, ht, hz, hi, ho, ha, hr⟩ := liftBuildSearchProg_exec_bounded
    H hMN E C p q hEM hCM hpM hqM edges component R A heA hcA s hEnd hgraph
    he hc hn hu hv hreach hw
  have hinner : ∀ x ∈ Z.support, x ≠ p → x ≠ q → x ∈ r.rep :=
    fun x hx hxp hxq => (hC x).mp (hi x hx hxp hxq)
  exact ⟨s', t, Z.support, hex, ht, liftReplacementSearchPath_of_walk hp hq Z hz hinner,
    ho, ha, hr⟩

end GraphMinor.Compute.Crossing
