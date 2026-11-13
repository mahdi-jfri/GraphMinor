module

public import GraphMinor.Compute.CrossingLiftBoundaryTestSpec

/-!
# Choosing the affected path of a replacement

Lemma 1 keeps both paths when neither uses a newly added boundary edge. Otherwise it
searches only for the first affected path. This file computes the two flags while
preserving all path and record arrays.
-/

@[expose] public section

namespace GraphMinor.Compute.Crossing

open GraphMinor.Crossing

/-- Test the two paths into adjacent flags, using a disjoint scratch register block. -/
def liftReplacementFlagsProg (Q P boundary edges R : ℕ) : Cmd :=
  .seq (liftBoundaryTestProg Q boundary edges R (R + 300))
    (liftBoundaryTestProg P boundary edges (R + 1) (R + 300))

open Classical in
/-- Both flags exactly detect new edges. The assumptions are validity, two paths in the
new graph, the recorded boundary and edge relation, stored arrays and word bounds. -/
theorem liftReplacementFlagsProg_exec {w N : ℕ} (r : ReplRecord (Fin N))
    (D L₁ L₂ B : List (Fin N)) (E : List (Fin N × Fin N))
    (hvalid : r.IsValid D) (h₁ : IsPathList r.newGraph L₁) (h₂ : IsPathList r.newGraph L₂)
    (hBnd : B.Nodup) (hB : ∀ x, x ∈ B ↔ x ∈ r.boundary)
    (hE : ∀ a b, (a, b) ∈ E ↔ r.graph.Adj a b ∧
      (a ∈ r.rep ∨ a ∈ r.boundary) ∧ (b ∈ r.rep ∨ b ∈ r.boundary))
    (Q P boundary edges R : ℕ) (s : State)
    (hQ : s.arrs Q = L₁.map Fin.val) (hP : s.arrs P = L₂.map Fin.val)
    (hbd : s.arrs boundary = B.map Fin.val) (he : s.arrs edges = E.flatMap encPair)
    (hw : 32 * (N + L₁.length + L₂.length + B.length + E.length + 5) < 2 ^ w) :
    ∃ s' t, Exec w (liftReplacementFlagsProg Q P boundary edges R) s s' t ∧
      t ≤ 1000 * (L₁.length + L₂.length + E.length + 1) + 3000 ∧
      s'.regs R = (if usesNewEdge r.graph L₁ then 1 else 0) ∧
      s'.regs (R + 1) = (if usesNewEdge r.graph L₂ then 1 else 0) ∧
      (∀ a, s'.arrs a = s.arrs a) ∧ (∀ k < R, s'.regs k = s.regs k) := by
  classical
  obtain ⟨s1, t1, he1, ht1, ho1, ha1, hr1⟩ := liftBoundaryTestProg_exec_graph (w := w)
    r D L₁ B E hvalid h₁ hBnd hB hE Q boundary edges R (R + 300) (by omega)
    s hQ hbd he (by omega)
  obtain ⟨s2, t2, he2, ht2, ho2, ha2, hr2⟩ := liftBoundaryTestProg_exec_graph (w := w)
    r D L₂ B E hvalid h₂ hBnd hB hE P boundary edges (R + 1) (R + 300) (by omega)
    s1 ((ha1 _).trans hP) ((ha1 _).trans hbd) ((ha1 _).trans he) (by omega)
  exact ⟨s2, t1 + t2, .seq he1 he2, by omega,
    (hr2 R (by omega) (by omega)).trans ho1, ho2,
    fun a => (ha2 a).trans (ha1 a), fun k hk =>
      (hr2 k (by omega) (by omega)).trans (hr1 k (by omega) (by omega))⟩

end GraphMinor.Compute.Crossing
