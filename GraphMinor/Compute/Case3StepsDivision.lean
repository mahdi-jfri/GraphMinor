module

public import GraphMinor.Compute.Case3StepsCompass
public import GraphMinor.Compute.Algorithm33Multigraph

/-!
# Calling (8.6) on a flat compass

Step (5) of Graph Minors XIII (9.9), page 104, applies (8.6) to the wall
society. We first call it on the compact simple compass. Flatness rules out its
cross output. Its remaining output gives the simple rural division and the core
from which the members can be computed. The call runs above the caller's array
and register bases.

This file treats the call and the simple division. Lifting the division to the
multigraph, and writing its members, require further arguments.
-/

@[expose] public section

namespace GraphMinor.Compute

/-- A valid (8.6) output on a cross-free society must be its division output. -/
theorem case3Alg86Output_division {x : Alg81Input} (out : List ℕ)
    (hcross : ¬ HasCrossInSociety x.G x.omega)
    (hout : IsValidAlg86Output x (decAlg86Out x out)) :
    ∃ d : Alg86DivisionOutput x,
      decAlg86Out x out = Sum.inr d ∧ IsValidAlg86DivisionOutput x d := by
  cases hdec : decAlg86Out x out with
  | inl c =>
    rw [hdec] at hout
    exact False.elim (hcross ⟨c.p₁, c.p₂, c.q₁, c.q₂, c.P, c.Q, hout.1⟩)
  | inr d =>
    exact ⟨d, rfl, by simpa only [hdec, IsValidAlg86Output] using hout⟩

/-- The output conditions of (8.6) determine its raw and merged member families. -/
theorem case3Alg86Division_families {x : Alg81Input} {d : Alg86DivisionOutput x}
    (hd : IsValidAlg86DivisionOutput x d) :
    d.rawDiv = alg86RawDivision x d.core.Z ∧ d.div = alg86Division x d.core.Z := by
  have hraw : d.rawDiv = alg86RawDivision x d.core.Z := by
    ext A
    exact hd.2.2.2.1 A
  refine ⟨hraw, ?_⟩
  ext B
  rw [hd.2.2.2.2.1 B, hraw]
  rfl

/-- Every member returned by (8.6) on the compact compass has the explicit
boundary description proved in `Case3StepsCompass`. The only assumptions are
wall validity and validity of the (8.6) output. -/
theorem case3Alg86Division_members {h n : ℕ} (D : MultiDigraph n)
    (W : WallOfHeight h D) (h2 : 2 ≤ h) (he : Even h) (hW : W.IsValid)
    {d : Alg86DivisionOutput (case3Alg81Input D W h2 he hW)}
    (hd : IsValidAlg86DivisionOutput (case3Alg81Input D W h2 he hW) d)
    (B : Alg86Subgraph (case3Alg81Input D W h2 he hW).G) :
    B ∈ d.div ↔
      ∃ (bd : Finset (Fin (case3Alg81Input D W h2 he hW).n))
        (hbd : IsRawBoundary (case3Alg81Input D W h2 he hW) d.core.Z bd),
        B = mergedMemberOfBoundary (case3Alg81Input D W h2 he hW) d.core.Z bd hbd.subset_Z := by
  rw [(case3Alg86Division_families hd).2]
  exact mem_alg86Division_iff_exists_isRawBoundary hd.2.2.1.2.2.1
    hd.2.2.1.2.2.2.2.2.1 hd.1
    (not_isAlg86TypeIII_case3Alg81Input D W h2 he hW) B

/-- The (8.6) call in step (5), after its compact input has been written.
Its constants depend only on the supplied program and its computation bound.
Every array and register below the chosen bases is preserved. This does not
include the cost of constructing the input or lifting the output. -/
theorem case3Alg86Call_exec (shiloachProg : Cmd)
    (h86 : ComputesArrRelInTime alg81Size encAlg81In
      (fun x out => IsValidAlg86Output x (decAlg86Out x out))
      (alg86Prog shiloachProg) (fun s => s)) :
    ∃ C c : ℕ, 1 ≤ C ∧ 1 ≤ c ∧
      ∀ {h n : ℕ} (D : MultiDigraph n) (W : WallOfHeight h D)
        (h2 : 2 ≤ h) (he : Even h) (hW : W.IsValid),
        W.IsFlatWall h2 →
        ∀ (a_base r_base w : ℕ),
          wordSize c ((n + 1) * (D.numEdges + n + 1)) ≤ w →
          ∀ s : State, s.arrs a_base = encAlg81In (case3Alg81Input D W h2 he hW) →
          ∃ (s' : State) (t : ℕ)
            (d : Alg86DivisionOutput (case3Alg81Input D W h2 he hW)),
            Exec w ((alg86Prog shiloachProg).shift a_base r_base) s s' t ∧
            t ≤ C * ((n + 1) * (D.numEdges + n + 1)) ∧
            decAlg86Out (case3Alg81Input D W h2 he hW) (s'.arrs (a_base + 1)) = Sum.inr d ∧
            IsValidAlg86DivisionOutput (case3Alg81Input D W h2 he hW) d ∧
            (∀ a < a_base, s'.arrs a = s.arrs a) ∧
            (∀ r < r_base, s'.regs r = s.regs r) := by
  obtain ⟨C, c, hC, hc, hrun⟩ := h86
  refine ⟨C, c, hC, hc, ?_⟩
  intro h n D W h2 he hW hflat a_base r_base w hw s hin
  let x := case3Alg81Input D W h2 he hW
  have hsize : alg81Size x ≤ (n + 1) * (D.numEdges + n + 1) :=
    alg81Size_case3Alg81Input_le D W h2 he hW
  have hin' : (s.unshift a_base r_base).arrs inArr = encAlg81In x := by
    simpa only [State.unshift_arrs, inArr, Nat.zero_add] using hin
  obtain ⟨s_sub, t, hex, ht, hout⟩ := hrun x (s.unshift a_base r_base) hin'
  obtain ⟨d, hdec, hd⟩ := case3Alg86Output_division (s_sub.arrs outArr)
    (not_hasCrossInSociety_case3Alg81Input D W h2 he hW hflat) hout
  have hw' : wordSize c (alg81Size x) ≤ w :=
    (wordSize_mono_right c hsize).trans hw
  refine ⟨s.applyShifted a_base r_base s_sub, t, d,
    Exec.shift_from a_base r_base (hex.mono_wordSize hw'),
    ht.trans (Nat.mul_le_mul_left C hsize), ?_, hd, ?_, ?_⟩
  · simpa only [State.applyShifted_arrs_add', outArr] using hdec
  · exact fun a ha => State.applyShifted_arrs_lt a_base r_base s s_sub ha
  · exact fun r hr => State.applyShifted_regs_lt a_base r_base s s_sub hr

end GraphMinor.Compute
