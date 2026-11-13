module

public import GraphMinor.GM06.Alg57CurrentReduction4Phase
public import GraphMinor.GM06.Alg57CurrentTerminalPhase
public import GraphMinor.GM06.Alg57OnePathEncoded
public import GraphMinor.GM06.Alg57OnePathTerminalPhase

/-!
# The two phases of VI (5.7) for every number of paths

The loop of algorithm (5.7) on page 133 calls two phase programs: the Reduction 4 phase,
with pure function `gm06Reduction4Phase`, and the terminal phase, with pure function
`gm06TerminalPhase`. Here we state what they compute, for every `k ≥ 1`, against the current
arrays and their drawing (`GM06CurrentDrawingRep`).

* `reduction4Phase_sound_of_pos`: if the Reduction 4 phase reports a rerouting, its rows encode a
  linkage `M` with a Reduction 4 step from `L`.
* `reduction4Phase_complete_of_pos`: if it reports none, no Reduction 4 step exists.
* `terminalPhase_linkage_of_pos`: if no reduction applies and no `sᵢ` has valency one, the rows of
  the terminal phase encode a linkage of winding `θ + 1/k` whose path `i` ends at the end of
  `Pᵢ₊₁`.

Each statement splits into the case `k ≥ 2`, proved in `Alg57CurrentReduction4Phase.lean` and
`Alg57CurrentTerminalPhase.lean`, and the case `k = 1`, proved in `Alg57OnePathPhase.lean`,
`Alg57OnePathEncoded.lean` and `Alg57OnePathTerminalPhase.lean`. For `k = 1` the completeness
statement also uses that Reduction 1 does not apply and that `s₁` does not have valency one.
-/

@[expose] public section

namespace GraphMinor.GM06

open Set Topology GraphMinor.Surface GraphMinor.GM11 GraphMinor.Compute

variable {k : ℕ} {G : Drawing ClosedCylinder}

namespace GM06CurrentDrawingRep

variable {x : GM06SuccessorInput} {L : CylinderLinkage k G} (rep : GM06CurrentDrawingRep x G L)

/-- **The Reduction 4 phase is sound** (VI (5.7), page 133, `k ≥ 1`). If Reduction 2 does not
apply and the phase reports a rerouting, its rows are the rows of a linkage `M` of the same drawing
with a Reduction 4 step from `L`. -/
theorem reduction4Phase_sound_of_pos (hk : 0 < k) (hG : IsCylinderSection5Drawing k G)
    (hno : ∀ (G₁ : Drawing ClosedCylinder) (L₁ : CylinderLinkage k G₁),
      IsCylinderSection5Drawing k G₁ → ¬ Section5Reduction2Step k G L G₁ L₁)
    {θ : ℝ} (hθ : L.HasTheta θ) (h : (gm06Reduction4Phase x rep.tagged.length).1 = true) :
    ∃ M : CylinderLinkage k G, Section5Reduction4Step k G L G M ∧
      GM06LinkageRowsEncoding M rep.tagged rep.vertex rep.edge
        (gm06Reduction4Phase x rep.tagged.length).2 := by
  rcases Nat.lt_or_eq_of_le (Nat.succ_le_of_lt hk) with hk2 | rfl
  · exact rep.reduction4Phase_sound hk2 hG hno hθ h
  · exact rep.reduction4Phase_one_sound_rows hG hno hθ h

/-- **The Reduction 4 phase is complete** (VI (5.7), page 133, `k ≥ 1`). If Reductions 1 and 2 do
not apply, no `sᵢ` has valency one, and the phase reports no rerouting, then no Reduction 4 step
exists. For `k ≥ 2` only the failure of Reduction 2 is used. -/
theorem reduction4Phase_complete_of_pos (hk : 0 < k) (hG : IsCylinderSection5Drawing k G)
    (hno1 : ∀ (H : Drawing ClosedCylinder) (M : CylinderLinkage k H),
      IsCylinderSection5Drawing k H → ¬ Section5Reduction1Step k G L H M)
    (hno2 : ∀ (H : Drawing ClosedCylinder) (M : CylinderLinkage k H),
      IsCylinderSection5Drawing k H → ¬ Section5Reduction2Step k G L H M)
    (hval : ∀ i, vertexValency G.toGraph (cylinderM1Point k i) ≠ 1)
    {θ : ℝ} (hθ : L.HasTheta θ) (h : (gm06Reduction4Phase x rep.tagged.length).1 = false) :
    ¬ ∃ M : CylinderLinkage k G, Section5Reduction4Step k G L G M := by
  rcases Nat.lt_or_eq_of_le (Nat.succ_le_of_lt hk) with hk2 | rfl
  · exact rep.reduction4Phase_complete hk2 hG hno2 hθ h
  · exact rep.reduction4Phase_one_complete hG hno1 hno2 (hval 0) hθ h

/-- **The terminal phase gives the next linkage** (VI (5.7), page 133, `k ≥ 1`). If no reduction
applies and no `sᵢ` has valency one, the rows written by the terminal phase encode a linkage `L'`
of `G` with winding `θ + 1/k`, whose path `i` ends at the end of `Pᵢ₊₁`. -/
theorem terminalPhase_linkage_of_pos (hk : 0 < k) (hG : IsCylinderSection5Drawing k G)
    (hno : ¬ Section5AnyReductionApplies k G L)
    (hval : ∀ i, vertexValency G.toGraph (cylinderM1Point k i) ≠ 1)
    {θ : ℝ} (hθ : L.HasTheta θ) :
    ∃ L' : CylinderLinkage k G, L'.HasTheta (θ + 1 / (k : ℝ)) ∧
      (∀ i, L'.curve i 1 = L.curve (finSuccCycle i) 1) ∧
      GM06LinkageRowsEncoding L' rep.tagged rep.vertex rep.edge
        (gm06TerminalPhase x rep.tagged.length) := by
  rcases Nat.lt_or_eq_of_le (Nat.succ_le_of_lt hk) with hk2 | rfl
  · exact rep.terminalPhase_linkage_phase hk2 hG hno hval hθ
  · rw [gm06TerminalPhase_eq_successorRows]
    exact rep.terminalPhase_one_linkage hG hno hval hθ

end GM06CurrentDrawingRep

end GraphMinor.GM06
