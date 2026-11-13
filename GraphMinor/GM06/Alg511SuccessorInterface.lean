module

public import GraphMinor.GM06.Alg57InputRep
public import GraphMinor.GM06.Alg511LoopCorrect
import Mathlib.Tactic

/-!
# Applying the region-free successor interface in the feasibility loop

The input and output relations of VI (5.7) use the original edge
labels, both cuff families and ordinary-dart path rows. Replacing
the current reference linkage changes only those path rows. The
fixed graph, cuff maps and positively oriented rotation witnesses
therefore give the input relation at every successful round.

The loop theorem below uses exactly `GM06SuccessorOutputRep` for
the returned bit and array 8. Its conclusion includes the actual
execution, the (5.12) call bound and a linkage witness on success.
The command remains a parameter until algorithm (5.7) is proved.
-/

public section
namespace GraphMinor.GM06
open GraphMinor.Compute GraphMinor.Surface

/-- Replacing the given linkage by returned ordinary-dart rows
retains every original graph, cuff and positive-rotation label.
The new input relation is built directly from those same witnesses. -/
noncomputable def alg511SuccessorInputWithRows
    {k : ℕ} {x : GM06SuccessorInput} {G : Drawing ClosedCylinder}
    {L : CylinderLinkage k G} (rep : GM06SuccessorInputRep x G L)
    (M : CylinderLinkage k G) (rows : List (List ℕ))
    (hrows : GM06LinkageRowsEncoding M rep.graph.initialTagged rep.graph.vertexLabels
      rep.graph.edgeLabels rows) : GM06SuccessorInputRep {x with linkage := rows} G M where
  graph := {
    vertex := rep.graph.vertex
    pairs := rep.graph.pairs
    endpoints := rep.graph.endpoints
    edge := rep.graph.edge
    link := rep.graph.link }
  source := rep.source
  target := rep.target
  inner := rep.inner
  outer := rep.outer
  source_point := rep.source_point
  target_point := rep.target_point
  linkage := hrows
  rotations := rep.rotations

/-- The (5.11) loop uses the exact region-free input/output contract
of (5.7). Only the ordinary returned path rows replace the reference
linkage; all original labels remain those of the initial input.
This theorem composes a command with its execution contract and
is not the numbered theorem asserting algorithm (5.11). -/
theorem alg511_loop_exec_with_successor_input
    {w p q a b k d B : ℕ} {x : GM06SuccessorInput} {G : Drawing ClosedCylinder}
    {L₀ : CylinderLinkage k G} (rep : GM06SuccessorInputRep x G L₀)
    (hG : IsCylinderSection5Drawing k G) (tables : List (Arr × List ℕ)) (successor : Cmd)
    (hθ₀ : L₀.HasTheta (((p : ℝ) - q) / k))
    (hd : 0 < d) (hw : 1 < 2 ^ w)
    (hpfit : p + G.V.ncard / k + 1 < 2 ^ w) (hqfit : q < 2 ^ w)
    (hafit : a < 2 ^ w) (hbfit : b < 2 ^ w)
    (hkfit : k < 2 ^ w) (hdfit : d < 2 ^ w)
    (hlfit : (p + G.V.ncard / k + 1) * d + b * k < 2 ^ w)
    (hrfit : q * d + a * k < 2 ^ w)
    (hgrid : ∃ z : ℤ, (k : ℝ) * (((a : ℝ) - b) / d) = z)
    (hle : ((p : ℝ) - q) / k ≤ ((a : ℝ) - b) / d)
    (hcall : ∀ (r : ℕ) (M : CylinderLinkage k G) (rows : List (List ℕ)) (s : State)
      (henc : GM06LinkageRowsEncoding M rep.graph.initialTagged rep.graph.vertexLabels rep.graph.edgeLabels rows),
      r ≤ G.V.ncard / k → alg511RoundTheta p q k r < ((a : ℝ) - b) / d →
      M.HasTheta (alg511RoundTheta p q k r) → s.arrs 8 = gm06EncodeRows rows →
      (∀ field ∈ tables, s.arrs field.1 = field.2) →
      GM06Alg511LoopRegisters p q a b k d r s →
      ∃ t u, Exec w successor s t u ∧ u ≤ B ∧
        (∀ j ∈ [54, 55, 62, 63, 52, 66, 6000], t.regs j = s.regs j) ∧
        (∀ field ∈ tables, t.arrs field.1 = field.2) ∧
        GM06SuccessorOutputRep (alg511SuccessorInputWithRows rep M rows henc)
          (alg511RoundTheta p q k r) (t.regs 0) (t.arrs 8))
    (s : State) (h8 : s.arrs 8 = gm06EncodeRows x.linkage)
    (htables : ∀ field ∈ tables, s.arrs field.1 = field.2)
    (hregs : s.regs 54 = p ∧ s.regs 55 = q ∧ s.regs 62 = a ∧ s.regs 63 = b ∧
      s.regs 52 = k ∧ s.regs 66 = d) :
    ∃ t u calls, Exec w (gm06Alg511LoopProg successor) s t u ∧
      calls ≤ 1 + G.V.ncard / k ∧
      u ≤ 21 + (1 + G.V.ncard / k) * (B + 22) ∧
      (t.regs 0 = 0 ↔ ¬ IsThetaFeasible k G (((a : ℝ) - b) / d)) ∧
      (t.regs 0 = 1 ↔ IsThetaFeasible k G (((a : ℝ) - b) / d)) ∧
      (t.regs 0 = 1 → ∃ (M : CylinderLinkage k G) (rows : List (List ℕ)),
        M.HasTheta (((a : ℝ) - b) / d) ∧
          GM06LinkageRowsEncoding M rep.graph.initialTagged rep.graph.vertexLabels rep.graph.edgeLabels rows ∧
          t.arrs 8 = gm06EncodeRows rows ∧ ∀ field ∈ tables, t.arrs field.1 = field.2) := by
  apply alg511_loop_exec_of_successor_exec hG rep.graph.initialTagged rep.graph.vertexLabels
    rep.graph.edgeLabels tables successor L₀ x.linkage hθ₀ rep.linkage hd hw hpfit hqfit hafit hbfit
    hkfit hdfit hlfit hrfit hgrid hle ?_ s h8 htables hregs
  intro r M rows s hr hlt hθ henc harr hfixed hs
  obtain ⟨t, u, he, ht, hkeep, hfixed', hout⟩ :=
    hcall r M rows s henc hr hlt hθ harr hfixed hs
  refine ⟨t, u, he, ht, hkeep, hfixed', ?_⟩
  rcases hout with hnegative | ⟨hone, N, rs, hwords, hθ', henc'⟩
  · exact Or.inl hnegative
  · exact Or.inr ⟨hone, N, rs, hθ', henc', hwords⟩

end GraphMinor.GM06
