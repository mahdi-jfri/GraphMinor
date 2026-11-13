module

public import GraphMinor.Compute.GM06ReachableBounds
public import GraphMinor.Compute.GM06PhaseSize
import GraphMinor.GM06.Alg57CurrentRows
import GraphMinor.GM06.Alg57RowBounds
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Ring

/-!
# Phase word bounds in the original input size

The two finite phases of VI (5.7), page 133, use permanent vertex
and edge slots. Current paths are simple and disjoint, while current
positive rotation rows list each active augmented end at most once.
These facts bound the phase size independently of earlier reductions.

The actual inverse trace keeps the original number of edge slots.
Consequently the phase size is linear in the ordinary input size,
and its cubic workspace budget fits the same logarithmic words
already used by the early branches. No supplied size or workspace
certificate is needed.
-/

public section
namespace GraphMinor.Compute
open Set GraphMinor.Surface GraphMinor.GM06 GraphMinor.GM11 TwoPaths

/-- Current structural arrays satisfy the ordinary length conditions
read by a whole phase, including both fixed cuff families. -/
theorem gm06Current_phase_lengths
    {k : ℕ} {x : GM06SuccessorInput} {G : Drawing ClosedCylinder}
    {L : CylinderLinkage k G} (cur : GM06CurrentDrawingRep x G L) :
    x.endpoints.length = 2 * cur.tagged.length ∧
      x.innerCuff.length = k ∧ x.outerCuff.length = k ∧
      x.linkage.length = k ∧ x.rotations.length = x.vertexCount ∧
      x.rotations.flatten.Nodup := by
  refine ⟨?_, ?_, ?_, cur.linkage.1, cur.rows_length, cur.rows_flatten_nodup⟩
  · rw [cur.endpoints, gm06EndpointWords_length, List.length_map]
  · rw [cur.inner, List.length_ofFn]
  · rw [cur.outer, List.length_ofFn]

/-- The current phase size depends linearly on its fixed slot counts,
regardless of how many reductions have already been performed. -/
theorem gm06Current_phase_size_le
    {k : ℕ} {x : GM06SuccessorInput} {G : Drawing ClosedCylinder}
    {L : CylinderLinkage k G} (cur : GM06CurrentDrawingRep x G L)
    (hG : IsCylinderSection5Drawing k G) :
    gm06PhaseSize x cur.tagged.length ≤ 2 * x.vertexCount + 9 * cur.tagged.length + 11 * k + 2 := by
  obtain ⟨he, hi, ho, hp, _, _⟩ := gm06Current_phase_lengths cur
  obtain ⟨hrf, hrc⟩ := cur.rotation_length_bounds hG
  have hpf := cur.linkage.length_bounds.2.1
  unfold gm06PhaseSize
  rw [he, hi, ho, hp]
  omega

/-- Every reached phase size is linear in the original ordinary
input size. The actual undo trace identifies its permanent edge slots. -/
theorem gm06Reached_phase_size_le
    {k : ℕ} {x : GM06SuccessorInput} {G₀ : Drawing ClosedCylinder}
    {L₀ : CylinderLinkage k G₀} (input : GM06SuccessorInputRep x G₀ L₀)
    (initial : GM06CurrentDrawingRep x G₀ L₀)
    (hinit : initial.tagged = input.graph.initialTagged)
    {ends : List ℕ} {rots paths : List (List ℕ)}
    {G : Drawing ClosedCylinder} {L : CylinderLinkage k G}
    (cur : GM06CurrentDrawingRep {x with endpoints := ends, rotations := rots, linkage := paths} G L)
    {records : List (Option (ℕ × ℕ))}
    (trace : GM06UndoTrace x.vertexCount k initial.undoState cur.undoState records)
    (hG : IsCylinderSection5Drawing k G) :
    gm06PhaseSize {x with endpoints := ends, rotations := rots, linkage := paths} cur.tagged.length ≤
      32 * (gm06SuccessorInputSize x + 1) := by
  have hb := gm06Current_phase_size_le cur hG
  have ht := gm06Reached_tagged_length input initial hinit cur trace
  obtain ⟨hn, hm, hk, _, _, _⟩ := input.size_bounds
  rw [ht] at hb ⊢
  change _ ≤ 2 * x.vertexCount + 9 * G₀.E.ncard + 11 * k + 2 at hb
  omega

private theorem cubic_phase_budget_fits (N : ℕ) :
    10000 * (32 * (N + 1)) ^ 3 < 2 ^ wordSize 32 N := by
  have hc : 327680000 ≤ (N + 2) ^ 29 := by
    have hh := Nat.pow_le_pow_left (by omega : 2 ≤ N + 2) 29
    exact (by decide : 327680000 ≤ 2 ^ 29).trans hh
  have hp : (N + 1) ^ 3 ≤ (N + 2) ^ 3 := Nat.pow_le_pow_left (by omega) 3
  calc
    10000 * (32 * (N + 1)) ^ 3 = 327680000 * (N + 1) ^ 3 := by ring
    _ ≤ (N + 2) ^ 29 * (N + 2) ^ 3 := Nat.mul_le_mul hc hp
    _ = (N + 2) ^ 32 := by rw [← pow_add]
    _ < _ := pow_lt_two_pow_wordSize (by decide : 1 ≤ 32) N

/-- The cubic phase word budget fits the original logarithmic word
size at every reached proper drawing. This covers quadratic saved
component records and candidate-search workspace. -/
theorem gm06Reached_phase_word_cap
    {k : ℕ} {x : GM06SuccessorInput} {G₀ : Drawing ClosedCylinder}
    {L₀ : CylinderLinkage k G₀} (input : GM06SuccessorInputRep x G₀ L₀)
    (initial : GM06CurrentDrawingRep x G₀ L₀)
    (hinit : initial.tagged = input.graph.initialTagged)
    {ends : List ℕ} {rots paths : List (List ℕ)}
    {G : Drawing ClosedCylinder} {L : CylinderLinkage k G}
    (cur : GM06CurrentDrawingRep {x with endpoints := ends, rotations := rots, linkage := paths} G L)
    {records : List (Option (ℕ × ℕ))}
    (trace : GM06UndoTrace x.vertexCount k initial.undoState cur.undoState records)
    (hG : IsCylinderSection5Drawing k G) :
    10000 * gm06PhaseSize {x with endpoints := ends, rotations := rots, linkage := paths}
      cur.tagged.length ^ 3 < 2 ^ wordSize 32 (gm06SuccessorInputSize x) := by
  have hs := gm06Reached_phase_size_le input initial hinit cur trace hG
  exact (Nat.mul_le_mul_left 10000 (Nat.pow_le_pow_left hs 3)).trans_lt (cubic_phase_budget_fits _)

/-- A polynomial budget in the current phase size is uniformly
polynomial in the original size. This numerical substitution applies
to either complete phase's eventual execution bound. -/
theorem gm06Reached_phase_polynomial_le
    {k : ℕ} {x : GM06SuccessorInput} {G₀ : Drawing ClosedCylinder}
    {L₀ : CylinderLinkage k G₀} (input : GM06SuccessorInputRep x G₀ L₀)
    (initial : GM06CurrentDrawingRep x G₀ L₀)
    (hinit : initial.tagged = input.graph.initialTagged)
    {ends : List ℕ} {rots paths : List (List ℕ)}
    {G : Drawing ClosedCylinder} {L : CylinderLinkage k G}
    (cur : GM06CurrentDrawingRep {x with endpoints := ends, rotations := rots, linkage := paths} G L)
    {records : List (Option (ℕ × ℕ))}
    (trace : GM06UndoTrace x.vertexCount k initial.undoState cur.undoState records)
    (hG : IsCylinderSection5Drawing k G) (C degree : ℕ) :
    C * gm06PhaseSize {x with endpoints := ends, rotations := rots, linkage := paths}
      cur.tagged.length ^ degree ≤ C * 32 ^ degree * (gm06SuccessorInputSize x + 1) ^ degree := by
  have hs := gm06Reached_phase_size_le input initial hinit cur trace hG
  calc
    _ ≤ C * (32 * (gm06SuccessorInputSize x + 1)) ^ degree :=
      Nat.mul_le_mul_left C (Nat.pow_le_pow_left hs degree)
    _ = _ := by rw [mul_pow, Nat.mul_assoc]

end GraphMinor.Compute
