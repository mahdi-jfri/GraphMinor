module

public import GraphMinor.GM06.Alg57InputWordBounds
public import GraphMinor.Compute.GM06EarlyReductionProgram
import GraphMinor.GM06.Alg57RowBounds

/-!
# Original-input bounds at every reached reduction state

The history for VI (5.7), page 133, preserves the number of original
edge slots. The vertex slots and cuff labels also remain fixed.
Thus the logarithmic word size chosen from the ordinary input
continues to hold the current codes and the early-scan workspace.

Each stored inverse pair is charged to a deleted actual vertex.
A reached proper drawing has a vertex, so the original history
allocation still has room for the next pair. The early-round time
bound is uniform in the original input size, regardless of previous
reroutings and contractions.
-/

public section
namespace GraphMinor.Compute
open Set GraphMinor.Surface GraphMinor.GM06 GraphMinor.GM11 TwoPaths

section Reached
variable {k : ℕ} {x : GM06SuccessorInput} {G₀ : Drawing ClosedCylinder}
  {L₀ : CylinderLinkage k G₀}
  (input : GM06SuccessorInputRep x G₀ L₀)
  (initial : GM06CurrentDrawingRep x G₀ L₀)
  (hinit : initial.tagged = input.graph.initialTagged)
  {ends : List ℕ} {rots paths : List (List ℕ)}
  {G : Drawing ClosedCylinder} {L : CylinderLinkage k G}
  (cur : GM06CurrentDrawingRep {x with endpoints := ends, rotations := rots, linkage := paths} G L)
  {records : List (Option (ℕ × ℕ))}
  (trace : GM06UndoTrace x.vertexCount k initial.undoState cur.undoState records)
include input initial hinit cur trace

/-- A reached current relation keeps exactly the original edge slots. -/
theorem gm06Reached_tagged_length : cur.tagged.length = G₀.E.ncard := by
  have hlength := trace.tagged_length
  change cur.tagged.length = initial.tagged.length at hlength
  rw [hinit, GM06SuccessorGraphRep.initialTagged, List.length_map] at hlength
  exact hlength.trans input.graph.pairCount_eq

/-- The word size from the original input still holds every current
rotation and linkage code used in the early branches. -/
theorem gm06Reached_word_caps
    (hG₀ : IsCylinderSection5Drawing k G₀) (hG : IsCylinderSection5Drawing k G) :
    let w := wordSize 32 (gm06SuccessorInputSize x)
    3 < 2 ^ w ∧ x.vertexCount * x.vertexCount < 2 ^ w ∧
      4 * (1 + x.vertexCount + 2 * cur.tagged.length + 4 * k) < 2 ^ w ∧
      4 * (gm06EncodeRows rots).length < 2 ^ w ∧
      (gm06EncodeRows paths).length < 2 ^ w ∧
      (∀ z ∈ gm06EncodeRows rots, z < 2 ^ w) ∧
      ∀ z ∈ gm06EncodeRows paths, z < 2 ^ w := by
  obtain ⟨hw, hsquare, hbudget, _, _, _⟩ := input.initial_word_caps hG₀
  have htag := gm06Reached_tagged_length input initial hinit cur trace
  have hbudget' : 4 * (1 + x.vertexCount + 2 * cur.tagged.length + 4 * k) <
      2 ^ wordSize 32 (gm06SuccessorInputSize x) := by rw [htag]; exact hbudget
  exact ⟨hw, hsquare, hbudget', cur.scan_word_bounds hG hbudget'⟩

/-- The concrete early-round budget is uniformly quartic in the
original ordinary input size. It does not grow with the history. -/
theorem gm06Reached_early_cost_le (hG : IsCylinderSection5Drawing k G) :
    gm06EarlyReductionsCost x.vertexCount cur.tagged.length k
      (gm06EncodeRows rots).length (gm06EncodeRows paths).length paths.flatten.length ≤
      5062500000 * (gm06SuccessorInputSize x + 1) ^ 4 := by
  obtain ⟨hn, hm, hk, _, _, _⟩ := input.size_bounds
  have htag := gm06Reached_tagged_length input initial hinit cur trace
  have hr := (cur.rotation_length_bounds hG).2
  have hp := cur.linkage.length_bounds.2.2
  have hf := cur.linkage.length_bounds.2.1
  change (gm06EncodeRows rots).length ≤ 1 + x.vertexCount + 2 * (cur.tagged.length + (k + k)) at hr
  change (gm06EncodeRows paths).length ≤ 1 + k + 2 * cur.tagged.length at hp
  change paths.flatten.length ≤ 2 * cur.tagged.length at hf
  rw [htag] at hr hp hf
  have hsum : 1 + x.vertexCount + cur.tagged.length + k +
      (gm06EncodeRows rots).length + (gm06EncodeRows paths).length + paths.flatten.length ≤
      15 * (gm06SuccessorInputSize x + 1) := by
    rw [htag]
    omega
  calc
    gm06EarlyReductionsCost x.vertexCount cur.tagged.length k
        (gm06EncodeRows rots).length (gm06EncodeRows paths).length paths.flatten.length ≤
      100000 * (1 + x.vertexCount + cur.tagged.length + k +
        (gm06EncodeRows rots).length + (gm06EncodeRows paths).length + paths.flatten.length) ^ 4 :=
      gm06EarlyReductionsCost_le_quartic _ _ _ _ _ _
    _ ≤ 100000 * (15 * (gm06SuccessorInputSize x + 1)) ^ 4 :=
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hsum 4)
    _ = 5062500000 * (gm06SuccessorInputSize x + 1) ^ 4 := by ring

end Reached

/-- The allocated original-input history has a free pair slot at
every reached proper drawing. This follows from the actual inverse
history's vertex credit and the original vertex-label bijection. -/
theorem gm06Reached_history_free_slot
    {k : ℕ} {x : GM06SuccessorInput} {G₀ : Drawing ClosedCylinder}
    {L₀ : CylinderLinkage k G₀} (input : GM06SuccessorInputRep x G₀ L₀)
    (initial : GM06CurrentDrawingRep x G₀ L₀)
    {ends : List ℕ} {rots paths : List (List ℕ)}
    {G : Drawing ClosedCylinder} {L : CylinderLinkage k G}
    (cur : GM06CurrentDrawingRep {x with endpoints := ends, rotations := rots, linkage := paths} G L)
    {records : List (Option (ℕ × ℕ))}
    (trace : GM06UndoTrace x.vertexCount k initial.undoState cur.undoState records)
    (hG : IsCylinderSection5Drawing k G) :
    2 * (records.filterMap id).length + 1 < 2 * (x.vertexCount + G₀.E.ncard) := by
  let i : Fin k := ⟨0, hG.1⟩
  have hnonempty : G.V.Nonempty := ⟨cur.vertex (cur.source i), cur.vertex_mem _ (cur.source_live i)⟩
  have hfree := trace.history_free_slot hnonempty
  change 2 * (records.filterMap id).length + 1 < 2 * (G₀.V.ncard + G₀.E.ncard) at hfree
  have hcount : x.vertexCount = G₀.V.ncard := input.graph.vertexCount_eq
  rw [hcount]
  exact hfree

/-- The number of numeric inverse records never exceeds the original
vertex count, independently of the number of rerouting rounds. -/
theorem gm06Reached_history_count_le
    {k : ℕ} {x : GM06SuccessorInput} {G₀ : Drawing ClosedCylinder}
    {L₀ : CylinderLinkage k G₀} (input : GM06SuccessorInputRep x G₀ L₀)
    (initial : GM06CurrentDrawingRep x G₀ L₀)
    {ends : List ℕ} {rots paths : List (List ℕ)}
    {G : Drawing ClosedCylinder} {L : CylinderLinkage k G}
    (cur : GM06CurrentDrawingRep {x with endpoints := ends, rotations := rots, linkage := paths} G L)
    {records : List (Option (ℕ × ℕ))}
    (trace : GM06UndoTrace x.vertexCount k initial.undoState cur.undoState records) :
    (records.filterMap id).length ≤ x.vertexCount := by
  have hcredit := trace.history_length_le
  change G.V.ncard + (records.filterMap id).length ≤ G₀.V.ncard at hcredit
  have hcount : x.vertexCount = G₀.V.ncard := input.graph.vertexCount_eq
  omega

end GraphMinor.Compute
