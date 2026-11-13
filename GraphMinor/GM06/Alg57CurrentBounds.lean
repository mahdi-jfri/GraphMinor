module

public import GraphMinor.GM06.Alg57CurrentUndo
public import GraphMinor.GM06.Alg57ReductionMeasure
public import GraphMinor.Compute.GM06PruneRotations
public import GraphMinor.Compute.GM02BalancedSeparationInput
import GraphMinor.GM06.Alg57CurrentRows
import GraphMinor.GM06.Alg57RowBounds
import GraphMinor.Compute.GM06ActiveEdgeLabels
import Mathlib.Data.Set.Card

/-!
# Uniform bounds for each reached current state

The loop in VI (5.7), page 133, retains its original vertex and
edge slots. Actual directed ends have distinct permanent words,
and all words lie below twice the original augmented edge count.
The linkage paths are simple and disjoint. These facts bound both
current row tables and all their headers independently of the
number of earlier reductions. The actual drawing size is bounded
by its original ordinary slots, which bounds the decreasing measure.
-/

public section
namespace GraphMinor.Compute

/-- The loop's integer measure, read from its actual live and active
masks and its persistent bit. This is `2μ+b` in Lemma 19 of the
implementation of VI (5.7), page 133. -/
@[expose] def gm06LoopMeasure (s : State) : ℕ :=
  2 * ((s.arrs 14).sum + (s.arrs 12).count 1) + s.regs 329

end GraphMinor.Compute
namespace GraphMinor.GM06
open Set GraphMinor.Surface GraphMinor.GM11 GraphMinor.Compute

private theorem activity_count_eq_filter_length {α : Type*} (tagged : List (α × ℕ)) :
    (tagged.map Prod.snd).count 1 = (tagged.filter (fun p => p.2 == 1)).length := by
  induction tagged with
  | nil => rfl
  | cons p tagged ih =>
    by_cases hp : p.2 = 1 <;> simp [hp, ih]

/-- The active ordinary edge flags count precisely the actual
remaining edges, even though permanent labels may contain gaps. -/
theorem GM06CurrentDrawingRep.edge_ncard_eq_activity_count
    {k : ℕ} {x : GM06SuccessorInput} {G : Drawing ClosedCylinder}
    {L : CylinderLinkage k G} (rep : GM06CurrentDrawingRep x G L) :
    G.E.ncard = (rep.tagged.map Prod.snd).count 1 := by
  obtain ⟨e, _⟩ := exists_active_edge_position_equiv rep.tagged rep.edge G.E rep.edge_inj
    (fun j hj => (rep.links j hj).edge_mem) rep.edge_cover
  have hc : G.E.ncard = (gm06ActiveEdgeIndices rep.tagged).length := by
    simpa only [Nat.card_fin, Nat.card_coe_set_eq] using (Nat.card_congr e).symm
  have hl := congrArg List.length (gm06ActiveEdgeIndices_map_get rep.tagged)
  simp only [List.length_map] at hl
  exact hc.trans (hl.trans (activity_count_eq_filter_length rep.tagged).symm)

/-- The actual RAM measure is exactly the mathematical drawing
measure in the chronological invariant. It therefore has no choice
of geometric representative hidden in its definition. -/
theorem GM06CurrentDrawingRep.ram_measure_eq
    {k : ℕ} {x : GM06SuccessorInput} {G : Drawing ClosedCylinder}
    {L : CylinderLinkage k G} (rep : GM06CurrentDrawingRep x G L)
    (s : State) (b : Bool) (h12 : s.arrs 12 = rep.tagged.map Prod.snd)
    (h14 : s.arrs 14 = gm02VertexBits rep.live) (h329 : s.regs 329 = b.toNat) :
    gm06LoopMeasure s = (Alg57DrawingState.mk G L b).measure := by
  have hlive : (gm02VertexBits rep.live).sum = rep.live.card := by
    change (bitSetList rep.live).sum = rep.live.card
    exact sum_bitSetList _
  rw [gm06LoopMeasure, h12, h14, h329, hlive,
    ← rep.vertex_ncard_eq_live_card, ← rep.edge_ncard_eq_activity_count]
  rfl

/-- Current ordinary edges use at most the original edge-slot count. -/
theorem GM06CurrentDrawingRep.edge_ncard_le
    {k : ℕ} {x : GM06SuccessorInput} {G : Drawing ClosedCylinder}
    {L : CylinderLinkage k G} (rep : GM06CurrentDrawingRep x G L) :
    G.E.ncard ≤ rep.tagged.length := by
  have hsub : G.E ⊆ range rep.edge := by
    intro e he
    obtain ⟨j, _, hj⟩ := rep.edge_cover e he
    exact ⟨j, hj⟩
  exact (Set.ncard_le_ncard hsub (Set.finite_range _)).trans (by
    simpa only [Set.image_univ, Set.ncard_univ, Nat.card_fin] using
      (Set.ncard_image_le (f := rep.edge) (s := Set.univ) (Set.finite_univ)))

/-- The ordinary drawing size is bounded by its permanent slot counts. -/
theorem GM06CurrentDrawingRep.size_le_slots
    {k : ℕ} {x : GM06SuccessorInput} {G : Drawing ClosedCylinder}
    {L : CylinderLinkage k G} (rep : GM06CurrentDrawingRep x G L) :
    G.V.ncard + G.E.ncard ≤ x.vertexCount + rep.tagged.length :=
  Nat.add_le_add rep.vertex_ncard_le rep.edge_ncard_le

/-- Every current rotation word lies in the fixed augmented dart space,
including words read in a retired row, whose row is empty. -/
theorem GM06CurrentDrawingRep.rotation_word_lt
    {k : ℕ} {x : GM06SuccessorInput} {G : Drawing ClosedCylinder}
    {L : CylinderLinkage k G} (rep : GM06CurrentDrawingRep x G L)
    (hG : IsCylinderSection5Drawing k G) {d : ℕ} (hd : d ∈ x.rotations.flatten) :
    d < 2 * (rep.tagged.length + (k + k)) := by
  obtain ⟨row, hr, hd⟩ := List.mem_flatten.mp hd
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hr
  let a : Fin x.vertexCount := ⟨i, rep.rows_length ▸ hi⟩
  exact rep.row_word_lt hG (a := a) (by simpa only [a, List.getD_eq_getElem _ [] hi] using hd)

/-- The complete current rotation table remains linear in the original
augmented dart space, even after original labels have been retired. -/
theorem GM06CurrentDrawingRep.rotation_length_bounds
    {k : ℕ} {x : GM06SuccessorInput} {G : Drawing ClosedCylinder}
    {L : CylinderLinkage k G} (rep : GM06CurrentDrawingRep x G L)
    (hG : IsCylinderSection5Drawing k G) :
    x.rotations.flatten.length ≤ 2 * (rep.tagged.length + (k + k)) ∧
      (gm06EncodeRows x.rotations).length ≤ 1 + x.vertexCount + 2 * (rep.tagged.length + (k + k)) := by
  classical
  have hbound : x.rotations.flatten.length ≤ 2 * (rep.tagged.length + (k + k)) := by
    rw [← List.toFinset_card_of_nodup rep.rows_flatten_nodup]
    have hh : x.rotations.flatten.toFinset ⊆ Finset.range (2 * (rep.tagged.length + (k + k))) := by
      intro d hd
      exact Finset.mem_range.mpr (rep.rotation_word_lt hG (List.mem_toFinset.mp hd))
    exact (Finset.card_le_card hh).trans_eq (Finset.card_range _)
  refine ⟨hbound, ?_⟩
  rw [gm06EncodeRows_length, rep.rows_length]
  omega

/-- All current rotation-code words, including length headers, have
one uniform bound derived from the actual rows. -/
theorem GM06CurrentDrawingRep.rotation_code_words_le
    {k : ℕ} {x : GM06SuccessorInput} {G : Drawing ClosedCylinder}
    {L : CylinderLinkage k G} (rep : GM06CurrentDrawingRep x G L)
    (hG : IsCylinderSection5Drawing k G) :
    ∀ z ∈ gm06EncodeRows x.rotations, z ≤ x.vertexCount + 2 * (rep.tagged.length + (k + k)) := by
  apply gm06EncodeRows_words_le
  · rw [rep.rows_length]
    omega
  · exact (rep.rotation_length_bounds hG).1.trans (by omega)
  · intro d hd
    exact (rep.rotation_word_lt hG hd).le.trans (by omega)

/-- The uniform row budget supplies all row-count and row-length
bounds used in the two initial-vertex scans. -/
theorem GM06CurrentDrawingRep.scan_row_bounds
    {k : ℕ} {x : GM06SuccessorInput} {G : Drawing ClosedCylinder}
    {L : CylinderLinkage k G} (rep : GM06CurrentDrawingRep x G L)
    (hG : IsCylinderSection5Drawing k G) :
    let B := 1 + x.vertexCount + 2 * rep.tagged.length + 4 * k
    k ≤ B ∧ x.rotations.length ≤ B ∧
      (∀ row ∈ x.linkage, row.length ≤ B) ∧
      ∀ row ∈ x.rotations, row.length ≤ B := by
  dsimp only
  refine ⟨by omega, by rw [rep.rows_length]; omega, ?_, ?_⟩
  · intro row hr
    have hh := (List.sublist_flatten_of_mem hr).length_le
    have hb := rep.linkage.length_bounds.2.1
    omega
  · intro row hr
    have hh := (List.sublist_flatten_of_mem hr).length_le
    have hb := (rep.rotation_length_bounds hG).1
    omega

/-- A single original-slot word bound supplies the current rotation
and linkage code bounds used on every return to the main loop. -/
theorem GM06CurrentDrawingRep.scan_word_bounds
    {w k : ℕ} {x : GM06SuccessorInput} {G : Drawing ClosedCylinder}
    {L : CylinderLinkage k G} (rep : GM06CurrentDrawingRep x G L)
    (hG : IsCylinderSection5Drawing k G)
    (hcap : 4 * (1 + x.vertexCount + 2 * rep.tagged.length + 4 * k) < 2 ^ w) :
    4 * (gm06EncodeRows x.rotations).length < 2 ^ w ∧
      (gm06EncodeRows x.linkage).length < 2 ^ w ∧
      (∀ z ∈ gm06EncodeRows x.rotations, z < 2 ^ w) ∧
      ∀ z ∈ gm06EncodeRows x.linkage, z < 2 ^ w := by
  have hr := (rep.rotation_length_bounds hG).2
  have hp := rep.linkage.length_bounds.2.2
  refine ⟨by omega, by omega, ?_, ?_⟩
  · intro z hz
    have hh := rep.rotation_code_words_le hG z hz
    omega
  · intro z hz
    have hh := rep.linkage.code_words_le z hz
    omega

end GraphMinor.GM06
