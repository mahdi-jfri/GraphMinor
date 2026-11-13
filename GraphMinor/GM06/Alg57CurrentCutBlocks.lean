module

public import GraphMinor.GM06.Alg57CurrentCutEnds
public import GraphMinor.GM06.Alg57InputCutBlocks
import GraphMinor.GM06.Alg57CuffRotation

/-!
# Current split ends are present and distinct

The current ordinary path words in VI (5.7), page 133, still encode
simple disjoint paths. Their undirected edge indices are distinct.
Decoded incoming and outgoing ends are active ordinary words at their
actual live endpoints. The fixed cuff markers have the two signed
labels of their live sources or targets. These facts supply every
local cut-block field apart from cuff adjacency.
-/

public section
namespace GraphMinor.GM06
open Set GraphMinor.Surface GraphMinor.GM11 GraphMinor.Compute
namespace GM06CurrentDrawingRep
variable {k : ℕ} {x : GM06SuccessorInput} {G : Drawing ClosedCylinder}
  {L : CylinderLinkage k G} (rep : GM06CurrentDrawingRep x G L)
include rep

/-- The disjoint input linkage has globally distinct undirected
edge indices. -/
theorem linkage_edge_indices_nodup : (x.linkage.flatten.map (fun d => d / 2)).Nodup := by
  rw [List.map_flatten]
  apply List.nodup_flatten.mpr
  constructor
  · intro row hr
    obtain ⟨old, hold, rfl⟩ := List.mem_map.mp hr
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hold
    obtain ⟨_, hW, henc, _⟩ := rep.linkage.path ⟨i, rep.linkage.1 ▸ hi⟩
    exact walk_encoding_edge_indices_nodup henc hW
  · rw [List.pairwise_iff_getElem]
    intro i j hi hj hij e hei hej
    have hi' : i < x.linkage.length := by simpa only [List.length_map] using hi
    have hj' : j < x.linkage.length := by simpa only [List.length_map] using hj
    simp only [List.getElem_map] at hei hej
    obtain ⟨a, ha, hae⟩ := List.mem_map.mp hei
    obtain ⟨b, hb, hbe⟩ := List.mem_map.mp hej
    let i' : Fin k := ⟨i, rep.linkage.1 ▸ hi'⟩
    let j' : Fin k := ⟨j, rep.linkage.1 ▸ hj'⟩
    obtain ⟨Wi, _, hiEnc, hiP⟩ := rep.linkage.path i'
    obtain ⟨Wj, _, hjEnc, hjP⟩ := rep.linkage.path j'
    obtain ⟨haBound, _⟩ := hiEnc.active_words a ha
    obtain ⟨hbBound, _⟩ := hjEnc.active_words b hb
    let f := rep.edge ⟨a / 2, by omega⟩
    have hiEdge : f ∈ (L.pathDrawing i').E := by
      rw [← hiP, walkDrawing_E]
      exact (hiEnc.edge_mem_iff f).mpr ⟨a, ha, haBound, rfl⟩
    have hjEdge : f ∈ (L.pathDrawing j').E := by
      rw [← hjP, walkDrawing_E]
      exact (hjEnc.edge_mem_iff f).mpr ⟨b, hb, hbBound,
        congrArg rep.edge (Fin.ext (hbe.trans hae.symm))⟩
    obtain ⟨p, hp⟩ := hiEdge.1
    exact disjoint_left.mp (L.pairwise_disjoint (fun h =>
      (Nat.ne_of_lt hij) (congrArg Fin.val h))) ((hiEdge.2.1 hp).1) ((hjEdge.2.1 hp).1)

/-- The input never traverses both directions of one linkage edge. -/
theorem linkage_not_reverse {d : ℕ} (hd : d ∈ x.linkage.flatten) :
    gm06DartMate d ∉ x.linkage.flatten := by
  intro hm
  have heq := List.inj_on_of_nodup_map rep.linkage_edge_indices_nodup
    hm hd (gm06DartMate_edge d)
  exact gm06DartMate_ne d heq

/-- The interior split case satisfies its complete local cut condition. -/
theorem cut_block_interior (v : Fin x.vertexCount) {a b : ℕ}
    (hp : gm06CutPositionAt (gm06BuildCutTables x.vertexCount rep.tagged.length
      x.endpoints x.linkage x.innerCuff x.outerCuff) v.val = some (.interior a b)) :
    CutBlockOK (.interior a b) (x.rotations.getD v.val []) := by
  obtain ⟨hin, hout⟩ := (computedCutPosition_interior_iff _ _ _ _).mp hp
  obtain ⟨ha, hva⟩ := gm06BuildCutTables_incoming_source x.endpoints x.linkage
    x.innerCuff x.outerCuff v.isLt hin
  obtain ⟨hb, hvb⟩ := gm06BuildCutTables_outgoing_source x.endpoints x.linkage
    x.innerCuff x.outerCuff v.isLt hout
  have hab : a ≠ b := by
    intro heq
    exact rep.linkage_not_reverse hb (heq ▸ ha)
  exact (cutBlockOK_interior_iff _ _ _).mpr
    ⟨rep.ordinary_word_mem_row v a
      (rep.cut_path_end_lt v hp (by simp [GM06CutPosition.pathEnds]))
      (rep.cut_path_end_active v hp (by simp [GM06CutPosition.pathEnds])) hva,
    rep.ordinary_word_mem_row v b (rep.path_word_lt hb)
      (rep.cut_path_end_active v hp (by simp [GM06CutPosition.pathEnds])) hvb, hab⟩

/-- The start split case has the three distinct ends of its row.
Its remaining condition is the order of the two cuff ends. -/
theorem cut_start_end_data (hG : IsCylinderSection5Drawing k G) (v : Fin x.vertexCount)
    {b cp cn : ℕ}
    (hp : gm06CutPositionAt (gm06BuildCutTables x.vertexCount rep.tagged.length
      x.endpoints x.linkage x.innerCuff x.outerCuff) v.val = some (.start b cp cn)) :
    b ∈ x.rotations.getD v.val [] ∧ cp ∈ x.rotations.getD v.val [] ∧
      cn ∈ x.rotations.getD v.val [] ∧ b ≠ cp ∧ b ≠ cn ∧ cp ≠ cn := by
  obtain ⟨i, hi, hcp, hcn⟩ := rep.cut_start_markers hG.1 v hp
  have hbBound := rep.cut_path_end_lt v hp (d := b) (by simp [GM06CutPosition.pathEnds])
  have hout := ((computedCutPosition_start_iff _ _ _ _ _).mp hp).2.1
  have hsource := (gm06BuildCutTables_outgoing_source x.endpoints x.linkage
    x.innerCuff x.outerCuff v.isLt hout).2
  have hcpMem : cp ∈ x.rotations.getD v.val [] := by
    rw [← hi, hcp]
    exact (rep.inner_markers hG i).1
  have hcnMem : cn ∈ x.rotations.getD v.val [] := by
    rw [← hi, hcn, previousCuffIndex_eq_pred]
    simpa only [finSuccCycle_pred_eq] using (rep.inner_markers hG (finPredCycle i)).2
  exact ⟨rep.ordinary_word_mem_row v b hbBound
    (rep.cut_path_end_active v hp (by simp [GM06CutPosition.pathEnds])) hsource, hcpMem, hcnMem,
    by omega, by omega, by omega⟩

/-- The terminal split case has the three distinct ends of its row.
Its remaining condition is the order of the two cuff ends. -/
theorem cut_terminal_end_data (hG : IsCylinderSection5Drawing k G) (v : Fin x.vertexCount)
    {a cp cn : ℕ}
    (hp : gm06CutPositionAt (gm06BuildCutTables x.vertexCount rep.tagged.length
      x.endpoints x.linkage x.innerCuff x.outerCuff) v.val = some (.terminal a cp cn)) :
    a ∈ x.rotations.getD v.val [] ∧ cp ∈ x.rotations.getD v.val [] ∧
      cn ∈ x.rotations.getD v.val [] ∧ a ≠ cp ∧ a ≠ cn ∧ cp ≠ cn := by
  obtain ⟨i, hi, hcp, hcn⟩ := rep.cut_terminal_markers hG.1 v hp
  have haBound := rep.cut_path_end_lt v hp (d := a) (by simp [GM06CutPosition.pathEnds])
  have hin := ((computedCutPosition_terminal_iff _ _ _ _ _).mp hp).1
  have hsource := (gm06BuildCutTables_incoming_source x.endpoints x.linkage
    x.innerCuff x.outerCuff v.isLt hin).2
  have hcpMem : cp ∈ x.rotations.getD v.val [] := by
    rw [← hi, hcp]
    simpa only [Nat.add_assoc] using (rep.outer_markers hG i).1
  have hcnMem : cn ∈ x.rotations.getD v.val [] := by
    rw [← hi, hcn, previousCuffIndex_eq_pred]
    simpa only [finSuccCycle_pred_eq, Nat.add_assoc] using
      (rep.outer_markers hG (finPredCycle i)).2
  exact ⟨rep.ordinary_word_mem_row v a haBound
    (rep.cut_path_end_active v hp (by simp [GM06CutPosition.pathEnds])) hsource, hcpMem, hcnMem,
    by omega, by omega, by omega⟩

end GM06CurrentDrawingRep
end GraphMinor.GM06
