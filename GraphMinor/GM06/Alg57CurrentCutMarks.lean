module

public import GraphMinor.GM06.Alg57CurrentCutPathKeys
public import GraphMinor.GM06.Alg57InputCutMarks
import GraphMinor.GM06.Section5LinkageEnds
import GraphMinor.GM06.Section4PathTools
import GraphMinor.GM06.Section5EndpointObstruction

/-!
# The computed positions in the current linkage

In VI (5.7), page 133, a marked current vertex with no arriving
end is a source, and one with no leaving end is a target. The walk
interpretation proves these facts directly from the computed tables.
Only live labels are compared: a retired slot has no prescribed point
meaning. Thus no injectivity assumption on retired slots is needed.
-/

public section
namespace GraphMinor.GM06
open Set GraphMinor.Surface GraphMinor.GM11 GraphMinor.Compute

private theorem walk_getLast_support {α β : Type*} {Gr : Graph α β} {s t : α}
    (W : GraphWalk Gr s t) : W.support.getLast W.support_ne_nil = t := by
  induction W with
  | nil h => rfl
  | cons hl R ih =>
    change (_ :: R.support).getLast _ = _
    rw [List.getLast_cons R.support_ne_nil]
    exact ih

private theorem walk_end_not_mem_dropLast {α β : Type*} {Gr : Graph α β} {s t : α}
    (W : GraphWalk Gr s t) (hW : W.IsSimple) : t ∉ W.support.dropLast := by
  have heq : W.support.dropLast ++ [t] = W.support := by
    calc
      _ = W.support.dropLast ++ [W.support.getLast W.support_ne_nil] :=
        congrArg (fun a => W.support.dropLast ++ [a]) (walk_getLast_support W).symm
      _ = W.support := List.dropLast_append_getLast W.support_ne_nil
  have hn : (W.support.dropLast ++ [t]).Nodup := heq.symm ▸ hW
  have hd := (List.nodup_append.mp hn).2.2
  exact fun ht => hd t ht t (List.mem_cons_self) rfl

namespace GM06CurrentDrawingRep
variable {k : ℕ} {x : GM06SuccessorInput} {G : Drawing ClosedCylinder}
  {L : CylinderLinkage k G} (rep : GM06CurrentDrawingRep x G L)
include rep

/-- No path arrives at an initial vertex: its own simple path
starts there, and the other linkage paths are disjoint. -/
theorem source_incoming_zero (i : Fin k) :
    (gm06BuildCutTables x.vertexCount rep.tagged.length x.endpoints
      x.linkage x.innerCuff x.outerCuff).incoming[(rep.source i).val]?.getD 0 = 0 := by
  apply (path_mark_zero_iff x.endpoints x.linkage true (rep.source i)
    (rep.cut_path_keys_nodup true)).mpr
  rw [gm06CutPathEndPairs_keys, List.map_flatten]
  intro hm
  obtain ⟨row, hrow, hv⟩ := List.mem_flatten.mp hm
  obtain ⟨old, hold, rfl⟩ := List.mem_map.mp hrow
  obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hold
  let j' : Fin k := ⟨j, rep.linkage.1 ▸ hj⟩
  obtain ⟨W, hW, henc, hP⟩ := rep.linkage.path j'
  have hvW := (rep.path_key_mem_iff j' true (rep.source i) (rep.source_live i) W henc).mp hv
  change rep.vertex (rep.source i) ∈ W.support.tail at hvW
  rw [show rep.vertex (rep.source i) = cylinderM1Point k i from rep.source_point i] at hvW
  by_cases hji : j' = i
  · subst i
    have hn : W.support.Nodup := hW
    rw [W.support_eq_cons] at hn
    exact (List.nodup_cons.mp hn).1 hvW
  · have hvP : cylinderM1Point k i ∈ (L.pathDrawing j').V := by
      rw [← hP, walkDrawing_V]
      exact (List.tail_sublist _).subset hvW
    exact disjoint_left.mp (L.pairwise_disjoint hji)
      ((L.pathDrawing j').V_subset_U hvP)
      ((L.pathDrawing i).V_subset_U (isPathDrawing_end_vertices (L.isPath i)).1)

/-- Every current initial vertex has a leaving path mark. -/
theorem source_outgoing_pos (i : Fin k) :
    (gm06BuildCutTables x.vertexCount rep.tagged.length x.endpoints
      x.linkage x.innerCuff x.outerCuff).outgoing[(rep.source i).val]?.getD 0 ≠ 0 := by
  intro hz
  have hnot := (path_mark_zero_iff x.endpoints x.linkage false (rep.source i)
    (rep.cut_path_keys_nodup false)).mp hz
  rw [gm06CutPathEndPairs_keys, List.map_flatten] at hnot
  obtain ⟨W, _, henc, _⟩ := rep.linkage.path i
  have hs : rep.vertex (rep.source i) ∈ W.support.dropLast := by
    rw [rep.source_point]
    apply List.mem_dropLast_of_mem_of_ne_getLast W.start_mem_support
    intro heq
    exact isPathDrawing_start_ne_end (L.isPath i) (heq.trans (walk_getLast_support W))
  apply hnot
  apply List.mem_flatten.mpr
  refine ⟨_, List.mem_map.mpr ⟨_, List.getElem_mem (show i.val < x.linkage.length by
    rw [rep.linkage.1]; exact i.isLt), rfl⟩, ?_⟩
  exact (rep.path_key_mem_iff i false (rep.source i) (rep.source_live i) W henc).mpr hs

/-- No path leaves a terminal vertex of the linkage. -/
theorem terminal_outgoing_zero (i : Fin k) (a : Fin x.vertexCount)
    (ha : rep.vertex a = L.curve i 1) (haLive : a ∈ rep.live) :
    (gm06BuildCutTables x.vertexCount rep.tagged.length x.endpoints
      x.linkage x.innerCuff x.outerCuff).outgoing[a.val]?.getD 0 = 0 := by
  apply (path_mark_zero_iff x.endpoints x.linkage false a
    (rep.cut_path_keys_nodup false)).mpr
  rw [gm06CutPathEndPairs_keys, List.map_flatten]
  intro hm
  obtain ⟨row, hrow, hv⟩ := List.mem_flatten.mp hm
  obtain ⟨old, hold, rfl⟩ := List.mem_map.mp hrow
  obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hold
  let j' : Fin k := ⟨j, rep.linkage.1 ▸ hj⟩
  obtain ⟨W, hW, henc, hP⟩ := rep.linkage.path j'
  have hvW := (rep.path_key_mem_iff j' false a haLive W henc).mp hv
  change rep.vertex a ∈ W.support.dropLast at hvW
  rw [ha] at hvW
  by_cases hji : j' = i
  · subst i
    exact walk_end_not_mem_dropLast W hW hvW
  · have hvP : L.curve i 1 ∈ (L.pathDrawing j').V := by
      rw [← hP, walkDrawing_V]
      exact (List.dropLast_sublist _).subset hvW
    exact disjoint_left.mp (L.pairwise_disjoint hji)
      ((L.pathDrawing j').V_subset_U hvP)
      ((L.pathDrawing i).V_subset_U (isPathDrawing_end_vertices (L.isPath i)).2)

/-- Every terminal vertex has an arriving path mark. -/
theorem terminal_incoming_pos (i : Fin k) (a : Fin x.vertexCount)
    (ha : rep.vertex a = L.curve i 1) (haLive : a ∈ rep.live) :
    (gm06BuildCutTables x.vertexCount rep.tagged.length x.endpoints
      x.linkage x.innerCuff x.outerCuff).incoming[a.val]?.getD 0 ≠ 0 := by
  intro hz
  have hnot := (path_mark_zero_iff x.endpoints x.linkage true a
    (rep.cut_path_keys_nodup true)).mp hz
  rw [gm06CutPathEndPairs_keys, List.map_flatten] at hnot
  obtain ⟨W, hW, henc, _⟩ := rep.linkage.path i
  have ht : L.curve i 1 ∈ W.support.tail := by
    have hh := W.end_mem_support
    rw [W.support_eq_cons] at hh
    rcases List.mem_cons.mp hh with hh | hh
    · exact False.elim (isPathDrawing_start_ne_end (L.isPath i) hh.symm)
    · exact hh
  apply hnot
  apply List.mem_flatten.mpr
  refine ⟨_, List.mem_map.mpr ⟨_, List.getElem_mem (show i.val < x.linkage.length by
    rw [rep.linkage.1]; exact i.isLt), rfl⟩, ?_⟩
  exact (rep.path_key_mem_iff i true a haLive W henc).mpr (ha.symm ▸ ht)

/-- A marked vertex with no incoming end is one of the supplied
initial cuff labels. -/
theorem source_of_marks (v : Fin x.vertexCount)
    (hin : (gm06BuildCutTables x.vertexCount rep.tagged.length x.endpoints
      x.linkage x.innerCuff x.outerCuff).incoming[v.val]?.getD 0 = 0)
    (hout : (gm06BuildCutTables x.vertexCount rep.tagged.length x.endpoints
      x.linkage x.innerCuff x.outerCuff).outgoing[v.val]?.getD 0 ≠ 0) :
    ∃ i : Fin k, rep.source i = v := by
  set marks := gm06BuildCutTables x.vertexCount rep.tagged.length x.endpoints
    x.linkage x.innerCuff x.outerCuff
  obtain ⟨b, hb⟩ : ∃ b, marks.outgoing[v.val]?.getD 0 = b + 1 :=
    ⟨marks.outgoing[v.val]?.getD 0 - 1, by change marks.outgoing[v.val]?.getD 0 ≠ 0 at hout; omega⟩
  obtain ⟨hd, horg⟩ := gm06BuildCutTables_outgoing_source x.endpoints x.linkage
    x.innerCuff x.outerCuff v.isLt hb
  obtain ⟨row, hr, hd⟩ := List.mem_flatten.mp hd
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hr
  let i' : Fin k := ⟨i, rep.linkage.1 ▸ hi⟩
  obtain ⟨W, _, henc, _⟩ := rep.linkage.path i'
  obtain ⟨q, hq, hqLive, _⟩ := rep.path_origin_mem i' false hd
  have hqv : q = v := Fin.ext (hq.symm.trans horg)
  have hvLive : v ∈ rep.live := hqv ▸ hqLive
  have hvkey : v.val ∈ (x.linkage[i]).map (fun d => x.endpoints[d]?.getD 0) :=
    List.mem_map.mpr ⟨b, hd, horg⟩
  have hvW : rep.vertex v ∈ W.support :=
    (List.dropLast_sublist _).subset ((rep.path_key_mem_iff i' false v hvLive W henc).mp hvkey)
  have hstart : rep.vertex v = cylinderM1Point k i' := by
    rw [W.support_eq_cons] at hvW
    rcases List.mem_cons.mp hvW with h | h
    · exact h
    · have hvkey' := (rep.path_key_mem_iff i' true v hvLive W henc).mpr h
      have hnot := (path_mark_zero_iff x.endpoints x.linkage true v
        (rep.cut_path_keys_nodup true)).mp hin
      rw [gm06CutPathEndPairs_keys, List.map_flatten] at hnot
      exact False.elim (hnot (List.mem_flatten.mpr ⟨_,
        List.mem_map.mpr ⟨_, List.getElem_mem hi, rfl⟩, hvkey'⟩))
  refine ⟨i', rep.vertex_inj (rep.source_live i') hvLive ?_⟩
  exact (rep.source_point i').trans hstart.symm

/-- A marked vertex with no outgoing end is one of the supplied
terminal cuff labels. -/
theorem target_of_marks (v : Fin x.vertexCount)
    (hin : (gm06BuildCutTables x.vertexCount rep.tagged.length x.endpoints
      x.linkage x.innerCuff x.outerCuff).incoming[v.val]?.getD 0 ≠ 0)
    (hout : (gm06BuildCutTables x.vertexCount rep.tagged.length x.endpoints
      x.linkage x.innerCuff x.outerCuff).outgoing[v.val]?.getD 0 = 0) :
    ∃ i : Fin k, rep.target i = v := by
  set marks := gm06BuildCutTables x.vertexCount rep.tagged.length x.endpoints
    x.linkage x.innerCuff x.outerCuff
  obtain ⟨a, ha⟩ : ∃ a, marks.incoming[v.val]?.getD 0 = a + 1 :=
    ⟨marks.incoming[v.val]?.getD 0 - 1, by change marks.incoming[v.val]?.getD 0 ≠ 0 at hin; omega⟩
  obtain ⟨hd, horg⟩ := gm06BuildCutTables_incoming_source x.endpoints x.linkage
    x.innerCuff x.outerCuff v.isLt ha
  obtain ⟨row, hr, hd⟩ := List.mem_flatten.mp hd
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hr
  let i' : Fin k := ⟨i, rep.linkage.1 ▸ hi⟩
  obtain ⟨W, _, henc, _⟩ := rep.linkage.path i'
  obtain ⟨q, hq, hqLive, _⟩ := rep.path_origin_mem i' true hd
  have hq' : x.endpoints[a]?.getD 0 = q.val := by
    simpa only [gm06DartMate_involutive a, ↓reduceIte] using hq
  have hqv : q = v := Fin.ext (hq'.symm.trans horg)
  have hvLive : v ∈ rep.live := hqv ▸ hqLive
  have hvkey : v.val ∈ (x.linkage[i]).map (fun d => x.endpoints[gm06DartMate d]?.getD 0) :=
    List.mem_map.mpr ⟨gm06DartMate a, hd, by simpa only [gm06DartMate_involutive a] using horg⟩
  have hvW : rep.vertex v ∈ W.support :=
    (List.tail_sublist _).subset ((rep.path_key_mem_iff i' true v hvLive W henc).mp hvkey)
  have hend : rep.vertex v = L.curve i' 1 := by
    by_contra hne
    have hvLast : rep.vertex v ≠ W.support.getLast W.support_ne_nil :=
      fun h => hne (h.trans (walk_getLast_support W))
    have hvkey' := (rep.path_key_mem_iff i' false v hvLive W henc).mpr
      (List.mem_dropLast_of_mem_of_ne_getLast hvW hvLast)
    have hnot := (path_mark_zero_iff x.endpoints x.linkage false v
      (rep.cut_path_keys_nodup false)).mp hout
    rw [gm06CutPathEndPairs_keys, List.map_flatten] at hnot
    exact hnot (List.mem_flatten.mpr ⟨_,
      List.mem_map.mpr ⟨_, List.getElem_mem hi, rfl⟩, hvkey'⟩)
  obtain ⟨j, hj⟩ := L.curve_one_mem i'
  refine ⟨j, rep.vertex_inj (rep.target_live j) hvLive ?_⟩
  exact (rep.target_point j).trans (hj.trans hend.symm)

end GM06CurrentDrawingRep
end GraphMinor.GM06
