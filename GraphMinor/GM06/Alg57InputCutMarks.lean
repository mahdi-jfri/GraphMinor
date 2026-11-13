module

public import GraphMinor.GM06.Alg57CutPathKeys
public import GraphMinor.GM06.Alg57ComputedCutChains
import GraphMinor.GM06.Section5LinkageEnds
import GraphMinor.GM06.Section5EndpointObstruction
import GraphMinor.GM06.Section4PathTools

/-!
# Reading computed path marks in the input drawing

For the linkage cut in VI (5.7), page 133, a zero mark says that
no path arrives at, or leaves, the vertex in question. The two
path-key lists have no repetitions. Their membership is read from
the actual path walks, without supplying path positions or marks.
In particular, a marked start is an initial cuff vertex and a
marked terminal is a terminal cuff vertex.
-/

public section
namespace GraphMinor.GM06
open Set GraphMinor.Surface GraphMinor.GM11 GraphMinor.Compute

/-- A path-end scatter stores zero exactly at keys which receive
no write. Every write stores a directed word plus one. -/
theorem path_mark_zero_iff {n : ℕ} (origins : List ℕ) (paths : List (List ℕ))
    (incoming : Bool) (v : Fin n)
    (hn : ((gm06CutPathEndPairs origins paths.flatten incoming).map Prod.fst).Nodup) :
    (gm06Scatter (gm06CutPathEndPairs origins paths.flatten incoming)
      (List.replicate n 0))[v.val]?.getD 0 = 0 ↔
        v.val ∉ (gm06CutPathEndPairs origins paths.flatten incoming).map Prod.fst := by
  constructor
  · intro hz hmem
    obtain ⟨p, hp, hv⟩ := List.mem_map.mp hmem
    obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hp
    change origins[if incoming then gm06DartMate d else d]?.getD 0 = v.val at hv
    have hlookup := gm06Scatter_getElem?_of_mem _ (List.replicate n 0) hn
      _ (gm06CutPathEndPairs_mem origins paths.flatten incoming d hd)
      (by simpa only [List.length_replicate, hv] using v.isLt)
    rw [hv] at hlookup
    rw [hlookup] at hz
    simp only [Option.getD_some] at hz
    omega
  · intro hnot
    rw [gm06Scatter_getElem?_of_not_mem _ _ _ hnot]
    simp only [List.getElem?_replicate, v.isLt, ↓reduceIte, Option.getD_some]

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

namespace GM06SuccessorInputRep
variable {k : ℕ} {x : GM06SuccessorInput} {G : Drawing ClosedCylinder}
  {L : CylinderLinkage k G} (rep : GM06SuccessorInputRep x G L)
include rep

private theorem input_endpoint_words : x.endpoints = gm06EndpointWords
    (rep.graph.initialTagged.map fun p => (p.1.1.val, p.1.2.val)) := by
  simpa only [GM06SuccessorGraphRep.initialTagged, List.map_map, Function.comp_def]
    using rep.graph.endpoints

/-- Every path-end origin lies in the supplied vertex-label space. -/
theorem cut_path_origin_lt (incoming : Bool) {d : ℕ} (hd : d ∈ x.linkage.flatten) :
    x.endpoints[if incoming then gm06DartMate d else d]?.getD 0 < x.vertexCount := by
  obtain ⟨row, hr, hd⟩ := List.mem_flatten.mp hd
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hr
  obtain ⟨a, ha, _⟩ := rep.path_origin_mem ⟨i, rep.linkage.1 ▸ hi⟩ incoming hd
  rw [ha]
  exact a.isLt

/-- The keys of one actual path row are its vertices with its
first or last vertex removed, according to the chosen orientation. -/
theorem path_key_mem_iff (i : Fin k) (incoming : Bool) (a : Fin x.vertexCount)
    (W : GraphWalk G.toGraph (cylinderM1Point k i) (L.curve i 1))
    (henc : GM06WalkDartEncoding G.toGraph rep.graph.initialTagged
      rep.graph.vertexLabels rep.graph.edgeLabels W
      (x.linkage[i.val]'(rep.linkage.1.symm ▸ i.isLt))) :
    a.val ∈ (x.linkage[i.val]'(rep.linkage.1.symm ▸ i.isLt)).map
      (fun d => x.endpoints[if incoming then gm06DartMate d else d]?.getD 0) ↔
        rep.graph.vertexLabels a ∈ if incoming then W.support.tail else W.support.dropLast := by
  let lab : ℕ → ClosedCylinder := fun v => if h : v < x.vertexCount then
    rep.graph.vertexLabels ⟨v, h⟩ else cylinderPoint 1 (by norm_num) 0
  have hlab (a : Fin x.vertexCount) : lab a.val = rep.graph.vertexLabels a := by
    simp only [lab, a.isLt, dite_true]
  rw [rep.input_endpoint_words]
  exact walk_encoding_origin_keys_mem_iff henc rep.graph.vertexLabels.injective lab hlab incoming a

/-- No path arrives at an initial vertex: its own simple path
starts there, and the other linkage paths are disjoint. -/
theorem source_incoming_zero (i : Fin k) :
    (gm06BuildCutTables x.vertexCount rep.graph.pairs.length x.endpoints
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
  have hvW := (rep.path_key_mem_iff j' true (rep.source i) W henc).mp hv
  change rep.graph.vertexLabels (rep.source i) ∈ W.support.tail at hvW
  rw [show rep.graph.vertexLabels (rep.source i) = cylinderM1Point k i from rep.source_point i] at hvW
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

/-- The first word marks each initial vertex as leaving its path. -/
theorem source_outgoing_pos (i : Fin k) :
    (gm06BuildCutTables x.vertexCount rep.graph.pairs.length x.endpoints
      x.linkage x.innerCuff x.outerCuff).outgoing[(rep.source i).val]?.getD 0 ≠ 0 := by
  obtain ⟨d, rest, hd, hrow, _, _, hsource⟩ := rep.linkage.first_word_data i
    rep.graph.vertexLabels.injective (rep.source i) (rep.source_point i)
  have hi : i.val < x.linkage.length := by rw [rep.linkage.1]; exact i.isLt
  have hmem : d ∈ x.linkage.flatten := List.mem_flatten.mpr
    ⟨_, List.getElem_mem hi, by rw [hrow]; exact List.mem_cons_self⟩
  have hsource' : x.endpoints[d]?.getD 0 = (rep.source i).val := by
    rw [rep.input_endpoint_words]
    exact hsource
  have hlookup := gm06BuildCutTables_outgoing_at (m := rep.graph.pairs.length)
    x.endpoints x.linkage x.innerCuff x.outerCuff hmem
    (by rw [hsource']; exact (rep.source i).isLt) (rep.cut_path_keys_nodup false)
  rw [hsource'] at hlookup
  rw [hlookup]
  exact Nat.ne_of_gt (Nat.succ_pos d)

/-- No path leaves a terminal vertex of the linkage. -/
theorem terminal_outgoing_zero (i : Fin k) (a : Fin x.vertexCount)
    (ha : rep.graph.vertexLabels a = L.curve i 1) :
    (gm06BuildCutTables x.vertexCount rep.graph.pairs.length x.endpoints
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
  have hvW := (rep.path_key_mem_iff j' false a W henc).mp hv
  change rep.graph.vertexLabels a ∈ W.support.dropLast at hvW
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
    (ha : rep.graph.vertexLabels a = L.curve i 1) :
    (gm06BuildCutTables x.vertexCount rep.graph.pairs.length x.endpoints
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
  exact (rep.path_key_mem_iff i true a W henc).mpr (ha.symm ▸ ht)

/-- A marked vertex with no incoming end is one of the supplied
initial cuff labels. -/
theorem source_of_marks (v : Fin x.vertexCount)
    (hin : (gm06BuildCutTables x.vertexCount rep.graph.pairs.length x.endpoints
      x.linkage x.innerCuff x.outerCuff).incoming[v.val]?.getD 0 = 0)
    (hout : (gm06BuildCutTables x.vertexCount rep.graph.pairs.length x.endpoints
      x.linkage x.innerCuff x.outerCuff).outgoing[v.val]?.getD 0 ≠ 0) :
    ∃ i : Fin k, rep.source i = v := by
  set marks := gm06BuildCutTables x.vertexCount rep.graph.pairs.length x.endpoints
    x.linkage x.innerCuff x.outerCuff
  obtain ⟨b, hb⟩ : ∃ b, marks.outgoing[v.val]?.getD 0 = b + 1 :=
    ⟨marks.outgoing[v.val]?.getD 0 - 1, by change marks.outgoing[v.val]?.getD 0 ≠ 0 at hout; omega⟩
  obtain ⟨hd, horg⟩ := gm06BuildCutTables_outgoing_source x.endpoints x.linkage
    x.innerCuff x.outerCuff v.isLt hb
  obtain ⟨row, hr, hd⟩ := List.mem_flatten.mp hd
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hr
  let i' : Fin k := ⟨i, rep.linkage.1 ▸ hi⟩
  obtain ⟨W, _, henc, _⟩ := rep.linkage.path i'
  have hvkey : v.val ∈ (x.linkage[i]).map (fun d => x.endpoints[d]?.getD 0) :=
    List.mem_map.mpr ⟨b, hd, horg⟩
  have hvW : rep.graph.vertexLabels v ∈ W.support :=
    (List.dropLast_sublist _).subset ((rep.path_key_mem_iff i' false v W henc).mp hvkey)
  have hstart : rep.graph.vertexLabels v = cylinderM1Point k i' := by
    rw [W.support_eq_cons] at hvW
    rcases List.mem_cons.mp hvW with h | h
    · exact h
    · have hvkey' := (rep.path_key_mem_iff i' true v W henc).mpr h
      have hnot := (path_mark_zero_iff x.endpoints x.linkage true v
        (rep.cut_path_keys_nodup true)).mp hin
      rw [gm06CutPathEndPairs_keys, List.map_flatten] at hnot
      exact False.elim (hnot (List.mem_flatten.mpr ⟨_,
        List.mem_map.mpr ⟨_, List.getElem_mem hi, rfl⟩, hvkey'⟩))
  refine ⟨i', rep.graph.vertexLabels.injective ?_⟩
  exact (rep.source_point i').trans hstart.symm

/-- A marked vertex with no outgoing end is one of the supplied
terminal cuff labels. -/
theorem target_of_marks (v : Fin x.vertexCount)
    (hin : (gm06BuildCutTables x.vertexCount rep.graph.pairs.length x.endpoints
      x.linkage x.innerCuff x.outerCuff).incoming[v.val]?.getD 0 ≠ 0)
    (hout : (gm06BuildCutTables x.vertexCount rep.graph.pairs.length x.endpoints
      x.linkage x.innerCuff x.outerCuff).outgoing[v.val]?.getD 0 = 0) :
    ∃ i : Fin k, rep.target i = v := by
  set marks := gm06BuildCutTables x.vertexCount rep.graph.pairs.length x.endpoints
    x.linkage x.innerCuff x.outerCuff
  obtain ⟨a, ha⟩ : ∃ a, marks.incoming[v.val]?.getD 0 = a + 1 :=
    ⟨marks.incoming[v.val]?.getD 0 - 1, by change marks.incoming[v.val]?.getD 0 ≠ 0 at hin; omega⟩
  obtain ⟨hd, horg⟩ := gm06BuildCutTables_incoming_source x.endpoints x.linkage
    x.innerCuff x.outerCuff v.isLt ha
  obtain ⟨row, hr, hd⟩ := List.mem_flatten.mp hd
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hr
  let i' : Fin k := ⟨i, rep.linkage.1 ▸ hi⟩
  obtain ⟨W, _, henc, _⟩ := rep.linkage.path i'
  have hvkey : v.val ∈ (x.linkage[i]).map (fun d => x.endpoints[gm06DartMate d]?.getD 0) :=
    List.mem_map.mpr ⟨gm06DartMate a, hd, by simpa only [gm06DartMate_involutive a] using horg⟩
  have hvW : rep.graph.vertexLabels v ∈ W.support :=
    (List.tail_sublist _).subset ((rep.path_key_mem_iff i' true v W henc).mp hvkey)
  have hend : rep.graph.vertexLabels v = L.curve i' 1 := by
    by_contra hne
    have hvLast : rep.graph.vertexLabels v ≠ W.support.getLast W.support_ne_nil :=
      fun h => hne (h.trans (walk_getLast_support W))
    have hvkey' := (rep.path_key_mem_iff i' false v W henc).mpr
      (List.mem_dropLast_of_mem_of_ne_getLast hvW hvLast)
    have hnot := (path_mark_zero_iff x.endpoints x.linkage false v
      (rep.cut_path_keys_nodup false)).mp hout
    rw [gm06CutPathEndPairs_keys, List.map_flatten] at hnot
    exact hnot (List.mem_flatten.mpr ⟨_,
      List.mem_map.mpr ⟨_, List.getElem_mem hi, rfl⟩, hvkey'⟩)
  obtain ⟨j, hj⟩ := L.curve_one_mem i'
  refine ⟨j, rep.graph.vertexLabels.injective ?_⟩
  exact (rep.target_point j).trans (hj.trans hend.symm)

end GM06SuccessorInputRep
end GraphMinor.GM06
