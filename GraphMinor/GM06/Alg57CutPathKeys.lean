module

public import GraphMinor.GM06.Alg57InputRep
public import GraphMinor.Compute.GM06CutMarkFacts
import GraphMinor.GM06.Alg57RowBounds
import GraphMinor.GM06.Section5Red

/-!
# Distinct path-end keys in the linkage cut

Section 9 of the implementation of VI (5.7), page 133, scatters
one leaving and one arriving mark per directed path word. Reading
the origins of those words gives the path's vertices with its last
or first vertex removed. Each such list has no repeated vertex,
and different linkage paths have disjoint vertex sets. Thus neither
scatter overwrites another path end. The proof reads only the given
ordinary endpoint and path fields.
-/

public section
namespace GraphMinor.GM06
open Set GraphMinor.Surface GraphMinor.GM11 GraphMinor.Compute

/-- Reading the origins of directed words in an encoded walk gives
its vertices without the last vertex, or without the first vertex
when the words are reversed before reading their origins. -/
theorem walk_encoding_map_origins {n : ℕ} {α β : Type*} {G : Graph α β}
    {tagged : List ((Fin n × Fin n) × ℕ)} {vertex : Fin n → α}
    {edge : Fin tagged.length → β} {s t : α} {W : GraphWalk G s t} {row : List ℕ}
    (h : GM06WalkDartEncoding G tagged vertex edge W row)
    (lab : ℕ → α) (hlab : ∀ a : Fin n, lab a.val = vertex a) (incoming : Bool) :
    (row.map (fun d =>
      lab ((gm06EndpointWords (tagged.map fun p => (p.1.1.val, p.1.2.val)))[
        if incoming then gm06DartMate d else d]?.getD 0))) =
      if incoming then W.support.tail else W.support.dropLast := by
  induction h generalizing incoming with
  | nil hx => cases incoming <;> rfl
  | @cons x y z e hl R row d hd hactive hedge htail hhead hrest ih =>
    have hwords := gm06Dart_endpoint_words tagged ⟨d, hd⟩
    cases incoming
    · simp only [Bool.false_eq_true, ↓reduceIte, List.map_cons,
        GraphWalk.support_cons, hwords.1, hlab, htail]
      rw [List.dropLast_cons_of_ne_nil R.support_ne_nil]
      exact congrArg (List.cons x) (ih false)
    · simp only [↓reduceIte, List.map_cons, GraphWalk.support_cons, List.tail_cons,
        hwords.2, hlab, hhead]
      exact (congrArg (List.cons y) (ih true)).trans R.support_eq_cons.symm

/-- For an injective vertex labelling, membership among the origin
keys is exactly membership among the corresponding path vertices. -/
theorem walk_encoding_origin_keys_mem_iff {n : ℕ} {α β : Type*} {G : Graph α β}
    {tagged : List ((Fin n × Fin n) × ℕ)} {vertex : Fin n → α}
    {edge : Fin tagged.length → β} {s t : α} {W : GraphWalk G s t} {row : List ℕ}
    (h : GM06WalkDartEncoding G tagged vertex edge W row)
    (hinj : Function.Injective vertex) (lab : ℕ → α)
    (hlab : ∀ a : Fin n, lab a.val = vertex a) (incoming : Bool) (a : Fin n) :
    a.val ∈ row.map (fun d =>
      (gm06EndpointWords (tagged.map fun p => (p.1.1.val, p.1.2.val)))[
        if incoming then gm06DartMate d else d]?.getD 0) ↔
      vertex a ∈ if incoming then W.support.tail else W.support.dropLast := by
  have hm := walk_encoding_map_origins h lab hlab incoming
  constructor
  · intro ha
    rw [← hm, ← hlab a]
    obtain ⟨d, hd, hda⟩ := List.mem_map.mp ha
    exact List.mem_map.mpr ⟨d, hd, congrArg lab hda⟩
  · intro ha
    rw [← hm, ← hlab a] at ha
    obtain ⟨d, hd, hda⟩ := List.mem_map.mp ha
    obtain ⟨hb, _⟩ := h.active_words d hd
    let q := if incoming then gm06DartHead tagged ⟨d, hb⟩
      else gm06DartTail tagged ⟨d, hb⟩
    have hread : (gm06EndpointWords (tagged.map fun p => (p.1.1.val, p.1.2.val)))[
        if incoming then gm06DartMate d else d]?.getD 0 = q.val := by
      cases incoming
      · exact (gm06Dart_endpoint_words tagged ⟨d, hb⟩).1
      · exact (gm06Dart_endpoint_words tagged ⟨d, hb⟩).2
    rw [hread, hlab q, hlab a] at hda
    have hqa := congrArg Fin.val (hinj hda)
    exact List.mem_map.mpr ⟨d, hd, hread.trans hqa⟩

/-- The endpoint keys of either orientation of a simple encoded
walk have no repetitions. No injectivity of the supplied vertex
map is needed for this direction. -/
theorem walk_encoding_origin_keys_nodup {n : ℕ} {α β : Type*} {G : Graph α β}
    {tagged : List ((Fin n × Fin n) × ℕ)} {vertex : Fin n → α}
    {edge : Fin tagged.length → β} {s t : α} {W : GraphWalk G s t} {row : List ℕ}
    (h : GM06WalkDartEncoding G tagged vertex edge W row) (hW : W.IsSimple)
    (lab : ℕ → α) (hlab : ∀ a : Fin n, lab a.val = vertex a) (incoming : Bool) :
    (row.map (fun d =>
      (gm06EndpointWords (tagged.map fun p => (p.1.1.val, p.1.2.val)))[
        if incoming then gm06DartMate d else d]?.getD 0)).Nodup := by
  apply List.Nodup.of_map lab
  rw [List.map_map]
  change (row.map (fun d => lab ((gm06EndpointWords
    (tagged.map fun p => (p.1.1.val, p.1.2.val)))[
      if incoming then gm06DartMate d else d]?.getD 0))).Nodup
  rw [walk_encoding_map_origins h lab hlab incoming]
  cases incoming
  · exact hW.sublist (List.dropLast_sublist _)
  · exact hW.sublist (List.tail_sublist _)

/-- Every key used by a linkage row is an actual vertex on that
path. This also supplies the finite endpoint bounds. -/
theorem GM06SuccessorInputRep.path_origin_mem
    {k : ℕ} {x : GM06SuccessorInput} {G : Drawing ClosedCylinder}
    {L : CylinderLinkage k G} (rep : GM06SuccessorInputRep x G L)
    (i : Fin k) (incoming : Bool) {d : ℕ}
    (hd : d ∈ x.linkage[i.val]'(rep.linkage.1.symm ▸ i.isLt)) :
    ∃ a : Fin x.vertexCount,
      x.endpoints[if incoming then gm06DartMate d else d]?.getD 0 = a.val ∧
        rep.graph.vertexLabels a ∈ (L.pathDrawing i).V := by
  obtain ⟨W, _, henc, hP⟩ := rep.linkage.path i
  obtain ⟨hbound, _⟩ := henc.active_words d hd
  let a := if incoming then gm06DartHead rep.graph.initialTagged ⟨d, hbound⟩
    else gm06DartTail rep.graph.initialTagged ⟨d, hbound⟩
  have hwords : x.endpoints = gm06EndpointWords
      (rep.graph.initialTagged.map fun p => (p.1.1.val, p.1.2.val)) := by
    simpa only [GM06SuccessorGraphRep.initialTagged, List.map_map, Function.comp_def]
      using rep.graph.endpoints
  have hread : x.endpoints[if incoming then gm06DartMate d else d]?.getD 0 = a.val := by
    rw [hwords]
    cases incoming
    · exact (gm06Dart_endpoint_words rep.graph.initialTagged ⟨d, hbound⟩).1
    · exact (gm06Dart_endpoint_words rep.graph.initialTagged ⟨d, hbound⟩).2
  let lab : ℕ → ClosedCylinder := fun v => if h : v < x.vertexCount then
    rep.graph.vertexLabels ⟨v, h⟩ else cylinderPoint 1 (by norm_num) 0
  have hlab (a : Fin x.vertexCount) : lab a.val = rep.graph.vertexLabels a := by
    simp only [lab, a.isLt, dite_true]
  have hmap := walk_encoding_map_origins henc lab hlab incoming
  have hmem : lab a.val ∈ if incoming then W.support.tail else W.support.dropLast := by
    rw [← hmap]
    apply List.mem_map.mpr
    refine ⟨d, hd, ?_⟩
    exact congrArg lab (by rw [← hwords]; exact hread)
  have hsupp : rep.graph.vertexLabels a ∈ W.support := by
    rw [hlab] at hmem
    cases incoming
    · exact (List.dropLast_sublist _).subset hmem
    · exact (List.tail_sublist _).subset hmem
  refine ⟨a, hread, ?_⟩
  rw [← hP, walkDrawing_V]
  exact hsupp

/-- Both computed path-end scatter tables have distinct vertex
keys, as follows from the simple disjoint input linkage. -/
theorem GM06SuccessorInputRep.cut_path_keys_nodup
    {k : ℕ} {x : GM06SuccessorInput} {G : Drawing ClosedCylinder}
    {L : CylinderLinkage k G} (rep : GM06SuccessorInputRep x G L) (incoming : Bool) :
    ((gm06CutPathEndPairs x.endpoints x.linkage.flatten incoming).map Prod.fst).Nodup := by
  rw [gm06CutPathEndPairs_keys, List.map_flatten]
  apply List.nodup_flatten.mpr
  constructor
  · intro row hr
    obtain ⟨old, hold, rfl⟩ := List.mem_map.mp hr
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hold
    let j : Fin k := ⟨i, rep.linkage.1 ▸ hi⟩
    obtain ⟨W, hW, henc, _⟩ := rep.linkage.path j
    let lab : ℕ → ClosedCylinder := fun v => if h : v < x.vertexCount then
      rep.graph.vertexLabels ⟨v, h⟩ else cylinderPoint 1 (by norm_num) 0
    have hlab (a : Fin x.vertexCount) : lab a.val = rep.graph.vertexLabels a := by
      simp only [lab, a.isLt, dite_true]
    have hn := walk_encoding_origin_keys_nodup henc hW lab hlab incoming
    have hwords : x.endpoints = gm06EndpointWords
        (rep.graph.initialTagged.map fun p => (p.1.1.val, p.1.2.val)) := by
      simpa only [GM06SuccessorGraphRep.initialTagged, List.map_map, Function.comp_def]
        using rep.graph.endpoints
    simpa only [← hwords] using hn
  · rw [List.pairwise_iff_getElem]
    intro i j hi hj hij v hvi hvj
    have hi' : i < x.linkage.length := by simpa only [List.length_map] using hi
    have hj' : j < x.linkage.length := by simpa only [List.length_map] using hj
    simp only [List.getElem_map] at hvi hvj
    obtain ⟨di, hdi, hdiEq⟩ := List.mem_map.mp hvi
    obtain ⟨dj, hdj, hdjEq⟩ := List.mem_map.mp hvj
    obtain ⟨a, ha, haP⟩ := rep.path_origin_mem ⟨i, rep.linkage.1 ▸ hi'⟩ incoming hdi
    obtain ⟨b, hb, hbP⟩ := rep.path_origin_mem ⟨j, rep.linkage.1 ▸ hj'⟩ incoming hdj
    have hab : a = b := Fin.ext (ha.symm.trans (hdiEq.trans (hdjEq.symm.trans hb)))
    exact disjoint_left.mp (L.pairwise_disjoint (fun h =>
      (Nat.ne_of_lt hij) (congrArg Fin.val h)))
      ((L.pathDrawing _).V_subset_U haP)
      (by simpa only [← hab] using (L.pathDrawing _).V_subset_U hbP)

end GraphMinor.GM06
