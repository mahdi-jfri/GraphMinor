module

public import GraphMinor.GM06.Alg57CurrentDrawingRep
public import GraphMinor.GM06.Alg57CutPathKeys

/-!
# Path-end keys in the current permanent arrays

The cut for VI (5.7), page 133, reads the current linkage rows and
ordinary endpoint words. Every such endpoint is live. The encoded
simple walks give distinct incoming and outgoing keys, even though
the finite vertex and edge spaces retain retired slots. Reverse
membership uses injectivity only on the live labels.
-/

public section
namespace GraphMinor.GM06
open Set GraphMinor.Surface GraphMinor.GM11 GraphMinor.Compute

/-- Every key used by a linkage row is an actual vertex on that
path. This also supplies the finite endpoint bounds. -/
theorem GM06CurrentDrawingRep.path_origin_mem
    {k : ℕ} {x : GM06SuccessorInput} {G : Drawing ClosedCylinder}
    {L : CylinderLinkage k G} (rep : GM06CurrentDrawingRep x G L)
    (i : Fin k) (incoming : Bool) {d : ℕ}
    (hd : d ∈ x.linkage[i.val]'(rep.linkage.1.symm ▸ i.isLt)) :
    ∃ a : Fin x.vertexCount,
      x.endpoints[if incoming then gm06DartMate d else d]?.getD 0 = a.val ∧ a ∈ rep.live ∧
        rep.vertex a ∈ (L.pathDrawing i).V := by
  obtain ⟨W, _, henc, hP⟩ := rep.linkage.path i
  obtain ⟨hbound, _⟩ := henc.active_words d hd
  let a := if incoming then gm06DartHead rep.tagged ⟨d, hbound⟩
    else gm06DartTail rep.tagged ⟨d, hbound⟩
  have hwords := rep.endpoints
  have hread : x.endpoints[if incoming then gm06DartMate d else d]?.getD 0 = a.val := by
    rw [hwords]
    cases incoming
    · exact (gm06Dart_endpoint_words rep.tagged ⟨d, hbound⟩).1
    · exact (gm06Dart_endpoint_words rep.tagged ⟨d, hbound⟩).2
  let lab : ℕ → ClosedCylinder := fun v => if h : v < x.vertexCount then
    rep.vertex ⟨v, h⟩ else cylinderPoint 1 (by norm_num) 0
  have hlab (a : Fin x.vertexCount) : lab a.val = rep.vertex a := by
    simp only [lab, a.isLt, dite_true]
  have hmap := walk_encoding_map_origins henc lab hlab incoming
  have hmem : lab a.val ∈ if incoming then W.support.tail else W.support.dropLast := by
    rw [← hmap]
    apply List.mem_map.mpr
    refine ⟨d, hd, ?_⟩
    exact congrArg lab (by rw [← hwords]; exact hread)
  have hsupp : rep.vertex a ∈ W.support := by
    rw [hlab] at hmem
    cases incoming
    · exact (List.dropLast_sublist _).subset hmem
    · exact (List.tail_sublist _).subset hmem
  have haLive : a ∈ rep.live := by
    obtain ⟨_, hactive⟩ := henc.active_words d hd
    have hl := rep.ends_live ⟨d / 2, by omega⟩ hactive
    cases incoming <;> simp only [a, gm06DartHead, gm06DartTail]
    all_goals split_ifs <;> first | exact hl.1 | exact hl.2
  refine ⟨a, hread, haLive, ?_⟩
  rw [← hP, walkDrawing_V]
  exact hsupp

/-- Both computed path-end scatter tables have distinct vertex
keys, as follows from the simple disjoint input linkage. -/
theorem GM06CurrentDrawingRep.cut_path_keys_nodup
    {k : ℕ} {x : GM06SuccessorInput} {G : Drawing ClosedCylinder}
    {L : CylinderLinkage k G} (rep : GM06CurrentDrawingRep x G L) (incoming : Bool) :
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
      rep.vertex ⟨v, h⟩ else cylinderPoint 1 (by norm_num) 0
    have hlab (a : Fin x.vertexCount) : lab a.val = rep.vertex a := by
      simp only [lab, a.isLt, dite_true]
    have hn := walk_encoding_origin_keys_nodup henc hW lab hlab incoming
    have hwords := rep.endpoints
    simpa only [← hwords] using hn
  · rw [List.pairwise_iff_getElem]
    intro i j hi hj hij v hvi hvj
    have hi' : i < x.linkage.length := by simpa only [List.length_map] using hi
    have hj' : j < x.linkage.length := by simpa only [List.length_map] using hj
    simp only [List.getElem_map] at hvi hvj
    obtain ⟨di, hdi, hdiEq⟩ := List.mem_map.mp hvi
    obtain ⟨dj, hdj, hdjEq⟩ := List.mem_map.mp hvj
    obtain ⟨a, ha, _, haP⟩ := rep.path_origin_mem ⟨i, rep.linkage.1 ▸ hi'⟩ incoming hdi
    obtain ⟨b, hb, _, hbP⟩ := rep.path_origin_mem ⟨j, rep.linkage.1 ▸ hj'⟩ incoming hdj
    have hab : a = b := Fin.ext (ha.symm.trans (hdiEq.trans (hdjEq.symm.trans hb)))
    exact disjoint_left.mp (L.pairwise_disjoint (fun h =>
      (Nat.ne_of_lt hij) (congrArg Fin.val h)))
      ((L.pathDrawing _).V_subset_U haP)
      (by simpa only [← hab] using (L.pathDrawing _).V_subset_U hbP)

namespace GM06CurrentDrawingRep
variable {k : ℕ} {x : GM06SuccessorInput} {G : Drawing ClosedCylinder}
  {L : CylinderLinkage k G} (rep : GM06CurrentDrawingRep x G L)
include rep

/-- The exact path-key membership test uses only live labels. -/
theorem path_key_mem_iff (i : Fin k) (incoming : Bool) (a : Fin x.vertexCount)
    (ha : a ∈ rep.live)
    (W : GraphWalk G.toGraph (cylinderM1Point k i) (L.curve i 1))
    (henc : GM06WalkDartEncoding G.toGraph rep.tagged rep.vertex rep.edge W
      (x.linkage[i.val]'(rep.linkage.1.symm ▸ i.isLt))) :
    a.val ∈ (x.linkage[i.val]'(rep.linkage.1.symm ▸ i.isLt)).map
      (fun d => x.endpoints[if incoming then gm06DartMate d else d]?.getD 0) ↔
        rep.vertex a ∈ if incoming then W.support.tail else W.support.dropLast := by
  let lab : ℕ → ClosedCylinder := fun v => if h : v < x.vertexCount then
    rep.vertex ⟨v, h⟩ else cylinderPoint 1 (by norm_num) 0
  have hlab (b : Fin x.vertexCount) : lab b.val = rep.vertex b := by
    simp only [lab, b.isLt, dite_true]
  have hm := walk_encoding_map_origins henc lab hlab incoming
  rw [← rep.endpoints] at hm
  constructor
  · intro hv
    rw [← hm, ← hlab a]
    obtain ⟨d, hd, hda⟩ := List.mem_map.mp hv
    exact List.mem_map.mpr ⟨d, hd, congrArg lab hda⟩
  · intro hv
    rw [← hm, ← hlab a] at hv
    obtain ⟨d, hd, hda⟩ := List.mem_map.mp hv
    obtain ⟨b, hb, hbLive, _⟩ := rep.path_origin_mem i incoming hd
    rw [hb, hlab b, hlab a] at hda
    have hba : b = a := rep.vertex_inj hbLive ha hda
    exact List.mem_map.mpr ⟨d, hd, hb.trans (congrArg Fin.val hba)⟩

/-- Every current linkage word is in its permanent ordinary dart space. -/
theorem path_word_lt {d : ℕ} (hd : d ∈ x.linkage.flatten) : d < 2 * rep.tagged.length := by
  obtain ⟨row, hr, hd⟩ := List.mem_flatten.mp hd
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hr
  obtain ⟨_, _, henc, _⟩ := rep.linkage.path ⟨i, rep.linkage.1 ▸ hi⟩
  exact (henc.active_words d hd).1

/-- Every origin read along a current path is a valid vertex slot. -/
theorem cut_path_origin_lt (incoming : Bool) {d : ℕ} (hd : d ∈ x.linkage.flatten) :
    x.endpoints[if incoming then gm06DartMate d else d]?.getD 0 < x.vertexCount := by
  obtain ⟨row, hr, hd⟩ := List.mem_flatten.mp hd
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hr
  obtain ⟨a, ha, _, _⟩ := rep.path_origin_mem ⟨i, rep.linkage.1 ▸ hi⟩ incoming hd
  rw [ha]
  exact a.isLt

end GM06CurrentDrawingRep
end GraphMinor.GM06
