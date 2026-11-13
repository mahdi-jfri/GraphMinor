module

public import GraphMinor.GM06.Alg57CurrentCuffAdjacency
public import GraphMinor.GM06.Alg57CurrentRows
public import GraphMinor.Compute.GM06CutPairedEnds
import GraphMinor.GM06.Alg511CuffEnumeration

/-!
# Projection of the face orbit in the actual current cut

For VI (5.7), page 133, current ordinary row words have the origins
specified by the endpoint array. The actual row interpretation proves
this even with gaps in the permanent edge labels. The computed cut
therefore has paired copied ends. Combining this with its proved
local blocks, fit condition and distinguished cuff dart gives the
face-orbit projection with no additional representation premise.
-/

public section
namespace GraphMinor.GM06
open Set GraphMinor.Surface GraphMinor.GM11 GraphMinor.Compute unitInterval

private theorem row_index_eq_of_mem {rows : List (List ℕ)} (hn : rows.flatten.Nodup)
    {i j : ℕ} {a b : List ℕ} (hi : rows[i]? = some a) (hj : rows[j]? = some b)
    {d : ℕ} (hda : d ∈ a) (hdb : d ∈ b) : i = j := by
  obtain ⟨hi', hai⟩ := List.getElem?_eq_some_iff.mp hi
  obtain ⟨hj', hbj⟩ := List.getElem?_eq_some_iff.mp hj
  have hp := List.pairwise_iff_getElem.mp (List.nodup_flatten.mp hn).2
  have hni : ¬ i < j := by
    intro hij
    exact hp i j hi' hj' hij (hai.symm ▸ hda) (hbj.symm ▸ hdb)
  have hnj : ¬ j < i := by
    intro hji
    exact hp j i hj' hi' hji (hbj.symm ▸ hdb) (hai.symm ▸ hda)
  omega

namespace GM06CurrentDrawingRep
variable {k : ℕ} {x : GM06SuccessorInput} {G : Drawing ClosedCylinder}
  {L : CylinderLinkage k G} (rep : GM06CurrentDrawingRep x G L)
include rep

/-- A current augmented edge with an ordinary permanent label is
exactly the active ordinary edge at that slot. -/
theorem ordinary_of_label_lt (hG : IsCylinderSection5Drawing k G)
    (f : (cylinderSphereDrawing rep.cuffed).E) (hf : rep.label f < rep.tagged.length) :
    ∃ j : Fin rep.tagged.length, rep.tagged[j].2 = 1 ∧
      f.val = cylinderToSphere '' rep.edge j ∧ rep.label f = j.val := by
  obtain ⟨e, heG, heI, heO⟩ := alg511_exists_cuff_edge_equiv hG rep.subdrawing
    rep.cuffed_U rep.cuffed_V
  have hmem : f.val ∈ (image cylinderToSphere) '' rep.cuffed.E := by
    simpa only [cylinderSphereDrawing_E] using f.property
  obtain ⟨g, hg, hgf⟩ := hmem
  obtain ⟨a, ha⟩ := e.surjective ⟨g, hg⟩
  cases a with
  | inl a =>
    have hga : g = a.val := (congrArg Subtype.val ha).symm.trans (heG a)
    obtain ⟨j, hj, hje⟩ := rep.edge_cover a.val a.property
    obtain ⟨q, hq, hl⟩ := rep.ordinary_labels j hj
    have hqf : q = f := Subtype.ext (hq.trans (by rw [hje, ← hga]; exact hgf))
    exact ⟨j, hj, hqf ▸ hq, hqf ▸ hl⟩
  | inr a =>
    cases a with
    | inl i =>
      have hgi : g = initialCuffGapCurve k i '' Ioo 0 1 :=
        (congrArg Subtype.val ha).symm.trans (heI i)
      obtain ⟨q, hq, hl⟩ := rep.inner_labels i
      have hqf : q = f := Subtype.ext (hq.trans (by rw [← hgi]; exact hgf))
      rw [← hqf, hl] at hf
      omega
    | inr i =>
      have hgi : g = alg511OuterCuffGapCurve k i '' Ioo 0 1 :=
        (congrArg Subtype.val ha).symm.trans (heO i)
      obtain ⟨q, hq, hl⟩ := rep.outer_labels i
      have hqf : q = f := Subtype.ext (hq.trans (by rw [← hgi]; exact hgf))
      rw [← hqf, hl] at hf
      omega

/-- An ordinary word occurring in a current row is active. -/
theorem row_ordinary_active (hG : IsCylinderSection5Drawing k G)
    (v : Fin x.vertexCount) {d : ℕ} (hd : d ∈ x.rotations.getD v.val [])
    (hbound : d < 2 * rep.tagged.length) :
    (rep.tagged[d / 2]'(by omega)).2 = 1 := by
  obtain ⟨_, a, ha⟩ := (rep.mem_row_iff v d).mp hd
  let f : (cylinderSphereDrawing rep.cuffed).E := ⟨a.val.1, a.property.1⟩
  have hcode : 2 * rep.label f + a.val.2.toNat = d := ha
  have hb : a.val.2.toNat ≤ 1 := by cases a.val.2 <;> decide
  have hf : rep.label f < rep.tagged.length := by omega
  obtain ⟨j, hj, _, hlabel⟩ := rep.ordinary_of_label_lt hG f hf
  have hindex : j.val = d / 2 := by omega
  simpa only [Fin.getElem_fin, hindex] using hj

/-- Every stored ordinary endpoint lies in the original vertex-slot range. -/
theorem endpoint_word_lt {a : ℕ} (ha : a ∈ x.endpoints) : a < x.vertexCount := by
  rw [rep.endpoints] at ha
  obtain ⟨p, hp, ha⟩ := List.mem_flatMap.mp ha
  obtain ⟨p, _, rfl⟩ := List.mem_map.mp hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl
  · exact p.1.1.isLt
  · exact p.1.2.isLt

/-- Every ordinary endpoint lookup is a valid vertex label. -/
theorem ordinary_origin_lt {d : ℕ} (hd : d < 2 * rep.tagged.length) :
    x.endpoints[d]?.getD 0 < x.vertexCount := by
  have hlen : x.endpoints.length = 2 * rep.tagged.length := by
    rw [rep.endpoints, gm06EndpointWords_length, List.length_map]
  have hd' : d < x.endpoints.length := hlen.symm ▸ hd
  rw [List.getElem?_eq_getElem hd', Option.getD_some]
  exact rep.endpoint_word_lt (List.getElem_mem hd')

/-- The ordinary endpoint array reads exactly the current row
index at each ordinary word occurring there. -/
theorem ordinary_origin_row (hG : IsCylinderSection5Drawing k G)
    (p : List ℕ × ℕ) (hp : p ∈ x.rotations.zipIdx) (d : ℕ) (hd : d ∈ p.1)
    (hbound : d < 2 * rep.tagged.length) : x.endpoints[d]?.getD 0 = p.2 := by
  have hrow : x.rotations[p.2]? = some p.1 := List.mem_zipIdx_iff_getElem?.mp hp
  have hi : p.2 < x.vertexCount := rep.rows_length ▸ (List.getElem?_eq_some_iff.mp hrow).1
  let v : Fin x.vertexCount := ⟨p.2, hi⟩
  have hget : x.rotations.getD v.val [] = p.1 := by
    rw [List.getD_eq_getElem?_getD, hrow]
    rfl
  have hactive := rep.row_ordinary_active hG v (hget.symm ▸ hd) hbound
  let w : Fin x.vertexCount := ⟨x.endpoints[d]?.getD 0, rep.ordinary_origin_lt hbound⟩
  have hw := rep.ordinary_word_mem_row w d hbound hactive rfl
  have hwlen : w.val < x.rotations.length := rep.rows_length.symm ▸ w.isLt
  rw [List.getD_eq_getElem _ _ hwlen] at hw
  exact row_index_eq_of_mem rep.rows_flatten_nodup (List.getElem?_eq_getElem hwlen) hrow hw hd

/-- The computed copied rows retain exactly the permitted copies
of each current directed word. -/
theorem cut_copies (hG : IsCylinderSection5Drawing k G) (d tag : ℕ) (ht : tag < 2) :
    gm06CutDart d tag ∈ (gm06CutAlongLinkageRotations x.vertexCount rep.tagged.length
      x.endpoints x.linkage x.innerCuff x.outerCuff x.rotations).flatten ↔
      d ∈ x.rotations.flatten ∧ (tag = 0 ∨ d ∈ x.linkage.flatten ∨ gm06DartMate d ∈ x.linkage.flatten) := by
  exact gm06CutAlongLinkage_copies x.endpoints x.linkage x.innerCuff x.outerCuff x.rotations
    rep.rows_length ht (fun _ hd => rep.path_word_lt hd)
    (rep.ordinary_origin_row hG) (rep.cut_path_keys_nodup true) (rep.cut_path_keys_nodup false)

/-- Reversal preserves the actual copied current rotation table. -/
theorem cut_rows_mate (hG : IsCylinderSection5Drawing k G) {q : ℕ}
    (hq : q ∈ (gm06CutAlongLinkageRotations x.vertexCount rep.tagged.length
      x.endpoints x.linkage x.innerCuff x.outerCuff x.rotations).flatten) :
    gm06DartMate q ∈ (gm06CutAlongLinkageRotations x.vertexCount rep.tagged.length
      x.endpoints x.linkage x.innerCuff x.outerCuff x.rotations).flatten := by
  let d := gm06UncutDart q
  let tag := q / 2 % 2
  have ht : tag < 2 := Nat.mod_lt _ (by decide)
  have heq : gm06CutDart d tag = q := gm06CutDart_rebuild q
  have hh := (rep.cut_copies hG d tag ht).mp (heq.symm ▸ hq)
  have hmate : gm06DartMate d ∈ x.rotations.flatten ∧
      (tag = 0 ∨ gm06DartMate d ∈ x.linkage.flatten ∨ gm06DartMate (gm06DartMate d) ∈ x.linkage.flatten) := by
    refine ⟨rep.rows_mate hh.1, ?_⟩
    rcases hh.2 with h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inr (by simpa only [gm06DartMate_involutive d] using h))
    · exact Or.inr (Or.inl h)
  have hm := (rep.cut_copies hG (gm06DartMate d) tag ht).mpr hmate
  simpa only [gm06CutDart_mate, heq] using hm

/-- The selected copied reverse inner cuff dart is in the actual cut. -/
theorem reverse_inner_mem_cut (hG : IsCylinderSection5Drawing k G) (i : Fin k) :
    gm06CutDart (2 * (rep.tagged.length + i.val) + 1) 0 ∈
      (gm06CutAlongLinkageRotations x.vertexCount rep.tagged.length x.endpoints x.linkage
        x.innerCuff x.outerCuff x.rotations).flatten := by
  apply (rep.cut_copies hG _ 0 (by decide)).mpr
  refine ⟨?_, Or.inl rfl⟩
  have hi : (rep.source (finSuccCycle i)).val < x.rotations.length :=
    rep.rows_length.symm ▸ (rep.source _).isLt
  have hm := (rep.inner_markers hG i).2
  rw [List.getD_eq_getElem _ _ hi] at hm
  exact List.mem_flatten.mpr ⟨_, List.getElem_mem hi, hm⟩

/-- The actual current cut face through the reverse inner gap
projects exactly to the old face orbit, with every cut premise derived. -/
theorem cut_face_orbit_projection_iff (hG : IsCylinderSection5Drawing k G) (i : Fin k) (d : ℕ) :
    let marks := gm06BuildCutTables x.vertexCount rep.tagged.length x.endpoints x.linkage
      x.innerCuff x.outerCuff
    let c := gm06CutDart (2 * (rep.tagged.length + i.val) + 1) 0
    (∃ n, (dartMatePerm.trans (gm06RotationPermutation x.rotations).symm)^[n]
      (gm06UncutDart c) = d) ↔
    ∃ n, gm06UncutDart ((dartMatePerm.trans
      (gm06RotationPermutation (gm06SplitRotationRows marks x.rotations)).symm)^[n] c) = d := by
  dsimp only
  exact GraphMinor.GM06.cut_face_orbit_projection_iff _ _ rep.rows_flatten_nodup
    (rep.cut_block_ok hG) (rep.cut_fits hG.1) (fun _ h => rep.cut_rows_mate hG h)
    (rep.reverse_inner_mem_cut hG i) (rep.reverse_inner_cut_mate_not_first hG.1 i) d

end GM06CurrentDrawingRep
end GraphMinor.GM06
