module

public import GraphMinor.GM06.Alg57CurrentDrawingRep
public import GraphMinor.Compute.GM06DartMate
import GraphMinor.GM06.Alg57RowBounds
import GraphMinor.GM06.Alg511CuffEnumeration

/-!
# Global row facts for the current drawing

The permanent rotation rows in VI (5.7), page 133, are disjoint
because a directed end has one vertex. Reversing a listed end gives
an end at another live vertex and hence another listed word. The
augmented labels remain in the original edge-slot range: every
augmented edge is an ordinary edge or one of the two cuff families.
These facts hold even when deleted labels leave gaps.
-/

public section
namespace GraphMinor.GM06
open Set Topology GraphMinor.Surface GraphMinor.GM11 GraphMinor.Compute unitInterval

namespace GM06CurrentDrawingRep
variable {k : ℕ} {x : GM06SuccessorInput} {G : Drawing ClosedCylinder}
  {L : CylinderLinkage k G} (rep : GM06CurrentDrawingRep x G L)
include rep

/-- A nonempty current row is at a live vertex slot. -/
theorem live_of_mem_row {a : Fin x.vertexCount} {d : ℕ}
    (hd : d ∈ x.rotations.getD a.val []) : a ∈ rep.live := by
  by_contra ha
  rw [rep.retired_rows a ha] at hd
  exact List.not_mem_nil hd

/-- Every row word names an actual directed end at its live vertex. -/
theorem mem_row_iff (a : Fin x.vertexCount) (d : ℕ) :
    d ∈ x.rotations.getD a.val [] ↔ a ∈ rep.live ∧
      ∃ h : halfEdges (cylinderSphereDrawing rep.cuffed) rep.par
        (cylinderToSphere (rep.vertex a)), gm06PersistentHalfEdgeLabel rep.label h = d := by
  constructor
  · intro hd
    have ha := rep.live_of_mem_row hd
    exact ⟨ha, ((rep.rows a ha).2.1 d).mp hd⟩
  · rintro ⟨ha, h⟩
    exact ((rep.rows a ha).2.1 d).mpr h

/-- Different current vertex slots have disjoint rows, including
empty rows at retired slots. Thus no directed end is listed twice. -/
theorem rows_flatten_nodup : x.rotations.flatten.Nodup := by
  apply List.nodup_flatten.mpr
  constructor
  · intro row hr
    obtain ⟨v, hv, heq⟩ := List.mem_iff_getElem.mp hr
    let a : Fin x.vertexCount := ⟨v, rep.rows_length ▸ hv⟩
    have hget : x.rotations.getD a.val [] = row := by
      rw [List.getD_eq_getElem _ _ hv, heq]
    by_cases ha : a ∈ rep.live
    · simpa only [hget] using (rep.rows a ha).1
    · rw [← hget, rep.retired_rows a ha]
      exact List.nodup_nil
  · rw [List.pairwise_iff_getElem]
    intro i j hi hj hij d hdi hdj
    let a : Fin x.vertexCount := ⟨i, rep.rows_length ▸ hi⟩
    let b : Fin x.vertexCount := ⟨j, rep.rows_length ▸ hj⟩
    have hda : d ∈ x.rotations.getD a.val [] := by
      simpa only [a, List.getD_eq_getElem _ _ hi] using hdi
    have hdb : d ∈ x.rotations.getD b.val [] := by
      simpa only [b, List.getD_eq_getElem _ _ hj] using hdj
    obtain ⟨ha, da, hda⟩ := (rep.mem_row_iff a d).mp hda
    obtain ⟨hb, db, hdb⟩ := (rep.mem_row_iff b d).mp hdb
    have hdab := gm06PersistentHalfEdgeLabel_data_eq rep.label da db (hda.trans hdb.symm)
    have hpoint : cylinderToSphere (rep.vertex a) = cylinderToSphere (rep.vertex b) :=
      da.property.2.symm.trans
        ((congrArg (fun q : Set (OnePoint EuclideanPlane) × Bool => rep.par q.1 (endOf q.2))
          hdab).trans db.property.2)
    have hab : a = b := rep.vertex_inj ha hb (injective_cylinderToSphere hpoint)
    exact (Nat.ne_of_lt hij) (congrArg Fin.val hab)

/-- Every sphere vertex of the cuffed drawing has a live original label. -/
theorem sphere_vertex_cover {v : OnePoint EuclideanPlane}
    (hv : v ∈ (cylinderSphereDrawing rep.cuffed).V) :
    ∃ a ∈ rep.live, cylinderToSphere (rep.vertex a) = v := by
  rw [cylinderSphereDrawing_V, rep.cuffed_V] at hv
  obtain ⟨w, hw, rfl⟩ := hv
  obtain ⟨a, ha, rfl⟩ := rep.vertex_cover w hw
  exact ⟨a, ha, rfl⟩

/-- Both ends of every current augmented edge occur in the full
row table. This also covers the two different ends of a loop. -/
theorem rows_mate {d : ℕ} (hd : d ∈ x.rotations.flatten) :
    gm06DartMate d ∈ x.rotations.flatten := by
  obtain ⟨row, hr, hd⟩ := List.mem_flatten.mp hd
  obtain ⟨i, hi, heq⟩ := List.mem_iff_getElem.mp hr
  let a : Fin x.vertexCount := ⟨i, rep.rows_length ▸ hi⟩
  have hget : x.rotations.getD a.val [] = row := by
    rw [List.getD_eq_getElem _ _ hi, heq]
  obtain ⟨ha, z, hz⟩ := (rep.mem_row_iff a d).mp (hget.symm ▸ hd)
  let e : (cylinderSphereDrawing rep.cuffed).E := ⟨z.val.1, z.property.1⟩
  let b := !z.val.2
  have hvertex : rep.par e.val (endOf b) ∈ (cylinderSphereDrawing rep.cuffed).V := by
    cases b <;> simp only [endOf] <;> first
    | exact rep.edgePar.zero e.val e.property
    | exact rep.edgePar.one e.val e.property
  obtain ⟨j, hj, hjeq⟩ := rep.sphere_vertex_cover hvertex
  let w : halfEdges (cylinderSphereDrawing rep.cuffed) rep.par
      (cylinderToSphere (rep.vertex j)) := ⟨(e.val, b), e.property, hjeq.symm⟩
  have hw : gm06PersistentHalfEdgeLabel rep.label w = gm06DartMate d := by
    rw [← hz]
    change 2 * rep.label e + b.toNat =
      gm06DartMate (2 * rep.label e + z.val.2.toNat)
    cases hb : z.val.2 <;> simp [b, hb, gm06DartMate, Nat.add_mod]
  have hm := (rep.mem_row_iff j _).mpr ⟨hj, w, hw⟩
  have hjlen : j.val < x.rotations.length := rep.rows_length.symm ▸ j.isLt
  rw [List.getD_eq_getElem _ _ hjlen] at hm
  exact List.mem_flatten.mpr ⟨_, List.getElem_mem hjlen, hm⟩

/-- Every current augmented edge keeps a label in the original
ordinary-plus-two-cuffs range, even after edge deletion. -/
theorem label_lt (hG : IsCylinderSection5Drawing k G)
    (f : (cylinderSphereDrawing rep.cuffed).E) : rep.label f < rep.tagged.length + (k + k) := by
  obtain ⟨e, heG, heI, heO⟩ := alg511_exists_cuff_edge_equiv hG rep.subdrawing
    rep.cuffed_U rep.cuffed_V
  have hf : f.val ∈ (image cylinderToSphere) '' rep.cuffed.E := by
    simpa only [cylinderSphereDrawing_E] using f.property
  obtain ⟨g, hg, hgf⟩ := hf
  obtain ⟨a, ha⟩ := e.surjective ⟨g, hg⟩
  cases a with
  | inl a =>
    have hga : g = a.val := (congrArg Subtype.val ha).symm.trans (heG a)
    obtain ⟨j, hj, hje⟩ := rep.edge_cover a.val a.property
    obtain ⟨q, hq, hl⟩ := rep.ordinary_labels j hj
    have hqf : q = f := Subtype.ext (hq.trans (by rw [hje, ← hga]; exact hgf))
    rw [← hqf, hl]
    omega
  | inr a =>
    cases a with
    | inl i =>
      have hgi : g = initialCuffGapCurve k i '' Ioo 0 1 :=
        (congrArg Subtype.val ha).symm.trans (heI i)
      obtain ⟨q, hq, hl⟩ := rep.inner_labels i
      have hqf : q = f := Subtype.ext (hq.trans (by rw [← hgi]; exact hgf))
      rw [← hqf, hl]
      omega
    | inr i =>
      have hgi : g = alg511OuterCuffGapCurve k i '' Ioo 0 1 :=
        (congrArg Subtype.val ha).symm.trans (heO i)
      obtain ⟨q, hq, hl⟩ := rep.outer_labels i
      have hqf : q = f := Subtype.ext (hq.trans (by rw [← hgi]; exact hgf))
      rw [← hqf, hl]
      omega

/-- A listed directed word lies in the permanent augmented dart space. -/
theorem row_word_lt (hG : IsCylinderSection5Drawing k G) {a : Fin x.vertexCount} {d : ℕ}
    (hd : d ∈ x.rotations.getD a.val []) : d < 2 * (rep.tagged.length + (k + k)) := by
  obtain ⟨_, z, hz⟩ := (rep.mem_row_iff a d).mp hd
  have he := rep.label_lt hG ⟨z.val.1, z.property.1⟩
  have hb : z.val.2.toNat ≤ 1 := by cases z.val.2 <;> decide
  change 2 * rep.label ⟨z.val.1, z.property.1⟩ + z.val.2.toNat = d at hz
  omega

end GM06CurrentDrawingRep
end GraphMinor.GM06
