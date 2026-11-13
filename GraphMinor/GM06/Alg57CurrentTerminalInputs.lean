module

public import GraphMinor.GM06.Alg57CurrentFind4Rep
public import GraphMinor.GM06.Alg57TerminalFaceRows
import GraphMinor.Compute.GM06FaceRowsProgram

/-!
# Actual component rows and endpoint tables for terminal tracing

Section 15 of the proof of VI (5.7), page 133, reads heads from the
copied origin table and marks the two boundary paths as targets.
The component query preserves the full cut's cyclic face order.
Its rotated row therefore traces an actual numeric dart walk.
All these tables are pure functions of the current finite arrays.
-/

public section
namespace GraphMinor.GM06
open Set GraphMinor.Surface GraphMinor.GM11 GraphMinor.Compute

/-- Copied head words, obtained by reading the reverse end's origin. -/
@[expose] def gm06TerminalHeadWords (m : ℕ) (origins : List ℕ) : List ℕ :=
  List.ofFn (fun d : Fin (2 * m) => origins[gm06DartMate d.val]?.getD 0)

/-- Terminal target bits: the lower path without its source,
together with all vertices of the upper path. -/
@[expose] def gm06TerminalTargetBits (n source : ℕ) (lower upper : List ℕ) : List ℕ :=
  gm06IncidenceBits n ((lower.filter (fun v => v != source)) ++ upper)

/-- Within the copied dart space, a head word is exactly a reverse
origin lookup. -/
theorem terminalHeadWords_get {m d : ℕ} (origins : List ℕ) (hd : d < 2 * m) :
    (gm06TerminalHeadWords m origins)[d]?.getD 0 = origins[gm06DartMate d]?.getD 0 := by
  simp only [gm06TerminalHeadWords, List.getElem?_ofFn, hd, dite_true, Option.getD_some]

/-- The target bit reads precisely its two supplied boundary lists. -/
theorem terminalTargetBits_ne_zero_iff (n source : ℕ) (lower upper : List ℕ) (u : Fin n) :
    (gm06TerminalTargetBits n source lower upper)[u.val]?.getD 0 ≠ 0 ↔
      (u.val ∈ lower ∧ u.val ≠ source) ∨ u.val ∈ upper := by
  simp only [gm06TerminalTargetBits, gm06IncidenceBits, List.getElem?_ofFn, u.isLt,
    dite_true, Option.getD_some, List.mem_append, List.mem_filter, bne_iff_ne]
  split_ifs with h
  · simpa only [ne_eq, one_ne_zero, not_false_eq_true, true_iff] using h
  · simp only [ne_eq, not_true_eq_false, false_iff]; exact h

namespace GM06CurrentDrawingRep
variable {k : ℕ} {x : GM06SuccessorInput} {G : Drawing ClosedCylinder}
  {L : CylinderLinkage k G} (rep : GM06CurrentDrawingRep x G L)
include rep

local notation "currentCut" => gm06CutDataOfLinkage x.vertexCount rep.tagged.length x.endpoints
  x.linkage x.innerCuff x.outerCuff x.rotations (List.range x.vertexCount)
local notation "cutNext" => Equiv.trans dartMatePerm
  (Equiv.symm (gm06RotationPermutation (GM06CutData.rotations currentCut)))
local notation "gap" i:arg => gm06CutDart (2 * (rep.tagged.length + Fin.val (i : Fin k)) + 1) 0
local notation "edgeCount" => 2 * (rep.tagged.length + (k + k))

/-- The natural-number version of the copied vertex interpretation,
with an arbitrary value outside its permanent vertex-slot range. -/
@[expose] noncomputable def cutPoint (v : ℕ) : ClosedCylinder :=
  if h : v < 2 * x.vertexCount then rep.cutVertexPoint ⟨v, h⟩
  else cylinderPoint 1 (by norm_num) 0

/-- Bounded natural labels have their actual copied vertex meaning. -/
theorem cutPoint_fin (v : Fin (2 * x.vertexCount)) : rep.cutPoint v.val = rep.cutVertexPoint v := by
  simp only [cutPoint, v.isLt, dite_true, Fin.eta]

/-- The actual component query preserves the full cut's cyclic
face order, in addition to its already proved orbit membership. -/
theorem component_cut_face_order (hG : IsCylinderSection5Drawing k G) (i : Fin k) :
    ∃ root : Fin (2 * x.vertexCount),
      root.val = gm06CutInnerRoot currentCut rep.tagged.length i.val ∧
      ∃ row : List ℕ, gm06CutFaceIncidence (2 * x.vertexCount) edgeCount
        (gm06CutComponentData currentCut root) (4 * (rep.tagged.length + i.val) + 1) =
          some (row, gm06IncV (2 * x.vertexCount) (currentCut).origins row, gm06IncE edgeCount row) ∧
      (∀ q, q ∈ row ↔ ∃ n, cutNext^[n] (gap i) = q) ∧
      row.Nodup ∧ (gap i) ∈ row ∧ ∀ q ∈ row, row.formPerm q = cutNext q := by
  obtain ⟨root, hroot, row, hout, horbit⟩ := rep.component_cut_face_row hG i
  obtain ⟨root', hroot', ht⟩ := rep.reverse_inner_in_component hG i
  have hroots : root' = root := Fin.ext (hroot'.trans hroot.symm)
  subst root'
  obtain ⟨hn, _, ha, hc, hm⟩ := rep.cut_data_face_encoding hG (List.range x.vertexCount)
  have hv := rep.cut_origins_valid
  have hcode : (gap i) = 4 * (rep.tagged.length + i.val) + 1 := by
    simp [gm06CutDart, Nat.add_div, Nat.add_mod]
  have horbit' : ∀ q, q ∈ row ↔ ∃ n, cutNext^[n] (gap i) = q := by
    simpa only [hcode] using horbit
  let part := gm06CutComponentData currentCut root
  obtain ⟨hpn, hpc, hpa, hpk, hpm⟩ := gm06CutComponentData_face_encoding currentCut root hn hc ha
  have htarget : (gap i) ∈ part.activeDarts := by simpa only [hcode] using ht
  have hquery : gm06CutFaceIncidence (2 * x.vertexCount) edgeCount part (gap i) =
      some (row, gm06IncV (2 * x.vertexCount) part.origins row, gm06IncE edgeCount row) := by
    have hpo : part.origins = (currentCut).origins := by rfl
    rw [hpo, hcode]
    exact hout
  obtain ⟨hrownd, hrowgap, hroworder⟩ := cutFaceIncidence_row_order part hpn hpk hpa hpc hpm htarget hquery
  obtain ⟨row', hout', hporbit⟩ := cutFaceIncidence_orbit part hpn hpk hpa hpc hpm htarget
  have hrows : row' = row := congrArg Prod.fst (Option.some.inj (hout'.symm.trans hquery))
  rw [hrows] at hporbit
  have hrowactive (q : ℕ) (hq : q ∈ row) : q ∈ part.activeDarts := by
    obtain ⟨n, rfl⟩ := (hporbit q).mp hq
    exact numeric_face_iterate_active part hpn hpc hpm htarget n
  refine ⟨root, hroot, row, hout, horbit', hrownd, hrowgap, fun q hq => ?_⟩
  exact (hroworder q hq).trans (cutComponentData_face_eq currentCut root hn hc hm
    (fun d hd => (hv d hd).1) (fun d hd => (hv d hd).2)
    (rep.cut_row_origins_eq hG _) (hrowactive q hq))

/-- The rotated actual face row is a numeric walk from the selected
cuff end's head to its tail, with heads read from the computed table. -/
theorem current_terminal_face_walk (hG : IsCylinderSection5Drawing k G)
    (i : Fin k) (row : List ℕ)
    (horbit : ∀ q, q ∈ row ↔ ∃ n, cutNext^[n] (gap i) = q)
    (hnd : row.Nodup) (hgap : (gap i) ∈ row)
    (horder : ∀ q ∈ row, row.formPerm q = cutNext q) :
    GM06DartWalk (fun q => (currentCut).origins[q]?.getD 0)
      (fun q => (gm06TerminalHeadWords edgeCount (currentCut).origins)[q]?.getD 0)
      ((gm06TerminalHeadWords edgeCount (currentCut).origins)[gap i]?.getD 0)
      (gm06TerminalFaceDarts (gap i) row) ((currentCut).origins[gap i]?.getD 0) := by
  obtain ⟨hn, hk, _, hc, hm⟩ := rep.cut_data_face_encoding hG (List.range x.vertexCount)
  have hactive := rep.cut_face_row_active hG (List.range x.vertexCount) i horbit
  apply terminalFaceDarts_walk _ _ hnd hgap
  intro q hq
  rw [terminalHeadWords_get _ (hk q ((hc q).mp (hactive q hq))), horder q hq]
  exact (numeric_face_head_origin currentCut hn (rep.cut_row_origins_eq hG _)
    ((hc _).mp (hm _ (hactive q hq)))).symm

end GM06CurrentDrawingRep
end GraphMinor.GM06
