module

public import GraphMinor.GM06.Alg57CurrentTerminalCuffs
import GraphMinor.GM11.Section87
import all GraphMinor.GM06.Alg57TerminalPathLink

/-!
# The actual terminal target marks

Section 15 of the proof of VI (5.7), page 133, marks the left
boundary after its source and the whole right boundary. On the
selected face the computed copied lists mark exactly those
geometric vertices. The source is unmarked, while the final
right source is marked. The rotated face walk consequently has
a first contact with the target set.
-/

public section
namespace GraphMinor.GM06
open Set GraphMinor.Surface GraphMinor.GM11 GraphMinor.Compute

private theorem dartWalk_nil_end {D V : Type*} {tail head : D → V} {s t : V}
    (h : GM06DartWalk tail head s [] t) : s = t := by
  cases h
  rfl

namespace GM06CurrentDrawingRep
variable {k : ℕ} {x : GM06SuccessorInput} {G : Drawing ClosedCylinder}
  {L : CylinderLinkage k G} (rep : GM06CurrentDrawingRep x G L)
  (hn : 0 < x.vertexCount)
include rep

set_option quotPrecheck false in
local notation "lower" i:arg => gm06CutPathLabels x.vertexCount hn x.endpoints
  (x.linkage[Fin.val (i : Fin k)]'(by rw [rep.linkage.1]; exact Fin.isLt (i : Fin k)))
  (Fin.val (rep.source (i : Fin k))) true
set_option quotPrecheck false in
local notation "upper" i:arg => gm06CutPathLabels x.vertexCount hn x.endpoints
  (x.linkage[Fin.val (finSuccCycle (i : Fin k))]'(by rw [rep.linkage.1]; exact Fin.isLt (finSuccCycle (i : Fin k))))
  (Fin.val (rep.source (finSuccCycle (i : Fin k)))) false
local notation "sourceCopy" i:arg => gm06CutVertexFin x.vertexCount hn (Fin.val (rep.source (i : Fin k))) true
local notation "endCopy" i:arg => gm06CutVertexFin x.vertexCount hn
  (Fin.val (rep.source (finSuccCycle (i : Fin k)))) false
local notation "targets" i:arg => gm06TerminalTargetBits (2 * x.vertexCount)
  (gm06CutVertex (Fin.val (rep.source (i : Fin k))) true)
  (List.map Fin.val (lower i)) (List.map Fin.val (upper i))
local notation "currentCut" => gm06CutDataOfLinkage x.vertexCount rep.tagged.length x.endpoints
  x.linkage x.innerCuff x.outerCuff x.rotations (List.range x.vertexCount)
local notation "cutNext" => Equiv.trans dartMatePerm
  (Equiv.symm (gm06RotationPermutation (GM06CutData.rotations currentCut)))
local notation "gap" i:arg => gm06CutDart (2 * (rep.tagged.length + Fin.val (i : Fin k)) + 1) 0
local notation "edgeCount" => 2 * (rep.tagged.length + (k + k))

private theorem source_mem_lower (i : Fin k) : (sourceCopy i) ∈ lower i := by
  simp only [gm06CutPathLabels, find4PathLabels, List.mem_cons, true_or]

/-- The listed source copy projects to its prescribed initial vertex. -/
theorem sourceCopy_point (i : Fin k) : rep.cutVertexPoint (sourceCopy i) = cylinderM1Point k i :=
  (rep.cutVertexFin_point hn (rep.source i) true).trans (rep.source_point i)

/-- On incident labels, the left boundary list is precisely the
vertex set of the selecting linkage path. -/
theorem selected_face_lower_iff (hk : 1 < k) (hG : IsCylinderSection5Drawing k G)
    (i : Fin k) (row : List ℕ)
    (horbit : ∀ q, q ∈ row ↔ ∃ n, cutNext^[n] (gap i) = q)
    (u : Fin (2 * x.vertexCount))
    (hu : (gm06IncV (2 * x.vertexCount) (currentCut).origins row)[u.val]?.getD 0 ≠ 0) :
    u ∈ lower i ↔ rep.cutVertexPoint u ∈ (L.pathDrawing i).V := by
  constructor
  · intro h
    exact ((rep.mem_computed_path_labels_iff hn i true u
      (rep.computed_path_labels_live hn i true h)).mp h).1
  · intro h
    obtain ⟨W, _, hV, hsupport, _⟩ := rep.computed_path_walk hn i true
    rw [hV, hsupport] at h
    obtain ⟨w, hw, heq⟩ := List.mem_map.mp h
    have hwu := rep.selected_face_path_union_inj hn hk hG i row horbit w u (Or.inr hw) (Or.inl hu) heq
    exact hwu ▸ hw

include hn in
/-- On incident copied labels, equality with the numeric source
is exactly equality with its geometric source point. -/
theorem selected_face_source_iff (hk : 1 < k) (hG : IsCylinderSection5Drawing k G)
    (i : Fin k) (row : List ℕ)
    (horbit : ∀ q, q ∈ row ↔ ∃ n, cutNext^[n] (gap i) = q)
    (u : Fin (2 * x.vertexCount))
    (hu : (gm06IncV (2 * x.vertexCount) (currentCut).origins row)[u.val]?.getD 0 ≠ 0) :
    u.val = gm06CutVertex (rep.source i).val true ↔ rep.cutVertexPoint u = cylinderM1Point k i := by
  have hval := cutVertexFin_val hn (rep.source i).isLt true
  constructor
  · intro h
    have he : u = (sourceCopy i) := Fin.ext (h.trans hval.symm)
    exact he.symm ▸ rep.sourceCopy_point hn i
  · intro h
    have he := rep.selected_face_path_union_inj hn hk hG i row horbit u (sourceCopy i)
      (Or.inl hu) (Or.inr (rep.source_mem_lower hn i)) (h.trans (rep.sourceCopy_point hn i).symm)
    exact (congrArg Fin.val he).trans hval

/-- The actual computed target bits agree with the geometric
terminal target set on every incident copied vertex label. -/
theorem selected_face_terminal_target_iff (hk : 1 < k) (hG : IsCylinderSection5Drawing k G)
    (i : Fin k) (row : List ℕ)
    (horbit : ∀ q, q ∈ row ↔ ∃ n, cutNext^[n] (gap i) = q)
    (u : Fin (2 * x.vertexCount))
    (hu : (gm06IncV (2 * x.vertexCount) (currentCut).origins row)[u.val]?.getD 0 ≠ 0) :
    (targets i)[u.val]?.getD 0 ≠ 0 ↔ rep.cutVertexPoint u ∈ terminalTargets L i := by
  have hv := (rep.selected_face_vertex_dart hG i row horbit u hu).1
  have hupper : u ∈ upper i ↔ rep.cutVertexPoint u ∈ (L.pathDrawing (finSuccCycle i)).V := by
    rw [rep.selected_face_upper_iff hn hk hG i row horbit u hu]
    exact ⟨fun h => mem_V_of_mem_U' (L.isSubdrawing _).1 h hv, fun h => (L.pathDrawing _).V_subset_U h⟩
  rw [terminalTargetBits_ne_zero_iff, List.mem_map_of_injective Fin.val_injective,
    List.mem_map_of_injective Fin.val_injective, rep.selected_face_lower_iff hn hk hG i row horbit u hu]
  simp only [ne_eq, rep.selected_face_source_iff hn hk hG i row horbit u hu, hupper]
  rfl

/-- The left source has zero target bit, as the lower source is
removed and every upper label has odd parity. -/
theorem terminal_source_unmarked (i : Fin k) :
    (targets i)[gm06CutVertex (rep.source i).val true]?.getD 0 = 0 := by
  have hval := cutVertexFin_val hn (rep.source i).isLt true
  by_contra hne
  have hne' : (targets i)[(sourceCopy i).val]?.getD 0 ≠ 0 := by simpa only [hval] using hne
  have hh := (terminalTargetBits_ne_zero_iff _ _ _ _ (sourceCopy i)).mp hne'
  rcases hh with h | h
  · exact h.2 hval
  · have hm : (sourceCopy i) ∈ upper i := (List.mem_map_of_injective Fin.val_injective).mp h
    have hp := cutPathLabels_mod x.vertexCount hn _ _ _ false hm
    have hs := cutVertexFin_mod x.vertexCount hn (rep.source i).val true
    simp only [Bool.not_false, Bool.toNat_true] at hp
    simp only [Bool.not_true, Bool.toNat_false] at hs
    omega

/-- The right source at the end of the face walk is marked. -/
theorem terminal_end_marked (i : Fin k) :
    (targets i)[gm06CutVertex (rep.source (finSuccCycle i)).val false]?.getD 0 ≠ 0 := by
  have hval := cutVertexFin_val hn (rep.source (finSuccCycle i)).isLt false
  rw [← hval]
  apply (terminalTargetBits_ne_zero_iff _ _ _ _ (endCopy i)).mpr
  apply Or.inr
  apply List.mem_map.mpr
  refine ⟨endCopy i, ?_, rfl⟩
  simp only [gm06CutPathLabels, find4PathLabels, List.mem_cons, true_or]

/-- The actual rotated face walk starts at the chosen left source
and ends at the following right source. -/
theorem current_terminal_walk (hG : IsCylinderSection5Drawing k G)
    (i : Fin k) (row : List ℕ)
    (horbit : ∀ q, q ∈ row ↔ ∃ n, cutNext^[n] (gap i) = q)
    (hnd : row.Nodup) (hgap : (gap i) ∈ row)
    (horder : ∀ q ∈ row, row.formPerm q = cutNext q) :
    GM06DartWalk (fun q => (currentCut).origins[q]?.getD 0)
      (fun q => (gm06TerminalHeadWords edgeCount (currentCut).origins)[q]?.getD 0)
      (gm06CutVertex (rep.source i).val true) (gm06TerminalFaceDarts (gap i) row)
      (gm06CutVertex (rep.source (finSuccCycle i)).val false) := by
  have hwalk := rep.current_terminal_face_walk hG i row horbit hnd hgap horder
  have hbound : (gap i) < 2 * edgeCount := by
    have hi := i.isLt
    have hcode : (gap i) = 4 * (rep.tagged.length + i.val) + 1 := by
      simp [gm06CutDart, Nat.add_div, Nat.add_mod]
    rw [hcode]
    omega
  have hmate : gm06DartMate (gap i) = gm06CutDart (2 * (rep.tagged.length + i.val)) 0 := by
    rw [← gm06CutDart_mate]
    simp [gm06DartMate]
  rw [terminalHeadWords_get _ hbound, hmate, (rep.inner_copied_origins hG i).1,
    (rep.inner_copied_origins hG i).2] at hwalk
  exact hwalk

/-- The complete rotated walk has a marked head, so the finite
first-contact trace always succeeds. -/
theorem current_terminal_contact (hG : IsCylinderSection5Drawing k G)
    (i : Fin k) (row : List ℕ)
    (horbit : ∀ q, q ∈ row ↔ ∃ n, cutNext^[n] (gap i) = q)
    (hnd : row.Nodup) (hgap : (gap i) ∈ row)
    (horder : ∀ q ∈ row, row.formPerm q = cutNext q) :
    ∃ q ∈ gm06TerminalFaceDarts (gap i) row,
      (targets i)[(gm06TerminalHeadWords edgeCount (currentCut).origins)[q]?.getD 0]?.getD 0 ≠ 0 := by
  have hwalk := rep.current_terminal_walk hG i row horbit hnd hgap horder
  have hne : gm06TerminalFaceDarts (gap i) row ≠ [] := by
    intro he
    rw [he] at hwalk
    have hends : gm06CutVertex (rep.source i).val true =
        gm06CutVertex (rep.source (finSuccCycle i)).val false := dartWalk_nil_end hwalk
    simp only [gm06CutVertex, Bool.not_true, Bool.not_false, Bool.toNat_true, Bool.toNat_false] at hends
    omega
  refine ⟨_, List.getLast_mem hne, ?_⟩
  rw [← GraphMinor.GM06.GM06DartWalk.end_eq hwalk hne]
  exact rep.terminal_end_marked hn i

end GM06CurrentDrawingRep
end GraphMinor.GM06
