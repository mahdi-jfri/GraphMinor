module

public import GraphMinor.GM06.Alg57FiniteFaceOrbit
public import GraphMinor.GM06.Alg57CutFaceLink
import GraphMinor.GM06.Alg57CurrentCutOrigins

/-!
# Face orbits survive restriction to a cut component

For VI (5.7), page 133, all ends in one vertex row have the same
origin. An edge belongs to a component exactly when its origin does.
Consequently restricting to a component keeps or removes whole rows.
The face successor and its iterates agree on the component's active
ends. This is a finite graph fact, independent of strip geometry.
-/

public section
namespace GraphMinor.GM06
open GraphMinor.Compute

/-- A paired active end belongs to the root component exactly when
its stored origin belongs to that component. -/
theorem cutComponentEdges_iff_origin {n : ℕ} (data : GM06CutData) (root : Fin n)
    (hpair : ∀ d ∈ data.activeDarts, gm06DartMate d ∈ data.activeDarts)
    (hbound : ∀ d ∈ data.activeDarts, data.origins[d]?.getD 0 < n)
    (hlive : ∀ d ∈ data.activeDarts, data.origins[d]?.getD 0 ∈ data.vertices)
    {d : ℕ} (hd : d ∈ data.activeDarts) :
    d / 2 ∈ gm06CutComponentEdges data root ↔
      data.origins[d]?.getD 0 ∈ gm06CutComponentVertices data root := by
  have hm := hpair d hd
  have he := gm06CutEdgeLabels_of_pair data d hd hm
  have hends := gm06CutEndpoints_dart data d
  let a : Fin n := ⟨data.origins[d]?.getD 0, hbound d hd⟩
  let b : Fin n := ⟨data.origins[gm06DartMate d]?.getD 0, hbound _ hm⟩
  have hab : (gm06CutGraph n data).Reachable a b := by
    by_cases hh : a = b
    · rw [hh]
    · have hadj : (gm06CutGraph n data).Adj a b :=
        ⟨hh, hlive d hd, hlive _ hm, d / 2, he, hends⟩
      exact hadj.reachable
  have hsame : data.origins[d]?.getD 0 ∈ gm06CutComponentVertices data root ↔
      data.origins[gm06DartMate d]?.getD 0 ∈ gm06CutComponentVertices data root := by
    change a.val ∈ _ ↔ b.val ∈ _
    rw [gm06CutComponentVertices_mem_iff, gm06CutComponentVertices_mem_iff]
    exact ⟨fun h => h.trans hab, fun h => h.trans hab.symm⟩
  rw [gm06CutComponentEdges_mem_iff]
  rcases hends with hends | hends <;>
    simp only [hends, he, true_and]
  · exact ⟨And.left, fun h => ⟨h, hsame.mp h⟩⟩
  · exact ⟨And.right, fun h => ⟨hsame.mp h, h⟩⟩

/-- Component restriction keeps a whole row whenever one of its
ends belongs to that component. -/
theorem cutComponentData_row_of_mem {n : ℕ} (data : GM06CutData) (root : Fin n)
    (hcover : ∀ d, d ∈ data.activeDarts ↔ d ∈ data.rotations.flatten)
    (hpair : ∀ d ∈ data.activeDarts, gm06DartMate d ∈ data.activeDarts)
    (hbound : ∀ d ∈ data.activeDarts, data.origins[d]?.getD 0 < n)
    (hlive : ∀ d ∈ data.activeDarts, data.origins[d]?.getD 0 ∈ data.vertices)
    (hrow : ∀ row ∈ data.rotations, ∀ a ∈ row, ∀ b ∈ row,
      data.origins[a]?.getD 0 = data.origins[b]?.getD 0)
    {row : List ℕ} (hr : row ∈ data.rotations) {d : ℕ} (hd : d ∈ row)
    (hcomp : d / 2 ∈ gm06CutComponentEdges data root) :
    row ∈ (gm06CutComponentData data root).rotations := by
  have hda := (hcover d).mpr (List.mem_flatten.mpr ⟨row, hr, hd⟩)
  have hkeep : row.filter (fun a => decide (a / 2 ∈ gm06CutComponentEdges data root)) = row := by
    apply List.filter_eq_self.mpr
    intro a ha
    have haa := (hcover a).mpr (List.mem_flatten.mpr ⟨row, hr, ha⟩)
    apply decide_eq_true
    apply (cutComponentEdges_iff_origin data root hpair hbound hlive haa).mpr
    rw [hrow row hr a ha d hd]
    exact (cutComponentEdges_iff_origin data root hpair hbound hlive hda).mp hcomp
  change row ∈ data.rotations.map _
  exact List.mem_map.mpr ⟨row, hr, hkeep⟩

/-- The numeric face successor in a component is the full face
successor at every active end of the component. -/
theorem cutComponentData_face_eq {n : ℕ} (data : GM06CutData) (root : Fin n)
    (hnd : data.rotations.flatten.Nodup)
    (hcover : ∀ d, d ∈ data.activeDarts ↔ d ∈ data.rotations.flatten)
    (hpair : ∀ d ∈ data.activeDarts, gm06DartMate d ∈ data.activeDarts)
    (hbound : ∀ d ∈ data.activeDarts, data.origins[d]?.getD 0 < n)
    (hlive : ∀ d ∈ data.activeDarts, data.origins[d]?.getD 0 ∈ data.vertices)
    (hrow : ∀ row ∈ data.rotations, ∀ a ∈ row, ∀ b ∈ row,
      data.origins[a]?.getD 0 = data.origins[b]?.getD 0)
    {d : ℕ} (hd : d ∈ (gm06CutComponentData data root).activeDarts) :
    (dartMatePerm.trans (gm06RotationPermutation (gm06CutComponentData data root).rotations).symm) d =
      (dartMatePerm.trans (gm06RotationPermutation data.rotations).symm) d := by
  have hdm := gm06CutComponentData_mate_closed data root d hd
  obtain ⟨hma, hmc⟩ := (gm06CutComponentData_active_iff data root _).mp hdm
  obtain ⟨row, hr, hdr⟩ := List.mem_flatten.mp ((hcover _).mp hma)
  have hrc := cutComponentData_row_of_mem data root hcover hpair hbound hlive hrow hr hdr hmc
  simp only [Equiv.trans_apply, dartMatePerm_apply]
  rw [rotationPermutation_symm_apply_row _ (gm06CutComponentData_nodup data root hnd) row hrc _ hdr,
    rotationPermutation_symm_apply_row _ hnd row hr _ hdr]

/-- Iterating the face successor from an active component end agrees
with iterating it in the full computed cut. -/
theorem cutComponentData_face_iterate_eq {n : ℕ} (data : GM06CutData) (root : Fin n)
    (hnd : data.rotations.flatten.Nodup)
    (hcover : ∀ d, d ∈ data.activeDarts ↔ d ∈ data.rotations.flatten)
    (hpair : ∀ d ∈ data.activeDarts, gm06DartMate d ∈ data.activeDarts)
    (hbound : ∀ d ∈ data.activeDarts, data.origins[d]?.getD 0 < n)
    (hlive : ∀ d ∈ data.activeDarts, data.origins[d]?.getD 0 ∈ data.vertices)
    (hrow : ∀ row ∈ data.rotations, ∀ a ∈ row, ∀ b ∈ row,
      data.origins[a]?.getD 0 = data.origins[b]?.getD 0)
    {d : ℕ} (hd : d ∈ (gm06CutComponentData data root).activeDarts) (j : ℕ) :
    (dartMatePerm.trans (gm06RotationPermutation (gm06CutComponentData data root).rotations).symm)^[j] d =
      (dartMatePerm.trans (gm06RotationPermutation data.rotations).symm)^[j] d := by
  have hc : ∀ a, a ∈ (gm06CutComponentData data root).activeDarts ↔
      a ∈ (gm06CutComponentData data root).rotations.flatten := by
    intro a
    rw [gm06CutComponentData_active_iff, gm06CutComponentData_flatten, List.mem_filter,
      decide_eq_true_eq, hcover]
  have hactive := numeric_face_iterate_active _ (gm06CutComponentData_nodup data root hnd)
    hc (gm06CutComponentData_mate_closed data root) hd
  induction j with
  | zero => rfl
  | succ j ih =>
    rw [Function.iterate_succ_apply', cutComponentData_face_eq data root hnd hcover hpair
      hbound hlive hrow (hactive j), ih, Function.iterate_succ_apply']

/-- The actual selected row in the root component contains exactly
the full cut's numeric orbit of its selecting dart. -/
theorem cutComponentFaceIncidence_orbit {n m target : ℕ} (data : GM06CutData) (root : Fin n)
    (hnd : data.rotations.flatten.Nodup)
    (hcover : ∀ d, d ∈ data.activeDarts ↔ d ∈ data.rotations.flatten)
    (hpair : ∀ d ∈ data.activeDarts, gm06DartMate d ∈ data.activeDarts)
    (hkeys : ∀ d ∈ data.activeDarts, d < 2 * m)
    (hbound : ∀ d ∈ data.activeDarts, data.origins[d]?.getD 0 < n)
    (hlive : ∀ d ∈ data.activeDarts, data.origins[d]?.getD 0 ∈ data.vertices)
    (hrow : ∀ row ∈ data.rotations, ∀ a ∈ row, ∀ b ∈ row,
      data.origins[a]?.getD 0 = data.origins[b]?.getD 0)
    (ht : target ∈ (gm06CutComponentData data root).activeDarts) :
    ∃ row : List ℕ, gm06CutFaceIncidence n m (gm06CutComponentData data root) target =
        some (row, gm06IncV n data.origins row, gm06IncE m row) ∧
      ∀ d : ℕ, d ∈ row ↔ ∃ j : ℕ,
        (dartMatePerm.trans (gm06RotationPermutation data.rotations).symm)^[j] target = d := by
  obtain ⟨hn, hc, ha, hk, hm⟩ := gm06CutComponentData_face_encoding data root hnd hcover hkeys
  obtain ⟨row, hout, horbit⟩ := cutFaceIncidence_orbit (gm06CutComponentData data root)
    hn hk ha hc hm ht
  refine ⟨row, hout, fun d => ?_⟩
  rw [horbit]
  exact exists_congr (fun j => by
    rw [cutComponentData_face_iterate_eq data root hnd hcover hpair hbound hlive hrow ht j])

end GraphMinor.GM06
