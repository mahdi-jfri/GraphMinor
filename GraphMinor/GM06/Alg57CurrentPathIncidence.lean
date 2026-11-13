module

public import GraphMinor.GM06.Alg57ComputedPathRows
import GraphMinor.GM11.Section87
import GraphMinor.GM06.Section5RegionGraphPath

/-!
# Path and opposite-boundary vertex incidence

For VI (5.7), page 133, the boundary lists consist of one chosen
copy of every vertex of the corresponding linkage path. Their
projection is injective because those original slots are live.
The selected face meets the left boundary in left copies and the
opposite boundary in right copies. These facts justify the upper
boundary test, injectivity with the listed path included, and the
vertex-incidence test along that path.
-/

public section
namespace GraphMinor.GM06
open Set GraphMinor.Surface GraphMinor.GM11 GraphMinor.Compute

/-- Either copied vertex has the parity prescribed by its side. -/
theorem cutVertexFin_mod (n : ℕ) (hn : 0 < n) (v : ℕ) (left : Bool) :
    (gm06CutVertexFin n hn v left).val % 2 = (!left).toNat := by
  cases left <;> simp [gm06CutVertexFin, gm06CutVertex, Nat.add_mod]

/-- Every vertex in a computed boundary list has the chosen side's parity. -/
theorem cutPathLabels_mod (n : ℕ) (hn : 0 < n) (origins path : List ℕ)
    (source : ℕ) (left : Bool) {u : Fin (2 * n)}
    (hu : u ∈ gm06CutPathLabels n hn origins path source left) : u.val % 2 = (!left).toNat := by
  simp only [gm06CutPathLabels, find4PathLabels, gm06CutPathSteps, List.map_map,
    Function.comp_def, List.mem_cons, List.mem_map] at hu
  rcases hu with rfl | ⟨d, _, rfl⟩ <;> exact cutVertexFin_mod n hn _ left

namespace GM06CurrentDrawingRep
variable {k : ℕ} {x : GM06SuccessorInput} {G : Drawing ClosedCylinder}
  {L : CylinderLinkage k G} (rep : GM06CurrentDrawingRep x G L)
  (hn : 0 < x.vertexCount)
include rep

set_option quotPrecheck false in
local notation "labels" i:arg left:arg =>
  gm06CutPathLabels x.vertexCount hn x.endpoints
    (x.linkage[Fin.val (i : Fin k)]'(by rw [rep.linkage.1]; exact Fin.isLt (i : Fin k)))
    (Fin.val (rep.source (i : Fin k))) left
local notation "currentCut" => gm06CutDataOfLinkage x.vertexCount rep.tagged.length x.endpoints
  x.linkage x.innerCuff x.outerCuff x.rotations (List.range x.vertexCount)
local notation "cutNext" => Equiv.trans dartMatePerm
  (Equiv.symm (gm06RotationPermutation (GM06CutData.rotations currentCut)))
local notation "gap" i:arg => gm06CutDart (2 * (rep.tagged.length + Fin.val (i : Fin k)) + 1) 0

/-- Equal points at live copied slots with equal parity have equal
copied labels. -/
theorem cutVertexPoint_inj_of_parity (u w : Fin (2 * x.vertexCount))
    (hu : (⟨u.val / 2, by have hh := u.isLt; omega⟩ : Fin x.vertexCount) ∈ rep.live)
    (hw : (⟨w.val / 2, by have hh := w.isLt; omega⟩ : Fin x.vertexCount) ∈ rep.live)
    (hpar : u.val % 2 = w.val % 2) (heq : rep.cutVertexPoint u = rep.cutVertexPoint w) : u = w := by
  have hhalf : u.val / 2 = w.val / 2 := congrArg Fin.val (rep.vertex_inj hu hw heq)
  apply Fin.ext
  omega

/-- Every copied vertex in an actual boundary list projects to a
live original slot. -/
theorem computed_path_labels_live (i : Fin k) (left : Bool) {u : Fin (2 * x.vertexCount)}
    (hu : u ∈ labels i left) :
    (⟨u.val / 2, by have hh := u.isLt; omega⟩ : Fin x.vertexCount) ∈ rep.live := by
  simp only [gm06CutPathLabels, find4PathLabels, gm06CutPathSteps, List.map_map,
    Function.comp_def, List.mem_cons, List.mem_map] at hu
  rcases hu with rfl | ⟨d, hd, rfl⟩
  · have he : (⟨(gm06CutVertexFin x.vertexCount hn (rep.source i).val left).val / 2,
        by have hh := (gm06CutVertexFin x.vertexCount hn (rep.source i).val left).isLt; omega⟩ :
        Fin x.vertexCount) = rep.source i := by
      apply Fin.ext
      change gm06CutVertex ((rep.source i).val % x.vertexCount) left / 2 = (rep.source i).val
      rw [gm06CutVertex_project, Nat.mod_eq_of_lt (rep.source i).isLt]
    exact he.symm ▸ rep.source_live i
  · obtain ⟨a, ha, halive, _⟩ := rep.path_origin_mem i true hd
    simp only [ite_true] at ha
    have he : (⟨(gm06CutVertexFin x.vertexCount hn
        (x.endpoints[gm06DartMate d]?.getD 0) left).val / 2,
        by have hh := (gm06CutVertexFin x.vertexCount hn
          (x.endpoints[gm06DartMate d]?.getD 0) left).isLt; omega⟩ : Fin x.vertexCount) = a := by
      apply Fin.ext
      change gm06CutVertex ((x.endpoints[gm06DartMate d]?.getD 0) % x.vertexCount) left / 2 = a.val
      rw [gm06CutVertex_project]
      rw [ha, Nat.mod_eq_of_lt a.isLt]
    exact he.symm ▸ halive

/-- Among live labels, a computed boundary list consists exactly
of its path's vertices with the chosen copied parity. -/
theorem mem_computed_path_labels_iff (i : Fin k) (left : Bool) (u : Fin (2 * x.vertexCount))
    (hu : (⟨u.val / 2, by have hh := u.isLt; omega⟩ : Fin x.vertexCount) ∈ rep.live) :
    u ∈ labels i left ↔ rep.cutVertexPoint u ∈ (L.pathDrawing i).V ∧ u.val % 2 = (!left).toNat := by
  obtain ⟨W, _, hWV, hsupport, _⟩ := rep.computed_path_walk hn i left
  constructor
  · intro hm
    refine ⟨?_, cutPathLabels_mod _ hn _ _ _ left hm⟩
    rw [hWV, hsupport]
    exact List.mem_map.mpr ⟨u, hm, rfl⟩
  · rintro ⟨hV, hpar⟩
    rw [hWV, hsupport] at hV
    obtain ⟨w, hw, heq⟩ := List.mem_map.mp hV
    have huw : w = u := rep.cutVertexPoint_inj_of_parity w u
      (rep.computed_path_labels_live hn i left hw) hu
      ((cutPathLabels_mod _ hn _ _ _ left hw).trans hpar.symm) heq
    exact huw ▸ hw

/-- An incident label always projects to a live original slot. -/
theorem selected_face_vertex_live (hG : IsCylinderSection5Drawing k G)
    (i : Fin k) (row : List ℕ)
    (horbit : ∀ q, q ∈ row ↔ ∃ n, cutNext^[n] (gap i) = q)
    (u : Fin (2 * x.vertexCount))
    (hu : (gm06IncV (2 * x.vertexCount) (currentCut).origins row)[u.val]?.getD 0 ≠ 0) :
    (⟨u.val / 2, by have hh := u.isLt; omega⟩ : Fin x.vertexCount) ∈ rep.live := by
  obtain ⟨q, hq, hqu⟩ := (incV_getD_ne_zero_iff _ _ _ u).mp hu
  have hactive := rep.cut_face_row_active hG (List.range x.vertexCount) i horbit q hq
  have hslot := rep.cut_active_origin_row hactive
  rw [hqu] at hslot
  exact rep.live_of_mem_row (splitRows_project_mem _ x.rotations u.val q hslot)

/-- On an incident label, membership in the computed right boundary
means exactly membership in the next linkage path. -/
theorem selected_face_upper_iff (hk : 1 < k) (hG : IsCylinderSection5Drawing k G)
    (i : Fin k) (row : List ℕ)
    (horbit : ∀ q, q ∈ row ↔ ∃ n, cutNext^[n] (gap i) = q)
    (u : Fin (2 * x.vertexCount))
    (hu : (gm06IncV (2 * x.vertexCount) (currentCut).origins row)[u.val]?.getD 0 ≠ 0) :
    u ∈ labels (finSuccCycle i) false ↔
      rep.cutVertexPoint u ∈ (L.pathDrawing (finSuccCycle i)).U := by
  rw [rep.mem_computed_path_labels_iff hn _ _ u (rep.selected_face_vertex_live hG i row horbit u hu)]
  constructor
  · exact fun h => (L.pathDrawing _).V_subset_U h.1
  · intro hU
    have hGv := (rep.selected_face_vertex_dart hG i row horbit u hu).1
    refine ⟨mem_V_of_mem_U' (L.isSubdrawing _).1 hU hGv, ?_⟩
    rcases rep.selected_face_path_side hG i row horbit u hu (finSuccCycle i) hU with h | h
    · exact False.elim (finSuccCycle_ne_of_one_lt hk i h.2)
    · exact h.1

/-- Vertex labels remain injective when the whole listed left path
is included alongside the incident labels, as required by FIND_4. -/
theorem selected_face_path_union_inj (hk : 1 < k) (hG : IsCylinderSection5Drawing k G)
    (i : Fin k) (row : List ℕ)
    (horbit : ∀ q, q ∈ row ↔ ∃ n, cutNext^[n] (gap i) = q)
    (u w : Fin (2 * x.vertexCount))
    (hu : (gm06IncV (2 * x.vertexCount) (currentCut).origins row)[u.val]?.getD 0 ≠ 0 ∨
      u ∈ labels i true)
    (hw : (gm06IncV (2 * x.vertexCount) (currentCut).origins row)[w.val]?.getD 0 ≠ 0 ∨
      w ∈ labels i true)
    (heq : rep.cutVertexPoint u = rep.cutVertexPoint w) : u = w := by
  have hmixed (a b : Fin (2 * x.vertexCount))
      (ha : (gm06IncV (2 * x.vertexCount) (currentCut).origins row)[a.val]?.getD 0 ≠ 0)
      (hb : b ∈ labels i true) (hab : rep.cutVertexPoint a = rep.cutVertexPoint b) : a = b := by
    have hbLive := rep.computed_path_labels_live hn i true hb
    have hbV := ((rep.mem_computed_path_labels_iff hn i true b hbLive).mp hb).1
    have haU : rep.cutVertexPoint a ∈ (L.pathDrawing i).U :=
      hab.symm ▸ (L.pathDrawing i).V_subset_U hbV
    have hpar : a.val % 2 = 0 := by
      rcases rep.selected_face_path_side hG i row horbit a ha i haU with h | h
      · exact h.1
      · exact False.elim (finSuccCycle_ne_of_one_lt hk i h.2.symm)
    apply rep.cutVertexPoint_inj_of_parity a b (rep.selected_face_vertex_live hG i row horbit a ha)
      hbLive _ hab
    simpa only [Bool.not_true, Bool.toNat_false] using hpar.trans (cutPathLabels_mod _ hn _ _ _ true hb).symm
  rcases hu with hu | hu <;> rcases hw with hw | hw
  · exact rep.selected_face_vertex_inj hk hG i row horbit u w hu hw heq
  · exact hmixed u w hu hw heq
  · exact (hmixed w u hw hu heq.symm).symm
  · exact rep.cutVertexPoint_inj_of_parity u w (rep.computed_path_labels_live hn i true hu)
      (rep.computed_path_labels_live hn i true hw)
      ((cutPathLabels_mod _ hn _ _ _ true hu).trans (cutPathLabels_mod _ hn _ _ _ true hw).symm) heq

/-- On the listed left path, the computed vertex-incidence bit is
exactly geometric incidence with the prescribed region closure. -/
theorem computed_path_incV_iff (hk : 1 < k) (hG : IsCylinderSection5Drawing k G)
    (hno : ∀ (G₁ : Drawing ClosedCylinder) (L₁ : CylinderLinkage k G₁),
      IsCylinderSection5Drawing k G₁ → ¬ Section5Reduction2Step k G L G₁ L₁) (i : Fin k) (row : List ℕ)
    (horbit : ∀ q, q ∈ row ↔ ∃ n, cutNext^[n] (gap i) = q)
    (u : Fin (2 * x.vertexCount)) (hu : u ∈ labels i true) :
    (gm06IncV (2 * x.vertexCount) (currentCut).origins row)[u.val]?.getD 0 ≠ 0 ↔
      rep.cutVertexPoint u ∈ closure (cylinderRegion k G i) := by
  constructor
  · exact fun h => (rep.selected_face_vertex_sound hk hG hno i row horbit u h).2
  · intro hR
    have hlive := rep.computed_path_labels_live hn i true hu
    have hV := rep.vertex_mem ⟨u.val / 2, by have hh := u.isLt; omega⟩ hlive
    obtain ⟨w, hw, heq⟩ := rep.selected_face_vertex_cover hk hG hno i row horbit _ hV hR
    have hwu := rep.selected_face_path_union_inj hn hk hG i row horbit w u (Or.inl hw) (Or.inr hu) heq
    exact hwu ▸ hw

end GM06CurrentDrawingRep
end GraphMinor.GM06
