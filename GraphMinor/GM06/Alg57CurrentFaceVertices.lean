module

public import GraphMinor.GM06.Alg57CurrentCutVertexInjectivity
public import GraphMinor.GM06.Alg57CurrentCutComponents
import GraphMinor.Compute.GM06CutOriginFacts
import GraphMinor.GM11.Section87
import GraphMinor.GM06.Section5RegionGraphPath
import GraphMinor.GM06.Alg57CuffRotation

/-!
# Vertex labels read from the actual selected face row

The vertex incidence bits in VI (5.7), page 133, mark exactly the
origins encountered by the selected cut face. Each origin reads its
actual copied row slot. The row interpretation gives a live vertex
of the current drawing, and the side classification makes these
labels injective when there are at least two linkage paths.
-/

public section
namespace GraphMinor.GM06
open Set GraphMinor.Surface GraphMinor.GM11 GraphMinor.Compute

/-- A nonzero vertex-incidence bit means that the vertex is the
origin of an end in the selected row. -/
theorem incV_getD_ne_zero_iff (n : ℕ) (origins row : List ℕ) (u : Fin n) :
    (gm06IncV n origins row)[u.val]?.getD 0 ≠ 0 ↔
      ∃ d ∈ row, origins[d]?.getD 0 = u.val := by
  simp only [gm06IncV, gm06IncidenceBits, List.getElem?_ofFn, u.isLt, dite_true,
    Option.getD_some, gm06FaceVertices, List.mem_map]
  split_ifs with h
  · simpa only [ne_eq, one_ne_zero, not_false_eq_true, true_iff] using h
  · simp only [ne_eq, not_true_eq_false, false_iff]
    exact h

namespace GM06CurrentDrawingRep
variable {k : ℕ} {x : GM06SuccessorInput} {G : Drawing ClosedCylinder}
  {L : CylinderLinkage k G} (rep : GM06CurrentDrawingRep x G L)
include rep

local notation "currentCut" => gm06CutDataOfLinkage x.vertexCount rep.tagged.length x.endpoints
  x.linkage x.innerCuff x.outerCuff x.rotations (List.range x.vertexCount)
local notation "cutNext" => Equiv.trans dartMatePerm (Equiv.symm (gm06RotationPermutation (GM06CutData.rotations currentCut)))
local notation "gap" i => gm06CutDart (2 * (rep.tagged.length + Fin.val (i : Fin k)) + 1) 0

/-- Every active copied end is in the row at its stored origin. -/
theorem cut_active_origin_row {q : ℕ} (hq : q ∈ (currentCut).activeDarts) :
    q ∈ (currentCut).rotations.getD ((currentCut).origins[q]?.getD 0) [] := by
  have hact := (gm06CutDataOfLinkage_active_iff _ _ _ _ _ _ _ _ _).mp hq
  have hv := (rep.cut_origins_valid q hq).1
  have hlen : (currentCut).origins[q]?.getD 0 < (currentCut).rotations.length := by
    simpa only [gm06CutDataOfLinkage, gm06SplitRotationRows_length, rep.rows_length] using hv
  rw [List.getD_eq_getElem _ _ hlen]
  exact (gm06CutOrigins_row_iff _ (gm06SplitRotationRows_nodup _ _ rep.rows_flatten_nodup)
    hact.2 hact.1 hlen).mp rfl

/-- Incident labels on an actual selected face row are injective
under projection to the current drawing's vertices. -/
theorem selected_face_vertex_inj (hk : 1 < k) (hG : IsCylinderSection5Drawing k G)
    (i : Fin k) (row : List ℕ)
    (horbit : ∀ q, q ∈ row ↔ ∃ n, cutNext^[n] (gap i) = q)
    (u w : Fin (2 * x.vertexCount))
    (hu : (gm06IncV (2 * x.vertexCount) (currentCut).origins row)[u.val]?.getD 0 ≠ 0)
    (hw : (gm06IncV (2 * x.vertexCount) (currentCut).origins row)[w.val]?.getD 0 ≠ 0)
    (heq : rep.cutVertexPoint u = rep.cutVertexPoint w) : u = w := by
  obtain ⟨q, hq, hqu⟩ := (incV_getD_ne_zero_iff _ _ _ u).mp hu
  obtain ⟨r, hr, hrw⟩ := (incV_getD_ne_zero_iff _ _ _ w).mp hw
  have hactive := rep.cut_face_row_active hG (List.range x.vertexCount) i horbit
  have hqr := rep.cut_active_origin_row (hactive q hq)
  have hrr := rep.cut_active_origin_row (hactive r hr)
  rw [hqu] at hqr
  rw [hrw] at hrr
  obtain ⟨n₁, rfl⟩ := (horbit q).mp hq
  obtain ⟨n₂, rfl⟩ := (horbit r).mp hr
  exact rep.cut_iterate_vertex_inj hk hG i n₁ n₂ u w hqr hrr heq

/-- A face-incidence label projects to a live vertex and an actual
cuffed dart at that vertex, with the indicated permanent word. -/
theorem selected_face_vertex_dart (hG : IsCylinderSection5Drawing k G)
    (i : Fin k) (row : List ℕ)
    (horbit : ∀ q, q ∈ row ↔ ∃ n, cutNext^[n] (gap i) = q)
    (u : Fin (2 * x.vertexCount))
    (hu : (gm06IncV (2 * x.vertexCount) (currentCut).origins row)[u.val]?.getD 0 ≠ 0) :
    rep.cutVertexPoint u ∈ G.V ∧ ∃ d : DrawingDart (cylinderSphereDrawing rep.cuffed),
      dartVertex rep.par d = cylinderToSphere (rep.cutVertexPoint u) ∧
        ∃ q ∈ row, gm06UncutDart q = persistentDartLabel rep.label d := by
  obtain ⟨q, hq, hqu⟩ := (incV_getD_ne_zero_iff _ _ _ u).mp hu
  have hactive := rep.cut_face_row_active hG (List.range x.vertexCount) i horbit q hq
  obtain ⟨a, ha, halive, d, hd, hl⟩ := rep.cut_origin_point (List.range x.vertexCount) hactive
  rw [hqu] at ha
  have hap : rep.vertex a = rep.cutVertexPoint u := congrArg rep.vertex (Fin.ext ha)
  exact ⟨hap ▸ rep.vertex_mem a halive, d, hd.trans (congrArg cylinderToSphere hap), q, hq, hl.symm⟩

/-- Every nonzero incidence bit in the selected row names a vertex
of the current graph in the closure of the prescribed region. -/
theorem selected_face_vertex_sound (hk : 1 < k) (hG : IsCylinderSection5Drawing k G)
    (hno : ∀ (G₁ : Drawing ClosedCylinder) (L₁ : CylinderLinkage k G₁),
      IsCylinderSection5Drawing k G₁ → ¬ Section5Reduction2Step k G L G₁ L₁) (i : Fin k) (row : List ℕ)
    (horbit : ∀ q, q ∈ row ↔ ∃ n, cutNext^[n] (gap i) = q)
    (u : Fin (2 * x.vertexCount))
    (hu : (gm06IncV (2 * x.vertexCount) (currentCut).origins row)[u.val]?.getD 0 ≠ 0) :
    rep.cutVertexPoint u ∈ G.V ∧ rep.cutVertexPoint u ∈ closure (cylinderRegion k G i) := by
  obtain ⟨hV, d, hd, q, hq, hlabel⟩ := rep.selected_face_vertex_dart hG i row horbit u hu
  refine ⟨hV, ((rep.region_incidence_cut_orbit hk hG hno i).1 _ hV).mpr ⟨d, hd, ?_⟩⟩
  obtain ⟨n, hn⟩ := (horbit q).mp hq
  exact ⟨n, (congrArg gm06UncutDart hn).trans hlabel⟩

/-- Every current vertex in the region closure has a nonzero
incidence bit at a copied slot representing that same vertex. -/
theorem selected_face_vertex_cover (hk : 1 < k) (hG : IsCylinderSection5Drawing k G)
    (hno : ∀ (G₁ : Drawing ClosedCylinder) (L₁ : CylinderLinkage k G₁),
      IsCylinderSection5Drawing k G₁ → ¬ Section5Reduction2Step k G L G₁ L₁) (i : Fin k) (row : List ℕ)
    (horbit : ∀ q, q ∈ row ↔ ∃ n, cutNext^[n] (gap i) = q)
    (v : ClosedCylinder) (hv : v ∈ G.V) (hvR : v ∈ closure (cylinderRegion k G i)) :
    ∃ u : Fin (2 * x.vertexCount),
      (gm06IncV (2 * x.vertexCount) (currentCut).origins row)[u.val]?.getD 0 ≠ 0 ∧
        rep.cutVertexPoint u = v := by
  obtain ⟨d, hd, n, hlabel⟩ := ((rep.region_incidence_cut_orbit hk hG hno i).1 v hv).mp hvR
  let q := cutNext^[n] (gap i)
  have hq : q ∈ row := (horbit q).mpr ⟨n, rfl⟩
  have hactive := rep.cut_face_row_active hG (List.range x.vertexCount) i horbit q hq
  let u : Fin (2 * x.vertexCount) := ⟨(currentCut).origins[q]?.getD 0,
    (rep.cut_origins_valid q hactive).1⟩
  have hinc : (gm06IncV (2 * x.vertexCount) (currentCut).origins row)[u.val]?.getD 0 ≠ 0 :=
    (incV_getD_ne_zero_iff _ _ _ u).mpr ⟨q, hq, rfl⟩
  obtain ⟨a, ha, halive, e, he, helabel⟩ := rep.cut_origin_point (List.range x.vertexCount) hactive
  have hed : e = d := persistentDartLabel_injective rep.label (helabel.trans hlabel)
  have hav : rep.vertex a = v := injective_cylinderToSphere
    (he.symm.trans ((congrArg (dartVertex rep.par) hed).trans hd))
  have hau : rep.vertex a = rep.cutVertexPoint u := congrArg rep.vertex (Fin.ext ha)
  exact ⟨u, hinc, hau.symm.trans hav⟩

/-- The actual cuff-rooted component query supplies sound, covering,
and injective incident vertex labels, with no representation premise
for the query or its copied slots. -/
theorem component_face_vertex_spec (hk : 1 < k) (hG : IsCylinderSection5Drawing k G)
    (hno : ∀ (G₁ : Drawing ClosedCylinder) (L₁ : CylinderLinkage k G₁),
      IsCylinderSection5Drawing k G₁ → ¬ Section5Reduction2Step k G L G₁ L₁) (i : Fin k) :
    ∃ root : Fin (2 * x.vertexCount),
      root.val = gm06CutInnerRoot currentCut rep.tagged.length i.val ∧
      ∃ row : List ℕ, gm06CutFaceIncidence (2 * x.vertexCount)
        (2 * (rep.tagged.length + (k + k))) (gm06CutComponentData currentCut root)
        (4 * (rep.tagged.length + i.val) + 1) =
          some (row, gm06IncV (2 * x.vertexCount) (currentCut).origins row,
            gm06IncE (2 * (rep.tagged.length + (k + k))) row) ∧
      (∀ u : Fin (2 * x.vertexCount),
        (gm06IncV (2 * x.vertexCount) (currentCut).origins row)[u.val]?.getD 0 ≠ 0 →
          rep.cutVertexPoint u ∈ G.V ∧ rep.cutVertexPoint u ∈ closure (cylinderRegion k G i)) ∧
      (∀ v ∈ G.V, v ∈ closure (cylinderRegion k G i) →
        ∃ u : Fin (2 * x.vertexCount),
          (gm06IncV (2 * x.vertexCount) (currentCut).origins row)[u.val]?.getD 0 ≠ 0 ∧
            rep.cutVertexPoint u = v) ∧
      (∀ u w : Fin (2 * x.vertexCount),
        (gm06IncV (2 * x.vertexCount) (currentCut).origins row)[u.val]?.getD 0 ≠ 0 →
        (gm06IncV (2 * x.vertexCount) (currentCut).origins row)[w.val]?.getD 0 ≠ 0 →
        rep.cutVertexPoint u = rep.cutVertexPoint w → u = w) := by
  obtain ⟨root, hroot, row, hout, horbit⟩ := rep.component_cut_face_row hG i
  have hcode : (gap i) = 4 * (rep.tagged.length + i.val) + 1 := by
    simp [gm06CutDart, Nat.add_div, Nat.add_mod]
  have horbit' : ∀ q, q ∈ row ↔ ∃ n, cutNext^[n] (gap i) = q := by
    simpa only [hcode] using horbit
  exact ⟨root, hroot, row, hout,
    rep.selected_face_vertex_sound hk hG hno i row horbit',
    rep.selected_face_vertex_cover hk hG hno i row horbit',
    rep.selected_face_vertex_inj hk hG i row horbit'⟩

/-- Every live vertex on a linkage path has a decoded split
position: the start has an outgoing end and every other vertex
has an incoming end in that path's encoded walk. -/
theorem cut_position_ne_none_of_path (a : Fin x.vertexCount) (halive : a ∈ rep.live)
    (j : Fin k) (ha : rep.vertex a ∈ (L.pathDrawing j).U) :
    gm06CutPositionAt (gm06BuildCutTables x.vertexCount rep.tagged.length
      x.endpoints x.linkage x.innerCuff x.outerCuff) a.val ≠ none := by
  intro hp
  obtain ⟨hin, hout⟩ := (gm06CutPositionAt_none_iff _ _).mp hp
  by_cases hs : rep.vertex a = cylinderM1Point k j
  · have has : a = rep.source j := rep.vertex_inj halive (rep.source_live j)
      (hs.trans (rep.source_point j).symm)
    exact rep.source_outgoing_pos j (has ▸ hout)
  obtain ⟨W, _, henc, hP⟩ := rep.linkage.path j
  have hav : rep.vertex a ∈ (L.pathDrawing j).V :=
    mem_V_of_mem_U' (L.isSubdrawing j).1 ha (rep.vertex_mem a halive)
  have hsupport : rep.vertex a ∈ W.support := by
    rw [← hP, walkDrawing_V] at hav
    exact hav
  have htail : rep.vertex a ∈ W.support.tail := by
    rw [W.support_eq_cons] at hsupport
    exact (List.mem_cons.mp hsupport).resolve_left hs
  have hkey := (rep.path_key_mem_iff j true a halive W henc).mpr htail
  have hnot := (path_mark_zero_iff x.endpoints x.linkage true a
    (rep.cut_path_keys_nodup true)).mp hin
  rw [gm06CutPathEndPairs_keys, List.map_flatten] at hnot
  apply hnot
  exact List.mem_flatten.mpr ⟨_, List.mem_map.mpr ⟨_, List.getElem_mem _, rfl⟩, hkey⟩

/-- An incident copied label on a linkage path is either the left
copy on the selecting path or the right copy on its successor. -/
theorem selected_face_path_side (hG : IsCylinderSection5Drawing k G)
    (i : Fin k) (row : List ℕ)
    (horbit : ∀ q, q ∈ row ↔ ∃ n, cutNext^[n] (gap i) = q)
    (u : Fin (2 * x.vertexCount))
    (hu : (gm06IncV (2 * x.vertexCount) (currentCut).origins row)[u.val]?.getD 0 ≠ 0)
    (j : Fin k) (hj : rep.cutVertexPoint u ∈ (L.pathDrawing j).U) :
    (u.val % 2 = 0 ∧ j = i) ∨ (u.val % 2 = 1 ∧ j = finSuccCycle i) := by
  obtain ⟨q, hq, hqu⟩ := (incV_getD_ne_zero_iff _ _ _ u).mp hu
  have hactive := rep.cut_face_row_active hG (List.range x.vertexCount) i horbit q hq
  have hslot := rep.cut_active_origin_row hactive
  rw [hqu] at hslot
  let a : Fin x.vertexCount := ⟨u.val / 2, by have hh := u.isLt; omega⟩
  have halive : a ∈ rep.live := rep.live_of_mem_row
    (splitRows_project_mem _ x.rotations u.val q hslot)
  have hja : rep.vertex a ∈ (L.pathDrawing j).U := hj
  obtain ⟨p, hp⟩ := Option.ne_none_iff_exists'.mp (rep.cut_position_ne_none_of_path a halive j hja)
  obtain ⟨n, rfl⟩ := (horbit q).mp hq
  by_cases hpar : u.val % 2 = 0
  · have he : u.val = gm06CutVertex a.val true := by
      simp only [gm06CutVertex, Bool.not_true, Bool.toNat_false, Nat.add_zero]
      dsimp only [a]
      omega
    have hji := rep.cut_iterate_path_side hG i n a j hja p hp true (he ▸ hslot)
    exact Or.inl ⟨hpar, hji⟩
  · have hpar' : u.val % 2 = 1 := by omega
    have he : u.val = gm06CutVertex a.val false := by
      simp only [gm06CutVertex, Bool.not_false, Bool.toNat_true]
      dsimp only [a]
      omega
    have hji := rep.cut_iterate_path_side hG i n a j hja p hp false (he ▸ hslot)
    simp only [Bool.false_eq_true, ite_false] at hji
    exact Or.inr ⟨hpar', (finSuccCycle_pred_eq j).symm.trans (congrArg finSuccCycle hji)⟩

end GM06CurrentDrawingRep
end GraphMinor.GM06
