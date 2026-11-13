module

public import GraphMinor.GM06.Alg57CurrentEdgeIncidence
import GraphMinor.GM06.Section5RegionGraphPath

/-!
# FIND_4 representation from actual current arrays

For VI (5.7), page 133, the selected face uses the left copy of
any edge of its own linkage path. A right copy would have an
incident right endpoint on that same path, contradicting the
proved strip-side classification when there are at least two
paths. This supplies the last path-incidence field of FIND_4.
All fields are then assembled for the actual component face query.
-/

public section
namespace GraphMinor.GM06
open Set GraphMinor.Surface GraphMinor.GM11 GraphMinor.Compute

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

private theorem selected_path_edge_left (hk : 1 < k) (hG : IsCylinderSection5Drawing k G)
    (i : Fin k) (row : List ℕ)
    (horbit : ∀ q, q ∈ row ↔ ∃ n, cutNext^[n] (gap i) = q)
    {q d : ℕ} (hq : q ∈ row)
    (hd : d ∈ (x.linkage[i.val]'(by rw [rep.linkage.1]; exact i.isLt)))
    (hindex : gm06UncutDart q / 2 = d / 2) : q / 2 = 2 * (d / 2) := by
  have hdflat : d ∈ x.linkage.flatten := List.mem_flatten.mpr ⟨_, List.getElem_mem _, hd⟩
  have hwords : gm06UncutDart q = d ∨ gm06DartMate (gm06UncutDart q) = d := by
    have hm : gm06UncutDart q / 2 ∈ [d].map (fun a => a / 2) := by
      simpa only [List.map_cons, List.map_nil, List.mem_singleton] using hindex
    simpa only [List.mem_singleton] using (edge_index_mem_iff [d] (gm06UncutDart q)).mp hm
  have hmember : gm06UncutDart q ∈ x.linkage.flatten ∨
      gm06DartMate (gm06UncutDart q) ∈ x.linkage.flatten :=
    hwords.elim (fun h => Or.inl (h.symm ▸ hdflat)) (fun h => Or.inr (h.symm ▸ hdflat))
  have horigin : ∃ a : Fin x.vertexCount,
      x.endpoints[gm06UncutDart q]?.getD 0 = a.val ∧ a ∈ rep.live ∧
        rep.vertex a ∈ (L.pathDrawing i).V := by
    rcases hwords with h | h
    · simpa only [h, Bool.false_eq_true, ite_false] using rep.path_origin_mem i false hd
    · have he : gm06UncutDart q = gm06DartMate d := by
        rw [← h, gm06DartMate_involutive]
      simpa only [ite_true, ← he] using rep.path_origin_mem i true hd
  have htag : q / 2 % 2 = 0 := by
    by_contra hne
    have ht : q / 2 % 2 = 1 := by omega
    have hreb := gm06CutDart_rebuild q
    rw [ht] at hreb
    obtain ⟨a, ha, _, haP⟩ := horigin
    have hcopy := rep.cut_path_copy_origin hmember false
    simp only [Bool.not_false, Bool.toNat_true] at hcopy
    rw [hreb, ha] at hcopy
    have hactive := rep.cut_face_row_active hG (List.range x.vertexCount) i horbit q hq
    let u : Fin (2 * x.vertexCount) := ⟨(currentCut).origins[q]?.getD 0,
      (rep.cut_origins_valid q hactive).1⟩
    have hu : u.val = gm06CutVertex a.val false := hcopy
    have hpoint : rep.cutVertexPoint u = rep.vertex a := by
      apply congrArg rep.vertex
      apply Fin.ext
      change u.val / 2 = a.val
      rw [hu, gm06CutVertex_project]
    have hui := (incV_getD_ne_zero_iff _ _ _ u).mpr ⟨q, hq, rfl⟩
    have huP : rep.cutVertexPoint u ∈ (L.pathDrawing i).U :=
      hpoint.symm ▸ (L.pathDrawing i).V_subset_U haP
    rcases rep.selected_face_path_side hG i row horbit u hui i huP with h | h
    · have hodd : u.val % 2 = 1 := by simp [hu, gm06CutVertex, Nat.add_mod]
      omega
    · exact finSuccCycle_ne_of_one_lt hk i h.2.symm
  unfold gm06UncutDart at hindex
  omega

/-- On the listed left boundary path, the computed edge-incidence
bit is exactly geometric incidence with the region closure. -/
theorem computed_path_incE_iff (hn : 0 < x.vertexCount) (hk : 1 < k)
    (hG : IsCylinderSection5Drawing k G) (hno : ∀ (G₁ : Drawing ClosedCylinder) (L₁ : CylinderLinkage k G₁),
      IsCylinderSection5Drawing k G₁ → ¬ Section5Reduction2Step k G L G₁ L₁)
    (i : Fin k) (row : List ℕ)
    (horbit : ∀ q, q ∈ row ↔ ∃ n, cutNext^[n] (gap i) = q)
    (st : ℕ × Fin (2 * x.vertexCount))
    (hst : st ∈ gm06CutPathSteps x.vertexCount hn x.endpoints
      (x.linkage[i.val]'(by rw [rep.linkage.1]; exact i.isLt)) true) :
    (gm06IncE edgeCount row)[st.1]?.getD 0 ≠ 0 ↔
      rep.cutEdgePoint st.1 ⊆ closure (cylinderRegion k G i) := by
  rw [gm06CutPathSteps] at hst
  obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hst
  have hdflat : d ∈ x.linkage.flatten := List.mem_flatten.mpr ⟨_, List.getElem_mem _, hd⟩
  have hdb := rep.path_word_lt hdflat
  have hde : gm06CutDart d 0 / 2 = 2 * (d / 2) := by
    have hm := Nat.mod_lt d (by decide : 0 < 2)
    unfold gm06CutDart
    omega
  change (gm06IncE edgeCount row)[gm06CutDart d 0 / 2]?.getD 0 ≠ 0 ↔
    rep.cutEdgePoint (gm06CutDart d 0 / 2) ⊆ closure (cylinderRegion k G i)
  rw [hde]
  have hord := (cutOrdinaryFlags_get rep.tagged.length k (2 * (d / 2))).mpr (by omega)
  constructor
  · intro hinc
    obtain ⟨_, _, _, hsub, _⟩ := rep.selected_face_edge_data hk hG hno i row horbit _ hord hinc
    exact hsub
  · intro hsub
    let j : Fin rep.tagged.length := ⟨d / 2, by omega⟩
    obtain ⟨sf, hsf, hl⟩ := rep.ordinary_labels j (rep.path_word_active hdflat).2
    let a : DrawingDart (cylinderSphereDrawing rep.cuffed) := ⟨(sf.val, false), sf.property⟩
    have hcode : persistentDartLabel rep.label a = 2 * (d / 2) := by
      simp only [persistentDartLabel, a, hl, Bool.toNat_false, Nat.add_zero, j]
    have he : rep.cutEdgePoint (2 * (d / 2)) = rep.edge j := by
      simp only [cutEdgePoint, Nat.mul_div_cancel_left _ (by decide : 0 < 2),
        show d / 2 < rep.tagged.length by omega, dite_true]
      rfl
    have hsphere : a.val.1 ⊆ cylinderToSphere '' closure (cylinderRegion k G i) := by
      change sf.val ⊆ _
      rw [hsf, ← he]
      exact image_mono hsub
    have hinc := ((rep.region_incidence_cut_orbit hk hG hno i).2 a).mp hsphere
    have hword : ∃ q ∈ row, gm06UncutDart q / 2 = d / 2 := by
      rcases hinc with ⟨n, h⟩ | ⟨n, h⟩
      · refine ⟨cutNext^[n] (gap i), (horbit _).mpr ⟨n, rfl⟩, ?_⟩
        dsimp only [gm06CutDataOfLinkage]
        rw [h, hcode]
        omega
      · refine ⟨cutNext^[n] (gap i), (horbit _).mpr ⟨n, rfl⟩, ?_⟩
        dsimp only [gm06CutDataOfLinkage]
        rw [h, hcode]
        simp only [gm06DartMate, Nat.mul_mod_right, ite_true]
        omega
    obtain ⟨q, hq, hindex⟩ := hword
    apply (incE_getD_ne_zero_iff edgeCount row _).mpr
    exact ⟨by omega, q, hq, rep.selected_path_edge_left hk hG i row horbit hq hd hindex⟩

/-- The actual component query and computed boundary lists satisfy
all fields of FIND_4's drawing representation for at least two
linkage paths. No cut or incidence representation is assumed. -/
theorem component_find4_rep (hn : 0 < x.vertexCount) (hk : 1 < k)
    (hG : IsCylinderSection5Drawing k G) (hno : ∀ (G₁ : Drawing ClosedCylinder) (L₁ : CylinderLinkage k G₁),
      IsCylinderSection5Drawing k G₁ → ¬ Section5Reduction2Step k G L G₁ L₁)
    (i : Fin k) :
    ∃ root : Fin (2 * x.vertexCount),
      root.val = gm06CutInnerRoot currentCut rep.tagged.length i.val ∧
      ∃ row : List ℕ, gm06CutFaceIncidence (2 * x.vertexCount) edgeCount
        (gm06CutComponentData currentCut root) (4 * (rep.tagged.length + i.val) + 1) =
          some (row, gm06IncV (2 * x.vertexCount) (currentCut).origins row, gm06IncE edgeCount row) ∧
      Find4Rep L i (gm06CandidateEnds edgeCount (currentCut).origins)
        (gm06CutOrdinaryFlags rep.tagged.length k)
        (gm06IncV (2 * x.vertexCount) (currentCut).origins row) (gm06IncE edgeCount row)
        ((gm06CutPathLabels x.vertexCount hn x.endpoints
          (x.linkage[(finSuccCycle i).val]?.getD []) (x.innerCuff[(finSuccCycle i).val]?.getD 0)
          false).map Fin.val)
        (gm06CutVertexFin x.vertexCount hn (x.innerCuff[i.val]?.getD 0) true)
        (gm06CutPathSteps x.vertexCount hn x.endpoints (x.linkage[i.val]?.getD []) true)
        rep.cutVertexPoint rep.cutEdgePoint := by
  obtain ⟨root, hroot, row, hout, horbit⟩ := rep.component_cut_face_row hG i
  have hcode : (gap i) = 4 * (rep.tagged.length + i.val) + 1 := by
    simp [gm06CutDart, Nat.add_div, Nat.add_mod]
  have horbit' : ∀ q, q ∈ row ↔ ∃ n, cutNext^[n] (gap i) = q := by
    simpa only [hcode] using horbit
  have hpath (j : Fin k) : x.linkage[j.val]?.getD [] =
      x.linkage[j.val]'(by rw [rep.linkage.1]; exact j.isLt) := by
    rw [List.getElem?_eq_getElem (show j.val < x.linkage.length by rw [rep.linkage.1]; exact j.isLt)]
    rfl
  have hsource (j : Fin k) : x.innerCuff[j.val]?.getD 0 = (rep.source j).val := by
    rw [rep.inner]
    simp only [List.getElem?_ofFn, j.isLt, dite_true, Option.getD_some]
  refine ⟨root, hroot, row, hout, ?_⟩
  rw [hpath i, hpath (finSuccCycle i), hsource i, hsource (finSuccCycle i)]
  refine {
    vertex_sound := rep.selected_face_vertex_sound hk hG hno i row horbit'
    vertex_cover := rep.selected_face_vertex_cover hk hG hno i row horbit'
    inj := rep.selected_face_path_union_inj hn hk hG i row horbit'
    upper_iff := ?_
    edge_sound := ?_
    edge_cover := ?_
    path_walk := rep.computed_path_walk hn i true
    path_incV := rep.computed_path_incV_iff hn hk hG hno i row horbit'
    path_incE := rep.computed_path_incE_iff hn hk hG hno i row horbit' }
  · intro u hu
    have hmem : u.val ∈ (gm06CutPathLabels x.vertexCount hn x.endpoints
        (x.linkage[(finSuccCycle i).val]'(by rw [rep.linkage.1]; exact (finSuccCycle i).isLt))
        (rep.source (finSuccCycle i)).val false).map Fin.val ↔
        u ∈ gm06CutPathLabels x.vertexCount hn x.endpoints
          (x.linkage[(finSuccCycle i).val]'(by rw [rep.linkage.1]; exact (finSuccCycle i).isLt))
          (rep.source (finSuccCycle i)).val false := by
      constructor
      · intro h
        obtain ⟨v, hv, he⟩ := List.mem_map.mp h
        exact Fin.ext he ▸ hv
      · intro h
        exact List.mem_map.mpr ⟨u, h, rfl⟩
    exact hmem.trans (rep.selected_face_upper_iff hn hk hG i row horbit' u hu)
  · intro e hord hinc
    obtain ⟨u, w, he, hsub, hlink, _, _⟩ :=
      rep.selected_face_edge_data hk hG hno i row horbit' e hord hinc
    exact ⟨u, w, he, hsub, hlink⟩
  · intro f a b hf _ hsub
    exact rep.selected_face_edge_cover hk hG hno i row horbit' f a b hf hsub

end GM06CurrentDrawingRep
end GraphMinor.GM06
