module

public import GraphMinor.GM06.Alg57CurrentPathIncidence
public import GraphMinor.GM06.Alg57CurrentCutEdgeEnds
public import GraphMinor.Compute.GM06CandidateEdges
import GraphMinor.Compute.GM06FaceRowsProgram

/-!
# Ordinary edge incidence in the actual selected cut face

Equation (10) in the proof of VI (5.7), page 133, marks an edge
when either directed end occurs in the selected row. An ordinary
marked edge is the actual current edge at its permanent label.
Both endpoints are incident: the next face end starts at the
previous end's head. These finite facts and the proved geometric
orbit interpretation supply the edge fields used by FIND_4.
-/

public section
namespace GraphMinor.GM06
open Set GraphMinor.Surface GraphMinor.GM11 GraphMinor.Compute

/-- Mark the copied slots of original ordinary edges, excluding
both families of auxiliary cuff edges. -/
@[expose] def gm06CutOrdinaryFlags (m k : ℕ) : List Bool :=
  List.ofFn (fun e : Fin (2 * (m + (k + k))) => decide (e.val / 2 < m))

/-- The ordinary-edge flag reads exactly the original label range. -/
theorem cutOrdinaryFlags_get (m k e : ℕ) :
    (gm06CutOrdinaryFlags m k)[e]?.getD false = true ↔ e / 2 < m := by
  by_cases he : e < 2 * (m + (k + k))
  · simp only [gm06CutOrdinaryFlags, List.getElem?_ofFn, he, dite_true,
      Option.getD_some, decide_eq_true_eq]
  · have hn : ¬ e / 2 < m := by omega
    simp only [gm06CutOrdinaryFlags, List.getElem?_ofFn, he, dite_false,
      Option.getD_none, Bool.false_eq_true, hn]

/-- A nonzero edge-incidence bit records one of the selected row's
permanent edge labels, within the supplied label space. -/
theorem incE_getD_ne_zero_iff (m : ℕ) (row : List ℕ) (e : ℕ) :
    (gm06IncE m row)[e]?.getD 0 ≠ 0 ↔ e < m ∧ ∃ d ∈ row, d / 2 = e := by
  by_cases he : e < m
  · simp only [gm06IncE, gm06IncidenceBits, List.getElem?_ofFn, he, dite_true,
      Option.getD_some, true_and, gm06FaceEdges, List.mem_map]
    split_ifs with h
    · simpa only [ne_eq, one_ne_zero, not_false_eq_true, true_iff] using h
    · simp only [ne_eq, not_true_eq_false, false_iff]; exact h
  · simp only [gm06IncE, gm06IncidenceBits, List.getElem?_ofFn, he, dite_false,
      Option.getD_none, ne_eq, not_true_eq_false, false_and]

/-- A numeric face successor starts at the head of its previous end. -/
theorem numeric_face_head_origin (data : GM06CutData) (hn : data.rotations.flatten.Nodup)
    (hsame : ∀ row ∈ data.rotations, ∀ a ∈ row, ∀ b ∈ row,
      data.origins[a]?.getD 0 = data.origins[b]?.getD 0)
    {q : ℕ} (hm : gm06DartMate q ∈ data.rotations.flatten) :
    data.origins[(dartMatePerm.trans (gm06RotationPermutation data.rotations).symm) q]?.getD 0 =
      data.origins[gm06DartMate q]?.getD 0 := by
  obtain ⟨row, hr, hm⟩ := List.mem_flatten.mp hm
  have hp : row.formPerm.symm (gm06DartMate q) ∈ row := by
    have hh := List.formPerm_apply_mem_of_mem (l := row.reverse) (x := gm06DartMate q)
      (List.mem_reverse.mpr hm)
    simpa only [List.formPerm_reverse, List.mem_reverse, Equiv.Perm.coe_inv] using hh
  simp only [Equiv.trans_apply, dartMatePerm_apply,
    rotationPermutation_symm_apply_row _ hn row hr _ hm]
  exact hsame row hr _ hp _ hm

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

/-- The head of every selected face end also has its vertex
incidence bit set, because the next face end has that origin. -/
theorem selected_face_head_inc (hG : IsCylinderSection5Drawing k G)
    (i : Fin k) (row : List ℕ)
    (horbit : ∀ q, q ∈ row ↔ ∃ n, cutNext^[n] (gap i) = q)
    {q : ℕ} (hq : q ∈ row) (w : Fin (2 * x.vertexCount))
    (hw : (currentCut).origins[gm06DartMate q]?.getD 0 = w.val) :
    (gm06IncV (2 * x.vertexCount) (currentCut).origins row)[w.val]?.getD 0 ≠ 0 := by
  obtain ⟨hn, _, _, hc, hm⟩ := rep.cut_data_face_encoding hG (List.range x.vertexCount)
  have hactive := rep.cut_face_row_active hG (List.range x.vertexCount) i horbit q hq
  have hhead := numeric_face_head_origin currentCut hn (rep.cut_row_origins_eq hG _)
    ((hc _).mp (hm _ hactive))
  apply (incV_getD_ne_zero_iff _ _ _ w).mpr
  refine ⟨cutNext q, ?_, hhead.trans hw⟩
  obtain ⟨n, hn⟩ := (horbit q).mp hq
  apply (horbit _).mpr
  exact ⟨n + 1, by rw [Function.iterate_succ_apply', hn]⟩

/-- The sphere edge at the permanent projection of an ordinary
copied end is the image of its actual geometric edge. -/
theorem cut_ordinary_sphere_edge (hG : IsCylinderSection5Drawing k G) {q : ℕ}
    (hq : q ∈ (currentCut).activeDarts) (hd : gm06UncutDart q < 2 * rep.tagged.length) :
    ∃ d : DrawingDart (cylinderSphereDrawing rep.cuffed),
      persistentDartLabel rep.label d = gm06UncutDart q ∧
        d.val.1 = cylinderToSphere '' rep.cutEdgePoint (q / 2) := by
  obtain ⟨a, _, _, d, _, hl⟩ := rep.cut_origin_point (List.range x.vertexCount) hq
  let f : (cylinderSphereDrawing rep.cuffed).E := ⟨d.val.1, d.property⟩
  have hcode : 2 * rep.label f + d.val.2.toNat = gm06UncutDart q := hl
  have hb : d.val.2.toNat ≤ 1 := by cases d.val.2 <;> decide
  have hlabel : rep.label f < rep.tagged.length := by omega
  obtain ⟨j, _, hf, hj⟩ := rep.ordinary_of_label_lt hG f hlabel
  have hindex : q / 2 / 2 = j.val := by
    rw [hj] at hcode
    unfold gm06UncutDart at hcode
    omega
  have he : rep.cutEdgePoint (q / 2) = rep.edge j := by
    simp only [cutEdgePoint, hindex, j.isLt, dite_true, Fin.eta]
  exact ⟨d, hl, hf.trans (congrArg (image cylinderToSphere) he.symm)⟩

/-- Every selected ordinary edge lies in the closure of its
prescribed cylinder region. -/
theorem selected_face_edge_subset (hk : 1 < k) (hG : IsCylinderSection5Drawing k G)
    (hno : ∀ (G₁ : Drawing ClosedCylinder) (L₁ : CylinderLinkage k G₁),
      IsCylinderSection5Drawing k G₁ → ¬ Section5Reduction2Step k G L G₁ L₁) (i : Fin k) (row : List ℕ)
    (horbit : ∀ q, q ∈ row ↔ ∃ n, cutNext^[n] (gap i) = q)
    {q : ℕ} (hq : q ∈ row) (hd : gm06UncutDart q < 2 * rep.tagged.length) :
    rep.cutEdgePoint (q / 2) ⊆ closure (cylinderRegion k G i) := by
  have hactive := rep.cut_face_row_active hG (List.range x.vertexCount) i horbit q hq
  obtain ⟨d, hl, hedge⟩ := rep.cut_ordinary_sphere_edge hG hactive hd
  have hsphere : d.val.1 ⊆ cylinderToSphere '' closure (cylinderRegion k G i) := by
    apply ((rep.region_incidence_cut_orbit hk hG hno i).2 d).mpr
    obtain ⟨n, hn⟩ := (horbit q).mp hq
    exact Or.inl ⟨n, (congrArg gm06UncutDart hn).trans hl.symm⟩
  rw [hedge] at hsphere
  intro p hp
  obtain ⟨v, hv, hvp⟩ := hsphere (mem_image_of_mem cylinderToSphere hp)
  exact injective_cylinderToSphere hvp ▸ hv

/-- An ordinary incident edge label has its actual endpoint pair,
its geometric link, and both endpoint incidence bits. -/
theorem selected_face_edge_data (hk : 1 < k) (hG : IsCylinderSection5Drawing k G)
    (hno : ∀ (G₁ : Drawing ClosedCylinder) (L₁ : CylinderLinkage k G₁),
      IsCylinderSection5Drawing k G₁ → ¬ Section5Reduction2Step k G L G₁ L₁) (i : Fin k) (row : List ℕ)
    (horbit : ∀ q, q ∈ row ↔ ∃ n, cutNext^[n] (gap i) = q)
    (e : ℕ) (hord : (gm06CutOrdinaryFlags rep.tagged.length k)[e]?.getD false = true)
    (hinc : (gm06IncE edgeCount row)[e]?.getD 0 ≠ 0) :
    ∃ u w : Fin (2 * x.vertexCount),
      (gm06CandidateEnds edgeCount (currentCut).origins)[e]?.getD (0, 0) = (u.val, w.val) ∧
      rep.cutEdgePoint e ⊆ closure (cylinderRegion k G i) ∧
      G.toGraph.IsLink (rep.cutEdgePoint e) (rep.cutVertexPoint u) (rep.cutVertexPoint w) ∧
      (gm06IncV (2 * x.vertexCount) (currentCut).origins row)[u.val]?.getD 0 ≠ 0 ∧
      (gm06IncV (2 * x.vertexCount) (currentCut).origins row)[w.val]?.getD 0 ≠ 0 := by
  obtain ⟨he, q, hq, hqe⟩ := (incE_getD_ne_zero_iff _ _ e).mp hinc
  have heord := (cutOrdinaryFlags_get _ _ e).mp hord
  have hd : gm06UncutDart q < 2 * rep.tagged.length := by
    unfold gm06UncutDart
    omega
  have hactive := rep.cut_face_row_active hG (List.range x.vertexCount) i horbit q hq
  obtain ⟨u, w, hu, hw, hlink⟩ := rep.cut_ordinary_isLink hG hactive hd
  have hsub := rep.selected_face_edge_subset hk hG hno i row horbit hq hd
  have hui := (incV_getD_ne_zero_iff _ _ _ u).mpr ⟨q, hq, hu⟩
  have hwi := rep.selected_face_head_inc hG i row horbit hq w hw
  rw [hqe] at hlink hsub
  have hend := gm06DartMate_end_cases q
  rcases hend with ⟨hpos, hneg⟩ | ⟨hneg, hpos⟩
  · refine ⟨u, w, ?_, hsub, hlink, hui, hwi⟩
    rw [gm06CandidateEnds_get _ he]
    apply Prod.ext
    · rw [← hqe, ← hpos]; exact hu
    · rw [← hqe, ← hneg]; exact hw
  · refine ⟨w, u, ?_, hsub, hlink.symm, hwi, hui⟩
    rw [gm06CandidateEnds_get _ he]
    apply Prod.ext
    · rw [← hqe, ← hpos]; exact hw
    · rw [← hqe, ← hneg]; exact hu

/-- Every actual ordinary edge in the region closure has an
incident copied label, with incident endpoint labels representing
its prescribed endpoints in one of the two orders. -/
theorem selected_face_edge_cover (hk : 1 < k) (hG : IsCylinderSection5Drawing k G)
    (hno : ∀ (G₁ : Drawing ClosedCylinder) (L₁ : CylinderLinkage k G₁),
      IsCylinderSection5Drawing k G₁ → ¬ Section5Reduction2Step k G L G₁ L₁) (i : Fin k) (row : List ℕ)
    (horbit : ∀ q, q ∈ row ↔ ∃ n, cutNext^[n] (gap i) = q)
    (f : Set ClosedCylinder) (a b : ClosedCylinder) (hf : G.toGraph.IsLink f a b)
    (hfR : f ⊆ closure (cylinderRegion k G i)) :
    ∃ e < (gm06CandidateEnds edgeCount (currentCut).origins).length,
      (gm06CutOrdinaryFlags rep.tagged.length k)[e]?.getD false = true ∧
      (gm06IncE edgeCount row)[e]?.getD 0 ≠ 0 ∧ rep.cutEdgePoint e = f ∧
      ∃ u w : Fin (2 * x.vertexCount),
        (gm06CandidateEnds edgeCount (currentCut).origins)[e]?.getD (0, 0) = (u.val, w.val) ∧
        (gm06IncV (2 * x.vertexCount) (currentCut).origins row)[u.val]?.getD 0 ≠ 0 ∧
        (gm06IncV (2 * x.vertexCount) (currentCut).origins row)[w.val]?.getD 0 ≠ 0 ∧
        ((rep.cutVertexPoint u = a ∧ rep.cutVertexPoint w = b) ∨
          (rep.cutVertexPoint u = b ∧ rep.cutVertexPoint w = a)) := by
  obtain ⟨j, hj, hjf⟩ := rep.edge_cover f hf.1
  obtain ⟨sf, hsf, hlabel⟩ := rep.ordinary_labels j hj
  let d : DrawingDart (cylinderSphereDrawing rep.cuffed) := ⟨(sf.val, false), sf.property⟩
  have hcode : persistentDartLabel rep.label d = 2 * j.val := by
    simp only [persistentDartLabel, d, hlabel, Bool.toNat_false, Nat.add_zero]
  have hsub : d.val.1 ⊆ cylinderToSphere '' closure (cylinderRegion k G i) := by
    change sf.val ⊆ _
    rw [hsf, hjf]
    exact image_mono hfR
  have hinc := ((rep.region_incidence_cut_orbit hk hG hno i).2 d).mp hsub
  have hword : ∃ q ∈ row, gm06UncutDart q / 2 = j.val := by
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
  obtain ⟨q, hq, hqj⟩ := hword
  let e := q / 2
  have hindex : e / 2 = j.val := by
    dsimp only [e]
    unfold gm06UncutDart at hqj
    omega
  have hactive := rep.cut_face_row_active hG (List.range x.vertexCount) i horbit q hq
  have hbound := (gm06CutDataOfLinkage_active_iff _ _ _ _ _ _ _ _ _).mp hactive
  have he : e < edgeCount := by
    rw [rep.cuff_lengths.1, rep.cuff_lengths.2] at hbound
    dsimp only [e]
    omega
  have hord := (cutOrdinaryFlags_get rep.tagged.length k e).mpr
    (show e / 2 < rep.tagged.length by rw [hindex]; exact j.isLt)
  have hei := (incE_getD_ne_zero_iff edgeCount row e).mpr ⟨he, q, hq, rfl⟩
  have hef : rep.cutEdgePoint e = f := by
    simp only [cutEdgePoint, hindex, j.isLt, dite_true, Fin.eta]
    exact hjf
  obtain ⟨u, w, hends, _, hlink, hui, hwi⟩ :=
    rep.selected_face_edge_data hk hG hno i row horbit e hord hei
  rw [hef] at hlink
  refine ⟨e, by simpa only [gm06CandidateEnds_length] using he, hord, hei, hef,
    u, w, hends, hui, hwi, ?_⟩
  exact pair_eq_pair_iff.mp (hlink.2.2.2.symm.trans hf.2.2.2)

end GM06CurrentDrawingRep
end GraphMinor.GM06
