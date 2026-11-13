module

public import GraphMinor.GM06.Alg57OnePathCutRows
public import GraphMinor.GM06.Alg57CurrentPathIncidence
public import GraphMinor.GM06.Alg57CurrentEdgeIncidence
import GraphMinor.GM06.Alg57CutCopiedSlots
import GraphMinor.GM06.Alg57CutOriginProjection

/-!
# The vertex slots of FIND_4 for one path

For one path the face that FIND_4 searches is the cut face orbit of `c̄₁`, and a vertex slot `u`
names the point `cutLab u` of the cut disc. Here we show that the vertex incidence bit of `u` is
set exactly when `cutLab u` is in `cutRc` and `u` is not the empty right copy of a vertex off
`P₁` (`incV_iff_label`). From this we get the vertex fields of `Find4Rep1`: soundness, cover,
injectivity, the test for the right copy of `P₁`, and the incidence of the left copy of `P₁`.
-/

@[expose] public section

namespace GraphMinor.GM06

open Set Topology GraphMinor.Surface GraphMinor.GM11 GraphMinor.Compute unitInterval

variable {G : Drawing ClosedCylinder} {θ : ℝ} {D : Set (ℝ × ℝ)}

namespace GM06CurrentDrawingRep

variable {x : GM06SuccessorInput} {L : CylinderLinkage 1 G} (rep : GM06CurrentDrawingRep x G L)

local notation "cutTables" => gm06BuildCutTables x.vertexCount rep.tagged.length x.endpoints
  x.linkage x.innerCuff x.outerCuff
local notation "splitRows" => gm06SplitRotationRows cutTables x.rotations
local notation "cutNext" => Equiv.trans dartMatePerm
  (Equiv.symm (gm06RotationPermutation (gm06SplitRotationRows cutTables x.rotations)))
local notation "gapCut" => gm06CutDart (2 * rep.tagged.length + 1) 0
local notation "currentCut" => gm06CutDataOfLinkage x.vertexCount rep.tagged.length x.endpoints
  x.linkage x.innerCuff x.outerCuff x.rotations (List.range x.vertexCount)

/-- A vertex off `P₁` is not split. -/
theorem off_position_none (a : Fin x.vertexCount) (haP : rep.vertex a ∉ (L.pathDrawing 0).U) :
    gm06CutPositionAt cutTables a.val = none := by
  rcases h : gm06CutPositionAt cutTables a.val with _ | p
  · rfl
  · exfalso
    obtain ⟨j, hj⟩ := rep.exists_path_of_cut_position a p h
    rw [Subsingleton.elim j 0] at hj
    exact haP ((L.pathDrawing 0).V_subset_U hj)

/-- The right copy of a vertex off `P₁` has an empty row. -/
theorem off_right_row_nil (a : Fin x.vertexCount) (haP : rep.vertex a ∉ (L.pathDrawing 0).U) :
    (splitRows).getD (gm06CutVertex a.val false) [] = [] := by
  have hlt : a.val < x.rotations.length := by rw [rep.rows_length]; exact a.isLt
  rw [splitRows_getD _ _ _ hlt false, rep.off_position_none a haP]
  simp [gm06CutSelectedRow, gm06CutRetain]

variable (hG : IsCylinderSection5Drawing 1 G)
  (hno : ∀ (G₁ : Drawing ClosedCylinder) (L₁ : CylinderLinkage 1 G₁),
    IsCylinderSection5Drawing 1 G₁ → ¬ Section5Reduction2Step 1 G L G₁ L₁) (hθ : L.HasTheta θ)
  (hD : IsClosedDisc D) (hBd : discBd D = liftedStripBoundary hG.1 L 1)
  (hstrip : D ⊆ {p : ℝ × ℝ | 1 ≤ p.1 ∧ p.1 ≤ 2})

include hno hθ hD hstrip in
/-- **The incidence of a vertex slot.** Let `u` be a slot over a live vertex. The cut face orbit
of `c̄₁` meets the row of `u` exactly when `cutLab u` is in `cutRc` and `u` is not the right copy
of a vertex off `P₁`. Over `P₁` this is `path_slot_incident_iff`. Off `P₁` the left copy is
`one_path_off_vertex_iff_red2`, and the right copy has an empty row. -/
theorem slot_incident_iff (u : Fin (2 * x.vertexCount))
    (ha : (⟨u.val / 2, by have := u.isLt; omega⟩ : Fin x.vertexCount) ∈ rep.live) :
    (∃ n, cutNext^[n] gapCut ∈ (splitRows).getD u.val []) ↔
      rep.cutLab hG hBd u ∈ cutRc G D ∧
        (rep.cutVertexPoint u ∈ (L.pathDrawing 0).U ∨ u.val % 2 = 0) := by
  set a : Fin x.vertexCount := ⟨u.val / 2, by have := u.isLt; omega⟩ with ha_def
  have hu : gm06CutVertex a.val (decide (u.val % 2 = 0)) = u.val := by
    simp only [gm06CutVertex, ha_def]
    by_cases h : u.val % 2 = 0 <;> simp [h] <;> omega
  have hrow : (splitRows).getD u.val [] =
      (splitRows).getD (gm06CutVertex a.val (decide (u.val % 2 = 0))) [] := by rw [hu]
  have hpt : rep.cutVertexPoint u = rep.vertex a := rfl
  rw [hrow]
  by_cases hP : rep.vertex a ∈ (L.pathDrawing 0).U
  · have hP' := hP
    rw [← (L.curve_parametrizes 0).2.1] at hP'
    obtain ⟨t, ht⟩ := hP'
    rw [rep.path_slot_incident_iff hG hno hθ hD hBd hstrip a ha ht.symm,
      rep.cutLab_curve hG hθ hD hBd hstrip u (hpt.trans ht.symm)]
    simp only [hpt, hP, true_or, and_true]
  · by_cases hev : u.val % 2 = 0
    · have hproj : cutProj D (rep.cutLab hG hBd u) = rep.vertex a := by
        unfold cutLab
        rw [cutProj_cutPointLabel L hG hθ hD hBd hstrip]
        rfl
      simp only [hev, decide_true, or_true, and_true]
      rw [← rep.one_path_off_vertex_iff_red2 hG hno hθ hD hBd hstrip a ha hP hproj]
    · have hnil := rep.off_right_row_nil a hP
      simp only [hev, decide_false, hnil, List.not_mem_nil, exists_false, false_iff, not_and,
        hpt, hP, or_self, not_false_eq_true, implies_true]

include hG in
/-- The vertex incidence bit of the cut face orbit of `c̄₁` reads the rows of the slots that the
orbit meets. -/
theorem incV_iff_orbit (row : List ℕ) (horbit : ∀ q, q ∈ row ↔ ∃ n, cutNext^[n] gapCut = q)
    (u : Fin (2 * x.vertexCount)) :
    (gm06IncV (2 * x.vertexCount) (currentCut).origins row)[u.val]?.getD 0 ≠ 0 ↔
      ∃ n, cutNext^[n] gapCut ∈ (splitRows).getD u.val [] := by
  rw [incV_getD_ne_zero_iff]
  constructor
  · rintro ⟨q, hq, hqu⟩
    have hact := rep.cut_face_row_active hG (List.range x.vertexCount) 0 horbit q hq
    have h := rep.cut_active_origin_row hact
    rw [hqu] at h
    obtain ⟨n, rfl⟩ := (horbit q).mp hq
    exact ⟨n, h⟩
  · rintro ⟨n, hn⟩
    exact ⟨_, (horbit _).mpr ⟨n, rfl⟩, rep.origin_eq_of_mem hG u.isLt hn⟩

include hno hθ hD hstrip in
/-- **The vertex incidence bit of a slot.** For a slot over a live vertex, the bit is set exactly
when `cutLab u` is in `cutRc` and `u` is not the right copy of a vertex off `P₁`. -/
theorem incV_iff_label (row : List ℕ) (horbit : ∀ q, q ∈ row ↔ ∃ n, cutNext^[n] gapCut = q)
    (u : Fin (2 * x.vertexCount))
    (ha : (⟨u.val / 2, by have := u.isLt; omega⟩ : Fin x.vertexCount) ∈ rep.live) :
    (gm06IncV (2 * x.vertexCount) (currentCut).origins row)[u.val]?.getD 0 ≠ 0 ↔
      rep.cutLab hG hBd u ∈ cutRc G D ∧
        (rep.cutVertexPoint u ∈ (L.pathDrawing 0).U ∨ u.val % 2 = 0) := by
  rw [rep.incV_iff_orbit hG row horbit u, rep.slot_incident_iff hG hno hθ hD hBd hstrip u ha]

/-- The two lifts of `P₁` do not meet, so a point on both names one side. -/
theorem cutSidePoint_side_eq {left left' : Bool} {t t' : I}
    (h : cutSidePoint L hG hBd left t = cutSidePoint L hG hBd left' t') : left = left' := by
  by_contra hne
  have hmem := cutSidePoint_mem_side L hG hBd left' t'
  rw [← h] at hmem
  apply cutSidePoint_notMem_other L hG hBd left t
  cases left <;> cases left' <;> simp_all

include hθ hD hstrip in
/-- The label of a slot lies over the vertex of the slot. -/
theorem cutProj_cutLab (u : Fin (2 * x.vertexCount)) :
    cutProj D (rep.cutLab hG hBd u) = rep.cutVertexPoint u := by
  unfold cutLab
  exact cutProj_cutPointLabel L hG hθ hD hBd hstrip _ _ _

include hθ hD hstrip in
/-- The label of a slot is on a lift exactly when its vertex is on `P₁` and the parity of the slot
is the side of the lift. -/
theorem cutLab_mem_side_iff (u : Fin (2 * x.vertexCount)) (left : Bool) :
    rep.cutLab hG hBd u ∈ cutSideSet L hG D (if left then 1 else 2) ↔
      rep.cutVertexPoint u ∈ (L.pathDrawing 0).U ∧ decide (u.val % 2 = 0) = left := by
  constructor
  · intro h
    have hP := cutProj_mem_path_of_mem_side L hG h
    rw [rep.cutProj_cutLab hG hθ hD hBd hstrip] at hP
    refine ⟨hP, ?_⟩
    have hP' := hP
    rw [← (L.curve_parametrizes 0).2.1] at hP'
    obtain ⟨t, ht⟩ := hP'
    rw [rep.cutLab_curve hG hθ hD hBd hstrip u ht.symm] at h
    by_contra hne
    apply cutSidePoint_notMem_other L hG hBd (decide (u.val % 2 = 0)) t
    revert h hne
    cases decide (u.val % 2 = 0) <;> cases left <;> simp
  · rintro ⟨hP, hl⟩
    rw [← (L.curve_parametrizes 0).2.1] at hP
    obtain ⟨t, ht⟩ := hP
    rw [rep.cutLab_curve hG hθ hD hBd hstrip u ht.symm, hl]
    exact cutSidePoint_mem_side L hG hBd left t

include hθ hD hstrip in
/-- Every point of the cut disc over a vertex `a` is the label of a copy of `a`, the left copy when
`a` is off `P₁`. -/
theorem exists_slot_of_proj (a : Fin x.vertexCount) {z : D} (hz : cutProj D z = rep.vertex a) :
    ∃ left : Bool, rep.cutLab hG hBd
      ⟨gm06CutVertex a.val left, by
        have := a.isLt; cases left <;> simp [gm06CutVertex] <;> omega⟩ = z ∧
      (rep.vertex a ∈ (L.pathDrawing 0).U ∨ left = true) := by
  have hpar (left : Bool) : decide (gm06CutVertex a.val left % 2 = 0) = left := by
    cases left <;> simp [gm06CutVertex, Nat.add_mod]
  have hpt (left : Bool) : rep.cutVertexPoint
      ⟨gm06CutVertex a.val left, by
        have := a.isLt; cases left <;> simp [gm06CutVertex] <;> omega⟩ = rep.vertex a := by
    apply congrArg rep.vertex
    apply Fin.ext
    exact gm06CutVertex_project a.val left
  by_cases hP : rep.vertex a ∈ (L.pathDrawing 0).U
  · have hP' := hP
    rw [← (L.curve_parametrizes 0).2.1] at hP'
    obtain ⟨t, ht⟩ := hP'
    have hzt : cutProj D z = L.curve 0 t := hz.trans ht.symm
    by_cases h2 : z ∈ cutSideSet L hG D 2
    · refine ⟨false, ?_, Or.inl hP⟩
      rw [rep.cutLab_curve hG hθ hD hBd hstrip _ ((hpt false).trans ht.symm), hpar false]
      exact (eq_cutSidePoint_of_proj L hG hθ hD hBd hstrip false hzt
        (notMem_other_of_mem_side L hG false h2)).symm
    · refine ⟨true, ?_, Or.inl hP⟩
      rw [rep.cutLab_curve hG hθ hD hBd hstrip _ ((hpt true).trans ht.symm), hpar true]
      exact (eq_cutSidePoint_of_proj L hG hθ hD hBd hstrip true hzt h2).symm
  · refine ⟨true, ?_, Or.inr rfl⟩
    exact rep.cutLab_off hG hθ hD hBd hstrip _ (by rw [hpt]; exact hP) (hz.trans (hpt true).symm)

/-- A slot whose half is a live vertex `a` is over a live vertex. -/
theorem live_of_half (u : Fin (2 * x.vertexCount)) {a : Fin x.vertexCount} (h : u.val / 2 = a.val)
    (ha : a ∈ rep.live) :
    (⟨u.val / 2, by have := u.isLt; omega⟩ : Fin x.vertexCount) ∈ rep.live := by
  have he : (⟨u.val / 2, by have := u.isLt; omega⟩ : Fin x.vertexCount) = a := Fin.ext h
  rw [he]
  exact ha

section Fields

variable (hn : 0 < x.vertexCount)


include hno hθ hD hstrip in
/-- **Soundness of the vertex bits.** An incident slot names a vertex of `F` in `cutRc`. -/
theorem slots_vertex_sound (row : List ℕ)
    (horbit : ∀ q, q ∈ row ↔ ∃ n, cutNext^[n] gapCut = q) (F : Drawing D)
    (hFV : F.V = (fun p : D => radialCylinderProjection p.1) ⁻¹' G.V) (u : Fin (2 * x.vertexCount))
    (hu : (gm06IncV (2 * x.vertexCount) (currentCut).origins row)[u.val]?.getD 0 ≠ 0) :
    rep.cutLab hG hBd u ∈ F.V ∧ rep.cutLab hG hBd u ∈ cutRc G D := by
  have hlive := rep.selected_face_vertex_live hG 0 row horbit u hu
  refine ⟨?_, ((rep.incV_iff_label hG hno hθ hD hBd hstrip row horbit u hlive).mp hu).1⟩
  rw [hFV]
  change cutProj D (rep.cutLab hG hBd u) ∈ G.V
  rw [rep.cutProj_cutLab hG hθ hD hBd hstrip]
  exact (rep.selected_face_vertex_dart hG 0 row horbit u hu).1

include hno hθ hD hstrip in
/-- **Cover by the vertex bits.** Every vertex of `F` in `cutRc` is the label of an incident
slot. -/
theorem slots_vertex_cover (row : List ℕ)
    (horbit : ∀ q, q ∈ row ↔ ∃ n, cutNext^[n] gapCut = q) (F : Drawing D)
    (hFV : F.V = (fun p : D => radialCylinderProjection p.1) ⁻¹' G.V) (z : D) (hzV : z ∈ F.V)
    (hzR : z ∈ cutRc G D) :
    ∃ u : Fin (2 * x.vertexCount), (gm06IncV (2 * x.vertexCount) (currentCut).origins row)[u.val]?.getD 0 ≠ 0 ∧ rep.cutLab hG hBd u = z := by
  have hzG : cutProj D z ∈ G.V := by rw [hFV] at hzV; exact hzV
  obtain ⟨a, ha, haz⟩ := rep.vertex_cover _ hzG
  obtain ⟨left, hlab, hside⟩ := rep.exists_slot_of_proj hG hθ hD hBd hstrip a haz.symm
  refine ⟨_, ?_, hlab⟩
  have hhalf := gm06CutVertex_project a.val left
  apply (rep.incV_iff_label hG hno hθ hD hBd hstrip row horbit _
    (rep.live_of_half _ hhalf ha)).mpr
  refine ⟨hlab ▸ hzR, ?_⟩
  rcases hside with h | h
  · left
    have hpt : rep.cutVertexPoint ⟨gm06CutVertex a.val left, by
        have := a.isLt; cases left <;> simp [gm06CutVertex] <;> omega⟩ = rep.vertex a :=
      congrArg rep.vertex (Fin.ext hhalf)
    rw [hpt]
    exact h
  · right
    subst h
    simp [gm06CutVertex]

include hno hθ hD hstrip in
/-- **Injectivity of the labels.** Two slots that are incident or on the left copy of `P₁` and
have the same label are equal. -/
theorem slots_inj (row : List ℕ)
    (horbit : ∀ q, q ∈ row ↔ ∃ n, cutNext^[n] gapCut = q) (u w : Fin (2 * x.vertexCount))
    (hu : (gm06IncV (2 * x.vertexCount) (currentCut).origins row)[u.val]?.getD 0 ≠ 0 ∨ u ∈ gm06CutPathLabels x.vertexCount hn x.endpoints
      (x.linkage[0]'(by rw [rep.linkage.1]; exact one_pos)) (rep.source 0).val true)
    (hw : (gm06IncV (2 * x.vertexCount) (currentCut).origins row)[w.val]?.getD 0 ≠ 0 ∨ w ∈ gm06CutPathLabels x.vertexCount hn x.endpoints
      (x.linkage[0]'(by rw [rep.linkage.1]; exact one_pos)) (rep.source 0).val true)
    (heq : rep.cutLab hG hBd u = rep.cutLab hG hBd w) : u = w := by
  have hfacts : ∀ v : Fin (2 * x.vertexCount), ((gm06IncV (2 * x.vertexCount) (currentCut).origins row)[v.val]?.getD 0 ≠ 0 ∨ v ∈ gm06CutPathLabels x.vertexCount hn x.endpoints
      (x.linkage[0]'(by rw [rep.linkage.1]; exact one_pos)) (rep.source 0).val true) →
      (⟨v.val / 2, by have := v.isLt; omega⟩ : Fin x.vertexCount) ∈ rep.live ∧
        (rep.cutVertexPoint v ∈ (L.pathDrawing 0).U ∨ v.val % 2 = 0) := by
    rintro v (hv | hv)
    · have hl := rep.selected_face_vertex_live hG 0 row horbit v hv
      exact ⟨hl, ((rep.incV_iff_label hG hno hθ hD hBd hstrip row horbit v hl).mp hv).2⟩
    · have hl := rep.computed_path_labels_live hn 0 true hv
      exact ⟨hl, Or.inr (by simpa using cutPathLabels_mod _ hn _ _ _ true hv)⟩
  obtain ⟨hul, hup⟩ := hfacts u hu
  obtain ⟨hwl, hwp⟩ := hfacts w hw
  have hpt : rep.cutVertexPoint u = rep.cutVertexPoint w := by
    rw [← rep.cutProj_cutLab hG hθ hD hBd hstrip u, ← rep.cutProj_cutLab hG hθ hD hBd hstrip w, heq]
  apply rep.cutVertexPoint_inj_of_parity u w hul hwl _ hpt
  by_cases hP : rep.cutVertexPoint u ∈ (L.pathDrawing 0).U
  · rw [← (L.curve_parametrizes 0).2.1] at hP
    obtain ⟨t, ht⟩ := hP
    rw [rep.cutLab_curve hG hθ hD hBd hstrip u ht.symm,
      rep.cutLab_curve hG hθ hD hBd hstrip w (hpt.symm.trans ht.symm)] at heq
    have hs := cutSidePoint_side_eq hG hBd heq
    by_cases hu0 : u.val % 2 = 0 <;> by_cases hw0 : w.val % 2 = 0 <;> simp_all <;> omega
  · have hu0 := hup.resolve_left hP
    have hw0 := hwp.resolve_left (hpt ▸ hP)
    omega

include hno hθ hD hstrip in
/-- **Incidence along the left copy of `P₁`.** For a slot of the left copy of `P₁`, the vertex
bit is set exactly when its label is in `cutRc`. -/
theorem slots_path_incV (row : List ℕ)
    (horbit : ∀ q, q ∈ row ↔ ∃ n, cutNext^[n] gapCut = q) (u : Fin (2 * x.vertexCount)) (hu : u ∈ gm06CutPathLabels x.vertexCount hn x.endpoints
      (x.linkage[0]'(by rw [rep.linkage.1]; exact one_pos)) (rep.source 0).val true) :
    (gm06IncV (2 * x.vertexCount) (currentCut).origins row)[u.val]?.getD 0 ≠ 0 ↔ rep.cutLab hG hBd u ∈ cutRc G D := by
  have hl := rep.computed_path_labels_live hn 0 true hu
  have hV := ((rep.mem_computed_path_labels_iff hn 0 true u hl).mp hu).1
  rw [rep.incV_iff_label hG hno hθ hD hBd hstrip row horbit u hl]
  exact ⟨fun h => h.1, fun h => ⟨h, Or.inl ((L.pathDrawing 0).V_subset_U hV)⟩⟩

include hθ hD hstrip in
/-- **The right copy of `P₁`.** An incident slot is a slot of the right copy of `P₁` exactly when
its label is on the right lift. -/
theorem slots_upper_iff (row : List ℕ)
    (horbit : ∀ q, q ∈ row ↔ ∃ n, cutNext^[n] gapCut = q) (F : Drawing D)
    (hFU : F.U = (fun p : D => radialCylinderProjection p.1) ⁻¹' G.U ∪ bd D)
    (hFV : F.V = (fun p : D => radialCylinderProjection p.1) ⁻¹' G.V)
    (hEdges : ∀ ec ∈ F.E, ec ⊆ bd D ∨
      ∃ e ∈ G.E \ (L.pathDrawing 0).E, ec = (fun p : D => radialCylinderProjection p.1) ⁻¹' e)
    (u : Fin (2 * x.vertexCount)) (hu : (gm06IncV (2 * x.vertexCount) (currentCut).origins row)[u.val]?.getD 0 ≠ 0) :
    u.val ∈ (gm06CutPathLabels x.vertexCount hn x.endpoints
      (x.linkage[0]'(by rw [rep.linkage.1]; exact one_pos)) (rep.source 0).val false).map Fin.val ↔ rep.cutLab hG hBd u ∈ (cutSide L hG F 2).U := by
  have hl := rep.selected_face_vertex_live hG 0 row horbit u hu
  have hGv := (rep.selected_face_vertex_dart hG 0 row horbit u hu).1
  have hmem : u.val ∈ (gm06CutPathLabels x.vertexCount hn x.endpoints
      (x.linkage[0]'(by rw [rep.linkage.1]; exact one_pos)) (rep.source 0).val false).map Fin.val ↔ u ∈ gm06CutPathLabels x.vertexCount hn x.endpoints
      (x.linkage[0]'(by rw [rep.linkage.1]; exact one_pos)) (rep.source 0).val false :=
    ⟨fun h => by obtain ⟨v, hv, he⟩ := List.mem_map.mp h; exact Fin.ext he ▸ hv,
      fun h => List.mem_map.mpr ⟨u, h, rfl⟩⟩
  rw [hmem]
  refine (rep.mem_computed_path_labels_iff hn 0 false u hl).trans ?_
  rw [(cutSide_V_U L hG hθ hD hBd hstrip F hFU hFV hEdges (m := 2) (n := 1)
      (Or.inr ⟨rfl, rfl⟩)).2]
  have hs := rep.cutLab_mem_side_iff hG hθ hD hBd hstrip u false
  simp only [Bool.false_eq_true, ite_false] at hs
  rw [hs]
  simp only [Bool.not_false, Bool.toNat_true, decide_eq_false_iff_not]
  constructor
  · rintro ⟨hV, hodd⟩
    exact ⟨(L.pathDrawing 0).V_subset_U hV, by omega⟩
  · rintro ⟨hU, hd⟩
    exact ⟨mem_V_of_mem_U' (L.isSubdrawing 0).1 hU hGv, by omega⟩

end Fields

end GM06CurrentDrawingRep

end GraphMinor.GM06
