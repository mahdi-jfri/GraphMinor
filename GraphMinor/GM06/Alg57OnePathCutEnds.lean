module

public import GraphMinor.GM06.Alg57OnePathCutSides
public import GraphMinor.GM06.Alg57OnePathCutLabels
public import GraphMinor.GM06.Alg57CurrentEdgeIncidence
public import GraphMinor.GM06.Alg57CurrentFaceVertices
import all GraphMinor.GM06.Alg57CutFaceLink
import GraphMinor.GM06.Alg57CutCopiedSlots
import GraphMinor.Compute.GM06CutRowEncoding
import GraphMinor.Compute.GM06CutPathMembership
import GraphMinor.GM06.Section5OpenCutSheet
import GraphMinor.GM06.Section5CutRegionCoordinates

/-!
# The copy of a vertex that holds an edge off the one path

At a vertex `v` of `P₁` the cut tables keep each dart along an edge off `P₁` in exactly one copy of
`v`: the left copy when the dart is in the left block of the position of `v`, and the right copy
otherwise (`off_dart_copy`). At a vertex off `P₁` there is only the left copy. Together with
`raySides_of_position` this says which lift of `v` is an end of the copy of the edge in the cut
disc.
-/

@[expose] public section

namespace GraphMinor.GM06

open Set Topology GraphMinor.Surface GraphMinor.GM11 GraphMinor.Compute unitInterval

variable {G : Drawing ClosedCylinder} {θ : ℝ} {D : Set (ℝ × ℝ)}

/-- A point of `D` over a point off `P₁` in the closure of a set `e` off `P₁` is in the closure of
the points over `e`. Near such a point the projection is a homeomorphism, through the open sheet
of `exists_open_sheet_on_single_strip`. -/
theorem mem_closure_preimage_off_path (L : CylinderLinkage 1 G) (hG : IsCylinderSection5Drawing 1 G)
    (hθ : L.HasTheta θ) (hD : IsClosedDisc D) (hBd : discBd D = liftedStripBoundary hG.1 L 1)
    (hstrip : D ⊆ {p : ℝ × ℝ | 1 ≤ p.1 ∧ p.1 ≤ 2}) {e : Set ClosedCylinder}
    (he : e ⊆ (L.pathDrawing 0).Uᶜ) {p : D} (hp : cutProj D p ∉ (L.pathDrawing 0).U)
    (hpe : cutProj D p ∈ closure e) : p ∈ closure (cutProj D ⁻¹' e) := by
  obtain ⟨sh, -, hproj, hrange⟩ := exists_open_sheet_on_single_strip L hG hθ hD hBd hstrip
  have hmem : cutCov D p ∈ range sh := by
    rw [hrange]
    exact ⟨⟨p.1, p.2, rfl⟩, hp⟩
  obtain ⟨y, hy⟩ := hmem
  have hyv : y.1 = cutProj D p := (hproj y).symm.trans (by rw [hy]; rfl)
  have hyT : y ∈ closure (Subtype.val ⁻¹' e : Set ((L.pathDrawing 0).Uᶜ : Set ClosedCylinder)) := by
    rw [Topology.IsInducing.subtypeVal.closure_eq_preimage_closure_image,
      Subtype.image_preimage_coe, inter_eq_right.mpr he, mem_preimage, hyv]
    exact hpe
  have hmaps : MapsTo sh (Subtype.val ⁻¹' e) (cutCov D '' (cutProj D ⁻¹' e)) := by
    intro z hz
    have hzr : sh z ∈ range sh := mem_range_self z
    rw [hrange] at hzr
    obtain ⟨⟨q, hqD, hq⟩, -⟩ := hzr
    refine ⟨⟨q, hqD⟩, ?_, hq⟩
    have hqz : radialCylinderProjection q = z.1 := by
      have := hproj z
      rw [← hq] at this
      exact this
    change radialCylinderProjection q ∈ e
    rw [hqz]
    exact hz
  have hemb := isClosedEmbedding_single_strip_coverMap hD hstrip
  have hcl : closure (cutCov D '' (cutProj D ⁻¹' e)) = cutCov D '' closure (cutProj D ⁻¹' e) :=
    hemb.closure_image_eq _
  have h := map_mem_closure sh.continuous hyT hmaps
  rw [hy, hcl] at h
  obtain ⟨p', hp', hpp⟩ := h
  rwa [hemb.injective hpp] at hp'

/-- Two darts along the same edge are equal or reverse. -/
theorem dart_eq_or_flip {S : Type*} [TopologicalSpace S] {Γ : Drawing S} {c c' : DrawingDart Γ}
    (h : c'.1.1 = c.1.1) : c' = c ∨ c' = dartFlip Γ c := by
  rcases c with ⟨⟨e, b⟩, hc⟩
  rcases c' with ⟨⟨e', b'⟩, hc'⟩
  simp only at h
  subst h
  cases b <;> cases b' <;> simp [dartFlip]

namespace GM06CurrentDrawingRep

variable {x : GM06SuccessorInput} {L : CylinderLinkage 1 G} (rep : GM06CurrentDrawingRep x G L)

local notation "cutTables" => gm06BuildCutTables x.vertexCount rep.tagged.length x.endpoints
  x.linkage x.innerCuff x.outerCuff

/-- The path ends of a position are path words or their reverses. -/
theorem pathEnds_path_word (a : Fin x.vertexCount) {p : GM06CutPosition}
    (hp : gm06CutPositionAt cutTables a.val = some p) {d : ℕ} (hd : d ∈ p.pathEnds) :
    d ∈ x.linkage.flatten ∨ gm06DartMate d ∈ x.linkage.flatten := by
  rcases (gm06CutPositionAt_pathEnds_iff _ a.val d).mp ⟨p, hp, hd⟩ with h | h
  · exact Or.inr (gm06BuildCutTables_incoming_source x.endpoints x.linkage x.innerCuff
      x.outerCuff a.isLt h).1
  · exact Or.inl (gm06BuildCutTables_outgoing_source x.endpoints x.linkage x.innerCuff
      x.outerCuff a.isLt h).1

/-- The first and last darts of a copy are path ends or cuff ends. -/
theorem cutFirst_cutLast_special (a : Fin x.vertexCount) {p : GM06CutPosition}
    (hp : gm06CutPositionAt cutTables a.val = some p) (left : Bool) :
    (cutFirst p left ∈ p.pathEnds ∨ 2 * rep.tagged.length ≤ cutFirst p left) ∧
      (cutLast p left ∈ p.pathEnds ∨ 2 * rep.tagged.length ≤ cutLast p left) := by
  cases p with
  | interior a' b' =>
    cases left <;> simp [cutFirst, cutLast, GM06CutPosition.pathEnds]
  | start b' cp cn =>
    obtain ⟨i, -, hcp, hcn⟩ := rep.cut_start_markers one_pos a hp
    cases left <;> simp [cutFirst, cutLast, GM06CutPosition.pathEnds] <;> omega
  | terminal a' cp cn =>
    obtain ⟨i, -, hcp, hcn⟩ := rep.cut_terminal_markers one_pos a hp
    cases left <;> simp [cutFirst, cutLast, GM06CutPosition.pathEnds] <;> omega

variable (hG : IsCylinderSection5Drawing 1 G)

include hG in
/-- For a dart that is not a path end or a cuff end, the left block is the side chosen by
the program's tables. -/
theorem cutLeftBlock_iff_dartLeft (a : Fin x.vertexCount) {p : GM06CutPosition}
    (hp : gm06CutPositionAt cutTables a.val = some p) {d : ℕ}
    (hd : d ∈ x.rotations.getD a.val []) (hdm : d < 2 * rep.tagged.length) (hdp : d ∉ p.pathEnds) :
    cutLeftBlock p (x.rotations.getD a.val []) d ↔
      gm06CutDartLeft p (x.rotations.getD a.val []) d = true := by
  have hlt : a.val < x.rotations.length := by rw [rep.rows_length]; exact a.isLt
  have hvr : x.rotations[a.val]? = some (x.rotations.getD a.val []) := by
    rw [List.getD_eq_getElem _ _ hlt, List.getElem?_eq_getElem hlt]
  have hok := rep.cut_block_ok hG a.val _ p hvr hp
  obtain ⟨-, -, -, hkeep⟩ := cutBlock_spec hok true
  have hk := hkeep d hd
  have hdl : gm06CutDartLeft p (x.rotations.getD a.val []) d = true ↔
      cutKeep p (x.rotations.getD a.val []) true d = true := by
    simp [cutKeep, hdp]
  obtain ⟨hF, hL⟩ := rep.cutFirst_cutLast_special a hp true
  have hdF : d ≠ cutFirst p true := by
    rintro rfl
    rcases hF with h | h
    · exact hdp h
    · omega
  have hdL : d ≠ cutLast p true := by
    rintro rfl
    rcases hL with h | h
    · exact hdp h
    · omega
  rw [hdl, hk, cutLeftBlock]
  constructor
  · rintro ⟨-, h | h⟩
    · exact absurd h hdF
    · exact Or.inr (Or.inr h)
  · rintro (h | h | h)
    · exact absurd h hdF
    · exact absurd h hdL
    · exact ⟨hd, Or.inr h⟩

include hG in
/-- **The copy that keeps a dart off `P₁`.** Let a cut dart `q` lie in the copy `left` of the
vertex `v`, and let its old dart `d` be an ordinary dart that is not a word of `P₁` or the reverse
of one. If `v` has a cut position `p`, then `left` holds exactly when `d` is in the left block of
`p`. If `v` is not split, then `left` holds. -/
theorem off_dart_copy (v : Fin x.vertexCount) (left : Bool) {q : ℕ}
    (hq : q ∈ (gm06SplitRotationRows cutTables x.rotations).getD (gm06CutVertex v.val left) [])
    (hdm : gm06UncutDart q < 2 * rep.tagged.length)
    (hdP : gm06UncutDart q ∉ x.linkage.flatten)
    (hdP' : gm06DartMate (gm06UncutDart q) ∉ x.linkage.flatten) :
    gm06UncutDart q ∈ x.rotations.getD v.val [] ∧
      (∀ p, gm06CutPositionAt cutTables v.val = some p →
        (left = true ↔ cutLeftBlock p (x.rotations.getD v.val []) (gm06UncutDart q))) ∧
      (gm06CutPositionAt cutTables v.val = none → left = true) := by
  have hlt : v.val < x.rotations.length := by rw [rep.rows_length]; exact v.isLt
  rw [splitRows_getD _ _ v.val hlt left] at hq
  unfold gm06CutSelectedRow at hq
  obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hq
  obtain ⟨hdrow, hret⟩ := List.mem_filter.mp hd
  have hproj : gm06UncutDart (gm06CutOutputDart (gm06CutPositionAt cutTables v.val) left d) = d := by
    cases h : gm06CutPositionAt cutTables v.val with
    | none => exact gm06UncutDart_cut d 0 (by decide)
    | some p => exact gm06CutRowDart_project p left d
  rw [hproj] at hdm hdP hdP' ⊢
  refine ⟨hdrow, fun p hp => ?_, fun hp => ?_⟩
  · have hdp : d ∉ p.pathEnds := fun h => by
      rcases rep.pathEnds_path_word v hp h with h' | h'
      · exact hdP h'
      · exact hdP' h'
    rw [rep.cutLeftBlock_iff_dartLeft hG v hp hdrow hdm hdp]
    simp only [gm06CutRetain, hp, hdp, decide_false, Bool.false_or, beq_iff_eq] at hret
    rw [hret]
  · simpa only [gm06CutRetain, hp] using hret

local notation "splitRows" => gm06SplitRotationRows cutTables x.rotations

/-- A member of a row of a list of rows is in its flattening. -/
theorem mem_flatten_of_mem_getD {rows : List (List ℕ)} {i q : ℕ} (h : q ∈ rows.getD i []) :
    q ∈ rows.flatten := by
  by_cases hi : i < rows.length
  · rw [List.getD_eq_getElem _ _ hi] at h
    exact List.mem_flatten.mpr ⟨_, List.getElem_mem hi, h⟩
  · rw [List.getD_eq_default _ _ (by omega)] at h
    exact absurd h List.not_mem_nil

include hG in
/-- The origin of a cut dart is the slot of the row that holds it. -/
theorem origin_eq_of_mem {s : ℕ} (hs : s < 2 * x.vertexCount) {q : ℕ} (hq : q ∈ (splitRows).getD s []) :
    (gm06CutDataOfLinkage x.vertexCount rep.tagged.length x.endpoints x.linkage x.innerCuff
      x.outerCuff x.rotations (List.range x.vertexCount)).origins[q]?.getD 0 = s := by
  obtain ⟨hn, hb, -, -, -⟩ := rep.cut_data_face_encoding hG (List.range x.vertexCount)
  have hqf := mem_flatten_of_mem_getD hq
  have hlen : s < (splitRows).length := by
    rw [gm06SplitRotationRows_length, rep.rows_length]; exact hs
  have hbq := hb q hqf
  dsimp only [gm06CutDataOfLinkage]
  rw [rep.cuff_lengths.1, rep.cuff_lengths.2]
  apply (gm06CutOrigins_row_iff _ hn hqf (by omega) hlen).mpr
  rwa [List.getD_eq_getElem _ _ hlen] at hq

include hG in
/-- **The facts about the slot of a cut dart off `P₁`.** Let the cut dart `q` lie in the row of the
copied slot `s`, over the original slot `a`, and let its old dart be an ordinary dart that is not a
word of `P₁` or the reverse of one. Then `a` is live, every dart with the old label of `q` starts
at the vertex of `a`, and `s` is the left copy exactly when the old dart is in the left block of
the position of `a`, or `a` is not split. -/
theorem off_slot_facts {s : Fin (2 * x.vertexCount)} (a : Fin x.vertexCount) (ha : a.val = s.val / 2)
    {q : ℕ} (hq : q ∈ (splitRows).getD s.val [])
    (hdm : gm06UncutDart q < 2 * rep.tagged.length) (hdP : gm06UncutDart q ∉ x.linkage.flatten)
    (hdP' : gm06DartMate (gm06UncutDart q) ∉ x.linkage.flatten) :
    a ∈ rep.live ∧ rep.cutVertexPoint s = rep.vertex a ∧
      (∀ c : DrawingDart (cylinderSphereDrawing rep.cuffed),
        persistentDartLabel rep.label c = gm06UncutDart q →
          dartVertex rep.par c = cylinderToSphere (rep.vertex a)) ∧
      (∀ p, gm06CutPositionAt cutTables a.val = some p →
        (cutLeftBlock p (x.rotations.getD a.val []) (gm06UncutDart q) ↔ s.val % 2 = 0)) ∧
      (gm06CutPositionAt cutTables a.val = none → s.val % 2 = 0) := by
  have hs : gm06CutVertex a.val (decide (s.val % 2 = 0)) = s.val := by
    unfold gm06CutVertex
    rw [ha]
    by_cases h : s.val % 2 = 0 <;> simp [h] <;> omega
  rw [← hs] at hq
  obtain ⟨hrow, hpos, hnone⟩ := rep.off_dart_copy hG a _ hq hdm hdP hdP'
  have hlive := rep.live_of_mem_row hrow
  refine ⟨hlive, congrArg rep.vertex (Fin.ext ha.symm), fun c hc => ?_, fun p hp => ?_,
    fun hp => ?_⟩
  · exact (rep.label_mem_row_iff a hlive c).mp (hc ▸ hrow)
  · rw [← hpos p hp, decide_eq_true_iff]
  · simpa using hnone hp

/-- The point of the cut disc named by a copied vertex label `u`: the point over the vertex of
`u`, on the left lift when `u` is even and on the right lift when `u` is odd. -/
noncomputable def cutLab (hBd : discBd D = liftedStripBoundary hG.1 L 1)
    (u : Fin (2 * x.vertexCount)) : D :=
  cutPointLabel L hG (cutSidePoint L hG hBd true 0) (decide (u.val % 2 = 0)) (rep.cutVertexPoint u)

/-- The set of the cut disc named by a copied edge label `e`: the points over its edge, without
the points of the lift of the other side. -/
noncomputable def cutEdgeLab (e : ℕ) : Set D :=
  cutEdgeLabel L hG (decide (e % 2 = 0)) (rep.cutEdgePoint e)

variable (hθ : L.HasTheta θ) (hD : IsClosedDisc D) (hBd : discBd D = liftedStripBoundary hG.1 L 1)
  (hstrip : D ⊆ {p : ℝ × ℝ | 1 ≤ p.1 ∧ p.1 ≤ 2})

include hθ hD hstrip in
/-- At a slot over `P₁(t)`, the label is the point of the lift of its side. -/
theorem cutLab_curve (u : Fin (2 * x.vertexCount)) {t : I} (ht : rep.cutVertexPoint u = L.curve 0 t) :
    rep.cutLab hG hBd u = cutSidePoint L hG hBd (decide (u.val % 2 = 0)) t := by
  unfold cutLab
  rw [ht, cutPointLabel_curve L hG hθ hD hBd hstrip]

include hθ hD hstrip in
/-- At a slot off `P₁`, the label is the only point over its vertex. -/
theorem cutLab_off (u : Fin (2 * x.vertexCount)) (hu : rep.cutVertexPoint u ∉ (L.pathDrawing 0).U)
    {z : D} (hz : cutProj D z = rep.cutVertexPoint u) : rep.cutLab hG hBd u = z := by
  unfold cutLab
  exact cutPointLabel_off L hG hθ hD hBd hstrip _ _ hu hz

include hθ hD hstrip in
/-- The side of a dart off `P₁` at a slot over `P₁(t)`. Let the cut dart `q` in the row of `s` have
the old dart of `c`, off `P₁`, and let `c` start at `P₁(t)`, the vertex of the slot `a` with
position `p`. Then `c` is in the left block of `p` exactly when `s` is even, and the label of `s`
is the point of the lift of that side. -/
theorem off_end_side {s : Fin (2 * x.vertexCount)} {q : ℕ} (hq : q ∈ (splitRows).getD s.val [])
    (hdm : gm06UncutDart q < 2 * rep.tagged.length) (hdP : gm06UncutDart q ∉ x.linkage.flatten)
    (hdP' : gm06DartMate (gm06UncutDart q) ∉ x.linkage.flatten)
    {c : DrawingDart (cylinderSphereDrawing rep.cuffed)}
    (hcl : persistentDartLabel rep.label c = gm06UncutDart q) {t : I}
    (hct : dartVertex rep.par c = cylinderToSphere (L.curve 0 t))
    (a : Fin x.vertexCount) (ha : a ∈ rep.live) (hat : rep.vertex a = L.curve 0 t)
    {p : GM06CutPosition} (hp : gm06CutPositionAt cutTables a.val = some p) :
    (cutLeftBlock p (x.rotations.getD a.val []) (persistentDartLabel rep.label c) ↔
      decide (s.val % 2 = 0) = true) ∧
      rep.cutLab hG hBd s = cutSidePoint L hG hBd (decide (s.val % 2 = 0)) t := by
  let b : Fin x.vertexCount := ⟨s.val / 2, by have := s.isLt; omega⟩
  obtain ⟨hlive, hpt, hvert, hpos, -⟩ := rep.off_slot_facts hG b rfl hq hdm hdP hdP'
  have hbt : rep.vertex b = L.curve 0 t :=
    injective_cylinderToSphere ((hvert c hcl).symm.trans hct)
  have hba : b = a := rep.vertex_inj hlive ha (hbt.trans hat.symm)
  rw [← hba] at hp
  refine ⟨?_, rep.cutLab_curve hG hθ hD hBd hstrip s (hpt.trans hbt)⟩
  rw [← hba, hcl, hpos p hp, decide_eq_true_iff]

variable {U₁ U₂ : Set CylinderCover} (hU₁ : IsOpen U₁) (hU₂ : IsOpen U₂) (hU : Disjoint U₁ U₂)
  (h₁ : ∀ t, coverLift L hG 1 t ∈ U₁) (h₂ : ∀ t, coverLift L hG 2 t ∈ U₂)
  {R : DartRotation (DrawingDart (cylinderSphereDrawing rep.cuffed))}
  (hR : IsDrawingRotation (cylinderSphereDrawing rep.cuffed) rep.par R)
  (hccw : IsCcwRotation (cylinderSphereDrawing rep.cuffed) rep.par R)
  (hrot : ∀ d, persistentDartLabel rep.label (R.rot d) =
    gm06RotationPermutation x.rotations (persistentDartLabel rep.label d))
  (heI : ∀ j : Fin 1, cylinderToSphere '' (initialCuffGapCurve 1 j '' Ioo 0 1) ∈
    (cylinderSphereDrawing rep.cuffed).E)
  (heO : ∀ j : Fin 1, cylinderToSphere '' (alg511OuterCuffGapCurve 1 j '' Ioo 0 1) ∈
    (cylinderSphereDrawing rep.cuffed).E)
  (hV : ∀ v ∈ (cylinderSphereDrawing rep.cuffed).V, ∃ a : DrawingDart (cylinderSphereDrawing rep.cuffed),
    dartVertex rep.par a = v)
  (F : Drawing D) (hFU : F.U = (fun p : D => radialCylinderProjection p.1) ⁻¹' G.U ∪ bd D)
  (hFV : F.V = (fun p : D => radialCylinderProjection p.1) ⁻¹' G.V)
  (hEdges : ∀ ec ∈ F.E, ec ⊆ bd D ∨
    ∃ e ∈ G.E \ (L.pathDrawing 0).E, ec = (fun p : D => radialCylinderProjection p.1) ⁻¹' e)

include hθ hD hstrip hU₁ hU₂ hU h₁ h₂ hR hccw hrot heI heO hV in
/-- **The label of the slot of a dart off `P₁` is an end of its edge in the cut disc.** Let `c` be a
dart along an edge `f` of `G` off `P₁`, whose cut copy lies in the row of the slot `s`. Then the
label of `s` is in the closure of the points over `f`. -/
theorem off_end_mem_closure {f : Set ClosedCylinder} (hfG : f ∈ G.E)
    (hfP : f ∉ (L.pathDrawing 0).E) {s : Fin (2 * x.vertexCount)} {q : ℕ}
    (hq : q ∈ (splitRows).getD s.val []) (hdm : gm06UncutDart q < 2 * rep.tagged.length)
    (hdP : gm06UncutDart q ∉ x.linkage.flatten)
    (hdP' : gm06DartMate (gm06UncutDart q) ∉ x.linkage.flatten)
    {c : DrawingDart (cylinderSphereDrawing rep.cuffed)}
    (hcl : persistentDartLabel rep.label c = gm06UncutDart q) (hcf : c.1.1 = cylinderToSphere '' f)
    (hsf : rep.cutVertexPoint s ∈ closure f) :
    rep.cutLab hG hBd s ∈ closure (cutProj D ⁻¹' f) := by
  let a : Fin x.vertexCount := ⟨s.val / 2, by have := s.isLt; omega⟩
  obtain ⟨hlive, hpt, hvert, -, -⟩ := rep.off_slot_facts hG a rfl hq hdm hdP hdP'
  by_cases hP : rep.vertex a ∈ (L.pathDrawing 0).U
  · obtain ⟨p, hp⟩ := Option.ne_none_iff_exists'.mp (rep.cut_position_ne_none_of_path a hlive 0 hP)
    rw [← (L.curve_parametrizes 0).2.1] at hP
    obtain ⟨t, ht⟩ := hP
    have hct : dartVertex rep.par c = cylinderToSphere (L.curve 0 t) := by
      rw [hvert c hcl, ht]
    obtain ⟨hside, hlab⟩ := rep.off_end_side hG hθ hD hBd hstrip hq hdm hdP hdP' hcl hct a hlive
      ht.symm hp
    have hrs := rep.raySides_of_position hG hθ hD hBd hstrip hU₁ hU₂ hU h₁ h₂ hR hccw hrot heI heO hV
      a ht.symm hp
    rw [hlab]
    exact mem_closure_of_raySides hθ hD hBd hstrip hU₁ hU₂ hU h₁ h₂ rep.edgePar hrs hfG hfP hct hcf
      hside
  · obtain ⟨z, hz⟩ := surjective_single_strip_projection L hG hθ hD hBd hstrip (rep.vertex a)
    have hz' : cutProj D z = rep.cutVertexPoint s := hz.trans hpt.symm
    rw [rep.cutLab_off hG hθ hD hBd hstrip s (hpt ▸ hP) hz']
    refine mem_closure_preimage_off_path L hG hθ hD hBd hstrip (fun y hy hyP => ?_)
      (by rw [hz', hpt]; exact hP) (by rw [hz']; exact hsf)
    exact disjoint_left.mp (deleted_edge_disjoint_subdrawing (L.isSubdrawing 0).1 hfG hfP) hy hyP

include hθ hD hstrip hU₁ hU₂ hU h₁ h₂ hR hccw hrot heI heO hV hFU hFV hEdges in
/-- **The ends of an edge off `P₁` in the cut disc.** Let the cut dart `q` lie in the row of the
slot `u` and its reverse in the row of `w`, and let the edge of `q` be off `P₁`. Then in `F` the
points over this edge form an edge joining the labels of `u` and `w`. -/
theorem off_edge_isLink {q : ℕ} (hdm : gm06UncutDart q < 2 * rep.tagged.length)
    (hfP : rep.cutEdgePoint (q / 2) ∉ (L.pathDrawing 0).E)
    {u w : Fin (2 * x.vertexCount)} (hu : q ∈ (splitRows).getD u.val [])
    (hw : gm06DartMate q ∈ (splitRows).getD w.val []) :
    F.toGraph.IsLink (cutProj D ⁻¹' rep.cutEdgePoint (q / 2)) (rep.cutLab hG hBd u)
      (rep.cutLab hG hBd w) := by
  have hqf := mem_flatten_of_mem_getD hu
  obtain ⟨-, hb, -, -, -⟩ := rep.cut_data_face_encoding hG (List.range x.vertexCount)
  have hact : q ∈ (gm06CutDataOfLinkage x.vertexCount rep.tagged.length x.endpoints x.linkage
      x.innerCuff x.outerCuff x.rotations (List.range x.vertexCount)).activeDarts := by
    refine (gm06CutDataOfLinkage_active_iff _ _ _ _ _ _ _ _ _).mpr ⟨?_, hqf⟩
    rw [rep.cuff_lengths.1, rep.cuff_lengths.2]
    have := hb q hqf
    omega
  obtain ⟨u', w', hu', hw', hlink⟩ := rep.cut_ordinary_isLink hG hact hdm
  have huu : u' = u := Fin.ext (hu'.symm.trans (rep.origin_eq_of_mem hG u.isLt hu))
  have hww : w' = w := Fin.ext (hw'.symm.trans (rep.origin_eq_of_mem hG w.isLt hw))
  subst huu hww
  obtain ⟨c, hcl, hcf⟩ := rep.cut_ordinary_sphere_edge hG hact hdm
  set f := rep.cutEdgePoint (q / 2) with hf_def
  have hfG : f ∈ G.E := hlink.1
  -- the old dart is off `P₁`
  have hidx : q / 2 / 2 = gm06UncutDart q / 2 := by unfold gm06UncutDart; omega
  have hfeq : f = rep.edge ⟨gm06UncutDart q / 2, by omega⟩ := by
    rw [hf_def]
    unfold cutEdgePoint
    rw [dif_pos (by omega)]
    exact congrArg rep.edge (Fin.ext hidx)
  have hdP : gm06UncutDart q ∉ x.linkage.flatten := fun h => by
    apply hfP
    rw [hfeq]
    exact rep.path_word_edge (rep.mem_linkage_zero_of_flatten h) hdm
  have hdP' : gm06DartMate (gm06UncutDart q) ∉ x.linkage.flatten := fun h => by
    have he := rep.path_word_edge (rep.mem_linkage_zero_of_flatten h) (gm06DartMate_lt hdm)
    have hfin : (⟨gm06DartMate (gm06UncutDart q) / 2, by have := gm06DartMate_lt hdm; omega⟩ :
        Fin rep.tagged.length) = ⟨gm06UncutDart q / 2, by omega⟩ := Fin.ext (gm06DartMate_edge _)
    rw [hfin, ← hfeq] at he
    exact hfP he
  -- the reverse dart
  have hmq : gm06UncutDart (gm06DartMate q) = gm06DartMate (gm06UncutDart q) := gm06UncutDart_mate q
  have hdm' : gm06UncutDart (gm06DartMate q) < 2 * rep.tagged.length := by
    rw [hmq]; exact gm06DartMate_lt hdm
  have hdPm : gm06UncutDart (gm06DartMate q) ∉ x.linkage.flatten := by rw [hmq]; exact hdP'
  have hdPm' : gm06DartMate (gm06UncutDart (gm06DartMate q)) ∉ x.linkage.flatten := by
    rw [hmq, gm06DartMate_involutive]; exact hdP
  have hcl' : persistentDartLabel rep.label (dartFlip _ c) = gm06UncutDart (gm06DartMate q) := by
    rw [persistentDartLabel_flip, hcl, hmq]
  have hcf' : (dartFlip _ c).1.1 = cylinderToSphere '' f := hcf
  -- the ends in `G`
  have hends : closure f ∩ G.V = {rep.cutVertexPoint u', rep.cutVertexPoint w'} := hlink.2.2.2
  have huf : rep.cutVertexPoint u' ∈ closure f := by
    have h : rep.cutVertexPoint u' ∈ closure f ∩ G.V := by rw [hends]; exact mem_insert _ _
    exact h.1
  have hwf : rep.cutVertexPoint w' ∈ closure f := by
    have h : rep.cutVertexPoint w' ∈ closure f ∩ G.V := by rw [hends]; exact mem_insert_of_mem _ rfl
    exact h.1
  have hEu := rep.off_end_mem_closure hG hθ hD hBd hstrip hU₁ hU₂ hU h₁ h₂ hR hccw hrot heI heO hV
    hfG hfP hu hdm hdP hdP' hcl hcf huf
  have hEw := rep.off_end_mem_closure hG hθ hD hBd hstrip hU₁ hU₂ hU h₁ h₂ hR hccw hrot heI heO hV
    hfG hfP hw hdm' hdPm hdPm' hcl' hcf' hwf
  have hVu : rep.cutLab hG hBd u' ∈ F.V :=
    cutPointLabel_mem_V L hG hθ hD hBd hstrip F hFV _ _ hlink.2.1
  have hVw : rep.cutLab hG hBd w' ∈ F.V :=
    cutPointLabel_mem_V L hG hθ hD hBd hstrip F hFV _ _ hlink.2.2.1
  refine ⟨preimage_off_path_mem_E L hG hθ hD hBd hstrip F hFU hFV hEdges hfG hfP, hVu, hVw, ?_⟩
  apply subset_antisymm
  · rintro z ⟨hzc, hzV⟩
    have hzf : cutProj D z ∈ closure f := by
      have h := image_closure_subset_closure_image (continuous_cutProj (D := D)) ⟨z, hzc, rfl⟩
      refine closure_mono ?_ h
      rintro _ ⟨z', hz', rfl⟩
      exact hz'
    have hzG : cutProj D z ∈ G.V := by rw [hFV] at hzV; exact hzV
    have hz2 : cutProj D z ∈ ({rep.cutVertexPoint u', rep.cutVertexPoint w'} : Set ClosedCylinder) := by
      rw [← hends]; exact ⟨hzf, hzG⟩
    by_cases hP : cutProj D z ∈ (L.pathDrawing 0).U
    · have hP' := hP
      rw [← (L.curve_parametrizes 0).2.1] at hP'
      obtain ⟨t, ht⟩ := hP'
      -- a live slot over `P₁(t)`
      have hslot : ∃ a : Fin x.vertexCount, a ∈ rep.live ∧ rep.vertex a = L.curve 0 t := by
        rcases hz2 with h | h
        · let a : Fin x.vertexCount := ⟨u'.val / 2, by have := u'.isLt; omega⟩
          obtain ⟨hlive, -, -, -, -⟩ := rep.off_slot_facts hG a rfl hu hdm hdP hdP'
          exact ⟨a, hlive, (ht.trans h).symm⟩
        · let a : Fin x.vertexCount := ⟨w'.val / 2, by have := w'.isLt; omega⟩
          obtain ⟨hlive, -, -, -, -⟩ := rep.off_slot_facts hG a rfl hw hdm' hdPm hdPm'
          exact ⟨a, hlive, (ht.trans h).symm⟩
      obtain ⟨a, ha, hat⟩ := hslot
      obtain ⟨p, hp⟩ := Option.ne_none_iff_exists'.mp
        (rep.cut_position_ne_none_of_path a ha 0 (by rw [hat, ht]; exact hP))
      have hrs := rep.raySides_of_position hG hθ hD hBd hstrip hU₁ hU₂ hU h₁ h₂ hR hccw hrot heI heO
        hV a hat hp
      obtain ⟨c'', hc''v, hc''f, hs1, hs2⟩ := exists_dart_of_mem_closure_of_raySides hθ hD hBd hstrip
        hU₁ hU₂ hU h₁ h₂ rep.subdrawing rep.edgePar hrs hfG hfP hzc ht.symm
      rcases dart_eq_or_flip (hc''f.trans hcf.symm) with rfl | rfl
      · obtain ⟨hside, hlab⟩ := rep.off_end_side hG hθ hD hBd hstrip hu hdm hdP hdP' hcl hc''v a ha
          hat hp
        left
        rw [hlab]
        cases hd : decide (u'.val % 2 = 0)
        · exact hs2 (fun h => by rw [hside, hd] at h; exact Bool.false_ne_true h)
        · exact hs1 (hside.mpr hd)
      · obtain ⟨hside, hlab⟩ := rep.off_end_side hG hθ hD hBd hstrip hw hdm' hdPm hdPm' hcl' hc''v a
          ha hat hp
        right
        rw [hlab]
        cases hd : decide (w'.val % 2 = 0)
        · exact hs2 (fun h => by rw [hside, hd] at h; exact Bool.false_ne_true h)
        · exact hs1 (hside.mpr hd)
    · rcases hz2 with h | h
      · left
        exact (rep.cutLab_off hG hθ hD hBd hstrip u' (h ▸ hP) h).symm
      · right
        exact (rep.cutLab_off hG hθ hD hBd hstrip w' (h ▸ hP) h).symm
  · rintro z (rfl | rfl)
    · exact ⟨hEu, hVu⟩
    · exact ⟨hEw, hVw⟩

/-- An active word whose edge is an edge of `P₁` is a word of `P₁` or the reverse of one. -/
theorem path_word_of_edge {d : ℕ} (hdm : d < 2 * rep.tagged.length)
    (hact : (rep.tagged[d / 2]'(by omega)).2 = 1)
    (he : rep.edge ⟨d / 2, by omega⟩ ∈ (L.pathDrawing 0).E) :
    d ∈ x.linkage.flatten ∨ gm06DartMate d ∈ x.linkage.flatten := by
  obtain ⟨W, -, henc, hP⟩ := rep.linkage.path 0
  rw [← hP, walkDrawing_E] at he
  obtain ⟨d', hd', hdb', heq⟩ := (henc.edge_mem_iff _).mp he
  obtain ⟨hdb'', hact'⟩ := henc.active_words d' hd'
  have hflat : d' ∈ x.linkage.flatten := List.mem_flatten.mpr ⟨_, List.getElem_mem _, hd'⟩
  have hidx : d' / 2 = d / 2 := congrArg Fin.val (rep.edge_inj hact' hact heq)
  rcases gm06DartMate_end_cases d with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
    rcases gm06DartMate_end_cases d' with ⟨h1', h2'⟩ | ⟨h1', h2'⟩
  · left; rw [show d = d' by omega]; exact hflat
  · right; rw [show gm06DartMate d = d' by omega]; exact hflat
  · right; rw [show gm06DartMate d = d' by omega]; exact hflat
  · left; rw [show d = d' by omega]; exact hflat

include hθ hD hstrip hFU hFV hEdges in
/-- **The ends of a copy of an edge of `P₁` in the cut disc.** Let the cut dart `q` lie in the row
of the slot `u` and its reverse in the row of `w`, and let the edge of `q` be an edge of `P₁`. Then
in `F` the copy of this edge on the lift of the tag of `q` joins the labels of `u` and `w`. -/
theorem path_edge_isLink {q : ℕ} (hdm : gm06UncutDart q < 2 * rep.tagged.length)
    (hfP : rep.cutEdgePoint (q / 2) ∈ (L.pathDrawing 0).E)
    {u w : Fin (2 * x.vertexCount)} (hu : q ∈ (splitRows).getD u.val [])
    (hw : gm06DartMate q ∈ (splitRows).getD w.val []) :
    F.toGraph.IsLink (rep.cutEdgeLab hG (q / 2)) (rep.cutLab hG hBd u) (rep.cutLab hG hBd w) := by
  have hqf := mem_flatten_of_mem_getD hu
  obtain ⟨-, hb, -, -, -⟩ := rep.cut_data_face_encoding hG (List.range x.vertexCount)
  have hact : q ∈ (gm06CutDataOfLinkage x.vertexCount rep.tagged.length x.endpoints x.linkage
      x.innerCuff x.outerCuff x.rotations (List.range x.vertexCount)).activeDarts := by
    refine (gm06CutDataOfLinkage_active_iff _ _ _ _ _ _ _ _ _).mpr ⟨?_, hqf⟩
    rw [rep.cuff_lengths.1, rep.cuff_lengths.2]
    have := hb q hqf
    omega
  obtain ⟨u', w', hu', hw', hlink⟩ := rep.cut_ordinary_isLink hG hact hdm
  have huu : u' = u := Fin.ext (hu'.symm.trans (rep.origin_eq_of_mem hG u.isLt hu))
  have hww : w' = w := Fin.ext (hw'.symm.trans (rep.origin_eq_of_mem hG w.isLt hw))
  subst huu hww
  set f := rep.cutEdgePoint (q / 2) with hf_def
  have hidx : q / 2 / 2 = gm06UncutDart q / 2 := by unfold gm06UncutDart; omega
  have hfeq : f = rep.edge ⟨gm06UncutDart q / 2, by omega⟩ := by
    rw [hf_def]
    unfold cutEdgePoint
    rw [dif_pos (by omega)]
    exact congrArg rep.edge (Fin.ext hidx)
  -- the old dart is a word of `P₁` or the reverse of one
  have hrow := splitRows_project_mem _ _ u'.val q hu
  let v : Fin x.vertexCount := ⟨u'.val / 2, by have := u'.isLt; omega⟩
  have hactive := rep.row_ordinary_active hG v hrow hdm
  have hpath := rep.path_word_of_edge hdm hactive (hfeq ▸ hfP)
  -- the tag of `q` names its side
  let left := decide (q / 2 % 2 = 0)
  have htag : (!left).toNat = q / 2 % 2 := by
    by_cases h : q / 2 % 2 = 0
    · simp [left, h]
    · have h1 : q / 2 % 2 = 1 := by omega
      simp [left, h1]
  have hq : gm06CutDart (gm06UncutDart q) (!left).toNat = q := by
    rw [htag]; exact gm06CutDart_rebuild q
  have horg := rep.cut_path_copy_origin hpath left
  rw [hq, rep.origin_eq_of_mem hG u'.isLt hu] at horg
  have hpath' : gm06DartMate (gm06UncutDart q) ∈ x.linkage.flatten ∨
      gm06DartMate (gm06DartMate (gm06UncutDart q)) ∈ x.linkage.flatten := by
    rw [gm06DartMate_involutive]; exact hpath.symm
  have horg' := rep.cut_path_copy_origin hpath' left
  rw [gm06CutDart_mate, hq, rep.origin_eq_of_mem hG w'.isLt hw] at horg'
  have hul : decide (u'.val % 2 = 0) = left := by
    rw [horg]; unfold gm06CutVertex; cases left <;> simp
  have hwl : decide (w'.val % 2 = 0) = left := by
    rw [horg']; unfold gm06CutVertex; cases left <;> simp
  -- the ends lie on `P₁`
  have hfU : f ⊆ (L.pathDrawing 0).U := fun c hc => (hfP.2.1 hc).1
  have hends : closure f ∩ G.V = {rep.cutVertexPoint u', rep.cutVertexPoint w'} := hlink.2.2.2
  have hcl : closure f ⊆ (L.pathDrawing 0).U := closure_minimal hfU (L.pathDrawing 0).isClosed_U
  have huP : rep.cutVertexPoint u' ∈ (L.pathDrawing 0).U := by
    have h : rep.cutVertexPoint u' ∈ closure f ∩ G.V := by rw [hends]; exact mem_insert _ _
    exact hcl h.1
  have hwP : rep.cutVertexPoint w' ∈ (L.pathDrawing 0).U := by
    have h : rep.cutVertexPoint w' ∈ closure f ∩ G.V := by
      rw [hends]; exact mem_insert_of_mem _ rfl
    exact hcl h.1
  rw [← (L.curve_parametrizes 0).2.1] at huP hwP
  obtain ⟨a, ha⟩ := huP
  obtain ⟨b, hb'⟩ := hwP
  have hl : G.toGraph.IsLink f (L.curve 0 a) (L.curve 0 b) := by rw [ha, hb']; exact hlink
  have hres := cutEdgeLabel_path_isLink L hG hθ hD hBd hstrip F hFU hFV hEdges left hfP hl
  rw [rep.cutLab_curve hG hθ hD hBd hstrip u' ha.symm, rep.cutLab_curve hG hθ hD hBd hstrip w' hb'.symm,
    hul, hwl]
  exact hres

include hθ hD hstrip hU₁ hU₂ hU h₁ h₂ hR hccw hrot heI heO hV hFU hFV hEdges in
/-- **The ends of a cut edge in the cut disc.** Let the cut dart `q` of an ordinary dart lie in the
row of the slot `u` and its reverse in the row of `w`. Then in `F` the set named by the edge label
of `q` is an edge joining the labels of `u` and `w`. -/
theorem cut_edge_isLink {q : ℕ} (hdm : gm06UncutDart q < 2 * rep.tagged.length)
    {u w : Fin (2 * x.vertexCount)} (hu : q ∈ (splitRows).getD u.val [])
    (hw : gm06DartMate q ∈ (splitRows).getD w.val []) :
    F.toGraph.IsLink (rep.cutEdgeLab hG (q / 2)) (rep.cutLab hG hBd u) (rep.cutLab hG hBd w) := by
  by_cases hfP : rep.cutEdgePoint (q / 2) ∈ (L.pathDrawing 0).E
  · exact rep.path_edge_isLink hG hθ hD hBd hstrip F hFU hFV hEdges hdm hfP hu hw
  · have hlink := rep.off_edge_isLink hG hθ hD hBd hstrip hU₁ hU₂ hU h₁ h₂ hR hccw hrot heI heO hV F
      hFU hFV hEdges hdm hfP hu hw
    have hfG : rep.cutEdgePoint (q / 2) ∈ G.E := by
      have hqf := mem_flatten_of_mem_getD hu
      obtain ⟨-, hb, -, -, -⟩ := rep.cut_data_face_encoding hG (List.range x.vertexCount)
      have hact : q ∈ (gm06CutDataOfLinkage x.vertexCount rep.tagged.length x.endpoints x.linkage
          x.innerCuff x.outerCuff x.rotations (List.range x.vertexCount)).activeDarts := by
        refine (gm06CutDataOfLinkage_active_iff _ _ _ _ _ _ _ _ _).mpr ⟨?_, hqf⟩
        rw [rep.cuff_lengths.1, rep.cuff_lengths.2]
        have := hb q hqf
        omega
      obtain ⟨u₀, w₀, -, -, hl⟩ := rep.cut_ordinary_isLink hG hact hdm
      exact hl.1
    unfold cutEdgeLab
    rw [cutEdgeLabel_off L hG _ hfG hfP]
    exact hlink

end GM06CurrentDrawingRep

end GraphMinor.GM06
