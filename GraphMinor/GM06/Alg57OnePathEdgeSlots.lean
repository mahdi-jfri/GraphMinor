module

public import GraphMinor.GM06.Alg57OnePathSlots
import GraphMinor.GM06.Section5CutStripSurface
import GraphMinor.GM06.Section5CutEdgePreimage

/-!
# The edge slots and the path of FIND_4 for one path

This file finishes the fields of `Find4Rep1` for the actual lists. An edge label `e` names the set
`cutEdgeLab e` of the cut disc. The cut face orbit of `c̄₁` meets the label `e` of a copy of an
edge of `P₁` exactly when that copy is in `cutRc` (`path_edge_orbit_iff`), and an edge off `P₁` is
met only by its left label (`off_edge_incident_iff`). With the ends of the cut edges
(`cut_edge_isLink`) this gives the edge fields. The left copy of `P₁` in the cut disc is the walk
of the left labels of `P₁` (`slots_path_walk`).
-/

@[expose] public section

namespace GraphMinor.GM06

open Set Topology Graph GraphMinor.Surface GraphMinor.GM11 GraphMinor.Compute unitInterval

/-- A walk can be moved along a map that sends links to links and vertices to vertices. -/
theorem GraphWalk.exists_map {α α' β β' : Type*} {G : Graph α β} {G' : Graph α' β'}
    (f : α → α') (g : β → β') {u v : α} (W : GraphWalk G u v)
    (hl : ∀ e x y, e ∈ W.edges → G.IsLink e x y → G'.IsLink (g e) (f x) (f y))
    (hV : ∀ x ∈ W.support, f x ∈ V(G')) :
    ∃ W' : GraphWalk G' (f u) (f v), W'.support = W.support.map f ∧
      W'.edges = W.edges.map g := by
  induction W with
  | nil h => exact ⟨.nil (hV _ (by simp)), by simp, by simp⟩
  | cons h r ih =>
    obtain ⟨W', hs, he⟩ := ih (fun e x y he hxy => hl e x y (by simp [he]) hxy)
      (fun x hx => hV x (by simp [hx]))
    exact ⟨.cons (hl _ _ _ (by simp) h) W', by simp [hs], by simp [he]⟩

variable {G : Drawing ClosedCylinder} {θ : ℝ} {D : Set (ℝ × ℝ)}

/-- A point of an edge of `P₁` is at an inner parameter, since the two ends of `P₁` are
vertices. -/
theorem path_edge_param_Ioo {L : CylinderLinkage 1 G} {f : Set ClosedCylinder}
    (hf : f ∈ (L.pathDrawing 0).E) {s : I} (hs : L.curve 0 s ∈ f) : s.1 ∈ Ioo (0 : ℝ) 1 := by
  obtain ⟨W, -, -, -⟩ := (L.isPath 0).1
  have h0 : L.curve 0 0 ∈ (L.pathDrawing 0).V := by
    rw [(L.curve_parametrizes 0).2.2.1]
    exact W.mem_vertexSet_of_mem_support W.start_mem_support
  have h1 : L.curve 0 1 ∈ (L.pathDrawing 0).V := W.mem_vertexSet_of_mem_support W.end_mem_support
  have hnot := (hf.2.1 hs).2
  refine ⟨lt_of_le_of_ne s.2.1 ?_, lt_of_le_of_ne s.2.2 ?_⟩
  · intro h
    apply hnot
    have hs0 : s = 0 := Subtype.ext h.symm
    rw [hs0]
    exact h0
  · intro h
    apply hnot
    have hs1 : s = 1 := Subtype.ext h
    rw [hs1]
    exact h1

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

/-- An edge label in range names the edge of its half. -/
theorem cutEdgePoint_of_lt {e : ℕ} (h : e / 2 < rep.tagged.length) :
    rep.cutEdgePoint e = rep.edge ⟨e / 2, h⟩ := dif_pos h

include rep in
/-- The edge of a copy of a dart of `P₁`, read on the cut orbit. A word `w` of `P₁` is read on
the orbit as the left copy of `w` or the right copy of its reverse, since the other two copies
are never on the orbit (`path_copies_not_in_orbit`). -/
theorem orbit_word_iff (hG : IsCylinderSection5Drawing 1 G) {w : ℕ}
    (hw : w ∈ x.linkage.flatten) (left : Bool) (n : ℕ) :
    gm06UncutDart (cutNext^[n] gapCut) = (if left then w else gm06DartMate w) ↔
      cutNext^[n] gapCut / 2 = 2 * (w / 2) + (!left).toNat := by
  obtain ⟨h1, h2⟩ := rep.path_copies_not_in_orbit hG hw n
  generalize cutNext^[n] gapCut = q at h1 h2 ⊢
  unfold gm06UncutDart
  unfold gm06CutDart at h1 h2
  rcases gm06DartMate_end_cases w with ⟨hw0, hm⟩ | ⟨hw1, hm⟩ <;> cases left <;>
    simp only [hm, Bool.false_eq_true, ite_true, ite_false, Bool.not_true, Bool.not_false,
      Bool.toNat_true, Bool.toNat_false] at h2 ⊢ <;> omega

variable (hG : IsCylinderSection5Drawing 1 G)
  (hno : ∀ (G₁ : Drawing ClosedCylinder) (L₁ : CylinderLinkage 1 G₁),
    IsCylinderSection5Drawing 1 G₁ → ¬ Section5Reduction2Step 1 G L G₁ L₁) (hθ : L.HasTheta θ)
  (hD : IsClosedDisc D) (hBd : discBd D = liftedStripBoundary hG.1 L 1)
  (hstrip : D ⊆ {p : ℝ × ℝ | 1 ≤ p.1 ∧ p.1 ≤ 2})

include hno hθ hD hBd hstrip in
/-- **The incidence of a copy of an edge of `P₁`.** Let `w` be a word of `P₁`. The copy on the
side `left` of its edge is in `cutRc` exactly when the cut face orbit of `c̄₁` has a dart with the
edge label of that copy. -/
theorem path_edge_orbit_iff {w : ℕ} (hw : w ∈ x.linkage.flatten) (left : Bool) :
    cutEdgeLabel L hG left (rep.edge ⟨w / 2, by have := rep.path_word_lt hw; omega⟩) ⊆
        cutRc G D ↔
      ∃ n, cutNext^[n] gapCut / 2 = 2 * (w / 2) + (!left).toNat := by
  have hwlt := rep.path_word_lt hw
  obtain ⟨c, τ, τ', hlt, hcl, hcv, hcf, hcX, -, -⟩ := rep.path_word_dart hw
  have hce := rep.dart_edge_of_label hG hcl hwlt
  have hjP := rep.path_word_edge (rep.mem_linkage_zero_of_flatten hw) hwlt
  set f := rep.edge ⟨w / 2, by omega⟩ with hf
  have hfU : f ⊆ (L.pathDrawing 0).U := fun c hc => (hjP.2.1 hc).1
  have hsp : ∀ s : I, spherePath L s.1 = cylinderToSphere (L.curve 0 s) := fun s =>
    spherePath_of_mem L s.2
  -- at every point of the edge, the side condition is the same orbit condition
  have hpt : ∀ s : I, L.curve 0 s ∈ f →
      (cutSidePoint L hG hBd left s ∈ cutRc G D ↔
        ∃ n, gm06UncutDart (cutNext^[n] gapCut) = if left then w else gm06DartMate w) := by
    intro s hs
    have hsI := path_edge_param_Ioo hjP hs
    have hsd : spherePath L s.1 ∈ c.1.1 := by
      rw [hce, hsp s]
      exact mem_image_of_mem _ hs
    obtain ⟨h1, h2⟩ := rep.one_path_edge_copy_iff_red2 hG hno hθ hD hBd hstrip hsI hcX τ.2 τ'.2
      hlt (by rw [hcv, hsp τ]) (by rw [hcf, hsp τ']) hsd
    rw [cutSidePoint_mem_cutRc_iff]
    cases left
    · simpa [hcl] using h2
    · simpa [hcl] using h1
  have horbit : (∃ n, gm06UncutDart (cutNext^[n] gapCut) = if left then w else gm06DartMate w) ↔
      ∃ n, cutNext^[n] gapCut / 2 = 2 * (w / 2) + (!left).toNat :=
    exists_congr fun n => rep.orbit_word_iff hG hw left n
  rw [← horbit, cutEdgeLabel_path_eq L hG hθ hD hBd hstrip left hfU]
  constructor
  · intro h
    obtain ⟨z, hz⟩ := hjP.2.2.1.nonempty
    have hzP := hfU hz
    rw [← (L.curve_parametrizes 0).2.1] at hzP
    obtain ⟨s, rfl⟩ := hzP
    exact (hpt s hz).mp (h ⟨s, hz, rfl⟩)
  · rintro h _ ⟨s, hs, rfl⟩
    exact (hpt s hs).mpr h

include hG in
/-- An ordinary dart on the cut orbit is a dart of an active edge. -/
theorem cut_dart_active {q : ℕ} (hq : q ∈ (currentCut).activeDarts)
    (hd : gm06UncutDart q < 2 * rep.tagged.length) :
    (rep.tagged[(⟨gm06UncutDart q / 2, by omega⟩ : Fin rep.tagged.length)]).2 = 1 := by
  obtain ⟨a, -, -, d, -, hl⟩ := rep.cut_origin_point (List.range x.vertexCount) hq
  let f : (cylinderSphereDrawing rep.cuffed).E := ⟨d.val.1, d.property⟩
  have hcode : 2 * rep.label f + d.val.2.toNat = gm06UncutDart q := hl
  have hb : d.val.2.toNat ≤ 1 := by cases d.val.2 <;> decide
  obtain ⟨j, hj, -, hlj⟩ := rep.ordinary_of_label_lt hG f (by omega)
  have he : (⟨gm06UncutDart q / 2, by omega⟩ : Fin rep.tagged.length) = j :=
    Fin.ext (show gm06UncutDart q / 2 = j.val by omega)
  exact (congrArg (fun i : Fin rep.tagged.length => (rep.tagged[i]).2) he).trans hj

include hθ hD hBd hstrip in
/-- The points of the cut disc named by an edge label lie over the whole edge. -/
theorem image_cutEdgeLabel (left : Bool) (f : Set ClosedCylinder) :
    cutProj D '' cutEdgeLabel L hG left f = f := by
  ext z
  constructor
  · rintro ⟨p, ⟨hpf, -⟩, rfl⟩
    exact hpf
  · intro hz
    by_cases hP : z ∈ (L.pathDrawing 0).U
    · rw [← (L.curve_parametrizes 0).2.1] at hP
      obtain ⟨t, rfl⟩ := hP
      refine ⟨cutSidePoint L hG hBd left t, ⟨?_, cutSidePoint_notMem_other L hG hBd left t⟩,
        cutProj_cutSidePoint L hG hBd left t⟩
      change cutProj D (cutSidePoint L hG hBd left t) ∈ f
      rw [cutProj_cutSidePoint]
      exact hz
    · obtain ⟨p, hp⟩ := surjective_single_strip_projection L hG hθ hD hBd hstrip z
      have hp' : cutProj D p = z := hp
      refine ⟨p, ⟨?_, fun hs => hP (hp' ▸ cutProj_mem_path_of_mem_side L hG hs)⟩, hp'⟩
      change cutProj D p ∈ f
      rw [hp']
      exact hz

include hno hθ hD hBd hstrip in
/-- **An edge label on the orbit names a set in `cutRc`.** -/
theorem orbit_edge_subset (row : List ℕ) (horbit : ∀ q, q ∈ row ↔ ∃ n, cutNext^[n] gapCut = q)
    {q : ℕ} (hq : q ∈ row) (hd : gm06UncutDart q < 2 * rep.tagged.length) :
    rep.cutEdgeLab hG (q / 2) ⊆ cutRc G D := by
  obtain ⟨n, hn⟩ := (horbit q).mp hq
  have hact := rep.cut_face_row_active hG (List.range x.vertexCount) 0 horbit q hq
  have hj := rep.cut_dart_active hG hact hd
  have hhalf : q / 2 / 2 = gm06UncutDart q / 2 := by unfold gm06UncutDart; omega
  have hpt : rep.cutEdgePoint (q / 2) = rep.edge ⟨gm06UncutDart q / 2, by omega⟩ := by
    rw [rep.cutEdgePoint_of_lt (by omega)]
    exact congrArg rep.edge (Fin.ext hhalf)
  unfold cutEdgeLab
  rw [hpt]
  by_cases hjP : rep.edge ⟨gm06UncutDart q / 2, by omega⟩ ∈ (L.pathDrawing 0).E
  · have hw : ∃ w ∈ x.linkage.flatten, w / 2 = gm06UncutDart q / 2 := by
      rcases rep.path_word_of_edge hd hj hjP with h | h
      · exact ⟨_, h, rfl⟩
      · exact ⟨_, h, gm06DartMate_edge _⟩
    obtain ⟨w, hw, hwq⟩ := hw
    have he : rep.edge ⟨gm06UncutDart q / 2, by omega⟩ =
        rep.edge ⟨w / 2, by have := rep.path_word_lt hw; omega⟩ :=
      congrArg rep.edge (Fin.ext hwq.symm)
    rw [he]
    apply (rep.path_edge_orbit_iff hG hno hθ hD hBd hstrip hw _).mpr
    refine ⟨n, ?_⟩
    rw [hn]
    by_cases h0 : q / 2 % 2 = 0 <;> simp [h0] <;> omega
  · have hfG : rep.edge ⟨gm06UncutDart q / 2, by omega⟩ ∈ G.E := (rep.links _ hj).1
    rw [cutEdgeLabel_off L hG _ hfG hjP]
    obtain ⟨h1, h2⟩ := rep.off_edge_incident_iff hG hno hθ hD hBd hstrip _ hj hjP
    by_cases h0 : q / 2 % 2 = 0
    · apply h1.mp
      refine ⟨n, ?_⟩
      rw [hn]
      simp only
      omega
    · exfalso
      apply h2
      refine ⟨n, ?_⟩
      rw [hn]
      simp only
      omega

section Ends

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

include hθ hD hstrip hU₁ hU₂ hU h₁ h₂ hR hccw hrot heI heO hV hFU hFV hEdges in
/-- **The ends of an edge label on the orbit.** For an ordinary dart `q` on the cut orbit, the
candidate ends of the label `q / 2` are two incident slots, and in `F` the set of the label joins
their labels. -/
theorem orbit_edge_data (row : List ℕ) (horbit : ∀ q, q ∈ row ↔ ∃ n, cutNext^[n] gapCut = q)
    {q : ℕ} (hq : q ∈ row) (hd : gm06UncutDart q < 2 * rep.tagged.length) :
    ∃ u w : Fin (2 * x.vertexCount),
      (gm06CandidateEnds (2 * (rep.tagged.length + (1 + 1))) (currentCut).origins)[q / 2]?.getD
        (0, 0) = (u.val, w.val) ∧
      F.toGraph.IsLink (rep.cutEdgeLab hG (q / 2)) (rep.cutLab hG hBd u) (rep.cutLab hG hBd w) ∧
      (gm06IncV (2 * x.vertexCount) (currentCut).origins row)[u.val]?.getD 0 ≠ 0 ∧
      (gm06IncV (2 * x.vertexCount) (currentCut).origins row)[w.val]?.getD 0 ≠ 0 := by
  have hact := rep.cut_face_row_active hG (List.range x.vertexCount) 0 horbit q hq
  have hmate := (rep.cut_data_face_encoding hG (List.range x.vertexCount)).2.2.2.2 q hact
  let u : Fin (2 * x.vertexCount) := ⟨(currentCut).origins[q]?.getD 0,
    (rep.cut_origins_valid q hact).1⟩
  let w : Fin (2 * x.vertexCount) := ⟨(currentCut).origins[gm06DartMate q]?.getD 0,
    (rep.cut_origins_valid _ hmate).1⟩
  have hu : q ∈ (splitRows).getD u.val [] := rep.cut_active_origin_row hact
  have hw : gm06DartMate q ∈ (splitRows).getD w.val [] := rep.cut_active_origin_row hmate
  have hlink := rep.cut_edge_isLink hG hθ hD hBd hstrip hU₁ hU₂ hU h₁ h₂ hR hccw hrot heI heO hV F
    hFU hFV hEdges hd hu hw
  have hui := (incV_getD_ne_zero_iff _ _ _ u).mpr ⟨q, hq, rfl⟩
  have hwi := rep.selected_face_head_inc hG 0 row horbit hq w rfl
  have hbound := ((gm06CutDataOfLinkage_active_iff _ _ _ _ _ _ _ _ _).mp hact).1
  rw [rep.cuff_lengths.1, rep.cuff_lengths.2] at hbound
  have he : q / 2 < 2 * (rep.tagged.length + (1 + 1)) := by omega
  rw [gm06CandidateEnds_get _ he]
  rcases gm06DartMate_end_cases q with ⟨hpos, hneg⟩ | ⟨hneg, hpos⟩
  · refine ⟨u, w, ?_, hlink, hui, hwi⟩
    apply Prod.ext
    · change (currentCut).origins[2 * (q / 2)]?.getD 0 = (currentCut).origins[q]?.getD 0
      rw [← hpos]
    · change (currentCut).origins[2 * (q / 2) + 1]?.getD 0 =
        (currentCut).origins[gm06DartMate q]?.getD 0
      rw [hneg]
  · refine ⟨w, u, ?_, hlink.symm, hwi, hui⟩
    apply Prod.ext
    · change (currentCut).origins[2 * (q / 2)]?.getD 0 =
        (currentCut).origins[gm06DartMate q]?.getD 0
      rw [hpos]
    · change (currentCut).origins[2 * (q / 2) + 1]?.getD 0 = (currentCut).origins[q]?.getD 0
      rw [← hneg]

include hno hθ hD hstrip hU₁ hU₂ hU h₁ h₂ hR hccw hrot heI heO hV hFU hFV hEdges in
/-- **Soundness of the edge bits.** An ordinary incident edge label has candidate ends, names a
set in `cutRc` over an edge of `G`, and in `F` this set joins the labels of the ends. -/
theorem slots_edge_sound (row : List ℕ) (horbit : ∀ q, q ∈ row ↔ ∃ n, cutNext^[n] gapCut = q)
    (e : ℕ) (hord : (gm06CutOrdinaryFlags rep.tagged.length 1)[e]?.getD false = true)
    (hinc : (gm06IncE (2 * (rep.tagged.length + (1 + 1))) row)[e]?.getD 0 ≠ 0) :
    ∃ u w : Fin (2 * x.vertexCount),
      (gm06CandidateEnds (2 * (rep.tagged.length + (1 + 1))) (currentCut).origins)[e]?.getD
        (0, 0) = (u.val, w.val) ∧
      rep.cutEdgeLab hG e ⊆ cutRc G D ∧ rep.cutEdgeLab hG e ∈ cutEok G D ∧
      F.toGraph.IsLink (rep.cutEdgeLab hG e) (rep.cutLab hG hBd u) (rep.cutLab hG hBd w) := by
  obtain ⟨-, q, hq, rfl⟩ := (incE_getD_ne_zero_iff _ _ _).mp hinc
  have heord := (cutOrdinaryFlags_get _ _ _).mp hord
  have hd : gm06UncutDart q < 2 * rep.tagged.length := by unfold gm06UncutDart; omega
  obtain ⟨u, w, hends, hlink, -, -⟩ := rep.orbit_edge_data hG hθ hD hBd hstrip hU₁ hU₂ hU h₁ h₂
    hR hccw hrot heI heO hV F hFU hFV hEdges row horbit hq hd
  refine ⟨u, w, hends, rep.orbit_edge_subset hG hno hθ hD hBd hstrip row horbit hq hd, ?_, hlink⟩
  have hact := rep.cut_face_row_active hG (List.range x.vertexCount) 0 horbit q hq
  obtain ⟨_, _, -, -, hl⟩ := rep.cut_ordinary_isLink hG hact hd
  change cutProj D '' rep.cutEdgeLab hG (q / 2) ∈ G.E
  unfold cutEdgeLab
  rw [image_cutEdgeLabel hG hθ hD hBd hstrip]
  exact hl.1

include hno hθ hD hBd hstrip hFU hFV hEdges in
/-- **Every edge of `F` in `cutRc` over an edge of `G` is named on the orbit.** -/
theorem orbit_label_of_edge (row : List ℕ) (horbit : ∀ q, q ∈ row ↔ ∃ n, cutNext^[n] gapCut = q)
    {f : Set D} (hfF : f ∈ F.E) (hfR : f ⊆ cutRc G D) (hfE : f ∈ cutEok G D) :
    ∃ q ∈ row, gm06UncutDart q < 2 * rep.tagged.length ∧ rep.cutEdgeLab hG (q / 2) = f := by
  rcases hEdges f hfF with hbd | ⟨g, ⟨hgG, hgP⟩, rfl⟩
  · -- an edge in the boundary circle is the copy of an edge of `P₁`
    have hgG : cutProj D '' f ∈ G.E := hfE
    set g := cutProj D '' f with hg
    obtain ⟨z, hz⟩ := hfF.2.2.1.nonempty
    have hzg : cutProj D z ∈ g := ⟨z, hz, rfl⟩
    have hzbd := hbd hz
    rw [← preimage_boundary_union_path_single_strip L hG hθ hD hBd hstrip] at hzbd
    rcases hzbd with hcuff | hzP
    · exact absurd (hG.2.1 ⟨hcuff, (hgG.2.1 hzg).1⟩) (hgG.2.1 hzg).2
    have hzPV : cutProj D z ∉ (L.pathDrawing 0).V := fun h =>
      (hgG.2.1 hzg).2 ((L.isSubdrawing 0).1.1 h)
    obtain ⟨g', hg', hzg'⟩ := (L.pathDrawing 0).exists_edge_of_mem hzP hzPV
    have hgg : g = g' := G.edge_eq_of_mem hgG ((L.isSubdrawing 0).1.2 hg') hzg hzg'
    rw [← hgg] at hg'
    have hzP' := hzP
    rw [← (L.curve_parametrizes 0).2.1] at hzP'
    obtain ⟨t, ht⟩ := hzP'
    have hside : ∃ left : Bool, z = cutSidePoint L hG hBd left t := by
      rcases eq_lift_of_proj_eq_curve L hG hθ hD hBd hstrip z.2 ht.symm with h | h
      · exact ⟨true, Subtype.ext h⟩
      · exact ⟨false, Subtype.ext h⟩
    obtain ⟨left, hzl⟩ := hside
    have hcopy := cutEdgeLabel_path_mem_E L hG hθ hD hBd hstrip F hFU hFV hEdges left hg'
    have hzc : z ∈ cutEdgeLabel L hG left g := by
      refine ⟨hzg, ?_⟩
      rw [hzl]
      exact cutSidePoint_notMem_other L hG hBd left t
    have hfc : f = cutEdgeLabel L hG left g := F.edge_eq_of_mem hfF hcopy hz hzc
    obtain ⟨j, hj, hjg⟩ := rep.edge_cover g hgG
    have hj2 : (⟨2 * j.val / 2, by omega⟩ : Fin rep.tagged.length) = j :=
      Fin.ext (show 2 * j.val / 2 = j.val by omega)
    have hwP : ∃ w ∈ x.linkage.flatten, w / 2 = j.val := by
      have hact : (rep.tagged[2 * j.val / 2]'(by omega)).2 = 1 := by
        have h2 : 2 * j.val / 2 = j.val := by omega
        simp only [h2]
        exact hj
      have hjP : rep.edge ⟨2 * j.val / 2, by omega⟩ ∈ (L.pathDrawing 0).E := by
        rw [hj2, hjg]
        exact hg'
      rcases rep.path_word_of_edge (by omega) hact hjP with h | h
      · exact ⟨_, h, by omega⟩
      · exact ⟨_, h, by rw [gm06DartMate_edge]; omega⟩
    obtain ⟨w, hw, hwj⟩ := hwP
    have hwe : rep.edge ⟨w / 2, by have := rep.path_word_lt hw; omega⟩ = g := by
      rw [← hjg]
      exact congrArg rep.edge (Fin.ext hwj)
    have hsub : cutEdgeLabel L hG left
        (rep.edge ⟨w / 2, by have := rep.path_word_lt hw; omega⟩) ⊆ cutRc G D := by
      rw [hwe, ← hfc]
      exact hfR
    obtain ⟨n, hn⟩ := (rep.path_edge_orbit_iff hG hno hθ hD hBd hstrip hw left).mp hsub
    have hl1 : (!left).toNat ≤ 1 := by cases left <;> decide
    have hwlt := rep.path_word_lt hw
    refine ⟨cutNext^[n] gapCut, (horbit _).mpr ⟨n, rfl⟩, ?_, ?_⟩
    · unfold gm06UncutDart
      omega
    · unfold cutEdgeLab
      have hpar : decide (cutNext^[n] gapCut / 2 % 2 = 0) = left := by
        rw [hn]
        cases left <;> simp <;> omega
      rw [hpar, hfc, rep.cutEdgePoint_of_lt (by omega), ← hwe]
      exact congrArg (fun i => cutEdgeLabel L hG left (rep.edge i))
        (Fin.ext (show cutNext^[n] gapCut / 2 / 2 = w / 2 by omega))
  · -- an edge off `P₁`
    obtain ⟨j, hj, rfl⟩ := rep.edge_cover g hgG
    obtain ⟨h1, -⟩ := rep.off_edge_incident_iff hG hno hθ hD hBd hstrip j hj hgP
    obtain ⟨n, hn⟩ := h1.mpr hfR
    refine ⟨cutNext^[n] gapCut, (horbit _).mpr ⟨n, rfl⟩, ?_, ?_⟩
    · unfold gm06UncutDart
      omega
    · unfold cutEdgeLab
      have hpar : decide (cutNext^[n] gapCut / 2 % 2 = 0) = true := by
        rw [hn]
        simp
      rw [hpar, rep.cutEdgePoint_of_lt (by omega)]
      have he : (⟨cutNext^[n] gapCut / 2 / 2, by omega⟩ : Fin rep.tagged.length) = j :=
        Fin.ext (show cutNext^[n] gapCut / 2 / 2 = j.val by omega)
      rw [he, cutEdgeLabel_off L hG _ (rep.links j hj).1 hgP]
      rfl

include hno hθ hD hstrip hU₁ hU₂ hU h₁ h₂ hR hccw hrot heI heO hV hFU hFV hEdges in
/-- **Cover by the edge bits.** Every edge of `F` in `cutRc` over an edge of `G` is named by an
ordinary incident edge label, whose candidate ends are incident slots labelled by the ends of the
edge. -/
theorem slots_edge_cover (row : List ℕ) (horbit : ∀ q, q ∈ row ↔ ∃ n, cutNext^[n] gapCut = q)
    (f : Set D) (a b : D) (hf : F.toGraph.IsLink f a b) (hfR : f ⊆ cutRc G D)
    (hfE : f ∈ cutEok G D) :
    ∃ e < (gm06CandidateEnds (2 * (rep.tagged.length + (1 + 1))) (currentCut).origins).length,
      (gm06CutOrdinaryFlags rep.tagged.length 1)[e]?.getD false = true ∧
      (gm06IncE (2 * (rep.tagged.length + (1 + 1))) row)[e]?.getD 0 ≠ 0 ∧
      rep.cutEdgeLab hG e = f ∧
      ∃ u w : Fin (2 * x.vertexCount),
        (gm06CandidateEnds (2 * (rep.tagged.length + (1 + 1))) (currentCut).origins)[e]?.getD
          (0, 0) = (u.val, w.val) ∧
        (gm06IncV (2 * x.vertexCount) (currentCut).origins row)[u.val]?.getD 0 ≠ 0 ∧
        (gm06IncV (2 * x.vertexCount) (currentCut).origins row)[w.val]?.getD 0 ≠ 0 ∧
        ((rep.cutLab hG hBd u = a ∧ rep.cutLab hG hBd w = b) ∨
          (rep.cutLab hG hBd u = b ∧ rep.cutLab hG hBd w = a)) := by
  obtain ⟨q, hq, hd, hqf⟩ := rep.orbit_label_of_edge hG hno hθ hD hBd hstrip F hFU hFV hEdges row
    horbit hf.1 hfR hfE
  have hact := rep.cut_face_row_active hG (List.range x.vertexCount) 0 horbit q hq
  have hbound := ((gm06CutDataOfLinkage_active_iff _ _ _ _ _ _ _ _ _).mp hact).1
  rw [rep.cuff_lengths.1, rep.cuff_lengths.2] at hbound
  have he : q / 2 < 2 * (rep.tagged.length + (1 + 1)) := by omega
  have hord : (gm06CutOrdinaryFlags rep.tagged.length 1)[q / 2]?.getD false = true :=
    (cutOrdinaryFlags_get _ _ _).mpr (by unfold gm06UncutDart at hd; omega)
  have hinc := (incE_getD_ne_zero_iff (2 * (rep.tagged.length + (1 + 1))) row (q / 2)).mpr
    ⟨he, q, hq, rfl⟩
  obtain ⟨u, w, hends, hlink, hui, hwi⟩ := rep.orbit_edge_data hG hθ hD hBd hstrip hU₁ hU₂ hU h₁
    h₂ hR hccw hrot heI heO hV F hFU hFV hEdges row horbit hq hd
  rw [hqf] at hlink
  refine ⟨q / 2, by rw [gm06CandidateEnds_length]; exact he, hord, hinc, hqf, u, w, hends, hui,
    hwi, ?_⟩
  exact pair_eq_pair_iff.mp (hlink.2.2.2.symm.trans hf.2.2.2)

end Ends

include hno hθ hD hBd hstrip in
/-- **Incidence along the left copy of `P₁`, for edges.** For a step of the left copy of `P₁`,
the edge bit is set exactly when the copy of the edge is in `cutRc`. -/
theorem slots_path_incE (hn : 0 < x.vertexCount) (row : List ℕ)
    (horbit : ∀ q, q ∈ row ↔ ∃ n, cutNext^[n] gapCut = q) (st : ℕ × Fin (2 * x.vertexCount))
    (hst : st ∈ gm06CutPathSteps x.vertexCount hn x.endpoints
      (x.linkage[0]'(by rw [rep.linkage.1]; exact one_pos)) true) :
    (gm06IncE (2 * (rep.tagged.length + (1 + 1))) row)[st.1]?.getD 0 ≠ 0 ↔
      rep.cutEdgeLab hG st.1 ⊆ cutRc G D := by
  rw [gm06CutPathSteps] at hst
  obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hst
  have hdflat : d ∈ x.linkage.flatten := List.mem_flatten.mpr ⟨_, List.getElem_mem _, hd⟩
  have hdb := rep.path_word_lt hdflat
  have hde : gm06CutDart d (!true).toNat / 2 = 2 * (d / 2) := by
    simp only [Bool.not_true, Bool.toNat_false]
    unfold gm06CutDart
    omega
  dsimp only
  rw [hde]
  have hlab : rep.cutEdgeLab (D := D) hG (2 * (d / 2)) =
      cutEdgeLabel (D := D) L hG true (rep.edge ⟨d / 2, by omega⟩) := by
    unfold cutEdgeLab
    rw [rep.cutEdgePoint_of_lt (by omega)]
    congr 1
    · simp
    · exact congrArg rep.edge (Fin.ext (show 2 * (d / 2) / 2 = d / 2 by omega))
  rw [hlab, rep.path_edge_orbit_iff hG hno hθ hD hBd hstrip hdflat true, incE_getD_ne_zero_iff]
  simp only [Bool.not_true, Bool.toNat_false, add_zero]
  constructor
  · rintro ⟨-, q, hq, hqe⟩
    obtain ⟨n, rfl⟩ := (horbit q).mp hq
    exact ⟨n, hqe⟩
  · rintro ⟨n, hn⟩
    exact ⟨by omega, _, (horbit _).mpr ⟨n, rfl⟩, hn⟩

/-- The edges of a walk of a drawing are edges of the drawing. -/
theorem walk_edge_mem {S : Type*} [TopologicalSpace S] {Γ : Drawing S} {u v : S}
    (W : GraphWalk Γ.toGraph u v) {e : Set S} (he : e ∈ W.edges) : e ∈ Γ.E := by
  induction W with
  | nil h => simp at he
  | cons h r ih =>
    simp only [GraphWalk.edges_cons, List.mem_cons] at he
    rcases he with rfl | he
    · exact h.1
    · exact ih he

include hθ hD hBd hstrip in
/-- **The left copy of `P₁` is the walk of the left labels.** The copy `cutSide L hG F 1` of `P₁`
is a simple walk from `cutLiftCurve 0` to `cutLiftCurve 1` whose vertices are the labels of the
left path slots and whose edges are the sets of the left path steps. -/
theorem slots_path_walk (hn : 0 < x.vertexCount) (F : Drawing D)
    (hFU : F.U = (fun p : D => radialCylinderProjection p.1) ⁻¹' G.U ∪ bd D)
    (hFV : F.V = (fun p : D => radialCylinderProjection p.1) ⁻¹' G.V)
    (hEdges : ∀ ec ∈ F.E, ec ⊆ bd D ∨
      ∃ e ∈ G.E \ (L.pathDrawing 0).E, ec = (fun p : D => radialCylinderProjection p.1) ⁻¹' e) :
    ∃ W : GraphWalk (cutSide L hG F 1).toGraph (cutLiftCurve L hG hBd 0) (cutLiftCurve L hG hBd 1),
      W.IsSimple ∧ (cutSide L hG F 1).V = {z | z ∈ W.support} ∧
      W.support = (gm06CutPathLabels x.vertexCount hn x.endpoints
        (x.linkage[0]'(by rw [rep.linkage.1]; exact one_pos)) (rep.source 0).val true).map
          (rep.cutLab hG hBd) ∧
      W.edges = (gm06CutPathSteps x.vertexCount hn x.endpoints
        (x.linkage[0]'(by rw [rep.linkage.1]; exact one_pos)) true).map
          (fun st => rep.cutEdgeLab hG st.1) := by
  obtain ⟨W, hWs, hWV, hsupp, hedges⟩ := rep.computed_path_walk hn 0 true
  set p₀ := cutSidePoint L hG hBd true 0
  have hPG := (L.isSubdrawing 0).1
  have hφ : ∀ t : I, cutPointLabel L hG p₀ true (L.curve 0 t) = cutSidePoint L hG hBd true t :=
    fun t => cutPointLabel_curve L hG hθ hD hBd hstrip p₀ true t
  have hproj : ∀ c, cutProj D (cutPointLabel L hG p₀ true c) = c :=
    fun c => cutProj_cutPointLabel L hG hθ hD hBd hstrip p₀ true c
  have hside1 : ∀ t : I, cutSidePoint L hG hBd true t ∈ cutSideSet L hG D 1 := fun t => ⟨t, rfl⟩
  have hcurve : ∀ c ∈ (L.pathDrawing 0).U, ∃ t : I, L.curve 0 t = c := by
    intro c hc
    rw [← (L.curve_parametrizes 0).2.1] at hc
    exact hc
  obtain ⟨W₁, hs₁, he₁⟩ := GraphWalk.exists_map (cutPointLabel L hG p₀ true)
    (cutEdgeLabel L hG true) W
    (fun e a b _ hl => by
      obtain ⟨s, rfl⟩ := hcurve a ((L.pathDrawing 0).V_subset_U hl.2.1)
      obtain ⟨s', rfl⟩ := hcurve b ((L.pathDrawing 0).V_subset_U hl.2.2.1)
      rw [hφ, hφ]
      exact cutEdgeLabel_path_isLink L hG hθ hD hBd hstrip F hFU hFV hEdges true hl.1
        ((hPG.isLink_iff hl.1).mp hl))
    (fun c hc => by
      have hcV : c ∈ (L.pathDrawing 0).V := W.mem_vertexSet_of_mem_support hc
      change _ ∈ F.V
      rw [hFV]
      change cutProj D _ ∈ G.V
      rw [hproj]
      exact hPG.1 hcV)
  have hsub := wholeSubdrawing_isSubdrawing F (cutSideSet L hG D 1)
  obtain ⟨hV1, -⟩ := cutSide_V_U L hG hθ hD hBd hstrip F hFU hFV hEdges (m := 1) (n := 2)
    (Or.inl ⟨rfl, rfl⟩)
  have hmemV : ∀ z, z ∈ W₁.support ↔ z ∈ (cutSide L hG F 1).V := by
    intro z
    rw [hs₁, hV1, List.mem_map]
    constructor
    · rintro ⟨c, hc, rfl⟩
      have hcV : c ∈ (L.pathDrawing 0).V := W.mem_vertexSet_of_mem_support hc
      obtain ⟨t, rfl⟩ := hcurve c ((L.pathDrawing 0).V_subset_U hcV)
      refine ⟨?_, by rw [hφ]; exact hside1 t⟩
      rw [hFV]
      change cutProj D _ ∈ G.V
      rw [hproj]
      exact hPG.1 hcV
    · rintro ⟨hzV, t, ht⟩
      have hz : z = cutSidePoint L hG hBd true t := Subtype.ext ht.symm
      have hzG : L.curve 0 t ∈ G.V := by
        rw [hFV] at hzV
        change cutProj D z ∈ G.V at hzV
        rwa [hz, cutProj_cutSidePoint] at hzV
      have hPV : L.curve 0 t ∈ (L.pathDrawing 0).V :=
        mem_V_of_mem_U' hPG (by rw [← (L.curve_parametrizes 0).2.1]; exact mem_range_self t) hzG
      rw [hWV] at hPV
      exact ⟨_, hPV, by rw [hφ, hz]⟩
  obtain ⟨W₂, hs₂, he₂⟩ := hsub.exists_walk_down W₁ (fun z hz => (hmemV z).mp hz)
    (fun g hg => by
      rw [he₁, List.mem_map] at hg
      obtain ⟨g', hg', rfl⟩ := hg
      have hg'P : g' ∈ (L.pathDrawing 0).E := walk_edge_mem W hg'
      change _ ∈ (wholeSubdrawing F (cutSideSet L hG D 1)).E
      rw [wholeSubdrawing, Drawing.span_E]
      refine ⟨⟨cutEdgeLabel_path_mem_E L hG hθ hD hBd hstrip F hFU hFV hEdges true hg'P, ?_⟩,
        cutEdgeLabel_path_mem_E L hG hθ hD hBd hstrip F hFU hFV hEdges true hg'P⟩
      rw [cutEdgeLabel_path_eq L hG hθ hD hBd hstrip true (fun c hc => (hg'P.2.1 hc).1)]
      rintro _ ⟨t, -, rfl⟩
      exact hside1 t)
  have h0 : cutPointLabel L hG p₀ true (cylinderM1Point 1 0) = cutLiftCurve L hG hBd 0 := by
    rw [← (L.curve_parametrizes 0).2.2.1, hφ]
    rfl
  have h1 : cutPointLabel L hG p₀ true (L.curve 0 1) = cutLiftCurve L hG hBd 1 := by
    rw [hφ]
    rfl
  have hinj : Function.Injective (cutPointLabel L hG p₀ true) := fun a b h => by
    rw [← hproj a, h, hproj b]
  have key : ∀ {a b : D}, a = cutLiftCurve L hG hBd 0 → b = cutLiftCurve L hG hBd 1 →
      ∀ W₂ : GraphWalk (cutSide L hG F 1).toGraph a b,
        W₂.support = W.support.map (cutPointLabel L hG p₀ true) →
        W₂.edges = W.edges.map (cutEdgeLabel L hG true) →
      ∃ W : GraphWalk (cutSide L hG F 1).toGraph (cutLiftCurve L hG hBd 0)
          (cutLiftCurve L hG hBd 1),
        W.IsSimple ∧ (cutSide L hG F 1).V = {z | z ∈ W.support} ∧
        W.support = (gm06CutPathLabels x.vertexCount hn x.endpoints
          (x.linkage[0]'(by rw [rep.linkage.1]; exact one_pos)) (rep.source 0).val true).map
            (rep.cutLab hG hBd) ∧
        W.edges = (gm06CutPathSteps x.vertexCount hn x.endpoints
          (x.linkage[0]'(by rw [rep.linkage.1]; exact one_pos)) true).map
            (fun st => rep.cutEdgeLab hG st.1) := by
    intro a b ha hb W₂ hs₂ he₂
    subst ha hb
    refine ⟨W₂, ?_, ?_, ?_, ?_⟩
    · change W₂.support.Nodup
      rw [hs₂]
      exact hWs.map hinj
    · ext z
      change _ ↔ z ∈ W₂.support
      rw [hs₂, ← hs₁]
      exact (hmemV z).symm
    · rw [hs₂, hsupp, List.map_map]
      apply List.map_congr_left
      intro u hu
      have hu0 := cutPathLabels_mod _ hn _ _ _ true hu
      simp only [Bool.not_true, Bool.toNat_false] at hu0
      change cutPointLabel L hG p₀ true (rep.cutVertexPoint u) = rep.cutLab hG hBd u
      unfold cutLab
      rw [show decide (u.val % 2 = 0) = true by simp [hu0]]
    · rw [he₂, hedges, List.map_map]
      apply List.map_congr_left
      intro st hst
      rw [gm06CutPathSteps] at hst
      obtain ⟨d, -, rfl⟩ := List.mem_map.mp hst
      have hev : decide (gm06CutDart d (!true).toNat / 2 % 2 = 0) = true := by
        simp only [Bool.not_true, Bool.toNat_false, decide_eq_true_eq]
        unfold gm06CutDart
        omega
      simp only [Function.comp_apply, cutEdgeLab, hev]
  exact key h0 h1 W₂ (hs₂.trans hs₁) (he₂.trans he₁)

end GM06CurrentDrawingRep

end GraphMinor.GM06
