module

public import GraphMinor.GM06.Alg57OnePathEncoded
public import GraphMinor.GM06.Alg57OnePathTerminal
public import GraphMinor.GM06.Alg57CurrentTerminalTargets
import all GraphMinor.GM06.Alg57CurrentTerminalRep
import GraphMinor.GM06.Alg57CurrentCandidateRows
import GraphMinor.GM06.Alg57CurrentPathIncidence
import GraphMinor.GM06.Alg57CurrentEdgeIncidence
import GraphMinor.GM06.Alg57CurrentTerminalCuffs
import GraphMinor.GM06.Alg57TerminalFaceRows
import GraphMinor.GM06.Section4PathTools

/-!
# The arrays of `TERMINAL_PATH` for one path

For one path (`k = 1`) the terminal phase of VI (5.7), page 133, runs `TERMINAL_PATH` on the face
row of `c̄₁` in the cut drawing. Here we show that its arrays satisfy `TerminalRep1`
(`GM06CurrentDrawingRep.onePath_terminal_rep_of_row`). The labels are those of the Reduction 4
phase: a slot names the point `cutLab` of the cut disc (`cutLabN` reads it on natural numbers), and
a dart `q` names the set `cutEdgeLab (q / 2)`.

Most fields hold for any number of paths and are proved in `Alg57CurrentTerminalTargets.lean`.
Three need a new argument for one path.

* The target bit of a slot is set exactly when the slot lies over `P₁` and is not the start: the
  left list holds the left copies of the vertices of `P₁`, the right list the right copies
  (`mem_computed_path_labels_iff`), and only the start has the label `Γ₁(0)` (`slots_inj`).
* A dart of the row with an unmarked tail is an ordinary dart. The inner cuff end is not in the
  rotated row, and the tail of the outer cuff end is the left copy of `t₁`, which is marked.
* An ordinary dart of the row joins the labels of its ends in the cut drawing, by
  `slots_edge_sound`.
-/

@[expose] public section

namespace GraphMinor.GM06

open Set Topology Real GraphMinor.Surface GraphMinor.GM11 GraphMinor.Compute

variable {G : Drawing ClosedCylinder} {θ : ℝ} {D : Set (ℝ × ℝ)}

namespace GM06CurrentDrawingRep

variable {x : GM06SuccessorInput} {L : CylinderLinkage 1 G} (rep : GM06CurrentDrawingRep x G L)

/-- The label of a slot read on natural numbers: `cutLab` on slots, and `Γ₁(0)` elsewhere. -/
noncomputable def cutLabN (hG : IsCylinderSection5Drawing 1 G)
    (hBd : discBd D = liftedStripBoundary hG.1 L 1) (v : ℕ) : D :=
  if hv : v < 2 * x.vertexCount then rep.cutLab hG hBd ⟨v, hv⟩ else cutLiftCurve L hG hBd 0

theorem cutLabN_fin (hG : IsCylinderSection5Drawing 1 G)
    (hBd : discBd D = liftedStripBoundary hG.1 L 1) (v : Fin (2 * x.vertexCount)) :
    rep.cutLabN hG hBd v.val = rep.cutLab hG hBd v := by
  simp [cutLabN, v.isLt]

local notation "currentCut" => gm06CutDataOfLinkage x.vertexCount rep.tagged.length x.endpoints
  x.linkage x.innerCuff x.outerCuff x.rotations (List.range x.vertexCount)
local notation "cutNext" => Equiv.trans dartMatePerm
  (Equiv.symm (gm06RotationPermutation (GM06CutData.rotations currentCut)))
local notation "cutTables" => gm06BuildCutTables x.vertexCount rep.tagged.length x.endpoints
  x.linkage x.innerCuff x.outerCuff
local notation "cutNextS" => Equiv.trans dartMatePerm
  (Equiv.symm (gm06RotationPermutation (gm06SplitRotationRows cutTables x.rotations)))
local notation "gapCut" => gm06CutDart (2 * rep.tagged.length + 1) 0
local notation "gap0" => gm06CutDart (2 * (rep.tagged.length + Fin.val (0 : Fin 1)) + 1) 0
local notation "edgeCount" => 2 * (rep.tagged.length + (1 + 1))
local notation "heads" => gm06TerminalHeadWords edgeCount (GM06CutData.origins currentCut)
set_option quotPrecheck false in
local notation "lower" hn:arg => gm06CutPathLabels x.vertexCount hn x.endpoints
  (x.linkage[Fin.val (0 : Fin 1)]'(by rw [rep.linkage.1]; exact Fin.isLt (0 : Fin 1)))
  (Fin.val (rep.source (0 : Fin 1))) true
set_option quotPrecheck false in
local notation "upper" hn:arg => gm06CutPathLabels x.vertexCount hn x.endpoints
  (x.linkage[Fin.val (finSuccCycle (0 : Fin 1))]'(by
    rw [rep.linkage.1]; exact Fin.isLt (finSuccCycle (0 : Fin 1))))
  (Fin.val (rep.source (finSuccCycle (0 : Fin 1)))) false
local notation "targets" hn:arg => gm06TerminalTargetBits (2 * x.vertexCount)
  (gm06CutVertex (Fin.val (rep.source (0 : Fin 1))) true)
  (List.map Fin.val (lower hn)) (List.map Fin.val (upper hn))

/-- **`TerminalRep1` for the actual arrays** (`k = 1`). On the face row of the reversed inner cuff
end, when no reduction applies, the arrays of `TERMINAL_PATH` represent the cut drawing `F` with
the labels `cutLabN` and `cutEdgeLab`. Also, a dart of the rotated row with an unmarked tail is an
ordinary dart. -/
theorem onePath_terminal_rep_of_row (hn : 0 < x.vertexCount) (hG : IsCylinderSection5Drawing 1 G)
    (hno : ¬ Section5AnyReductionApplies 1 G L) (hθ : L.HasTheta θ) (hD : IsClosedDisc D)
    (hBd : discBd D = liftedStripBoundary hG.1 L 1)
    (hstrip : D ⊆ {p : ℝ × ℝ | 1 ≤ p.1 ∧ p.1 ≤ 2}) (F : Drawing D)
    (hFU : F.U = (fun p : D => radialCylinderProjection p.1) ⁻¹' G.U ∪ bd D)
    (hFV : F.V = (fun p : D => radialCylinderProjection p.1) ⁻¹' G.V)
    (hEdges : ∀ ec ∈ F.E, ec ⊆ bd D ∨
      ∃ e ∈ G.E \ (L.pathDrawing 0).E, ec = (fun p : D => radialCylinderProjection p.1) ⁻¹' e)
    (row : List ℕ) (horbit : ∀ q, q ∈ row ↔ ∃ n, cutNext^[n] gap0 = q)
    (hnd : row.Nodup) (hgap : gap0 ∈ row) (horder : ∀ q ∈ row, row.formPerm q = cutNext q) :
    (∀ q ∈ gm06TerminalFaceDarts gap0 row,
      (targets hn)[(currentCut).origins[q]?.getD 0]?.getD 0 = 0 →
        gm06UncutDart q < 2 * rep.tagged.length) ∧
    TerminalRep1 L F (cutLiftCurve L hG hBd 0) heads (targets hn) (gm06TerminalFaceDarts gap0 row)
      (gm06CutVertex (rep.source 0).val true) (fun q => (currentCut).origins[q]?.getD 0)
      (rep.cutLabN hG hBd) (fun q => rep.cutEdgeLab hG (q / 2)) := by
  classical
  have hno2 : ∀ (G₁ : Drawing ClosedCylinder) (L₁ : CylinderLinkage 1 G₁),
      IsCylinderSection5Drawing 1 G₁ → ¬ Section5Reduction2Step 1 G L G₁ L₁ :=
    fun G₁ L₁ hG₁ hRed => hno ⟨G₁, L₁, hG₁, Or.inr (Or.inl hRed)⟩
  obtain ⟨U₁, U₂, hU₁, hU₂, hU, h₁, h₂⟩ := exists_side_sets L hG
  obtain ⟨R, hR, hccw, -, hrot, heI, heO, hV, -⟩ := rep.one_path_setting_red2 hG hno2
  have hg : gap0 = gapCut := by simp
  have horbit' : ∀ q, q ∈ row ↔ ∃ n, cutNextS^[n] gapCut = q := fun q => by
    rw [← hg]; exact horbit q
  -- the start
  have hs0 : (gm06CutVertexFin x.vertexCount hn (rep.source 0).val true).val =
      gm06CutVertex (rep.source 0).val true := cutVertexFin_val hn (rep.source 0).isLt true
  have hstartLab : rep.cutLab hG hBd (gm06CutVertexFin x.vertexCount hn (rep.source 0).val true) =
      cutLiftCurve L hG hBd 0 := by
    have hpar := cutVertexFin_mod x.vertexCount hn (rep.source 0).val true
    rw [rep.cutLab_curve hG hθ hD hBd hstrip _ (t := 0)]
    · apply Subtype.ext
      rw [cutSidePoint_val, cutLiftCurve_val]
      simp [hpar]
    · rw [rep.sourceCopy_point hn 0]
      exact (L.curve_parametrizes 0).2.2.1.symm
  have hsourceLow : gm06CutVertexFin x.vertexCount hn (rep.source 0).val true ∈ lower hn := by
    simp [gm06CutPathLabels, find4PathLabels]
  -- a dart of the rotated row with an unmarked tail is ordinary
  have hord : ∀ q ∈ gm06TerminalFaceDarts gap0 row,
      (targets hn)[(currentCut).origins[q]?.getD 0]?.getD 0 = 0 →
        gm06UncutDart q < 2 * rep.tagged.length := by
    intro q hq htarget
    have hqr := terminal_row_mem hq
    have hactive := rep.cut_face_row_active hG (List.range x.vertexCount) 0 horbit q hqr
    by_contra hlarge
    rcases rep.selected_face_cuff_cases hG 0 row horbit hqr (by omega) with he | ⟨j, he⟩
    · exact (terminalFaceDarts_rotate hnd hgap).2.1 (he ▸ hq)
    have hj0 : j = 0 := Subsingleton.elim _ _
    subst hj0
    let u : Fin (2 * x.vertexCount) := ⟨(currentCut).origins[q]?.getD 0,
      (rep.cut_origins_valid q hactive).1⟩
    have hui := (incV_getD_ne_zero_iff _ _ _ u).mpr ⟨q, hqr, rfl⟩
    have hu : u.val = gm06CutVertex (rep.target 0).val true := by
      dsimp only [u]
      rw [he]
      exact rep.positive_outer_origin hG 0
    have hpoint : rep.cutVertexPoint u = cylinderM2Point 1 0 := by
      trans rep.vertex (rep.target 0)
      · apply congrArg rep.vertex
        apply Fin.ext
        change u.val / 2 = (rep.target 0).val
        rw [hu, gm06CutVertex_project]
      · exact rep.target_point 0
    obtain ⟨j', hj'⟩ := L.curve_one_surjective
      (mem_range_self 0 : cylinderM2Point 1 0 ∈ cylinderM2 1)
    have hj'0 : j' = 0 := Subsingleton.elim _ _
    subst hj'0
    have huP : rep.cutVertexPoint u ∈ (L.pathDrawing 0).V := by
      rw [hpoint, ← hj']
      exact (isPathDrawing_end_vertices (L.isPath 0)).2
    have hl := rep.selected_face_vertex_live hG 0 row horbit u hui
    have hlow : u ∈ lower hn :=
      (rep.mem_computed_path_labels_iff hn 0 true u hl).mpr ⟨huP, by simp [hu, gm06CutVertex]⟩
    have hne : u.val ≠ gm06CutVertex (rep.source 0).val true := by
      intro h
      have h1 : rep.cutVertexPoint u = cylinderM1Point 1 0 := by
        rw [← rep.sourceCopy_point hn 0]
        congr 1
        exact Fin.ext (h.trans hs0.symm)
      rw [hpoint] at h1
      have hh := congrArg (fun p : ClosedCylinder => p.val.1) h1
      norm_num [cylinderM1Point, cylinderM2Point, cylinderPoint] at hh
    exact ((terminalTargetBits_ne_zero_iff _ _ _ _ u).mpr
      (Or.inl ⟨List.mem_map_of_mem hlow, hne⟩)) htarget
  refine ⟨hord, {
    start_lab := ?_
    start_tgt := rep.terminal_source_unmarked hn 0
    walk := ⟨_, rep.current_terminal_walk hG 0 row horbit hnd hgap horder⟩
    contact := rep.current_terminal_contact hn hG 0 row horbit hnd hgap horder
    target_iff := ?_
    edge := ?_
    inj := ?_ }⟩
  · rw [← hs0, cutLabN_fin]
    exact hstartLab
  · intro q hq
    obtain ⟨u, hu, hui⟩ := rep.terminal_head_vertex hG 0 row horbit (terminal_row_mem hq)
    rw [hu, cutLabN_fin]
    have hl := rep.selected_face_vertex_live hG 0 row horbit u hui
    rw [terminalTargetBits_ne_zero_iff _ _ _ _ u, List.mem_map_of_injective Fin.val_injective,
      List.mem_map_of_injective Fin.val_injective, rep.mem_computed_path_labels_iff hn 0 true u hl,
      rep.mem_computed_path_labels_iff hn (finSuccCycle 0) false u hl]
    have hfs : finSuccCycle (0 : Fin 1) = 0 := Subsingleton.elim _ _
    rw [hfs]
    simp only [terminalTargets1, mem_sdiff, mem_ofPred_eq, mem_singleton_iff,
      rep.cutProj_cutLab hG hθ hD hBd hstrip, Bool.not_true, Bool.not_false, Bool.toNat_false,
      Bool.toNat_true]
    have hsl : rep.cutLab hG hBd u = cutLiftCurve L hG hBd 0 ↔
        u.val = gm06CutVertex (rep.source 0).val true := by
      constructor
      · intro h
        have := rep.slots_inj hG hno2 hθ hD hBd hstrip hn row horbit' u _ (Or.inl hui)
          (Or.inr hsourceLow) (h.trans hstartLab.symm)
        rw [this]
        exact hs0
      · intro h
        have hu' : u = gm06CutVertexFin x.vertexCount hn (rep.source 0).val true :=
          Fin.ext (h.trans hs0.symm)
        rw [hu']
        exact hstartLab
    have hpar := cutVertexFin_mod x.vertexCount hn (rep.source 0).val true
    rw [hs0] at hpar
    simp only [Bool.not_true, Bool.toNat_false] at hpar
    constructor
    · rintro (⟨⟨hP, -⟩, hne⟩ | ⟨hP, hodd⟩)
      · exact ⟨hP, fun h => hne (hsl.mp h)⟩
      · refine ⟨hP, fun h => ?_⟩
        have h' := hsl.mp h
        omega
    · rintro ⟨hP, hne⟩
      rcases Nat.mod_two_eq_zero_or_one u.val with h0 | h1
      · exact Or.inl ⟨⟨hP, h0⟩, fun h => hne (hsl.mpr h)⟩
      · exact Or.inr ⟨hP, h1⟩
  · intro q hq htail
    have hd := hord q hq htail
    have hqr := terminal_row_mem hq
    have hactive := rep.cut_face_row_active hG (List.range x.vertexCount) 0 horbit q hqr
    obtain ⟨_, hkeys, _, hc, _⟩ := rep.cut_data_face_encoding hG (List.range x.vertexCount)
    have hqb : q < 2 * edgeCount := hkeys q ((hc q).mp hactive)
    have hordf : (gm06CutOrdinaryFlags rep.tagged.length 1)[q / 2]?.getD false = true :=
      (cutOrdinaryFlags_get _ _ _).mpr (by unfold gm06UncutDart at hd; omega)
    have hinc : (gm06IncE edgeCount row)[q / 2]?.getD 0 ≠ 0 :=
      (incE_getD_ne_zero_iff _ _ _).mpr ⟨by omega, q, hqr, rfl⟩
    obtain ⟨u, w, hends, hsub, hok, hlink⟩ := rep.slots_edge_sound hG hno2 hθ hD hBd hstrip hU₁
      hU₂ hU h₁ h₂ hR hccw hrot heI heO hV F hFU hFV hEdges row horbit' (q / 2) hordf hinc
    refine ⟨?_, hsub, hok⟩
    rw [terminalHeadWords_get _ hqb]
    rw [gm06CandidateEnds_get _ (by omega : q / 2 < edgeCount)] at hends
    simp only [Prod.mk.injEq] at hends
    rw [← rep.cutLabN_fin hG hBd u, ← rep.cutLabN_fin hG hBd w] at hlink
    unfold gm06DartMate
    rcases Nat.mod_two_eq_zero_or_one q with hpar | hpar
    · rw [show 2 * (q / 2) = q by omega] at hends
      simp only [hpar, ↓reduceIte]
      rw [hends.1, hends.2]
      exact hlink
    · rw [show 2 * (q / 2) = q - 1 by omega, show q - 1 + 1 = q by omega] at hends
      have hodd : ¬ q % 2 = 0 := by omega
      simp only [hodd, ↓reduceIte]
      rw [hends.1, hends.2]
      exact hlink.symm
  · intro v hv w hw heq
    obtain ⟨u, hu, hui⟩ := rep.terminal_walk_vertices_inc hn hG 0 row horbit hgap hv
    obtain ⟨z, hz, hzi⟩ := rep.terminal_walk_vertices_inc hn hG 0 row horbit hgap hw
    rw [← hu, ← hz, cutLabN_fin, cutLabN_fin] at heq
    have huz := rep.slots_inj hG hno2 hθ hD hBd hstrip hn row horbit' u z (Or.inl hui)
      (Or.inl hzi) heq
    rw [← hu, ← hz, huz]

end GM06CurrentDrawingRep

end GraphMinor.GM06
