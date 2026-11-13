module

public import GraphMinor.GM06.Alg57OnePathFind4
public import GraphMinor.GM06.Alg57OnePathSuccessor
public import GraphMinor.GM06.Alg57TerminalPathLink
public import GraphMinor.Compute.GM06FirstContact
public import GraphMinor.Compute.GM06LoopErasure
import GraphMinor.GM06.Section5CutPointContact
import GraphMinor.GM06.Section5CutTerminalExclusion
import GraphMinor.GM06.Section5CutProjectedPath
import GraphMinor.GM06.Section5SingleStripRightContact
import GraphMinor.GM06.Section5CutPathParameter
import GraphMinor.GM06.Section5CutInitialGap
import GraphMinor.GM06.Section5CutGapEdge
import GraphMinor.GM06.Section5BoundaryGap
import GraphMinor.GM06.Section5Red
import GraphMinor.GM06.Section5EndpointObstruction
import GraphMinor.GM06.Section4PathTools
import GraphMinor.GM11.Walks

/-!
# `TERMINAL_PATH` for one path

For `k = 1`, `TERMINAL_PATH` runs in the cut disc `D`. It follows the face walk of `c̄₁` in the cut
graph from the start `s̃` of the lift `Γ₁` to its first vertex over `P₁` other than `s̃` (a vertex
of `Γ₁` after `s̃`, or of `Γ₂`), then erases closed subwalks (`gm06TerminalTrace` and
`gm06EraseClosedSubwalks`).

* `TerminalRep1`: when the dart lists represent the cut drawing `F`.
* `terminal_path_spec_one`: the output is a path `Q` of `F` from `s̃` to a vertex `v ≠ s̃` over `P₁`,
  over the closure of the lifted region, with no other vertex over `P₁`, and with edges over edges
  of `G` (Lemma 15, the trace part).
* `exists_successor_linkage_of_terminal_path_one`: Lemmas 14, 15 and 16 for `k = 1`. When no
  reduction applies and `s₁` does not have valency one, there is a linkage of winding `θ + 1`
  whose path is the projection of `Q` followed by the tail of `P₁` after its end. The geometric
  steps are `cut_first_contact_path_point_contact` (the path meets the boundary of `D` only
  at its ends; Lemma 14 is used here), `cut_first_contact_terminal_not_initial`,
  `exists_original_path_of_cut_path_point_contact`, `exists_right_seam_parameter_of_single_strip_contact`
  (the end is on `Γ₂`, since an end on `Γ₁` would give Reduction 4; this is Lemma 2 in the lifted
  strip), and `exists_parameterized_projection_with_cover_lift`.
-/

public section

namespace GraphMinor.GM06

open Set Topology Real GraphMinor.Surface GraphMinor.GM11 GraphMinor.Compute

variable {G : Drawing ClosedCylinder} {θ : ℝ} {D : Set (ℝ × ℝ)}

/-- The targets of the one-path terminal trace: the points of the cut disc over `P₁`, except the
start `s̃`. -/
@[expose] def terminalTargets1 (L : CylinderLinkage 1 G) (D : Set (ℝ × ℝ)) (s : D) : Set D :=
  {p | cutProj D p ∈ (L.pathDrawing 0).V} \ {s}

/-- **The dart lists of `TERMINAL_PATH` represent the cut drawing** (`k = 1`). As `TerminalRep`,
with labels in the cut disc, the start `s̃`, targets `terminalTargets1`, and traced edges in the
closure of the lifted region and over edges of `G`. -/
structure TerminalRep1 (L : CylinderLinkage 1 G) (F : Drawing D) (s : D)
    (heads targets ds : List ℕ) (s₀ : ℕ) (tail : ℕ → ℕ) (lab : ℕ → D) (edgeOf : ℕ → Set D) :
    Prop where
  start_lab : lab s₀ = s
  start_tgt : targets[s₀]?.getD 0 = 0
  walk : ∃ t, GM06DartWalk tail (fun d => heads[d]?.getD 0) s₀ ds t
  contact : ∃ d ∈ ds, targets[heads[d]?.getD 0]?.getD 0 ≠ 0
  target_iff : ∀ d ∈ ds,
    (targets[heads[d]?.getD 0]?.getD 0 ≠ 0 ↔ lab (heads[d]?.getD 0) ∈ terminalTargets1 L D s)
  edge : ∀ d ∈ ds, targets[tail d]?.getD 0 = 0 →
    F.toGraph.IsLink (edgeOf d) (lab (tail d)) (lab (heads[d]?.getD 0)) ∧
      edgeOf d ⊆ cutRc G D ∧ edgeOf d ∈ cutEok G D
  inj : ∀ v ∈ gm06WalkVertices (fun d => heads[d]?.getD 0) s₀ ds,
    ∀ w ∈ gm06WalkVertices (fun d => heads[d]?.getD 0) s₀ ds, lab v = lab w → v = w

/-- **Lemma 15, the trace part** (`k = 1`). The output of `TERMINAL_PATH` is a path of the cut
drawing from `s̃` to a vertex `v ≠ s̃` over `P₁`, over the closure of the lifted region, whose other
vertices are not over `P₁`, and whose edges are over edges of `G`. -/
theorem terminal_path_spec_one {L : CylinderLinkage 1 G} {F : Drawing D} {s : D}
    (hsR : s ∈ cutRc G D)
    {heads targets ds : List ℕ} {s₀ : ℕ} {tail : ℕ → ℕ} {lab : ℕ → D} {edgeOf : ℕ → Set D}
    (rep : TerminalRep1 L F s heads targets ds s₀ tail lab edgeOf) :
    ∃ (v : D) (Q : Drawing D),
      Q.V = {x | x ∈ (gm06WalkVertices (fun d => heads[d]?.getD 0) s₀
        (gm06EraseClosedSubwalks (fun d => heads[d]?.getD 0) s₀
          (gm06TerminalTrace heads targets ds).1)).map lab} ∧
      Q.E = {e | e ∈ (gm06EraseClosedSubwalks (fun d => heads[d]?.getD 0) s₀
          (gm06TerminalTrace heads targets ds).1).map edgeOf} ∧
      IsSubpathOf F Q s v ∧ Q.U ⊆ cutRc G D ∧
      Q.V ∩ {p | cutProj D p ∈ (L.pathDrawing 0).V} ⊆ {s, v} ∧
      cutProj D v ∈ (L.pathDrawing 0).V ∧ v ≠ s ∧ ∀ e ∈ Q.E, e ∈ cutEok G D := by
  set H : ℕ → ℕ := fun d => heads[d]?.getD 0 with hH
  set trace := (gm06TerminalTrace heads targets ds).1 with htrace
  obtain ⟨hpre, hinternal, hfalse⟩ := gm06TerminalTrace_spec heads targets ds
  have hflag : (gm06TerminalTrace heads targets ds).2 = true := by
    by_contra hf
    obtain ⟨d, hd, hdt⟩ := rep.contact
    exact hdt ((hfalse.mp (Bool.eq_false_iff.mpr hf)) d hd)
  obtain ⟨dl, hlast, hstop⟩ := gm06FirstContact_last (gm06TerminalContact heads targets) ds hflag
  change trace.getLast? = some dl at hlast
  have hne : trace ≠ [] := by
    intro h; rw [h] at hlast; cases hlast
  have hdl : dl = trace.getLast hne := by
    rw [List.getLast?_eq_getLast hne] at hlast
    exact (Option.some.inj hlast).symm
  have hstop' : targets[H dl]?.getD 0 ≠ 0 := by
    simpa [gm06TerminalContact] using hstop
  have htrace_ds : ∀ d ∈ trace, d ∈ ds := fun d hd => hpre.subset hd
  obtain ⟨t, hw⟩ := rep.walk
  obtain ⟨rest, hrest⟩ := hpre
  obtain ⟨u₀, hwt⟩ : ∃ u, GM06DartWalk tail H s₀ trace u :=
    GM06DartWalk.of_append (hrest ▸ hw)
  have hu₀ : u₀ = H dl := by rw [GM06DartWalk.end_eq hwt hne, hdl]
  subst hu₀
  have htails : ∀ d ∈ trace, targets[tail d]?.getD 0 = 0 := by
    intro d hd
    rcases List.mem_cons.mp (GM06DartWalk.tail_mem hwt d hd) with h | h
    · rw [h]; exact rep.start_tgt
    · obtain ⟨d', hd', hdd⟩ := List.mem_map.mp h
      rw [← hdd]
      exact hinternal d' hd'
  have hedge : ∀ d ∈ trace, F.toGraph.IsLink (edgeOf d) (lab (tail d)) (lab (H d)) ∧
      edgeOf d ⊆ cutRc G D ∧ edgeOf d ∈ cutEok G D := fun d hd =>
    rep.edge d (htrace_ds d hd) (htails d hd)
  obtain ⟨hwQ, hndQ, hsubQ⟩ := gm06EraseClosedSubwalks_spec hwt
  set Qd := gm06EraseClosedSubwalks H s₀ trace with hQd
  have hQd_trace : ∀ d ∈ Qd, d ∈ trace := fun d hd => hsubQ.subset hd
  have hlabu : lab (H dl) ∈ F.V := (hedge dl (by rw [hdl]; exact List.getLast_mem hne)).1.2.2.1
  obtain ⟨W, hWs, hWe⟩ : ∃ W : GraphWalk F.toGraph s (lab (H dl)),
      W.support = (gm06WalkVertices H s₀ Qd).map lab ∧ W.edges = Qd.map edgeOf := by
    rw [← rep.start_lab]
    exact GM06DartWalk.exists_graphWalk hwQ (fun d hd => (hedge d (hQd_trace d hd)).1) hlabu
  have hvert : ∀ v ∈ gm06WalkVertices H s₀ Qd, v ∈ gm06WalkVertices H s₀ ds := by
    intro v hv
    rcases List.mem_cons.mp hv with rfl | hv
    · exact List.mem_cons_self
    · obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hv
      exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨d, htrace_ds d (hQd_trace d hd), rfl⟩)
  have hWsimple : W.IsSimple := by
    unfold GraphWalk.IsSimple
    rw [hWs]
    exact hndQ.map_on (fun v hv w hw h => rep.inj v (hvert v hv) w (hvert w hw) h)
  have hdl_ds : dl ∈ ds := htrace_ds dl (by rw [hdl]; exact List.getLast_mem hne)
  have huT : lab (H dl) ∈ terminalTargets1 L D s := (rep.target_iff dl hdl_ds).mp hstop'
  have hsne : s ≠ lab (H dl) := fun h => huT.2 h.symm
  have hQsub : IsSubpathOf F (walkDrawing F W) s (lab (H dl)) :=
    ⟨walkDrawing_isSubdrawing F W, (walkDrawing_isSubdrawing F W).U_subset,
      isPathDrawing_walkDrawing_of_isSimple F hWsimple hsne⟩
  have hheadR : ∀ d ∈ trace, lab (H d) ∈ cutRc G D := by
    intro d hd
    obtain ⟨hl, hR, -⟩ := hedge d hd
    have : lab (H d) ∈ closure (edgeOf d) ∩ F.V := by
      rw [hl.2.2.2]; exact mem_insert_of_mem _ (mem_singleton _)
    exact closure_minimal hR isClosed_cutRc this.1
  have hQR : (walkDrawing F W).U ⊆ cutRc G D := by
    rw [walkDrawing_U_subset_iff F W isClosed_cutRc, hWs, hWe]
    refine ⟨fun y hy => ?_, fun e he => ?_⟩
    · obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hy
      rcases List.mem_cons.mp hv with rfl | hv
      · rw [rep.start_lab]; exact hsR
      · obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hv
        exact hheadR d (hQd_trace d hd)
    · obtain ⟨d, hd, rfl⟩ := List.mem_map.mp he
      exact (hedge d (hQd_trace d hd)).2.1
  have hint : (walkDrawing F W).V ∩ {p | cutProj D p ∈ (L.pathDrawing 0).V} ⊆
      {s, lab (H dl)} := by
    rintro x ⟨hx, hxL⟩
    rw [walkDrawing_V, mem_ofPred_eq, hWs] at hx
    obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hx
    rcases List.mem_cons.mp hv with rfl | hv
    · exact Or.inl rep.start_lab
    obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hv
    have hdt := hQd_trace d hd
    rw [← List.dropLast_append_getLast hne] at hdt
    rcases List.mem_append.mp hdt with hdrop | hlastd
    · have h0 : targets[H d]?.getD 0 = 0 := hinternal d hdrop
      by_cases hs : lab (H d) = s
      · exact Or.inl hs
      · exact absurd ((rep.target_iff d (htrace_ds d (List.mem_of_mem_dropLast hdrop))).mpr
          ⟨hxL, hs⟩) (by simpa using h0)
    · rw [List.mem_singleton.mp hlastd, ← hdl]
      exact Or.inr rfl
  have hEok : ∀ e ∈ (walkDrawing F W).E, e ∈ cutEok G D := by
    intro e he
    rw [walkDrawing_E, mem_ofPred_eq, hWe] at he
    obtain ⟨d, hd, rfl⟩ := List.mem_map.mp he
    exact (hedge d (hQd_trace d hd)).2.2
  refine ⟨lab (H dl), walkDrawing F W, ?_, ?_, hQsub, hQR, hint, huT.1, fun h => hsne h.symm,
    hEok⟩
  · rw [walkDrawing_V, hWs]
  · rw [walkDrawing_E, hWe]

/-- **Lemmas 14, 15 and 16 for `k = 1`, with the new linkage.** Suppose no reduction applies and
`s₁` does not have valency one, and the dart lists of `TERMINAL_PATH` represent the cut drawing.
Then its output path `Q`, projected to `G` and followed by the tail `T` of `P₁` after its end, is
the path of a linkage of winding `θ + 1`. -/
theorem exists_successor_linkage_of_terminal_path_one (L : CylinderLinkage 1 G)
    (hG : IsCylinderSection5Drawing 1 G) (hθ : L.HasTheta θ)
    (hno : ¬ Section5AnyReductionApplies 1 G L)
    (hval : vertexValency G.toGraph (cylinderM1Point 1 0) ≠ 1)
    (hD : IsClosedDisc D) (hBd : discBd D = liftedStripBoundary hG.1 L 1)
    (hstrip : D ⊆ {p : ℝ × ℝ | 1 ≤ p.1 ∧ p.1 ≤ 2}) (F : Drawing D)
    (hFU : F.U = (fun p : D => radialCylinderProjection p.1) ⁻¹' G.U ∪ bd D)
    (hFV : F.V = (fun p : D => radialCylinderProjection p.1) ⁻¹' G.V)
    (hEdges : ∀ ec ∈ F.E, ec ⊆ bd D ∨
      ∃ e ∈ G.E \ (L.pathDrawing 0).E, ec = (fun p : D => radialCylinderProjection p.1) ⁻¹' e)
    {s : D} (hs : s.1 = (1, 2 * π))
    {heads targets ds : List ℕ} {s₀ : ℕ} {tail : ℕ → ℕ} {lab : ℕ → D} {edgeOf : ℕ → Set D}
    (rep : TerminalRep1 L F s heads targets ds s₀ tail lab edgeOf) :
    ∃ (Q : Drawing D) (u : unitInterval) (T : Drawing ClosedCylinder) (L' : CylinderLinkage 1 G),
      Q.V = {x | x ∈ (gm06WalkVertices (fun d => heads[d]?.getD 0) s₀
        (gm06EraseClosedSubwalks (fun d => heads[d]?.getD 0) s₀
          (gm06TerminalTrace heads targets ds).1)).map lab} ∧
      Q.E = {e | e ∈ (gm06EraseClosedSubwalks (fun d => heads[d]?.getD 0) s₀
          (gm06TerminalTrace heads targets ds).1).map edgeOf} ∧
      L'.HasTheta (θ + 1) ∧
      IsSection5Tail (L.pathDrawing 0) T (L.curve 0 u) (L.curve 0 1) ∧
      (L'.pathDrawing 0).U = cutProj D '' Q.U ∪ T.U := by
  have hsf : s = cutLiftCurve L hG hBd 0 := Subtype.ext (by rw [hs, cutLiftCurve_zero])
  have hsR : s ∈ cutRc G D := by
    rw [hsf]
    exact (onePath_setting L hG hθ hD hBd hstrip F hFU hFV hEdges).2.2.2.2.1
  obtain ⟨v, Q, hQV, hQE, hQ, hQR, hcontact, hvP, hvs, hEok⟩ := terminal_path_spec_one hsR rep
  have hEdges' : ∀ ec ∈ F.E, ec ⊆ bd D ∨
      ∃ e ∈ G.E, ec = (fun p : D => radialCylinderProjection p.1) ⁻¹' e := by
    intro ec hec
    rcases hEdges ec hec with hbd | ⟨e, he, heq⟩
    · exact Or.inl hbd
    · exact Or.inr ⟨e, he.1, heq⟩
  obtain ⟨g, hgcoord, -, hgbd, hgproj⟩ := exists_single_strip_initial_gap_curve L hG hBd
  have hbdF : bd D ⊆ F.U := by rw [hFU]; exact subset_union_right
  obtain ⟨b, hb, hbBd, hgap, -⟩ :=
    exists_boundary_edge_containing_cut_initial_gap hG F hFV hbdF hEdges' g hgbd hgproj
  have hg0 : g 0 = s := Subtype.ext (by rw [hgcoord, hs]; norm_num)
  subst hg0
  -- the inner cuff edge is not over an edge of `G`
  have hbQ : b ∉ Q.E := by
    intro hbQ
    have hbE := hEok b hbQ
    let m : unitInterval := ⟨1 / 2, by norm_num, by norm_num⟩
    have hm : m ∈ Ioo (0 : unitInterval) 1 := by
      constructor
      · change (0 : ℝ) < 1 / 2
        norm_num
      · change (1 / 2 : ℝ) < 1
        norm_num
    have hmb : g m ∈ b := hgap ⟨m, hm, rfl⟩
    have hgapR := (initialCuffGapCurve_props hG 0).2.2.2.2 ⟨m, hm, rfl⟩
    have hoff : initialCuffGapCurve 1 0 m ∉ G.U :=
      (connectedComponentIn_subset _ _ hgapR).2
    apply hoff
    rw [← hgproj m]
    exact G.closure_subset_U hbE (subset_closure ⟨g m, hmb, rfl⟩)
  have hQR' : (fun p : D => planeToCylinderCover p.1) '' Q.U ⊆
      closure (cylinderCoverRegion 1 G 0) := by
    rintro _ ⟨p, hp, rfl⟩
    exact hQR hp
  obtain ⟨-, hpoint⟩ := cut_first_contact_path_point_contact L hG hθ hno hval hD hBd hstrip
    F hFU hFV hEdges g hgcoord hQ hQR' hcontact hb hbBd hgap hbQ
  have htNot := cut_first_contact_terminal_not_initial L hG hθ hno hD hBd hstrip hEdges g hgcoord
    hQ hpoint
  have hscoord : (g 0).1 = (1, 2 * π) := hs
  have hsproj : radialCylinderProjection (g 0).1 = cylinderM1Point 1 0 := by
    rw [hscoord, radialCylinderProjection_one_two_pi]
  have hends : radialCylinderProjection (g 0).1 ≠ radialCylinderProjection v.1 := by
    rw [hsproj]
    exact htNot.symm
  obtain ⟨P, hP, hPU, hPL⟩ := exists_original_path_of_cut_path_point_contact L hG hθ hD hBd hstrip
    hFV hEdges hQ hpoint hends
  rw [hsproj] at hP hPL
  obtain ⟨u, hu, huV, huEq, htΓ⟩ := exists_right_seam_parameter_of_single_strip_contact L hG hθ hno
    hval hD hBd hstrip hQ.2.2 hscoord hvP htNot hpoint hQR' hP hPU hPL
  obtain ⟨q, hq, -, hqEnd⟩ := exists_parameterized_projection_with_cover_lift L hG hθ hD hBd hstrip
    hQ.2.2 hscoord hpoint hends hPU hQR'
  have hP' : IsSubpathOf G P (cylinderM1Point 1 0) (L.curve 0 u) := by rw [huEq]; exact hP
  have hPL' : P.U ∩ (L.pathDrawing 0).U ⊆ {cylinderM1Point 1 0, L.curve 0 u} := by
    rw [huEq]; exact hPL
  have hq' : ParametrizesSet q P.U (cylinderM1Point 1 0) (L.curve 0 u) := by rw [huEq]; exact hq
  rw [htΓ] at hqEnd
  obtain ⟨T, L', hL', hT, hU⟩ := exists_successor_linkage_of_single_path_right_contact L hG hθ u hu
    huV hP' hPL' q hq' hqEnd
  exact ⟨Q, u, T, L', hQV, hQE, hL', hT, by rw [hU, hPU]; rfl⟩

end GraphMinor.GM06
