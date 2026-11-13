module

public import GraphMinor.GM06.Alg57OnePathTerminalRep
public import GraphMinor.GM06.Alg57CurrentTerminalPhase
import all GraphMinor.GM06.Alg57CurrentTerminalRep
import GraphMinor.GM06.Section5CutPointContact
import GraphMinor.GM06.Section5CutTerminalExclusion
import GraphMinor.GM06.Section5CutProjectedPath
import GraphMinor.GM06.Section5SingleStripRightContact
import GraphMinor.GM06.Section5CutPathParameter
import GraphMinor.GM06.Section5CutInitialGap
import GraphMinor.GM06.Section5CutGapEdge
import GraphMinor.GM06.Section5BoundaryGap
import GraphMinor.GM06.Section5SinglePathSpliceWinding
import GraphMinor.GM06.Section5ReplaceLinkagePath
import GraphMinor.GM06.Section5CoverStripDiscSheet
import GraphMinor.GM06.Section5CutStripBoundary
import GraphMinor.GM06.Section5StripImage
import GraphMinor.GM06.Section5LiftedPaths
import GraphMinor.GM06.Section5Red
import GraphMinor.GM06.Section5EndpointObstruction
import GraphMinor.GM06.Section4PathTools
import GraphMinor.GM06.Alg57CurrentPathIncidence
import GraphMinor.GM06.Alg57Find4Link
import GraphMinor.GM11.Walks

/-!
# The terminal phase for one path

When no reduction applies and `s₁` does not have valency one, the terminal phase of VI (5.7),
page 133, writes the row `gm06TerminalSuccessorRows`: the projected darts of the path `Q` returned
by `TERMINAL_PATH` on the cut face of `c̄₁`, followed by the old row of `P₁` after the end of `Q`.
For one path (`k = 1`) we prove that this row encodes a linkage of winding `θ + 1`
(`GM06CurrentDrawingRep.terminalPhase_one_linkage`).

The theorem `exists_successor_linkage_of_terminal_path_one` gives such a linkage, but not its row.
We keep the walks along the way.

* `terminal_erased_walk_one`: the erased trace is a dart walk to a marked slot `t`, and its labels
  form a path `Q̃` of the cut drawing with the properties of `terminal_path_spec_one`.
* `terminal_one_geometry`: the end of `Q̃` is the right copy `Γ₂(u)` of a vertex `P₁(u)`, `u > 0`,
  the projection is injective on `Q̃`, and its image is a path `P` of `G` with the data needed by
  Lemma 16 (the proof of `exists_successor_linkage_of_terminal_path_one`).
* `exists_encoded_successor_linkage_one`: Lemma 16 for an encoded walk whose drawing is `P`
  together with the tail of `P₁` from `P₁(u)`.

In the phase, `t` is a right copy, so it is on the right boundary list, and its position there
splits the old row at `P₁(u)`.
-/

@[expose] public section

namespace GraphMinor.GM06

open Set Topology Real GraphMinor.Surface GraphMinor.GM11 GraphMinor.Compute

variable {G : Drawing ClosedCylinder} {θ : ℝ} {D : Set (ℝ × ℝ)}

/-- **The erased trace for one path.** The output of `TERMINAL_PATH` is a dart walk from `s₀` to a
marked slot `t`, without repeated vertices, through darts of the face walk with unmarked tails.
Its labels form a simple walk of the cut drawing from `s̃`, whose drawing has the properties of
`terminal_path_spec_one`. -/
theorem terminal_erased_walk_one {L : CylinderLinkage 1 G} {F : Drawing D} {s : D}
    (hsR : s ∈ cutRc G D)
    {heads targets ds : List ℕ} {s₀ : ℕ} {tail : ℕ → ℕ} {lab : ℕ → D} {edgeOf : ℕ → Set D}
    (rep : TerminalRep1 L F s heads targets ds s₀ tail lab edgeOf) :
    ∃ t : ℕ, GM06DartWalk tail (fun d => heads[d]?.getD 0) s₀
        (gm06EraseClosedSubwalks (fun d => heads[d]?.getD 0) s₀
          (gm06TerminalTrace heads targets ds).1) t ∧
      (gm06WalkVertices (fun d => heads[d]?.getD 0) s₀
        (gm06EraseClosedSubwalks (fun d => heads[d]?.getD 0) s₀
          (gm06TerminalTrace heads targets ds).1)).Nodup ∧
      (∀ d ∈ gm06EraseClosedSubwalks (fun d => heads[d]?.getD 0) s₀
          (gm06TerminalTrace heads targets ds).1, d ∈ ds ∧ targets[tail d]?.getD 0 = 0) ∧
      targets[t]?.getD 0 ≠ 0 ∧
      ∃ W : GraphWalk F.toGraph s (lab t), W.IsSimple ∧
        W.support = (gm06WalkVertices (fun d => heads[d]?.getD 0) s₀
          (gm06EraseClosedSubwalks (fun d => heads[d]?.getD 0) s₀
            (gm06TerminalTrace heads targets ds).1)).map lab ∧
        W.edges = (gm06EraseClosedSubwalks (fun d => heads[d]?.getD 0) s₀
          (gm06TerminalTrace heads targets ds).1).map edgeOf ∧
        IsSubpathOf F (walkDrawing F W) s (lab t) ∧ (walkDrawing F W).U ⊆ cutRc G D ∧
        (walkDrawing F W).V ∩ {p | cutProj D p ∈ (L.pathDrawing 0).V} ⊆ {s, lab t} ∧
        cutProj D (lab t) ∈ (L.pathDrawing 0).V ∧ lab t ≠ s ∧
        ∀ e ∈ (walkDrawing F W).E, e ∈ cutEok G D := by
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
    rw [List.getLast?_eq_some_getLast hne] at hlast
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
  refine ⟨H dl, hwQ, hndQ, fun d hd => ⟨htrace_ds d (hQd_trace d hd), htails d (hQd_trace d hd)⟩,
    hstop', W, hWsimple, hWs, hWe, hQsub, hQR, hint, huT.1, fun h => hsne h.symm, hEok⟩

/-- **The geometry of the terminal path for one path.** Let `Q̃` be a path of the cut drawing from
`s̃` to a vertex `v` over `P₁`, in the closure of the lifted region, whose other vertices are not
over `P₁` and whose edges lie over edges of `G`. If no reduction applies and `s₁` does not have
valency one, then `v` is the right copy `Γ₂(u)` of a vertex `P₁(u)` with `u > 0`, the projection is
injective on `Q̃`, and the image of `Q̃` is a path `P` of `G` from `s₁` to `P₁(u)` meeting `P₁` only
at its ends, with a parametrization whose aligned lift ends at `Γ₂(u)`. These are the steps of
`exists_successor_linkage_of_terminal_path_one`. -/
theorem terminal_one_geometry (L : CylinderLinkage 1 G)
    (hG : IsCylinderSection5Drawing 1 G) (hθ : L.HasTheta θ)
    (hno : ¬ Section5AnyReductionApplies 1 G L)
    (hval : vertexValency G.toGraph (cylinderM1Point 1 0) ≠ 1)
    (hD : IsClosedDisc D) (hBd : discBd D = liftedStripBoundary hG.1 L 1)
    (hstrip : D ⊆ {p : ℝ × ℝ | 1 ≤ p.1 ∧ p.1 ≤ 2}) (F : Drawing D)
    (hFU : F.U = (fun p : D => radialCylinderProjection p.1) ⁻¹' G.U ∪ bd D)
    (hFV : F.V = (fun p : D => radialCylinderProjection p.1) ⁻¹' G.V)
    (hEdges : ∀ ec ∈ F.E, ec ⊆ bd D ∨
      ∃ e ∈ G.E \ (L.pathDrawing 0).E, ec = (fun p : D => radialCylinderProjection p.1) ⁻¹' e)
    {s : D} (hs : s.1 = (1, 2 * π)) {v : D} {Q : Drawing D} (hQ : IsSubpathOf F Q s v)
    (hQR : Q.U ⊆ cutRc G D)
    (hcontact : Q.V ∩ {p | cutProj D p ∈ (L.pathDrawing 0).V} ⊆ {s, v})
    (hvP : cutProj D v ∈ (L.pathDrawing 0).V) (hEok : ∀ e ∈ Q.E, e ∈ cutEok G D) :
    ∃ (u : unitInterval) (P : Drawing ClosedCylinder) (q : Curve ClosedCylinder),
      0 < u ∧ L.curve 0 u ∈ (L.pathDrawing 0).V ∧ L.curve 0 u = cutProj D v ∧
      v.1 = liftedLinkageCurve hG.1 L 2 u ∧ InjOn (cutProj D) Q.U ∧
      IsSubpathOf G P (cylinderM1Point 1 0) (L.curve 0 u) ∧ P.U = cutProj D '' Q.U ∧
      P.U ∩ (L.pathDrawing 0).U ⊆ {cylinderM1Point 1 0, L.curve 0 u} ∧
      ParametrizesSet q P.U (cylinderM1Point 1 0) (L.curve 0 u) ∧
      cylinderCurveLiftAt q (cylinderInitialLift 1 0).2 1 =
        planeToCylinderCover (liftedLinkageCurve hG.1 L 2 u) := by
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
  have hinj := injOn_cut_projection_of_path_point_contact L hG hθ hD hBd hstrip hpoint hends
  exact ⟨u, P, q, hu, huV, huEq, htΓ, hinj, hP', hPU, hPL', hq', hqEnd⟩

/-- **Lemma 16 for `k = 1`, with given rows.** Let `P` be a path from `s₁` to `P₁(u)` with a
parametrization whose aligned lift ends at `Γ₂(u)`, let `T` be the tail of `P₁` from `P₁(u)`, and
let `W` be a simple walk of `G` from `s₁` to the end of `P₁` whose drawing is `P ∪ T`. If `W` is
encoded by the only row, then the rows encode a linkage of winding `θ + 1`. -/
theorem exists_encoded_successor_linkage_one (L : CylinderLinkage 1 G)
    (hG : IsCylinderSection5Drawing 1 G) (hθ : L.HasTheta θ) (u : unitInterval)
    {P : Drawing ClosedCylinder}
    (q : Curve ClosedCylinder) (hq : ParametrizesSet q P.U (cylinderM1Point 1 0) (L.curve 0 u))
    (hqEnd : cylinderCurveLiftAt q (cylinderInitialLift 1 0).2 1 =
      planeToCylinderCover (liftedLinkageCurve hG.1 L 2 u))
    {T : Drawing ClosedCylinder} (hT : IsSection5Tail (L.pathDrawing 0) T (L.curve 0 u) (L.curve 0 1))
    (hTP : T.IsSubdrawing (L.pathDrawing 0))
    {n : ℕ} {tagged : List ((Fin n × Fin n) × ℕ)} {vertex : Fin n → ClosedCylinder}
    {edge : Fin tagged.length → Set ClosedCylinder} {rows : List (List ℕ)} (hlen : rows.length = 1)
    (W : GraphWalk G.toGraph (cylinderM1Point 1 0) (L.curve 0 1)) (hW : W.IsSimple)
    (henc : GM06WalkDartEncoding G.toGraph tagged vertex edge W (rows[0]?.getD []))
    (hWU : (walkDrawing G W).U = P.U ∪ T.U) :
    ∃ L' : CylinderLinkage 1 G, L'.HasTheta (θ + 1) ∧ L'.curve 0 1 = L.curve 0 1 ∧
      GM06LinkageRowsEncoding L' tagged vertex edge rows := by
  obtain ⟨L', hRi, hEnd, -⟩ := exists_linkage_replacing_path L 0 (walkDrawing_isSubdrawing G W)
    (isPathDrawing_walkDrawing_of_isSimple G hW (isPathDrawing_start_ne_end (L.isPath 0)))
    (fun j hj => False.elim (hj (Subsingleton.elim _ _)))
  have hR' : IsPathDrawing (L'.pathDrawing 0) (cylinderM1Point 1 0) (L.curve 0 1) := by
    simpa only [hEnd] using L'.isPath 0
  have hg := L'.curve_parametrizes 0
  have hg' : ParametrizesSet (L'.curve 0) (L'.pathDrawing 0).U (cylinderM1Point 1 0)
      (L.curve 0 1) :=
    ⟨hg.1, hg.2.1, hg.2.2.1, hg.2.2.2.trans hEnd⟩
  have hU : (L'.pathDrawing 0).U = P.U ∪ T.U := by rw [hRi, hWU]
  have hw := windingNumber_single_path_right_contact_splice L hG u q hq hqEnd hT hTP hR' hU
    (L'.curve 0) hg'
  refine ⟨L', ?_, hEnd, hlen, fun j => ?_⟩
  · intro i
    have hi : i = 0 := Subsingleton.elim _ _
    subst i
    rw [hw, hθ 0]
  · have hj : j = 0 := Subsingleton.elim _ _
    subst hj
    rw [hEnd, hRi]
    exact ⟨W, hW, henc, rfl⟩

namespace GM06CurrentDrawingRep

variable {x : GM06SuccessorInput} {L : CylinderLinkage 1 G} (rep : GM06CurrentDrawingRep x G L)

local notation "currentCut" => gm06CutDataOfLinkage x.vertexCount rep.tagged.length x.endpoints
  x.linkage x.innerCuff x.outerCuff x.rotations (List.range x.vertexCount)
local notation "edgeCount" => 2 * (rep.tagged.length + (1 + 1))
local notation "heads" => gm06TerminalHeadWords edgeCount (GM06CutData.origins currentCut)

/-- **The terminal phase gives the next linkage for one path** (VI (5.7), page 133, `k = 1`). If
no reduction applies and `s₁` does not have valency one, the rows `gm06TerminalSuccessorRows`
encode a linkage `L'` of `G` with winding `θ + 1`, whose path ends at the end of `P₁`. The
statement has the shape of `terminalPhase_linkage` for `k = 1`. -/
theorem terminalPhase_one_linkage (hG : IsCylinderSection5Drawing 1 G)
    (hno : ¬ Section5AnyReductionApplies 1 G L)
    (hval : ∀ i, vertexValency G.toGraph (cylinderM1Point 1 i) ≠ 1) (hθ : L.HasTheta θ) :
    ∃ L' : CylinderLinkage 1 G, L'.HasTheta (θ + 1 / ((1 : ℕ) : ℝ)) ∧
      (∀ i, L'.curve i 1 = L.curve (finSuccCycle i) 1) ∧
      GM06LinkageRowsEncoding L' rep.tagged rep.vertex rep.edge
        (gm06TerminalSuccessorRows x rep.tagged.length) := by
  classical
  have hn : 0 < x.vertexCount := Nat.zero_lt_of_lt (rep.source 0).isLt
  obtain ⟨D, hD, hBd, hstrip, -⟩ := exists_cover_strip_disc_sheet L hG hθ 1
  obtain ⟨F, hFU, hFV, hEdges⟩ := exists_augmented_drawing_on_single_strip L hG hθ hD hBd hstrip
  obtain ⟨root, hroot, row, hout, horbit, hnd, hgap, horder⟩ := rep.component_cut_face_order hG 0
  obtain ⟨hord, trep⟩ := rep.onePath_terminal_rep_of_row hn hG hno hθ hD hBd hstrip F hFU hFV
    hEdges row horbit hnd hgap horder
  have hact : ∀ q ∈ gm06TerminalFaceDarts
      (gm06CutDart (2 * (rep.tagged.length + (0 : Fin 1).val) + 1) 0) row,
      q ∈ (currentCut).activeDarts := fun q hq =>
    rep.cut_face_row_active hG (List.range x.vertexCount) 0 horbit q (terminal_row_mem hq)
  have hinc : ∀ v ∈ gm06WalkVertices (fun q => (heads)[q]?.getD 0)
      (gm06CutVertex (rep.source 0).val true) (gm06TerminalFaceDarts
        (gm06CutDart (2 * (rep.tagged.length + (0 : Fin 1).val) + 1) 0) row),
      ∃ u : Fin (2 * x.vertexCount), u.val = v ∧
        (gm06IncV (2 * x.vertexCount) (currentCut).origins row)[u.val]?.getD 0 ≠ 0 :=
    fun v hv => rep.terminal_walk_vertices_inc hn hG 0 row horbit hgap hv
  have hhorbit := horbit
  obtain ⟨root', hroot', hpart⟩ := rep.phase_component_at hG 0
  have hrr : root' = root := Fin.ext (hroot'.trans hroot.symm)
  subst root'
  have hcode : gm06CutDart (2 * (rep.tagged.length + (0 : Fin 1).val) + 1) 0 =
      4 * (rep.tagged.length + (0 : Fin 1).val) + 1 := by
    simp [gm06CutDart, Nat.add_div, Nat.add_mod]
  rw [hcode] at hgap hact hord trep hinc
  have hface : gm06CutFaceIncidence (2 * x.vertexCount)
      (2 * (rep.tagged.length + x.innerCuff.length + x.outerCuff.length))
      (gm06CutComponentData currentCut root) (4 * (rep.tagged.length + (0 : Fin 1).val) + 1) =
        some (row, gm06IncV (2 * x.vertexCount) (currentCut).origins row,
          gm06IncE edgeCount row) := by
    rw [rep.cuff_lengths.1, rep.cuff_lengths.2, Nat.add_assoc]
    exact hout
  have hpath (j : Fin 1) : x.linkage[j.val]?.getD [] =
      x.linkage[j.val]'(by rw [rep.linkage.1]; exact j.isLt) := by
    rw [List.getElem?_eq_getElem (show j.val < x.linkage.length by
      rw [rep.linkage.1]; exact j.isLt)]
    rfl
  have hsource (j : Fin 1) : x.innerCuff[j.val]?.getD 0 = (rep.source j).val := by
    rw [rep.inner]
    simp only [List.getElem?_ofFn, j.isLt, dite_true, Option.getD_some]
  have hfs : finSuccCycle (0 : Fin 1) = 0 := Subsingleton.elim _ _
  simp only [hfs] at hord trep
  rw [← hpath 0, ← hsource 0] at hord trep
  rw [← hsource 0] at hinc
  -- the only row
  have hrows1 : (gm06TerminalSuccessorRows x rep.tagged.length).length = 1 := by
    rw [gm06TerminalSuccessorRows_length, rep.cuff_lengths.1]
  have hrow : (gm06TerminalSuccessorRows x rep.tagged.length)[0]?.getD [] =
      gm06TerminalRowOfPath x rep.tagged.length (0 : Fin 1).val (currentCut).origins
        (gm06TerminalPath (2 * x.vertexCount) (currentCut).origins row
          (gm06PhaseBoundaryVertices x (0 : Fin 1).val 0)
          (gm06PhaseBoundaryVertices x (gm06PhaseNext x (0 : Fin 1).val) 1)
          (4 * (rep.tagged.length + (0 : Fin 1).val) + 1)) := by
    rw [gm06TerminalSuccessorRows_getD _ _ (by rw [rep.cuff_lengths.1]; exact one_pos)]
    exact gm06TerminalSuccessorRow_eq hpart hface
  rw [rep.terminalPath_eq_erase hn hG 0 row hgap] at hrow
  simp only [hfs] at hrow
  -- the erased trace and its geometry
  have hsR := (onePath_setting L hG hθ hD hBd hstrip F hFU hFV hEdges).2.2.2.2.1
  obtain ⟨t, hwQ, hndQ, hQd, hmark, W, hWs, hWsupp, hWedges, hsub, hQR, hcontact, hvP, -, hEok⟩ :=
    terminal_erased_walk_one hsR trep
  obtain ⟨u, P, q, hu, huV, huEq, hvΓ, hinj, -, hPU, hPL, hq, hqEnd⟩ :=
    terminal_one_geometry L hG hθ hno (hval 0) hD hBd hstrip F hFU hFV hEdges
      (cutLiftCurve_zero L hG hBd) hsub hQR hcontact hvP hEok
  set Qd := gm06EraseClosedSubwalks (fun d => (heads)[d]?.getD 0)
    (gm06CutVertex (x.innerCuff[(0 : Fin 1).val]?.getD 0) true)
    (gm06TerminalTrace heads
      (gm06TerminalTargetBits (2 * x.vertexCount)
        (gm06CutVertex (x.innerCuff[(0 : Fin 1).val]?.getD 0) true)
        ((gm06CutPathLabels x.vertexCount hn x.endpoints (x.linkage[(0 : Fin 1).val]?.getD [])
          (x.innerCuff[(0 : Fin 1).val]?.getD 0) true).map Fin.val)
        ((gm06CutPathLabels x.vertexCount hn x.endpoints (x.linkage[(0 : Fin 1).val]?.getD [])
          (x.innerCuff[(0 : Fin 1).val]?.getD 0) false).map Fin.val))
      (gm06TerminalFaceDarts (4 * (rep.tagged.length + (0 : Fin 1).val) + 1) row)).1 with hQdDef
  set s₀ := gm06CutVertex (x.innerCuff[(0 : Fin 1).val]?.getD 0) true with hs₀
  obtain ⟨_, hkeys, _, hc, _⟩ := rep.cut_data_face_encoding hG (List.range x.vertexCount)
  have hbound : ∀ d ∈ Qd, d < 2 * edgeCount := fun d hd =>
    hkeys d ((hc d).mp (hact d (hQd d hd).1))
  have hheadEq : ∀ d ∈ Qd, (heads)[d]?.getD 0 = gm06CutNeighbourHead (currentCut).origins d :=
    fun d hd => terminalHeadWords_get _ (hbound d hd)
  have hw' : GM06DartWalk (fun q => (currentCut).origins[q]?.getD 0)
      (gm06CutNeighbourHead (currentCut).origins) s₀ Qd t := GM06DartWalk.congr_head hwQ hheadEq
  have hvl : gm06WalkVertices (fun d => (heads)[d]?.getD 0) s₀ Qd =
      gm06WalkVertices (fun d => (currentCut).origins[gm06DartMate d]?.getD 0) s₀ Qd := by
    simp only [gm06WalkVertices]
    congr 1
    exact List.map_congr_left hheadEq
  have hvert : ∀ v ∈ gm06WalkVertices (fun d => (heads)[d]?.getD 0) s₀ Qd,
      v ∈ gm06WalkVertices (fun d => (heads)[d]?.getD 0) s₀
        (gm06TerminalFaceDarts (4 * (rep.tagged.length + (0 : Fin 1).val) + 1) row) := by
    intro v hv
    rcases List.mem_cons.mp hv with rfl | hv
    · exact List.mem_cons_self
    · obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hv
      exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨d, (hQd d hd).1, rfl⟩)
  -- slots of the erased trace name points over their vertices
  have hcp : ∀ v ∈ gm06WalkVertices (fun d => (heads)[d]?.getD 0) s₀ Qd,
      rep.cutPoint v = cutProj D (rep.cutLabN hG hBd v) := by
    intro v hv
    obtain ⟨w, rfl, -⟩ := hinc v (hvert v hv)
    rw [rep.cutPoint_fin, rep.cutLabN_fin, rep.cutProj_cutLab hG hθ hD hBd hstrip]
  have htlast : (gm06WalkVertices (fun d => (heads)[d]?.getD 0) s₀ Qd).getLast
      (List.cons_ne_nil _ _) = t := GM06DartWalk.walkVertices_getLast hwQ
  have htmem : t ∈ gm06WalkVertices (fun d => (heads)[d]?.getD 0) s₀ Qd := by
    rw [← htlast]; exact List.getLast_mem _
  have hs₀mem : s₀ ∈ gm06WalkVertices (fun d => (heads)[d]?.getD 0) s₀ Qd := List.mem_cons_self
  obtain ⟨tF, htF, htinc⟩ := hinc t (hvert t htmem)
  subst htF
  have hcpt : rep.cutPoint tF.val = L.curve 0 u := by
    rw [hcp _ htmem, huEq]
  have hcps : rep.cutPoint s₀ = cylinderM1Point 1 0 := by
    rw [hcp _ hs₀mem, trep.start_lab, cutProj_cutLiftCurve, (L.curve_parametrizes 0).2.2.1]
  -- the end is a slot of the right copy of `P₁`
  have hside : rep.cutLab hG hBd tF ∈ (cutSide L hG F 2).U := by
    rw [(cutSide_V_U L hG hθ hD hBd hstrip F hFU hFV hEdges (m := 2) (n := 1)
      (Or.inr ⟨rfl, rfl⟩)).2]
    change (rep.cutLab hG hBd tF).1 ∈ range (liftedLinkageCurve hG.1 L 2)
    rw [← rep.cutLabN_fin hG hBd tF, hvΓ]
    exact ⟨u, rfl⟩
  have hupper : tF.val ∈ (gm06CutPathLabels x.vertexCount hn x.endpoints
      (x.linkage[(0 : Fin 1).val]?.getD []) (x.innerCuff[(0 : Fin 1).val]?.getD 0) false).map
        Fin.val := by
    rw [hpath 0, hsource 0]
    exact (rep.slots_upper_iff hG hθ hD hBd hstrip hn row hhorbit F hFU hFV hEdges tF
      htinc).mpr hside
  -- the tail of `P₁` after the end
  obtain ⟨WPn, hWPns, hWPnenc, hWPnD, -, hWPnsupp, -⟩ := rep.computed_encoded_path_walk hn 0 false
  rw [← hpath 0, ← hsource 0] at hWPnsupp
  rw [← hpath 0] at hWPnenc
  set labelsN := gm06CutPathLabels x.vertexCount hn x.endpoints
    (x.linkage[(0 : Fin 1).val]?.getD []) (x.innerCuff[(0 : Fin 1).val]?.getD 0) false
    with hlabelsN
  set p := (labelsN.map Fin.val).idxOf tF.val with hp
  have hplt : p < (labelsN.map Fin.val).length := List.idxOf_lt_length_of_mem hupper
  have hpget : (labelsN.map Fin.val)[p] = tF.val := List.getElem_idxOf hplt
  have hlabLen : labelsN.length = (x.linkage[(0 : Fin 1).val]?.getD []).length + 1 := by
    simp only [hlabelsN, gm06CutPathLabels, find4PathLabels, gm06CutPathSteps, List.length_cons,
      List.length_map]
  have hpl : p ≤ (x.linkage[(0 : Fin 1).val]?.getD []).length := by
    rw [List.length_map] at hplt
    omega
  have hsuppP : WPn.support[p]? = some (rep.cutPoint tF.val) := by
    rw [hWPnsupp, List.getElem?_map]
    rw [List.length_map] at hplt
    rw [List.getElem?_eq_getElem hplt, Option.map_some]
    rw [List.getElem_map] at hpget
    rw [← hpget, rep.cutPoint_fin]
  rw [hcpt] at hsuppP
  obtain ⟨z, -, Bw, -, hBenc, hz, -, hBS, -, hBE⟩ := hWPnenc.exists_split_take_drop p hpl
  obtain rfl : z = L.curve 0 u := Option.some.inj (hz.symm.trans hsuppP)
  have hWPnnd : WPn.support.Nodup := hWPns
  obtain ⟨WP', hs', he'⟩ := (L.isSubdrawing 0).1.exists_walk_down WPn
    (fun v hv => by rw [← hWPnD, walkDrawing_V]; exact hv)
    (fun e he => by rw [← hWPnD, walkDrawing_E]; exact he)
  have hWP's : WP'.IsSimple := by
    unfold GraphWalk.IsSimple; rw [hs']; exact hWPns
  have hWP'len : p ≤ WP'.length := by
    have h1 := GraphWalk.support_length WP'
    rw [hs', hWPnsupp, List.length_map, hlabLen] at h1
    omega
  obtain ⟨z', -, B', hz', -, h2', -, h4'⟩ := GraphWalk.exists_split_take_drop WP' p hWP'len
  rw [hs', hsuppP] at hz'
  obtain rfl : z' = L.curve 0 u := Option.some.inj hz'.symm
  have hT : IsSection5Tail (L.pathDrawing 0) (walkDrawing (L.pathDrawing 0) B') (L.curve 0 u)
      (L.curve 0 1) := genTail_of_split hWP's (by rw [hs']; exact hsuppP) h2' h4'
  have hTU : (walkDrawing (L.pathDrawing 0) B').U = (walkDrawing G Bw).U := by
    ext y
    rw [mem_walkDrawing_U, mem_walkDrawing_U, h2', h4', hBS, hBE, hs', he']
  -- the projected walk of the erased trace
  have htG : rep.cutPoint tF.val ∈ G.V := by
    rw [hcpt]; exact (L.isSubdrawing 0).1.1 huV
  obtain ⟨Wq, hWqenc, hWqsupp, hWqedges⟩ : ∃ Wq : GraphWalk G.toGraph (cylinderM1Point 1 0)
      (L.curve 0 u), GM06WalkDartEncoding G.toGraph rep.tagged rep.vertex rep.edge Wq
        (Qd.map gm06ProjectCutDart) ∧
      Wq.support = (gm06WalkVertices (fun d => (currentCut).origins[gm06DartMate d]?.getD 0)
        s₀ Qd).map rep.cutPoint ∧ Wq.edges = Qd.map (fun d => rep.cutEdgePoint (d / 2)) := by
    rw [← hcps, ← hcpt]
    exact rep.exists_encoded_cut_walk hG hw' htG
      fun d hd => ⟨hact d (hQd d hd).1, hord d (hQd d hd).1 (hQd d hd).2⟩
  have hWqsupp' : Wq.support = W.support.map (cutProj D) := by
    rw [hWqsupp, hWsupp, ← hvl, List.map_map]
    exact List.map_congr_left fun v hv => hcp v hv
  have hcl : ∀ e, cutProj D '' closure (rep.cutEdgeLab hG e) = closure (rep.cutEdgePoint e) := by
    intro e
    rw [← (isClosedMap_cutProj hD).closure_image_eq_of_continuous continuous_cutProj]
    unfold cutEdgeLab
    rw [image_cutEdgeLabel hG hθ hD hBd hstrip]
  have hWqU : (walkDrawing G Wq).U = cutProj D '' (walkDrawing F W).U := by
    ext y
    rw [mem_walkDrawing_U, hWqsupp', hWqedges]
    constructor
    · rintro (hy | ⟨e, he, hye⟩)
      · obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hy
        exact ⟨p, (mem_walkDrawing_U F W).mpr (Or.inl hp), rfl⟩
      · obtain ⟨d, hd, rfl⟩ := List.mem_map.mp he
        rw [← hcl] at hye
        obtain ⟨p, hp, rfl⟩ := hye
        exact ⟨p, (mem_walkDrawing_U F W).mpr
          (Or.inr ⟨_, hWedges ▸ List.mem_map_of_mem hd, hp⟩), rfl⟩
    · rintro ⟨p, hp, rfl⟩
      rcases (mem_walkDrawing_U F W).mp hp with hp | ⟨e, he, hpe⟩
      · exact Or.inl (List.mem_map_of_mem hp)
      · rw [hWedges] at he
        obtain ⟨d, hd, rfl⟩ := List.mem_map.mp he
        exact Or.inr ⟨_, List.mem_map_of_mem hd, hcl _ ▸ ⟨p, hpe, rfl⟩⟩
  have hWqnd : Wq.support.Nodup := by
    rw [hWqsupp']
    exact (show W.support.Nodup from hWs).map_on fun a ha b hb hab =>
      hinj ((mem_walkDrawing_U F W).mpr (Or.inl ha)) ((mem_walkDrawing_U F W).mpr (Or.inl hb)) hab
  -- the joined walk
  have hBnd : Bw.support.Nodup := by
    rw [hBS]; exact hWPnnd.sublist (List.drop_sublist _ _)
  have hus : L.curve 0 u ≠ cylinderM1Point 1 0 := by
    intro h
    have heq : L.curve 0 u = L.curve 0 0 := h.trans (L.curve_parametrizes 0).2.2.1.symm
    exact hu.ne' ((L.curve_parametrizes 0).1 heq)
  have hBnot : cylinderM1Point 1 0 ∉ Bw.support := by
    intro hs
    rw [hBS] at hs
    obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp hs
    rw [List.getElem?_drop] at hj
    have h0 := GraphWalk.support_getElem?_zero WPn
    have := nodup_index_eq_of_getElem? hWPnnd hj h0
    have hp0 : p = 0 := by omega
    rw [hp0, h0] at hsuppP
    exact hus (Option.some.inj hsuppP).symm
  have hJs : (Wq.append Bw).IsSimple := by
    unfold GraphWalk.IsSimple
    rw [GraphWalk.support_append]
    refine List.Nodup.append hWqnd (hBnd.sublist (List.tail_sublist _)) ?_
    intro y hyq hyB
    have hyB' : y ∈ Bw.support := List.mem_of_mem_tail hyB
    have hyP : y ∈ P.U := by
      rw [hPU, ← hWqU]; exact (mem_walkDrawing_U G Wq).mpr (Or.inl hyq)
    have hyL : y ∈ (L.pathDrawing 0).U := by
      rw [← hWPnD]
      refine (mem_walkDrawing_U G WPn).mpr (Or.inl ?_)
      rw [hBS] at hyB'
      exact List.mem_of_mem_drop hyB'
    rcases hPL ⟨hyP, hyL⟩ with h | h
    · rw [h] at hyB'
      exact hBnot hyB'
    · rw [mem_singleton_iff.mp h] at hyB
      rw [Bw.support_eq_cons] at hBnd
      exact (List.nodup_cons.mp hBnd).1 hyB
  have hWU : (walkDrawing G (Wq.append Bw)).U = P.U ∪ (walkDrawing (L.pathDrawing 0) B').U := by
    rw [hPU, ← hWqU, hTU]
    ext y
    simp only [mem_union, mem_walkDrawing_U, GraphWalk.mem_support_append,
      GraphWalk.edges_append, List.mem_append]
    constructor
    · rintro ((h | h) | ⟨e, h | h, hy⟩)
      · exact Or.inl (Or.inl h)
      · exact Or.inr (Or.inl h)
      · exact Or.inl (Or.inr ⟨e, h, hy⟩)
      · exact Or.inr (Or.inr ⟨e, h, hy⟩)
    · rintro ((h | ⟨e, h, hy⟩) | (h | ⟨e, h, hy⟩))
      · exact Or.inl (Or.inl h)
      · exact Or.inr ⟨e, Or.inl h, hy⟩
      · exact Or.inl (Or.inr h)
      · exact Or.inr ⟨e, Or.inr h, hy⟩
  -- the computed row is the encoding of the joined walk
  have hlast : (gm06WalkVertices (gm06CutNeighbourHead (currentCut).origins)
      (gm06CutNeighbourHead (currentCut).origins (4 * (rep.tagged.length + (0 : Fin 1).val) + 1))
        Qd).getLast (List.cons_ne_nil _ _) = tF.val := by
    rw [rep.neighbourHead_gap hG 0]
    exact GM06DartWalk.walkVertices_getLast hw'
  have hupB := rep.computed_path_labels_phase hn 0 false
  simp only [Bool.not_false, Bool.toNat_true] at hupB
  unfold gm06TerminalRowOfPath at hrow
  rw [hlast, rep.phase_next_eq 0, hfs, ← hupB] at hrow
  have henc : GM06WalkDartEncoding G.toGraph rep.tagged rep.vertex rep.edge (Wq.append Bw)
      ((gm06TerminalSuccessorRows x rep.tagged.length)[0]?.getD []) := by
    rw [hrow]
    exact hWqenc.append hBenc
  obtain ⟨L', hθ', hend, henc'⟩ := exists_encoded_successor_linkage_one L hG hθ u q hq hqEnd hT
    (walkDrawing_isSubdrawing _ B') hrows1 (Wq.append Bw) hJs henc hWU
  refine ⟨L', by simpa using hθ', fun i => ?_, henc'⟩
  rw [Subsingleton.elim i 0, hfs]
  exact hend

end GM06CurrentDrawingRep

end GraphMinor.GM06
