module

public import GraphMinor.GM06.Alg57OnePathPhase
public import GraphMinor.GM06.Alg57ComputedWalkEncoding
import GraphMinor.GM06.Alg57CurrentReduction4Phase
import GraphMinor.GM06.Alg57CurrentCandidateRows
import GraphMinor.GM06.Alg57TerminalPathLink
import GraphMinor.GM06.Alg57Find4Generic
import GraphMinor.GM06.Alg57OnePathSound
import GraphMinor.GM06.Section5ReplaceLinkagePath
import GraphMinor.GM06.Section5CoverStripDiscSheet
import GraphMinor.GM06.Section5CutStripBoundary
import GraphMinor.GM06.Section5Red
import GraphMinor.GM06.Section5EndpointObstruction
import GraphMinor.GM06.Section4PathTools
import GraphMinor.GM06.Alg57Find4Link
import GraphMinor.GM06.Alg57CandidateGraph
import GraphMinor.GM06.Alg57OnePathFind4
import GraphMinor.GM11.Walks

/-!
# The rows written by the Reduction 4 phase for one path

`reduction4Phase_one_sound` in `Alg57OnePathPhase.lean` shows that a reported rerouting for one
path (`k = 1`) gives a Reduction 4 step. Algorithm (5.7) needs more: the new row written by
APPLY_4 must encode the new path. Here we prove this
(`GM06CurrentDrawingRep.reduction4Phase_one_sound_rows`).

The returned darts trace a walk `W̃` of the cut drawing `F` from the left copy of `s₁` to the left
copy of the contact `v`. Its projection is a walk `Wc` of `G`, encoded by the projected darts. The
suffix of the old row encodes the tail `T` of `P₁` from `v`. The walk `W̃` misses the right copy of
`P₁`, so the projection is injective on it (`injOn_cutProj_of_not_mem_right`), and it meets the
tail only at `v`. So `Wc` followed by the tail is a path, and its drawing is the union used by the
one-path Reduction 4 step. Two general facts carry the rows:

* `exists_encoded_linkage_replacing_walk`: a simple walk with the ends of path `i` and missing the
  other paths replaces path `i`, and the new rows encode the new linkage;
* `exists_encoded_reduction4Step_one_of_cut_path`: the step of
  `exists_reduction4Step_one_of_cut_path`, with a given encoded walk in place of the new path.
-/

@[expose] public section

namespace GraphMinor.GM06

open Set Topology Real GraphMinor.Surface GraphMinor.GM11 GraphMinor.Compute unitInterval

/-- **Replacing one path by an encoded walk.** A simple walk of `G` from `sᵢ` to the end of
`Pᵢ` that misses the other paths replaces `Pᵢ`. If the old rows encode `L`, then the rows with the
row of the walk in place `i` encode the new linkage. -/
theorem exists_encoded_linkage_replacing_walk {n k : ℕ} {G : Drawing ClosedCylinder}
    (L : CylinderLinkage k G) (i : Fin k)
    {tagged : List ((Fin n × Fin n) × ℕ)} {vertex : Fin n → ClosedCylinder}
    {edge : Fin tagged.length → Set ClosedCylinder} {rows : List (List ℕ)} {row : List ℕ}
    (hrows : GM06LinkageRowsEncoding L tagged vertex edge rows)
    (W : GraphWalk G.toGraph (cylinderM1Point k i) (L.curve i 1)) (hW : W.IsSimple)
    (henc : GM06WalkDartEncoding G.toGraph tagged vertex edge W row)
    (hdisj : ∀ j, j ≠ i → Disjoint (walkDrawing G W).U (L.pathDrawing j).U) :
    ∃ L' : CylinderLinkage k G, L'.pathDrawing i = walkDrawing G W ∧
      (∀ j, j ≠ i → L'.pathDrawing j = L.pathDrawing j ∧ L'.curve j = L.curve j) ∧
      GM06LinkageRowsEncoding L' tagged vertex edge (rows.set i.val row) := by
  obtain ⟨L', hP, hc, hun⟩ := exists_linkage_replacing_path L i (walkDrawing_isSubdrawing G W)
    (isPathDrawing_walkDrawing_of_isSimple G hW (isPathDrawing_start_ne_end (L.isPath i))) hdisj
  refine ⟨L', hP, hun, ?_⟩
  have hlen : (rows.set i.val row).length = k := by rw [List.length_set, hrows.1]
  refine ⟨hlen, fun j => ?_⟩
  have hjlen : j.val < rows.length := hrows.1.symm ▸ j.isLt
  rw [List.getElem?_eq_getElem (hlen.symm ▸ j.isLt), Option.getD_some]
  by_cases hj : j = i
  · subst j
    rw [List.getElem_set_self, hP, hc]
    exact ⟨W, hW, henc, rfl⟩
  · have hne : i.val ≠ j.val := fun h => hj (Fin.ext h.symm)
    rw [List.getElem_set_ne hne, (hun j hj).1, (hun j hj).2]
    have h := hrows.path j
    exact h

/-- A walk of `P` from `s` to `t` without repeated vertices, cut at position `q`, gives a tail of
`P` from the vertex at `q`: the drawing of the second part. -/
theorem genTail_of_split {S : Type*} [TopologicalSpace S] [T2Space S] {P : Drawing S}
    {s t v : S} {W : GraphWalk P.toGraph s t} (hW : W.IsSimple) {q : ℕ}
    (hx : W.support[q]? = some v) {W₂ : GraphWalk P.toGraph v t}
    (h2 : W₂.support = W.support.drop q) (h4 : W₂.edges = W.edges.drop q) :
    IsGenTail P (walkDrawing P W₂) v t := by
  have hnd : W.support.Nodup := hW
  have hW₂s : W₂.IsSimple := by
    unfold GraphWalk.IsSimple; rw [h2]; exact hnd.sublist (List.drop_sublist _ _)
  have hql : q < W.support.length := (List.getElem?_eq_some_iff.mp hx).1
  have hsuppLen : W.support.length = W.length + 1 := GraphWalk.support_length W
  by_cases hqr : q = W.length
  · have hl1 : W₂.support.length = 1 := by rw [h2, List.length_drop]; omega
    have hxt : v = t := GraphWalk.eq_of_support_length_one W₂ hl1
    have hsupp : W₂.support = [v] := by
      rw [W₂.support_eq_cons] at hl1 ⊢
      simp only [List.length_cons, add_eq_right, List.length_eq_zero_iff] at hl1
      rw [hl1]
    have hedges : W₂.edges = [] := by
      rw [h4, List.drop_eq_nil_iff, ← GraphWalk.length]; omega
    refine Or.inl ⟨hxt, ?_, ?_⟩
    · ext y
      rw [mem_walkDrawing_U, hsupp, hedges]
      simp
    · rw [walkDrawing_V, hsupp]
      ext y; simp
  · have hne : v ≠ t := by
      intro h
      have ht' : W.support[W.length]? = some v :=
        (GraphWalk.support_getElem?_length W).trans (congrArg some h.symm)
      exact hqr (nodup_index_eq_of_getElem? hnd hx ht')
    exact Or.inr ⟨walkDrawing_isSubdrawing P W₂, walkDrawing_U_subset P W₂,
      isPathDrawing_walkDrawing_of_isSimple P hW₂s hne⟩

variable {G : Drawing ClosedCylinder} {θ : ℝ} {D : Set (ℝ × ℝ)}

/-- **The one-path Reduction 4 step with given rows.** This is
`exists_reduction4Step_one_of_cut_path`, with the new path given as a simple encoded walk `W` of
`G` whose drawing is the projection of `Q̃` together with the tail `T`. The new rows encode the new
linkage. -/
theorem exists_encoded_reduction4Step_one_of_cut_path (L : CylinderLinkage 1 G)
    (hG : IsCylinderSection5Drawing 1 G) (hθ : L.HasTheta θ) (hD : IsClosedDisc D)
    (hBd : discBd D = liftedStripBoundary hG.1 L 1)
    (hstrip : D ⊆ {p : ℝ × ℝ | 1 ≤ p.1 ∧ p.1 ≤ 2}) {F : Drawing D}
    (hFV : F.V = cutProj D ⁻¹' G.V) {Q : Drawing D} {s t : D} (hQ : IsSubpathOf F Q s t)
    (hscoord : s.1 = (1, 2 * π)) {u : unitInterval} (hu : 0 < u)
    (huV : L.curve 0 u ∈ (L.pathDrawing 0).V) (ht : t.1 = liftedLinkageCurve hG.1 L 1 u)
    (hright : ∀ p ∈ Q.U, p.1 ∉ range (liftedLinkageCurve hG.1 L 2))
    (hE : ∀ ec ∈ Q.E, cutProj D '' ec ∈ G.E)
    (hR : cutCov D '' Q.U ⊆ closure (cylinderCoverRegion 1 G 0))
    (hpre : ¬ (cylinderCurveLiftAt (L.curve 0) (cylinderInitialLift 1 0).2 '' Icc 0 u ⊆
      closure (cylinderCoverRegion 1 G 0)))
    {T : Drawing ClosedCylinder} (hT : IsSection5Tail (L.pathDrawing 0) T (L.curve 0 u) (L.curve 0 1))
    {n : ℕ} {tagged : List ((Fin n × Fin n) × ℕ)} {vertex : Fin n → ClosedCylinder}
    {edge : Fin tagged.length → Set ClosedCylinder} {rows : List (List ℕ)} {row : List ℕ}
    (hrows : GM06LinkageRowsEncoding L tagged vertex edge rows)
    (W : GraphWalk G.toGraph (cylinderM1Point 1 0) (L.curve 0 1)) (hW : W.IsSimple)
    (henc : GM06WalkDartEncoding G.toGraph tagged vertex edge W row)
    (hWU : (walkDrawing G W).U = cutProj D '' Q.U ∪ T.U) :
    ∃ L' : CylinderLinkage 1 G, Section5Reduction4Step 1 G L G L' ∧
      GM06LinkageRowsEncoding L' tagged vertex edge (rows.set 0 row) := by
  have hinj := injOn_cutProj_of_not_mem_right L hG hθ hD hBd hstrip hright
  have hs : cutProj D s = cylinderM1Point 1 0 := by
    change radialCylinderProjection s.1 = _
    rw [hscoord, radialCylinderProjection_one_two_pi]
  have htP : cutProj D t = L.curve 0 u := by
    change radialCylinderProjection t.1 = _
    rw [ht, radialCylinderProjection_lift_one]
  have hvs : L.curve 0 u ≠ cylinderM1Point 1 0 := by
    intro h
    have heq : L.curve 0 u = L.curve 0 0 := h.trans (L.curve_parametrizes 0).2.2.1.symm
    exact hu.ne' ((L.curve_parametrizes 0).1 heq)
  have hends : cutProj D s ≠ cutProj D t := by rw [hs, htP]; exact hvs.symm
  obtain ⟨P, hP, hPU⟩ := exists_projected_path_of_injOn hD hFV hQ hinj hE hends
  rw [hs, htP] at hP
  obtain ⟨q, hq, hqR, hqEnd⟩ := exists_parameterized_projection_of_injOn hQ.2.2 hscoord hinj hPU
  rw [htP] at hq
  obtain ⟨L', hRi, hunchanged, henc'⟩ := exists_encoded_linkage_replacing_walk L 0 hrows W hW henc
    (fun j hj => False.elim (hj (Subsingleton.elim _ _)))
  have hlift : cylinderCurveLiftAt (L.curve 0) (cylinderInitialLift 1 0).2 u = cutCov D t := by
    rw [cylinderCurveLiftAt_linkage_one L hG.1 u]
    change _ = planeToCylinderCover t.1
    rw [ht]
  have htQ : t ∈ Q.U := Q.V_subset_U (isPathDrawing_end_vertices hQ.2.2).2
  have huR : cylinderCurveLiftAt (L.curve 0) (cylinderInitialLift 1 0).2 u ∈
      closure (cylinderCoverRegion 1 G 0) := by
    rw [hlift]; exact hR (mem_image_of_mem _ htQ)
  refine ⟨L', ⟨rfl, Or.inr ⟨rfl, 0, u, T, P, q, huV, huR, hpre, hT, hP.1, hP.2.1, hP.2.2, hq,
    by rw [hqR]; exact hR, by rw [hqEnd, hlift], ?_, hunchanged⟩⟩, henc'⟩
  rw [hRi, hWU, hPU]

section CutLevel

variable (L : CylinderLinkage 1 G) (hG : IsCylinderSection5Drawing 1 G) (hθ : L.HasTheta θ)
  (hD : IsClosedDisc D) (hBd : discBd D = liftedStripBoundary hG.1 L 1)
  (hstrip : D ⊆ {p : ℝ × ℝ | 1 ≤ p.1 ∧ p.1 ≤ 2}) (F : Drawing D)
  (hFU : F.U = (fun p : D => radialCylinderProjection p.1) ⁻¹' G.U ∪ bd D)
  (hFV : F.V = (fun p : D => radialCylinderProjection p.1) ⁻¹' G.V)
  (hEdges : ∀ ec ∈ F.E, ec ⊆ bd D ∨
    ∃ e ∈ G.E \ (L.pathDrawing 0).E, ec = (fun p : D => radialCylinderProjection p.1) ⁻¹' e)

include hθ hD hstrip hFU hFV hEdges in
/-- **The data of a cut path.** Reduction 4 at the left copy, for a given path `Q̃` of the cut
drawing, gives the data used by `exists_reduction4Step_one_of_cut_path` for the same `Q̃`. This is
the forward half of `genReduction4At_iff_onePathReduction4At`, keeping `Q̃`. -/
theorem onePath_cut_path_data {w : D} {P_sw T' Q : Drawing D}
    (hw : w ∈ (cutSide L hG F 1).V)
    (hsw : IsSubpathOf (cutSide L hG F 1) P_sw (cutLiftCurve L hG hBd 0) w)
    (hpre : ¬ P_sw.U ⊆ cutRc G D)
    (hT' : IsGenTail (cutSide L hG F 1) T' w (cutLiftCurve L hG hBd 1))
    (hQ : IsPathDrawing Q (cutLiftCurve L hG hBd 0) w) (hQR : Q.U ⊆ cutRc G D)
    (hQT : Q.U ∩ T'.U ⊆ {w}) (hQB : Disjoint Q.U (cutSide L hG F 2).U) :
    ∃ u : unitInterval, w = cutLiftCurve L hG hBd u ∧ 0 < u ∧ L.curve 0 u ∈ (L.pathDrawing 0).V ∧
      ¬ (cylinderCurveLiftAt (L.curve 0) (cylinderInitialLift 1 0).2 '' Icc 0 u ⊆
        closure (cylinderCoverRegion 1 G 0)) ∧
      (∀ p ∈ Q.U, p.1 ∉ range (liftedLinkageCurve hG.1 L 2)) ∧
      cutCov D '' Q.U ⊆ closure (cylinderCoverRegion 1 G 0) ∧
      ∀ T : Drawing ClosedCylinder, IsSection5Tail (L.pathDrawing 0) T (L.curve 0 u) (L.curve 0 1) →
        cutProj D '' Q.U ∩ T.U ⊆ {L.curve 0 u} := by
  obtain ⟨hP1V, hP1U⟩ := cutSide_V_U L hG hθ hD hBd hstrip F hFU hFV hEdges
    (m := 1) (n := 2) (Or.inl ⟨rfl, rfl⟩)
  obtain ⟨-, hP2U⟩ := cutSide_V_U L hG hθ hD hBd hstrip F hFU hFV hEdges
    (m := 2) (n := 1) (Or.inr ⟨rfl, rfl⟩)
  have hfi := cutLiftCurve_injective L hG hBd
  have hPG : (L.pathDrawing 0).IsSubdrawing G := (L.isSubdrawing 0).1
  have hci := (L.curve_parametrizes 0).1
  have hcr := (L.curve_parametrizes 0).2.1
  rw [hP1V] at hw
  have hwr : w ∈ range (cutLiftCurve L hG hBd) := by
    rw [range_cutLiftCurve]; exact hw.2
  obtain ⟨u, rfl⟩ := hwr
  have hsw' : cutLiftCurve L hG hBd 0 ≠ cutLiftCurve L hG hBd u := isPathDrawing_start_ne_end hQ
  have hu0 : 0 < u := lt_of_le_of_ne unitInterval.nonneg' fun h => hsw' (by rw [h])
  have huV : L.curve 0 u ∈ (L.pathDrawing 0).V := by
    have h1 : cutProj D (cutLiftCurve L hG hBd u) ∈ G.V := by
      have := hw.1
      rw [hFV] at this
      exact this
    rw [cutProj_cutLiftCurve] at h1
    exact mem_V_of_mem_U_of_isSubdrawing hPG (by rw [← hcr]; exact mem_range_self u) h1
  have hpre' : ¬ (cylinderCurveLiftAt (L.curve 0) (cylinderInitialLift 1 0).2 '' Icc 0 u ⊆
      closure (cylinderCoverRegion 1 G 0)) := by
    intro H
    apply hpre
    rw [cutLift_subarc L hG hBd hsw.2.2 (hP1U ▸ hsw.2.1), uIcc_of_le unitInterval.nonneg']
    rintro _ ⟨τ, hτ, rfl⟩
    change cutCov D (cutLiftCurve L hG hBd τ) ∈ closure (cylinderCoverRegion 1 G 0)
    rw [cutCov_cutLiftCurve]
    exact H ⟨τ, hτ, rfl⟩
  have hright : ∀ p ∈ Q.U, p.1 ∉ range (liftedLinkageCurve hG.1 L 2) := fun p hp h =>
    disjoint_left.mp hQB hp (by rw [hP2U]; exact h)
  refine ⟨u, rfl, hu0, huV, hpre', hright, ?_, ?_⟩
  · rintro _ ⟨p, hp, rfl⟩
    exact hQR hp
  intro T hT
  rintro _ ⟨⟨p, hp, rfl⟩, hxT⟩
  rw [section5Tail_U L hT] at hxT
  obtain ⟨τ, hτ, hτp⟩ := hxT
  rcases mem_lifts_of_cutProj_mem_path L hG hθ hD hBd hstrip (p := p)
      (by rw [← hτp, ← hcr]; exact mem_range_self τ) with h1 | h2
  · obtain ⟨r, hr⟩ := h1
    have hpf : p = cutLiftCurve L hG hBd r := Subtype.ext hr.symm
    have hrτ : r = τ := hci (by rw [← cutProj_cutLiftCurve L hG hBd r, ← hpf, hτp])
    subst hrτ hpf
    suffices hpu : cutLiftCurve L hG hBd r = cutLiftCurve L hG hBd u by
      rw [hpu, cutProj_cutLiftCurve]
      exact mem_singleton _
    rcases hT' with ⟨hwt, -, -⟩ | ⟨-, hT'P, hT'path⟩
    · have hu1 : u = 1 := hfi hwt
      have hru : r = u := le_antisymm (hu1 ▸ hτ.2) hτ.1
      rw [hru]
    · have hmem : cutLiftCurve L hG hBd r ∈ T'.U := by
        rw [cutLift_subarc L hG hBd hT'path (hP1U ▸ hT'P), uIcc_of_le unitInterval.le_one']
        exact ⟨r, hτ, rfl⟩
      exact hQT ⟨hp, hmem⟩
  · exact absurd h2 (hright p hp)

include hθ hD hstrip hFU hFV hEdges in
/-- **The exact one-path Reduction 4 replacement** (`k = 1`). Let `q` be a contact of `FIND_4` in
the one-path setting. Let `W̃` be a simple walk of the cut drawing from the left copy of `s₁` to
the contact, whose vertices pass the candidate test at `q` and whose edges are allowed and lie in
the region closure. Let `Wc` be its projection to `G`, encoded by `crow`, and let `WP` be an encoded
walk tracing `P₁` along the projected path labels. Then the rows with `crow` followed by the
suffix of the row of `WP` in place `0` encode a linkage with a Reduction 4 step from `L`. -/
theorem exists_encoded_reduction4_one_of_cut_walk
    {n : ℕ} {ends : List (ℕ × ℕ)} {ordinary : List Bool} {incV incE upper : List ℕ}
    {start : Fin n} {steps : List (ℕ × Fin n)} {lab : Fin n → D} {edgeLab : ℕ → Set D}
    (rep : Find4Rep1 L hG F (cutLiftCurve L hG hBd 0) (cutLiftCurve L hG hBd 1) ends ordinary
      incV incE upper start steps lab edgeLab)
    {q : ℕ}
    (hq : q ∈ gm06Reduction4Contacts incV incE start.val (steps.map (fun st => (st.1, st.2.val))))
    {m : ℕ} {tagged : List ((Fin m × Fin m) × ℕ)} {vertex : Fin m → ClosedCylinder}
    {edge : Fin tagged.length → Set ClosedCylinder} {rows : List (List ℕ)}
    (hrows : GM06LinkageRowsEncoding L tagged vertex edge rows)
    {path : List ℕ} (hpath : path.length = steps.length)
    {WP : GraphWalk G.toGraph (cylinderM1Point 1 0) (L.curve 0 1)} (hWPs : WP.IsSimple)
    (hWPenc : GM06WalkDartEncoding G.toGraph tagged vertex edge WP path)
    (hWPdraw : walkDrawing G WP = L.pathDrawing 0)
    (hWPsupp : WP.support = (find4PathLabels start steps).map (fun u => cutProj D (lab u)))
    {a b : D} (Wf : GraphWalk F.toGraph a b)
    (ha : a = lab start) (hb : b = lab (gm06Find4Target start steps q))
    (hWfs : Wf.IsSimple)
    (hWfV : ∀ y ∈ Wf.support, ∃ u : Fin n,
      gm06CandidateVertex incV upper (gm06Find4PathVertices start steps) q u.val = true ∧ lab u = y)
    (hWfE : ∀ e ∈ Wf.edges, e ⊆ cutRc G D ∧ e ∈ cutEok G D)
    {a' b' : ClosedCylinder} (Wc : GraphWalk G.toGraph a' b')
    (ha' : a' = cutProj D a) (hb' : b' = cutProj D b)
    (hWcsupp : Wc.support = Wf.support.map (cutProj D))
    (hWcU : (walkDrawing G Wc).U = cutProj D '' (walkDrawing F Wf).U)
    {crow : List ℕ} (hWcenc : GM06WalkDartEncoding G.toGraph tagged vertex edge Wc crow) :
    ∃ L' : CylinderLinkage 1 G, Section5Reduction4Step 1 G L G L' ∧
      GM06LinkageRowsEncoding L' tagged vertex edge (rows.set 0 (crow ++ path.drop q)) := by
  classical
  subst hb
  obtain ⟨hP1F, hP2F, hf, hRc, hsR, hPB⟩ := onePath_setting L hG hθ hD hBd hstrip F hFU hFV hEdges
  obtain ⟨W, hWs, hWV, hWsupp, hWedges⟩ := rep.path_walk
  obtain ⟨hq1, hql, hinc⟩ := contact_target_inc hq
  have hpre : gm06PrefixOK incV incE start.val
      ((steps.map (fun st => (st.1, st.2.val))).take q) = false := by
    rw [mem_gm06Reduction4Contacts_iff] at hq
    obtain ⟨q', -, rfl, -, hpre⟩ := hq
    exact hpre
  obtain ⟨P_sv, -, hx, hsub, -, hpreIff, -, -, -⟩ :=
    gen_find4_contact rep hP1F hf hRc hsR hPB hWs hWV hWsupp hWedges hq1 hql
  have hlen : W.length = steps.length := by
    rw [GraphWalk.length, hWedges, List.length_map]
  obtain ⟨z, -, W₂, hz, -, h2, -, h4⟩ := GraphWalk.exists_split_take_drop W q (by omega)
  obtain rfl : z = lab (gm06Find4Target start steps q) := Option.some.inj (hz.symm.trans hx)
  have htail := genTail_of_split hWs hz h2 h4
  have hvP : lab (gm06Find4Target start steps q) ∈ (cutSide L hG F 1).V := by
    rw [hWV]; exact List.mem_of_getElem? hx
  have hcand : ∀ y ∈ Wf.support, IsGenCandVertex F (cutRc G D) (cutSide L hG F 2).U
      (walkDrawing (cutSide L hG F 1) W₂) (lab (gm06Find4Target start steps q)) y := by
    intro y hy
    obtain ⟨u, hu, rfl⟩ := hWfV y hy
    exact (gen_candidateVertex_iff rep hP1F hWs hWsupp hz h2 u
      ((gm06CandidateVertex_iff _ _ _ _ _).mp hu).1).mp hu
  have hlabs : lab start = cutLiftCurve L hG hBd 0 := by
    have := hWsupp ▸ GraphWalk.support_getElem?_zero W
    simpa [find4PathLabels] using this
  rw [hlabs] at ha
  subst ha
  have hsv : cutLiftCurve L hG hBd 0 ≠ lab (gm06Find4Target start steps q) :=
    isPathDrawing_start_ne_end hsub.2.2
  have hWfnd : Wf.support.Nodup := hWfs
  have hQ := isPathDrawing_walkDrawing_of_isSimple F hWfs hsv
  have hQR : (walkDrawing F Wf).U ⊆ cutRc G D := by
    intro y hy
    rw [mem_walkDrawing_U] at hy
    rcases hy with hy | ⟨e, he, hye⟩
    · exact (hcand y hy).2.1
    · exact closure_minimal (hWfE e he).1 hRc hye
  have hTG := isSubdrawing_of_genTail hP1F hvP htail
  have hQT : (walkDrawing F Wf).U ∩ (walkDrawing (cutSide L hG F 1) W₂).U ⊆
      {lab (gm06Find4Target start steps q)} :=
    walkDrawing_inter_U_subset hTG Wf hWfnd subsingleton_singleton
      fun y hy hyT => (hcand y hy).2.2.2 hyT
  have hQB : Disjoint (walkDrawing F Wf).U (cutSide L hG F 2).U := by
    rw [disjoint_iff_inter_eq_empty, ← subset_empty_iff]
    exact walkDrawing_inter_U_subset hP2F Wf hWfnd subsingleton_empty
      fun y hy hyB => absurd hyB (hcand y hy).2.2.1
  have hpre' : ¬ P_sv.U ⊆ cutRc G D := by
    rw [hpreIff]
    simpa using hpre
  obtain ⟨u, hvu, hu, huV, hpreC, hright, hR, hQTf⟩ := onePath_cut_path_data L hG hθ hD hBd hstrip
    F hFU hFV hEdges hvP hsub hpre' htail hQ hQR hQT hQB
  rw [cutProj_cutLiftCurve, (L.curve_parametrizes 0).2.2.1] at ha'
  rw [hvu, cutProj_cutLiftCurve] at hb'
  subst ha' hb'
  -- the tail of `P₁` from `v`, as the suffix of `WP`
  obtain ⟨z', -, B, -, hBenc, hz', -, hBS, -, hBE⟩ := hWPenc.exists_split_take_drop q (by omega)
  have hz'v : z' = L.curve 0 u := by
    rw [hWPsupp, List.getElem?_map, find4PathLabels_getElem?_target start steps hq1 hql] at hz'
    simp only [Option.map_some, Option.some.injEq] at hz'
    rw [← hz', hvu, cutProj_cutLiftCurve]
  subst hz'v
  obtain ⟨WP', hs', he'⟩ := (L.isSubdrawing 0).1.exists_walk_down WP
    (fun v hv => by rw [← hWPdraw, walkDrawing_V]; exact hv)
    (fun e he => by rw [← hWPdraw, walkDrawing_E]; exact he)
  have hWP's : WP'.IsSimple := by
    unfold GraphWalk.IsSimple; rw [hs']; exact hWPs
  have hWP'len : q ≤ WP'.length := by
    have h1 := GraphWalk.support_length WP'
    rw [hs', hWPsupp] at h1
    simp only [find4PathLabels, List.length_map, List.length_cons] at h1
    omega
  obtain ⟨z'', -, B', hz'', -, h2', -, h4'⟩ := GraphWalk.exists_split_take_drop WP' q hWP'len
  have hz''v : z'' = L.curve 0 u := by
    rw [hs'] at hz''
    rw [hWPsupp, List.getElem?_map, find4PathLabels_getElem?_target start steps hq1 hql] at hz''
    simp only [Option.map_some, Option.some.injEq] at hz''
    rw [← hz'', hvu, cutProj_cutLiftCurve]
  subst hz''v
  have hT : IsSection5Tail (L.pathDrawing 0) (walkDrawing (L.pathDrawing 0) B') (L.curve 0 u)
      (L.curve 0 1) := genTail_of_split hWP's hz'' h2' h4'
  have hTU : (walkDrawing (L.pathDrawing 0) B').U = (walkDrawing G B).U := by
    ext y
    rw [mem_walkDrawing_U, mem_walkDrawing_U, h2', h4', hBS, hBE, hs', he']
  have hQTG := hQTf _ hT
  -- the joined walk is simple
  have hinj := injOn_cutProj_of_not_mem_right L hG hθ hD hBd hstrip hright
  have hWcnd : Wc.support.Nodup := by
    rw [hWcsupp]
    exact hWfnd.map_on fun x hx y hy hxy =>
      hinj ((mem_walkDrawing_U F Wf).mpr (Or.inl hx)) ((mem_walkDrawing_U F Wf).mpr (Or.inl hy)) hxy
  have hBnd : B.support.Nodup := by
    rw [hBS]; exact (show WP.support.Nodup from hWPs).sublist (List.drop_sublist _ _)
  have hWf : (Wc.append B).IsSimple := by
    unfold GraphWalk.IsSimple
    rw [GraphWalk.support_append]
    refine List.Nodup.append hWcnd (hBnd.sublist (List.tail_sublist _)) ?_
    intro y hyc hyB
    have hyz : y ≠ L.curve 0 u := by
      rintro rfl
      rw [B.support_eq_cons] at hBnd
      exact (List.nodup_cons.mp hBnd).1 hyB
    have hyT : y ∈ (walkDrawing (L.pathDrawing 0) B').U := by
      rw [hTU]
      exact (mem_walkDrawing_U G B).mpr (Or.inl (List.mem_of_mem_tail hyB))
    have hyQ : y ∈ cutProj D '' (walkDrawing F Wf).U := by
      rw [hWcsupp] at hyc
      obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hyc
      exact ⟨p, (mem_walkDrawing_U F Wf).mpr (Or.inl hp), rfl⟩
    exact hyz (hQTG ⟨hyQ, hyT⟩)
  have hWU : (walkDrawing G (Wc.append B)).U =
      cutProj D '' (walkDrawing F Wf).U ∪ (walkDrawing (L.pathDrawing 0) B').U := by
    rw [← hWcU, hTU]
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
  exact exists_encoded_reduction4Step_one_of_cut_path L hG hθ hD hBd hstrip hFV
    ⟨walkDrawing_isSubdrawing F Wf, (walkDrawing_isSubdrawing F Wf).U_subset, hQ⟩
    (cutLiftCurve_zero L hG hBd) hu huV (by rw [hvu, cutLiftCurve_val]) hright
    (fun ec hec => by rw [walkDrawing_E] at hec; exact (hWfE ec hec).2) hR hpreC hT hrows
    (Wc.append B) hWf (hWcenc.append hBenc) hWU

end CutLevel

namespace GM06CurrentDrawingRep

variable {x : GM06SuccessorInput} {L : CylinderLinkage 1 G} (rep : GM06CurrentDrawingRep x G L)

local notation "currentCut" => gm06CutDataOfLinkage x.vertexCount rep.tagged.length x.endpoints
  x.linkage x.innerCuff x.outerCuff x.rotations (List.range x.vertexCount)
local notation "edgeCount" => 2 * (rep.tagged.length + (1 + 1))

/-- **The Reduction 4 phase is sound for one path, with its rows** (VI (5.7), page 133, `k = 1`).
If the phase reports a rerouting, its new rows encode a linkage `M` of the same drawing with a
Reduction 4 step from `L`. The rows are the actual output of APPLY_4: the projected darts of the
returned walk followed by the suffix of the old row. -/
theorem reduction4Phase_one_sound_rows (hG : IsCylinderSection5Drawing 1 G)
    (hno : ∀ (G₁ : Drawing ClosedCylinder) (L₁ : CylinderLinkage 1 G₁),
      IsCylinderSection5Drawing 1 G₁ → ¬ Section5Reduction2Step 1 G L G₁ L₁)
    (hθ : L.HasTheta θ) (h : (gm06Reduction4Phase x rep.tagged.length).1 = true) :
    ∃ M : CylinderLinkage 1 G, Section5Reduction4Step 1 G L G M ∧
      GM06LinkageRowsEncoding M rep.tagged rep.vertex rep.edge
        (gm06Reduction4Phase x rep.tagged.length).2 := by
  classical
  have hn : 0 < x.vertexCount := Nat.zero_lt_of_lt (rep.source 0).isLt
  cases hw : gm06Reduction4PhaseWitness x rep.tagged.length with
  | none =>
    rw [gm06Reduction4Phase_of_none hw] at h
    simp at h
  | some w =>
  obtain ⟨i, j, darts⟩ := w
  rw [gm06Reduction4Phase_of_some hw]
  obtain ⟨hi, hat⟩ := gm06Reduction4PhaseWitness_some hw
  rw [rep.cuff_lengths.1] at hi
  have hi0 : i = 0 := by omega
  subst hi0
  obtain ⟨D, hD, hBd, hstrip, -⟩ := exists_cover_strip_disc_sheet L hG hθ 1
  obtain ⟨F, hFU, hFV, hEdges⟩ := exists_augmented_drawing_on_single_strip L hG hθ hD hBd hstrip
  obtain ⟨row, hact, hphase, hrep⟩ :=
    rep.onePath_phase_find4_rep hn hG hno hθ hD hBd hstrip F hFU hFV hEdges
  rw [hphase] at hat
  obtain ⟨hj, hwalk, hnodup, hcand⟩ := gm06Find4Darts_sound _ _ _ _ _ _ _
    rep.cut_origin_table_length rep.cut_origin_table_bounds j darts hat
  obtain ⟨hj1, hjl, hinc⟩ := contact_target_inc hj
  set start := gm06CutVertexFin x.vertexCount hn (x.innerCuff[0]?.getD 0) true with hstart
  set steps := gm06CutPathSteps x.vertexCount hn x.endpoints (x.linkage[0]?.getD []) true
    with hsteps
  have hwalk' : GM06DartWalk (fun d => (currentCut).origins[d]?.getD 0)
      (fun d => (currentCut).origins[gm06DartMate d]?.getD 0) start.val darts
      (gm06Find4Target start steps j).val := hwalk
  -- the start is not the contact, so the returned row is nonempty
  have hst : start ≠ gm06Find4Target start steps j := by
    intro he
    obtain ⟨W, hWs, -, hWsupp, -⟩ := hrep.path_walk
    have hs0 : W.support[0]? = some (rep.cutLab hG hBd start) := by
      rw [hWsupp]
      simp [find4PathLabels]
    have hx : W.support[j]? = some (rep.cutLab hG hBd start) := by
      rw [hWsupp, List.getElem?_map, find4PathLabels_getElem?_target start steps hj1 hjl, ← he]
      rfl
    have := nodup_index_eq_of_getElem? hWs hs0 hx
    omega
  have hne : darts ≠ [] := by
    rintro rfl
    have hst' : ∀ {s t : ℕ}, GM06DartWalk (fun d => (currentCut).origins[d]?.getD 0)
        (fun d => (currentCut).origins[gm06DartMate d]?.getD 0) s [] t → s = t :=
      fun h => by cases h; rfl
    exact hst (Fin.ext (hst' hwalk'))
  -- the endpoints of the returned darts pass the candidate test
  have hends : ∀ v ∈ gm06WalkVertices (fun d => (currentCut).origins[gm06DartMate d]?.getD 0)
      start.val darts, v < 2 * x.vertexCount ∧
        gm06CandidateVertex (gm06IncV (2 * x.vertexCount) (currentCut).origins row)
          (gm06PhaseBoundaryVertices x (gm06PhaseNext x 0) 1)
          (gm06Find4PathVertices start steps) j v = true :=
    GM06DartWalk.vertices_of_endpoints hwalk' hne fun d hd => by
      have hh := candidateDart_ends _ _ _ _ _ _ _ _ _ (hcand d hd)
      exact ⟨⟨rep.cut_origin_getD_lt hn d, hh.2.2.2.1⟩,
        ⟨rep.cut_origin_getD_lt hn _, hh.2.2.2.2⟩⟩
  -- the walk of the cut drawing traced by the returned darts
  let labN : ℕ → D := fun v => if hv : v < 2 * x.vertexCount then rep.cutLab hG hBd ⟨v, hv⟩
    else cutLiftCurve L hG hBd 0
  have hlabN : ∀ v : Fin (2 * x.vertexCount), labN v.val = rep.cutLab hG hBd v := fun v => by
    simp [labN, v.isLt]
  have hl : ∀ d ∈ darts, F.toGraph.IsLink (rep.cutEdgeLab hG (d / 2))
      (labN ((currentCut).origins[d]?.getD 0))
      (labN ((currentCut).origins[gm06DartMate d]?.getD 0)) := by
    intro d hd
    have hh := candidateDart_ends _ _ _ _ _ _ _ _ _ (hcand d hd)
    obtain ⟨u, w, hends, -, -, hlink⟩ := hrep.edge_sound (d / 2) hh.2.1 hh.2.2.1
    rw [gm06CandidateEnds_get _ (by omega : d / 2 < edgeCount)] at hends
    simp only [Prod.mk.injEq] at hends
    rw [← hlabN u, ← hlabN w] at hlink
    unfold gm06DartMate
    rcases Nat.mod_two_eq_zero_or_one d with hpar | hpar
    · rw [show 2 * (d / 2) = d by omega] at hends
      simp only [hpar, ↓reduceIte]
      rw [hends.1, hends.2]
      exact hlink
    · rw [show 2 * (d / 2) = d - 1 by omega, show d - 1 + 1 = d by omega] at hends
      have hodd : ¬ d % 2 = 0 := by omega
      simp only [hodd, ↓reduceIte]
      rw [hends.1, hends.2]
      exact hlink.symm
  have htF : labN (gm06Find4Target start steps j).val ∈ F.V := by
    rw [hlabN]
    exact (hrep.vertex_sound _ hinc).1
  obtain ⟨Wf, hWfsupp, hWfedges⟩ := GM06DartWalk.exists_graphWalk (Γ := F) hwalk' hl htF
  -- the projected walk of `G`, encoded by the projected darts
  have hcutPoint : ∀ v : Fin (2 * x.vertexCount), rep.cutPoint v.val = cutProj D (labN v.val) :=
    fun v => by rw [rep.cutPoint_fin, hlabN, rep.cutProj_cutLab hG hθ hD hBd hstrip]
  have htG : rep.cutPoint (gm06Find4Target start steps j).val ∈ G.V := by
    rw [rep.cutPoint_fin]
    rw [← rep.cutProj_cutLab hG hθ hD hBd hstrip]
    have := (hrep.vertex_sound _ hinc).1
    rw [hFV] at this
    exact this
  obtain ⟨Wc, hWcenc, hWcsupp, hWcedges⟩ := rep.exists_encoded_cut_walk hG hwalk' htG
    fun d hd => rep.candidate_dart_active hG row hact _ _ j d (hcand d hd)
  have hWcsupp' : Wc.support = Wf.support.map (cutProj D) := by
    rw [hWcsupp, hWfsupp, List.map_map]
    refine List.map_congr_left fun v hv => ?_
    exact hcutPoint ⟨v, (hends v hv).1⟩
  have hcl : ∀ e, cutProj D '' closure (rep.cutEdgeLab hG e) = closure (rep.cutEdgePoint e) := by
    intro e
    rw [← (isClosedMap_cutProj hD).closure_image_eq_of_continuous continuous_cutProj]
    unfold cutEdgeLab
    rw [image_cutEdgeLabel hG hθ hD hBd hstrip]
  have hWcU : (walkDrawing G Wc).U = cutProj D '' (walkDrawing F Wf).U := by
    ext y
    rw [mem_walkDrawing_U, hWcsupp', hWcedges]
    constructor
    · rintro (hy | ⟨e, he, hye⟩)
      · obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hy
        exact ⟨p, (mem_walkDrawing_U F Wf).mpr (Or.inl hp), rfl⟩
      · obtain ⟨d, hd, rfl⟩ := List.mem_map.mp he
        rw [← hcl] at hye
        obtain ⟨p, hp, rfl⟩ := hye
        exact ⟨p, (mem_walkDrawing_U F Wf).mpr
          (Or.inr ⟨_, hWfedges ▸ List.mem_map_of_mem hd, hp⟩), rfl⟩
    · rintro ⟨p, hp, rfl⟩
      rcases (mem_walkDrawing_U F Wf).mp hp with hp | ⟨e, he, hpe⟩
      · exact Or.inl (List.mem_map_of_mem hp)
      · rw [hWfedges] at he
        obtain ⟨d, hd, rfl⟩ := List.mem_map.mp he
        exact Or.inr ⟨_, List.mem_map_of_mem hd, hcl _ ▸ ⟨p, hpe, rfl⟩⟩
  -- the walk of the cut drawing has the properties of `exists_encoded_reduction4_one_of_cut_walk`
  have hWfs : Wf.IsSimple := by
    unfold GraphWalk.IsSimple
    rw [hWfsupp]
    refine List.Nodup.map_on ?_ hnodup
    intro a ha b hb hab
    obtain ⟨ha', hac⟩ := hends a ha
    obtain ⟨hb', hbc⟩ := hends b hb
    have e1 := hlabN ⟨a, ha'⟩
    have e2 := hlabN ⟨b, hb'⟩
    have := hrep.inj ⟨a, ha'⟩ ⟨b, hb'⟩ (Or.inl ((gm06CandidateVertex_iff _ _ _ _ _).mp hac).1)
      (Or.inl ((gm06CandidateVertex_iff _ _ _ _ _).mp hbc).1) (e1.symm.trans (hab.trans e2))
    exact congrArg Fin.val this
  have hWfV : ∀ y ∈ Wf.support, ∃ u : Fin (2 * x.vertexCount),
      gm06CandidateVertex (gm06IncV (2 * x.vertexCount) (currentCut).origins row)
        (gm06PhaseBoundaryVertices x (gm06PhaseNext x 0) 1)
        (gm06Find4PathVertices start steps) j u.val = true ∧ rep.cutLab hG hBd u = y := by
    intro y hy
    rw [hWfsupp] at hy
    obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hy
    obtain ⟨hvb, hvc⟩ := hends v hv
    exact ⟨⟨v, hvb⟩, hvc, (hlabN ⟨v, hvb⟩).symm⟩
  have hWfE : ∀ e ∈ Wf.edges, e ⊆ cutRc G D ∧ e ∈ cutEok G D := by
    intro e he
    rw [hWfedges] at he
    obtain ⟨d, hd, rfl⟩ := List.mem_map.mp he
    have hh := candidateDart_ends _ _ _ _ _ _ _ _ _ (hcand d hd)
    obtain ⟨-, -, -, hsub, hok, -⟩ := hrep.edge_sound (d / 2) hh.2.1 hh.2.2.1
    exact ⟨hsub, hok⟩
  -- the encoded walk tracing the old path
  have hpathEq : x.linkage[0]?.getD [] = x.linkage[0]'(by rw [rep.linkage.1]; exact one_pos) := by
    rw [List.getElem?_eq_getElem (show 0 < x.linkage.length by rw [rep.linkage.1]; exact one_pos)]
    rfl
  have hsource : x.innerCuff[0]?.getD 0 = (rep.source 0).val := by
    rw [rep.inner]
    simp only [List.getElem?_ofFn]
    rfl
  obtain ⟨WP, hWPs, hWPenc, hWPdraw, -, hWPsupp, -⟩ := rep.computed_encoded_path_walk hn 0 true
  simp only [Fin.val_zero] at hWPsupp hWPenc
  rw [← hpathEq, ← hsource] at hWPsupp
  rw [← hpathEq] at hWPenc
  have hWPsupp' : WP.support =
      (find4PathLabels start steps).map (fun u => cutProj D (rep.cutLab hG hBd u)) := by
    rw [hWPsupp]
    have hf : (fun u => cutProj D (rep.cutLab hG hBd u)) = rep.cutVertexPoint :=
      funext (rep.cutProj_cutLab hG hθ hD hBd hstrip)
    rw [hf]
    rfl
  have hlen : (x.linkage[0]?.getD []).length = steps.length := by
    rw [hsteps, gm06CutPathSteps, List.length_map]
  exact exists_encoded_reduction4_one_of_cut_walk L hG hθ hD hBd hstrip F hFU hFV hEdges hrep hj
    rep.linkage hlen hWPs hWPenc hWPdraw hWPsupp' Wf (hlabN start) (hlabN _) hWfs hWfV hWfE Wc
    (hcutPoint start) (hcutPoint _) hWcsupp' hWcU hWcenc

end GM06CurrentDrawingRep

end GraphMinor.GM06
