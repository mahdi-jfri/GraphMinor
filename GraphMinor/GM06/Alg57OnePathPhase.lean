module

public import GraphMinor.GM06.Alg57OnePathEdgeSlots
public import GraphMinor.GM06.Alg57CurrentPhaseInputs
import GraphMinor.GM06.Section5CoverStripDiscSheet
import GraphMinor.GM06.Section5CutStripBoundary
import GraphMinor.GM06.Alg57OnePathReduction4
import GraphMinor.GM06.Alg57CurrentCandidateRows

/-!
# The Reduction 4 phase for one path

For one path (`k = 1`) the Reduction 4 phase of VI (5.7), page 133, runs `FIND_4` on the cut face
orbit of `c̄₁`. Here we show that the lists it uses represent the one-path search of
`Alg57OnePathFind4.lean` (`onePath_phase_find4_rep`): the vertex slots name the points
`cutLab`, the edge labels name the sets `cutEdgeLab`, the start and the steps are the left copy
of `P₁`, and the upper boundary is its right copy. Then the phase is sound and complete
(`reduction4Phase_one_sound`, `reduction4Phase_one_complete`).
-/

@[expose] public section

namespace GraphMinor.GM06

open Set Topology GraphMinor.Surface GraphMinor.GM11 GraphMinor.Compute unitInterval

variable {G : Drawing ClosedCylinder} {θ : ℝ} {D : Set (ℝ × ℝ)}

namespace GM06CurrentDrawingRep

variable {x : GM06SuccessorInput} {L : CylinderLinkage 1 G} (rep : GM06CurrentDrawingRep x G L)

local notation "cutTables" => gm06BuildCutTables x.vertexCount rep.tagged.length x.endpoints
  x.linkage x.innerCuff x.outerCuff
local notation "cutNext" => Equiv.trans dartMatePerm
  (Equiv.symm (gm06RotationPermutation (gm06SplitRotationRows cutTables x.rotations)))
local notation "gapCut" => gm06CutDart (2 * rep.tagged.length + 1) 0
local notation "currentCut" => gm06CutDataOfLinkage x.vertexCount rep.tagged.length x.endpoints
  x.linkage x.innerCuff x.outerCuff x.rotations (List.range x.vertexCount)
local notation "edgeCount" => 2 * (rep.tagged.length + (1 + 1))

/-- **The lists of the one-path phase represent the one-path search.** For one path, after
failure of Reduction 2, the query of the Reduction 4 phase is `FIND_4` on lists that satisfy
`Find4Rep1` with the labels `cutLab` and `cutEdgeLab`, for any cut disc `D` and cut drawing `F`
of the strip. Every dart of the face row is active. -/
theorem onePath_phase_find4_rep (hn : 0 < x.vertexCount) (hG : IsCylinderSection5Drawing 1 G)
    (hno : ∀ (G₁ : Drawing ClosedCylinder) (L₁ : CylinderLinkage 1 G₁),
      IsCylinderSection5Drawing 1 G₁ → ¬ Section5Reduction2Step 1 G L G₁ L₁)
    (hθ : L.HasTheta θ) (hD : IsClosedDisc D) (hBd : discBd D = liftedStripBoundary hG.1 L 1)
    (hstrip : D ⊆ {p : ℝ × ℝ | 1 ≤ p.1 ∧ p.1 ≤ 2}) (F : Drawing D)
    (hFU : F.U = (fun p : D => radialCylinderProjection p.1) ⁻¹' G.U ∪ bd D)
    (hFV : F.V = (fun p : D => radialCylinderProjection p.1) ⁻¹' G.V)
    (hEdges : ∀ ec ∈ F.E, ec ⊆ bd D ∨
      ∃ e ∈ G.E \ (L.pathDrawing 0).E, ec = (fun p : D => radialCylinderProjection p.1) ⁻¹' e) :
    ∃ row : List ℕ, (∀ r ∈ row, r ∈ (currentCut).activeDarts) ∧
      gm06Reduction4PhaseAt x rep.tagged.length 0 =
        gm06Find4Darts edgeCount (currentCut).origins
          (gm06CandidateOrdinary edgeCount rep.tagged.length)
          (gm06IncV (2 * x.vertexCount) (currentCut).origins row) (gm06IncE edgeCount row)
          (gm06PhaseBoundaryVertices x (gm06PhaseNext x 0) 1)
          (gm06CutVertexFin x.vertexCount hn (x.innerCuff[0]?.getD 0) true)
          (gm06CutPathSteps x.vertexCount hn x.endpoints (x.linkage[0]?.getD []) true) ∧
      Find4Rep1 L hG F (cutLiftCurve L hG hBd 0) (cutLiftCurve L hG hBd 1)
        (gm06CandidateEnds edgeCount (currentCut).origins)
        (gm06CandidateOrdinary edgeCount rep.tagged.length)
        (gm06IncV (2 * x.vertexCount) (currentCut).origins row) (gm06IncE edgeCount row)
        (gm06PhaseBoundaryVertices x (gm06PhaseNext x 0) 1)
        (gm06CutVertexFin x.vertexCount hn (x.innerCuff[0]?.getD 0) true)
        (gm06CutPathSteps x.vertexCount hn x.endpoints (x.linkage[0]?.getD []) true)
        (rep.cutLab hG hBd) (rep.cutEdgeLab hG) := by
  obtain ⟨U₁, U₂, hU₁, hU₂, hU, h₁, h₂⟩ := exists_side_sets L hG
  obtain ⟨R, hR, hccw, -, hrot, heI, heO, hV, -⟩ := rep.one_path_setting_red2 hG hno
  obtain ⟨root, hroot, row, hout, horbit⟩ := rep.component_cut_face_row hG 0
  have hact := rep.component_query_row_active hG 0 root hroot row hout
  have hcode : gm06CutDart (2 * rep.tagged.length + 1) 0 =
      4 * (rep.tagged.length + (0 : Fin 1).val) + 1 := by
    simp only [gm06CutDart, Fin.val_zero]
    omega
  have horbit' : ∀ q, q ∈ row ↔ ∃ n, cutNext^[n] gapCut = q := by
    intro q
    rw [hcode]
    exact horbit q
  refine ⟨row, hact, ?_, ?_⟩
  · obtain ⟨root', hroot', hpart⟩ := rep.phase_component_at hG 0
    have he : root' = root := Fin.ext (hroot'.trans hroot.symm)
    subst root'
    simp only [Fin.val_zero] at hpart
    unfold gm06Reduction4PhaseAt
    rw [hpart]
    simp only [Option.bind_some, gm06Reduction4PhaseComponent, rep.cuff_lengths.1,
      rep.cuff_lengths.2, Nat.add_assoc]
    simp only [Fin.val_zero] at hout
    rw [hout]
    change gm06PhaseFind4Words (2 * x.vertexCount) edgeCount (currentCut).origins _ _ _ _ _ _ = _
    have hs : x.innerCuff[0]?.getD 0 < x.vertexCount := by
      rw [rep.inner]
      simp only [List.getElem?_ofFn]
      exact (rep.source 0).isLt
    have hv := cutVertexFin_val hn hs true
    simp only [gm06CutVertex, Bool.not_true, Bool.toNat_false, Nat.add_zero] at hv
    have hsteps := rep.computed_path_steps_phase hn (0 : Fin 1)
    simp only [Fin.val_zero] at hsteps
    rw [← hv, ← hsteps]
    exact gm06PhaseFind4Words_eq _ _ _ _ _ _ _
  · have hpath : x.linkage[0]?.getD [] = x.linkage[0]'(by rw [rep.linkage.1]; exact one_pos) := by
      rw [List.getElem?_eq_getElem (show 0 < x.linkage.length by rw [rep.linkage.1]; exact one_pos)]
      rfl
    have hsource : x.innerCuff[0]?.getD 0 = (rep.source 0).val := by
      rw [rep.inner]
      simp only [List.getElem?_ofFn]
      rfl
    have hupper : gm06PhaseBoundaryVertices x (gm06PhaseNext x 0) 1 =
        (gm06CutPathLabels x.vertexCount hn x.endpoints
          (x.linkage[0]'(by rw [rep.linkage.1]; exact one_pos)) (rep.source 0).val false).map
          Fin.val := by
      have h := rep.computed_path_labels_phase hn (0 : Fin 1) false
      have hnext := rep.phase_next_eq (0 : Fin 1)
      simp only [Fin.val_eq_zero, Bool.not_false, Bool.toNat_true] at h hnext
      rw [hnext, ← h, hpath, hsource]
    rw [← cutOrdinaryFlags_eq_candidate, hupper, hpath, hsource]
    exact {
      vertex_sound := rep.slots_vertex_sound hG hno hθ hD hBd hstrip row horbit' F hFV
      vertex_cover := rep.slots_vertex_cover hG hno hθ hD hBd hstrip row horbit' F hFV
      inj := rep.slots_inj hG hno hθ hD hBd hstrip hn row horbit'
      upper_iff := rep.slots_upper_iff hG hθ hD hBd hstrip hn row horbit' F hFU hFV hEdges
      edge_sound := rep.slots_edge_sound hG hno hθ hD hBd hstrip hU₁ hU₂ hU h₁ h₂ hR hccw hrot heI
        heO hV F hFU hFV hEdges row horbit'
      edge_cover := fun f a b hf _ hfR hfE => rep.slots_edge_cover hG hno hθ hD hBd hstrip hU₁ hU₂
        hU h₁ h₂ hR hccw hrot heI heO hV F hFU hFV hEdges row horbit' f a b hf hfR hfE
      path_walk := rep.slots_path_walk hG hθ hD hBd hstrip hn F hFU hFV hEdges
      path_incV := rep.slots_path_incV hG hno hθ hD hBd hstrip hn row horbit'
      path_incE := rep.slots_path_incE hG hno hθ hD hBd hstrip hn row horbit' }

/-- **The one-path phase reads `FIND_4`.** There is a cut disc and a cut drawing for which the
query of the Reduction 4 phase is `FIND_4` on lists that satisfy `Find4Rep1`. -/
theorem onePath_phase_find4 (hn : 0 < x.vertexCount) (hG : IsCylinderSection5Drawing 1 G)
    (hno : ∀ (G₁ : Drawing ClosedCylinder) (L₁ : CylinderLinkage 1 G₁),
      IsCylinderSection5Drawing 1 G₁ → ¬ Section5Reduction2Step 1 G L G₁ L₁)
    (hθ : L.HasTheta θ) :
    ∃ (D : Set (ℝ × ℝ)) (_ : IsClosedDisc D) (hBd : discBd D = liftedStripBoundary hG.1 L 1)
      (_ : D ⊆ {p : ℝ × ℝ | 1 ≤ p.1 ∧ p.1 ≤ 2}) (F : Drawing D)
      (_ : F.U = (fun p : D => radialCylinderProjection p.1) ⁻¹' G.U ∪ bd D)
      (_ : F.V = (fun p : D => radialCylinderProjection p.1) ⁻¹' G.V)
      (_ : ∀ ec ∈ F.E, ec ⊆ bd D ∨
        ∃ e ∈ G.E \ (L.pathDrawing 0).E, ec = (fun p : D => radialCylinderProjection p.1) ⁻¹' e)
      (row : List ℕ),
      gm06Reduction4PhaseAt x rep.tagged.length 0 =
        gm06Find4Darts edgeCount (currentCut).origins
          (gm06CandidateOrdinary edgeCount rep.tagged.length)
          (gm06IncV (2 * x.vertexCount) (currentCut).origins row) (gm06IncE edgeCount row)
          (gm06PhaseBoundaryVertices x (gm06PhaseNext x 0) 1)
          (gm06CutVertexFin x.vertexCount hn (x.innerCuff[0]?.getD 0) true)
          (gm06CutPathSteps x.vertexCount hn x.endpoints (x.linkage[0]?.getD []) true) ∧
      Find4Rep1 L hG F (cutLiftCurve L hG hBd 0) (cutLiftCurve L hG hBd 1)
        (gm06CandidateEnds edgeCount (currentCut).origins)
        (gm06CandidateOrdinary edgeCount rep.tagged.length)
        (gm06IncV (2 * x.vertexCount) (currentCut).origins row) (gm06IncE edgeCount row)
        (gm06PhaseBoundaryVertices x (gm06PhaseNext x 0) 1)
        (gm06CutVertexFin x.vertexCount hn (x.innerCuff[0]?.getD 0) true)
        (gm06CutPathSteps x.vertexCount hn x.endpoints (x.linkage[0]?.getD []) true)
        (rep.cutLab hG hBd) (rep.cutEdgeLab hG) := by
  obtain ⟨D, hD, hBd, hstrip, -⟩ := exists_cover_strip_disc_sheet L hG hθ 1
  obtain ⟨F, hFU, hFV, hEdges⟩ := exists_augmented_drawing_on_single_strip L hG hθ hD hBd hstrip
  obtain ⟨row, -, h1, h2⟩ := rep.onePath_phase_find4_rep hn hG hno hθ hD hBd hstrip F hFU hFV hEdges
  exact ⟨D, hD, hBd, hstrip, F, hFU, hFV, hEdges, row, h1, h2⟩

/-- **The Reduction 4 phase is complete for one path** (VI (5.7), page 133, `k = 1`). If the phase
reports no rerouting, no Reduction 4 step exists. This needs that Reductions 1 and 2 do not apply
and that `s₁` does not have valency one. -/
theorem reduction4Phase_one_complete (hG : IsCylinderSection5Drawing 1 G)
    (hno1 : ∀ (H : Drawing ClosedCylinder) (M : CylinderLinkage 1 H),
      IsCylinderSection5Drawing 1 H → ¬ Section5Reduction1Step 1 G L H M)
    (hno2 : ∀ (H : Drawing ClosedCylinder) (M : CylinderLinkage 1 H),
      IsCylinderSection5Drawing 1 H → ¬ Section5Reduction2Step 1 G L H M)
    (hval : vertexValency G.toGraph (cylinderM1Point 1 0) ≠ 1) (hθ : L.HasTheta θ)
    (h : (gm06Reduction4Phase x rep.tagged.length).1 = false) :
    ¬ ∃ M : CylinderLinkage 1 G, Section5Reduction4Step 1 G L G M := by
  have hn : 0 < x.vertexCount := Nat.zero_lt_of_lt (rep.source 0).isLt
  have hw : gm06Reduction4PhaseWitness x rep.tagged.length = none := by
    cases hw : gm06Reduction4PhaseWitness x rep.tagged.length with
    | none => rfl
    | some w =>
      obtain ⟨i, j, d⟩ := w
      rw [gm06Reduction4Phase_of_some hw] at h
      simp at h
  have hnone := (gm06Reduction4PhaseWitness_none_iff x _).mp hw 0
    (by rw [rep.cuff_lengths.1]; exact one_pos)
  obtain ⟨D, hD, hBd, hstrip, F, hFU, hFV, hEdges, row, hphase, hrep⟩ :=
    rep.onePath_phase_find4 hn hG hno2 hθ
  rw [hphase, gm06Find4Darts, Option.map_eq_none_iff] at hnone
  exact not_exists_reduction4Step_one_of_find4_none L hG hθ hD hBd hstrip F hFU hFV hEdges hno1
    hno2 hval rfl rfl hrep hnone

/-- **The Reduction 4 phase finds a step for one path** (VI (5.7), page 133, `k = 1`). If the
phase reports a rerouting, a Reduction 4 step exists. -/
theorem reduction4Phase_one_sound (hG : IsCylinderSection5Drawing 1 G)
    (hno : ∀ (G₁ : Drawing ClosedCylinder) (L₁ : CylinderLinkage 1 G₁),
      IsCylinderSection5Drawing 1 G₁ → ¬ Section5Reduction2Step 1 G L G₁ L₁)
    (hθ : L.HasTheta θ) (h : (gm06Reduction4Phase x rep.tagged.length).1 = true) :
    ∃ M : CylinderLinkage 1 G, Section5Reduction4Step 1 G L G M := by
  have hn : 0 < x.vertexCount := Nat.zero_lt_of_lt (rep.source 0).isLt
  cases hw : gm06Reduction4PhaseWitness x rep.tagged.length with
  | none =>
    rw [gm06Reduction4Phase_of_none hw] at h
    simp at h
  | some w =>
    obtain ⟨i, j, darts⟩ := w
    obtain ⟨hi, hat⟩ := gm06Reduction4PhaseWitness_some hw
    rw [rep.cuff_lengths.1] at hi
    have hi0 : i = 0 := by omega
    subst hi0
    obtain ⟨D, hD, hBd, hstrip, F, hFU, hFV, hEdges, row, hphase, hrep⟩ :=
      rep.onePath_phase_find4 hn hG hno hθ
    rw [hphase, gm06Find4Darts, Option.map_eq_some_iff] at hat
    obtain ⟨⟨j', path⟩, hfind, -⟩ := hat
    exact exists_reduction4Step_one_of_find4_some L hG hθ hD hBd hstrip F hFU hFV hEdges rfl rfl
      hrep hfind

end GM06CurrentDrawingRep

end GraphMinor.GM06
