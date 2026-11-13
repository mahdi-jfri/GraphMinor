module

public import GraphMinor.GM06.Alg57CurrentCandidateRows
public import GraphMinor.GM06.Alg57Find4Link
import GraphMinor.GM06.Alg57CandidateGraph
import GraphMinor.GM06.Alg57Reduction4Complete
import GraphMinor.GM06.Section5Red
import GraphMinor.GM06.Section5EndpointObstruction

/-!
# The Reduction 4 phase of VI (5.7) in the current drawing

The Reduction 4 phase of the algorithm on page 133 cuts the current
drawing along the linkage, selects the face of each component through
the reversed inner cuff gap, and runs FIND_4 in cuff order. On the
first witness, APPLY_4 replaces the path row by the projected directed
candidate row followed by the old suffix.

We prove the two outcomes for at least two paths.

* If the phase returns bit `1`, its new rows encode a linkage `M` of the
  same drawing with `Section5Reduction4Step k G L G M`
  (`GM06CurrentDrawingRep.reduction4Phase_sound`).
* If it returns bit `0`, no Reduction 4 step exists
  (`GM06CurrentDrawingRep.reduction4Phase_complete`).

The second is a direct consequence of the representation proved in
`Alg57CurrentPhaseInputs.lean` and of `not_reduction4At_of_find4_none`.
For the first we must keep the exact rows. The returned darts form a
walk `Wc` of `G` from `sᵢ` to the contact `v` whose vertices pass the
candidate test. The suffix of the old row is the tail `T` of `Pᵢ` from
`v`. Each vertex of `Wc` other than `v` is off `T`, so `Wc` followed by
`T` is a path. Its drawing is the union of the drawings of `Wc` and
`T`, which is exactly the replacement in Reduction 4. The linkage with
this path in place of `Pᵢ` is built by
`exists_encoded_reduction4_linkage`, which keeps the encoded row.
-/

public section
namespace GraphMinor.GM06
open Set Topology GraphMinor.Surface GraphMinor.GM11 GraphMinor.Compute

variable {k : ℕ} {G : Drawing ClosedCylinder}

section Find4Level

variable {L : CylinderLinkage k G} {i : Fin k} {n : ℕ}
  {ends : List (ℕ × ℕ)} {ordinary : List Bool} {incV incE upper : List ℕ}
  {start : Fin n} {steps : List (ℕ × Fin n)}
  {lab : Fin n → ClosedCylinder} {edgeLab : ℕ → Set ClosedCylinder}

/-- A contact of FIND_4 is a positive position of the path whose
target is incident with the closed region. -/
theorem contact_target_inc {q : ℕ}
    (hq : q ∈ gm06Reduction4Contacts incV incE start.val (steps.map (fun st => (st.1, st.2.val)))) :
    1 ≤ q ∧ q ≤ steps.length ∧ incV[(gm06Find4Target start steps q).val]?.getD 0 ≠ 0 := by
  rw [mem_gm06Reduction4Contacts_iff] at hq
  obtain ⟨q', hq', rfl, hinc, -⟩ := hq
  simp only [List.length_map] at hq'
  have htgt : gm06Find4Target start steps (q' + 1) = steps[q'].2 := by
    simp [gm06Find4Target, List.getElem?_eq_getElem hq']
  refine ⟨by omega, by omega, ?_⟩
  rw [htgt]
  simpa [List.getElem?_eq_getElem hq'] using hinc

/-- The start of the path differs from the target at every positive
position, since the path labels name distinct vertices of `Pᵢ`. -/
theorem find4_start_ne_target
    (rep : Find4Rep L i ends ordinary incV incE upper start steps lab edgeLab)
    {q : ℕ} (hq1 : 1 ≤ q) (hq : q ≤ steps.length) :
    start ≠ gm06Find4Target start steps q := by
  intro h
  obtain ⟨W, hWs, -, hWsupp, -⟩ := rep.path_walk
  have hs0 : W.support[0]? = some (lab start) := by
    rw [hWsupp]
    simp [find4PathLabels]
  have hx : W.support[q]? = some (lab start) := by
    rw [hWsupp, List.getElem?_map, find4PathLabels_getElem?_target start steps hq1 hq, ← h]
    rfl
  have := nodup_index_eq_of_getElem? hWs hs0 hx
  omega

/-- **The exact Reduction 4 replacement** (`k ≥ 2`). Let `q` be a
contact of FIND_4, and let `Wc` be a simple walk of `G` from the
start of `Pᵢ` to the contact whose vertices pass the candidate test at
`q` and whose edges lie in the closure of `Rᵢ`. Let `WP` be an encoded
walk tracing `Pᵢ` along the path labels. Then the rows with the
encoding of `Wc` followed by the suffix of the row of `WP` in place of
row `i` encode a linkage `L'` with a Reduction 4 step from `L`. -/
theorem exists_encoded_reduction4_of_candidate_walk
    (rep : Find4Rep L i ends ordinary incV incE upper start steps lab edgeLab)
    (hk : 1 < k) (hG : IsCylinderSection5Drawing k G) {θ : ℝ} (hθ : L.HasTheta θ)
    {q : ℕ}
    (hq : q ∈ gm06Reduction4Contacts incV incE start.val (steps.map (fun st => (st.1, st.2.val))))
    {m : ℕ} {tagged : List ((Fin m × Fin m) × ℕ)} {vertex : Fin m → ClosedCylinder}
    {edge : Fin tagged.length → Set ClosedCylinder} {rows : List (List ℕ)}
    (hrows : GM06LinkageRowsEncoding L tagged vertex edge rows)
    {path : List ℕ} (hpath : path.length = steps.length)
    {WP : GraphWalk G.toGraph (cylinderM1Point k i) (L.curve i 1)}
    (hWPenc : GM06WalkDartEncoding G.toGraph tagged vertex edge WP path)
    (hWPsupp : WP.support = (find4PathLabels start steps).map lab)
    (hWPedges : WP.edges = steps.map (fun st => edgeLab st.1))
    {a b : ClosedCylinder} (Wc : GraphWalk G.toGraph a b)
    (ha : a = lab start) (hb : b = lab (gm06Find4Target start steps q))
    (hWcs : Wc.IsSimple)
    (hWcV : ∀ y ∈ Wc.support, ∃ u : Fin n,
      gm06CandidateVertex incV upper (gm06Find4PathVertices start steps) q u.val = true ∧ lab u = y)
    (hWcE : ∀ e ∈ Wc.edges, e ⊆ closure (cylinderRegion k G i))
    {crow : List ℕ} (hWcenc : GM06WalkDartEncoding G.toGraph tagged vertex edge Wc crow) :
    ∃ L' : CylinderLinkage k G, Section5Reduction4Step k G L G L' ∧
      GM06LinkageRowsEncoding L' tagged vertex edge (rows.set i.val (crow ++ path.drop q)) := by
  classical
  obtain ⟨W, hWs, hWV, hWsupp, hWedges⟩ := rep.path_walk
  obtain ⟨hq1, hql, hinc⟩ := contact_target_inc hq
  have hpre : gm06PrefixOK incV incE start.val
      ((steps.map (fun st => (st.1, st.2.val))).take q) = false := by
    rw [mem_gm06Reduction4Contacts_iff] at hq
    obtain ⟨q', -, rfl, -, hpre⟩ := hq
    exact hpre
  obtain ⟨P_sv, T₀, hx, hsub, -, hpreIff, -, -, -⟩ :=
    find4_contact rep hk hG hθ hWs hWV hWsupp hWedges hq1 hql
  have hvR := (rep.vertex_sound _ hinc).2
  rw [← hb] at hx hsub hvR
  -- the start of `Pᵢ`
  have hlabs : lab start = cylinderM1Point k i := by
    have := hWsupp ▸ GraphWalk.support_getElem?_zero W
    simpa [find4PathLabels] using this
  obtain rfl : a = cylinderM1Point k i := ha.trans hlabs
  -- the tail of `Pᵢ` from the contact, as the suffix of `W`
  have hlen : W.length = steps.length := by
    rw [GraphWalk.length, hWedges, List.length_map]
  obtain ⟨z, -, W₂, hz, -, h2, -, h4⟩ := GraphWalk.exists_split_take_drop W q (by omega)
  obtain rfl : z = b := Option.some.inj (hz.symm.trans hx)
  have hnd : W.support.Nodup := hWs
  have hW₂s : W₂.IsSimple := by
    unfold GraphWalk.IsSimple; rw [h2]; exact hnd.sublist (List.drop_sublist _ _)
  have hvP : z ∈ (L.pathDrawing i).V := by rw [hWV]; exact List.mem_of_getElem? hx
  have htail : IsSection5Tail (L.pathDrawing i) (walkDrawing (L.pathDrawing i) W₂) z
      (L.curve i 1) := by
    by_cases hqr : q = steps.length
    · have hl1 : W₂.support.length = 1 := by
        rw [h2, List.length_drop, GraphWalk.support_length W, hlen]; omega
      have hxt : z = L.curve i 1 := GraphWalk.eq_of_support_length_one W₂ hl1
      have hsupp : W₂.support = [z] := by
        rw [W₂.support_eq_cons] at hl1 ⊢
        simp only [List.length_cons, add_eq_right, List.length_eq_zero_iff] at hl1
        rw [hl1]
      have hedges : W₂.edges = [] := by
        rw [h4, List.drop_eq_nil_iff, hWedges, List.length_map]; omega
      refine Or.inl ⟨hxt, ?_, ?_⟩
      · ext y
        rw [mem_walkDrawing_U, hsupp, hedges]
        simp
      · rw [walkDrawing_V, hsupp]
        ext y; simp
    · have hne : z ≠ L.curve i 1 := by
        intro h
        have ht' : W.support[steps.length]? = some z := by
          rw [← hlen]; exact (GraphWalk.support_getElem?_length W).trans (congrArg some h.symm)
        exact hqr (nodup_index_eq_of_getElem? hnd hx ht')
      exact Or.inr ⟨walkDrawing_isSubdrawing (L.pathDrawing i) W₂,
        walkDrawing_U_subset (L.pathDrawing i) W₂,
        isPathDrawing_walkDrawing_of_isSimple (L.pathDrawing i) hW₂s hne⟩
  have hTG := isSubdrawing_of_section5Tail L i hvP htail
  have hsv : cylinderM1Point k i ≠ z := isPathDrawing_start_ne_end hsub.2.2
  -- the candidate walk lies in the candidate graph of the drawing
  have hcandV : ∀ y ∈ Wc.support,
      IsReduction4CandidateVertex L i (walkDrawing (L.pathDrawing i) W₂) z y := by
    intro y hy
    obtain ⟨u, hu, rfl⟩ := hWcV y hy
    exact (candidateVertex_iff rep hk hG hθ hWs hWsupp hx h2 u
      ((gm06CandidateVertex_iff _ _ _ _ _).mp hu).1).mp hu
  have hWcnd : Wc.support.Nodup := hWcs
  have hQR : (walkDrawing G Wc).U ⊆ closure (cylinderRegion k G i) := by
    intro y hy
    rw [mem_walkDrawing_U] at hy
    rcases hy with hy | ⟨e, he, hye⟩
    · exact (hcandV y hy).2.1
    · exact closure_minimal (hWcE e he) isClosed_closure hye
  have hQP : ∀ j, j ≠ i → Disjoint (walkDrawing G Wc).U (L.pathDrawing j).U := by
    intro j hj
    rw [disjoint_iff_inter_eq_empty, ← subset_empty_iff]
    exact walkDrawing_inter_U_subset (L.isSubdrawing j).1 Wc hWcnd subsingleton_empty
      fun y hy hyj => absurd hyj ((hcandV y hy).2.2.1 j hj)
  -- the encoded suffix of the old row
  have hWPnd : WP.support.Nodup := by rw [hWPsupp, ← hWsupp]; exact hnd
  obtain ⟨z', -, B, -, hBenc, hz', -, hBS, -, hBE⟩ :=
    hWPenc.exists_split_take_drop q (by omega)
  have hz'z : z' = z := by
    rw [hWPsupp, ← hWsupp] at hz'
    exact Option.some.inj (hz'.symm.trans hx)
  subst hz'z
  have hW₂B : W₂.support = B.support := by rw [h2, hBS, hWPsupp, hWsupp]
  have hW₂Be : W₂.edges = B.edges := by rw [h4, hBE, hWPedges, hWedges]
  have hBnd : B.support.Nodup := by rw [hBS]; exact hWPnd.sublist (List.drop_sublist _ _)
  -- the joined walk is simple
  have hWf : (Wc.append B).IsSimple := by
    unfold GraphWalk.IsSimple
    rw [GraphWalk.support_append]
    refine List.Nodup.append hWcnd (hBnd.sublist (List.tail_sublist _)) ?_
    intro y hyc hyB
    have hBc := B.support_eq_cons
    have hyz : y ≠ z' := by
      rintro rfl
      rw [hBc] at hBnd
      exact (List.nodup_cons.mp hBnd).1 hyB
    have hyT : y ∈ (walkDrawing (L.pathDrawing i) W₂).U := by
      rw [mem_walkDrawing_U, hW₂B]
      exact Or.inl (List.mem_of_mem_tail hyB)
    exact hyz ((hcandV y hyc).2.2.2 hyT)
  have hRU : (walkDrawing G (Wc.append B)).U =
      (walkDrawing G Wc).U ∪ (walkDrawing (L.pathDrawing i) W₂).U := by
    ext y
    simp only [mem_union, mem_walkDrawing_U, GraphWalk.mem_support_append,
      GraphWalk.edges_append, List.mem_append, hW₂B, hW₂Be]
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
  have hpre' : ¬ P_sv.U ⊆ closure (cylinderRegion k G i) := by
    rw [hpreIff]
    simpa using hpre
  exact exists_encoded_reduction4_linkage L hk i tagged vertex edge rows (crow ++ path.drop q)
    hrows hvP hvR hsub hpre' htail (walkDrawing_isSubdrawing G Wc)
    (isPathDrawing_walkDrawing_of_isSimple G hWcs hsv) hQR hQP (Wc.append B) hWf
    (hWcenc.append hBenc) hRU

end Find4Level

namespace GM06CurrentDrawingRep
variable {x : GM06SuccessorInput} {L : CylinderLinkage k G} (rep : GM06CurrentDrawingRep x G L)
include rep

local notation "currentCut" => gm06CutDataOfLinkage x.vertexCount rep.tagged.length x.endpoints
  x.linkage x.innerCuff x.outerCuff x.rotations (List.range x.vertexCount)
local notation "edgeCount" => 2 * (rep.tagged.length + (k + k))

/-- The phase query of `phase_find4_rep`, together with the activity
of every dart of the selected face row. -/
theorem phase_find4_rep_active (hn : 0 < x.vertexCount) (hk : 1 < k)
    (hG : IsCylinderSection5Drawing k G)
    (hno : ∀ (G₁ : Drawing ClosedCylinder) (L₁ : CylinderLinkage k G₁),
      IsCylinderSection5Drawing k G₁ → ¬ Section5Reduction2Step k G L G₁ L₁)
    (i : Fin k) :
    ∃ row : List ℕ, (∀ r ∈ row, r ∈ (currentCut).activeDarts) ∧
      gm06Reduction4PhaseAt x rep.tagged.length i.val =
        gm06Find4Darts edgeCount (currentCut).origins
          (gm06CandidateOrdinary edgeCount rep.tagged.length)
          (gm06IncV (2 * x.vertexCount) (currentCut).origins row)
          (gm06IncE edgeCount row)
          (gm06PhaseBoundaryVertices x (gm06PhaseNext x i.val) 1)
          (gm06CutVertexFin x.vertexCount hn (x.innerCuff[i.val]?.getD 0) true)
          (gm06CutPathSteps x.vertexCount hn x.endpoints (x.linkage[i.val]?.getD []) true) ∧
      Find4Rep L i (gm06CandidateEnds edgeCount (currentCut).origins)
          (gm06CandidateOrdinary edgeCount rep.tagged.length)
          (gm06IncV (2 * x.vertexCount) (currentCut).origins row)
          (gm06IncE edgeCount row)
          (gm06PhaseBoundaryVertices x (gm06PhaseNext x i.val) 1)
          (gm06CutVertexFin x.vertexCount hn (x.innerCuff[i.val]?.getD 0) true)
          (gm06CutPathSteps x.vertexCount hn x.endpoints (x.linkage[i.val]?.getD []) true)
          rep.cutVertexPoint rep.cutEdgePoint := by
  obtain ⟨root, hroot, row, hquery, hrep⟩ := rep.component_find4_rep hn hk hG hno i
  have hact := rep.component_query_row_active hG i root hroot row hquery
  obtain ⟨root', hroot', hpart⟩ := rep.phase_component_at hG i
  have he : root' = root := Fin.ext (hroot'.trans hroot.symm)
  subst root'
  have hupper := rep.computed_path_labels_phase hn (finSuccCycle i) false
  simp only [Bool.not_false, Bool.toNat_true] at hupper
  rw [cutOrdinaryFlags_eq_candidate, hupper, ← rep.phase_next_eq i] at hrep
  refine ⟨row, hact, ?_, hrep⟩
  unfold gm06Reduction4PhaseAt
  rw [hpart]
  simp only [Option.bind_some, gm06Reduction4PhaseComponent, rep.cuff_lengths.1,
    rep.cuff_lengths.2, Nat.add_assoc, hquery]
  change gm06PhaseFind4Words (2 * x.vertexCount) (2 * (rep.tagged.length + (k + k)))
    (currentCut).origins _ _ _ _ _ _ = _
  have hs : x.innerCuff[i.val]?.getD 0 < x.vertexCount := by
    rw [rep.inner]
    simp only [List.getElem?_ofFn, i.isLt, dite_true, Option.getD_some]
    exact (rep.source i).isLt
  have hv := cutVertexFin_val hn hs true
  simp only [gm06CutVertex, Bool.not_true, Bool.toNat_false, Nat.add_zero] at hv
  rw [← hv, ← rep.computed_path_steps_phase hn i]
  exact gm06PhaseFind4Words_eq _ _ _ _ _ _ _

/-- Every stored copied origin, read with default zero, is a copied
vertex slot. -/
theorem cut_origin_getD_lt (hn : 0 < x.vertexCount) (d : ℕ) :
    (currentCut).origins[d]?.getD 0 < 2 * x.vertexCount := by
  cases h : (currentCut).origins[d]? with
  | none => simp only [Option.getD_none]; omega
  | some v => exact rep.cut_origin_table_bounds v (List.mem_of_getElem? h)

/-- **The Reduction 4 phase is sound** (VI (5.7), page 133, `k ≥ 2`).
If the phase reports a rerouting, its new rows encode a linkage `M` of
the same drawing with a Reduction 4 step from `L`. The rows are the
actual output of APPLY_4: the projected directed candidate row followed
by the suffix of the old row. -/
theorem reduction4Phase_sound (hk : 1 < k) (hG : IsCylinderSection5Drawing k G)
    (hno : ∀ (G₁ : Drawing ClosedCylinder) (L₁ : CylinderLinkage k G₁),
      IsCylinderSection5Drawing k G₁ → ¬ Section5Reduction2Step k G L G₁ L₁)
    {θ : ℝ} (hθ : L.HasTheta θ)
    (h : (gm06Reduction4Phase x rep.tagged.length).1 = true) :
    ∃ M : CylinderLinkage k G, Section5Reduction4Step k G L G M ∧
      GM06LinkageRowsEncoding M rep.tagged rep.vertex rep.edge
        (gm06Reduction4Phase x rep.tagged.length).2 := by
  classical
  have hn : 0 < x.vertexCount := Nat.zero_lt_of_lt (rep.source ⟨0, by omega⟩).isLt
  cases hw : gm06Reduction4PhaseWitness x rep.tagged.length with
  | none =>
    rw [gm06Reduction4Phase_of_none hw] at h
    simp at h
  | some w =>
  obtain ⟨i, j, darts⟩ := w
  rw [gm06Reduction4Phase_of_some hw]
  obtain ⟨hi, hat⟩ := gm06Reduction4PhaseWitness_some hw
  rw [rep.cuff_lengths.1] at hi
  obtain ⟨i, rfl⟩ : ∃ i' : Fin k, i'.val = i := ⟨⟨i, hi⟩, rfl⟩
  obtain ⟨row, hact, hphase, hrep⟩ := rep.phase_find4_rep_active hn hk hG hno i
  rw [hphase] at hat
  obtain ⟨hj, hwalk, hnodup, hcand⟩ := gm06Find4Darts_sound _ _ _ _ _ _ _
    rep.cut_origin_table_length rep.cut_origin_table_bounds j darts hat
  obtain ⟨hj1, hjl, hinc⟩ := contact_target_inc hj
  set start := gm06CutVertexFin x.vertexCount hn (x.innerCuff[i.val]?.getD 0) true with hstart
  set steps := gm06CutPathSteps x.vertexCount hn x.endpoints (x.linkage[i.val]?.getD []) true
    with hsteps
  have hwalk' : GM06DartWalk (fun d => (currentCut).origins[d]?.getD 0)
      (fun d => (currentCut).origins[gm06DartMate d]?.getD 0) start.val darts
      (gm06Find4Target start steps j).val := hwalk
  -- the returned row is nonempty
  have hne : darts ≠ [] := by
    rintro rfl
    have hst : ∀ {s t : ℕ}, GM06DartWalk (fun d => (currentCut).origins[d]?.getD 0)
        (fun d => (currentCut).origins[gm06DartMate d]?.getD 0) s [] t → s = t :=
      fun h => by cases h; rfl
    exact find4_start_ne_target hrep hj1 hjl (Fin.ext (hst hwalk'))
  -- the endpoints of the returned darts pass the candidate test
  have hends : ∀ v ∈ gm06WalkVertices (fun d => (currentCut).origins[gm06DartMate d]?.getD 0)
      start.val darts, v < 2 * x.vertexCount ∧
        gm06CandidateVertex (gm06IncV (2 * x.vertexCount) (currentCut).origins row)
          (gm06PhaseBoundaryVertices x (gm06PhaseNext x i.val) 1)
          (gm06Find4PathVertices start steps) j v = true :=
    GM06DartWalk.vertices_of_endpoints hwalk' hne fun d hd => by
      have hh := candidateDart_ends _ _ _ _ _ _ _ _ _ (hcand d hd)
      exact ⟨⟨rep.cut_origin_getD_lt hn d, hh.2.2.2.1⟩,
        ⟨rep.cut_origin_getD_lt hn _, hh.2.2.2.2⟩⟩
  have htG : rep.cutPoint (gm06Find4Target start steps j).val ∈ G.V := by
    rw [rep.cutPoint_fin]
    exact (hrep.vertex_sound _ hinc).1
  obtain ⟨Wc, hWcenc, hWcsupp, hWcedges⟩ := rep.exists_encoded_cut_walk hG hwalk' htG
    fun d hd => rep.candidate_dart_active hG row hact _ _ j d (hcand d hd)
  -- the encoded walk tracing the old path
  have hpathEq : x.linkage[i.val]?.getD [] =
      x.linkage[i.val]'(by rw [rep.linkage.1]; exact i.isLt) := by
    rw [List.getElem?_eq_getElem (show i.val < x.linkage.length by rw [rep.linkage.1]; exact i.isLt)]
    rfl
  have hsource : x.innerCuff[i.val]?.getD 0 = (rep.source i).val := by
    rw [rep.inner]
    simp only [List.getElem?_ofFn, i.isLt, dite_true, Option.getD_some]
  obtain ⟨WP, -, hWPenc, -, -, hWPsupp, hWPedges⟩ := rep.computed_encoded_path_walk hn i true
  rw [← hpathEq, ← hsource] at hWPsupp
  rw [← hpathEq] at hWPedges hWPenc
  have hlen : (x.linkage[i.val]?.getD []).length = steps.length := by
    rw [hsteps, gm06CutPathSteps, List.length_map]
  refine (exists_encoded_reduction4_of_candidate_walk hrep hk hG hθ hj
    rep.linkage hlen hWPenc hWPsupp hWPedges Wc (rep.cutPoint_fin start) (rep.cutPoint_fin _)
    ?_ ?_ ?_ hWcenc).imp fun M hM => ⟨hM.1, hM.2⟩
  · unfold GraphWalk.IsSimple
    rw [hWcsupp]
    refine List.Nodup.map_on ?_ hnodup
    intro a ha b hb hab
    obtain ⟨ha', hac⟩ := hends a ha
    obtain ⟨hb', hbc⟩ := hends b hb
    have e1 : rep.cutPoint a = rep.cutVertexPoint ⟨a, ha'⟩ := rep.cutPoint_fin ⟨a, ha'⟩
    have e2 : rep.cutPoint b = rep.cutVertexPoint ⟨b, hb'⟩ := rep.cutPoint_fin ⟨b, hb'⟩
    have := hrep.inj ⟨a, ha'⟩ ⟨b, hb'⟩ (Or.inl ((gm06CandidateVertex_iff _ _ _ _ _).mp hac).1)
      (Or.inl ((gm06CandidateVertex_iff _ _ _ _ _).mp hbc).1) (e1.symm.trans (hab.trans e2))
    exact congrArg Fin.val this
  · intro y hy
    rw [hWcsupp] at hy
    obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hy
    obtain ⟨hvb, hvc⟩ := hends v hv
    exact ⟨⟨v, hvb⟩, hvc, (rep.cutPoint_fin ⟨v, hvb⟩).symm⟩
  · intro e he
    rw [hWcedges] at he
    obtain ⟨d, hd, rfl⟩ := List.mem_map.mp he
    have hh := candidateDart_ends _ _ _ _ _ _ _ _ _ (hcand d hd)
    obtain ⟨-, -, -, hsub, -⟩ := hrep.edge_sound (d / 2) hh.2.1 hh.2.2.1
    exact hsub

/-- **The Reduction 4 phase is complete** (VI (5.7), page 133, `k ≥ 2`).
If the phase reports no rerouting, no Reduction 4 step exists. Its
rows are then unchanged, by `gm06Reduction4Phase_of_none`. -/
theorem reduction4Phase_complete (hk : 1 < k) (hG : IsCylinderSection5Drawing k G)
    (hno : ∀ (G₁ : Drawing ClosedCylinder) (L₁ : CylinderLinkage k G₁),
      IsCylinderSection5Drawing k G₁ → ¬ Section5Reduction2Step k G L G₁ L₁)
    {θ : ℝ} (hθ : L.HasTheta θ)
    (h : (gm06Reduction4Phase x rep.tagged.length).1 = false) :
    ¬ ∃ M : CylinderLinkage k G, Section5Reduction4Step k G L G M := by
  have hn : 0 < x.vertexCount := Nat.zero_lt_of_lt (rep.source ⟨0, by omega⟩).isLt
  have hw : gm06Reduction4PhaseWitness x rep.tagged.length = none := by
    cases hw : gm06Reduction4PhaseWitness x rep.tagged.length with
    | none => rfl
    | some w =>
      obtain ⟨i, j, d⟩ := w
      rw [gm06Reduction4Phase_of_some hw] at h
      simp at h
  apply not_exists_reduction4Step_of_forall L hk
  intro i
  obtain ⟨row, -, hphase, hrep⟩ := rep.phase_find4_rep_active hn hk hG hno i
  have hnone := (gm06Reduction4PhaseWitness_none_iff x _).mp hw i.val
    (by rw [rep.cuff_lengths.1]; exact i.isLt)
  rw [hphase, gm06Find4Darts, Option.map_eq_none_iff] at hnone
  exact not_reduction4At_of_find4_none hrep hk hG hθ hnone

end GM06CurrentDrawingRep
end GraphMinor.GM06
