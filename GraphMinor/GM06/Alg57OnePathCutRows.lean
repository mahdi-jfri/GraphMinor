module

public import GraphMinor.GM06.Alg57OnePathCutEnds
public import GraphMinor.GM06.Alg57OnePathRed2
import all GraphMinor.GM06.Alg57CutFaceLink
import GraphMinor.GM06.Alg57CutCopiedSlots
import GraphMinor.Compute.GM06CutPathMembership

/-!
# Incidence of the cut slots with the region, for one path

The face of the cut drawing that FIND_4 searches is the cut face orbit of `c̄₁`. Here we say, for
each slot and each edge label of the cut tables, when the orbit meets it, in terms of the points of
the cut disc that the labels name (`cutLab` and `cutEdgeLab`). A slot over `P₁(t)` is met exactly
when its lift of `P₁(t)` is in `cutRc` (`path_slot_incident_iff`). This is the lifted incidence in
the form of `one_path_vertex_copy_iff_red2` and its relatives, with the darts of `P₁` read
from the rows.
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

variable (hG : IsCylinderSection5Drawing 1 G)
  (hno : ∀ (G₁ : Drawing ClosedCylinder) (L₁ : CylinderLinkage 1 G₁),
    IsCylinderSection5Drawing 1 G₁ → ¬ Section5Reduction2Step 1 G L G₁ L₁) (hθ : L.HasTheta θ)
  (hD : IsClosedDisc D) (hBd : discBd D = liftedStripBoundary hG.1 L 1)
  (hstrip : D ⊆ {p : ℝ × ℝ | 1 ≤ p.1 ∧ p.1 ≤ 2})

/-- A point of a lift is in `cutRc` exactly when its point of the cover is in the closure of the
lifted region. -/
theorem cutSidePoint_mem_cutRc_iff (left : Bool) (t : I) :
    cutSidePoint L hG hBd left t ∈ cutRc G D ↔
      coverLift L hG (if left then 1 else 2) t ∈ closure (cylinderCoverRegion 1 G 0) := Iff.rfl

include hno hθ hD hstrip in
/-- **The incidence of a slot over `P₁`.** Let the live slot `a` be at `P₁(t)`. The cut face orbit
of `c̄₁` meets the copy `left` of `a` exactly when the lift of `P₁(t)` on the side `left` is in
`cutRc`. -/
theorem path_slot_incident_iff (a : Fin x.vertexCount) (ha : a ∈ rep.live) {t : I}
    (hat : rep.vertex a = L.curve 0 t) (left : Bool) :
    (∃ n, cutNext^[n] gapCut ∈ (splitRows).getD (gm06CutVertex a.val left) []) ↔
      cutSidePoint L hG hBd left t ∈ cutRc G D := by
  rw [cutSidePoint_mem_cutRc_iff]
  have hinj := (L.curve_parametrizes 0).1
  have hsp : ∀ s : I, spherePath L s.1 = cylinderToSphere (L.curve 0 s) := fun s =>
    spherePath_of_mem L s.2
  have haP : rep.vertex a ∈ (L.pathDrawing 0).U := by
    rw [hat, ← (L.curve_parametrizes 0).2.1]; exact mem_range_self t
  obtain ⟨p, hp⟩ := Option.ne_none_iff_exists'.mp (rep.cut_position_ne_none_of_path a ha 0 haP)
  cases p with
  | interior a' b' =>
    obtain ⟨hin, hout⟩ := (computedCutPosition_interior_iff _ _ _ _).mp hp
    obtain ⟨hmin, ha'org⟩ := gm06BuildCutTables_incoming_source x.endpoints x.linkage
      x.innerCuff x.outerCuff a.isLt hin
    obtain ⟨hbin, hb'org⟩ := gm06BuildCutTables_outgoing_source x.endpoints x.linkage
      x.innerCuff x.outerCuff a.isLt hout
    obtain ⟨B, τB, τE, hltB, hBl, hBv, hBf, hBX, hBτ, -⟩ := rep.path_word_dart hbin
    obtain ⟨C, τC, τD, hltC, hCl, hCv, hCf, hCX, -, hCτD⟩ := rep.path_word_dart hmin
    have htB : t = τB := hinj (hat.symm.trans (hBτ a hb'org))
    have htC : t = τD := hinj (hat.symm.trans (hCτD a (by
      rw [gm06DartMate_involutive]; exact ha'org)))
    subst htB htC
    have ht : t.1 ∈ Ioo (0 : ℝ) 1 :=
      ⟨lt_of_le_of_lt τC.2.1 hltC, lt_of_lt_of_le hltB τE.2.2⟩
    set A := dartFlip _ C with hA
    have hAl : persistentDartLabel rep.label A = a' := by
      rw [hA, persistentDartLabel_flip, hCl, gm06DartMate_involutive]
    have hp' : gm06CutPositionAt cutTables a.val =
        some (.interior (persistentDartLabel rep.label A) (persistentDartLabel rep.label B)) := by
      rw [hAl, hBl]; exact hp
    obtain ⟨h1, h2⟩ := rep.one_path_vertex_copy_iff_red2 hG hno hθ hD hBd hstrip ht (a := A) (b := B)
      (by rw [hBv, hsp]) hBX τE.2 hltB (by rw [hBf, hsp])
      (by rw [hA, hCf, hsp]) (by rw [hA]; exact hCX) τC.2 hltC
      (by rw [hA, dartFlip_dartFlip, hCv, hsp]) a.isLt hp'
    cases left
    · exact h2.symm
    · exact h1.symm
  | start b' cp cn =>
    obtain ⟨i, hia, -, -⟩ := rep.cut_start_markers one_pos a hp
    have hi0 : i = 0 := Subsingleton.elim _ _
    subst hi0
    have ht0 : t = 0 := hinj (hat.symm.trans (by
      rw [← hia, rep.source_point 0]; exact (L.curve_parametrizes 0).2.2.1.symm))
    subst ht0
    have hcopy := rep.one_path_start_copies hG left
    rw [← hia]
    refine ⟨fun _ => coverLift_zero_mem_closure L hG hθ hD hBd hstrip ?_, fun _ => hcopy⟩
    cases left <;> simp
  | terminal a' cp cn =>
    obtain ⟨i, hia, hcp, hcn⟩ := rep.cut_terminal_markers one_pos a hp
    have hi0 : i = 0 := Subsingleton.elim _ _
    subst hi0
    have hin := ((computedCutPosition_terminal_iff _ _ _ _ _).mp hp).1
    obtain ⟨hmin, ha'org⟩ := gm06BuildCutTables_incoming_source x.endpoints x.linkage
      x.innerCuff x.outerCuff a.isLt hin
    obtain ⟨C, τC, τD, hltC, hCl, hCv, hCf, hCX, -, hCτD⟩ := rep.path_word_dart hmin
    have ht1 : t = 1 := hinj (hat.symm.trans (by
      rw [← hia, rep.target_point 0]
      obtain ⟨j, hj⟩ := L.curve_one_mem 0
      rw [← hj, Subsingleton.elim j 0]))
    have htC : t = τD := hinj (hat.symm.trans (hCτD a (by
      rw [gm06DartMate_involutive]; exact ha'org)))
    subst ht1
    set A := dartFlip _ C with hA
    have hAl : persistentDartLabel rep.label A = a' := by
      rw [hA, persistentDartLabel_flip, hCl, gm06DartMate_involutive]
    have hp' : gm06CutPositionAt cutTables a.val =
        some (.terminal (persistentDartLabel rep.label A) (2 * (rep.tagged.length + 1))
          (2 * (rep.tagged.length + 1) + 1)) := by
      rw [hAl, hp, hcp, hcn]
      simp [gm06PreviousCuffIndex]
    obtain ⟨h1, h2⟩ := rep.one_path_end_copy_iff_red2 hG hno hθ hD hBd hstrip (a := A)
      (by rw [hA, hCf, ← htC, ← hsp 1]; rfl) (by rw [hA]; exact hCX) τC.2
      (lt_of_lt_of_le hltC (le_of_eq htC.symm) |>.trans_le le_rfl)
      (by rw [hA, dartFlip_dartFlip, hCv, hsp]) a.isLt hp'
    cases left
    · exact h2.symm
    · exact h1.symm

include hG in
/-- **The cut orbit never holds the wrong copy of a path dart.** For a word `w` of `P₁`, the right
copy of `w` and the left copy of its reverse are last darts of copies of split vertices, so the
cut face orbit of `c̄₁` never reaches them. -/
theorem path_copies_not_in_orbit {w : ℕ} (hw : w ∈ x.linkage.flatten) (n : ℕ) :
    cutNext^[n] gapCut ≠ gm06CutDart w 1 ∧
      cutNext^[n] gapCut ≠ gm06CutDart (gm06DartMate w) 0 := by
  have hnl := rep.cut_iterate_not_last hG 0 n
  simp only [Fin.val_zero, add_zero] at hnl
  have hwb := rep.path_word_lt hw
  have hmw : gm06DartMate w ∉ x.linkage.flatten := rep.linkage_not_reverse hw
  have hrows : ∀ v : ℕ, v < x.vertexCount → x.rotations[v]? = some (x.rotations.getD v []) := by
    intro v hv
    have hlt : v < x.rotations.length := by rw [rep.rows_length]; exact hv
    rw [List.getD_eq_getElem _ _ hlt, List.getElem?_eq_getElem hlt]
  constructor
  · intro h
    apply hnl
    rw [h]
    have hv := rep.ordinary_origin_lt hwb
    obtain ⟨p, hp, hend⟩ := (gm06BuildCutTables_pathEnds_iff (m := rep.tagged.length) x.endpoints
      x.linkage x.innerCuff x.outerCuff hv (rep.cut_path_keys_nodup true)
      (rep.cut_path_keys_nodup false)).mpr (Or.inl hw)
    refine ⟨_, _, p, false, hrows _ hv, hp, ?_⟩
    cases p with
    | interior a b =>
      obtain ⟨hin, -⟩ := (computedCutPosition_interior_iff _ _ _ _).mp hp
      have ha := (gm06BuildCutTables_incoming_source x.endpoints x.linkage x.innerCuff x.outerCuff
        hv hin).1
      simp only [GM06CutPosition.pathEnds, List.mem_cons, List.not_mem_nil, or_false] at hend
      rcases hend with rfl | rfl
      · exact absurd ha hmw
      · simp [cutLast, gm06CutRowDart, GM06CutPosition.pathEnds]
    | start b cp cn =>
      simp only [GM06CutPosition.pathEnds, List.mem_singleton] at hend
      subst hend
      simp [cutLast, gm06CutRowDart, GM06CutPosition.pathEnds]
    | terminal a cp cn =>
      have hin := ((computedCutPosition_terminal_iff _ _ _ _ _).mp hp).1
      have ha := (gm06BuildCutTables_incoming_source x.endpoints x.linkage x.innerCuff x.outerCuff
        hv hin).1
      simp only [GM06CutPosition.pathEnds, List.mem_singleton] at hend
      subst hend
      exact absurd ha hmw
  · intro h
    apply hnl
    rw [h]
    have hv := rep.ordinary_origin_lt (gm06DartMate_lt hwb)
    obtain ⟨p, hp, hend⟩ := (gm06BuildCutTables_pathEnds_iff (m := rep.tagged.length) x.endpoints
      x.linkage x.innerCuff x.outerCuff hv (rep.cut_path_keys_nodup true)
      (rep.cut_path_keys_nodup false)).mpr (Or.inr (by rw [gm06DartMate_involutive]; exact hw))
    refine ⟨_, _, p, true, hrows _ hv, hp, ?_⟩
    cases p with
    | interior a b =>
      obtain ⟨-, hout⟩ := (computedCutPosition_interior_iff _ _ _ _).mp hp
      have hb := (gm06BuildCutTables_outgoing_source x.endpoints x.linkage x.innerCuff x.outerCuff
        hv hout).1
      simp only [GM06CutPosition.pathEnds, List.mem_cons, List.not_mem_nil, or_false] at hend
      rcases hend with h' | h'
      · rw [h']
        simp [cutLast, gm06CutRowDart, GM06CutPosition.pathEnds]
      · rw [← h'] at hb
        exact absurd hb hmw
    | start b cp cn =>
      have hout := ((computedCutPosition_start_iff _ _ _ _ _).mp hp).2.1
      have hb := (gm06BuildCutTables_outgoing_source x.endpoints x.linkage x.innerCuff x.outerCuff
        hv hout).1
      simp only [GM06CutPosition.pathEnds, List.mem_singleton] at hend
      rw [← hend] at hb
      exact absurd hb hmw
    | terminal a cp cn =>
      simp only [GM06CutPosition.pathEnds, List.mem_singleton] at hend
      rw [hend]
      simp [cutLast, gm06CutRowDart, GM06CutPosition.pathEnds]

include hG in
/-- A dart of `G⁺` with an ordinary label is along the edge of that label. -/
theorem dart_edge_of_label {c : DrawingDart (cylinderSphereDrawing rep.cuffed)} {d : ℕ}
    (hcl : persistentDartLabel rep.label c = d) (hd : d < 2 * rep.tagged.length) :
    c.1.1 = cylinderToSphere '' rep.edge ⟨d / 2, by omega⟩ := by
  let f : (cylinderSphereDrawing rep.cuffed).E := ⟨c.val.1, c.property⟩
  have hcode : 2 * rep.label f + c.val.2.toNat = d := hcl
  have hb : c.val.2.toNat ≤ 1 := by cases c.val.2 <;> decide
  have hlabel : rep.label f < rep.tagged.length := by omega
  obtain ⟨j, _, hf, hj⟩ := rep.ordinary_of_label_lt hG f hlabel
  have hindex : j = ⟨d / 2, by omega⟩ := Fin.ext (show j.val = d / 2 by omega)
  rw [← hindex]
  exact hf

include hG in
/-- The iterates of the cut orbit are cut darts. -/
theorem orbit_mem_flatten (n : ℕ) : cutNext^[n] gapCut ∈ (splitRows).flatten := by
  have hc : gapCut ∈ (splitRows).flatten := by
    have h := rep.reverse_inner_mem_cut hG 0
    simp only [Fin.val_zero, add_zero] at h
    exact h
  exact cut_iterate_mem cutTables x.rotations rep.rows_flatten_nodup
    (fun _ h => rep.cut_rows_mate hG h) hc n

include hG in
/-- A right copy in the cut rows is the copy of a word of `P₁` or of its reverse. -/
theorem right_copy_path {q : ℕ} (hq : q ∈ (splitRows).flatten) (htag : q / 2 % 2 = 1) :
    gm06UncutDart q ∈ x.linkage.flatten ∨ gm06DartMate (gm06UncutDart q) ∈ x.linkage.flatten := by
  have hreb := gm06CutDart_rebuild q
  rw [htag] at hreb
  have h := (rep.cut_copies hG (gm06UncutDart q) 1 (by decide)).mp (hreb.symm ▸ hq)
  rcases h.2 with h | h | h
  · exact absurd h (by decide)
  · exact Or.inl h
  · exact Or.inr h

include hG hno hθ hD hBd hstrip in
/-- **The incidence of an edge off `P₁`, read from the cut orbit.** For an active edge `j` off
`P₁`, the cut orbit has a dart with edge label `2j` exactly when the points over the edge are in
`cutRc`, and it never has a dart with edge label `2j + 1`. -/
theorem off_edge_incident_iff (j : Fin rep.tagged.length) (hj : rep.tagged[j].2 = 1)
    (hjP : rep.edge j ∉ (L.pathDrawing 0).E) :
    ((∃ n, cutNext^[n] gapCut / 2 = 2 * j.val) ↔ cutProj D ⁻¹' rep.edge j ⊆ cutRc G D) ∧
      ¬ ∃ n, cutNext^[n] gapCut / 2 = 2 * j.val + 1 := by
  obtain ⟨sf, hsf, hl⟩ := rep.ordinary_labels j hj
  let d0 : DrawingDart (cylinderSphereDrawing rep.cuffed) := ⟨(sf.val, false), sf.property⟩
  have hcode : persistentDartLabel rep.label d0 = 2 * j.val := by
    simp only [persistentDartLabel, d0, hl, Bool.toNat_false, Nat.add_zero]
  have hjG : rep.edge j ∈ G.E := (rep.links j hj).1
  -- a cut dart of the edge is a left copy
  have hnotpath : ∀ q, gm06UncutDart q / 2 = j.val →
      ¬ (gm06UncutDart q ∈ x.linkage.flatten ∨ gm06DartMate (gm06UncutDart q) ∈ x.linkage.flatten) := by
    intro q hq h
    apply hjP
    have hlt : gm06UncutDart q < 2 * rep.tagged.length := by have := j.isLt; omega
    rcases h with h | h
    · have he := rep.path_word_edge (rep.mem_linkage_zero_of_flatten h) hlt
      have hfin : (⟨gm06UncutDart q / 2, by omega⟩ : Fin rep.tagged.length) = j := Fin.ext hq
      rwa [hfin] at he
    · have he := rep.path_word_edge (rep.mem_linkage_zero_of_flatten h) (gm06DartMate_lt hlt)
      have hfin : (⟨gm06DartMate (gm06UncutDart q) / 2, by have := gm06DartMate_lt hlt; omega⟩ :
          Fin rep.tagged.length) = j := Fin.ext ((gm06DartMate_edge _).trans hq)
      rwa [hfin] at he
  have htag0 : ∀ n, gm06UncutDart (cutNext^[n] gapCut) / 2 = j.val →
      cutNext^[n] gapCut / 2 % 2 = 0 := by
    intro n hn
    by_contra h
    exact hnotpath _ hn (rep.right_copy_path hG (rep.orbit_mem_flatten hG n) (by omega))
  refine ⟨?_, ?_⟩
  · change _ ↔ (fun p : D => radialCylinderProjection p.1) ⁻¹' rep.edge j ⊆ cutRc G D
    rw [rep.one_path_off_edge_iff_red2 hG hno hθ hD hBd hstrip hjG hjP d0
      (by change sf.val = _; rw [hsf]), hcode]
    constructor
    · rintro ⟨n, hn⟩
      rcases Nat.mod_two_eq_zero_or_one (cutNext^[n] gapCut) with h | h
      · left
        exact ⟨n, by unfold gm06UncutDart; omega⟩
      · right
        refine ⟨n, ?_⟩
        simp only [gm06DartMate, Nat.mul_mod_right, ite_true]
        unfold gm06UncutDart
        omega
    · rintro (⟨n, hn⟩ | ⟨n, hn⟩)
      · refine ⟨n, ?_⟩
        have h0 := htag0 n (by rw [hn]; omega)
        unfold gm06UncutDart at hn
        omega
      · refine ⟨n, ?_⟩
        simp only [gm06DartMate, Nat.mul_mod_right, ite_true] at hn
        have h0 := htag0 n (by rw [hn]; omega)
        unfold gm06UncutDart at hn
        omega
  · rintro ⟨n, hn⟩
    have h0 := htag0 n (by unfold gm06UncutDart; omega)
    omega

end GM06CurrentDrawingRep

end GraphMinor.GM06
