module

public import GraphMinor.GM06.Alg57OnePathWords
public import GraphMinor.GM06.Alg57OnePathInnerSides
public import GraphMinor.GM06.Alg57OnePathStartSides
public import GraphMinor.GM06.Alg57OnePathEndSides
public import GraphMinor.GM06.Alg57OnePathRed2
import all GraphMinor.GM06.Alg57CutFaceLink

/-!
# The sides of the rays read from the cut tables

At a vertex `v = P₁(t)` the cut tables split the rotation row of `v` into a left block, kept by
the left copy, and a right block. The left block runs from `cutFirst p true` to just before
`cutLast p true` (`cutLeftBlock`). At an inner vertex these are the forward and backward darts of
`P₁`, at the start the forward dart and the positive inner cuff end, and at the end the positive
outer cuff end and the backward dart. So the three side statements `raySides_inner`,
`raySides_start` and `raySides_end` say the same thing in every case: the ray of a dart along an
edge off `P₁` is on side one exactly when the label of the dart is in the left block
(`raySides_of_position`).
-/

@[expose] public section

namespace GraphMinor.GM06

open Set Topology GraphMinor.Surface GraphMinor.GM11 GraphMinor.Compute unitInterval

variable {G : Drawing ClosedCylinder} {θ : ℝ} {D : Set (ℝ × ℝ)}

/-- The left block of a split row: from the first dart of the left copy up to, but not
including, its last dart. -/
def cutLeftBlock (p : GM06CutPosition) (row : List ℕ) (ℓ : ℕ) : Prop :=
  ℓ ∈ row ∧ (ℓ = cutFirst p true ∨ GM06DrawingData.cyclicBetween (row.idxOf (cutFirst p true))
    (row.idxOf (cutLast p true)) (row.idxOf ℓ) = true)

/-- `RaySides` only depends on the side of the darts at the vertex. -/
theorem RaySides.congr {L : CylinderLinkage 1 G} {H : Drawing ClosedCylinder}
    {γ : Set (OnePoint EuclideanPlane) → I → OnePoint EuclideanPlane}
    {R : DartRotation (DrawingDart (cylinderSphereDrawing H))} {U₁ : Set CylinderCover} {t : I}
    {side side' : DrawingDart (cylinderSphereDrawing H) → Prop}
    (h : RaySides L D U₁ γ R t side)
    (hss : ∀ d, dartVertex γ d = cylinderToSphere (L.curve 0 t) → (side d ↔ side' d)) :
    RaySides L D U₁ γ R t side' := by
  obtain ⟨Φ, Ψ, z, hst, hΨ, hray⟩ := h
  refine ⟨Φ, Ψ, z, hst, hΨ, fun d hd f hf hfP hdf r hr hr1 => ?_⟩
  rw [← hss d hd]
  exact hray d hd f hf hfP hdf r hr hr1

namespace GM06CurrentDrawingRep

variable {x : GM06SuccessorInput} {L : CylinderLinkage 1 G} (rep : GM06CurrentDrawingRep x G L)

local notation "cutTables" => gm06BuildCutTables x.vertexCount rep.tagged.length x.endpoints
  x.linkage x.innerCuff x.outerCuff

/-- With one path every linkage word is in the row of `P₁`. -/
theorem mem_linkage_zero_of_flatten {d : ℕ} (hd : d ∈ x.linkage.flatten) :
    d ∈ x.linkage[0]'(by rw [rep.linkage.1]; exact one_pos) := by
  obtain ⟨row, hr, hd⟩ := List.mem_flatten.mp hd
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hr
  have h0 : i = 0 := by have := rep.linkage.1; omega
  subst h0
  exact hd

/-- **The dart of a word of `P₁`.** A word of the row of `P₁` is the label of a dart along an
edge of `P₁`, from `P₁(τ)` to `P₁(τ')` with `τ < τ'`, where `P₁(τ)` and `P₁(τ')` are the vertices of
its tail and head slots. -/
theorem path_word_dart {w : ℕ} (hw : w ∈ x.linkage.flatten) :
    ∃ (c : DrawingDart (cylinderSphereDrawing rep.cuffed)) (τ τ' : I), τ < τ' ∧
      persistentDartLabel rep.label c = w ∧
      dartVertex rep.par c = cylinderToSphere (L.curve 0 τ) ∧
      dartVertex rep.par (dartFlip _ c) = cylinderToSphere (L.curve 0 τ') ∧
      c.1.1 ⊆ cylinderToSphere '' (L.pathDrawing 0).U ∧
      (∀ a : Fin x.vertexCount, x.endpoints[w]?.getD 0 = a.val → rep.vertex a = L.curve 0 τ) ∧
      (∀ b : Fin x.vertexCount, x.endpoints[gm06DartMate w]?.getD 0 = b.val →
        rep.vertex b = L.curve 0 τ') := by
  have hw0 := rep.mem_linkage_zero_of_flatten hw
  obtain ⟨hwb, hact⟩ := rep.path_word_active hw
  let a : Fin x.vertexCount := ⟨_, rep.ordinary_origin_lt hwb⟩
  let b : Fin x.vertexCount := ⟨_, rep.ordinary_origin_lt (gm06DartMate_lt hwb)⟩
  obtain ⟨τ, τ', hlt, hτ, hσ⟩ := rep.path_word_params hw0 a b rfl rfl
  obtain ⟨c, hcl, hcv, hcf, hce⟩ := rep.exists_word_dart hwb hact a b rfl rfl
  refine ⟨c, τ, τ', hlt, hcl, by rw [hcv, hτ], by rw [hcf, hσ], ?_, ?_, ?_⟩
  · rw [hce]
    exact image_mono fun y hy => ((rep.path_word_edge hw0 hwb).2.1 hy).1
  · intro a' ha'
    have : a' = a := Fin.ext ha'.symm
    rw [this, hτ]
  · intro b' hb'
    have : b' = b := Fin.ext hb'.symm
    rw [this, hσ]

variable (hG : IsCylinderSection5Drawing 1 G)

include hG in
/-- The block of the rotation of `R` from `U` up to `W` is the left block when `U` and `W` are the
first and last darts of the left copy. -/
theorem block_dart_iff {R : DartRotation (DrawingDart (cylinderSphereDrawing rep.cuffed))}
    (hrot : ∀ d, persistentDartLabel rep.label (R.rot d) =
      gm06RotationPermutation x.rotations (persistentDartLabel rep.label d))
    (a : Fin x.vertexCount) {p : GM06CutPosition}
    (hp : gm06CutPositionAt cutTables a.val = some p)
    {U W : DrawingDart (cylinderSphereDrawing rep.cuffed)}
    (hU : persistentDartLabel rep.label U = cutFirst p true)
    (hW : persistentDartLabel rep.label W = cutLast p true)
    (d : DrawingDart (cylinderSphereDrawing rep.cuffed)) :
    (∃ i, (∀ j ≤ i, R.rot^[j] U ≠ W) ∧ R.rot^[i] U = d) ↔
      cutLeftBlock p (x.rotations.getD a.val []) (persistentDartLabel rep.label d) := by
  have hlt : a.val < x.rotations.length := by rw [rep.rows_length]; exact a.isLt
  set row := x.rotations.getD a.val [] with hrowD
  have hvr : x.rotations[a.val]? = some row := by
    rw [hrowD, List.getD_eq_getElem _ _ hlt, List.getElem?_eq_getElem hlt]
  have hrow : row ∈ x.rotations := List.mem_of_getElem? hvr
  have hrn : row.Nodup := (List.nodup_flatten.mp rep.rows_flatten_nodup).1 row hrow
  have hok := rep.cut_block_ok hG a.val row p hvr hp
  obtain ⟨hf, hl, hfl, -⟩ := cutBlock_spec hok true
  rw [← hU] at hf hfl
  rw [← hW] at hl hfl
  have hinj := persistentDartLabel_injective rep.label
  have hit := fun j => persistentDartLabel_rot_iterate rep.label x.rotations
    rep.rows_flatten_nodup R hrot hrow hf j
  unfold cutLeftBlock
  rw [← hU, ← hW, block_iff_iterate hrn hf hl hfl]
  refine exists_congr fun i => and_congr (forall_congr' fun j => imp_congr_right fun _ => ?_) ?_
  · rw [← hit j]; exact hinj.ne_iff.symm
  · rw [← hit i]; exact hinj.eq_iff.symm

variable (hθ : L.HasTheta θ) (hD : IsClosedDisc D) (hBd : discBd D = liftedStripBoundary hG.1 L 1)
  (hstrip : D ⊆ {p : ℝ × ℝ | 1 ≤ p.1 ∧ p.1 ≤ 2})
  {U₁ U₂ : Set CylinderCover} (hU₁ : IsOpen U₁) (hU₂ : IsOpen U₂) (hU : Disjoint U₁ U₂)
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

include hθ hD hBd hstrip hU₁ hU₂ hU h₁ h₂ hR hccw hrot heI heO hV in
/-- **The sides of the rays at a vertex of `P₁`, read from the cut tables.** Let `v` be a live
slot at `P₁(t)` with cut position `p`. Then the ray of a dart at `P₁(t)` along an edge off `P₁` is
on side one exactly when the label of the dart is in the left block of `p`. -/
theorem raySides_of_position (a : Fin x.vertexCount) {t : I} (hat : rep.vertex a = L.curve 0 t)
    {p : GM06CutPosition} (hp : gm06CutPositionAt cutTables a.val = some p) :
    RaySides L D U₁ rep.par R t
      (fun d => cutLeftBlock p (x.rotations.getD a.val []) (persistentDartLabel rep.label d)) := by
  have hinj := (L.curve_parametrizes 0).1
  have hsp : ∀ s : I, spherePath L s.1 = cylinderToSphere (L.curve 0 s) := fun s =>
    spherePath_of_mem L s.2
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
    have hrs := raySides_inner L hG hθ hD hBd hstrip hU₁ hU₂ hU h₁ h₂ rep.subdrawing rep.cuffed_U
      rep.cuffed_V rep.edgePar hR hccw heI rep.inner_par hV ht (a := A) (b := B)
      (by rw [hBv, hsp]) hBX τE.2 hltB (by rw [hBf, hsp])
      (by rw [hA, hCf, hsp]) (by rw [hA]; exact hCX) τC.2 hltC
      (by rw [hA, dartFlip_dartFlip, hCv, hsp])
    exact hrs.congr fun d _ => rep.block_dart_iff hG hrot a hp hBl hAl d
  | start b' cp cn =>
    obtain ⟨i, hia, hcp, -⟩ := rep.cut_start_markers one_pos a hp
    have hi0 : i = 0 := Subsingleton.elim _ _
    subst hi0
    have hout := ((computedCutPosition_start_iff _ _ _ _ _).mp hp).2.1
    obtain ⟨hbin, hb'org⟩ := gm06BuildCutTables_outgoing_source x.endpoints x.linkage
      x.innerCuff x.outerCuff a.isLt hout
    obtain ⟨B, τB, τE, hltB, hBl, hBv, hBf, hBX, hBτ, -⟩ := rep.path_word_dart hbin
    have ht0 : t = 0 := hinj (hat.symm.trans (by
      rw [← hia, rep.source_point 0]; exact (L.curve_parametrizes 0).2.2.1.symm))
    have htB : t = τB := hinj (hat.symm.trans (hBτ a hb'org))
    subst ht0
    have hrs := raySides_start L hG hθ hD hBd hstrip hU₁ hU₂ hU h₁ h₂ rep.subdrawing rep.cuffed_U
      rep.cuffed_V rep.edgePar hR hccw heI rep.inner_par (b := B)
      (by rw [hBv, ← htB, ← hsp 0]; rfl) hBX
    refine hrs.congr fun d _ => rep.block_dart_iff hG hrot a hp hBl ?_ d
    obtain ⟨f, hf, hfl⟩ := rep.inner_labels 0
    have hfe : (⟨cylinderToSphere '' (initialCuffGapCurve 1 0 '' Ioo 0 1), heI 0⟩ :
        (cylinderSphereDrawing rep.cuffed).E) = f := Subtype.ext hf.symm
    simp only [persistentDartLabel, hfe, hfl, cutLast, hcp, Bool.toNat_false, Fin.val_zero]
    omega
  | terminal a' cp cn =>
    obtain ⟨i, hia, hcp, -⟩ := rep.cut_terminal_markers one_pos a hp
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
    have hrs := raySides_end L hG hθ hD hBd hstrip hU₁ hU₂ hU h₁ h₂ rep.subdrawing rep.cuffed_U
      rep.cuffed_V rep.edgePar hR hccw heI rep.inner_par heO rep.outer_par hV (a := A)
      (by rw [hA, hCf, ← htC, ← hsp 1]; rfl) (by rw [hA]; exact hCX) τC.2
      (lt_of_lt_of_le hltC (le_of_eq htC.symm) |>.trans_le le_rfl)
      (by rw [hA, dartFlip_dartFlip, hCv, hsp])
    refine hrs.congr fun d _ => rep.block_dart_iff hG hrot a hp ?_ hAl d
    obtain ⟨f, hf, hfl⟩ := rep.outer_labels 0
    have hfe : (⟨cylinderToSphere '' (alg511OuterCuffGapCurve 1 0 '' Ioo 0 1), heO 0⟩ :
        (cylinderSphereDrawing rep.cuffed).E) = f := Subtype.ext hf.symm
    simp only [persistentDartLabel, hfe, hfl, cutFirst, hcp, Bool.toNat_false, Fin.val_zero]
    omega

end GM06CurrentDrawingRep

end GraphMinor.GM06
