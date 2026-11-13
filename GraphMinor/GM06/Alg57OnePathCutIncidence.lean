module

public import GraphMinor.GM06.Alg57OnePathFaceForm
public import GraphMinor.GM06.Alg57OnePathCopyRows
public import GraphMinor.GM06.Alg57CurrentRegionOrbit
public import GraphMinor.GM06.Alg57CurrentCutOrbit
public import GraphMinor.GM06.Alg57CutCopiedSlots
import GraphMinor.Compute.GM06RotationPredecessors
import all GraphMinor.GM06.Alg57CutFaceLink

/-!
# The lifted incidence for `k = 1` read from the cut face orbit

This is Lemma 11 of our proof of VI (5.7), for one path, in the cover. Take the current
arrays `rep : GM06CurrentDrawingRep x G L` with one linkage path and no reduction. Let `c` be the
cut copy of the reverse inner gap dart `c̄₁` and `cutNext` the face map of the split rows `K₁`.
At a vertex of `P₁` the cut drawing has two copies, the left one (on `Γ₁`) and the right one (on
`Γ₂`). We prove:

* `one_path_vertex_copy_iff`: at an inner vertex `x = P₁(t)` of `P₁`, the lift `Γ₁(t)` is in the
  closure of `R̃₁` exactly when the cut orbit of `c` contains a dart of the left copy of `x`, and
  `Γ₂(t)` is in it exactly when the orbit contains a dart of the right copy;
* `one_path_end_copy_iff`: the same at the end `P₁(1)`.

The proof chains three steps. The face form of the lifted incidence (`lifted_face_vertex`,
`lifted_face_end`) speaks of a half-open block of darts at `x` in the face orbit of `c̄₁`. The
labels turn the rotation into the row permutation and face orbits into numeric orbits
(`faceOf_eq_iff_permanent_orbit`). Finally `cut_orbit_mem_copy_iff` says the cut orbit visits a
copy exactly when the old orbit meets the half-open block of that copy.
-/

@[expose] public section

namespace GraphMinor.GM06

open Set GraphMinor.Surface GraphMinor.GM11 GraphMinor.Compute unitInterval

/-- Rotation iterates of a labelled dart are row permutation iterates of its label. -/
theorem persistentDartLabel_rot_iterate {Γ : Drawing (OnePoint EuclideanPlane)}
    (label : Γ.E ↪ ℕ) (rows : List (List ℕ)) (hn : rows.flatten.Nodup)
    (R : DartRotation (DrawingDart Γ))
    (hrot : ∀ d, persistentDartLabel label (R.rot d) =
      gm06RotationPermutation rows (persistentDartLabel label d))
    {row : List ℕ} (hrow : row ∈ rows) {d : DrawingDart Γ} (hd : persistentDartLabel label d ∈ row)
    (j : ℕ) : persistentDartLabel label (R.rot^[j] d) = row.formPerm^[j] (persistentDartLabel label d) := by
  induction j with
  | zero => rfl
  | succ j ih =>
    have hmem : row.formPerm^[j] (persistentDartLabel label d) ∈ row := by
      clear ih
      induction j with
      | zero => exact hd
      | succ j ih' =>
        rw [Function.iterate_succ_apply']
        exact List.formPerm_apply_mem_of_mem ih'
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', hrot, ih,
      gm06RotationPermutation_apply_row rows hn row hrow _ hmem]

namespace GM06CurrentDrawingRep

variable {x : GM06SuccessorInput} {G : Drawing ClosedCylinder} {L : CylinderLinkage 1 G}
  (rep : GM06CurrentDrawingRep x G L)

local notation "cutTables" => gm06BuildCutTables x.vertexCount rep.tagged.length x.endpoints
  x.linkage x.innerCuff x.outerCuff
local notation "cutNext" => Equiv.trans dartMatePerm
  (Equiv.symm (gm06RotationPermutation (gm06SplitRotationRows cutTables x.rotations)))
local notation "gapCut" => gm06CutDart (2 * rep.tagged.length + 1) 0

include rep in
/-- The facts about the current drawing that the one-path statements use: its rotation, the
labels of the cuff gaps, and the old face orbit of `c̄₁` read numerically. -/
theorem one_path_setting (hG : IsCylinderSection5Drawing 1 G)
    (hno : ¬ Section5AnyReductionApplies 1 G L) :
    ∃ R : DartRotation (DrawingDart (cylinderSphereDrawing rep.cuffed)),
      IsDrawingRotation (cylinderSphereDrawing rep.cuffed) rep.par R ∧
      IsCcwRotation (cylinderSphereDrawing rep.cuffed) rep.par R ∧
      R.rev = dartFlip (cylinderSphereDrawing rep.cuffed) ∧
      (∀ d, persistentDartLabel rep.label (R.rot d) =
        gm06RotationPermutation x.rotations (persistentDartLabel rep.label d)) ∧
      ∃ (heI : ∀ j : Fin 1, cylinderToSphere '' (initialCuffGapCurve 1 j '' Ioo 0 1) ∈
          (cylinderSphereDrawing rep.cuffed).E)
        (heO : ∀ j : Fin 1, cylinderToSphere '' (alg511OuterCuffGapCurve 1 j '' Ioo 0 1) ∈
          (cylinderSphereDrawing rep.cuffed).E),
        (∀ v ∈ (cylinderSphereDrawing rep.cuffed).V,
          ∃ a : DrawingDart (cylinderSphereDrawing rep.cuffed), dartVertex rep.par a = v) ∧
        persistentDartLabel rep.label
          ⟨(cylinderToSphere '' (alg511OuterCuffGapCurve 1 0 '' Ioo 0 1), false), heO 0⟩ =
            2 * (rep.tagged.length + 1) ∧
        persistentDartLabel rep.label
          ⟨(cylinderToSphere '' (alg511OuterCuffGapCurve 1 0 '' Ioo 0 1), true), heO 0⟩ =
            2 * (rep.tagged.length + 1) + 1 ∧
        ∀ d, R.faceOf d = R.faceOf (reverseInnerGapDart 1 0 rep.cuffed (heI 0)) ↔
          ∃ n, (Equiv.trans dartMatePerm (Equiv.symm (gm06RotationPermutation x.rotations)))^[n]
            (gm06UncutDart gapCut) = persistentDartLabel rep.label d := by
  obtain ⟨R, hR, hccw, hrev, hrot⟩ := rep.exists_ccwRotation
  have heI : ∀ j : Fin 1, cylinderToSphere '' (initialCuffGapCurve 1 j '' Ioo 0 1) ∈
      (cylinderSphereDrawing rep.cuffed).E := fun j => by
    obtain ⟨f, hf, -⟩ := rep.inner_labels j
    exact hf ▸ f.property
  have heO : ∀ j : Fin 1, cylinderToSphere '' (alg511OuterCuffGapCurve 1 j '' Ioo 0 1) ∈
      (cylinderSphereDrawing rep.cuffed).E := fun j => by
    obtain ⟨f, hf, -⟩ := rep.outer_labels j
    exact hf ▸ f.property
  have hV := exists_dart_of_isPreconnected_U rep.edgePar
    (isPreconnected_cylinderSphereDrawing_U_of_no_reduction' L one_pos hG hno rep.cuffed_U)
    ⟨_, heI 0⟩
  have hO : ∀ b : Bool, persistentDartLabel rep.label
      ⟨(cylinderToSphere '' (alg511OuterCuffGapCurve 1 0 '' Ioo 0 1), b), heO 0⟩ =
        2 * (rep.tagged.length + 1) + b.toNat := by
    intro b
    obtain ⟨f, hf, hl⟩ := rep.outer_labels 0
    have heq : (⟨cylinderToSphere '' (alg511OuterCuffGapCurve 1 0 '' Ioo 0 1), heO 0⟩ :
        (cylinderSphereDrawing rep.cuffed).E) = f := Subtype.ext hf.symm
    simp only [persistentDartLabel, heq, hl, Fin.val_zero]
  have hc : gm06UncutDart gapCut = 2 * (rep.tagged.length + (0 : Fin 1).val) + 1 := by
    simp [gm06UncutDart, gm06CutDart, Nat.add_div, Nat.add_mod]
    omega
  refine ⟨R, hR, hccw, hrev, hrot, heI, heO, hV, by simpa using hO false, by simpa using hO true,
    fun d => ?_⟩
  rw [faceOf_eq_iff_permanent_orbit rep.label x.rotations R hrev hrot, hc,
    rep.reverseInnerGapDart_label 0 (heI 0)]

section Copies

variable {θ : ℝ} {D : Set (ℝ × ℝ)} (hG : IsCylinderSection5Drawing 1 G)
  (hno : ¬ Section5AnyReductionApplies 1 G L) (hθ : L.HasTheta θ)
  (hD : IsClosedDisc D) (hBd : discBd D = liftedStripBoundary hG.1 L 1)
  (hstrip : D ⊆ {p : ℝ × ℝ | 1 ≤ p.1 ∧ p.1 ≤ 2})

include hθ hD hBd hstrip hno in
/-- **The lifted incidence at an inner vertex of `P₁`, read from the cut orbit.** Let `x = P₁(t)` be
a vertex of `P₁` other than its ends, at slot `v`, with backward path dart `a` and forward path
dart `b`, so that the cut position at `v` is `interior a b`. Then `Γ₁(t)` is in the closure of `R̃₁`
exactly when the cut face orbit of `c̄₁` contains a dart of the left copy of `v`, and `Γ₂(t)` is in
it exactly when that orbit contains a dart of the right copy. -/
theorem one_path_vertex_copy_iff {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1)
    {a b : DrawingDart (cylinderSphereDrawing rep.cuffed)}
    (hb : dartVertex rep.par b = spherePath L t)
    (hbX : b.1.1 ⊆ cylinderToSphere '' (L.pathDrawing 0).U)
    {t₁ : ℝ} (ht₁ : t₁ ∈ Icc (0 : ℝ) 1) (htt₁ : t < t₁)
    (hb1 : dartVertex rep.par (dartFlip _ b) = spherePath L t₁)
    (ha : dartVertex rep.par a = spherePath L t)
    (haX : a.1.1 ⊆ cylinderToSphere '' (L.pathDrawing 0).U)
    {t₂ : ℝ} (ht₂ : t₂ ∈ Icc (0 : ℝ) 1) (htt₂ : t₂ < t)
    (ha1 : dartVertex rep.par (dartFlip _ a) = spherePath L t₂)
    {v : ℕ} (hv : v < x.vertexCount)
    (hp : gm06CutPositionAt cutTables v =
      some (.interior (persistentDartLabel rep.label a) (persistentDartLabel rep.label b))) :
    (coverLift L hG 1 ⟨t, Ioo_subset_Icc_self ht⟩ ∈ closure (cylinderCoverRegion 1 G 0) ↔
      ∃ n, (cutNext)^[n] gapCut ∈
        (gm06SplitRotationRows cutTables x.rotations).getD (gm06CutVertex v true) []) ∧
    (coverLift L hG 2 ⟨t, Ioo_subset_Icc_self ht⟩ ∈ closure (cylinderCoverRegion 1 G 0) ↔
      ∃ n, (cutNext)^[n] gapCut ∈
        (gm06SplitRotationRows cutTables x.rotations).getD (gm06CutVertex v false) []) := by
  obtain ⟨R, hR, hccw, -, hrot, heI, heO, hV, -, -, hface⟩ := rep.one_path_setting hG hno
  obtain ⟨h1, h2⟩ := lifted_face_vertex L hG hθ hD hBd hstrip hno rep.subdrawing rep.cuffed_U
    rep.cuffed_V rep.edgePar hR hccw heI rep.inner_par hV ht hb hbX ht₁ htt₁ hb1 ha haX ht₂ htt₂
    ha1
  have hlt : v < x.rotations.length := rep.rows_length ▸ hv
  set row := x.rotations.getD v [] with hrow_def
  have hvr : x.rotations[v]? = some row := by
    rw [hrow_def, List.getD_eq_getElem _ _ hlt, List.getElem?_eq_getElem hlt]
  have hrow : row ∈ x.rotations := List.mem_of_getElem? hvr
  have hok := rep.cut_block_ok hG v row _ hvr hp
  have hlb : persistentDartLabel rep.label b ∈ row := (cutBlock_spec hok true).1
  have hla : persistentDartLabel rep.label a ∈ row := (cutBlock_spec hok true).2.1
  have hcopy := fun left => cut_orbit_mem_copy_iff cutTables x.rotations rep.rows_flatten_nodup
    (rep.cut_block_ok hG) (rep.cut_fits one_pos) (fun _ h => rep.cut_rows_mate hG h)
    (rep.reverse_inner_mem_cut hG 0) (rep.reverse_inner_cut_mate_not_first one_pos 0) hvr hp left
  simp only [Fin.val_zero, add_zero] at hcopy
  have hit := fun {d} (hd : persistentDartLabel rep.label d ∈ row) =>
    persistentDartLabel_rot_iterate rep.label x.rotations rep.rows_flatten_nodup R hrot hrow hd
  have hinj := persistentDartLabel_injective rep.label
  rw [splitRows_getD_of_position hlt hp, splitRows_getD_of_position hlt hp, hcopy true,
    hcopy false, h1, h2]
  simp only [cutFirst, cutLast]
  constructor
  · refine exists_congr fun i => and_congr (forall_congr' fun j => imp_congr_right fun _ => ?_) ?_
    · rw [← hit hlb j]; exact hinj.ne_iff.symm
    · rw [hface, hit hlb i]
  · refine exists_congr fun i => and_congr (forall_congr' fun j => imp_congr_right fun _ => ?_) ?_
    · rw [← hit hla j]; exact hinj.ne_iff.symm
    · rw [hface, hit hla i]

include hθ hD hBd hstrip hno in
/-- **The lifted incidence at the end of `P₁`, read from the cut orbit.** Let `P₁(1)` be at slot
`v`, with `a` the dart of the last edge of `P₁` at it, so that the cut position at `v` is the
terminal position with `a` and the two outer cuff ends. Then `Γ₁(1)` is in the closure of `R̃₁`
exactly when the cut face orbit of `c̄₁` contains a dart of the left copy of `v`, and `Γ₂(1)` is in
it exactly when that orbit contains a dart of the right copy. -/
theorem one_path_end_copy_iff {a : DrawingDart (cylinderSphereDrawing rep.cuffed)}
    (ha : dartVertex rep.par a = spherePath L 1)
    (haX : a.1.1 ⊆ cylinderToSphere '' (L.pathDrawing 0).U)
    {t₂ : ℝ} (ht₂ : t₂ ∈ Icc (0 : ℝ) 1) (htt₂ : t₂ < 1)
    (ha1 : dartVertex rep.par (dartFlip _ a) = spherePath L t₂)
    {v : ℕ} (hv : v < x.vertexCount)
    (hp : gm06CutPositionAt cutTables v =
      some (.terminal (persistentDartLabel rep.label a) (2 * (rep.tagged.length + 1))
        (2 * (rep.tagged.length + 1) + 1))) :
    (coverLift L hG 1 1 ∈ closure (cylinderCoverRegion 1 G 0) ↔
      ∃ n, (cutNext)^[n] gapCut ∈
        (gm06SplitRotationRows cutTables x.rotations).getD (gm06CutVertex v true) []) ∧
    (coverLift L hG 2 1 ∈ closure (cylinderCoverRegion 1 G 0) ↔
      ∃ n, (cutNext)^[n] gapCut ∈
        (gm06SplitRotationRows cutTables x.rotations).getD (gm06CutVertex v false) []) := by
  obtain ⟨R, hR, hccw, -, hrot, heI, heO, hV, hOf, hOt, hface⟩ := rep.one_path_setting hG hno
  obtain ⟨h1, h2⟩ := lifted_face_end L hG hθ hD hBd hstrip hno rep.subdrawing rep.cuffed_U
    rep.cuffed_V rep.edgePar hR hccw heI rep.inner_par heO rep.outer_par hV ha haX ht₂ htt₂ ha1
  have hlt : v < x.rotations.length := rep.rows_length ▸ hv
  set row := x.rotations.getD v [] with hrow_def
  have hvr : x.rotations[v]? = some row := by
    rw [hrow_def, List.getD_eq_getElem _ _ hlt, List.getElem?_eq_getElem hlt]
  have hrow : row ∈ x.rotations := List.mem_of_getElem? hvr
  have hok := rep.cut_block_ok hG v row _ hvr hp
  have hcopy := fun left => cut_orbit_mem_copy_iff cutTables x.rotations rep.rows_flatten_nodup
    (rep.cut_block_ok hG) (rep.cut_fits one_pos) (fun _ h => rep.cut_rows_mate hG h)
    (rep.reverse_inner_mem_cut hG 0) (rep.reverse_inner_cut_mate_not_first one_pos 0) hvr hp left
  simp only [Fin.val_zero, add_zero] at hcopy
  have hit := fun {d} (hd : persistentDartLabel rep.label d ∈ row) =>
    persistentDartLabel_rot_iterate rep.label x.rotations rep.rows_flatten_nodup R hrot hrow hd
  have hinj := persistentDartLabel_injective rep.label
  have hla : persistentDartLabel rep.label a ∈ row := (cutBlock_spec hok false).1
  have hcp : 2 * (rep.tagged.length + 1) ∈ row := (cutBlock_spec hok true).1
  rw [← hOf] at hcp
  rw [splitRows_getD_of_position hlt hp, splitRows_getD_of_position hlt hp, hcopy true,
    hcopy false, h1, h2]
  simp only [cutFirst, cutLast]
  rw [← hOt, ← hOf]
  constructor
  · refine exists_congr fun i => and_congr (forall_congr' fun j => imp_congr_right fun _ => ?_) ?_
    · rw [← hit hcp j]; exact hinj.ne_iff.symm
    · rw [hface, hit hcp i]
  · refine exists_congr fun i => and_congr (forall_congr' fun j => imp_congr_right fun _ => ?_) ?_
    · rw [← hit hla j]; exact hinj.ne_iff.symm
    · rw [hface, hit hla i]

include hθ hD hBd hstrip hno in
/-- **The lifted incidence inside an edge of `P₁`, read from the cut orbit.** Let `d` be the dart of
an edge of `P₁` that runs forward along `P₁`, and `P₁(s)` an inner point of that edge. Then `Γ₁(s)`
is in the closure of `R̃₁` exactly when the cut face orbit of `c̄₁` contains a copy of `d`, and
`Γ₂(s)` is in it exactly when that orbit contains a copy of the reverse of `d`. -/
theorem one_path_edge_copy_iff {s : ℝ} (hs : s ∈ Ioo (0 : ℝ) 1)
    {d : DrawingDart (cylinderSphereDrawing rep.cuffed)}
    (hdX : d.1.1 ⊆ cylinderToSphere '' (L.pathDrawing 0).U)
    {t₀ t₁ : ℝ} (ht₀ : t₀ ∈ Icc (0 : ℝ) 1) (ht₁ : t₁ ∈ Icc (0 : ℝ) 1) (htt : t₀ < t₁)
    (hd0 : dartVertex rep.par d = spherePath L t₀)
    (hd1 : dartVertex rep.par (dartFlip _ d) = spherePath L t₁)
    (hsd : spherePath L s ∈ d.1.1) :
    (coverLift L hG 1 ⟨s, Ioo_subset_Icc_self hs⟩ ∈ closure (cylinderCoverRegion 1 G 0) ↔
      ∃ n, gm06UncutDart ((cutNext)^[n] gapCut) = persistentDartLabel rep.label d) ∧
    (coverLift L hG 2 ⟨s, Ioo_subset_Icc_self hs⟩ ∈ closure (cylinderCoverRegion 1 G 0) ↔
      ∃ n, gm06UncutDart ((cutNext)^[n] gapCut) =
        gm06DartMate (persistentDartLabel rep.label d)) := by
  obtain ⟨R, hR, hccw, -, hrot, heI, heO, hV, -, -, hface⟩ := rep.one_path_setting hG hno
  obtain ⟨h1, h2⟩ := lifted_face_edge L hG hθ hD hBd hstrip hno rep.subdrawing rep.cuffed_U
    rep.cuffed_V rep.edgePar hR hccw heI rep.inner_par hV hs hdX ht₀ ht₁ htt hd0 hd1 hsd
  have hproj := fun e => rep.cut_face_orbit_projection_iff hG 0 e
  simp only [Fin.val_zero, add_zero] at hproj
  rw [h1, h2, hface, hface, ← hproj, ← hproj, persistentDartLabel_flip]
  exact ⟨Iff.rfl, Iff.rfl⟩

include hG in
/-- **Both copies of the start of `P₁` are on the cut orbit.** The right copy of `s₁` holds the cut
copy of `c̄₁` itself, and the left copy holds the dart before the positive inner cuff end, which is
the next dart of the old orbit. This matches `coverLift_zero_mem_closure`: both lifts of `s₁` are
in the closure of `R̃₁`. -/
theorem one_path_start_copies (left : Bool) :
    ∃ n, (cutNext)^[n] gapCut ∈
      (gm06SplitRotationRows cutTables x.rotations).getD (gm06CutVertex (rep.source 0).val left)
        [] := by
  obtain ⟨b, hp⟩ := rep.cut_source_position one_pos 0
  simp only [Fin.val_zero, add_zero, gm06PreviousCuffIndex, if_true, Nat.sub_self] at hp
  have hlt : (rep.source 0).val < x.rotations.length := by
    rw [rep.rows_length]; exact (rep.source 0).isLt
  set row := x.rotations.getD (rep.source 0).val [] with hrow_def
  have hvr : x.rotations[(rep.source 0).val]? = some row := by
    rw [hrow_def, List.getD_eq_getElem _ _ hlt, List.getElem?_eq_getElem hlt]
  have hrow : row ∈ x.rotations := List.mem_of_getElem? hvr
  have hrn : row.Nodup := (List.nodup_flatten.mp rep.rows_flatten_nodup).1 row hrow
  have hok := rep.cut_block_ok hG _ row _ hvr hp
  obtain ⟨hb, hcp, hne, -⟩ := cutBlock_spec hok true
  obtain ⟨hcn, -, hne', hkeepF⟩ := cutBlock_spec hok false
  simp only [cutFirst, cutLast] at hb hcp hne hcn hne' hkeepF
  have hcopy := cut_orbit_mem_copy_iff cutTables x.rotations rep.rows_flatten_nodup
    (rep.cut_block_ok hG) (rep.cut_fits one_pos) (fun _ h => rep.cut_rows_mate hG h)
    (rep.reverse_inner_mem_cut hG 0) (rep.reverse_inner_cut_mate_not_first one_pos 0) hvr hp true
  simp only [Fin.val_zero, add_zero, cutFirst, cutLast] at hcopy
  rw [splitRows_getD_of_position hlt hp]
  cases left
  · -- the right copy holds the cut copy of `c̄₁`
    refine ⟨0, ?_⟩
    rw [Function.iterate_zero_apply, gm06CutRotation_eq_map_filter]
    refine List.mem_map.mpr ⟨2 * rep.tagged.length + 1,
      List.mem_filter.mpr ⟨hcn, (hkeepF _ hcn).mpr (Or.inl rfl)⟩, ?_⟩
    simp [gm06CutRowDart, GM06CutPosition.pathEnds, hne']
  · -- the left copy holds the dart before the positive inner cuff end
    rw [hcopy]
    set y := row.formPerm.symm (2 * rep.tagged.length) with hy_def
    have hfy : row.formPerm y = 2 * rep.tagged.length := Equiv.apply_symm_apply _ _
    have hy : y ∈ row := List.mem_of_formPerm_apply_mem (by rw [hfy]; exact hcp)
    have hiy := List.idxOf_lt_length_of_mem hy
    have hicp := List.idxOf_lt_length_of_mem hcp
    have hib := List.idxOf_lt_length_of_mem hb
    have hf := List.formPerm_apply_getElem row hrn (row.idxOf y) hiy
    rw [List.getElem_idxOf hiy, hfy] at hf
    have hidx : (row.idxOf y + 1) % row.length = row.idxOf (2 * rep.tagged.length) :=
      hrn.getElem_inj_iff.mp (hf.symm.trans (List.getElem_idxOf hicp).symm)
    have hbc := idxOf_ne_of_ne hb hcp hne
    have hblock : y = b ∨ GM06DrawingData.cyclicBetween (row.idxOf b)
        (row.idxOf (2 * rep.tagged.length)) (row.idxOf y) = true := by
      by_cases hyb : y = b
      · exact Or.inl hyb
      right
      have hyb' := idxOf_ne_of_ne hy hb hyb
      unfold GM06DrawingData.cyclicBetween
      rcases mod_two_cases (m := row.idxOf y + 1) (n := row.length) (by omega) with
        ⟨hm, hm2⟩ | ⟨hm, hm2⟩ <;> rw [hm] at hidx <;> split_ifs <;>
        simp only [decide_eq_true_eq] <;> omega
    obtain ⟨i, hi, hiy'⟩ := (block_iff_iterate hrn hb hcp hne y).mp ⟨hy, hblock⟩
    refine ⟨i, hi, 1, ?_⟩
    have hu : gm06UncutDart gapCut = 2 * rep.tagged.length + 1 := by
      simp only [gm06UncutDart, gm06CutDart]
      omega
    have hmate : gm06DartMate (2 * rep.tagged.length + 1) = 2 * rep.tagged.length := by
      simp only [gm06DartMate]
      split_ifs <;> omega
    rw [hiy', Function.iterate_one, hu, Equiv.trans_apply, dartMatePerm_apply, hmate,
      rotationPermutation_symm_apply_row x.rotations rep.rows_flatten_nodup row hrow _ hcp]

end Copies

end GM06CurrentDrawingRep

end GraphMinor.GM06
