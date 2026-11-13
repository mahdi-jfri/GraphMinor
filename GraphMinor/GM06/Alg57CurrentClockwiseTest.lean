module

public import GraphMinor.GM06.Alg57CurrentDrawingRep
public import GraphMinor.GM06.Section5SignedRotationClockwise
public import GraphMinor.Compute.GM06ClockwiseCuffMarkers
import GraphMinor.GM06.Alg57ContractedCuffData
import GraphMinor.GM06.Alg57CurrentEndClassification
import GraphMinor.GM06.Alg57CurrentCuffEnds
import GraphMinor.GM06.Alg57TargetBlockData
import GraphMinor.GM06.Alg57InputCutFits

/-!
# Reading the clockwise test from the actual current rotations

The Reduction 1 scan in VI (5.7), page 133, uses the negative cuff
end, first linkage end and positive cuff end. They are actual ends
of the current cuff augmentation, even after deletions and
contractions. Their numeric words and positive polar directions
come from the current row interpretation. Thus the existing signed
crossing theorem reads the corrected side condition from these
literal permanent rows, without extra geometric input fields.
-/

public section
namespace GraphMinor.GM06
open Set Topology Real GraphMinor.Surface GraphMinor.GM11 GraphMinor.Compute unitInterval

/-- The full positive inner-gap parametrization starts at the
canonical initial lift. -/
theorem initialCuffGapCurve_forward_angle {k : ℕ} (i : Fin k) (t : I) :
    initialCuffGapCurve k i t = cylinderPoint 1 (by norm_num)
      ((cylinderInitialLift k i).2 + 2 * π * (t : ℝ) / k) := by
  apply Subtype.ext
  apply Prod.ext
  · rfl
  · change Circle.exp _ = Circle.exp _
    congr 1
    dsimp only [initialCuffGapCurve, ContinuousMap.coe_mk, cylinderInitialLift]
    ring

/-- The preceding inner gap has the same full parametrization
measured backwards from the canonical initial lift. Its wrap at
index zero differs by a full turn, including when there is one path. -/
theorem initialCuffGapCurve_preceding_angle {k : ℕ} (i : Fin k) (t : I) :
    initialCuffGapCurve k (finPredCycle i) t = cylinderPoint 1 (by norm_num)
      ((cylinderInitialLift k i).2 - 2 * π / k + 2 * π * (t : ℝ) / k) := by
  apply Subtype.ext
  apply Prod.ext
  · rfl
  · change Circle.exp _ = Circle.exp _
    by_cases hi : i.val = 0
    · have hk : (k : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr i.pos.ne'
      have hk' : ((k - 1 + 1 : ℕ) : ℝ) = k := by rw [Nat.sub_add_cancel i.pos]
      simp only [finPredCycle, hi, dite_true,
        cylinderInitialLift, Nat.zero_add, Nat.cast_one]
      rw [hk']
      have heq : 2 * ((k : ℝ) + (t : ℝ)) * π / k = 2 * π * (t : ℝ) / k + 2 * π := by
        field_simp
        ring
      rw [heq, Circle.exp_add_two_pi]
      congr 1
      ring
    · have hi' : 1 ≤ i.val := Nat.one_le_iff_ne_zero.mpr hi
      have heq : ((i.val - 1 + 1 : ℕ) : ℝ) = i.val := by rw [Nat.sub_add_cancel hi']
      simp only [finPredCycle, hi, dite_false,
        cylinderInitialLift]
      rw [heq, Nat.cast_add, Nat.cast_one]
      congr 1
      ring

/-- Every actual current source row supplies all three markers
and computes the clockwise condition for every active ordinary edge.
The returned first word is the literal first linkage word. -/
theorem GM06CurrentDrawingRep.source_row_clockwise_test
    {k : ℕ} {x : GM06SuccessorInput} {G : Drawing ClosedCylinder} {θ : ℝ}
    {L : CylinderLinkage k G} (rep : GM06CurrentDrawingRep x G L)
    (hG : IsCylinderSection5Drawing k G) (hθ : L.HasTheta θ) (i : Fin k) :
    let xs := x.rotations.getD (rep.source i).val []
    let neg := 2 * (rep.tagged.length + gm06PreviousCuffIndex k i.val) + 1
    let pos := 2 * (rep.tagged.length + i.val)
    ∃ (first : ℕ) (rest : List ℕ),
      x.linkage.getD i.val [] = first :: rest ∧ first < 2 * rep.tagged.length ∧
      xs.Nodup ∧ neg ∈ xs ∧ first ∈ xs ∧ pos ∈ xs ∧
      neg ≠ first ∧ neg ≠ pos ∧ first ≠ pos ∧
      ∀ j : Fin rep.tagged.length, rep.tagged[j].2 = 1 →
        (IsClockwiseInitialEdge L i (rep.edge j) ↔
          gm06CalibratedSectorFlag xs neg first pos (2 * j.val) = 1 ∨
          gm06CalibratedSectorFlag xs neg first pos (2 * j.val + 1) = 1) := by
  classical
  dsimp only
  have hi : i.val < x.linkage.length := by rw [rep.linkage.1]; exact i.isLt
  have hne := rep.linkage.row_nonempty i
  cases hrow : x.linkage[i.val]'hi with
  | nil => simp only [hrow, List.length_nil] at hne; omega
  | cons first rest =>
    obtain ⟨W, _, henc, hP⟩ := rep.linkage.path i
    rw [hrow] at henc
    obtain ⟨hfirst, hactive⟩ := henc.active_words first (by simp)
    obtain ⟨_, _, _, _, _, _, _, htail, _, _⟩ := henc.first_step
    have hpath : rep.edge ⟨first / 2, by omega⟩ ∈ (L.pathDrawing i).E := by
      rw [← hP, walkDrawing_E]
      exact (henc.edge_mem_iff _).mpr ⟨first, by simp, hfirst, rfl⟩
    have hends := rep.ordinary_dart_halfedges ⟨first, hfirst⟩ hactive
    rw [htail] at hends
    obtain ⟨b, _, hbedge, _, hbword, _⟩ := hends
    obtain ⟨minus, plus, _, hm, hp, hml, hpl, _⟩ := rep.inner_cuff_ends i
    have hrowrep := rep.rows (rep.source i) (rep.source_live i)
    rw [rep.source_point] at hrowrep
    have hpV : cylinderToSphere (cylinderM1Point k i) ∈ (cylinderSphereDrawing rep.cuffed).V := by
      rw [cylinderSphereDrawing_V]
      have hsG : cylinderM1Point k i ∈ G.V := rep.source_point i ▸ rep.vertex_mem _ (rep.source_live i)
      exact mem_image_of_mem _ (rep.cuffed_V.symm ▸ hsG)
    obtain ⟨Φ, z, hpolar, _, _, hzi, hsorted, hspoke, hlabel⟩ :=
      hrowrep.exists_small_chart_all rep.edgePar hpV ⟨cylToPlane (cylinderM1Point k i), rfl⟩
        isOpen_univ (mem_univ _)
    let d := fun a : halfEdges (cylinderSphereDrawing rep.cuffed) rep.par
      (cylinderToSphere (cylinderM1Point k i)) => z (gm06PersistentHalfEdgeLabel rep.label a)
    have hmAngle (t : I) : rep.par minus.val.1 t = cylinderToSphere (cylinderPoint 1 (by norm_num)
        ((cylinderInitialLift k i).2 - 2 * π / k + 2 * π * (t : ℝ) / k)) := by
      rw [congrArg Prod.fst hm, rep.inner_par, initialCuffGapCurve_preceding_angle]
    have hpAngle (t : I) : rep.par plus.val.1 t = cylinderToSphere (cylinderPoint 1 (by norm_num)
        ((cylinderInitialLift k i).2 + 2 * π * (t : ℝ) / k)) := by
      rw [congrArg Prod.fst hp, rep.inner_par, initialCuffGapCurve_forward_angle]
    have hneg : 2 * (rep.tagged.length + gm06PreviousCuffIndex k i.val) + 1 ∈
        x.rotations.getD (rep.source i).val [] := by
      rw [previousCuffIndex_eq_pred]
      exact (hrowrep.2.1 _).mpr ⟨minus, hml⟩
    have hfirstRow : first ∈ x.rotations.getD (rep.source i).val [] :=
      (hrowrep.2.1 _).mpr ⟨b, hbword⟩
    have hpos : 2 * (rep.tagged.length + i.val) ∈ x.rotations.getD (rep.source i).val [] :=
      (hrowrep.2.1 _).mpr ⟨plus, hpl⟩
    have hbdF : bd ClosedCylinder ⊆ rep.cuffed.U := by
      rw [rep.cuffed_U]
      exact subset_union_right
    have htest := clockwise_edge_iff_calibrated_signed_rotation rep.edge
      (fun j => rep.tagged[j].2 = 1) L hG rep.subdrawing hbdF hθ i rep.edgePar hpolar
      minus b plus d hspoke (congrArg Prod.snd hm) (congrArg Prod.snd hp)
      hmAngle hpAngle (by rw [hbedge, cylinderSphereDrawing_E]; exact mem_image_of_mem _ hpath)
      (fun j hj => (rep.links j hj).edge_mem)
      (x.rotations.getD (rep.source i).val []) z hzi hsorted
      _ first _ hneg hfirstRow hpos
      (by simp only [d, previousCuffIndex_eq_pred, hml])
      (by simp only [d, hbword]) (by simp only [d, hpl]) (by
        intro j hj u
        obtain ⟨f, hf, hl⟩ := rep.ordinary_labels j hj
        simpa only [hf, hl] using hlabel f u)
    exact ⟨first, rest, (List.getD_eq_getElem _ [] hi).trans hrow, hfirst,
      hrowrep.1, hneg, hfirstRow, hpos, htest⟩

end GraphMinor.GM06
