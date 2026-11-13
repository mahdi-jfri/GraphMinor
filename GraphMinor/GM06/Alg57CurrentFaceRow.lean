module

public import GraphMinor.GM06.Alg57CurrentRegionOrbit
public import GraphMinor.GM06.Alg57FiniteFaceOrbit
import GraphMinor.Compute.GM06CutRowsFacts

/-!
# The selected face row of the current computed cut

For VI (5.7), page 133, the current drawing supplies all bounds,
uniqueness and paired-end conditions needed by the pure finite face
routine. Its selected row is the actual numeric split orbit. Mapping
that row back to old darts reads incidence with the specified region.
-/

public section
namespace GraphMinor.GM06
open Set Topology GraphMinor.Surface GraphMinor.GM11 GraphMinor.Compute unitInterval

namespace GM06CurrentDrawingRep
variable {k : ℕ} {x : GM06SuccessorInput} {G : Drawing ClosedCylinder}
  {L : CylinderLinkage k G} (rep : GM06CurrentDrawingRep x G L)
include rep

/-- Every word in the full current row table is in the augmented
permanent dart range. -/
theorem rows_word_lt (hG : IsCylinderSection5Drawing k G) {d : ℕ}
    (hd : d ∈ x.rotations.flatten) : d < 2 * (rep.tagged.length + (k + k)) := by
  obtain ⟨row, hr, hd⟩ := List.mem_flatten.mp hd
  obtain ⟨a, ha, heq⟩ := List.mem_iff_getElem.mp hr
  let v : Fin x.vertexCount := ⟨a, rep.rows_length ▸ ha⟩
  apply rep.row_word_lt hG (a := v)
  simpa only [v, List.getD_eq_getElem _ _ ha, heq] using hd

/-- The current computed cut has all finite face-input properties,
with no hypotheses about its face or component representation. -/
theorem cut_data_face_encoding (hG : IsCylinderSection5Drawing k G) (live : List ℕ) :
    let data := gm06CutDataOfLinkage x.vertexCount rep.tagged.length x.endpoints x.linkage
      x.innerCuff x.outerCuff x.rotations live
    let m := 2 * (rep.tagged.length + (k + k))
    data.rotations.flatten.Nodup ∧
      (∀ d ∈ data.rotations.flatten, d < 2 * m) ∧
      (∀ d ∈ data.activeDarts, d < 2 * m) ∧
      (∀ d, d ∈ data.activeDarts ↔ d ∈ data.rotations.flatten) ∧
      ∀ d ∈ data.activeDarts, gm06DartMate d ∈ data.activeDarts := by
  have hlen := rep.cuff_lengths
  have hkeys : ∀ d ∈ x.rotations.flatten,
      d < 2 * (rep.tagged.length + x.innerCuff.length + x.outerCuff.length) := by
    intro d hd
    have hh := rep.rows_word_lt hG hd
    rw [hlen.1, hlen.2]
    omega
  have hb := gm06CutDataOfLinkage_dart_bounds (n := x.vertexCount) x.endpoints x.linkage
    x.innerCuff x.outerCuff x.rotations live hkeys
  simp only [hlen.1, hlen.2] at hb
  refine ⟨gm06SplitRotationRows_nodup _ _ rep.rows_flatten_nodup, ?_, ?_, ?_, ?_⟩
  · intro d hd
    have hh := hb.1 d hd
    omega
  · intro d hd
    have hh := hb.2.1 d hd
    omega
  · intro d
    have hac := gm06CutDataOfLinkage_active_iff x.vertexCount rep.tagged.length
      x.endpoints x.linkage x.innerCuff x.outerCuff x.rotations live d
    dsimp only at hac
    rw [hac]
    exact and_iff_right_of_imp (fun hd => by
      have hh := hb.1 d hd
      simp only [hlen.1, hlen.2]
      omega)
  · intro d hd
    have hm := rep.cut_rows_mate hG (q := d)
    apply (gm06CutDataOfLinkage_active_iff _ _ _ _ _ _ _ _ _).mpr
    have hh := (gm06CutDataOfLinkage_active_iff _ _ _ _ _ _ _ _ _).mp hd
    have hbound : gm06DartMate d < 4 * (rep.tagged.length + x.innerCuff.length + x.outerCuff.length) := by
      have hb := gm06DartMate_lt (m := 2 * (rep.tagged.length + x.innerCuff.length + x.outerCuff.length))
        (j := d) (by omega)
      omega
    exact ⟨hbound, hm hh.2⟩

/-- The pure face routine on the complete computed cut returns the
exact selected numeric orbit for each inner cuff index. -/
theorem cut_face_row (hG : IsCylinderSection5Drawing k G) (live : List ℕ) (i : Fin k) :
    let data := gm06CutDataOfLinkage x.vertexCount rep.tagged.length x.endpoints x.linkage
      x.innerCuff x.outerCuff x.rotations live
    let m := 2 * (rep.tagged.length + (k + k))
    let c := gm06CutDart (2 * (rep.tagged.length + i.val) + 1) 0
    ∃ row : List ℕ, gm06CutFaceIncidence (2 * x.vertexCount) m data c =
        some (row, gm06IncV (2 * x.vertexCount) data.origins row, gm06IncE m row) ∧
      ∀ d : ℕ, d ∈ row ↔ ∃ j : ℕ,
        (dartMatePerm.trans (gm06RotationPermutation data.rotations).symm)^[j] c = d := by
  dsimp only
  obtain ⟨hn, hk, ha, hc, hm⟩ := rep.cut_data_face_encoding hG live
  apply cutFaceIncidence_orbit _ hn hk ha hc hm
  exact (hc _).mpr (rep.reverse_inner_mem_cut hG i)

/-- The selected row of the actual complete cut reads precisely
region incidence after projecting each of its directed labels. -/
theorem region_incidence_cut_row (hk : 1 < k)
    (hG : IsCylinderSection5Drawing k G) (hno : ∀ (G₁ : Drawing ClosedCylinder) (L₁ : CylinderLinkage k G₁),
      IsCylinderSection5Drawing k G₁ → ¬ Section5Reduction2Step k G L G₁ L₁)
    (live : List ℕ) (i : Fin k) :
    let data := gm06CutDataOfLinkage x.vertexCount rep.tagged.length x.endpoints x.linkage
      x.innerCuff x.outerCuff x.rotations live
    let m := 2 * (rep.tagged.length + (k + k))
    let c := gm06CutDart (2 * (rep.tagged.length + i.val) + 1) 0
    ∃ row : List ℕ, gm06CutFaceIncidence (2 * x.vertexCount) m data c =
        some (row, gm06IncV (2 * x.vertexCount) data.origins row, gm06IncE m row) ∧
      (∀ v : ClosedCylinder, v ∈ G.V →
        (v ∈ closure (cylinderRegion k G i) ↔
          ∃ d : DrawingDart (cylinderSphereDrawing rep.cuffed),
            dartVertex rep.par d = cylinderToSphere v ∧
            ∃ q ∈ row, gm06UncutDart q = persistentDartLabel rep.label d)) ∧
      (∀ d : DrawingDart (cylinderSphereDrawing rep.cuffed),
        d.val.1 ⊆ cylinderToSphere '' closure (cylinderRegion k G i) ↔
          (∃ q ∈ row, gm06UncutDart q = persistentDartLabel rep.label d) ∨
          ∃ q ∈ row, gm06UncutDart q = gm06DartMate (persistentDartLabel rep.label d)) := by
  dsimp only
  obtain ⟨row, hout, horbit⟩ := rep.cut_face_row hG live i
  have hmem (d : ℕ) : (∃ q ∈ row, gm06UncutDart q = d) ↔
      ∃ j : ℕ, gm06UncutDart ((dartMatePerm.trans
        (gm06RotationPermutation (gm06SplitRotationRows
          (gm06BuildCutTables x.vertexCount rep.tagged.length x.endpoints x.linkage
            x.innerCuff x.outerCuff) x.rotations)).symm)^[j]
              (gm06CutDart (2 * (rep.tagged.length + i.val) + 1) 0)) = d := by
    constructor
    · rintro ⟨q, hq, hqd⟩
      obtain ⟨j, hj⟩ := (horbit q).mp hq
      exact ⟨j, (congrArg gm06UncutDart hj).trans hqd⟩
    · rintro ⟨j, hj⟩
      exact ⟨_, (horbit _).mpr ⟨j, rfl⟩, hj⟩
  obtain ⟨hV, hE⟩ := rep.region_incidence_cut_orbit hk hG hno i
  refine ⟨row, hout, ?_, ?_⟩
  · intro v hv
    rw [hV v hv]
    exact exists_congr (fun d => and_congr_right (fun _ => (hmem _).symm))
  · intro d
    rw [hE, ← hmem, ← hmem]

end GM06CurrentDrawingRep
end GraphMinor.GM06
