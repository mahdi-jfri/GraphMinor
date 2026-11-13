module

public import GraphMinor.Compute.GM06Alg511BinaryReflectDrawing
public import GraphMinor.GM06.Alg511ReflectedPositiveInput
public import GraphMinor.GM06.Alg511ReflectedRowEncoding
public import GraphMinor.GM06.Alg511SuccessorSize
import Mathlib.Tactic

/-!
# The computed reflected drawing and actual linkage

The original positive drawing representation bounds every rotation
word by the augmented ordinary/inner/outer edge range. Apply the
verified finite drawing reflection to these rows, both cuffs and the
stored path table. Its exact output fields represent the reflected
positive cylinder drawing and reflected actual linkage.

Winding and target change sign, with feasibility preserved. All
binary current, target and increment rows stay untouched by this
geometric-data program. This completes the concrete drawing/encoding
part of the orientation reversal in VI (5.11), page 134. No region
rows are read or interpreted.
-/

public section
namespace GraphMinor.GM06
open GraphMinor.Compute GraphMinor.Compute.TwoPaths GraphMinor.Surface Set

/-- Every supplied positive rotation word names one of the
ordinary ends or one of the two fixed cuff families. -/
theorem GM06Alg511PositiveDrawingRep.rotation_darts_lt {x : GM06Alg511WindingInput} {G : Drawing ClosedCylinder}
    (rep : GM06Alg511PositiveDrawingRep x G) :
    ∀ row ∈ x.drawing.rotations, ∀ d ∈ row,
      d < 2 * (rep.graphTurn.graph.pairs.length + x.drawing.pathCount + x.drawing.pathCount) := by
  obtain ⟨F, edge, γ, _, _, _, _, _, _, _, _, _, _, hlen, hrows⟩ := rep.rotations
  change x.drawing.rotations.length = x.drawing.vertexCount at hlen
  intro row hrow d hd
  obtain ⟨i, hi, hget⟩ := List.mem_iff_getElem.mp hrow
  have hin : i < x.drawing.vertexCount := by rw [← hlen]; exact hi
  have hread : x.drawing.rotations.getD i [] = row := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some]
    exact hget
  have hv := hrows ⟨i, hin⟩
  change GM06SuccessorRotationRowRep edge γ (cylinderToSphere (rep.graphTurn.graph.vertex ⟨i, hin⟩).val)
    (x.drawing.rotations.getD i []) at hv
  rw [hread] at hv
  obtain ⟨a, ha⟩ := (hv.2.1 d).mp hd
  rw [← ha]
  have hbound := halfEdgeLabel_lt edge a
  omega

/-- The actual drawing reflection program produces all six fields
for the reflected successor instance, with its actual reflected
linkage, negated winding and unchanged feasibility question. Its
resource premises are graph/code sizes only. -/
theorem alg511_binary_drawing_reflection_exec {w : ℕ} {x : GM06Alg511WindingInput} {G : Drawing ClosedCylinder}
    (rep : GM06Alg511PositiveDrawingRep x G) (hk : 0 < x.drawing.pathCount)
    (L : CylinderLinkage x.drawing.pathCount G) (rows : List (List ℕ))
    (henc : GM06LinkageRowsEncoding L rep.graphTurn.graph.initialTagged rep.graphTurn.graph.vertexLabels rep.graphTurn.graph.edgeLabels rows)
    (theta : ℝ) (hTheta : L.HasTheta theta) (s : State)
    (hw : 2 < 2 ^ w) (hn : x.drawing.vertexCount < 2 ^ w)
    (haug : 2 * (rep.graphTurn.graph.pairs.length + x.drawing.pathCount + x.drawing.pathCount) < 2 ^ w)
    (hcode : (gm06EncodeRows x.drawing.rotations).length < 2 ^ w)
    (hwords : ∀ d ∈ gm06EncodeRows x.drawing.rotations, d < 2 ^ w)
    (hcap : 1 + x.drawing.pathCount + x.drawing.pathCount * x.drawing.vertexCount < 2 ^ w)
    (hvertices : s.arrs 1500 = [x.drawing.vertexCount])
    (hE : s.arrs 1230 = x.drawing.endpoints) (hR : s.arrs 1231 = gm06EncodeRows x.drawing.rotations)
    (hI : s.arrs 1210 = x.drawing.innerCuff) (hO : s.arrs 1211 = x.drawing.outerCuff)
    (hP : s.arrs 8 = gm06EncodeRows rows) (hK : s.regs 52 = x.drawing.pathCount) :
    ∃ t u, Exec w gm06Alg511BinaryReflectDrawingProg s t u ∧
      u ≤ 80 + 24 * (gm06EncodeRows x.drawing.rotations).length +
        x.drawing.rotations.length * (607 + 600 * (gm06EncodeRows x.drawing.rotations).length) +
        28 * x.drawing.innerCuff.length + 28 * x.drawing.outerCuff.length +
        12 * (1 + x.drawing.pathCount + x.drawing.pathCount * x.drawing.vertexCount) +
        x.drawing.pathCount * (307 + 40 * x.drawing.pathCount + 150 * x.drawing.vertexCount +
          100 * (1 + x.drawing.pathCount + x.drawing.pathCount * x.drawing.vertexCount)) ∧
      t.arrs 1500 = [x.reflected.drawing.vertexCount] ∧ t.arrs 1230 = x.reflected.drawing.endpoints ∧
      t.arrs 1231 = gm06EncodeRows x.reflected.drawing.rotations ∧
      t.arrs 1210 = x.reflected.drawing.innerCuff ∧ t.arrs 1211 = x.reflected.drawing.outerCuff ∧
      t.arrs 8 = gm06EncodeRows (gm06Alg511ReflectedPathRows rows) ∧
      t.regs 52 = x.reflected.drawing.pathCount ∧
      GM06LinkageRowsEncoding (alg511ReflectedStoredLinkage hk L)
        (alg511ReflectedPositiveDrawingRep rep hk).graphTurn.graph.initialTagged
        (alg511ReflectedPositiveDrawingRep rep hk).graphTurn.graph.vertexLabels
        (alg511ReflectedPositiveDrawingRep rep hk).graphTurn.graph.edgeLabels (gm06Alg511ReflectedPathRows rows) ∧
      (alg511ReflectedStoredLinkage hk L).HasTheta (-theta) ∧
      (IsThetaFeasible x.reflected.drawing.pathCount (section5ReflectedDrawing x.drawing.pathCount G) x.reflected.drawing.target ↔
        IsThetaFeasible x.drawing.pathCount G x.drawing.target) ∧
      Keeps [20, 60, 4, 1400, 1401, 31, 7, 8, 9, 11, 23, 24, 323, 324, 313, 98, 1701]
        [4, 25, 26, 27, 28, 1231, 1210, 1702, 1211, 1703, 1700, 13, 8] s t := by
  have hends : x.drawing.endpoints.length = 2 * rep.graphTurn.graph.pairs.length := by
    have hh := rep.graphTurn.graph.endpoints
    change x.drawing.endpoints = _ at hh
    rw [hh, gm06EndpointWords_length, List.length_map]
  have hhalf : x.drawing.endpoints.length / 2 = rep.graphTurn.graph.pairs.length := by omega
  have hkfit : x.drawing.pathCount < 2 ^ w := (rep.graphTurn.pathCount_le_vertexCount hk).trans_lt hn
  have hIlen : x.drawing.innerCuff.length = x.drawing.pathCount := by rw [rep.graphTurn.inner, List.length_ofFn]
  have hOlen : x.drawing.outerCuff.length = x.drawing.pathCount := by rw [rep.graphTurn.outer, List.length_ofFn]
  have hwi : ∀ v ∈ x.drawing.innerCuff, v < 2 ^ w := by
    intro v hv
    rw [rep.graphTurn.inner] at hv
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hv
    exact (rep.graphTurn.source i).isLt.trans hn
  have hwo : ∀ v ∈ x.drawing.outerCuff, v < 2 ^ w := by
    intro v hv
    rw [rep.graphTurn.outer] at hv
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hv
    exact (rep.graphTurn.target i).isLt.trans hn
  have hpathBounds := alg511_linkage_rows_bounds rep.graphTurn.graph henc
  have hendsFit : x.drawing.endpoints.length < 2 ^ w := by omega
  have hpaths : ∀ row ∈ rows, row.length ≤ x.drawing.vertexCount ∧ ∀ d ∈ row, d < 2 ^ w := by
    intro row hr
    have hh := hpathBounds.2 row hr
    change row.length + 1 ≤ x.drawing.vertexCount ∧ _ at hh
    exact ⟨by omega, fun d hd => (hh.2 d hd).trans hendsFit⟩
  obtain ⟨t, u, he, ht, hkeep, hrot, hinner, houter, hpath⟩ := gm06Alg511BinaryReflectDrawingProg_exec (w := w)
    rep.graphTurn.graph.pairs.length x.drawing.pathCount x.drawing.vertexCount
    x.drawing.endpoints x.drawing.innerCuff x.drawing.outerCuff x.drawing.rotations rows s hw hn hends haug hcode hwords
      rep.rotation_darts_lt (hIlen ▸ hkfit) (hOlen ▸ hkfit) hwi hwo henc.1 hcap hpaths hE hR hI hO hP hK
  have hrot' : t.arrs 1231 = gm06EncodeRows x.reflected.drawing.rotations := by
    change t.arrs 1231 = gm06EncodeRows (x.drawing.rotations.map
      (fun row => row.reverse.map (gm06Alg511ReflectAugmentedDart (x.drawing.endpoints.length / 2) x.drawing.pathCount)))
    unfold gm06Alg511ReflectedTableRow at hrot
    simpa only [hhalf, Bool.false_eq_true, ite_false] using hrot
  exact ⟨t, u, he, ht, (hkeep.2 1500 (by decide)).trans hvertices, (hkeep.2 1230 (by decide)).trans hE, hrot',
    hinner, houter, hpath, (hkeep.1 52 (by decide)).trans hK,
    alg511_reflected_linkage_rows rep.graphTurn hk L rows henc,
    alg511_reflectedStoredLinkage_hasTheta hk L hTheta, alg511_reflected_target_feasible_iff hk, hkeep⟩

end GraphMinor.GM06
